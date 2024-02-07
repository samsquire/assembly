
multibarrier-evented:     file format elf64-x86-64


Disassembly of section .init:

0000000000002000 <_init>:
    2000:	f3 0f 1e fa          	endbr64
    2004:	48 83 ec 08          	sub    $0x8,%rsp
    2008:	48 8b 05 d9 7f 00 00 	mov    0x7fd9(%rip),%rax        # 9fe8 <__gmon_start__@Base>
    200f:	48 85 c0             	test   %rax,%rax
    2012:	74 02                	je     2016 <_init+0x16>
    2014:	ff d0                	call   *%rax
    2016:	48 83 c4 08          	add    $0x8,%rsp
    201a:	c3                   	ret

Disassembly of section .plt:

0000000000002020 <.plt>:
    2020:	ff 35 4a 7e 00 00    	push   0x7e4a(%rip)        # 9e70 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 4c 7e 00 00    	jmp    *0x7e4c(%rip)        # 9e78 <_GLOBAL_OFFSET_TABLE_+0x10>
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

Disassembly of section .plt.got:

00000000000022e0 <__cxa_finalize@plt>:
    22e0:	f3 0f 1e fa          	endbr64
    22e4:	ff 25 0e 7d 00 00    	jmp    *0x7d0e(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    22ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

00000000000022f0 <free@plt>:
    22f0:	f3 0f 1e fa          	endbr64
    22f4:	ff 25 86 7b 00 00    	jmp    *0x7b86(%rip)        # 9e80 <free@GLIBC_2.2.5>
    22fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002300 <putchar@plt>:
    2300:	f3 0f 1e fa          	endbr64
    2304:	ff 25 7e 7b 00 00    	jmp    *0x7b7e(%rip)        # 9e88 <putchar@GLIBC_2.2.5>
    230a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002310 <pthread_setaffinity_np@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 76 7b 00 00    	jmp    *0x7b76(%rip)        # 9e90 <pthread_setaffinity_np@GLIBC_2.34>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002320 <puts@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 6e 7b 00 00    	jmp    *0x7b6e(%rip)        # 9e98 <puts@GLIBC_2.2.5>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <setsockopt@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 66 7b 00 00    	jmp    *0x7b66(%rip)        # 9ea0 <setsockopt@GLIBC_2.2.5>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <clock_gettime@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 5e 7b 00 00    	jmp    *0x7b5e(%rip)        # 9ea8 <clock_gettime@GLIBC_2.17>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <fclose@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 56 7b 00 00    	jmp    *0x7b56(%rip)        # 9eb0 <fclose@GLIBC_2.2.5>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <strlen@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 4e 7b 00 00    	jmp    *0x7b4e(%rip)        # 9eb8 <strlen@GLIBC_2.2.5>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <__stack_chk_fail@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 46 7b 00 00    	jmp    *0x7b46(%rip)        # 9ec0 <__stack_chk_fail@GLIBC_2.4>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <io_uring_submit@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 3e 7b 00 00    	jmp    *0x7b3e(%rip)        # 9ec8 <io_uring_submit@LIBURING_2.0>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <nanosleep@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 36 7b 00 00    	jmp    *0x7b36(%rip)        # 9ed0 <nanosleep@GLIBC_2.2.5>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <strrchr@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 2e 7b 00 00    	jmp    *0x7b2e(%rip)        # 9ed8 <strrchr@GLIBC_2.2.5>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <fputs@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 26 7b 00 00    	jmp    *0x7b26(%rip)        # 9ee0 <fputs@GLIBC_2.2.5>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <close@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 1e 7b 00 00    	jmp    *0x7b1e(%rip)        # 9ee8 <close@GLIBC_2.2.5>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <strtok_r@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 16 7b 00 00    	jmp    *0x7b16(%rip)        # 9ef0 <strtok_r@GLIBC_2.2.5>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <read@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 0e 7b 00 00    	jmp    *0x7b0e(%rip)        # 9ef8 <read@GLIBC_2.2.5>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <calloc@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 06 7b 00 00    	jmp    *0x7b06(%rip)        # 9f00 <calloc@GLIBC_2.2.5>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <strcmp@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 fe 7a 00 00    	jmp    *0x7afe(%rip)        # 9f08 <strcmp@GLIBC_2.2.5>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <__memcpy_chk@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 f6 7a 00 00    	jmp    *0x7af6(%rip)        # 9f10 <__memcpy_chk@GLIBC_2.3.4>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <stat@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 ee 7a 00 00    	jmp    *0x7aee(%rip)        # 9f18 <stat@GLIBC_2.33>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <memcpy@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 e6 7a 00 00    	jmp    *0x7ae6(%rip)        # 9f20 <memcpy@GLIBC_2.14>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <io_uring_queue_init@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 de 7a 00 00    	jmp    *0x7ade(%rip)        # 9f28 <io_uring_queue_init@LIBURING_2.0>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <eventfd_write@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 d6 7a 00 00    	jmp    *0x7ad6(%rip)        # 9f30 <eventfd_write@GLIBC_2.7>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <malloc@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 ce 7a 00 00    	jmp    *0x7ace(%rip)        # 9f38 <malloc@GLIBC_2.2.5>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <listen@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 c6 7a 00 00    	jmp    *0x7ac6(%rip)        # 9f40 <listen@GLIBC_2.2.5>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <__strcpy_chk@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 be 7a 00 00    	jmp    *0x7abe(%rip)        # 9f48 <__strcpy_chk@GLIBC_2.3.4>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <__io_uring_get_cqe@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 b6 7a 00 00    	jmp    *0x7ab6(%rip)        # 9f50 <__io_uring_get_cqe@LIBURING_2.0>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <__printf_chk@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 ae 7a 00 00    	jmp    *0x7aae(%rip)        # 9f58 <__printf_chk@GLIBC_2.3.4>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <bind@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 a6 7a 00 00    	jmp    *0x7aa6(%rip)        # 9f60 <bind@GLIBC_2.2.5>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <pthread_create@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 9e 7a 00 00    	jmp    *0x7a9e(%rip)        # 9f68 <pthread_create@GLIBC_2.34>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <open@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 96 7a 00 00    	jmp    *0x7a96(%rip)        # 9f70 <open@GLIBC_2.2.5>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <fopen@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 8e 7a 00 00    	jmp    *0x7a8e(%rip)        # 9f78 <fopen@GLIBC_2.2.5>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <perror@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 86 7a 00 00    	jmp    *0x7a86(%rip)        # 9f80 <perror@GLIBC_2.2.5>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <exit@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 7e 7a 00 00    	jmp    *0x7a7e(%rip)        # 9f88 <exit@GLIBC_2.2.5>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <eventfd@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 76 7a 00 00    	jmp    *0x7a76(%rip)        # 9f90 <eventfd@GLIBC_2.7>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <fwrite@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 6e 7a 00 00    	jmp    *0x7a6e(%rip)        # 9f98 <fwrite@GLIBC_2.2.5>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <__fprintf_chk@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 66 7a 00 00    	jmp    *0x7a66(%rip)        # 9fa0 <__fprintf_chk@GLIBC_2.3.4>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002540 <io_uring_register_eventfd@plt>:
    2540:	f3 0f 1e fa          	endbr64
    2544:	ff 25 5e 7a 00 00    	jmp    *0x7a5e(%rip)        # 9fa8 <io_uring_register_eventfd@LIBURING_2.0>
    254a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002550 <pthread_join@plt>:
    2550:	f3 0f 1e fa          	endbr64
    2554:	ff 25 56 7a 00 00    	jmp    *0x7a56(%rip)        # 9fb0 <pthread_join@GLIBC_2.34>
    255a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002560 <strerror@plt>:
    2560:	f3 0f 1e fa          	endbr64
    2564:	ff 25 4e 7a 00 00    	jmp    *0x7a4e(%rip)        # 9fb8 <strerror@GLIBC_2.2.5>
    256a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002570 <__ctype_tolower_loc@plt>:
    2570:	f3 0f 1e fa          	endbr64
    2574:	ff 25 46 7a 00 00    	jmp    *0x7a46(%rip)        # 9fc0 <__ctype_tolower_loc@GLIBC_2.3>
    257a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002580 <__sprintf_chk@plt>:
    2580:	f3 0f 1e fa          	endbr64
    2584:	ff 25 3e 7a 00 00    	jmp    *0x7a3e(%rip)        # 9fc8 <__sprintf_chk@GLIBC_2.3.4>
    258a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002590 <socket@plt>:
    2590:	f3 0f 1e fa          	endbr64
    2594:	ff 25 36 7a 00 00    	jmp    *0x7a36(%rip)        # 9fd0 <socket@GLIBC_2.2.5>
    259a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

00000000000025a0 <fatal_error>:
struct Snapshot {
  struct timespec start;
  struct timespec end;
};

void fatal_error(const char *syscall) {
    25a0:	f3 0f 1e fa          	endbr64
    25a4:	50                   	push   %rax
    25a5:	58                   	pop    %rax
    25a6:	50                   	push   %rax
    perror(syscall);
    25a7:	e8 44 ff ff ff       	call   24f0 <perror@plt>
    exit(1);
    25ac:	bf 01 00 00 00       	mov    $0x1,%edi
    25b1:	e8 4a ff ff ff       	call   2500 <exit@plt>

00000000000025b6 <copy_file_contents.cold>:
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");
    25b6:	48 8d 3d 63 4c 00 00 	lea    0x4c63(%rip),%rdi        # 7220 <_IO_stdin_used+0x220>
    25bd:	e8 de ff ff ff       	call   25a0 <fatal_error>

00000000000025c2 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    25c2:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
    25c8:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25d0:	0f 0b                	ud2

00000000000025d2 <add_read_request.cold>:
    25d2:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25da:	0f 0b                	ud2

00000000000025dc <_send_static_string_content.cold>:
    25dc:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    25e2:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25ea:	0f 0b                	ud2

00000000000025ec <add_accept_request.cold>:
    25ec:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25f4:	0f 0b                	ud2

00000000000025f6 <io_thread.cold>:
        break;
      }
      printf("Received wait finished\n");
      struct Request *req = (struct Request *) cqe->user_data;
      if (ret < 0)
          fatal_error("io_uring_wait_cqe");
    25f6:	48 8d 3d f3 4b 00 00 	lea    0x4bf3(%rip),%rdi        # 71f0 <_IO_stdin_used+0x1f0>
    25fd:	e8 9e ff ff ff       	call   25a0 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    2602:	48 8d 3d 6b 4b 00 00 	lea    0x4b6b(%rip),%rdi        # 7174 <_IO_stdin_used+0x174>
    2609:	e8 92 ff ff ff       	call   25a0 <fatal_error>
    fatal_error("listen()");
    260e:	48 8d 3d 7f 4b 00 00 	lea    0x4b7f(%rip),%rdi        # 7194 <_IO_stdin_used+0x194>
    2615:	e8 86 ff ff ff       	call   25a0 <fatal_error>
    261a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2622:	0f 0b                	ud2
    2624:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    262c:	0f 0b                	ud2
      fatal_error("socket()");
    262e:	48 8d 3d 36 4b 00 00 	lea    0x4b36(%rip),%rdi        # 716b <_IO_stdin_used+0x16b>
    2635:	e8 66 ff ff ff       	call   25a0 <fatal_error>
      fatal_error("bind()");
    263a:	48 8d 3d 4c 4b 00 00 	lea    0x4b4c(%rip),%rdi        # 718d <_IO_stdin_used+0x18d>
    2641:	e8 5a ff ff ff       	call   25a0 <fatal_error>
    2646:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000002650 <main>:
    }


  return 0;
}
int main() {
    2650:	f3 0f 1e fa          	endbr64
    2654:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2656:	48 8d 3d f3 4f 00 00 	lea    0x4ff3(%rip),%rdi        # 7650 <_IO_stdin_used+0x650>
    265d:	41 56                	push   %r14
    265f:	41 55                	push   %r13
    2661:	41 54                	push   %r12
    2663:	55                   	push   %rbp
    2664:	53                   	push   %rbx
    2665:	48 81 ec 98 00 00 00 	sub    $0x98,%rsp
    266c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2675:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    267d:	48 8d 05 5c 16 00 00 	lea    0x165c(%rip),%rax        # 3ce0 <barriered_reset>
    2684:	66 48 0f 6e e8       	movq   %rax,%xmm5
    2689:	0f 16 2d d0 75 00 00 	movhps 0x75d0(%rip),%xmm5        # 9c60 <__do_global_dtors_aux_fini_array_entry+0x8>
    2690:	0f 29 6c 24 50       	movaps %xmm5,0x50(%rsp)
    2695:	e8 86 fc ff ff       	call   2320 <puts@plt>
    269a:	bf 0a 00 00 00       	mov    $0xa,%edi
    269f:	e8 5c fc ff ff       	call   2300 <putchar@plt>
    26a4:	ba 01 00 00 00       	mov    $0x1,%edx
    26a9:	48 8d 35 be 4b 00 00 	lea    0x4bbe(%rip),%rsi        # 726e <_IO_stdin_used+0x26e>
    26b0:	31 c0                	xor    %eax,%eax
    26b2:	bf 01 00 00 00       	mov    $0x1,%edi
    26b7:	e8 e4 fd ff ff       	call   24a0 <__printf_chk@plt>
    26bc:	ba 02 00 00 00       	mov    $0x2,%edx
    26c1:	48 8d 35 b6 4b 00 00 	lea    0x4bb6(%rip),%rsi        # 727e <_IO_stdin_used+0x27e>
    26c8:	31 c0                	xor    %eax,%eax
    26ca:	bf 01 00 00 00       	mov    $0x1,%edi
    26cf:	e8 cc fd ff ff       	call   24a0 <__printf_chk@plt>
    26d4:	ba 01 00 00 00       	mov    $0x1,%edx
    26d9:	48 8d 35 b3 4b 00 00 	lea    0x4bb3(%rip),%rsi        # 7293 <_IO_stdin_used+0x293>
    26e0:	31 c0                	xor    %eax,%eax
    26e2:	bf 01 00 00 00       	mov    $0x1,%edi
    26e7:	e8 b4 fd ff ff       	call   24a0 <__printf_chk@plt>
    26ec:	ba 02 00 00 00       	mov    $0x2,%edx
    26f1:	48 8d 35 ab 4b 00 00 	lea    0x4bab(%rip),%rsi        # 72a3 <_IO_stdin_used+0x2a3>
    26f8:	31 c0                	xor    %eax,%eax
    26fa:	bf 01 00 00 00       	mov    $0x1,%edi
    26ff:	e8 9c fd ff ff       	call   24a0 <__printf_chk@plt>
    2704:	48 8d 3d ae 4b 00 00 	lea    0x4bae(%rip),%rdi        # 72b9 <_IO_stdin_used+0x2b9>
    270b:	e8 10 fc ff ff       	call   2320 <puts@plt>
    2710:	ba 02 00 00 00       	mov    $0x2,%edx
    2715:	48 8d 35 b9 4b 00 00 	lea    0x4bb9(%rip),%rsi        # 72d5 <_IO_stdin_used+0x2d5>
    271c:	31 c0                	xor    %eax,%eax
    271e:	bf 01 00 00 00       	mov    $0x1,%edi
    2723:	e8 78 fd ff ff       	call   24a0 <__printf_chk@plt>
    2728:	ba 06 00 00 00       	mov    $0x6,%edx
    272d:	48 8d 35 bb 4b 00 00 	lea    0x4bbb(%rip),%rsi        # 72ef <_IO_stdin_used+0x2ef>
    2734:	31 c0                	xor    %eax,%eax
    2736:	bf 01 00 00 00       	mov    $0x1,%edi
    273b:	e8 60 fd ff ff       	call   24a0 <__printf_chk@plt>
    2740:	ba 01 00 00 00       	mov    $0x1,%edx
    2745:	48 8d 35 b7 4b 00 00 	lea    0x4bb7(%rip),%rsi        # 7303 <_IO_stdin_used+0x303>
    274c:	31 c0                	xor    %eax,%eax
    274e:	bf 01 00 00 00       	mov    $0x1,%edi
    2753:	e8 48 fd ff ff       	call   24a0 <__printf_chk@plt>
    2758:	ba 01 00 00 00       	mov    $0x1,%edx
    275d:	48 8d 35 b0 4b 00 00 	lea    0x4bb0(%rip),%rsi        # 7314 <_IO_stdin_used+0x314>
    2764:	31 c0                	xor    %eax,%eax
    2766:	bf 01 00 00 00       	mov    $0x1,%edi
    276b:	e8 30 fd ff ff       	call   24a0 <__printf_chk@plt>
    2770:	ba 02 00 00 00       	mov    $0x2,%edx
    2775:	48 8d 35 b0 4b 00 00 	lea    0x4bb0(%rip),%rsi        # 732c <_IO_stdin_used+0x32c>
    277c:	31 c0                	xor    %eax,%eax
    277e:	bf 01 00 00 00       	mov    $0x1,%edi
    2783:	e8 18 fd ff ff       	call   24a0 <__printf_chk@plt>
    2788:	ba 01 00 00 00       	mov    $0x1,%edx
    278d:	48 8d 35 24 4f 00 00 	lea    0x4f24(%rip),%rsi        # 76b8 <_IO_stdin_used+0x6b8>
    2794:	31 c0                	xor    %eax,%eax
    2796:	bf 01 00 00 00       	mov    $0x1,%edi
    279b:	e8 00 fd ff ff       	call   24a0 <__printf_chk@plt>
    27a0:	ba 01 00 00 00       	mov    $0x1,%edx
    27a5:	48 8d 35 3c 4f 00 00 	lea    0x4f3c(%rip),%rsi        # 76e8 <_IO_stdin_used+0x6e8>
    27ac:	31 c0                	xor    %eax,%eax
    27ae:	bf 01 00 00 00       	mov    $0x1,%edi
    27b3:	e8 e8 fc ff ff       	call   24a0 <__printf_chk@plt>
    27b8:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    27bd:	48 8d 35 84 4b 00 00 	lea    0x4b84(%rip),%rsi        # 7348 <_IO_stdin_used+0x348>
    27c4:	31 c0                	xor    %eax,%eax
    27c6:	bf 01 00 00 00       	mov    $0x1,%edi
    27cb:	e8 d0 fc ff ff       	call   24a0 <__printf_chk@plt>
    27d0:	ba 05 00 00 00       	mov    $0x5,%edx
    27d5:	48 8d 35 86 4b 00 00 	lea    0x4b86(%rip),%rsi        # 7362 <_IO_stdin_used+0x362>
    27dc:	31 c0                	xor    %eax,%eax
    27de:	bf 01 00 00 00       	mov    $0x1,%edi
    27e3:	e8 b8 fc ff ff       	call   24a0 <__printf_chk@plt>
    27e8:	48 8d 3d 00 49 00 00 	lea    0x4900(%rip),%rdi        # 70ef <_IO_stdin_used+0xef>
    27ef:	e8 2c fb ff ff       	call   2320 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    27f4:	be 18 00 00 00       	mov    $0x18,%esi
    27f9:	bf 01 00 00 00       	mov    $0x1,%edi
    27fe:	e8 ed fb ff ff       	call   23f0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2803:	be c8 00 00 00       	mov    $0xc8,%esi
    2808:	bf 06 00 00 00       	mov    $0x6,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    280d:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2812:	e8 d9 fb ff ff       	call   23f0 <calloc@plt>
    2817:	ba 02 00 00 00       	mov    $0x2,%edx
    281c:	bf 01 00 00 00       	mov    $0x1,%edi
    2821:	48 8d 35 4e 4b 00 00 	lea    0x4b4e(%rip),%rsi        # 7376 <_IO_stdin_used+0x376>
    2828:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    282d:	31 c0                	xor    %eax,%eax
    282f:	e8 6c fc ff ff       	call   24a0 <__printf_chk@plt>
    2834:	ba 04 00 00 00       	mov    $0x4,%edx
    2839:	48 8d 35 4c 4b 00 00 	lea    0x4b4c(%rip),%rsi        # 738c <_IO_stdin_used+0x38c>
    2840:	31 c0                	xor    %eax,%eax
    2842:	bf 01 00 00 00       	mov    $0x1,%edi
    2847:	e8 54 fc ff ff       	call   24a0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    284c:	be 10 00 00 00       	mov    $0x10,%esi
    2851:	bf 04 00 00 00       	mov    $0x4,%edi
    2856:	e8 95 fb ff ff       	call   23f0 <calloc@plt>
    285b:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
    2860:	49 89 c4             	mov    %rax,%r12
    2863:	48 8d 58 40          	lea    0x40(%rax),%rbx
    2867:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    286c:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    2871:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2879:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    287e:	49 83 c4 10          	add    $0x10,%r12
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2882:	e8 69 fb ff ff       	call   23f0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2887:	be 20 00 00 00       	mov    $0x20,%esi
    288c:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2891:	49 89 44 24 f8       	mov    %rax,-0x8(%r12)
    2896:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
    2899:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    28a3:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    28ad:	e8 3e fb ff ff       	call   23f0 <calloc@plt>
    28b2:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    28b9:	4c 39 e3             	cmp    %r12,%rbx
    28bc:	75 ae                	jne    286c <main+0x21c>
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
        other = abs(x - 1) % total_threads;
        thread_data[x].thread_index = 1;
    28be:	4c 8b 64 24 38       	mov    0x38(%rsp),%r12
    28c3:	45 31 f6             	xor    %r14d,%r14d
    28c6:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
    28ce:	4c 89 74 24 40       	mov    %r14,0x40(%rsp)
    28d3:	49 8d 84 24 c8 00 00 00 	lea    0xc8(%r12),%rax
    28db:	4d 89 e1             	mov    %r12,%r9
    28de:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    28e3:	4c 89 f0             	mov    %r14,%rax
    28e6:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    28ea:	31 d2                	xor    %edx,%edx
    28ec:	48 8d 35 1d 4e 00 00 	lea    0x4e1d(%rip),%rsi        # 7710 <_IO_stdin_used+0x710>
    28f3:	89 c5                	mov    %eax,%ebp
    28f5:	bf 01 00 00 00       	mov    $0x1,%edi
    28fa:	41 89 c7             	mov    %eax,%r15d
    28fd:	31 c0                	xor    %eax,%eax
    28ff:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2904:	89 d9                	mov    %ebx,%ecx
    2906:	e8 95 fb ff ff       	call   24a0 <__printf_chk@plt>
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    290b:	be 08 00 00 00       	mov    $0x8,%esi
    2910:	bf 02 00 00 00       	mov    $0x2,%edi
    2915:	e8 d6 fa ff ff       	call   23f0 <calloc@plt>
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    291a:	be 80 00 00 00       	mov    $0x80,%esi
    291f:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2924:	49 89 c5             	mov    %rax,%r13
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2927:	e8 c4 fa ff ff       	call   23f0 <calloc@plt>
      if (x % 2 == 1) {
    292c:	85 db                	test   %ebx,%ebx
    292e:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2933:	49 89 c6             	mov    %rax,%r14
      if (x % 2 == 1) {
    2936:	0f 84 79 0b 00 00    	je     34b5 <main+0xe65>
        my_thread_data[0] = &thread_data[other]; 
        my_thread_data[1] = &thread_data[x]; 
        me_thread = 1;
        // printf("odd %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
        thread_data[x].protected_state = &protected_state[k];
    293c:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
        other = abs(x - 1) % total_threads;
    2941:	31 db                	xor    %ebx,%ebx
        thread_data[x].thread_index = 1;
    2943:	41 c7 84 24 cc 00 00 00 01 00 00 00 	movl   $0x1,0xcc(%r12)
        thread_data[x].protected_state = &protected_state[k];
    294f:	49 89 84 24 10 01 00 00 	mov    %rax,0x110(%r12)
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2957:	49 8d 45 08          	lea    0x8(%r13),%rax
    295b:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2960:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    2965:	4d 89 65 00          	mov    %r12,0x0(%r13)
    2969:	89 d9                	mov    %ebx,%ecx
    296b:	bf 01 00 00 00       	mov    $0x1,%edi
    2970:	45 8b 41 04          	mov    0x4(%r9),%r8d
    2974:	8b 54 24 08          	mov    0x8(%rsp),%edx
    2978:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    297d:	48 8d 35 bc 4d 00 00 	lea    0x4dbc(%rip),%rsi        # 7740 <_IO_stdin_used+0x740>
    2984:	49 89 45 08          	mov    %rax,0x8(%r13)
    2988:	31 c0                	xor    %eax,%eax
    298a:	e8 11 fb ff ff       	call   24a0 <__printf_chk@plt>
      thread_data[x].other = other;
    298f:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2994:	44 89 f9             	mov    %r15d,%ecx
    2997:	31 c0                	xor    %eax,%eax
    2999:	48 8d 35 d0 4d 00 00 	lea    0x4dd0(%rip),%rsi        # 7770 <_IO_stdin_used+0x770>
    29a0:	bf 01 00 00 00       	mov    $0x1,%edi
    29a5:	41 89 99 b8 00 00 00 	mov    %ebx,0xb8(%r9)
    29ac:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    29b0:	89 da                	mov    %ebx,%edx
    29b2:	e8 e9 fa ff ff       	call   24a0 <__printf_chk@plt>
          CPU_SET(curcpu, sendercpu);
    29b7:	89 e9                	mov    %ebp,%ecx
    29b9:	b8 01 00 00 00       	mov    $0x1,%eax
      thread_data[x].kind = KERNEL_THREAD;
    29be:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
          CPU_SET(curcpu, sendercpu);
    29c3:	48 d3 e0             	shl    %cl,%rax
    29c6:	49 09 06             	or     %rax,(%r14)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    29c9:	be 10 00 00 00       	mov    $0x10,%esi
    29ce:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].group_count = group_count;
    29d3:	48 8b 05 b6 52 00 00 	mov    0x52b6(%rip),%rax        # 7c90 <_IO_stdin_used+0xc90>
      thread_data[x].cpu_set = sendercpu;
    29da:	4d 89 b1 b0 00 00 00 	mov    %r14,0xb0(%r9)
      thread_data[x].real_thread_index = x;
    29e1:	41 89 de             	mov    %ebx,%r14d
    29e4:	41 89 59 08          	mov    %ebx,0x8(%r9)
    29e8:	41 83 f6 01          	xor    $0x1,%r14d
      thread_data[x].group_count = group_count;
    29ec:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
      thread_data[x].thread_count = 2;
    29f3:	48 8b 05 9e 52 00 00 	mov    0x529e(%rip),%rax        # 7c98 <_IO_stdin_used+0xc98>
      thread_data[x].threads = my_thread_data;
    29fa:	4d 89 69 18          	mov    %r13,0x18(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    29fe:	45 31 ed             	xor    %r13d,%r13d
      thread_data[x].kind = KERNEL_THREAD;
    2a01:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].all_threads = thread_data;
    2a08:	4d 89 61 20          	mov    %r12,0x20(%r9)
      thread_data[x].thread_count = 2;
    2a0c:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].task_count = total_barrier_count;
    2a10:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a18:	e8 d3 f9 ff ff       	call   23f0 <calloc@plt>
    2a1d:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a22:	be 10 00 00 00       	mov    $0x10,%esi
    2a27:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a2c:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a30:	e8 bb f9 ff ff       	call   23f0 <calloc@plt>
    2a35:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a3a:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2a3f:	66 0f 6f 3d 19 52 00 00 	movdqa 0x5219(%rip),%xmm7        # 7c60 <_IO_stdin_used+0xc60>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a47:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a4c:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2a50:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a58:	e8 93 f9 ff ff       	call   23f0 <calloc@plt>
    2a5d:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a62:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_timestamp_count = 0;
    2a67:	66 0f 6f 3d f1 51 00 00 	movdqa 0x51f1(%rip),%xmm7        # 7c60 <_IO_stdin_used+0xc60>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a6f:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a74:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2a7b:	41 0f 11 b9 98 00 00 00 	movups %xmm7,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a83:	e8 68 f9 ff ff       	call   23f0 <calloc@plt>
        thread_data[x].tasks = barriers;
    2a88:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a8d:	4c 89 64 24 78       	mov    %r12,0x78(%rsp)
    2a92:	44 89 74 24 10       	mov    %r14d,0x10(%rsp)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a97:	48 89 c3             	mov    %rax,%rbx
        thread_data[x].tasks = barriers;
    2a9a:	49 89 41 38          	mov    %rax,0x38(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a9e:	4c 89 cd             	mov    %r9,%rbp
          thread_data[x].tasks[y].protected = do_protected_write; 
    2aa1:	4d 63 f5             	movslq %r13d,%r14
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2aa4:	be 38 00 00 00       	mov    $0x38,%esi
    2aa9:	bf 02 00 00 00       	mov    $0x2,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2aae:	45 31 ff             	xor    %r15d,%r15d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2ab1:	4c 89 f0             	mov    %r14,%rax
    2ab4:	48 c1 e0 09          	shl    $0x9,%rax
    2ab8:	48 01 c3             	add    %rax,%rbx
    2abb:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2ac0:	48 8d 05 d9 11 00 00 	lea    0x11d9(%rip),%rax        # 3ca0 <do_protected_write>
    2ac7:	48 89 83 20 01 00 00 	mov    %rax,0x120(%rbx)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2ace:	e8 1d f9 ff ff       	call   23f0 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2ad3:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    2ad8:	48 89 83 70 01 00 00 	mov    %rax,0x170(%rbx)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2adf:	4c 89 74 24 28       	mov    %r14,0x28(%rsp)
    2ae4:	49 89 c6             	mov    %rax,%r14
    2ae7:	31 c9                	xor    %ecx,%ecx
    2ae9:	44 89 fa             	mov    %r15d,%edx
    2aec:	48 8d 35 b3 48 00 00 	lea    0x48b3(%rip),%rsi        # 73a6 <_IO_stdin_used+0x3a6>
    2af3:	31 c0                	xor    %eax,%eax
    2af5:	bf 01 00 00 00       	mov    $0x1,%edi
    2afa:	49 83 c6 38          	add    $0x38,%r14
    2afe:	e8 9d f9 ff ff       	call   24a0 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b03:	be 08 00 00 00       	mov    $0x8,%esi
    2b08:	bf 01 00 00 00       	mov    $0x1,%edi
    2b0d:	e8 de f8 ff ff       	call   23f0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b12:	be 08 00 00 00       	mov    $0x8,%esi
    2b17:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b1c:	49 89 c4             	mov    %rax,%r12
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b1f:	e8 cc f8 ff ff       	call   23f0 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2b24:	be 80 03 00 00       	mov    $0x380,%esi
    2b29:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b2e:	48 89 c5             	mov    %rax,%rbp
              struct Data *data = calloc(3, sizeof(struct Data));
    2b31:	e8 ba f8 ff ff       	call   23f0 <calloc@plt>
              mailboxes[b].kind = MAILBOX_FRIEND;
    2b36:	41 c7 46 f8 01 00 00 00 	movl   $0x1,-0x8(%r14)
    2b3e:	44 89 fa             	mov    %r15d,%edx
    2b41:	48 8d 35 48 4c 00 00 	lea    0x4c48(%rip),%rsi        # 7790 <_IO_stdin_used+0x790>
              struct Data *data = calloc(3, sizeof(struct Data));
    2b48:	48 89 c3             	mov    %rax,%rbx
    2b4b:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].kind = MAILBOX_LOWER;
    2b50:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].a = x;
    2b5a:	8b 44 24 08          	mov    0x8(%rsp),%eax
              mailboxes[b].lower = &data[0];
    2b5e:	49 89 5e c8          	mov    %rbx,-0x38(%r14)
              data[0].a = x;
    2b62:	89 83 1c 03 00 00    	mov    %eax,0x31c(%rbx)
              data[1].a = x;
    2b68:	89 83 9c 06 00 00    	mov    %eax,0x69c(%rbx)
              mailboxes[b].higher = &data[1];
    2b6e:	48 8d 83 80 03 00 00 	lea    0x380(%rbx),%rax
    2b75:	49 89 46 d0          	mov    %rax,-0x30(%r14)
    2b79:	8b 44 24 10          	mov    0x10(%rsp),%eax
              data[0].b = y;
    2b7d:	44 89 ab 20 03 00 00 	mov    %r13d,0x320(%rbx)
              data[0].c = b;
    2b84:	41 89 46 fc          	mov    %eax,-0x4(%r14)
    2b88:	89 c1                	mov    %eax,%ecx
    2b8a:	31 c0                	xor    %eax,%eax
    2b8c:	44 89 bb 24 03 00 00 	mov    %r15d,0x324(%rbx)
              data[1].kind = MAILBOX_HIGHER;
    2b93:	c7 83 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%rbx)
              data[1].b = y;
    2b9d:	44 89 ab a0 06 00 00 	mov    %r13d,0x6a0(%rbx)
              data[1].c = b;
    2ba4:	44 89 bb a4 06 00 00 	mov    %r15d,0x6a4(%rbx)
              data[0].finished_reading = 1;
    2bab:	c7 83 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rbx)
    2bb5:	e8 e6 f8 ff ff       	call   24a0 <__printf_chk@plt>
              data[0].messages_count = 0;
    2bba:	66 0f 6f 15 ae 50 00 00 	movdqa 0x50ae(%rip),%xmm2        # 7c70 <_IO_stdin_used+0xc70>
              data[0].messages = messages;
    2bc2:	4c 89 23             	mov    %r12,(%rbx)
              data[1].messages = messages2;
    2bc5:	48 89 ab 80 03 00 00 	mov    %rbp,0x380(%rbx)
              data[0].messages_count = 0;
    2bcc:	0f 29 93 80 00 00 00 	movaps %xmm2,0x80(%rbx)
              data[1].messages_count = 0;
    2bd3:	0f 29 93 00 04 00 00 	movaps %xmm2,0x400(%rbx)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2bda:	45 85 ff             	test   %r15d,%r15d
    2bdd:	75 0b                	jne    2bea <main+0x59a>
    2bdf:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    2be5:	e9 fd fe ff ff       	jmp    2ae7 <main+0x497>
          char *message = malloc(sizeof(char) * 256);
    2bea:	be 01 00 00 00       	mov    $0x1,%esi
    2bef:	bf 00 01 00 00       	mov    $0x100,%edi
    2bf4:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    2bf9:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    2bfe:	e8 ed f7 ff ff       	call   23f0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2c03:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    2c08:	48 89 c3             	mov    %rax,%rbx
          struct Message *messaged = malloc(sizeof(struct Message));
    2c0b:	e8 50 f8 ff ff       	call   2460 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2c10:	48 83 ec 08          	sub    $0x8,%rsp
    2c14:	48 89 df             	mov    %rbx,%rdi
    2c17:	45 89 e9             	mov    %r13d,%r9d
    2c1a:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2c1f:	ba 00 01 00 00       	mov    $0x100,%edx
    2c24:	48 8d 0d 8d 4b 00 00 	lea    0x4b8d(%rip),%rcx        # 77b8 <_IO_stdin_used+0x7b8>
    2c2b:	31 c0                	xor    %eax,%eax
    2c2d:	6a 00                	push   $0x0
    2c2f:	44 8b 44 24 18       	mov    0x18(%rsp),%r8d
    2c34:	be 01 00 00 00       	mov    $0x1,%esi
    2c39:	e8 42 f9 ff ff       	call   2580 <__sprintf_chk@plt>
          messaged->message = message;
    2c3e:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
          messaged->thread_index = thread_data[x].real_thread_index;
    2c43:	48 63 45 08          	movslq 0x8(%rbp),%rax
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2c47:	be 20 00 00 00       	mov    $0x20,%esi
    2c4c:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->message = message;
    2c51:	49 89 1b             	mov    %rbx,(%r11)
          thread_data[x].tasks[y].group = k;
    2c54:	48 8b 5d 38          	mov    0x38(%rbp),%rbx
          messaged->task_index = y;
    2c58:	4d 89 73 10          	mov    %r14,0x10(%r11)
          thread_data[x].tasks[y].group = k;
    2c5c:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
          messaged->thread_index = thread_data[x].real_thread_index;
    2c61:	49 89 43 08          	mov    %rax,0x8(%r11)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2c65:	41 8d 45 01          	lea    0x1(%r13),%eax
          thread_data[x].tasks[y].group = k;
    2c69:	49 01 de             	add    %rbx,%r14
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2c6c:	83 e0 01             	and    $0x1,%eax
          messaged->group = k;
    2c6f:	41 c7 43 18 00 00 00 00 	movl   $0x0,0x18(%r11)
          thread_data[x].tasks[y].group = k;
    2c77:	41 c7 86 94 01 00 00 00 00 00 00 	movl   $0x0,0x194(%r14)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2c82:	41 c7 06 41 00 00 00 	movl   $0x41,(%r14)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2c89:	41 89 86 90 01 00 00 	mov    %eax,0x190(%r14)
          thread_data[x].tasks[y].message = messaged;
    2c90:	4d 89 9e 88 01 00 00 	mov    %r11,0x188(%r14)
          thread_data[x].tasks[y].sending = 1;
    2c97:	41 c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r14)
          thread_data[x].tasks[y].snapshot_count = 99;
    2ca2:	49 c7 86 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%r14)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2cad:	e8 3e f7 ff ff       	call   23f0 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    2cb2:	49 c7 86 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%r14)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2cbd:	49 89 86 50 01 00 00 	mov    %rax,0x150(%r14)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2cc4:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    2cc9:	48 8b 00             	mov    (%rax),%rax
    2ccc:	8b 50 04             	mov    0x4(%rax),%edx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2ccf:	49 89 86 28 01 00 00 	mov    %rax,0x128(%r14)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2cd6:	41 89 96 30 01 00 00 	mov    %edx,0x130(%r14)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2cdd:	5e                   	pop    %rsi
    2cde:	5f                   	pop    %rdi
    2cdf:	48 39 e8             	cmp    %rbp,%rax
    2ce2:	0f 85 b1 0e 00 00    	jne    3b99 <main+0x1549>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2ce8:	66 0f 6f 25 90 4f 00 00 	movdqa 0x4f90(%rip),%xmm4        # 7c80 <_IO_stdin_used+0xc80>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2cf0:	45 89 6e 04          	mov    %r13d,0x4(%r14)
          thread_data[x].tasks[y].available = 1;
    2cf4:	48 8b 05 a5 4f 00 00 	mov    0x4fa5(%rip),%rax        # 7ca0 <_IO_stdin_used+0xca0>
          thread_data[x].tasks[y].arrived = 0;
    2cfb:	41 c7 86 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r14)
          thread_data[x].tasks[y].worker_count = thread_count;
    2d06:	41 c7 86 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%r14)
          thread_data[x].tasks[y].available = 1;
    2d11:	49 89 86 44 01 00 00 	mov    %rax,0x144(%r14)
          thread_data[x].tasks[y].thread_count = 2;
    2d18:	41 0f 11 a6 34 01 00 00 	movups %xmm4,0x134(%r14)
          if (y == barrier_count - 1) {
    2d20:	41 83 fd 01          	cmp    $0x1,%r13d
    2d24:	0f 84 f8 00 00 00    	je     2e22 <main+0x7d2>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2d2a:	45 85 ed             	test   %r13d,%r13d
    2d2d:	0f 84 d9 00 00 00    	je     2e0c <main+0x7bc>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    2d33:	49 89 e9             	mov    %rbp,%r9
    2d36:	48 8d 05 33 33 00 00 	lea    0x3333(%rip),%rax        # 6070 <barriered_work>
    2d3d:	4c 89 f5             	mov    %r14,%rbp
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2d40:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    2d45:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2d4c:	bf 01 00 00 00       	mov    $0x1,%edi
               thread_data[x].tasks[y].run = barriered_work; 
    2d51:	4c 8b 64 24 78       	mov    0x78(%rsp),%r12
    2d56:	45 89 fe             	mov    %r15d,%r14d
        thread_data[x].buffers_count = buffers_per_thread;
    2d59:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    2d64:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2d69:	e8 82 f6 ff ff       	call   23f0 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2d6e:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    2d73:	48 8b 74 24 70       	mov    0x70(%rsp),%rsi
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2d78:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2d7d:	66 0f 6f 74 24 50    	movdqa 0x50(%rsp),%xmm6
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2d83:	48 8d 14 fe          	lea    (%rsi,%rdi,8),%rdx
    for (int d = 0 ; d < threads_per_group ; d++) {
    2d87:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2d8b:	48 83 c7 02          	add    $0x2,%rdi
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2d8f:	49 89 41 50          	mov    %rax,0x50(%r9)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2d93:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2d9a:	48 89 10             	mov    %rdx,(%rax)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2d9d:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    2da2:	48 89 7c 24 40       	mov    %rdi,0x40(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2da7:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2daa:	0f 11 b3 18 05 00 00 	movups %xmm6,0x518(%rbx)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    2db1:	c7 83 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rbx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2dbb:	48 89 83 28 05 00 00 	mov    %rax,0x528(%rbx)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2dc2:	c7 83 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rbx)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    2dcc:	c7 83 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rbx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2dd6:	41 8b 81 3c ff ff ff 	mov    -0xc4(%r9),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2ddd:	c7 83 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rbx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2de7:	89 83 30 05 00 00    	mov    %eax,0x530(%rbx)
        thread_data[x].tasks[barrier_count].available = 1; 
    2ded:	48 8b 05 ac 4e 00 00 	mov    0x4eac(%rip),%rax        # 7ca0 <_IO_stdin_used+0xca0>
    2df4:	48 89 83 44 05 00 00 	mov    %rax,0x544(%rbx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2dfb:	85 c9                	test   %ecx,%ecx
    2dfd:	75 32                	jne    2e31 <main+0x7e1>
    2dff:	44 89 74 24 08       	mov    %r14d,0x8(%rsp)
    2e04:	48 89 f8             	mov    %rdi,%rax
    2e07:	e9 da fa ff ff       	jmp    28e6 <main+0x296>
    2e0c:	48 8d 05 fd 37 00 00 	lea    0x37fd(%rip),%rax        # 6610 <barriered_work_ingest_andwork>
            thread_data[x].tasks[y].run = barriered_work; 
    2e13:	49 89 86 18 01 00 00 	mov    %rax,0x118(%r14)
    2e1a:	45 89 fd             	mov    %r15d,%r13d
    2e1d:	e9 7f fc ff ff       	jmp    2aa1 <main+0x451>
    2e22:	48 8d 05 47 32 00 00 	lea    0x3247(%rip),%rax        # 6070 <barriered_work>
    2e29:	41 bf 02 00 00 00    	mov    $0x2,%r15d
    2e2f:	eb e2                	jmp    2e13 <main+0x7c3>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(200, sizeof(struct Data*)); 
    2e31:	bf c8 00 00 00       	mov    $0xc8,%edi
    2e36:	be 08 00 00 00       	mov    $0x8,%esi
    2e3b:	31 ed                	xor    %ebp,%ebp
    2e3d:	e8 ae f5 ff ff       	call   23f0 <calloc@plt>
    2e42:	49 89 c7             	mov    %rax,%r15
  int datas_size = 0; 
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e45:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2e4a:	48 8d 58 38          	lea    0x38(%rax),%rbx
    2e4e:	48 05 c8 01 00 00    	add    $0x1c8,%rax
    2e54:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  struct Data ** cdatas = calloc(200, sizeof(struct Data*)); 
    2e59:	48 89 df             	mov    %rbx,%rdi
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2e5c:	44 8b 47 08          	mov    0x8(%rdi),%r8d
    2e60:	45 85 c0             	test   %r8d,%r8d
    2e63:	7e 50                	jle    2eb5 <main+0x865>
    2e65:	48 8b 17             	mov    (%rdi),%rdx
    2e68:	49 63 f0             	movslq %r8d,%rsi
    2e6b:	48 63 c5             	movslq %ebp,%rax
    2e6e:	48 c1 e6 09          	shl    $0x9,%rsi
    2e72:	49 8d 0c c7          	lea    (%r15,%rax,8),%rcx
    2e76:	48 01 d6             	add    %rdx,%rsi
    2e79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    2e80:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2e87:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    2e8e:	48 83 c1 20          	add    $0x20,%rcx
    2e92:	f3 0f 7e 40 38       	movq   0x38(%rax),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    2e97:	f3 0f 7e 08          	movq   (%rax),%xmm1
    2e9b:	0f 16 40 40          	movhps 0x40(%rax),%xmm0
    2e9f:	0f 16 48 08          	movhps 0x8(%rax),%xmm1
    2ea3:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    2ea7:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2eab:	48 39 d6             	cmp    %rdx,%rsi
    2eae:	75 d0                	jne    2e80 <main+0x830>
    2eb0:	42 8d 6c 85 00       	lea    0x0(%rbp,%r8,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    2eb5:	48 81 c7 c8 00 00 00 	add    $0xc8,%rdi
    2ebc:	48 39 7c 24 10       	cmp    %rdi,0x10(%rsp)
    2ec1:	75 99                	jne    2e5c <main+0x80c>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2ec3:	48 8d 3d ec 44 00 00 	lea    0x44ec(%rip),%rdi        # 73b6 <_IO_stdin_used+0x3b6>
    2eca:	e8 51 f4 ff ff       	call   2320 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    2ecf:	48 8d 35 f5 44 00 00 	lea    0x44f5(%rip),%rsi        # 73cb <_IO_stdin_used+0x3cb>
    2ed6:	48 8d 3d f0 44 00 00 	lea    0x44f0(%rip),%rdi        # 73cd <_IO_stdin_used+0x3cd>
    2edd:	e8 fe f5 ff ff       	call   24e0 <fopen@plt>
    2ee2:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < datas_size; x++) {
    2ee5:	85 ed                	test   %ebp,%ebp
    2ee7:	0f 8e 83 00 00 00    	jle    2f70 <main+0x920>
    2eed:	48 63 ed             	movslq %ebp,%rbp
    2ef0:	4c 8d 25 16 45 00 00 	lea    0x4516(%rip),%r12        # 740d <_IO_stdin_used+0x40d>
    2ef7:	4d 8d 2c ef          	lea    (%r15,%rbp,8),%r13
    char * c = calloc(250, sizeof(char));
    2efb:	be 01 00 00 00       	mov    $0x1,%esi
    2f00:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    2f05:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    2f09:	e8 e2 f4 ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2f0e:	48 8d 0d e3 44 00 00 	lea    0x44e3(%rip),%rcx        # 73f8 <_IO_stdin_used+0x3f8>
    2f15:	be 01 00 00 00       	mov    $0x1,%esi
    2f1a:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d %d %d %d\n", cdatas[x]->kind, cdatas[x]->a, cdatas[x]->b, cdatas[x]->c);
    2f1d:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    2f21:	48 89 ef             	mov    %rbp,%rdi
    2f24:	8b 90 24 03 00 00    	mov    0x324(%rax),%edx
    2f2a:	44 8b 88 1c 03 00 00 	mov    0x31c(%rax),%r9d
    2f31:	44 8b 80 18 03 00 00 	mov    0x318(%rax),%r8d
    2f38:	52                   	push   %rdx
    2f39:	8b 80 20 03 00 00    	mov    0x320(%rax),%eax
    2f3f:	ba fa 00 00 00       	mov    $0xfa,%edx
    2f44:	50                   	push   %rax
    2f45:	31 c0                	xor    %eax,%eax
    2f47:	e8 34 f6 ff ff       	call   2580 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2f4c:	48 89 ea             	mov    %rbp,%rdx
    2f4f:	4c 89 e6             	mov    %r12,%rsi
    2f52:	bf 01 00 00 00       	mov    $0x1,%edi
    2f57:	31 c0                	xor    %eax,%eax
    2f59:	e8 42 f5 ff ff       	call   24a0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    2f5e:	4c 89 f6             	mov    %r14,%rsi
    2f61:	48 89 ef             	mov    %rbp,%rdi
    2f64:	e8 47 f4 ff ff       	call   23b0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    2f69:	58                   	pop    %rax
    2f6a:	5a                   	pop    %rdx
    2f6b:	4d 39 fd             	cmp    %r15,%r13
    2f6e:	75 8b                	jne    2efb <main+0x8ab>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    2f70:	4c 89 f7             	mov    %r14,%rdi
    2f73:	4c 8d 3d b3 44 00 00 	lea    0x44b3(%rip),%r15        # 742d <_IO_stdin_used+0x42d>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2f7a:	49 89 de             	mov    %rbx,%r14
    2f7d:	e8 ce f3 ff ff       	call   2350 <fclose@plt>
    2f82:	48 8d 3d 4d 44 00 00 	lea    0x444d(%rip),%rdi        # 73d6 <_IO_stdin_used+0x3d6>
    2f89:	e8 92 f3 ff ff       	call   2320 <puts@plt>
    2f8e:	31 d2                	xor    %edx,%edx
    2f90:	48 8d 35 57 44 00 00 	lea    0x4457(%rip),%rsi        # 73ee <_IO_stdin_used+0x3ee>
    2f97:	31 c0                	xor    %eax,%eax
    2f99:	bf 01 00 00 00       	mov    $0x1,%edi
    2f9e:	e8 fd f4 ff ff       	call   24a0 <__printf_chk@plt>

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    2fa3:	c7 44 24 40 00 00 00 00 	movl   $0x0,0x40(%rsp)
    2fab:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    2fb0:	8b 54 24 40          	mov    0x40(%rsp),%edx
    2fb4:	48 8d 35 55 44 00 00 	lea    0x4455(%rip),%rsi        # 7410 <_IO_stdin_used+0x410>
    2fbb:	31 c0                	xor    %eax,%eax
    2fbd:	45 31 ed             	xor    %r13d,%r13d
    2fc0:	bf 01 00 00 00       	mov    $0x1,%edi
    2fc5:	89 d1                	mov    %edx,%ecx
    2fc7:	e8 d4 f4 ff ff       	call   24a0 <__printf_chk@plt>
    2fcc:	44 89 ea             	mov    %r13d,%edx
    2fcf:	48 8d 35 4c 44 00 00 	lea    0x444c(%rip),%rsi        # 7422 <_IO_stdin_used+0x422>
    2fd6:	31 c0                	xor    %eax,%eax
    2fd8:	4c 89 eb             	mov    %r13,%rbx
    2fdb:	bf 01 00 00 00       	mov    $0x1,%edi
    2fe0:	48 c1 e3 09          	shl    $0x9,%rbx
    2fe4:	31 ed                	xor    %ebp,%ebp
      int x = (k * threads_per_group) + d;
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    2fe6:	45 31 e4             	xor    %r12d,%r12d
    2fe9:	e8 b2 f4 ff ff       	call   24a0 <__printf_chk@plt>
          char * mailbox_kind = calloc(100, sizeof(char));
    2fee:	be 01 00 00 00       	mov    $0x1,%esi
    2ff3:	bf 64 00 00 00       	mov    $0x64,%edi
    2ff8:	e8 f3 f3 ff ff       	call   23f0 <calloc@plt>
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    2ffd:	49 8b 36             	mov    (%r14),%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
    3000:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3003:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    300b:	48 01 e8             	add    %rbp,%rax
    300e:	8b 50 30             	mov    0x30(%rax),%edx
    3011:	83 fa 02             	cmp    $0x2,%edx
    3014:	74 50                	je     3066 <main+0xa16>
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    3016:	83 fa 01             	cmp    $0x1,%edx
    3019:	74 65                	je     3080 <main+0xa30>
    301b:	44 8b 40 34          	mov    0x34(%rax),%r8d
    301f:	44 89 e2             	mov    %r12d,%edx
    3022:	4c 89 fe             	mov    %r15,%rsi
    3025:	bf 01 00 00 00       	mov    $0x1,%edi
    302a:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    302c:	48 83 c5 38          	add    $0x38,%rbp
    3030:	e8 6b f4 ff ff       	call   24a0 <__printf_chk@plt>
    3035:	45 85 e4             	test   %r12d,%r12d
    3038:	75 07                	jne    3041 <main+0x9f1>
    303a:	44 8b 64 24 08       	mov    0x8(%rsp),%r12d
    303f:	eb ad                	jmp    2fee <main+0x99e>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3041:	49 83 c5 01          	add    $0x1,%r13
    3045:	49 83 fd 03          	cmp    $0x3,%r13
    3049:	75 81                	jne    2fcc <main+0x97c>
    for (int d = 0 ; d < threads_per_group ; d++) {
    304b:	44 8b 6c 24 40       	mov    0x40(%rsp),%r13d
    3050:	49 81 c6 c8 00 00 00 	add    $0xc8,%r14
    3057:	45 85 ed             	test   %r13d,%r13d
    305a:	75 3e                	jne    309a <main+0xa4a>
    305c:	44 89 64 24 40       	mov    %r12d,0x40(%rsp)
    3061:	e9 4a ff ff ff       	jmp    2fb0 <main+0x960>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3066:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    3070:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    3073:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    307b:	48 01 e8             	add    %rbp,%rax
    307e:	eb 9b                	jmp    301b <main+0x9cb>
    3080:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3086:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    308d:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    3095:	48 01 e8             	add    %rbp,%rax
    3098:	eb 81                	jmp    301b <main+0x9cb>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    309a:	ba 03 00 00 00       	mov    $0x3,%edx
    309f:	48 8d 35 a2 43 00 00 	lea    0x43a2(%rip),%rsi        # 7448 <_IO_stdin_used+0x448>
    30a6:	bf 01 00 00 00       	mov    $0x1,%edi
    30ab:	31 c0                	xor    %eax,%eax
    30ad:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    30b2:	e8 e9 f3 ff ff       	call   24a0 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    30b7:	be 08 00 00 00       	mov    $0x8,%esi
    30bc:	bf 02 00 00 00       	mov    $0x2,%edi
    30c1:	e8 2a f3 ff ff       	call   23f0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    30c6:	4c 8b 7c 24 38       	mov    0x38(%rsp),%r15
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    30cb:	be 38 00 00 00       	mov    $0x38,%esi
    30d0:	bf 06 00 00 00       	mov    $0x6,%edi
    my_thread_data[0] = &thread_data[x]; 
    30d5:	4d 8d a7 58 02 00 00 	lea    0x258(%r15),%r12
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    30dc:	4c 89 78 08          	mov    %r15,0x8(%rax)
    thread_data[x].threads = my_thread_data;
    30e0:	49 89 87 70 02 00 00 	mov    %rax,0x270(%r15)
    my_thread_data[0] = &thread_data[x]; 
    30e7:	4c 89 20             	mov    %r12,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    30ea:	49 8b 47 38          	mov    0x38(%r15),%rax
    thread_data[x].thread_count = 2;
    30ee:	41 c7 87 80 02 00 00 02 00 00 00 	movl   $0x2,0x280(%r15)
    thread_data[x].thread_index = 0;
    30f9:	41 c7 87 5c 02 00 00 00 00 00 00 	movl   $0x0,0x25c(%r15)
    thread_data[x].task_count = total_barrier_count;
    3104:	41 c7 87 98 02 00 00 03 00 00 00 	movl   $0x3,0x298(%r15)
    thread_data[n].tasks[0].scheduled = 1;
    310f:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3119:	49 8b 87 00 01 00 00 	mov    0x100(%r15),%rax
    3120:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    312a:	e8 c1 f2 ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    312f:	be 38 00 00 00       	mov    $0x38,%esi
    3134:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3139:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    313c:	e8 af f2 ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3141:	be 38 00 00 00       	mov    $0x38,%esi
    3146:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    314b:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    314e:	e8 9d f2 ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3153:	be 38 00 00 00       	mov    $0x38,%esi
    3158:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    315d:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3162:	e8 89 f2 ff ff       	call   23f0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3167:	be 08 00 00 00       	mov    $0x8,%esi
    316c:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3171:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3176:	e8 75 f2 ff ff       	call   23f0 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    317b:	be 08 00 00 00       	mov    $0x8,%esi
    3180:	bf 06 00 00 00       	mov    $0x6,%edi
  thread_data[timer_threadi].type = TIMER;
    3185:	41 c7 87 9c 01 00 00 00 00 00 00 	movl   $0x0,0x19c(%r15)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3190:	48 89 c5             	mov    %rax,%rbp
  thread_data[timer_threadi].task_count = total_barrier_count;
    3193:	48 8b 05 0e 4b 00 00 	mov    0x4b0e(%rip),%rax        # 7ca8 <_IO_stdin_used+0xca8>
    319a:	49 89 87 d0 01 00 00 	mov    %rax,0x1d0(%r15)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    31a1:	e8 4a f2 ff ff       	call   23f0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    31a6:	48 8b 7c 24 48       	mov    0x48(%rsp),%rdi
    31ab:	49 8d 8f 90 01 00 00 	lea    0x190(%r15),%rcx
    31b2:	48 8d 35 9e 42 00 00 	lea    0x429e(%rip),%rsi        # 7457 <_IO_stdin_used+0x457>
    31b9:	4c 89 38             	mov    %r15,(%rax)
    31bc:	48 89 78 08          	mov    %rdi,0x8(%rax)
    31c0:	4c 89 ff             	mov    %r15,%rdi
    31c3:	4d 8d bf 20 03 00 00 	lea    0x320(%r15),%r15
    31ca:	48 8d 97 e8 03 00 00 	lea    0x3e8(%rdi),%rdx
    31d1:	48 89 48 10          	mov    %rcx,0x10(%rax)
    31d5:	48 89 50 28          	mov    %rdx,0x28(%rax)
  }
  thread_data[timer_threadi].threads = my_thread_data;
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    31d9:	48 8b 15 b8 4a 00 00 	mov    0x4ab8(%rip),%rdx        # 7c98 <_IO_stdin_used+0xc98>
    my_thread_data[n] = &thread_data[n]; 
    31e0:	4c 89 60 18          	mov    %r12,0x18(%rax)
    31e4:	4c 89 78 20          	mov    %r15,0x20(%rax)
  thread_data[timer_threadi].threads = my_thread_data;
    31e8:	48 89 87 a8 01 00 00 	mov    %rax,0x1a8(%rdi)
    31ef:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    31f1:	48 89 97 b8 01 00 00 	mov    %rdx,0x1b8(%rdi)
    31f8:	ba 02 00 00 00       	mov    $0x2,%edx
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    31fd:	c7 87 c0 01 00 00 02 00 00 00 	movl   $0x2,0x1c0(%rdi)
  thread_data[timer_threadi].thread_index = 0;
    3207:	c7 87 94 01 00 00 00 00 00 00 	movl   $0x0,0x194(%rdi)
    3211:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
    3216:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    321b:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    3220:	e8 7b f2 ff ff       	call   24a0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3225:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    322a:	49 8d 76 70          	lea    0x70(%r14),%rsi
    322e:	48 8d 7d 10          	lea    0x10(%rbp),%rdi
    3232:	48 8d 15 27 0c 00 00 	lea    0xc27(%rip),%rdx        # 3e60 <timer_thread>
    3239:	e8 82 f2 ff ff       	call   24c0 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    323e:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    3243:	31 c9                	xor    %ecx,%ecx
    3245:	31 d2                	xor    %edx,%edx
    3247:	4c 8d 0d 9a 45 00 00 	lea    0x459a(%rip),%r9        # 77e8 <_IO_stdin_used+0x7e8>
    324e:	bf 01 00 00 00       	mov    $0x1,%edi
    3253:	31 c0                	xor    %eax,%eax
    3255:	41 c7 46 0c 01 00 00 00 	movl   $0x1,0xc(%r14)
    325d:	4c 89 ce             	mov    %r9,%rsi
      thread_data[x].running = 1;
    3260:	41 c7 46 44 01 00 00 00 	movl   $0x1,0x44(%r14)
    3268:	e8 33 f2 ff ff       	call   24a0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    326d:	4c 89 f1             	mov    %r14,%rcx
    3270:	4c 89 74 24 38       	mov    %r14,0x38(%rsp)
    3275:	4c 89 ee             	mov    %r13,%rsi
    3278:	4c 8d 35 41 29 00 00 	lea    0x2941(%rip),%r14        # 5bc0 <barriered_thread>
    327f:	48 89 ef             	mov    %rbp,%rdi
    3282:	4c 89 f2             	mov    %r14,%rdx
    3285:	e8 36 f2 ff ff       	call   24c0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    328a:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    328f:	be 08 00 00 00       	mov    $0x8,%esi
    3294:	48 8b 97 b0 00 00 00 	mov    0xb0(%rdi),%rdx
    329b:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    329f:	e8 6c f0 ff ff       	call   2310 <pthread_setaffinity_np@plt>
      thread_data[x].type = WORKER;
    32a4:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    32a9:	31 c9                	xor    %ecx,%ecx
    32ab:	31 c0                	xor    %eax,%eax
    32ad:	4c 8d 0d 34 45 00 00 	lea    0x4534(%rip),%r9        # 77e8 <_IO_stdin_used+0x7e8>
    32b4:	ba 01 00 00 00       	mov    $0x1,%edx
    32b9:	c7 87 d4 00 00 00 01 00 00 00 	movl   $0x1,0xd4(%rdi)
    32c3:	4c 89 ce             	mov    %r9,%rsi
      thread_data[x].running = 1;
    32c6:	c7 87 0c 01 00 00 01 00 00 00 	movl   $0x1,0x10c(%rdi)
    32d0:	bf 01 00 00 00       	mov    $0x1,%edi
    32d5:	e8 c6 f1 ff ff       	call   24a0 <__printf_chk@plt>
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    32da:	49 8d 75 38          	lea    0x38(%r13),%rsi
    32de:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
    32e2:	4c 89 f2             	mov    %r14,%rdx
    32e5:	4c 8b 6c 24 48       	mov    0x48(%rsp),%r13
    32ea:	4c 89 e9             	mov    %r13,%rcx
    32ed:	e8 ce f1 ff ff       	call   24c0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    32f2:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    32f7:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
    32fb:	be 08 00 00 00       	mov    $0x8,%esi
    3300:	49 8b 96 78 01 00 00 	mov    0x178(%r14),%rdx
    3307:	e8 04 f0 ff ff       	call   2310 <pthread_setaffinity_np@plt>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    330c:	48 8b 3d 9d 49 00 00 	mov    0x499d(%rip),%rdi        # 7cb0 <_IO_stdin_used+0xcb0>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3313:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    3318:	41 c7 86 64 02 00 00 02 00 00 00 	movl   $0x2,0x264(%r14)
    thread_data[x].task_count = 0;
    3323:	49 89 be 98 02 00 00 	mov    %rdi,0x298(%r14)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    332a:	bf 01 00 00 00       	mov    $0x1,%edi
    332f:	e8 bc f0 ff ff       	call   23f0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3334:	31 ff                	xor    %edi,%edi
    3336:	be 00 08 00 00       	mov    $0x800,%esi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    333b:	49 89 86 b0 02 00 00 	mov    %rax,0x2b0(%r14)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3342:	e8 c9 f1 ff ff       	call   2510 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3347:	be 08 00 00 00       	mov    $0x8,%esi
    334c:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3351:	41 89 86 b8 02 00 00 	mov    %eax,0x2b8(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3358:	e8 93 f0 ff ff       	call   23f0 <calloc@plt>
    335d:	ba 03 00 00 00       	mov    $0x3,%edx
    3362:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3367:	41 c7 86 80 02 00 00 02 00 00 00 	movl   $0x2,0x280(%r14)
      my_thread_data[n] = &thread_data[n]; 
    3372:	4c 89 30             	mov    %r14,(%rax)
    3375:	48 8d 35 f9 40 00 00 	lea    0x40f9(%rip),%rsi        # 7475 <_IO_stdin_used+0x475>
    337c:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[x].threads = my_thread_data;
    3380:	49 89 86 70 02 00 00 	mov    %rax,0x270(%r14)
    3387:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3389:	41 c7 86 5c 02 00 00 03 00 00 00 	movl   $0x3,0x25c(%r14)
    3394:	4d 89 fe             	mov    %r15,%r14
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3397:	41 bf 04 00 00 00    	mov    $0x4,%r15d
    339d:	e8 fe f0 ff ff       	call   24a0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    33a2:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    33a7:	48 8d 7d 18          	lea    0x18(%rbp),%rdi
    33ab:	4c 89 e1             	mov    %r12,%rcx
    33ae:	48 8d 15 1b 20 00 00 	lea    0x201b(%rip),%rdx        # 53d0 <io_thread>
    33b5:	4c 8d 65 20          	lea    0x20(%rbp),%r12
    33b9:	48 81 c6 a8 00 00 00 	add    $0xa8,%rsi
    33c0:	e8 fb f0 ff ff       	call   24c0 <pthread_create@plt>
    33c5:	ba 04 00 00 00       	mov    $0x4,%edx
    33ca:	48 8d 35 bb 40 00 00 	lea    0x40bb(%rip),%rsi        # 748c <_IO_stdin_used+0x48c>
    33d1:	31 c0                	xor    %eax,%eax
    33d3:	bf 01 00 00 00       	mov    $0x1,%edi
    33d8:	e8 c3 f0 ff ff       	call   24a0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    33dd:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    33e2:	48 89 e8             	mov    %rbp,%rax
    33e5:	48 89 dd             	mov    %rbx,%rbp
    33e8:	48 89 c3             	mov    %rax,%rbx
    33eb:	49 81 c5 e0 00 00 00 	add    $0xe0,%r13
    33f2:	44 89 fa             	mov    %r15d,%edx
    33f5:	48 8d 35 a6 40 00 00 	lea    0x40a6(%rip),%rsi        # 74a2 <_IO_stdin_used+0x4a2>
    33fc:	bf 01 00 00 00       	mov    $0x1,%edi
    3401:	31 c0                	xor    %eax,%eax
    3403:	e8 98 f0 ff ff       	call   24a0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3408:	be 08 00 00 00       	mov    $0x8,%esi
    340d:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3412:	48 8b 05 97 48 00 00 	mov    0x4897(%rip),%rax        # 7cb0 <_IO_stdin_used+0xcb0>
    thread_data[x].type = EXTERNAL;
    3419:	41 c7 46 0c 03 00 00 00 	movl   $0x3,0xc(%r14)
    thread_data[x].task_count = 0;
    3421:	49 89 46 40          	mov    %rax,0x40(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3425:	e8 c6 ef ff ff       	call   23f0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    342a:	48 8b 7c 24 68       	mov    0x68(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    342f:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3434:	41 c7 86 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    343f:	49 89 46 50          	mov    %rax,0x50(%r14)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3443:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3446:	bf 02 00 00 00       	mov    $0x2,%edi
    344b:	e8 a0 ef ff ff       	call   23f0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3450:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3455:	4c 89 f1             	mov    %r14,%rcx
    3458:	4c 89 e7             	mov    %r12,%rdi
    thread_data[x].threads = my_thread_data;
    345b:	49 89 46 18          	mov    %rax,0x18(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    345f:	48 8d 15 ea 08 00 00 	lea    0x8ea(%rip),%rdx        # 3d50 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3466:	49 83 c4 08          	add    $0x8,%r12
    346a:	49 81 c6 c8 00 00 00 	add    $0xc8,%r14
      my_thread_data[n] = &thread_data[n]; 
    3471:	48 89 30             	mov    %rsi,(%rax)
    3474:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    thread_data[x].thread_index = x;
    3479:	45 89 be 3c ff ff ff 	mov    %r15d,-0xc4(%r14)
      my_thread_data[n] = &thread_data[n]; 
    3480:	48 89 70 08          	mov    %rsi,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3484:	48 8b 05 0d 48 00 00 	mov    0x480d(%rip),%rax        # 7c98 <_IO_stdin_used+0xc98>
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    348b:	4c 89 ee             	mov    %r13,%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    348e:	49 83 c5 38          	add    $0x38,%r13
    thread_data[x].thread_count = thread_count;
    3492:	49 89 86 60 ff ff ff 	mov    %rax,-0xa0(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3499:	e8 22 f0 ff ff       	call   24c0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    349e:	48 83 44 24 68 10    	addq   $0x10,0x68(%rsp)
    34a4:	41 83 ff 04          	cmp    $0x4,%r15d
    34a8:	75 2d                	jne    34d7 <main+0xe87>
    34aa:	41 bf 05 00 00 00    	mov    $0x5,%r15d
    34b0:	e9 3d ff ff ff       	jmp    33f2 <main+0xda2>
        thread_data[x].protected_state = &protected_state[k];
    34b5:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    34ba:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
        other = (x + 1) % total_threads;
    34bf:	bb 01 00 00 00       	mov    $0x1,%ebx
        thread_data[x].thread_index = 0;
    34c4:	41 c7 44 24 04 00 00 00 00 	movl   $0x0,0x4(%r12)
        thread_data[x].protected_state = &protected_state[k];
    34cd:	49 89 44 24 48       	mov    %rax,0x48(%r12)
    34d2:	e9 89 f4 ff ff       	jmp    2960 <main+0x310>
    34d7:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    34dc:	48 87 eb             	xchg   %rbp,%rbx
    34df:	4c 8d 25 d9 3f 00 00 	lea    0x3fd9(%rip),%r12        # 74bf <_IO_stdin_used+0x4bf>
    34e6:	4c 8d 70 04          	lea    0x4(%rax),%r14
    34ea:	4c 8d a8 b4 04 00 00 	lea    0x4b4(%rax),%r13
    34f1:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    34f5:	41 8b 16             	mov    (%r14),%edx
    34f8:	4c 89 e6             	mov    %r12,%rsi
    34fb:	bf 01 00 00 00       	mov    $0x1,%edi
    3500:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3502:	49 81 c6 c8 00 00 00 	add    $0xc8,%r14
    3509:	e8 92 ef ff ff       	call   24a0 <__printf_chk@plt>
    350e:	4d 39 ee             	cmp    %r13,%r14
    3511:	75 de                	jne    34f1 <main+0xea1>
    3513:	48 8d 3d b8 3f 00 00 	lea    0x3fb8(%rip),%rdi        # 74d2 <_IO_stdin_used+0x4d2>
    351a:	45 31 f6             	xor    %r14d,%r14d
    351d:	4c 8d ac 24 80 00 00 00 	lea    0x80(%rsp),%r13
    3525:	e8 f6 ed ff ff       	call   2320 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    352a:	4c 8d 25 bf 3f 00 00 	lea    0x3fbf(%rip),%r12        # 74f0 <_IO_stdin_used+0x4f0>
    void * result; 
    pthread_join(thread[x], &result);
    3531:	4a 8b 7c f5 00       	mov    0x0(%rbp,%r14,8),%rdi
    3536:	4c 89 ee             	mov    %r13,%rsi
    3539:	e8 12 f0 ff ff       	call   2550 <pthread_join@plt>
    353e:	44 89 f2             	mov    %r14d,%edx
    3541:	4c 89 e6             	mov    %r12,%rsi
    3544:	bf 01 00 00 00       	mov    $0x1,%edi
    3549:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    354b:	49 83 c6 01          	add    $0x1,%r14
    354f:	e8 4c ef ff ff       	call   24a0 <__printf_chk@plt>
    3554:	49 83 fe 06          	cmp    $0x6,%r14
    3558:	75 d7                	jne    3531 <main+0xee1>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(200, sizeof(struct Data*)); 
    355a:	bf c8 00 00 00       	mov    $0xc8,%edi
    355f:	be 08 00 00 00       	mov    $0x8,%esi
    3564:	31 ed                	xor    %ebp,%ebp
    3566:	e8 85 ee ff ff       	call   23f0 <calloc@plt>
    356b:	48 89 df             	mov    %rbx,%rdi
    356e:	49 89 c7             	mov    %rax,%r15
  int datas2_size = 0; 
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3571:	44 8b 47 08          	mov    0x8(%rdi),%r8d
    3575:	45 85 c0             	test   %r8d,%r8d
    3578:	7e 4b                	jle    35c5 <main+0xf75>
    357a:	48 8b 17             	mov    (%rdi),%rdx
    357d:	49 63 f0             	movslq %r8d,%rsi
    3580:	48 63 c5             	movslq %ebp,%rax
    3583:	48 c1 e6 09          	shl    $0x9,%rsi
    3587:	49 8d 0c c7          	lea    (%r15,%rax,8),%rcx
    358b:	48 01 d6             	add    %rdx,%rsi
    358e:	66 90                	xchg   %ax,%ax
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3590:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3597:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    359e:	48 83 c1 20          	add    $0x20,%rcx
    35a2:	f3 0f 7e 40 38       	movq   0x38(%rax),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    35a7:	f3 0f 7e 08          	movq   (%rax),%xmm1
    35ab:	0f 16 40 40          	movhps 0x40(%rax),%xmm0
    35af:	0f 16 48 08          	movhps 0x8(%rax),%xmm1
    35b3:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    35b7:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    35bb:	48 39 d6             	cmp    %rdx,%rsi
    35be:	75 d0                	jne    3590 <main+0xf40>
    35c0:	42 8d 6c 85 00       	lea    0x0(%rbp,%r8,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    35c5:	48 81 c7 c8 00 00 00 	add    $0xc8,%rdi
    35cc:	48 39 7c 24 10       	cmp    %rdi,0x10(%rsp)
    35d1:	75 9e                	jne    3571 <main+0xf21>
    35d3:	48 8d 3d 2a 3f 00 00 	lea    0x3f2a(%rip),%rdi        # 7504 <_IO_stdin_used+0x504>
    35da:	e8 41 ed ff ff       	call   2320 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    35df:	48 8d 35 e5 3d 00 00 	lea    0x3de5(%rip),%rsi        # 73cb <_IO_stdin_used+0x3cb>
    35e6:	48 8d 3d 2f 3f 00 00 	lea    0x3f2f(%rip),%rdi        # 751c <_IO_stdin_used+0x51c>
    35ed:	e8 ee ee ff ff       	call   24e0 <fopen@plt>
    35f2:	49 89 c5             	mov    %rax,%r13
  for (int x = 0 ; x < datas2_size; x++) {
    35f5:	85 ed                	test   %ebp,%ebp
    35f7:	0f 8e 84 00 00 00    	jle    3681 <main+0x1031>
    35fd:	48 63 ed             	movslq %ebp,%rbp
    3600:	4c 8d 25 06 3e 00 00 	lea    0x3e06(%rip),%r12        # 740d <_IO_stdin_used+0x40d>
    3607:	4d 8d 34 ef          	lea    (%r15,%rbp,8),%r14
    char * c = calloc(250, sizeof(char));
    360b:	be 01 00 00 00       	mov    $0x1,%esi
    3610:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3615:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    3619:	e8 d2 ed ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    361e:	48 8d 0d 00 3f 00 00 	lea    0x3f00(%rip),%rcx        # 7525 <_IO_stdin_used+0x525>
    3625:	be 01 00 00 00       	mov    $0x1,%esi
    362a:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox2 %d %d %d %d\n", datas[x]->kind, datas[x]->a, datas[x]->b, datas[x]->c);
    362d:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3631:	48 89 ef             	mov    %rbp,%rdi
    3634:	8b 90 24 03 00 00    	mov    0x324(%rax),%edx
    363a:	44 8b 88 1c 03 00 00 	mov    0x31c(%rax),%r9d
    3641:	44 8b 80 18 03 00 00 	mov    0x318(%rax),%r8d
    3648:	52                   	push   %rdx
    3649:	8b 80 20 03 00 00    	mov    0x320(%rax),%eax
    364f:	ba fa 00 00 00       	mov    $0xfa,%edx
    3654:	50                   	push   %rax
    3655:	31 c0                	xor    %eax,%eax
    3657:	e8 24 ef ff ff       	call   2580 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    365c:	48 89 ea             	mov    %rbp,%rdx
    365f:	4c 89 e6             	mov    %r12,%rsi
    3662:	bf 01 00 00 00       	mov    $0x1,%edi
    3667:	31 c0                	xor    %eax,%eax
    3669:	e8 32 ee ff ff       	call   24a0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    366e:	48 89 ef             	mov    %rbp,%rdi
    3671:	4c 89 ee             	mov    %r13,%rsi
    3674:	e8 37 ed ff ff       	call   23b0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3679:	41 5b                	pop    %r11
    367b:	5d                   	pop    %rbp
    367c:	4d 39 f7             	cmp    %r14,%r15
    367f:	75 8a                	jne    360b <main+0xfbb>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3681:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  fclose(m2);
    368b:	4c 89 ef             	mov    %r13,%rdi
    368e:	45 31 f6             	xor    %r14d,%r14d
    3691:	45 31 ed             	xor    %r13d,%r13d
    3694:	e8 b7 ec ff ff       	call   2350 <fclose@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3699:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    369e:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  fclose(m2);
    36a6:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
    36af:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    36b4:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    36bd:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    36c6:	bf 0a 00 00 00       	mov    $0xa,%edi
    36cb:	44 8b 64 24 10       	mov    0x10(%rsp),%r12d
    36d0:	e8 2b ec ff ff       	call   2300 <putchar@plt>
    36d5:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    36da:	bf 01 00 00 00       	mov    $0x1,%edi
    36df:	48 8d 35 55 3e 00 00 	lea    0x3e55(%rip),%rsi        # 753b <_IO_stdin_used+0x53b>
    36e6:	41 83 f4 01          	xor    $0x1,%r12d
    36ea:	48 8b 10             	mov    (%rax),%rdx
    36ed:	31 c0                	xor    %eax,%eax
    36ef:	e8 ac ed ff ff       	call   24a0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    36f4:	8b 53 08             	mov    0x8(%rbx),%edx
    36f7:	85 d2                	test   %edx,%edx
    36f9:	0f 8e 93 04 00 00    	jle    3b92 <main+0x1542>
    36ff:	48 63 ca             	movslq %edx,%rcx
    3702:	48 8b 03             	mov    (%rbx),%rax
      long v = 0;
    3705:	31 d2                	xor    %edx,%edx
    3707:	48 c1 e1 09          	shl    $0x9,%rcx
    370b:	48 01 c1             	add    %rax,%rcx
    370e:	66 90                	xchg   %ax,%ax
        v += thread_data[me].tasks[n].v;
    3710:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3717:	48 05 00 02 00 00    	add    $0x200,%rax
    371d:	48 39 c8             	cmp    %rcx,%rax
    3720:	75 ee                	jne    3710 <main+0x10c0>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3722:	4c 89 e0             	mov    %r12,%rax
    3725:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    372a:	48 f7 d8             	neg    %rax
    372d:	25 c8 00 00 00       	and    $0xc8,%eax
    3732:	48 01 f8             	add    %rdi,%rax
    3735:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3739:	85 c9                	test   %ecx,%ecx
    373b:	7e 25                	jle    3762 <main+0x1112>
    373d:	48 8b 40 38          	mov    0x38(%rax),%rax
    3741:	48 c1 e1 09          	shl    $0x9,%rcx
    3745:	48 01 c1             	add    %rax,%rcx
    3748:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3750:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3757:	48 05 00 02 00 00    	add    $0x200,%rax
    375d:	48 39 c1             	cmp    %rax,%rcx
    3760:	75 ee                	jne    3750 <main+0x1100>
    3762:	48 8d 35 e7 3d 00 00 	lea    0x3de7(%rip),%rsi        # 7550 <_IO_stdin_used+0x550>
    3769:	bf 01 00 00 00       	mov    $0x1,%edi
    376e:	31 c0                	xor    %eax,%eax
    3770:	e8 2b ed ff ff       	call   24a0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3775:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    377a:	bf 01 00 00 00       	mov    $0x1,%edi
    377f:	48 8d 35 92 40 00 00 	lea    0x4092(%rip),%rsi        # 7818 <_IO_stdin_used+0x818>
    3786:	48 8b 08             	mov    (%rax),%rcx
    3789:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3793:	48 f7 e9             	imul   %rcx
    3796:	48 c1 f9 3f          	sar    $0x3f,%rcx
    379a:	31 c0                	xor    %eax,%eax
    379c:	48 d1 fa             	sar    %rdx
    379f:	48 29 ca             	sub    %rcx,%rdx
    37a2:	e8 f9 ec ff ff       	call   24a0 <__printf_chk@plt>
    37a7:	bf 0a 00 00 00       	mov    $0xa,%edi
    37ac:	e8 4f eb ff ff       	call   2300 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    37b1:	44 8b 53 08          	mov    0x8(%rbx),%r10d
    37b5:	45 85 d2             	test   %r10d,%r10d
    37b8:	0f 8e 05 01 00 00    	jle    38c3 <main+0x1273>
        total += thread_data[x].tasks[n].n;
    37be:	45 31 ff             	xor    %r15d,%r15d
    37c1:	48 8b 13             	mov    (%rbx),%rdx
    37c4:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    37c9:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    37ce:	4c 8b 44 24 28       	mov    0x28(%rsp),%r8
    37d3:	4c 89 f9             	mov    %r15,%rcx
    37d6:	4d 89 ef             	mov    %r13,%r15
    37d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    37e0:	49 89 cc             	mov    %rcx,%r12
        sends += thread_data[x].tasks[n].sends;
    37e3:	45 31 ed             	xor    %r13d,%r13d
    37e6:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
        total += thread_data[x].tasks[n].n;
    37ea:	49 c1 e4 09          	shl    $0x9,%r12
    37ee:	48 89 4c 24 30       	mov    %rcx,0x30(%rsp)
    37f3:	4c 89 e8             	mov    %r13,%rax
    37f6:	4d 89 f5             	mov    %r14,%r13
    37f9:	4c 01 e2             	add    %r12,%rdx
    37fc:	4d 89 fe             	mov    %r15,%r14
    37ff:	49 89 c7             	mov    %rax,%r15
    3802:	4c 03 92 08 01 00 00 	add    0x108(%rdx),%r10
        ingests += thread_data[x].tasks[n].ingest_count;
    3809:	48 03 ba 68 01 00 00 	add    0x168(%rdx),%rdi
        sends += thread_data[x].tasks[n].sends;
    3810:	4c 03 82 78 01 00 00 	add    0x178(%rdx),%r8
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3817:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    381c:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
    3821:	4c 89 44 24 28       	mov    %r8,0x28(%rsp)
    3826:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    382a:	8b 54 24 10          	mov    0x10(%rsp),%edx
    382e:	45 89 f8             	mov    %r15d,%r8d
    3831:	bf 01 00 00 00       	mov    $0x1,%edi
    3836:	48 8d 35 20 3d 00 00 	lea    0x3d20(%rip),%rsi        # 755d <_IO_stdin_used+0x55d>
    383d:	31 c0                	xor    %eax,%eax
    383f:	e8 5c ec ff ff       	call   24a0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3844:	48 8b 13             	mov    (%rbx),%rdx
    3847:	4c 89 f8             	mov    %r15,%rax
    384a:	48 f7 d8             	neg    %rax
    384d:	83 e0 38             	and    $0x38,%eax
    3850:	4a 03 84 22 70 01 00 00 	add    0x170(%rdx,%r12,1),%rax
    3858:	48 8b 08             	mov    (%rax),%rcx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    385b:	48 8b 40 08          	mov    0x8(%rax),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    385f:	4c 8b 89 08 03 00 00 	mov    0x308(%rcx),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3866:	4c 8b 91 10 03 00 00 	mov    0x310(%rcx),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    386d:	4d 01 e9             	add    %r13,%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3870:	4d 01 f2             	add    %r14,%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3873:	4c 03 88 08 03 00 00 	add    0x308(%rax),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    387a:	4c 03 90 10 03 00 00 	add    0x310(%rax),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3881:	4d 89 cd             	mov    %r9,%r13
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3884:	4d 89 d6             	mov    %r10,%r14
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3887:	4d 85 ff             	test   %r15,%r15
    388a:	75 08                	jne    3894 <main+0x1244>
    388c:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    3892:	eb 92                	jmp    3826 <main+0x11d6>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3894:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    3899:	4d 89 f7             	mov    %r14,%r15
    389c:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    38a1:	4d 89 ce             	mov    %r9,%r14
    38a4:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    38a9:	4c 8b 44 24 28       	mov    0x28(%rsp),%r8
    38ae:	48 83 c1 01          	add    $0x1,%rcx
    38b2:	39 4b 08             	cmp    %ecx,0x8(%rbx)
    38b5:	0f 8f 25 ff ff ff    	jg     37e0 <main+0x1190>
    38bb:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
    38c0:	4d 89 fd             	mov    %r15,%r13
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    38c3:	45 31 ff             	xor    %r15d,%r15d
    38c6:	48 83 7b 68 00       	cmpq   $0x0,0x68(%rbx)
    38cb:	4c 8d 25 66 3f 00 00 	lea    0x3f66(%rip),%r12        # 7838 <_IO_stdin_used+0x838>
    38d2:	7e 56                	jle    392a <main+0x12da>
    38d4:	0f 1f 40 00          	nopl   0x0(%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    38d8:	48 8b 43 58          	mov    0x58(%rbx),%rax
    38dc:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    38e0:	48 83 ec 08          	sub    $0x8,%rsp
    38e4:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    38e9:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    38ed:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    38f1:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    38f5:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    38f9:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    38fc:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3900:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3903:	48 f7 e5             	mul    %rbp
    3906:	8b 49 20             	mov    0x20(%rcx),%ecx
    3909:	56                   	push   %rsi
    390a:	31 c0                	xor    %eax,%eax
    390c:	4c 89 e6             	mov    %r12,%rsi
    390f:	48 c1 ea 12          	shr    $0x12,%rdx
    3913:	49 89 d1             	mov    %rdx,%r9
    3916:	ba 02 00 00 00       	mov    $0x2,%edx
    391b:	e8 80 eb ff ff       	call   24a0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3920:	41 58                	pop    %r8
    3922:	41 59                	pop    %r9
    3924:	4c 39 7b 68          	cmp    %r15,0x68(%rbx)
    3928:	7f ae                	jg     38d8 <main+0x1288>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    392a:	8b 8b 84 00 00 00    	mov    0x84(%rbx),%ecx
    3930:	85 c9                	test   %ecx,%ecx
    3932:	0f 8e 06 01 00 00    	jle    3a3e <main+0x13ee>
    3938:	4c 89 74 24 50       	mov    %r14,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    393d:	4c 8b 4b 18          	mov    0x18(%rbx),%r9
    3941:	45 31 e4             	xor    %r12d,%r12d
    3944:	4c 89 6c 24 68       	mov    %r13,0x68(%rsp)
    3949:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3950:	4b 8b 04 e1          	mov    (%r9,%r12,8),%rax
    3954:	45 89 e5             	mov    %r12d,%r13d
    3957:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    395f:	8b 30                	mov    (%rax),%esi
    3961:	85 f6                	test   %esi,%esi
    3963:	0f 8e be 00 00 00    	jle    3a27 <main+0x13d7>
    3969:	4c 89 64 24 18       	mov    %r12,0x18(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    396e:	31 d2                	xor    %edx,%edx
    3970:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3974:	48 89 d7             	mov    %rdx,%rdi
    3977:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3980:	49 89 fc             	mov    %rdi,%r12
    3983:	45 31 ff             	xor    %r15d,%r15d
    3986:	49 c1 e4 08          	shl    $0x8,%r12
    398a:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    398e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    3994:	85 d2                	test   %edx,%edx
    3996:	7e 78                	jle    3a10 <main+0x13c0>
    3998:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    399d:	0f 1f 00             	nopl   (%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    39a0:	4c 89 f9             	mov    %r15,%rcx
    39a3:	48 83 ec 08          	sub    $0x8,%rsp
    39a7:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    39ac:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    39b0:	48 c1 e1 05          	shl    $0x5,%rcx
    39b4:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    39bb:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    39bf:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    39c3:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    39c6:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    39ca:	4c 2b 01             	sub    (%rcx),%r8
    39cd:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    39ce:	48 f7 e5             	mul    %rbp
    39d1:	44 89 e9             	mov    %r13d,%ecx
    39d4:	48 8d 35 ad 3e 00 00 	lea    0x3ead(%rip),%rsi        # 7888 <_IO_stdin_used+0x888>
    39db:	31 c0                	xor    %eax,%eax
    39dd:	48 c1 ea 12          	shr    $0x12,%rdx
    39e1:	49 89 d1             	mov    %rdx,%r9
    39e4:	ba 02 00 00 00       	mov    $0x2,%edx
    39e9:	e8 b2 ea ff ff       	call   24a0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    39ee:	4c 8b 4b 18          	mov    0x18(%rbx),%r9
    39f2:	5e                   	pop    %rsi
    39f3:	5f                   	pop    %rdi
    39f4:	4b 8b 14 31          	mov    (%r9,%r14,1),%rdx
    39f8:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    39fc:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    3a00:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    3a07:	7f 97                	jg     39a0 <main+0x1350>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3a09:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    3a0e:	8b 32                	mov    (%rdx),%esi
    3a10:	48 83 c7 01          	add    $0x1,%rdi
    3a14:	39 fe                	cmp    %edi,%esi
    3a16:	0f 8f 64 ff ff ff    	jg     3980 <main+0x1330>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3a1c:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    3a21:	8b 8b 84 00 00 00    	mov    0x84(%rbx),%ecx
    3a27:	49 83 c4 01          	add    $0x1,%r12
    3a2b:	44 39 e1             	cmp    %r12d,%ecx
    3a2e:	0f 8f 1c ff ff ff    	jg     3950 <main+0x1300>
    3a34:	4c 8b 74 24 50       	mov    0x50(%rsp),%r14
    3a39:	4c 8b 6c 24 68       	mov    0x68(%rsp),%r13
    for (int d = 0 ; d < threads_per_group ; d++) {
    3a3e:	8b 44 24 10          	mov    0x10(%rsp),%eax
    3a42:	48 83 44 24 48 18    	addq   $0x18,0x48(%rsp)
    3a48:	48 81 c3 c8 00 00 00 	add    $0xc8,%rbx
    3a4f:	85 c0                	test   %eax,%eax
    3a51:	75 0d                	jne    3a60 <main+0x1410>
    3a53:	8b 44 24 40          	mov    0x40(%rsp),%eax
    3a57:	89 44 24 10          	mov    %eax,0x10(%rsp)
    3a5b:	e9 66 fc ff ff       	jmp    36c6 <main+0x1076>
    3a60:	4c 8b 7c 24 30       	mov    0x30(%rsp),%r15
    3a65:	48 8d 35 01 3b 00 00 	lea    0x3b01(%rip),%rsi        # 756d <_IO_stdin_used+0x56d>
    3a6c:	bf 01 00 00 00       	mov    $0x1,%edi
    3a71:	31 c0                	xor    %eax,%eax
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3a73:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    3a7d:	4c 89 fa             	mov    %r15,%rdx
    3a80:	e8 1b ea ff ff       	call   24a0 <__printf_chk@plt>
    3a85:	bf 0a 00 00 00       	mov    $0xa,%edi
    3a8a:	e8 71 e8 ff ff       	call   2300 <putchar@plt>
    3a8f:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    3a94:	bf 01 00 00 00       	mov    $0x1,%edi
    3a99:	48 8d 35 40 3e 00 00 	lea    0x3e40(%rip),%rsi        # 78e0 <_IO_stdin_used+0x8e0>
    3aa0:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3aa4:	31 c0                	xor    %eax,%eax
    3aa6:	e8 f5 e9 ff ff       	call   24a0 <__printf_chk@plt>
    3aab:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    3ab0:	bf 01 00 00 00       	mov    $0x1,%edi
    3ab5:	48 8d 35 4c 3e 00 00 	lea    0x3e4c(%rip),%rsi        # 7908 <_IO_stdin_used+0x908>
    3abc:	48 f7 eb             	imul   %rbx
    3abf:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    3ac4:	48 c1 f8 3f          	sar    $0x3f,%rax
    3ac8:	48 d1 fa             	sar    %rdx
    3acb:	48 29 c2             	sub    %rax,%rdx
    3ace:	31 c0                	xor    %eax,%eax
    3ad0:	e8 cb e9 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3ad5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3ada:	bf 01 00 00 00       	mov    $0x1,%edi
    3adf:	48 8d 35 52 3e 00 00 	lea    0x3e52(%rip),%rsi        # 7938 <_IO_stdin_used+0x938>
    3ae6:	48 f7 eb             	imul   %rbx
    3ae9:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3aee:	48 c1 f8 3f          	sar    $0x3f,%rax
    3af2:	48 d1 fa             	sar    %rdx
    3af5:	48 29 c2             	sub    %rax,%rdx
    3af8:	31 c0                	xor    %eax,%eax
    3afa:	e8 a1 e9 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3aff:	4c 89 f8             	mov    %r15,%rax
    3b02:	bf 01 00 00 00       	mov    $0x1,%edi
    3b07:	48 8d 35 5a 3e 00 00 	lea    0x3e5a(%rip),%rsi        # 7968 <_IO_stdin_used+0x968>
    3b0e:	48 f7 eb             	imul   %rbx
    3b11:	4c 89 f8             	mov    %r15,%rax
    3b14:	48 c1 f8 3f          	sar    $0x3f,%rax
    3b18:	48 d1 fa             	sar    %rdx
    3b1b:	48 29 c2             	sub    %rax,%rdx
    3b1e:	31 c0                	xor    %eax,%eax
    3b20:	e8 7b e9 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3b25:	4c 89 f0             	mov    %r14,%rax
    3b28:	49 c1 fe 3f          	sar    $0x3f,%r14
    3b2c:	48 8d 35 4e 3a 00 00 	lea    0x3a4e(%rip),%rsi        # 7581 <_IO_stdin_used+0x581>
    3b33:	48 f7 eb             	imul   %rbx
    3b36:	bf 01 00 00 00       	mov    $0x1,%edi
    3b3b:	31 c0                	xor    %eax,%eax
    3b3d:	48 d1 fa             	sar    %rdx
    3b40:	4c 29 f2             	sub    %r14,%rdx
    3b43:	e8 58 e9 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3b48:	4c 89 e8             	mov    %r13,%rax
    3b4b:	49 c1 fd 3f          	sar    $0x3f,%r13
    3b4f:	48 8d 35 3c 3a 00 00 	lea    0x3a3c(%rip),%rsi        # 7592 <_IO_stdin_used+0x592>
    3b56:	48 f7 eb             	imul   %rbx
    3b59:	bf 01 00 00 00       	mov    $0x1,%edi
    3b5e:	48 d1 fa             	sar    %rdx
    3b61:	4c 29 ea             	sub    %r13,%rdx
    3b64:	31 c0                	xor    %eax,%eax
    3b66:	e8 35 e9 ff ff       	call   24a0 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3b6b:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    3b73:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3b7c:	75 25                	jne    3ba3 <main+0x1553>
    3b7e:	48 81 c4 98 00 00 00 	add    $0x98,%rsp
    3b85:	31 c0                	xor    %eax,%eax
    3b87:	5b                   	pop    %rbx
    3b88:	5d                   	pop    %rbp
    3b89:	41 5c                	pop    %r12
    3b8b:	41 5d                	pop    %r13
    3b8d:	41 5e                	pop    %r14
    3b8f:	41 5f                	pop    %r15
    3b91:	c3                   	ret
      long v = 0;
    3b92:	31 d2                	xor    %edx,%edx
    3b94:	e9 89 fb ff ff       	jmp    3722 <main+0x10d2>
            exit(1);
    3b99:	bf 01 00 00 00       	mov    $0x1,%edi
    3b9e:	e8 5d e9 ff ff       	call   2500 <exit@plt>
}
    3ba3:	e8 c8 e7 ff ff       	call   2370 <__stack_chk_fail@plt>
    3ba8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000003bb0 <_start>:
    3bb0:	f3 0f 1e fa          	endbr64
    3bb4:	31 ed                	xor    %ebp,%ebp
    3bb6:	49 89 d1             	mov    %rdx,%r9
    3bb9:	5e                   	pop    %rsi
    3bba:	48 89 e2             	mov    %rsp,%rdx
    3bbd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3bc1:	50                   	push   %rax
    3bc2:	54                   	push   %rsp
    3bc3:	45 31 c0             	xor    %r8d,%r8d
    3bc6:	31 c9                	xor    %ecx,%ecx
    3bc8:	48 8d 3d 81 ea ff ff 	lea    -0x157f(%rip),%rdi        # 2650 <main>
    3bcf:	ff 15 03 64 00 00    	call   *0x6403(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3bd5:	f4                   	hlt
    3bd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003be0 <deregister_tm_clones>:
    3be0:	48 8d 3d 39 64 00 00 	lea    0x6439(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3be7:	48 8d 05 32 64 00 00 	lea    0x6432(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    3bee:	48 39 f8             	cmp    %rdi,%rax
    3bf1:	74 15                	je     3c08 <deregister_tm_clones+0x28>
    3bf3:	48 8b 05 e6 63 00 00 	mov    0x63e6(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    3bfa:	48 85 c0             	test   %rax,%rax
    3bfd:	74 09                	je     3c08 <deregister_tm_clones+0x28>
    3bff:	ff e0                	jmp    *%rax
    3c01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3c08:	c3                   	ret
    3c09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c10 <register_tm_clones>:
    3c10:	48 8d 3d 09 64 00 00 	lea    0x6409(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3c17:	48 8d 35 02 64 00 00 	lea    0x6402(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    3c1e:	48 29 fe             	sub    %rdi,%rsi
    3c21:	48 89 f0             	mov    %rsi,%rax
    3c24:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3c28:	48 c1 f8 03          	sar    $0x3,%rax
    3c2c:	48 01 c6             	add    %rax,%rsi
    3c2f:	48 d1 fe             	sar    %rsi
    3c32:	74 14                	je     3c48 <register_tm_clones+0x38>
    3c34:	48 8b 05 b5 63 00 00 	mov    0x63b5(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    3c3b:	48 85 c0             	test   %rax,%rax
    3c3e:	74 08                	je     3c48 <register_tm_clones+0x38>
    3c40:	ff e0                	jmp    *%rax
    3c42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c48:	c3                   	ret
    3c49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c50 <__do_global_dtors_aux>:
    3c50:	f3 0f 1e fa          	endbr64
    3c54:	80 3d cd 63 00 00 00 	cmpb   $0x0,0x63cd(%rip)        # a028 <completed.0>
    3c5b:	75 2b                	jne    3c88 <__do_global_dtors_aux+0x38>
    3c5d:	55                   	push   %rbp
    3c5e:	48 83 3d 92 63 00 00 00 	cmpq   $0x0,0x6392(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3c66:	48 89 e5             	mov    %rsp,%rbp
    3c69:	74 0c                	je     3c77 <__do_global_dtors_aux+0x27>
    3c6b:	48 8b 3d 96 63 00 00 	mov    0x6396(%rip),%rdi        # a008 <__dso_handle>
    3c72:	e8 69 e6 ff ff       	call   22e0 <__cxa_finalize@plt>
    3c77:	e8 64 ff ff ff       	call   3be0 <deregister_tm_clones>
    3c7c:	c6 05 a5 63 00 00 01 	movb   $0x1,0x63a5(%rip)        # a028 <completed.0>
    3c83:	5d                   	pop    %rbp
    3c84:	c3                   	ret
    3c85:	0f 1f 00             	nopl   (%rax)
    3c88:	c3                   	ret
    3c89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c90 <frame_dummy>:
    3c90:	f3 0f 1e fa          	endbr64
    3c94:	e9 77 ff ff ff       	jmp    3c10 <register_tm_clones>
    3c99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003ca0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3ca0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3ca4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3cab:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    3caf:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3cb7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    3cbb:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3cbf:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3cc6:	48 85 c9             	test   %rcx,%rcx
    3cc9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3cd0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3cd4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3cd8:	31 c0                	xor    %eax,%eax
    3cda:	c3                   	ret
    3cdb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003ce0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3ce0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3ce4:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    3ceb:	85 c9                	test   %ecx,%ecx
    3ced:	7e 4f                	jle    3d3e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3cef:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3cf6:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    3cfd:	48 c1 e1 09          	shl    $0x9,%rcx
    3d01:	48 8b 50 18          	mov    0x18(%rax),%rdx
    3d05:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3d09:	48 8b 70 38          	mov    0x38(%rax),%rsi
    3d0d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3d0f:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    3d13:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3d18:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3d20:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3d28:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3d33:	48 05 00 02 00 00    	add    $0x200,%rax
    3d39:	48 39 c1             	cmp    %rax,%rcx
    3d3c:	75 da                	jne    3d18 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    3d3e:	0f ae f8             	sfence
}
    3d41:	31 c0                	xor    %eax,%eax
    3d43:	c3                   	ret
    3d44:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3d4f:	90                   	nop

0000000000003d50 <external_thread>:
void * external_thread(void *arg) {
    3d50:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3d54:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    3d58:	0f 85 fb 00 00 00    	jne    3e59 <external_thread+0x109>
void * external_thread(void *arg) {
    3d5e:	41 57                	push   %r15
    3d60:	49 89 ff             	mov    %rdi,%r15
    3d63:	41 56                	push   %r14
    3d65:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    3d67:	4c 8d 2d 96 32 00 00 	lea    0x3296(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    3d6e:	41 54                	push   %r12
    3d70:	55                   	push   %rbp
    3d71:	53                   	push   %rbx
    3d72:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    3d76:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    3d7c:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    3d80:	85 c9                	test   %ecx,%ecx
    3d82:	7e 6e                	jle    3df2 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3d84:	45 31 e4             	xor    %r12d,%r12d
    3d87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3d90:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    3d98:	31 db                	xor    %ebx,%ebx
    3d9a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3d9e:	48 8b 06             	mov    (%rsi),%rax
    3da1:	8b 10                	mov    (%rax),%edx
    3da3:	85 d2                	test   %edx,%edx
    3da5:	7e 2a                	jle    3dd1 <external_thread+0x81>
    3da7:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    3dab:	48 89 dd             	mov    %rbx,%rbp
    3dae:	48 c1 e5 08          	shl    $0x8,%rbp
    3db2:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    3db6:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    3dbd:	45 85 c0             	test   %r8d,%r8d
    3dc0:	74 36                	je     3df8 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3dc2:	48 83 c3 01          	add    $0x1,%rbx
    3dc6:	39 da                	cmp    %ebx,%edx
    3dc8:	7f e1                	jg     3dab <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    3dca:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    3dd1:	49 83 c4 01          	add    $0x1,%r12
    3dd5:	44 39 e1             	cmp    %r12d,%ecx
    3dd8:	7f b6                	jg     3d90 <external_thread+0x40>
  while (data->running == 1) {
    3dda:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    3ddf:	74 9f                	je     3d80 <external_thread+0x30>
}
    3de1:	48 83 c4 08          	add    $0x8,%rsp
    3de5:	31 c0                	xor    %eax,%eax
    3de7:	5b                   	pop    %rbx
    3de8:	5d                   	pop    %rbp
    3de9:	41 5c                	pop    %r12
    3deb:	41 5d                	pop    %r13
    3ded:	41 5e                	pop    %r14
    3def:	41 5f                	pop    %r15
    3df1:	c3                   	ret
  while (data->running == 1) {
    3df2:	eb fe                	jmp    3df2 <external_thread+0xa2>
    3df4:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    3df8:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    3dfb:	48 8b 06             	mov    (%rsi),%rax
    3dfe:	48 8b 78 08          	mov    0x8(%rax),%rdi
    3e02:	48 01 ef             	add    %rbp,%rdi
    3e05:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    3e0c:	48 c1 e6 05          	shl    $0x5,%rsi
    3e10:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    3e17:	bf 04 00 00 00       	mov    $0x4,%edi
    3e1c:	e8 1f e5 ff ff       	call   2340 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    3e21:	49 8b 47 50          	mov    0x50(%r15),%rax
    3e25:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    3e29:	48 8b 40 08          	mov    0x8(%rax),%rax
    3e2d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    3e38:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3e3b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    3e3f:	48 83 c3 01          	add    $0x1,%rbx
    3e43:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3e47:	48 8b 06             	mov    (%rsi),%rax
    3e4a:	8b 10                	mov    (%rax),%edx
    3e4c:	39 da                	cmp    %ebx,%edx
    3e4e:	0f 8f 53 ff ff ff    	jg     3da7 <external_thread+0x57>
    3e54:	e9 71 ff ff ff       	jmp    3dca <external_thread+0x7a>
}
    3e59:	31 c0                	xor    %eax,%eax
    3e5b:	c3                   	ret
    3e5c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003e60 <timer_thread>:
void* timer_thread(void *arg) {
    3e60:	f3 0f 1e fa          	endbr64
    3e64:	41 57                	push   %r15
    3e66:	48 8d 35 a3 31 00 00 	lea    0x31a3(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3e6d:	41 56                	push   %r14
    3e6f:	41 55                	push   %r13
    3e71:	41 54                	push   %r12
    3e73:	55                   	push   %rbp
    3e74:	48 89 fd             	mov    %rdi,%rbp
    3e77:	53                   	push   %rbx
    3e78:	48 83 ec 58          	sub    $0x58,%rsp
    3e7c:	8b 57 04             	mov    0x4(%rdi),%edx
    3e7f:	bf 01 00 00 00       	mov    $0x1,%edi
    3e84:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3e8d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3e92:	31 c0                	xor    %eax,%eax
    3e94:	e8 07 e6 ff ff       	call   24a0 <__printf_chk@plt>
  struct timespec preempt = {
    3e99:	66 0f 6f 05 df 3c 00 00 	movdqa 0x3cdf(%rip),%xmm0        # 7b80 <_IO_stdin_used+0xb80>
    3ea1:	ba 88 13 00 00       	mov    $0x1388,%edx
    3ea6:	31 c0                	xor    %eax,%eax
    3ea8:	48 8d 35 73 31 00 00 	lea    0x3173(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3eaf:	bf 01 00 00 00       	mov    $0x1,%edi
    3eb4:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3eb9:	e8 e2 e5 ff ff       	call   24a0 <__printf_chk@plt>
  while (data->running && n < times) {
    3ebe:	44 8b 65 44          	mov    0x44(%rbp),%r12d
    3ec2:	45 85 e4             	test   %r12d,%r12d
    3ec5:	0f 84 9b 00 00 00    	je     3f66 <timer_thread+0x106>
  int n = 0;
    3ecb:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    3ece:	45 31 e4             	xor    %r12d,%r12d
    3ed1:	49 89 e6             	mov    %rsp,%r14
    y++;
    3ed4:	31 db                	xor    %ebx,%ebx
    3ed6:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    nanosleep(&preempt , &rem2);
    3edb:	4c 89 ef             	mov    %r13,%rdi
    3ede:	4c 89 f6             	mov    %r14,%rsi
    n++;
    3ee1:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3ee5:	e8 a6 e4 ff ff       	call   2390 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3eea:	48 63 45 30          	movslq 0x30(%rbp),%rax
    y++;
    3eee:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3ef3:	85 c0                	test   %eax,%eax
    3ef5:	7e 46                	jle    3f3d <timer_thread+0xdd>
    3ef7:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3efb:	49 c1 e4 09          	shl    $0x9,%r12
    3eff:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3f03:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3f08:	4c 8b 19             	mov    (%rcx),%r11
    3f0b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f0d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3f11:	99                   	cltd
    3f12:	41 f7 7b 40          	idivl  0x40(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    3f16:	49 8b 73 38          	mov    0x38(%r11),%rsi
    3f1a:	48 63 d2             	movslq %edx,%rdx
    3f1d:	48 c1 e2 09          	shl    $0x9,%rdx
    3f21:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3f2c:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f38:	49 39 c8             	cmp    %rcx,%r8
    3f3b:	75 cb                	jne    3f08 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    3f3d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3f40:	48 8b 45 18          	mov    0x18(%rbp),%rax
  while (data->running && n < times) {
    3f44:	44 8b 45 44          	mov    0x44(%rbp),%r8d
    if (y >= data->threads[0]->task_count) {
    3f48:	48 8b 00             	mov    (%rax),%rax
    y++;
    3f4b:	39 78 40             	cmp    %edi,0x40(%rax)
    3f4e:	0f 4e fb             	cmovle %ebx,%edi
    3f51:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3f54:	45 85 c0             	test   %r8d,%r8d
    3f57:	74 0d                	je     3f66 <timer_thread+0x106>
    3f59:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    3f60:	0f 85 75 ff ff ff    	jne    3edb <timer_thread+0x7b>
    3f66:	48 8d 3d cb 30 00 00 	lea    0x30cb(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3f6d:	e8 ae e3 ff ff       	call   2320 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f72:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    3f76:	85 d2                	test   %edx,%edx
    3f78:	7e 6b                	jle    3fe5 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    3f7a:	48 63 45 40          	movslq 0x40(%rbp),%rax
    3f7e:	85 c0                	test   %eax,%eax
    3f80:	7e 63                	jle    3fe5 <timer_thread+0x185>
    3f82:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3f86:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    3f8a:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3f92:	31 c9                	xor    %ecx,%ecx
    3f94:	48 89 c6             	mov    %rax,%rsi
    3f97:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3f9b:	48 8b 40 38          	mov    0x38(%rax),%rax
    3f9f:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    3fa3:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3fa9:	74 15                	je     3fc0 <timer_thread+0x160>
    3fab:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3fb5:	48 05 00 02 00 00    	add    $0x200,%rax
    3fbb:	48 39 c2             	cmp    %rax,%rdx
    3fbe:	74 1c                	je     3fdc <timer_thread+0x17c>
      data->threads[x]->tasks[y].sending = 0;
    3fc0:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3fca:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3fd0:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3fd7:	48 39 c2             	cmp    %rax,%rdx
    3fda:	75 e4                	jne    3fc0 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3fdc:	48 83 c1 08          	add    $0x8,%rcx
    3fe0:	48 39 cf             	cmp    %rcx,%rdi
    3fe3:	75 b2                	jne    3f97 <timer_thread+0x137>
  asm volatile ("mfence" ::: "memory");
    3fe5:	0f ae f0             	mfence
  struct timespec drain = {
    3fe8:	66 0f 6f 05 a0 3b 00 00 	movdqa 0x3ba0(%rip),%xmm0        # 7b90 <_IO_stdin_used+0xb90>
    3ff0:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ff5:	48 63 45 28          	movslq 0x28(%rbp),%rax
    y++;
    3ff9:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ffe:	85 c0                	test   %eax,%eax
    4000:	7e 4a                	jle    404c <timer_thread+0x1ec>
    4002:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4006:	4d 63 e4             	movslq %r12d,%r12
    4009:	49 c1 e4 09          	shl    $0x9,%r12
    400d:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4011:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4018:	48 8b 19             	mov    (%rcx),%rbx
    401b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    401d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4021:	99                   	cltd
    4022:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4025:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4029:	48 63 d2             	movslq %edx,%rdx
    402c:	48 c1 e2 09          	shl    $0x9,%rdx
    4030:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    403b:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4047:	49 39 c8             	cmp    %rcx,%r8
    404a:	75 cc                	jne    4018 <timer_thread+0x1b8>
    asm volatile ("mfence" ::: "memory");
    404c:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    404f:	48 8b 45 18          	mov    0x18(%rbp),%rax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4053:	8b 4d 30             	mov    0x30(%rbp),%ecx
    y++;
    4056:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    4059:	48 8b 00             	mov    (%rax),%rax
    y++;
    405c:	39 78 40             	cmp    %edi,0x40(%rax)
    405f:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4063:	85 c9                	test   %ecx,%ecx
    4065:	0f 8e 16 01 00 00    	jle    4181 <timer_thread+0x321>
    406b:	31 db                	xor    %ebx,%ebx
    int all_empty = 1;
    406d:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    4073:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int y = 0 ; y < 2 ; y++) {
    4078:	45 31 f6             	xor    %r14d,%r14d
    407b:	41 89 dd             	mov    %ebx,%r13d
    407e:	4c 8d 3c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r15
    4086:	44 89 f6             	mov    %r14d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4089:	85 c9                	test   %ecx,%ecx
    408b:	0f 8e af 00 00 00    	jle    4140 <timer_thread+0x2e0>
    4091:	4c 89 f7             	mov    %r14,%rdi
      y = 0;
    4094:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4096:	45 31 c0             	xor    %r8d,%r8d
    4099:	48 c1 e7 09          	shl    $0x9,%rdi
    409d:	0f 1f 00             	nopl   (%rax)
          if (x == k) { continue; }
    40a0:	41 39 d8             	cmp    %ebx,%r8d
    40a3:	74 36                	je     40db <timer_thread+0x27b>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    40a5:	48 8b 55 18          	mov    0x18(%rbp),%rdx
    40a9:	4a 8b 14 3a          	mov    (%rdx,%r15,1),%rdx
    40ad:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    40b1:	4c 8b 94 3a 70 01 00 00 	mov    0x170(%rdx,%rdi,1),%r10
    40b9:	49 01 c2             	add    %rax,%r10
    40bc:	4d 8b 0a             	mov    (%r10),%r9
    40bf:	49 8b 52 08          	mov    0x8(%r10),%rdx
    40c3:	4d 8b 89 80 00 00 00 	mov    0x80(%r9),%r9
    40ca:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    40d1:	4d 85 c9             	test   %r9,%r9
    40d4:	7f 2a                	jg     4100 <timer_thread+0x2a0>
    40d6:	48 85 d2             	test   %rdx,%rdx
    40d9:	7f 25                	jg     4100 <timer_thread+0x2a0>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    40db:	41 83 c0 01          	add    $0x1,%r8d
    40df:	48 83 c0 38          	add    $0x38,%rax
    40e3:	41 39 c8             	cmp    %ecx,%r8d
    40e6:	75 b8                	jne    40a0 <timer_thread+0x240>
      for (int y = 0 ; y < 2 ; y++) {
    40e8:	49 83 fe 01          	cmp    $0x1,%r14
    40ec:	74 52                	je     4140 <timer_thread+0x2e0>
    40ee:	49 83 c6 01          	add    $0x1,%r14
    40f2:	44 89 f6             	mov    %r14d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    40f5:	eb 9a                	jmp    4091 <timer_thread+0x231>
    40f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4100:	48 83 ec 08          	sub    $0x8,%rsp
    4104:	89 f1                	mov    %esi,%ecx
    4106:	bf 01 00 00 00       	mov    $0x1,%edi
    410b:	31 c0                	xor    %eax,%eax
    410d:	52                   	push   %rdx
    410e:	48 8d 35 48 2f 00 00 	lea    0x2f48(%rip),%rsi        # 705d <_IO_stdin_used+0x5d>
    4115:	44 89 ea             	mov    %r13d,%edx
    4118:	e8 83 e3 ff ff       	call   24a0 <__printf_chk@plt>
      for (int y = 0 ; y < 2 ; y++) {
    411d:	5a                   	pop    %rdx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    411e:	8b 4d 30             	mov    0x30(%rbp),%ecx
      for (int y = 0 ; y < 2 ; y++) {
    4121:	5e                   	pop    %rsi
    4122:	49 83 fe 01          	cmp    $0x1,%r14
    4126:	74 48                	je     4170 <timer_thread+0x310>
    4128:	49 83 c6 01          	add    $0x1,%r14
    412c:	45 31 db             	xor    %r11d,%r11d
    412f:	44 89 f6             	mov    %r14d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4132:	85 c9                	test   %ecx,%ecx
    4134:	0f 8f 57 ff ff ff    	jg     4091 <timer_thread+0x231>
    413a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4140:	48 83 c3 01          	add    $0x1,%rbx
    4144:	39 d9                	cmp    %ebx,%ecx
    4146:	0f 8f 2c ff ff ff    	jg     4078 <timer_thread+0x218>
    if (all_empty == 1) {
    414c:	41 83 fb 01          	cmp    $0x1,%r11d
    4150:	74 2f                	je     4181 <timer_thread+0x321>
      nanosleep(&drain , &drainrem);
    4152:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4157:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    415c:	e8 2f e2 ff ff       	call   2390 <nanosleep@plt>
    4161:	e9 8f fe ff ff       	jmp    3ff5 <timer_thread+0x195>
    4166:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4170:	48 83 c3 01          	add    $0x1,%rbx
    4174:	45 31 db             	xor    %r11d,%r11d
    4177:	39 d9                	cmp    %ebx,%ecx
    4179:	0f 8f f9 fe ff ff    	jg     4078 <timer_thread+0x218>
    417f:	eb cb                	jmp    414c <timer_thread+0x2ec>
    4181:	48 8d 3d cc 2e 00 00 	lea    0x2ecc(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    4188:	e8 93 e1 ff ff       	call   2320 <puts@plt>
  while (data->running) {
    418d:	8b 7d 44             	mov    0x44(%rbp),%edi
    4190:	85 ff                	test   %edi,%edi
    4192:	0f 84 e6 00 00 00    	je     427e <timer_thread+0x41e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4198:	8b 45 2c             	mov    0x2c(%rbp),%eax
    419b:	31 db                	xor    %ebx,%ebx
    419d:	4c 8d 25 d0 2e 00 00 	lea    0x2ed0(%rip),%r12        # 7074 <_IO_stdin_used+0x74>
    41a4:	4c 8d 2d e4 2e 00 00 	lea    0x2ee4(%rip),%r13        # 708f <_IO_stdin_used+0x8f>
    41ab:	85 c0                	test   %eax,%eax
    41ad:	7e 34                	jle    41e3 <timer_thread+0x383>
    41af:	90                   	nop
    41b0:	31 c0                	xor    %eax,%eax
    41b2:	89 da                	mov    %ebx,%edx
    41b4:	4c 89 e6             	mov    %r12,%rsi
    41b7:	bf 01 00 00 00       	mov    $0x1,%edi
    41bc:	e8 df e2 ff ff       	call   24a0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    41c1:	48 8b 45 18          	mov    0x18(%rbp),%rax
    41c5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    41c9:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    41cd:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    41d4:	0f 84 d1 00 00 00    	je     42ab <timer_thread+0x44b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    41da:	48 83 c3 01          	add    $0x1,%rbx
    41de:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    41e1:	7f cd                	jg     41b0 <timer_thread+0x350>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    41e3:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    41e7:	85 d2                	test   %edx,%edx
    41e9:	7e 7d                	jle    4268 <timer_thread+0x408>
      for (int y = 0 ; y < data->task_count ; y++) {
    41eb:	8b 45 40             	mov    0x40(%rbp),%eax
    41ee:	85 c0                	test   %eax,%eax
    41f0:	7e 76                	jle    4268 <timer_thread+0x408>
    41f2:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    41f5:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    41f9:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4201:	31 c9                	xor    %ecx,%ecx
    4203:	48 c1 e6 09          	shl    $0x9,%rsi
    4207:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4210:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4214:	48 8b 40 38          	mov    0x38(%rax),%rax
    4218:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    421c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4222:	74 1c                	je     4240 <timer_thread+0x3e0>
    4224:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    422e:	48 05 00 02 00 00    	add    $0x200,%rax
    4234:	48 39 c2             	cmp    %rax,%rdx
    4237:	74 26                	je     425f <timer_thread+0x3ff>
    4239:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4240:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    424a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4250:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    425a:	48 39 c2             	cmp    %rax,%rdx
    425d:	75 e1                	jne    4240 <timer_thread+0x3e0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    425f:	48 83 c1 08          	add    $0x8,%rcx
    4263:	48 39 f9             	cmp    %rdi,%rcx
    4266:	75 a8                	jne    4210 <timer_thread+0x3b0>
    asm volatile ("mfence" ::: "memory");
    4268:	0f ae f0             	mfence
    426b:	48 8d 3d 2f 2e 00 00 	lea    0x2e2f(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    4272:	e8 a9 e0 ff ff       	call   2320 <puts@plt>
    data->running = 0;
    4277:	c7 45 44 00 00 00 00 	movl   $0x0,0x44(%rbp)
    427e:	48 8d 3d 23 2e 00 00 	lea    0x2e23(%rip),%rdi        # 70a8 <_IO_stdin_used+0xa8>
    4285:	e8 96 e0 ff ff       	call   2320 <puts@plt>
}
    428a:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    428f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4298:	75 40                	jne    42da <timer_thread+0x47a>
    429a:	48 83 c4 58          	add    $0x58,%rsp
    429e:	31 c0                	xor    %eax,%eax
    42a0:	5b                   	pop    %rbx
    42a1:	5d                   	pop    %rbp
    42a2:	41 5c                	pop    %r12
    42a4:	41 5d                	pop    %r13
    42a6:	41 5e                	pop    %r14
    42a8:	41 5f                	pop    %r15
    42aa:	c3                   	ret
    42ab:	4c 89 ef             	mov    %r13,%rdi
    42ae:	e8 6d e0 ff ff       	call   2320 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    42b3:	48 8b 45 18          	mov    0x18(%rbp),%rax
    42b7:	be 01 00 00 00       	mov    $0x1,%esi
    42bc:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    42c0:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    42c4:	8b 78 60             	mov    0x60(%rax),%edi
    42c7:	e8 84 e1 ff ff       	call   2450 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    42cc:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    42cf:	0f 8f db fe ff ff    	jg     41b0 <timer_thread+0x350>
    42d5:	e9 09 ff ff ff       	jmp    41e3 <timer_thread+0x383>
}
    42da:	e8 91 e0 ff ff       	call   2370 <__stack_chk_fail@plt>
    42df:	90                   	nop

00000000000042e0 <sendm.part.0>:
int sendm(struct BarrierTask *data) {
    42e0:	41 57                	push   %r15
    42e2:	41 56                	push   %r14
    42e4:	41 55                	push   %r13
    42e6:	41 54                	push   %r12
    42e8:	55                   	push   %rbp
    42e9:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    42ea:	8b af 40 01 00 00    	mov    0x140(%rdi),%ebp
    42f0:	85 ed                	test   %ebp,%ebp
    42f2:	0f 8e 7a 01 00 00    	jle    4472 <sendm.part.0+0x192>
        if (n == data->thread->real_thread_index) { continue; }
    42f8:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    42ff:	49 89 ff             	mov    %rdi,%r15
    4302:	45 31 f6             	xor    %r14d,%r14d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    4305:	45 31 ed             	xor    %r13d,%r13d
    4308:	41 89 ec             	mov    %ebp,%r12d
        if (n == data->thread->real_thread_index) { continue; }
    430b:	8b 40 08             	mov    0x8(%rax),%eax
    430e:	89 44 24 cc          	mov    %eax,-0x34(%rsp)
    4312:	48 8d 87 88 01 00 00 	lea    0x188(%rdi),%rax
    4319:	48 89 44 24 e8       	mov    %rax,-0x18(%rsp)
    431e:	48 8d 87 90 01 00 00 	lea    0x190(%rdi),%rax
    4325:	48 89 44 24 f0       	mov    %rax,-0x10(%rsp)
    432a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4330:	44 39 6c 24 cc       	cmp    %r13d,-0x34(%rsp)
    4335:	0f 84 26 01 00 00    	je     4461 <sendm.part.0+0x181>
        struct Data *them = data->mailboxes[n].higher;
    433b:	49 8b 87 70 01 00 00 	mov    0x170(%r15),%rax
    4342:	4c 01 f0             	add    %r14,%rax
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    4345:	44 8b 40 30          	mov    0x30(%rax),%r8d
        struct Data *them = data->mailboxes[n].higher;
    4349:	48 8b 48 08          	mov    0x8(%rax),%rcx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    434d:	41 83 f8 02          	cmp    $0x2,%r8d
    4351:	0f 84 29 01 00 00    	je     4480 <sendm.part.0+0x1a0>
        for (; them->messages_count < min;) {
    4357:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    435e:	48 63 a9 88 00 00 00 	movslq 0x88(%rcx),%rbp
    4365:	48 39 ee             	cmp    %rbp,%rsi
    4368:	0f 8d f3 00 00 00    	jge    4461 <sendm.part.0+0x181>
    436e:	49 8b 87 08 01 00 00 	mov    0x108(%r15),%rax
    4375:	48 39 ee             	cmp    %rbp,%rsi
    4378:	49 89 eb             	mov    %rbp,%r11
          them->messages[them->messages_count++] = data->message; 
    437b:	48 8b 11             	mov    (%rcx),%rdx
    437e:	41 0f 9c c1          	setl   %r9b
    4382:	49 29 f3             	sub    %rsi,%r11
    4385:	48 89 44 24 d0       	mov    %rax,-0x30(%rsp)
    438a:	48 8b 81 08 03 00 00 	mov    0x308(%rcx),%rax
    4391:	49 8d 5b ff          	lea    -0x1(%r11),%rbx
    4395:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    439a:	48 89 44 24 d8       	mov    %rax,-0x28(%rsp)
    439f:	48 83 fb 02          	cmp    $0x2,%rbx
    43a3:	0f 86 a7 01 00 00    	jbe    4550 <sendm.part.0+0x270>
    43a9:	45 84 c9             	test   %r9b,%r9b
    43ac:	0f 84 9e 01 00 00    	je     4550 <sendm.part.0+0x270>
    43b2:	4c 8d 14 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r10
    43ba:	4a 8d 04 12          	lea    (%rdx,%r10,1),%rax
    43be:	48 89 44 24 e0       	mov    %rax,-0x20(%rsp)
    43c3:	49 89 c3             	mov    %rax,%r11
    43c6:	48 8d 04 ea          	lea    (%rdx,%rbp,8),%rax
    43ca:	48 39 44 24 e8       	cmp    %rax,-0x18(%rsp)
    43cf:	0f 83 cb 00 00 00    	jae    44a0 <sendm.part.0+0x1c0>
    43d5:	4c 89 d8             	mov    %r11,%rax
    43d8:	4c 8b 5c 24 f0       	mov    -0x10(%rsp),%r11
    43dd:	48 89 f7             	mov    %rsi,%rdi
    43e0:	4c 39 d8             	cmp    %r11,%rax
    43e3:	0f 83 b7 00 00 00    	jae    44a0 <sendm.part.0+0x1c0>
    43e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    43f0:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    43f7:	48 89 04 fa          	mov    %rax,(%rdx,%rdi,8)
        for (; them->messages_count < min;) {
    43fb:	48 83 c7 01          	add    $0x1,%rdi
    43ff:	48 39 fd             	cmp    %rdi,%rbp
    4402:	7f ec                	jg     43f0 <sendm.part.0+0x110>
    4404:	0f 1f 40 00          	nopl   0x0(%rax)
    4408:	31 ff                	xor    %edi,%edi
    440a:	45 84 c9             	test   %r9b,%r9b
    440d:	4c 8b 5c 24 d0       	mov    -0x30(%rsp),%r11
    4412:	48 0f 45 fb          	cmovne %rbx,%rdi
    4416:	4d 8d 5c 3b 01       	lea    0x1(%r11,%rdi,1),%r11
    441b:	48 8d 74 3e 01       	lea    0x1(%rsi,%rdi,1),%rsi
    4420:	4d 89 9f 08 01 00 00 	mov    %r11,0x108(%r15)
    4427:	4c 8b 5c 24 d8       	mov    -0x28(%rsp),%r11
    442c:	48 89 b1 80 00 00 00 	mov    %rsi,0x80(%rcx)
    4433:	48 8d 34 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rsi
    443b:	bb 00 00 00 00       	mov    $0x0,%ebx
    4440:	48 0f 44 f3          	cmove  %rbx,%rsi
    4444:	4d 8d 5c 3b 01       	lea    0x1(%r11,%rdi,1),%r11
    4449:	4c 01 d2             	add    %r10,%rdx
    444c:	4c 89 99 08 03 00 00 	mov    %r11,0x308(%rcx)
    4453:	48 89 04 32          	mov    %rax,(%rdx,%rsi,1)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    4457:	41 83 f8 02          	cmp    $0x2,%r8d
    445b:	0f 84 bf 00 00 00    	je     4520 <sendm.part.0+0x240>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    4461:	41 83 c5 01          	add    $0x1,%r13d
    4465:	49 83 c6 38          	add    $0x38,%r14
    4469:	45 39 e5             	cmp    %r12d,%r13d
    446c:	0f 85 be fe ff ff    	jne    4330 <sendm.part.0+0x50>
      asm volatile ("sfence" ::: "memory");
    4472:	0f ae f8             	sfence
}
    4475:	5b                   	pop    %rbx
    4476:	5d                   	pop    %rbp
    4477:	41 5c                	pop    %r12
    4479:	41 5d                	pop    %r13
    447b:	41 5e                	pop    %r14
    447d:	41 5f                	pop    %r15
    447f:	c3                   	ret
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    4480:	8b 81 00 01 00 00    	mov    0x100(%rcx),%eax
    4486:	83 f8 01             	cmp    $0x1,%eax
    4489:	0f 84 d1 00 00 00    	je     4560 <sendm.part.0+0x280>
        else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    448f:	85 c0                	test   %eax,%eax
    4491:	74 ce                	je     4461 <sendm.part.0+0x181>
    4493:	e9 bf fe ff ff       	jmp    4357 <sendm.part.0+0x77>
    4498:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    44a0:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    44a5:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    44ac:	48 8b 7c 24 e0       	mov    -0x20(%rsp),%rdi
    44b1:	49 d1 eb             	shr    %r11
    44b4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    44b9:	4c 89 dd             	mov    %r11,%rbp
    44bc:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    44c0:	48 c1 e5 04          	shl    $0x4,%rbp
    44c4:	49 89 eb             	mov    %rbp,%r11
    44c7:	48 01 fd             	add    %rdi,%rbp
    44ca:	41 83 e3 10          	and    $0x10,%r11d
    44ce:	74 11                	je     44e1 <sendm.part.0+0x201>
          them->messages[them->messages_count++] = data->message; 
    44d0:	0f 11 07             	movups %xmm0,(%rdi)
        for (; them->messages_count < min;) {
    44d3:	48 83 c7 10          	add    $0x10,%rdi
    44d7:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    44dc:	48 39 fd             	cmp    %rdi,%rbp
    44df:	74 1a                	je     44fb <sendm.part.0+0x21b>
    44e1:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
          them->messages[them->messages_count++] = data->message; 
    44e6:	0f 11 07             	movups %xmm0,(%rdi)
    44e9:	48 83 c7 20          	add    $0x20,%rdi
    44ed:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    44f1:	48 39 fd             	cmp    %rdi,%rbp
    44f4:	75 f0                	jne    44e6 <sendm.part.0+0x206>
    44f6:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    44fb:	4c 89 df             	mov    %r11,%rdi
    44fe:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    4502:	48 01 f7             	add    %rsi,%rdi
    4505:	41 83 e3 01          	and    $0x1,%r11d
    4509:	0f 84 f9 fe ff ff    	je     4408 <sendm.part.0+0x128>
          them->messages[them->messages_count++] = data->message; 
    450f:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    4516:	48 89 04 fa          	mov    %rax,(%rdx,%rdi,8)
        for (; them->messages_count < min;) {
    451a:	e9 e9 fe ff ff       	jmp    4408 <sendm.part.0+0x128>
    451f:	90                   	nop
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    4520:	83 b9 00 01 00 00 01 	cmpl   $0x1,0x100(%rcx)
    4527:	0f 85 34 ff ff ff    	jne    4461 <sendm.part.0+0x181>
          them->available_sending = 0;
    452d:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
          them->available_receiving = 1;
    4537:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
          them->finished_reading = 0;
    4541:	c7 81 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rcx)
    454b:	e9 11 ff ff ff       	jmp    4461 <sendm.part.0+0x181>
          them->messages[them->messages_count++] = data->message; 
    4550:	48 89 f7             	mov    %rsi,%rdi
    4553:	4c 8d 14 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r10
    455b:	e9 90 fe ff ff       	jmp    43f0 <sendm.part.0+0x110>
        for (; them->messages_count < min;) {
    4560:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    4567:	48 63 a9 88 00 00 00 	movslq 0x88(%rcx),%rbp
    456e:	48 39 f5             	cmp    %rsi,%rbp
    4571:	0f 8f f7 fd ff ff    	jg     436e <sendm.part.0+0x8e>
    4577:	eb b4                	jmp    452d <sendm.part.0+0x24d>
    4579:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004580 <strtolower>:
void strtolower(char *str) {
    4580:	f3 0f 1e fa          	endbr64
    4584:	55                   	push   %rbp
    4585:	53                   	push   %rbx
    4586:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    458a:	48 0f be 1f          	movsbq (%rdi),%rbx
    458e:	84 db                	test   %bl,%bl
    4590:	74 24                	je     45b6 <strtolower+0x36>
    4592:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4595:	e8 d6 df ff ff       	call   2570 <__ctype_tolower_loc@plt>
    459a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    45a0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    45a3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    45a7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    45aa:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    45ad:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    45b2:	84 db                	test   %bl,%bl
    45b4:	75 ea                	jne    45a0 <strtolower+0x20>
}
    45b6:	48 83 c4 08          	add    $0x8,%rsp
    45ba:	5b                   	pop    %rbx
    45bb:	5d                   	pop    %rbp
    45bc:	c3                   	ret
    45bd:	0f 1f 00             	nopl   (%rax)

00000000000045c0 <zh_malloc>:
void *zh_malloc(size_t size) {
    45c0:	f3 0f 1e fa          	endbr64
    45c4:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    45c8:	e8 93 de ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    45cd:	48 85 c0             	test   %rax,%rax
    45d0:	74 05                	je     45d7 <zh_malloc+0x17>
}
    45d2:	48 83 c4 08          	add    $0x8,%rsp
    45d6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    45d7:	48 8b 0d 42 5a 00 00 	mov    0x5a42(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    45de:	ba 28 00 00 00       	mov    $0x28,%edx
    45e3:	be 01 00 00 00       	mov    $0x1,%esi
    45e8:	48 8d 3d b9 2f 00 00 	lea    0x2fb9(%rip),%rdi        # 75a8 <_IO_stdin_used+0x5a8>
    45ef:	e8 2c df ff ff       	call   2520 <fwrite@plt>
        exit(1);
    45f4:	bf 01 00 00 00       	mov    $0x1,%edi
    45f9:	e8 02 df ff ff       	call   2500 <exit@plt>
    45fe:	66 90                	xchg   %ax,%ax

0000000000004600 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4600:	f3 0f 1e fa          	endbr64
    4604:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4605:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    460a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    460d:	e8 8e dd ff ff       	call   23a0 <strrchr@plt>
    if (!dot || dot == filename)
    4612:	48 85 c0             	test   %rax,%rax
    4615:	74 11                	je     4628 <get_filename_ext+0x28>
    4617:	48 39 c3             	cmp    %rax,%rbx
    461a:	74 0c                	je     4628 <get_filename_ext+0x28>
    return dot + 1;
    461c:	48 83 c0 01          	add    $0x1,%rax
}
    4620:	5b                   	pop    %rbx
    4621:	c3                   	ret
    4622:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4628:	48 8d 05 c1 2a 00 00 	lea    0x2ac1(%rip),%rax        # 70f0 <_IO_stdin_used+0xf0>
}
    462f:	5b                   	pop    %rbx
    4630:	c3                   	ret
    4631:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    463c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004640 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4640:	f3 0f 1e fa          	endbr64
    4644:	41 55                	push   %r13
    4646:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4649:	48 89 fe             	mov    %rdi,%rsi
    464c:	41 54                	push   %r12
    464e:	55                   	push   %rbp
    464f:	48 89 d5             	mov    %rdx,%rbp
    4652:	ba 00 04 00 00       	mov    $0x400,%edx
    4657:	53                   	push   %rbx
    4658:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    465f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4668:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4670:	31 c0                	xor    %eax,%eax
    4672:	49 89 e4             	mov    %rsp,%r12
    4675:	4c 89 e7             	mov    %r12,%rdi
    4678:	e8 03 de ff ff       	call   2480 <__strcpy_chk@plt>
    for (; *str; ++str)
    467d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4682:	84 db                	test   %bl,%bl
    4684:	74 24                	je     46aa <send_headers+0x6a>
        *str = (char)tolower(*str);
    4686:	e8 e5 de ff ff       	call   2570 <__ctype_tolower_loc@plt>
    468b:	48 8b 08             	mov    (%rax),%rcx
    468e:	4c 89 e0             	mov    %r12,%rax
    4691:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4698:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    469b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    469f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    46a2:	48 0f be 18          	movsbq (%rax),%rbx
    46a6:	84 db                	test   %bl,%bl
    46a8:	75 ee                	jne    4698 <send_headers+0x58>
    void *buf = malloc(size);
    46aa:	bf 11 00 00 00       	mov    $0x11,%edi
    46af:	e8 ac dd ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    46b4:	48 85 c0             	test   %rax,%rax
    46b7:	0f 84 7e 04 00 00    	je     4b3b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    46bd:	66 0f 6f 05 db 34 00 00 	movdqa 0x34db(%rip),%xmm0        # 7ba0 <_IO_stdin_used+0xba0>
    iov[0].iov_base = zh_malloc(slen);
    46c5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    46c9:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    46ce:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    46d6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    46da:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    46dd:	e8 7e dd ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    46e2:	48 85 c0             	test   %rax,%rax
    46e5:	0f 84 50 04 00 00    	je     4b3b <send_headers+0x4fb>
    46eb:	66 0f 6f 05 bd 34 00 00 	movdqa 0x34bd(%rip),%xmm0        # 7bb0 <_IO_stdin_used+0xbb0>
    iov[1].iov_base = zh_malloc(slen);
    46f3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    46f7:	4c 89 e7             	mov    %r12,%rdi
    46fa:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4704:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    470c:	0f 11 00             	movups %xmm0,(%rax)
    470f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4713:	be 2e 00 00 00       	mov    $0x2e,%esi
    4718:	e8 83 dc ff ff       	call   23a0 <strrchr@plt>
    if (!dot || dot == filename)
    471d:	48 85 c0             	test   %rax,%rax
    4720:	0f 84 ea 02 00 00    	je     4a10 <send_headers+0x3d0>
    4726:	4c 39 e0             	cmp    %r12,%rax
    4729:	0f 84 e1 02 00 00    	je     4a10 <send_headers+0x3d0>
    return dot + 1;
    472f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4733:	48 8d 3d 84 29 00 00 	lea    0x2984(%rip),%rdi        # 70be <_IO_stdin_used+0xbe>
    473a:	48 89 de             	mov    %rbx,%rsi
    473d:	e8 be dc ff ff       	call   2400 <strcmp@plt>
    4742:	85 c0                	test   %eax,%eax
    4744:	75 20                	jne    4766 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4746:	66 0f 6f 05 72 34 00 00 	movdqa 0x3472(%rip),%xmm0        # 7bc0 <_IO_stdin_used+0xbc0>
    474e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4756:	66 0f 6f 05 72 34 00 00 	movdqa 0x3472(%rip),%xmm0        # 7bd0 <_IO_stdin_used+0xbd0>
    475e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4766:	48 89 de             	mov    %rbx,%rsi
    4769:	48 8d 3d 52 29 00 00 	lea    0x2952(%rip),%rdi        # 70c2 <_IO_stdin_used+0xc2>
    4770:	e8 8b dc ff ff       	call   2400 <strcmp@plt>
    4775:	85 c0                	test   %eax,%eax
    4777:	75 20                	jne    4799 <send_headers+0x159>
    4779:	66 0f 6f 05 3f 34 00 00 	movdqa 0x343f(%rip),%xmm0        # 7bc0 <_IO_stdin_used+0xbc0>
    4781:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4789:	66 0f 6f 05 3f 34 00 00 	movdqa 0x343f(%rip),%xmm0        # 7bd0 <_IO_stdin_used+0xbd0>
    4791:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4799:	48 89 de             	mov    %rbx,%rsi
    479c:	48 8d 3d 24 29 00 00 	lea    0x2924(%rip),%rdi        # 70c7 <_IO_stdin_used+0xc7>
    47a3:	e8 58 dc ff ff       	call   2400 <strcmp@plt>
    47a8:	85 c0                	test   %eax,%eax
    47aa:	0f 84 10 02 00 00    	je     49c0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    47b0:	48 89 de             	mov    %rbx,%rsi
    47b3:	48 8d 3d 11 29 00 00 	lea    0x2911(%rip),%rdi        # 70cb <_IO_stdin_used+0xcb>
    47ba:	e8 41 dc ff ff       	call   2400 <strcmp@plt>
    47bf:	85 c0                	test   %eax,%eax
    47c1:	0f 84 a9 02 00 00    	je     4a70 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    47c7:	48 89 de             	mov    %rbx,%rsi
    47ca:	48 8d 3d fe 28 00 00 	lea    0x28fe(%rip),%rdi        # 70cf <_IO_stdin_used+0xcf>
    47d1:	e8 2a dc ff ff       	call   2400 <strcmp@plt>
    47d6:	85 c0                	test   %eax,%eax
    47d8:	0f 84 6a 02 00 00    	je     4a48 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    47de:	48 89 de             	mov    %rbx,%rsi
    47e1:	48 8d 3d 2a 29 00 00 	lea    0x292a(%rip),%rdi        # 7112 <_IO_stdin_used+0x112>
    47e8:	e8 13 dc ff ff       	call   2400 <strcmp@plt>
    47ed:	85 c0                	test   %eax,%eax
    47ef:	0f 84 2b 02 00 00    	je     4a20 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    47f5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    47f8:	0f 84 52 01 00 00    	je     4950 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    47fe:	48 89 de             	mov    %rbx,%rsi
    4801:	48 8d 3d cb 28 00 00 	lea    0x28cb(%rip),%rdi        # 70d3 <_IO_stdin_used+0xd3>
    4808:	e8 f3 db ff ff       	call   2400 <strcmp@plt>
    480d:	85 c0                	test   %eax,%eax
    480f:	0f 84 ab 02 00 00    	je     4ac0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4815:	48 89 de             	mov    %rbx,%rsi
    4818:	48 8d 3d b8 28 00 00 	lea    0x28b8(%rip),%rdi        # 70d7 <_IO_stdin_used+0xd7>
    481f:	e8 dc db ff ff       	call   2400 <strcmp@plt>
    4824:	85 c0                	test   %eax,%eax
    4826:	0f 84 6c 02 00 00    	je     4a98 <send_headers+0x458>
    slen = strlen(send_buffer);
    482c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4834:	4c 89 e7             	mov    %r12,%rdi
    4837:	e8 24 db ff ff       	call   2360 <strlen@plt>
    void *buf = malloc(size);
    483c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    483f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4842:	e8 19 dc ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4847:	48 85 c0             	test   %rax,%rax
    484a:	0f 84 eb 02 00 00    	je     4b3b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4850:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4854:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4858:	83 fb 08             	cmp    $0x8,%ebx
    485b:	0f 83 3f 01 00 00    	jae    49a0 <send_headers+0x360>
    4861:	f6 c3 04             	test   $0x4,%bl
    4864:	0f 85 7b 02 00 00    	jne    4ae5 <send_headers+0x4a5>
    486a:	85 db                	test   %ebx,%ebx
    486c:	74 13                	je     4881 <send_headers+0x241>
    486e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4876:	88 10                	mov    %dl,(%rax)
    4878:	f6 c3 02             	test   $0x2,%bl
    487b:	0f 85 96 02 00 00    	jne    4b17 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4881:	4d 89 e8             	mov    %r13,%r8
    4884:	48 8d 0d 50 28 00 00 	lea    0x2850(%rip),%rcx        # 70db <_IO_stdin_used+0xdb>
    488b:	4c 89 e7             	mov    %r12,%rdi
    488e:	31 c0                	xor    %eax,%eax
    4890:	ba 00 04 00 00       	mov    $0x400,%edx
    4895:	be 01 00 00 00       	mov    $0x1,%esi
    489a:	e8 e1 dc ff ff       	call   2580 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    489f:	4c 89 e7             	mov    %r12,%rdi
    48a2:	e8 b9 da ff ff       	call   2360 <strlen@plt>
    void *buf = malloc(size);
    48a7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    48aa:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    48ad:	e8 ae db ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    48b2:	48 85 c0             	test   %rax,%rax
    48b5:	0f 84 80 02 00 00    	je     4b3b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    48bb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    48bf:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    48c3:	83 fb 08             	cmp    $0x8,%ebx
    48c6:	0f 83 1c 01 00 00    	jae    49e8 <send_headers+0x3a8>
    48cc:	f6 c3 04             	test   $0x4,%bl
    48cf:	0f 85 29 02 00 00    	jne    4afe <send_headers+0x4be>
    48d5:	85 db                	test   %ebx,%ebx
    48d7:	74 13                	je     48ec <send_headers+0x2ac>
    48d9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    48e1:	88 10                	mov    %dl,(%rax)
    48e3:	f6 c3 02             	test   $0x2,%bl
    48e6:	0f 85 3d 02 00 00    	jne    4b29 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    48ec:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    48f1:	bf 02 00 00 00       	mov    $0x2,%edi
    48f6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    48fe:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4906:	e8 55 db ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    490b:	48 85 c0             	test   %rax,%rax
    490e:	0f 84 27 02 00 00    	je     4b3b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4914:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    491c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4920:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4928:	66 89 10             	mov    %dx,(%rax)
}
    492b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4933:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    493c:	0f 85 20 02 00 00    	jne    4b62 <send_headers+0x522>
    4942:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4949:	5b                   	pop    %rbx
    494a:	5d                   	pop    %rbp
    494b:	41 5c                	pop    %r12
    494d:	41 5d                	pop    %r13
    494f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4950:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4954:	0f 85 a4 fe ff ff    	jne    47fe <send_headers+0x1be>
    495a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    495e:	0f 85 9a fe ff ff    	jne    47fe <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4964:	66 0f 6f 05 b4 32 00 00 	movdqa 0x32b4(%rip),%xmm0        # 7c20 <_IO_stdin_used+0xc20>
    496c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4976:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    497e:	66 0f 6f 05 aa 32 00 00 	movdqa 0x32aa(%rip),%xmm0        # 7c30 <_IO_stdin_used+0xc30>
    4986:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    498e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4996:	e9 63 fe ff ff       	jmp    47fe <send_headers+0x1be>
    499b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    49a0:	89 da                	mov    %ebx,%edx
    49a2:	48 89 c7             	mov    %rax,%rdi
    49a5:	4c 89 e6             	mov    %r12,%rsi
    49a8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    49ad:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    49b2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    49b5:	c1 e9 03             	shr    $0x3,%ecx
    49b8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    49bb:	e9 c1 fe ff ff       	jmp    4881 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    49c0:	66 0f 6f 05 f8 31 00 00 	movdqa 0x31f8(%rip),%xmm0        # 7bc0 <_IO_stdin_used+0xbc0>
    49c8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    49d0:	66 0f 6f 05 08 32 00 00 	movdqa 0x3208(%rip),%xmm0        # 7be0 <_IO_stdin_used+0xbe0>
    49d8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    49e0:	e9 cb fd ff ff       	jmp    47b0 <send_headers+0x170>
    49e5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    49e8:	89 da                	mov    %ebx,%edx
    49ea:	48 89 c7             	mov    %rax,%rdi
    49ed:	4c 89 e6             	mov    %r12,%rsi
    49f0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    49f5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    49fa:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    49fd:	c1 e9 03             	shr    $0x3,%ecx
    4a00:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4a03:	e9 e4 fe ff ff       	jmp    48ec <send_headers+0x2ac>
    4a08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4a10:	48 8d 1d d9 26 00 00 	lea    0x26d9(%rip),%rbx        # 70f0 <_IO_stdin_used+0xf0>
    4a17:	e9 94 fd ff ff       	jmp    47b0 <send_headers+0x170>
    4a1c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a20:	66 0f 6f 05 d8 31 00 00 	movdqa 0x31d8(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    4a28:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a30:	66 0f 6f 05 d8 31 00 00 	movdqa 0x31d8(%rip),%xmm0        # 7c10 <_IO_stdin_used+0xc10>
    4a38:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a40:	e9 b0 fd ff ff       	jmp    47f5 <send_headers+0x1b5>
    4a45:	0f 1f 00             	nopl   (%rax)
    4a48:	66 0f 6f 05 b0 31 00 00 	movdqa 0x31b0(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    4a50:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a58:	66 0f 6f 05 b0 31 00 00 	movdqa 0x31b0(%rip),%xmm0        # 7c10 <_IO_stdin_used+0xc10>
    4a60:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a68:	e9 71 fd ff ff       	jmp    47de <send_headers+0x19e>
    4a6d:	0f 1f 00             	nopl   (%rax)
    4a70:	66 0f 6f 05 48 31 00 00 	movdqa 0x3148(%rip),%xmm0        # 7bc0 <_IO_stdin_used+0xbc0>
    4a78:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a80:	66 0f 6f 05 68 31 00 00 	movdqa 0x3168(%rip),%xmm0        # 7bf0 <_IO_stdin_used+0xbf0>
    4a88:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a90:	e9 32 fd ff ff       	jmp    47c7 <send_headers+0x187>
    4a95:	0f 1f 00             	nopl   (%rax)
    4a98:	66 0f 6f 05 60 31 00 00 	movdqa 0x3160(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    4aa0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4aa8:	66 0f 6f 05 a0 31 00 00 	movdqa 0x31a0(%rip),%xmm0        # 7c50 <_IO_stdin_used+0xc50>
    4ab0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4ab8:	e9 6f fd ff ff       	jmp    482c <send_headers+0x1ec>
    4abd:	0f 1f 00             	nopl   (%rax)
    4ac0:	66 0f 6f 05 38 31 00 00 	movdqa 0x3138(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    4ac8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ad0:	66 0f 6f 05 68 31 00 00 	movdqa 0x3168(%rip),%xmm0        # 7c40 <_IO_stdin_used+0xc40>
    4ad8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4ae0:	e9 30 fd ff ff       	jmp    4815 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ae5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4aec:	89 db                	mov    %ebx,%ebx
    4aee:	89 10                	mov    %edx,(%rax)
    4af0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4af5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4af9:	e9 83 fd ff ff       	jmp    4881 <send_headers+0x241>
    4afe:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4b05:	89 db                	mov    %ebx,%ebx
    4b07:	89 10                	mov    %edx,(%rax)
    4b09:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4b0e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4b12:	e9 d5 fd ff ff       	jmp    48ec <send_headers+0x2ac>
    4b17:	89 db                	mov    %ebx,%ebx
    4b19:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4b1f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4b24:	e9 58 fd ff ff       	jmp    4881 <send_headers+0x241>
    4b29:	89 db                	mov    %ebx,%ebx
    4b2b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4b31:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4b36:	e9 b1 fd ff ff       	jmp    48ec <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4b3b:	48 8b 0d de 54 00 00 	mov    0x54de(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4b42:	ba 28 00 00 00       	mov    $0x28,%edx
    4b47:	be 01 00 00 00       	mov    $0x1,%esi
    4b4c:	48 8d 3d 55 2a 00 00 	lea    0x2a55(%rip),%rdi        # 75a8 <_IO_stdin_used+0x5a8>
    4b53:	e8 c8 d9 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4b58:	bf 01 00 00 00       	mov    $0x1,%edi
    4b5d:	e8 9e d9 ff ff       	call   2500 <exit@plt>
}
    4b62:	e8 09 d8 ff ff       	call   2370 <__stack_chk_fail@plt>
    4b67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004b70 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4b70:	f3 0f 1e fa          	endbr64
    4b74:	41 55                	push   %r13
    4b76:	49 89 d5             	mov    %rdx,%r13
    4b79:	41 54                	push   %r12
    4b7b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    4b7e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4b81:	55                   	push   %rbp
    4b82:	53                   	push   %rbx
    4b83:	48 89 f3             	mov    %rsi,%rbx
    4b86:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4b8a:	e8 d1 d8 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4b8f:	48 85 c0             	test   %rax,%rax
    4b92:	74 6b                	je     4bff <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4b94:	4c 89 e7             	mov    %r12,%rdi
    4b97:	48 89 c5             	mov    %rax,%rbp
    4b9a:	31 f6                	xor    %esi,%esi
    4b9c:	31 c0                	xor    %eax,%eax
    4b9e:	e8 2d d9 ff ff       	call   24d0 <open@plt>
    4ba3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4ba6:	85 c0                	test   %eax,%eax
    4ba8:	0f 88 08 da ff ff    	js     25b6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4bae:	48 89 da             	mov    %rbx,%rdx
    4bb1:	48 89 ee             	mov    %rbp,%rsi
    4bb4:	89 c7                	mov    %eax,%edi
    4bb6:	e8 25 d8 ff ff       	call   23e0 <read@plt>
    if (ret < file_size) {
    4bbb:	48 98                	cltq
    4bbd:	48 39 d8             	cmp    %rbx,%rax
    4bc0:	7c 1e                	jl     4be0 <copy_file_contents+0x70>
    close(fd);
    4bc2:	44 89 e7             	mov    %r12d,%edi
    4bc5:	e8 f6 d7 ff ff       	call   23c0 <close@plt>
    iov->iov_base = buf;
    4bca:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    4bce:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4bd2:	48 83 c4 08          	add    $0x8,%rsp
    4bd6:	5b                   	pop    %rbx
    4bd7:	5d                   	pop    %rbp
    4bd8:	41 5c                	pop    %r12
    4bda:	41 5d                	pop    %r13
    4bdc:	c3                   	ret
    4bdd:	0f 1f 00             	nopl   (%rax)
    4be0:	48 8b 0d 39 54 00 00 	mov    0x5439(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4be7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    4bec:	be 01 00 00 00       	mov    $0x1,%esi
    4bf1:	48 8d 3d f9 24 00 00 	lea    0x24f9(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4bf8:	e8 23 d9 ff ff       	call   2520 <fwrite@plt>
    4bfd:	eb c3                	jmp    4bc2 <copy_file_contents+0x52>
    4bff:	48 8b 0d 1a 54 00 00 	mov    0x541a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c06:	ba 28 00 00 00       	mov    $0x28,%edx
    4c0b:	be 01 00 00 00       	mov    $0x1,%esi
    4c10:	48 8d 3d 91 29 00 00 	lea    0x2991(%rip),%rdi        # 75a8 <_IO_stdin_used+0x5a8>
    4c17:	e8 04 d9 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4c1c:	bf 01 00 00 00       	mov    $0x1,%edi
    4c21:	e8 da d8 ff ff       	call   2500 <exit@plt>
    4c26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004c30 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4c30:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4c34:	8b 46 44             	mov    0x44(%rsi),%eax
    4c37:	48 89 fa             	mov    %rdi,%rdx
    4c3a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    4c3d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4c43:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4c46:	48 8b 07             	mov    (%rdi),%rax
    4c49:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4c4c:	f6 c1 02             	test   $0x2,%cl
    4c4f:	74 00                	je     4c51 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4c51:	89 f0                	mov    %esi,%eax
    4c53:	44 29 c0             	sub    %r8d,%eax
    4c56:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4c59:	0f 82 63 d9 ff ff    	jb     25c2 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4c5f:	c1 e9 0a             	shr    $0xa,%ecx
    4c62:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c66:	8b 47 44             	mov    0x44(%rdi),%eax
    4c69:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4c6c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4c6f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4c72:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4c75:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c79:	d3 e0                	shl    %cl,%eax
    4c7b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    4c7e:	48 c1 e0 06          	shl    $0x6,%rax
    4c82:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4c86:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    4c8c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4c8f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4c93:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4c99:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4ca1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4ca5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4ca8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4caf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4cb7:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    4cbb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    4cbf:	e8 bc d6 ff ff       	call   2380 <io_uring_submit@plt>
}
    4cc4:	31 c0                	xor    %eax,%eax
    4cc6:	48 83 c4 08          	add    $0x8,%rsp
    4cca:	c3                   	ret
    4ccb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004cd0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4cd0:	f3 0f 1e fa          	endbr64
    4cd4:	41 55                	push   %r13
    4cd6:	41 89 fd             	mov    %edi,%r13d
    4cd9:	41 54                	push   %r12
    4cdb:	55                   	push   %rbp
    4cdc:	53                   	push   %rbx
    4cdd:	48 89 f3             	mov    %rsi,%rbx
    4ce0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4ce4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4ce7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    4ced:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4cf0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4cf3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4cf5:	f6 c1 02             	test   $0x2,%cl
    4cf8:	74 00                	je     4cfa <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    4cfa:	89 c2                	mov    %eax,%edx
    4cfc:	29 f2                	sub    %esi,%edx
    4cfe:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4d01:	0f 82 cb d8 ff ff    	jb     25d2 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d07:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    4d0a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    4d0d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4d10:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4d15:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d18:	23 6b 58             	and    0x58(%rbx),%ebp
    4d1b:	d3 e5                	shl    %cl,%ebp
    4d1d:	48 c1 e5 06          	shl    $0x6,%rbp
    4d21:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4d25:	e8 36 d7 ff ff       	call   2460 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    4d2a:	be 01 00 00 00       	mov    $0x1,%esi
    4d2f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4d34:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4d37:	e8 b4 d6 ff ff       	call   23f0 <calloc@plt>
    req->client_socket = client_socket;
    4d3c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4d41:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4d45:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4d48:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4d4d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4d52:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    4d5b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4d63:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4d67:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    4d6b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4d72:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4d7a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    4d7e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4d86:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    4d8e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4d92:	e8 e9 d5 ff ff       	call   2380 <io_uring_submit@plt>
}
    4d97:	48 83 c4 08          	add    $0x8,%rsp
    4d9b:	31 c0                	xor    %eax,%eax
    4d9d:	5b                   	pop    %rbx
    4d9e:	5d                   	pop    %rbp
    4d9f:	41 5c                	pop    %r12
    4da1:	41 5d                	pop    %r13
    4da3:	c3                   	ret
    4da4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4daf:	90                   	nop

0000000000004db0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4db0:	f3 0f 1e fa          	endbr64
    4db4:	41 56                	push   %r14
    4db6:	41 89 f6             	mov    %esi,%r14d
    4db9:	41 55                	push   %r13
    4dbb:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    4dbe:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4dc3:	41 54                	push   %r12
    4dc5:	55                   	push   %rbp
    4dc6:	48 89 d5             	mov    %rdx,%rbp
    4dc9:	53                   	push   %rbx
    void *buf = malloc(size);
    4dca:	e8 91 d6 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4dcf:	48 85 c0             	test   %rax,%rax
    4dd2:	0f 84 dd 00 00 00    	je     4eb5 <_send_static_string_content+0x105>
    4dd8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    4ddb:	4c 89 ef             	mov    %r13,%rdi
    4dde:	e8 7d d5 ff ff       	call   2360 <strlen@plt>
    req->iovec_count = 1;
    4de3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    4dea:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    4dee:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4df1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4df4:	e8 67 d6 ff ff       	call   2460 <malloc@plt>
    4df9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    4dfc:	48 85 c0             	test   %rax,%rax
    4dff:	0f 84 b0 00 00 00    	je     4eb5 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4e05:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4e09:	4c 89 e2             	mov    %r12,%rdx
    4e0c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    4e0f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4e13:	e8 18 d6 ff ff       	call   2430 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4e18:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e1b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4e21:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4e24:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4e28:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4e2a:	f6 c1 02             	test   $0x2,%cl
    4e2d:	0f 85 7d 00 00 00    	jne    4eb0 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4e33:	89 d0                	mov    %edx,%eax
    4e35:	29 f0                	sub    %esi,%eax
    4e37:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    4e3a:	0f 82 9c d7 ff ff    	jb     25dc <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4e40:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e43:	8b 45 44             	mov    0x44(%rbp),%eax
    4e46:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4e49:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    4e4c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4e4f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4e52:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4e58:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e5c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4e5e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4e61:	48 89 ef             	mov    %rbp,%rdi
    4e64:	48 c1 e0 06          	shl    $0x6,%rax
    4e68:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    4e6c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4e6f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4e73:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4e79:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4e81:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4e85:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4e88:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4e8f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4e97:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    4e9b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    4e9f:	5b                   	pop    %rbx
    4ea0:	5d                   	pop    %rbp
    4ea1:	41 5c                	pop    %r12
    4ea3:	41 5d                	pop    %r13
    4ea5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4ea7:	e9 d4 d4 ff ff       	jmp    2380 <io_uring_submit@plt>
    4eac:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4eb0:	e9 7e ff ff ff       	jmp    4e33 <_send_static_string_content+0x83>
    4eb5:	48 8b 0d 64 51 00 00 	mov    0x5164(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4ebc:	ba 28 00 00 00       	mov    $0x28,%edx
    4ec1:	be 01 00 00 00       	mov    $0x1,%esi
    4ec6:	48 8d 3d db 26 00 00 	lea    0x26db(%rip),%rdi        # 75a8 <_IO_stdin_used+0x5a8>
    4ecd:	e8 4e d6 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4ed2:	bf 01 00 00 00       	mov    $0x1,%edi
    4ed7:	e8 24 d6 ff ff       	call   2500 <exit@plt>
    4edc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004ee0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4ee0:	f3 0f 1e fa          	endbr64
    4ee4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4ee7:	89 fe                	mov    %edi,%esi
    4ee9:	48 8b 3d 28 51 00 00 	mov    0x5128(%rip),%rdi        # a018 <unimplemented_content>
    4ef0:	e9 bb fe ff ff       	jmp    4db0 <_send_static_string_content>
    4ef5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004f00 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4f00:	f3 0f 1e fa          	endbr64
    4f04:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4f07:	89 fe                	mov    %edi,%esi
    4f09:	48 8b 3d 00 51 00 00 	mov    0x5100(%rip),%rdi        # a010 <http_404_content>
    4f10:	e9 9b fe ff ff       	jmp    4db0 <_send_static_string_content>
    4f15:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004f20 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4f20:	f3 0f 1e fa          	endbr64
    4f24:	41 56                	push   %r14
    4f26:	41 55                	push   %r13
    4f28:	49 89 d5             	mov    %rdx,%r13
    4f2b:	41 54                	push   %r12
    4f2d:	41 89 f4             	mov    %esi,%r12d
    4f30:	55                   	push   %rbp
    4f31:	48 89 fd             	mov    %rdi,%rbp
    4f34:	53                   	push   %rbx
    4f35:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    4f3c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4f45:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    4f4d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    4f4f:	e8 0c d4 ff ff       	call   2360 <strlen@plt>
    4f54:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4f59:	48 89 c3             	mov    %rax,%rbx
    4f5c:	0f 84 b6 00 00 00    	je     5018 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f62:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4f67:	48 89 ee             	mov    %rbp,%rsi
    4f6a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4f6e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4f73:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4f7b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f83:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4f8e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4f96:	e8 75 d4 ff ff       	call   2410 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4f9b:	48 89 e6             	mov    %rsp,%rsi
    4f9e:	4c 89 f7             	mov    %r14,%rdi
    4fa1:	e8 7a d4 ff ff       	call   2420 <stat@plt>
    4fa6:	83 f8 ff             	cmp    $0xffffffff,%eax
    4fa9:	0f 84 d3 00 00 00    	je     5082 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    4faf:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4fb3:	25 00 f0 00 00       	and    $0xf000,%eax
    4fb8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4fbd:	0f 84 f5 00 00 00    	je     50b8 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4fc3:	48 8b 3d 46 50 00 00 	mov    0x5046(%rip),%rdi        # a010 <http_404_content>
    4fca:	4c 89 ea             	mov    %r13,%rdx
    4fcd:	44 89 e6             	mov    %r12d,%esi
    4fd0:	e8 db fd ff ff       	call   4db0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4fd5:	4c 89 f2             	mov    %r14,%rdx
    4fd8:	bf 01 00 00 00       	mov    $0x1,%edi
    4fdd:	31 c0                	xor    %eax,%eax
    4fdf:	48 8d 35 5b 21 00 00 	lea    0x215b(%rip),%rsi        # 7141 <_IO_stdin_used+0x141>
    4fe6:	e8 b5 d4 ff ff       	call   24a0 <__printf_chk@plt>
}
    4feb:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4ff3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4ffc:	0f 85 20 01 00 00    	jne    5122 <handle_get_method+0x202>
    5002:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5009:	5b                   	pop    %rbx
    500a:	5d                   	pop    %rbp
    500b:	41 5c                	pop    %r12
    500d:	41 5d                	pop    %r13
    500f:	41 5e                	pop    %r14
    5011:	c3                   	ret
    5012:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5018:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    501d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5025:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    502a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    502d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5035:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5038:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5040:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    504b:	e8 c0 d3 ff ff       	call   2410 <__memcpy_chk@plt>
    5050:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5055:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    505a:	48 8d 35 ab 20 00 00 	lea    0x20ab(%rip),%rsi        # 710c <_IO_stdin_used+0x10c>
    5061:	48 29 d9             	sub    %rbx,%rcx
    5064:	ba 0b 00 00 00       	mov    $0xb,%edx
    5069:	e8 a2 d3 ff ff       	call   2410 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    506e:	48 89 e6             	mov    %rsp,%rsi
    5071:	4c 89 f7             	mov    %r14,%rdi
    5074:	e8 a7 d3 ff ff       	call   2420 <stat@plt>
    5079:	83 f8 ff             	cmp    $0xffffffff,%eax
    507c:	0f 85 2d ff ff ff    	jne    4faf <handle_get_method+0x8f>
    5082:	4c 89 f2             	mov    %r14,%rdx
    5085:	48 89 e9             	mov    %rbp,%rcx
    5088:	48 8d 35 88 20 00 00 	lea    0x2088(%rip),%rsi        # 7117 <_IO_stdin_used+0x117>
    508f:	31 c0                	xor    %eax,%eax
    5091:	bf 01 00 00 00       	mov    $0x1,%edi
    5096:	e8 05 d4 ff ff       	call   24a0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    509b:	48 8b 3d 6e 4f 00 00 	mov    0x4f6e(%rip),%rdi        # a010 <http_404_content>
    50a2:	4c 89 ea             	mov    %r13,%rdx
    50a5:	44 89 e6             	mov    %r12d,%esi
    50a8:	e8 03 fd ff ff       	call   4db0 <_send_static_string_content>
}
    50ad:	e9 39 ff ff ff       	jmp    4feb <handle_get_method+0xcb>
    50b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    50b8:	bf 70 00 00 00       	mov    $0x70,%edi
    50bd:	e8 9e d3 ff ff       	call   2460 <malloc@plt>
    50c2:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    50c5:	48 85 c0             	test   %rax,%rax
    50c8:	74 5d                	je     5127 <handle_get_method+0x207>
            req->client_socket = client_socket;
    50ca:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    50ce:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    50d3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    50d7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    50da:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    50e1:	e8 5a f5 ff ff       	call   4640 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    50e6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    50eb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    50ef:	4c 89 f7             	mov    %r14,%rdi
    50f2:	e8 79 fa ff ff       	call   4b70 <copy_file_contents>
    50f7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    50fc:	4c 89 f2             	mov    %r14,%rdx
    50ff:	31 c0                	xor    %eax,%eax
    5101:	48 8d 35 27 20 00 00 	lea    0x2027(%rip),%rsi        # 712f <_IO_stdin_used+0x12f>
    5108:	bf 01 00 00 00       	mov    $0x1,%edi
    510d:	e8 8e d3 ff ff       	call   24a0 <__printf_chk@plt>
            add_write_request(req, ring);
    5112:	4c 89 ee             	mov    %r13,%rsi
    5115:	48 89 df             	mov    %rbx,%rdi
    5118:	e8 13 fb ff ff       	call   4c30 <add_write_request>
    511d:	e9 c9 fe ff ff       	jmp    4feb <handle_get_method+0xcb>
}
    5122:	e8 49 d2 ff ff       	call   2370 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5127:	48 8b 0d f2 4e 00 00 	mov    0x4ef2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    512e:	ba 28 00 00 00       	mov    $0x28,%edx
    5133:	be 01 00 00 00       	mov    $0x1,%esi
    5138:	48 8d 3d 69 24 00 00 	lea    0x2469(%rip),%rdi        # 75a8 <_IO_stdin_used+0x5a8>
    513f:	e8 dc d3 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5144:	bf 01 00 00 00       	mov    $0x1,%edi
    5149:	e8 b2 d3 ff ff       	call   2500 <exit@plt>
    514e:	66 90                	xchg   %ax,%ax

0000000000005150 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5150:	f3 0f 1e fa          	endbr64
    5154:	41 57                	push   %r15
    5156:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5158:	4c 8d 35 47 1f 00 00 	lea    0x1f47(%rip),%r14        # 70a6 <_IO_stdin_used+0xa6>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    515f:	41 55                	push   %r13
    5161:	49 89 d5             	mov    %rdx,%r13
    5164:	41 54                	push   %r12
    5166:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    5169:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    516c:	55                   	push   %rbp
    516d:	53                   	push   %rbx
    516e:	48 83 ec 18          	sub    $0x18,%rsp
    5172:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    517b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5180:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5182:	49 89 e7             	mov    %rsp,%r15
    5185:	4c 89 fa             	mov    %r15,%rdx
    5188:	e8 43 d2 ff ff       	call   23d0 <strtok_r@plt>
    for (; *str; ++str)
    518d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    5191:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    5194:	84 db                	test   %bl,%bl
    5196:	74 1d                	je     51b5 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    5198:	e8 d3 d3 ff ff       	call   2570 <__ctype_tolower_loc@plt>
    519d:	48 89 ea             	mov    %rbp,%rdx
    51a0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    51a3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    51a7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    51aa:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    51ad:	48 0f be 1a          	movsbq (%rdx),%rbx
    51b1:	84 db                	test   %bl,%bl
    51b3:	75 eb                	jne    51a0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    51b5:	4c 89 fa             	mov    %r15,%rdx
    51b8:	4c 89 f6             	mov    %r14,%rsi
    51bb:	31 ff                	xor    %edi,%edi
    51bd:	e8 0e d2 ff ff       	call   23d0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    51c2:	48 8d 35 8b 1f 00 00 	lea    0x1f8b(%rip),%rsi        # 7154 <_IO_stdin_used+0x154>
    51c9:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    51cc:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    51cf:	e8 2c d2 ff ff       	call   2400 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    51d4:	4c 89 ea             	mov    %r13,%rdx
    51d7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    51da:	85 c0                	test   %eax,%eax
    51dc:	75 2a                	jne    5208 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    51de:	48 89 df             	mov    %rbx,%rdi
    51e1:	e8 3a fd ff ff       	call   4f20 <handle_get_method>
}
    51e6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    51eb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    51f4:	75 20                	jne    5216 <handle_http_method+0xc6>
    51f6:	48 83 c4 18          	add    $0x18,%rsp
    51fa:	5b                   	pop    %rbx
    51fb:	5d                   	pop    %rbp
    51fc:	41 5c                	pop    %r12
    51fe:	41 5d                	pop    %r13
    5200:	41 5e                	pop    %r14
    5202:	41 5f                	pop    %r15
    5204:	c3                   	ret
    5205:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5208:	48 8b 3d 09 4e 00 00 	mov    0x4e09(%rip),%rdi        # a018 <unimplemented_content>
    520f:	e8 9c fb ff ff       	call   4db0 <_send_static_string_content>
}
    5214:	eb d0                	jmp    51e6 <handle_http_method+0x96>
    5216:	e8 55 d1 ff ff       	call   2370 <__stack_chk_fail@plt>
    521b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005220 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5220:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5224:	85 d2                	test   %edx,%edx
    5226:	7e 38                	jle    5260 <get_line+0x40>
    5228:	48 63 d2             	movslq %edx,%rdx
    522b:	48 83 c7 01          	add    $0x1,%rdi
    522f:	48 01 f2             	add    %rsi,%rdx
    5232:	eb 11                	jmp    5245 <get_line+0x25>
    5234:	0f 1f 40 00          	nopl   0x0(%rax)
    5238:	48 83 c6 01          	add    $0x1,%rsi
    523c:	48 83 c7 01          	add    $0x1,%rdi
    5240:	48 39 d6             	cmp    %rdx,%rsi
    5243:	74 1b                	je     5260 <get_line+0x40>
        dest[i] = src[i];
    5245:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5249:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    524b:	3c 0d                	cmp    $0xd,%al
    524d:	75 e9                	jne    5238 <get_line+0x18>
    524f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5252:	75 e4                	jne    5238 <get_line+0x18>
            dest[i] = '\0';
    5254:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5257:	31 c0                	xor    %eax,%eax
    5259:	c3                   	ret
    525a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5260:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5265:	c3                   	ret
    5266:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005270 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    5270:	f3 0f 1e fa          	endbr64
    5274:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    527b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    527f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5288:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5290:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5292:	49 89 e2             	mov    %rsp,%r10
    5295:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    529d:	4c 89 d0             	mov    %r10,%rax
    52a0:	eb 13                	jmp    52b5 <handle_client_request+0x45>
    52a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    52a8:	48 83 c0 01          	add    $0x1,%rax
    52ac:	48 83 c1 01          	add    $0x1,%rcx
    52b0:	4c 39 c8             	cmp    %r9,%rax
    52b3:	74 4b                	je     5300 <handle_client_request+0x90>
        dest[i] = src[i];
    52b5:	44 0f b6 01          	movzbl (%rcx),%r8d
    52b9:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    52bc:	41 80 f8 0d          	cmp    $0xd,%r8b
    52c0:	75 e6                	jne    52a8 <handle_client_request+0x38>
    52c2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    52c6:	75 e0                	jne    52a8 <handle_client_request+0x38>
            dest[i] = '\0';
    52c8:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    52cb:	8b 47 08             	mov    0x8(%rdi),%eax
    52ce:	48 89 f2             	mov    %rsi,%rdx
    52d1:	4c 89 d7             	mov    %r10,%rdi
    52d4:	89 c6                	mov    %eax,%esi
    52d6:	e8 75 fe ff ff       	call   5150 <handle_http_method>
}
    52db:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    52e3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    52ec:	75 39                	jne    5327 <handle_client_request+0xb7>
    52ee:	31 c0                	xor    %eax,%eax
    52f0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    52f7:	c3                   	ret
    52f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5300:	48 8b 0d 19 4d 00 00 	mov    0x4d19(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5307:	ba 12 00 00 00       	mov    $0x12,%edx
    530c:	be 01 00 00 00       	mov    $0x1,%esi
    5311:	48 8d 3d 40 1e 00 00 	lea    0x1e40(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    5318:	e8 03 d2 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    531d:	bf 01 00 00 00       	mov    $0x1,%edi
    5322:	e8 d9 d1 ff ff       	call   2500 <exit@plt>
}
    5327:	e8 44 d0 ff ff       	call   2370 <__stack_chk_fail@plt>
    532c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005330 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5330:	f3 0f 1e fa          	endbr64
    5334:	55                   	push   %rbp
    5335:	53                   	push   %rbx
    5336:	48 89 cb             	mov    %rcx,%rbx
    5339:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    533d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5340:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5343:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5349:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    534c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    534f:	f6 c1 02             	test   $0x2,%cl
    5352:	74 00                	je     5354 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    5354:	41 89 c0             	mov    %eax,%r8d
    5357:	45 29 c8             	sub    %r9d,%r8d
    535a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    535e:	0f 82 88 d2 ff ff    	jb     25ec <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5364:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5367:	8b 6b 44             	mov    0x44(%rbx),%ebp
    536a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    536d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5370:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5373:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5377:	d3 e5                	shl    %cl,%ebp
    5379:	48 c1 e5 06          	shl    $0x6,%rbp
    537d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5381:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5384:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5389:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5390:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5394:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5398:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    53a0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    53a8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    53ac:	e8 af d0 ff ff       	call   2460 <malloc@plt>
  io_uring_submit(ring);
    53b1:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    53b4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    53ba:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    53be:	48 83 c4 08          	add    $0x8,%rsp
    53c2:	5b                   	pop    %rbx
    53c3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    53c4:	e9 b7 cf ff ff       	jmp    2380 <io_uring_submit@plt>
    53c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000053d0 <io_thread>:
void* io_thread(void *arg) {
    53d0:	f3 0f 1e fa          	endbr64
    53d4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    53d6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    53d8:	41 56                	push   %r14
    53da:	41 55                	push   %r13
    53dc:	41 54                	push   %r12
    53de:	55                   	push   %rbp
    53df:	48 89 fd             	mov    %rdi,%rbp
    53e2:	53                   	push   %rbx
    53e3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    53ea:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    53f3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    53fb:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    53ff:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5404:	bf 00 01 00 00       	mov    $0x100,%edi
    5409:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    540c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5410:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5415:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    541a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    541f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5424:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    542c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5431:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5439:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    543e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5446:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    544b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5453:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5458:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5460:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5465:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    546d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5475:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    547d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5485:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    548d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5495:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    549d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    54a5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    54ad:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    54b5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    54bd:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    54c4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    54cc:	e8 6f cf ff ff       	call   2440 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    54d1:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    54d5:	31 f6                	xor    %esi,%esi
    54d7:	e8 64 d0 ff ff       	call   2540 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    54dc:	31 d2                	xor    %edx,%edx
    54de:	be 01 00 00 00       	mov    $0x1,%esi
    54e3:	bf 02 00 00 00       	mov    $0x2,%edi
    54e8:	e8 a3 d0 ff ff       	call   2590 <socket@plt>
  if (sock == -1)
    54ed:	83 f8 ff             	cmp    $0xffffffff,%eax
    54f0:	0f 84 38 d1 ff ff    	je     262e <io_thread.cold+0x38>
  if (setsockopt(sock,
    54f6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    54fb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5501:	89 c7                	mov    %eax,%edi
    5503:	41 89 c4             	mov    %eax,%r12d
    5506:	ba 02 00 00 00       	mov    $0x2,%edx
    550b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5510:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5518:	e8 13 ce ff ff       	call   2330 <setsockopt@plt>
    551d:	85 c0                	test   %eax,%eax
    551f:	0f 88 dd d0 ff ff    	js     2602 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5525:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    552a:	ba 10 00 00 00       	mov    $0x10,%edx
    552f:	44 89 e7             	mov    %r12d,%edi
    5532:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    553b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5543:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    554b:	e8 60 cf ff ff       	call   24b0 <bind@plt>
    5550:	85 c0                	test   %eax,%eax
    5552:	0f 88 e2 d0 ff ff    	js     263a <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5558:	be 0a 00 00 00       	mov    $0xa,%esi
    555d:	44 89 e7             	mov    %r12d,%edi
    5560:	e8 0b cf ff ff       	call   2470 <listen@plt>
    5565:	85 c0                	test   %eax,%eax
    5567:	0f 88 a1 d0 ff ff    	js     260e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    556d:	ba db 18 00 00       	mov    $0x18db,%edx
    5572:	48 8d 35 24 1c 00 00 	lea    0x1c24(%rip),%rsi        # 719d <_IO_stdin_used+0x19d>
    5579:	bf 01 00 00 00       	mov    $0x1,%edi
    557e:	31 c0                	xor    %eax,%eax
    5580:	e8 1b cf ff ff       	call   24a0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5585:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    558a:	48 89 d9             	mov    %rbx,%rcx
    558d:	44 89 e7             	mov    %r12d,%edi
    5590:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5595:	48 89 c6             	mov    %rax,%rsi
    5598:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    559d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    55a2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    55aa:	e8 81 fd ff ff       	call   5330 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    55af:	bf 01 00 00 00       	mov    $0x1,%edi
    55b4:	be 10 00 00 00       	mov    $0x10,%esi
    55b9:	e8 32 ce ff ff       	call   23f0 <calloc@plt>
    void *buf = malloc(size);
    55be:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    55c3:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    55c6:	e8 95 ce ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    55cb:	48 85 c0             	test   %rax,%rax
    55ce:	0f 84 ae 04 00 00    	je     5a82 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    55d4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    55d8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    55df:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    55e6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    55ee:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    55f1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    55f6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    55f8:	f6 c1 02             	test   $0x2,%cl
    55fb:	0f 85 0f 04 00 00    	jne    5a10 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5601:	89 d0                	mov    %edx,%eax
    5603:	29 f0                	sub    %esi,%eax
    5605:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    560c:	0f 82 12 d0 ff ff    	jb     2624 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5612:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5615:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5619:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    561d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5620:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5627:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    562a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5631:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5638:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    563a:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    563d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5642:	48 c1 e0 06          	shl    $0x6,%rax
    5646:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    564e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5654:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5657:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    565f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5663:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    566b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5673:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5677:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    567b:	e8 00 cd ff ff       	call   2380 <io_uring_submit@plt>
  while (data->running == 1) {
    5680:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5684:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5689:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5691:	0f 85 d7 01 00 00    	jne    586e <io_thread+0x49e>
    5697:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    569c:	4d 89 ce             	mov    %r9,%r14
    569f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    56a4:	0f 1f 40 00          	nopl   0x0(%rax)
    56a8:	48 8d 3d 04 1b 00 00 	lea    0x1b04(%rip),%rdi        # 71b3 <_IO_stdin_used+0x1b3>
    56af:	e8 6c cc ff ff       	call   2320 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    56b4:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    56bb:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    56c2:	c1 e9 0b             	shr    $0xb,%ecx
    56c5:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    56c8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    56d0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    56d2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    56da:	8b 16                	mov    (%rsi),%edx
		if (!available)
    56dc:	39 d0                	cmp    %edx,%eax
    56de:	74 36                	je     5716 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    56e0:	89 f8                	mov    %edi,%eax
    56e2:	21 d0                	and    %edx,%eax
    56e4:	d3 e0                	shl    %cl,%eax
    56e6:	48 c1 e0 04          	shl    $0x4,%rax
    56ea:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    56f2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    56fa:	0f 85 a8 01 00 00    	jne    58a8 <io_thread+0x4d8>
    5700:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5704:	0f 85 0e 03 00 00    	jne    5a18 <io_thread+0x648>
			if (cqe->res < 0)
    570a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    570d:	83 c2 01             	add    $0x1,%edx
    5710:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5712:	85 c0                	test   %eax,%eax
    5714:	79 b2                	jns    56c8 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5716:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    571f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5720:	45 31 c0             	xor    %r8d,%r8d
    5723:	31 d2                	xor    %edx,%edx
    5725:	b9 01 00 00 00       	mov    $0x1,%ecx
    572a:	4c 89 f6             	mov    %r14,%rsi
    572d:	48 89 df             	mov    %rbx,%rdi
    5730:	e8 5b cd ff ff       	call   2490 <__io_uring_get_cqe@plt>
    5735:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5738:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    573d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5741:	0f 84 e1 02 00 00    	je     5a28 <io_thread+0x658>
    5747:	48 8d 3d 8b 1a 00 00 	lea    0x1a8b(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    574e:	e8 cd cb ff ff       	call   2320 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5753:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5758:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    575b:	45 85 ff             	test   %r15d,%r15d
    575e:	0f 88 92 ce ff ff    	js     25f6 <io_thread.cold>
      if (cqe->res < 0) {
    5764:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5767:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    576b:	85 c0                	test   %eax,%eax
    576d:	0f 88 d5 02 00 00    	js     5a48 <io_thread+0x678>
      switch (req->event_type) {
    5773:	41 83 f8 01          	cmp    $0x1,%r8d
    5777:	0f 84 7b 01 00 00    	je     58f8 <io_thread+0x528>
    577d:	41 83 f8 02          	cmp    $0x2,%r8d
    5781:	0f 84 a1 01 00 00    	je     5928 <io_thread+0x558>
    5787:	45 85 c0             	test   %r8d,%r8d
    578a:	0f 85 50 01 00 00    	jne    58e0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5790:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5795:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    579a:	48 89 d9             	mov    %rbx,%rcx
    579d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    57a1:	e8 8a fb ff ff       	call   5330 <add_accept_request>
              add_read_request(cqe->res, &ring);
    57a6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    57ab:	48 89 de             	mov    %rbx,%rsi
    57ae:	8b 78 08             	mov    0x8(%rax),%edi
    57b1:	e8 1a f5 ff ff       	call   4cd0 <add_read_request>
              free(req);
    57b6:	4c 89 e7             	mov    %r12,%rdi
    57b9:	e8 32 cb ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    57be:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    57c3:	48 85 c0             	test   %rax,%rax
    57c6:	0f 85 14 01 00 00    	jne    58e0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    57cc:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    57d3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    57da:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    57dd:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    57e2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    57e4:	f6 c1 02             	test   $0x2,%cl
    57e7:	74 00                	je     57e9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    57e9:	89 d0                	mov    %edx,%eax
    57eb:	29 f0                	sub    %esi,%eax
    57ed:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    57f4:	0f 82 20 ce ff ff    	jb     261a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    57fa:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    57fd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5802:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5806:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5809:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5810:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5813:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    581a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5821:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5823:	8b 55 60             	mov    0x60(%rbp),%edx
    5826:	48 c1 e0 06          	shl    $0x6,%rax
    582a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5832:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5838:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    583b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5843:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5847:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    584f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5857:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    585b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    585f:	e8 1c cb ff ff       	call   2380 <io_uring_submit@plt>
  while (data->running == 1) {
    5864:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5868:	0f 84 3a fe ff ff    	je     56a8 <io_thread+0x2d8>
    586e:	48 8d 3d 9d 19 00 00 	lea    0x199d(%rip),%rdi        # 7212 <_IO_stdin_used+0x212>
    5875:	e8 a6 ca ff ff       	call   2320 <puts@plt>
}
    587a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5882:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    588b:	0f 85 18 02 00 00    	jne    5aa9 <io_thread+0x6d9>
    5891:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5898:	31 c0                	xor    %eax,%eax
    589a:	5b                   	pop    %rbx
    589b:	5d                   	pop    %rbp
    589c:	41 5c                	pop    %r12
    589e:	41 5d                	pop    %r13
    58a0:	41 5e                	pop    %r14
    58a2:	41 5f                	pop    %r15
    58a4:	c3                   	ret
    58a5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    58a8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    58ad:	48 85 c0             	test   %rax,%rax
    58b0:	0f 84 6a fe ff ff    	je     5720 <io_thread+0x350>
      if (cqe->user_data == 1) {
    58b6:	48 83 38 01          	cmpq   $0x1,(%rax)
    58ba:	0f 84 68 01 00 00    	je     5a28 <io_thread+0x658>
    58c0:	48 8d 3d 12 19 00 00 	lea    0x1912(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    58c7:	e8 54 ca ff ff       	call   2320 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    58cc:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    58d1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    58d4:	e9 8b fe ff ff       	jmp    5764 <io_thread+0x394>
    58d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    58e0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    58e8:	8b 02                	mov    (%rdx),%eax
    58ea:	83 c0 01             	add    $0x1,%eax
    58ed:	89 02                	mov    %eax,(%rdx)
}
    58ef:	e9 d8 fe ff ff       	jmp    57cc <io_thread+0x3fc>
    58f4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    58f8:	85 c0                	test   %eax,%eax
    58fa:	75 74                	jne    5970 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    58fc:	48 8b 0d 1d 47 00 00 	mov    0x471d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5903:	ba 0f 00 00 00       	mov    $0xf,%edx
    5908:	be 01 00 00 00       	mov    $0x1,%esi
    590d:	48 8d 3d ee 18 00 00 	lea    0x18ee(%rip),%rdi        # 7202 <_IO_stdin_used+0x202>
    5914:	e8 07 cc ff ff       	call   2520 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5919:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    591e:	e9 a0 fe ff ff       	jmp    57c3 <io_thread+0x3f3>
    5923:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5928:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    592d:	45 31 ff             	xor    %r15d,%r15d
    5930:	85 c0                	test   %eax,%eax
    5932:	7e 20                	jle    5954 <io_thread+0x584>
    5934:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5938:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    593b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    593f:	48 c1 e0 04          	shl    $0x4,%rax
    5943:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5948:	e8 a3 c9 ff ff       	call   22f0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    594d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5952:	7f e4                	jg     5938 <io_thread+0x568>
              close(req->client_socket);
    5954:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5959:	e8 62 ca ff ff       	call   23c0 <close@plt>
              free(req);
    595e:	4c 89 e7             	mov    %r12,%rdi
    5961:	e8 8a c9 ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5966:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    596b:	e9 53 fe ff ff       	jmp    57c3 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5970:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5975:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    597a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5982:	eb 11                	jmp    5995 <io_thread+0x5c5>
    5984:	0f 1f 40 00          	nopl   0x0(%rax)
    5988:	48 83 c0 01          	add    $0x1,%rax
    598c:	48 83 c2 01          	add    $0x1,%rdx
    5990:	48 39 c6             	cmp    %rax,%rsi
    5993:	74 4b                	je     59e0 <io_thread+0x610>
        dest[i] = src[i];
    5995:	0f b6 0a             	movzbl (%rdx),%ecx
    5998:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    599a:	80 f9 0d             	cmp    $0xd,%cl
    599d:	75 e9                	jne    5988 <io_thread+0x5b8>
    599f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    59a3:	75 e3                	jne    5988 <io_thread+0x5b8>
            dest[i] = '\0';
    59a5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    59a8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    59ad:	48 89 da             	mov    %rbx,%rdx
    59b0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    59b5:	e8 96 f7 ff ff       	call   5150 <handle_http_method>
              free(req->iov[0].iov_base);
    59ba:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    59bf:	e8 2c c9 ff ff       	call   22f0 <free@plt>
              free(req);
    59c4:	4c 89 e7             	mov    %r12,%rdi
    59c7:	e8 24 c9 ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    59cc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    59d1:	e9 ed fd ff ff       	jmp    57c3 <io_thread+0x3f3>
    59d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    59e0:	48 8b 0d 39 46 00 00 	mov    0x4639(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    59e7:	ba 12 00 00 00       	mov    $0x12,%edx
    59ec:	be 01 00 00 00       	mov    $0x1,%esi
    59f1:	48 8d 3d 60 17 00 00 	lea    0x1760(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    59f8:	e8 23 cb ff ff       	call   2520 <fwrite@plt>
        exit(1);
    59fd:	bf 01 00 00 00       	mov    $0x1,%edi
    5a02:	e8 f9 ca ff ff       	call   2500 <exit@plt>
    5a07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5a10:	e9 ec fb ff ff       	jmp    5601 <io_thread+0x231>
    5a15:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5a18:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    5a1d:	e9 94 fe ff ff       	jmp    58b6 <io_thread+0x4e6>
    5a22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5a28:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5a30:	48 8d 3d 8e 17 00 00 	lea    0x178e(%rip),%rdi        # 71c5 <_IO_stdin_used+0x1c5>
    5a37:	8b 02                	mov    (%rdx),%eax
    5a39:	83 c0 01             	add    $0x1,%eax
    5a3c:	89 02                	mov    %eax,(%rdx)
    5a3e:	e8 dd c8 ff ff       	call   2320 <puts@plt>
    5a43:	e9 26 fe ff ff       	jmp    586e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5a48:	f7 d8                	neg    %eax
    5a4a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5a4f:	89 c7                	mov    %eax,%edi
    5a51:	e8 0a cb ff ff       	call   2560 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5a56:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5a5b:	be 01 00 00 00       	mov    $0x1,%esi
    5a60:	48 8b 3d b9 45 00 00 	mov    0x45b9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5a67:	48 89 c1             	mov    %rax,%rcx
    5a6a:	48 8d 15 67 1b 00 00 	lea    0x1b67(%rip),%rdx        # 75d8 <_IO_stdin_used+0x5d8>
    5a71:	31 c0                	xor    %eax,%eax
    5a73:	e8 b8 ca ff ff       	call   2530 <__fprintf_chk@plt>
          exit(1);
    5a78:	bf 01 00 00 00       	mov    $0x1,%edi
    5a7d:	e8 7e ca ff ff       	call   2500 <exit@plt>
    5a82:	48 8b 0d 97 45 00 00 	mov    0x4597(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5a89:	ba 28 00 00 00       	mov    $0x28,%edx
    5a8e:	be 01 00 00 00       	mov    $0x1,%esi
    5a93:	48 8d 3d 0e 1b 00 00 	lea    0x1b0e(%rip),%rdi        # 75a8 <_IO_stdin_used+0x5a8>
    5a9a:	e8 81 ca ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5a9f:	bf 01 00 00 00       	mov    $0x1,%edi
    5aa4:	e8 57 ca ff ff       	call   2500 <exit@plt>
}
    5aa9:	e8 c2 c8 ff ff       	call   2370 <__stack_chk_fail@plt>
    5aae:	66 90                	xchg   %ax,%ax

0000000000005ab0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5ab0:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5ab4:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5abb:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5ac1:	85 c9                	test   %ecx,%ecx
    5ac3:	0f 8e ea 00 00 00    	jle    5bb3 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    5ac9:	41 56                	push   %r14
    5acb:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5acd:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    5ad0:	41 54                	push   %r12
    5ad2:	49 89 fc             	mov    %rdi,%r12
    5ad5:	55                   	push   %rbp
    5ad6:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5ad7:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5adb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5ae0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    5ae4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    5aec:	31 db                	xor    %ebx,%ebx
    5aee:	8b 10                	mov    (%rax),%edx
    5af0:	85 d2                	test   %edx,%edx
    5af2:	7e 26                	jle    5b1a <barriered_work_ingest+0x6a>
    5af4:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    5af8:	48 89 dd             	mov    %rbx,%rbp
    5afb:	48 c1 e5 08          	shl    $0x8,%rbp
    5aff:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    5b03:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    5b0a:	74 24                	je     5b30 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5b0c:	48 83 c3 01          	add    $0x1,%rbx
    5b10:	39 da                	cmp    %ebx,%edx
    5b12:	7f e4                	jg     5af8 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5b14:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5b1a:	49 83 c5 01          	add    $0x1,%r13
    5b1e:	44 39 e9             	cmp    %r13d,%ecx
    5b21:	7f bd                	jg     5ae0 <barriered_work_ingest+0x30>
}
    5b23:	5b                   	pop    %rbx
    5b24:	31 c0                	xor    %eax,%eax
    5b26:	5d                   	pop    %rbp
    5b27:	41 5c                	pop    %r12
    5b29:	41 5d                	pop    %r13
    5b2b:	41 5e                	pop    %r14
    5b2d:	c3                   	ret
    5b2e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    5b30:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5b39:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5b40:	bf 04 00 00 00       	mov    $0x4,%edi
    5b45:	48 c1 e6 05          	shl    $0x5,%rsi
    5b49:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5b50:	48 83 c6 10          	add    $0x10,%rsi
    5b54:	e8 e7 c7 ff ff       	call   2340 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5b59:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5b61:	48 8b 40 50          	mov    0x50(%rax),%rax
    5b65:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5b69:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    5b6d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5b77:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    5b7d:	83 c0 01             	add    $0x1,%eax
    5b80:	99                   	cltd
    5b81:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5b87:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    5b8d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5b90:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5b98:	48 83 c3 01          	add    $0x1,%rbx
    5b9c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5ba0:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5ba4:	8b 10                	mov    (%rax),%edx
    5ba6:	39 da                	cmp    %ebx,%edx
    5ba8:	0f 8f 46 ff ff ff    	jg     5af4 <barriered_work_ingest+0x44>
    5bae:	e9 61 ff ff ff       	jmp    5b14 <barriered_work_ingest+0x64>
}
    5bb3:	31 c0                	xor    %eax,%eax
    5bb5:	c3                   	ret
    5bb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005bc0 <barriered_thread>:
void* barriered_thread(void *arg) {
    5bc0:	f3 0f 1e fa          	endbr64
    5bc4:	41 56                	push   %r14
    5bc6:	41 55                	push   %r13
    5bc8:	41 54                	push   %r12
  int t = 0;
    5bca:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    5bcd:	55                   	push   %rbp
  int waiting = 0;
    5bce:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    5bd0:	53                   	push   %rbx
    5bd1:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    5bd4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5bd8:	0f 85 74 02 00 00    	jne    5e52 <barriered_thread+0x292>
    if (t >= data->task_count) {
    5bde:	8b 43 40             	mov    0x40(%rbx),%eax
    5be1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5be8:	41 39 c4             	cmp    %eax,%r12d
    5beb:	0f 8d 6f 01 00 00    	jge    5d60 <barriered_thread+0x1a0>
    5bf1:	49 63 fc             	movslq %r12d,%rdi
    5bf4:	48 c1 e7 09          	shl    $0x9,%rdi
    5bf8:	49 89 fd             	mov    %rdi,%r13
    5bfb:	eb 32                	jmp    5c2f <barriered_thread+0x6f>
    5bfd:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5c00:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5c04:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5c08:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5c0c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5c10:	4c 01 ef             	add    %r13,%rdi
    5c13:	e8 98 fe ff ff       	call   5ab0 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    5c18:	8b 43 40             	mov    0x40(%rbx),%eax
    5c1b:	41 83 c4 01          	add    $0x1,%r12d
    5c1f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    5c26:	44 39 e0             	cmp    %r12d,%eax
    5c29:	0f 8e 19 02 00 00    	jle    5e48 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    5c2f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5c33:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    5c37:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    5c3e:	75 c0                	jne    5c00 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5c40:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    5c44:	83 e8 01             	sub    $0x1,%eax
    5c47:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    5c4c:	45 85 e4             	test   %r12d,%r12d
    5c4f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5c52:	45 85 c0             	test   %r8d,%r8d
    5c55:	0f 8e 2d 01 00 00    	jle    5d88 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5c5b:	48 63 c8             	movslq %eax,%rcx
    5c5e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5c62:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5c65:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5c6b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    5c72:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    5c76:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    5c79:	45 31 f6             	xor    %r14d,%r14d
    5c7c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5c80:	48 8b 10             	mov    (%rax),%rdx
    5c83:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    5c87:	49 01 cb             	add    %rcx,%r11
    5c8a:	4c 89 da             	mov    %r11,%rdx
    5c8d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    5c94:	75 04                	jne    5c9a <barriered_thread+0xda>
            arrived++;
    5c96:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5c9a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    5ca0:	75 04                	jne    5ca6 <barriered_thread+0xe6>
            prearrive++;
    5ca2:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5ca6:	48 83 c0 08          	add    $0x8,%rax
    5caa:	48 39 c6             	cmp    %rax,%rsi
    5cad:	75 d1                	jne    5c80 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    5caf:	45 85 d2             	test   %r10d,%r10d
    5cb2:	0f 84 c0 00 00 00    	je     5d78 <barriered_thread+0x1b8>
    5cb8:	45 39 d0             	cmp    %r10d,%r8d
    5cbb:	0f 84 b7 00 00 00    	je     5d78 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    5cc1:	45 85 f6             	test   %r14d,%r14d
    5cc4:	74 0a                	je     5cd0 <barriered_thread+0x110>
    5cc6:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    5cca:	0f 85 ae 01 00 00    	jne    5e7e <barriered_thread+0x2be>
    5cd0:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    5cd4:	4c 01 ea             	add    %r13,%rdx
    5cd7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    5cde:	45 85 e4             	test   %r12d,%r12d
    5ce1:	75 14                	jne    5cf7 <barriered_thread+0x137>
    5ce3:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5cea:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5cf1:	0f 8c 69 01 00 00    	jl     5e60 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5cf7:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    5cfb:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    5cff:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5d09:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    5d0d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5d11:	4c 01 ef             	add    %r13,%rdi
    5d14:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    5d1a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    5d1e:	4c 01 e8             	add    %r13,%rax
    5d21:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5d28:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    5d2b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5d30:	83 e8 01             	sub    $0x1,%eax
    5d33:	44 39 e0             	cmp    %r12d,%eax
    5d36:	0f 84 a4 00 00 00    	je     5de0 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    5d3c:	0f ae f8             	sfence
          if (waiting == 0) {
    5d3f:	85 ed                	test   %ebp,%ebp
    5d41:	0f 84 d1 00 00 00    	je     5e18 <barriered_thread+0x258>
        int arrived = 0; 
    5d47:	bd 01 00 00 00       	mov    $0x1,%ebp
    5d4c:	e9 c7 fe ff ff       	jmp    5c18 <barriered_thread+0x58>
  while (data->running == 1) {
    5d51:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5d55:	0f 85 f7 00 00 00    	jne    5e52 <barriered_thread+0x292>
    5d5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    5d60:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    5d68:	85 c0                	test   %eax,%eax
    5d6a:	7e e5                	jle    5d51 <barriered_thread+0x191>
    5d6c:	45 31 e4             	xor    %r12d,%r12d
    5d6f:	e9 7d fe ff ff       	jmp    5bf1 <barriered_thread+0x31>
    5d74:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5d78:	83 fd 01             	cmp    $0x1,%ebp
    5d7b:	74 1b                	je     5d98 <barriered_thread+0x1d8>
        int arrived = 0; 
    5d7d:	31 ed                	xor    %ebp,%ebp
    5d7f:	e9 3d ff ff ff       	jmp    5cc1 <barriered_thread+0x101>
    5d84:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5d88:	83 fd 01             	cmp    $0x1,%ebp
    5d8b:	0f 85 43 ff ff ff    	jne    5cd4 <barriered_thread+0x114>
        int arrived = 0; 
    5d91:	45 31 f6             	xor    %r14d,%r14d
    5d94:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5d98:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5d9f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    5da4:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5da6:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5daa:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5db1:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    5db6:	e8 85 c5 ff ff       	call   2340 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    5dbb:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5dc2:	48 83 c0 01          	add    $0x1,%rax
    5dc6:	48 99                	cqto
    5dc8:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    5dcf:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    5dd6:	e9 e6 fe ff ff       	jmp    5cc1 <barriered_thread+0x101>
    5ddb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5de0:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5de7:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5dee:	0f 8d 48 ff ff ff    	jge    5d3c <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    5df4:	48 c1 e6 04          	shl    $0x4,%rsi
    5df8:	bf 04 00 00 00       	mov    $0x4,%edi
    5dfd:	48 03 73 70          	add    0x70(%rbx),%rsi
    5e01:	e8 3a c5 ff ff       	call   2340 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    5e06:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    5e0e:	e9 29 ff ff ff       	jmp    5d3c <barriered_thread+0x17c>
    5e13:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    5e18:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5e1f:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    5e24:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5e28:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5e2f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5e33:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5e37:	e8 04 c5 ff ff       	call   2340 <clock_gettime@plt>
            waiting = 1;
    5e3c:	e9 06 ff ff ff       	jmp    5d47 <barriered_thread+0x187>
    5e41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    5e48:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5e4c:	0f 84 96 fd ff ff    	je     5be8 <barriered_thread+0x28>
}
    5e52:	5b                   	pop    %rbx
    5e53:	31 c0                	xor    %eax,%eax
    5e55:	5d                   	pop    %rbp
    5e56:	41 5c                	pop    %r12
    5e58:	41 5d                	pop    %r13
    5e5a:	41 5e                	pop    %r14
    5e5c:	c3                   	ret
    5e5d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    5e60:	48 c1 e6 04          	shl    $0x4,%rsi
    5e64:	bf 04 00 00 00       	mov    $0x4,%edi
    5e69:	48 03 73 68          	add    0x68(%rbx),%rsi
    5e6d:	e8 ce c4 ff ff       	call   2340 <clock_gettime@plt>
          data->tasks[t].available = 0;
    5e72:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5e76:	4c 01 ea             	add    %r13,%rdx
    5e79:	e9 79 fe ff ff       	jmp    5cf7 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5e7e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5e82:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5e86:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5e8a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5e8e:	4c 01 ef             	add    %r13,%rdi
    5e91:	e8 1a fc ff ff       	call   5ab0 <barriered_work_ingest>
          break;
    5e96:	e9 39 fd ff ff       	jmp    5bd4 <barriered_thread+0x14>
    5e9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005ea0 <receive>:
int receive(struct BarrierTask *data) {
    5ea0:	f3 0f 1e fa          	endbr64
    5ea4:	41 57                	push   %r15
    5ea6:	41 56                	push   %r14
    5ea8:	41 55                	push   %r13
    5eaa:	41 54                	push   %r12
    5eac:	55                   	push   %rbp
    5ead:	53                   	push   %rbx
    5eae:	48 83 ec 18          	sub    $0x18,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5eb2:	44 8b b7 40 01 00 00 	mov    0x140(%rdi),%r14d
    5eb9:	45 85 f6             	test   %r14d,%r14d
    5ebc:	0f 8e 17 01 00 00    	jle    5fd9 <receive+0x139>
    if (n == data->thread->real_thread_index) { continue; }
    5ec2:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5ec9:	48 89 f9             	mov    %rdi,%rcx
    5ecc:	45 31 e4             	xor    %r12d,%r12d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5ecf:	31 db                	xor    %ebx,%ebx
    if (n == data->thread->real_thread_index) { continue; }
    5ed1:	48 63 68 08          	movslq 0x8(%rax),%rbp
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5ed5:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    if (n == data->thread->real_thread_index) { continue; }
    5eda:	49 89 ef             	mov    %rbp,%r15
    5edd:	0f 1f 00             	nopl   (%rax)
    5ee0:	41 39 df             	cmp    %ebx,%r15d
    5ee3:	0f 84 e0 00 00 00    	je     5fc9 <receive+0x129>
    struct Data *me = data->mailboxes[n].lower;
    5ee9:	48 8b 81 70 01 00 00 	mov    0x170(%rcx),%rax
    5ef0:	4c 01 e0             	add    %r12,%rax
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    5ef3:	44 8b 68 30          	mov    0x30(%rax),%r13d
    struct Data *me = data->mailboxes[n].lower;
    5ef7:	48 8b 10             	mov    (%rax),%rdx
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    5efa:	41 83 fd 02          	cmp    $0x2,%r13d
    5efe:	0f 84 24 01 00 00    	je     6028 <receive+0x188>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5f04:	48 83 ba 80 00 00 00 00 	cmpq   $0x0,0x80(%rdx)
    5f0c:	0f 8e 3b 01 00 00    	jle    604d <receive+0x1ad>
      data->sends++;
    5f12:	4c 8b 81 78 01 00 00 	mov    0x178(%rcx),%r8
      data->n++;
    5f19:	48 8b b9 08 01 00 00 	mov    0x108(%rcx),%rdi
      me->received++;
    5f20:	31 c0                	xor    %eax,%eax
    5f22:	48 8b b2 10 03 00 00 	mov    0x310(%rdx),%rsi
      if (me->messages[x]->group == data->group) {
    5f29:	4c 8b 1a             	mov    (%rdx),%r11
    5f2c:	4d 8d 48 01          	lea    0x1(%r8),%r9
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5f30:	4c 63 51 04          	movslq 0x4(%rcx),%r10
    5f34:	4c 8d 47 01          	lea    0x1(%rdi),%r8
    5f38:	48 8d 7e 01          	lea    0x1(%rsi),%rdi
    5f3c:	eb 0f                	jmp    5f4d <receive+0xad>
    5f3e:	66 90                	xchg   %ax,%ax
    for (int x = 0 ; x < me->messages_count ; x++) {
    5f40:	48 83 c0 01          	add    $0x1,%rax
    5f44:	48 39 82 80 00 00 00 	cmp    %rax,0x80(%rdx)
    5f4b:	7e 6b                	jle    5fb8 <receive+0x118>
      data->sends++;
    5f4d:	49 8d 34 01          	lea    (%r9,%rax,1),%rsi
    5f51:	48 89 b1 78 01 00 00 	mov    %rsi,0x178(%rcx)
      data->n++;
    5f58:	49 8d 34 00          	lea    (%r8,%rax,1),%rsi
    5f5c:	48 89 b1 08 01 00 00 	mov    %rsi,0x108(%rcx)
      me->received++;
    5f63:	48 8d 34 07          	lea    (%rdi,%rax,1),%rsi
    5f67:	48 89 b2 10 03 00 00 	mov    %rsi,0x310(%rdx)
      if (me->messages[x]->group == data->group) {
    5f6e:	49 8b 34 c3          	mov    (%r11,%rax,8),%rsi
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5f72:	4c 39 56 10          	cmp    %r10,0x10(%rsi)
    5f76:	75 c8                	jne    5f40 <receive+0xa0>
    5f78:	48 39 6e 08          	cmp    %rbp,0x8(%rsi)
    5f7c:	75 c2                	jne    5f40 <receive+0xa0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    5f7e:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5f83:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5f85:	bf 01 00 00 00       	mov    $0x1,%edi
    5f8a:	ba 01 00 00 00       	mov    $0x1,%edx
    5f8f:	48 8d 35 6a 16 00 00 	lea    0x166a(%rip),%rsi        # 7600 <_IO_stdin_used+0x600>
    5f96:	48 63 40 04          	movslq 0x4(%rax),%rax
    5f9a:	48 39 e8             	cmp    %rbp,%rax
    5f9d:	0f 94 c1             	sete   %cl
    5fa0:	31 c0                	xor    %eax,%eax
    5fa2:	e8 f9 c4 ff ff       	call   24a0 <__printf_chk@plt>
        exit(1);
    5fa7:	bf 01 00 00 00       	mov    $0x1,%edi
    5fac:	e8 4f c5 ff ff       	call   2500 <exit@plt>
    5fb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    me->messages_count = 0;
    5fb8:	48 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rdx)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    5fc3:	41 83 fd 02          	cmp    $0x2,%r13d
    5fc7:	74 27                	je     5ff0 <receive+0x150>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5fc9:	83 c3 01             	add    $0x1,%ebx
    5fcc:	49 83 c4 38          	add    $0x38,%r12
    5fd0:	44 39 f3             	cmp    %r14d,%ebx
    5fd3:	0f 85 07 ff ff ff    	jne    5ee0 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    5fd9:	0f ae f8             	sfence
}
    5fdc:	48 83 c4 18          	add    $0x18,%rsp
    5fe0:	31 c0                	xor    %eax,%eax
    5fe2:	5b                   	pop    %rbx
    5fe3:	5d                   	pop    %rbp
    5fe4:	41 5c                	pop    %r12
    5fe6:	41 5d                	pop    %r13
    5fe8:	41 5e                	pop    %r14
    5fea:	41 5f                	pop    %r15
    5fec:	c3                   	ret
    5fed:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    5ff0:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    5ff6:	83 f8 01             	cmp    $0x1,%eax
    5ff9:	75 ce                	jne    5fc9 <receive+0x129>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5ffb:	83 c3 01             	add    $0x1,%ebx
    5ffe:	49 83 c4 38          	add    $0x38,%r12
      me->available_reading = 0;
    6002:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    600c:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6016:	44 39 f3             	cmp    %r14d,%ebx
    6019:	0f 85 c1 fe ff ff    	jne    5ee0 <receive+0x40>
    601f:	eb b8                	jmp    5fd9 <receive+0x139>
    6021:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    6028:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    602e:	85 c0                	test   %eax,%eax
    6030:	74 97                	je     5fc9 <receive+0x129>
    for (int x = 0 ; x < me->messages_count ; x++) {
    6032:	48 83 ba 80 00 00 00 00 	cmpq   $0x0,0x80(%rdx)
    603a:	0f 8f d2 fe ff ff    	jg     5f12 <receive+0x72>
    me->messages_count = 0;
    6040:	48 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rdx)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    604b:	eb a9                	jmp    5ff6 <receive+0x156>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    604d:	83 c3 01             	add    $0x1,%ebx
    6050:	49 83 c4 38          	add    $0x38,%r12
    me->messages_count = 0;
    6054:	48 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    605f:	44 39 f3             	cmp    %r14d,%ebx
    6062:	0f 85 78 fe ff ff    	jne    5ee0 <receive+0x40>
    6068:	e9 6c ff ff ff       	jmp    5fd9 <receive+0x139>
    606d:	0f 1f 00             	nopl   (%rax)

0000000000006070 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    6070:	f3 0f 1e fa          	endbr64
    6074:	41 57                	push   %r15
    6076:	49 89 ff             	mov    %rdi,%r15
    6079:	41 56                	push   %r14
    607b:	41 55                	push   %r13
    607d:	41 54                	push   %r12
    607f:	55                   	push   %rbp
    6080:	53                   	push   %rbx
    6081:	48 83 ec 58          	sub    $0x58,%rsp
  if (data->thread_index == data->task_index) {
    6085:	8b 47 04             	mov    0x4(%rdi),%eax
    6088:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    608e:	74 4b                	je     60db <barriered_work+0x6b>
    receive(data);
    6090:	e8 0b fe ff ff       	call   5ea0 <receive>
    while (data->scheduled == 1) {
    6095:	41 83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r15)
    609d:	75 16                	jne    60b5 <barriered_work+0x45>
    609f:	90                   	nop
      data->n++;
    60a0:	49 83 87 08 01 00 00 01 	addq   $0x1,0x108(%r15)
      asm volatile ("sfence" ::: "memory");
    60a8:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    60ab:	41 83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r15)
    60b3:	74 eb                	je     60a0 <barriered_work+0x30>
  if (data->sending == 1) {
    60b5:	41 83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%r15)
    60bd:	75 08                	jne    60c7 <barriered_work+0x57>
    60bf:	4c 89 ff             	mov    %r15,%rdi
    60c2:	e8 19 e2 ff ff       	call   42e0 <sendm.part.0>
  asm volatile ("sfence" ::: "memory");
    60c7:	0f ae f8             	sfence
}
    60ca:	48 83 c4 58          	add    $0x58,%rsp
    60ce:	31 c0                	xor    %eax,%eax
    60d0:	5b                   	pop    %rbx
    60d1:	5d                   	pop    %rbp
    60d2:	41 5c                	pop    %r12
    60d4:	41 5d                	pop    %r13
    60d6:	41 5e                	pop    %r14
    60d8:	41 5f                	pop    %r15
    60da:	c3                   	ret
       receive(data);
    60db:	e8 c0 fd ff ff       	call   5ea0 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    60e0:	41 8b 9f 40 01 00 00 	mov    0x140(%r15),%ebx
        int t = data->task_index;
    60e7:	41 8b 47 04          	mov    0x4(%r15),%eax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    60eb:	89 5c 24 24          	mov    %ebx,0x24(%rsp)
    60ef:	85 db                	test   %ebx,%ebx
    60f1:	0f 8e fa 03 00 00    	jle    64f1 <barriered_work+0x481>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    60f7:	48 63 c8             	movslq %eax,%rcx
              int next_task = abs((t + 1) % (data->thread_count));
    60fa:	83 c0 01             	add    $0x1,%eax
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    60fd:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    6106:	49 8b 9f 28 01 00 00 	mov    0x128(%r15),%rbx
    610d:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
    6116:	48 c1 e1 09          	shl    $0x9,%rcx
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    611a:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
              int next_task = abs((t + 1) % (data->thread_count));
    6122:	89 44 24 48          	mov    %eax,0x48(%rsp)
    6126:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6130:	44 8b 44 24 20       	mov    0x20(%rsp),%r8d
    6135:	44 8b 4c 24 24       	mov    0x24(%rsp),%r9d
int barriered_work(struct BarrierTask *data) {
    613a:	31 f6                	xor    %esi,%esi
    613c:	31 d2                	xor    %edx,%edx
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    613e:	31 c0                	xor    %eax,%eax
    6140:	eb 1d                	jmp    615f <barriered_work+0xef>
    6142:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6148:	83 c0 01             	add    $0x1,%eax
    614b:	48 83 c2 38          	add    $0x38,%rdx
    614f:	48 81 c6 c8 00 00 00 	add    $0xc8,%rsi
    6156:	44 39 c8             	cmp    %r9d,%eax
    6159:	0f 84 71 02 00 00    	je     63d0 <barriered_work+0x360>
              if (y == b) { continue; }
    615f:	41 39 c0             	cmp    %eax,%r8d
    6162:	74 e4                	je     6148 <barriered_work+0xd8>
              int next_task = abs((t + 1) % (data->thread_count));
    6164:	49 63 bf 34 01 00 00 	movslq 0x134(%r15),%rdi
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    616b:	39 43 08             	cmp    %eax,0x8(%rbx)
    616e:	75 d8                	jne    6148 <barriered_work+0xd8>
    6170:	4c 8b 53 20          	mov    0x20(%rbx),%r10
    6174:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    6179:	4d 8b 5c 32 38       	mov    0x38(%r10,%rsi,1),%r11
    617e:	4d 03 a4 0b 70 01 00 00 	add    0x170(%r11,%rcx,1),%r12
    6186:	41 83 7c 24 30 02    	cmpl   $0x2,0x30(%r12)
    618c:	75 ba                	jne    6148 <barriered_work+0xd8>
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    618e:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    6193:	4b 8b 6c 32 38       	mov    0x38(%r10,%r14,1),%rbp
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    6198:	85 ff                	test   %edi,%edi
    619a:	0f 8e 1b 04 00 00    	jle    65bb <barriered_work+0x54b>
                  int all_wrote = 1;
    61a0:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    61a5:	48 c1 e7 09          	shl    $0x9,%rdi
    61a9:	49 89 ee             	mov    %rbp,%r14
    61ac:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    61b2:	48 89 7c 24 10       	mov    %rdi,0x10(%rsp)
    61b7:	4c 8d 6c 3d 00       	lea    0x0(%rbp,%rdi,1),%r13
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    61bc:	48 89 ef             	mov    %rbp,%rdi
    61bf:	90                   	nop
                    if (((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving == 0) {
    61c0:	4c 8b 9f 70 01 00 00 	mov    0x170(%rdi),%r11
    61c7:	4d 8b 5c 13 08       	mov    0x8(%r11,%rdx,1),%r11
                      all_wrote = 0;
    61cc:	45 8b 9b 80 01 00 00 	mov    0x180(%r11),%r11d
    61d3:	45 85 db             	test   %r11d,%r11d
    61d6:	41 bb 00 00 00 00    	mov    $0x0,%r11d
    61dc:	45 0f 44 d3          	cmove  %r11d,%r10d
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    61e0:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    61e7:	4c 39 ef             	cmp    %r13,%rdi
    61ea:	75 d4                	jne    61c0 <barriered_work+0x150>
                  if (all_finished == 1 && all_wrote == 1 /*&& ((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available == 0 */) {
    61ec:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    61f1:	41 83 fa 01          	cmp    $0x1,%r10d
    61f5:	0f 85 4d ff ff ff    	jne    6148 <barriered_work+0xd8>
    61fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                        ((struct Data*)data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving = 0;
    6200:	49 8b be 70 01 00 00 	mov    0x170(%r14),%rdi
                      for (int nn = 0 ; nn < data->thread_count; nn++) {
    6207:	49 81 c6 00 02 00 00 	add    $0x200,%r14
                        ((struct Data*)data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving = 0;
    620e:	48 8b 7c 17 08       	mov    0x8(%rdi,%rdx,1),%rdi
    6213:	c7 87 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rdi)
                      for (int nn = 0 ; nn < data->thread_count; nn++) {
    621d:	4d 39 ee             	cmp    %r13,%r14
    6220:	75 de                	jne    6200 <barriered_work+0x190>
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    6222:	48 8b bc 0d 70 01 00 00 	mov    0x170(%rbp,%rcx,1),%rdi
    622a:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    622f:	89 44 24 40          	mov    %eax,0x40(%rsp)
    6233:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    6238:	48 8b 5c 17 18       	mov    0x18(%rdi,%rdx,1),%rbx
    623d:	49 81 c6 70 01 00 00 	add    $0x170,%r14
                      void * right = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1];
    6244:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    6248:	4c 8b 2b             	mov    (%rbx),%r13
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    624b:	48 89 5c 24 38       	mov    %rbx,0x38(%rsp)
    6250:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
                      void * right = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1];
    6255:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    625a:	49 8b 7c 24 18       	mov    0x18(%r12),%rdi
    625f:	4c 8b 27             	mov    (%rdi),%r12
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    6262:	48 8b 7f 08          	mov    0x8(%rdi),%rdi
    6266:	48 89 7c 24 30       	mov    %rdi,0x30(%rsp)
    626b:	bf 70 01 00 00       	mov    $0x170,%edi
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].lower = data->thread->all_threads[b].tasks[nn].mailboxes[y].higher ;
    6270:	49 8b 0c 3b          	mov    (%r11,%rdi,1),%rcx
                        void * ynnblow = data->thread->all_threads[y].tasks[nn].mailboxes[b].lower;
    6274:	4c 8b 54 3d 00       	mov    0x0(%rbp,%rdi,1),%r10
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6279:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].lower = data->thread->all_threads[b].tasks[nn].mailboxes[y].higher ;
    6280:	48 01 d9             	add    %rbx,%rcx
                        void * ynnblow = data->thread->all_threads[y].tasks[nn].mailboxes[b].lower;
    6283:	49 01 d2             	add    %rdx,%r10
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].lower = data->thread->all_threads[b].tasks[nn].mailboxes[y].higher ;
    6286:	48 8b 41 08          	mov    0x8(%rcx),%rax
                        void * yynnbhigh = data->thread->all_threads[y].tasks[nn].mailboxes[b].higher;
    628a:	f3 41 0f 6f 02       	movdqu (%r10),%xmm0
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].lower = data->thread->all_threads[b].tasks[nn].mailboxes[y].higher ;
    628f:	49 89 02             	mov    %rax,(%r10)
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].higher = data->thread->all_threads[b].tasks[nn].mailboxes[y].lower ;
    6292:	48 8b 01             	mov    (%rcx),%rax
                        void * ynnblow = data->thread->all_threads[y].tasks[nn].mailboxes[b].lower;
    6295:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].higher = data->thread->all_threads[b].tasks[nn].mailboxes[y].lower ;
    629a:	49 89 42 08          	mov    %rax,0x8(%r10)
                        data->thread->all_threads[b].tasks[nn].mailboxes[y].lower = yynnbhigh;
    629e:	0f 11 01             	movups %xmm0,(%rcx)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    62a1:	49 39 fe             	cmp    %rdi,%r14
    62a4:	75 ca                	jne    6270 <barriered_work+0x200>
    62a6:	44 89 44 24 4c       	mov    %r8d,0x4c(%rsp)
    62ab:	8b 44 24 40          	mov    0x40(%rsp),%eax
    62af:	bf 70 01 00 00       	mov    $0x170,%edi
    62b4:	4c 89 6c 24 40       	mov    %r13,0x40(%rsp)
    62b9:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    62be:	66 90                	xchg   %ax,%ax
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_reading = 0;
    62c0:	4d 8b 04 3b          	mov    (%r11,%rdi,1),%r8
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_reading = 0;
    62c4:	48 8b 4c 3d 00       	mov    0x0(%rbp,%rdi,1),%rcx
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_reading = 0;
    62c9:	4d 01 e8             	add    %r13,%r8
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_reading = 0;
    62cc:	48 01 d1             	add    %rdx,%rcx
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_reading = 0;
    62cf:	49 8b 58 08          	mov    0x8(%r8),%rbx
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_reading = 0;
    62d3:	4c 8b 51 08          	mov    0x8(%rcx),%r10
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->available_reading = 1;
    62d7:	4d 8b 00             	mov    (%r8),%r8
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].lower)->available_reading = 1;
    62da:	48 8b 09             	mov    (%rcx),%rcx
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_reading = 0;
    62dd:	c7 83 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rbx)
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_reading = 0;
    62e7:	41 c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%r10)
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->available_reading = 1;
    62f2:	41 c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%r8)
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].lower)->available_reading = 1;
    62fd:	c7 81 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rcx)
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_sending = 1;
    6307:	c7 83 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rbx)
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_sending = 1;
    6311:	41 c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r10)
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    631c:	49 39 c8             	cmp    %rcx,%r8
    631f:	0f 84 c5 02 00 00    	je     65ea <barriered_work+0x57a>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6325:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    632c:	49 39 fe             	cmp    %rdi,%r14
    632f:	75 8f                	jne    62c0 <barriered_work+0x250>
    6331:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6336:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    633b:	4c 8b 6c 24 40       	mov    0x40(%rsp),%r13
    6340:	44 8b 44 24 4c       	mov    0x4c(%rsp),%r8d
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0] = right;
    6345:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0] = right3;
    634a:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0] = right;
    634f:	48 89 3b             	mov    %rdi,(%rbx)
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1] = left;
    6352:	49 8b bf 28 01 00 00 	mov    0x128(%r15),%rdi
    6359:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    635e:	48 8b 7f 20          	mov    0x20(%rdi),%rdi
    6362:	48 8b 7c 1f 38       	mov    0x38(%rdi,%rbx,1),%rdi
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0] = right3;
    6367:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1] = left;
    636c:	48 8b bc 0f 70 01 00 00 	mov    0x170(%rdi,%rcx,1),%rdi
    6374:	48 8b 7c 17 18       	mov    0x18(%rdi,%rdx,1),%rdi
    6379:	4c 89 6f 08          	mov    %r13,0x8(%rdi)
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0] = right3;
    637d:	49 8b bf 28 01 00 00 	mov    0x128(%r15),%rdi
    6384:	48 8b 7f 20          	mov    0x20(%rdi),%rdi
    6388:	48 8b 7c 37 38       	mov    0x38(%rdi,%rsi,1),%rdi
    638d:	48 8b bc 0f 70 01 00 00 	mov    0x170(%rdi,%rcx,1),%rdi
    6395:	48 8b 7c 1f 18       	mov    0x18(%rdi,%rbx,1),%rdi
    639a:	4c 89 37             	mov    %r14,(%rdi)
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1] = left3;
    639d:	49 8b bf 28 01 00 00 	mov    0x128(%r15),%rdi
    63a4:	48 8b 7f 20          	mov    0x20(%rdi),%rdi
    63a8:	48 8b 7c 37 38       	mov    0x38(%rdi,%rsi,1),%rdi
    63ad:	48 8b bc 0f 70 01 00 00 	mov    0x170(%rdi,%rcx,1),%rdi
    63b5:	48 8b 7c 1f 18       	mov    0x18(%rdi,%rbx,1),%rdi
    63ba:	4c 89 67 08          	mov    %r12,0x8(%rdi)
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    63be:	49 8b 9f 28 01 00 00 	mov    0x128(%r15),%rbx
    63c5:	e9 7e fd ff ff       	jmp    6148 <barriered_work+0xd8>
    63ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    63d0:	44 8b 9b c4 00 00 00 	mov    0xc4(%rbx),%r11d
          int k = data->group;
    63d7:	41 8b 87 94 01 00 00 	mov    0x194(%r15),%eax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    63de:	45 85 db             	test   %r11d,%r11d
    63e1:	0f 8e e6 00 00 00    	jle    64cd <barriered_work+0x45d>
            int y = (k * data->thread->threads_per_group) + d;
    63e7:	41 0f af c3          	imul   %r11d,%eax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    63eb:	45 31 d2             	xor    %r10d,%r10d
    63ee:	48 98                	cltq
    63f0:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    63f4:	4c 8d 24 c5 00 00 00 00 	lea    0x0(,%rax,8),%r12
    63fc:	48 8d 14 92          	lea    (%rdx,%rdx,4),%rdx
    6400:	49 29 c4             	sub    %rax,%r12
    6403:	4c 8d 34 d5 00 00 00 00 	lea    0x0(,%rdx,8),%r14
    640b:	49 c1 e4 03          	shl    $0x3,%r12
    640f:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
            int y = (k * data->thread->threads_per_group) + d;
    6414:	4d 89 e5             	mov    %r12,%r13
    6417:	4c 89 f5             	mov    %r14,%rbp
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    641a:	4c 89 64 24 10       	mov    %r12,0x10(%rsp)
    641f:	44 8b 64 24 48       	mov    0x48(%rsp),%r12d
    6424:	0f 1f 40 00          	nopl   0x0(%rax)
    6428:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    642d:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6432:	31 f6                	xor    %esi,%esi
    6434:	0f 1f 40 00          	nopl   0x0(%rax)
              if (b == y) { continue; } 
    6438:	41 39 f2             	cmp    %esi,%r10d
    643b:	74 65                	je     64a2 <barriered_work+0x432>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    643d:	4c 8b 4b 20          	mov    0x20(%rbx),%r9
    6441:	49 8b 44 29 38       	mov    0x38(%r9,%rbp,1),%rax
    6446:	48 8b 94 08 70 01 00 00 	mov    0x170(%rax,%rcx,1),%rdx
    644e:	48 01 fa             	add    %rdi,%rdx
              if (kind == MAILBOX_FRIEND) {
    6451:	83 7a 30 01          	cmpl   $0x1,0x30(%rdx)
    6455:	75 4b                	jne    64a2 <barriered_work+0x432>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    6457:	4b 8b 44 01 38       	mov    0x38(%r9,%r8,1),%rax
                    void * _a = data->thread->all_threads[y].tasks[t].mailboxes[b].higher;
    645c:	f3 0f 6f 02          	movdqu (%rdx),%xmm0
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    6460:	48 8b 84 08 70 01 00 00 	mov    0x170(%rax,%rcx,1),%rax
                    void * _b = data->thread->all_threads[y].tasks[t].mailboxes[b].lower;
    6468:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    646d:	4a 63 44 28 34       	movslq 0x34(%rax,%r13,1),%rax
    6472:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6476:	4c 8d 34 80          	lea    (%rax,%rax,4),%r14
              int next_task = abs((t + 1) % (data->thread_count));
    647a:	44 89 e0             	mov    %r12d,%eax
    647d:	99                   	cltd
    647e:	41 f7 bf 34 01 00 00 	idivl  0x134(%r15)
    6485:	89 d0                	mov    %edx,%eax
    6487:	f7 d8                	neg    %eax
    6489:	0f 48 c2             	cmovs  %edx,%eax
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    648c:	48 98                	cltq
    648e:	48 c1 e0 09          	shl    $0x9,%rax
    6492:	4b 03 44 f1 38       	add    0x38(%r9,%r14,8),%rax
                    data->thread->all_threads[other].tasks[next_task].mailboxes[b].lower = _a;
    6497:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    649e:	0f 11 04 38          	movups %xmm0,(%rax,%rdi,1)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    64a2:	83 c6 01             	add    $0x1,%esi
    64a5:	48 83 c7 38          	add    $0x38,%rdi
    64a9:	49 81 c0 c8 00 00 00 	add    $0xc8,%r8
    64b0:	44 39 de             	cmp    %r11d,%esi
    64b3:	75 83                	jne    6438 <barriered_work+0x3c8>
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    64b5:	41 83 c2 01          	add    $0x1,%r10d
    64b9:	48 81 c5 c8 00 00 00 	add    $0xc8,%rbp
    64c0:	49 83 c5 38          	add    $0x38,%r13
    64c4:	45 39 da             	cmp    %r11d,%r10d
    64c7:	0f 85 5b ff ff ff    	jne    6428 <barriered_work+0x3b8>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    64cd:	83 44 24 20 01       	addl   $0x1,0x20(%rsp)
    64d2:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    64d6:	8b 44 24 20          	mov    0x20(%rsp),%eax
    64da:	48 83 44 24 18 38    	addq   $0x38,0x18(%rsp)
    64e0:	48 81 44 24 28 c8 00 00 00 	addq   $0xc8,0x28(%rsp)
    64e9:	39 f8                	cmp    %edi,%eax
    64eb:	0f 85 3f fc ff ff    	jne    6130 <barriered_work+0xc0>
      asm volatile ("sfence" ::: "memory");
    64f1:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    64f4:	49 8b b7 60 01 00 00 	mov    0x160(%r15),%rsi
    64fb:	31 ff                	xor    %edi,%edi
    64fd:	48 c1 e6 05          	shl    $0x5,%rsi
    6501:	49 03 b7 50 01 00 00 	add    0x150(%r15),%rsi
    6508:	e8 33 be ff ff       	call   2340 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    650d:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    6514:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6518:	8b 5a 10             	mov    0x10(%rdx),%ebx
    651b:	83 c3 01             	add    $0x1,%ebx
    while (data->scheduled == 1) {
    651e:	41 83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r15)
    int modcount = ++data->thread->protected_state->modcount;
    6526:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    6529:	75 53                	jne    657e <barriered_work+0x50e>
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    652b:	49 63 97 30 01 00 00 	movslq 0x130(%r15),%rdx
    6532:	48 8b 40 18          	mov    0x18(%rax),%rax
    6536:	49 63 7f 04          	movslq 0x4(%r15),%rdi
      data->n++;
    653a:	49 83 87 08 01 00 00 01 	addq   $0x1,0x108(%r15)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6542:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6546:	48 c1 e7 09          	shl    $0x9,%rdi
    654a:	48 03 78 38          	add    0x38(%rax),%rdi
    654e:	41 ff 97 20 01 00 00 	call   *0x120(%r15)
      asm volatile ("sfence" ::: "memory");
    6555:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6558:	41 83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r15)
    if (modcount != data->thread->protected_state->modcount) {
    6560:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    while (data->scheduled == 1) {
    6567:	74 c2                	je     652b <barriered_work+0x4bb>
    if (modcount != data->thread->protected_state->modcount) {
    6569:	48 8b 40 48          	mov    0x48(%rax),%rax
    656d:	3b 58 10             	cmp    0x10(%rax),%ebx
    6570:	74 0c                	je     657e <barriered_work+0x50e>
    6572:	48 8d 3d c7 0c 00 00 	lea    0xcc7(%rip),%rdi        # 7240 <_IO_stdin_used+0x240>
    6579:	e8 a2 bd ff ff       	call   2320 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    657e:	49 8b b7 60 01 00 00 	mov    0x160(%r15),%rsi
    6585:	31 ff                	xor    %edi,%edi
    6587:	48 c1 e6 05          	shl    $0x5,%rsi
    658b:	49 03 b7 50 01 00 00 	add    0x150(%r15),%rsi
    6592:	48 83 c6 10          	add    $0x10,%rsi
    6596:	e8 a5 bd ff ff       	call   2340 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    659b:	49 8b 87 60 01 00 00 	mov    0x160(%r15),%rax
    65a2:	48 83 c0 01          	add    $0x1,%rax
    65a6:	48 99                	cqto
    65a8:	49 f7 bf 58 01 00 00 	idivq  0x158(%r15)
    65af:	49 89 97 60 01 00 00 	mov    %rdx,0x160(%r15)
    65b6:	e9 fa fa ff ff       	jmp    60b5 <barriered_work+0x45>
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    65bb:	48 8b bc 0d 70 01 00 00 	mov    0x170(%rbp,%rcx,1),%rdi
    65c3:	48 8b 5c 17 18       	mov    0x18(%rdi,%rdx,1),%rbx
                      void * right = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1];
    65c8:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    65cc:	4c 8b 2b             	mov    (%rbx),%r13
                      void * right = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1];
    65cf:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    65d4:	49 8b 7c 24 18       	mov    0x18(%r12),%rdi
    65d9:	4c 8b 27             	mov    (%rdi),%r12
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    65dc:	48 8b 7f 08          	mov    0x8(%rdi),%rdi
    65e0:	48 89 7c 24 30       	mov    %rdi,0x30(%rsp)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    65e5:	e9 5b fd ff ff       	jmp    6345 <barriered_work+0x2d5>
    65ea:	bf 01 00 00 00       	mov    $0x1,%edi
    65ef:	48 8d 35 2f 0c 00 00 	lea    0xc2f(%rip),%rsi        # 7225 <_IO_stdin_used+0x225>
    65f6:	31 c0                	xor    %eax,%eax
    65f8:	e8 a3 be ff ff       	call   24a0 <__printf_chk@plt>
                          exit(1);
    65fd:	bf 01 00 00 00       	mov    $0x1,%edi
    6602:	e8 f9 be ff ff       	call   2500 <exit@plt>
    6607:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006610 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6610:	f3 0f 1e fa          	endbr64
    6614:	53                   	push   %rbx
    6615:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6618:	e8 93 f4 ff ff       	call   5ab0 <barriered_work_ingest>
  barriered_work(data);
    661d:	48 89 df             	mov    %rbx,%rdi
}
    6620:	5b                   	pop    %rbx
  barriered_work(data);
    6621:	e9 4a fa ff ff       	jmp    6070 <barriered_work>
    6626:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006630 <sendm>:
int sendm(struct BarrierTask *data) {
    6630:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    6634:	83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%rdi)
    663b:	74 03                	je     6640 <sendm+0x10>
}
    663d:	31 c0                	xor    %eax,%eax
    663f:	c3                   	ret
int sendm(struct BarrierTask *data) {
    6640:	48 83 ec 08          	sub    $0x8,%rsp
    6644:	e8 97 dc ff ff       	call   42e0 <sendm.part.0>
}
    6649:	31 c0                	xor    %eax,%eax
    664b:	48 83 c4 08          	add    $0x8,%rsp
    664f:	c3                   	ret

0000000000006650 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6650:	f3 0f 1e fa          	endbr64
}
    6654:	31 c0                	xor    %eax,%eax
    6656:	c3                   	ret
    6657:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006660 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6660:	f3 0f 1e fa          	endbr64
    6664:	31 c0                	xor    %eax,%eax
    6666:	c3                   	ret
    6667:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006670 <after>:
int after(struct timespec left, struct timespec right) {
    6670:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6674:	31 c0                	xor    %eax,%eax
    6676:	48 39 d7             	cmp    %rdx,%rdi
    6679:	7e 08                	jle    6683 <after+0x13>
    667b:	31 c0                	xor    %eax,%eax
    667d:	48 39 ce             	cmp    %rcx,%rsi
    6680:	0f 9f c0             	setg   %al
}
    6683:	c3                   	ret
    6684:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    668f:	90                   	nop

0000000000006690 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6690:	f3 0f 1e fa          	endbr64
    6694:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6699:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    669e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    66a0:	48 39 d7             	cmp    %rdx,%rdi
    66a3:	7f 18                	jg     66bd <within+0x2d>
    66a5:	4d 39 d8             	cmp    %r11,%r8
    66a8:	0f 9e c2             	setle  %dl
    66ab:	48 39 ce             	cmp    %rcx,%rsi
    66ae:	0f 9e c0             	setle  %al
    66b1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    66b3:	31 c0                	xor    %eax,%eax
    66b5:	4d 39 d1             	cmp    %r10,%r9
    66b8:	0f 9e c0             	setle  %al
    66bb:	21 d0                	and    %edx,%eax
}
    66bd:	c3                   	ret
    66be:	66 90                	xchg   %ax,%ax

00000000000066c0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    66c0:	f3 0f 1e fa          	endbr64
    66c4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    66c9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    66ce:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    66d3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    66d8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    66dd:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    66e2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    66e7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    66ec:	48 39 fe             	cmp    %rdi,%rsi
    66ef:	7d 2f                	jge    6720 <overlap+0x60>
    66f1:	48 39 ca             	cmp    %rcx,%rdx
    66f4:	7d 62                	jge    6758 <overlap+0x98>
    66f6:	4d 39 da             	cmp    %r11,%r10
    66f9:	7d 0e                	jge    6709 <overlap+0x49>
    return 1;
    66fb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6700:	4d 39 c1             	cmp    %r8,%r9
    6703:	0f 8c 7f 00 00 00    	jl     6788 <overlap+0xc8>
  return 0;
    6709:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    670b:	4d 39 c1             	cmp    %r8,%r9
    670e:	7f 4c                	jg     675c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6710:	31 c0                	xor    %eax,%eax
    6712:	4d 39 da             	cmp    %r11,%r10
    6715:	0f 9e c0             	setle  %al
    6718:	c3                   	ret
    6719:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6720:	7e 4e                	jle    6770 <overlap+0xb0>
    6722:	48 39 ca             	cmp    %rcx,%rdx
    6725:	7f 39                	jg     6760 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6727:	75 31                	jne    675a <overlap+0x9a>
    6729:	4d 39 c1             	cmp    %r8,%r9
    672c:	7c 2c                	jl     675a <overlap+0x9a>
    return 1;
    672e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6733:	4d 39 da             	cmp    %r11,%r10
    6736:	7d 24                	jge    675c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6738:	48 39 ca             	cmp    %rcx,%rdx
    673b:	0f 94 c2             	sete   %dl
    673e:	48 39 fe             	cmp    %rdi,%rsi
    6741:	0f 94 c0             	sete   %al
    6744:	21 c2                	and    %eax,%edx
    6746:	31 c0                	xor    %eax,%eax
    6748:	4d 39 c1             	cmp    %r8,%r9
    674b:	0f 94 c0             	sete   %al
    674e:	21 d0                	and    %edx,%eax
    6750:	c3                   	ret
    6751:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6758:	74 af                	je     6709 <overlap+0x49>
  return 0;
    675a:	31 c0                	xor    %eax,%eax
}
    675c:	c3                   	ret
    675d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6760:	4d 39 da             	cmp    %r11,%r10
    6763:	7e c4                	jle    6729 <overlap+0x69>
    return 1;
    6765:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    676a:	4d 39 c1             	cmp    %r8,%r9
    676d:	7e ba                	jle    6729 <overlap+0x69>
    676f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6770:	48 39 ca             	cmp    %rcx,%rdx
    6773:	7c 94                	jl     6709 <overlap+0x49>
    6775:	4d 39 c1             	cmp    %r8,%r9
    6778:	7d b4                	jge    672e <overlap+0x6e>
    677a:	48 39 ca             	cmp    %rcx,%rdx
    677d:	74 91                	je     6710 <overlap+0x50>
    677f:	eb d9                	jmp    675a <overlap+0x9a>
    6781:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6788:	c3                   	ret
    6789:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006790 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6790:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6794:	85 f6                	test   %esi,%esi
    6796:	0f 8e 44 03 00 00    	jle    6ae0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    679c:	41 57                	push   %r15
    679e:	41 89 f7             	mov    %esi,%r15d
    67a1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    67a3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    67a6:	41 55                	push   %r13
    67a8:	41 54                	push   %r12
    67aa:	55                   	push   %rbp
    67ab:	53                   	push   %rbx
    67ac:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    67b0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    67b4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    67b9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    67be:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    67c1:	45 39 e6             	cmp    %r12d,%r14d
    67c4:	0f 84 4e 02 00 00    	je     6a18 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    67ca:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    67cf:	8b 50 08             	mov    0x8(%rax),%edx
    67d2:	85 d2                	test   %edx,%edx
    67d4:	0f 8e 3e 02 00 00    	jle    6a18 <verify+0x288>
    67da:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    67df:	31 c9                	xor    %ecx,%ecx
    67e1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    67e6:	31 c0                	xor    %eax,%eax
    67e8:	44 89 f2             	mov    %r14d,%edx
    67eb:	bf 01 00 00 00       	mov    $0x1,%edi
    67f0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    67f5:	48 8d 35 54 0a 00 00 	lea    0xa54(%rip),%rsi        # 7250 <_IO_stdin_used+0x250>
    67fc:	e8 9f bc ff ff       	call   24a0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6801:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6806:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    680b:	8b 40 08             	mov    0x8(%rax),%eax
    680e:	85 c0                	test   %eax,%eax
    6810:	0f 8e e6 01 00 00    	jle    69fc <verify+0x26c>
    6816:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6819:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    681e:	31 db                	xor    %ebx,%ebx
    6820:	48 c1 e0 09          	shl    $0x9,%rax
    6824:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6829:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    682e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6833:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6838:	4c 8b 20             	mov    (%rax),%r12
    683b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6840:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6845:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    684a:	49 89 de             	mov    %rbx,%r14
    684d:	48 8d 35 11 0a 00 00 	lea    0xa11(%rip),%rsi        # 7265 <_IO_stdin_used+0x265>
    6854:	49 c1 e6 09          	shl    $0x9,%r14
    6858:	bf 01 00 00 00       	mov    $0x1,%edi
    685d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6861:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    6869:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    686e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    6876:	31 c0                	xor    %eax,%eax
    6878:	e8 23 bc ff ff       	call   24a0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    687d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6882:	4c 8b 20             	mov    (%rax),%r12
    6885:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    688e:	0f 8e 47 01 00 00    	jle    69db <verify+0x24b>
    6894:	4c 03 75 00          	add    0x0(%rbp),%r14
    6898:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    689d:	ba 01 00 00 00       	mov    $0x1,%edx
    68a2:	4d 89 f5             	mov    %r14,%r13
    68a5:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    68ac:	4d 85 f6             	test   %r14,%r14
    68af:	0f 8e 21 01 00 00    	jle    69d6 <verify+0x246>
    68b5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    68b8:	48 89 d5             	mov    %rdx,%rbp
    68bb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    68c0:	31 db                	xor    %ebx,%ebx
    68c2:	4d 89 f2             	mov    %r14,%r10
    68c5:	48 c1 e5 05          	shl    $0x5,%rbp
    68c9:	48 83 ed 20          	sub    $0x20,%rbp
    68cd:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    68d1:	49 89 ee             	mov    %rbp,%r14
    68d4:	48 89 dd             	mov    %rbx,%rbp
    68d7:	48 89 d3             	mov    %rdx,%rbx
    68da:	eb 31                	jmp    690d <verify+0x17d>
    68dc:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    68e0:	4c 39 c2             	cmp    %r8,%rdx
    68e3:	0f 8d 57 01 00 00    	jge    6a40 <verify+0x2b0>
    68e9:	4c 39 df             	cmp    %r11,%rdi
    68ec:	7e 05                	jle    68f3 <verify+0x163>
    68ee:	49 39 c1             	cmp    %rax,%r9
    68f1:	7c 75                	jl     6968 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    68f3:	4c 39 df             	cmp    %r11,%rdi
    68f6:	0f 8d ab 01 00 00    	jge    6aa7 <verify+0x317>
    68fc:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6900:	48 83 c5 01          	add    $0x1,%rbp
    6904:	49 39 ea             	cmp    %rbp,%r10
    6907:	0f 8e a9 00 00 00    	jle    69b6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    690d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    6914:	48 89 e8             	mov    %rbp,%rax
    6917:	48 c1 e0 05          	shl    $0x5,%rax
    691b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    6922:	4c 01 f2             	add    %r14,%rdx
    6925:	48 8b 08             	mov    (%rax),%rcx
    6928:	48 8b 78 10          	mov    0x10(%rax),%rdi
    692c:	48 8b 32             	mov    (%rdx),%rsi
    692f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6933:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6937:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    693b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    693f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6943:	48 39 f1             	cmp    %rsi,%rcx
    6946:	7c 98                	jl     68e0 <verify+0x150>
    6948:	0f 8e 42 01 00 00    	jle    6a90 <verify+0x300>
    694e:	4c 39 c2             	cmp    %r8,%rdx
    6951:	0f 8f f9 00 00 00    	jg     6a50 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6957:	75 a7                	jne    6900 <verify+0x170>
    6959:	4c 39 df             	cmp    %r11,%rdi
    695c:	7f a2                	jg     6900 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    695e:	49 39 c1             	cmp    %rax,%r9
    6961:	7c 9d                	jl     6900 <verify+0x170>
    6963:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6968:	49 89 c1             	mov    %rax,%r9
    696b:	48 89 f9             	mov    %rdi,%rcx
    696e:	48 89 f2             	mov    %rsi,%rdx
    6971:	bf 01 00 00 00       	mov    $0x1,%edi
    6976:	48 8d 35 ab 0c 00 00 	lea    0xcab(%rip),%rsi        # 7628 <_IO_stdin_used+0x628>
    697d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    697f:	48 83 c5 01          	add    $0x1,%rbp
    6983:	e8 18 bb ff ff       	call   24a0 <__printf_chk@plt>
    6988:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    698d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    6992:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6995:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    699a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    69a1:	4c 8b 20             	mov    (%rax),%r12
    69a4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    69a9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    69ad:	49 39 ea             	cmp    %rbp,%r10
    69b0:	0f 8f 57 ff ff ff    	jg     690d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    69b6:	48 89 da             	mov    %rbx,%rdx
    69b9:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    69c0:	7d 14                	jge    69d6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    69c2:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    69c9:	48 83 c2 01          	add    $0x1,%rdx
    69cd:	4d 85 f6             	test   %r14,%r14
    69d0:	0f 8f e2 fe ff ff    	jg     68b8 <verify+0x128>
    69d6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    69db:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    69e0:	48 83 c3 01          	add    $0x1,%rbx
    69e4:	39 58 08             	cmp    %ebx,0x8(%rax)
    69e7:	0f 8f 53 fe ff ff    	jg     6840 <verify+0xb0>
    69ed:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    69f2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    69f7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    69fc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6a01:	48 83 c1 01          	add    $0x1,%rcx
    6a05:	39 48 08             	cmp    %ecx,0x8(%rax)
    6a08:	0f 8f d8 fd ff ff    	jg     67e6 <verify+0x56>
    6a0e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6a13:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6a18:	48 81 44 24 10 c8 00 00 00 	addq   $0xc8,0x10(%rsp)
    6a21:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6a26:	41 39 c7             	cmp    %eax,%r15d
    6a29:	0f 84 86 00 00 00    	je     6ab5 <verify+0x325>
    6a2f:	41 89 c4             	mov    %eax,%r12d
    6a32:	e9 8a fd ff ff       	jmp    67c1 <verify+0x31>
    6a37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6a40:	0f 85 ba fe ff ff    	jne    6900 <verify+0x170>
    6a46:	e9 a8 fe ff ff       	jmp    68f3 <verify+0x163>
    6a4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6a50:	49 39 c1             	cmp    %rax,%r9
    6a53:	7e 09                	jle    6a5e <verify+0x2ce>
    6a55:	4c 39 df             	cmp    %r11,%rdi
    6a58:	0f 8c 0a ff ff ff    	jl     6968 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6a5e:	4c 39 df             	cmp    %r11,%rdi
    6a61:	0f 8f 99 fe ff ff    	jg     6900 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6a67:	49 39 c1             	cmp    %rax,%r9
    6a6a:	0f 8d f8 fe ff ff    	jge    6968 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6a70:	48 39 f1             	cmp    %rsi,%rcx
    6a73:	0f 85 87 fe ff ff    	jne    6900 <verify+0x170>
    6a79:	4c 39 c2             	cmp    %r8,%rdx
    6a7c:	0f 85 7e fe ff ff    	jne    6900 <verify+0x170>
    6a82:	4c 39 df             	cmp    %r11,%rdi
    6a85:	0f 84 dd fe ff ff    	je     6968 <verify+0x1d8>
    6a8b:	e9 70 fe ff ff       	jmp    6900 <verify+0x170>
    6a90:	4c 39 c2             	cmp    %r8,%rdx
    6a93:	0f 8c 5a fe ff ff    	jl     68f3 <verify+0x163>
    6a99:	4c 39 df             	cmp    %r11,%rdi
    6a9c:	7e c9                	jle    6a67 <verify+0x2d7>
    6a9e:	4c 39 c2             	cmp    %r8,%rdx
    6aa1:	0f 85 59 fe ff ff    	jne    6900 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6aa7:	49 39 c1             	cmp    %rax,%r9
    6aaa:	0f 8f 50 fe ff ff    	jg     6900 <verify+0x170>
    6ab0:	e9 b3 fe ff ff       	jmp    6968 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    6ab5:	48 81 44 24 18 c8 00 00 00 	addq   $0xc8,0x18(%rsp)
    6abe:	41 8d 46 01          	lea    0x1(%r14),%eax
    6ac2:	45 39 e6             	cmp    %r12d,%r14d
    6ac5:	74 08                	je     6acf <verify+0x33f>
    6ac7:	41 89 c6             	mov    %eax,%r14d
    6aca:	e9 ea fc ff ff       	jmp    67b9 <verify+0x29>
}
    6acf:	48 83 c4 58          	add    $0x58,%rsp
    6ad3:	31 c0                	xor    %eax,%eax
    6ad5:	5b                   	pop    %rbx
    6ad6:	5d                   	pop    %rbp
    6ad7:	41 5c                	pop    %r12
    6ad9:	41 5d                	pop    %r13
    6adb:	41 5e                	pop    %r14
    6add:	41 5f                	pop    %r15
    6adf:	c3                   	ret
    6ae0:	31 c0                	xor    %eax,%eax
    6ae2:	c3                   	ret

Disassembly of section .fini:

0000000000006ae4 <_fini>:
    6ae4:	f3 0f 1e fa          	endbr64
    6ae8:	48 83 ec 08          	sub    $0x8,%rsp
    6aec:	48 83 c4 08          	add    $0x8,%rsp
    6af0:	c3                   	ret
