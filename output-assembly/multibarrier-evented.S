
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
    25b6:	48 8d 3d 69 4c 00 00 	lea    0x4c69(%rip),%rdi        # 7226 <_IO_stdin_used+0x226>
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
    25f6:	48 8d 3d f9 4b 00 00 	lea    0x4bf9(%rip),%rdi        # 71f6 <_IO_stdin_used+0x1f6>
    25fd:	e8 9e ff ff ff       	call   25a0 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    2602:	48 8d 3d 71 4b 00 00 	lea    0x4b71(%rip),%rdi        # 717a <_IO_stdin_used+0x17a>
    2609:	e8 92 ff ff ff       	call   25a0 <fatal_error>
    fatal_error("listen()");
    260e:	48 8d 3d 85 4b 00 00 	lea    0x4b85(%rip),%rdi        # 719a <_IO_stdin_used+0x19a>
    2615:	e8 86 ff ff ff       	call   25a0 <fatal_error>
    261a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2622:	0f 0b                	ud2
    2624:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    262c:	0f 0b                	ud2
      fatal_error("socket()");
    262e:	48 8d 3d 3c 4b 00 00 	lea    0x4b3c(%rip),%rdi        # 7171 <_IO_stdin_used+0x171>
    2635:	e8 66 ff ff ff       	call   25a0 <fatal_error>
      fatal_error("bind()");
    263a:	48 8d 3d 52 4b 00 00 	lea    0x4b52(%rip),%rdi        # 7193 <_IO_stdin_used+0x193>
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
    2656:	48 8d 3d eb 4f 00 00 	lea    0x4feb(%rip),%rdi        # 7648 <_IO_stdin_used+0x648>
    265d:	41 56                	push   %r14
    265f:	41 55                	push   %r13
    2661:	41 54                	push   %r12
    2663:	55                   	push   %rbp
    2664:	53                   	push   %rbx
    2665:	48 81 ec 98 00 00 00 	sub    $0x98,%rsp
    266c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2675:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    267d:	48 8d 05 4c 16 00 00 	lea    0x164c(%rip),%rax        # 3cd0 <barriered_reset>
    2684:	66 48 0f 6e e8       	movq   %rax,%xmm5
    2689:	0f 16 2d d0 75 00 00 	movhps 0x75d0(%rip),%xmm5        # 9c60 <__do_global_dtors_aux_fini_array_entry+0x8>
    2690:	0f 29 6c 24 60       	movaps %xmm5,0x60(%rsp)
    2695:	e8 86 fc ff ff       	call   2320 <puts@plt>
    269a:	bf 0a 00 00 00       	mov    $0xa,%edi
    269f:	e8 5c fc ff ff       	call   2300 <putchar@plt>
    26a4:	ba 01 00 00 00       	mov    $0x1,%edx
    26a9:	48 8d 35 de 4b 00 00 	lea    0x4bde(%rip),%rsi        # 728e <_IO_stdin_used+0x28e>
    26b0:	31 c0                	xor    %eax,%eax
    26b2:	bf 01 00 00 00       	mov    $0x1,%edi
    26b7:	e8 e4 fd ff ff       	call   24a0 <__printf_chk@plt>
    26bc:	ba 02 00 00 00       	mov    $0x2,%edx
    26c1:	48 8d 35 d6 4b 00 00 	lea    0x4bd6(%rip),%rsi        # 729e <_IO_stdin_used+0x29e>
    26c8:	31 c0                	xor    %eax,%eax
    26ca:	bf 01 00 00 00       	mov    $0x1,%edi
    26cf:	e8 cc fd ff ff       	call   24a0 <__printf_chk@plt>
    26d4:	ba 01 00 00 00       	mov    $0x1,%edx
    26d9:	48 8d 35 d3 4b 00 00 	lea    0x4bd3(%rip),%rsi        # 72b3 <_IO_stdin_used+0x2b3>
    26e0:	31 c0                	xor    %eax,%eax
    26e2:	bf 01 00 00 00       	mov    $0x1,%edi
    26e7:	e8 b4 fd ff ff       	call   24a0 <__printf_chk@plt>
    26ec:	ba 02 00 00 00       	mov    $0x2,%edx
    26f1:	48 8d 35 cb 4b 00 00 	lea    0x4bcb(%rip),%rsi        # 72c3 <_IO_stdin_used+0x2c3>
    26f8:	31 c0                	xor    %eax,%eax
    26fa:	bf 01 00 00 00       	mov    $0x1,%edi
    26ff:	e8 9c fd ff ff       	call   24a0 <__printf_chk@plt>
    2704:	48 8d 3d ce 4b 00 00 	lea    0x4bce(%rip),%rdi        # 72d9 <_IO_stdin_used+0x2d9>
    270b:	e8 10 fc ff ff       	call   2320 <puts@plt>
    2710:	ba 02 00 00 00       	mov    $0x2,%edx
    2715:	48 8d 35 d9 4b 00 00 	lea    0x4bd9(%rip),%rsi        # 72f5 <_IO_stdin_used+0x2f5>
    271c:	31 c0                	xor    %eax,%eax
    271e:	bf 01 00 00 00       	mov    $0x1,%edi
    2723:	e8 78 fd ff ff       	call   24a0 <__printf_chk@plt>
    2728:	ba 06 00 00 00       	mov    $0x6,%edx
    272d:	48 8d 35 db 4b 00 00 	lea    0x4bdb(%rip),%rsi        # 730f <_IO_stdin_used+0x30f>
    2734:	31 c0                	xor    %eax,%eax
    2736:	bf 01 00 00 00       	mov    $0x1,%edi
    273b:	e8 60 fd ff ff       	call   24a0 <__printf_chk@plt>
    2740:	ba 01 00 00 00       	mov    $0x1,%edx
    2745:	48 8d 35 d7 4b 00 00 	lea    0x4bd7(%rip),%rsi        # 7323 <_IO_stdin_used+0x323>
    274c:	31 c0                	xor    %eax,%eax
    274e:	bf 01 00 00 00       	mov    $0x1,%edi
    2753:	e8 48 fd ff ff       	call   24a0 <__printf_chk@plt>
    2758:	ba 01 00 00 00       	mov    $0x1,%edx
    275d:	48 8d 35 d0 4b 00 00 	lea    0x4bd0(%rip),%rsi        # 7334 <_IO_stdin_used+0x334>
    2764:	31 c0                	xor    %eax,%eax
    2766:	bf 01 00 00 00       	mov    $0x1,%edi
    276b:	e8 30 fd ff ff       	call   24a0 <__printf_chk@plt>
    2770:	ba 02 00 00 00       	mov    $0x2,%edx
    2775:	48 8d 35 d0 4b 00 00 	lea    0x4bd0(%rip),%rsi        # 734c <_IO_stdin_used+0x34c>
    277c:	31 c0                	xor    %eax,%eax
    277e:	bf 01 00 00 00       	mov    $0x1,%edi
    2783:	e8 18 fd ff ff       	call   24a0 <__printf_chk@plt>
    2788:	ba 01 00 00 00       	mov    $0x1,%edx
    278d:	48 8d 35 1c 4f 00 00 	lea    0x4f1c(%rip),%rsi        # 76b0 <_IO_stdin_used+0x6b0>
    2794:	31 c0                	xor    %eax,%eax
    2796:	bf 01 00 00 00       	mov    $0x1,%edi
    279b:	e8 00 fd ff ff       	call   24a0 <__printf_chk@plt>
    27a0:	ba 01 00 00 00       	mov    $0x1,%edx
    27a5:	48 8d 35 34 4f 00 00 	lea    0x4f34(%rip),%rsi        # 76e0 <_IO_stdin_used+0x6e0>
    27ac:	31 c0                	xor    %eax,%eax
    27ae:	bf 01 00 00 00       	mov    $0x1,%edi
    27b3:	e8 e8 fc ff ff       	call   24a0 <__printf_chk@plt>
    27b8:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    27bd:	48 8d 35 a4 4b 00 00 	lea    0x4ba4(%rip),%rsi        # 7368 <_IO_stdin_used+0x368>
    27c4:	31 c0                	xor    %eax,%eax
    27c6:	bf 01 00 00 00       	mov    $0x1,%edi
    27cb:	e8 d0 fc ff ff       	call   24a0 <__printf_chk@plt>
    27d0:	ba 05 00 00 00       	mov    $0x5,%edx
    27d5:	48 8d 35 a6 4b 00 00 	lea    0x4ba6(%rip),%rsi        # 7382 <_IO_stdin_used+0x382>
    27dc:	31 c0                	xor    %eax,%eax
    27de:	bf 01 00 00 00       	mov    $0x1,%edi
    27e3:	e8 b8 fc ff ff       	call   24a0 <__printf_chk@plt>
    27e8:	48 8d 3d 06 49 00 00 	lea    0x4906(%rip),%rdi        # 70f5 <_IO_stdin_used+0xf5>
    27ef:	e8 2c fb ff ff       	call   2320 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    27f4:	be 18 00 00 00       	mov    $0x18,%esi
    27f9:	bf 01 00 00 00       	mov    $0x1,%edi
    27fe:	e8 ed fb ff ff       	call   23f0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2803:	be c8 00 00 00       	mov    $0xc8,%esi
    2808:	bf 06 00 00 00       	mov    $0x6,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    280d:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2812:	e8 d9 fb ff ff       	call   23f0 <calloc@plt>
    2817:	ba 02 00 00 00       	mov    $0x2,%edx
    281c:	bf 01 00 00 00       	mov    $0x1,%edi
    2821:	48 8d 35 6e 4b 00 00 	lea    0x4b6e(%rip),%rsi        # 7396 <_IO_stdin_used+0x396>
    2828:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    282d:	31 c0                	xor    %eax,%eax
    282f:	e8 6c fc ff ff       	call   24a0 <__printf_chk@plt>
    2834:	ba 04 00 00 00       	mov    $0x4,%edx
    2839:	48 8d 35 6c 4b 00 00 	lea    0x4b6c(%rip),%rsi        # 73ac <_IO_stdin_used+0x3ac>
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
    2860:	49 89 c7             	mov    %rax,%r15
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    2863:	48 8d 58 40          	lea    0x40(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2867:	49 89 c4             	mov    %rax,%r12
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    286a:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    286f:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2877:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    287c:	49 83 c4 10          	add    $0x10,%r12
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2880:	e8 6b fb ff ff       	call   23f0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2885:	be 20 00 00 00       	mov    $0x20,%esi
    288a:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    288f:	49 89 44 24 f8       	mov    %rax,-0x8(%r12)
    2894:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
    2897:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    28a1:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    28ab:	e8 40 fb ff ff       	call   23f0 <calloc@plt>
    28b0:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    28b7:	4c 39 e3             	cmp    %r12,%rbx
    28ba:	75 ae                	jne    286a <main+0x21a>
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
        other = abs(x - 1) % total_threads;
        thread_data[x].thread_index = 1;
    28bc:	4c 8b 4c 24 30       	mov    0x30(%rsp),%r9
    28c1:	c7 04 24 00 00 00 00 	movl   $0x0,(%rsp)
    28c8:	48 c7 44 24 48 00 00 00 00 	movq   $0x0,0x48(%rsp)
    28d1:	49 8d 81 c8 00 00 00 	lea    0xc8(%r9),%rax
    28d8:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    28e0:	4c 89 cb             	mov    %r9,%rbx
    28e3:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
    28e8:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    28ed:	44 8b 24 24          	mov    (%rsp),%r12d
    28f1:	31 d2                	xor    %edx,%edx
    28f3:	bf 01 00 00 00       	mov    $0x1,%edi
    28f8:	48 8d 35 09 4e 00 00 	lea    0x4e09(%rip),%rsi        # 7708 <_IO_stdin_used+0x708>
    28ff:	44 89 e1             	mov    %r12d,%ecx
    2902:	89 44 24 08          	mov    %eax,0x8(%rsp)
    2906:	41 89 c5             	mov    %eax,%r13d
    2909:	31 c0                	xor    %eax,%eax
    290b:	e8 90 fb ff ff       	call   24a0 <__printf_chk@plt>
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2910:	be 08 00 00 00       	mov    $0x8,%esi
    2915:	bf 02 00 00 00       	mov    $0x2,%edi
    291a:	e8 d1 fa ff ff       	call   23f0 <calloc@plt>
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    291f:	be 80 00 00 00       	mov    $0x80,%esi
    2924:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2929:	49 89 c6             	mov    %rax,%r14
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    292c:	e8 bf fa ff ff       	call   23f0 <calloc@plt>
    2931:	48 89 c5             	mov    %rax,%rbp
        thread_data[x].thread_index = 1;
    2934:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
      if (x % 2 == 1) {
    2939:	45 85 e4             	test   %r12d,%r12d
    293c:	0f 84 75 0b 00 00    	je     34b7 <main+0xe67>
        my_thread_data[0] = &thread_data[other]; 
        my_thread_data[1] = &thread_data[x]; 
        me_thread = 1;
        // printf("odd %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
        thread_data[x].protected_state = &protected_state[k];
    2942:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
        other = abs(x - 1) % total_threads;
    2947:	45 31 e4             	xor    %r12d,%r12d
        thread_data[x].thread_index = 1;
    294a:	c7 80 cc 00 00 00 01 00 00 00 	movl   $0x1,0xcc(%rax)
        thread_data[x].protected_state = &protected_state[k];
    2954:	48 89 b8 10 01 00 00 	mov    %rdi,0x110(%rax)
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    295b:	49 8d 46 08          	lea    0x8(%r14),%rax
    295f:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2964:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    2969:	8b 14 24             	mov    (%rsp),%edx
    296c:	44 89 e1             	mov    %r12d,%ecx
    296f:	bf 01 00 00 00       	mov    $0x1,%edi
    2974:	44 8b 43 04          	mov    0x4(%rbx),%r8d
    2978:	48 8d 35 b9 4d 00 00 	lea    0x4db9(%rip),%rsi        # 7738 <_IO_stdin_used+0x738>
    297f:	49 89 46 08          	mov    %rax,0x8(%r14)
    2983:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    2988:	49 89 06             	mov    %rax,(%r14)
    298b:	31 c0                	xor    %eax,%eax
    298d:	e8 0e fb ff ff       	call   24a0 <__printf_chk@plt>
    2992:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2996:	bf 01 00 00 00       	mov    $0x1,%edi
    299b:	31 c0                	xor    %eax,%eax
      thread_data[x].other = other;
    299d:	44 89 a3 b8 00 00 00 	mov    %r12d,0xb8(%rbx)
    29a4:	44 8b 24 24          	mov    (%rsp),%r12d
    29a8:	48 8d 35 b9 4d 00 00 	lea    0x4db9(%rip),%rsi        # 7768 <_IO_stdin_used+0x768>
    29af:	44 89 e2             	mov    %r12d,%edx
    29b2:	e8 e9 fa ff ff       	call   24a0 <__printf_chk@plt>
          CPU_SET(curcpu, sendercpu);
    29b7:	44 89 e9             	mov    %r13d,%ecx
    29ba:	b8 01 00 00 00       	mov    $0x1,%eax
      thread_data[x].threads = my_thread_data;
    29bf:	4c 89 73 18          	mov    %r14,0x18(%rbx)
          CPU_SET(curcpu, sendercpu);
    29c3:	48 d3 e0             	shl    %cl,%rax
    29c6:	48 09 45 00          	or     %rax,0x0(%rbp)
      thread_data[x].all_threads = thread_data;
    29ca:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
      thread_data[x].real_thread_index = x;
    29cf:	45 89 e5             	mov    %r12d,%r13d
    29d2:	44 89 63 08          	mov    %r12d,0x8(%rbx)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    29d6:	be 10 00 00 00       	mov    $0x10,%esi
    29db:	41 83 f5 01          	xor    $0x1,%r13d
        for (int y = 0 ; y < total_barrier_count ; y++) {
    29df:	45 31 f6             	xor    %r14d,%r14d
      thread_data[x].all_threads = thread_data;
    29e2:	48 89 43 20          	mov    %rax,0x20(%rbx)
      thread_data[x].group_count = group_count;
    29e6:	48 8b 05 a3 52 00 00 	mov    0x52a3(%rip),%rax        # 7c90 <_IO_stdin_used+0xc90>
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    29ed:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].kind = KERNEL_THREAD;
    29f2:	c7 03 5f 00 00 00    	movl   $0x5f,(%rbx)
      thread_data[x].group_count = group_count;
    29f8:	48 89 83 c0 00 00 00 	mov    %rax,0xc0(%rbx)
      thread_data[x].thread_count = 2;
    29ff:	48 8b 05 92 52 00 00 	mov    0x5292(%rip),%rax        # 7c98 <_IO_stdin_used+0xc98>
      thread_data[x].cpu_set = sendercpu;
    2a06:	48 89 ab b0 00 00 00 	mov    %rbp,0xb0(%rbx)
      thread_data[x].thread_count = 2;
    2a0d:	48 89 43 28          	mov    %rax,0x28(%rbx)
      thread_data[x].task_count = total_barrier_count;
    2a11:	c7 43 40 03 00 00 00 	movl   $0x3,0x40(%rbx)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a18:	e8 d3 f9 ff ff       	call   23f0 <calloc@plt>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a1d:	be 10 00 00 00       	mov    $0x10,%esi
    2a22:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a27:	48 89 43 68          	mov    %rax,0x68(%rbx)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a2b:	e8 c0 f9 ff ff       	call   23f0 <calloc@plt>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a30:	be 28 00 00 00       	mov    $0x28,%esi
    2a35:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].timestamp_count = 0;
    2a3a:	66 0f 6f 3d 1e 52 00 00 	movdqa 0x521e(%rip),%xmm7        # 7c60 <_IO_stdin_used+0xc60>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a42:	48 89 43 70          	mov    %rax,0x70(%rbx)
      thread_data[x].timestamp_count = 0;
    2a46:	0f 11 bb 80 00 00 00 	movups %xmm7,0x80(%rbx)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a4d:	e8 9e f9 ff ff       	call   23f0 <calloc@plt>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a52:	be 00 02 00 00       	mov    $0x200,%esi
    2a57:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2a5c:	66 0f 6f 3d fc 51 00 00 	movdqa 0x51fc(%rip),%xmm7        # 7c60 <_IO_stdin_used+0xc60>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a64:	48 89 83 90 00 00 00 	mov    %rax,0x90(%rbx)
      thread_data[x].task_timestamp_count = 0;
    2a6b:	0f 11 bb 98 00 00 00 	movups %xmm7,0x98(%rbx)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a72:	e8 79 f9 ff ff       	call   23f0 <calloc@plt>
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a77:	4c 89 7c 24 78       	mov    %r15,0x78(%rsp)
        thread_data[x].tasks = barriers;
    2a7c:	48 89 43 38          	mov    %rax,0x38(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a80:	48 89 c2             	mov    %rax,%rdx
    2a83:	44 89 6c 24 18       	mov    %r13d,0x18(%rsp)
    2a88:	49 89 dd             	mov    %rbx,%r13
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a8b:	49 63 c6             	movslq %r14d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2a8e:	be 38 00 00 00       	mov    $0x38,%esi
    2a93:	bf 02 00 00 00       	mov    $0x2,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2a98:	31 db                	xor    %ebx,%ebx
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a9a:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2a9f:	48 c1 e0 09          	shl    $0x9,%rax
    2aa3:	48 8d 2c 02          	lea    (%rdx,%rax,1),%rbp
    2aa7:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    2aac:	48 8d 05 dd 11 00 00 	lea    0x11dd(%rip),%rax        # 3c90 <do_protected_write>
    2ab3:	48 89 85 20 01 00 00 	mov    %rax,0x120(%rbp)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2aba:	e8 31 f9 ff ff       	call   23f0 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2abf:	44 8b 7c 24 10       	mov    0x10(%rsp),%r15d
    2ac4:	4c 89 6c 24 38       	mov    %r13,0x38(%rsp)
    2ac9:	48 89 85 70 01 00 00 	mov    %rax,0x170(%rbp)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2ad0:	49 89 c4             	mov    %rax,%r12
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ad3:	45 89 fd             	mov    %r15d,%r13d
    2ad6:	41 89 df             	mov    %ebx,%r15d
    2ad9:	31 c9                	xor    %ecx,%ecx
    2adb:	44 89 fa             	mov    %r15d,%edx
    2ade:	48 8d 35 e1 48 00 00 	lea    0x48e1(%rip),%rsi        # 73c6 <_IO_stdin_used+0x3c6>
    2ae5:	31 c0                	xor    %eax,%eax
    2ae7:	bf 01 00 00 00       	mov    $0x1,%edi
    2aec:	49 83 c4 38          	add    $0x38,%r12
    2af0:	e8 ab f9 ff ff       	call   24a0 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2af5:	be 08 00 00 00       	mov    $0x8,%esi
    2afa:	bf 01 00 00 00       	mov    $0x1,%edi
    2aff:	e8 ec f8 ff ff       	call   23f0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b04:	be 08 00 00 00       	mov    $0x8,%esi
    2b09:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b0e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b13:	e8 d8 f8 ff ff       	call   23f0 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2b18:	be 80 03 00 00       	mov    $0x380,%esi
    2b1d:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b22:	48 89 c3             	mov    %rax,%rbx
              struct Data *data = calloc(3, sizeof(struct Data));
    2b25:	e8 c6 f8 ff ff       	call   23f0 <calloc@plt>
              data[0].a = x;
    2b2a:	8b 3c 24             	mov    (%rsp),%edi
    2b2d:	44 89 fa             	mov    %r15d,%edx
              mailboxes[b].pending = NULL;
    2b30:	49 c7 44 24 d8 00 00 00 00 	movq   $0x0,-0x28(%r12)
              struct Data *data = calloc(3, sizeof(struct Data));
    2b39:	48 89 c5             	mov    %rax,%rbp
              data[0].b = y;
    2b3c:	44 89 b0 20 03 00 00 	mov    %r14d,0x320(%rax)
    2b43:	48 8d 35 3e 4c 00 00 	lea    0x4c3e(%rip),%rsi        # 7788 <_IO_stdin_used+0x788>
              data[0].a = x;
    2b4a:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].kind = MAILBOX_LOWER;
    2b50:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].c = b;
    2b5a:	44 89 b8 24 03 00 00 	mov    %r15d,0x324(%rax)
              data[0].id = dataid++;
    2b61:	41 8d 45 01          	lea    0x1(%r13),%eax
              data[1].id = dataid++;
    2b65:	89 85 a8 06 00 00    	mov    %eax,0x6a8(%rbp)
              mailboxes[b].higher = &data[1];
    2b6b:	48 8d 85 80 03 00 00 	lea    0x380(%rbp),%rax
    2b72:	49 89 44 24 d0       	mov    %rax,-0x30(%r12)
    2b77:	8b 44 24 18          	mov    0x18(%rsp),%eax
              data[0].id = dataid++;
    2b7b:	44 89 ad 28 03 00 00 	mov    %r13d,0x328(%rbp)
              data[1].id = dataid++;
    2b82:	41 83 c5 02          	add    $0x2,%r13d
    2b86:	41 89 44 24 fc       	mov    %eax,-0x4(%r12)
    2b8b:	89 c1                	mov    %eax,%ecx
    2b8d:	31 c0                	xor    %eax,%eax
              data[1].a = x;
    2b8f:	89 bd 9c 06 00 00    	mov    %edi,0x69c(%rbp)
    2b95:	bf 01 00 00 00       	mov    $0x1,%edi
              mailboxes[b].lower = &data[0];
    2b9a:	49 89 6c 24 c8       	mov    %rbp,-0x38(%r12)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2b9f:	41 c7 44 24 f8 01 00 00 00 	movl   $0x1,-0x8(%r12)
              data[1].kind = MAILBOX_HIGHER;
    2ba8:	c7 85 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%rbp)
              data[1].b = y;
    2bb2:	44 89 b5 a0 06 00 00 	mov    %r14d,0x6a0(%rbp)
              data[1].c = b;
    2bb9:	44 89 bd a4 06 00 00 	mov    %r15d,0x6a4(%rbp)
              data[0].finished_reading = 1;
    2bc0:	c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rbp)
    2bca:	e8 d1 f8 ff ff       	call   24a0 <__printf_chk@plt>
              data[0].messages_count = 0;
    2bcf:	66 0f 6f 15 99 50 00 00 	movdqa 0x5099(%rip),%xmm2        # 7c70 <_IO_stdin_used+0xc70>
              data[0].messages = messages;
    2bd7:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
              data[1].messages = messages2;
    2bdc:	48 89 9d 80 03 00 00 	mov    %rbx,0x380(%rbp)
              data[0].messages = messages;
    2be3:	4c 89 55 00          	mov    %r10,0x0(%rbp)
              data[0].messages_count = 0;
    2be7:	0f 29 95 80 00 00 00 	movaps %xmm2,0x80(%rbp)
              data[1].messages_count = 0;
    2bee:	0f 29 95 00 04 00 00 	movaps %xmm2,0x400(%rbp)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2bf5:	45 85 ff             	test   %r15d,%r15d
    2bf8:	75 0b                	jne    2c05 <main+0x5b5>
    2bfa:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    2c00:	e9 d4 fe ff ff       	jmp    2ad9 <main+0x489>
          char *message = malloc(sizeof(char) * 256);
    2c05:	be 01 00 00 00       	mov    $0x1,%esi
    2c0a:	bf 00 01 00 00       	mov    $0x100,%edi
    2c0f:	4c 8b 6c 24 38       	mov    0x38(%rsp),%r13
    2c14:	44 89 fb             	mov    %r15d,%ebx
    2c17:	83 44 24 10 04       	addl   $0x4,0x10(%rsp)
    2c1c:	e8 cf f7 ff ff       	call   23f0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2c21:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    2c26:	48 89 c5             	mov    %rax,%rbp
          struct Message *messaged = malloc(sizeof(struct Message));
    2c29:	e8 32 f8 ff ff       	call   2460 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2c2e:	48 83 ec 08          	sub    $0x8,%rsp
    2c32:	48 89 ef             	mov    %rbp,%rdi
    2c35:	45 89 f1             	mov    %r14d,%r9d
    2c38:	6a 00                	push   $0x0
    2c3a:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
    2c3f:	49 89 c4             	mov    %rax,%r12
    2c42:	ba 00 01 00 00       	mov    $0x100,%edx
    2c47:	48 8d 0d 62 4b 00 00 	lea    0x4b62(%rip),%rcx        # 77b0 <_IO_stdin_used+0x7b0>
    2c4e:	be 01 00 00 00       	mov    $0x1,%esi
    2c53:	31 c0                	xor    %eax,%eax
    2c55:	e8 26 f9 ff ff       	call   2580 <__sprintf_chk@plt>
          messaged->task_index = y;
    2c5a:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
          thread_data[x].tasks[y].group = k;
    2c5f:	49 8b 55 38          	mov    0x38(%r13),%rdx
          messaged->message = message;
    2c63:	49 89 2c 24          	mov    %rbp,(%r12)
          thread_data[x].tasks[y].group = k;
    2c67:	48 8b 6c 24 30       	mov    0x30(%rsp),%rbp
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2c6c:	be 20 00 00 00       	mov    $0x20,%esi
    2c71:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->group = k;
    2c76:	41 c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%r12)
          messaged->task_index = y;
    2c7f:	49 89 44 24 10       	mov    %rax,0x10(%r12)
          messaged->thread_index = thread_data[x].real_thread_index;
    2c84:	49 63 45 08          	movslq 0x8(%r13),%rax
          thread_data[x].tasks[y].group = k;
    2c88:	48 01 d5             	add    %rdx,%rbp
    2c8b:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
          messaged->thread_index = thread_data[x].real_thread_index;
    2c90:	49 89 44 24 08       	mov    %rax,0x8(%r12)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2c95:	41 8d 46 01          	lea    0x1(%r14),%eax
    2c99:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].message = messaged;
    2c9c:	4c 89 a5 88 01 00 00 	mov    %r12,0x188(%rbp)
          thread_data[x].tasks[y].group = k;
    2ca3:	c7 85 94 01 00 00 00 00 00 00 	movl   $0x0,0x194(%rbp)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2cad:	c7 45 00 41 00 00 00 	movl   $0x41,0x0(%rbp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2cb4:	89 85 90 01 00 00    	mov    %eax,0x190(%rbp)
          thread_data[x].tasks[y].sending = 1;
    2cba:	c7 85 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rbp)
          thread_data[x].tasks[y].snapshot_count = 99;
    2cc4:	48 c7 85 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2ccf:	e8 1c f7 ff ff       	call   23f0 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    2cd4:	48 c7 85 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2cdf:	48 89 85 50 01 00 00 	mov    %rax,0x150(%rbp)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2ce6:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    2ceb:	48 8b 00             	mov    (%rax),%rax
    2cee:	8b 48 04             	mov    0x4(%rax),%ecx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2cf1:	4c 39 e8             	cmp    %r13,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2cf4:	48 89 85 28 01 00 00 	mov    %rax,0x128(%rbp)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2cfb:	89 8d 30 01 00 00    	mov    %ecx,0x130(%rbp)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2d01:	41 5c                	pop    %r12
    2d03:	41 5f                	pop    %r15
    2d05:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    2d0a:	0f 85 78 0e 00 00    	jne    3b88 <main+0x1538>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2d10:	66 0f 6f 25 68 4f 00 00 	movdqa 0x4f68(%rip),%xmm4        # 7c80 <_IO_stdin_used+0xc80>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2d18:	44 89 75 04          	mov    %r14d,0x4(%rbp)
          thread_data[x].tasks[y].available = 1;
    2d1c:	48 8b 05 7d 4f 00 00 	mov    0x4f7d(%rip),%rax        # 7ca0 <_IO_stdin_used+0xca0>
          thread_data[x].tasks[y].arrived = 0;
    2d23:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
          thread_data[x].tasks[y].worker_count = thread_count;
    2d2d:	c7 85 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rbp)
          thread_data[x].tasks[y].available = 1;
    2d37:	48 89 85 44 01 00 00 	mov    %rax,0x144(%rbp)
          thread_data[x].tasks[y].thread_count = 2;
    2d3e:	0f 11 a5 34 01 00 00 	movups %xmm4,0x134(%rbp)
          if (y == barrier_count - 1) {
    2d45:	41 83 fe 01          	cmp    $0x1,%r14d
    2d49:	0f 84 e5 00 00 00    	je     2e34 <main+0x7e4>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2d4f:	45 85 f6             	test   %r14d,%r14d
    2d52:	0f 84 c6 00 00 00    	je     2e1e <main+0x7ce>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    2d58:	89 d8                	mov    %ebx,%eax
    2d5a:	49 89 ec             	mov    %rbp,%r12
    2d5d:	4c 89 eb             	mov    %r13,%rbx
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2d60:	bf 01 00 00 00       	mov    $0x1,%edi
               thread_data[x].tasks[y].run = barriered_work; 
    2d65:	41 89 c5             	mov    %eax,%r13d
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2d68:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    2d6d:	48 89 d5             	mov    %rdx,%rbp
    2d70:	4c 8b 7c 24 78       	mov    0x78(%rsp),%r15
    2d75:	48 8d 05 74 33 00 00 	lea    0x3374(%rip),%rax        # 60f0 <barriered_work>
    for (int d = 0 ; d < threads_per_group ; d++) {
    2d7c:	48 81 c3 c8 00 00 00 	add    $0xc8,%rbx
               thread_data[x].tasks[y].run = barriered_work; 
    2d83:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
        thread_data[x].buffers_count = buffers_per_thread;
    2d8b:	c7 43 f4 01 00 00 00 	movl   $0x1,-0xc(%rbx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2d92:	e8 59 f6 ff ff       	call   23f0 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2d97:	48 8b 7c 24 48       	mov    0x48(%rsp),%rdi
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2d9c:	66 0f 6f 74 24 60    	movdqa 0x60(%rsp),%xmm6
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2da2:	48 89 43 88          	mov    %rax,-0x78(%rbx)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2da6:	49 8d 0c ff          	lea    (%r15,%rdi,8),%rcx
    for (int d = 0 ; d < threads_per_group ; d++) {
    2daa:	48 83 c7 02          	add    $0x2,%rdi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2dae:	48 89 08             	mov    %rcx,(%rax)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2db1:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2db6:	0f 11 b5 18 05 00 00 	movups %xmm6,0x518(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2dbd:	48 8b 00             	mov    (%rax),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    2dc0:	48 89 7c 24 48       	mov    %rdi,0x48(%rsp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    2dc5:	c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2dcf:	48 89 85 28 05 00 00 	mov    %rax,0x528(%rbp)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2dd6:	c7 85 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rbp)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    2de0:	c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2dea:	8b 83 3c ff ff ff    	mov    -0xc4(%rbx),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2df0:	c7 85 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2dfa:	89 85 30 05 00 00    	mov    %eax,0x530(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
    2e00:	48 8b 05 99 4e 00 00 	mov    0x4e99(%rip),%rax        # 7ca0 <_IO_stdin_used+0xca0>
    2e07:	48 89 85 44 05 00 00 	mov    %rax,0x544(%rbp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e0e:	8b 2c 24             	mov    (%rsp),%ebp
    2e11:	85 ed                	test   %ebp,%ebp
    2e13:	75 2d                	jne    2e42 <main+0x7f2>
    2e15:	44 89 2c 24          	mov    %r13d,(%rsp)
    2e19:	e9 ca fa ff ff       	jmp    28e8 <main+0x298>
    2e1e:	48 8d 05 bb 3a 00 00 	lea    0x3abb(%rip),%rax        # 68e0 <barriered_work_ingest_andwork>
            thread_data[x].tasks[y].run = barriered_work; 
    2e25:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
    2e2c:	41 89 de             	mov    %ebx,%r14d
    2e2f:	e9 57 fc ff ff       	jmp    2a8b <main+0x43b>
    2e34:	48 8d 05 b5 32 00 00 	lea    0x32b5(%rip),%rax        # 60f0 <barriered_work>
    2e3b:	bb 02 00 00 00       	mov    $0x2,%ebx
    2e40:	eb e3                	jmp    2e25 <main+0x7d5>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    2e42:	bf 00 04 00 00       	mov    $0x400,%edi
    2e47:	be 08 00 00 00       	mov    $0x8,%esi
    2e4c:	31 ed                	xor    %ebp,%ebp
    2e4e:	e8 9d f5 ff ff       	call   23f0 <calloc@plt>
    2e53:	49 89 c6             	mov    %rax,%r14
  int datas_size = 0; 
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e56:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    2e5b:	48 8d 58 38          	lea    0x38(%rax),%rbx
    2e5f:	48 05 c8 01 00 00    	add    $0x1c8,%rax
    2e65:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    2e6a:	48 89 df             	mov    %rbx,%rdi
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2e6d:	44 8b 47 08          	mov    0x8(%rdi),%r8d
    2e71:	45 85 c0             	test   %r8d,%r8d
    2e74:	7e 4f                	jle    2ec5 <main+0x875>
    2e76:	48 8b 17             	mov    (%rdi),%rdx
    2e79:	49 63 f0             	movslq %r8d,%rsi
    2e7c:	48 63 c5             	movslq %ebp,%rax
    2e7f:	48 c1 e6 09          	shl    $0x9,%rsi
    2e83:	49 8d 0c c6          	lea    (%r14,%rax,8),%rcx
    2e87:	48 01 d6             	add    %rdx,%rsi
    2e8a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    2e90:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2e97:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    2e9e:	48 83 c1 20          	add    $0x20,%rcx
    2ea2:	f3 0f 7e 40 38       	movq   0x38(%rax),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    2ea7:	f3 0f 7e 08          	movq   (%rax),%xmm1
    2eab:	0f 16 40 40          	movhps 0x40(%rax),%xmm0
    2eaf:	0f 16 48 08          	movhps 0x8(%rax),%xmm1
    2eb3:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    2eb7:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2ebb:	48 39 d6             	cmp    %rdx,%rsi
    2ebe:	75 d0                	jne    2e90 <main+0x840>
    2ec0:	42 8d 6c 85 00       	lea    0x0(%rbp,%r8,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    2ec5:	48 81 c7 c8 00 00 00 	add    $0xc8,%rdi
    2ecc:	48 39 7c 24 08       	cmp    %rdi,0x8(%rsp)
    2ed1:	75 9a                	jne    2e6d <main+0x81d>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2ed3:	48 8d 3d fc 44 00 00 	lea    0x44fc(%rip),%rdi        # 73d6 <_IO_stdin_used+0x3d6>
    2eda:	e8 41 f4 ff ff       	call   2320 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    2edf:	48 8d 35 6c 43 00 00 	lea    0x436c(%rip),%rsi        # 7252 <_IO_stdin_used+0x252>
    2ee6:	48 8d 3d fe 44 00 00 	lea    0x44fe(%rip),%rdi        # 73eb <_IO_stdin_used+0x3eb>
    2eed:	e8 ee f5 ff ff       	call   24e0 <fopen@plt>
    2ef2:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas_size; x++) {
    2ef5:	85 ed                	test   %ebp,%ebp
    2ef7:	7e 7c                	jle    2f75 <main+0x925>
    2ef9:	48 63 ed             	movslq %ebp,%rbp
    2efc:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    2f01:	4c 8d 2d 4c 43 00 00 	lea    0x434c(%rip),%r13        # 7254 <_IO_stdin_used+0x254>
    2f08:	4c 8d 25 07 45 00 00 	lea    0x4507(%rip),%r12        # 7416 <_IO_stdin_used+0x416>
    2f0f:	49 8d 04 ee          	lea    (%r14,%rbp,8),%rax
    2f13:	48 89 c3             	mov    %rax,%rbx
    char * c = calloc(250, sizeof(char));
    2f16:	be 01 00 00 00       	mov    $0x1,%esi
    2f1b:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    2f20:	49 83 c6 08          	add    $0x8,%r14
    char * c = calloc(250, sizeof(char));
    2f24:	e8 c7 f4 ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2f29:	4c 89 e9             	mov    %r13,%rcx
    2f2c:	ba fa 00 00 00       	mov    $0xfa,%edx
    2f31:	be 01 00 00 00       	mov    $0x1,%esi
    2f36:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    2f39:	49 8b 46 f8          	mov    -0x8(%r14),%rax
    2f3d:	48 89 ef             	mov    %rbp,%rdi
    2f40:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    2f47:	31 c0                	xor    %eax,%eax
    2f49:	e8 32 f6 ff ff       	call   2580 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2f4e:	48 89 ea             	mov    %rbp,%rdx
    2f51:	4c 89 e6             	mov    %r12,%rsi
    2f54:	bf 01 00 00 00       	mov    $0x1,%edi
    2f59:	31 c0                	xor    %eax,%eax
    2f5b:	e8 40 f5 ff ff       	call   24a0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    2f60:	4c 89 fe             	mov    %r15,%rsi
    2f63:	48 89 ef             	mov    %rbp,%rdi
    2f66:	e8 45 f4 ff ff       	call   23b0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    2f6b:	4c 39 f3             	cmp    %r14,%rbx
    2f6e:	75 a6                	jne    2f16 <main+0x8c6>
    2f70:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    2f75:	4c 89 ff             	mov    %r15,%rdi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2f78:	49 89 de             	mov    %rbx,%r14
    2f7b:	4c 8d 3d b4 44 00 00 	lea    0x44b4(%rip),%r15        # 7436 <_IO_stdin_used+0x436>
    2f82:	e8 c9 f3 ff ff       	call   2350 <fclose@plt>
    2f87:	48 8d 3d 66 44 00 00 	lea    0x4466(%rip),%rdi        # 73f4 <_IO_stdin_used+0x3f4>
    2f8e:	e8 8d f3 ff ff       	call   2320 <puts@plt>
    2f93:	31 d2                	xor    %edx,%edx
    2f95:	48 8d 35 70 44 00 00 	lea    0x4470(%rip),%rsi        # 740c <_IO_stdin_used+0x40c>
    2f9c:	31 c0                	xor    %eax,%eax
    2f9e:	bf 01 00 00 00       	mov    $0x1,%edi
    2fa3:	e8 f8 f4 ff ff       	call   24a0 <__printf_chk@plt>

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    2fa8:	c7 44 24 38 00 00 00 00 	movl   $0x0,0x38(%rsp)
    2fb0:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    2fb5:	8b 54 24 38          	mov    0x38(%rsp),%edx
    2fb9:	48 8d 35 59 44 00 00 	lea    0x4459(%rip),%rsi        # 7419 <_IO_stdin_used+0x419>
    2fc0:	31 c0                	xor    %eax,%eax
    2fc2:	45 31 ed             	xor    %r13d,%r13d
    2fc5:	bf 01 00 00 00       	mov    $0x1,%edi
    2fca:	89 d1                	mov    %edx,%ecx
    2fcc:	e8 cf f4 ff ff       	call   24a0 <__printf_chk@plt>
    2fd1:	44 89 ea             	mov    %r13d,%edx
    2fd4:	48 8d 35 50 44 00 00 	lea    0x4450(%rip),%rsi        # 742b <_IO_stdin_used+0x42b>
    2fdb:	31 c0                	xor    %eax,%eax
    2fdd:	4c 89 eb             	mov    %r13,%rbx
    2fe0:	bf 01 00 00 00       	mov    $0x1,%edi
    2fe5:	48 c1 e3 09          	shl    $0x9,%rbx
    2fe9:	31 ed                	xor    %ebp,%ebp
      int x = (k * threads_per_group) + d;
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    2feb:	45 31 e4             	xor    %r12d,%r12d
    2fee:	e8 ad f4 ff ff       	call   24a0 <__printf_chk@plt>
          char * mailbox_kind = calloc(100, sizeof(char));
    2ff3:	be 01 00 00 00       	mov    $0x1,%esi
    2ff8:	bf 64 00 00 00       	mov    $0x64,%edi
    2ffd:	e8 ee f3 ff ff       	call   23f0 <calloc@plt>
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3002:	49 8b 36             	mov    (%r14),%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
    3005:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3008:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    3010:	48 01 e8             	add    %rbp,%rax
    3013:	8b 50 30             	mov    0x30(%rax),%edx
    3016:	83 fa 02             	cmp    $0x2,%edx
    3019:	74 4f                	je     306a <main+0xa1a>
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    301b:	83 fa 01             	cmp    $0x1,%edx
    301e:	74 64                	je     3084 <main+0xa34>
    3020:	44 8b 40 34          	mov    0x34(%rax),%r8d
    3024:	44 89 e2             	mov    %r12d,%edx
    3027:	4c 89 fe             	mov    %r15,%rsi
    302a:	bf 01 00 00 00       	mov    $0x1,%edi
    302f:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3031:	48 83 c5 38          	add    $0x38,%rbp
    3035:	e8 66 f4 ff ff       	call   24a0 <__printf_chk@plt>
    303a:	45 85 e4             	test   %r12d,%r12d
    303d:	75 06                	jne    3045 <main+0x9f5>
    303f:	44 8b 24 24          	mov    (%rsp),%r12d
    3043:	eb ae                	jmp    2ff3 <main+0x9a3>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3045:	49 83 c5 01          	add    $0x1,%r13
    3049:	49 83 fd 03          	cmp    $0x3,%r13
    304d:	75 82                	jne    2fd1 <main+0x981>
    for (int d = 0 ; d < threads_per_group ; d++) {
    304f:	44 8b 5c 24 38       	mov    0x38(%rsp),%r11d
    3054:	49 81 c6 c8 00 00 00 	add    $0xc8,%r14
    305b:	45 85 db             	test   %r11d,%r11d
    305e:	75 3e                	jne    309e <main+0xa4e>
    3060:	44 89 64 24 38       	mov    %r12d,0x38(%rsp)
    3065:	e9 4b ff ff ff       	jmp    2fb5 <main+0x965>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    306a:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    3074:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    3077:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    307f:	48 01 e8             	add    %rbp,%rax
    3082:	eb 9c                	jmp    3020 <main+0x9d0>
    3084:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    308a:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    3091:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    3099:	48 01 e8             	add    %rbp,%rax
    309c:	eb 82                	jmp    3020 <main+0x9d0>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    309e:	ba 03 00 00 00       	mov    $0x3,%edx
    30a3:	48 8d 35 a7 43 00 00 	lea    0x43a7(%rip),%rsi        # 7451 <_IO_stdin_used+0x451>
    30aa:	bf 01 00 00 00       	mov    $0x1,%edi
    30af:	31 c0                	xor    %eax,%eax
    30b1:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    30b6:	e8 e5 f3 ff ff       	call   24a0 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    30bb:	be 08 00 00 00       	mov    $0x8,%esi
    30c0:	bf 02 00 00 00       	mov    $0x2,%edi
    30c5:	e8 26 f3 ff ff       	call   23f0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    30ca:	4c 8b 7c 24 30       	mov    0x30(%rsp),%r15
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    30cf:	be 38 00 00 00       	mov    $0x38,%esi
    30d4:	bf 06 00 00 00       	mov    $0x6,%edi
    my_thread_data[0] = &thread_data[x]; 
    30d9:	4d 8d a7 58 02 00 00 	lea    0x258(%r15),%r12
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    30e0:	4c 89 78 08          	mov    %r15,0x8(%rax)
    thread_data[x].threads = my_thread_data;
    30e4:	49 89 87 70 02 00 00 	mov    %rax,0x270(%r15)
    my_thread_data[0] = &thread_data[x]; 
    30eb:	4c 89 20             	mov    %r12,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    30ee:	49 8b 47 38          	mov    0x38(%r15),%rax
    thread_data[x].thread_count = 2;
    30f2:	41 c7 87 80 02 00 00 02 00 00 00 	movl   $0x2,0x280(%r15)
    thread_data[x].thread_index = 0;
    30fd:	41 c7 87 5c 02 00 00 00 00 00 00 	movl   $0x0,0x25c(%r15)
    thread_data[x].task_count = total_barrier_count;
    3108:	41 c7 87 98 02 00 00 03 00 00 00 	movl   $0x3,0x298(%r15)
    thread_data[n].tasks[0].scheduled = 1;
    3113:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    311d:	49 8b 87 00 01 00 00 	mov    0x100(%r15),%rax
    3124:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    312e:	e8 bd f2 ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3133:	be 38 00 00 00       	mov    $0x38,%esi
    3138:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    313d:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3140:	e8 ab f2 ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3145:	be 38 00 00 00       	mov    $0x38,%esi
    314a:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    314f:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3152:	e8 99 f2 ff ff       	call   23f0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3157:	be 38 00 00 00       	mov    $0x38,%esi
    315c:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3161:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3165:	e8 86 f2 ff ff       	call   23f0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    316a:	be 08 00 00 00       	mov    $0x8,%esi
    316f:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3174:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3179:	e8 72 f2 ff ff       	call   23f0 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    317e:	be 08 00 00 00       	mov    $0x8,%esi
    3183:	bf 06 00 00 00       	mov    $0x6,%edi
  thread_data[timer_threadi].type = TIMER;
    3188:	41 c7 87 9c 01 00 00 00 00 00 00 	movl   $0x0,0x19c(%r15)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3193:	48 89 c5             	mov    %rax,%rbp
  thread_data[timer_threadi].task_count = total_barrier_count;
    3196:	48 8b 05 0b 4b 00 00 	mov    0x4b0b(%rip),%rax        # 7ca8 <_IO_stdin_used+0xca8>
    319d:	49 89 87 d0 01 00 00 	mov    %rax,0x1d0(%r15)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    31a4:	e8 47 f2 ff ff       	call   23f0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    31a9:	48 8b 7c 24 50       	mov    0x50(%rsp),%rdi
    31ae:	49 8d 8f 90 01 00 00 	lea    0x190(%r15),%rcx
    31b5:	48 8d 35 a4 42 00 00 	lea    0x42a4(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    31bc:	4c 89 38             	mov    %r15,(%rax)
    31bf:	48 89 78 08          	mov    %rdi,0x8(%rax)
    31c3:	4c 89 ff             	mov    %r15,%rdi
    31c6:	4d 8d bf 20 03 00 00 	lea    0x320(%r15),%r15
    31cd:	48 8d 97 e8 03 00 00 	lea    0x3e8(%rdi),%rdx
    31d4:	48 89 48 10          	mov    %rcx,0x10(%rax)
    31d8:	48 89 50 28          	mov    %rdx,0x28(%rax)
  }
  thread_data[timer_threadi].threads = my_thread_data;
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    31dc:	48 8b 15 b5 4a 00 00 	mov    0x4ab5(%rip),%rdx        # 7c98 <_IO_stdin_used+0xc98>
    my_thread_data[n] = &thread_data[n]; 
    31e3:	4c 89 60 18          	mov    %r12,0x18(%rax)
    31e7:	4c 89 78 20          	mov    %r15,0x20(%rax)
  thread_data[timer_threadi].threads = my_thread_data;
    31eb:	48 89 87 a8 01 00 00 	mov    %rax,0x1a8(%rdi)
    31f2:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    31f4:	48 89 97 b8 01 00 00 	mov    %rdx,0x1b8(%rdi)
    31fb:	ba 02 00 00 00       	mov    $0x2,%edx
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3200:	c7 87 c0 01 00 00 02 00 00 00 	movl   $0x2,0x1c0(%rdi)
  thread_data[timer_threadi].thread_index = 0;
    320a:	c7 87 94 01 00 00 00 00 00 00 	movl   $0x0,0x194(%rdi)
    3214:	48 89 7c 24 30       	mov    %rdi,0x30(%rsp)
    3219:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    321e:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    3223:	e8 78 f2 ff ff       	call   24a0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3228:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    322d:	49 8d 76 70          	lea    0x70(%r14),%rsi
    3231:	48 8d 7d 10          	lea    0x10(%rbp),%rdi
    3235:	48 8d 15 14 0c 00 00 	lea    0xc14(%rip),%rdx        # 3e50 <timer_thread>
    323c:	e8 7f f2 ff ff       	call   24c0 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    3241:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    3246:	31 c9                	xor    %ecx,%ecx
    3248:	31 d2                	xor    %edx,%edx
    324a:	4c 8d 0d 8f 45 00 00 	lea    0x458f(%rip),%r9        # 77e0 <_IO_stdin_used+0x7e0>
    3251:	bf 01 00 00 00       	mov    $0x1,%edi
    3256:	31 c0                	xor    %eax,%eax
    3258:	41 c7 46 0c 01 00 00 00 	movl   $0x1,0xc(%r14)
    3260:	4c 89 ce             	mov    %r9,%rsi
      thread_data[x].running = 1;
    3263:	41 c7 46 44 01 00 00 00 	movl   $0x1,0x44(%r14)
    326b:	e8 30 f2 ff ff       	call   24a0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3270:	4c 89 f1             	mov    %r14,%rcx
    3273:	4c 89 74 24 30       	mov    %r14,0x30(%rsp)
    3278:	4c 89 ee             	mov    %r13,%rsi
    327b:	4c 8d 35 be 29 00 00 	lea    0x29be(%rip),%r14        # 5c40 <barriered_thread>
    3282:	48 89 ef             	mov    %rbp,%rdi
    3285:	4c 89 f2             	mov    %r14,%rdx
    3288:	e8 33 f2 ff ff       	call   24c0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    328d:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    3292:	be 08 00 00 00       	mov    $0x8,%esi
    3297:	48 8b 97 b0 00 00 00 	mov    0xb0(%rdi),%rdx
    329e:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    32a2:	e8 69 f0 ff ff       	call   2310 <pthread_setaffinity_np@plt>
      thread_data[x].type = WORKER;
    32a7:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    32ac:	31 c9                	xor    %ecx,%ecx
    32ae:	31 c0                	xor    %eax,%eax
    32b0:	4c 8d 0d 29 45 00 00 	lea    0x4529(%rip),%r9        # 77e0 <_IO_stdin_used+0x7e0>
    32b7:	ba 01 00 00 00       	mov    $0x1,%edx
    32bc:	c7 87 d4 00 00 00 01 00 00 00 	movl   $0x1,0xd4(%rdi)
    32c6:	4c 89 ce             	mov    %r9,%rsi
      thread_data[x].running = 1;
    32c9:	c7 87 0c 01 00 00 01 00 00 00 	movl   $0x1,0x10c(%rdi)
    32d3:	bf 01 00 00 00       	mov    $0x1,%edi
    32d8:	e8 c3 f1 ff ff       	call   24a0 <__printf_chk@plt>
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    32dd:	49 8d 75 38          	lea    0x38(%r13),%rsi
    32e1:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
    32e5:	4c 89 f2             	mov    %r14,%rdx
    32e8:	4c 8b 6c 24 50       	mov    0x50(%rsp),%r13
    32ed:	4c 89 e9             	mov    %r13,%rcx
    32f0:	e8 cb f1 ff ff       	call   24c0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    32f5:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    32fa:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
    32fe:	be 08 00 00 00       	mov    $0x8,%esi
    3303:	49 8b 96 78 01 00 00 	mov    0x178(%r14),%rdx
    330a:	e8 01 f0 ff ff       	call   2310 <pthread_setaffinity_np@plt>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    330f:	48 8b 3d 9a 49 00 00 	mov    0x499a(%rip),%rdi        # 7cb0 <_IO_stdin_used+0xcb0>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3316:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    331b:	41 c7 86 64 02 00 00 02 00 00 00 	movl   $0x2,0x264(%r14)
    thread_data[x].task_count = 0;
    3326:	49 89 be 98 02 00 00 	mov    %rdi,0x298(%r14)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    332d:	bf 01 00 00 00       	mov    $0x1,%edi
    3332:	e8 b9 f0 ff ff       	call   23f0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3337:	31 ff                	xor    %edi,%edi
    3339:	be 00 08 00 00       	mov    $0x800,%esi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    333e:	49 89 86 b0 02 00 00 	mov    %rax,0x2b0(%r14)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3345:	e8 c6 f1 ff ff       	call   2510 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    334a:	be 08 00 00 00       	mov    $0x8,%esi
    334f:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3354:	41 89 86 b8 02 00 00 	mov    %eax,0x2b8(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    335b:	e8 90 f0 ff ff       	call   23f0 <calloc@plt>
    3360:	ba 03 00 00 00       	mov    $0x3,%edx
    3365:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    336a:	41 c7 86 80 02 00 00 02 00 00 00 	movl   $0x2,0x280(%r14)
      my_thread_data[n] = &thread_data[n]; 
    3375:	4c 89 30             	mov    %r14,(%rax)
    3378:	48 8d 35 ff 40 00 00 	lea    0x40ff(%rip),%rsi        # 747e <_IO_stdin_used+0x47e>
    337f:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[x].threads = my_thread_data;
    3383:	49 89 86 70 02 00 00 	mov    %rax,0x270(%r14)
    338a:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    338c:	41 c7 86 5c 02 00 00 03 00 00 00 	movl   $0x3,0x25c(%r14)
    3397:	4d 89 fe             	mov    %r15,%r14
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    339a:	41 bf 04 00 00 00    	mov    $0x4,%r15d
    33a0:	e8 fb f0 ff ff       	call   24a0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    33a5:	48 8b 34 24          	mov    (%rsp),%rsi
    33a9:	48 8d 7d 18          	lea    0x18(%rbp),%rdi
    33ad:	4c 89 e1             	mov    %r12,%rcx
    33b0:	48 8d 15 99 20 00 00 	lea    0x2099(%rip),%rdx        # 5450 <io_thread>
    33b7:	4c 8d 65 20          	lea    0x20(%rbp),%r12
    33bb:	48 81 c6 a8 00 00 00 	add    $0xa8,%rsi
    33c2:	e8 f9 f0 ff ff       	call   24c0 <pthread_create@plt>
    33c7:	ba 04 00 00 00       	mov    $0x4,%edx
    33cc:	48 8d 35 c2 40 00 00 	lea    0x40c2(%rip),%rsi        # 7495 <_IO_stdin_used+0x495>
    33d3:	31 c0                	xor    %eax,%eax
    33d5:	bf 01 00 00 00       	mov    $0x1,%edi
    33da:	e8 c1 f0 ff ff       	call   24a0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    33df:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    33e4:	48 89 e8             	mov    %rbp,%rax
    33e7:	48 89 dd             	mov    %rbx,%rbp
    33ea:	48 89 c3             	mov    %rax,%rbx
    33ed:	49 81 c5 e0 00 00 00 	add    $0xe0,%r13
    33f4:	44 89 fa             	mov    %r15d,%edx
    33f7:	48 8d 35 ad 40 00 00 	lea    0x40ad(%rip),%rsi        # 74ab <_IO_stdin_used+0x4ab>
    33fe:	bf 01 00 00 00       	mov    $0x1,%edi
    3403:	31 c0                	xor    %eax,%eax
    3405:	e8 96 f0 ff ff       	call   24a0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    340a:	be 08 00 00 00       	mov    $0x8,%esi
    340f:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3414:	48 8b 05 95 48 00 00 	mov    0x4895(%rip),%rax        # 7cb0 <_IO_stdin_used+0xcb0>
    thread_data[x].type = EXTERNAL;
    341b:	41 c7 46 0c 03 00 00 00 	movl   $0x3,0xc(%r14)
    thread_data[x].task_count = 0;
    3423:	49 89 46 40          	mov    %rax,0x40(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3427:	e8 c4 ef ff ff       	call   23f0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    342c:	48 8b 7c 24 70       	mov    0x70(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3431:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3436:	41 c7 86 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3441:	49 89 46 50          	mov    %rax,0x50(%r14)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3445:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3448:	bf 02 00 00 00       	mov    $0x2,%edi
    344d:	e8 9e ef ff ff       	call   23f0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3452:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3457:	4c 89 f1             	mov    %r14,%rcx
    345a:	4c 89 e7             	mov    %r12,%rdi
    thread_data[x].threads = my_thread_data;
    345d:	49 89 46 18          	mov    %rax,0x18(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3461:	48 8d 15 d8 08 00 00 	lea    0x8d8(%rip),%rdx        # 3d40 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3468:	49 83 c4 08          	add    $0x8,%r12
    346c:	49 81 c6 c8 00 00 00 	add    $0xc8,%r14
      my_thread_data[n] = &thread_data[n]; 
    3473:	48 89 30             	mov    %rsi,(%rax)
    3476:	48 8b 74 24 50       	mov    0x50(%rsp),%rsi
    thread_data[x].thread_index = x;
    347b:	45 89 be 3c ff ff ff 	mov    %r15d,-0xc4(%r14)
      my_thread_data[n] = &thread_data[n]; 
    3482:	48 89 70 08          	mov    %rsi,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3486:	48 8b 05 0b 48 00 00 	mov    0x480b(%rip),%rax        # 7c98 <_IO_stdin_used+0xc98>
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    348d:	4c 89 ee             	mov    %r13,%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3490:	49 83 c5 38          	add    $0x38,%r13
    thread_data[x].thread_count = thread_count;
    3494:	49 89 86 60 ff ff ff 	mov    %rax,-0xa0(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    349b:	e8 20 f0 ff ff       	call   24c0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    34a0:	48 83 44 24 70 10    	addq   $0x10,0x70(%rsp)
    34a6:	41 83 ff 04          	cmp    $0x4,%r15d
    34aa:	75 2b                	jne    34d7 <main+0xe87>
    34ac:	41 bf 05 00 00 00    	mov    $0x5,%r15d
    34b2:	e9 3d ff ff ff       	jmp    33f4 <main+0xda4>
        thread_data[x].protected_state = &protected_state[k];
    34b7:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
        thread_data[x].thread_index = 0;
    34bc:	c7 40 04 00 00 00 00 	movl   $0x0,0x4(%rax)
        other = (x + 1) % total_threads;
    34c3:	41 bc 01 00 00 00    	mov    $0x1,%r12d
        thread_data[x].protected_state = &protected_state[k];
    34c9:	4c 89 74 24 40       	mov    %r14,0x40(%rsp)
    34ce:	48 89 78 48          	mov    %rdi,0x48(%rax)
    34d2:	e9 8d f4 ff ff       	jmp    2964 <main+0x314>
    34d7:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    34dc:	48 87 eb             	xchg   %rbp,%rbx
    34df:	4c 8d 25 e2 3f 00 00 	lea    0x3fe2(%rip),%r12        # 74c8 <_IO_stdin_used+0x4c8>
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
    3513:	48 8d 3d c1 3f 00 00 	lea    0x3fc1(%rip),%rdi        # 74db <_IO_stdin_used+0x4db>
    351a:	45 31 f6             	xor    %r14d,%r14d
    351d:	4c 8d ac 24 80 00 00 00 	lea    0x80(%rsp),%r13
    3525:	e8 f6 ed ff ff       	call   2320 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    352a:	4c 8d 25 c8 3f 00 00 	lea    0x3fc8(%rip),%r12        # 74f9 <_IO_stdin_used+0x4f9>
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
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    355a:	bf 00 04 00 00       	mov    $0x400,%edi
    355f:	be 08 00 00 00       	mov    $0x8,%esi
    3564:	31 ed                	xor    %ebp,%ebp
    3566:	e8 85 ee ff ff       	call   23f0 <calloc@plt>
    356b:	48 89 df             	mov    %rbx,%rdi
    356e:	49 89 c6             	mov    %rax,%r14
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
    3587:	49 8d 0c c6          	lea    (%r14,%rax,8),%rcx
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
    35cc:	48 39 7c 24 08       	cmp    %rdi,0x8(%rsp)
    35d1:	75 9e                	jne    3571 <main+0xf21>
    35d3:	48 8d 3d 33 3f 00 00 	lea    0x3f33(%rip),%rdi        # 750d <_IO_stdin_used+0x50d>
    35da:	e8 41 ed ff ff       	call   2320 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    35df:	48 8d 35 6c 3c 00 00 	lea    0x3c6c(%rip),%rsi        # 7252 <_IO_stdin_used+0x252>
    35e6:	48 8d 3d 38 3f 00 00 	lea    0x3f38(%rip),%rdi        # 7525 <_IO_stdin_used+0x525>
    35ed:	e8 ee ee ff ff       	call   24e0 <fopen@plt>
    35f2:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas2_size; x++) {
    35f5:	85 ed                	test   %ebp,%ebp
    35f7:	7e 7a                	jle    3673 <main+0x1023>
    35f9:	48 63 ed             	movslq %ebp,%rbp
    35fc:	48 89 1c 24          	mov    %rbx,(%rsp)
    3600:	4c 8d 2d 4d 3c 00 00 	lea    0x3c4d(%rip),%r13        # 7254 <_IO_stdin_used+0x254>
    3607:	4c 8d 25 08 3e 00 00 	lea    0x3e08(%rip),%r12        # 7416 <_IO_stdin_used+0x416>
    360e:	49 8d 04 ee          	lea    (%r14,%rbp,8),%rax
    3612:	48 89 c3             	mov    %rax,%rbx
    char * c = calloc(250, sizeof(char));
    3615:	be 01 00 00 00       	mov    $0x1,%esi
    361a:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    361f:	49 83 c6 08          	add    $0x8,%r14
    char * c = calloc(250, sizeof(char));
    3623:	e8 c8 ed ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3628:	4c 89 e9             	mov    %r13,%rcx
    362b:	ba fa 00 00 00       	mov    $0xfa,%edx
    3630:	be 01 00 00 00       	mov    $0x1,%esi
    3635:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3638:	49 8b 46 f8          	mov    -0x8(%r14),%rax
    363c:	48 89 ef             	mov    %rbp,%rdi
    363f:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3646:	31 c0                	xor    %eax,%eax
    3648:	e8 33 ef ff ff       	call   2580 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    364d:	48 89 ea             	mov    %rbp,%rdx
    3650:	4c 89 e6             	mov    %r12,%rsi
    3653:	bf 01 00 00 00       	mov    $0x1,%edi
    3658:	31 c0                	xor    %eax,%eax
    365a:	e8 41 ee ff ff       	call   24a0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    365f:	4c 89 fe             	mov    %r15,%rsi
    3662:	48 89 ef             	mov    %rbp,%rdi
    3665:	e8 46 ed ff ff       	call   23b0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    366a:	49 39 de             	cmp    %rbx,%r14
    366d:	75 a6                	jne    3615 <main+0xfc5>
    366f:	48 8b 1c 24          	mov    (%rsp),%rbx
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
    3673:	4c 89 ff             	mov    %r15,%rdi
    3676:	45 31 ed             	xor    %r13d,%r13d
    3679:	45 31 f6             	xor    %r14d,%r14d
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    367c:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  fclose(m2);
    3686:	e8 c5 ec ff ff       	call   2350 <fclose@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    368b:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    3690:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
  fclose(m2);
    3698:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    36a1:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    36a6:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    36af:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    36b8:	bf 0a 00 00 00       	mov    $0xa,%edi
    36bd:	44 8b 64 24 08       	mov    0x8(%rsp),%r12d
    36c2:	e8 39 ec ff ff       	call   2300 <putchar@plt>
    36c7:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    36cc:	bf 01 00 00 00       	mov    $0x1,%edi
    36d1:	48 8d 35 56 3e 00 00 	lea    0x3e56(%rip),%rsi        # 752e <_IO_stdin_used+0x52e>
    36d8:	41 83 f4 01          	xor    $0x1,%r12d
    36dc:	48 8b 10             	mov    (%rax),%rdx
    36df:	31 c0                	xor    %eax,%eax
    36e1:	e8 ba ed ff ff       	call   24a0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    36e6:	8b 53 08             	mov    0x8(%rbx),%edx
    36e9:	85 d2                	test   %edx,%edx
    36eb:	0f 8e 90 04 00 00    	jle    3b81 <main+0x1531>
    36f1:	48 63 ca             	movslq %edx,%rcx
    36f4:	48 8b 03             	mov    (%rbx),%rax
      long v = 0;
    36f7:	31 d2                	xor    %edx,%edx
    36f9:	48 c1 e1 09          	shl    $0x9,%rcx
    36fd:	48 01 c1             	add    %rax,%rcx
        v += thread_data[me].tasks[n].v;
    3700:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3707:	48 05 00 02 00 00    	add    $0x200,%rax
    370d:	48 39 c8             	cmp    %rcx,%rax
    3710:	75 ee                	jne    3700 <main+0x10b0>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3712:	4c 89 e0             	mov    %r12,%rax
    3715:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    371a:	48 f7 d8             	neg    %rax
    371d:	25 c8 00 00 00       	and    $0xc8,%eax
    3722:	48 01 f8             	add    %rdi,%rax
    3725:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3729:	85 c9                	test   %ecx,%ecx
    372b:	7e 25                	jle    3752 <main+0x1102>
    372d:	48 8b 40 38          	mov    0x38(%rax),%rax
    3731:	48 c1 e1 09          	shl    $0x9,%rcx
    3735:	48 01 c1             	add    %rax,%rcx
    3738:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3740:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3747:	48 05 00 02 00 00    	add    $0x200,%rax
    374d:	48 39 c1             	cmp    %rax,%rcx
    3750:	75 ee                	jne    3740 <main+0x10f0>
    3752:	48 8d 35 ea 3d 00 00 	lea    0x3dea(%rip),%rsi        # 7543 <_IO_stdin_used+0x543>
    3759:	bf 01 00 00 00       	mov    $0x1,%edi
    375e:	31 c0                	xor    %eax,%eax
    3760:	e8 3b ed ff ff       	call   24a0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3765:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    376a:	bf 01 00 00 00       	mov    $0x1,%edi
    376f:	48 8d 35 9a 40 00 00 	lea    0x409a(%rip),%rsi        # 7810 <_IO_stdin_used+0x810>
    3776:	48 8b 08             	mov    (%rax),%rcx
    3779:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3783:	48 f7 e9             	imul   %rcx
    3786:	48 c1 f9 3f          	sar    $0x3f,%rcx
    378a:	31 c0                	xor    %eax,%eax
    378c:	48 d1 fa             	sar    %rdx
    378f:	48 29 ca             	sub    %rcx,%rdx
    3792:	e8 09 ed ff ff       	call   24a0 <__printf_chk@plt>
    3797:	bf 0a 00 00 00       	mov    $0xa,%edi
    379c:	e8 5f eb ff ff       	call   2300 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    37a1:	44 8b 53 08          	mov    0x8(%rbx),%r10d
    37a5:	45 85 d2             	test   %r10d,%r10d
    37a8:	0f 8e 02 01 00 00    	jle    38b0 <main+0x1260>
        total += thread_data[x].tasks[n].n;
    37ae:	45 31 ff             	xor    %r15d,%r15d
    37b1:	48 8b 13             	mov    (%rbx),%rdx
    37b4:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    37b9:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    37be:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    37c3:	4c 89 f9             	mov    %r15,%rcx
    37c6:	4d 89 ef             	mov    %r13,%r15
    37c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    37d0:	49 89 cc             	mov    %rcx,%r12
        sends += thread_data[x].tasks[n].sends;
    37d3:	45 31 ed             	xor    %r13d,%r13d
    37d6:	89 0c 24             	mov    %ecx,(%rsp)
        total += thread_data[x].tasks[n].n;
    37d9:	49 c1 e4 09          	shl    $0x9,%r12
    37dd:	48 89 4c 24 28       	mov    %rcx,0x28(%rsp)
    37e2:	4c 89 e8             	mov    %r13,%rax
    37e5:	4d 89 f5             	mov    %r14,%r13
    37e8:	4c 01 e2             	add    %r12,%rdx
    37eb:	49 89 c6             	mov    %rax,%r14
    37ee:	48 03 ba 08 01 00 00 	add    0x108(%rdx),%rdi
        ingests += thread_data[x].tasks[n].ingest_count;
    37f5:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
        sends += thread_data[x].tasks[n].sends;
    37fc:	4c 03 82 78 01 00 00 	add    0x178(%rdx),%r8
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3803:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    3808:	48 89 7c 24 18       	mov    %rdi,0x18(%rsp)
    380d:	4c 89 44 24 20       	mov    %r8,0x20(%rsp)
    3812:	8b 0c 24             	mov    (%rsp),%ecx
    3815:	8b 54 24 08          	mov    0x8(%rsp),%edx
    3819:	45 89 f0             	mov    %r14d,%r8d
    381c:	bf 01 00 00 00       	mov    $0x1,%edi
    3821:	48 8d 35 28 3d 00 00 	lea    0x3d28(%rip),%rsi        # 7550 <_IO_stdin_used+0x550>
    3828:	31 c0                	xor    %eax,%eax
    382a:	e8 71 ec ff ff       	call   24a0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    382f:	48 8b 13             	mov    (%rbx),%rdx
    3832:	4c 89 f0             	mov    %r14,%rax
    3835:	48 f7 d8             	neg    %rax
    3838:	83 e0 38             	and    $0x38,%eax
    383b:	4a 03 84 22 70 01 00 00 	add    0x170(%rdx,%r12,1),%rax
    3843:	48 8b 08             	mov    (%rax),%rcx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3846:	48 8b 40 08          	mov    0x8(%rax),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    384a:	4c 8b 89 08 03 00 00 	mov    0x308(%rcx),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3851:	4c 8b 91 10 03 00 00 	mov    0x310(%rcx),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3858:	4d 01 e9             	add    %r13,%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    385b:	4d 01 fa             	add    %r15,%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    385e:	4c 03 88 08 03 00 00 	add    0x308(%rax),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3865:	4c 03 90 10 03 00 00 	add    0x310(%rax),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    386c:	4d 89 cd             	mov    %r9,%r13
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    386f:	4d 89 d7             	mov    %r10,%r15
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3872:	4d 85 f6             	test   %r14,%r14
    3875:	75 08                	jne    387f <main+0x122f>
    3877:	41 be 01 00 00 00    	mov    $0x1,%r14d
    387d:	eb 93                	jmp    3812 <main+0x11c2>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    387f:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3884:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    3889:	4d 89 ce             	mov    %r9,%r14
    388c:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    3891:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    3896:	48 83 c1 01          	add    $0x1,%rcx
    389a:	39 4b 08             	cmp    %ecx,0x8(%rbx)
    389d:	0f 8f 2d ff ff ff    	jg     37d0 <main+0x1180>
    38a3:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    38a8:	4d 89 fd             	mov    %r15,%r13
    38ab:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    38b0:	45 31 ff             	xor    %r15d,%r15d
    38b3:	48 83 7b 68 00       	cmpq   $0x0,0x68(%rbx)
    38b8:	4c 8d 25 71 3f 00 00 	lea    0x3f71(%rip),%r12        # 7830 <_IO_stdin_used+0x830>
    38bf:	7e 59                	jle    391a <main+0x12ca>
    38c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    38c8:	48 8b 43 58          	mov    0x58(%rbx),%rax
    38cc:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    38d0:	48 83 ec 08          	sub    $0x8,%rsp
    38d4:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    38d9:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    38dd:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    38e1:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    38e5:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    38e9:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    38ec:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    38f0:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    38f3:	48 f7 e5             	mul    %rbp
    38f6:	8b 49 20             	mov    0x20(%rcx),%ecx
    38f9:	56                   	push   %rsi
    38fa:	31 c0                	xor    %eax,%eax
    38fc:	4c 89 e6             	mov    %r12,%rsi
    38ff:	48 c1 ea 12          	shr    $0x12,%rdx
    3903:	49 89 d1             	mov    %rdx,%r9
    3906:	ba 02 00 00 00       	mov    $0x2,%edx
    390b:	e8 90 eb ff ff       	call   24a0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3910:	41 58                	pop    %r8
    3912:	41 59                	pop    %r9
    3914:	4c 39 7b 68          	cmp    %r15,0x68(%rbx)
    3918:	7f ae                	jg     38c8 <main+0x1278>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    391a:	8b 8b 84 00 00 00    	mov    0x84(%rbx),%ecx
    3920:	85 c9                	test   %ecx,%ecx
    3922:	0f 8e 05 01 00 00    	jle    3a2d <main+0x13dd>
    3928:	4c 89 74 24 48       	mov    %r14,0x48(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    392d:	4c 8b 4b 18          	mov    0x18(%rbx),%r9
    3931:	45 31 e4             	xor    %r12d,%r12d
    3934:	4c 89 6c 24 50       	mov    %r13,0x50(%rsp)
    3939:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3940:	4b 8b 04 e1          	mov    (%r9,%r12,8),%rax
    3944:	45 89 e5             	mov    %r12d,%r13d
    3947:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    394f:	8b 30                	mov    (%rax),%esi
    3951:	85 f6                	test   %esi,%esi
    3953:	0f 8e bd 00 00 00    	jle    3a16 <main+0x13c6>
    3959:	4c 89 64 24 10       	mov    %r12,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    395e:	31 d2                	xor    %edx,%edx
    3960:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3964:	48 89 d7             	mov    %rdx,%rdi
    3967:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3970:	49 89 fc             	mov    %rdi,%r12
    3973:	45 31 ff             	xor    %r15d,%r15d
    3976:	49 c1 e4 08          	shl    $0x8,%r12
    397a:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    397e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    3984:	85 d2                	test   %edx,%edx
    3986:	7e 77                	jle    39ff <main+0x13af>
    3988:	48 89 3c 24          	mov    %rdi,(%rsp)
    398c:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3990:	4c 89 f9             	mov    %r15,%rcx
    3993:	48 83 ec 08          	sub    $0x8,%rsp
    3997:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    399c:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    39a0:	48 c1 e1 05          	shl    $0x5,%rcx
    39a4:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    39ab:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    39af:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    39b3:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    39b6:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    39ba:	4c 2b 01             	sub    (%rcx),%r8
    39bd:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    39be:	48 f7 e5             	mul    %rbp
    39c1:	44 89 e9             	mov    %r13d,%ecx
    39c4:	48 8d 35 b5 3e 00 00 	lea    0x3eb5(%rip),%rsi        # 7880 <_IO_stdin_used+0x880>
    39cb:	31 c0                	xor    %eax,%eax
    39cd:	48 c1 ea 12          	shr    $0x12,%rdx
    39d1:	49 89 d1             	mov    %rdx,%r9
    39d4:	ba 02 00 00 00       	mov    $0x2,%edx
    39d9:	e8 c2 ea ff ff       	call   24a0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    39de:	4c 8b 4b 18          	mov    0x18(%rbx),%r9
    39e2:	5e                   	pop    %rsi
    39e3:	5f                   	pop    %rdi
    39e4:	4b 8b 14 31          	mov    (%r9,%r14,1),%rdx
    39e8:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    39ec:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    39f0:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    39f7:	7f 97                	jg     3990 <main+0x1340>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    39f9:	48 8b 3c 24          	mov    (%rsp),%rdi
    39fd:	8b 32                	mov    (%rdx),%esi
    39ff:	48 83 c7 01          	add    $0x1,%rdi
    3a03:	39 fe                	cmp    %edi,%esi
    3a05:	0f 8f 65 ff ff ff    	jg     3970 <main+0x1320>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3a0b:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
    3a10:	8b 8b 84 00 00 00    	mov    0x84(%rbx),%ecx
    3a16:	49 83 c4 01          	add    $0x1,%r12
    3a1a:	44 39 e1             	cmp    %r12d,%ecx
    3a1d:	0f 8f 1d ff ff ff    	jg     3940 <main+0x12f0>
    3a23:	4c 8b 74 24 48       	mov    0x48(%rsp),%r14
    3a28:	4c 8b 6c 24 50       	mov    0x50(%rsp),%r13
    for (int d = 0 ; d < threads_per_group ; d++) {
    3a2d:	8b 44 24 08          	mov    0x8(%rsp),%eax
    3a31:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    3a37:	48 81 c3 c8 00 00 00 	add    $0xc8,%rbx
    3a3e:	85 c0                	test   %eax,%eax
    3a40:	75 0d                	jne    3a4f <main+0x13ff>
    3a42:	8b 44 24 38          	mov    0x38(%rsp),%eax
    3a46:	89 44 24 08          	mov    %eax,0x8(%rsp)
    3a4a:	e9 69 fc ff ff       	jmp    36b8 <main+0x1068>
    3a4f:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    3a54:	48 8d 35 05 3b 00 00 	lea    0x3b05(%rip),%rsi        # 7560 <_IO_stdin_used+0x560>
    3a5b:	bf 01 00 00 00       	mov    $0x1,%edi
    3a60:	31 c0                	xor    %eax,%eax
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3a62:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    3a6c:	4c 89 fa             	mov    %r15,%rdx
    3a6f:	e8 2c ea ff ff       	call   24a0 <__printf_chk@plt>
    3a74:	bf 0a 00 00 00       	mov    $0xa,%edi
    3a79:	e8 82 e8 ff ff       	call   2300 <putchar@plt>
    3a7e:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    3a83:	bf 01 00 00 00       	mov    $0x1,%edi
    3a88:	48 8d 35 49 3e 00 00 	lea    0x3e49(%rip),%rsi        # 78d8 <_IO_stdin_used+0x8d8>
    3a8f:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3a93:	31 c0                	xor    %eax,%eax
    3a95:	e8 06 ea ff ff       	call   24a0 <__printf_chk@plt>
    3a9a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3a9f:	bf 01 00 00 00       	mov    $0x1,%edi
    3aa4:	48 8d 35 55 3e 00 00 	lea    0x3e55(%rip),%rsi        # 7900 <_IO_stdin_used+0x900>
    3aab:	48 f7 eb             	imul   %rbx
    3aae:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3ab3:	48 c1 f8 3f          	sar    $0x3f,%rax
    3ab7:	48 d1 fa             	sar    %rdx
    3aba:	48 29 c2             	sub    %rax,%rdx
    3abd:	31 c0                	xor    %eax,%eax
    3abf:	e8 dc e9 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3ac4:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    3ac9:	bf 01 00 00 00       	mov    $0x1,%edi
    3ace:	48 8d 35 5b 3e 00 00 	lea    0x3e5b(%rip),%rsi        # 7930 <_IO_stdin_used+0x930>
    3ad5:	48 f7 eb             	imul   %rbx
    3ad8:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    3add:	48 c1 f8 3f          	sar    $0x3f,%rax
    3ae1:	48 d1 fa             	sar    %rdx
    3ae4:	48 29 c2             	sub    %rax,%rdx
    3ae7:	31 c0                	xor    %eax,%eax
    3ae9:	e8 b2 e9 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3aee:	4c 89 f8             	mov    %r15,%rax
    3af1:	bf 01 00 00 00       	mov    $0x1,%edi
    3af6:	48 8d 35 63 3e 00 00 	lea    0x3e63(%rip),%rsi        # 7960 <_IO_stdin_used+0x960>
    3afd:	48 f7 eb             	imul   %rbx
    3b00:	4c 89 f8             	mov    %r15,%rax
    3b03:	48 c1 f8 3f          	sar    $0x3f,%rax
    3b07:	48 d1 fa             	sar    %rdx
    3b0a:	48 29 c2             	sub    %rax,%rdx
    3b0d:	31 c0                	xor    %eax,%eax
    3b0f:	e8 8c e9 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3b14:	4c 89 f0             	mov    %r14,%rax
    3b17:	49 c1 fe 3f          	sar    $0x3f,%r14
    3b1b:	48 8d 35 52 3a 00 00 	lea    0x3a52(%rip),%rsi        # 7574 <_IO_stdin_used+0x574>
    3b22:	48 f7 eb             	imul   %rbx
    3b25:	bf 01 00 00 00       	mov    $0x1,%edi
    3b2a:	31 c0                	xor    %eax,%eax
    3b2c:	48 d1 fa             	sar    %rdx
    3b2f:	4c 29 f2             	sub    %r14,%rdx
    3b32:	e8 69 e9 ff ff       	call   24a0 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3b37:	4c 89 e8             	mov    %r13,%rax
    3b3a:	49 c1 fd 3f          	sar    $0x3f,%r13
    3b3e:	48 8d 35 40 3a 00 00 	lea    0x3a40(%rip),%rsi        # 7585 <_IO_stdin_used+0x585>
    3b45:	48 f7 eb             	imul   %rbx
    3b48:	bf 01 00 00 00       	mov    $0x1,%edi
    3b4d:	48 d1 fa             	sar    %rdx
    3b50:	4c 29 ea             	sub    %r13,%rdx
    3b53:	31 c0                	xor    %eax,%eax
    3b55:	e8 46 e9 ff ff       	call   24a0 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3b5a:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    3b62:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3b6b:	75 25                	jne    3b92 <main+0x1542>
    3b6d:	48 81 c4 98 00 00 00 	add    $0x98,%rsp
    3b74:	31 c0                	xor    %eax,%eax
    3b76:	5b                   	pop    %rbx
    3b77:	5d                   	pop    %rbp
    3b78:	41 5c                	pop    %r12
    3b7a:	41 5d                	pop    %r13
    3b7c:	41 5e                	pop    %r14
    3b7e:	41 5f                	pop    %r15
    3b80:	c3                   	ret
      long v = 0;
    3b81:	31 d2                	xor    %edx,%edx
    3b83:	e9 8a fb ff ff       	jmp    3712 <main+0x10c2>
            exit(1);
    3b88:	bf 01 00 00 00       	mov    $0x1,%edi
    3b8d:	e8 6e e9 ff ff       	call   2500 <exit@plt>
}
    3b92:	e8 d9 e7 ff ff       	call   2370 <__stack_chk_fail@plt>
    3b97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000003ba0 <_start>:
    3ba0:	f3 0f 1e fa          	endbr64
    3ba4:	31 ed                	xor    %ebp,%ebp
    3ba6:	49 89 d1             	mov    %rdx,%r9
    3ba9:	5e                   	pop    %rsi
    3baa:	48 89 e2             	mov    %rsp,%rdx
    3bad:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3bb1:	50                   	push   %rax
    3bb2:	54                   	push   %rsp
    3bb3:	45 31 c0             	xor    %r8d,%r8d
    3bb6:	31 c9                	xor    %ecx,%ecx
    3bb8:	48 8d 3d 91 ea ff ff 	lea    -0x156f(%rip),%rdi        # 2650 <main>
    3bbf:	ff 15 13 64 00 00    	call   *0x6413(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3bc5:	f4                   	hlt
    3bc6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003bd0 <deregister_tm_clones>:
    3bd0:	48 8d 3d 49 64 00 00 	lea    0x6449(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3bd7:	48 8d 05 42 64 00 00 	lea    0x6442(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    3bde:	48 39 f8             	cmp    %rdi,%rax
    3be1:	74 15                	je     3bf8 <deregister_tm_clones+0x28>
    3be3:	48 8b 05 f6 63 00 00 	mov    0x63f6(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    3bea:	48 85 c0             	test   %rax,%rax
    3bed:	74 09                	je     3bf8 <deregister_tm_clones+0x28>
    3bef:	ff e0                	jmp    *%rax
    3bf1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3bf8:	c3                   	ret
    3bf9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c00 <register_tm_clones>:
    3c00:	48 8d 3d 19 64 00 00 	lea    0x6419(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3c07:	48 8d 35 12 64 00 00 	lea    0x6412(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    3c0e:	48 29 fe             	sub    %rdi,%rsi
    3c11:	48 89 f0             	mov    %rsi,%rax
    3c14:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3c18:	48 c1 f8 03          	sar    $0x3,%rax
    3c1c:	48 01 c6             	add    %rax,%rsi
    3c1f:	48 d1 fe             	sar    %rsi
    3c22:	74 14                	je     3c38 <register_tm_clones+0x38>
    3c24:	48 8b 05 c5 63 00 00 	mov    0x63c5(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    3c2b:	48 85 c0             	test   %rax,%rax
    3c2e:	74 08                	je     3c38 <register_tm_clones+0x38>
    3c30:	ff e0                	jmp    *%rax
    3c32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c38:	c3                   	ret
    3c39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c40 <__do_global_dtors_aux>:
    3c40:	f3 0f 1e fa          	endbr64
    3c44:	80 3d dd 63 00 00 00 	cmpb   $0x0,0x63dd(%rip)        # a028 <completed.0>
    3c4b:	75 2b                	jne    3c78 <__do_global_dtors_aux+0x38>
    3c4d:	55                   	push   %rbp
    3c4e:	48 83 3d a2 63 00 00 00 	cmpq   $0x0,0x63a2(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3c56:	48 89 e5             	mov    %rsp,%rbp
    3c59:	74 0c                	je     3c67 <__do_global_dtors_aux+0x27>
    3c5b:	48 8b 3d a6 63 00 00 	mov    0x63a6(%rip),%rdi        # a008 <__dso_handle>
    3c62:	e8 79 e6 ff ff       	call   22e0 <__cxa_finalize@plt>
    3c67:	e8 64 ff ff ff       	call   3bd0 <deregister_tm_clones>
    3c6c:	c6 05 b5 63 00 00 01 	movb   $0x1,0x63b5(%rip)        # a028 <completed.0>
    3c73:	5d                   	pop    %rbp
    3c74:	c3                   	ret
    3c75:	0f 1f 00             	nopl   (%rax)
    3c78:	c3                   	ret
    3c79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c80 <frame_dummy>:
    3c80:	f3 0f 1e fa          	endbr64
    3c84:	e9 77 ff ff ff       	jmp    3c00 <register_tm_clones>
    3c89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c90 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3c90:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3c94:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3c9b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    3c9f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3ca7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    3cab:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3caf:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3cb6:	48 85 c9             	test   %rcx,%rcx
    3cb9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3cc0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3cc4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3cc8:	31 c0                	xor    %eax,%eax
    3cca:	c3                   	ret
    3ccb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003cd0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3cd0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3cd4:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    3cdb:	85 c9                	test   %ecx,%ecx
    3cdd:	7e 4f                	jle    3d2e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3cdf:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3ce6:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    3ced:	48 c1 e1 09          	shl    $0x9,%rcx
    3cf1:	48 8b 50 18          	mov    0x18(%rax),%rdx
    3cf5:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3cf9:	48 8b 70 38          	mov    0x38(%rax),%rsi
    3cfd:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3cff:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    3d03:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3d08:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3d10:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3d18:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3d23:	48 05 00 02 00 00    	add    $0x200,%rax
    3d29:	48 39 c1             	cmp    %rax,%rcx
    3d2c:	75 da                	jne    3d08 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    3d2e:	0f ae f8             	sfence
}
    3d31:	31 c0                	xor    %eax,%eax
    3d33:	c3                   	ret
    3d34:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3d3f:	90                   	nop

0000000000003d40 <external_thread>:
void * external_thread(void *arg) {
    3d40:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3d44:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    3d48:	0f 85 fb 00 00 00    	jne    3e49 <external_thread+0x109>
void * external_thread(void *arg) {
    3d4e:	41 57                	push   %r15
    3d50:	49 89 ff             	mov    %rdi,%r15
    3d53:	41 56                	push   %r14
    3d55:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    3d57:	4c 8d 2d a6 32 00 00 	lea    0x32a6(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    3d5e:	41 54                	push   %r12
    3d60:	55                   	push   %rbp
    3d61:	53                   	push   %rbx
    3d62:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    3d66:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    3d6c:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    3d70:	85 c9                	test   %ecx,%ecx
    3d72:	7e 6e                	jle    3de2 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3d74:	45 31 e4             	xor    %r12d,%r12d
    3d77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3d80:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    3d88:	31 db                	xor    %ebx,%ebx
    3d8a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3d8e:	48 8b 06             	mov    (%rsi),%rax
    3d91:	8b 10                	mov    (%rax),%edx
    3d93:	85 d2                	test   %edx,%edx
    3d95:	7e 2a                	jle    3dc1 <external_thread+0x81>
    3d97:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    3d9b:	48 89 dd             	mov    %rbx,%rbp
    3d9e:	48 c1 e5 08          	shl    $0x8,%rbp
    3da2:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    3da6:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    3dad:	45 85 c0             	test   %r8d,%r8d
    3db0:	74 36                	je     3de8 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3db2:	48 83 c3 01          	add    $0x1,%rbx
    3db6:	39 da                	cmp    %ebx,%edx
    3db8:	7f e1                	jg     3d9b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    3dba:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    3dc1:	49 83 c4 01          	add    $0x1,%r12
    3dc5:	44 39 e1             	cmp    %r12d,%ecx
    3dc8:	7f b6                	jg     3d80 <external_thread+0x40>
  while (data->running == 1) {
    3dca:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    3dcf:	74 9f                	je     3d70 <external_thread+0x30>
}
    3dd1:	48 83 c4 08          	add    $0x8,%rsp
    3dd5:	31 c0                	xor    %eax,%eax
    3dd7:	5b                   	pop    %rbx
    3dd8:	5d                   	pop    %rbp
    3dd9:	41 5c                	pop    %r12
    3ddb:	41 5d                	pop    %r13
    3ddd:	41 5e                	pop    %r14
    3ddf:	41 5f                	pop    %r15
    3de1:	c3                   	ret
  while (data->running == 1) {
    3de2:	eb fe                	jmp    3de2 <external_thread+0xa2>
    3de4:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    3de8:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    3deb:	48 8b 06             	mov    (%rsi),%rax
    3dee:	48 8b 78 08          	mov    0x8(%rax),%rdi
    3df2:	48 01 ef             	add    %rbp,%rdi
    3df5:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    3dfc:	48 c1 e6 05          	shl    $0x5,%rsi
    3e00:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    3e07:	bf 04 00 00 00       	mov    $0x4,%edi
    3e0c:	e8 2f e5 ff ff       	call   2340 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    3e11:	49 8b 47 50          	mov    0x50(%r15),%rax
    3e15:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    3e19:	48 8b 40 08          	mov    0x8(%rax),%rax
    3e1d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    3e28:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3e2b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    3e2f:	48 83 c3 01          	add    $0x1,%rbx
    3e33:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3e37:	48 8b 06             	mov    (%rsi),%rax
    3e3a:	8b 10                	mov    (%rax),%edx
    3e3c:	39 da                	cmp    %ebx,%edx
    3e3e:	0f 8f 53 ff ff ff    	jg     3d97 <external_thread+0x57>
    3e44:	e9 71 ff ff ff       	jmp    3dba <external_thread+0x7a>
}
    3e49:	31 c0                	xor    %eax,%eax
    3e4b:	c3                   	ret
    3e4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003e50 <timer_thread>:
void* timer_thread(void *arg) {
    3e50:	f3 0f 1e fa          	endbr64
    3e54:	41 57                	push   %r15
    3e56:	48 8d 35 b3 31 00 00 	lea    0x31b3(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3e5d:	41 56                	push   %r14
    3e5f:	41 55                	push   %r13
    3e61:	41 54                	push   %r12
    3e63:	55                   	push   %rbp
    3e64:	53                   	push   %rbx
    3e65:	48 89 fb             	mov    %rdi,%rbx
    3e68:	48 83 ec 68          	sub    $0x68,%rsp
    3e6c:	8b 57 04             	mov    0x4(%rdi),%edx
    3e6f:	bf 01 00 00 00       	mov    $0x1,%edi
    3e74:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3e7d:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    3e82:	31 c0                	xor    %eax,%eax
    3e84:	e8 17 e6 ff ff       	call   24a0 <__printf_chk@plt>
  struct timespec preempt = {
    3e89:	66 0f 6f 05 ef 3c 00 00 	movdqa 0x3cef(%rip),%xmm0        # 7b80 <_IO_stdin_used+0xb80>
    3e91:	ba 88 13 00 00       	mov    $0x1388,%edx
    3e96:	31 c0                	xor    %eax,%eax
    3e98:	48 8d 35 83 31 00 00 	lea    0x3183(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3e9f:	bf 01 00 00 00       	mov    $0x1,%edi
    3ea4:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
    3ea9:	e8 f2 e5 ff ff       	call   24a0 <__printf_chk@plt>
  while (data->running && n < times) {
    3eae:	8b 6b 44             	mov    0x44(%rbx),%ebp
    3eb1:	85 ed                	test   %ebp,%ebp
    3eb3:	0f 84 9b 00 00 00    	je     3f54 <timer_thread+0x104>
  int n = 0;
    3eb9:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    3ebc:	31 ed                	xor    %ebp,%ebp
    3ebe:	4c 8d 74 24 10       	lea    0x10(%rsp),%r14
    y++;
    3ec3:	45 31 e4             	xor    %r12d,%r12d
    3ec6:	4c 8d 6c 24 20       	lea    0x20(%rsp),%r13
    nanosleep(&preempt , &rem2);
    3ecb:	4c 89 ef             	mov    %r13,%rdi
    3ece:	4c 89 f6             	mov    %r14,%rsi
    n++;
    3ed1:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3ed5:	e8 b6 e4 ff ff       	call   2390 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3eda:	48 63 43 30          	movslq 0x30(%rbx),%rax
    y++;
    3ede:	8d 7d 01             	lea    0x1(%rbp),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3ee1:	85 c0                	test   %eax,%eax
    3ee3:	7e 48                	jle    3f2d <timer_thread+0xdd>
    3ee5:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3ee9:	4c 63 c5             	movslq %ebp,%r8
    3eec:	49 c1 e0 09          	shl    $0x9,%r8
    3ef0:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3ef4:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3ef8:	4c 8b 19             	mov    (%rcx),%r11
    3efb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3efd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3f01:	99                   	cltd
    3f02:	41 f7 7b 40          	idivl  0x40(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    3f06:	49 8b 73 38          	mov    0x38(%r11),%rsi
    3f0a:	48 63 d2             	movslq %edx,%rdx
    3f0d:	48 c1 e2 09          	shl    $0x9,%rdx
    3f11:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3f1c:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f28:	49 39 c9             	cmp    %rcx,%r9
    3f2b:	75 cb                	jne    3ef8 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    3f2d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3f30:	48 8b 43 18          	mov    0x18(%rbx),%rax
  while (data->running && n < times) {
    3f34:	8b 4b 44             	mov    0x44(%rbx),%ecx
    if (y >= data->threads[0]->task_count) {
    3f37:	48 8b 00             	mov    (%rax),%rax
    y++;
    3f3a:	39 78 40             	cmp    %edi,0x40(%rax)
    3f3d:	41 0f 4e fc          	cmovle %r12d,%edi
    3f41:	89 fd                	mov    %edi,%ebp
  while (data->running && n < times) {
    3f43:	85 c9                	test   %ecx,%ecx
    3f45:	74 0d                	je     3f54 <timer_thread+0x104>
    3f47:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    3f4e:	0f 85 77 ff ff ff    	jne    3ecb <timer_thread+0x7b>
    3f54:	48 8d 3d dd 30 00 00 	lea    0x30dd(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3f5b:	e8 c0 e3 ff ff       	call   2320 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f60:	48 63 53 30          	movslq 0x30(%rbx),%rdx
    3f64:	85 d2                	test   %edx,%edx
    3f66:	7e 6d                	jle    3fd5 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    3f68:	48 63 43 40          	movslq 0x40(%rbx),%rax
    3f6c:	85 c0                	test   %eax,%eax
    3f6e:	7e 65                	jle    3fd5 <timer_thread+0x185>
    3f70:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3f74:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    3f78:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3f80:	31 c9                	xor    %ecx,%ecx
    3f82:	48 89 c6             	mov    %rax,%rsi
    3f85:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3f89:	48 8b 40 38          	mov    0x38(%rax),%rax
    3f8d:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    3f91:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3f97:	74 17                	je     3fb0 <timer_thread+0x160>
    3f99:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3fa3:	48 05 00 02 00 00    	add    $0x200,%rax
    3fa9:	48 39 c2             	cmp    %rax,%rdx
    3fac:	74 1e                	je     3fcc <timer_thread+0x17c>
    3fae:	66 90                	xchg   %ax,%ax
      data->threads[x]->tasks[y].sending = 0;
    3fb0:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3fba:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3fc0:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3fc7:	48 39 c2             	cmp    %rax,%rdx
    3fca:	75 e4                	jne    3fb0 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3fcc:	48 83 c1 08          	add    $0x8,%rcx
    3fd0:	48 39 cf             	cmp    %rcx,%rdi
    3fd3:	75 b0                	jne    3f85 <timer_thread+0x135>
  asm volatile ("mfence" ::: "memory");
    3fd5:	0f ae f0             	mfence
  struct timespec drain = {
    3fd8:	66 0f 6f 05 b0 3b 00 00 	movdqa 0x3bb0(%rip),%xmm0        # 7b90 <_IO_stdin_used+0xb90>
    3fe0:	4c 8d 3d 76 30 00 00 	lea    0x3076(%rip),%r15        # 705d <_IO_stdin_used+0x5d>
    3fe7:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3fec:	48 63 43 28          	movslq 0x28(%rbx),%rax
    y++;
    3ff0:	8d 7d 01             	lea    0x1(%rbp),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ff3:	85 c0                	test   %eax,%eax
    3ff5:	7e 4e                	jle    4045 <timer_thread+0x1f5>
    3ff7:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3ffb:	4c 63 c5             	movslq %ebp,%r8
    3ffe:	49 c1 e0 09          	shl    $0x9,%r8
    4002:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4006:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    4010:	4c 8b 11             	mov    (%rcx),%r10
    4013:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    4015:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4019:	99                   	cltd
    401a:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    401e:	49 8b 72 38          	mov    0x38(%r10),%rsi
    4022:	48 63 d2             	movslq %edx,%rdx
    4025:	48 c1 e2 09          	shl    $0x9,%rdx
    4029:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4034:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4040:	4c 39 c9             	cmp    %r9,%rcx
    4043:	75 cb                	jne    4010 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    4045:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4048:	48 8b 43 18          	mov    0x18(%rbx),%rax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    404c:	44 8b 53 30          	mov    0x30(%rbx),%r10d
    if (y >= data->threads[0]->task_count) {
    4050:	48 8b 00             	mov    (%rax),%rax
    y++;
    4053:	39 78 40             	cmp    %edi,0x40(%rax)
    4056:	b8 00 00 00 00       	mov    $0x0,%eax
    405b:	0f 4f c7             	cmovg  %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    405e:	45 85 d2             	test   %r10d,%r10d
    4061:	0f 8e 45 01 00 00    	jle    41ac <timer_thread+0x35c>
    int all_empty = 1;
    4067:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    406b:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    406e:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    4074:	0f 1f 40 00          	nopl   0x0(%rax)
      for (int y = 0 ; y < 2 ; y++) {
    4078:	45 31 ed             	xor    %r13d,%r13d
    407b:	44 89 f5             	mov    %r14d,%ebp
    407e:	4e 8d 24 f5 00 00 00 00 	lea    0x0(,%r14,8),%r12
    4086:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4089:	45 85 d2             	test   %r10d,%r10d
    408c:	0f 8e bd 00 00 00    	jle    414f <timer_thread+0x2ff>
    4092:	44 89 5c 24 08       	mov    %r11d,0x8(%rsp)
    4097:	4d 89 eb             	mov    %r13,%r11
      y = 0;
    409a:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    409c:	45 31 c0             	xor    %r8d,%r8d
    409f:	49 c1 e3 09          	shl    $0x9,%r11
    40a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (x == k) { continue; }
    40a8:	45 39 f0             	cmp    %r14d,%r8d
    40ab:	74 36                	je     40e3 <timer_thread+0x293>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    40ad:	48 8b 53 18          	mov    0x18(%rbx),%rdx
    40b1:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    40b5:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    40b9:	4a 8b 8c 1a 70 01 00 00 	mov    0x170(%rdx,%r11,1),%rcx
    40c1:	48 01 c1             	add    %rax,%rcx
    40c4:	48 8b 11             	mov    (%rcx),%rdx
    40c7:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    40cb:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    40d2:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    40d9:	4d 85 c9             	test   %r9,%r9
    40dc:	7f 2a                	jg     4108 <timer_thread+0x2b8>
    40de:	48 85 f6             	test   %rsi,%rsi
    40e1:	7f 25                	jg     4108 <timer_thread+0x2b8>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    40e3:	41 83 c0 01          	add    $0x1,%r8d
    40e7:	48 83 c0 38          	add    $0x38,%rax
    40eb:	45 39 d0             	cmp    %r10d,%r8d
    40ee:	75 b8                	jne    40a8 <timer_thread+0x258>
      for (int y = 0 ; y < 2 ; y++) {
    40f0:	49 83 fd 01          	cmp    $0x1,%r13
    40f4:	0f 84 9e 00 00 00    	je     4198 <timer_thread+0x348>
    40fa:	49 83 c5 01          	add    $0x1,%r13
    40fe:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4101:	eb 94                	jmp    4097 <timer_thread+0x247>
    4103:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4108:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
    410e:	48 83 ec 08          	sub    $0x8,%rsp
    4112:	89 f9                	mov    %edi,%ecx
    4114:	bf 01 00 00 00       	mov    $0x1,%edi
    4119:	50                   	push   %rax
    411a:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    4120:	89 ea                	mov    %ebp,%edx
    4122:	50                   	push   %rax
    4123:	31 c0                	xor    %eax,%eax
    4125:	56                   	push   %rsi
    4126:	4c 89 fe             	mov    %r15,%rsi
    4129:	e8 72 e3 ff ff       	call   24a0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    412e:	44 8b 53 30          	mov    0x30(%rbx),%r10d
      for (int y = 0 ; y < 2 ; y++) {
    4132:	48 83 c4 20          	add    $0x20,%rsp
    4136:	49 83 fd 01          	cmp    $0x1,%r13
    413a:	74 44                	je     4180 <timer_thread+0x330>
    413c:	49 83 c5 01          	add    $0x1,%r13
    4140:	45 31 db             	xor    %r11d,%r11d
    4143:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4146:	45 85 d2             	test   %r10d,%r10d
    4149:	0f 8f 43 ff ff ff    	jg     4092 <timer_thread+0x242>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    414f:	49 83 c6 01          	add    $0x1,%r14
    4153:	45 39 f2             	cmp    %r14d,%r10d
    4156:	0f 8f 1c ff ff ff    	jg     4078 <timer_thread+0x228>
    415c:	8b 6c 24 0c          	mov    0xc(%rsp),%ebp
    if (all_empty == 1) {
    4160:	41 83 fb 01          	cmp    $0x1,%r11d
    4164:	74 46                	je     41ac <timer_thread+0x35c>
      nanosleep(&drain , &drainrem);
    4166:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    416b:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    4170:	e8 1b e2 ff ff       	call   2390 <nanosleep@plt>
    4175:	e9 72 fe ff ff       	jmp    3fec <timer_thread+0x19c>
    417a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4180:	49 83 c6 01          	add    $0x1,%r14
    4184:	45 31 db             	xor    %r11d,%r11d
    4187:	45 39 f2             	cmp    %r14d,%r10d
    418a:	0f 8f e8 fe ff ff    	jg     4078 <timer_thread+0x228>
    4190:	eb ca                	jmp    415c <timer_thread+0x30c>
    4192:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4198:	49 83 c6 01          	add    $0x1,%r14
    419c:	44 8b 5c 24 08       	mov    0x8(%rsp),%r11d
    41a1:	45 39 f2             	cmp    %r14d,%r10d
    41a4:	0f 8f ce fe ff ff    	jg     4078 <timer_thread+0x228>
    41aa:	eb b0                	jmp    415c <timer_thread+0x30c>
    41ac:	48 8d 3d a1 2e 00 00 	lea    0x2ea1(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    41b3:	e8 68 e1 ff ff       	call   2320 <puts@plt>
  while (data->running) {
    41b8:	8b 53 44             	mov    0x44(%rbx),%edx
    41bb:	85 d2                	test   %edx,%edx
    41bd:	0f 84 eb 00 00 00    	je     42ae <timer_thread+0x45e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    41c3:	8b 43 2c             	mov    0x2c(%rbx),%eax
    41c6:	31 ed                	xor    %ebp,%ebp
    41c8:	4c 8d 25 ab 2e 00 00 	lea    0x2eab(%rip),%r12        # 707a <_IO_stdin_used+0x7a>
    41cf:	4c 8d 2d bf 2e 00 00 	lea    0x2ebf(%rip),%r13        # 7095 <_IO_stdin_used+0x95>
    41d6:	85 c0                	test   %eax,%eax
    41d8:	7e 39                	jle    4213 <timer_thread+0x3c3>
    41da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    41e0:	31 c0                	xor    %eax,%eax
    41e2:	89 ea                	mov    %ebp,%edx
    41e4:	4c 89 e6             	mov    %r12,%rsi
    41e7:	bf 01 00 00 00       	mov    $0x1,%edi
    41ec:	e8 af e2 ff ff       	call   24a0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    41f1:	48 8b 43 18          	mov    0x18(%rbx),%rax
    41f5:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
      if (data->threads[x]->type == IO) {
    41f9:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    41fd:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4204:	0f 84 d1 00 00 00    	je     42db <timer_thread+0x48b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    420a:	48 83 c5 01          	add    $0x1,%rbp
    420e:	39 6b 2c             	cmp    %ebp,0x2c(%rbx)
    4211:	7f cd                	jg     41e0 <timer_thread+0x390>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4213:	48 63 53 30          	movslq 0x30(%rbx),%rdx
    4217:	85 d2                	test   %edx,%edx
    4219:	7e 7d                	jle    4298 <timer_thread+0x448>
      for (int y = 0 ; y < data->task_count ; y++) {
    421b:	8b 43 40             	mov    0x40(%rbx),%eax
    421e:	85 c0                	test   %eax,%eax
    4220:	7e 76                	jle    4298 <timer_thread+0x448>
    4222:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4225:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    4229:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4231:	31 c9                	xor    %ecx,%ecx
    4233:	48 c1 e6 09          	shl    $0x9,%rsi
    4237:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4240:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4244:	48 8b 40 38          	mov    0x38(%rax),%rax
    4248:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    424c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4252:	74 1c                	je     4270 <timer_thread+0x420>
    4254:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    425e:	48 05 00 02 00 00    	add    $0x200,%rax
    4264:	48 39 d0             	cmp    %rdx,%rax
    4267:	74 26                	je     428f <timer_thread+0x43f>
    4269:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4270:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    427a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4280:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    428a:	48 39 d0             	cmp    %rdx,%rax
    428d:	75 e1                	jne    4270 <timer_thread+0x420>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    428f:	48 83 c1 08          	add    $0x8,%rcx
    4293:	48 39 f9             	cmp    %rdi,%rcx
    4296:	75 a8                	jne    4240 <timer_thread+0x3f0>
    asm volatile ("mfence" ::: "memory");
    4298:	0f ae f0             	mfence
    429b:	48 8d 3d 05 2e 00 00 	lea    0x2e05(%rip),%rdi        # 70a7 <_IO_stdin_used+0xa7>
    42a2:	e8 79 e0 ff ff       	call   2320 <puts@plt>
    data->running = 0;
    42a7:	c7 43 44 00 00 00 00 	movl   $0x0,0x44(%rbx)
    42ae:	48 8d 3d f9 2d 00 00 	lea    0x2df9(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    42b5:	e8 66 e0 ff ff       	call   2320 <puts@plt>
}
    42ba:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    42bf:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    42c8:	75 40                	jne    430a <timer_thread+0x4ba>
    42ca:	48 83 c4 68          	add    $0x68,%rsp
    42ce:	31 c0                	xor    %eax,%eax
    42d0:	5b                   	pop    %rbx
    42d1:	5d                   	pop    %rbp
    42d2:	41 5c                	pop    %r12
    42d4:	41 5d                	pop    %r13
    42d6:	41 5e                	pop    %r14
    42d8:	41 5f                	pop    %r15
    42da:	c3                   	ret
    42db:	4c 89 ef             	mov    %r13,%rdi
    42de:	e8 3d e0 ff ff       	call   2320 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    42e3:	48 8b 43 18          	mov    0x18(%rbx),%rax
    42e7:	be 01 00 00 00       	mov    $0x1,%esi
    42ec:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    42f0:	48 83 c5 01          	add    $0x1,%rbp
        eventfd_write(data->threads[x]->_eventfd, 1);
    42f4:	8b 78 60             	mov    0x60(%rax),%edi
    42f7:	e8 54 e1 ff ff       	call   2450 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    42fc:	39 6b 2c             	cmp    %ebp,0x2c(%rbx)
    42ff:	0f 8f db fe ff ff    	jg     41e0 <timer_thread+0x390>
    4305:	e9 09 ff ff ff       	jmp    4213 <timer_thread+0x3c3>
}
    430a:	e8 61 e0 ff ff       	call   2370 <__stack_chk_fail@plt>
    430f:	90                   	nop

0000000000004310 <sendm.part.0>:
int sendm(struct BarrierTask *data) {
    4310:	41 57                	push   %r15
    4312:	41 56                	push   %r14
    4314:	41 55                	push   %r13
    4316:	41 54                	push   %r12
    4318:	55                   	push   %rbp
    4319:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    431a:	8b af 40 01 00 00    	mov    0x140(%rdi),%ebp
    4320:	85 ed                	test   %ebp,%ebp
    4322:	0f 8e 9a 01 00 00    	jle    44c2 <sendm.part.0+0x1b2>
        if (n == data->thread->real_thread_index) { continue; }
    4328:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    432f:	49 89 ff             	mov    %rdi,%r15
    4332:	45 31 f6             	xor    %r14d,%r14d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    4335:	45 31 ed             	xor    %r13d,%r13d
    4338:	41 89 ec             	mov    %ebp,%r12d
        if (n == data->thread->real_thread_index) { continue; }
    433b:	8b 40 08             	mov    0x8(%rax),%eax
    433e:	89 44 24 cc          	mov    %eax,-0x34(%rsp)
    4342:	48 8d 87 88 01 00 00 	lea    0x188(%rdi),%rax
    4349:	48 89 44 24 e8       	mov    %rax,-0x18(%rsp)
    434e:	48 8d 87 90 01 00 00 	lea    0x190(%rdi),%rax
    4355:	48 89 44 24 f0       	mov    %rax,-0x10(%rsp)
    435a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4360:	44 39 6c 24 cc       	cmp    %r13d,-0x34(%rsp)
    4365:	0f 84 46 01 00 00    	je     44b1 <sendm.part.0+0x1a1>
        struct Data *them = data->mailboxes[n].higher;
    436b:	49 8b 87 70 01 00 00 	mov    0x170(%r15),%rax
    4372:	4c 01 f0             	add    %r14,%rax
        if (data->mailboxes[n].pending != NULL) {
    4375:	48 8b 48 10          	mov    0x10(%rax),%rcx
        struct Data *them = data->mailboxes[n].higher;
    4379:	48 8b 50 08          	mov    0x8(%rax),%rdx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    437d:	44 8b 40 30          	mov    0x30(%rax),%r8d
        if (data->mailboxes[n].pending != NULL) {
    4381:	48 85 c9             	test   %rcx,%rcx
    4384:	0f 84 46 01 00 00    	je     44d0 <sendm.part.0+0x1c0>
          data->mailboxes[n].higher = them;
    438a:	48 89 48 08          	mov    %rcx,0x8(%rax)
          data->mailboxes[n].pending = NULL;
    438e:	48 c7 40 10 00 00 00 00 	movq   $0x0,0x10(%rax)
          them->available_sending = 1;
    4396:	c7 81 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rcx)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    43a0:	41 83 f8 02          	cmp    $0x2,%r8d
    43a4:	0f 84 29 02 00 00    	je     45d3 <sendm.part.0+0x2c3>
        for (; them->messages_count < min;) {
    43aa:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    43b1:	48 63 a9 88 00 00 00 	movslq 0x88(%rcx),%rbp
    43b8:	48 39 ee             	cmp    %rbp,%rsi
    43bb:	0f 8d f0 00 00 00    	jge    44b1 <sendm.part.0+0x1a1>
    43c1:	49 8b 87 08 01 00 00 	mov    0x108(%r15),%rax
    43c8:	48 39 ee             	cmp    %rbp,%rsi
    43cb:	49 89 eb             	mov    %rbp,%r11
          them->messages[them->messages_count++] = data->message; 
    43ce:	48 8b 11             	mov    (%rcx),%rdx
    43d1:	41 0f 9c c1          	setl   %r9b
    43d5:	49 29 f3             	sub    %rsi,%r11
    43d8:	48 89 44 24 d0       	mov    %rax,-0x30(%rsp)
    43dd:	48 8b 81 08 03 00 00 	mov    0x308(%rcx),%rax
    43e4:	49 8d 5b ff          	lea    -0x1(%r11),%rbx
    43e8:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    43ed:	48 89 44 24 d8       	mov    %rax,-0x28(%rsp)
    43f2:	48 83 fb 02          	cmp    $0x2,%rbx
    43f6:	0f 86 c4 01 00 00    	jbe    45c0 <sendm.part.0+0x2b0>
    43fc:	45 84 c9             	test   %r9b,%r9b
    43ff:	0f 84 bb 01 00 00    	je     45c0 <sendm.part.0+0x2b0>
    4405:	4c 8d 14 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r10
    440d:	4a 8d 04 12          	lea    (%rdx,%r10,1),%rax
    4411:	48 89 44 24 e0       	mov    %rax,-0x20(%rsp)
    4416:	49 89 c3             	mov    %rax,%r11
    4419:	48 8d 04 ea          	lea    (%rdx,%rbp,8),%rax
    441d:	48 39 44 24 e8       	cmp    %rax,-0x18(%rsp)
    4422:	0f 83 e8 00 00 00    	jae    4510 <sendm.part.0+0x200>
    4428:	4c 89 d8             	mov    %r11,%rax
    442b:	4c 8b 5c 24 f0       	mov    -0x10(%rsp),%r11
    4430:	48 89 f7             	mov    %rsi,%rdi
    4433:	4c 39 d8             	cmp    %r11,%rax
    4436:	0f 83 d4 00 00 00    	jae    4510 <sendm.part.0+0x200>
    443c:	0f 1f 40 00          	nopl   0x0(%rax)
    4440:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    4447:	48 89 04 fa          	mov    %rax,(%rdx,%rdi,8)
        for (; them->messages_count < min;) {
    444b:	48 83 c7 01          	add    $0x1,%rdi
    444f:	48 39 fd             	cmp    %rdi,%rbp
    4452:	7f ec                	jg     4440 <sendm.part.0+0x130>
    4454:	0f 1f 40 00          	nopl   0x0(%rax)
    4458:	31 ff                	xor    %edi,%edi
    445a:	45 84 c9             	test   %r9b,%r9b
    445d:	4c 8b 5c 24 d0       	mov    -0x30(%rsp),%r11
    4462:	48 0f 45 fb          	cmovne %rbx,%rdi
    4466:	4d 8d 5c 3b 01       	lea    0x1(%r11,%rdi,1),%r11
    446b:	48 8d 74 3e 01       	lea    0x1(%rsi,%rdi,1),%rsi
    4470:	4d 89 9f 08 01 00 00 	mov    %r11,0x108(%r15)
    4477:	4c 8b 5c 24 d8       	mov    -0x28(%rsp),%r11
    447c:	48 89 b1 80 00 00 00 	mov    %rsi,0x80(%rcx)
    4483:	48 8d 34 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rsi
    448b:	bb 00 00 00 00       	mov    $0x0,%ebx
    4490:	48 0f 44 f3          	cmove  %rbx,%rsi
    4494:	4d 8d 5c 3b 01       	lea    0x1(%r11,%rdi,1),%r11
    4499:	4c 01 d2             	add    %r10,%rdx
    449c:	4c 89 99 08 03 00 00 	mov    %r11,0x308(%rcx)
    44a3:	48 89 04 32          	mov    %rax,(%rdx,%rsi,1)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    44a7:	41 83 f8 02          	cmp    $0x2,%r8d
    44ab:	0f 84 df 00 00 00    	je     4590 <sendm.part.0+0x280>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    44b1:	41 83 c5 01          	add    $0x1,%r13d
    44b5:	49 83 c6 38          	add    $0x38,%r14
    44b9:	45 39 e5             	cmp    %r12d,%r13d
    44bc:	0f 85 9e fe ff ff    	jne    4360 <sendm.part.0+0x50>
      asm volatile ("sfence" ::: "memory");
    44c2:	0f ae f8             	sfence
}
    44c5:	5b                   	pop    %rbx
    44c6:	5d                   	pop    %rbp
    44c7:	41 5c                	pop    %r12
    44c9:	41 5d                	pop    %r13
    44cb:	41 5e                	pop    %r14
    44cd:	41 5f                	pop    %r15
    44cf:	c3                   	ret
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    44d0:	41 83 f8 02          	cmp    $0x2,%r8d
    44d4:	0f 85 12 01 00 00    	jne    45ec <sendm.part.0+0x2dc>
    44da:	8b 82 00 01 00 00    	mov    0x100(%rdx),%eax
    44e0:	83 f8 01             	cmp    $0x1,%eax
    44e3:	0f 84 e7 00 00 00    	je     45d0 <sendm.part.0+0x2c0>
        else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    44e9:	85 c0                	test   %eax,%eax
    44eb:	74 c4                	je     44b1 <sendm.part.0+0x1a1>
        for (; them->messages_count < min;) {
    44ed:	48 8b b2 80 00 00 00 	mov    0x80(%rdx),%rsi
    44f4:	48 63 aa 88 00 00 00 	movslq 0x88(%rdx),%rbp
    44fb:	48 39 ee             	cmp    %rbp,%rsi
    44fe:	7d b1                	jge    44b1 <sendm.part.0+0x1a1>
    4500:	48 89 d1             	mov    %rdx,%rcx
    4503:	e9 b9 fe ff ff       	jmp    43c1 <sendm.part.0+0xb1>
    4508:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4510:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    4515:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    451c:	48 8b 7c 24 e0       	mov    -0x20(%rsp),%rdi
    4521:	49 d1 eb             	shr    %r11
    4524:	66 48 0f 6e c0       	movq   %rax,%xmm0
    4529:	4c 89 dd             	mov    %r11,%rbp
    452c:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    4530:	48 c1 e5 04          	shl    $0x4,%rbp
    4534:	49 89 eb             	mov    %rbp,%r11
    4537:	48 01 fd             	add    %rdi,%rbp
    453a:	41 83 e3 10          	and    $0x10,%r11d
    453e:	74 11                	je     4551 <sendm.part.0+0x241>
          them->messages[them->messages_count++] = data->message; 
    4540:	0f 11 07             	movups %xmm0,(%rdi)
        for (; them->messages_count < min;) {
    4543:	48 83 c7 10          	add    $0x10,%rdi
    4547:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    454c:	48 39 fd             	cmp    %rdi,%rbp
    454f:	74 1a                	je     456b <sendm.part.0+0x25b>
    4551:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
          them->messages[them->messages_count++] = data->message; 
    4556:	0f 11 07             	movups %xmm0,(%rdi)
    4559:	48 83 c7 20          	add    $0x20,%rdi
    455d:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    4561:	48 39 fd             	cmp    %rdi,%rbp
    4564:	75 f0                	jne    4556 <sendm.part.0+0x246>
    4566:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    456b:	4c 89 df             	mov    %r11,%rdi
    456e:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    4572:	48 01 f7             	add    %rsi,%rdi
    4575:	41 83 e3 01          	and    $0x1,%r11d
    4579:	0f 84 d9 fe ff ff    	je     4458 <sendm.part.0+0x148>
          them->messages[them->messages_count++] = data->message; 
    457f:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    4586:	48 89 04 fa          	mov    %rax,(%rdx,%rdi,8)
        for (; them->messages_count < min;) {
    458a:	e9 c9 fe ff ff       	jmp    4458 <sendm.part.0+0x148>
    458f:	90                   	nop
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    4590:	83 b9 00 01 00 00 01 	cmpl   $0x1,0x100(%rcx)
    4597:	0f 85 14 ff ff ff    	jne    44b1 <sendm.part.0+0x1a1>
          them->available_sending = 0;
    459d:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
          them->available_receiving = 1;
    45a7:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
          them->finished_reading = 0;
    45b1:	c7 81 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rcx)
    45bb:	e9 f1 fe ff ff       	jmp    44b1 <sendm.part.0+0x1a1>
          them->messages[them->messages_count++] = data->message; 
    45c0:	48 89 f7             	mov    %rsi,%rdi
    45c3:	4c 8d 14 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r10
    45cb:	e9 70 fe ff ff       	jmp    4440 <sendm.part.0+0x130>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    45d0:	48 89 d1             	mov    %rdx,%rcx
        for (; them->messages_count < min;) {
    45d3:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    45da:	48 63 a9 88 00 00 00 	movslq 0x88(%rcx),%rbp
    45e1:	48 39 f5             	cmp    %rsi,%rbp
    45e4:	0f 8f d7 fd ff ff    	jg     43c1 <sendm.part.0+0xb1>
    45ea:	eb b1                	jmp    459d <sendm.part.0+0x28d>
    45ec:	48 89 d1             	mov    %rdx,%rcx
    45ef:	e9 b6 fd ff ff       	jmp    43aa <sendm.part.0+0x9a>
    45f4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    45ff:	90                   	nop

0000000000004600 <strtolower>:
void strtolower(char *str) {
    4600:	f3 0f 1e fa          	endbr64
    4604:	55                   	push   %rbp
    4605:	53                   	push   %rbx
    4606:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    460a:	48 0f be 1f          	movsbq (%rdi),%rbx
    460e:	84 db                	test   %bl,%bl
    4610:	74 24                	je     4636 <strtolower+0x36>
    4612:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4615:	e8 56 df ff ff       	call   2570 <__ctype_tolower_loc@plt>
    461a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4620:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4623:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4627:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    462a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    462d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4632:	84 db                	test   %bl,%bl
    4634:	75 ea                	jne    4620 <strtolower+0x20>
}
    4636:	48 83 c4 08          	add    $0x8,%rsp
    463a:	5b                   	pop    %rbx
    463b:	5d                   	pop    %rbp
    463c:	c3                   	ret
    463d:	0f 1f 00             	nopl   (%rax)

0000000000004640 <zh_malloc>:
void *zh_malloc(size_t size) {
    4640:	f3 0f 1e fa          	endbr64
    4644:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4648:	e8 13 de ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    464d:	48 85 c0             	test   %rax,%rax
    4650:	74 05                	je     4657 <zh_malloc+0x17>
}
    4652:	48 83 c4 08          	add    $0x8,%rsp
    4656:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4657:	48 8b 0d c2 59 00 00 	mov    0x59c2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    465e:	ba 28 00 00 00       	mov    $0x28,%edx
    4663:	be 01 00 00 00       	mov    $0x1,%esi
    4668:	48 8d 3d 31 2f 00 00 	lea    0x2f31(%rip),%rdi        # 75a0 <_IO_stdin_used+0x5a0>
    466f:	e8 ac de ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4674:	bf 01 00 00 00       	mov    $0x1,%edi
    4679:	e8 82 de ff ff       	call   2500 <exit@plt>
    467e:	66 90                	xchg   %ax,%ax

0000000000004680 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4680:	f3 0f 1e fa          	endbr64
    4684:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4685:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    468a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    468d:	e8 0e dd ff ff       	call   23a0 <strrchr@plt>
    if (!dot || dot == filename)
    4692:	48 85 c0             	test   %rax,%rax
    4695:	74 11                	je     46a8 <get_filename_ext+0x28>
    4697:	48 39 c3             	cmp    %rax,%rbx
    469a:	74 0c                	je     46a8 <get_filename_ext+0x28>
    return dot + 1;
    469c:	48 83 c0 01          	add    $0x1,%rax
}
    46a0:	5b                   	pop    %rbx
    46a1:	c3                   	ret
    46a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    46a8:	48 8d 05 47 2a 00 00 	lea    0x2a47(%rip),%rax        # 70f6 <_IO_stdin_used+0xf6>
}
    46af:	5b                   	pop    %rbx
    46b0:	c3                   	ret
    46b1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    46bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000046c0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    46c0:	f3 0f 1e fa          	endbr64
    46c4:	41 55                	push   %r13
    46c6:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    46c9:	48 89 fe             	mov    %rdi,%rsi
    46cc:	41 54                	push   %r12
    46ce:	55                   	push   %rbp
    46cf:	48 89 d5             	mov    %rdx,%rbp
    46d2:	ba 00 04 00 00       	mov    $0x400,%edx
    46d7:	53                   	push   %rbx
    46d8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    46df:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    46e8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    46f0:	31 c0                	xor    %eax,%eax
    46f2:	49 89 e4             	mov    %rsp,%r12
    46f5:	4c 89 e7             	mov    %r12,%rdi
    46f8:	e8 83 dd ff ff       	call   2480 <__strcpy_chk@plt>
    for (; *str; ++str)
    46fd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4702:	84 db                	test   %bl,%bl
    4704:	74 24                	je     472a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4706:	e8 65 de ff ff       	call   2570 <__ctype_tolower_loc@plt>
    470b:	48 8b 08             	mov    (%rax),%rcx
    470e:	4c 89 e0             	mov    %r12,%rax
    4711:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4718:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    471b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    471f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4722:	48 0f be 18          	movsbq (%rax),%rbx
    4726:	84 db                	test   %bl,%bl
    4728:	75 ee                	jne    4718 <send_headers+0x58>
    void *buf = malloc(size);
    472a:	bf 11 00 00 00       	mov    $0x11,%edi
    472f:	e8 2c dd ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4734:	48 85 c0             	test   %rax,%rax
    4737:	0f 84 7e 04 00 00    	je     4bbb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    473d:	66 0f 6f 05 5b 34 00 00 	movdqa 0x345b(%rip),%xmm0        # 7ba0 <_IO_stdin_used+0xba0>
    iov[0].iov_base = zh_malloc(slen);
    4745:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4749:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    474e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4756:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    475a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    475d:	e8 fe dc ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4762:	48 85 c0             	test   %rax,%rax
    4765:	0f 84 50 04 00 00    	je     4bbb <send_headers+0x4fb>
    476b:	66 0f 6f 05 3d 34 00 00 	movdqa 0x343d(%rip),%xmm0        # 7bb0 <_IO_stdin_used+0xbb0>
    iov[1].iov_base = zh_malloc(slen);
    4773:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4777:	4c 89 e7             	mov    %r12,%rdi
    477a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4784:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    478c:	0f 11 00             	movups %xmm0,(%rax)
    478f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4793:	be 2e 00 00 00       	mov    $0x2e,%esi
    4798:	e8 03 dc ff ff       	call   23a0 <strrchr@plt>
    if (!dot || dot == filename)
    479d:	48 85 c0             	test   %rax,%rax
    47a0:	0f 84 ea 02 00 00    	je     4a90 <send_headers+0x3d0>
    47a6:	4c 39 e0             	cmp    %r12,%rax
    47a9:	0f 84 e1 02 00 00    	je     4a90 <send_headers+0x3d0>
    return dot + 1;
    47af:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    47b3:	48 8d 3d 0a 29 00 00 	lea    0x290a(%rip),%rdi        # 70c4 <_IO_stdin_used+0xc4>
    47ba:	48 89 de             	mov    %rbx,%rsi
    47bd:	e8 3e dc ff ff       	call   2400 <strcmp@plt>
    47c2:	85 c0                	test   %eax,%eax
    47c4:	75 20                	jne    47e6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    47c6:	66 0f 6f 05 f2 33 00 00 	movdqa 0x33f2(%rip),%xmm0        # 7bc0 <_IO_stdin_used+0xbc0>
    47ce:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    47d6:	66 0f 6f 05 f2 33 00 00 	movdqa 0x33f2(%rip),%xmm0        # 7bd0 <_IO_stdin_used+0xbd0>
    47de:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    47e6:	48 89 de             	mov    %rbx,%rsi
    47e9:	48 8d 3d d8 28 00 00 	lea    0x28d8(%rip),%rdi        # 70c8 <_IO_stdin_used+0xc8>
    47f0:	e8 0b dc ff ff       	call   2400 <strcmp@plt>
    47f5:	85 c0                	test   %eax,%eax
    47f7:	75 20                	jne    4819 <send_headers+0x159>
    47f9:	66 0f 6f 05 bf 33 00 00 	movdqa 0x33bf(%rip),%xmm0        # 7bc0 <_IO_stdin_used+0xbc0>
    4801:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4809:	66 0f 6f 05 bf 33 00 00 	movdqa 0x33bf(%rip),%xmm0        # 7bd0 <_IO_stdin_used+0xbd0>
    4811:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4819:	48 89 de             	mov    %rbx,%rsi
    481c:	48 8d 3d aa 28 00 00 	lea    0x28aa(%rip),%rdi        # 70cd <_IO_stdin_used+0xcd>
    4823:	e8 d8 db ff ff       	call   2400 <strcmp@plt>
    4828:	85 c0                	test   %eax,%eax
    482a:	0f 84 10 02 00 00    	je     4a40 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4830:	48 89 de             	mov    %rbx,%rsi
    4833:	48 8d 3d 97 28 00 00 	lea    0x2897(%rip),%rdi        # 70d1 <_IO_stdin_used+0xd1>
    483a:	e8 c1 db ff ff       	call   2400 <strcmp@plt>
    483f:	85 c0                	test   %eax,%eax
    4841:	0f 84 a9 02 00 00    	je     4af0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4847:	48 89 de             	mov    %rbx,%rsi
    484a:	48 8d 3d 84 28 00 00 	lea    0x2884(%rip),%rdi        # 70d5 <_IO_stdin_used+0xd5>
    4851:	e8 aa db ff ff       	call   2400 <strcmp@plt>
    4856:	85 c0                	test   %eax,%eax
    4858:	0f 84 6a 02 00 00    	je     4ac8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    485e:	48 89 de             	mov    %rbx,%rsi
    4861:	48 8d 3d b0 28 00 00 	lea    0x28b0(%rip),%rdi        # 7118 <_IO_stdin_used+0x118>
    4868:	e8 93 db ff ff       	call   2400 <strcmp@plt>
    486d:	85 c0                	test   %eax,%eax
    486f:	0f 84 2b 02 00 00    	je     4aa0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4875:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4878:	0f 84 52 01 00 00    	je     49d0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    487e:	48 89 de             	mov    %rbx,%rsi
    4881:	48 8d 3d 51 28 00 00 	lea    0x2851(%rip),%rdi        # 70d9 <_IO_stdin_used+0xd9>
    4888:	e8 73 db ff ff       	call   2400 <strcmp@plt>
    488d:	85 c0                	test   %eax,%eax
    488f:	0f 84 ab 02 00 00    	je     4b40 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4895:	48 89 de             	mov    %rbx,%rsi
    4898:	48 8d 3d 3e 28 00 00 	lea    0x283e(%rip),%rdi        # 70dd <_IO_stdin_used+0xdd>
    489f:	e8 5c db ff ff       	call   2400 <strcmp@plt>
    48a4:	85 c0                	test   %eax,%eax
    48a6:	0f 84 6c 02 00 00    	je     4b18 <send_headers+0x458>
    slen = strlen(send_buffer);
    48ac:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    48b4:	4c 89 e7             	mov    %r12,%rdi
    48b7:	e8 a4 da ff ff       	call   2360 <strlen@plt>
    void *buf = malloc(size);
    48bc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    48bf:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    48c2:	e8 99 db ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    48c7:	48 85 c0             	test   %rax,%rax
    48ca:	0f 84 eb 02 00 00    	je     4bbb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    48d0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    48d4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    48d8:	83 fb 08             	cmp    $0x8,%ebx
    48db:	0f 83 3f 01 00 00    	jae    4a20 <send_headers+0x360>
    48e1:	f6 c3 04             	test   $0x4,%bl
    48e4:	0f 85 7b 02 00 00    	jne    4b65 <send_headers+0x4a5>
    48ea:	85 db                	test   %ebx,%ebx
    48ec:	74 13                	je     4901 <send_headers+0x241>
    48ee:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    48f6:	88 10                	mov    %dl,(%rax)
    48f8:	f6 c3 02             	test   $0x2,%bl
    48fb:	0f 85 96 02 00 00    	jne    4b97 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4901:	4d 89 e8             	mov    %r13,%r8
    4904:	48 8d 0d d6 27 00 00 	lea    0x27d6(%rip),%rcx        # 70e1 <_IO_stdin_used+0xe1>
    490b:	4c 89 e7             	mov    %r12,%rdi
    490e:	31 c0                	xor    %eax,%eax
    4910:	ba 00 04 00 00       	mov    $0x400,%edx
    4915:	be 01 00 00 00       	mov    $0x1,%esi
    491a:	e8 61 dc ff ff       	call   2580 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    491f:	4c 89 e7             	mov    %r12,%rdi
    4922:	e8 39 da ff ff       	call   2360 <strlen@plt>
    void *buf = malloc(size);
    4927:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    492a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    492d:	e8 2e db ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4932:	48 85 c0             	test   %rax,%rax
    4935:	0f 84 80 02 00 00    	je     4bbb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    493b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    493f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4943:	83 fb 08             	cmp    $0x8,%ebx
    4946:	0f 83 1c 01 00 00    	jae    4a68 <send_headers+0x3a8>
    494c:	f6 c3 04             	test   $0x4,%bl
    494f:	0f 85 29 02 00 00    	jne    4b7e <send_headers+0x4be>
    4955:	85 db                	test   %ebx,%ebx
    4957:	74 13                	je     496c <send_headers+0x2ac>
    4959:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4961:	88 10                	mov    %dl,(%rax)
    4963:	f6 c3 02             	test   $0x2,%bl
    4966:	0f 85 3d 02 00 00    	jne    4ba9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    496c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4971:	bf 02 00 00 00       	mov    $0x2,%edi
    4976:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    497e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4986:	e8 d5 da ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    498b:	48 85 c0             	test   %rax,%rax
    498e:	0f 84 27 02 00 00    	je     4bbb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4994:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    499c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    49a0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    49a8:	66 89 10             	mov    %dx,(%rax)
}
    49ab:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    49b3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    49bc:	0f 85 20 02 00 00    	jne    4be2 <send_headers+0x522>
    49c2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    49c9:	5b                   	pop    %rbx
    49ca:	5d                   	pop    %rbp
    49cb:	41 5c                	pop    %r12
    49cd:	41 5d                	pop    %r13
    49cf:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    49d0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    49d4:	0f 85 a4 fe ff ff    	jne    487e <send_headers+0x1be>
    49da:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    49de:	0f 85 9a fe ff ff    	jne    487e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    49e4:	66 0f 6f 05 34 32 00 00 	movdqa 0x3234(%rip),%xmm0        # 7c20 <_IO_stdin_used+0xc20>
    49ec:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    49f6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    49fe:	66 0f 6f 05 2a 32 00 00 	movdqa 0x322a(%rip),%xmm0        # 7c30 <_IO_stdin_used+0xc30>
    4a06:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4a0e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4a16:	e9 63 fe ff ff       	jmp    487e <send_headers+0x1be>
    4a1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4a20:	89 da                	mov    %ebx,%edx
    4a22:	48 89 c7             	mov    %rax,%rdi
    4a25:	4c 89 e6             	mov    %r12,%rsi
    4a28:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4a2d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4a32:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4a35:	c1 e9 03             	shr    $0x3,%ecx
    4a38:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4a3b:	e9 c1 fe ff ff       	jmp    4901 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a40:	66 0f 6f 05 78 31 00 00 	movdqa 0x3178(%rip),%xmm0        # 7bc0 <_IO_stdin_used+0xbc0>
    4a48:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a50:	66 0f 6f 05 88 31 00 00 	movdqa 0x3188(%rip),%xmm0        # 7be0 <_IO_stdin_used+0xbe0>
    4a58:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a60:	e9 cb fd ff ff       	jmp    4830 <send_headers+0x170>
    4a65:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4a68:	89 da                	mov    %ebx,%edx
    4a6a:	48 89 c7             	mov    %rax,%rdi
    4a6d:	4c 89 e6             	mov    %r12,%rsi
    4a70:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4a75:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4a7a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4a7d:	c1 e9 03             	shr    $0x3,%ecx
    4a80:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4a83:	e9 e4 fe ff ff       	jmp    496c <send_headers+0x2ac>
    4a88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4a90:	48 8d 1d 5f 26 00 00 	lea    0x265f(%rip),%rbx        # 70f6 <_IO_stdin_used+0xf6>
    4a97:	e9 94 fd ff ff       	jmp    4830 <send_headers+0x170>
    4a9c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4aa0:	66 0f 6f 05 58 31 00 00 	movdqa 0x3158(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    4aa8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ab0:	66 0f 6f 05 58 31 00 00 	movdqa 0x3158(%rip),%xmm0        # 7c10 <_IO_stdin_used+0xc10>
    4ab8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4ac0:	e9 b0 fd ff ff       	jmp    4875 <send_headers+0x1b5>
    4ac5:	0f 1f 00             	nopl   (%rax)
    4ac8:	66 0f 6f 05 30 31 00 00 	movdqa 0x3130(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    4ad0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ad8:	66 0f 6f 05 30 31 00 00 	movdqa 0x3130(%rip),%xmm0        # 7c10 <_IO_stdin_used+0xc10>
    4ae0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4ae8:	e9 71 fd ff ff       	jmp    485e <send_headers+0x19e>
    4aed:	0f 1f 00             	nopl   (%rax)
    4af0:	66 0f 6f 05 c8 30 00 00 	movdqa 0x30c8(%rip),%xmm0        # 7bc0 <_IO_stdin_used+0xbc0>
    4af8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b00:	66 0f 6f 05 e8 30 00 00 	movdqa 0x30e8(%rip),%xmm0        # 7bf0 <_IO_stdin_used+0xbf0>
    4b08:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4b10:	e9 32 fd ff ff       	jmp    4847 <send_headers+0x187>
    4b15:	0f 1f 00             	nopl   (%rax)
    4b18:	66 0f 6f 05 e0 30 00 00 	movdqa 0x30e0(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    4b20:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b28:	66 0f 6f 05 20 31 00 00 	movdqa 0x3120(%rip),%xmm0        # 7c50 <_IO_stdin_used+0xc50>
    4b30:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4b38:	e9 6f fd ff ff       	jmp    48ac <send_headers+0x1ec>
    4b3d:	0f 1f 00             	nopl   (%rax)
    4b40:	66 0f 6f 05 b8 30 00 00 	movdqa 0x30b8(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    4b48:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b50:	66 0f 6f 05 e8 30 00 00 	movdqa 0x30e8(%rip),%xmm0        # 7c40 <_IO_stdin_used+0xc40>
    4b58:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4b60:	e9 30 fd ff ff       	jmp    4895 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4b65:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4b6c:	89 db                	mov    %ebx,%ebx
    4b6e:	89 10                	mov    %edx,(%rax)
    4b70:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4b75:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4b79:	e9 83 fd ff ff       	jmp    4901 <send_headers+0x241>
    4b7e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4b85:	89 db                	mov    %ebx,%ebx
    4b87:	89 10                	mov    %edx,(%rax)
    4b89:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4b8e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4b92:	e9 d5 fd ff ff       	jmp    496c <send_headers+0x2ac>
    4b97:	89 db                	mov    %ebx,%ebx
    4b99:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4b9f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4ba4:	e9 58 fd ff ff       	jmp    4901 <send_headers+0x241>
    4ba9:	89 db                	mov    %ebx,%ebx
    4bab:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4bb1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4bb6:	e9 b1 fd ff ff       	jmp    496c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4bbb:	48 8b 0d 5e 54 00 00 	mov    0x545e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4bc2:	ba 28 00 00 00       	mov    $0x28,%edx
    4bc7:	be 01 00 00 00       	mov    $0x1,%esi
    4bcc:	48 8d 3d cd 29 00 00 	lea    0x29cd(%rip),%rdi        # 75a0 <_IO_stdin_used+0x5a0>
    4bd3:	e8 48 d9 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4bd8:	bf 01 00 00 00       	mov    $0x1,%edi
    4bdd:	e8 1e d9 ff ff       	call   2500 <exit@plt>
}
    4be2:	e8 89 d7 ff ff       	call   2370 <__stack_chk_fail@plt>
    4be7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004bf0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4bf0:	f3 0f 1e fa          	endbr64
    4bf4:	41 55                	push   %r13
    4bf6:	49 89 d5             	mov    %rdx,%r13
    4bf9:	41 54                	push   %r12
    4bfb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    4bfe:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4c01:	55                   	push   %rbp
    4c02:	53                   	push   %rbx
    4c03:	48 89 f3             	mov    %rsi,%rbx
    4c06:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4c0a:	e8 51 d8 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4c0f:	48 85 c0             	test   %rax,%rax
    4c12:	74 6b                	je     4c7f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4c14:	4c 89 e7             	mov    %r12,%rdi
    4c17:	48 89 c5             	mov    %rax,%rbp
    4c1a:	31 f6                	xor    %esi,%esi
    4c1c:	31 c0                	xor    %eax,%eax
    4c1e:	e8 ad d8 ff ff       	call   24d0 <open@plt>
    4c23:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4c26:	85 c0                	test   %eax,%eax
    4c28:	0f 88 88 d9 ff ff    	js     25b6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4c2e:	48 89 da             	mov    %rbx,%rdx
    4c31:	48 89 ee             	mov    %rbp,%rsi
    4c34:	89 c7                	mov    %eax,%edi
    4c36:	e8 a5 d7 ff ff       	call   23e0 <read@plt>
    if (ret < file_size) {
    4c3b:	48 98                	cltq
    4c3d:	48 39 d8             	cmp    %rbx,%rax
    4c40:	7c 1e                	jl     4c60 <copy_file_contents+0x70>
    close(fd);
    4c42:	44 89 e7             	mov    %r12d,%edi
    4c45:	e8 76 d7 ff ff       	call   23c0 <close@plt>
    iov->iov_base = buf;
    4c4a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    4c4e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4c52:	48 83 c4 08          	add    $0x8,%rsp
    4c56:	5b                   	pop    %rbx
    4c57:	5d                   	pop    %rbp
    4c58:	41 5c                	pop    %r12
    4c5a:	41 5d                	pop    %r13
    4c5c:	c3                   	ret
    4c5d:	0f 1f 00             	nopl   (%rax)
    4c60:	48 8b 0d b9 53 00 00 	mov    0x53b9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c67:	ba 1a 00 00 00       	mov    $0x1a,%edx
    4c6c:	be 01 00 00 00       	mov    $0x1,%esi
    4c71:	48 8d 3d 7f 24 00 00 	lea    0x247f(%rip),%rdi        # 70f7 <_IO_stdin_used+0xf7>
    4c78:	e8 a3 d8 ff ff       	call   2520 <fwrite@plt>
    4c7d:	eb c3                	jmp    4c42 <copy_file_contents+0x52>
    4c7f:	48 8b 0d 9a 53 00 00 	mov    0x539a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c86:	ba 28 00 00 00       	mov    $0x28,%edx
    4c8b:	be 01 00 00 00       	mov    $0x1,%esi
    4c90:	48 8d 3d 09 29 00 00 	lea    0x2909(%rip),%rdi        # 75a0 <_IO_stdin_used+0x5a0>
    4c97:	e8 84 d8 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4c9c:	bf 01 00 00 00       	mov    $0x1,%edi
    4ca1:	e8 5a d8 ff ff       	call   2500 <exit@plt>
    4ca6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004cb0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4cb0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4cb4:	8b 46 44             	mov    0x44(%rsi),%eax
    4cb7:	48 89 fa             	mov    %rdi,%rdx
    4cba:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    4cbd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4cc3:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4cc6:	48 8b 07             	mov    (%rdi),%rax
    4cc9:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4ccc:	f6 c1 02             	test   $0x2,%cl
    4ccf:	74 00                	je     4cd1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4cd1:	89 f0                	mov    %esi,%eax
    4cd3:	44 29 c0             	sub    %r8d,%eax
    4cd6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4cd9:	0f 82 e3 d8 ff ff    	jb     25c2 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4cdf:	c1 e9 0a             	shr    $0xa,%ecx
    4ce2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ce6:	8b 47 44             	mov    0x44(%rdi),%eax
    4ce9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4cec:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4cef:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4cf2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4cf5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4cf9:	d3 e0                	shl    %cl,%eax
    4cfb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    4cfe:	48 c1 e0 06          	shl    $0x6,%rax
    4d02:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4d06:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    4d0c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4d0f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4d13:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4d19:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4d21:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4d25:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4d28:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4d2f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4d37:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    4d3b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    4d3f:	e8 3c d6 ff ff       	call   2380 <io_uring_submit@plt>
}
    4d44:	31 c0                	xor    %eax,%eax
    4d46:	48 83 c4 08          	add    $0x8,%rsp
    4d4a:	c3                   	ret
    4d4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004d50 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4d50:	f3 0f 1e fa          	endbr64
    4d54:	41 55                	push   %r13
    4d56:	41 89 fd             	mov    %edi,%r13d
    4d59:	41 54                	push   %r12
    4d5b:	55                   	push   %rbp
    4d5c:	53                   	push   %rbx
    4d5d:	48 89 f3             	mov    %rsi,%rbx
    4d60:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4d64:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4d67:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    4d6d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4d70:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4d73:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4d75:	f6 c1 02             	test   $0x2,%cl
    4d78:	74 00                	je     4d7a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    4d7a:	89 c2                	mov    %eax,%edx
    4d7c:	29 f2                	sub    %esi,%edx
    4d7e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4d81:	0f 82 4b d8 ff ff    	jb     25d2 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d87:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    4d8a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    4d8d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4d90:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4d95:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d98:	23 6b 58             	and    0x58(%rbx),%ebp
    4d9b:	d3 e5                	shl    %cl,%ebp
    4d9d:	48 c1 e5 06          	shl    $0x6,%rbp
    4da1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4da5:	e8 b6 d6 ff ff       	call   2460 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    4daa:	be 01 00 00 00       	mov    $0x1,%esi
    4daf:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4db4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4db7:	e8 34 d6 ff ff       	call   23f0 <calloc@plt>
    req->client_socket = client_socket;
    4dbc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4dc1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4dc5:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4dc8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4dcd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4dd2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    4ddb:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4de3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4de7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    4deb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4df2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4dfa:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    4dfe:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4e06:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    4e0e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4e12:	e8 69 d5 ff ff       	call   2380 <io_uring_submit@plt>
}
    4e17:	48 83 c4 08          	add    $0x8,%rsp
    4e1b:	31 c0                	xor    %eax,%eax
    4e1d:	5b                   	pop    %rbx
    4e1e:	5d                   	pop    %rbp
    4e1f:	41 5c                	pop    %r12
    4e21:	41 5d                	pop    %r13
    4e23:	c3                   	ret
    4e24:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4e2f:	90                   	nop

0000000000004e30 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4e30:	f3 0f 1e fa          	endbr64
    4e34:	41 56                	push   %r14
    4e36:	41 89 f6             	mov    %esi,%r14d
    4e39:	41 55                	push   %r13
    4e3b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    4e3e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4e43:	41 54                	push   %r12
    4e45:	55                   	push   %rbp
    4e46:	48 89 d5             	mov    %rdx,%rbp
    4e49:	53                   	push   %rbx
    void *buf = malloc(size);
    4e4a:	e8 11 d6 ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    4e4f:	48 85 c0             	test   %rax,%rax
    4e52:	0f 84 dd 00 00 00    	je     4f35 <_send_static_string_content+0x105>
    4e58:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    4e5b:	4c 89 ef             	mov    %r13,%rdi
    4e5e:	e8 fd d4 ff ff       	call   2360 <strlen@plt>
    req->iovec_count = 1;
    4e63:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    4e6a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    4e6e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4e71:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4e74:	e8 e7 d5 ff ff       	call   2460 <malloc@plt>
    4e79:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    4e7c:	48 85 c0             	test   %rax,%rax
    4e7f:	0f 84 b0 00 00 00    	je     4f35 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4e85:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4e89:	4c 89 e2             	mov    %r12,%rdx
    4e8c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    4e8f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4e93:	e8 98 d5 ff ff       	call   2430 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4e98:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e9b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4ea1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4ea4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4ea8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4eaa:	f6 c1 02             	test   $0x2,%cl
    4ead:	0f 85 7d 00 00 00    	jne    4f30 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4eb3:	89 d0                	mov    %edx,%eax
    4eb5:	29 f0                	sub    %esi,%eax
    4eb7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    4eba:	0f 82 1c d7 ff ff    	jb     25dc <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4ec0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ec3:	8b 45 44             	mov    0x44(%rbp),%eax
    4ec6:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4ec9:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    4ecc:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4ecf:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4ed2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4ed8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4edc:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4ede:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4ee1:	48 89 ef             	mov    %rbp,%rdi
    4ee4:	48 c1 e0 06          	shl    $0x6,%rax
    4ee8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    4eec:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4eef:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4ef3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4ef9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4f01:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4f05:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4f08:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4f0f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4f17:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    4f1b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    4f1f:	5b                   	pop    %rbx
    4f20:	5d                   	pop    %rbp
    4f21:	41 5c                	pop    %r12
    4f23:	41 5d                	pop    %r13
    4f25:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4f27:	e9 54 d4 ff ff       	jmp    2380 <io_uring_submit@plt>
    4f2c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4f30:	e9 7e ff ff ff       	jmp    4eb3 <_send_static_string_content+0x83>
    4f35:	48 8b 0d e4 50 00 00 	mov    0x50e4(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4f3c:	ba 28 00 00 00       	mov    $0x28,%edx
    4f41:	be 01 00 00 00       	mov    $0x1,%esi
    4f46:	48 8d 3d 53 26 00 00 	lea    0x2653(%rip),%rdi        # 75a0 <_IO_stdin_used+0x5a0>
    4f4d:	e8 ce d5 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4f52:	bf 01 00 00 00       	mov    $0x1,%edi
    4f57:	e8 a4 d5 ff ff       	call   2500 <exit@plt>
    4f5c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004f60 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4f60:	f3 0f 1e fa          	endbr64
    4f64:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4f67:	89 fe                	mov    %edi,%esi
    4f69:	48 8b 3d a8 50 00 00 	mov    0x50a8(%rip),%rdi        # a018 <unimplemented_content>
    4f70:	e9 bb fe ff ff       	jmp    4e30 <_send_static_string_content>
    4f75:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004f80 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4f80:	f3 0f 1e fa          	endbr64
    4f84:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4f87:	89 fe                	mov    %edi,%esi
    4f89:	48 8b 3d 80 50 00 00 	mov    0x5080(%rip),%rdi        # a010 <http_404_content>
    4f90:	e9 9b fe ff ff       	jmp    4e30 <_send_static_string_content>
    4f95:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004fa0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4fa0:	f3 0f 1e fa          	endbr64
    4fa4:	41 56                	push   %r14
    4fa6:	41 55                	push   %r13
    4fa8:	49 89 d5             	mov    %rdx,%r13
    4fab:	41 54                	push   %r12
    4fad:	41 89 f4             	mov    %esi,%r12d
    4fb0:	55                   	push   %rbp
    4fb1:	48 89 fd             	mov    %rdi,%rbp
    4fb4:	53                   	push   %rbx
    4fb5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    4fbc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4fc5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    4fcd:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    4fcf:	e8 8c d3 ff ff       	call   2360 <strlen@plt>
    4fd4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4fd9:	48 89 c3             	mov    %rax,%rbx
    4fdc:	0f 84 b6 00 00 00    	je     5098 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4fe2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4fe7:	48 89 ee             	mov    %rbp,%rsi
    4fea:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4fee:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4ff3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4ffb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5003:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    500e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5016:	e8 f5 d3 ff ff       	call   2410 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    501b:	48 89 e6             	mov    %rsp,%rsi
    501e:	4c 89 f7             	mov    %r14,%rdi
    5021:	e8 fa d3 ff ff       	call   2420 <stat@plt>
    5026:	83 f8 ff             	cmp    $0xffffffff,%eax
    5029:	0f 84 d3 00 00 00    	je     5102 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    502f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5033:	25 00 f0 00 00       	and    $0xf000,%eax
    5038:	3d 00 80 00 00       	cmp    $0x8000,%eax
    503d:	0f 84 f5 00 00 00    	je     5138 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    5043:	48 8b 3d c6 4f 00 00 	mov    0x4fc6(%rip),%rdi        # a010 <http_404_content>
    504a:	4c 89 ea             	mov    %r13,%rdx
    504d:	44 89 e6             	mov    %r12d,%esi
    5050:	e8 db fd ff ff       	call   4e30 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5055:	4c 89 f2             	mov    %r14,%rdx
    5058:	bf 01 00 00 00       	mov    $0x1,%edi
    505d:	31 c0                	xor    %eax,%eax
    505f:	48 8d 35 e1 20 00 00 	lea    0x20e1(%rip),%rsi        # 7147 <_IO_stdin_used+0x147>
    5066:	e8 35 d4 ff ff       	call   24a0 <__printf_chk@plt>
}
    506b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5073:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    507c:	0f 85 20 01 00 00    	jne    51a2 <handle_get_method+0x202>
    5082:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5089:	5b                   	pop    %rbx
    508a:	5d                   	pop    %rbp
    508b:	41 5c                	pop    %r12
    508d:	41 5d                	pop    %r13
    508f:	41 5e                	pop    %r14
    5091:	c3                   	ret
    5092:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5098:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    509d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    50a5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    50aa:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    50ad:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    50b5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    50b8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    50c0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    50cb:	e8 40 d3 ff ff       	call   2410 <__memcpy_chk@plt>
    50d0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    50d5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    50da:	48 8d 35 31 20 00 00 	lea    0x2031(%rip),%rsi        # 7112 <_IO_stdin_used+0x112>
    50e1:	48 29 d9             	sub    %rbx,%rcx
    50e4:	ba 0b 00 00 00       	mov    $0xb,%edx
    50e9:	e8 22 d3 ff ff       	call   2410 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    50ee:	48 89 e6             	mov    %rsp,%rsi
    50f1:	4c 89 f7             	mov    %r14,%rdi
    50f4:	e8 27 d3 ff ff       	call   2420 <stat@plt>
    50f9:	83 f8 ff             	cmp    $0xffffffff,%eax
    50fc:	0f 85 2d ff ff ff    	jne    502f <handle_get_method+0x8f>
    5102:	4c 89 f2             	mov    %r14,%rdx
    5105:	48 89 e9             	mov    %rbp,%rcx
    5108:	48 8d 35 0e 20 00 00 	lea    0x200e(%rip),%rsi        # 711d <_IO_stdin_used+0x11d>
    510f:	31 c0                	xor    %eax,%eax
    5111:	bf 01 00 00 00       	mov    $0x1,%edi
    5116:	e8 85 d3 ff ff       	call   24a0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    511b:	48 8b 3d ee 4e 00 00 	mov    0x4eee(%rip),%rdi        # a010 <http_404_content>
    5122:	4c 89 ea             	mov    %r13,%rdx
    5125:	44 89 e6             	mov    %r12d,%esi
    5128:	e8 03 fd ff ff       	call   4e30 <_send_static_string_content>
}
    512d:	e9 39 ff ff ff       	jmp    506b <handle_get_method+0xcb>
    5132:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5138:	bf 70 00 00 00       	mov    $0x70,%edi
    513d:	e8 1e d3 ff ff       	call   2460 <malloc@plt>
    5142:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5145:	48 85 c0             	test   %rax,%rax
    5148:	74 5d                	je     51a7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    514a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    514e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5153:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5157:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    515a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    5161:	e8 5a f5 ff ff       	call   46c0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5166:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    516b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    516f:	4c 89 f7             	mov    %r14,%rdi
    5172:	e8 79 fa ff ff       	call   4bf0 <copy_file_contents>
    5177:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    517c:	4c 89 f2             	mov    %r14,%rdx
    517f:	31 c0                	xor    %eax,%eax
    5181:	48 8d 35 ad 1f 00 00 	lea    0x1fad(%rip),%rsi        # 7135 <_IO_stdin_used+0x135>
    5188:	bf 01 00 00 00       	mov    $0x1,%edi
    518d:	e8 0e d3 ff ff       	call   24a0 <__printf_chk@plt>
            add_write_request(req, ring);
    5192:	4c 89 ee             	mov    %r13,%rsi
    5195:	48 89 df             	mov    %rbx,%rdi
    5198:	e8 13 fb ff ff       	call   4cb0 <add_write_request>
    519d:	e9 c9 fe ff ff       	jmp    506b <handle_get_method+0xcb>
}
    51a2:	e8 c9 d1 ff ff       	call   2370 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    51a7:	48 8b 0d 72 4e 00 00 	mov    0x4e72(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    51ae:	ba 28 00 00 00       	mov    $0x28,%edx
    51b3:	be 01 00 00 00       	mov    $0x1,%esi
    51b8:	48 8d 3d e1 23 00 00 	lea    0x23e1(%rip),%rdi        # 75a0 <_IO_stdin_used+0x5a0>
    51bf:	e8 5c d3 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    51c4:	bf 01 00 00 00       	mov    $0x1,%edi
    51c9:	e8 32 d3 ff ff       	call   2500 <exit@plt>
    51ce:	66 90                	xchg   %ax,%ax

00000000000051d0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    51d0:	f3 0f 1e fa          	endbr64
    51d4:	41 57                	push   %r15
    51d6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    51d8:	4c 8d 35 cd 1e 00 00 	lea    0x1ecd(%rip),%r14        # 70ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    51df:	41 55                	push   %r13
    51e1:	49 89 d5             	mov    %rdx,%r13
    51e4:	41 54                	push   %r12
    51e6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    51e9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    51ec:	55                   	push   %rbp
    51ed:	53                   	push   %rbx
    51ee:	48 83 ec 18          	sub    $0x18,%rsp
    51f2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    51fb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5200:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5202:	49 89 e7             	mov    %rsp,%r15
    5205:	4c 89 fa             	mov    %r15,%rdx
    5208:	e8 c3 d1 ff ff       	call   23d0 <strtok_r@plt>
    for (; *str; ++str)
    520d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    5211:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    5214:	84 db                	test   %bl,%bl
    5216:	74 1d                	je     5235 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    5218:	e8 53 d3 ff ff       	call   2570 <__ctype_tolower_loc@plt>
    521d:	48 89 ea             	mov    %rbp,%rdx
    5220:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    5223:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    5227:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    522a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    522d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5231:	84 db                	test   %bl,%bl
    5233:	75 eb                	jne    5220 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    5235:	4c 89 fa             	mov    %r15,%rdx
    5238:	4c 89 f6             	mov    %r14,%rsi
    523b:	31 ff                	xor    %edi,%edi
    523d:	e8 8e d1 ff ff       	call   23d0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5242:	48 8d 35 11 1f 00 00 	lea    0x1f11(%rip),%rsi        # 715a <_IO_stdin_used+0x15a>
    5249:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    524c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    524f:	e8 ac d1 ff ff       	call   2400 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    5254:	4c 89 ea             	mov    %r13,%rdx
    5257:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    525a:	85 c0                	test   %eax,%eax
    525c:	75 2a                	jne    5288 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    525e:	48 89 df             	mov    %rbx,%rdi
    5261:	e8 3a fd ff ff       	call   4fa0 <handle_get_method>
}
    5266:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    526b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5274:	75 20                	jne    5296 <handle_http_method+0xc6>
    5276:	48 83 c4 18          	add    $0x18,%rsp
    527a:	5b                   	pop    %rbx
    527b:	5d                   	pop    %rbp
    527c:	41 5c                	pop    %r12
    527e:	41 5d                	pop    %r13
    5280:	41 5e                	pop    %r14
    5282:	41 5f                	pop    %r15
    5284:	c3                   	ret
    5285:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5288:	48 8b 3d 89 4d 00 00 	mov    0x4d89(%rip),%rdi        # a018 <unimplemented_content>
    528f:	e8 9c fb ff ff       	call   4e30 <_send_static_string_content>
}
    5294:	eb d0                	jmp    5266 <handle_http_method+0x96>
    5296:	e8 d5 d0 ff ff       	call   2370 <__stack_chk_fail@plt>
    529b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000052a0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    52a0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    52a4:	85 d2                	test   %edx,%edx
    52a6:	7e 38                	jle    52e0 <get_line+0x40>
    52a8:	48 63 d2             	movslq %edx,%rdx
    52ab:	48 83 c7 01          	add    $0x1,%rdi
    52af:	48 01 f2             	add    %rsi,%rdx
    52b2:	eb 11                	jmp    52c5 <get_line+0x25>
    52b4:	0f 1f 40 00          	nopl   0x0(%rax)
    52b8:	48 83 c6 01          	add    $0x1,%rsi
    52bc:	48 83 c7 01          	add    $0x1,%rdi
    52c0:	48 39 d6             	cmp    %rdx,%rsi
    52c3:	74 1b                	je     52e0 <get_line+0x40>
        dest[i] = src[i];
    52c5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    52c9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    52cb:	3c 0d                	cmp    $0xd,%al
    52cd:	75 e9                	jne    52b8 <get_line+0x18>
    52cf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    52d2:	75 e4                	jne    52b8 <get_line+0x18>
            dest[i] = '\0';
    52d4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    52d7:	31 c0                	xor    %eax,%eax
    52d9:	c3                   	ret
    52da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    52e0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    52e5:	c3                   	ret
    52e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000052f0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    52f0:	f3 0f 1e fa          	endbr64
    52f4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    52fb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    52ff:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5308:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5310:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5312:	49 89 e2             	mov    %rsp,%r10
    5315:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    531d:	4c 89 d0             	mov    %r10,%rax
    5320:	eb 13                	jmp    5335 <handle_client_request+0x45>
    5322:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5328:	48 83 c0 01          	add    $0x1,%rax
    532c:	48 83 c1 01          	add    $0x1,%rcx
    5330:	4c 39 c8             	cmp    %r9,%rax
    5333:	74 4b                	je     5380 <handle_client_request+0x90>
        dest[i] = src[i];
    5335:	44 0f b6 01          	movzbl (%rcx),%r8d
    5339:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    533c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5340:	75 e6                	jne    5328 <handle_client_request+0x38>
    5342:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5346:	75 e0                	jne    5328 <handle_client_request+0x38>
            dest[i] = '\0';
    5348:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    534b:	8b 47 08             	mov    0x8(%rdi),%eax
    534e:	48 89 f2             	mov    %rsi,%rdx
    5351:	4c 89 d7             	mov    %r10,%rdi
    5354:	89 c6                	mov    %eax,%esi
    5356:	e8 75 fe ff ff       	call   51d0 <handle_http_method>
}
    535b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5363:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    536c:	75 39                	jne    53a7 <handle_client_request+0xb7>
    536e:	31 c0                	xor    %eax,%eax
    5370:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5377:	c3                   	ret
    5378:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5380:	48 8b 0d 99 4c 00 00 	mov    0x4c99(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5387:	ba 12 00 00 00       	mov    $0x12,%edx
    538c:	be 01 00 00 00       	mov    $0x1,%esi
    5391:	48 8d 3d c6 1d 00 00 	lea    0x1dc6(%rip),%rdi        # 715e <_IO_stdin_used+0x15e>
    5398:	e8 83 d1 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    539d:	bf 01 00 00 00       	mov    $0x1,%edi
    53a2:	e8 59 d1 ff ff       	call   2500 <exit@plt>
}
    53a7:	e8 c4 cf ff ff       	call   2370 <__stack_chk_fail@plt>
    53ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000053b0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    53b0:	f3 0f 1e fa          	endbr64
    53b4:	55                   	push   %rbp
    53b5:	53                   	push   %rbx
    53b6:	48 89 cb             	mov    %rcx,%rbx
    53b9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    53bd:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    53c0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    53c3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    53c9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    53cc:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    53cf:	f6 c1 02             	test   $0x2,%cl
    53d2:	74 00                	je     53d4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    53d4:	41 89 c0             	mov    %eax,%r8d
    53d7:	45 29 c8             	sub    %r9d,%r8d
    53da:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    53de:	0f 82 08 d2 ff ff    	jb     25ec <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    53e4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53e7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    53ea:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    53ed:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    53f0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    53f3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53f7:	d3 e5                	shl    %cl,%ebp
    53f9:	48 c1 e5 06          	shl    $0x6,%rbp
    53fd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5401:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5404:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5409:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5410:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5414:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5418:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    5420:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    5428:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    542c:	e8 2f d0 ff ff       	call   2460 <malloc@plt>
  io_uring_submit(ring);
    5431:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5434:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    543a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    543e:	48 83 c4 08          	add    $0x8,%rsp
    5442:	5b                   	pop    %rbx
    5443:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5444:	e9 37 cf ff ff       	jmp    2380 <io_uring_submit@plt>
    5449:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005450 <io_thread>:
void* io_thread(void *arg) {
    5450:	f3 0f 1e fa          	endbr64
    5454:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5456:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5458:	41 56                	push   %r14
    545a:	41 55                	push   %r13
    545c:	41 54                	push   %r12
    545e:	55                   	push   %rbp
    545f:	48 89 fd             	mov    %rdi,%rbp
    5462:	53                   	push   %rbx
    5463:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    546a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5473:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    547b:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    547f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5484:	bf 00 01 00 00       	mov    $0x100,%edi
    5489:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    548c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5490:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5495:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    549a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    549f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    54a4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    54ac:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    54b1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    54b9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    54be:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    54c6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    54cb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    54d3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    54d8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    54e0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    54e5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    54ed:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    54f5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    54fd:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5505:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    550d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5515:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    551d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5525:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    552d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5535:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    553d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5544:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    554c:	e8 ef ce ff ff       	call   2440 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5551:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5555:	31 f6                	xor    %esi,%esi
    5557:	e8 e4 cf ff ff       	call   2540 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    555c:	31 d2                	xor    %edx,%edx
    555e:	be 01 00 00 00       	mov    $0x1,%esi
    5563:	bf 02 00 00 00       	mov    $0x2,%edi
    5568:	e8 23 d0 ff ff       	call   2590 <socket@plt>
  if (sock == -1)
    556d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5570:	0f 84 b8 d0 ff ff    	je     262e <io_thread.cold+0x38>
  if (setsockopt(sock,
    5576:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    557b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5581:	89 c7                	mov    %eax,%edi
    5583:	41 89 c4             	mov    %eax,%r12d
    5586:	ba 02 00 00 00       	mov    $0x2,%edx
    558b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5590:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5598:	e8 93 cd ff ff       	call   2330 <setsockopt@plt>
    559d:	85 c0                	test   %eax,%eax
    559f:	0f 88 5d d0 ff ff    	js     2602 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    55a5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    55aa:	ba 10 00 00 00       	mov    $0x10,%edx
    55af:	44 89 e7             	mov    %r12d,%edi
    55b2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    55bb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    55c3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    55cb:	e8 e0 ce ff ff       	call   24b0 <bind@plt>
    55d0:	85 c0                	test   %eax,%eax
    55d2:	0f 88 62 d0 ff ff    	js     263a <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    55d8:	be 0a 00 00 00       	mov    $0xa,%esi
    55dd:	44 89 e7             	mov    %r12d,%edi
    55e0:	e8 8b ce ff ff       	call   2470 <listen@plt>
    55e5:	85 c0                	test   %eax,%eax
    55e7:	0f 88 21 d0 ff ff    	js     260e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    55ed:	ba db 18 00 00       	mov    $0x18db,%edx
    55f2:	48 8d 35 aa 1b 00 00 	lea    0x1baa(%rip),%rsi        # 71a3 <_IO_stdin_used+0x1a3>
    55f9:	bf 01 00 00 00       	mov    $0x1,%edi
    55fe:	31 c0                	xor    %eax,%eax
    5600:	e8 9b ce ff ff       	call   24a0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5605:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    560a:	48 89 d9             	mov    %rbx,%rcx
    560d:	44 89 e7             	mov    %r12d,%edi
    5610:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5615:	48 89 c6             	mov    %rax,%rsi
    5618:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    561d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5622:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    562a:	e8 81 fd ff ff       	call   53b0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    562f:	bf 01 00 00 00       	mov    $0x1,%edi
    5634:	be 10 00 00 00       	mov    $0x10,%esi
    5639:	e8 b2 cd ff ff       	call   23f0 <calloc@plt>
    void *buf = malloc(size);
    563e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5643:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5646:	e8 15 ce ff ff       	call   2460 <malloc@plt>
    if (!buf) {
    564b:	48 85 c0             	test   %rax,%rax
    564e:	0f 84 ae 04 00 00    	je     5b02 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5654:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5658:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    565f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5666:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    566e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5671:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5676:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5678:	f6 c1 02             	test   $0x2,%cl
    567b:	0f 85 0f 04 00 00    	jne    5a90 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5681:	89 d0                	mov    %edx,%eax
    5683:	29 f0                	sub    %esi,%eax
    5685:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    568c:	0f 82 92 cf ff ff    	jb     2624 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5692:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5695:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5699:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    569d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    56a0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    56a7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    56aa:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    56b1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    56b8:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    56ba:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    56bd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    56c2:	48 c1 e0 06          	shl    $0x6,%rax
    56c6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    56ce:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    56d4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    56d7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    56df:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    56e3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    56eb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    56f3:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    56f7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    56fb:	e8 80 cc ff ff       	call   2380 <io_uring_submit@plt>
  while (data->running == 1) {
    5700:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5704:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5709:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5711:	0f 85 d7 01 00 00    	jne    58ee <io_thread+0x49e>
    5717:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    571c:	4d 89 ce             	mov    %r9,%r14
    571f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5724:	0f 1f 40 00          	nopl   0x0(%rax)
    5728:	48 8d 3d 8a 1a 00 00 	lea    0x1a8a(%rip),%rdi        # 71b9 <_IO_stdin_used+0x1b9>
    572f:	e8 ec cb ff ff       	call   2320 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5734:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    573b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5742:	c1 e9 0b             	shr    $0xb,%ecx
    5745:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5748:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5750:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5752:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    575a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    575c:	39 d0                	cmp    %edx,%eax
    575e:	74 36                	je     5796 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5760:	89 f8                	mov    %edi,%eax
    5762:	21 d0                	and    %edx,%eax
    5764:	d3 e0                	shl    %cl,%eax
    5766:	48 c1 e0 04          	shl    $0x4,%rax
    576a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5772:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    577a:	0f 85 a8 01 00 00    	jne    5928 <io_thread+0x4d8>
    5780:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5784:	0f 85 0e 03 00 00    	jne    5a98 <io_thread+0x648>
			if (cqe->res < 0)
    578a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    578d:	83 c2 01             	add    $0x1,%edx
    5790:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5792:	85 c0                	test   %eax,%eax
    5794:	79 b2                	jns    5748 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5796:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    579f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    57a0:	45 31 c0             	xor    %r8d,%r8d
    57a3:	31 d2                	xor    %edx,%edx
    57a5:	b9 01 00 00 00       	mov    $0x1,%ecx
    57aa:	4c 89 f6             	mov    %r14,%rsi
    57ad:	48 89 df             	mov    %rbx,%rdi
    57b0:	e8 db cc ff ff       	call   2490 <__io_uring_get_cqe@plt>
    57b5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    57b8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    57bd:	48 83 38 01          	cmpq   $0x1,(%rax)
    57c1:	0f 84 e1 02 00 00    	je     5aa8 <io_thread+0x658>
    57c7:	48 8d 3d 11 1a 00 00 	lea    0x1a11(%rip),%rdi        # 71df <_IO_stdin_used+0x1df>
    57ce:	e8 4d cb ff ff       	call   2320 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    57d3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    57d8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    57db:	45 85 ff             	test   %r15d,%r15d
    57de:	0f 88 12 ce ff ff    	js     25f6 <io_thread.cold>
      if (cqe->res < 0) {
    57e4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    57e7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    57eb:	85 c0                	test   %eax,%eax
    57ed:	0f 88 d5 02 00 00    	js     5ac8 <io_thread+0x678>
      switch (req->event_type) {
    57f3:	41 83 f8 01          	cmp    $0x1,%r8d
    57f7:	0f 84 7b 01 00 00    	je     5978 <io_thread+0x528>
    57fd:	41 83 f8 02          	cmp    $0x2,%r8d
    5801:	0f 84 a1 01 00 00    	je     59a8 <io_thread+0x558>
    5807:	45 85 c0             	test   %r8d,%r8d
    580a:	0f 85 50 01 00 00    	jne    5960 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5810:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5815:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    581a:	48 89 d9             	mov    %rbx,%rcx
    581d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5821:	e8 8a fb ff ff       	call   53b0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5826:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    582b:	48 89 de             	mov    %rbx,%rsi
    582e:	8b 78 08             	mov    0x8(%rax),%edi
    5831:	e8 1a f5 ff ff       	call   4d50 <add_read_request>
              free(req);
    5836:	4c 89 e7             	mov    %r12,%rdi
    5839:	e8 b2 ca ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    583e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5843:	48 85 c0             	test   %rax,%rax
    5846:	0f 85 14 01 00 00    	jne    5960 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    584c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5853:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    585a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    585d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5862:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5864:	f6 c1 02             	test   $0x2,%cl
    5867:	74 00                	je     5869 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5869:	89 d0                	mov    %edx,%eax
    586b:	29 f0                	sub    %esi,%eax
    586d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5874:	0f 82 a0 cd ff ff    	jb     261a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    587a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    587d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5882:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5886:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5889:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5890:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5893:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    589a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    58a1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    58a3:	8b 55 60             	mov    0x60(%rbp),%edx
    58a6:	48 c1 e0 06          	shl    $0x6,%rax
    58aa:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    58b2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    58b8:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    58bb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    58c3:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    58c7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    58cf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    58d7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    58db:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    58df:	e8 9c ca ff ff       	call   2380 <io_uring_submit@plt>
  while (data->running == 1) {
    58e4:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    58e8:	0f 84 3a fe ff ff    	je     5728 <io_thread+0x2d8>
    58ee:	48 8d 3d 23 19 00 00 	lea    0x1923(%rip),%rdi        # 7218 <_IO_stdin_used+0x218>
    58f5:	e8 26 ca ff ff       	call   2320 <puts@plt>
}
    58fa:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5902:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    590b:	0f 85 18 02 00 00    	jne    5b29 <io_thread+0x6d9>
    5911:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5918:	31 c0                	xor    %eax,%eax
    591a:	5b                   	pop    %rbx
    591b:	5d                   	pop    %rbp
    591c:	41 5c                	pop    %r12
    591e:	41 5d                	pop    %r13
    5920:	41 5e                	pop    %r14
    5922:	41 5f                	pop    %r15
    5924:	c3                   	ret
    5925:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5928:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    592d:	48 85 c0             	test   %rax,%rax
    5930:	0f 84 6a fe ff ff    	je     57a0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5936:	48 83 38 01          	cmpq   $0x1,(%rax)
    593a:	0f 84 68 01 00 00    	je     5aa8 <io_thread+0x658>
    5940:	48 8d 3d 98 18 00 00 	lea    0x1898(%rip),%rdi        # 71df <_IO_stdin_used+0x1df>
    5947:	e8 d4 c9 ff ff       	call   2320 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    594c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5951:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5954:	e9 8b fe ff ff       	jmp    57e4 <io_thread+0x394>
    5959:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5960:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5968:	8b 02                	mov    (%rdx),%eax
    596a:	83 c0 01             	add    $0x1,%eax
    596d:	89 02                	mov    %eax,(%rdx)
}
    596f:	e9 d8 fe ff ff       	jmp    584c <io_thread+0x3fc>
    5974:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5978:	85 c0                	test   %eax,%eax
    597a:	75 74                	jne    59f0 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    597c:	48 8b 0d 9d 46 00 00 	mov    0x469d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5983:	ba 0f 00 00 00       	mov    $0xf,%edx
    5988:	be 01 00 00 00       	mov    $0x1,%esi
    598d:	48 8d 3d 74 18 00 00 	lea    0x1874(%rip),%rdi        # 7208 <_IO_stdin_used+0x208>
    5994:	e8 87 cb ff ff       	call   2520 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5999:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    599e:	e9 a0 fe ff ff       	jmp    5843 <io_thread+0x3f3>
    59a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    59a8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    59ad:	45 31 ff             	xor    %r15d,%r15d
    59b0:	85 c0                	test   %eax,%eax
    59b2:	7e 20                	jle    59d4 <io_thread+0x584>
    59b4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    59b8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    59bb:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    59bf:	48 c1 e0 04          	shl    $0x4,%rax
    59c3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    59c8:	e8 23 c9 ff ff       	call   22f0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    59cd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    59d2:	7f e4                	jg     59b8 <io_thread+0x568>
              close(req->client_socket);
    59d4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    59d9:	e8 e2 c9 ff ff       	call   23c0 <close@plt>
              free(req);
    59de:	4c 89 e7             	mov    %r12,%rdi
    59e1:	e8 0a c9 ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    59e6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    59eb:	e9 53 fe ff ff       	jmp    5843 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    59f0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    59f5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    59fa:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5a02:	eb 11                	jmp    5a15 <io_thread+0x5c5>
    5a04:	0f 1f 40 00          	nopl   0x0(%rax)
    5a08:	48 83 c0 01          	add    $0x1,%rax
    5a0c:	48 83 c2 01          	add    $0x1,%rdx
    5a10:	48 39 c6             	cmp    %rax,%rsi
    5a13:	74 4b                	je     5a60 <io_thread+0x610>
        dest[i] = src[i];
    5a15:	0f b6 0a             	movzbl (%rdx),%ecx
    5a18:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5a1a:	80 f9 0d             	cmp    $0xd,%cl
    5a1d:	75 e9                	jne    5a08 <io_thread+0x5b8>
    5a1f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5a23:	75 e3                	jne    5a08 <io_thread+0x5b8>
            dest[i] = '\0';
    5a25:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5a28:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    5a2d:	48 89 da             	mov    %rbx,%rdx
    5a30:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5a35:	e8 96 f7 ff ff       	call   51d0 <handle_http_method>
              free(req->iov[0].iov_base);
    5a3a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    5a3f:	e8 ac c8 ff ff       	call   22f0 <free@plt>
              free(req);
    5a44:	4c 89 e7             	mov    %r12,%rdi
    5a47:	e8 a4 c8 ff ff       	call   22f0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5a4c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5a51:	e9 ed fd ff ff       	jmp    5843 <io_thread+0x3f3>
    5a56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5a60:	48 8b 0d b9 45 00 00 	mov    0x45b9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5a67:	ba 12 00 00 00       	mov    $0x12,%edx
    5a6c:	be 01 00 00 00       	mov    $0x1,%esi
    5a71:	48 8d 3d e6 16 00 00 	lea    0x16e6(%rip),%rdi        # 715e <_IO_stdin_used+0x15e>
    5a78:	e8 a3 ca ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5a7d:	bf 01 00 00 00       	mov    $0x1,%edi
    5a82:	e8 79 ca ff ff       	call   2500 <exit@plt>
    5a87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5a90:	e9 ec fb ff ff       	jmp    5681 <io_thread+0x231>
    5a95:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5a98:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    5a9d:	e9 94 fe ff ff       	jmp    5936 <io_thread+0x4e6>
    5aa2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5aa8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5ab0:	48 8d 3d 14 17 00 00 	lea    0x1714(%rip),%rdi        # 71cb <_IO_stdin_used+0x1cb>
    5ab7:	8b 02                	mov    (%rdx),%eax
    5ab9:	83 c0 01             	add    $0x1,%eax
    5abc:	89 02                	mov    %eax,(%rdx)
    5abe:	e8 5d c8 ff ff       	call   2320 <puts@plt>
    5ac3:	e9 26 fe ff ff       	jmp    58ee <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5ac8:	f7 d8                	neg    %eax
    5aca:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5acf:	89 c7                	mov    %eax,%edi
    5ad1:	e8 8a ca ff ff       	call   2560 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5ad6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5adb:	be 01 00 00 00       	mov    $0x1,%esi
    5ae0:	48 8b 3d 39 45 00 00 	mov    0x4539(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5ae7:	48 89 c1             	mov    %rax,%rcx
    5aea:	48 8d 15 df 1a 00 00 	lea    0x1adf(%rip),%rdx        # 75d0 <_IO_stdin_used+0x5d0>
    5af1:	31 c0                	xor    %eax,%eax
    5af3:	e8 38 ca ff ff       	call   2530 <__fprintf_chk@plt>
          exit(1);
    5af8:	bf 01 00 00 00       	mov    $0x1,%edi
    5afd:	e8 fe c9 ff ff       	call   2500 <exit@plt>
    5b02:	48 8b 0d 17 45 00 00 	mov    0x4517(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5b09:	ba 28 00 00 00       	mov    $0x28,%edx
    5b0e:	be 01 00 00 00       	mov    $0x1,%esi
    5b13:	48 8d 3d 86 1a 00 00 	lea    0x1a86(%rip),%rdi        # 75a0 <_IO_stdin_used+0x5a0>
    5b1a:	e8 01 ca ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5b1f:	bf 01 00 00 00       	mov    $0x1,%edi
    5b24:	e8 d7 c9 ff ff       	call   2500 <exit@plt>
}
    5b29:	e8 42 c8 ff ff       	call   2370 <__stack_chk_fail@plt>
    5b2e:	66 90                	xchg   %ax,%ax

0000000000005b30 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5b30:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5b34:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5b3b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5b41:	85 c9                	test   %ecx,%ecx
    5b43:	0f 8e ea 00 00 00    	jle    5c33 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    5b49:	41 56                	push   %r14
    5b4b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5b4d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    5b50:	41 54                	push   %r12
    5b52:	49 89 fc             	mov    %rdi,%r12
    5b55:	55                   	push   %rbp
    5b56:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5b57:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5b5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5b60:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    5b64:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    5b6c:	31 db                	xor    %ebx,%ebx
    5b6e:	8b 10                	mov    (%rax),%edx
    5b70:	85 d2                	test   %edx,%edx
    5b72:	7e 26                	jle    5b9a <barriered_work_ingest+0x6a>
    5b74:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    5b78:	48 89 dd             	mov    %rbx,%rbp
    5b7b:	48 c1 e5 08          	shl    $0x8,%rbp
    5b7f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    5b83:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    5b8a:	74 24                	je     5bb0 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5b8c:	48 83 c3 01          	add    $0x1,%rbx
    5b90:	39 da                	cmp    %ebx,%edx
    5b92:	7f e4                	jg     5b78 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5b94:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5b9a:	49 83 c5 01          	add    $0x1,%r13
    5b9e:	44 39 e9             	cmp    %r13d,%ecx
    5ba1:	7f bd                	jg     5b60 <barriered_work_ingest+0x30>
}
    5ba3:	5b                   	pop    %rbx
    5ba4:	31 c0                	xor    %eax,%eax
    5ba6:	5d                   	pop    %rbp
    5ba7:	41 5c                	pop    %r12
    5ba9:	41 5d                	pop    %r13
    5bab:	41 5e                	pop    %r14
    5bad:	c3                   	ret
    5bae:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    5bb0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5bb9:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5bc0:	bf 04 00 00 00       	mov    $0x4,%edi
    5bc5:	48 c1 e6 05          	shl    $0x5,%rsi
    5bc9:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5bd0:	48 83 c6 10          	add    $0x10,%rsi
    5bd4:	e8 67 c7 ff ff       	call   2340 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5bd9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5be1:	48 8b 40 50          	mov    0x50(%rax),%rax
    5be5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5be9:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    5bed:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5bf7:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    5bfd:	83 c0 01             	add    $0x1,%eax
    5c00:	99                   	cltd
    5c01:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5c07:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    5c0d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5c10:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5c18:	48 83 c3 01          	add    $0x1,%rbx
    5c1c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5c20:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5c24:	8b 10                	mov    (%rax),%edx
    5c26:	39 da                	cmp    %ebx,%edx
    5c28:	0f 8f 46 ff ff ff    	jg     5b74 <barriered_work_ingest+0x44>
    5c2e:	e9 61 ff ff ff       	jmp    5b94 <barriered_work_ingest+0x64>
}
    5c33:	31 c0                	xor    %eax,%eax
    5c35:	c3                   	ret
    5c36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005c40 <barriered_thread>:
void* barriered_thread(void *arg) {
    5c40:	f3 0f 1e fa          	endbr64
    5c44:	41 56                	push   %r14
    5c46:	41 55                	push   %r13
    5c48:	41 54                	push   %r12
  int t = 0;
    5c4a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    5c4d:	55                   	push   %rbp
  int waiting = 0;
    5c4e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    5c50:	53                   	push   %rbx
    5c51:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    5c54:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5c58:	0f 85 74 02 00 00    	jne    5ed2 <barriered_thread+0x292>
    if (t >= data->task_count) {
    5c5e:	8b 43 40             	mov    0x40(%rbx),%eax
    5c61:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5c68:	41 39 c4             	cmp    %eax,%r12d
    5c6b:	0f 8d 6f 01 00 00    	jge    5de0 <barriered_thread+0x1a0>
    5c71:	49 63 fc             	movslq %r12d,%rdi
    5c74:	48 c1 e7 09          	shl    $0x9,%rdi
    5c78:	49 89 fd             	mov    %rdi,%r13
    5c7b:	eb 32                	jmp    5caf <barriered_thread+0x6f>
    5c7d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5c80:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5c84:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5c88:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5c8c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5c90:	4c 01 ef             	add    %r13,%rdi
    5c93:	e8 98 fe ff ff       	call   5b30 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    5c98:	8b 43 40             	mov    0x40(%rbx),%eax
    5c9b:	41 83 c4 01          	add    $0x1,%r12d
    5c9f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    5ca6:	44 39 e0             	cmp    %r12d,%eax
    5ca9:	0f 8e 19 02 00 00    	jle    5ec8 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    5caf:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5cb3:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    5cb7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    5cbe:	75 c0                	jne    5c80 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5cc0:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    5cc4:	83 e8 01             	sub    $0x1,%eax
    5cc7:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    5ccc:	45 85 e4             	test   %r12d,%r12d
    5ccf:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5cd2:	45 85 c0             	test   %r8d,%r8d
    5cd5:	0f 8e 2d 01 00 00    	jle    5e08 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5cdb:	48 63 c8             	movslq %eax,%rcx
    5cde:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5ce2:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5ce5:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5ceb:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    5cf2:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    5cf6:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    5cf9:	45 31 f6             	xor    %r14d,%r14d
    5cfc:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5d00:	48 8b 10             	mov    (%rax),%rdx
    5d03:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    5d07:	49 01 cb             	add    %rcx,%r11
    5d0a:	4c 89 da             	mov    %r11,%rdx
    5d0d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    5d14:	75 04                	jne    5d1a <barriered_thread+0xda>
            arrived++;
    5d16:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5d1a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    5d20:	75 04                	jne    5d26 <barriered_thread+0xe6>
            prearrive++;
    5d22:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5d26:	48 83 c0 08          	add    $0x8,%rax
    5d2a:	48 39 c6             	cmp    %rax,%rsi
    5d2d:	75 d1                	jne    5d00 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    5d2f:	45 85 d2             	test   %r10d,%r10d
    5d32:	0f 84 c0 00 00 00    	je     5df8 <barriered_thread+0x1b8>
    5d38:	45 39 d0             	cmp    %r10d,%r8d
    5d3b:	0f 84 b7 00 00 00    	je     5df8 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    5d41:	45 85 f6             	test   %r14d,%r14d
    5d44:	74 0a                	je     5d50 <barriered_thread+0x110>
    5d46:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    5d4a:	0f 85 ae 01 00 00    	jne    5efe <barriered_thread+0x2be>
    5d50:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    5d54:	4c 01 ea             	add    %r13,%rdx
    5d57:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    5d5e:	45 85 e4             	test   %r12d,%r12d
    5d61:	75 14                	jne    5d77 <barriered_thread+0x137>
    5d63:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5d6a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5d71:	0f 8c 69 01 00 00    	jl     5ee0 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5d77:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    5d7b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    5d7f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5d89:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    5d8d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5d91:	4c 01 ef             	add    %r13,%rdi
    5d94:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    5d9a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    5d9e:	4c 01 e8             	add    %r13,%rax
    5da1:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5da8:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    5dab:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5db0:	83 e8 01             	sub    $0x1,%eax
    5db3:	44 39 e0             	cmp    %r12d,%eax
    5db6:	0f 84 a4 00 00 00    	je     5e60 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    5dbc:	0f ae f8             	sfence
          if (waiting == 0) {
    5dbf:	85 ed                	test   %ebp,%ebp
    5dc1:	0f 84 d1 00 00 00    	je     5e98 <barriered_thread+0x258>
        int arrived = 0; 
    5dc7:	bd 01 00 00 00       	mov    $0x1,%ebp
    5dcc:	e9 c7 fe ff ff       	jmp    5c98 <barriered_thread+0x58>
  while (data->running == 1) {
    5dd1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5dd5:	0f 85 f7 00 00 00    	jne    5ed2 <barriered_thread+0x292>
    5ddb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    5de0:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    5de8:	85 c0                	test   %eax,%eax
    5dea:	7e e5                	jle    5dd1 <barriered_thread+0x191>
    5dec:	45 31 e4             	xor    %r12d,%r12d
    5def:	e9 7d fe ff ff       	jmp    5c71 <barriered_thread+0x31>
    5df4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5df8:	83 fd 01             	cmp    $0x1,%ebp
    5dfb:	74 1b                	je     5e18 <barriered_thread+0x1d8>
        int arrived = 0; 
    5dfd:	31 ed                	xor    %ebp,%ebp
    5dff:	e9 3d ff ff ff       	jmp    5d41 <barriered_thread+0x101>
    5e04:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5e08:	83 fd 01             	cmp    $0x1,%ebp
    5e0b:	0f 85 43 ff ff ff    	jne    5d54 <barriered_thread+0x114>
        int arrived = 0; 
    5e11:	45 31 f6             	xor    %r14d,%r14d
    5e14:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5e18:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5e1f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    5e24:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5e26:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5e2a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5e31:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    5e36:	e8 05 c5 ff ff       	call   2340 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    5e3b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5e42:	48 83 c0 01          	add    $0x1,%rax
    5e46:	48 99                	cqto
    5e48:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    5e4f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    5e56:	e9 e6 fe ff ff       	jmp    5d41 <barriered_thread+0x101>
    5e5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5e60:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5e67:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5e6e:	0f 8d 48 ff ff ff    	jge    5dbc <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    5e74:	48 c1 e6 04          	shl    $0x4,%rsi
    5e78:	bf 04 00 00 00       	mov    $0x4,%edi
    5e7d:	48 03 73 70          	add    0x70(%rbx),%rsi
    5e81:	e8 ba c4 ff ff       	call   2340 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    5e86:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    5e8e:	e9 29 ff ff ff       	jmp    5dbc <barriered_thread+0x17c>
    5e93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    5e98:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5e9f:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    5ea4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5ea8:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5eaf:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5eb3:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5eb7:	e8 84 c4 ff ff       	call   2340 <clock_gettime@plt>
            waiting = 1;
    5ebc:	e9 06 ff ff ff       	jmp    5dc7 <barriered_thread+0x187>
    5ec1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    5ec8:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5ecc:	0f 84 96 fd ff ff    	je     5c68 <barriered_thread+0x28>
}
    5ed2:	5b                   	pop    %rbx
    5ed3:	31 c0                	xor    %eax,%eax
    5ed5:	5d                   	pop    %rbp
    5ed6:	41 5c                	pop    %r12
    5ed8:	41 5d                	pop    %r13
    5eda:	41 5e                	pop    %r14
    5edc:	c3                   	ret
    5edd:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    5ee0:	48 c1 e6 04          	shl    $0x4,%rsi
    5ee4:	bf 04 00 00 00       	mov    $0x4,%edi
    5ee9:	48 03 73 68          	add    0x68(%rbx),%rsi
    5eed:	e8 4e c4 ff ff       	call   2340 <clock_gettime@plt>
          data->tasks[t].available = 0;
    5ef2:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5ef6:	4c 01 ea             	add    %r13,%rdx
    5ef9:	e9 79 fe ff ff       	jmp    5d77 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5efe:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5f02:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5f06:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5f0a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5f0e:	4c 01 ef             	add    %r13,%rdi
    5f11:	e8 1a fc ff ff       	call   5b30 <barriered_work_ingest>
          break;
    5f16:	e9 39 fd ff ff       	jmp    5c54 <barriered_thread+0x14>
    5f1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005f20 <receive>:
int receive(struct BarrierTask *data) {
    5f20:	f3 0f 1e fa          	endbr64
    5f24:	41 57                	push   %r15
    5f26:	41 56                	push   %r14
    5f28:	41 55                	push   %r13
    5f2a:	41 54                	push   %r12
    5f2c:	55                   	push   %rbp
    5f2d:	53                   	push   %rbx
    5f2e:	48 83 ec 18          	sub    $0x18,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5f32:	44 8b b7 40 01 00 00 	mov    0x140(%rdi),%r14d
    5f39:	45 85 f6             	test   %r14d,%r14d
    5f3c:	0f 8e 17 01 00 00    	jle    6059 <receive+0x139>
    if (n == data->thread->real_thread_index) { continue; }
    5f42:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5f49:	48 89 f9             	mov    %rdi,%rcx
    5f4c:	45 31 e4             	xor    %r12d,%r12d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5f4f:	31 db                	xor    %ebx,%ebx
    if (n == data->thread->real_thread_index) { continue; }
    5f51:	48 63 68 08          	movslq 0x8(%rax),%rbp
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5f55:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    if (n == data->thread->real_thread_index) { continue; }
    5f5a:	49 89 ef             	mov    %rbp,%r15
    5f5d:	0f 1f 00             	nopl   (%rax)
    5f60:	41 39 df             	cmp    %ebx,%r15d
    5f63:	0f 84 e0 00 00 00    	je     6049 <receive+0x129>
    struct Data *me = data->mailboxes[n].lower;
    5f69:	48 8b 81 70 01 00 00 	mov    0x170(%rcx),%rax
    5f70:	4c 01 e0             	add    %r12,%rax
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    5f73:	44 8b 68 30          	mov    0x30(%rax),%r13d
    struct Data *me = data->mailboxes[n].lower;
    5f77:	48 8b 10             	mov    (%rax),%rdx
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    5f7a:	41 83 fd 02          	cmp    $0x2,%r13d
    5f7e:	0f 84 24 01 00 00    	je     60a8 <receive+0x188>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5f84:	48 83 ba 80 00 00 00 00 	cmpq   $0x0,0x80(%rdx)
    5f8c:	0f 8e 3b 01 00 00    	jle    60cd <receive+0x1ad>
      data->sends++;
    5f92:	4c 8b 81 78 01 00 00 	mov    0x178(%rcx),%r8
      data->n++;
    5f99:	48 8b b9 08 01 00 00 	mov    0x108(%rcx),%rdi
      me->received++;
    5fa0:	31 c0                	xor    %eax,%eax
    5fa2:	48 8b b2 10 03 00 00 	mov    0x310(%rdx),%rsi
      if (me->messages[x]->group == data->group) {
    5fa9:	4c 8b 1a             	mov    (%rdx),%r11
    5fac:	4d 8d 48 01          	lea    0x1(%r8),%r9
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5fb0:	4c 63 51 04          	movslq 0x4(%rcx),%r10
    5fb4:	4c 8d 47 01          	lea    0x1(%rdi),%r8
    5fb8:	48 8d 7e 01          	lea    0x1(%rsi),%rdi
    5fbc:	eb 0f                	jmp    5fcd <receive+0xad>
    5fbe:	66 90                	xchg   %ax,%ax
    for (int x = 0 ; x < me->messages_count ; x++) {
    5fc0:	48 83 c0 01          	add    $0x1,%rax
    5fc4:	48 39 82 80 00 00 00 	cmp    %rax,0x80(%rdx)
    5fcb:	7e 6b                	jle    6038 <receive+0x118>
      data->sends++;
    5fcd:	49 8d 34 01          	lea    (%r9,%rax,1),%rsi
    5fd1:	48 89 b1 78 01 00 00 	mov    %rsi,0x178(%rcx)
      data->n++;
    5fd8:	49 8d 34 00          	lea    (%r8,%rax,1),%rsi
    5fdc:	48 89 b1 08 01 00 00 	mov    %rsi,0x108(%rcx)
      me->received++;
    5fe3:	48 8d 34 07          	lea    (%rdi,%rax,1),%rsi
    5fe7:	48 89 b2 10 03 00 00 	mov    %rsi,0x310(%rdx)
      if (me->messages[x]->group == data->group) {
    5fee:	49 8b 34 c3          	mov    (%r11,%rax,8),%rsi
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5ff2:	4c 39 56 10          	cmp    %r10,0x10(%rsi)
    5ff6:	75 c8                	jne    5fc0 <receive+0xa0>
    5ff8:	48 39 6e 08          	cmp    %rbp,0x8(%rsi)
    5ffc:	75 c2                	jne    5fc0 <receive+0xa0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    5ffe:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6003:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6005:	bf 01 00 00 00       	mov    $0x1,%edi
    600a:	ba 01 00 00 00       	mov    $0x1,%edx
    600f:	48 8d 35 e2 15 00 00 	lea    0x15e2(%rip),%rsi        # 75f8 <_IO_stdin_used+0x5f8>
    6016:	48 63 40 04          	movslq 0x4(%rax),%rax
    601a:	48 39 e8             	cmp    %rbp,%rax
    601d:	0f 94 c1             	sete   %cl
    6020:	31 c0                	xor    %eax,%eax
    6022:	e8 79 c4 ff ff       	call   24a0 <__printf_chk@plt>
        exit(1);
    6027:	bf 01 00 00 00       	mov    $0x1,%edi
    602c:	e8 cf c4 ff ff       	call   2500 <exit@plt>
    6031:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    me->messages_count = 0;
    6038:	48 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rdx)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    6043:	41 83 fd 02          	cmp    $0x2,%r13d
    6047:	74 27                	je     6070 <receive+0x150>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6049:	83 c3 01             	add    $0x1,%ebx
    604c:	49 83 c4 38          	add    $0x38,%r12
    6050:	44 39 f3             	cmp    %r14d,%ebx
    6053:	0f 85 07 ff ff ff    	jne    5f60 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    6059:	0f ae f8             	sfence
}
    605c:	48 83 c4 18          	add    $0x18,%rsp
    6060:	31 c0                	xor    %eax,%eax
    6062:	5b                   	pop    %rbx
    6063:	5d                   	pop    %rbp
    6064:	41 5c                	pop    %r12
    6066:	41 5d                	pop    %r13
    6068:	41 5e                	pop    %r14
    606a:	41 5f                	pop    %r15
    606c:	c3                   	ret
    606d:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    6070:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    6076:	83 f8 01             	cmp    $0x1,%eax
    6079:	75 ce                	jne    6049 <receive+0x129>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    607b:	83 c3 01             	add    $0x1,%ebx
    607e:	49 83 c4 38          	add    $0x38,%r12
      me->available_reading = 0;
    6082:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    608c:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6096:	44 39 f3             	cmp    %r14d,%ebx
    6099:	0f 85 c1 fe ff ff    	jne    5f60 <receive+0x40>
    609f:	eb b8                	jmp    6059 <receive+0x139>
    60a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    60a8:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    60ae:	85 c0                	test   %eax,%eax
    60b0:	74 97                	je     6049 <receive+0x129>
    for (int x = 0 ; x < me->messages_count ; x++) {
    60b2:	48 83 ba 80 00 00 00 00 	cmpq   $0x0,0x80(%rdx)
    60ba:	0f 8f d2 fe ff ff    	jg     5f92 <receive+0x72>
    me->messages_count = 0;
    60c0:	48 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rdx)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    60cb:	eb a9                	jmp    6076 <receive+0x156>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    60cd:	83 c3 01             	add    $0x1,%ebx
    60d0:	49 83 c4 38          	add    $0x38,%r12
    me->messages_count = 0;
    60d4:	48 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    60df:	44 39 f3             	cmp    %r14d,%ebx
    60e2:	0f 85 78 fe ff ff    	jne    5f60 <receive+0x40>
    60e8:	e9 6c ff ff ff       	jmp    6059 <receive+0x139>
    60ed:	0f 1f 00             	nopl   (%rax)

00000000000060f0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    60f0:	f3 0f 1e fa          	endbr64
    60f4:	41 57                	push   %r15
    60f6:	41 56                	push   %r14
    60f8:	41 55                	push   %r13
    60fa:	41 54                	push   %r12
    60fc:	55                   	push   %rbp
    60fd:	53                   	push   %rbx
      receive(data);
    60fe:	48 89 fb             	mov    %rdi,%rbx
int barriered_work(struct BarrierTask *data) {
    6101:	48 83 ec 48          	sub    $0x48,%rsp
  if (data->thread_index == data->task_index) {
    6105:	8b 57 04             	mov    0x4(%rdi),%edx
int barriered_work(struct BarrierTask *data) {
    6108:	48 89 7c 24 10       	mov    %rdi,0x10(%rsp)
  if (data->thread_index == data->task_index) {
    610d:	39 97 30 01 00 00    	cmp    %edx,0x130(%rdi)
    6113:	0f 84 6a 04 00 00    	je     6583 <barriered_work+0x493>
    receive(data);
    6119:	e8 02 fe ff ff       	call   5f20 <receive>
    while (data->scheduled == 1) {
    611e:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6125:	75 19                	jne    6140 <barriered_work+0x50>
    6127:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
      data->n++;
    612c:	48 83 80 08 01 00 00 01 	addq   $0x1,0x108(%rax)
      asm volatile ("sfence" ::: "memory");
    6134:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6137:	83 b8 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rax)
    613e:	74 ec                	je     612c <barriered_work+0x3c>
  if (data->sending == 1) {
    6140:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6145:	83 b8 80 01 00 00 01 	cmpl   $0x1,0x180(%rax)
    614c:	0f 84 22 04 00 00    	je     6574 <barriered_work+0x484>
  asm volatile ("sfence" ::: "memory");
    6152:	0f ae f8             	sfence
}
    6155:	48 83 c4 48          	add    $0x48,%rsp
    6159:	31 c0                	xor    %eax,%eax
    615b:	5b                   	pop    %rbx
    615c:	5d                   	pop    %rbp
    615d:	41 5c                	pop    %r12
    615f:	41 5d                	pop    %r13
    6161:	41 5e                	pop    %r14
    6163:	41 5f                	pop    %r15
    6165:	c3                   	ret
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6166:	49 63 93 c4 00 00 00 	movslq 0xc4(%r11),%rdx
          int k = data->group;
    616d:	41 8b 85 94 01 00 00 	mov    0x194(%r13),%eax
    6174:	4c 89 ce             	mov    %r9,%rsi
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6177:	85 d2                	test   %edx,%edx
    6179:	0f 8e b1 00 00 00    	jle    6230 <barriered_work+0x140>
            int y = (k * data->thread->threads_per_group) + d;
    617f:	0f af c2             	imul   %edx,%eax
    6182:	48 98                	cltq
    6184:	48 8d 0c 80          	lea    (%rax,%rax,4),%rcx
    6188:	48 8d 1c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbx
    6190:	48 8d 3c 89          	lea    (%rcx,%rcx,4),%rdi
    6194:	48 29 c3             	sub    %rax,%rbx
    6197:	49 8b 4b 20          	mov    0x20(%r11),%rcx
    619b:	48 01 d0             	add    %rdx,%rax
    619e:	4c 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%r10
    61a6:	48 c1 e3 03          	shl    $0x3,%rbx
    61aa:	48 8d 2c f9          	lea    (%rcx,%rdi,8),%rbp
    61ae:	49 29 c2             	sub    %rax,%r10
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    61b1:	49 89 d8             	mov    %rbx,%r8
    61b4:	49 c1 e2 03          	shl    $0x3,%r10
    61b8:	49 89 e9             	mov    %rbp,%r9
    61bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    61c0:	49 8b 41 38          	mov    0x38(%r9),%rax
    61c4:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    61c9:	48 89 ea             	mov    %rbp,%rdx
    61cc:	48 8b 8c 30 70 01 00 00 	mov    0x170(%rax,%rsi,1),%rcx
    61d4:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    61d8:	4c 01 d1             	add    %r10,%rcx
    61db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              if (kind == MAILBOX_FRIEND) {
    61e0:	83 78 30 01          	cmpl   $0x1,0x30(%rax)
    61e4:	75 25                	jne    620b <barriered_work+0x11b>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    61e6:	48 8b 7a 38          	mov    0x38(%rdx),%rdi
    return mailbox->higher;
    61ea:	f3 0f 6f 00          	movdqu (%rax),%xmm0
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    61ee:	4c 8b 8c 37 70 01 00 00 	mov    0x170(%rdi,%rsi,1),%r9
    return mailbox->lower;
    61f6:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    61fb:	4d 01 c1             	add    %r8,%r9
    61fe:	4c 89 cf             	mov    %r9,%rdi
    mailbox->lower = data;
    6201:	4d 8b 49 08          	mov    0x8(%r9),%r9
    6205:	4c 89 08             	mov    %r9,(%rax)
    6208:	0f 11 07             	movups %xmm0,(%rdi)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    620b:	48 83 c0 38          	add    $0x38,%rax
    620f:	48 81 c2 c8 00 00 00 	add    $0xc8,%rdx
    6216:	48 39 c1             	cmp    %rax,%rcx
    6219:	75 c5                	jne    61e0 <barriered_work+0xf0>
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    621b:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    6220:	49 83 c0 38          	add    $0x38,%r8
    6224:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
    622b:	4d 39 c2             	cmp    %r8,%r10
    622e:	75 90                	jne    61c0 <barriered_work+0xd0>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6230:	41 83 c4 01          	add    $0x1,%r12d
    6234:	49 83 c6 38          	add    $0x38,%r14
    6238:	48 81 44 24 18 c8 00 00 00 	addq   $0xc8,0x18(%rsp)
    6241:	45 39 fc             	cmp    %r15d,%r12d
    6244:	0f 85 72 03 00 00    	jne    65bc <barriered_work+0x4cc>
      struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    624a:	be 08 00 00 00       	mov    $0x8,%esi
    624f:	bf 00 04 00 00       	mov    $0x400,%edi
    6254:	e8 97 c1 ff ff       	call   23f0 <calloc@plt>
    6259:	48 89 c5             	mov    %rax,%rbp
      for (int k = 0 ; k < data->thread->group_count ; k++) {
    625c:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6261:	48 8b 90 28 01 00 00 	mov    0x128(%rax),%rdx
    6268:	8b 82 c0 00 00 00    	mov    0xc0(%rdx),%eax
    626e:	89 44 24 18          	mov    %eax,0x18(%rsp)
    6272:	85 c0                	test   %eax,%eax
    6274:	0f 8e 0e 06 00 00    	jle    6888 <barriered_work+0x798>
        for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    627a:	8b 82 c4 00 00 00    	mov    0xc4(%rdx),%eax
    6280:	45 8d 5f fe          	lea    -0x2(%r15),%r11d
      for (int k = 0 ; k < data->thread->group_count ; k++) {
    6284:	31 f6                	xor    %esi,%esi
    6286:	45 8d 67 ff          	lea    -0x1(%r15),%r12d
    628a:	49 83 c3 01          	add    $0x1,%r11
    628e:	47 8d 04 24          	lea    (%r12,%r12,1),%r8d
        for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6292:	31 c9                	xor    %ecx,%ecx
      int datas2_size = 0; 
    6294:	31 db                	xor    %ebx,%ebx
    6296:	89 c7                	mov    %eax,%edi
    6298:	49 c1 e3 04          	shl    $0x4,%r11
    629c:	89 f0                	mov    %esi,%eax
    629e:	48 89 d6             	mov    %rdx,%rsi
    62a1:	89 fa                	mov    %edi,%edx
        for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    62a3:	85 d2                	test   %edx,%edx
    62a5:	0f 8e f8 00 00 00    	jle    63a3 <barriered_work+0x2b3>
    62ab:	4c 63 c9             	movslq %ecx,%r9
          for (int n = 0 ; n < data->thread->all_threads[x].task_count ; n++) {
    62ae:	4c 8b 56 20          	mov    0x20(%rsi),%r10
    62b2:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    62b7:	4b 8d 3c 89          	lea    (%r9,%r9,4),%rdi
    62bb:	89 4c 24 28          	mov    %ecx,0x28(%rsp)
    62bf:	48 8d 3c bf          	lea    (%rdi,%rdi,4),%rdi
    62c3:	89 44 24 30          	mov    %eax,0x30(%rsp)
    62c7:	4d 8d 2c fa          	lea    (%r10,%rdi,8),%r13
    62cb:	48 63 fa             	movslq %edx,%rdi
    62ce:	4c 01 cf             	add    %r9,%rdi
    62d1:	48 8d 3c bf          	lea    (%rdi,%rdi,4),%rdi
    62d5:	48 8d 3c bf          	lea    (%rdi,%rdi,4),%rdi
    62d9:	4d 8d 34 fa          	lea    (%r10,%rdi,8),%r14
    62dd:	0f 1f 00             	nopl   (%rax)
    62e0:	41 8b 4d 40          	mov    0x40(%r13),%ecx
    62e4:	85 c9                	test   %ecx,%ecx
    62e6:	0f 8e 9a 00 00 00    	jle    6386 <barriered_work+0x296>
    62ec:	4c 63 c9             	movslq %ecx,%r9
    62ef:	31 c9                	xor    %ecx,%ecx
    62f1:	49 c1 e1 09          	shl    $0x9,%r9
            for (int kk = 0 ; kk < data->mailbox_thread_count ; kk++) {
    62f5:	45 85 ff             	test   %r15d,%r15d
    62f8:	0f 8e 6f 05 00 00    	jle    686d <barriered_work+0x77d>
    62fe:	4d 8b 55 38          	mov    0x38(%r13),%r10
    6302:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    6307:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
              datas[datas2_size++] = ((struct Data*) ((struct Mailbox)data->thread->all_threads[x].tasks[n].mailboxes[kk]).lower);
    6310:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6315:	4c 8b 94 08 70 01 00 00 	mov    0x170(%rax,%rcx,1),%r10
    631d:	41 83 ff 01          	cmp    $0x1,%r15d
    6321:	0f 84 ed 04 00 00    	je     6814 <barriered_work+0x724>
    6327:	48 63 c3             	movslq %ebx,%rax
    632a:	4c 89 d6             	mov    %r10,%rsi
    632d:	48 8d 44 c5 00       	lea    0x0(%rbp,%rax,8),%rax
    6332:	49 8d 3c 03          	lea    (%r11,%rax,1),%rdi
    6336:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6340:	f3 0f 6f 16          	movdqu (%rsi),%xmm2
    6344:	48 83 c0 10          	add    $0x10,%rax
    6348:	48 83 c6 38          	add    $0x38,%rsi
    634c:	0f 11 50 f0          	movups %xmm2,-0x10(%rax)
            for (int kk = 0 ; kk < data->mailbox_thread_count ; kk++) {
    6350:	48 39 c7             	cmp    %rax,%rdi
    6353:	75 eb                	jne    6340 <barriered_work+0x250>
    6355:	42 8d 3c 03          	lea    (%rbx,%r8,1),%edi
    6359:	49 63 c4             	movslq %r12d,%rax
              datas[datas2_size++] = ((struct Data*) ((struct Mailbox)data->thread->all_threads[x].tasks[n].mailboxes[kk]).lower);
    635c:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
    6364:	48 63 ff             	movslq %edi,%rdi
    6367:	42 8d 5c 03 02       	lea    0x2(%rbx,%r8,1),%ebx
          for (int n = 0 ; n < data->thread->all_threads[x].task_count ; n++) {
    636c:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
              datas[datas2_size++] = ((struct Data*) ((struct Mailbox)data->thread->all_threads[x].tasks[n].mailboxes[kk]).lower);
    6373:	48 29 c6             	sub    %rax,%rsi
    6376:	f3 41 0f 6f 04 f2    	movdqu (%r10,%rsi,8),%xmm0
    637c:	0f 11 44 fd 00       	movups %xmm0,0x0(%rbp,%rdi,8)
          for (int n = 0 ; n < data->thread->all_threads[x].task_count ; n++) {
    6381:	4c 39 c9             	cmp    %r9,%rcx
    6384:	75 8a                	jne    6310 <barriered_work+0x220>
        for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6386:	49 81 c5 c8 00 00 00 	add    $0xc8,%r13
    638d:	4d 39 ee             	cmp    %r13,%r14
    6390:	0f 85 4a ff ff ff    	jne    62e0 <barriered_work+0x1f0>
    6396:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    639b:	8b 4c 24 28          	mov    0x28(%rsp),%ecx
    639f:	8b 44 24 30          	mov    0x30(%rsp),%eax
      for (int k = 0 ; k < data->thread->group_count ; k++) {
    63a3:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    63a7:	83 c0 01             	add    $0x1,%eax
    63aa:	01 d1                	add    %edx,%ecx
    63ac:	39 f8                	cmp    %edi,%eax
    63ae:	0f 85 ef fe ff ff    	jne    62a3 <barriered_work+0x1b3>
      char * name = calloc(100, sizeof(char));
    63b4:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    63b9:	bf 64 00 00 00       	mov    $0x64,%edi
    63be:	be 01 00 00 00       	mov    $0x1,%esi
    63c3:	e8 28 c0 ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    63c8:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    63cd:	be 01 00 00 00       	mov    $0x1,%esi
    63d2:	48 8d 0d 6d 0e 00 00 	lea    0xe6d(%rip),%rcx        # 7246 <_IO_stdin_used+0x246>
    63d9:	49 89 c4             	mov    %rax,%r12
    63dc:	48 89 c7             	mov    %rax,%rdi
    63df:	31 c0                	xor    %eax,%eax
    63e1:	44 8b 42 08          	mov    0x8(%rdx),%r8d
    63e5:	ba 64 00 00 00       	mov    $0x64,%edx
    63ea:	e8 91 c1 ff ff       	call   2580 <__sprintf_chk@plt>
      m2 = fopen(name, "w");
    63ef:	4c 89 e7             	mov    %r12,%rdi
    63f2:	48 8d 35 59 0e 00 00 	lea    0xe59(%rip),%rsi        # 7252 <_IO_stdin_used+0x252>
    63f9:	e8 e2 c0 ff ff       	call   24e0 <fopen@plt>
    63fe:	49 89 c4             	mov    %rax,%r12
      for (int x = 0 ; x < datas2_size; x++) {
    6401:	85 db                	test   %ebx,%ebx
    6403:	7e 5a                	jle    645f <barriered_work+0x36f>
    6405:	48 63 db             	movslq %ebx,%rbx
    6408:	49 89 ed             	mov    %rbp,%r13
    640b:	4c 8d 35 42 0e 00 00 	lea    0xe42(%rip),%r14        # 7254 <_IO_stdin_used+0x254>
    6412:	48 8d 5c dd 00       	lea    0x0(%rbp,%rbx,8),%rbx
        char * c = calloc(250, sizeof(char));
    6417:	be 01 00 00 00       	mov    $0x1,%esi
    641c:	bf fa 00 00 00       	mov    $0xfa,%edi
      for (int x = 0 ; x < datas2_size; x++) {
    6421:	49 83 c5 08          	add    $0x8,%r13
        char * c = calloc(250, sizeof(char));
    6425:	e8 c6 bf ff ff       	call   23f0 <calloc@plt>
    642a:	4c 89 f1             	mov    %r14,%rcx
    642d:	ba fa 00 00 00       	mov    $0xfa,%edx
    6432:	be 01 00 00 00       	mov    $0x1,%esi
    6437:	49 89 c7             	mov    %rax,%r15
        sprintf(c, "mailbox %d\n", datas[x]->id);
    643a:	49 8b 45 f8          	mov    -0x8(%r13),%rax
    643e:	4c 89 ff             	mov    %r15,%rdi
    6441:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    6448:	31 c0                	xor    %eax,%eax
    644a:	e8 31 c1 ff ff       	call   2580 <__sprintf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    644f:	4c 89 e6             	mov    %r12,%rsi
    6452:	4c 89 ff             	mov    %r15,%rdi
    6455:	e8 56 bf ff ff       	call   23b0 <fputs@plt>
      for (int x = 0 ; x < datas2_size; x++) {
    645a:	4c 39 eb             	cmp    %r13,%rbx
    645d:	75 b8                	jne    6417 <barriered_work+0x327>
      fclose(m2);
    645f:	4c 89 e7             	mov    %r12,%rdi
    6462:	e8 e9 be ff ff       	call   2350 <fclose@plt>
      free(datas);
    6467:	48 89 ef             	mov    %rbp,%rdi
    646a:	e8 81 be ff ff       	call   22f0 <free@plt>
      asm volatile ("sfence" ::: "memory");
    646f:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6472:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6477:	31 ff                	xor    %edi,%edi
    6479:	48 8b 95 60 01 00 00 	mov    0x160(%rbp),%rdx
    6480:	48 89 d6             	mov    %rdx,%rsi
    6483:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
    6488:	48 c1 e6 05          	shl    $0x5,%rsi
    648c:	48 03 b5 50 01 00 00 	add    0x150(%rbp),%rsi
    6493:	e8 a8 be ff ff       	call   2340 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6498:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    649f:	48 8b 50 48          	mov    0x48(%rax),%rdx
    64a3:	8b 5a 10             	mov    0x10(%rdx),%ebx
    64a6:	83 c3 01             	add    $0x1,%ebx
    while (data->scheduled == 1) {
    64a9:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    int modcount = ++data->thread->protected_state->modcount;
    64b0:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    64b3:	74 12                	je     64c7 <barriered_work+0x3d7>
    64b5:	eb 66                	jmp    651d <barriered_work+0x42d>
    64b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    if (modcount != data->thread->protected_state->modcount) {
    64c0:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    64c7:	48 63 95 30 01 00 00 	movslq 0x130(%rbp),%rdx
    64ce:	48 8b 40 18          	mov    0x18(%rax),%rax
    64d2:	48 63 7d 04          	movslq 0x4(%rbp),%rdi
      data->n++;
    64d6:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    64de:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    64e2:	48 c1 e7 09          	shl    $0x9,%rdi
    64e6:	48 03 78 38          	add    0x38(%rax),%rdi
    64ea:	ff 95 20 01 00 00    	call   *0x120(%rbp)
      asm volatile ("sfence" ::: "memory");
    64f0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    64f3:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    64fa:	74 c4                	je     64c0 <barriered_work+0x3d0>
    if (modcount != data->thread->protected_state->modcount) {
    64fc:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6501:	48 8b 80 28 01 00 00 	mov    0x128(%rax),%rax
    6508:	48 8b 40 48          	mov    0x48(%rax),%rax
    650c:	3b 58 10             	cmp    0x10(%rax),%ebx
    650f:	74 0c                	je     651d <barriered_work+0x42d>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6511:	48 8d 3d 48 0d 00 00 	lea    0xd48(%rip),%rdi        # 7260 <_IO_stdin_used+0x260>
    6518:	e8 03 be ff ff       	call   2320 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    651d:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    6522:	31 ff                	xor    %edi,%edi
    6524:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    652b:	48 89 c6             	mov    %rax,%rsi
    652e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    6533:	48 c1 e6 05          	shl    $0x5,%rsi
    6537:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    653e:	48 83 c6 10          	add    $0x10,%rsi
    6542:	e8 f9 bd ff ff       	call   2340 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6547:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    654e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    6553:	48 83 c0 01          	add    $0x1,%rax
    6557:	48 99                	cqto
    6559:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
  if (data->sending == 1) {
    6560:	83 bb 80 01 00 00 01 	cmpl   $0x1,0x180(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6567:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
  if (data->sending == 1) {
    656e:	0f 85 de fb ff ff    	jne    6152 <barriered_work+0x62>
    6574:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    6579:	e8 92 dd ff ff       	call   4310 <sendm.part.0>
    657e:	e9 cf fb ff ff       	jmp    6152 <barriered_work+0x62>
      receive(data);
    6583:	e8 98 f9 ff ff       	call   5f20 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6588:	44 8b bb 40 01 00 00 	mov    0x140(%rbx),%r15d
        int t = data->task_index;
    658f:	48 63 73 04          	movslq 0x4(%rbx),%rsi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6593:	45 85 ff             	test   %r15d,%r15d
    6596:	0f 8e ae fc ff ff    	jle    624a <barriered_work+0x15a>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    659c:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    65a5:	45 31 ed             	xor    %r13d,%r13d
    65a8:	48 c1 e6 09          	shl    $0x9,%rsi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    65ac:	45 31 e4             	xor    %r12d,%r12d
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    65af:	4c 8b 9b 28 01 00 00 	mov    0x128(%rbx),%r11
    65b6:	4d 89 ee             	mov    %r13,%r14
    65b9:	49 89 dd             	mov    %rbx,%r13
int barriered_work(struct BarrierTask *data) {
    65bc:	31 c9                	xor    %ecx,%ecx
    65be:	31 d2                	xor    %edx,%edx
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    65c0:	31 c0                	xor    %eax,%eax
    65c2:	49 89 f1             	mov    %rsi,%r9
    65c5:	eb 20                	jmp    65e7 <barriered_work+0x4f7>
    65c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    65d0:	83 c0 01             	add    $0x1,%eax
    65d3:	48 83 c2 38          	add    $0x38,%rdx
    65d7:	48 81 c1 c8 00 00 00 	add    $0xc8,%rcx
    65de:	44 39 f8             	cmp    %r15d,%eax
    65e1:	0f 84 7f fb ff ff    	je     6166 <barriered_work+0x76>
              if (y == b) { continue; }
    65e7:	41 39 c4             	cmp    %eax,%r12d
    65ea:	74 e4                	je     65d0 <barriered_work+0x4e0>
              int next_task = abs((t + 1) % (data->thread_count));
    65ec:	49 63 b5 34 01 00 00 	movslq 0x134(%r13),%rsi
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    65f3:	41 39 43 08          	cmp    %eax,0x8(%r11)
    65f7:	75 d7                	jne    65d0 <barriered_work+0x4e0>
    65f9:	49 8b 7b 20          	mov    0x20(%r11),%rdi
    65fd:	4c 8b 44 0f 38       	mov    0x38(%rdi,%rcx,1),%r8
    6602:	4f 8b 94 08 70 01 00 00 	mov    0x170(%r8,%r9,1),%r10
    660a:	4d 01 f2             	add    %r14,%r10
    660d:	41 83 7a 30 02       	cmpl   $0x2,0x30(%r10)
    6612:	75 bc                	jne    65d0 <barriered_work+0x4e0>
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    6614:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    6619:	48 8b 6c 1f 38       	mov    0x38(%rdi,%rbx,1),%rbp
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    661e:	85 f6                	test   %esi,%esi
    6620:	0f 8e f7 01 00 00    	jle    681d <barriered_work+0x72d>
    6626:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    662b:	48 c1 e6 09          	shl    $0x9,%rsi
                  int all_wrote = 1;
    662f:	bf 01 00 00 00       	mov    $0x1,%edi
    6634:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    6639:	48 8d 1c 2e          	lea    (%rsi,%rbp,1),%rbx
    663d:	48 89 74 24 30       	mov    %rsi,0x30(%rsp)
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    6642:	48 89 ee             	mov    %rbp,%rsi
    6645:	0f 1f 00             	nopl   (%rax)
                    if (((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving == 0) {
    6648:	4c 8b 86 70 01 00 00 	mov    0x170(%rsi),%r8
    664f:	4d 8b 44 10 08       	mov    0x8(%r8,%rdx,1),%r8
                      all_wrote = 0;
    6654:	45 8b 80 80 01 00 00 	mov    0x180(%r8),%r8d
    665b:	45 85 c0             	test   %r8d,%r8d
    665e:	41 b8 00 00 00 00    	mov    $0x0,%r8d
    6664:	41 0f 44 f8          	cmove  %r8d,%edi
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    6668:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    666f:	48 39 f3             	cmp    %rsi,%rbx
    6672:	75 d4                	jne    6648 <barriered_work+0x558>
                  if (all_finished == 1 && all_wrote == 1 /*&& ((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available == 0 */) {
    6674:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    6679:	83 ff 01             	cmp    $0x1,%edi
    667c:	0f 85 4e ff ff ff    	jne    65d0 <barriered_work+0x4e0>
    6682:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
                        ((struct Data*)data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving = 0;
    6687:	48 8b be 70 01 00 00 	mov    0x170(%rsi),%rdi
                      for (int nn = 0 ; nn < data->thread_count; nn++) {
    668e:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
                        ((struct Data*)data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving = 0;
    6695:	48 8b 7c 17 08       	mov    0x8(%rdi,%rdx,1),%rdi
    669a:	c7 87 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rdi)
                      for (int nn = 0 ; nn < data->thread_count; nn++) {
    66a4:	48 39 f3             	cmp    %rsi,%rbx
    66a7:	75 de                	jne    6687 <barriered_work+0x597>
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    66a9:	4a 8b b4 0d 70 01 00 00 	mov    0x170(%rbp,%r9,1),%rsi
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    66b1:	89 44 24 3c          	mov    %eax,0x3c(%rsp)
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    66b5:	48 8b 7c 16 18       	mov    0x18(%rsi,%rdx,1),%rdi
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    66ba:	49 8b 72 18          	mov    0x18(%r10),%rsi
    66be:	4c 8b 1e             	mov    (%rsi),%r11
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    66c1:	48 8b 1f             	mov    (%rdi),%rbx
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    66c4:	48 8b 76 08          	mov    0x8(%rsi),%rsi
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    66c8:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    66cd:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    66d2:	4c 89 4c 24 30       	mov    %r9,0x30(%rsp)
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    66d7:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
                      void * right = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1];
    66dc:	48 8b 5f 08          	mov    0x8(%rdi),%rbx
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    66e0:	49 81 c3 70 01 00 00 	add    $0x170,%r11
    66e7:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    66ec:	be 70 01 00 00       	mov    $0x170,%esi
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    66f1:	4c 8b 4c 35 00       	mov    0x0(%rbp,%rsi,1),%r9
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    66f6:	4d 8b 14 30          	mov    (%r8,%rsi,1),%r10
                  for (int nn = 0 ; nn < data->thread_count ; nn++) {
    66fa:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6701:	49 01 d1             	add    %rdx,%r9
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6704:	4d 01 f2             	add    %r14,%r10
    return mailbox->higher;
    6707:	f3 41 0f 6f 01       	movdqu (%r9),%xmm0
    mailbox->lower = data;
    670c:	49 8b 42 08          	mov    0x8(%r10),%rax
    return mailbox->lower;
    6710:	66 0f 6f c8          	movdqa %xmm0,%xmm1
    mailbox->lower = data;
    6714:	49 89 01             	mov    %rax,(%r9)
                        ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6717:	0f 12 d8             	movhlps %xmm0,%xmm3
    return mailbox->lower;
    671a:	66 0f c6 c8 01       	shufpd $0x1,%xmm0,%xmm1
    mailbox->lower = data;
    671f:	41 0f 11 0a          	movups %xmm1,(%r10)
                        ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6723:	4d 8b 09             	mov    (%r9),%r9
                        ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6726:	66 49 0f 7e da       	movq   %xmm3,%r10
    672b:	41 c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%r10)
                        ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6736:	41 c7 81 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%r9)
                        ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_sending = 1;
    6741:	66 49 0f 7e c1       	movq   %xmm0,%r9
    6746:	41 c7 81 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r9)
                  for (int nn = 0 ; nn < data->thread_count ; nn++) {
    6751:	49 39 f3             	cmp    %rsi,%r11
    6754:	75 9b                	jne    66f1 <barriered_work+0x601>
    6756:	8b 44 24 3c          	mov    0x3c(%rsp),%eax
    675a:	4c 8b 4c 24 30       	mov    0x30(%rsp),%r9
    675f:	be 70 01 00 00       	mov    $0x170,%esi
    6764:	89 44 24 30          	mov    %eax,0x30(%rsp)
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6768:	48 8b 44 35 00       	mov    0x0(%rbp,%rsi,1),%rax
    676d:	4d 8b 14 30          	mov    (%r8,%rsi,1),%r10
    6771:	48 8b 04 10          	mov    (%rax,%rdx,1),%rax
    6775:	4b 39 04 32          	cmp    %rax,(%r10,%r14,1)
    6779:	0f 84 d1 00 00 00    	je     6850 <barriered_work+0x760>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    677f:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    6786:	49 39 f3             	cmp    %rsi,%r11
    6789:	75 dd                	jne    6768 <barriered_work+0x678>
    678b:	8b 44 24 30          	mov    0x30(%rsp),%eax
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0] = right;
    678f:	48 89 1f             	mov    %rbx,(%rdi)
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1] = left;
    6792:	49 8b b5 28 01 00 00 	mov    0x128(%r13),%rsi
    6799:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    679e:	48 8b 76 20          	mov    0x20(%rsi),%rsi
    67a2:	48 8b 74 1e 38       	mov    0x38(%rsi,%rbx,1),%rsi
    67a7:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    67ac:	4a 8b b4 0e 70 01 00 00 	mov    0x170(%rsi,%r9,1),%rsi
    67b4:	48 8b 74 16 18       	mov    0x18(%rsi,%rdx,1),%rsi
    67b9:	48 89 5e 08          	mov    %rbx,0x8(%rsi)
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0] = right3;
    67bd:	49 8b b5 28 01 00 00 	mov    0x128(%r13),%rsi
    67c4:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    67c9:	48 8b 76 20          	mov    0x20(%rsi),%rsi
    67cd:	48 8b 74 0e 38       	mov    0x38(%rsi,%rcx,1),%rsi
    67d2:	4a 8b b4 0e 70 01 00 00 	mov    0x170(%rsi,%r9,1),%rsi
    67da:	4a 8b 74 36 18       	mov    0x18(%rsi,%r14,1),%rsi
    67df:	48 89 1e             	mov    %rbx,(%rsi)
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1] = left3;
    67e2:	49 8b b5 28 01 00 00 	mov    0x128(%r13),%rsi
    67e9:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    67ee:	48 8b 76 20          	mov    0x20(%rsi),%rsi
    67f2:	48 8b 74 0e 38       	mov    0x38(%rsi,%rcx,1),%rsi
    67f7:	4a 8b b4 0e 70 01 00 00 	mov    0x170(%rsi,%r9,1),%rsi
    67ff:	4a 8b 74 36 18       	mov    0x18(%rsi,%r14,1),%rsi
    6804:	48 89 5e 08          	mov    %rbx,0x8(%rsi)
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6808:	4d 8b 9d 28 01 00 00 	mov    0x128(%r13),%r11
    680f:	e9 bc fd ff ff       	jmp    65d0 <barriered_work+0x4e0>
              datas[datas2_size++] = ((struct Data*) ((struct Mailbox)data->thread->all_threads[x].tasks[n].mailboxes[kk]).lower);
    6814:	89 df                	mov    %ebx,%edi
            for (int kk = 0 ; kk < data->mailbox_thread_count ; kk++) {
    6816:	31 c0                	xor    %eax,%eax
    6818:	e9 3f fb ff ff       	jmp    635c <barriered_work+0x26c>
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    681d:	4a 8b b4 0d 70 01 00 00 	mov    0x170(%rbp,%r9,1),%rsi
    6825:	48 8b 7c 16 18       	mov    0x18(%rsi,%rdx,1),%rdi
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    682a:	49 8b 72 18          	mov    0x18(%r10),%rsi
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    682e:	48 8b 1f             	mov    (%rdi),%rbx
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    6831:	4c 8b 1e             	mov    (%rsi),%r11
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    6834:	48 8b 76 08          	mov    0x8(%rsi),%rsi
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    6838:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
                      void * right = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1];
    683d:	48 8b 5f 08          	mov    0x8(%rdi),%rbx
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    6841:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    6846:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
                  for (int nn = 0 ; nn < data->thread_count ; nn++) {
    684b:	e9 3f ff ff ff       	jmp    678f <barriered_work+0x69f>
    6850:	bf 01 00 00 00       	mov    $0x1,%edi
    6855:	48 8d 35 cf 09 00 00 	lea    0x9cf(%rip),%rsi        # 722b <_IO_stdin_used+0x22b>
    685c:	31 c0                	xor    %eax,%eax
    685e:	e8 3d bc ff ff       	call   24a0 <__printf_chk@plt>
                          exit(1);
    6863:	bf 01 00 00 00       	mov    $0x1,%edi
    6868:	e8 93 bc ff ff       	call   2500 <exit@plt>
          for (int n = 0 ; n < data->thread->all_threads[x].task_count ; n++) {
    686d:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
    6874:	49 39 c9             	cmp    %rcx,%r9
    6877:	0f 85 78 fa ff ff    	jne    62f5 <barriered_work+0x205>
    687d:	e9 04 fb ff ff       	jmp    6386 <barriered_work+0x296>
    6882:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      char * name = calloc(100, sizeof(char));
    6888:	be 01 00 00 00       	mov    $0x1,%esi
    688d:	bf 64 00 00 00       	mov    $0x64,%edi
    6892:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
    6897:	e8 54 bb ff ff       	call   23f0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    689c:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    68a1:	be 01 00 00 00       	mov    $0x1,%esi
    68a6:	48 8d 0d 99 09 00 00 	lea    0x999(%rip),%rcx        # 7246 <_IO_stdin_used+0x246>
    68ad:	48 89 c7             	mov    %rax,%rdi
    68b0:	48 89 c3             	mov    %rax,%rbx
    68b3:	31 c0                	xor    %eax,%eax
    68b5:	44 8b 42 08          	mov    0x8(%rdx),%r8d
    68b9:	ba 64 00 00 00       	mov    $0x64,%edx
    68be:	e8 bd bc ff ff       	call   2580 <__sprintf_chk@plt>
      m2 = fopen(name, "w");
    68c3:	48 8d 35 88 09 00 00 	lea    0x988(%rip),%rsi        # 7252 <_IO_stdin_used+0x252>
    68ca:	48 89 df             	mov    %rbx,%rdi
    68cd:	e8 0e bc ff ff       	call   24e0 <fopen@plt>
    68d2:	49 89 c4             	mov    %rax,%r12
      for (int x = 0 ; x < datas2_size; x++) {
    68d5:	e9 85 fb ff ff       	jmp    645f <barriered_work+0x36f>
    68da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000068e0 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    68e0:	f3 0f 1e fa          	endbr64
    68e4:	53                   	push   %rbx
    68e5:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    68e8:	e8 43 f2 ff ff       	call   5b30 <barriered_work_ingest>
  barriered_work(data);
    68ed:	48 89 df             	mov    %rbx,%rdi
}
    68f0:	5b                   	pop    %rbx
  barriered_work(data);
    68f1:	e9 fa f7 ff ff       	jmp    60f0 <barriered_work>
    68f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006900 <sendm>:
int sendm(struct BarrierTask *data) {
    6900:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    6904:	83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%rdi)
    690b:	74 03                	je     6910 <sendm+0x10>
}
    690d:	31 c0                	xor    %eax,%eax
    690f:	c3                   	ret
int sendm(struct BarrierTask *data) {
    6910:	48 83 ec 08          	sub    $0x8,%rsp
    6914:	e8 f7 d9 ff ff       	call   4310 <sendm.part.0>
}
    6919:	31 c0                	xor    %eax,%eax
    691b:	48 83 c4 08          	add    $0x8,%rsp
    691f:	c3                   	ret

0000000000006920 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    6920:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6924:	85 f6                	test   %esi,%esi
    6926:	74 10                	je     6938 <mailboxkind+0x18>
  return NULL;
    6928:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    692a:	83 fe 01             	cmp    $0x1,%esi
    692d:	74 01                	je     6930 <mailboxkind+0x10>
}
    692f:	c3                   	ret
    return mailbox->higher;
    6930:	48 8b 47 08          	mov    0x8(%rdi),%rax
}
    6934:	c3                   	ret
    6935:	0f 1f 00             	nopl   (%rax)
    return mailbox->lower;
    6938:	48 8b 07             	mov    (%rdi),%rax
    693b:	c3                   	ret
    693c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006940 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    6940:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6944:	85 d2                	test   %edx,%edx
    6946:	75 08                	jne    6950 <setmailboxkind+0x10>
    mailbox->lower = data;
    6948:	48 89 37             	mov    %rsi,(%rdi)
}
    694b:	31 c0                	xor    %eax,%eax
    694d:	c3                   	ret
    694e:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    6950:	83 fa 01             	cmp    $0x1,%edx
    6953:	74 13                	je     6968 <setmailboxkind+0x28>
  if (kind == 2) {
    6955:	83 fa 02             	cmp    $0x2,%edx
    6958:	75 f1                	jne    694b <setmailboxkind+0xb>
    mailbox->pending = data;
    695a:	48 89 77 10          	mov    %rsi,0x10(%rdi)
}
    695e:	31 c0                	xor    %eax,%eax
    6960:	c3                   	ret
    6961:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    mailbox->higher = data;
    6968:	48 89 77 08          	mov    %rsi,0x8(%rdi)
}
    696c:	31 c0                	xor    %eax,%eax
    696e:	c3                   	ret
    696f:	90                   	nop

0000000000006970 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6970:	f3 0f 1e fa          	endbr64
}
    6974:	31 c0                	xor    %eax,%eax
    6976:	c3                   	ret
    6977:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006980 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6980:	f3 0f 1e fa          	endbr64
    6984:	31 c0                	xor    %eax,%eax
    6986:	c3                   	ret
    6987:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006990 <after>:
int after(struct timespec left, struct timespec right) {
    6990:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6994:	31 c0                	xor    %eax,%eax
    6996:	48 39 d7             	cmp    %rdx,%rdi
    6999:	7e 08                	jle    69a3 <after+0x13>
    699b:	31 c0                	xor    %eax,%eax
    699d:	48 39 ce             	cmp    %rcx,%rsi
    69a0:	0f 9f c0             	setg   %al
}
    69a3:	c3                   	ret
    69a4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    69af:	90                   	nop

00000000000069b0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    69b0:	f3 0f 1e fa          	endbr64
    69b4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    69b9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    69be:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    69c0:	48 39 d7             	cmp    %rdx,%rdi
    69c3:	7f 18                	jg     69dd <within+0x2d>
    69c5:	4d 39 d8             	cmp    %r11,%r8
    69c8:	0f 9e c2             	setle  %dl
    69cb:	48 39 ce             	cmp    %rcx,%rsi
    69ce:	0f 9e c0             	setle  %al
    69d1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    69d3:	31 c0                	xor    %eax,%eax
    69d5:	4d 39 d1             	cmp    %r10,%r9
    69d8:	0f 9e c0             	setle  %al
    69db:	21 d0                	and    %edx,%eax
}
    69dd:	c3                   	ret
    69de:	66 90                	xchg   %ax,%ax

00000000000069e0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    69e0:	f3 0f 1e fa          	endbr64
    69e4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    69e9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    69ee:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    69f3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    69f8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    69fd:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6a02:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6a07:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    6a0c:	48 39 fe             	cmp    %rdi,%rsi
    6a0f:	7d 2f                	jge    6a40 <overlap+0x60>
    6a11:	48 39 ca             	cmp    %rcx,%rdx
    6a14:	7d 62                	jge    6a78 <overlap+0x98>
    6a16:	4d 39 da             	cmp    %r11,%r10
    6a19:	7d 0e                	jge    6a29 <overlap+0x49>
    return 1;
    6a1b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6a20:	4d 39 c1             	cmp    %r8,%r9
    6a23:	0f 8c 7f 00 00 00    	jl     6aa8 <overlap+0xc8>
  return 0;
    6a29:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6a2b:	4d 39 c1             	cmp    %r8,%r9
    6a2e:	7f 4c                	jg     6a7c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6a30:	31 c0                	xor    %eax,%eax
    6a32:	4d 39 da             	cmp    %r11,%r10
    6a35:	0f 9e c0             	setle  %al
    6a38:	c3                   	ret
    6a39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6a40:	7e 4e                	jle    6a90 <overlap+0xb0>
    6a42:	48 39 ca             	cmp    %rcx,%rdx
    6a45:	7f 39                	jg     6a80 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6a47:	75 31                	jne    6a7a <overlap+0x9a>
    6a49:	4d 39 c1             	cmp    %r8,%r9
    6a4c:	7c 2c                	jl     6a7a <overlap+0x9a>
    return 1;
    6a4e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6a53:	4d 39 da             	cmp    %r11,%r10
    6a56:	7d 24                	jge    6a7c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6a58:	48 39 ca             	cmp    %rcx,%rdx
    6a5b:	0f 94 c2             	sete   %dl
    6a5e:	48 39 fe             	cmp    %rdi,%rsi
    6a61:	0f 94 c0             	sete   %al
    6a64:	21 c2                	and    %eax,%edx
    6a66:	31 c0                	xor    %eax,%eax
    6a68:	4d 39 c1             	cmp    %r8,%r9
    6a6b:	0f 94 c0             	sete   %al
    6a6e:	21 d0                	and    %edx,%eax
    6a70:	c3                   	ret
    6a71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6a78:	74 af                	je     6a29 <overlap+0x49>
  return 0;
    6a7a:	31 c0                	xor    %eax,%eax
}
    6a7c:	c3                   	ret
    6a7d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6a80:	4d 39 da             	cmp    %r11,%r10
    6a83:	7e c4                	jle    6a49 <overlap+0x69>
    return 1;
    6a85:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6a8a:	4d 39 c1             	cmp    %r8,%r9
    6a8d:	7e ba                	jle    6a49 <overlap+0x69>
    6a8f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6a90:	48 39 ca             	cmp    %rcx,%rdx
    6a93:	7c 94                	jl     6a29 <overlap+0x49>
    6a95:	4d 39 c1             	cmp    %r8,%r9
    6a98:	7d b4                	jge    6a4e <overlap+0x6e>
    6a9a:	48 39 ca             	cmp    %rcx,%rdx
    6a9d:	74 91                	je     6a30 <overlap+0x50>
    6a9f:	eb d9                	jmp    6a7a <overlap+0x9a>
    6aa1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6aa8:	c3                   	ret
    6aa9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006ab0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6ab0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6ab4:	85 f6                	test   %esi,%esi
    6ab6:	0f 8e 44 03 00 00    	jle    6e00 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    6abc:	41 57                	push   %r15
    6abe:	41 89 f7             	mov    %esi,%r15d
    6ac1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6ac3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6ac6:	41 55                	push   %r13
    6ac8:	41 54                	push   %r12
    6aca:	55                   	push   %rbp
    6acb:	53                   	push   %rbx
    6acc:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6ad0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6ad4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6ad9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    6ade:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6ae1:	45 39 e6             	cmp    %r12d,%r14d
    6ae4:	0f 84 4e 02 00 00    	je     6d38 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6aea:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6aef:	8b 50 08             	mov    0x8(%rax),%edx
    6af2:	85 d2                	test   %edx,%edx
    6af4:	0f 8e 3e 02 00 00    	jle    6d38 <verify+0x288>
    6afa:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    6aff:	31 c9                	xor    %ecx,%ecx
    6b01:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6b06:	31 c0                	xor    %eax,%eax
    6b08:	44 89 f2             	mov    %r14d,%edx
    6b0b:	bf 01 00 00 00       	mov    $0x1,%edi
    6b10:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6b15:	48 8d 35 54 07 00 00 	lea    0x754(%rip),%rsi        # 7270 <_IO_stdin_used+0x270>
    6b1c:	e8 7f b9 ff ff       	call   24a0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6b21:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6b26:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    6b2b:	8b 40 08             	mov    0x8(%rax),%eax
    6b2e:	85 c0                	test   %eax,%eax
    6b30:	0f 8e e6 01 00 00    	jle    6d1c <verify+0x26c>
    6b36:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6b39:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    6b3e:	31 db                	xor    %ebx,%ebx
    6b40:	48 c1 e0 09          	shl    $0x9,%rax
    6b44:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6b49:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    6b4e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6b53:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6b58:	4c 8b 20             	mov    (%rax),%r12
    6b5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6b60:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6b65:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    6b6a:	49 89 de             	mov    %rbx,%r14
    6b6d:	48 8d 35 11 07 00 00 	lea    0x711(%rip),%rsi        # 7285 <_IO_stdin_used+0x285>
    6b74:	49 c1 e6 09          	shl    $0x9,%r14
    6b78:	bf 01 00 00 00       	mov    $0x1,%edi
    6b7d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6b81:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    6b89:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    6b8e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    6b96:	31 c0                	xor    %eax,%eax
    6b98:	e8 03 b9 ff ff       	call   24a0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6b9d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6ba2:	4c 8b 20             	mov    (%rax),%r12
    6ba5:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    6bae:	0f 8e 47 01 00 00    	jle    6cfb <verify+0x24b>
    6bb4:	4c 03 75 00          	add    0x0(%rbp),%r14
    6bb8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6bbd:	ba 01 00 00 00       	mov    $0x1,%edx
    6bc2:	4d 89 f5             	mov    %r14,%r13
    6bc5:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6bcc:	4d 85 f6             	test   %r14,%r14
    6bcf:	0f 8e 21 01 00 00    	jle    6cf6 <verify+0x246>
    6bd5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6bd8:	48 89 d5             	mov    %rdx,%rbp
    6bdb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6be0:	31 db                	xor    %ebx,%ebx
    6be2:	4d 89 f2             	mov    %r14,%r10
    6be5:	48 c1 e5 05          	shl    $0x5,%rbp
    6be9:	48 83 ed 20          	sub    $0x20,%rbp
    6bed:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6bf1:	49 89 ee             	mov    %rbp,%r14
    6bf4:	48 89 dd             	mov    %rbx,%rbp
    6bf7:	48 89 d3             	mov    %rdx,%rbx
    6bfa:	eb 31                	jmp    6c2d <verify+0x17d>
    6bfc:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6c00:	4c 39 c2             	cmp    %r8,%rdx
    6c03:	0f 8d 57 01 00 00    	jge    6d60 <verify+0x2b0>
    6c09:	4c 39 df             	cmp    %r11,%rdi
    6c0c:	7e 05                	jle    6c13 <verify+0x163>
    6c0e:	49 39 c1             	cmp    %rax,%r9
    6c11:	7c 75                	jl     6c88 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6c13:	4c 39 df             	cmp    %r11,%rdi
    6c16:	0f 8d ab 01 00 00    	jge    6dc7 <verify+0x317>
    6c1c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6c20:	48 83 c5 01          	add    $0x1,%rbp
    6c24:	49 39 ea             	cmp    %rbp,%r10
    6c27:	0f 8e a9 00 00 00    	jle    6cd6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6c2d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    6c34:	48 89 e8             	mov    %rbp,%rax
    6c37:	48 c1 e0 05          	shl    $0x5,%rax
    6c3b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    6c42:	4c 01 f2             	add    %r14,%rdx
    6c45:	48 8b 08             	mov    (%rax),%rcx
    6c48:	48 8b 78 10          	mov    0x10(%rax),%rdi
    6c4c:	48 8b 32             	mov    (%rdx),%rsi
    6c4f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6c53:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6c57:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    6c5b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    6c5f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6c63:	48 39 f1             	cmp    %rsi,%rcx
    6c66:	7c 98                	jl     6c00 <verify+0x150>
    6c68:	0f 8e 42 01 00 00    	jle    6db0 <verify+0x300>
    6c6e:	4c 39 c2             	cmp    %r8,%rdx
    6c71:	0f 8f f9 00 00 00    	jg     6d70 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6c77:	75 a7                	jne    6c20 <verify+0x170>
    6c79:	4c 39 df             	cmp    %r11,%rdi
    6c7c:	7f a2                	jg     6c20 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6c7e:	49 39 c1             	cmp    %rax,%r9
    6c81:	7c 9d                	jl     6c20 <verify+0x170>
    6c83:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6c88:	49 89 c1             	mov    %rax,%r9
    6c8b:	48 89 f9             	mov    %rdi,%rcx
    6c8e:	48 89 f2             	mov    %rsi,%rdx
    6c91:	bf 01 00 00 00       	mov    $0x1,%edi
    6c96:	48 8d 35 83 09 00 00 	lea    0x983(%rip),%rsi        # 7620 <_IO_stdin_used+0x620>
    6c9d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6c9f:	48 83 c5 01          	add    $0x1,%rbp
    6ca3:	e8 f8 b7 ff ff       	call   24a0 <__printf_chk@plt>
    6ca8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6cad:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    6cb2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6cb5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6cba:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6cc1:	4c 8b 20             	mov    (%rax),%r12
    6cc4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6cc9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6ccd:	49 39 ea             	cmp    %rbp,%r10
    6cd0:	0f 8f 57 ff ff ff    	jg     6c2d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6cd6:	48 89 da             	mov    %rbx,%rdx
    6cd9:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    6ce0:	7d 14                	jge    6cf6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6ce2:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6ce9:	48 83 c2 01          	add    $0x1,%rdx
    6ced:	4d 85 f6             	test   %r14,%r14
    6cf0:	0f 8f e2 fe ff ff    	jg     6bd8 <verify+0x128>
    6cf6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6cfb:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6d00:	48 83 c3 01          	add    $0x1,%rbx
    6d04:	39 58 08             	cmp    %ebx,0x8(%rax)
    6d07:	0f 8f 53 fe ff ff    	jg     6b60 <verify+0xb0>
    6d0d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6d12:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6d17:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6d1c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6d21:	48 83 c1 01          	add    $0x1,%rcx
    6d25:	39 48 08             	cmp    %ecx,0x8(%rax)
    6d28:	0f 8f d8 fd ff ff    	jg     6b06 <verify+0x56>
    6d2e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6d33:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6d38:	48 81 44 24 10 c8 00 00 00 	addq   $0xc8,0x10(%rsp)
    6d41:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6d46:	41 39 c7             	cmp    %eax,%r15d
    6d49:	0f 84 86 00 00 00    	je     6dd5 <verify+0x325>
    6d4f:	41 89 c4             	mov    %eax,%r12d
    6d52:	e9 8a fd ff ff       	jmp    6ae1 <verify+0x31>
    6d57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6d60:	0f 85 ba fe ff ff    	jne    6c20 <verify+0x170>
    6d66:	e9 a8 fe ff ff       	jmp    6c13 <verify+0x163>
    6d6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6d70:	49 39 c1             	cmp    %rax,%r9
    6d73:	7e 09                	jle    6d7e <verify+0x2ce>
    6d75:	4c 39 df             	cmp    %r11,%rdi
    6d78:	0f 8c 0a ff ff ff    	jl     6c88 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6d7e:	4c 39 df             	cmp    %r11,%rdi
    6d81:	0f 8f 99 fe ff ff    	jg     6c20 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6d87:	49 39 c1             	cmp    %rax,%r9
    6d8a:	0f 8d f8 fe ff ff    	jge    6c88 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6d90:	48 39 f1             	cmp    %rsi,%rcx
    6d93:	0f 85 87 fe ff ff    	jne    6c20 <verify+0x170>
    6d99:	4c 39 c2             	cmp    %r8,%rdx
    6d9c:	0f 85 7e fe ff ff    	jne    6c20 <verify+0x170>
    6da2:	4c 39 df             	cmp    %r11,%rdi
    6da5:	0f 84 dd fe ff ff    	je     6c88 <verify+0x1d8>
    6dab:	e9 70 fe ff ff       	jmp    6c20 <verify+0x170>
    6db0:	4c 39 c2             	cmp    %r8,%rdx
    6db3:	0f 8c 5a fe ff ff    	jl     6c13 <verify+0x163>
    6db9:	4c 39 df             	cmp    %r11,%rdi
    6dbc:	7e c9                	jle    6d87 <verify+0x2d7>
    6dbe:	4c 39 c2             	cmp    %r8,%rdx
    6dc1:	0f 85 59 fe ff ff    	jne    6c20 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6dc7:	49 39 c1             	cmp    %rax,%r9
    6dca:	0f 8f 50 fe ff ff    	jg     6c20 <verify+0x170>
    6dd0:	e9 b3 fe ff ff       	jmp    6c88 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    6dd5:	48 81 44 24 18 c8 00 00 00 	addq   $0xc8,0x18(%rsp)
    6dde:	41 8d 46 01          	lea    0x1(%r14),%eax
    6de2:	45 39 e6             	cmp    %r12d,%r14d
    6de5:	74 08                	je     6def <verify+0x33f>
    6de7:	41 89 c6             	mov    %eax,%r14d
    6dea:	e9 ea fc ff ff       	jmp    6ad9 <verify+0x29>
}
    6def:	48 83 c4 58          	add    $0x58,%rsp
    6df3:	31 c0                	xor    %eax,%eax
    6df5:	5b                   	pop    %rbx
    6df6:	5d                   	pop    %rbp
    6df7:	41 5c                	pop    %r12
    6df9:	41 5d                	pop    %r13
    6dfb:	41 5e                	pop    %r14
    6dfd:	41 5f                	pop    %r15
    6dff:	c3                   	ret
    6e00:	31 c0                	xor    %eax,%eax
    6e02:	c3                   	ret

Disassembly of section .fini:

0000000000006e04 <_fini>:
    6e04:	f3 0f 1e fa          	endbr64
    6e08:	48 83 ec 08          	sub    $0x8,%rsp
    6e0c:	48 83 c4 08          	add    $0x8,%rsp
    6e10:	c3                   	ret
