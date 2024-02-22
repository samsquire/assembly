
multibarrier-evented4:     file format elf64-x86-64


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
    2020:	ff 35 42 7e 00 00    	push   0x7e42(%rip)        # 9e68 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 44 7e 00 00    	jmp    *0x7e44(%rip)        # 9e70 <_GLOBAL_OFFSET_TABLE_+0x10>
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
    22f4:	ff 25 fe 7c 00 00    	jmp    *0x7cfe(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    22fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000002300 <free@plt>:
    2300:	f3 0f 1e fa          	endbr64
    2304:	ff 25 6e 7b 00 00    	jmp    *0x7b6e(%rip)        # 9e78 <free@GLIBC_2.2.5>
    230a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002310 <putchar@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 66 7b 00 00    	jmp    *0x7b66(%rip)        # 9e80 <putchar@GLIBC_2.2.5>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002320 <pthread_setaffinity_np@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 5e 7b 00 00    	jmp    *0x7b5e(%rip)        # 9e88 <pthread_setaffinity_np@GLIBC_2.34>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <puts@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 56 7b 00 00    	jmp    *0x7b56(%rip)        # 9e90 <puts@GLIBC_2.2.5>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <setsockopt@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 4e 7b 00 00    	jmp    *0x7b4e(%rip)        # 9e98 <setsockopt@GLIBC_2.2.5>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <clock_gettime@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 46 7b 00 00    	jmp    *0x7b46(%rip)        # 9ea0 <clock_gettime@GLIBC_2.17>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <fclose@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 3e 7b 00 00    	jmp    *0x7b3e(%rip)        # 9ea8 <fclose@GLIBC_2.2.5>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <strlen@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 36 7b 00 00    	jmp    *0x7b36(%rip)        # 9eb0 <strlen@GLIBC_2.2.5>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <__stack_chk_fail@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 2e 7b 00 00    	jmp    *0x7b2e(%rip)        # 9eb8 <__stack_chk_fail@GLIBC_2.4>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <io_uring_submit@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 26 7b 00 00    	jmp    *0x7b26(%rip)        # 9ec0 <io_uring_submit@LIBURING_2.0>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <nanosleep@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 1e 7b 00 00    	jmp    *0x7b1e(%rip)        # 9ec8 <nanosleep@GLIBC_2.2.5>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <strrchr@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 16 7b 00 00    	jmp    *0x7b16(%rip)        # 9ed0 <strrchr@GLIBC_2.2.5>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <fputs@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 0e 7b 00 00    	jmp    *0x7b0e(%rip)        # 9ed8 <fputs@GLIBC_2.2.5>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <close@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 06 7b 00 00    	jmp    *0x7b06(%rip)        # 9ee0 <close@GLIBC_2.2.5>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <strtok_r@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 fe 7a 00 00    	jmp    *0x7afe(%rip)        # 9ee8 <strtok_r@GLIBC_2.2.5>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <read@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 f6 7a 00 00    	jmp    *0x7af6(%rip)        # 9ef0 <read@GLIBC_2.2.5>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <calloc@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 ee 7a 00 00    	jmp    *0x7aee(%rip)        # 9ef8 <calloc@GLIBC_2.2.5>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <strcmp@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 e6 7a 00 00    	jmp    *0x7ae6(%rip)        # 9f00 <strcmp@GLIBC_2.2.5>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <__memcpy_chk@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 de 7a 00 00    	jmp    *0x7ade(%rip)        # 9f08 <__memcpy_chk@GLIBC_2.3.4>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <stat@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 d6 7a 00 00    	jmp    *0x7ad6(%rip)        # 9f10 <stat@GLIBC_2.33>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <memcpy@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 ce 7a 00 00    	jmp    *0x7ace(%rip)        # 9f18 <memcpy@GLIBC_2.14>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <io_uring_queue_init@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 c6 7a 00 00    	jmp    *0x7ac6(%rip)        # 9f20 <io_uring_queue_init@LIBURING_2.0>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <eventfd_write@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 be 7a 00 00    	jmp    *0x7abe(%rip)        # 9f28 <eventfd_write@GLIBC_2.7>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <malloc@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 b6 7a 00 00    	jmp    *0x7ab6(%rip)        # 9f30 <malloc@GLIBC_2.2.5>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <listen@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 ae 7a 00 00    	jmp    *0x7aae(%rip)        # 9f38 <listen@GLIBC_2.2.5>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <__strcpy_chk@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 a6 7a 00 00    	jmp    *0x7aa6(%rip)        # 9f40 <__strcpy_chk@GLIBC_2.3.4>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <__io_uring_get_cqe@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 9e 7a 00 00    	jmp    *0x7a9e(%rip)        # 9f48 <__io_uring_get_cqe@LIBURING_2.0>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <__printf_chk@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 96 7a 00 00    	jmp    *0x7a96(%rip)        # 9f50 <__printf_chk@GLIBC_2.3.4>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <bind@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 8e 7a 00 00    	jmp    *0x7a8e(%rip)        # 9f58 <bind@GLIBC_2.2.5>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <pthread_create@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 86 7a 00 00    	jmp    *0x7a86(%rip)        # 9f60 <pthread_create@GLIBC_2.34>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <open@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 7e 7a 00 00    	jmp    *0x7a7e(%rip)        # 9f68 <open@GLIBC_2.2.5>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <fopen@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 76 7a 00 00    	jmp    *0x7a76(%rip)        # 9f70 <fopen@GLIBC_2.2.5>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <perror@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 6e 7a 00 00    	jmp    *0x7a6e(%rip)        # 9f78 <perror@GLIBC_2.2.5>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <exit@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 66 7a 00 00    	jmp    *0x7a66(%rip)        # 9f80 <exit@GLIBC_2.2.5>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <eventfd@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 5e 7a 00 00    	jmp    *0x7a5e(%rip)        # 9f88 <eventfd@GLIBC_2.7>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <fwrite@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 56 7a 00 00    	jmp    *0x7a56(%rip)        # 9f90 <fwrite@GLIBC_2.2.5>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002540 <__fprintf_chk@plt>:
    2540:	f3 0f 1e fa          	endbr64
    2544:	ff 25 4e 7a 00 00    	jmp    *0x7a4e(%rip)        # 9f98 <__fprintf_chk@GLIBC_2.3.4>
    254a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002550 <io_uring_register_eventfd@plt>:
    2550:	f3 0f 1e fa          	endbr64
    2554:	ff 25 46 7a 00 00    	jmp    *0x7a46(%rip)        # 9fa0 <io_uring_register_eventfd@LIBURING_2.0>
    255a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002560 <pthread_join@plt>:
    2560:	f3 0f 1e fa          	endbr64
    2564:	ff 25 3e 7a 00 00    	jmp    *0x7a3e(%rip)        # 9fa8 <pthread_join@GLIBC_2.34>
    256a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002570 <strerror@plt>:
    2570:	f3 0f 1e fa          	endbr64
    2574:	ff 25 36 7a 00 00    	jmp    *0x7a36(%rip)        # 9fb0 <strerror@GLIBC_2.2.5>
    257a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002580 <pthread_mutex_init@plt>:
    2580:	f3 0f 1e fa          	endbr64
    2584:	ff 25 2e 7a 00 00    	jmp    *0x7a2e(%rip)        # 9fb8 <pthread_mutex_init@GLIBC_2.2.5>
    258a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002590 <__ctype_tolower_loc@plt>:
    2590:	f3 0f 1e fa          	endbr64
    2594:	ff 25 26 7a 00 00    	jmp    *0x7a26(%rip)        # 9fc0 <__ctype_tolower_loc@GLIBC_2.3>
    259a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025a0 <__sprintf_chk@plt>:
    25a0:	f3 0f 1e fa          	endbr64
    25a4:	ff 25 1e 7a 00 00    	jmp    *0x7a1e(%rip)        # 9fc8 <__sprintf_chk@GLIBC_2.3.4>
    25aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025b0 <socket@plt>:
    25b0:	f3 0f 1e fa          	endbr64
    25b4:	ff 25 16 7a 00 00    	jmp    *0x7a16(%rip)        # 9fd0 <socket@GLIBC_2.2.5>
    25ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

00000000000025c0 <fatal_error>:
    25c0:	f3 0f 1e fa          	endbr64
    25c4:	50                   	push   %rax
    25c5:	58                   	pop    %rax
    25c6:	50                   	push   %rax
    25c7:	e8 34 ff ff ff       	call   2500 <perror@plt>
    25cc:	bf 01 00 00 00       	mov    $0x1,%edi
    25d1:	e8 3a ff ff ff       	call   2510 <exit@plt>

00000000000025d6 <copy_file_contents.cold>:
    25d6:	48 8d 3d 49 4c 00 00 	lea    0x4c49(%rip),%rdi        # 7226 <_IO_stdin_used+0x226>
    25dd:	e8 de ff ff ff       	call   25c0 <fatal_error>

00000000000025e2 <add_write_request.cold>:
    25e2:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
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
    2616:	48 8d 3d d9 4b 00 00 	lea    0x4bd9(%rip),%rdi        # 71f6 <_IO_stdin_used+0x1f6>
    261d:	e8 9e ff ff ff       	call   25c0 <fatal_error>
    2622:	48 8d 3d 51 4b 00 00 	lea    0x4b51(%rip),%rdi        # 717a <_IO_stdin_used+0x17a>
    2629:	e8 92 ff ff ff       	call   25c0 <fatal_error>
    262e:	48 8d 3d 65 4b 00 00 	lea    0x4b65(%rip),%rdi        # 719a <_IO_stdin_used+0x19a>
    2635:	e8 86 ff ff ff       	call   25c0 <fatal_error>
    263a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2642:	0f 0b                	ud2
    2644:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    264c:	0f 0b                	ud2
    264e:	48 8d 3d 1c 4b 00 00 	lea    0x4b1c(%rip),%rdi        # 7171 <_IO_stdin_used+0x171>
    2655:	e8 66 ff ff ff       	call   25c0 <fatal_error>
    265a:	48 8d 3d 32 4b 00 00 	lea    0x4b32(%rip),%rdi        # 7193 <_IO_stdin_used+0x193>
    2661:	e8 5a ff ff ff       	call   25c0 <fatal_error>
    2666:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000002670 <main>:
    2670:	f3 0f 1e fa          	endbr64
    2674:	41 57                	push   %r15
    2676:	48 8d 3d d3 4f 00 00 	lea    0x4fd3(%rip),%rdi        # 7650 <_IO_stdin_used+0x650>
    267d:	41 56                	push   %r14
    267f:	41 55                	push   %r13
    2681:	41 54                	push   %r12
    2683:	55                   	push   %rbp
    2684:	48 8d 2d f1 4c 00 00 	lea    0x4cf1(%rip),%rbp        # 737c <_IO_stdin_used+0x37c>
    268b:	53                   	push   %rbx
    268c:	48 81 ec b8 00 00 00 	sub    $0xb8,%rsp
    2693:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    269c:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
    26a4:	48 8d 05 f5 17 00 00 	lea    0x17f5(%rip),%rax        # 3ea0 <barriered_reset>
    26ab:	66 48 0f 6e e8       	movq   %rax,%xmm5
    26b0:	0f 16 2d a1 75 00 00 	movhps 0x75a1(%rip),%xmm5        # 9c58 <__do_global_dtors_aux_fini_array_entry+0x8>
    26b7:	0f 29 6c 24 70       	movaps %xmm5,0x70(%rsp)
    26bc:	e8 6f fc ff ff       	call   2330 <puts@plt>
    26c1:	bf 0a 00 00 00       	mov    $0xa,%edi
    26c6:	e8 45 fc ff ff       	call   2310 <putchar@plt>
    26cb:	ba 01 00 00 00       	mov    $0x1,%edx
    26d0:	48 8d 35 9d 4b 00 00 	lea    0x4b9d(%rip),%rsi        # 7274 <_IO_stdin_used+0x274>
    26d7:	31 c0                	xor    %eax,%eax
    26d9:	bf 01 00 00 00       	mov    $0x1,%edi
    26de:	e8 cd fd ff ff       	call   24b0 <__printf_chk@plt>
    26e3:	ba 02 00 00 00       	mov    $0x2,%edx
    26e8:	48 8d 35 95 4b 00 00 	lea    0x4b95(%rip),%rsi        # 7284 <_IO_stdin_used+0x284>
    26ef:	31 c0                	xor    %eax,%eax
    26f1:	bf 01 00 00 00       	mov    $0x1,%edi
    26f6:	e8 b5 fd ff ff       	call   24b0 <__printf_chk@plt>
    26fb:	ba 01 00 00 00       	mov    $0x1,%edx
    2700:	48 8d 35 92 4b 00 00 	lea    0x4b92(%rip),%rsi        # 7299 <_IO_stdin_used+0x299>
    2707:	31 c0                	xor    %eax,%eax
    2709:	bf 01 00 00 00       	mov    $0x1,%edi
    270e:	e8 9d fd ff ff       	call   24b0 <__printf_chk@plt>
    2713:	ba 02 00 00 00       	mov    $0x2,%edx
    2718:	48 8d 35 8a 4b 00 00 	lea    0x4b8a(%rip),%rsi        # 72a9 <_IO_stdin_used+0x2a9>
    271f:	31 c0                	xor    %eax,%eax
    2721:	bf 01 00 00 00       	mov    $0x1,%edi
    2726:	e8 85 fd ff ff       	call   24b0 <__printf_chk@plt>
    272b:	48 8d 3d 8d 4b 00 00 	lea    0x4b8d(%rip),%rdi        # 72bf <_IO_stdin_used+0x2bf>
    2732:	e8 f9 fb ff ff       	call   2330 <puts@plt>
    2737:	ba 02 00 00 00       	mov    $0x2,%edx
    273c:	48 8d 35 98 4b 00 00 	lea    0x4b98(%rip),%rsi        # 72db <_IO_stdin_used+0x2db>
    2743:	31 c0                	xor    %eax,%eax
    2745:	bf 01 00 00 00       	mov    $0x1,%edi
    274a:	e8 61 fd ff ff       	call   24b0 <__printf_chk@plt>
    274f:	ba 06 00 00 00       	mov    $0x6,%edx
    2754:	48 8d 35 9a 4b 00 00 	lea    0x4b9a(%rip),%rsi        # 72f5 <_IO_stdin_used+0x2f5>
    275b:	31 c0                	xor    %eax,%eax
    275d:	bf 01 00 00 00       	mov    $0x1,%edi
    2762:	e8 49 fd ff ff       	call   24b0 <__printf_chk@plt>
    2767:	ba 01 00 00 00       	mov    $0x1,%edx
    276c:	48 8d 35 96 4b 00 00 	lea    0x4b96(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
    2773:	31 c0                	xor    %eax,%eax
    2775:	bf 01 00 00 00       	mov    $0x1,%edi
    277a:	e8 31 fd ff ff       	call   24b0 <__printf_chk@plt>
    277f:	ba 01 00 00 00       	mov    $0x1,%edx
    2784:	48 8d 35 8f 4b 00 00 	lea    0x4b8f(%rip),%rsi        # 731a <_IO_stdin_used+0x31a>
    278b:	31 c0                	xor    %eax,%eax
    278d:	bf 01 00 00 00       	mov    $0x1,%edi
    2792:	e8 19 fd ff ff       	call   24b0 <__printf_chk@plt>
    2797:	ba 02 00 00 00       	mov    $0x2,%edx
    279c:	48 8d 35 8f 4b 00 00 	lea    0x4b8f(%rip),%rsi        # 7332 <_IO_stdin_used+0x332>
    27a3:	31 c0                	xor    %eax,%eax
    27a5:	bf 01 00 00 00       	mov    $0x1,%edi
    27aa:	e8 01 fd ff ff       	call   24b0 <__printf_chk@plt>
    27af:	ba 01 00 00 00       	mov    $0x1,%edx
    27b4:	48 8d 35 fd 4e 00 00 	lea    0x4efd(%rip),%rsi        # 76b8 <_IO_stdin_used+0x6b8>
    27bb:	31 c0                	xor    %eax,%eax
    27bd:	bf 01 00 00 00       	mov    $0x1,%edi
    27c2:	e8 e9 fc ff ff       	call   24b0 <__printf_chk@plt>
    27c7:	ba 01 00 00 00       	mov    $0x1,%edx
    27cc:	48 8d 35 15 4f 00 00 	lea    0x4f15(%rip),%rsi        # 76e8 <_IO_stdin_used+0x6e8>
    27d3:	31 c0                	xor    %eax,%eax
    27d5:	bf 01 00 00 00       	mov    $0x1,%edi
    27da:	e8 d1 fc ff ff       	call   24b0 <__printf_chk@plt>
    27df:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    27e4:	48 8d 35 63 4b 00 00 	lea    0x4b63(%rip),%rsi        # 734e <_IO_stdin_used+0x34e>
    27eb:	31 c0                	xor    %eax,%eax
    27ed:	bf 01 00 00 00       	mov    $0x1,%edi
    27f2:	e8 b9 fc ff ff       	call   24b0 <__printf_chk@plt>
    27f7:	ba 05 00 00 00       	mov    $0x5,%edx
    27fc:	48 8d 35 65 4b 00 00 	lea    0x4b65(%rip),%rsi        # 7368 <_IO_stdin_used+0x368>
    2803:	31 c0                	xor    %eax,%eax
    2805:	bf 01 00 00 00       	mov    $0x1,%edi
    280a:	e8 a1 fc ff ff       	call   24b0 <__printf_chk@plt>
    280f:	48 8d 3d df 48 00 00 	lea    0x48df(%rip),%rdi        # 70f5 <_IO_stdin_used+0xf5>
    2816:	e8 15 fb ff ff       	call   2330 <puts@plt>
    281b:	be 18 00 00 00       	mov    $0x18,%esi
    2820:	bf 01 00 00 00       	mov    $0x1,%edi
    2825:	e8 d6 fb ff ff       	call   2400 <calloc@plt>
    282a:	be e0 00 00 00       	mov    $0xe0,%esi
    282f:	45 31 f6             	xor    %r14d,%r14d
    2832:	45 31 ed             	xor    %r13d,%r13d
    2835:	bf 06 00 00 00       	mov    $0x6,%edi
    283a:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    283f:	e8 bc fb ff ff       	call   2400 <calloc@plt>
    2844:	be 28 00 00 00       	mov    $0x28,%esi
    2849:	bf 01 00 00 00       	mov    $0x1,%edi
    284e:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2853:	e8 a8 fb ff ff       	call   2400 <calloc@plt>
    2858:	be 28 00 00 00       	mov    $0x28,%esi
    285d:	bf 24 00 00 00       	mov    $0x24,%edi
    2862:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
    286a:	e8 91 fb ff ff       	call   2400 <calloc@plt>
    286f:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
    2877:	49 89 c7             	mov    %rax,%r15
    287a:	4d 89 fc             	mov    %r15,%r12
    287d:	31 db                	xor    %ebx,%ebx
    287f:	90                   	nop
    2880:	41 8d 54 1d 00       	lea    0x0(%r13,%rbx,1),%edx
    2885:	41 89 d8             	mov    %ebx,%r8d
    2888:	44 89 f1             	mov    %r14d,%ecx
    288b:	48 89 ee             	mov    %rbp,%rsi
    288e:	bf 01 00 00 00       	mov    $0x1,%edi
    2893:	31 c0                	xor    %eax,%eax
    2895:	83 c3 01             	add    $0x1,%ebx
    2898:	e8 13 fc ff ff       	call   24b0 <__printf_chk@plt>
    289d:	4c 89 e7             	mov    %r12,%rdi
    28a0:	31 f6                	xor    %esi,%esi
    28a2:	49 83 c4 28          	add    $0x28,%r12
    28a6:	e8 d5 fc ff ff       	call   2580 <pthread_mutex_init@plt>
    28ab:	83 fb 06             	cmp    $0x6,%ebx
    28ae:	75 d0                	jne    2880 <main+0x210>
    28b0:	41 83 c5 06          	add    $0x6,%r13d
    28b4:	41 83 c6 01          	add    $0x1,%r14d
    28b8:	49 81 c7 f0 00 00 00 	add    $0xf0,%r15
    28bf:	41 83 fd 24          	cmp    $0x24,%r13d
    28c3:	75 b5                	jne    287a <main+0x20a>
    28c5:	ba 02 00 00 00       	mov    $0x2,%edx
    28ca:	48 8d 35 bb 4a 00 00 	lea    0x4abb(%rip),%rsi        # 738c <_IO_stdin_used+0x38c>
    28d1:	bf 01 00 00 00       	mov    $0x1,%edi
    28d6:	31 c0                	xor    %eax,%eax
    28d8:	e8 d3 fb ff ff       	call   24b0 <__printf_chk@plt>
    28dd:	ba 04 00 00 00       	mov    $0x4,%edx
    28e2:	48 8d 35 b9 4a 00 00 	lea    0x4ab9(%rip),%rsi        # 73a2 <_IO_stdin_used+0x3a2>
    28e9:	31 c0                	xor    %eax,%eax
    28eb:	bf 01 00 00 00       	mov    $0x1,%edi
    28f0:	e8 bb fb ff ff       	call   24b0 <__printf_chk@plt>
    28f5:	be 10 00 00 00       	mov    $0x10,%esi
    28fa:	bf 04 00 00 00       	mov    $0x4,%edi
    28ff:	e8 fc fa ff ff       	call   2400 <calloc@plt>
    2904:	48 89 84 24 80 00 00 00 	mov    %rax,0x80(%rsp)
    290c:	49 89 c7             	mov    %rax,%r15
    290f:	48 8d 58 40          	lea    0x40(%rax),%rbx
    2913:	49 89 c4             	mov    %rax,%r12
    2916:	be 00 01 00 00       	mov    $0x100,%esi
    291b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    2923:	bf 01 00 00 00       	mov    $0x1,%edi
    2928:	49 83 c4 10          	add    $0x10,%r12
    292c:	e8 cf fa ff ff       	call   2400 <calloc@plt>
    2931:	be 20 00 00 00       	mov    $0x20,%esi
    2936:	bf 64 00 00 00       	mov    $0x64,%edi
    293b:	49 89 44 24 f8       	mov    %rax,-0x8(%r12)
    2940:	48 89 c5             	mov    %rax,%rbp
    2943:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    294d:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
    2957:	e8 a4 fa ff ff       	call   2400 <calloc@plt>
    295c:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
    2963:	4c 39 e3             	cmp    %r12,%rbx
    2966:	75 ae                	jne    2916 <main+0x2a6>
    2968:	4c 8b 4c 24 40       	mov    0x40(%rsp),%r9
    296d:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    2975:	48 c7 44 24 58 00 00 00 00 	movq   $0x0,0x58(%rsp)
    297e:	49 8d 81 e0 00 00 00 	lea    0xe0(%r9),%rax
    2985:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
    298d:	4c 89 cb             	mov    %r9,%rbx
    2990:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2995:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
    299d:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    29a2:	44 8b 64 24 08       	mov    0x8(%rsp),%r12d
    29a7:	31 d2                	xor    %edx,%edx
    29a9:	48 8d 35 60 4d 00 00 	lea    0x4d60(%rip),%rsi        # 7710 <_IO_stdin_used+0x710>
    29b0:	bf 01 00 00 00       	mov    $0x1,%edi
    29b5:	44 89 e1             	mov    %r12d,%ecx
    29b8:	89 44 24 10          	mov    %eax,0x10(%rsp)
    29bc:	41 89 c5             	mov    %eax,%r13d
    29bf:	31 c0                	xor    %eax,%eax
    29c1:	e8 ea fa ff ff       	call   24b0 <__printf_chk@plt>
    29c6:	be 08 00 00 00       	mov    $0x8,%esi
    29cb:	bf 02 00 00 00       	mov    $0x2,%edi
    29d0:	e8 2b fa ff ff       	call   2400 <calloc@plt>
    29d5:	be 80 00 00 00       	mov    $0x80,%esi
    29da:	bf 01 00 00 00       	mov    $0x1,%edi
    29df:	49 89 c6             	mov    %rax,%r14
    29e2:	e8 19 fa ff ff       	call   2400 <calloc@plt>
    29e7:	48 89 c5             	mov    %rax,%rbp
    29ea:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    29ef:	45 85 e4             	test   %r12d,%r12d
    29f2:	0f 84 10 0c 00 00    	je     3608 <main+0xf98>
    29f8:	48 8b 7c 24 68       	mov    0x68(%rsp),%rdi
    29fd:	45 31 e4             	xor    %r12d,%r12d
    2a00:	c7 80 e4 00 00 00 01 00 00 00 	movl   $0x1,0xe4(%rax)
    2a0a:	48 89 b8 28 01 00 00 	mov    %rdi,0x128(%rax)
    2a11:	49 8d 46 08          	lea    0x8(%r14),%rax
    2a15:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
    2a1a:	44 8b 43 04          	mov    0x4(%rbx),%r8d
    2a1e:	8b 54 24 08          	mov    0x8(%rsp),%edx
    2a22:	44 89 e1             	mov    %r12d,%ecx
    2a25:	bf 01 00 00 00       	mov    $0x1,%edi
    2a2a:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    2a2f:	48 8d 35 0a 4d 00 00 	lea    0x4d0a(%rip),%rsi        # 7740 <_IO_stdin_used+0x740>
    2a36:	49 89 46 08          	mov    %rax,0x8(%r14)
    2a3a:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    2a3f:	49 89 06             	mov    %rax,(%r14)
    2a42:	31 c0                	xor    %eax,%eax
    2a44:	e8 67 fa ff ff       	call   24b0 <__printf_chk@plt>
    2a49:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
    2a4d:	bf 01 00 00 00       	mov    $0x1,%edi
    2a52:	31 c0                	xor    %eax,%eax
    2a54:	44 89 a3 b8 00 00 00 	mov    %r12d,0xb8(%rbx)
    2a5b:	44 8b 64 24 08       	mov    0x8(%rsp),%r12d
    2a60:	48 8d 35 09 4d 00 00 	lea    0x4d09(%rip),%rsi        # 7770 <_IO_stdin_used+0x770>
    2a67:	44 89 e2             	mov    %r12d,%edx
    2a6a:	e8 41 fa ff ff       	call   24b0 <__printf_chk@plt>
    2a6f:	44 89 e9             	mov    %r13d,%ecx
    2a72:	4c 89 73 18          	mov    %r14,0x18(%rbx)
    2a76:	45 89 e5             	mov    %r12d,%r13d
    2a79:	b8 01 00 00 00       	mov    $0x1,%eax
    2a7e:	44 89 63 08          	mov    %r12d,0x8(%rbx)
    2a82:	41 83 f5 01          	xor    $0x1,%r13d
    2a86:	45 31 f6             	xor    %r14d,%r14d
    2a89:	48 d3 e0             	shl    %cl,%rax
    2a8c:	48 09 45 00          	or     %rax,0x0(%rbp)
    2a90:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    2a95:	be 10 00 00 00       	mov    $0x10,%esi
    2a9a:	48 8b bc 24 98 00 00 00 	mov    0x98(%rsp),%rdi
    2aa2:	c7 03 5f 00 00 00    	movl   $0x5f,(%rbx)
    2aa8:	48 89 43 20          	mov    %rax,0x20(%rbx)
    2aac:	48 8b 05 1d 52 00 00 	mov    0x521d(%rip),%rax        # 7cd0 <_IO_stdin_used+0xcd0>
    2ab3:	48 89 bb c8 00 00 00 	mov    %rdi,0xc8(%rbx)
    2aba:	48 8b bc 24 90 00 00 00 	mov    0x90(%rsp),%rdi
    2ac2:	48 89 83 c0 00 00 00 	mov    %rax,0xc0(%rbx)
    2ac9:	48 8b 05 08 52 00 00 	mov    0x5208(%rip),%rax        # 7cd8 <_IO_stdin_used+0xcd8>
    2ad0:	48 89 bb d0 00 00 00 	mov    %rdi,0xd0(%rbx)
    2ad7:	bf 64 00 00 00       	mov    $0x64,%edi
    2adc:	48 89 ab b0 00 00 00 	mov    %rbp,0xb0(%rbx)
    2ae3:	48 89 43 28          	mov    %rax,0x28(%rbx)
    2ae7:	c7 43 40 03 00 00 00 	movl   $0x3,0x40(%rbx)
    2aee:	e8 0d f9 ff ff       	call   2400 <calloc@plt>
    2af3:	be 10 00 00 00       	mov    $0x10,%esi
    2af8:	bf 64 00 00 00       	mov    $0x64,%edi
    2afd:	48 89 43 68          	mov    %rax,0x68(%rbx)
    2b01:	e8 fa f8 ff ff       	call   2400 <calloc@plt>
    2b06:	be 28 00 00 00       	mov    $0x28,%esi
    2b0b:	bf 64 00 00 00       	mov    $0x64,%edi
    2b10:	66 0f 6f 3d 88 51 00 00 	movdqa 0x5188(%rip),%xmm7        # 7ca0 <_IO_stdin_used+0xca0>
    2b18:	48 89 43 70          	mov    %rax,0x70(%rbx)
    2b1c:	0f 11 bb 80 00 00 00 	movups %xmm7,0x80(%rbx)
    2b23:	e8 d8 f8 ff ff       	call   2400 <calloc@plt>
    2b28:	be 00 02 00 00       	mov    $0x200,%esi
    2b2d:	bf 03 00 00 00       	mov    $0x3,%edi
    2b32:	66 0f 6f 3d 66 51 00 00 	movdqa 0x5166(%rip),%xmm7        # 7ca0 <_IO_stdin_used+0xca0>
    2b3a:	48 89 83 90 00 00 00 	mov    %rax,0x90(%rbx)
    2b41:	0f 11 bb 98 00 00 00 	movups %xmm7,0x98(%rbx)
    2b48:	e8 b3 f8 ff ff       	call   2400 <calloc@plt>
    2b4d:	4c 89 bc 24 88 00 00 00 	mov    %r15,0x88(%rsp)
    2b55:	48 89 43 38          	mov    %rax,0x38(%rbx)
    2b59:	48 89 c2             	mov    %rax,%rdx
    2b5c:	44 89 6c 24 18       	mov    %r13d,0x18(%rsp)
    2b61:	49 89 dd             	mov    %rbx,%r13
    2b64:	49 63 c6             	movslq %r14d,%rax
    2b67:	be 80 01 00 00       	mov    $0x180,%esi
    2b6c:	bf 02 00 00 00       	mov    $0x2,%edi
    2b71:	31 db                	xor    %ebx,%ebx
    2b73:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2b78:	48 c1 e0 09          	shl    $0x9,%rax
    2b7c:	48 8d 2c 02          	lea    (%rdx,%rax,1),%rbp
    2b80:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2b85:	48 8d 05 d4 12 00 00 	lea    0x12d4(%rip),%rax        # 3e60 <do_protected_write>
    2b8c:	48 89 85 20 01 00 00 	mov    %rax,0x120(%rbp)
    2b93:	e8 68 f8 ff ff       	call   2400 <calloc@plt>
    2b98:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
    2b9d:	4c 89 6c 24 48       	mov    %r13,0x48(%rsp)
    2ba2:	48 89 85 70 01 00 00 	mov    %rax,0x170(%rbp)
    2ba9:	49 89 c4             	mov    %rax,%r12
    2bac:	45 89 fd             	mov    %r15d,%r13d
    2baf:	41 89 df             	mov    %ebx,%r15d
    2bb2:	31 c9                	xor    %ecx,%ecx
    2bb4:	44 89 fa             	mov    %r15d,%edx
    2bb7:	48 8d 35 fe 47 00 00 	lea    0x47fe(%rip),%rsi        # 73bc <_IO_stdin_used+0x3bc>
    2bbe:	31 c0                	xor    %eax,%eax
    2bc0:	bf 01 00 00 00       	mov    $0x1,%edi
    2bc5:	49 81 c4 80 01 00 00 	add    $0x180,%r12
    2bcc:	e8 df f8 ff ff       	call   24b0 <__printf_chk@plt>
    2bd1:	be 08 00 00 00       	mov    $0x8,%esi
    2bd6:	bf 01 00 00 00       	mov    $0x1,%edi
    2bdb:	e8 20 f8 ff ff       	call   2400 <calloc@plt>
    2be0:	be 08 00 00 00       	mov    $0x8,%esi
    2be5:	bf 01 00 00 00       	mov    $0x1,%edi
    2bea:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2bef:	e8 0c f8 ff ff       	call   2400 <calloc@plt>
    2bf4:	be 80 03 00 00       	mov    $0x380,%esi
    2bf9:	bf 03 00 00 00       	mov    $0x3,%edi
    2bfe:	48 89 c3             	mov    %rax,%rbx
    2c01:	e8 fa f7 ff ff       	call   2400 <calloc@plt>
    2c06:	8b 7c 24 08          	mov    0x8(%rsp),%edi
    2c0a:	44 89 fa             	mov    %r15d,%edx
    2c0d:	49 c7 84 24 08 ff ff ff 00 00 00 00 	movq   $0x0,-0xf8(%r12)
    2c19:	48 89 c5             	mov    %rax,%rbp
    2c1c:	44 89 b0 20 03 00 00 	mov    %r14d,0x320(%rax)
    2c23:	48 8d 35 66 4b 00 00 	lea    0x4b66(%rip),%rsi        # 7790 <_IO_stdin_used+0x790>
    2c2a:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
    2c30:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
    2c3a:	44 89 b8 24 03 00 00 	mov    %r15d,0x324(%rax)
    2c41:	41 8d 45 01          	lea    0x1(%r13),%eax
    2c45:	89 85 a8 06 00 00    	mov    %eax,0x6a8(%rbp)
    2c4b:	48 8d 85 80 03 00 00 	lea    0x380(%rbp),%rax
    2c52:	49 89 84 24 00 ff ff ff 	mov    %rax,-0x100(%r12)
    2c5a:	8b 44 24 18          	mov    0x18(%rsp),%eax
    2c5e:	44 89 ad 28 03 00 00 	mov    %r13d,0x328(%rbp)
    2c65:	41 83 c5 02          	add    $0x2,%r13d
    2c69:	41 89 84 24 34 ff ff ff 	mov    %eax,-0xcc(%r12)
    2c71:	89 c1                	mov    %eax,%ecx
    2c73:	31 c0                	xor    %eax,%eax
    2c75:	89 bd 9c 06 00 00    	mov    %edi,0x69c(%rbp)
    2c7b:	bf 01 00 00 00       	mov    $0x1,%edi
    2c80:	49 89 ac 24 80 fe ff ff 	mov    %rbp,-0x180(%r12)
    2c88:	49 c7 84 24 10 ff ff ff 00 00 00 00 	movq   $0x0,-0xf0(%r12)
    2c94:	41 c7 84 24 30 ff ff ff 01 00 00 00 	movl   $0x1,-0xd0(%r12)
    2ca0:	c7 85 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%rbp)
    2caa:	44 89 b5 a0 06 00 00 	mov    %r14d,0x6a0(%rbp)
    2cb1:	44 89 bd a4 06 00 00 	mov    %r15d,0x6a4(%rbp)
    2cb8:	c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rbp)
    2cc2:	c7 85 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%rbp)
    2ccc:	e8 df f7 ff ff       	call   24b0 <__printf_chk@plt>
    2cd1:	66 0f 6f 15 d7 4f 00 00 	movdqa 0x4fd7(%rip),%xmm2        # 7cb0 <_IO_stdin_used+0xcb0>
    2cd9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2cde:	48 89 9d 80 03 00 00 	mov    %rbx,0x380(%rbp)
    2ce5:	4c 89 55 00          	mov    %r10,0x0(%rbp)
    2ce9:	0f 29 95 80 00 00 00 	movaps %xmm2,0x80(%rbp)
    2cf0:	0f 29 95 00 04 00 00 	movaps %xmm2,0x400(%rbp)
    2cf7:	45 85 ff             	test   %r15d,%r15d
    2cfa:	75 0b                	jne    2d07 <main+0x697>
    2cfc:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    2d02:	e9 ab fe ff ff       	jmp    2bb2 <main+0x542>
    2d07:	be 01 00 00 00       	mov    $0x1,%esi
    2d0c:	bf 00 01 00 00       	mov    $0x100,%edi
    2d11:	4c 8b 6c 24 48       	mov    0x48(%rsp),%r13
    2d16:	44 89 fb             	mov    %r15d,%ebx
    2d19:	83 44 24 28 04       	addl   $0x4,0x28(%rsp)
    2d1e:	e8 dd f6 ff ff       	call   2400 <calloc@plt>
    2d23:	bf 20 00 00 00       	mov    $0x20,%edi
    2d28:	48 89 c5             	mov    %rax,%rbp
    2d2b:	e8 40 f7 ff ff       	call   2470 <malloc@plt>
    2d30:	48 83 ec 08          	sub    $0x8,%rsp
    2d34:	48 89 ef             	mov    %rbp,%rdi
    2d37:	45 89 f1             	mov    %r14d,%r9d
    2d3a:	6a 00                	push   $0x0
    2d3c:	44 8b 44 24 18       	mov    0x18(%rsp),%r8d
    2d41:	49 89 c4             	mov    %rax,%r12
    2d44:	ba 00 01 00 00       	mov    $0x100,%edx
    2d49:	48 8d 0d 68 4a 00 00 	lea    0x4a68(%rip),%rcx        # 77b8 <_IO_stdin_used+0x7b8>
    2d50:	be 01 00 00 00       	mov    $0x1,%esi
    2d55:	31 c0                	xor    %eax,%eax
    2d57:	e8 44 f8 ff ff       	call   25a0 <__sprintf_chk@plt>
    2d5c:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    2d61:	49 8b 55 38          	mov    0x38(%r13),%rdx
    2d65:	49 89 2c 24          	mov    %rbp,(%r12)
    2d69:	48 8b 6c 24 40       	mov    0x40(%rsp),%rbp
    2d6e:	be 20 00 00 00       	mov    $0x20,%esi
    2d73:	bf 63 00 00 00       	mov    $0x63,%edi
    2d78:	41 c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%r12)
    2d81:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    2d86:	49 63 45 08          	movslq 0x8(%r13),%rax
    2d8a:	48 01 d5             	add    %rdx,%rbp
    2d8d:	48 89 54 24 20       	mov    %rdx,0x20(%rsp)
    2d92:	49 89 44 24 08       	mov    %rax,0x8(%r12)
    2d97:	8b 44 24 30          	mov    0x30(%rsp),%eax
    2d9b:	c7 85 94 01 00 00 00 00 00 00 	movl   $0x0,0x194(%rbp)
    2da5:	89 85 98 01 00 00    	mov    %eax,0x198(%rbp)
    2dab:	83 c0 01             	add    $0x1,%eax
    2dae:	89 44 24 30          	mov    %eax,0x30(%rsp)
    2db2:	41 8d 46 01          	lea    0x1(%r14),%eax
    2db6:	83 e0 01             	and    $0x1,%eax
    2db9:	c7 45 00 41 00 00 00 	movl   $0x41,0x0(%rbp)
    2dc0:	89 85 90 01 00 00    	mov    %eax,0x190(%rbp)
    2dc6:	4c 89 a5 88 01 00 00 	mov    %r12,0x188(%rbp)
    2dcd:	c7 85 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rbp)
    2dd7:	48 c7 85 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbp)
    2de2:	e8 19 f6 ff ff       	call   2400 <calloc@plt>
    2de7:	48 c7 85 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbp)
    2df2:	48 89 85 50 01 00 00 	mov    %rax,0x150(%rbp)
    2df9:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    2dfe:	48 8b 00             	mov    (%rax),%rax
    2e01:	8b 48 04             	mov    0x4(%rax),%ecx
    2e04:	4c 39 e8             	cmp    %r13,%rax
    2e07:	48 89 85 28 01 00 00 	mov    %rax,0x128(%rbp)
    2e0e:	89 8d 30 01 00 00    	mov    %ecx,0x130(%rbp)
    2e14:	5a                   	pop    %rdx
    2e15:	59                   	pop    %rcx
    2e16:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    2e1b:	0f 85 31 0f 00 00    	jne    3d52 <main+0x16e2>
    2e21:	66 0f 6f 25 97 4e 00 00 	movdqa 0x4e97(%rip),%xmm4        # 7cc0 <_IO_stdin_used+0xcc0>
    2e29:	44 89 75 04          	mov    %r14d,0x4(%rbp)
    2e2d:	48 8b 05 ac 4e 00 00 	mov    0x4eac(%rip),%rax        # 7ce0 <_IO_stdin_used+0xce0>
    2e34:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
    2e3e:	c7 85 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rbp)
    2e48:	48 89 85 44 01 00 00 	mov    %rax,0x144(%rbp)
    2e4f:	0f 11 a5 34 01 00 00 	movups %xmm4,0x134(%rbp)
    2e56:	41 83 fe 01          	cmp    $0x1,%r14d
    2e5a:	0f 84 ee 00 00 00    	je     2f4e <main+0x8de>
    2e60:	45 85 f6             	test   %r14d,%r14d
    2e63:	0f 84 cf 00 00 00    	je     2f38 <main+0x8c8>
    2e69:	44 89 f8             	mov    %r15d,%eax
    2e6c:	4c 89 eb             	mov    %r13,%rbx
    2e6f:	49 89 ec             	mov    %rbp,%r12
    2e72:	bf 01 00 00 00       	mov    $0x1,%edi
    2e77:	41 89 c5             	mov    %eax,%r13d
    2e7a:	be 08 00 00 00       	mov    $0x8,%esi
    2e7f:	48 8d 05 0a 34 00 00 	lea    0x340a(%rip),%rax        # 6290 <barriered_work>
    2e86:	48 89 d5             	mov    %rdx,%rbp
    2e89:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
    2e91:	4c 8b bc 24 88 00 00 00 	mov    0x88(%rsp),%r15
    2e99:	48 81 c3 e0 00 00 00 	add    $0xe0,%rbx
    2ea0:	c7 43 dc 01 00 00 00 	movl   $0x1,-0x24(%rbx)
    2ea7:	e8 54 f5 ff ff       	call   2400 <calloc@plt>
    2eac:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
    2eb1:	66 0f 6f 74 24 70    	movdqa 0x70(%rsp),%xmm6
    2eb7:	48 89 83 70 ff ff ff 	mov    %rax,-0x90(%rbx)
    2ebe:	49 8d 0c ff          	lea    (%r15,%rdi,8),%rcx
    2ec2:	48 83 c7 02          	add    $0x2,%rdi
    2ec6:	48 89 08             	mov    %rcx,(%rax)
    2ec9:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    2ece:	48 89 7c 24 58       	mov    %rdi,0x58(%rsp)
    2ed3:	48 8b 00             	mov    (%rax),%rax
    2ed6:	0f 11 b5 18 05 00 00 	movups %xmm6,0x518(%rbp)
    2edd:	c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rbp)
    2ee7:	48 89 85 28 05 00 00 	mov    %rax,0x528(%rbp)
    2eee:	c7 85 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rbp)
    2ef8:	c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rbp)
    2f02:	8b 83 24 ff ff ff    	mov    -0xdc(%rbx),%eax
    2f08:	c7 85 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rbp)
    2f12:	89 85 30 05 00 00    	mov    %eax,0x530(%rbp)
    2f18:	48 8b 05 c1 4d 00 00 	mov    0x4dc1(%rip),%rax        # 7ce0 <_IO_stdin_used+0xce0>
    2f1f:	48 89 85 44 05 00 00 	mov    %rax,0x544(%rbp)
    2f26:	8b 44 24 08          	mov    0x8(%rsp),%eax
    2f2a:	85 c0                	test   %eax,%eax
    2f2c:	75 2e                	jne    2f5c <main+0x8ec>
    2f2e:	44 89 6c 24 08       	mov    %r13d,0x8(%rsp)
    2f33:	e9 65 fa ff ff       	jmp    299d <main+0x32d>
    2f38:	48 8d 05 21 39 00 00 	lea    0x3921(%rip),%rax        # 6860 <barriered_work_ingest_andwork>
    2f3f:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
    2f46:	41 89 de             	mov    %ebx,%r14d
    2f49:	e9 16 fc ff ff       	jmp    2b64 <main+0x4f4>
    2f4e:	48 8d 05 3b 33 00 00 	lea    0x333b(%rip),%rax        # 6290 <barriered_work>
    2f55:	bb 02 00 00 00       	mov    $0x2,%ebx
    2f5a:	eb e3                	jmp    2f3f <main+0x8cf>
    2f5c:	bf 00 04 00 00       	mov    $0x400,%edi
    2f61:	be 08 00 00 00       	mov    $0x8,%esi
    2f66:	31 ed                	xor    %ebp,%ebp
    2f68:	e8 93 f4 ff ff       	call   2400 <calloc@plt>
    2f6d:	49 89 c6             	mov    %rax,%r14
    2f70:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    2f75:	48 8d 58 38          	lea    0x38(%rax),%rbx
    2f79:	48 05 f8 01 00 00    	add    $0x1f8,%rax
    2f7f:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    2f84:	48 89 df             	mov    %rbx,%rdi
    2f87:	44 8b 47 08          	mov    0x8(%rdi),%r8d
    2f8b:	45 85 c0             	test   %r8d,%r8d
    2f8e:	7e 56                	jle    2fe6 <main+0x976>
    2f90:	48 8b 17             	mov    (%rdi),%rdx
    2f93:	49 63 f0             	movslq %r8d,%rsi
    2f96:	48 63 c5             	movslq %ebp,%rax
    2f99:	48 c1 e6 09          	shl    $0x9,%rsi
    2f9d:	49 8d 0c c6          	lea    (%r14,%rax,8),%rcx
    2fa1:	48 01 d6             	add    %rdx,%rsi
    2fa4:	0f 1f 40 00          	nopl   0x0(%rax)
    2fa8:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
    2faf:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    2fb6:	48 83 c1 20          	add    $0x20,%rcx
    2fba:	f3 0f 7e 80 80 01 00 00 	movq   0x180(%rax),%xmm0
    2fc2:	f3 0f 7e 08          	movq   (%rax),%xmm1
    2fc6:	0f 16 80 00 02 00 00 	movhps 0x200(%rax),%xmm0
    2fcd:	0f 16 88 80 00 00 00 	movhps 0x80(%rax),%xmm1
    2fd4:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    2fd8:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
    2fdc:	48 39 d6             	cmp    %rdx,%rsi
    2fdf:	75 c7                	jne    2fa8 <main+0x938>
    2fe1:	42 8d 6c 85 00       	lea    0x0(%rbp,%r8,4),%ebp
    2fe6:	48 81 c7 e0 00 00 00 	add    $0xe0,%rdi
    2fed:	48 39 7c 24 20       	cmp    %rdi,0x20(%rsp)
    2ff2:	75 93                	jne    2f87 <main+0x917>
    2ff4:	48 8d 3d d1 43 00 00 	lea    0x43d1(%rip),%rdi        # 73cc <_IO_stdin_used+0x3cc>
    2ffb:	e8 30 f3 ff ff       	call   2330 <puts@plt>
    3000:	48 8d 35 da 43 00 00 	lea    0x43da(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    3007:	48 8d 3d d5 43 00 00 	lea    0x43d5(%rip),%rdi        # 73e3 <_IO_stdin_used+0x3e3>
    300e:	e8 dd f4 ff ff       	call   24f0 <fopen@plt>
    3013:	49 89 c7             	mov    %rax,%r15
    3016:	85 ed                	test   %ebp,%ebp
    3018:	7e 7c                	jle    3096 <main+0xa26>
    301a:	48 63 ed             	movslq %ebp,%rbp
    301d:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    3022:	4c 8d 2d e5 43 00 00 	lea    0x43e5(%rip),%r13        # 740e <_IO_stdin_used+0x40e>
    3029:	4c 8d 25 ea 43 00 00 	lea    0x43ea(%rip),%r12        # 741a <_IO_stdin_used+0x41a>
    3030:	49 8d 04 ee          	lea    (%r14,%rbp,8),%rax
    3034:	48 89 c3             	mov    %rax,%rbx
    3037:	be 01 00 00 00       	mov    $0x1,%esi
    303c:	bf fa 00 00 00       	mov    $0xfa,%edi
    3041:	49 83 c6 08          	add    $0x8,%r14
    3045:	e8 b6 f3 ff ff       	call   2400 <calloc@plt>
    304a:	4c 89 e9             	mov    %r13,%rcx
    304d:	ba fa 00 00 00       	mov    $0xfa,%edx
    3052:	be 01 00 00 00       	mov    $0x1,%esi
    3057:	48 89 c5             	mov    %rax,%rbp
    305a:	49 8b 46 f8          	mov    -0x8(%r14),%rax
    305e:	48 89 ef             	mov    %rbp,%rdi
    3061:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3068:	31 c0                	xor    %eax,%eax
    306a:	e8 31 f5 ff ff       	call   25a0 <__sprintf_chk@plt>
    306f:	48 89 ea             	mov    %rbp,%rdx
    3072:	4c 89 e6             	mov    %r12,%rsi
    3075:	bf 01 00 00 00       	mov    $0x1,%edi
    307a:	31 c0                	xor    %eax,%eax
    307c:	e8 2f f4 ff ff       	call   24b0 <__printf_chk@plt>
    3081:	4c 89 fe             	mov    %r15,%rsi
    3084:	48 89 ef             	mov    %rbp,%rdi
    3087:	e8 34 f3 ff ff       	call   23c0 <fputs@plt>
    308c:	4c 39 f3             	cmp    %r14,%rbx
    308f:	75 a6                	jne    3037 <main+0x9c7>
    3091:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    3096:	4c 89 ff             	mov    %r15,%rdi
    3099:	4c 8d 35 8f 43 00 00 	lea    0x438f(%rip),%r14        # 742f <_IO_stdin_used+0x42f>
    30a0:	4c 8d 2d 93 43 00 00 	lea    0x4393(%rip),%r13        # 743a <_IO_stdin_used+0x43a>
    30a7:	49 bf 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%r15
    30b1:	e8 aa f2 ff ff       	call   2360 <fclose@plt>
    30b6:	48 8d 3d 2f 43 00 00 	lea    0x432f(%rip),%rdi        # 73ec <_IO_stdin_used+0x3ec>
    30bd:	e8 6e f2 ff ff       	call   2330 <puts@plt>
    30c2:	31 d2                	xor    %edx,%edx
    30c4:	48 8d 35 39 43 00 00 	lea    0x4339(%rip),%rsi        # 7404 <_IO_stdin_used+0x404>
    30cb:	31 c0                	xor    %eax,%eax
    30cd:	bf 01 00 00 00       	mov    $0x1,%edi
    30d2:	e8 d9 f3 ff ff       	call   24b0 <__printf_chk@plt>
    30d7:	c7 44 24 48 00 00 00 00 	movl   $0x0,0x48(%rsp)
    30df:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    30e4:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    30e9:	8b 54 24 48          	mov    0x48(%rsp),%edx
    30ed:	48 8d 35 29 43 00 00 	lea    0x4329(%rip),%rsi        # 741d <_IO_stdin_used+0x41d>
    30f4:	bf 01 00 00 00       	mov    $0x1,%edi
    30f9:	31 c0                	xor    %eax,%eax
    30fb:	89 d1                	mov    %edx,%ecx
    30fd:	e8 ae f3 ff ff       	call   24b0 <__printf_chk@plt>
    3102:	31 c9                	xor    %ecx,%ecx
    3104:	89 ca                	mov    %ecx,%edx
    3106:	4c 89 f6             	mov    %r14,%rsi
    3109:	bf 01 00 00 00       	mov    $0x1,%edi
    310e:	31 c0                	xor    %eax,%eax
    3110:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    3115:	31 ed                	xor    %ebp,%ebp
    3117:	e8 94 f3 ff ff       	call   24b0 <__printf_chk@plt>
    311c:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    3121:	48 c1 e3 09          	shl    $0x9,%rbx
    3125:	be 01 00 00 00       	mov    $0x1,%esi
    312a:	bf 64 00 00 00       	mov    $0x64,%edi
    312f:	41 89 ec             	mov    %ebp,%r12d
    3132:	e8 c9 f2 ff ff       	call   2400 <calloc@plt>
    3137:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    313c:	48 89 c1             	mov    %rax,%rcx
    313f:	48 89 e8             	mov    %rbp,%rax
    3142:	4c 8b 07             	mov    (%rdi),%r8
    3145:	48 f7 d8             	neg    %rax
    3148:	25 80 01 00 00       	and    $0x180,%eax
    314d:	49 8b b4 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rsi
    3155:	48 01 c6             	add    %rax,%rsi
    3158:	8b be b0 00 00 00    	mov    0xb0(%rsi),%edi
    315e:	83 ff 02             	cmp    $0x2,%edi
    3161:	74 60                	je     31c3 <main+0xb53>
    3163:	83 ff 01             	cmp    $0x1,%edi
    3166:	74 6b                	je     31d3 <main+0xb63>
    3168:	44 8b 86 b4 00 00 00 	mov    0xb4(%rsi),%r8d
    316f:	31 c0                	xor    %eax,%eax
    3171:	44 89 e2             	mov    %r12d,%edx
    3174:	4c 89 ee             	mov    %r13,%rsi
    3177:	bf 01 00 00 00       	mov    $0x1,%edi
    317c:	e8 2f f3 ff ff       	call   24b0 <__printf_chk@plt>
    3181:	48 85 ed             	test   %rbp,%rbp
    3184:	75 07                	jne    318d <main+0xb1d>
    3186:	bd 01 00 00 00       	mov    $0x1,%ebp
    318b:	eb 98                	jmp    3125 <main+0xab5>
    318d:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3192:	48 83 c1 01          	add    $0x1,%rcx
    3196:	48 83 f9 03          	cmp    $0x3,%rcx
    319a:	0f 85 64 ff ff ff    	jne    3104 <main+0xa94>
    31a0:	8b 44 24 48          	mov    0x48(%rsp),%eax
    31a4:	48 89 6c 24 38       	mov    %rbp,0x38(%rsp)
    31a9:	48 81 44 24 10 e0 00 00 00 	addq   $0xe0,0x10(%rsp)
    31b2:	85 c0                	test   %eax,%eax
    31b4:	75 3a                	jne    31f0 <main+0xb80>
    31b6:	8b 44 24 08          	mov    0x8(%rsp),%eax
    31ba:	89 44 24 48          	mov    %eax,0x48(%rsp)
    31be:	e9 26 ff ff ff       	jmp    30e9 <main+0xa79>
    31c3:	4c 89 39             	mov    %r15,(%rcx)
    31c6:	49 03 84 18 70 01 00 00 	add    0x170(%r8,%rbx,1),%rax
    31ce:	48 89 c6             	mov    %rax,%rsi
    31d1:	eb 95                	jmp    3168 <main+0xaf8>
    31d3:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    31d9:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    31e0:	49 03 84 18 70 01 00 00 	add    0x170(%r8,%rbx,1),%rax
    31e8:	48 89 c6             	mov    %rax,%rsi
    31eb:	e9 78 ff ff ff       	jmp    3168 <main+0xaf8>
    31f0:	ba 03 00 00 00       	mov    $0x3,%edx
    31f5:	48 8d 35 59 42 00 00 	lea    0x4259(%rip),%rsi        # 7455 <_IO_stdin_used+0x455>
    31fc:	bf 01 00 00 00       	mov    $0x1,%edi
    3201:	31 c0                	xor    %eax,%eax
    3203:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    3208:	e8 a3 f2 ff ff       	call   24b0 <__printf_chk@plt>
    320d:	be 08 00 00 00       	mov    $0x8,%esi
    3212:	bf 02 00 00 00       	mov    $0x2,%edi
    3217:	e8 e4 f1 ff ff       	call   2400 <calloc@plt>
    321c:	4c 8b 7c 24 40       	mov    0x40(%rsp),%r15
    3221:	be 38 00 00 00       	mov    $0x38,%esi
    3226:	bf 06 00 00 00       	mov    $0x6,%edi
    322b:	4d 8d a7 a0 02 00 00 	lea    0x2a0(%r15),%r12
    3232:	4c 89 78 08          	mov    %r15,0x8(%rax)
    3236:	49 89 87 b8 02 00 00 	mov    %rax,0x2b8(%r15)
    323d:	4c 89 20             	mov    %r12,(%rax)
    3240:	49 8b 47 38          	mov    0x38(%r15),%rax
    3244:	41 c7 87 c8 02 00 00 02 00 00 00 	movl   $0x2,0x2c8(%r15)
    324f:	41 c7 87 a4 02 00 00 00 00 00 00 	movl   $0x0,0x2a4(%r15)
    325a:	41 c7 87 e0 02 00 00 03 00 00 00 	movl   $0x3,0x2e0(%r15)
    3265:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    326f:	49 8b 87 18 01 00 00 	mov    0x118(%r15),%rax
    3276:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3280:	e8 7b f1 ff ff       	call   2400 <calloc@plt>
    3285:	be 38 00 00 00       	mov    $0x38,%esi
    328a:	bf 06 00 00 00       	mov    $0x6,%edi
    328f:	49 89 c5             	mov    %rax,%r13
    3292:	e8 69 f1 ff ff       	call   2400 <calloc@plt>
    3297:	be 38 00 00 00       	mov    $0x38,%esi
    329c:	bf 06 00 00 00       	mov    $0x6,%edi
    32a1:	49 89 c6             	mov    %rax,%r14
    32a4:	e8 57 f1 ff ff       	call   2400 <calloc@plt>
    32a9:	be 38 00 00 00       	mov    $0x38,%esi
    32ae:	bf 06 00 00 00       	mov    $0x6,%edi
    32b3:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    32b8:	e8 43 f1 ff ff       	call   2400 <calloc@plt>
    32bd:	be 08 00 00 00       	mov    $0x8,%esi
    32c2:	bf 06 00 00 00       	mov    $0x6,%edi
    32c7:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    32cc:	e8 2f f1 ff ff       	call   2400 <calloc@plt>
    32d1:	be 08 00 00 00       	mov    $0x8,%esi
    32d6:	bf 06 00 00 00       	mov    $0x6,%edi
    32db:	41 c7 87 cc 01 00 00 00 00 00 00 	movl   $0x0,0x1cc(%r15)
    32e6:	48 89 c5             	mov    %rax,%rbp
    32e9:	48 8b 05 f8 49 00 00 	mov    0x49f8(%rip),%rax        # 7ce8 <_IO_stdin_used+0xce8>
    32f0:	49 89 87 00 02 00 00 	mov    %rax,0x200(%r15)
    32f7:	e8 04 f1 ff ff       	call   2400 <calloc@plt>
    32fc:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    3301:	49 8d 8f c0 01 00 00 	lea    0x1c0(%r15),%rcx
    3308:	48 8d 35 55 41 00 00 	lea    0x4155(%rip),%rsi        # 7464 <_IO_stdin_used+0x464>
    330f:	4c 89 38             	mov    %r15,(%rax)
    3312:	48 89 78 08          	mov    %rdi,0x8(%rax)
    3316:	4c 89 ff             	mov    %r15,%rdi
    3319:	4d 8d bf 80 03 00 00 	lea    0x380(%r15),%r15
    3320:	48 8d 97 60 04 00 00 	lea    0x460(%rdi),%rdx
    3327:	48 89 48 10          	mov    %rcx,0x10(%rax)
    332b:	48 89 50 28          	mov    %rdx,0x28(%rax)
    332f:	48 8b 15 a2 49 00 00 	mov    0x49a2(%rip),%rdx        # 7cd8 <_IO_stdin_used+0xcd8>
    3336:	4c 89 60 18          	mov    %r12,0x18(%rax)
    333a:	4c 89 78 20          	mov    %r15,0x20(%rax)
    333e:	48 89 87 d8 01 00 00 	mov    %rax,0x1d8(%rdi)
    3345:	31 c0                	xor    %eax,%eax
    3347:	48 89 97 e8 01 00 00 	mov    %rdx,0x1e8(%rdi)
    334e:	ba 02 00 00 00       	mov    $0x2,%edx
    3353:	c7 87 f0 01 00 00 02 00 00 00 	movl   $0x2,0x1f0(%rdi)
    335d:	c7 87 c4 01 00 00 00 00 00 00 	movl   $0x0,0x1c4(%rdi)
    3367:	48 89 7c 24 40       	mov    %rdi,0x40(%rsp)
    336c:	bf 01 00 00 00       	mov    $0x1,%edi
    3371:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    3376:	e8 35 f1 ff ff       	call   24b0 <__printf_chk@plt>
    337b:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3380:	49 8d 76 70          	lea    0x70(%r14),%rsi
    3384:	48 8d 7d 10          	lea    0x10(%rbp),%rdi
    3388:	48 8d 15 91 0c 00 00 	lea    0xc91(%rip),%rdx        # 4020 <timer_thread>
    338f:	e8 3c f1 ff ff       	call   24d0 <pthread_create@plt>
    3394:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
    3399:	31 c9                	xor    %ecx,%ecx
    339b:	31 d2                	xor    %edx,%edx
    339d:	4c 8d 0d 44 44 00 00 	lea    0x4444(%rip),%r9        # 77e8 <_IO_stdin_used+0x7e8>
    33a4:	bf 01 00 00 00       	mov    $0x1,%edi
    33a9:	31 c0                	xor    %eax,%eax
    33ab:	41 c7 46 0c 01 00 00 00 	movl   $0x1,0xc(%r14)
    33b3:	4c 89 ce             	mov    %r9,%rsi
    33b6:	41 c7 46 44 01 00 00 00 	movl   $0x1,0x44(%r14)
    33be:	e8 ed f0 ff ff       	call   24b0 <__printf_chk@plt>
    33c3:	4c 89 f1             	mov    %r14,%rcx
    33c6:	4c 89 74 24 40       	mov    %r14,0x40(%rsp)
    33cb:	4c 89 ee             	mov    %r13,%rsi
    33ce:	4c 8d 35 eb 27 00 00 	lea    0x27eb(%rip),%r14        # 5bc0 <barriered_thread>
    33d5:	48 89 ef             	mov    %rbp,%rdi
    33d8:	4c 89 f2             	mov    %r14,%rdx
    33db:	e8 f0 f0 ff ff       	call   24d0 <pthread_create@plt>
    33e0:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    33e5:	be 08 00 00 00       	mov    $0x8,%esi
    33ea:	48 8b 97 b0 00 00 00 	mov    0xb0(%rdi),%rdx
    33f1:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    33f5:	e8 26 ef ff ff       	call   2320 <pthread_setaffinity_np@plt>
    33fa:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    33ff:	31 c9                	xor    %ecx,%ecx
    3401:	31 c0                	xor    %eax,%eax
    3403:	4c 8d 0d de 43 00 00 	lea    0x43de(%rip),%r9        # 77e8 <_IO_stdin_used+0x7e8>
    340a:	ba 01 00 00 00       	mov    $0x1,%edx
    340f:	c7 87 ec 00 00 00 01 00 00 00 	movl   $0x1,0xec(%rdi)
    3419:	4c 89 ce             	mov    %r9,%rsi
    341c:	c7 87 24 01 00 00 01 00 00 00 	movl   $0x1,0x124(%rdi)
    3426:	bf 01 00 00 00       	mov    $0x1,%edi
    342b:	e8 80 f0 ff ff       	call   24b0 <__printf_chk@plt>
    3430:	49 8d 75 38          	lea    0x38(%r13),%rsi
    3434:	4c 89 f2             	mov    %r14,%rdx
    3437:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
    343b:	4c 8b 6c 24 60       	mov    0x60(%rsp),%r13
    3440:	4c 89 e9             	mov    %r13,%rcx
    3443:	e8 88 f0 ff ff       	call   24d0 <pthread_create@plt>
    3448:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
    344d:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
    3451:	be 08 00 00 00       	mov    $0x8,%esi
    3456:	49 8b 96 90 01 00 00 	mov    0x190(%r14),%rdx
    345d:	e8 be ee ff ff       	call   2320 <pthread_setaffinity_np@plt>
    3462:	48 8b 3d 87 48 00 00 	mov    0x4887(%rip),%rdi        # 7cf0 <_IO_stdin_used+0xcf0>
    3469:	be d8 00 00 00       	mov    $0xd8,%esi
    346e:	41 c7 86 ac 02 00 00 02 00 00 00 	movl   $0x2,0x2ac(%r14)
    3479:	49 89 be e0 02 00 00 	mov    %rdi,0x2e0(%r14)
    3480:	bf 01 00 00 00       	mov    $0x1,%edi
    3485:	e8 76 ef ff ff       	call   2400 <calloc@plt>
    348a:	31 ff                	xor    %edi,%edi
    348c:	be 00 08 00 00       	mov    $0x800,%esi
    3491:	49 89 86 f8 02 00 00 	mov    %rax,0x2f8(%r14)
    3498:	e8 83 f0 ff ff       	call   2520 <eventfd@plt>
    349d:	be 08 00 00 00       	mov    $0x8,%esi
    34a2:	bf 02 00 00 00       	mov    $0x2,%edi
    34a7:	41 89 86 00 03 00 00 	mov    %eax,0x300(%r14)
    34ae:	e8 4d ef ff ff       	call   2400 <calloc@plt>
    34b3:	ba 03 00 00 00       	mov    $0x3,%edx
    34b8:	bf 01 00 00 00       	mov    $0x1,%edi
    34bd:	41 c7 86 c8 02 00 00 02 00 00 00 	movl   $0x2,0x2c8(%r14)
    34c8:	4c 89 30             	mov    %r14,(%rax)
    34cb:	48 8d 35 b0 3f 00 00 	lea    0x3fb0(%rip),%rsi        # 7482 <_IO_stdin_used+0x482>
    34d2:	4c 89 68 08          	mov    %r13,0x8(%rax)
    34d6:	49 89 86 b8 02 00 00 	mov    %rax,0x2b8(%r14)
    34dd:	31 c0                	xor    %eax,%eax
    34df:	41 c7 86 a4 02 00 00 03 00 00 00 	movl   $0x3,0x2a4(%r14)
    34ea:	4d 89 fe             	mov    %r15,%r14
    34ed:	41 bf 04 00 00 00    	mov    $0x4,%r15d
    34f3:	e8 b8 ef ff ff       	call   24b0 <__printf_chk@plt>
    34f8:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    34fd:	4c 89 e1             	mov    %r12,%rcx
    3500:	48 8d 7d 18          	lea    0x18(%rbp),%rdi
    3504:	48 8d 15 c5 1e 00 00 	lea    0x1ec5(%rip),%rdx        # 53d0 <io_thread>
    350b:	4c 8d 65 20          	lea    0x20(%rbp),%r12
    350f:	48 81 c6 a8 00 00 00 	add    $0xa8,%rsi
    3516:	e8 b5 ef ff ff       	call   24d0 <pthread_create@plt>
    351b:	ba 04 00 00 00       	mov    $0x4,%edx
    3520:	48 8d 35 72 3f 00 00 	lea    0x3f72(%rip),%rsi        # 7499 <_IO_stdin_used+0x499>
    3527:	31 c0                	xor    %eax,%eax
    3529:	bf 01 00 00 00       	mov    $0x1,%edi
    352e:	e8 7d ef ff ff       	call   24b0 <__printf_chk@plt>
    3533:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    3538:	49 81 c5 e0 00 00 00 	add    $0xe0,%r13
    353f:	44 89 fa             	mov    %r15d,%edx
    3542:	48 8d 35 66 3f 00 00 	lea    0x3f66(%rip),%rsi        # 74af <_IO_stdin_used+0x4af>
    3549:	bf 01 00 00 00       	mov    $0x1,%edi
    354e:	31 c0                	xor    %eax,%eax
    3550:	e8 5b ef ff ff       	call   24b0 <__printf_chk@plt>
    3555:	be 08 00 00 00       	mov    $0x8,%esi
    355a:	bf 01 00 00 00       	mov    $0x1,%edi
    355f:	48 8b 05 8a 47 00 00 	mov    0x478a(%rip),%rax        # 7cf0 <_IO_stdin_used+0xcf0>
    3566:	41 c7 46 0c 03 00 00 00 	movl   $0x3,0xc(%r14)
    356e:	49 89 46 40          	mov    %rax,0x40(%r14)
    3572:	e8 89 ee ff ff       	call   2400 <calloc@plt>
    3577:	48 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%rdi
    357f:	be 08 00 00 00       	mov    $0x8,%esi
    3584:	41 c7 86 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r14)
    358f:	49 89 46 50          	mov    %rax,0x50(%r14)
    3593:	48 89 38             	mov    %rdi,(%rax)
    3596:	bf 02 00 00 00       	mov    $0x2,%edi
    359b:	e8 60 ee ff ff       	call   2400 <calloc@plt>
    35a0:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    35a5:	4c 89 f1             	mov    %r14,%rcx
    35a8:	4c 89 e7             	mov    %r12,%rdi
    35ab:	49 89 46 18          	mov    %rax,0x18(%r14)
    35af:	48 8d 15 5a 09 00 00 	lea    0x95a(%rip),%rdx        # 3f10 <external_thread>
    35b6:	49 83 c4 08          	add    $0x8,%r12
    35ba:	49 81 c6 e0 00 00 00 	add    $0xe0,%r14
    35c1:	48 89 30             	mov    %rsi,(%rax)
    35c4:	48 8b 74 24 60       	mov    0x60(%rsp),%rsi
    35c9:	45 89 be 24 ff ff ff 	mov    %r15d,-0xdc(%r14)
    35d0:	48 89 70 08          	mov    %rsi,0x8(%rax)
    35d4:	48 8b 05 fd 46 00 00 	mov    0x46fd(%rip),%rax        # 7cd8 <_IO_stdin_used+0xcd8>
    35db:	4c 89 ee             	mov    %r13,%rsi
    35de:	49 83 c5 38          	add    $0x38,%r13
    35e2:	49 89 86 48 ff ff ff 	mov    %rax,-0xb8(%r14)
    35e9:	e8 e2 ee ff ff       	call   24d0 <pthread_create@plt>
    35ee:	48 83 84 24 80 00 00 00 10 	addq   $0x10,0x80(%rsp)
    35f7:	41 83 ff 04          	cmp    $0x4,%r15d
    35fb:	75 2b                	jne    3628 <main+0xfb8>
    35fd:	41 bf 05 00 00 00    	mov    $0x5,%r15d
    3603:	e9 37 ff ff ff       	jmp    353f <main+0xecf>
    3608:	48 8b 7c 24 68       	mov    0x68(%rsp),%rdi
    360d:	c7 40 04 00 00 00 00 	movl   $0x0,0x4(%rax)
    3614:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    361a:	4c 89 74 24 50       	mov    %r14,0x50(%rsp)
    361f:	48 89 78 48          	mov    %rdi,0x48(%rax)
    3623:	e9 f2 f3 ff ff       	jmp    2a1a <main+0x3aa>
    3628:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    362d:	4c 8d 25 98 3e 00 00 	lea    0x3e98(%rip),%r12        # 74cc <_IO_stdin_used+0x4cc>
    3634:	4c 8d 70 04          	lea    0x4(%rax),%r14
    3638:	4c 8d a8 44 05 00 00 	lea    0x544(%rax),%r13
    363f:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    3643:	41 8b 16             	mov    (%r14),%edx
    3646:	4c 89 e6             	mov    %r12,%rsi
    3649:	bf 01 00 00 00       	mov    $0x1,%edi
    364e:	31 c0                	xor    %eax,%eax
    3650:	49 81 c6 e0 00 00 00 	add    $0xe0,%r14
    3657:	e8 54 ee ff ff       	call   24b0 <__printf_chk@plt>
    365c:	4d 39 f5             	cmp    %r14,%r13
    365f:	75 de                	jne    363f <main+0xfcf>
    3661:	48 8d 3d 77 3e 00 00 	lea    0x3e77(%rip),%rdi        # 74df <_IO_stdin_used+0x4df>
    3668:	45 31 f6             	xor    %r14d,%r14d
    366b:	4c 8d ac 24 a0 00 00 00 	lea    0xa0(%rsp),%r13
    3673:	e8 b8 ec ff ff       	call   2330 <puts@plt>
    3678:	4c 8d 25 7e 3e 00 00 	lea    0x3e7e(%rip),%r12        # 74fd <_IO_stdin_used+0x4fd>
    367f:	4a 8b 7c f5 00       	mov    0x0(%rbp,%r14,8),%rdi
    3684:	4c 89 ee             	mov    %r13,%rsi
    3687:	e8 d4 ee ff ff       	call   2560 <pthread_join@plt>
    368c:	44 89 f2             	mov    %r14d,%edx
    368f:	4c 89 e6             	mov    %r12,%rsi
    3692:	bf 01 00 00 00       	mov    $0x1,%edi
    3697:	31 c0                	xor    %eax,%eax
    3699:	49 83 c6 01          	add    $0x1,%r14
    369d:	e8 0e ee ff ff       	call   24b0 <__printf_chk@plt>
    36a2:	49 83 fe 06          	cmp    $0x6,%r14
    36a6:	75 d7                	jne    367f <main+0x100f>
    36a8:	bf 00 04 00 00       	mov    $0x400,%edi
    36ad:	be 08 00 00 00       	mov    $0x8,%esi
    36b2:	31 ed                	xor    %ebp,%ebp
    36b4:	e8 47 ed ff ff       	call   2400 <calloc@plt>
    36b9:	48 89 df             	mov    %rbx,%rdi
    36bc:	49 89 c6             	mov    %rax,%r14
    36bf:	44 8b 47 08          	mov    0x8(%rdi),%r8d
    36c3:	45 85 c0             	test   %r8d,%r8d
    36c6:	7e 56                	jle    371e <main+0x10ae>
    36c8:	48 8b 17             	mov    (%rdi),%rdx
    36cb:	49 63 f0             	movslq %r8d,%rsi
    36ce:	48 63 c5             	movslq %ebp,%rax
    36d1:	48 c1 e6 09          	shl    $0x9,%rsi
    36d5:	49 8d 0c c6          	lea    (%r14,%rax,8),%rcx
    36d9:	48 01 d6             	add    %rdx,%rsi
    36dc:	0f 1f 40 00          	nopl   0x0(%rax)
    36e0:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
    36e7:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    36ee:	48 83 c1 20          	add    $0x20,%rcx
    36f2:	f3 0f 7e 80 80 01 00 00 	movq   0x180(%rax),%xmm0
    36fa:	f3 0f 7e 08          	movq   (%rax),%xmm1
    36fe:	0f 16 80 00 02 00 00 	movhps 0x200(%rax),%xmm0
    3705:	0f 16 88 80 00 00 00 	movhps 0x80(%rax),%xmm1
    370c:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    3710:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
    3714:	48 39 d6             	cmp    %rdx,%rsi
    3717:	75 c7                	jne    36e0 <main+0x1070>
    3719:	42 8d 6c 85 00       	lea    0x0(%rbp,%r8,4),%ebp
    371e:	48 81 c7 e0 00 00 00 	add    $0xe0,%rdi
    3725:	48 39 7c 24 20       	cmp    %rdi,0x20(%rsp)
    372a:	75 93                	jne    36bf <main+0x104f>
    372c:	48 8d 3d de 3d 00 00 	lea    0x3dde(%rip),%rdi        # 7511 <_IO_stdin_used+0x511>
    3733:	e8 f8 eb ff ff       	call   2330 <puts@plt>
    3738:	48 8d 35 a2 3c 00 00 	lea    0x3ca2(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    373f:	48 8d 3d e3 3d 00 00 	lea    0x3de3(%rip),%rdi        # 7529 <_IO_stdin_used+0x529>
    3746:	e8 a5 ed ff ff       	call   24f0 <fopen@plt>
    374b:	49 89 c7             	mov    %rax,%r15
    374e:	85 ed                	test   %ebp,%ebp
    3750:	7e 7c                	jle    37ce <main+0x115e>
    3752:	48 63 ed             	movslq %ebp,%rbp
    3755:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    375a:	4c 8d 2d ad 3c 00 00 	lea    0x3cad(%rip),%r13        # 740e <_IO_stdin_used+0x40e>
    3761:	4c 8d 25 b2 3c 00 00 	lea    0x3cb2(%rip),%r12        # 741a <_IO_stdin_used+0x41a>
    3768:	49 8d 04 ee          	lea    (%r14,%rbp,8),%rax
    376c:	48 89 c3             	mov    %rax,%rbx
    376f:	be 01 00 00 00       	mov    $0x1,%esi
    3774:	bf fa 00 00 00       	mov    $0xfa,%edi
    3779:	49 83 c6 08          	add    $0x8,%r14
    377d:	e8 7e ec ff ff       	call   2400 <calloc@plt>
    3782:	4c 89 e9             	mov    %r13,%rcx
    3785:	ba fa 00 00 00       	mov    $0xfa,%edx
    378a:	be 01 00 00 00       	mov    $0x1,%esi
    378f:	48 89 c5             	mov    %rax,%rbp
    3792:	49 8b 46 f8          	mov    -0x8(%r14),%rax
    3796:	48 89 ef             	mov    %rbp,%rdi
    3799:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    37a0:	31 c0                	xor    %eax,%eax
    37a2:	e8 f9 ed ff ff       	call   25a0 <__sprintf_chk@plt>
    37a7:	48 89 ea             	mov    %rbp,%rdx
    37aa:	4c 89 e6             	mov    %r12,%rsi
    37ad:	bf 01 00 00 00       	mov    $0x1,%edi
    37b2:	31 c0                	xor    %eax,%eax
    37b4:	e8 f7 ec ff ff       	call   24b0 <__printf_chk@plt>
    37b9:	4c 89 fe             	mov    %r15,%rsi
    37bc:	48 89 ef             	mov    %rbp,%rdi
    37bf:	e8 fc eb ff ff       	call   23c0 <fputs@plt>
    37c4:	49 39 de             	cmp    %rbx,%r14
    37c7:	75 a6                	jne    376f <main+0x10ff>
    37c9:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    37ce:	4c 89 ff             	mov    %r15,%rdi
    37d1:	45 31 ed             	xor    %r13d,%r13d
    37d4:	45 31 e4             	xor    %r12d,%r12d
    37d7:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
    37e1:	e8 7a eb ff ff       	call   2360 <fclose@plt>
    37e6:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    37eb:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
    37f4:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    37fd:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
    3802:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    380b:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
    3814:	bf 0a 00 00 00       	mov    $0xa,%edi
    3819:	45 89 ee             	mov    %r13d,%r14d
    381c:	e8 ef ea ff ff       	call   2310 <putchar@plt>
    3821:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    3826:	48 8d 35 05 3d 00 00 	lea    0x3d05(%rip),%rsi        # 7532 <_IO_stdin_used+0x532>
    382d:	bf 01 00 00 00       	mov    $0x1,%edi
    3832:	41 83 f6 01          	xor    $0x1,%r14d
    3836:	48 8b 10             	mov    (%rax),%rdx
    3839:	31 c0                	xor    %eax,%eax
    383b:	e8 70 ec ff ff       	call   24b0 <__printf_chk@plt>
    3840:	8b 53 08             	mov    0x8(%rbx),%edx
    3843:	85 d2                	test   %edx,%edx
    3845:	0f 8e 00 05 00 00    	jle    3d4b <main+0x16db>
    384b:	48 63 ca             	movslq %edx,%rcx
    384e:	48 8b 03             	mov    (%rbx),%rax
    3851:	31 d2                	xor    %edx,%edx
    3853:	48 c1 e1 09          	shl    $0x9,%rcx
    3857:	48 01 c1             	add    %rax,%rcx
    385a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3860:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    3867:	48 05 00 02 00 00    	add    $0x200,%rax
    386d:	48 39 c8             	cmp    %rcx,%rax
    3870:	75 ee                	jne    3860 <main+0x11f0>
    3872:	4c 89 f0             	mov    %r14,%rax
    3875:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    387a:	48 f7 d8             	neg    %rax
    387d:	25 e0 00 00 00       	and    $0xe0,%eax
    3882:	48 01 f8             	add    %rdi,%rax
    3885:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3889:	85 c9                	test   %ecx,%ecx
    388b:	7e 25                	jle    38b2 <main+0x1242>
    388d:	48 8b 40 38          	mov    0x38(%rax),%rax
    3891:	48 c1 e1 09          	shl    $0x9,%rcx
    3895:	48 01 c1             	add    %rax,%rcx
    3898:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    38a0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    38a7:	48 05 00 02 00 00    	add    $0x200,%rax
    38ad:	48 39 c1             	cmp    %rax,%rcx
    38b0:	75 ee                	jne    38a0 <main+0x1230>
    38b2:	48 8d 35 8e 3c 00 00 	lea    0x3c8e(%rip),%rsi        # 7547 <_IO_stdin_used+0x547>
    38b9:	bf 01 00 00 00       	mov    $0x1,%edi
    38be:	31 c0                	xor    %eax,%eax
    38c0:	e8 eb eb ff ff       	call   24b0 <__printf_chk@plt>
    38c5:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    38ca:	bf 01 00 00 00       	mov    $0x1,%edi
    38cf:	48 8d 35 42 3f 00 00 	lea    0x3f42(%rip),%rsi        # 7818 <_IO_stdin_used+0x818>
    38d6:	48 8b 08             	mov    (%rax),%rcx
    38d9:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    38e3:	48 f7 e9             	imul   %rcx
    38e6:	48 c1 f9 3f          	sar    $0x3f,%rcx
    38ea:	31 c0                	xor    %eax,%eax
    38ec:	48 d1 fa             	sar    %rdx
    38ef:	48 29 ca             	sub    %rcx,%rdx
    38f2:	e8 b9 eb ff ff       	call   24b0 <__printf_chk@plt>
    38f7:	bf 0a 00 00 00       	mov    $0xa,%edi
    38fc:	e8 0f ea ff ff       	call   2310 <putchar@plt>
    3901:	44 8b 73 08          	mov    0x8(%rbx),%r14d
    3905:	45 85 f6             	test   %r14d,%r14d
    3908:	0f 8e 46 01 00 00    	jle    3a54 <main+0x13e4>
    390e:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    3913:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3918:	44 89 6c 24 08       	mov    %r13d,0x8(%rsp)
    391d:	31 d2                	xor    %edx,%edx
    391f:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    3924:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    3929:	49 89 dd             	mov    %rbx,%r13
    392c:	0f 1f 40 00          	nopl   0x0(%rax)
    3930:	49 8b 45 00          	mov    0x0(%r13),%rax
    3934:	49 89 d1             	mov    %rdx,%r9
    3937:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    393c:	89 d3                	mov    %edx,%ebx
    393e:	49 c1 e1 09          	shl    $0x9,%r9
    3942:	45 31 f6             	xor    %r14d,%r14d
    3945:	4c 01 c8             	add    %r9,%rax
    3948:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    394d:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
    3954:	48 03 88 68 01 00 00 	add    0x168(%rax),%rcx
    395b:	48 03 b0 78 01 00 00 	add    0x178(%rax),%rsi
    3962:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    3967:	48 89 4c 24 28       	mov    %rcx,0x28(%rsp)
    396c:	48 89 74 24 30       	mov    %rsi,0x30(%rsp)
    3971:	8b 54 24 08          	mov    0x8(%rsp),%edx
    3975:	45 89 f0             	mov    %r14d,%r8d
    3978:	89 d9                	mov    %ebx,%ecx
    397a:	48 8d 35 d3 3b 00 00 	lea    0x3bd3(%rip),%rsi        # 7554 <_IO_stdin_used+0x554>
    3981:	bf 01 00 00 00       	mov    $0x1,%edi
    3986:	31 c0                	xor    %eax,%eax
    3988:	e8 23 eb ff ff       	call   24b0 <__printf_chk@plt>
    398d:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    3992:	4c 89 f0             	mov    %r14,%rax
    3995:	45 89 f0             	mov    %r14d,%r8d
    3998:	49 8b 55 00          	mov    0x0(%r13),%rdx
    399c:	48 f7 d8             	neg    %rax
    399f:	48 83 ec 08          	sub    $0x8,%rsp
    39a3:	25 80 01 00 00       	and    $0x180,%eax
    39a8:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    39b0:	48 8b 38             	mov    (%rax),%rdi
    39b3:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    39ba:	48 8b 87 10 03 00 00 	mov    0x310(%rdi),%rax
    39c1:	48 8b 96 08 03 00 00 	mov    0x308(%rsi),%rdx
    39c8:	48 8b b6 10 03 00 00 	mov    0x310(%rsi),%rsi
    39cf:	48 8b 8f 08 03 00 00 	mov    0x308(%rdi),%rcx
    39d6:	bf 01 00 00 00       	mov    $0x1,%edi
    39db:	49 01 c4             	add    %rax,%r12
    39de:	48 01 f0             	add    %rsi,%rax
    39e1:	49 01 cf             	add    %rcx,%r15
    39e4:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
    39e8:	49 01 f4             	add    %rsi,%r12
    39eb:	50                   	push   %rax
    39ec:	49 01 d7             	add    %rdx,%r15
    39ef:	8b 54 24 18          	mov    0x18(%rsp),%edx
    39f3:	89 d9                	mov    %ebx,%ecx
    39f5:	48 8d 35 3c 3e 00 00 	lea    0x3e3c(%rip),%rsi        # 7838 <_IO_stdin_used+0x838>
    39fc:	31 c0                	xor    %eax,%eax
    39fe:	e8 ad ea ff ff       	call   24b0 <__printf_chk@plt>
    3a03:	41 5a                	pop    %r10
    3a05:	41 5b                	pop    %r11
    3a07:	4d 85 f6             	test   %r14,%r14
    3a0a:	75 0a                	jne    3a16 <main+0x13a6>
    3a0c:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    3a11:	e9 5b ff ff ff       	jmp    3971 <main+0x1301>
    3a16:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    3a1b:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    3a20:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3a25:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    3a2a:	48 83 c2 01          	add    $0x1,%rdx
    3a2e:	41 39 55 08          	cmp    %edx,0x8(%r13)
    3a32:	0f 8f f8 fe ff ff    	jg     3930 <main+0x12c0>
    3a38:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
    3a3d:	4c 89 eb             	mov    %r13,%rbx
    3a40:	44 8b 6c 24 08       	mov    0x8(%rsp),%r13d
    3a45:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    3a4a:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    3a4f:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    3a54:	45 31 ff             	xor    %r15d,%r15d
    3a57:	48 83 7b 68 00       	cmpq   $0x0,0x68(%rbx)
    3a5c:	4c 8d 35 f5 3d 00 00 	lea    0x3df5(%rip),%r14        # 7858 <_IO_stdin_used+0x858>
    3a63:	7e 55                	jle    3aba <main+0x144a>
    3a65:	0f 1f 00             	nopl   (%rax)
    3a68:	48 8b 43 58          	mov    0x58(%rbx),%rax
    3a6c:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    3a70:	48 83 ec 08          	sub    $0x8,%rsp
    3a74:	bf 01 00 00 00       	mov    $0x1,%edi
    3a79:	49 83 c7 01          	add    $0x1,%r15
    3a7d:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    3a81:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3a85:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    3a89:	48 89 f0             	mov    %rsi,%rax
    3a8c:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3a90:	4c 2b 01             	sub    (%rcx),%r8
    3a93:	48 f7 e5             	mul    %rbp
    3a96:	8b 49 20             	mov    0x20(%rcx),%ecx
    3a99:	56                   	push   %rsi
    3a9a:	31 c0                	xor    %eax,%eax
    3a9c:	4c 89 f6             	mov    %r14,%rsi
    3a9f:	48 c1 ea 12          	shr    $0x12,%rdx
    3aa3:	49 89 d1             	mov    %rdx,%r9
    3aa6:	ba 02 00 00 00       	mov    $0x2,%edx
    3aab:	e8 00 ea ff ff       	call   24b0 <__printf_chk@plt>
    3ab0:	41 58                	pop    %r8
    3ab2:	41 59                	pop    %r9
    3ab4:	4c 39 7b 68          	cmp    %r15,0x68(%rbx)
    3ab8:	7f ae                	jg     3a68 <main+0x13f8>
    3aba:	8b 93 84 00 00 00    	mov    0x84(%rbx),%edx
    3ac0:	85 d2                	test   %edx,%edx
    3ac2:	0f 8e 09 01 00 00    	jle    3bd1 <main+0x1561>
    3ac8:	4c 89 64 24 58       	mov    %r12,0x58(%rsp)
    3acd:	48 8b 7b 18          	mov    0x18(%rbx),%rdi
    3ad1:	45 31 ff             	xor    %r15d,%r15d
    3ad4:	44 89 6c 24 60       	mov    %r13d,0x60(%rsp)
    3ad9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3ae0:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    3ae4:	45 89 fc             	mov    %r15d,%r12d
    3ae7:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    3aef:	8b 30                	mov    (%rax),%esi
    3af1:	85 f6                	test   %esi,%esi
    3af3:	0f 8e c1 00 00 00    	jle    3bba <main+0x154a>
    3af9:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    3afe:	31 d2                	xor    %edx,%edx
    3b00:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3b04:	49 89 f8             	mov    %rdi,%r8
    3b07:	48 89 d7             	mov    %rdx,%rdi
    3b0a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3b10:	49 89 fe             	mov    %rdi,%r14
    3b13:	45 31 ff             	xor    %r15d,%r15d
    3b16:	49 c1 e6 08          	shl    $0x8,%r14
    3b1a:	4a 8d 04 31          	lea    (%rcx,%r14,1),%rax
    3b1e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    3b24:	85 d2                	test   %edx,%edx
    3b26:	7e 78                	jle    3ba0 <main+0x1530>
    3b28:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    3b2d:	0f 1f 00             	nopl   (%rax)
    3b30:	4c 89 f9             	mov    %r15,%rcx
    3b33:	48 83 ec 08          	sub    $0x8,%rsp
    3b37:	bf 01 00 00 00       	mov    $0x1,%edi
    3b3c:	49 83 c7 01          	add    $0x1,%r15
    3b40:	48 c1 e1 05          	shl    $0x5,%rcx
    3b44:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
    3b4b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3b4f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    3b53:	48 89 f0             	mov    %rsi,%rax
    3b56:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3b5a:	4c 2b 01             	sub    (%rcx),%r8
    3b5d:	56                   	push   %rsi
    3b5e:	48 f7 e5             	mul    %rbp
    3b61:	44 89 e1             	mov    %r12d,%ecx
    3b64:	48 8d 35 3d 3d 00 00 	lea    0x3d3d(%rip),%rsi        # 78a8 <_IO_stdin_used+0x8a8>
    3b6b:	31 c0                	xor    %eax,%eax
    3b6d:	48 c1 ea 12          	shr    $0x12,%rdx
    3b71:	49 89 d1             	mov    %rdx,%r9
    3b74:	ba 02 00 00 00       	mov    $0x2,%edx
    3b79:	e8 32 e9 ff ff       	call   24b0 <__printf_chk@plt>
    3b7e:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    3b82:	5e                   	pop    %rsi
    3b83:	5f                   	pop    %rdi
    3b84:	4b 8b 14 28          	mov    (%r8,%r13,1),%rdx
    3b88:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    3b8c:	4a 8d 04 31          	lea    (%rcx,%r14,1),%rax
    3b90:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    3b97:	7f 97                	jg     3b30 <main+0x14c0>
    3b99:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    3b9e:	8b 32                	mov    (%rdx),%esi
    3ba0:	48 83 c7 01          	add    $0x1,%rdi
    3ba4:	39 fe                	cmp    %edi,%esi
    3ba6:	0f 8f 64 ff ff ff    	jg     3b10 <main+0x14a0>
    3bac:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    3bb1:	8b 93 84 00 00 00    	mov    0x84(%rbx),%edx
    3bb7:	4c 89 c7             	mov    %r8,%rdi
    3bba:	49 83 c7 01          	add    $0x1,%r15
    3bbe:	44 39 fa             	cmp    %r15d,%edx
    3bc1:	0f 8f 19 ff ff ff    	jg     3ae0 <main+0x1470>
    3bc7:	4c 8b 64 24 58       	mov    0x58(%rsp),%r12
    3bcc:	44 8b 6c 24 60       	mov    0x60(%rsp),%r13d
    3bd1:	48 83 44 24 50 18    	addq   $0x18,0x50(%rsp)
    3bd7:	48 81 c3 e0 00 00 00 	add    $0xe0,%rbx
    3bde:	45 85 ed             	test   %r13d,%r13d
    3be1:	75 0a                	jne    3bed <main+0x157d>
    3be3:	44 8b 6c 24 48       	mov    0x48(%rsp),%r13d
    3be8:	e9 27 fc ff ff       	jmp    3814 <main+0x11a4>
    3bed:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    3bf2:	48 8d 35 6b 39 00 00 	lea    0x396b(%rip),%rsi        # 7564 <_IO_stdin_used+0x564>
    3bf9:	bf 01 00 00 00       	mov    $0x1,%edi
    3bfe:	31 c0                	xor    %eax,%eax
    3c00:	4c 89 f2             	mov    %r14,%rdx
    3c03:	e8 a8 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c08:	bf 0a 00 00 00       	mov    $0xa,%edi
    3c0d:	e8 fe e6 ff ff       	call   2310 <putchar@plt>
    3c12:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
    3c17:	48 8d 35 e2 3c 00 00 	lea    0x3ce2(%rip),%rsi        # 7900 <_IO_stdin_used+0x900>
    3c1e:	31 c0                	xor    %eax,%eax
    3c20:	bf 01 00 00 00       	mov    $0x1,%edi
    3c25:	48 8b 53 08          	mov    0x8(%rbx),%rdx
    3c29:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    3c33:	e8 78 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c38:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3c3d:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    3c42:	48 8d 35 df 3c 00 00 	lea    0x3cdf(%rip),%rsi        # 7928 <_IO_stdin_used+0x928>
    3c49:	48 f7 eb             	imul   %rbx
    3c4c:	48 c1 ff 3f          	sar    $0x3f,%rdi
    3c50:	31 c0                	xor    %eax,%eax
    3c52:	48 d1 fa             	sar    %rdx
    3c55:	48 29 fa             	sub    %rdi,%rdx
    3c58:	bf 01 00 00 00       	mov    $0x1,%edi
    3c5d:	e8 4e e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c62:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    3c67:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3c6c:	48 8d 35 e5 3c 00 00 	lea    0x3ce5(%rip),%rsi        # 7958 <_IO_stdin_used+0x958>
    3c73:	48 f7 eb             	imul   %rbx
    3c76:	48 c1 ff 3f          	sar    $0x3f,%rdi
    3c7a:	31 c0                	xor    %eax,%eax
    3c7c:	48 d1 fa             	sar    %rdx
    3c7f:	48 29 fa             	sub    %rdi,%rdx
    3c82:	bf 01 00 00 00       	mov    $0x1,%edi
    3c87:	e8 24 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c8c:	4c 89 f0             	mov    %r14,%rax
    3c8f:	bf 01 00 00 00       	mov    $0x1,%edi
    3c94:	48 8d 35 ed 3c 00 00 	lea    0x3ced(%rip),%rsi        # 7988 <_IO_stdin_used+0x988>
    3c9b:	48 f7 eb             	imul   %rbx
    3c9e:	4c 89 f0             	mov    %r14,%rax
    3ca1:	48 c1 f8 3f          	sar    $0x3f,%rax
    3ca5:	48 d1 fa             	sar    %rdx
    3ca8:	48 29 c2             	sub    %rax,%rdx
    3cab:	31 c0                	xor    %eax,%eax
    3cad:	e8 fe e7 ff ff       	call   24b0 <__printf_chk@plt>
    3cb2:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3cb7:	bf 01 00 00 00       	mov    $0x1,%edi
    3cbc:	48 8d 35 b5 38 00 00 	lea    0x38b5(%rip),%rsi        # 7578 <_IO_stdin_used+0x578>
    3cc3:	48 f7 eb             	imul   %rbx
    3cc6:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3ccb:	48 c1 f8 3f          	sar    $0x3f,%rax
    3ccf:	48 d1 fa             	sar    %rdx
    3cd2:	48 29 c2             	sub    %rax,%rdx
    3cd5:	31 c0                	xor    %eax,%eax
    3cd7:	48 89 d5             	mov    %rdx,%rbp
    3cda:	e8 d1 e7 ff ff       	call   24b0 <__printf_chk@plt>
    3cdf:	4c 89 e0             	mov    %r12,%rax
    3ce2:	bf 01 00 00 00       	mov    $0x1,%edi
    3ce7:	48 8d 35 ba 3c 00 00 	lea    0x3cba(%rip),%rsi        # 79a8 <_IO_stdin_used+0x9a8>
    3cee:	48 f7 eb             	imul   %rbx
    3cf1:	4c 89 e0             	mov    %r12,%rax
    3cf4:	48 c1 f8 3f          	sar    $0x3f,%rax
    3cf8:	48 89 d3             	mov    %rdx,%rbx
    3cfb:	48 d1 fb             	sar    %rbx
    3cfe:	48 29 c3             	sub    %rax,%rbx
    3d01:	31 c0                	xor    %eax,%eax
    3d03:	48 89 da             	mov    %rbx,%rdx
    3d06:	48 29 eb             	sub    %rbp,%rbx
    3d09:	e8 a2 e7 ff ff       	call   24b0 <__printf_chk@plt>
    3d0e:	31 c0                	xor    %eax,%eax
    3d10:	48 89 da             	mov    %rbx,%rdx
    3d13:	bf 01 00 00 00       	mov    $0x1,%edi
    3d18:	48 8d 35 75 38 00 00 	lea    0x3875(%rip),%rsi        # 7594 <_IO_stdin_used+0x594>
    3d1f:	e8 8c e7 ff ff       	call   24b0 <__printf_chk@plt>
    3d24:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    3d2c:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3d35:	75 25                	jne    3d5c <main+0x16ec>
    3d37:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    3d3e:	31 c0                	xor    %eax,%eax
    3d40:	5b                   	pop    %rbx
    3d41:	5d                   	pop    %rbp
    3d42:	41 5c                	pop    %r12
    3d44:	41 5d                	pop    %r13
    3d46:	41 5e                	pop    %r14
    3d48:	41 5f                	pop    %r15
    3d4a:	c3                   	ret
    3d4b:	31 d2                	xor    %edx,%edx
    3d4d:	e9 20 fb ff ff       	jmp    3872 <main+0x1202>
    3d52:	bf 01 00 00 00       	mov    $0x1,%edi
    3d57:	e8 b4 e7 ff ff       	call   2510 <exit@plt>
    3d5c:	e8 1f e6 ff ff       	call   2380 <__stack_chk_fail@plt>
    3d61:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3d6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003d70 <_start>:
    3d70:	f3 0f 1e fa          	endbr64
    3d74:	31 ed                	xor    %ebp,%ebp
    3d76:	49 89 d1             	mov    %rdx,%r9
    3d79:	5e                   	pop    %rsi
    3d7a:	48 89 e2             	mov    %rsp,%rdx
    3d7d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3d81:	50                   	push   %rax
    3d82:	54                   	push   %rsp
    3d83:	45 31 c0             	xor    %r8d,%r8d
    3d86:	31 c9                	xor    %ecx,%ecx
    3d88:	48 8d 3d e1 e8 ff ff 	lea    -0x171f(%rip),%rdi        # 2670 <main>
    3d8f:	ff 15 43 62 00 00    	call   *0x6243(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3d95:	f4                   	hlt
    3d96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003da0 <deregister_tm_clones>:
    3da0:	48 8d 3d 79 62 00 00 	lea    0x6279(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3da7:	48 8d 05 72 62 00 00 	lea    0x6272(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    3dae:	48 39 f8             	cmp    %rdi,%rax
    3db1:	74 15                	je     3dc8 <deregister_tm_clones+0x28>
    3db3:	48 8b 05 26 62 00 00 	mov    0x6226(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    3dba:	48 85 c0             	test   %rax,%rax
    3dbd:	74 09                	je     3dc8 <deregister_tm_clones+0x28>
    3dbf:	ff e0                	jmp    *%rax
    3dc1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3dc8:	c3                   	ret
    3dc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003dd0 <register_tm_clones>:
    3dd0:	48 8d 3d 49 62 00 00 	lea    0x6249(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3dd7:	48 8d 35 42 62 00 00 	lea    0x6242(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    3dde:	48 29 fe             	sub    %rdi,%rsi
    3de1:	48 89 f0             	mov    %rsi,%rax
    3de4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3de8:	48 c1 f8 03          	sar    $0x3,%rax
    3dec:	48 01 c6             	add    %rax,%rsi
    3def:	48 d1 fe             	sar    %rsi
    3df2:	74 14                	je     3e08 <register_tm_clones+0x38>
    3df4:	48 8b 05 f5 61 00 00 	mov    0x61f5(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    3dfb:	48 85 c0             	test   %rax,%rax
    3dfe:	74 08                	je     3e08 <register_tm_clones+0x38>
    3e00:	ff e0                	jmp    *%rax
    3e02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3e08:	c3                   	ret
    3e09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003e10 <__do_global_dtors_aux>:
    3e10:	f3 0f 1e fa          	endbr64
    3e14:	80 3d 0d 62 00 00 00 	cmpb   $0x0,0x620d(%rip)        # a028 <completed.0>
    3e1b:	75 2b                	jne    3e48 <__do_global_dtors_aux+0x38>
    3e1d:	55                   	push   %rbp
    3e1e:	48 83 3d d2 61 00 00 00 	cmpq   $0x0,0x61d2(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3e26:	48 89 e5             	mov    %rsp,%rbp
    3e29:	74 0c                	je     3e37 <__do_global_dtors_aux+0x27>
    3e2b:	48 8b 3d d6 61 00 00 	mov    0x61d6(%rip),%rdi        # a008 <__dso_handle>
    3e32:	e8 b9 e4 ff ff       	call   22f0 <__cxa_finalize@plt>
    3e37:	e8 64 ff ff ff       	call   3da0 <deregister_tm_clones>
    3e3c:	c6 05 e5 61 00 00 01 	movb   $0x1,0x61e5(%rip)        # a028 <completed.0>
    3e43:	5d                   	pop    %rbp
    3e44:	c3                   	ret
    3e45:	0f 1f 00             	nopl   (%rax)
    3e48:	c3                   	ret
    3e49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003e50 <frame_dummy>:
    3e50:	f3 0f 1e fa          	endbr64
    3e54:	e9 77 ff ff ff       	jmp    3dd0 <register_tm_clones>
    3e59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003e60 <do_protected_write>:
    3e60:	f3 0f 1e fa          	endbr64
    3e64:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3e6b:	48 8b 40 48          	mov    0x48(%rax),%rax
    3e6f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
    3e77:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3e7b:	48 83 00 01          	addq   $0x1,(%rax)
    3e7f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3e86:	48 85 c9             	test   %rcx,%rcx
    3e89:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3e90:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3e94:	48 89 50 08          	mov    %rdx,0x8(%rax)
    3e98:	31 c0                	xor    %eax,%eax
    3e9a:	c3                   	ret
    3e9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003ea0 <barriered_reset>:
    3ea0:	f3 0f 1e fa          	endbr64
    3ea4:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    3eab:	85 c9                	test   %ecx,%ecx
    3ead:	7e 4f                	jle    3efe <barriered_reset+0x5e>
    3eaf:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3eb6:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    3ebd:	48 c1 e1 09          	shl    $0x9,%rcx
    3ec1:	48 8b 50 18          	mov    0x18(%rax),%rdx
    3ec5:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
    3ec9:	48 8b 70 38          	mov    0x38(%rax),%rsi
    3ecd:	31 c0                	xor    %eax,%eax
    3ecf:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    3ed3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3ed8:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
    3ee0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
    3ee8:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    3ef3:	48 05 00 02 00 00    	add    $0x200,%rax
    3ef9:	48 39 c1             	cmp    %rax,%rcx
    3efc:	75 da                	jne    3ed8 <barriered_reset+0x38>
    3efe:	0f ae f8             	sfence
    3f01:	31 c0                	xor    %eax,%eax
    3f03:	c3                   	ret
    3f04:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3f0f:	90                   	nop

0000000000003f10 <external_thread>:
    3f10:	f3 0f 1e fa          	endbr64
    3f14:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    3f18:	0f 85 fb 00 00 00    	jne    4019 <external_thread+0x109>
    3f1e:	41 57                	push   %r15
    3f20:	49 89 ff             	mov    %rdi,%r15
    3f23:	41 56                	push   %r14
    3f25:	41 55                	push   %r13
    3f27:	4c 8d 2d d6 30 00 00 	lea    0x30d6(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
    3f2e:	41 54                	push   %r12
    3f30:	55                   	push   %rbp
    3f31:	53                   	push   %rbx
    3f32:	48 83 ec 08          	sub    $0x8,%rsp
    3f36:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    3f3c:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    3f40:	85 c9                	test   %ecx,%ecx
    3f42:	7e 6e                	jle    3fb2 <external_thread+0xa2>
    3f44:	45 31 e4             	xor    %r12d,%r12d
    3f47:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3f50:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    3f58:	31 db                	xor    %ebx,%ebx
    3f5a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3f5e:	48 8b 06             	mov    (%rsi),%rax
    3f61:	8b 10                	mov    (%rax),%edx
    3f63:	85 d2                	test   %edx,%edx
    3f65:	7e 2a                	jle    3f91 <external_thread+0x81>
    3f67:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3f6b:	48 89 dd             	mov    %rbx,%rbp
    3f6e:	48 c1 e5 08          	shl    $0x8,%rbp
    3f72:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    3f76:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    3f7d:	45 85 c0             	test   %r8d,%r8d
    3f80:	74 36                	je     3fb8 <external_thread+0xa8>
    3f82:	48 83 c3 01          	add    $0x1,%rbx
    3f86:	39 da                	cmp    %ebx,%edx
    3f88:	7f e1                	jg     3f6b <external_thread+0x5b>
    3f8a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    3f91:	49 83 c4 01          	add    $0x1,%r12
    3f95:	44 39 e1             	cmp    %r12d,%ecx
    3f98:	7f b6                	jg     3f50 <external_thread+0x40>
    3f9a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    3f9f:	74 9f                	je     3f40 <external_thread+0x30>
    3fa1:	48 83 c4 08          	add    $0x8,%rsp
    3fa5:	31 c0                	xor    %eax,%eax
    3fa7:	5b                   	pop    %rbx
    3fa8:	5d                   	pop    %rbp
    3fa9:	41 5c                	pop    %r12
    3fab:	41 5d                	pop    %r13
    3fad:	41 5e                	pop    %r14
    3faf:	41 5f                	pop    %r15
    3fb1:	c3                   	ret
    3fb2:	eb fe                	jmp    3fb2 <external_thread+0xa2>
    3fb4:	0f 1f 40 00          	nopl   0x0(%rax)
    3fb8:	4c 89 28             	mov    %r13,(%rax)
    3fbb:	48 8b 06             	mov    (%rsi),%rax
    3fbe:	48 8b 78 08          	mov    0x8(%rax),%rdi
    3fc2:	48 01 ef             	add    %rbp,%rdi
    3fc5:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    3fcc:	48 c1 e6 05          	shl    $0x5,%rsi
    3fd0:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    3fd7:	bf 04 00 00 00       	mov    $0x4,%edi
    3fdc:	e8 6f e3 ff ff       	call   2350 <clock_gettime@plt>
    3fe1:	49 8b 47 50          	mov    0x50(%r15),%rax
    3fe5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    3fe9:	48 8b 40 08          	mov    0x8(%rax),%rax
    3fed:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
    3ff8:	0f ae f8             	sfence
    3ffb:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    3fff:	48 83 c3 01          	add    $0x1,%rbx
    4003:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    4007:	48 8b 06             	mov    (%rsi),%rax
    400a:	8b 10                	mov    (%rax),%edx
    400c:	39 da                	cmp    %ebx,%edx
    400e:	0f 8f 53 ff ff ff    	jg     3f67 <external_thread+0x57>
    4014:	e9 71 ff ff ff       	jmp    3f8a <external_thread+0x7a>
    4019:	31 c0                	xor    %eax,%eax
    401b:	c3                   	ret
    401c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004020 <timer_thread>:
    4020:	f3 0f 1e fa          	endbr64
    4024:	41 57                	push   %r15
    4026:	48 8d 35 e3 2f 00 00 	lea    0x2fe3(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    402d:	41 56                	push   %r14
    402f:	49 89 fe             	mov    %rdi,%r14
    4032:	41 55                	push   %r13
    4034:	41 54                	push   %r12
    4036:	55                   	push   %rbp
    4037:	53                   	push   %rbx
    4038:	48 83 ec 68          	sub    $0x68,%rsp
    403c:	8b 57 04             	mov    0x4(%rdi),%edx
    403f:	bf 01 00 00 00       	mov    $0x1,%edi
    4044:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    404d:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    4052:	31 c0                	xor    %eax,%eax
    4054:	e8 57 e4 ff ff       	call   24b0 <__printf_chk@plt>
    4059:	66 0f 6f 05 5f 3b 00 00 	movdqa 0x3b5f(%rip),%xmm0        # 7bc0 <_IO_stdin_used+0xbc0>
    4061:	ba 88 13 00 00       	mov    $0x1388,%edx
    4066:	31 c0                	xor    %eax,%eax
    4068:	48 8d 35 b3 2f 00 00 	lea    0x2fb3(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    406f:	bf 01 00 00 00       	mov    $0x1,%edi
    4074:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
    4079:	e8 32 e4 ff ff       	call   24b0 <__printf_chk@plt>
    407e:	41 8b 5e 44          	mov    0x44(%r14),%ebx
    4082:	85 db                	test   %ebx,%ebx
    4084:	0f 84 9c 00 00 00    	je     4126 <timer_thread+0x106>
    408a:	45 31 ff             	xor    %r15d,%r15d
    408d:	31 db                	xor    %ebx,%ebx
    408f:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    4094:	31 ed                	xor    %ebp,%ebp
    4096:	4c 8d 64 24 20       	lea    0x20(%rsp),%r12
    409b:	4c 89 e7             	mov    %r12,%rdi
    409e:	4c 89 ee             	mov    %r13,%rsi
    40a1:	41 83 c7 01          	add    $0x1,%r15d
    40a5:	e8 f6 e2 ff ff       	call   23a0 <nanosleep@plt>
    40aa:	49 63 46 30          	movslq 0x30(%r14),%rax
    40ae:	8d 7b 01             	lea    0x1(%rbx),%edi
    40b1:	85 c0                	test   %eax,%eax
    40b3:	7e 4a                	jle    40ff <timer_thread+0xdf>
    40b5:	49 8b 4e 18          	mov    0x18(%r14),%rcx
    40b9:	4c 63 c3             	movslq %ebx,%r8
    40bc:	49 c1 e0 09          	shl    $0x9,%r8
    40c0:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    40c4:	0f 1f 40 00          	nopl   0x0(%rax)
    40c8:	48 8b 19             	mov    (%rcx),%rbx
    40cb:	89 f8                	mov    %edi,%eax
    40cd:	48 83 c1 08          	add    $0x8,%rcx
    40d1:	99                   	cltd
    40d2:	f7 7b 40             	idivl  0x40(%rbx)
    40d5:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    40d9:	83 ea 01             	sub    $0x1,%edx
    40dc:	48 63 d2             	movslq %edx,%rdx
    40df:	48 c1 e2 09          	shl    $0x9,%rdx
    40e3:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    40ee:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    40fa:	49 39 c9             	cmp    %rcx,%r9
    40fd:	75 c9                	jne    40c8 <timer_thread+0xa8>
    40ff:	0f ae f0             	mfence
    4102:	49 8b 46 18          	mov    0x18(%r14),%rax
    4106:	41 8b 4e 44          	mov    0x44(%r14),%ecx
    410a:	89 fb                	mov    %edi,%ebx
    410c:	48 8b 00             	mov    (%rax),%rax
    410f:	39 78 40             	cmp    %edi,0x40(%rax)
    4112:	0f 4e dd             	cmovle %ebp,%ebx
    4115:	85 c9                	test   %ecx,%ecx
    4117:	74 0d                	je     4126 <timer_thread+0x106>
    4119:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    4120:	0f 85 75 ff ff ff    	jne    409b <timer_thread+0x7b>
    4126:	48 8d 3d 0b 2f 00 00 	lea    0x2f0b(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    412d:	e8 fe e1 ff ff       	call   2330 <puts@plt>
    4132:	49 63 56 30          	movslq 0x30(%r14),%rdx
    4136:	85 d2                	test   %edx,%edx
    4138:	7e 6b                	jle    41a5 <timer_thread+0x185>
    413a:	49 63 46 40          	movslq 0x40(%r14),%rax
    413e:	85 c0                	test   %eax,%eax
    4140:	7e 63                	jle    41a5 <timer_thread+0x185>
    4142:	48 c1 e0 09          	shl    $0x9,%rax
    4146:	4d 8b 46 18          	mov    0x18(%r14),%r8
    414a:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4152:	31 c9                	xor    %ecx,%ecx
    4154:	48 89 c6             	mov    %rax,%rsi
    4157:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    415b:	48 8b 40 38          	mov    0x38(%rax),%rax
    415f:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4163:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4169:	74 15                	je     4180 <timer_thread+0x160>
    416b:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    4175:	48 05 00 02 00 00    	add    $0x200,%rax
    417b:	48 39 c2             	cmp    %rax,%rdx
    417e:	74 1c                	je     419c <timer_thread+0x17c>
    4180:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    418a:	48 05 00 04 00 00    	add    $0x400,%rax
    4190:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    4197:	48 39 c2             	cmp    %rax,%rdx
    419a:	75 e4                	jne    4180 <timer_thread+0x160>
    419c:	48 83 c1 08          	add    $0x8,%rcx
    41a0:	48 39 cf             	cmp    %rcx,%rdi
    41a3:	75 b2                	jne    4157 <timer_thread+0x137>
    41a5:	0f ae f0             	mfence
    41a8:	66 0f 6f 05 20 3a 00 00 	movdqa 0x3a20(%rip),%xmm0        # 7bd0 <_IO_stdin_used+0xbd0>
    41b0:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    41b5:	49 63 46 28          	movslq 0x28(%r14),%rax
    41b9:	8d 7b 01             	lea    0x1(%rbx),%edi
    41bc:	85 c0                	test   %eax,%eax
    41be:	7e 47                	jle    4207 <timer_thread+0x1e7>
    41c0:	49 8b 4e 18          	mov    0x18(%r14),%rcx
    41c4:	4c 63 c3             	movslq %ebx,%r8
    41c7:	49 c1 e0 09          	shl    $0x9,%r8
    41cb:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    41cf:	90                   	nop
    41d0:	48 8b 19             	mov    (%rcx),%rbx
    41d3:	89 f8                	mov    %edi,%eax
    41d5:	48 83 c1 08          	add    $0x8,%rcx
    41d9:	99                   	cltd
    41da:	f7 7b 40             	idivl  0x40(%rbx)
    41dd:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    41e1:	83 ea 01             	sub    $0x1,%edx
    41e4:	48 63 d2             	movslq %edx,%rdx
    41e7:	48 c1 e2 09          	shl    $0x9,%rdx
    41eb:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    41f6:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    4202:	49 39 c9             	cmp    %rcx,%r9
    4205:	75 c9                	jne    41d0 <timer_thread+0x1b0>
    4207:	0f ae f0             	mfence
    420a:	49 8b 76 18          	mov    0x18(%r14),%rsi
    420e:	31 db                	xor    %ebx,%ebx
    4210:	48 8b 06             	mov    (%rsi),%rax
    4213:	39 78 40             	cmp    %edi,0x40(%rax)
    4216:	0f 4f df             	cmovg  %edi,%ebx
    4219:	41 8b 7e 30          	mov    0x30(%r14),%edi
    421d:	85 ff                	test   %edi,%edi
    421f:	0f 8e c7 01 00 00    	jle    43ec <timer_thread+0x3cc>
    4225:	89 5c 24 0c          	mov    %ebx,0xc(%rsp)
    4229:	45 31 ed             	xor    %r13d,%r13d
    422c:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    4232:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4238:	45 31 e4             	xor    %r12d,%r12d
    423b:	44 89 eb             	mov    %r13d,%ebx
    423e:	4a 8d 2c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbp
    4246:	44 89 e6             	mov    %r12d,%esi
    4249:	85 ff                	test   %edi,%edi
    424b:	0f 8e bf 00 00 00    	jle    4310 <timer_thread+0x2f0>
    4251:	4d 89 e2             	mov    %r12,%r10
    4254:	31 c0                	xor    %eax,%eax
    4256:	45 31 c0             	xor    %r8d,%r8d
    4259:	49 c1 e2 09          	shl    $0x9,%r10
    425d:	0f 1f 00             	nopl   (%rax)
    4260:	45 39 e8             	cmp    %r13d,%r8d
    4263:	74 3c                	je     42a1 <timer_thread+0x281>
    4265:	49 8b 56 18          	mov    0x18(%r14),%rdx
    4269:	48 8b 14 2a          	mov    (%rdx,%rbp,1),%rdx
    426d:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4271:	4a 8b 8c 12 70 01 00 00 	mov    0x170(%rdx,%r10,1),%rcx
    4279:	48 01 c1             	add    %rax,%rcx
    427c:	48 89 ca             	mov    %rcx,%rdx
    427f:	48 8b 09             	mov    (%rcx),%rcx
    4282:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    4289:	4c 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9
    4290:	4c 8b 9a 80 00 00 00 	mov    0x80(%rdx),%r11
    4297:	4d 85 c9             	test   %r9,%r9
    429a:	7f 24                	jg     42c0 <timer_thread+0x2a0>
    429c:	4d 85 db             	test   %r11,%r11
    429f:	7f 1f                	jg     42c0 <timer_thread+0x2a0>
    42a1:	41 83 c0 01          	add    $0x1,%r8d
    42a5:	48 05 80 01 00 00    	add    $0x180,%rax
    42ab:	44 39 c7             	cmp    %r8d,%edi
    42ae:	75 b0                	jne    4260 <timer_thread+0x240>
    42b0:	49 83 fc 01          	cmp    $0x1,%r12
    42b4:	74 5a                	je     4310 <timer_thread+0x2f0>
    42b6:	49 83 c4 01          	add    $0x1,%r12
    42ba:	44 89 e6             	mov    %r12d,%esi
    42bd:	eb 92                	jmp    4251 <timer_thread+0x231>
    42bf:	90                   	nop
    42c0:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    42c6:	48 83 ec 08          	sub    $0x8,%rsp
    42ca:	bf 01 00 00 00       	mov    $0x1,%edi
    42cf:	89 da                	mov    %ebx,%edx
    42d1:	50                   	push   %rax
    42d2:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
    42d8:	89 f1                	mov    %esi,%ecx
    42da:	48 8d 35 7c 2d 00 00 	lea    0x2d7c(%rip),%rsi        # 705d <_IO_stdin_used+0x5d>
    42e1:	50                   	push   %rax
    42e2:	31 c0                	xor    %eax,%eax
    42e4:	41 53                	push   %r11
    42e6:	e8 c5 e1 ff ff       	call   24b0 <__printf_chk@plt>
    42eb:	41 8b 7e 30          	mov    0x30(%r14),%edi
    42ef:	48 83 c4 20          	add    $0x20,%rsp
    42f3:	49 83 fc 01          	cmp    $0x1,%r12
    42f7:	0f 84 83 00 00 00    	je     4380 <timer_thread+0x360>
    42fd:	49 83 c4 01          	add    $0x1,%r12
    4301:	45 31 ff             	xor    %r15d,%r15d
    4304:	44 89 e6             	mov    %r12d,%esi
    4307:	85 ff                	test   %edi,%edi
    4309:	0f 8f 42 ff ff ff    	jg     4251 <timer_thread+0x231>
    430f:	90                   	nop
    4310:	49 83 c5 01          	add    $0x1,%r13
    4314:	44 39 ef             	cmp    %r13d,%edi
    4317:	0f 8f 1b ff ff ff    	jg     4238 <timer_thread+0x218>
    431d:	8b 5c 24 0c          	mov    0xc(%rsp),%ebx
    4321:	85 ff                	test   %edi,%edi
    4323:	7e 38                	jle    435d <timer_thread+0x33d>
    4325:	31 ed                	xor    %ebp,%ebp
    4327:	bf 01 00 00 00       	mov    $0x1,%edi
    432c:	49 8b 76 18          	mov    0x18(%r14),%rsi
    4330:	41 8b 56 40          	mov    0x40(%r14),%edx
    4334:	48 8b 04 ee          	mov    (%rsi,%rbp,8),%rax
    4338:	48 8b 40 38          	mov    0x38(%rax),%rax
    433c:	8b 88 9c 01 00 00    	mov    0x19c(%rax),%ecx
    4342:	39 d1                	cmp    %edx,%ecx
    4344:	7c 7a                	jl     43c0 <timer_thread+0x3a0>
    4346:	8b 80 9c 03 00 00    	mov    0x39c(%rax),%eax
    434c:	39 d0                	cmp    %edx,%eax
    434e:	7c 48                	jl     4398 <timer_thread+0x378>
    4350:	48 83 c5 01          	add    $0x1,%rbp
    4354:	41 39 6e 30          	cmp    %ebp,0x30(%r14)
    4358:	7f da                	jg     4334 <timer_thread+0x314>
    435a:	41 21 ff             	and    %edi,%r15d
    435d:	45 85 ff             	test   %r15d,%r15d
    4360:	0f 85 86 00 00 00    	jne    43ec <timer_thread+0x3cc>
    4366:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    436b:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    4370:	e8 2b e0 ff ff       	call   23a0 <nanosleep@plt>
    4375:	e9 3b fe ff ff       	jmp    41b5 <timer_thread+0x195>
    437a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4380:	49 83 c5 01          	add    $0x1,%r13
    4384:	45 31 ff             	xor    %r15d,%r15d
    4387:	44 39 ef             	cmp    %r13d,%edi
    438a:	0f 8f a8 fe ff ff    	jg     4238 <timer_thread+0x218>
    4390:	eb 8b                	jmp    431d <timer_thread+0x2fd>
    4392:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4398:	89 c2                	mov    %eax,%edx
    439a:	bf 01 00 00 00       	mov    $0x1,%edi
    439f:	31 c0                	xor    %eax,%eax
    43a1:	48 83 c5 01          	add    $0x1,%rbp
    43a5:	48 8d 35 59 2f 00 00 	lea    0x2f59(%rip),%rsi        # 7305 <_IO_stdin_used+0x305>
    43ac:	e8 ff e0 ff ff       	call   24b0 <__printf_chk@plt>
    43b1:	31 ff                	xor    %edi,%edi
    43b3:	41 39 6e 30          	cmp    %ebp,0x30(%r14)
    43b7:	0f 8f 6f ff ff ff    	jg     432c <timer_thread+0x30c>
    43bd:	eb 9b                	jmp    435a <timer_thread+0x33a>
    43bf:	90                   	nop
    43c0:	89 ca                	mov    %ecx,%edx
    43c2:	48 8d 35 3c 2f 00 00 	lea    0x2f3c(%rip),%rsi        # 7305 <_IO_stdin_used+0x305>
    43c9:	bf 01 00 00 00       	mov    $0x1,%edi
    43ce:	31 c0                	xor    %eax,%eax
    43d0:	e8 db e0 ff ff       	call   24b0 <__printf_chk@plt>
    43d5:	49 8b 76 18          	mov    0x18(%r14),%rsi
    43d9:	41 8b 56 40          	mov    0x40(%r14),%edx
    43dd:	31 ff                	xor    %edi,%edi
    43df:	48 8b 04 ee          	mov    (%rsi,%rbp,8),%rax
    43e3:	48 8b 40 38          	mov    0x38(%rax),%rax
    43e7:	e9 5a ff ff ff       	jmp    4346 <timer_thread+0x326>
    43ec:	48 8d 3d 61 2c 00 00 	lea    0x2c61(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    43f3:	e8 38 df ff ff       	call   2330 <puts@plt>
    43f8:	41 8b 56 44          	mov    0x44(%r14),%edx
    43fc:	85 d2                	test   %edx,%edx
    43fe:	0f 84 eb 00 00 00    	je     44ef <timer_thread+0x4cf>
    4404:	41 8b 46 2c          	mov    0x2c(%r14),%eax
    4408:	31 db                	xor    %ebx,%ebx
    440a:	48 8d 2d 69 2c 00 00 	lea    0x2c69(%rip),%rbp        # 707a <_IO_stdin_used+0x7a>
    4411:	4c 8d 25 7d 2c 00 00 	lea    0x2c7d(%rip),%r12        # 7095 <_IO_stdin_used+0x95>
    4418:	85 c0                	test   %eax,%eax
    441a:	7e 38                	jle    4454 <timer_thread+0x434>
    441c:	0f 1f 40 00          	nopl   0x0(%rax)
    4420:	31 c0                	xor    %eax,%eax
    4422:	89 da                	mov    %ebx,%edx
    4424:	48 89 ee             	mov    %rbp,%rsi
    4427:	bf 01 00 00 00       	mov    $0x1,%edi
    442c:	e8 7f e0 ff ff       	call   24b0 <__printf_chk@plt>
    4431:	49 8b 46 18          	mov    0x18(%r14),%rax
    4435:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4439:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
    443d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
    4444:	0f 84 d2 00 00 00    	je     451c <timer_thread+0x4fc>
    444a:	48 83 c3 01          	add    $0x1,%rbx
    444e:	41 39 5e 2c          	cmp    %ebx,0x2c(%r14)
    4452:	7f cc                	jg     4420 <timer_thread+0x400>
    4454:	49 63 56 30          	movslq 0x30(%r14),%rdx
    4458:	85 d2                	test   %edx,%edx
    445a:	7e 7c                	jle    44d8 <timer_thread+0x4b8>
    445c:	41 8b 46 40          	mov    0x40(%r14),%eax
    4460:	85 c0                	test   %eax,%eax
    4462:	7e 74                	jle    44d8 <timer_thread+0x4b8>
    4464:	48 63 f0             	movslq %eax,%rsi
    4467:	4d 8b 46 18          	mov    0x18(%r14),%r8
    446b:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4473:	31 c9                	xor    %ecx,%ecx
    4475:	48 c1 e6 09          	shl    $0x9,%rsi
    4479:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4480:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4484:	48 8b 40 38          	mov    0x38(%rax),%rax
    4488:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    448c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4492:	74 1c                	je     44b0 <timer_thread+0x490>
    4494:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    449e:	48 05 00 02 00 00    	add    $0x200,%rax
    44a4:	48 39 d0             	cmp    %rdx,%rax
    44a7:	74 26                	je     44cf <timer_thread+0x4af>
    44a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    44b0:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    44ba:	48 05 00 04 00 00    	add    $0x400,%rax
    44c0:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
    44ca:	48 39 d0             	cmp    %rdx,%rax
    44cd:	75 e1                	jne    44b0 <timer_thread+0x490>
    44cf:	48 83 c1 08          	add    $0x8,%rcx
    44d3:	48 39 cf             	cmp    %rcx,%rdi
    44d6:	75 a8                	jne    4480 <timer_thread+0x460>
    44d8:	0f ae f0             	mfence
    44db:	48 8d 3d c5 2b 00 00 	lea    0x2bc5(%rip),%rdi        # 70a7 <_IO_stdin_used+0xa7>
    44e2:	e8 49 de ff ff       	call   2330 <puts@plt>
    44e7:	41 c7 46 44 00 00 00 00 	movl   $0x0,0x44(%r14)
    44ef:	48 8d 3d b8 2b 00 00 	lea    0x2bb8(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    44f6:	e8 35 de ff ff       	call   2330 <puts@plt>
    44fb:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    4500:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4509:	75 41                	jne    454c <timer_thread+0x52c>
    450b:	48 83 c4 68          	add    $0x68,%rsp
    450f:	31 c0                	xor    %eax,%eax
    4511:	5b                   	pop    %rbx
    4512:	5d                   	pop    %rbp
    4513:	41 5c                	pop    %r12
    4515:	41 5d                	pop    %r13
    4517:	41 5e                	pop    %r14
    4519:	41 5f                	pop    %r15
    451b:	c3                   	ret
    451c:	4c 89 e7             	mov    %r12,%rdi
    451f:	e8 0c de ff ff       	call   2330 <puts@plt>
    4524:	49 8b 46 18          	mov    0x18(%r14),%rax
    4528:	be 01 00 00 00       	mov    $0x1,%esi
    452d:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4531:	48 83 c3 01          	add    $0x1,%rbx
    4535:	8b 78 60             	mov    0x60(%rax),%edi
    4538:	e8 23 df ff ff       	call   2460 <eventfd_write@plt>
    453d:	41 39 5e 2c          	cmp    %ebx,0x2c(%r14)
    4541:	0f 8f d9 fe ff ff    	jg     4420 <timer_thread+0x400>
    4547:	e9 08 ff ff ff       	jmp    4454 <timer_thread+0x434>
    454c:	e8 2f de ff ff       	call   2380 <__stack_chk_fail@plt>
    4551:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    455c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004560 <minf>:
    4560:	f3 0f 1e fa          	endbr64
    4564:	39 f7                	cmp    %esi,%edi
    4566:	89 f0                	mov    %esi,%eax
    4568:	0f 4e c7             	cmovle %edi,%eax
    456b:	c3                   	ret
    456c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004570 <maxf>:
    4570:	f3 0f 1e fa          	endbr64
    4574:	39 f7                	cmp    %esi,%edi
    4576:	89 f0                	mov    %esi,%eax
    4578:	0f 4d c7             	cmovge %edi,%eax
    457b:	c3                   	ret
    457c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004580 <strtolower>:
    4580:	f3 0f 1e fa          	endbr64
    4584:	55                   	push   %rbp
    4585:	53                   	push   %rbx
    4586:	48 83 ec 08          	sub    $0x8,%rsp
    458a:	48 0f be 1f          	movsbq (%rdi),%rbx
    458e:	84 db                	test   %bl,%bl
    4590:	74 24                	je     45b6 <strtolower+0x36>
    4592:	48 89 fd             	mov    %rdi,%rbp
    4595:	e8 f6 df ff ff       	call   2590 <__ctype_tolower_loc@plt>
    459a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    45a0:	48 8b 10             	mov    (%rax),%rdx
    45a3:	48 83 c5 01          	add    $0x1,%rbp
    45a7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    45aa:	88 55 ff             	mov    %dl,-0x1(%rbp)
    45ad:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    45b2:	84 db                	test   %bl,%bl
    45b4:	75 ea                	jne    45a0 <strtolower+0x20>
    45b6:	48 83 c4 08          	add    $0x8,%rsp
    45ba:	5b                   	pop    %rbx
    45bb:	5d                   	pop    %rbp
    45bc:	c3                   	ret
    45bd:	0f 1f 00             	nopl   (%rax)

00000000000045c0 <zh_malloc>:
    45c0:	f3 0f 1e fa          	endbr64
    45c4:	48 83 ec 08          	sub    $0x8,%rsp
    45c8:	e8 a3 de ff ff       	call   2470 <malloc@plt>
    45cd:	48 85 c0             	test   %rax,%rax
    45d0:	74 05                	je     45d7 <zh_malloc+0x17>
    45d2:	48 83 c4 08          	add    $0x8,%rsp
    45d6:	c3                   	ret
    45d7:	48 8b 0d 42 5a 00 00 	mov    0x5a42(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    45de:	ba 28 00 00 00       	mov    $0x28,%edx
    45e3:	be 01 00 00 00       	mov    $0x1,%esi
    45e8:	48 8d 3d b9 2f 00 00 	lea    0x2fb9(%rip),%rdi        # 75a8 <_IO_stdin_used+0x5a8>
    45ef:	e8 3c df ff ff       	call   2530 <fwrite@plt>
    45f4:	bf 01 00 00 00       	mov    $0x1,%edi
    45f9:	e8 12 df ff ff       	call   2510 <exit@plt>
    45fe:	66 90                	xchg   %ax,%ax

0000000000004600 <get_filename_ext>:
    4600:	f3 0f 1e fa          	endbr64
    4604:	53                   	push   %rbx
    4605:	be 2e 00 00 00       	mov    $0x2e,%esi
    460a:	48 89 fb             	mov    %rdi,%rbx
    460d:	e8 9e dd ff ff       	call   23b0 <strrchr@plt>
    4612:	48 85 c0             	test   %rax,%rax
    4615:	74 11                	je     4628 <get_filename_ext+0x28>
    4617:	48 39 c3             	cmp    %rax,%rbx
    461a:	74 0c                	je     4628 <get_filename_ext+0x28>
    461c:	48 83 c0 01          	add    $0x1,%rax
    4620:	5b                   	pop    %rbx
    4621:	c3                   	ret
    4622:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4628:	48 8d 05 c7 2a 00 00 	lea    0x2ac7(%rip),%rax        # 70f6 <_IO_stdin_used+0xf6>
    462f:	5b                   	pop    %rbx
    4630:	c3                   	ret
    4631:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    463c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004640 <send_headers>:
    4640:	f3 0f 1e fa          	endbr64
    4644:	41 55                	push   %r13
    4646:	49 89 f5             	mov    %rsi,%r13
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
    4678:	e8 13 de ff ff       	call   2490 <__strcpy_chk@plt>
    467d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4682:	84 db                	test   %bl,%bl
    4684:	74 24                	je     46aa <send_headers+0x6a>
    4686:	e8 05 df ff ff       	call   2590 <__ctype_tolower_loc@plt>
    468b:	48 8b 08             	mov    (%rax),%rcx
    468e:	4c 89 e0             	mov    %r12,%rax
    4691:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4698:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    469b:	48 83 c0 01          	add    $0x1,%rax
    469f:	88 50 ff             	mov    %dl,-0x1(%rax)
    46a2:	48 0f be 18          	movsbq (%rax),%rbx
    46a6:	84 db                	test   %bl,%bl
    46a8:	75 ee                	jne    4698 <send_headers+0x58>
    46aa:	bf 11 00 00 00       	mov    $0x11,%edi
    46af:	e8 bc dd ff ff       	call   2470 <malloc@plt>
    46b4:	48 85 c0             	test   %rax,%rax
    46b7:	0f 84 7e 04 00 00    	je     4b3b <send_headers+0x4fb>
    46bd:	66 0f 6f 05 1b 35 00 00 	movdqa 0x351b(%rip),%xmm0        # 7be0 <_IO_stdin_used+0xbe0>
    46c5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    46c9:	bf 17 00 00 00       	mov    $0x17,%edi
    46ce:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    46d6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    46da:	0f 11 00             	movups %xmm0,(%rax)
    46dd:	e8 8e dd ff ff       	call   2470 <malloc@plt>
    46e2:	48 85 c0             	test   %rax,%rax
    46e5:	0f 84 50 04 00 00    	je     4b3b <send_headers+0x4fb>
    46eb:	66 0f 6f 05 fd 34 00 00 	movdqa 0x34fd(%rip),%xmm0        # 7bf0 <_IO_stdin_used+0xbf0>
    46f3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    46f7:	4c 89 e7             	mov    %r12,%rdi
    46fa:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    4704:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    470c:	0f 11 00             	movups %xmm0,(%rax)
    470f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    4713:	be 2e 00 00 00       	mov    $0x2e,%esi
    4718:	e8 93 dc ff ff       	call   23b0 <strrchr@plt>
    471d:	48 85 c0             	test   %rax,%rax
    4720:	0f 84 ea 02 00 00    	je     4a10 <send_headers+0x3d0>
    4726:	4c 39 e0             	cmp    %r12,%rax
    4729:	0f 84 e1 02 00 00    	je     4a10 <send_headers+0x3d0>
    472f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    4733:	48 8d 3d 8a 29 00 00 	lea    0x298a(%rip),%rdi        # 70c4 <_IO_stdin_used+0xc4>
    473a:	48 89 de             	mov    %rbx,%rsi
    473d:	e8 ce dc ff ff       	call   2410 <strcmp@plt>
    4742:	85 c0                	test   %eax,%eax
    4744:	75 20                	jne    4766 <send_headers+0x126>
    4746:	66 0f 6f 05 b2 34 00 00 	movdqa 0x34b2(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    474e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4756:	66 0f 6f 05 b2 34 00 00 	movdqa 0x34b2(%rip),%xmm0        # 7c10 <_IO_stdin_used+0xc10>
    475e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4766:	48 89 de             	mov    %rbx,%rsi
    4769:	48 8d 3d 58 29 00 00 	lea    0x2958(%rip),%rdi        # 70c8 <_IO_stdin_used+0xc8>
    4770:	e8 9b dc ff ff       	call   2410 <strcmp@plt>
    4775:	85 c0                	test   %eax,%eax
    4777:	75 20                	jne    4799 <send_headers+0x159>
    4779:	66 0f 6f 05 7f 34 00 00 	movdqa 0x347f(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    4781:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4789:	66 0f 6f 05 7f 34 00 00 	movdqa 0x347f(%rip),%xmm0        # 7c10 <_IO_stdin_used+0xc10>
    4791:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4799:	48 89 de             	mov    %rbx,%rsi
    479c:	48 8d 3d 2a 29 00 00 	lea    0x292a(%rip),%rdi        # 70cd <_IO_stdin_used+0xcd>
    47a3:	e8 68 dc ff ff       	call   2410 <strcmp@plt>
    47a8:	85 c0                	test   %eax,%eax
    47aa:	0f 84 10 02 00 00    	je     49c0 <send_headers+0x380>
    47b0:	48 89 de             	mov    %rbx,%rsi
    47b3:	48 8d 3d 17 29 00 00 	lea    0x2917(%rip),%rdi        # 70d1 <_IO_stdin_used+0xd1>
    47ba:	e8 51 dc ff ff       	call   2410 <strcmp@plt>
    47bf:	85 c0                	test   %eax,%eax
    47c1:	0f 84 a9 02 00 00    	je     4a70 <send_headers+0x430>
    47c7:	48 89 de             	mov    %rbx,%rsi
    47ca:	48 8d 3d 04 29 00 00 	lea    0x2904(%rip),%rdi        # 70d5 <_IO_stdin_used+0xd5>
    47d1:	e8 3a dc ff ff       	call   2410 <strcmp@plt>
    47d6:	85 c0                	test   %eax,%eax
    47d8:	0f 84 6a 02 00 00    	je     4a48 <send_headers+0x408>
    47de:	48 89 de             	mov    %rbx,%rsi
    47e1:	48 8d 3d 30 29 00 00 	lea    0x2930(%rip),%rdi        # 7118 <_IO_stdin_used+0x118>
    47e8:	e8 23 dc ff ff       	call   2410 <strcmp@plt>
    47ed:	85 c0                	test   %eax,%eax
    47ef:	0f 84 2b 02 00 00    	je     4a20 <send_headers+0x3e0>
    47f5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    47f8:	0f 84 52 01 00 00    	je     4950 <send_headers+0x310>
    47fe:	48 89 de             	mov    %rbx,%rsi
    4801:	48 8d 3d d1 28 00 00 	lea    0x28d1(%rip),%rdi        # 70d9 <_IO_stdin_used+0xd9>
    4808:	e8 03 dc ff ff       	call   2410 <strcmp@plt>
    480d:	85 c0                	test   %eax,%eax
    480f:	0f 84 ab 02 00 00    	je     4ac0 <send_headers+0x480>
    4815:	48 89 de             	mov    %rbx,%rsi
    4818:	48 8d 3d be 28 00 00 	lea    0x28be(%rip),%rdi        # 70dd <_IO_stdin_used+0xdd>
    481f:	e8 ec db ff ff       	call   2410 <strcmp@plt>
    4824:	85 c0                	test   %eax,%eax
    4826:	0f 84 6c 02 00 00    	je     4a98 <send_headers+0x458>
    482c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4834:	4c 89 e7             	mov    %r12,%rdi
    4837:	e8 34 db ff ff       	call   2370 <strlen@plt>
    483c:	48 89 c7             	mov    %rax,%rdi
    483f:	48 89 c3             	mov    %rax,%rbx
    4842:	e8 29 dc ff ff       	call   2470 <malloc@plt>
    4847:	48 85 c0             	test   %rax,%rax
    484a:	0f 84 eb 02 00 00    	je     4b3b <send_headers+0x4fb>
    4850:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4854:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
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
    4881:	4d 89 e8             	mov    %r13,%r8
    4884:	48 8d 0d 56 28 00 00 	lea    0x2856(%rip),%rcx        # 70e1 <_IO_stdin_used+0xe1>
    488b:	4c 89 e7             	mov    %r12,%rdi
    488e:	31 c0                	xor    %eax,%eax
    4890:	ba 00 04 00 00       	mov    $0x400,%edx
    4895:	be 01 00 00 00       	mov    $0x1,%esi
    489a:	e8 01 dd ff ff       	call   25a0 <__sprintf_chk@plt>
    489f:	4c 89 e7             	mov    %r12,%rdi
    48a2:	e8 c9 da ff ff       	call   2370 <strlen@plt>
    48a7:	48 89 c7             	mov    %rax,%rdi
    48aa:	48 89 c3             	mov    %rax,%rbx
    48ad:	e8 be db ff ff       	call   2470 <malloc@plt>
    48b2:	48 85 c0             	test   %rax,%rax
    48b5:	0f 84 80 02 00 00    	je     4b3b <send_headers+0x4fb>
    48bb:	48 89 45 30          	mov    %rax,0x30(%rbp)
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
    48ec:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    48f1:	bf 02 00 00 00       	mov    $0x2,%edi
    48f6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    48fe:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4906:	e8 65 db ff ff       	call   2470 <malloc@plt>
    490b:	48 85 c0             	test   %rax,%rax
    490e:	0f 84 27 02 00 00    	je     4b3b <send_headers+0x4fb>
    4914:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    491c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    4920:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4928:	66 89 10             	mov    %dx,(%rax)
    492b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4933:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    493c:	0f 85 20 02 00 00    	jne    4b62 <send_headers+0x522>
    4942:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4949:	5b                   	pop    %rbx
    494a:	5d                   	pop    %rbp
    494b:	41 5c                	pop    %r12
    494d:	41 5d                	pop    %r13
    494f:	c3                   	ret
    4950:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4954:	0f 85 a4 fe ff ff    	jne    47fe <send_headers+0x1be>
    495a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    495e:	0f 85 9a fe ff ff    	jne    47fe <send_headers+0x1be>
    4964:	66 0f 6f 05 f4 32 00 00 	movdqa 0x32f4(%rip),%xmm0        # 7c60 <_IO_stdin_used+0xc60>
    496c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4976:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    497e:	66 0f 6f 05 ea 32 00 00 	movdqa 0x32ea(%rip),%xmm0        # 7c70 <_IO_stdin_used+0xc70>
    4986:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    498e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4996:	e9 63 fe ff ff       	jmp    47fe <send_headers+0x1be>
    499b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    49a0:	89 da                	mov    %ebx,%edx
    49a2:	48 89 c7             	mov    %rax,%rdi
    49a5:	4c 89 e6             	mov    %r12,%rsi
    49a8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    49ad:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    49b2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    49b5:	c1 e9 03             	shr    $0x3,%ecx
    49b8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    49bb:	e9 c1 fe ff ff       	jmp    4881 <send_headers+0x241>
    49c0:	66 0f 6f 05 38 32 00 00 	movdqa 0x3238(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    49c8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    49d0:	66 0f 6f 05 48 32 00 00 	movdqa 0x3248(%rip),%xmm0        # 7c20 <_IO_stdin_used+0xc20>
    49d8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    49e0:	e9 cb fd ff ff       	jmp    47b0 <send_headers+0x170>
    49e5:	0f 1f 00             	nopl   (%rax)
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
    4a10:	48 8d 1d df 26 00 00 	lea    0x26df(%rip),%rbx        # 70f6 <_IO_stdin_used+0xf6>
    4a17:	e9 94 fd ff ff       	jmp    47b0 <send_headers+0x170>
    4a1c:	0f 1f 40 00          	nopl   0x0(%rax)
    4a20:	66 0f 6f 05 18 32 00 00 	movdqa 0x3218(%rip),%xmm0        # 7c40 <_IO_stdin_used+0xc40>
    4a28:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a30:	66 0f 6f 05 18 32 00 00 	movdqa 0x3218(%rip),%xmm0        # 7c50 <_IO_stdin_used+0xc50>
    4a38:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a40:	e9 b0 fd ff ff       	jmp    47f5 <send_headers+0x1b5>
    4a45:	0f 1f 00             	nopl   (%rax)
    4a48:	66 0f 6f 05 f0 31 00 00 	movdqa 0x31f0(%rip),%xmm0        # 7c40 <_IO_stdin_used+0xc40>
    4a50:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a58:	66 0f 6f 05 f0 31 00 00 	movdqa 0x31f0(%rip),%xmm0        # 7c50 <_IO_stdin_used+0xc50>
    4a60:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a68:	e9 71 fd ff ff       	jmp    47de <send_headers+0x19e>
    4a6d:	0f 1f 00             	nopl   (%rax)
    4a70:	66 0f 6f 05 88 31 00 00 	movdqa 0x3188(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    4a78:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a80:	66 0f 6f 05 a8 31 00 00 	movdqa 0x31a8(%rip),%xmm0        # 7c30 <_IO_stdin_used+0xc30>
    4a88:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a90:	e9 32 fd ff ff       	jmp    47c7 <send_headers+0x187>
    4a95:	0f 1f 00             	nopl   (%rax)
    4a98:	66 0f 6f 05 a0 31 00 00 	movdqa 0x31a0(%rip),%xmm0        # 7c40 <_IO_stdin_used+0xc40>
    4aa0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4aa8:	66 0f 6f 05 e0 31 00 00 	movdqa 0x31e0(%rip),%xmm0        # 7c90 <_IO_stdin_used+0xc90>
    4ab0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4ab8:	e9 6f fd ff ff       	jmp    482c <send_headers+0x1ec>
    4abd:	0f 1f 00             	nopl   (%rax)
    4ac0:	66 0f 6f 05 78 31 00 00 	movdqa 0x3178(%rip),%xmm0        # 7c40 <_IO_stdin_used+0xc40>
    4ac8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ad0:	66 0f 6f 05 a8 31 00 00 	movdqa 0x31a8(%rip),%xmm0        # 7c80 <_IO_stdin_used+0xc80>
    4ad8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4ae0:	e9 30 fd ff ff       	jmp    4815 <send_headers+0x1d5>
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
    4b3b:	48 8b 0d de 54 00 00 	mov    0x54de(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4b42:	ba 28 00 00 00       	mov    $0x28,%edx
    4b47:	be 01 00 00 00       	mov    $0x1,%esi
    4b4c:	48 8d 3d 55 2a 00 00 	lea    0x2a55(%rip),%rdi        # 75a8 <_IO_stdin_used+0x5a8>
    4b53:	e8 d8 d9 ff ff       	call   2530 <fwrite@plt>
    4b58:	bf 01 00 00 00       	mov    $0x1,%edi
    4b5d:	e8 ae d9 ff ff       	call   2510 <exit@plt>
    4b62:	e8 19 d8 ff ff       	call   2380 <__stack_chk_fail@plt>
    4b67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004b70 <copy_file_contents>:
    4b70:	f3 0f 1e fa          	endbr64
    4b74:	41 55                	push   %r13
    4b76:	49 89 d5             	mov    %rdx,%r13
    4b79:	41 54                	push   %r12
    4b7b:	49 89 fc             	mov    %rdi,%r12
    4b7e:	48 89 f7             	mov    %rsi,%rdi
    4b81:	55                   	push   %rbp
    4b82:	53                   	push   %rbx
    4b83:	48 89 f3             	mov    %rsi,%rbx
    4b86:	48 83 ec 08          	sub    $0x8,%rsp
    4b8a:	e8 e1 d8 ff ff       	call   2470 <malloc@plt>
    4b8f:	48 85 c0             	test   %rax,%rax
    4b92:	74 6b                	je     4bff <copy_file_contents+0x8f>
    4b94:	4c 89 e7             	mov    %r12,%rdi
    4b97:	48 89 c5             	mov    %rax,%rbp
    4b9a:	31 f6                	xor    %esi,%esi
    4b9c:	31 c0                	xor    %eax,%eax
    4b9e:	e8 3d d9 ff ff       	call   24e0 <open@plt>
    4ba3:	41 89 c4             	mov    %eax,%r12d
    4ba6:	85 c0                	test   %eax,%eax
    4ba8:	0f 88 28 da ff ff    	js     25d6 <copy_file_contents.cold>
    4bae:	48 89 da             	mov    %rbx,%rdx
    4bb1:	48 89 ee             	mov    %rbp,%rsi
    4bb4:	89 c7                	mov    %eax,%edi
    4bb6:	e8 35 d8 ff ff       	call   23f0 <read@plt>
    4bbb:	48 98                	cltq
    4bbd:	48 39 d8             	cmp    %rbx,%rax
    4bc0:	7c 1e                	jl     4be0 <copy_file_contents+0x70>
    4bc2:	44 89 e7             	mov    %r12d,%edi
    4bc5:	e8 06 d8 ff ff       	call   23d0 <close@plt>
    4bca:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    4bce:	49 89 5d 08          	mov    %rbx,0x8(%r13)
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
    4bf1:	48 8d 3d ff 24 00 00 	lea    0x24ff(%rip),%rdi        # 70f7 <_IO_stdin_used+0xf7>
    4bf8:	e8 33 d9 ff ff       	call   2530 <fwrite@plt>
    4bfd:	eb c3                	jmp    4bc2 <copy_file_contents+0x52>
    4bff:	48 8b 0d 1a 54 00 00 	mov    0x541a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c06:	ba 28 00 00 00       	mov    $0x28,%edx
    4c0b:	be 01 00 00 00       	mov    $0x1,%esi
    4c10:	48 8d 3d 91 29 00 00 	lea    0x2991(%rip),%rdi        # 75a8 <_IO_stdin_used+0x5a8>
    4c17:	e8 14 d9 ff ff       	call   2530 <fwrite@plt>
    4c1c:	bf 01 00 00 00       	mov    $0x1,%edi
    4c21:	e8 ea d8 ff ff       	call   2510 <exit@plt>
    4c26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004c30 <add_write_request>:
    4c30:	f3 0f 1e fa          	endbr64
    4c34:	8b 46 44             	mov    0x44(%rsi),%eax
    4c37:	48 89 fa             	mov    %rdi,%rdx
    4c3a:	48 89 f7             	mov    %rsi,%rdi
    4c3d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    4c43:	8d 70 01             	lea    0x1(%rax),%esi
    4c46:	48 8b 07             	mov    (%rdi),%rax
    4c49:	44 8b 00             	mov    (%rax),%r8d
    4c4c:	f6 c1 02             	test   $0x2,%cl
    4c4f:	74 00                	je     4c51 <add_write_request+0x21>
    4c51:	89 f0                	mov    %esi,%eax
    4c53:	44 29 c0             	sub    %r8d,%eax
    4c56:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4c59:	0f 82 83 d9 ff ff    	jb     25e2 <add_write_request.cold>
    4c5f:	c1 e9 0a             	shr    $0xa,%ecx
    4c62:	48 83 ec 08          	sub    $0x8,%rsp
    4c66:	8b 47 44             	mov    0x44(%rdi),%eax
    4c69:	23 47 58             	and    0x58(%rdi),%eax
    4c6c:	83 e1 01             	and    $0x1,%ecx
    4c6f:	89 77 44             	mov    %esi,0x44(%rdi)
    4c72:	8b 72 08             	mov    0x8(%rdx),%esi
    4c75:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4c79:	d3 e0                	shl    %cl,%eax
    4c7b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    4c7e:	48 c1 e0 06          	shl    $0x6,%rax
    4c82:	48 03 47 38          	add    0x38(%rdi),%rax
    4c86:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    4c8c:	89 70 04             	mov    %esi,0x4(%rax)
    4c8f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    4c93:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4c99:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4ca1:	48 89 70 10          	mov    %rsi,0x10(%rax)
    4ca5:	89 48 18             	mov    %ecx,0x18(%rax)
    4ca8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    4caf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4cb7:	48 89 50 20          	mov    %rdx,0x20(%rax)
    4cbb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4cbf:	e8 cc d6 ff ff       	call   2390 <io_uring_submit@plt>
    4cc4:	31 c0                	xor    %eax,%eax
    4cc6:	48 83 c4 08          	add    $0x8,%rsp
    4cca:	c3                   	ret
    4ccb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004cd0 <add_read_request>:
    4cd0:	f3 0f 1e fa          	endbr64
    4cd4:	41 55                	push   %r13
    4cd6:	41 89 fd             	mov    %edi,%r13d
    4cd9:	41 54                	push   %r12
    4cdb:	55                   	push   %rbp
    4cdc:	53                   	push   %rbx
    4cdd:	48 89 f3             	mov    %rsi,%rbx
    4ce0:	48 83 ec 08          	sub    $0x8,%rsp
    4ce4:	8b 46 44             	mov    0x44(%rsi),%eax
    4ce7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    4ced:	48 8b 16             	mov    (%rsi),%rdx
    4cf0:	83 c0 01             	add    $0x1,%eax
    4cf3:	8b 32                	mov    (%rdx),%esi
    4cf5:	f6 c1 02             	test   $0x2,%cl
    4cf8:	74 00                	je     4cfa <add_read_request+0x2a>
    4cfa:	89 c2                	mov    %eax,%edx
    4cfc:	29 f2                	sub    %esi,%edx
    4cfe:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4d01:	0f 82 eb d8 ff ff    	jb     25f2 <add_read_request.cold>
    4d07:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4d0a:	c1 e9 0a             	shr    $0xa,%ecx
    4d0d:	89 43 44             	mov    %eax,0x44(%rbx)
    4d10:	bf 20 00 00 00       	mov    $0x20,%edi
    4d15:	83 e1 01             	and    $0x1,%ecx
    4d18:	23 6b 58             	and    0x58(%rbx),%ebp
    4d1b:	d3 e5                	shl    %cl,%ebp
    4d1d:	48 c1 e5 06          	shl    $0x6,%rbp
    4d21:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4d25:	e8 46 d7 ff ff       	call   2470 <malloc@plt>
    4d2a:	be 01 00 00 00       	mov    $0x1,%esi
    4d2f:	bf 00 20 00 00       	mov    $0x2000,%edi
    4d34:	49 89 c4             	mov    %rax,%r12
    4d37:	e8 c4 d6 ff ff       	call   2400 <calloc@plt>
    4d3c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    4d41:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4d45:	48 89 df             	mov    %rbx,%rdi
    4d48:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    4d4d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    4d52:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    4d5b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    4d63:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    4d67:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    4d6b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    4d72:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    4d7a:	48 89 45 10          	mov    %rax,0x10(%rbp)
    4d7e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    4d86:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    4d8e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4d92:	e8 f9 d5 ff ff       	call   2390 <io_uring_submit@plt>
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
    4db0:	f3 0f 1e fa          	endbr64
    4db4:	41 56                	push   %r14
    4db6:	41 89 f6             	mov    %esi,%r14d
    4db9:	41 55                	push   %r13
    4dbb:	49 89 fd             	mov    %rdi,%r13
    4dbe:	bf 20 00 00 00       	mov    $0x20,%edi
    4dc3:	41 54                	push   %r12
    4dc5:	55                   	push   %rbp
    4dc6:	48 89 d5             	mov    %rdx,%rbp
    4dc9:	53                   	push   %rbx
    4dca:	e8 a1 d6 ff ff       	call   2470 <malloc@plt>
    4dcf:	48 85 c0             	test   %rax,%rax
    4dd2:	0f 84 dd 00 00 00    	je     4eb5 <_send_static_string_content+0x105>
    4dd8:	48 89 c3             	mov    %rax,%rbx
    4ddb:	4c 89 ef             	mov    %r13,%rdi
    4dde:	e8 8d d5 ff ff       	call   2370 <strlen@plt>
    4de3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    4dea:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    4dee:	48 89 c7             	mov    %rax,%rdi
    4df1:	49 89 c4             	mov    %rax,%r12
    4df4:	e8 77 d6 ff ff       	call   2470 <malloc@plt>
    4df9:	48 89 c7             	mov    %rax,%rdi
    4dfc:	48 85 c0             	test   %rax,%rax
    4dff:	0f 84 b0 00 00 00    	je     4eb5 <_send_static_string_content+0x105>
    4e05:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4e09:	4c 89 e2             	mov    %r12,%rdx
    4e0c:	4c 89 ee             	mov    %r13,%rsi
    4e0f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4e13:	e8 28 d6 ff ff       	call   2440 <memcpy@plt>
    4e18:	8b 45 44             	mov    0x44(%rbp),%eax
    4e1b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    4e21:	8d 50 01             	lea    0x1(%rax),%edx
    4e24:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4e28:	8b 30                	mov    (%rax),%esi
    4e2a:	f6 c1 02             	test   $0x2,%cl
    4e2d:	0f 85 7d 00 00 00    	jne    4eb0 <_send_static_string_content+0x100>
    4e33:	89 d0                	mov    %edx,%eax
    4e35:	29 f0                	sub    %esi,%eax
    4e37:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    4e3a:	0f 82 bc d7 ff ff    	jb     25fc <_send_static_string_content.cold>
    4e40:	c1 e9 0a             	shr    $0xa,%ecx
    4e43:	8b 45 44             	mov    0x44(%rbp),%eax
    4e46:	23 45 58             	and    0x58(%rbp),%eax
    4e49:	89 55 44             	mov    %edx,0x44(%rbp)
    4e4c:	83 e1 01             	and    $0x1,%ecx
    4e4f:	8b 53 04             	mov    0x4(%rbx),%edx
    4e52:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    4e58:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4e5c:	d3 e0                	shl    %cl,%eax
    4e5e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    4e61:	48 89 ef             	mov    %rbp,%rdi
    4e64:	48 c1 e0 06          	shl    $0x6,%rax
    4e68:	48 03 45 38          	add    0x38(%rbp),%rax
    4e6c:	89 48 04             	mov    %ecx,0x4(%rax)
    4e6f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    4e73:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4e79:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4e81:	48 89 48 10          	mov    %rcx,0x10(%rax)
    4e85:	89 50 18             	mov    %edx,0x18(%rax)
    4e88:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    4e8f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4e97:	48 89 58 20          	mov    %rbx,0x20(%rax)
    4e9b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4e9f:	5b                   	pop    %rbx
    4ea0:	5d                   	pop    %rbp
    4ea1:	41 5c                	pop    %r12
    4ea3:	41 5d                	pop    %r13
    4ea5:	41 5e                	pop    %r14
    4ea7:	e9 e4 d4 ff ff       	jmp    2390 <io_uring_submit@plt>
    4eac:	0f 1f 40 00          	nopl   0x0(%rax)
    4eb0:	e9 7e ff ff ff       	jmp    4e33 <_send_static_string_content+0x83>
    4eb5:	48 8b 0d 64 51 00 00 	mov    0x5164(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4ebc:	ba 28 00 00 00       	mov    $0x28,%edx
    4ec1:	be 01 00 00 00       	mov    $0x1,%esi
    4ec6:	48 8d 3d db 26 00 00 	lea    0x26db(%rip),%rdi        # 75a8 <_IO_stdin_used+0x5a8>
    4ecd:	e8 5e d6 ff ff       	call   2530 <fwrite@plt>
    4ed2:	bf 01 00 00 00       	mov    $0x1,%edi
    4ed7:	e8 34 d6 ff ff       	call   2510 <exit@plt>
    4edc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004ee0 <handle_unimplemented_method>:
    4ee0:	f3 0f 1e fa          	endbr64
    4ee4:	48 89 f2             	mov    %rsi,%rdx
    4ee7:	89 fe                	mov    %edi,%esi
    4ee9:	48 8b 3d 28 51 00 00 	mov    0x5128(%rip),%rdi        # a018 <unimplemented_content>
    4ef0:	e9 bb fe ff ff       	jmp    4db0 <_send_static_string_content>
    4ef5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004f00 <handle_http_404>:
    4f00:	f3 0f 1e fa          	endbr64
    4f04:	48 89 f2             	mov    %rsi,%rdx
    4f07:	89 fe                	mov    %edi,%esi
    4f09:	48 8b 3d 00 51 00 00 	mov    0x5100(%rip),%rdi        # a010 <http_404_content>
    4f10:	e9 9b fe ff ff       	jmp    4db0 <_send_static_string_content>
    4f15:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004f20 <handle_get_method>:
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
    4f4f:	e8 1c d4 ff ff       	call   2370 <strlen@plt>
    4f54:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4f59:	48 89 c3             	mov    %rax,%rbx
    4f5c:	0f 84 b6 00 00 00    	je     5018 <handle_get_method+0xf8>
    4f62:	b8 69 63 00 00       	mov    $0x6369,%eax
    4f67:	48 89 ee             	mov    %rbp,%rsi
    4f6a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4f6e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4f73:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4f7b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4f83:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4f8e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    4f96:	e8 85 d4 ff ff       	call   2420 <__memcpy_chk@plt>
    4f9b:	48 89 e6             	mov    %rsp,%rsi
    4f9e:	4c 89 f7             	mov    %r14,%rdi
    4fa1:	e8 8a d4 ff ff       	call   2430 <stat@plt>
    4fa6:	83 f8 ff             	cmp    $0xffffffff,%eax
    4fa9:	0f 84 d3 00 00 00    	je     5082 <handle_get_method+0x162>
    4faf:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4fb3:	25 00 f0 00 00       	and    $0xf000,%eax
    4fb8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4fbd:	0f 84 f5 00 00 00    	je     50b8 <handle_get_method+0x198>
    4fc3:	48 8b 3d 46 50 00 00 	mov    0x5046(%rip),%rdi        # a010 <http_404_content>
    4fca:	4c 89 ea             	mov    %r13,%rdx
    4fcd:	44 89 e6             	mov    %r12d,%esi
    4fd0:	e8 db fd ff ff       	call   4db0 <_send_static_string_content>
    4fd5:	4c 89 f2             	mov    %r14,%rdx
    4fd8:	bf 01 00 00 00       	mov    $0x1,%edi
    4fdd:	31 c0                	xor    %eax,%eax
    4fdf:	48 8d 35 61 21 00 00 	lea    0x2161(%rip),%rsi        # 7147 <_IO_stdin_used+0x147>
    4fe6:	e8 c5 d4 ff ff       	call   24b0 <__printf_chk@plt>
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
    5018:	ba 69 63 00 00       	mov    $0x6369,%edx
    501d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5025:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    502a:	48 89 ee             	mov    %rbp,%rsi
    502d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    5035:	48 89 c2             	mov    %rax,%rdx
    5038:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5040:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    504b:	e8 d0 d3 ff ff       	call   2420 <__memcpy_chk@plt>
    5050:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5055:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    505a:	48 8d 35 b1 20 00 00 	lea    0x20b1(%rip),%rsi        # 7112 <_IO_stdin_used+0x112>
    5061:	48 29 d9             	sub    %rbx,%rcx
    5064:	ba 0b 00 00 00       	mov    $0xb,%edx
    5069:	e8 b2 d3 ff ff       	call   2420 <__memcpy_chk@plt>
    506e:	48 89 e6             	mov    %rsp,%rsi
    5071:	4c 89 f7             	mov    %r14,%rdi
    5074:	e8 b7 d3 ff ff       	call   2430 <stat@plt>
    5079:	83 f8 ff             	cmp    $0xffffffff,%eax
    507c:	0f 85 2d ff ff ff    	jne    4faf <handle_get_method+0x8f>
    5082:	4c 89 f2             	mov    %r14,%rdx
    5085:	48 89 e9             	mov    %rbp,%rcx
    5088:	48 8d 35 8e 20 00 00 	lea    0x208e(%rip),%rsi        # 711d <_IO_stdin_used+0x11d>
    508f:	31 c0                	xor    %eax,%eax
    5091:	bf 01 00 00 00       	mov    $0x1,%edi
    5096:	e8 15 d4 ff ff       	call   24b0 <__printf_chk@plt>
    509b:	48 8b 3d 6e 4f 00 00 	mov    0x4f6e(%rip),%rdi        # a010 <http_404_content>
    50a2:	4c 89 ea             	mov    %r13,%rdx
    50a5:	44 89 e6             	mov    %r12d,%esi
    50a8:	e8 03 fd ff ff       	call   4db0 <_send_static_string_content>
    50ad:	e9 39 ff ff ff       	jmp    4feb <handle_get_method+0xcb>
    50b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    50b8:	bf 70 00 00 00       	mov    $0x70,%edi
    50bd:	e8 ae d3 ff ff       	call   2470 <malloc@plt>
    50c2:	48 89 c3             	mov    %rax,%rbx
    50c5:	48 85 c0             	test   %rax,%rax
    50c8:	74 5d                	je     5127 <handle_get_method+0x207>
    50ca:	44 89 60 08          	mov    %r12d,0x8(%rax)
    50ce:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    50d3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    50d7:	4c 89 f7             	mov    %r14,%rdi
    50da:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    50e1:	e8 5a f5 ff ff       	call   4640 <send_headers>
    50e6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    50eb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    50ef:	4c 89 f7             	mov    %r14,%rdi
    50f2:	e8 79 fa ff ff       	call   4b70 <copy_file_contents>
    50f7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    50fc:	4c 89 f2             	mov    %r14,%rdx
    50ff:	31 c0                	xor    %eax,%eax
    5101:	48 8d 35 2d 20 00 00 	lea    0x202d(%rip),%rsi        # 7135 <_IO_stdin_used+0x135>
    5108:	bf 01 00 00 00       	mov    $0x1,%edi
    510d:	e8 9e d3 ff ff       	call   24b0 <__printf_chk@plt>
    5112:	4c 89 ee             	mov    %r13,%rsi
    5115:	48 89 df             	mov    %rbx,%rdi
    5118:	e8 13 fb ff ff       	call   4c30 <add_write_request>
    511d:	e9 c9 fe ff ff       	jmp    4feb <handle_get_method+0xcb>
    5122:	e8 59 d2 ff ff       	call   2380 <__stack_chk_fail@plt>
    5127:	48 8b 0d f2 4e 00 00 	mov    0x4ef2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    512e:	ba 28 00 00 00       	mov    $0x28,%edx
    5133:	be 01 00 00 00       	mov    $0x1,%esi
    5138:	48 8d 3d 69 24 00 00 	lea    0x2469(%rip),%rdi        # 75a8 <_IO_stdin_used+0x5a8>
    513f:	e8 ec d3 ff ff       	call   2530 <fwrite@plt>
    5144:	bf 01 00 00 00       	mov    $0x1,%edi
    5149:	e8 c2 d3 ff ff       	call   2510 <exit@plt>
    514e:	66 90                	xchg   %ax,%ax

0000000000005150 <handle_http_method>:
    5150:	f3 0f 1e fa          	endbr64
    5154:	41 57                	push   %r15
    5156:	41 56                	push   %r14
    5158:	4c 8d 35 4d 1f 00 00 	lea    0x1f4d(%rip),%r14        # 70ac <_IO_stdin_used+0xac>
    515f:	41 55                	push   %r13
    5161:	49 89 d5             	mov    %rdx,%r13
    5164:	41 54                	push   %r12
    5166:	41 89 f4             	mov    %esi,%r12d
    5169:	4c 89 f6             	mov    %r14,%rsi
    516c:	55                   	push   %rbp
    516d:	53                   	push   %rbx
    516e:	48 83 ec 18          	sub    $0x18,%rsp
    5172:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    517b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5180:	31 c0                	xor    %eax,%eax
    5182:	49 89 e7             	mov    %rsp,%r15
    5185:	4c 89 fa             	mov    %r15,%rdx
    5188:	e8 53 d2 ff ff       	call   23e0 <strtok_r@plt>
    518d:	48 0f be 18          	movsbq (%rax),%rbx
    5191:	48 89 c5             	mov    %rax,%rbp
    5194:	84 db                	test   %bl,%bl
    5196:	74 1d                	je     51b5 <handle_http_method+0x65>
    5198:	e8 f3 d3 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    519d:	48 89 ea             	mov    %rbp,%rdx
    51a0:	48 8b 08             	mov    (%rax),%rcx
    51a3:	48 83 c2 01          	add    $0x1,%rdx
    51a7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    51aa:	88 4a ff             	mov    %cl,-0x1(%rdx)
    51ad:	48 0f be 1a          	movsbq (%rdx),%rbx
    51b1:	84 db                	test   %bl,%bl
    51b3:	75 eb                	jne    51a0 <handle_http_method+0x50>
    51b5:	4c 89 fa             	mov    %r15,%rdx
    51b8:	4c 89 f6             	mov    %r14,%rsi
    51bb:	31 ff                	xor    %edi,%edi
    51bd:	e8 1e d2 ff ff       	call   23e0 <strtok_r@plt>
    51c2:	48 8d 35 91 1f 00 00 	lea    0x1f91(%rip),%rsi        # 715a <_IO_stdin_used+0x15a>
    51c9:	48 89 ef             	mov    %rbp,%rdi
    51cc:	48 89 c3             	mov    %rax,%rbx
    51cf:	e8 3c d2 ff ff       	call   2410 <strcmp@plt>
    51d4:	4c 89 ea             	mov    %r13,%rdx
    51d7:	44 89 e6             	mov    %r12d,%esi
    51da:	85 c0                	test   %eax,%eax
    51dc:	75 2a                	jne    5208 <handle_http_method+0xb8>
    51de:	48 89 df             	mov    %rbx,%rdi
    51e1:	e8 3a fd ff ff       	call   4f20 <handle_get_method>
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
    5208:	48 8b 3d 09 4e 00 00 	mov    0x4e09(%rip),%rdi        # a018 <unimplemented_content>
    520f:	e8 9c fb ff ff       	call   4db0 <_send_static_string_content>
    5214:	eb d0                	jmp    51e6 <handle_http_method+0x96>
    5216:	e8 65 d1 ff ff       	call   2380 <__stack_chk_fail@plt>
    521b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005220 <get_line>:
    5220:	f3 0f 1e fa          	endbr64
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
    5245:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5249:	88 06                	mov    %al,(%rsi)
    524b:	3c 0d                	cmp    $0xd,%al
    524d:	75 e9                	jne    5238 <get_line+0x18>
    524f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5252:	75 e4                	jne    5238 <get_line+0x18>
    5254:	c6 06 00             	movb   $0x0,(%rsi)
    5257:	31 c0                	xor    %eax,%eax
    5259:	c3                   	ret
    525a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5260:	b8 01 00 00 00       	mov    $0x1,%eax
    5265:	c3                   	ret
    5266:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005270 <handle_client_request>:
    5270:	f3 0f 1e fa          	endbr64
    5274:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    527b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    527f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5288:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5290:	31 c0                	xor    %eax,%eax
    5292:	49 89 e2             	mov    %rsp,%r10
    5295:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    529d:	4c 89 d0             	mov    %r10,%rax
    52a0:	eb 13                	jmp    52b5 <handle_client_request+0x45>
    52a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    52a8:	48 83 c0 01          	add    $0x1,%rax
    52ac:	48 83 c1 01          	add    $0x1,%rcx
    52b0:	4c 39 c8             	cmp    %r9,%rax
    52b3:	74 4b                	je     5300 <handle_client_request+0x90>
    52b5:	44 0f b6 01          	movzbl (%rcx),%r8d
    52b9:	44 88 00             	mov    %r8b,(%rax)
    52bc:	41 80 f8 0d          	cmp    $0xd,%r8b
    52c0:	75 e6                	jne    52a8 <handle_client_request+0x38>
    52c2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    52c6:	75 e0                	jne    52a8 <handle_client_request+0x38>
    52c8:	c6 00 00             	movb   $0x0,(%rax)
    52cb:	8b 47 08             	mov    0x8(%rdi),%eax
    52ce:	48 89 f2             	mov    %rsi,%rdx
    52d1:	4c 89 d7             	mov    %r10,%rdi
    52d4:	89 c6                	mov    %eax,%esi
    52d6:	e8 75 fe ff ff       	call   5150 <handle_http_method>
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
    5311:	48 8d 3d 46 1e 00 00 	lea    0x1e46(%rip),%rdi        # 715e <_IO_stdin_used+0x15e>
    5318:	e8 13 d2 ff ff       	call   2530 <fwrite@plt>
    531d:	bf 01 00 00 00       	mov    $0x1,%edi
    5322:	e8 e9 d1 ff ff       	call   2510 <exit@plt>
    5327:	e8 54 d0 ff ff       	call   2380 <__stack_chk_fail@plt>
    532c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005330 <add_accept_request>:
    5330:	f3 0f 1e fa          	endbr64
    5334:	55                   	push   %rbp
    5335:	53                   	push   %rbx
    5336:	48 89 cb             	mov    %rcx,%rbx
    5339:	48 83 ec 08          	sub    $0x8,%rsp
    533d:	8b 41 44             	mov    0x44(%rcx),%eax
    5340:	4c 8b 03             	mov    (%rbx),%r8
    5343:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    5349:	83 c0 01             	add    $0x1,%eax
    534c:	45 8b 08             	mov    (%r8),%r9d
    534f:	f6 c1 02             	test   $0x2,%cl
    5352:	74 00                	je     5354 <add_accept_request+0x24>
    5354:	41 89 c0             	mov    %eax,%r8d
    5357:	45 29 c8             	sub    %r9d,%r8d
    535a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    535e:	0f 82 a8 d2 ff ff    	jb     260c <add_accept_request.cold>
    5364:	c1 e9 0a             	shr    $0xa,%ecx
    5367:	8b 6b 44             	mov    0x44(%rbx),%ebp
    536a:	23 6b 58             	and    0x58(%rbx),%ebp
    536d:	89 43 44             	mov    %eax,0x44(%rbx)
    5370:	83 e1 01             	and    $0x1,%ecx
    5373:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5377:	d3 e5                	shl    %cl,%ebp
    5379:	48 c1 e5 06          	shl    $0x6,%rbp
    537d:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5381:	89 7d 04             	mov    %edi,0x4(%rbp)
    5384:	bf 10 00 00 00       	mov    $0x10,%edi
    5389:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    5390:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    5394:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    5398:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    53a0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    53a8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    53ac:	e8 bf d0 ff ff       	call   2470 <malloc@plt>
    53b1:	48 89 df             	mov    %rbx,%rdi
    53b4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    53ba:	48 89 45 20          	mov    %rax,0x20(%rbp)
    53be:	48 83 c4 08          	add    $0x8,%rsp
    53c2:	5b                   	pop    %rbx
    53c3:	5d                   	pop    %rbp
    53c4:	e9 c7 cf ff ff       	jmp    2390 <io_uring_submit@plt>
    53c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000053d0 <io_thread>:
    53d0:	f3 0f 1e fa          	endbr64
    53d4:	41 57                	push   %r15
    53d6:	31 d2                	xor    %edx,%edx
    53d8:	41 56                	push   %r14
    53da:	41 55                	push   %r13
    53dc:	41 54                	push   %r12
    53de:	55                   	push   %rbp
    53df:	48 89 fd             	mov    %rdi,%rbp
    53e2:	53                   	push   %rbx
    53e3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    53ea:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    53f3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    53fb:	48 8b 47 58          	mov    0x58(%rdi),%rax
    53ff:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5404:	bf 00 01 00 00       	mov    $0x100,%edi
    5409:	48 89 de             	mov    %rbx,%rsi
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
    54cc:	e8 7f cf ff ff       	call   2450 <io_uring_queue_init@plt>
    54d1:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    54d5:	31 f6                	xor    %esi,%esi
    54d7:	e8 74 d0 ff ff       	call   2550 <io_uring_register_eventfd@plt>
    54dc:	31 d2                	xor    %edx,%edx
    54de:	be 01 00 00 00       	mov    $0x1,%esi
    54e3:	bf 02 00 00 00       	mov    $0x2,%edi
    54e8:	e8 c3 d0 ff ff       	call   25b0 <socket@plt>
    54ed:	83 f8 ff             	cmp    $0xffffffff,%eax
    54f0:	0f 84 58 d1 ff ff    	je     264e <io_thread.cold+0x38>
    54f6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    54fb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5501:	89 c7                	mov    %eax,%edi
    5503:	41 89 c4             	mov    %eax,%r12d
    5506:	ba 02 00 00 00       	mov    $0x2,%edx
    550b:	be 01 00 00 00       	mov    $0x1,%esi
    5510:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    5518:	e8 23 ce ff ff       	call   2340 <setsockopt@plt>
    551d:	85 c0                	test   %eax,%eax
    551f:	0f 88 fd d0 ff ff    	js     2622 <io_thread.cold+0xc>
    5525:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    552a:	ba 10 00 00 00       	mov    $0x10,%edx
    552f:	44 89 e7             	mov    %r12d,%edi
    5532:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    553b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    5543:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
    554b:	e8 70 cf ff ff       	call   24c0 <bind@plt>
    5550:	85 c0                	test   %eax,%eax
    5552:	0f 88 02 d1 ff ff    	js     265a <io_thread.cold+0x44>
    5558:	be 0a 00 00 00       	mov    $0xa,%esi
    555d:	44 89 e7             	mov    %r12d,%edi
    5560:	e8 1b cf ff ff       	call   2480 <listen@plt>
    5565:	85 c0                	test   %eax,%eax
    5567:	0f 88 c1 d0 ff ff    	js     262e <io_thread.cold+0x18>
    556d:	ba db 18 00 00       	mov    $0x18db,%edx
    5572:	48 8d 35 2a 1c 00 00 	lea    0x1c2a(%rip),%rsi        # 71a3 <_IO_stdin_used+0x1a3>
    5579:	bf 01 00 00 00       	mov    $0x1,%edi
    557e:	31 c0                	xor    %eax,%eax
    5580:	e8 2b cf ff ff       	call   24b0 <__printf_chk@plt>
    5585:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    558a:	48 89 d9             	mov    %rbx,%rcx
    558d:	44 89 e7             	mov    %r12d,%edi
    5590:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5595:	48 89 c6             	mov    %rax,%rsi
    5598:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    559d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    55a2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    55aa:	e8 81 fd ff ff       	call   5330 <add_accept_request>
    55af:	bf 01 00 00 00       	mov    $0x1,%edi
    55b4:	be 10 00 00 00       	mov    $0x10,%esi
    55b9:	e8 42 ce ff ff       	call   2400 <calloc@plt>
    55be:	bf 0a 00 00 00       	mov    $0xa,%edi
    55c3:	49 89 c5             	mov    %rax,%r13
    55c6:	e8 a5 ce ff ff       	call   2470 <malloc@plt>
    55cb:	48 85 c0             	test   %rax,%rax
    55ce:	0f 84 ae 04 00 00    	je     5a82 <io_thread+0x6b2>
    55d4:	49 89 45 00          	mov    %rax,0x0(%r13)
    55d8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    55df:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    55e6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    55ee:	8d 50 01             	lea    0x1(%rax),%edx
    55f1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    55f6:	8b 30                	mov    (%rax),%esi
    55f8:	f6 c1 02             	test   $0x2,%cl
    55fb:	0f 85 0f 04 00 00    	jne    5a10 <io_thread+0x640>
    5601:	89 d0                	mov    %edx,%eax
    5603:	29 f0                	sub    %esi,%eax
    5605:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    560c:	0f 82 32 d0 ff ff    	jb     2644 <io_thread.cold+0x2e>
    5612:	c1 e9 0a             	shr    $0xa,%ecx
    5615:	48 8d 75 60          	lea    0x60(%rbp),%rsi
    5619:	66 0f ef c0          	pxor   %xmm0,%xmm0
    561d:	48 89 df             	mov    %rbx,%rdi
    5620:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5627:	83 e1 01             	and    $0x1,%ecx
    562a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5631:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5638:	d3 e0                	shl    %cl,%eax
    563a:	8b 55 60             	mov    0x60(%rbp),%edx
    563d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5642:	48 c1 e0 06          	shl    $0x6,%rax
    5646:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    564e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5654:	89 50 04             	mov    %edx,0x4(%rax)
    5657:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    565f:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5663:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    566b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5673:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5677:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    567b:	e8 10 cd ff ff       	call   2390 <io_uring_submit@plt>
    5680:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5684:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5689:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5691:	0f 85 d7 01 00 00    	jne    586e <io_thread+0x49e>
    5697:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    569c:	4d 89 ce             	mov    %r9,%r14
    569f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    56a4:	0f 1f 40 00          	nopl   0x0(%rax)
    56a8:	48 8d 3d 0a 1b 00 00 	lea    0x1b0a(%rip),%rdi        # 71b9 <_IO_stdin_used+0x1b9>
    56af:	e8 7c cc ff ff       	call   2330 <puts@plt>
    56b4:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    56bb:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    56c2:	c1 e9 0b             	shr    $0xb,%ecx
    56c5:	83 e1 01             	and    $0x1,%ecx
    56c8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    56d0:	8b 00                	mov    (%rax),%eax
    56d2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    56da:	8b 16                	mov    (%rsi),%edx
    56dc:	39 d0                	cmp    %edx,%eax
    56de:	74 36                	je     5716 <io_thread+0x346>
    56e0:	89 f8                	mov    %edi,%eax
    56e2:	21 d0                	and    %edx,%eax
    56e4:	d3 e0                	shl    %cl,%eax
    56e6:	48 c1 e0 04          	shl    $0x4,%rax
    56ea:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    56f2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    56fa:	0f 85 a8 01 00 00    	jne    58a8 <io_thread+0x4d8>
    5700:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5704:	0f 85 0e 03 00 00    	jne    5a18 <io_thread+0x648>
    570a:	8b 40 08             	mov    0x8(%rax),%eax
    570d:	83 c2 01             	add    $0x1,%edx
    5710:	89 16                	mov    %edx,(%rsi)
    5712:	85 c0                	test   %eax,%eax
    5714:	79 b2                	jns    56c8 <io_thread+0x2f8>
    5716:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    571f:	90                   	nop
    5720:	45 31 c0             	xor    %r8d,%r8d
    5723:	31 d2                	xor    %edx,%edx
    5725:	b9 01 00 00 00       	mov    $0x1,%ecx
    572a:	4c 89 f6             	mov    %r14,%rsi
    572d:	48 89 df             	mov    %rbx,%rdi
    5730:	e8 6b cd ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    5735:	41 89 c7             	mov    %eax,%r15d
    5738:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    573d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5741:	0f 84 e1 02 00 00    	je     5a28 <io_thread+0x658>
    5747:	48 8d 3d 91 1a 00 00 	lea    0x1a91(%rip),%rdi        # 71df <_IO_stdin_used+0x1df>
    574e:	e8 dd cb ff ff       	call   2330 <puts@plt>
    5753:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5758:	4c 8b 22             	mov    (%rdx),%r12
    575b:	45 85 ff             	test   %r15d,%r15d
    575e:	0f 88 b2 ce ff ff    	js     2616 <io_thread.cold>
    5764:	8b 42 08             	mov    0x8(%rdx),%eax
    5767:	45 8b 04 24          	mov    (%r12),%r8d
    576b:	85 c0                	test   %eax,%eax
    576d:	0f 88 d5 02 00 00    	js     5a48 <io_thread+0x678>
    5773:	41 83 f8 01          	cmp    $0x1,%r8d
    5777:	0f 84 7b 01 00 00    	je     58f8 <io_thread+0x528>
    577d:	41 83 f8 02          	cmp    $0x2,%r8d
    5781:	0f 84 a1 01 00 00    	je     5928 <io_thread+0x558>
    5787:	45 85 c0             	test   %r8d,%r8d
    578a:	0f 85 50 01 00 00    	jne    58e0 <io_thread+0x510>
    5790:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5795:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    579a:	48 89 d9             	mov    %rbx,%rcx
    579d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    57a1:	e8 8a fb ff ff       	call   5330 <add_accept_request>
    57a6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    57ab:	48 89 de             	mov    %rbx,%rsi
    57ae:	8b 78 08             	mov    0x8(%rax),%edi
    57b1:	e8 1a f5 ff ff       	call   4cd0 <add_read_request>
    57b6:	4c 89 e7             	mov    %r12,%rdi
    57b9:	e8 42 cb ff ff       	call   2300 <free@plt>
    57be:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    57c3:	48 85 c0             	test   %rax,%rax
    57c6:	0f 85 14 01 00 00    	jne    58e0 <io_thread+0x510>
    57cc:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    57d3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    57da:	8d 50 01             	lea    0x1(%rax),%edx
    57dd:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    57e2:	8b 30                	mov    (%rax),%esi
    57e4:	f6 c1 02             	test   $0x2,%cl
    57e7:	74 00                	je     57e9 <io_thread+0x419>
    57e9:	89 d0                	mov    %edx,%eax
    57eb:	29 f0                	sub    %esi,%eax
    57ed:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    57f4:	0f 82 40 ce ff ff    	jb     263a <io_thread.cold+0x24>
    57fa:	c1 e9 0a             	shr    $0xa,%ecx
    57fd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    5802:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5806:	48 89 df             	mov    %rbx,%rdi
    5809:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5810:	83 e1 01             	and    $0x1,%ecx
    5813:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    581a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5821:	d3 e0                	shl    %cl,%eax
    5823:	8b 55 60             	mov    0x60(%rbp),%edx
    5826:	48 c1 e0 06          	shl    $0x6,%rax
    582a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5832:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5838:	89 50 04             	mov    %edx,0x4(%rax)
    583b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5843:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5847:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    584f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5857:	48 89 70 20          	mov    %rsi,0x20(%rax)
    585b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    585f:	e8 2c cb ff ff       	call   2390 <io_uring_submit@plt>
    5864:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5868:	0f 84 3a fe ff ff    	je     56a8 <io_thread+0x2d8>
    586e:	48 8d 3d a3 19 00 00 	lea    0x19a3(%rip),%rdi        # 7218 <_IO_stdin_used+0x218>
    5875:	e8 b6 ca ff ff       	call   2330 <puts@plt>
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
    58a8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    58ad:	48 85 c0             	test   %rax,%rax
    58b0:	0f 84 6a fe ff ff    	je     5720 <io_thread+0x350>
    58b6:	48 83 38 01          	cmpq   $0x1,(%rax)
    58ba:	0f 84 68 01 00 00    	je     5a28 <io_thread+0x658>
    58c0:	48 8d 3d 18 19 00 00 	lea    0x1918(%rip),%rdi        # 71df <_IO_stdin_used+0x1df>
    58c7:	e8 64 ca ff ff       	call   2330 <puts@plt>
    58cc:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    58d1:	4c 8b 22             	mov    (%rdx),%r12
    58d4:	e9 8b fe ff ff       	jmp    5764 <io_thread+0x394>
    58d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    58e0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    58e8:	8b 02                	mov    (%rdx),%eax
    58ea:	83 c0 01             	add    $0x1,%eax
    58ed:	89 02                	mov    %eax,(%rdx)
    58ef:	e9 d8 fe ff ff       	jmp    57cc <io_thread+0x3fc>
    58f4:	0f 1f 40 00          	nopl   0x0(%rax)
    58f8:	85 c0                	test   %eax,%eax
    58fa:	75 74                	jne    5970 <io_thread+0x5a0>
    58fc:	48 8b 0d 1d 47 00 00 	mov    0x471d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5903:	ba 0f 00 00 00       	mov    $0xf,%edx
    5908:	be 01 00 00 00       	mov    $0x1,%esi
    590d:	48 8d 3d f4 18 00 00 	lea    0x18f4(%rip),%rdi        # 7208 <_IO_stdin_used+0x208>
    5914:	e8 17 cc ff ff       	call   2530 <fwrite@plt>
    5919:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    591e:	e9 a0 fe ff ff       	jmp    57c3 <io_thread+0x3f3>
    5923:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5928:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    592d:	45 31 ff             	xor    %r15d,%r15d
    5930:	85 c0                	test   %eax,%eax
    5932:	7e 20                	jle    5954 <io_thread+0x584>
    5934:	0f 1f 40 00          	nopl   0x0(%rax)
    5938:	4c 89 f8             	mov    %r15,%rax
    593b:	49 83 c7 01          	add    $0x1,%r15
    593f:	48 c1 e0 04          	shl    $0x4,%rax
    5943:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5948:	e8 b3 c9 ff ff       	call   2300 <free@plt>
    594d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5952:	7f e4                	jg     5938 <io_thread+0x568>
    5954:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5959:	e8 72 ca ff ff       	call   23d0 <close@plt>
    595e:	4c 89 e7             	mov    %r12,%rdi
    5961:	e8 9a c9 ff ff       	call   2300 <free@plt>
    5966:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    596b:	e9 53 fe ff ff       	jmp    57c3 <io_thread+0x3f3>
    5970:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5975:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    597a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5982:	eb 11                	jmp    5995 <io_thread+0x5c5>
    5984:	0f 1f 40 00          	nopl   0x0(%rax)
    5988:	48 83 c0 01          	add    $0x1,%rax
    598c:	48 83 c2 01          	add    $0x1,%rdx
    5990:	48 39 c6             	cmp    %rax,%rsi
    5993:	74 4b                	je     59e0 <io_thread+0x610>
    5995:	0f b6 0a             	movzbl (%rdx),%ecx
    5998:	88 08                	mov    %cl,(%rax)
    599a:	80 f9 0d             	cmp    $0xd,%cl
    599d:	75 e9                	jne    5988 <io_thread+0x5b8>
    599f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    59a3:	75 e3                	jne    5988 <io_thread+0x5b8>
    59a5:	c6 00 00             	movb   $0x0,(%rax)
    59a8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    59ad:	48 89 da             	mov    %rbx,%rdx
    59b0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    59b5:	e8 96 f7 ff ff       	call   5150 <handle_http_method>
    59ba:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    59bf:	e8 3c c9 ff ff       	call   2300 <free@plt>
    59c4:	4c 89 e7             	mov    %r12,%rdi
    59c7:	e8 34 c9 ff ff       	call   2300 <free@plt>
    59cc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    59d1:	e9 ed fd ff ff       	jmp    57c3 <io_thread+0x3f3>
    59d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    59e0:	48 8b 0d 39 46 00 00 	mov    0x4639(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    59e7:	ba 12 00 00 00       	mov    $0x12,%edx
    59ec:	be 01 00 00 00       	mov    $0x1,%esi
    59f1:	48 8d 3d 66 17 00 00 	lea    0x1766(%rip),%rdi        # 715e <_IO_stdin_used+0x15e>
    59f8:	e8 33 cb ff ff       	call   2530 <fwrite@plt>
    59fd:	bf 01 00 00 00       	mov    $0x1,%edi
    5a02:	e8 09 cb ff ff       	call   2510 <exit@plt>
    5a07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5a10:	e9 ec fb ff ff       	jmp    5601 <io_thread+0x231>
    5a15:	0f 1f 00             	nopl   (%rax)
    5a18:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    5a1d:	e9 94 fe ff ff       	jmp    58b6 <io_thread+0x4e6>
    5a22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5a28:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5a30:	48 8d 3d 94 17 00 00 	lea    0x1794(%rip),%rdi        # 71cb <_IO_stdin_used+0x1cb>
    5a37:	8b 02                	mov    (%rdx),%eax
    5a39:	83 c0 01             	add    $0x1,%eax
    5a3c:	89 02                	mov    %eax,(%rdx)
    5a3e:	e8 ed c8 ff ff       	call   2330 <puts@plt>
    5a43:	e9 26 fe ff ff       	jmp    586e <io_thread+0x49e>
    5a48:	f7 d8                	neg    %eax
    5a4a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5a4f:	89 c7                	mov    %eax,%edi
    5a51:	e8 1a cb ff ff       	call   2570 <strerror@plt>
    5a56:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5a5b:	be 01 00 00 00       	mov    $0x1,%esi
    5a60:	48 8b 3d b9 45 00 00 	mov    0x45b9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5a67:	48 89 c1             	mov    %rax,%rcx
    5a6a:	48 8d 15 67 1b 00 00 	lea    0x1b67(%rip),%rdx        # 75d8 <_IO_stdin_used+0x5d8>
    5a71:	31 c0                	xor    %eax,%eax
    5a73:	e8 c8 ca ff ff       	call   2540 <__fprintf_chk@plt>
    5a78:	bf 01 00 00 00       	mov    $0x1,%edi
    5a7d:	e8 8e ca ff ff       	call   2510 <exit@plt>
    5a82:	48 8b 0d 97 45 00 00 	mov    0x4597(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5a89:	ba 28 00 00 00       	mov    $0x28,%edx
    5a8e:	be 01 00 00 00       	mov    $0x1,%esi
    5a93:	48 8d 3d 0e 1b 00 00 	lea    0x1b0e(%rip),%rdi        # 75a8 <_IO_stdin_used+0x5a8>
    5a9a:	e8 91 ca ff ff       	call   2530 <fwrite@plt>
    5a9f:	bf 01 00 00 00       	mov    $0x1,%edi
    5aa4:	e8 67 ca ff ff       	call   2510 <exit@plt>
    5aa9:	e8 d2 c8 ff ff       	call   2380 <__stack_chk_fail@plt>
    5aae:	66 90                	xchg   %ax,%ax

0000000000005ab0 <barriered_work_ingest>:
    5ab0:	f3 0f 1e fa          	endbr64
    5ab4:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5abb:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5ac1:	85 c9                	test   %ecx,%ecx
    5ac3:	0f 8e ea 00 00 00    	jle    5bb3 <barriered_work_ingest+0x103>
    5ac9:	41 56                	push   %r14
    5acb:	41 55                	push   %r13
    5acd:	45 31 ed             	xor    %r13d,%r13d
    5ad0:	41 54                	push   %r12
    5ad2:	49 89 fc             	mov    %rdi,%r12
    5ad5:	55                   	push   %rbp
    5ad6:	53                   	push   %rbx
    5ad7:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5adb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5ae0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    5ae4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    5aec:	31 db                	xor    %ebx,%ebx
    5aee:	8b 10                	mov    (%rax),%edx
    5af0:	85 d2                	test   %edx,%edx
    5af2:	7e 26                	jle    5b1a <barriered_work_ingest+0x6a>
    5af4:	48 8b 48 08          	mov    0x8(%rax),%rcx
    5af8:	48 89 dd             	mov    %rbx,%rbp
    5afb:	48 c1 e5 08          	shl    $0x8,%rbp
    5aff:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    5b03:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    5b0a:	74 24                	je     5b30 <barriered_work_ingest+0x80>
    5b0c:	48 83 c3 01          	add    $0x1,%rbx
    5b10:	39 da                	cmp    %ebx,%edx
    5b12:	7f e4                	jg     5af8 <barriered_work_ingest+0x48>
    5b14:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5b1a:	49 83 c5 01          	add    $0x1,%r13
    5b1e:	44 39 e9             	cmp    %r13d,%ecx
    5b21:	7f bd                	jg     5ae0 <barriered_work_ingest+0x30>
    5b23:	5b                   	pop    %rbx
    5b24:	31 c0                	xor    %eax,%eax
    5b26:	5d                   	pop    %rbp
    5b27:	41 5c                	pop    %r12
    5b29:	41 5d                	pop    %r13
    5b2b:	41 5e                	pop    %r14
    5b2d:	c3                   	ret
    5b2e:	66 90                	xchg   %ax,%ax
    5b30:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
    5b39:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5b40:	bf 04 00 00 00       	mov    $0x4,%edi
    5b45:	48 c1 e6 05          	shl    $0x5,%rsi
    5b49:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5b50:	48 83 c6 10          	add    $0x10,%rsi
    5b54:	e8 f7 c7 ff ff       	call   2350 <clock_gettime@plt>
    5b59:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5b61:	48 8b 40 50          	mov    0x50(%rax),%rax
    5b65:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5b69:	48 03 68 08          	add    0x8(%rax),%rbp
    5b6d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
    5b77:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    5b7d:	83 c0 01             	add    $0x1,%eax
    5b80:	99                   	cltd
    5b81:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5b87:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
    5b8d:	0f ae f8             	sfence
    5b90:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5b98:	48 83 c3 01          	add    $0x1,%rbx
    5b9c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5ba0:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5ba4:	8b 10                	mov    (%rax),%edx
    5ba6:	39 da                	cmp    %ebx,%edx
    5ba8:	0f 8f 46 ff ff ff    	jg     5af4 <barriered_work_ingest+0x44>
    5bae:	e9 61 ff ff ff       	jmp    5b14 <barriered_work_ingest+0x64>
    5bb3:	31 c0                	xor    %eax,%eax
    5bb5:	c3                   	ret
    5bb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005bc0 <barriered_thread>:
    5bc0:	f3 0f 1e fa          	endbr64
    5bc4:	41 56                	push   %r14
    5bc6:	41 55                	push   %r13
    5bc8:	41 54                	push   %r12
    5bca:	45 31 e4             	xor    %r12d,%r12d
    5bcd:	55                   	push   %rbp
    5bce:	31 ed                	xor    %ebp,%ebp
    5bd0:	53                   	push   %rbx
    5bd1:	48 89 fb             	mov    %rdi,%rbx
    5bd4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5bd8:	0f 85 74 02 00 00    	jne    5e52 <barriered_thread+0x292>
    5bde:	8b 43 40             	mov    0x40(%rbx),%eax
    5be1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5be8:	41 39 c4             	cmp    %eax,%r12d
    5beb:	0f 8d 6f 01 00 00    	jge    5d60 <barriered_thread+0x1a0>
    5bf1:	49 63 fc             	movslq %r12d,%rdi
    5bf4:	48 c1 e7 09          	shl    $0x9,%rdi
    5bf8:	49 89 fd             	mov    %rdi,%r13
    5bfb:	eb 32                	jmp    5c2f <barriered_thread+0x6f>
    5bfd:	0f 1f 00             	nopl   (%rax)
    5c00:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5c04:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5c08:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5c0c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5c10:	4c 01 ef             	add    %r13,%rdi
    5c13:	e8 98 fe ff ff       	call   5ab0 <barriered_work_ingest>
    5c18:	8b 43 40             	mov    0x40(%rbx),%eax
    5c1b:	41 83 c4 01          	add    $0x1,%r12d
    5c1f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    5c26:	44 39 e0             	cmp    %r12d,%eax
    5c29:	0f 8e 19 02 00 00    	jle    5e48 <barriered_thread+0x288>
    5c2f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5c33:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    5c37:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    5c3e:	75 c0                	jne    5c00 <barriered_thread+0x40>
    5c40:	44 8b 43 28          	mov    0x28(%rbx),%r8d
    5c44:	83 e8 01             	sub    $0x1,%eax
    5c47:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    5c4c:	45 85 e4             	test   %r12d,%r12d
    5c4f:	0f 4f c1             	cmovg  %ecx,%eax
    5c52:	45 85 c0             	test   %r8d,%r8d
    5c55:	0f 8e 2d 01 00 00    	jle    5d88 <barriered_thread+0x1c8>
    5c5b:	48 63 c8             	movslq %eax,%rcx
    5c5e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5c62:	49 63 d0             	movslq %r8d,%rdx
    5c65:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
    5c6b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    5c72:	48 c1 e1 09          	shl    $0x9,%rcx
    5c76:	45 31 d2             	xor    %r10d,%r10d
    5c79:	45 31 f6             	xor    %r14d,%r14d
    5c7c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5c80:	48 8b 10             	mov    (%rax),%rdx
    5c83:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    5c87:	49 01 cb             	add    %rcx,%r11
    5c8a:	4c 89 da             	mov    %r11,%rdx
    5c8d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    5c94:	75 04                	jne    5c9a <barriered_thread+0xda>
    5c96:	41 83 c6 01          	add    $0x1,%r14d
    5c9a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    5ca0:	75 04                	jne    5ca6 <barriered_thread+0xe6>
    5ca2:	41 83 c2 01          	add    $0x1,%r10d
    5ca6:	48 83 c0 08          	add    $0x8,%rax
    5caa:	48 39 c6             	cmp    %rax,%rsi
    5cad:	75 d1                	jne    5c80 <barriered_thread+0xc0>
    5caf:	45 85 d2             	test   %r10d,%r10d
    5cb2:	0f 84 c0 00 00 00    	je     5d78 <barriered_thread+0x1b8>
    5cb8:	45 39 d0             	cmp    %r10d,%r8d
    5cbb:	0f 84 b7 00 00 00    	je     5d78 <barriered_thread+0x1b8>
    5cc1:	45 85 f6             	test   %r14d,%r14d
    5cc4:	74 0a                	je     5cd0 <barriered_thread+0x110>
    5cc6:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    5cca:	0f 85 ae 01 00 00    	jne    5e7e <barriered_thread+0x2be>
    5cd0:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5cd4:	4c 01 ea             	add    %r13,%rdx
    5cd7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
    5cde:	45 85 e4             	test   %r12d,%r12d
    5ce1:	75 14                	jne    5cf7 <barriered_thread+0x137>
    5ce3:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5cea:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5cf1:	0f 8c 69 01 00 00    	jl     5e60 <barriered_thread+0x2a0>
    5cf7:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    5cfb:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5cff:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
    5d09:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    5d0d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5d11:	4c 01 ef             	add    %r13,%rdi
    5d14:	ff 92 18 01 00 00    	call   *0x118(%rdx)
    5d1a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    5d1e:	4c 01 e8             	add    %r13,%rax
    5d21:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
    5d28:	8b 43 40             	mov    0x40(%rbx),%eax
    5d2b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
    5d30:	83 e8 01             	sub    $0x1,%eax
    5d33:	44 39 e0             	cmp    %r12d,%eax
    5d36:	0f 84 a4 00 00 00    	je     5de0 <barriered_thread+0x220>
    5d3c:	0f ae f8             	sfence
    5d3f:	85 ed                	test   %ebp,%ebp
    5d41:	0f 84 d1 00 00 00    	je     5e18 <barriered_thread+0x258>
    5d47:	bd 01 00 00 00       	mov    $0x1,%ebp
    5d4c:	e9 c7 fe ff ff       	jmp    5c18 <barriered_thread+0x58>
    5d51:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5d55:	0f 85 f7 00 00 00    	jne    5e52 <barriered_thread+0x292>
    5d5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5d60:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    5d68:	85 c0                	test   %eax,%eax
    5d6a:	7e e5                	jle    5d51 <barriered_thread+0x191>
    5d6c:	45 31 e4             	xor    %r12d,%r12d
    5d6f:	e9 7d fe ff ff       	jmp    5bf1 <barriered_thread+0x31>
    5d74:	0f 1f 40 00          	nopl   0x0(%rax)
    5d78:	83 fd 01             	cmp    $0x1,%ebp
    5d7b:	74 1b                	je     5d98 <barriered_thread+0x1d8>
    5d7d:	31 ed                	xor    %ebp,%ebp
    5d7f:	e9 3d ff ff ff       	jmp    5cc1 <barriered_thread+0x101>
    5d84:	0f 1f 40 00          	nopl   0x0(%rax)
    5d88:	83 fd 01             	cmp    $0x1,%ebp
    5d8b:	0f 85 43 ff ff ff    	jne    5cd4 <barriered_thread+0x114>
    5d91:	45 31 f6             	xor    %r14d,%r14d
    5d94:	0f 1f 40 00          	nopl   0x0(%rax)
    5d98:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5d9f:	bf 04 00 00 00       	mov    $0x4,%edi
    5da4:	31 ed                	xor    %ebp,%ebp
    5da6:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5daa:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5db1:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    5db6:	e8 95 c5 ff ff       	call   2350 <clock_gettime@plt>
    5dbb:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5dc2:	48 83 c0 01          	add    $0x1,%rax
    5dc6:	48 99                	cqto
    5dc8:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    5dcf:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
    5dd6:	e9 e6 fe ff ff       	jmp    5cc1 <barriered_thread+0x101>
    5ddb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5de0:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5de7:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5dee:	0f 8d 48 ff ff ff    	jge    5d3c <barriered_thread+0x17c>
    5df4:	48 c1 e6 04          	shl    $0x4,%rsi
    5df8:	bf 04 00 00 00       	mov    $0x4,%edi
    5dfd:	48 03 73 70          	add    0x70(%rbx),%rsi
    5e01:	e8 4a c5 ff ff       	call   2350 <clock_gettime@plt>
    5e06:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    5e0e:	e9 29 ff ff ff       	jmp    5d3c <barriered_thread+0x17c>
    5e13:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5e18:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5e1f:	bf 04 00 00 00       	mov    $0x4,%edi
    5e24:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5e28:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5e2f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5e33:	44 89 66 20          	mov    %r12d,0x20(%rsi)
    5e37:	e8 14 c5 ff ff       	call   2350 <clock_gettime@plt>
    5e3c:	e9 06 ff ff ff       	jmp    5d47 <barriered_thread+0x187>
    5e41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5e48:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5e4c:	0f 84 96 fd ff ff    	je     5be8 <barriered_thread+0x28>
    5e52:	5b                   	pop    %rbx
    5e53:	31 c0                	xor    %eax,%eax
    5e55:	5d                   	pop    %rbp
    5e56:	41 5c                	pop    %r12
    5e58:	41 5d                	pop    %r13
    5e5a:	41 5e                	pop    %r14
    5e5c:	c3                   	ret
    5e5d:	0f 1f 00             	nopl   (%rax)
    5e60:	48 c1 e6 04          	shl    $0x4,%rsi
    5e64:	bf 04 00 00 00       	mov    $0x4,%edi
    5e69:	48 03 73 68          	add    0x68(%rbx),%rsi
    5e6d:	e8 de c4 ff ff       	call   2350 <clock_gettime@plt>
    5e72:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5e76:	4c 01 ea             	add    %r13,%rdx
    5e79:	e9 79 fe ff ff       	jmp    5cf7 <barriered_thread+0x137>
    5e7e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5e82:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5e86:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5e8a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5e8e:	4c 01 ef             	add    %r13,%rdi
    5e91:	e8 1a fc ff ff       	call   5ab0 <barriered_work_ingest>
    5e96:	e9 39 fd ff ff       	jmp    5bd4 <barriered_thread+0x14>
    5e9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005ea0 <receive>:
    5ea0:	f3 0f 1e fa          	endbr64
    5ea4:	41 57                	push   %r15
    5ea6:	41 56                	push   %r14
    5ea8:	41 55                	push   %r13
    5eaa:	41 54                	push   %r12
    5eac:	55                   	push   %rbp
    5ead:	53                   	push   %rbx
    5eae:	48 83 ec 08          	sub    $0x8,%rsp
    5eb2:	44 8b b7 40 01 00 00 	mov    0x140(%rdi),%r14d
    5eb9:	45 85 f6             	test   %r14d,%r14d
    5ebc:	0f 8e 37 01 00 00    	jle    5ff9 <receive+0x159>
    5ec2:	4c 8b bf 28 01 00 00 	mov    0x128(%rdi),%r15
    5ec9:	48 89 fe             	mov    %rdi,%rsi
    5ecc:	45 31 e4             	xor    %r12d,%r12d
    5ecf:	31 db                	xor    %ebx,%ebx
    5ed1:	49 63 6f 08          	movslq 0x8(%r15),%rbp
    5ed5:	49 89 ed             	mov    %rbp,%r13
    5ed8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5ee0:	41 39 dd             	cmp    %ebx,%r13d
    5ee3:	0f 84 fd 00 00 00    	je     5fe6 <receive+0x146>
    5ee9:	48 8b 86 70 01 00 00 	mov    0x170(%rsi),%rax
    5ef0:	4a 8b 14 20          	mov    (%rax,%r12,1),%rdx
    5ef4:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    5efa:	83 f8 01             	cmp    $0x1,%eax
    5efd:	74 11                	je     5f10 <receive+0x70>
    5eff:	83 ba 18 03 00 00 02 	cmpl   $0x2,0x318(%rdx)
    5f06:	75 08                	jne    5f10 <receive+0x70>
    5f08:	85 c0                	test   %eax,%eax
    5f0a:	0f 84 d6 00 00 00    	je     5fe6 <receive+0x146>
    5f10:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    5f17:	48 85 ff             	test   %rdi,%rdi
    5f1a:	0f 8e a8 00 00 00    	jle    5fc8 <receive+0x128>
    5f20:	4c 8b 8e 78 01 00 00 	mov    0x178(%rsi),%r9
    5f27:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    5f2e:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    5f32:	4c 8b 1a             	mov    (%rdx),%r11
    5f35:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    5f39:	49 01 f9             	add    %rdi,%r9
    5f3c:	49 01 f8             	add    %rdi,%r8
    5f3f:	48 03 ba 10 03 00 00 	add    0x310(%rdx),%rdi
    5f46:	eb 0e                	jmp    5f56 <receive+0xb6>
    5f48:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5f50:	48 83 e8 01          	sub    $0x1,%rax
    5f54:	72 72                	jb     5fc8 <receive+0x128>
    5f56:	4c 89 c9             	mov    %r9,%rcx
    5f59:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
    5f60:	48 29 c1             	sub    %rax,%rcx
    5f63:	48 89 8e 78 01 00 00 	mov    %rcx,0x178(%rsi)
    5f6a:	4c 89 c1             	mov    %r8,%rcx
    5f6d:	48 29 c1             	sub    %rax,%rcx
    5f70:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
    5f77:	48 89 f9             	mov    %rdi,%rcx
    5f7a:	48 29 c1             	sub    %rax,%rcx
    5f7d:	48 89 8a 10 03 00 00 	mov    %rcx,0x310(%rdx)
    5f84:	48 63 c8             	movslq %eax,%rcx
    5f87:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
    5f8b:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    5f8f:	75 bf                	jne    5f50 <receive+0xb0>
    5f91:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    5f95:	75 b9                	jne    5f50 <receive+0xb0>
    5f97:	49 63 47 04          	movslq 0x4(%r15),%rax
    5f9b:	31 c9                	xor    %ecx,%ecx
    5f9d:	bf 01 00 00 00       	mov    $0x1,%edi
    5fa2:	ba 01 00 00 00       	mov    $0x1,%edx
    5fa7:	48 8d 35 52 16 00 00 	lea    0x1652(%rip),%rsi        # 7600 <_IO_stdin_used+0x600>
    5fae:	48 39 e8             	cmp    %rbp,%rax
    5fb1:	0f 94 c1             	sete   %cl
    5fb4:	31 c0                	xor    %eax,%eax
    5fb6:	e8 f5 c4 ff ff       	call   24b0 <__printf_chk@plt>
    5fbb:	bf 01 00 00 00       	mov    $0x1,%edi
    5fc0:	e8 4b c5 ff ff       	call   2510 <exit@plt>
    5fc5:	0f 1f 00             	nopl   (%rax)
    5fc8:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
    5fd2:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
    5fdc:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
    5fe6:	83 c3 01             	add    $0x1,%ebx
    5fe9:	49 81 c4 80 01 00 00 	add    $0x180,%r12
    5ff0:	44 39 f3             	cmp    %r14d,%ebx
    5ff3:	0f 85 e7 fe ff ff    	jne    5ee0 <receive+0x40>
    5ff9:	0f ae f8             	sfence
    5ffc:	48 83 c4 08          	add    $0x8,%rsp
    6000:	31 c0                	xor    %eax,%eax
    6002:	5b                   	pop    %rbx
    6003:	5d                   	pop    %rbp
    6004:	41 5c                	pop    %r12
    6006:	41 5d                	pop    %r13
    6008:	41 5e                	pop    %r14
    600a:	41 5f                	pop    %r15
    600c:	c3                   	ret
    600d:	0f 1f 00             	nopl   (%rax)

0000000000006010 <sendm>:
    6010:	f3 0f 1e fa          	endbr64
    6014:	41 57                	push   %r15
    6016:	41 56                	push   %r14
    6018:	41 55                	push   %r13
    601a:	41 54                	push   %r12
    601c:	55                   	push   %rbp
    601d:	53                   	push   %rbx
    601e:	8b af 40 01 00 00    	mov    0x140(%rdi),%ebp
    6024:	85 ed                	test   %ebp,%ebp
    6026:	0f 8e a6 00 00 00    	jle    60d2 <sendm+0xc2>
    602c:	4c 8b a7 28 01 00 00 	mov    0x128(%rdi),%r12
    6033:	49 89 ff             	mov    %rdi,%r15
    6036:	31 c9                	xor    %ecx,%ecx
    6038:	31 c0                	xor    %eax,%eax
    603a:	45 8b 6c 24 08       	mov    0x8(%r12),%r13d
    603f:	90                   	nop
    6040:	41 39 c5             	cmp    %eax,%r13d
    6043:	74 7b                	je     60c0 <sendm+0xb0>
    6045:	49 8b 97 70 01 00 00 	mov    0x170(%r15),%rdx
    604c:	48 01 ca             	add    %rcx,%rdx
    604f:	48 8b 9a 00 01 00 00 	mov    0x100(%rdx),%rbx
    6056:	48 8b b2 80 00 00 00 	mov    0x80(%rdx),%rsi
    605d:	48 8d 7b 01          	lea    0x1(%rbx),%rdi
    6061:	48 89 ba 00 01 00 00 	mov    %rdi,0x100(%rdx)
    6068:	48 83 ff 09          	cmp    $0x9,%rdi
    606c:	7e 52                	jle    60c0 <sendm+0xb0>
    606e:	48 8b be 80 00 00 00 	mov    0x80(%rsi),%rdi
    6075:	48 85 ff             	test   %rdi,%rdi
    6078:	7f 46                	jg     60c0 <sendm+0xb0>
    607a:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
    6081:	41 83 f8 01          	cmp    $0x1,%r8d
    6085:	74 0e                	je     6095 <sendm+0x85>
    6087:	83 be 18 03 00 00 02 	cmpl   $0x2,0x318(%rsi)
    608e:	75 05                	jne    6095 <sendm+0x85>
    6090:	45 85 c0             	test   %r8d,%r8d
    6093:	74 2b                	je     60c0 <sendm+0xb0>
    6095:	41 83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%r15)
    609d:	74 49                	je     60e8 <sendm+0xd8>
    609f:	83 ba b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx)
    60a6:	75 18                	jne    60c0 <sendm+0xb0>
    60a8:	48 c7 82 00 01 00 00 00 00 00 00 	movq   $0x0,0x100(%rdx)
    60b3:	41 c7 84 24 d8 00 00 00 01 00 00 00 	movl   $0x1,0xd8(%r12)
    60bf:	90                   	nop
    60c0:	83 c0 01             	add    $0x1,%eax
    60c3:	48 81 c1 80 01 00 00 	add    $0x180,%rcx
    60ca:	39 e8                	cmp    %ebp,%eax
    60cc:	0f 85 6e ff ff ff    	jne    6040 <sendm+0x30>
    60d2:	0f ae f8             	sfence
    60d5:	31 c0                	xor    %eax,%eax
    60d7:	5b                   	pop    %rbx
    60d8:	5d                   	pop    %rbp
    60d9:	41 5c                	pop    %r12
    60db:	41 5d                	pop    %r13
    60dd:	41 5e                	pop    %r14
    60df:	41 5f                	pop    %r15
    60e1:	c3                   	ret
    60e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    60e8:	4c 63 9e 88 00 00 00 	movslq 0x88(%rsi),%r11
    60ef:	4c 39 df             	cmp    %r11,%rdi
    60f2:	0f 8d c2 00 00 00    	jge    61ba <sendm+0x1aa>
    60f8:	49 8b 9f 08 01 00 00 	mov    0x108(%r15),%rbx
    60ff:	4d 89 de             	mov    %r11,%r14
    6102:	4c 8b 16             	mov    (%rsi),%r10
    6105:	49 29 fe             	sub    %rdi,%r14
    6108:	48 89 5c 24 d8       	mov    %rbx,-0x28(%rsp)
    610d:	48 8b 9e 08 03 00 00 	mov    0x308(%rsi),%rbx
    6114:	4d 8d 46 ff          	lea    -0x1(%r14),%r8
    6118:	48 89 5c 24 e0       	mov    %rbx,-0x20(%rsp)
    611d:	49 83 f8 02          	cmp    $0x2,%r8
    6121:	0f 86 39 01 00 00    	jbe    6260 <sendm+0x250>
    6127:	48 8d 1c fd 00 00 00 00 	lea    0x0(,%rdi,8),%rbx
    612f:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    6137:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    613c:	4c 01 d3             	add    %r10,%rbx
    613f:	4d 8d 87 88 01 00 00 	lea    0x188(%r15),%r8
    6146:	48 89 5c 24 d0       	mov    %rbx,-0x30(%rsp)
    614b:	4b 8d 1c 0a          	lea    (%r10,%r9,1),%rbx
    614f:	49 39 d8             	cmp    %rbx,%r8
    6152:	0f 83 88 00 00 00    	jae    61e0 <sendm+0x1d0>
    6158:	49 8d 9f 90 01 00 00 	lea    0x190(%r15),%rbx
    615f:	48 39 5c 24 d0       	cmp    %rbx,-0x30(%rsp)
    6164:	73 7a                	jae    61e0 <sendm+0x1d0>
    6166:	4c 8b 44 24 e8       	mov    -0x18(%rsp),%r8
    616b:	4b 8d 3c 0a          	lea    (%r10,%r9,1),%rdi
    616f:	4d 01 d0             	add    %r10,%r8
    6172:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6178:	4d 8b 8f 88 01 00 00 	mov    0x188(%r15),%r9
    617f:	49 83 c0 08          	add    $0x8,%r8
    6183:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
    6187:	4c 39 c7             	cmp    %r8,%rdi
    618a:	75 ec                	jne    6178 <sendm+0x168>
    618c:	0f 1f 40 00          	nopl   0x0(%rax)
    6190:	48 8b 7c 24 d8       	mov    -0x28(%rsp),%rdi
    6195:	4c 01 f7             	add    %r14,%rdi
    6198:	49 89 bf 08 01 00 00 	mov    %rdi,0x108(%r15)
    619f:	48 8b 7c 24 e0       	mov    -0x20(%rsp),%rdi
    61a4:	4c 89 9e 80 00 00 00 	mov    %r11,0x80(%rsi)
    61ab:	4c 01 f7             	add    %r14,%rdi
    61ae:	48 89 be 08 03 00 00 	mov    %rdi,0x308(%rsi)
    61b5:	4f 89 4c da f8       	mov    %r9,-0x8(%r10,%r11,8)
    61ba:	c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rsi)
    61c4:	c7 86 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rsi)
    61ce:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
    61d8:	e9 c2 fe ff ff       	jmp    609f <sendm+0x8f>
    61dd:	0f 1f 00             	nopl   (%rax)
    61e0:	4c 89 f3             	mov    %r14,%rbx
    61e3:	4c 8b 44 24 d0       	mov    -0x30(%rsp),%r8
    61e8:	4d 8b 8f 88 01 00 00 	mov    0x188(%r15),%r9
    61ef:	48 d1 eb             	shr    %rbx
    61f2:	48 c1 e3 04          	shl    $0x4,%rbx
    61f6:	66 49 0f 6e c1       	movq   %r9,%xmm0
    61fb:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    6200:	4c 01 c3             	add    %r8,%rbx
    6203:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    6207:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    620c:	48 8b 5c 24 e8       	mov    -0x18(%rsp),%rbx
    6211:	83 e3 10             	and    $0x10,%ebx
    6214:	75 64                	jne    627a <sendm+0x26a>
    6216:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    621b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6220:	41 0f 11 00          	movups %xmm0,(%r8)
    6224:	49 83 c0 20          	add    $0x20,%r8
    6228:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
    622d:	49 39 d8             	cmp    %rbx,%r8
    6230:	75 ee                	jne    6220 <sendm+0x210>
    6232:	4d 89 f0             	mov    %r14,%r8
    6235:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    6239:	49 01 f8             	add    %rdi,%r8
    623c:	41 f6 c6 01          	test   $0x1,%r14b
    6240:	0f 84 4a ff ff ff    	je     6190 <sendm+0x180>
    6246:	4d 8b 8f 88 01 00 00 	mov    0x188(%r15),%r9
    624d:	4f 89 0c c2          	mov    %r9,(%r10,%r8,8)
    6251:	e9 3a ff ff ff       	jmp    6190 <sendm+0x180>
    6256:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6260:	48 8d 1c fd 00 00 00 00 	lea    0x0(,%rdi,8),%rbx
    6268:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    6270:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    6275:	e9 ec fe ff ff       	jmp    6166 <sendm+0x156>
    627a:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    627f:	41 0f 11 00          	movups %xmm0,(%r8)
    6283:	49 83 c0 10          	add    $0x10,%r8
    6287:	49 39 d8             	cmp    %rbx,%r8
    628a:	75 94                	jne    6220 <sendm+0x210>
    628c:	eb a4                	jmp    6232 <sendm+0x222>
    628e:	66 90                	xchg   %ax,%ax

0000000000006290 <barriered_work>:
    6290:	f3 0f 1e fa          	endbr64
    6294:	41 57                	push   %r15
    6296:	41 56                	push   %r14
    6298:	41 55                	push   %r13
    629a:	41 54                	push   %r12
    629c:	55                   	push   %rbp
    629d:	53                   	push   %rbx
    629e:	48 89 fb             	mov    %rdi,%rbx
    62a1:	48 83 ec 58          	sub    $0x58,%rsp
    62a5:	44 8b 67 04          	mov    0x4(%rdi),%r12d
    62a9:	44 39 a7 30 01 00 00 	cmp    %r12d,0x130(%rdi)
    62b0:	74 5e                	je     6310 <barriered_work+0x80>
    62b2:	e8 e9 fb ff ff       	call   5ea0 <receive>
    62b7:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    62be:	75 14                	jne    62d4 <barriered_work+0x44>
    62c0:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    62c8:	0f ae f8             	sfence
    62cb:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    62d2:	74 ec                	je     62c0 <barriered_work+0x30>
    62d4:	48 89 df             	mov    %rbx,%rdi
    62d7:	e8 34 fd ff ff       	call   6010 <sendm>
    62dc:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    62e2:	83 e8 01             	sub    $0x1,%eax
    62e5:	44 39 e0             	cmp    %r12d,%eax
    62e8:	0f 84 82 01 00 00    	je     6470 <barriered_work+0x1e0>
    62ee:	c7 83 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%rbx)
    62f8:	0f ae f8             	sfence
    62fb:	48 83 c4 58          	add    $0x58,%rsp
    62ff:	31 c0                	xor    %eax,%eax
    6301:	5b                   	pop    %rbx
    6302:	5d                   	pop    %rbp
    6303:	41 5c                	pop    %r12
    6305:	41 5d                	pop    %r13
    6307:	41 5e                	pop    %r14
    6309:	41 5f                	pop    %r15
    630b:	c3                   	ret
    630c:	0f 1f 40 00          	nopl   0x0(%rax)
    6310:	e8 8b fb ff ff       	call   5ea0 <receive>
    6315:	4c 8b ab 28 01 00 00 	mov    0x128(%rbx),%r13
    631c:	41 83 bd d8 00 00 00 01 	cmpl   $0x1,0xd8(%r13)
    6324:	0f 84 a6 02 00 00    	je     65d0 <barriered_work+0x340>
    632a:	49 63 85 c4 00 00 00 	movslq 0xc4(%r13),%rax
    6331:	8b 8b 94 01 00 00    	mov    0x194(%rbx),%ecx
    6337:	8b 93 30 01 00 00    	mov    0x130(%rbx),%edx
    633d:	0f af c8             	imul   %eax,%ecx
    6340:	01 ca                	add    %ecx,%edx
    6342:	85 c0                	test   %eax,%eax
    6344:	0f 8e a6 01 00 00    	jle    64f0 <barriered_work+0x260>
    634a:	48 63 d2             	movslq %edx,%rdx
    634d:	4d 8b 55 20          	mov    0x20(%r13),%r10
    6351:	44 8b 83 34 01 00 00 	mov    0x134(%rbx),%r8d
    6358:	48 8d 34 d5 00 00 00 00 	lea    0x0(,%rdx,8),%rsi
    6360:	4c 8d 1c 52          	lea    (%rdx,%rdx,2),%r11
    6364:	48 29 d6             	sub    %rdx,%rsi
    6367:	48 63 d1             	movslq %ecx,%rdx
    636a:	49 c1 e3 07          	shl    $0x7,%r11
    636e:	48 c1 e6 05          	shl    $0x5,%rsi
    6372:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    637a:	48 01 d0             	add    %rdx,%rax
    637d:	49 8b 6c 32 38       	mov    0x38(%r10,%rsi,1),%rbp
    6382:	49 63 f4             	movslq %r12d,%rsi
    6385:	48 29 d1             	sub    %rdx,%rcx
    6388:	4c 8d 2c 40          	lea    (%rax,%rax,2),%r13
    638c:	48 c1 e6 09          	shl    $0x9,%rsi
    6390:	48 c1 e1 05          	shl    $0x5,%rcx
    6394:	4c 8b b4 35 70 01 00 00 	mov    0x170(%rbp,%rsi,1),%r14
    639c:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
    63a0:	49 01 ca             	add    %rcx,%r10
    63a3:	49 c1 e5 07          	shl    $0x7,%r13
    63a7:	48 c1 e6 07          	shl    $0x7,%rsi
    63ab:	eb 1a                	jmp    63c7 <barriered_work+0x137>
    63ad:	0f 1f 00             	nopl   (%rax)
    63b0:	48 81 c6 80 01 00 00 	add    $0x180,%rsi
    63b7:	49 81 c2 e0 00 00 00 	add    $0xe0,%r10
    63be:	49 39 f5             	cmp    %rsi,%r13
    63c1:	0f 84 29 01 00 00    	je     64f0 <barriered_work+0x260>
    63c7:	41 83 bc 36 b0 00 00 00 01 	cmpl   $0x1,0xb0(%r14,%rsi,1)
    63d0:	75 de                	jne    63b0 <barriered_work+0x120>
    63d2:	49 8b 7a 38          	mov    0x38(%r10),%rdi
    63d6:	45 85 c0             	test   %r8d,%r8d
    63d9:	7e d5                	jle    63b0 <barriered_work+0x120>
    63db:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    63e0:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    63e7:	31 c9                	xor    %ecx,%ecx
    63e9:	eb 55                	jmp    6440 <barriered_work+0x1b0>
    63eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    63f0:	48 63 d2             	movslq %edx,%rdx
    63f3:	48 c1 e2 09          	shl    $0x9,%rdx
    63f7:	4c 8b bc 15 70 01 00 00 	mov    0x170(%rbp,%rdx,1),%r15
    63ff:	49 01 f7             	add    %rsi,%r15
    6402:	4c 89 fa             	mov    %r15,%rdx
    6405:	4d 8b 3f             	mov    (%r15),%r15
    6408:	49 83 bf 80 00 00 00 00 	cmpq   $0x0,0x80(%r15)
    6410:	75 22                	jne    6434 <barriered_work+0x1a4>
    6412:	4c 8b 90 80 00 00 00 	mov    0x80(%rax),%r10
    6419:	4c 89 12             	mov    %r10,(%rdx)
    641c:	4c 8b 92 80 00 00 00 	mov    0x80(%rdx),%r10
    6423:	4c 89 b8 80 00 00 00 	mov    %r15,0x80(%rax)
    642a:	4c 89 10             	mov    %r10,(%rax)
    642d:	4c 89 8a 80 00 00 00 	mov    %r9,0x80(%rdx)
    6434:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    643b:	41 39 c8             	cmp    %ecx,%r8d
    643e:	74 1c                	je     645c <barriered_work+0x1cc>
    6440:	83 c1 01             	add    $0x1,%ecx
    6443:	89 c8                	mov    %ecx,%eax
    6445:	99                   	cltd
    6446:	41 f7 f8             	idiv   %r8d
    6449:	48 8b 07             	mov    (%rdi),%rax
    644c:	4c 01 d8             	add    %r11,%rax
    644f:	4c 8b 08             	mov    (%rax),%r9
    6452:	49 83 b9 80 00 00 00 00 	cmpq   $0x0,0x80(%r9)
    645a:	74 94                	je     63f0 <barriered_work+0x160>
    645c:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    6461:	e9 4a ff ff ff       	jmp    63b0 <barriered_work+0x120>
    6466:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6470:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    6477:	85 d2                	test   %edx,%edx
    6479:	0f 8e 6f fe ff ff    	jle    62ee <barriered_work+0x5e>
    647f:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    6486:	48 c1 e2 09          	shl    $0x9,%rdx
    648a:	48 63 71 08          	movslq 0x8(%rcx),%rsi
    648e:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
    6496:	48 29 f0             	sub    %rsi,%rax
    6499:	48 c1 e0 05          	shl    $0x5,%rax
    649d:	48 03 41 20          	add    0x20(%rcx),%rax
    64a1:	48 8b 40 38          	mov    0x38(%rax),%rax
    64a5:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    64a9:	80 e6 02             	and    $0x2,%dh
    64ac:	74 1a                	je     64c8 <barriered_work+0x238>
    64ae:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
    64b5:	48 05 00 02 00 00    	add    $0x200,%rax
    64bb:	48 39 c8             	cmp    %rcx,%rax
    64be:	0f 84 2a fe ff ff    	je     62ee <barriered_work+0x5e>
    64c4:	0f 1f 40 00          	nopl   0x0(%rax)
    64c8:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
    64cf:	83 80 9c 03 00 00 01 	addl   $0x1,0x39c(%rax)
    64d6:	48 05 00 04 00 00    	add    $0x400,%rax
    64dc:	48 39 c8             	cmp    %rcx,%rax
    64df:	75 e7                	jne    64c8 <barriered_work+0x238>
    64e1:	e9 08 fe ff ff       	jmp    62ee <barriered_work+0x5e>
    64e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    64f0:	48 89 df             	mov    %rbx,%rdi
    64f3:	e8 a8 f9 ff ff       	call   5ea0 <receive>
    64f8:	0f ae f8             	sfence
    64fb:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6502:	31 ff                	xor    %edi,%edi
    6504:	48 c1 e6 05          	shl    $0x5,%rsi
    6508:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    650f:	e8 3c be ff ff       	call   2350 <clock_gettime@plt>
    6514:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    651b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6522:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6526:	8b 4a 10             	mov    0x10(%rdx),%ecx
    6529:	8d 69 01             	lea    0x1(%rcx),%ebp
    652c:	89 6a 10             	mov    %ebp,0x10(%rdx)
    652f:	75 58                	jne    6589 <barriered_work+0x2f9>
    6531:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6538:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    653f:	48 8b 40 18          	mov    0x18(%rax),%rax
    6543:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
    6547:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    654f:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6553:	48 c1 e7 09          	shl    $0x9,%rdi
    6557:	48 03 78 38          	add    0x38(%rax),%rdi
    655b:	ff 93 20 01 00 00    	call   *0x120(%rbx)
    6561:	0f ae f8             	sfence
    6564:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    656b:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6572:	74 c4                	je     6538 <barriered_work+0x2a8>
    6574:	48 8b 40 48          	mov    0x48(%rax),%rax
    6578:	3b 68 10             	cmp    0x10(%rax),%ebp
    657b:	74 0c                	je     6589 <barriered_work+0x2f9>
    657d:	48 8d 3d c2 0c 00 00 	lea    0xcc2(%rip),%rdi        # 7246 <_IO_stdin_used+0x246>
    6584:	e8 a7 bd ff ff       	call   2330 <puts@plt>
    6589:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6590:	31 ff                	xor    %edi,%edi
    6592:	48 c1 e6 05          	shl    $0x5,%rsi
    6596:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    659d:	48 83 c6 10          	add    $0x10,%rsi
    65a1:	e8 aa bd ff ff       	call   2350 <clock_gettime@plt>
    65a6:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    65ad:	48 83 c0 01          	add    $0x1,%rax
    65b1:	48 99                	cqto
    65b3:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    65ba:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    65c1:	e9 16 fd ff ff       	jmp    62dc <barriered_work+0x4c>
    65c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    65d0:	44 8b bb 40 01 00 00 	mov    0x140(%rbx),%r15d
    65d7:	41 c7 85 d8 00 00 00 00 00 00 00 	movl   $0x0,0xd8(%r13)
    65e2:	45 85 ff             	test   %r15d,%r15d
    65e5:	0f 8e 3f fd ff ff    	jle    632a <barriered_work+0x9a>
    65eb:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    65f1:	41 8b 55 08          	mov    0x8(%r13),%edx
    65f5:	31 f6                	xor    %esi,%esi
    65f7:	45 31 c0             	xor    %r8d,%r8d
    65fa:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
    6602:	89 44 24 24          	mov    %eax,0x24(%rsp)
    6606:	49 63 c4             	movslq %r12d,%rax
    6609:	41 89 d3             	mov    %edx,%r11d
    660c:	48 c1 e0 09          	shl    $0x9,%rax
    6610:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
    6615:	49 89 c6             	mov    %rax,%r14
    6618:	48 63 c2             	movslq %edx,%rax
    661b:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    6623:	48 29 c1             	sub    %rax,%rcx
    6626:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    662a:	48 c1 e1 05          	shl    $0x5,%rcx
    662e:	48 c1 e0 07          	shl    $0x7,%rax
    6632:	48 89 cd             	mov    %rcx,%rbp
    6635:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    663a:	48 89 d9             	mov    %rbx,%rcx
    663d:	eb 21                	jmp    6660 <barriered_work+0x3d0>
    663f:	90                   	nop
    6640:	83 44 24 08 01       	addl   $0x1,0x8(%rsp)
    6645:	8b 44 24 08          	mov    0x8(%rsp),%eax
    6649:	49 81 c0 80 01 00 00 	add    $0x180,%r8
    6650:	48 81 c6 e0 00 00 00 	add    $0xe0,%rsi
    6657:	44 39 f8             	cmp    %r15d,%eax
    665a:	0f 84 f0 01 00 00    	je     6850 <barriered_work+0x5c0>
    6660:	8b 44 24 08          	mov    0x8(%rsp),%eax
    6664:	41 39 c3             	cmp    %eax,%r11d
    6667:	74 d7                	je     6640 <barriered_work+0x3b0>
    6669:	49 8b 55 20          	mov    0x20(%r13),%rdx
    666d:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    6672:	4a 8d 04 37          	lea    (%rdi,%r14,1),%rax
    6676:	44 8b 88 98 01 00 00 	mov    0x198(%rax),%r9d
    667d:	45 85 c9             	test   %r9d,%r9d
    6680:	75 be                	jne    6640 <barriered_work+0x3b0>
    6682:	4c 8b 4c 2a 38       	mov    0x38(%rdx,%rbp,1),%r9
    6687:	4b 8d 14 31          	lea    (%r9,%r14,1),%rdx
    668b:	44 8b 92 98 01 00 00 	mov    0x198(%rdx),%r10d
    6692:	45 85 d2             	test   %r10d,%r10d
    6695:	75 a9                	jne    6640 <barriered_work+0x3b0>
    6697:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    669e:	42 83 bc 02 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r8,1)
    66a7:	75 97                	jne    6640 <barriered_work+0x3b0>
    66a9:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    66b0:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    66b5:	83 bc 18 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rbx,1)
    66bd:	75 81                	jne    6640 <barriered_work+0x3b0>
    66bf:	8b 54 24 24          	mov    0x24(%rsp),%edx
    66c3:	85 d2                	test   %edx,%edx
    66c5:	0f 8e 75 ff ff ff    	jle    6640 <barriered_work+0x3b0>
    66cb:	48 63 c2             	movslq %edx,%rax
    66ce:	4c 89 74 24 30       	mov    %r14,0x30(%rsp)
    66d3:	48 c1 e0 09          	shl    $0x9,%rax
    66d7:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    66dc:	48 89 74 24 40       	mov    %rsi,0x40(%rsp)
    66e1:	48 89 c3             	mov    %rax,%rbx
    66e4:	4c 8d a0 98 01 00 00 	lea    0x198(%rax),%r12
    66eb:	b8 70 01 00 00       	mov    $0x170,%eax
    66f0:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    66f5:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    66fa:	44 89 5c 24 38       	mov    %r11d,0x38(%rsp)
    66ff:	49 89 c3             	mov    %rax,%r11
    6702:	48 89 5c 24 48       	mov    %rbx,0x48(%rsp)
    6707:	89 d3                	mov    %edx,%ebx
    6709:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6710:	41 83 c2 01          	add    $0x1,%r10d
    6714:	4b 8b 34 19          	mov    (%r9,%r11,1),%rsi
    6718:	44 89 d0             	mov    %r10d,%eax
    671b:	99                   	cltd
    671c:	4c 01 c6             	add    %r8,%rsi
    671f:	f7 fb                	idiv   %ebx
    6721:	4c 8b 36             	mov    (%rsi),%r14
    6724:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
    6729:	4c 8b b6 80 00 00 00 	mov    0x80(%rsi),%r14
    6730:	48 63 d2             	movslq %edx,%rdx
    6733:	48 c1 e2 09          	shl    $0x9,%rdx
    6737:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    673f:	4c 01 e8             	add    %r13,%rax
    6742:	4c 8b 38             	mov    (%rax),%r15
    6745:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    674c:	4c 89 30             	mov    %r14,(%rax)
    674f:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    6754:	4c 89 b0 80 00 00 00 	mov    %r14,0x80(%rax)
    675b:	48 89 16             	mov    %rdx,(%rsi)
    675e:	4c 89 be 80 00 00 00 	mov    %r15,0x80(%rsi)
    6765:	be 98 01 00 00       	mov    $0x198,%esi
    676a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6770:	41 c7 04 31 01 00 00 00 	movl   $0x1,(%r9,%rsi,1)
    6778:	c7 04 37 01 00 00 00 	movl   $0x1,(%rdi,%rsi,1)
    677f:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    6786:	49 39 f4             	cmp    %rsi,%r12
    6789:	75 e5                	jne    6770 <barriered_work+0x4e0>
    678b:	4a 8b 34 1f          	mov    (%rdi,%r11,1),%rsi
    678f:	48 8b 00             	mov    (%rax),%rax
    6792:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
    679d:	49 81 c3 00 02 00 00 	add    $0x200,%r11
    67a4:	4a 8b b4 2e 80 00 00 00 	mov    0x80(%rsi,%r13,1),%rsi
    67ac:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
    67b6:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
    67c0:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    67ca:	44 39 d3             	cmp    %r10d,%ebx
    67cd:	0f 85 3d ff ff ff    	jne    6710 <barriered_work+0x480>
    67d3:	48 8b 5c 24 48       	mov    0x48(%rsp),%rbx
    67d8:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    67dd:	b8 70 01 00 00       	mov    $0x170,%eax
    67e2:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    67e7:	44 8b 5c 24 38       	mov    0x38(%rsp),%r11d
    67ec:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
    67f1:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    67f6:	48 81 c3 70 01 00 00 	add    $0x170,%rbx
    67fd:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    6802:	eb 13                	jmp    6817 <barriered_work+0x587>
    6804:	0f 1f 40 00          	nopl   0x0(%rax)
    6808:	48 05 00 02 00 00    	add    $0x200,%rax
    680e:	48 39 c3             	cmp    %rax,%rbx
    6811:	0f 84 29 fe ff ff    	je     6640 <barriered_work+0x3b0>
    6817:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    681b:	4d 8b 14 01          	mov    (%r9,%rax,1),%r10
    681f:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    6823:	4b 39 14 02          	cmp    %rdx,(%r10,%r8,1)
    6827:	75 df                	jne    6808 <barriered_work+0x578>
    6829:	bf 01 00 00 00       	mov    $0x1,%edi
    682e:	48 8d 35 f6 09 00 00 	lea    0x9f6(%rip),%rsi        # 722b <_IO_stdin_used+0x22b>
    6835:	31 c0                	xor    %eax,%eax
    6837:	e8 74 bc ff ff       	call   24b0 <__printf_chk@plt>
    683c:	bf 01 00 00 00       	mov    $0x1,%edi
    6841:	e8 ca bc ff ff       	call   2510 <exit@plt>
    6846:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6850:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    6855:	48 89 cb             	mov    %rcx,%rbx
    6858:	e9 cd fa ff ff       	jmp    632a <barriered_work+0x9a>
    685d:	0f 1f 00             	nopl   (%rax)

0000000000006860 <barriered_work_ingest_andwork>:
    6860:	f3 0f 1e fa          	endbr64
    6864:	53                   	push   %rbx
    6865:	48 89 fb             	mov    %rdi,%rbx
    6868:	e8 43 f2 ff ff       	call   5ab0 <barriered_work_ingest>
    686d:	48 89 df             	mov    %rbx,%rdi
    6870:	5b                   	pop    %rbx
    6871:	e9 1a fa ff ff       	jmp    6290 <barriered_work>
    6876:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006880 <mailboxkind>:
    6880:	f3 0f 1e fa          	endbr64
    6884:	85 f6                	test   %esi,%esi
    6886:	74 18                	je     68a0 <mailboxkind+0x20>
    6888:	31 c0                	xor    %eax,%eax
    688a:	83 fe 01             	cmp    $0x1,%esi
    688d:	74 01                	je     6890 <mailboxkind+0x10>
    688f:	c3                   	ret
    6890:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
    6897:	c3                   	ret
    6898:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    68a0:	48 8b 07             	mov    (%rdi),%rax
    68a3:	c3                   	ret
    68a4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    68af:	90                   	nop

00000000000068b0 <setmailboxkind>:
    68b0:	f3 0f 1e fa          	endbr64
    68b4:	85 d2                	test   %edx,%edx
    68b6:	75 08                	jne    68c0 <setmailboxkind+0x10>
    68b8:	48 89 37             	mov    %rsi,(%rdi)
    68bb:	31 c0                	xor    %eax,%eax
    68bd:	c3                   	ret
    68be:	66 90                	xchg   %ax,%ax
    68c0:	83 fa 01             	cmp    $0x1,%edx
    68c3:	74 13                	je     68d8 <setmailboxkind+0x28>
    68c5:	83 fa 02             	cmp    $0x2,%edx
    68c8:	75 1e                	jne    68e8 <setmailboxkind+0x38>
    68ca:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
    68d1:	31 c0                	xor    %eax,%eax
    68d3:	c3                   	ret
    68d4:	0f 1f 40 00          	nopl   0x0(%rax)
    68d8:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
    68df:	31 c0                	xor    %eax,%eax
    68e1:	c3                   	ret
    68e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    68e8:	83 fa 03             	cmp    $0x3,%edx
    68eb:	75 ce                	jne    68bb <setmailboxkind+0xb>
    68ed:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
    68f4:	31 c0                	xor    %eax,%eax
    68f6:	c3                   	ret
    68f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006900 <barriered_nulltask>:
    6900:	f3 0f 1e fa          	endbr64
    6904:	31 c0                	xor    %eax,%eax
    6906:	c3                   	ret
    6907:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006910 <barriered_steal>:
    6910:	f3 0f 1e fa          	endbr64
    6914:	31 c0                	xor    %eax,%eax
    6916:	c3                   	ret
    6917:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006920 <after>:
    6920:	f3 0f 1e fa          	endbr64
    6924:	31 c0                	xor    %eax,%eax
    6926:	48 39 d7             	cmp    %rdx,%rdi
    6929:	7e 08                	jle    6933 <after+0x13>
    692b:	31 c0                	xor    %eax,%eax
    692d:	48 39 ce             	cmp    %rcx,%rsi
    6930:	0f 9f c0             	setg   %al
    6933:	c3                   	ret
    6934:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    693f:	90                   	nop

0000000000006940 <within>:
    6940:	f3 0f 1e fa          	endbr64
    6944:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6949:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    694e:	31 c0                	xor    %eax,%eax
    6950:	48 39 d7             	cmp    %rdx,%rdi
    6953:	7f 18                	jg     696d <within+0x2d>
    6955:	4d 39 d8             	cmp    %r11,%r8
    6958:	0f 9e c2             	setle  %dl
    695b:	48 39 ce             	cmp    %rcx,%rsi
    695e:	0f 9e c0             	setle  %al
    6961:	21 c2                	and    %eax,%edx
    6963:	31 c0                	xor    %eax,%eax
    6965:	4d 39 d1             	cmp    %r10,%r9
    6968:	0f 9e c0             	setle  %al
    696b:	21 d0                	and    %edx,%eax
    696d:	c3                   	ret
    696e:	66 90                	xchg   %ax,%ax

0000000000006970 <overlap>:
    6970:	f3 0f 1e fa          	endbr64
    6974:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6979:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    697e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6983:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6988:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    698d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
    6992:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6997:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    699c:	48 39 fe             	cmp    %rdi,%rsi
    699f:	7d 2f                	jge    69d0 <overlap+0x60>
    69a1:	48 39 ca             	cmp    %rcx,%rdx
    69a4:	7d 62                	jge    6a08 <overlap+0x98>
    69a6:	4d 39 da             	cmp    %r11,%r10
    69a9:	7d 0e                	jge    69b9 <overlap+0x49>
    69ab:	b8 01 00 00 00       	mov    $0x1,%eax
    69b0:	4d 39 c1             	cmp    %r8,%r9
    69b3:	0f 8c 7f 00 00 00    	jl     6a38 <overlap+0xc8>
    69b9:	31 c0                	xor    %eax,%eax
    69bb:	4d 39 c1             	cmp    %r8,%r9
    69be:	7f 4c                	jg     6a0c <overlap+0x9c>
    69c0:	31 c0                	xor    %eax,%eax
    69c2:	4d 39 da             	cmp    %r11,%r10
    69c5:	0f 9e c0             	setle  %al
    69c8:	c3                   	ret
    69c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    69d0:	7e 4e                	jle    6a20 <overlap+0xb0>
    69d2:	48 39 ca             	cmp    %rcx,%rdx
    69d5:	7f 39                	jg     6a10 <overlap+0xa0>
    69d7:	75 31                	jne    6a0a <overlap+0x9a>
    69d9:	4d 39 c1             	cmp    %r8,%r9
    69dc:	7c 2c                	jl     6a0a <overlap+0x9a>
    69de:	b8 01 00 00 00       	mov    $0x1,%eax
    69e3:	4d 39 da             	cmp    %r11,%r10
    69e6:	7d 24                	jge    6a0c <overlap+0x9c>
    69e8:	48 39 ca             	cmp    %rcx,%rdx
    69eb:	0f 94 c2             	sete   %dl
    69ee:	48 39 fe             	cmp    %rdi,%rsi
    69f1:	0f 94 c0             	sete   %al
    69f4:	21 c2                	and    %eax,%edx
    69f6:	31 c0                	xor    %eax,%eax
    69f8:	4d 39 c1             	cmp    %r8,%r9
    69fb:	0f 94 c0             	sete   %al
    69fe:	21 d0                	and    %edx,%eax
    6a00:	c3                   	ret
    6a01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6a08:	74 af                	je     69b9 <overlap+0x49>
    6a0a:	31 c0                	xor    %eax,%eax
    6a0c:	c3                   	ret
    6a0d:	0f 1f 00             	nopl   (%rax)
    6a10:	4d 39 da             	cmp    %r11,%r10
    6a13:	7e c4                	jle    69d9 <overlap+0x69>
    6a15:	b8 01 00 00 00       	mov    $0x1,%eax
    6a1a:	4d 39 c1             	cmp    %r8,%r9
    6a1d:	7e ba                	jle    69d9 <overlap+0x69>
    6a1f:	c3                   	ret
    6a20:	48 39 ca             	cmp    %rcx,%rdx
    6a23:	7c 94                	jl     69b9 <overlap+0x49>
    6a25:	4d 39 c1             	cmp    %r8,%r9
    6a28:	7d b4                	jge    69de <overlap+0x6e>
    6a2a:	48 39 ca             	cmp    %rcx,%rdx
    6a2d:	74 91                	je     69c0 <overlap+0x50>
    6a2f:	eb d9                	jmp    6a0a <overlap+0x9a>
    6a31:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6a38:	c3                   	ret
    6a39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006a40 <verify>:
    6a40:	f3 0f 1e fa          	endbr64
    6a44:	85 f6                	test   %esi,%esi
    6a46:	0f 8e 44 03 00 00    	jle    6d90 <verify+0x350>
    6a4c:	41 57                	push   %r15
    6a4e:	41 89 f7             	mov    %esi,%r15d
    6a51:	41 56                	push   %r14
    6a53:	45 31 f6             	xor    %r14d,%r14d
    6a56:	41 55                	push   %r13
    6a58:	41 54                	push   %r12
    6a5a:	55                   	push   %rbp
    6a5b:	53                   	push   %rbx
    6a5c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6a60:	48 83 ec 58          	sub    $0x58,%rsp
    6a64:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    6a69:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    6a6e:	45 31 e4             	xor    %r12d,%r12d
    6a71:	45 39 e6             	cmp    %r12d,%r14d
    6a74:	0f 84 4e 02 00 00    	je     6cc8 <verify+0x288>
    6a7a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6a7f:	8b 50 08             	mov    0x8(%rax),%edx
    6a82:	85 d2                	test   %edx,%edx
    6a84:	0f 8e 3e 02 00 00    	jle    6cc8 <verify+0x288>
    6a8a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    6a8f:	31 c9                	xor    %ecx,%ecx
    6a91:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    6a96:	31 c0                	xor    %eax,%eax
    6a98:	44 89 f2             	mov    %r14d,%edx
    6a9b:	bf 01 00 00 00       	mov    $0x1,%edi
    6aa0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6aa5:	48 8d 35 aa 07 00 00 	lea    0x7aa(%rip),%rsi        # 7256 <_IO_stdin_used+0x256>
    6aac:	e8 ff b9 ff ff       	call   24b0 <__printf_chk@plt>
    6ab1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6ab6:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    6abb:	8b 40 08             	mov    0x8(%rax),%eax
    6abe:	85 c0                	test   %eax,%eax
    6ac0:	0f 8e e6 01 00 00    	jle    6cac <verify+0x26c>
    6ac6:	48 89 c8             	mov    %rcx,%rax
    6ac9:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    6ace:	31 db                	xor    %ebx,%ebx
    6ad0:	48 c1 e0 09          	shl    $0x9,%rax
    6ad4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6ad9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    6ade:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6ae3:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6ae8:	4c 8b 20             	mov    (%rax),%r12
    6aeb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6af0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6af5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    6afa:	49 89 de             	mov    %rbx,%r14
    6afd:	48 8d 35 67 07 00 00 	lea    0x767(%rip),%rsi        # 726b <_IO_stdin_used+0x26b>
    6b04:	49 c1 e6 09          	shl    $0x9,%r14
    6b08:	bf 01 00 00 00       	mov    $0x1,%edi
    6b0d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6b11:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    6b19:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    6b1e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    6b26:	31 c0                	xor    %eax,%eax
    6b28:	e8 83 b9 ff ff       	call   24b0 <__printf_chk@plt>
    6b2d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6b32:	4c 8b 20             	mov    (%rax),%r12
    6b35:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    6b3e:	0f 8e 47 01 00 00    	jle    6c8b <verify+0x24b>
    6b44:	4c 03 75 00          	add    0x0(%rbp),%r14
    6b48:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    6b4d:	ba 01 00 00 00       	mov    $0x1,%edx
    6b52:	4d 89 f5             	mov    %r14,%r13
    6b55:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6b5c:	4d 85 f6             	test   %r14,%r14
    6b5f:	0f 8e 21 01 00 00    	jle    6c86 <verify+0x246>
    6b65:	0f 1f 00             	nopl   (%rax)
    6b68:	48 89 d5             	mov    %rdx,%rbp
    6b6b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6b70:	31 db                	xor    %ebx,%ebx
    6b72:	4d 89 f2             	mov    %r14,%r10
    6b75:	48 c1 e5 05          	shl    $0x5,%rbp
    6b79:	48 83 ed 20          	sub    $0x20,%rbp
    6b7d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6b81:	49 89 ee             	mov    %rbp,%r14
    6b84:	48 89 dd             	mov    %rbx,%rbp
    6b87:	48 89 d3             	mov    %rdx,%rbx
    6b8a:	eb 31                	jmp    6bbd <verify+0x17d>
    6b8c:	0f 1f 40 00          	nopl   0x0(%rax)
    6b90:	4c 39 c2             	cmp    %r8,%rdx
    6b93:	0f 8d 57 01 00 00    	jge    6cf0 <verify+0x2b0>
    6b99:	4c 39 df             	cmp    %r11,%rdi
    6b9c:	7e 05                	jle    6ba3 <verify+0x163>
    6b9e:	49 39 c1             	cmp    %rax,%r9
    6ba1:	7c 75                	jl     6c18 <verify+0x1d8>
    6ba3:	4c 39 df             	cmp    %r11,%rdi
    6ba6:	0f 8d ab 01 00 00    	jge    6d57 <verify+0x317>
    6bac:	0f 1f 40 00          	nopl   0x0(%rax)
    6bb0:	48 83 c5 01          	add    $0x1,%rbp
    6bb4:	49 39 ea             	cmp    %rbp,%r10
    6bb7:	0f 8e a9 00 00 00    	jle    6c66 <verify+0x226>
    6bbd:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    6bc4:	48 89 e8             	mov    %rbp,%rax
    6bc7:	48 c1 e0 05          	shl    $0x5,%rax
    6bcb:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    6bd2:	4c 01 f2             	add    %r14,%rdx
    6bd5:	48 8b 08             	mov    (%rax),%rcx
    6bd8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    6bdc:	48 8b 32             	mov    (%rdx),%rsi
    6bdf:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6be3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6be7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    6beb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    6bef:	48 8b 40 18          	mov    0x18(%rax),%rax
    6bf3:	48 39 f1             	cmp    %rsi,%rcx
    6bf6:	7c 98                	jl     6b90 <verify+0x150>
    6bf8:	0f 8e 42 01 00 00    	jle    6d40 <verify+0x300>
    6bfe:	4c 39 c2             	cmp    %r8,%rdx
    6c01:	0f 8f f9 00 00 00    	jg     6d00 <verify+0x2c0>
    6c07:	75 a7                	jne    6bb0 <verify+0x170>
    6c09:	4c 39 df             	cmp    %r11,%rdi
    6c0c:	7f a2                	jg     6bb0 <verify+0x170>
    6c0e:	49 39 c1             	cmp    %rax,%r9
    6c11:	7c 9d                	jl     6bb0 <verify+0x170>
    6c13:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6c18:	49 89 c1             	mov    %rax,%r9
    6c1b:	48 89 f9             	mov    %rdi,%rcx
    6c1e:	48 89 f2             	mov    %rsi,%rdx
    6c21:	bf 01 00 00 00       	mov    $0x1,%edi
    6c26:	48 8d 35 fb 09 00 00 	lea    0x9fb(%rip),%rsi        # 7628 <_IO_stdin_used+0x628>
    6c2d:	31 c0                	xor    %eax,%eax
    6c2f:	48 83 c5 01          	add    $0x1,%rbp
    6c33:	e8 78 b8 ff ff       	call   24b0 <__printf_chk@plt>
    6c38:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6c3d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    6c42:	4c 03 28             	add    (%rax),%r13
    6c45:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6c4a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
    6c51:	4c 8b 20             	mov    (%rax),%r12
    6c54:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6c59:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6c5d:	49 39 ea             	cmp    %rbp,%r10
    6c60:	0f 8f 57 ff ff ff    	jg     6bbd <verify+0x17d>
    6c66:	48 89 da             	mov    %rbx,%rdx
    6c69:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    6c70:	7d 14                	jge    6c86 <verify+0x246>
    6c72:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6c79:	48 83 c2 01          	add    $0x1,%rdx
    6c7d:	4d 85 f6             	test   %r14,%r14
    6c80:	0f 8f e2 fe ff ff    	jg     6b68 <verify+0x128>
    6c86:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    6c8b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6c90:	48 83 c3 01          	add    $0x1,%rbx
    6c94:	39 58 08             	cmp    %ebx,0x8(%rax)
    6c97:	0f 8f 53 fe ff ff    	jg     6af0 <verify+0xb0>
    6c9d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6ca2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6ca7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
    6cac:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6cb1:	48 83 c1 01          	add    $0x1,%rcx
    6cb5:	39 48 08             	cmp    %ecx,0x8(%rax)
    6cb8:	0f 8f d8 fd ff ff    	jg     6a96 <verify+0x56>
    6cbe:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6cc3:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    6cc8:	48 81 44 24 10 e0 00 00 00 	addq   $0xe0,0x10(%rsp)
    6cd1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6cd6:	41 39 c7             	cmp    %eax,%r15d
    6cd9:	0f 84 86 00 00 00    	je     6d65 <verify+0x325>
    6cdf:	41 89 c4             	mov    %eax,%r12d
    6ce2:	e9 8a fd ff ff       	jmp    6a71 <verify+0x31>
    6ce7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    6cf0:	0f 85 ba fe ff ff    	jne    6bb0 <verify+0x170>
    6cf6:	e9 a8 fe ff ff       	jmp    6ba3 <verify+0x163>
    6cfb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6d00:	49 39 c1             	cmp    %rax,%r9
    6d03:	7e 09                	jle    6d0e <verify+0x2ce>
    6d05:	4c 39 df             	cmp    %r11,%rdi
    6d08:	0f 8c 0a ff ff ff    	jl     6c18 <verify+0x1d8>
    6d0e:	4c 39 df             	cmp    %r11,%rdi
    6d11:	0f 8f 99 fe ff ff    	jg     6bb0 <verify+0x170>
    6d17:	49 39 c1             	cmp    %rax,%r9
    6d1a:	0f 8d f8 fe ff ff    	jge    6c18 <verify+0x1d8>
    6d20:	48 39 f1             	cmp    %rsi,%rcx
    6d23:	0f 85 87 fe ff ff    	jne    6bb0 <verify+0x170>
    6d29:	4c 39 c2             	cmp    %r8,%rdx
    6d2c:	0f 85 7e fe ff ff    	jne    6bb0 <verify+0x170>
    6d32:	4c 39 df             	cmp    %r11,%rdi
    6d35:	0f 84 dd fe ff ff    	je     6c18 <verify+0x1d8>
    6d3b:	e9 70 fe ff ff       	jmp    6bb0 <verify+0x170>
    6d40:	4c 39 c2             	cmp    %r8,%rdx
    6d43:	0f 8c 5a fe ff ff    	jl     6ba3 <verify+0x163>
    6d49:	4c 39 df             	cmp    %r11,%rdi
    6d4c:	7e c9                	jle    6d17 <verify+0x2d7>
    6d4e:	4c 39 c2             	cmp    %r8,%rdx
    6d51:	0f 85 59 fe ff ff    	jne    6bb0 <verify+0x170>
    6d57:	49 39 c1             	cmp    %rax,%r9
    6d5a:	0f 8f 50 fe ff ff    	jg     6bb0 <verify+0x170>
    6d60:	e9 b3 fe ff ff       	jmp    6c18 <verify+0x1d8>
    6d65:	48 81 44 24 18 e0 00 00 00 	addq   $0xe0,0x18(%rsp)
    6d6e:	41 8d 46 01          	lea    0x1(%r14),%eax
    6d72:	45 39 e6             	cmp    %r12d,%r14d
    6d75:	74 08                	je     6d7f <verify+0x33f>
    6d77:	41 89 c6             	mov    %eax,%r14d
    6d7a:	e9 ea fc ff ff       	jmp    6a69 <verify+0x29>
    6d7f:	48 83 c4 58          	add    $0x58,%rsp
    6d83:	31 c0                	xor    %eax,%eax
    6d85:	5b                   	pop    %rbx
    6d86:	5d                   	pop    %rbp
    6d87:	41 5c                	pop    %r12
    6d89:	41 5d                	pop    %r13
    6d8b:	41 5e                	pop    %r14
    6d8d:	41 5f                	pop    %r15
    6d8f:	c3                   	ret
    6d90:	31 c0                	xor    %eax,%eax
    6d92:	c3                   	ret

Disassembly of section .fini:

0000000000006d94 <_fini>:
    6d94:	f3 0f 1e fa          	endbr64
    6d98:	48 83 ec 08          	sub    $0x8,%rsp
    6d9c:	48 83 c4 08          	add    $0x8,%rsp
    6da0:	c3                   	ret
