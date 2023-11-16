
multibarrier:     file format elf64-x86-64


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
    2020:	ff 35 62 7e 00 00    	push   0x7e62(%rip)        # 9e88 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 64 7e 00 00    	jmp    *0x7e64(%rip)        # 9e90 <_GLOBAL_OFFSET_TABLE_+0x10>
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

Disassembly of section .plt.got:

00000000000022b0 <__cxa_finalize@plt>:
    22b0:	f3 0f 1e fa          	endbr64
    22b4:	ff 25 3e 7d 00 00    	jmp    *0x7d3e(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    22ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

00000000000022c0 <free@plt>:
    22c0:	f3 0f 1e fa          	endbr64
    22c4:	ff 25 ce 7b 00 00    	jmp    *0x7bce(%rip)        # 9e98 <free@GLIBC_2.2.5>
    22ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000022d0 <putchar@plt>:
    22d0:	f3 0f 1e fa          	endbr64
    22d4:	ff 25 c6 7b 00 00    	jmp    *0x7bc6(%rip)        # 9ea0 <putchar@GLIBC_2.2.5>
    22da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000022e0 <pthread_setaffinity_np@plt>:
    22e0:	f3 0f 1e fa          	endbr64
    22e4:	ff 25 be 7b 00 00    	jmp    *0x7bbe(%rip)        # 9ea8 <pthread_setaffinity_np@GLIBC_2.34>
    22ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000022f0 <puts@plt>:
    22f0:	f3 0f 1e fa          	endbr64
    22f4:	ff 25 b6 7b 00 00    	jmp    *0x7bb6(%rip)        # 9eb0 <puts@GLIBC_2.2.5>
    22fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002300 <setsockopt@plt>:
    2300:	f3 0f 1e fa          	endbr64
    2304:	ff 25 ae 7b 00 00    	jmp    *0x7bae(%rip)        # 9eb8 <setsockopt@GLIBC_2.2.5>
    230a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002310 <clock_gettime@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 a6 7b 00 00    	jmp    *0x7ba6(%rip)        # 9ec0 <clock_gettime@GLIBC_2.17>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002320 <strlen@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 9e 7b 00 00    	jmp    *0x7b9e(%rip)        # 9ec8 <strlen@GLIBC_2.2.5>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <__stack_chk_fail@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 96 7b 00 00    	jmp    *0x7b96(%rip)        # 9ed0 <__stack_chk_fail@GLIBC_2.4>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <io_uring_submit@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 8e 7b 00 00    	jmp    *0x7b8e(%rip)        # 9ed8 <io_uring_submit@LIBURING_2.0>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <nanosleep@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 86 7b 00 00    	jmp    *0x7b86(%rip)        # 9ee0 <nanosleep@GLIBC_2.2.5>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <strrchr@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 7e 7b 00 00    	jmp    *0x7b7e(%rip)        # 9ee8 <strrchr@GLIBC_2.2.5>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <close@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 76 7b 00 00    	jmp    *0x7b76(%rip)        # 9ef0 <close@GLIBC_2.2.5>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <strtok_r@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 6e 7b 00 00    	jmp    *0x7b6e(%rip)        # 9ef8 <strtok_r@GLIBC_2.2.5>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <read@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 66 7b 00 00    	jmp    *0x7b66(%rip)        # 9f00 <read@GLIBC_2.2.5>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <calloc@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 5e 7b 00 00    	jmp    *0x7b5e(%rip)        # 9f08 <calloc@GLIBC_2.2.5>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <strcmp@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 56 7b 00 00    	jmp    *0x7b56(%rip)        # 9f10 <strcmp@GLIBC_2.2.5>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <__memcpy_chk@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 4e 7b 00 00    	jmp    *0x7b4e(%rip)        # 9f18 <__memcpy_chk@GLIBC_2.3.4>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <stat@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 46 7b 00 00    	jmp    *0x7b46(%rip)        # 9f20 <stat@GLIBC_2.33>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <memcpy@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 3e 7b 00 00    	jmp    *0x7b3e(%rip)        # 9f28 <memcpy@GLIBC_2.14>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <io_uring_queue_init@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 36 7b 00 00    	jmp    *0x7b36(%rip)        # 9f30 <io_uring_queue_init@LIBURING_2.0>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <eventfd_write@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 2e 7b 00 00    	jmp    *0x7b2e(%rip)        # 9f38 <eventfd_write@GLIBC_2.7>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <malloc@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 26 7b 00 00    	jmp    *0x7b26(%rip)        # 9f40 <malloc@GLIBC_2.2.5>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <listen@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 1e 7b 00 00    	jmp    *0x7b1e(%rip)        # 9f48 <listen@GLIBC_2.2.5>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <__strcpy_chk@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 16 7b 00 00    	jmp    *0x7b16(%rip)        # 9f50 <__strcpy_chk@GLIBC_2.3.4>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <__io_uring_get_cqe@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 0e 7b 00 00    	jmp    *0x7b0e(%rip)        # 9f58 <__io_uring_get_cqe@LIBURING_2.0>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <__printf_chk@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 06 7b 00 00    	jmp    *0x7b06(%rip)        # 9f60 <__printf_chk@GLIBC_2.3.4>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <bind@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 fe 7a 00 00    	jmp    *0x7afe(%rip)        # 9f68 <bind@GLIBC_2.2.5>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <pthread_create@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 f6 7a 00 00    	jmp    *0x7af6(%rip)        # 9f70 <pthread_create@GLIBC_2.34>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <open@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 ee 7a 00 00    	jmp    *0x7aee(%rip)        # 9f78 <open@GLIBC_2.2.5>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <perror@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 e6 7a 00 00    	jmp    *0x7ae6(%rip)        # 9f80 <perror@GLIBC_2.2.5>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <exit@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 de 7a 00 00    	jmp    *0x7ade(%rip)        # 9f88 <exit@GLIBC_2.2.5>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <eventfd@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 d6 7a 00 00    	jmp    *0x7ad6(%rip)        # 9f90 <eventfd@GLIBC_2.7>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <fwrite@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 ce 7a 00 00    	jmp    *0x7ace(%rip)        # 9f98 <fwrite@GLIBC_2.2.5>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <__fprintf_chk@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 c6 7a 00 00    	jmp    *0x7ac6(%rip)        # 9fa0 <__fprintf_chk@GLIBC_2.3.4>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <io_uring_register_eventfd@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 be 7a 00 00    	jmp    *0x7abe(%rip)        # 9fa8 <io_uring_register_eventfd@LIBURING_2.0>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <pthread_join@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 b6 7a 00 00    	jmp    *0x7ab6(%rip)        # 9fb0 <pthread_join@GLIBC_2.34>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <strerror@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 ae 7a 00 00    	jmp    *0x7aae(%rip)        # 9fb8 <strerror@GLIBC_2.2.5>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <__ctype_tolower_loc@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 a6 7a 00 00    	jmp    *0x7aa6(%rip)        # 9fc0 <__ctype_tolower_loc@GLIBC_2.3>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <__sprintf_chk@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 9e 7a 00 00    	jmp    *0x7a9e(%rip)        # 9fc8 <__sprintf_chk@GLIBC_2.3.4>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <socket@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 96 7a 00 00    	jmp    *0x7a96(%rip)        # 9fd0 <socket@GLIBC_2.2.5>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000002540 <fatal_error>:
struct Snapshot {
  struct timespec start;
  struct timespec end;
};

void fatal_error(const char *syscall) {
    2540:	f3 0f 1e fa          	endbr64
    2544:	50                   	push   %rax
    2545:	58                   	pop    %rax
    2546:	50                   	push   %rax
    perror(syscall);
    2547:	e8 44 ff ff ff       	call   2490 <perror@plt>
    exit(1);
    254c:	bf 01 00 00 00       	mov    $0x1,%edi
    2551:	e8 4a ff ff ff       	call   24a0 <exit@plt>

0000000000002556 <copy_file_contents.cold>:
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");
    2556:	48 8d 3d a2 4c 00 00 	lea    0x4ca2(%rip),%rdi        # 71ff <_IO_stdin_used+0x1ff>
    255d:	e8 de ff ff ff       	call   2540 <fatal_error>

0000000000002562 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    2562:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
    2568:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2570:	0f 0b                	ud2

0000000000002572 <add_read_request.cold>:
    2572:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    257a:	0f 0b                	ud2

000000000000257c <_send_static_string_content.cold>:
    257c:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    2582:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    258a:	0f 0b                	ud2

000000000000258c <add_accept_request.cold>:
    258c:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2594:	0f 0b                	ud2

0000000000002596 <io_thread.cold>:
        break;
      }
      printf("Received wait finished\n");
      struct Request *req = (struct Request *) cqe->user_data;
      if (ret < 0)
          fatal_error("io_uring_wait_cqe");
    2596:	48 8d 3d 32 4c 00 00 	lea    0x4c32(%rip),%rdi        # 71cf <_IO_stdin_used+0x1cf>
    259d:	e8 9e ff ff ff       	call   2540 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    25a2:	48 8d 3d aa 4b 00 00 	lea    0x4baa(%rip),%rdi        # 7153 <_IO_stdin_used+0x153>
    25a9:	e8 92 ff ff ff       	call   2540 <fatal_error>
    fatal_error("listen()");
    25ae:	48 8d 3d be 4b 00 00 	lea    0x4bbe(%rip),%rdi        # 7173 <_IO_stdin_used+0x173>
    25b5:	e8 86 ff ff ff       	call   2540 <fatal_error>
    25ba:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25c2:	0f 0b                	ud2
    25c4:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25cc:	0f 0b                	ud2
      fatal_error("socket()");
    25ce:	48 8d 3d 75 4b 00 00 	lea    0x4b75(%rip),%rdi        # 714a <_IO_stdin_used+0x14a>
    25d5:	e8 66 ff ff ff       	call   2540 <fatal_error>
      fatal_error("bind()");
    25da:	48 8d 3d 8b 4b 00 00 	lea    0x4b8b(%rip),%rdi        # 716c <_IO_stdin_used+0x16c>
    25e1:	e8 5a ff ff ff       	call   2540 <fatal_error>
    25e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000025f0 <main>:
    }


  return 0;
}
int main() {
    25f0:	f3 0f 1e fa          	endbr64
    25f4:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    25f6:	48 8d 3d b3 4e 00 00 	lea    0x4eb3(%rip),%rdi        # 74b0 <_IO_stdin_used+0x4b0>
    25fd:	41 56                	push   %r14
    25ff:	41 55                	push   %r13
    2601:	41 54                	push   %r12
    2603:	55                   	push   %rbp
    2604:	53                   	push   %rbx
    2605:	48 81 ec b8 00 00 00 	sub    $0xb8,%rsp
    260c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2615:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
    261d:	48 8d 05 ec 11 00 00 	lea    0x11ec(%rip),%rax        # 3810 <barriered_reset>
    2624:	66 48 0f 6e e8       	movq   %rax,%xmm5
    2629:	0f 16 2d 48 76 00 00 	movhps 0x7648(%rip),%xmm5        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    2630:	0f 29 6c 24 30       	movaps %xmm5,0x30(%rsp)
    2635:	e8 b6 fc ff ff       	call   22f0 <puts@plt>
    263a:	bf 0a 00 00 00       	mov    $0xa,%edi
    263f:	e8 8c fc ff ff       	call   22d0 <putchar@plt>
    2644:	48 8d 3d f3 4b 00 00 	lea    0x4bf3(%rip),%rdi        # 723e <_IO_stdin_used+0x23e>
    264b:	e8 a0 fc ff ff       	call   22f0 <puts@plt>
    2650:	ba 0c 00 00 00       	mov    $0xc,%edx
    2655:	48 8d 35 fe 4b 00 00 	lea    0x4bfe(%rip),%rsi        # 725a <_IO_stdin_used+0x25a>
    265c:	31 c0                	xor    %eax,%eax
    265e:	bf 01 00 00 00       	mov    $0x1,%edi
    2663:	e8 e8 fd ff ff       	call   2450 <__printf_chk@plt>
    2668:	ba 0f 00 00 00       	mov    $0xf,%edx
    266d:	48 8d 35 00 4c 00 00 	lea    0x4c00(%rip),%rsi        # 7274 <_IO_stdin_used+0x274>
    2674:	31 c0                	xor    %eax,%eax
    2676:	bf 01 00 00 00       	mov    $0x1,%edi
    267b:	e8 d0 fd ff ff       	call   2450 <__printf_chk@plt>
    2680:	ba 01 00 00 00       	mov    $0x1,%edx
    2685:	48 8d 35 fc 4b 00 00 	lea    0x4bfc(%rip),%rsi        # 7288 <_IO_stdin_used+0x288>
    268c:	31 c0                	xor    %eax,%eax
    268e:	bf 01 00 00 00       	mov    $0x1,%edi
    2693:	e8 b8 fd ff ff       	call   2450 <__printf_chk@plt>
    2698:	ba 01 00 00 00       	mov    $0x1,%edx
    269d:	48 8d 35 f5 4b 00 00 	lea    0x4bf5(%rip),%rsi        # 7299 <_IO_stdin_used+0x299>
    26a4:	31 c0                	xor    %eax,%eax
    26a6:	bf 01 00 00 00       	mov    $0x1,%edi
    26ab:	e8 a0 fd ff ff       	call   2450 <__printf_chk@plt>
    26b0:	ba 01 00 00 00       	mov    $0x1,%edx
    26b5:	48 8d 35 f5 4b 00 00 	lea    0x4bf5(%rip),%rsi        # 72b1 <_IO_stdin_used+0x2b1>
    26bc:	31 c0                	xor    %eax,%eax
    26be:	bf 01 00 00 00       	mov    $0x1,%edi
    26c3:	e8 88 fd ff ff       	call   2450 <__printf_chk@plt>
    26c8:	ba 01 00 00 00       	mov    $0x1,%edx
    26cd:	48 8d 35 44 4e 00 00 	lea    0x4e44(%rip),%rsi        # 7518 <_IO_stdin_used+0x518>
    26d4:	31 c0                	xor    %eax,%eax
    26d6:	bf 01 00 00 00       	mov    $0x1,%edi
    26db:	e8 70 fd ff ff       	call   2450 <__printf_chk@plt>
    26e0:	ba 01 00 00 00       	mov    $0x1,%edx
    26e5:	48 8d 35 5c 4e 00 00 	lea    0x4e5c(%rip),%rsi        # 7548 <_IO_stdin_used+0x548>
    26ec:	31 c0                	xor    %eax,%eax
    26ee:	bf 01 00 00 00       	mov    $0x1,%edi
    26f3:	e8 58 fd ff ff       	call   2450 <__printf_chk@plt>
    26f8:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    26fd:	48 8d 35 c9 4b 00 00 	lea    0x4bc9(%rip),%rsi        # 72cd <_IO_stdin_used+0x2cd>
    2704:	31 c0                	xor    %eax,%eax
    2706:	bf 01 00 00 00       	mov    $0x1,%edi
    270b:	e8 40 fd ff ff       	call   2450 <__printf_chk@plt>
    2710:	ba 05 00 00 00       	mov    $0x5,%edx
    2715:	48 8d 35 cb 4b 00 00 	lea    0x4bcb(%rip),%rsi        # 72e7 <_IO_stdin_used+0x2e7>
    271c:	31 c0                	xor    %eax,%eax
    271e:	bf 01 00 00 00       	mov    $0x1,%edi
    2723:	e8 28 fd ff ff       	call   2450 <__printf_chk@plt>
    2728:	48 8d 3d 9f 49 00 00 	lea    0x499f(%rip),%rdi        # 70ce <_IO_stdin_used+0xce>
    272f:	e8 bc fb ff ff       	call   22f0 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    2734:	be 18 00 00 00       	mov    $0x18,%esi
    2739:	bf 0c 00 00 00       	mov    $0xc,%edi
    273e:	e8 5d fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2743:	be b0 00 00 00       	mov    $0xb0,%esi
    2748:	bf 0f 00 00 00       	mov    $0xf,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    274d:	49 89 c7             	mov    %rax,%r15
    2750:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2755:	e8 46 fc ff ff       	call   23a0 <calloc@plt>
  int barrier_count = 2;
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    275a:	be 10 00 00 00       	mov    $0x10,%esi
    275f:	bf 01 00 00 00       	mov    $0x1,%edi
    2764:	4d 8d 67 e8          	lea    -0x18(%r15),%r12
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2768:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    276d:	45 31 ff             	xor    %r15d,%r15d
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2770:	e8 2b fc ff ff       	call   23a0 <calloc@plt>
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2775:	be 10 00 00 00       	mov    $0x10,%esi
    277a:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    277f:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2785:	48 89 c3             	mov    %rax,%rbx
    2788:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    278d:	e8 0e fc ff ff       	call   23a0 <calloc@plt>
    2792:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    }
  }
  int external_thread_index = 0;
    2797:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    279f:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
    27a3:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    27aa:	4d 89 d1             	mov    %r10,%r9
    27ad:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    27b2:	4c 89 54 24 58       	mov    %r10,0x58(%rsp)
    27b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27c0:	be 08 00 00 00       	mov    $0x8,%esi
    27c5:	bf 02 00 00 00       	mov    $0x2,%edi
    27ca:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    27cf:	44 89 fd             	mov    %r15d,%ebp
    27d2:	e8 c9 fb ff ff       	call   23a0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27d7:	be 80 00 00 00       	mov    $0x80,%esi
    27dc:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27e1:	49 89 c5             	mov    %rax,%r13
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27e4:	e8 b7 fb ff ff       	call   23a0 <calloc@plt>
    if (x % 2 == 1) {
    27e9:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27ee:	48 89 c3             	mov    %rax,%rbx
    if (x % 2 == 1) {
    27f1:	44 89 f8             	mov    %r15d,%eax
    27f4:	41 83 c7 01          	add    $0x1,%r15d
    27f8:	83 e0 01             	and    $0x1,%eax
    27fb:	85 c0                	test   %eax,%eax
    27fd:	0f 84 56 0e 00 00    	je     3659 <main+0x1069>
      my_thread_data[0] = &thread_data[other]; 
    2803:	49 8d 89 50 ff ff ff 	lea    -0xb0(%r9),%rcx
      my_thread_data[1] = &thread_data[x]; 
    280a:	4d 89 4d 08          	mov    %r9,0x8(%r13)
    280e:	4d 89 c8             	mov    %r9,%r8
    2811:	89 ea                	mov    %ebp,%edx
      my_thread_data[0] = &thread_data[other]; 
    2813:	49 89 4d 00          	mov    %rcx,0x0(%r13)
    2817:	bf 01 00 00 00       	mov    $0x1,%edi
    281c:	31 c0                	xor    %eax,%eax
      other = abs(x - 1) % total_threads;
    281e:	44 8d 75 ff          	lea    -0x1(%rbp),%r14d
      thread_data[x].thread_index = 1;
    2822:	41 c7 01 01 00 00 00 	movl   $0x1,(%r9)
    2829:	48 8d 35 cb 4a 00 00 	lea    0x4acb(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
    2830:	e8 1b fc ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    2835:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    283a:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    283f:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2844:	4d 89 61 38          	mov    %r12,0x38(%r9)
    2848:	45 8b 01             	mov    (%r9),%r8d
    284b:	44 89 f1             	mov    %r14d,%ecx
    284e:	89 ea                	mov    %ebp,%edx
    2850:	48 8d 35 19 4d 00 00 	lea    0x4d19(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    2857:	bf 01 00 00 00       	mov    $0x1,%edi
    285c:	31 c0                	xor    %eax,%eax
    285e:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      CPU_SET(j, sendercpu);
    2863:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    2869:	e8 e2 fb ff ff       	call   2450 <__printf_chk@plt>
    thread_data[x].other = other;
    286e:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2873:	45 89 b1 a8 00 00 00 	mov    %r14d,0xa8(%r9)
    for (int j = 0 ; j < cores / 2 ; j++) {
    287a:	45 31 f6             	xor    %r14d,%r14d
    287d:	0f 1f 00             	nopl   (%rax)
    2880:	44 89 f1             	mov    %r14d,%ecx
    2883:	89 ea                	mov    %ebp,%edx
    2885:	48 8d 35 14 4d 00 00 	lea    0x4d14(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    288c:	31 c0                	xor    %eax,%eax
    288e:	bf 01 00 00 00       	mov    $0x1,%edi
    2893:	e8 b8 fb ff ff       	call   2450 <__printf_chk@plt>
      CPU_SET(j, sendercpu);
    2898:	44 89 f1             	mov    %r14d,%ecx
    289b:	4c 89 e0             	mov    %r12,%rax
    for (int j = 0 ; j < cores / 2 ; j++) {
    289e:	41 83 c6 01          	add    $0x1,%r14d
      CPU_SET(j, sendercpu);
    28a2:	48 d3 e0             	shl    %cl,%rax
    28a5:	48 09 03             	or     %rax,(%rbx)
    for (int j = 0 ; j < cores / 2 ; j++) {
    28a8:	41 83 fe 06          	cmp    $0x6,%r14d
    28ac:	75 d2                	jne    2880 <main+0x290>
    thread_data[x].cpu_set = sendercpu;
    28ae:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    thread_data[x].thread_count = 2;
    28b3:	48 8b 05 86 51 00 00 	mov    0x5186(%rip),%rax        # 7a40 <_IO_stdin_used+0xa40>
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28ba:	be 10 00 00 00       	mov    $0x10,%esi
        thread_data[x].tasks[y].sending = 1;
    28bf:	41 89 ee             	mov    %ebp,%r14d
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28c2:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].cpu_set = sendercpu;
    28c7:	49 89 99 a0 00 00 00 	mov    %rbx,0xa0(%r9)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28ce:	31 db                	xor    %ebx,%ebx
    thread_data[x].real_thread_index = x;
    28d0:	41 89 69 04          	mov    %ebp,0x4(%r9)
    thread_data[x].threads = my_thread_data;
    28d4:	4d 89 69 10          	mov    %r13,0x10(%r9)
    thread_data[x].thread_count = 2;
    28d8:	49 89 41 18          	mov    %rax,0x18(%r9)
    thread_data[x].task_count = total_barrier_count;
    28dc:	41 c7 41 30 03 00 00 00 	movl   $0x3,0x30(%r9)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28e4:	e8 b7 fa ff ff       	call   23a0 <calloc@plt>
    28e9:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28ee:	be 10 00 00 00       	mov    $0x10,%esi
    28f3:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28f8:	49 89 41 58          	mov    %rax,0x58(%r9)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28fc:	e8 9f fa ff ff       	call   23a0 <calloc@plt>
    2901:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2906:	be 28 00 00 00       	mov    $0x28,%esi
    thread_data[x].timestamp_count = 0;
    290b:	66 0f 6f 15 0d 51 00 00 	movdqa 0x510d(%rip),%xmm2        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2913:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2918:	49 89 41 60          	mov    %rax,0x60(%r9)
    thread_data[x].timestamp_count = 0;
    291c:	41 0f 11 51 70       	movups %xmm2,0x70(%r9)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2921:	e8 7a fa ff ff       	call   23a0 <calloc@plt>
    2926:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    292b:	be 80 01 00 00       	mov    $0x180,%esi
    thread_data[x].task_timestamp_count = 0;
    2930:	66 0f 6f 1d e8 50 00 00 	movdqa 0x50e8(%rip),%xmm3        # 7a20 <_IO_stdin_used+0xa20>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2938:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    293d:	49 89 81 80 00 00 00 	mov    %rax,0x80(%r9)
    thread_data[x].task_timestamp_count = 0;
    2944:	41 0f 11 99 88 00 00 00 	movups %xmm3,0x88(%r9)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    294c:	e8 4f fa ff ff       	call   23a0 <calloc@plt>
      thread_data[x].tasks = barriers;
    2951:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        thread_data[x].tasks[y].sending = 1;
    2956:	44 89 7c 24 28       	mov    %r15d,0x28(%rsp)
    295b:	48 89 c2             	mov    %rax,%rdx
      thread_data[x].tasks = barriers;
    295e:	49 89 41 28          	mov    %rax,0x28(%r9)
        thread_data[x].tasks[y].sending = 1;
    2962:	4c 89 cd             	mov    %r9,%rbp
        thread_data[x].tasks[y].protected = do_protected_write; 
    2965:	4c 63 fb             	movslq %ebx,%r15
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2968:	be 20 00 00 00       	mov    $0x20,%esi
    296d:	bf 0c 00 00 00       	mov    $0xc,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    2972:	4f 8d 24 7f          	lea    (%r15,%r15,2),%r12
    2976:	48 8d 05 53 0e 00 00 	lea    0xe53(%rip),%rax        # 37d0 <do_protected_write>
    297d:	49 c1 e4 07          	shl    $0x7,%r12
    2981:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
    2985:	49 89 85 a0 00 00 00 	mov    %rax,0xa0(%r13)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    298c:	e8 0f fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    2991:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    2995:	49 89 85 e8 00 00 00 	mov    %rax,0xe8(%r13)
        for (int b = 0 ; b < 2 ; b++) {
    299c:	49 89 c5             	mov    %rax,%r13
    299f:	48 8d 40 40          	lea    0x40(%rax),%rax
    29a3:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    29a8:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29ad:	be 08 00 00 00       	mov    $0x8,%esi
    29b2:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    29b7:	49 83 c5 20          	add    $0x20,%r13
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29bb:	e8 e0 f9 ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29c0:	be 08 00 00 00       	mov    $0x8,%esi
    29c5:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29ca:	48 89 c5             	mov    %rax,%rbp
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29cd:	e8 ce f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29d2:	be 18 00 00 00       	mov    $0x18,%esi
    29d7:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29dc:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29df:	e8 bc f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    29e4:	66 0f 6f 05 44 50 00 00 	movdqa 0x5044(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
          mailboxes[b].higher = &data[1];
    29ec:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29f0:	49 89 45 e0          	mov    %rax,-0x20(%r13)
          mailboxes[b].higher = &data[1];
    29f4:	49 89 75 e8          	mov    %rsi,-0x18(%r13)
          data[0].messages = messages;
    29f8:	48 89 28             	mov    %rbp,(%rax)
          data[1].messages = messages2;
    29fb:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    29ff:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    2a03:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    2a07:	4c 39 6c 24 08       	cmp    %r13,0x8(%rsp)
    2a0c:	75 9f                	jne    29ad <main+0x3bd>
        char *message = malloc(sizeof(char) * 256);
    2a0e:	be 01 00 00 00       	mov    $0x1,%esi
    2a13:	bf 00 01 00 00       	mov    $0x100,%edi
    2a18:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    2a1c:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    2a21:	e8 7a f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a26:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a2b:	49 89 c5             	mov    %rax,%r13
        struct Message *messaged = malloc(sizeof(struct Message));
    2a2e:	e8 dd f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a33:	4c 89 ef             	mov    %r13,%rdi
    2a36:	41 89 d9             	mov    %ebx,%r9d
    2a39:	45 89 f0             	mov    %r14d,%r8d
    2a3c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2a41:	48 8d 0d 78 4b 00 00 	lea    0x4b78(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a48:	ba 00 01 00 00       	mov    $0x100,%edx
    2a4d:	31 c0                	xor    %eax,%eax
    2a4f:	be 01 00 00 00       	mov    $0x1,%esi
    2a54:	e8 c7 fa ff ff       	call   2520 <__sprintf_chk@plt>
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a59:	48 8b 55 28          	mov    0x28(%rbp),%rdx
        messaged->thread_index = thread_data[x].thread_index;
    2a5d:	48 63 45 00          	movslq 0x0(%rbp),%rax
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a61:	8d 4b 01             	lea    0x1(%rbx),%ecx
        messaged->message = message;
    2a64:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a69:	be 20 00 00 00       	mov    $0x20,%esi
    2a6e:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a73:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2a77:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
        messaged->message = message;
    2a7c:	4d 89 2a             	mov    %r13,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a7f:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
        messaged->task_index = y;
    2a83:	4d 89 7a 10          	mov    %r15,0x10(%r10)
        messaged->thread_index = thread_data[x].thread_index;
    2a87:	49 89 c7             	mov    %rax,%r15
    2a8a:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a8e:	41 89 8d 08 01 00 00 	mov    %ecx,0x108(%r13)
        thread_data[x].tasks[y].message = messaged;
    2a95:	4d 89 95 00 01 00 00 	mov    %r10,0x100(%r13)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a9c:	49 c7 85 d0 00 00 00 63 00 00 00 	movq   $0x63,0xd0(%r13)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2aa7:	e8 f4 f8 ff ff       	call   23a0 <calloc@plt>
        if (y == barrier_count - 1) {
    2aac:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2aaf:	41 89 5d 00          	mov    %ebx,0x0(%r13)
        if (y == barrier_count - 1) {
    2ab3:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2ab7:	49 89 85 c8 00 00 00 	mov    %rax,0xc8(%r13)
        if (y == barrier_count - 1) {
    2abe:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
        thread_data[x].tasks[y].available = 1;
    2ac3:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2acd:	49 89 85 b8 00 00 00 	mov    %rax,0xb8(%r13)
        thread_data[x].tasks[y].sending = 1;
    2ad4:	48 b8 01 00 00 00 0c 00 00 00 	movabs $0xc00000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2ade:	49 c7 85 d8 00 00 00 00 00 00 00 	movq   $0x0,0xd8(%r13)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2ae9:	45 89 bd b0 00 00 00 	mov    %r15d,0xb0(%r13)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2af0:	49 89 ad a8 00 00 00 	mov    %rbp,0xa8(%r13)
        thread_data[x].tasks[y].arrived = 0;
    2af7:	41 c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r13)
        thread_data[x].tasks[y].thread_count = 2;
    2b02:	41 c7 85 b4 00 00 00 02 00 00 00 	movl   $0x2,0xb4(%r13)
        thread_data[x].tasks[y].sending = 1;
    2b0d:	49 89 85 f8 00 00 00 	mov    %rax,0xf8(%r13)
        if (y == barrier_count - 1) {
    2b14:	0f 84 27 0b 00 00    	je     3641 <main+0x1051>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2b1a:	44 39 f3             	cmp    %r14d,%ebx
    2b1d:	75 69                	jne    2b88 <main+0x598>
    2b1f:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    2b23:	85 db                	test   %ebx,%ebx
    2b25:	7f 61                	jg     2b88 <main+0x598>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2b27:	44 89 f2             	mov    %r14d,%edx
    2b2a:	bf 01 00 00 00       	mov    $0x1,%edi
    2b2f:	31 c0                	xor    %eax,%eax
    2b31:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2b35:	48 8d 35 ac 4a 00 00 	lea    0x4aac(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2b3c:	e8 0f f9 ff ff       	call   2450 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b41:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    2b46:	48 63 c3             	movslq %ebx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b49:	48 8b 55 28          	mov    0x28(%rbp),%rdx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b4d:	48 89 c7             	mov    %rax,%rdi
    2b50:	48 c1 e0 04          	shl    $0x4,%rax
    2b54:	48 01 c8             	add    %rcx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b57:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b5b:	48 89 45 40          	mov    %rax,0x40(%rbp)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b5f:	48 8d 05 ea 31 00 00 	lea    0x31ea(%rip),%rax        # 5d50 <barriered_work_ingest>
    2b66:	4a 89 84 22 98 00 00 00 	mov    %rax,0x98(%rdx,%r12,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b6e:	8d 47 01             	lea    0x1(%rdi),%eax
    2b71:	89 44 24 20          	mov    %eax,0x20(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b75:	83 f9 03             	cmp    $0x3,%ecx
    2b78:	74 21                	je     2b9b <main+0x5ab>
    2b7a:	bb 01 00 00 00       	mov    $0x1,%ebx
    2b7f:	e9 e1 fd ff ff       	jmp    2965 <main+0x375>
    2b84:	0f 1f 40 00          	nopl   0x0(%rax)
            thread_data[x].tasks[y].run = barriered_work; 
    2b88:	48 8d 05 b1 2c 00 00 	lea    0x2cb1(%rip),%rax        # 5840 <barriered_work>
    2b8f:	49 89 85 98 00 00 00 	mov    %rax,0x98(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b96:	83 f9 03             	cmp    $0x3,%ecx
    2b99:	75 df                	jne    2b7a <main+0x58a>

          }
        }
      }
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b9b:	66 0f 6f 64 24 30    	movdqa 0x30(%rsp),%xmm4
    2ba1:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
    2ba6:	49 89 e9             	mov    %rbp,%r9
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2ba9:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2bb3:	c7 82 80 03 00 00 00 00 00 00 	movl   $0x0,0x380(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2bbd:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    2bc2:	49 81 c1 b0 00 00 00 	add    $0xb0,%r9
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2bc9:	c7 82 00 03 00 00 02 00 00 00 	movl   $0x2,0x300(%rdx)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2bd3:	48 89 82 b4 03 00 00 	mov    %rax,0x3b4(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bda:	8b 45 00             	mov    0x0(%rbp),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2bdd:	48 89 aa a8 03 00 00 	mov    %rbp,0x3a8(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2be4:	89 82 b0 03 00 00    	mov    %eax,0x3b0(%rdx)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2bea:	c7 82 fc 03 00 00 0c 00 00 00 	movl   $0xc,0x3fc(%rdx)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2bf4:	c7 82 bc 03 00 00 03 00 00 00 	movl   $0x3,0x3bc(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2bfe:	0f 11 a2 98 03 00 00 	movups %xmm4,0x398(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2c05:	41 83 ff 0f          	cmp    $0xf,%r15d
    2c09:	0f 85 b1 fb ff ff    	jne    27c0 <main+0x1d0>
    2c0f:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    2c14:	ba 0d 00 00 00       	mov    $0xd,%edx
    2c19:	48 8d 35 f8 46 00 00 	lea    0x46f8(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2c20:	31 c0                	xor    %eax,%eax
    2c22:	bf 01 00 00 00       	mov    $0x1,%edi
    2c27:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    2c2c:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2c31:	e8 1a f8 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c36:	be 08 00 00 00       	mov    $0x8,%esi
    2c3b:	bf 02 00 00 00       	mov    $0x2,%edi
    2c40:	e8 5b f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2c45:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c4a:	bf 0f 00 00 00       	mov    $0xf,%edi
    my_thread_data[0] = &thread_data[x]; 
    2c4f:	4d 8d ba f0 08 00 00 	lea    0x8f0(%r10),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c56:	4d 8d b2 60 01 00 00 	lea    0x160(%r10),%r14
    thread_data[x].threads = my_thread_data;
    2c5d:	49 89 82 00 09 00 00 	mov    %rax,0x900(%r10)
    my_thread_data[0] = &thread_data[x]; 
    2c64:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c67:	49 8d 8a 10 02 00 00 	lea    0x210(%r10),%rcx
    2c6e:	49 8d 92 70 03 00 00 	lea    0x370(%r10),%rdx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c75:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c79:	49 8b 42 28          	mov    0x28(%r10),%rax
    2c7d:	4d 8d 9a d0 04 00 00 	lea    0x4d0(%r10),%r11
    2c84:	4d 8d 82 80 05 00 00 	lea    0x580(%r10),%r8
    2c8b:	49 8d b2 c0 02 00 00 	lea    0x2c0(%r10),%rsi
    2c92:	49 8d 9a 20 04 00 00 	lea    0x420(%r10),%rbx
    thread_data[x].thread_count = 2;
    2c99:	41 c7 82 08 09 00 00 02 00 00 00 	movl   $0x2,0x908(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2ca4:	48 89 4c 24 58       	mov    %rcx,0x58(%rsp)
    2ca9:	4d 8d 8a 30 06 00 00 	lea    0x630(%r10),%r9
    2cb0:	4d 8d a2 e0 06 00 00 	lea    0x6e0(%r10),%r12
    2cb7:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    2cbc:	4d 8d aa 90 07 00 00 	lea    0x790(%r10),%r13
    thread_data[x].thread_index = 0;
    2cc3:	41 c7 82 f0 08 00 00 00 00 00 00 	movl   $0x0,0x8f0(%r10)
    thread_data[x].task_count = total_barrier_count;
    2cce:	41 c7 82 20 09 00 00 03 00 00 00 	movl   $0x3,0x920(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2cd9:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2ce3:	49 8d 82 b0 00 00 00 	lea    0xb0(%r10),%rax
    2cea:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2cef:	49 8b 82 d8 00 00 00 	mov    0xd8(%r10),%rax
    2cf6:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    2cfb:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2d05:	49 8b 82 88 01 00 00 	mov    0x188(%r10),%rax
    2d0c:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    2d11:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2d1b:	49 8b 82 38 02 00 00 	mov    0x238(%r10),%rax
    my_thread_data[0] = &thread_data[x]; 
    2d22:	4c 89 7c 24 70       	mov    %r15,0x70(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d27:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2d31:	49 8b 82 e8 02 00 00 	mov    0x2e8(%r10),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2d38:	4c 89 74 24 78       	mov    %r14,0x78(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d3d:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2d47:	49 8b 82 98 03 00 00 	mov    0x398(%r10),%rax
    2d4e:	48 89 74 24 50       	mov    %rsi,0x50(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d53:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2d58:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2d62:	49 8b 82 48 04 00 00 	mov    0x448(%r10),%rax
    2d69:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    2d6e:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2d78:	49 8b 82 f8 04 00 00 	mov    0x4f8(%r10),%rax
    2d7f:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2d89:	49 8b 82 a8 05 00 00 	mov    0x5a8(%r10),%rax
    2d90:	4c 89 4c 24 30       	mov    %r9,0x30(%rsp)
    2d95:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2d9f:	49 8b 82 58 06 00 00 	mov    0x658(%r10),%rax
    2da6:	4c 89 94 24 80 00 00 00 	mov    %r10,0x80(%rsp)
    2dae:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2db8:	49 8b 82 08 07 00 00 	mov    0x708(%r10),%rax
    2dbf:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    2dc4:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2dce:	49 8b 82 b8 07 00 00 	mov    0x7b8(%r10),%rax
    2dd5:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    2dda:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2de4:	e8 b7 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2de9:	be 38 00 00 00       	mov    $0x38,%esi
    2dee:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2df3:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2df6:	e8 a5 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dfb:	be 38 00 00 00       	mov    $0x38,%esi
    2e00:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e05:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e08:	e8 93 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e0d:	be 38 00 00 00       	mov    $0x38,%esi
    2e12:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e17:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e1f:	e8 7c f5 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e24:	be 08 00 00 00       	mov    $0x8,%esi
    2e29:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e2e:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e36:	e8 65 f5 ff ff       	call   23a0 <calloc@plt>
  thread_data[thread_count].type = TIMER;
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2e3b:	be 08 00 00 00       	mov    $0x8,%esi
    2e40:	bf 0f 00 00 00       	mov    $0xf,%edi
  thread_data[thread_count].type = TIMER;
    2e45:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e4d:	49 89 c5             	mov    %rax,%r13
  thread_data[thread_count].task_count = total_barrier_count;
    2e50:	48 8b 05 f1 4b 00 00 	mov    0x4bf1(%rip),%rax        # 7a48 <_IO_stdin_used+0xa48>
  thread_data[thread_count].type = TIMER;
    2e57:	41 c7 82 48 08 00 00 00 00 00 00 	movl   $0x0,0x848(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2e62:	49 89 82 70 08 00 00 	mov    %rax,0x870(%r10)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2e69:	e8 32 f5 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2e6e:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    2e73:	48 8b 4c 24 58       	mov    0x58(%rsp),%rcx
    2e78:	48 8b 74 24 50       	mov    0x50(%rsp),%rsi
    2e7d:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    2e82:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2e86:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    2e8b:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    2e90:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2e94:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    2e99:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
    2ea1:	48 89 48 18          	mov    %rcx,0x18(%rax)
    2ea5:	4c 8b 4c 24 30       	mov    0x30(%rsp),%r9
    2eaa:	48 89 70 20          	mov    %rsi,0x20(%rax)
    2eae:	48 8d 35 72 44 00 00 	lea    0x4472(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2eb5:	48 89 78 30          	mov    %rdi,0x30(%rax)
    2eb9:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    2ebe:	4d 8d b2 40 08 00 00 	lea    0x840(%r10),%r14
    2ec5:	4c 89 10             	mov    %r10,(%rax)
    2ec8:	48 89 78 50          	mov    %rdi,0x50(%rax)
    2ecc:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    2ed1:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2ed5:	ba 0c 00 00 00       	mov    $0xc,%edx
    2eda:	48 89 78 58          	mov    %rdi,0x58(%rax)
    2ede:	49 8d ba a0 09 00 00 	lea    0x9a0(%r10),%rdi
    2ee5:	4c 89 58 38          	mov    %r11,0x38(%rax)
    2ee9:	4c 89 40 40          	mov    %r8,0x40(%rax)
    2eed:	4c 89 48 48          	mov    %r9,0x48(%rax)
    2ef1:	4c 89 70 60          	mov    %r14,0x60(%rax)
    2ef5:	4c 89 78 68          	mov    %r15,0x68(%rax)
    2ef9:	4c 8d 3d 80 09 00 00 	lea    0x980(%rip),%r15        # 3880 <barriered_thread>
    2f00:	48 89 78 70          	mov    %rdi,0x70(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2f04:	49 89 82 50 08 00 00 	mov    %rax,0x850(%r10)
    2f0b:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2f0d:	41 c7 82 58 08 00 00 0c 00 00 00 	movl   $0xc,0x858(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2f18:	41 c7 82 60 08 00 00 02 00 00 00 	movl   $0x2,0x860(%r10)
  thread_data[thread_count].thread_index = 0;
    2f23:	41 c7 82 40 08 00 00 00 00 00 00 	movl   $0x0,0x840(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2f2e:	48 89 bc 24 80 00 00 00 	mov    %rdi,0x80(%rsp)
    2f36:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].thread_index = 0;
    2f3b:	4c 89 94 24 98 00 00 00 	mov    %r10,0x98(%rsp)
    2f43:	e8 08 f5 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2f48:	48 8d b3 a0 02 00 00 	lea    0x2a0(%rbx),%rsi
    2f4f:	49 8d 7d 60          	lea    0x60(%r13),%rdi
    2f53:	4c 89 f1             	mov    %r14,%rcx
    2f56:	48 8d 15 63 0c 00 00 	lea    0xc63(%rip),%rdx        # 3bc0 <timer_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    2f5d:	45 31 f6             	xor    %r14d,%r14d
    2f60:	4c 89 eb             	mov    %r13,%rbx
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2f63:	e8 08 f5 ff ff       	call   2470 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2f68:	44 89 f0             	mov    %r14d,%eax
    2f6b:	4d 89 ee             	mov    %r13,%r14
    2f6e:	41 89 c5             	mov    %eax,%r13d
    thread_data[x].type = WORKER;
    2f71:	c7 45 08 01 00 00 00 	movl   $0x1,0x8(%rbp)
    2f78:	44 89 ea             	mov    %r13d,%edx
    2f7b:	bf 01 00 00 00       	mov    $0x1,%edi
    2f80:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2f82:	c7 45 34 01 00 00 00 	movl   $0x1,0x34(%rbp)
    2f89:	48 8d 35 78 46 00 00 	lea    0x4678(%rip),%rsi        # 7608 <_IO_stdin_used+0x608>
  for (int x = 0 ; x < thread_count ; x++) {
    2f90:	41 83 c5 01          	add    $0x1,%r13d
    2f94:	e8 b7 f4 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2f99:	48 89 e9             	mov    %rbp,%rcx
    2f9c:	4c 89 e6             	mov    %r12,%rsi
    2f9f:	48 89 df             	mov    %rbx,%rdi
    2fa2:	4c 89 fa             	mov    %r15,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2fa5:	48 81 c5 b0 00 00 00 	add    $0xb0,%rbp
    2fac:	48 83 c3 08          	add    $0x8,%rbx
    2fb0:	49 83 c4 38          	add    $0x38,%r12
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2fb4:	e8 b7 f4 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2fb9:	48 8b 55 f0          	mov    -0x10(%rbp),%rdx
    2fbd:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    2fc1:	be 08 00 00 00       	mov    $0x8,%esi
    2fc6:	e8 15 f3 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2fcb:	41 83 fd 0c          	cmp    $0xc,%r13d
    2fcf:	75 a0                	jne    2f71 <main+0x981>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2fd1:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2fd9:	48 8b 1d 70 4a 00 00 	mov    0x4a70(%rip),%rbx        # 7a50 <_IO_stdin_used+0xa50>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2fe0:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    2fe5:	4d 89 f5             	mov    %r14,%r13
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2fe8:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    2fed:	49 89 9a 20 09 00 00 	mov    %rbx,0x920(%r10)
    thread_data[x].type = IO;
    2ff4:	41 c7 82 f8 08 00 00 02 00 00 00 	movl   $0x2,0x8f8(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2fff:	e8 9c f3 ff ff       	call   23a0 <calloc@plt>
    3004:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    300c:	be 00 08 00 00       	mov    $0x800,%esi
    3011:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3013:	49 89 82 38 09 00 00 	mov    %rax,0x938(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    301a:	e8 91 f4 ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    301f:	be 08 00 00 00       	mov    $0x8,%esi
    3024:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3029:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    3031:	41 89 82 40 09 00 00 	mov    %eax,0x940(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3038:	e8 63 f3 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    303d:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    3042:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    3047:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    304f:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3054:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    3059:	4c 8b 74 24 78       	mov    0x78(%rsp),%r14
    305e:	4c 89 58 48          	mov    %r11,0x48(%rax)
    3062:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    3067:	4c 8b 7c 24 60       	mov    0x60(%rsp),%r15
    306c:	4c 89 40 50          	mov    %r8,0x50(%rax)
    3070:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    3075:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    307a:	4c 89 48 58          	mov    %r9,0x58(%rax)
    307e:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3083:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    3088:	4c 89 10             	mov    %r10,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    308b:	49 89 82 00 09 00 00 	mov    %rax,0x900(%r10)
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3092:	41 c7 82 08 09 00 00 0c 00 00 00 	movl   $0xc,0x908(%r10)
    thread_data[x].thread_index = x;
    309d:	41 c7 82 f0 08 00 00 0d 00 00 00 	movl   $0xd,0x8f0(%r10)
      my_thread_data[n] = &thread_data[n]; 
    30a8:	4c 89 70 10          	mov    %r14,0x10(%rax)
    30ac:	48 89 68 18          	mov    %rbp,0x18(%rax)
    30b0:	4c 89 60 20          	mov    %r12,0x20(%rax)
    30b4:	48 89 78 28          	mov    %rdi,0x28(%rax)
    30b8:	bf 01 00 00 00       	mov    $0x1,%edi
    30bd:	48 89 48 30          	mov    %rcx,0x30(%rax)
    30c1:	48 89 70 38          	mov    %rsi,0x38(%rax)
    30c5:	48 8d 35 79 42 00 00 	lea    0x4279(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    30cc:	48 89 50 40          	mov    %rdx,0x40(%rax)
    30d0:	ba 0d 00 00 00       	mov    $0xd,%edx
    30d5:	4c 89 78 08          	mov    %r15,0x8(%rax)
    30d9:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    30db:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    30e0:	e8 6b f3 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    30e5:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    30ea:	49 8d 7d 68          	lea    0x68(%r13),%rdi
    30ee:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    30f6:	48 8d 15 83 1d 00 00 	lea    0x1d83(%rip),%rdx        # 4e80 <io_thread>
    30fd:	48 05 d8 02 00 00    	add    $0x2d8,%rax
    3103:	48 89 c6             	mov    %rax,%rsi
    3106:	e8 65 f3 ff ff       	call   2470 <pthread_create@plt>
    310b:	ba 0e 00 00 00       	mov    $0xe,%edx
    3110:	48 8d 35 45 42 00 00 	lea    0x4245(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    3117:	31 c0                	xor    %eax,%eax
    3119:	bf 01 00 00 00       	mov    $0x1,%edi
    311e:	e8 2d f3 ff ff       	call   2450 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    3123:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    3128:	48 8b 44 24 48       	mov    0x48(%rsp),%rax

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    312d:	be 08 00 00 00       	mov    $0x8,%esi
    3132:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x].task_count = 0;
    3137:	49 89 9a d0 09 00 00 	mov    %rbx,0x9d0(%r10)
    313e:	31 db                	xor    %ebx,%ebx
    thread_data[x].type = EXTERNAL;
    3140:	41 c7 82 a8 09 00 00 03 00 00 00 	movl   $0x3,0x9a8(%r10)
    thread_data[x].buffers = &buffers[buffer_index];
    314b:	49 89 82 e0 09 00 00 	mov    %rax,0x9e0(%r10)
    3152:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3157:	e8 44 f2 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    315c:	4c 8b 54 24 48       	mov    0x48(%rsp),%r10
    3161:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    3166:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    316b:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3170:	4c 89 70 10          	mov    %r14,0x10(%rax)
    3174:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3179:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    317e:	4c 89 10             	mov    %r10,(%rax)
    3181:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    3186:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    318b:	48 89 68 18          	mov    %rbp,0x18(%rax)
    318f:	48 8d 2d 01 42 00 00 	lea    0x4201(%rip),%rbp        # 7397 <_IO_stdin_used+0x397>
    3196:	4c 89 60 20          	mov    %r12,0x20(%rax)
    319a:	4c 8d a4 24 a0 00 00 00 	lea    0xa0(%rsp),%r12
    31a2:	48 89 78 28          	mov    %rdi,0x28(%rax)
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31a6:	49 8d 7d 70          	lea    0x70(%r13),%rdi
      my_thread_data[n] = &thread_data[n]; 
    31aa:	48 89 48 30          	mov    %rcx,0x30(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31ae:	48 8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%rcx
      my_thread_data[n] = &thread_data[n]; 
    31b6:	48 89 70 38          	mov    %rsi,0x38(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31ba:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    31c2:	48 89 50 40          	mov    %rdx,0x40(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31c6:	48 8d 15 33 09 00 00 	lea    0x933(%rip),%rdx        # 3b00 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    31cd:	4c 89 58 48          	mov    %r11,0x48(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31d1:	48 81 c6 10 03 00 00 	add    $0x310,%rsi
      my_thread_data[n] = &thread_data[n]; 
    31d8:	4c 89 40 50          	mov    %r8,0x50(%rax)
    31dc:	4c 89 48 58          	mov    %r9,0x58(%rax)
    thread_data[x].threads = my_thread_data;
    31e0:	49 89 82 b0 09 00 00 	mov    %rax,0x9b0(%r10)
      my_thread_data[n] = &thread_data[n]; 
    31e7:	4c 89 78 08          	mov    %r15,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    31eb:	48 8b 05 66 48 00 00 	mov    0x4866(%rip),%rax        # 7a58 <_IO_stdin_used+0xa58>
    thread_data[x].thread_index = x;
    31f2:	41 c7 82 a0 09 00 00 0e 00 00 00 	movl   $0xe,0x9a0(%r10)
    thread_data[x].thread_count = thread_count;
    31fd:	49 89 82 b8 09 00 00 	mov    %rax,0x9b8(%r10)
    thread_data[x].thread_index = x;
    3204:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3209:	e8 62 f2 ff ff       	call   2470 <pthread_create@plt>
    320e:	48 8d 3d 64 41 00 00 	lea    0x4164(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    3215:	e8 d6 f0 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    321a:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    321f:	90                   	nop
    void * result; 
    pthread_join(thread[x], &result);
    3220:	49 8b 7c dd 00       	mov    0x0(%r13,%rbx,8),%rdi
    3225:	4c 89 e6             	mov    %r12,%rsi
    3228:	e8 c3 f2 ff ff       	call   24f0 <pthread_join@plt>
    322d:	89 da                	mov    %ebx,%edx
    322f:	48 89 ee             	mov    %rbp,%rsi
    3232:	bf 01 00 00 00       	mov    $0x1,%edi
    3237:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3239:	48 83 c3 01          	add    $0x1,%rbx
    323d:	e8 0e f2 ff ff       	call   2450 <__printf_chk@plt>
    3242:	48 83 fb 0f          	cmp    $0xf,%rbx
    3246:	75 d8                	jne    3220 <main+0xc30>
    3248:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    324d:	4d 89 f2             	mov    %r14,%r10
    3250:	4d 8d 6e 28          	lea    0x28(%r14),%r13
    printf("Finished thread %d\n", x);
  }
  long total = 0;
    3254:	45 31 f6             	xor    %r14d,%r14d
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    3257:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    325f:	4d 89 ef             	mov    %r13,%r15
  long received = 0;
    3262:	31 db                	xor    %ebx,%ebx
  long sents = 0;
    3264:	31 ed                	xor    %ebp,%ebp
    3266:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  long ingests = 0;
    326b:	45 31 c9             	xor    %r9d,%r9d
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    326e:	4d 89 f5             	mov    %r14,%r13
    3271:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    if (x % 2 == 1) {
    3276:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    327a:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    327f:	89 f8                	mov    %edi,%eax
    3281:	41 89 fc             	mov    %edi,%r12d
      other = (x + 1) % total_threads;
    3284:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
    3287:	83 e0 01             	and    $0x1,%eax
      other = abs(x - 1) % total_threads;
    328a:	41 83 ec 01          	sub    $0x1,%r12d
      other = (x + 1) % total_threads;
    328e:	89 7c 24 10          	mov    %edi,0x10(%rsp)
      other = abs(x - 1) % total_threads;
    3292:	85 c0                	test   %eax,%eax
    3294:	44 0f 44 e7          	cmove  %edi,%r12d
    3298:	bf 0a 00 00 00       	mov    $0xa,%edi
    329d:	e8 2e f0 ff ff       	call   22d0 <putchar@plt>
    32a2:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    32a7:	bf 01 00 00 00       	mov    $0x1,%edi
    32ac:	48 8d 35 f8 40 00 00 	lea    0x40f8(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    32b3:	48 8b 10             	mov    (%rax),%rdx
    32b6:	31 c0                	xor    %eax,%eax
    32b8:	e8 93 f1 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    32bd:	49 63 57 08          	movslq 0x8(%r15),%rdx
    32c1:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    32c6:	85 d2                	test   %edx,%edx
    32c8:	0f 8e 04 04 00 00    	jle    36d2 <main+0x10e2>
    32ce:	49 8b 07             	mov    (%r15),%rax
    32d1:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
    long v = 0;
    32d5:	31 d2                	xor    %edx,%edx
    32d7:	48 c1 e6 07          	shl    $0x7,%rsi
    32db:	48 05 90 00 00 00    	add    $0x90,%rax
    32e1:	48 01 c6             	add    %rax,%rsi
    32e4:	0f 1f 40 00          	nopl   0x0(%rax)
      v += thread_data[me].tasks[n].v;
    32e8:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    32eb:	48 05 80 01 00 00    	add    $0x180,%rax
    32f1:	48 39 f0             	cmp    %rsi,%rax
    32f4:	75 f2                	jne    32e8 <main+0xcf8>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    32f6:	4d 63 e4             	movslq %r12d,%r12
    32f9:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    32fe:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    3302:	49 8d 04 44          	lea    (%r12,%rax,2),%rax
    3306:	48 c1 e0 04          	shl    $0x4,%rax
    330a:	48 01 f8             	add    %rdi,%rax
    330d:	48 63 70 30          	movslq 0x30(%rax),%rsi
    3311:	85 f6                	test   %esi,%esi
    3313:	7e 29                	jle    333e <main+0xd4e>
      v += thread_data[other].tasks[n].v;
    3315:	48 8b 40 28          	mov    0x28(%rax),%rax
    3319:	48 8d 34 76          	lea    (%rsi,%rsi,2),%rsi
    331d:	48 c1 e6 07          	shl    $0x7,%rsi
    3321:	48 05 90 00 00 00    	add    $0x90,%rax
    3327:	48 01 c6             	add    %rax,%rsi
    332a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3330:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3333:	48 05 80 01 00 00    	add    $0x180,%rax
    3339:	48 39 f0             	cmp    %rsi,%rax
    333c:	75 f2                	jne    3330 <main+0xd40>
    333e:	48 8d 35 7b 40 00 00 	lea    0x407b(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    3345:	bf 01 00 00 00       	mov    $0x1,%edi
    334a:	31 c0                	xor    %eax,%eax
    334c:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    3351:	e8 fa f0 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3356:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    335b:	bf 01 00 00 00       	mov    $0x1,%edi
    3360:	48 8b 30             	mov    (%rax),%rsi
    3363:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    336d:	48 f7 ee             	imul   %rsi
    3370:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3374:	31 c0                	xor    %eax,%eax
    3376:	48 d1 fa             	sar    %rdx
    3379:	48 29 f2             	sub    %rsi,%rdx
    337c:	48 8d 35 ad 42 00 00 	lea    0x42ad(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    3383:	e8 c8 f0 ff ff       	call   2450 <__printf_chk@plt>
    3388:	bf 0a 00 00 00       	mov    $0xa,%edi
    338d:	e8 3e ef ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3392:	49 63 47 08          	movslq 0x8(%r15),%rax
    3396:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    339b:	85 c0                	test   %eax,%eax
    339d:	0f 8e d2 00 00 00    	jle    3475 <main+0xe85>
    33a3:	49 8b 3f             	mov    (%r15),%rdi
    33a6:	48 8d 34 40          	lea    (%rax,%rax,2),%rsi
    33aa:	48 c1 e6 07          	shl    $0x7,%rsi
    33ae:	48 8d 97 88 00 00 00 	lea    0x88(%rdi),%rdx
    33b5:	48 01 d6             	add    %rdx,%rsi
    33b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33c0:	48 8b 42 60          	mov    0x60(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    33c4:	4c 03 2a             	add    (%rdx),%r13
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    33c7:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
      ingests += thread_data[x].tasks[n].ingest_count;
    33ce:	4c 03 b2 d8 fe ff ff 	add    -0x128(%rdx),%r14
      sends += thread_data[x].tasks[n].sends;
    33d5:	4c 03 8a e8 fe ff ff 	add    -0x118(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33dc:	48 03 68 10          	add    0x10(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33e0:	48 03 58 18          	add    0x18(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33e4:	48 03 68 30          	add    0x30(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33e8:	48 03 58 38          	add    0x38(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33ec:	48 03 68 50          	add    0x50(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33f0:	48 03 58 58          	add    0x58(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33f4:	48 03 68 70          	add    0x70(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33f8:	48 03 58 78          	add    0x78(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33fc:	48 03 a8 90 00 00 00 	add    0x90(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3403:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    340a:	48 03 a8 b0 00 00 00 	add    0xb0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3411:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3418:	48 03 a8 d0 00 00 00 	add    0xd0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    341f:	48 03 98 d8 00 00 00 	add    0xd8(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3426:	48 03 a8 f0 00 00 00 	add    0xf0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    342d:	48 03 98 f8 00 00 00 	add    0xf8(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3434:	48 03 a8 10 01 00 00 	add    0x110(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    343b:	48 03 98 18 01 00 00 	add    0x118(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3442:	48 03 a8 30 01 00 00 	add    0x130(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3449:	48 03 98 38 01 00 00 	add    0x138(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3450:	48 03 a8 50 01 00 00 	add    0x150(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3457:	48 03 98 58 01 00 00 	add    0x158(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    345e:	48 03 a8 70 01 00 00 	add    0x170(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3465:	48 03 98 78 01 00 00 	add    0x178(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    346c:	48 39 f2             	cmp    %rsi,%rdx
    346f:	0f 85 4b ff ff ff    	jne    33c0 <main+0xdd0>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3475:	45 31 e4             	xor    %r12d,%r12d
    3478:	49 83 7f 68 00       	cmpq   $0x0,0x68(%r15)
    347d:	7e 77                	jle    34f6 <main+0xf06>
    347f:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    3484:	4c 89 fb             	mov    %r15,%rbx
    3487:	4d 89 e7             	mov    %r12,%r15
    348a:	4d 89 cc             	mov    %r9,%r12
    348d:	0f 1f 00             	nopl   (%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3490:	48 8b 43 58          	mov    0x58(%rbx),%rax
    3494:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    3498:	48 83 ec 08          	sub    $0x8,%rsp
    349c:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    34a1:	49 83 c7 01          	add    $0x1,%r15
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    34a5:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    34a9:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    34b3:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    34b7:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    34bb:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    34be:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    34c2:	4c 2b 01             	sub    (%rcx),%r8
    34c5:	31 c0                	xor    %eax,%eax
    34c7:	8b 49 20             	mov    0x20(%rcx),%ecx
    34ca:	56                   	push   %rsi
    34cb:	48 8d 35 7e 41 00 00 	lea    0x417e(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    34d2:	48 c1 ea 12          	shr    $0x12,%rdx
    34d6:	49 89 d1             	mov    %rdx,%r9
    34d9:	ba 02 00 00 00       	mov    $0x2,%edx
    34de:	e8 6d ef ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    34e3:	58                   	pop    %rax
    34e4:	5a                   	pop    %rdx
    34e5:	4c 39 7b 68          	cmp    %r15,0x68(%rbx)
    34e9:	7f a5                	jg     3490 <main+0xea0>
    34eb:	49 89 df             	mov    %rbx,%r15
    34ee:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    34f3:	4d 89 e1             	mov    %r12,%r9
  for (int x = 0 ; x < thread_count ; x++) {
    34f6:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    34fc:	49 81 c7 b0 00 00 00 	add    $0xb0,%r15
    3503:	83 7c 24 10 0c       	cmpl   $0xc,0x10(%rsp)
    3508:	0f 85 68 fd ff ff    	jne    3276 <main+0xc86>
    350e:	4c 89 ea             	mov    %r13,%rdx
    3511:	48 8d 35 b5 3e 00 00 	lea    0x3eb5(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    3518:	31 c0                	xor    %eax,%eax
    351a:	4d 89 cf             	mov    %r9,%r15
    351d:	bf 01 00 00 00       	mov    $0x1,%edi
    3522:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3527:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    3531:	e8 1a ef ff ff       	call   2450 <__printf_chk@plt>
    3536:	bf 0a 00 00 00       	mov    $0xa,%edi
    353b:	e8 90 ed ff ff       	call   22d0 <putchar@plt>
    3540:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    3545:	bf 01 00 00 00       	mov    $0x1,%edi
    354a:	48 8d 35 4f 41 00 00 	lea    0x414f(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    3551:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3555:	31 c0                	xor    %eax,%eax
    3557:	e8 f4 ee ff ff       	call   2450 <__printf_chk@plt>
    355c:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3561:	bf 01 00 00 00       	mov    $0x1,%edi
    3566:	48 8d 35 5b 41 00 00 	lea    0x415b(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    356d:	4c 89 c8             	mov    %r9,%rax
    3570:	49 c1 f9 3f          	sar    $0x3f,%r9
    3574:	49 f7 ec             	imul   %r12
    3577:	31 c0                	xor    %eax,%eax
    3579:	48 d1 fa             	sar    %rdx
    357c:	4c 29 ca             	sub    %r9,%rdx
    357f:	e8 cc ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3584:	4c 89 f8             	mov    %r15,%rax
    3587:	4d 89 fb             	mov    %r15,%r11
    358a:	bf 01 00 00 00       	mov    $0x1,%edi
    358f:	49 f7 ec             	imul   %r12
    3592:	49 c1 fb 3f          	sar    $0x3f,%r11
    3596:	48 8d 35 5b 41 00 00 	lea    0x415b(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    359d:	31 c0                	xor    %eax,%eax
    359f:	48 d1 fa             	sar    %rdx
    35a2:	4c 29 da             	sub    %r11,%rdx
    35a5:	e8 a6 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    35aa:	4c 89 e8             	mov    %r13,%rax
    35ad:	4c 89 e9             	mov    %r13,%rcx
    35b0:	bf 01 00 00 00       	mov    $0x1,%edi
    35b5:	49 f7 ec             	imul   %r12
    35b8:	48 c1 f9 3f          	sar    $0x3f,%rcx
    35bc:	48 8d 35 65 41 00 00 	lea    0x4165(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    35c3:	31 c0                	xor    %eax,%eax
    35c5:	48 d1 fa             	sar    %rdx
    35c8:	48 29 ca             	sub    %rcx,%rdx
    35cb:	e8 80 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    35d0:	48 89 e8             	mov    %rbp,%rax
    35d3:	48 c1 fd 3f          	sar    $0x3f,%rbp
    35d7:	48 8d 35 03 3e 00 00 	lea    0x3e03(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    35de:	49 f7 ec             	imul   %r12
    35e1:	bf 01 00 00 00       	mov    $0x1,%edi
    35e6:	31 c0                	xor    %eax,%eax
    35e8:	48 d1 fa             	sar    %rdx
    35eb:	48 29 ea             	sub    %rbp,%rdx
    35ee:	e8 5d ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    35f3:	48 89 d8             	mov    %rbx,%rax
    35f6:	48 c1 fb 3f          	sar    $0x3f,%rbx
    35fa:	48 8d 35 f1 3d 00 00 	lea    0x3df1(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    3601:	49 f7 ec             	imul   %r12
    3604:	bf 01 00 00 00       	mov    $0x1,%edi
    3609:	48 d1 fa             	sar    %rdx
    360c:	48 29 da             	sub    %rbx,%rdx
    360f:	31 c0                	xor    %eax,%eax
    3611:	e8 3a ee ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3616:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    361e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3627:	0f 85 ac 00 00 00    	jne    36d9 <main+0x10e9>
    362d:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    3634:	31 c0                	xor    %eax,%eax
    3636:	5b                   	pop    %rbx
    3637:	5d                   	pop    %rbp
    3638:	41 5c                	pop    %r12
    363a:	41 5d                	pop    %r13
    363c:	41 5e                	pop    %r14
    363e:	41 5f                	pop    %r15
    3640:	c3                   	ret
          thread_data[x].tasks[y].run = barriered_work; 
    3641:	48 8d 05 f8 21 00 00 	lea    0x21f8(%rip),%rax        # 5840 <barriered_work>
    3648:	bb 02 00 00 00       	mov    $0x2,%ebx
    364d:	49 89 85 98 00 00 00 	mov    %rax,0x98(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3654:	e9 0c f3 ff ff       	jmp    2965 <main+0x375>
      other = (x + 1) % total_threads;
    3659:	b8 89 88 88 88       	mov    $0x88888889,%eax
    365e:	45 89 fe             	mov    %r15d,%r14d
      my_thread_data[0] = &thread_data[x]; 
    3661:	4d 89 4d 00          	mov    %r9,0x0(%r13)
    3665:	4c 89 c9             	mov    %r9,%rcx
      other = (x + 1) % total_threads;
    3668:	4c 0f af f0          	imul   %rax,%r14
    366c:	bf 01 00 00 00       	mov    $0x1,%edi
    3671:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    3676:	48 8d 35 8c 3c 00 00 	lea    0x3c8c(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      thread_data[x].thread_index = 0;
    367d:	41 c7 01 00 00 00 00 	movl   $0x0,(%r9)
      other = (x + 1) % total_threads;
    3684:	49 c1 ee 23          	shr    $0x23,%r14
    3688:	44 89 f0             	mov    %r14d,%eax
    368b:	c1 e0 04             	shl    $0x4,%eax
    368e:	44 29 f0             	sub    %r14d,%eax
    3691:	45 89 fe             	mov    %r15d,%r14d
    3694:	41 29 c6             	sub    %eax,%r14d
      my_thread_data[1] = &thread_data[other]; 
    3697:	49 63 c6             	movslq %r14d,%rax
    369a:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    369e:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    36a2:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    36a7:	89 ea                	mov    %ebp,%edx
    36a9:	49 c1 e0 04          	shl    $0x4,%r8
    36ad:	49 01 c0             	add    %rax,%r8
    36b0:	31 c0                	xor    %eax,%eax
    36b2:	4d 89 45 08          	mov    %r8,0x8(%r13)
    36b6:	e8 95 ed ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    36bb:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    36c0:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    36c5:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    36ca:	49 89 c4             	mov    %rax,%r12
    36cd:	e9 72 f1 ff ff       	jmp    2844 <main+0x254>
    long v = 0;
    36d2:	31 d2                	xor    %edx,%edx
    36d4:	e9 1d fc ff ff       	jmp    32f6 <main+0xd06>
}
    36d9:	e8 52 ec ff ff       	call   2330 <__stack_chk_fail@plt>
    36de:	66 90                	xchg   %ax,%ax

00000000000036e0 <_start>:
    36e0:	f3 0f 1e fa          	endbr64
    36e4:	31 ed                	xor    %ebp,%ebp
    36e6:	49 89 d1             	mov    %rdx,%r9
    36e9:	5e                   	pop    %rsi
    36ea:	48 89 e2             	mov    %rsp,%rdx
    36ed:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    36f1:	50                   	push   %rax
    36f2:	54                   	push   %rsp
    36f3:	45 31 c0             	xor    %r8d,%r8d
    36f6:	31 c9                	xor    %ecx,%ecx
    36f8:	48 8d 3d f1 ee ff ff 	lea    -0x110f(%rip),%rdi        # 25f0 <main>
    36ff:	ff 15 d3 68 00 00    	call   *0x68d3(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3705:	f4                   	hlt
    3706:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003710 <deregister_tm_clones>:
    3710:	48 8d 3d 09 69 00 00 	lea    0x6909(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3717:	48 8d 05 02 69 00 00 	lea    0x6902(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    371e:	48 39 f8             	cmp    %rdi,%rax
    3721:	74 15                	je     3738 <deregister_tm_clones+0x28>
    3723:	48 8b 05 b6 68 00 00 	mov    0x68b6(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    372a:	48 85 c0             	test   %rax,%rax
    372d:	74 09                	je     3738 <deregister_tm_clones+0x28>
    372f:	ff e0                	jmp    *%rax
    3731:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3738:	c3                   	ret
    3739:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003740 <register_tm_clones>:
    3740:	48 8d 3d d9 68 00 00 	lea    0x68d9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3747:	48 8d 35 d2 68 00 00 	lea    0x68d2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    374e:	48 29 fe             	sub    %rdi,%rsi
    3751:	48 89 f0             	mov    %rsi,%rax
    3754:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3758:	48 c1 f8 03          	sar    $0x3,%rax
    375c:	48 01 c6             	add    %rax,%rsi
    375f:	48 d1 fe             	sar    %rsi
    3762:	74 14                	je     3778 <register_tm_clones+0x38>
    3764:	48 8b 05 85 68 00 00 	mov    0x6885(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    376b:	48 85 c0             	test   %rax,%rax
    376e:	74 08                	je     3778 <register_tm_clones+0x38>
    3770:	ff e0                	jmp    *%rax
    3772:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3778:	c3                   	ret
    3779:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003780 <__do_global_dtors_aux>:
    3780:	f3 0f 1e fa          	endbr64
    3784:	80 3d 9d 68 00 00 00 	cmpb   $0x0,0x689d(%rip)        # a028 <completed.0>
    378b:	75 2b                	jne    37b8 <__do_global_dtors_aux+0x38>
    378d:	55                   	push   %rbp
    378e:	48 83 3d 62 68 00 00 00 	cmpq   $0x0,0x6862(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3796:	48 89 e5             	mov    %rsp,%rbp
    3799:	74 0c                	je     37a7 <__do_global_dtors_aux+0x27>
    379b:	48 8b 3d 66 68 00 00 	mov    0x6866(%rip),%rdi        # a008 <__dso_handle>
    37a2:	e8 09 eb ff ff       	call   22b0 <__cxa_finalize@plt>
    37a7:	e8 64 ff ff ff       	call   3710 <deregister_tm_clones>
    37ac:	c6 05 75 68 00 00 01 	movb   $0x1,0x6875(%rip)        # a028 <completed.0>
    37b3:	5d                   	pop    %rbp
    37b4:	c3                   	ret
    37b5:	0f 1f 00             	nopl   (%rax)
    37b8:	c3                   	ret
    37b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037c0 <frame_dummy>:
    37c0:	f3 0f 1e fa          	endbr64
    37c4:	e9 77 ff ff ff       	jmp    3740 <register_tm_clones>
    37c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037d0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    37d0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    37d4:	48 8b 87 a8 00 00 00 	mov    0xa8(%rdi),%rax
    37db:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    37df:	48 83 87 90 00 00 00 01 	addq   $0x1,0x90(%rdi)
  if (protected->balance > 0) {
    37e7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    37eb:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    37ef:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    37f6:	48 85 c9             	test   %rcx,%rcx
    37f9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3800:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3804:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3808:	31 c0                	xor    %eax,%eax
    380a:	c3                   	ret
    380b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003810 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3810:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3814:	48 63 87 bc 00 00 00 	movslq 0xbc(%rdi),%rax
    381b:	85 c0                	test   %eax,%eax
    381d:	7e 4f                	jle    386e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    381f:	48 8b 8f a8 00 00 00 	mov    0xa8(%rdi),%rcx
    3826:	48 63 b7 b0 00 00 00 	movslq 0xb0(%rdi),%rsi
    382d:	48 8b 51 10          	mov    0x10(%rcx),%rdx
    3831:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3835:	48 8b 71 28          	mov    0x28(%rcx),%rsi
    3839:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
    383d:	31 c0                	xor    %eax,%eax
    383f:	48 c1 e1 07          	shl    $0x7,%rcx
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3843:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    3847:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3850:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3858:	c7 84 06 b8 00 00 00 01 00 00 00 	movl   $0x1,0xb8(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3863:	48 05 80 01 00 00    	add    $0x180,%rax
    3869:	48 39 c1             	cmp    %rax,%rcx
    386c:	75 e2                	jne    3850 <barriered_reset+0x40>
  asm volatile ("sfence" ::: "memory");
    386e:	0f ae f8             	sfence
}
    3871:	31 c0                	xor    %eax,%eax
    3873:	c3                   	ret
    3874:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    387f:	90                   	nop

0000000000003880 <barriered_thread>:
void* barriered_thread(void *arg) {
    3880:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3884:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    3888:	0f 85 69 02 00 00    	jne    3af7 <barriered_thread+0x277>
void* barriered_thread(void *arg) {
    388e:	41 54                	push   %r12
  int waiting = 0;
    3890:	45 31 d2             	xor    %r10d,%r10d
    3893:	49 89 fc             	mov    %rdi,%r12
void* barriered_thread(void *arg) {
    3896:	55                   	push   %rbp
    3897:	53                   	push   %rbx
    if (t >= data->task_count) {
    3898:	44 8b 47 30          	mov    0x30(%rdi),%r8d
  int t = 0;
    389c:	31 db                	xor    %ebx,%ebx
    389e:	66 90                	xchg   %ax,%ax
    if (t >= data->task_count) {
    38a0:	44 39 c3             	cmp    %r8d,%ebx
    38a3:	0f 8d 6f 01 00 00    	jge    3a18 <barriered_thread+0x198>
    38a9:	48 63 c3             	movslq %ebx,%rax
    38ac:	48 8d 2c 40          	lea    (%rax,%rax,2),%rbp
    38b0:	48 c1 e5 07          	shl    $0x7,%rbp
    38b4:	eb 1d                	jmp    38d3 <barriered_thread+0x53>
    38b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (; t < data->task_count; t++) {
    38c0:	83 c3 01             	add    $0x1,%ebx
    38c3:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    38ca:	44 39 c3             	cmp    %r8d,%ebx
    38cd:	0f 8d 2d 01 00 00    	jge    3a00 <barriered_thread+0x180>
      if (data->tasks[t].available == 1) {
    38d3:	49 8b 44 24 28       	mov    0x28(%r12),%rax
    38d8:	48 8d 14 28          	lea    (%rax,%rbp,1),%rdx
    38dc:	83 ba b8 00 00 00 01 	cmpl   $0x1,0xb8(%rdx)
    38e3:	75 db                	jne    38c0 <barriered_thread+0x40>
        if (t > 0) {
    38e5:	85 db                	test   %ebx,%ebx
    38e7:	0f 8e 43 01 00 00    	jle    3a30 <barriered_thread+0x1b0>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    38ed:	45 8b 4c 24 18       	mov    0x18(%r12),%r9d
          previous = t - 1;
    38f2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    38f5:	45 85 c9             	test   %r9d,%r9d
    38f8:	0f 8e ea 01 00 00    	jle    3ae8 <barriered_thread+0x268>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    38fe:	48 63 c1             	movslq %ecx,%rax
    3901:	8b ba 80 00 00 00    	mov    0x80(%rdx),%edi
    3907:	49 63 d1             	movslq %r9d,%rdx
        int arrived = 0; 
    390a:	45 31 db             	xor    %r11d,%r11d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    390d:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
    3911:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    3916:	48 c1 e1 07          	shl    $0x7,%rcx
    391a:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    391e:	66 90                	xchg   %ax,%ax
    3920:	48 8b 10             	mov    (%rax),%rdx
    3923:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    3927:	3b bc 0a 80 00 00 00 	cmp    0x80(%rdx,%rcx,1),%edi
    392e:	75 04                	jne    3934 <barriered_thread+0xb4>
            arrived++;
    3930:	41 83 c3 01          	add    $0x1,%r11d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3934:	48 83 c0 08          	add    $0x8,%rax
    3938:	48 39 f0             	cmp    %rsi,%rax
    393b:	75 e3                	jne    3920 <barriered_thread+0xa0>
        if (arrived == 0 || arrived == data->thread_count) {
    393d:	45 39 cb             	cmp    %r9d,%r11d
    3940:	74 09                	je     394b <barriered_thread+0xcb>
    3942:	45 85 db             	test   %r11d,%r11d
    3945:	0f 85 b5 00 00 00    	jne    3a00 <barriered_thread+0x180>
          if (waiting == 1) {
    394b:	41 83 fa 01          	cmp    $0x1,%r10d
    394f:	0f 84 fb 00 00 00    	je     3a50 <barriered_thread+0x1d0>
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    3955:	85 db                	test   %ebx,%ebx
    3957:	75 10                	jne    3969 <barriered_thread+0xe9>
    3959:	49 8b 74 24 70       	mov    0x70(%r12),%rsi
    395e:	49 3b 74 24 78       	cmp    0x78(%r12),%rsi
    3963:	0f 8c 67 01 00 00    	jl     3ad0 <barriered_thread+0x250>
    3969:	49 8b 44 24 28       	mov    0x28(%r12),%rax
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    396e:	49 63 0c 24          	movslq (%r12),%rcx
    3972:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
          data->tasks[t].available = 0;
    3977:	48 01 e8             	add    %rbp,%rax
    397a:	c7 80 b8 00 00 00 00 00 00 00 	movl   $0x0,0xb8(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3984:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    3988:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
    398c:	48 01 ef             	add    %rbp,%rdi
    398f:	ff 90 98 00 00 00    	call   *0x98(%rax)
          data->tasks[t].arrived++;
    3995:	49 8b 44 24 28       	mov    0x28(%r12),%rax
    399a:	48 01 e8             	add    %rbp,%rax
    399d:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    39a4:	41 8b 44 24 30       	mov    0x30(%r12),%eax
          data->iteration_count++;
    39a9:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    39af:	83 e8 01             	sub    $0x1,%eax
    39b2:	39 d8                	cmp    %ebx,%eax
    39b4:	0f 84 e6 00 00 00    	je     3aa0 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    39ba:	0f ae f8             	sfence
            data->task_snapshot[data->task_timestamp_count].task = t;
    39bd:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    39c5:	bf 04 00 00 00       	mov    $0x4,%edi
    for (; t < data->task_count; t++) {
    39ca:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
            data->task_snapshot[data->task_timestamp_count].task = t;
    39d1:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    39d5:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    39dd:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    39e1:	89 5e 20             	mov    %ebx,0x20(%rsi)
    for (; t < data->task_count; t++) {
    39e4:	83 c3 01             	add    $0x1,%ebx
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    39e7:	e8 24 e9 ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    39ec:	45 8b 44 24 30       	mov    0x30(%r12),%r8d
            waiting = 1;
    39f1:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    for (; t < data->task_count; t++) {
    39f7:	44 39 c3             	cmp    %r8d,%ebx
    39fa:	0f 8c d3 fe ff ff    	jl     38d3 <barriered_thread+0x53>
  while (data->running == 1) {
    3a00:	41 8b 44 24 34       	mov    0x34(%r12),%eax
    3a05:	83 f8 01             	cmp    $0x1,%eax
    3a08:	0f 84 92 fe ff ff    	je     38a0 <barriered_thread+0x20>
}
    3a0e:	5b                   	pop    %rbx
    3a0f:	31 c0                	xor    %eax,%eax
    3a11:	5d                   	pop    %rbp
    3a12:	41 5c                	pop    %r12
    3a14:	c3                   	ret
    3a15:	0f 1f 00             	nopl   (%rax)
      data->cycles++;
    3a18:	49 83 84 24 98 00 00 00 01 	addq   $0x1,0x98(%r12)
    for (; t < data->task_count; t++) {
    3a21:	45 85 c0             	test   %r8d,%r8d
    3a24:	7e f2                	jle    3a18 <barriered_thread+0x198>
    3a26:	31 db                	xor    %ebx,%ebx
    3a28:	e9 7c fe ff ff       	jmp    38a9 <barriered_thread+0x29>
    3a2d:	0f 1f 00             	nopl   (%rax)
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3a30:	45 8b 4c 24 18       	mov    0x18(%r12),%r9d
          previous = data->task_count - 1;
    3a35:	41 8d 48 ff          	lea    -0x1(%r8),%ecx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3a39:	45 85 c9             	test   %r9d,%r9d
    3a3c:	0f 8f bc fe ff ff    	jg     38fe <barriered_thread+0x7e>
          if (waiting == 1) {
    3a42:	41 83 fa 01          	cmp    $0x1,%r10d
    3a46:	0f 85 09 ff ff ff    	jne    3955 <barriered_thread+0xd5>
    3a4c:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3a50:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
    3a58:	bf 04 00 00 00       	mov    $0x4,%edi
    3a5d:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3a61:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3a69:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3a6e:	e8 9d e8 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3a73:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
    3a7b:	48 83 c0 01          	add    $0x1,%rax
    3a7f:	48 99                	cqto
    3a81:	49 f7 bc 24 90 00 00 00 	idivq  0x90(%r12)
    3a89:	49 89 94 24 88 00 00 00 	mov    %rdx,0x88(%r12)
            waiting = 0; 
    3a91:	e9 bf fe ff ff       	jmp    3955 <barriered_thread+0xd5>
    3a96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3aa0:	49 8b 74 24 70       	mov    0x70(%r12),%rsi
    3aa5:	49 3b 74 24 78       	cmp    0x78(%r12),%rsi
    3aaa:	0f 8d 0a ff ff ff    	jge    39ba <barriered_thread+0x13a>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    3ab0:	48 c1 e6 04          	shl    $0x4,%rsi
    3ab4:	bf 04 00 00 00       	mov    $0x4,%edi
    3ab9:	49 03 74 24 60       	add    0x60(%r12),%rsi
    3abe:	e8 4d e8 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3ac3:	49 83 44 24 70 01    	addq   $0x1,0x70(%r12)
    3ac9:	e9 ec fe ff ff       	jmp    39ba <barriered_thread+0x13a>
    3ace:	66 90                	xchg   %ax,%ax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3ad0:	48 c1 e6 04          	shl    $0x4,%rsi
    3ad4:	bf 04 00 00 00       	mov    $0x4,%edi
    3ad9:	49 03 74 24 58       	add    0x58(%r12),%rsi
    3ade:	e8 2d e8 ff ff       	call   2310 <clock_gettime@plt>
    3ae3:	e9 81 fe ff ff       	jmp    3969 <barriered_thread+0xe9>
          if (waiting == 1) {
    3ae8:	41 83 fa 01          	cmp    $0x1,%r10d
    3aec:	0f 85 7c fe ff ff    	jne    396e <barriered_thread+0xee>
    3af2:	e9 59 ff ff ff       	jmp    3a50 <barriered_thread+0x1d0>
}
    3af7:	31 c0                	xor    %eax,%eax
    3af9:	c3                   	ret
    3afa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000003b00 <external_thread>:
void * external_thread(void *arg) {
    3b00:	f3 0f 1e fa          	endbr64
    3b04:	41 55                	push   %r13
    3b06:	41 54                	push   %r12
    3b08:	55                   	push   %rbp
    3b09:	53                   	push   %rbx
    3b0a:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    3b0e:	66 0f 6f 05 2a 3e 00 00 	movdqa 0x3e2a(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
void * external_thread(void *arg) {
    3b16:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3b1f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3b24:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3b26:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
  struct timespec req = {
    3b2a:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    3b2e:	75 64                	jne    3b94 <external_thread+0x94>
    3b30:	49 89 fd             	mov    %rdi,%r13
    3b33:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3b38:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    3b3b:	4c 8d 25 c2 34 00 00 	lea    0x34c2(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    3b42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    nanosleep(&req , &rem);
    3b48:	48 89 ee             	mov    %rbp,%rsi
    3b4b:	48 89 df             	mov    %rbx,%rdi
    3b4e:	e8 fd e7 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3b53:	49 8b 45 40          	mov    0x40(%r13),%rax
    3b57:	48 63 10             	movslq (%rax),%rdx
    3b5a:	85 d2                	test   %edx,%edx
    3b5c:	7e 2c                	jle    3b8a <external_thread+0x8a>
    3b5e:	48 8b 40 08          	mov    0x8(%rax),%rax
    3b62:	48 c1 e2 04          	shl    $0x4,%rdx
    3b66:	48 01 c2             	add    %rax,%rdx
    3b69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    3b70:	8b 48 08             	mov    0x8(%rax),%ecx
    3b73:	85 c9                	test   %ecx,%ecx
    3b75:	75 0a                	jne    3b81 <external_thread+0x81>
        data->buffers->buffer[x].data = "Hello world";
    3b77:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    3b7a:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3b81:	48 83 c0 10          	add    $0x10,%rax
    3b85:	48 39 c2             	cmp    %rax,%rdx
    3b88:	75 e6                	jne    3b70 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    3b8a:	0f ae f0             	mfence
  while (data->running == 1) {
    3b8d:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
    3b92:	74 b4                	je     3b48 <external_thread+0x48>
}
    3b94:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3b99:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3ba2:	75 0d                	jne    3bb1 <external_thread+0xb1>
    3ba4:	48 83 c4 38          	add    $0x38,%rsp
    3ba8:	31 c0                	xor    %eax,%eax
    3baa:	5b                   	pop    %rbx
    3bab:	5d                   	pop    %rbp
    3bac:	41 5c                	pop    %r12
    3bae:	41 5d                	pop    %r13
    3bb0:	c3                   	ret
    3bb1:	e8 7a e7 ff ff       	call   2330 <__stack_chk_fail@plt>
    3bb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003bc0 <timer_thread>:
void* timer_thread(void *arg) {
    3bc0:	f3 0f 1e fa          	endbr64
    3bc4:	41 57                	push   %r15
    3bc6:	48 8d 35 43 34 00 00 	lea    0x3443(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3bcd:	49 89 ff             	mov    %rdi,%r15
    3bd0:	41 56                	push   %r14
    3bd2:	41 55                	push   %r13
    3bd4:	41 54                	push   %r12
    3bd6:	55                   	push   %rbp
    3bd7:	53                   	push   %rbx
    3bd8:	48 83 ec 58          	sub    $0x58,%rsp
    3bdc:	8b 17                	mov    (%rdi),%edx
    3bde:	bf 01 00 00 00       	mov    $0x1,%edi
    3be3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3bec:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3bf1:	31 c0                	xor    %eax,%eax
    3bf3:	e8 58 e8 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3bf8:	66 0f 6f 05 40 3d 00 00 	movdqa 0x3d40(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3c00:	ba 88 13 00 00       	mov    $0x1388,%edx
    3c05:	31 c0                	xor    %eax,%eax
    3c07:	48 8d 35 14 34 00 00 	lea    0x3414(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3c0e:	bf 01 00 00 00       	mov    $0x1,%edi
    3c13:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3c18:	e8 33 e8 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3c1d:	45 8b 6f 34          	mov    0x34(%r15),%r13d
    3c21:	45 85 ed             	test   %r13d,%r13d
    3c24:	0f 84 a7 00 00 00    	je     3cd1 <timer_thread+0x111>
  int n = 0;
    3c2a:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    3c2d:	45 31 ed             	xor    %r13d,%r13d
    3c30:	49 89 e4             	mov    %rsp,%r12
    y++;
    3c33:	31 db                	xor    %ebx,%ebx
    3c35:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    3c3a:	48 89 ef             	mov    %rbp,%rdi
    3c3d:	4c 89 e6             	mov    %r12,%rsi
    n++;
    3c40:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3c44:	e8 07 e7 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c49:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3c4d:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c51:	85 c0                	test   %eax,%eax
    3c53:	7e 54                	jle    3ca9 <timer_thread+0xe9>
    3c55:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3c59:	4f 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%r8
    3c5e:	49 c1 e0 07          	shl    $0x7,%r8
    3c62:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3c66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3c70:	4c 8b 19             	mov    (%rcx),%r11
    3c73:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c75:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3c79:	99                   	cltd
    3c7a:	41 f7 7b 30          	idivl  0x30(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    3c7e:	49 8b 73 28          	mov    0x28(%r11),%rsi
    3c82:	48 63 d2             	movslq %edx,%rdx
    3c85:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
    3c89:	48 c1 e0 07          	shl    $0x7,%rax
    3c8d:	c7 84 06 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rsi,%rax,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3c98:	42 c7 84 06 c0 00 00 00 00 00 00 00 	movl   $0x0,0xc0(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ca4:	49 39 c9             	cmp    %rcx,%r9
    3ca7:	75 c7                	jne    3c70 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    3ca9:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3cac:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3cb0:	41 8b 57 34          	mov    0x34(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3cb4:	48 8b 00             	mov    (%rax),%rax
    y++;
    3cb7:	39 78 30             	cmp    %edi,0x30(%rax)
    3cba:	0f 4e fb             	cmovle %ebx,%edi
    3cbd:	4c 63 ef             	movslq %edi,%r13
  while (data->running && n < times) {
    3cc0:	85 d2                	test   %edx,%edx
    3cc2:	74 0d                	je     3cd1 <timer_thread+0x111>
    3cc4:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3ccb:	0f 85 69 ff ff ff    	jne    3c3a <timer_thread+0x7a>
    3cd1:	48 8d 3d 60 33 00 00 	lea    0x3360(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3cd8:	e8 13 e6 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3cdd:	49 63 47 1c          	movslq 0x1c(%r15),%rax
    3ce1:	85 c0                	test   %eax,%eax
    3ce3:	0f 8e 84 00 00 00    	jle    3d6d <timer_thread+0x1ad>
    for (int y = 0 ; y < data->task_count ; y++) {
    3ce9:	41 8b 57 30          	mov    0x30(%r15),%edx
    3ced:	85 d2                	test   %edx,%edx
    3cef:	7e 7c                	jle    3d6d <timer_thread+0x1ad>
    3cf1:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    3cf9:	48 63 c2             	movslq %edx,%rax
      data->threads[x]->tasks[y].sending = 0;
    3cfc:	4d 8b 4f 10          	mov    0x10(%r15),%r9
    3d00:	31 f6                	xor    %esi,%esi
    3d02:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    3d06:	48 c1 e0 07          	shl    $0x7,%rax
    3d0a:	4c 8d 80 f8 00 00 00 	lea    0xf8(%rax),%r8
    3d11:	49 8b 04 31          	mov    (%r9,%rsi,1),%rax
    3d15:	48 8b 78 28          	mov    0x28(%rax),%rdi
    3d19:	4a 8d 14 07          	lea    (%rdi,%r8,1),%rdx
    3d1d:	48 8d 87 f8 00 00 00 	lea    0xf8(%rdi),%rax
    3d24:	49 89 d2             	mov    %rdx,%r10
    3d27:	49 29 c2             	sub    %rax,%r10
    3d2a:	41 81 e2 80 00 00 00 	and    $0x80,%r10d
    3d31:	74 16                	je     3d49 <timer_thread+0x189>
    for (int y = 0 ; y < data->task_count ; y++) {
    3d33:	48 8d 87 78 02 00 00 	lea    0x278(%rdi),%rax
      data->threads[x]->tasks[y].sending = 0;
    3d3a:	c7 87 f8 00 00 00 00 00 00 00 	movl   $0x0,0xf8(%rdi)
    for (int y = 0 ; y < data->task_count ; y++) {
    3d44:	48 39 c2             	cmp    %rax,%rdx
    3d47:	74 1b                	je     3d64 <timer_thread+0x1a4>
      data->threads[x]->tasks[y].sending = 0;
    3d49:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3d4f:	48 05 00 03 00 00    	add    $0x300,%rax
      data->threads[x]->tasks[y].sending = 0;
    3d55:	c7 80 80 fe ff ff 00 00 00 00 	movl   $0x0,-0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3d5f:	48 39 c2             	cmp    %rax,%rdx
    3d62:	75 e5                	jne    3d49 <timer_thread+0x189>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d64:	48 83 c6 08          	add    $0x8,%rsi
    3d68:	48 39 f1             	cmp    %rsi,%rcx
    3d6b:	75 a4                	jne    3d11 <timer_thread+0x151>
  asm volatile ("mfence" ::: "memory");
    3d6d:	0f ae f0             	mfence
  struct timespec drain = {
    3d70:	66 0f 6f 05 d8 3b 00 00 	movdqa 0x3bd8(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3d78:	48 8d 2d de 32 00 00 	lea    0x32de(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3d7f:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d84:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3d88:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d8c:	85 c0                	test   %eax,%eax
    3d8e:	7e 50                	jle    3de0 <timer_thread+0x220>
    3d90:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3d94:	4d 63 ed             	movslq %r13d,%r13
    3d97:	4f 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%r8
    3d9c:	49 c1 e0 07          	shl    $0x7,%r8
    3da0:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3da4:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3da8:	48 8b 19             	mov    (%rcx),%rbx
    3dab:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3dad:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3db1:	99                   	cltd
    3db2:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3db5:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3db9:	48 63 c2             	movslq %edx,%rax
    3dbc:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    3dc0:	48 c1 e0 07          	shl    $0x7,%rax
    3dc4:	c7 84 06 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rsi,%rax,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3dcf:	42 c7 84 06 c0 00 00 00 00 00 00 00 	movl   $0x0,0xc0(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ddb:	49 39 c9             	cmp    %rcx,%r9
    3dde:	75 c8                	jne    3da8 <timer_thread+0x1e8>
    asm volatile ("mfence" ::: "memory");
    3de0:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3de3:	49 8b 47 10          	mov    0x10(%r15),%rax
    y++;
    3de7:	45 31 ed             	xor    %r13d,%r13d
    if (y >= data->threads[0]->task_count) {
    3dea:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3ded:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3df0:	44 0f 4f ef          	cmovg  %edi,%r13d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3df4:	41 8b 7f 20          	mov    0x20(%r15),%edi
    3df8:	85 ff                	test   %edi,%edi
    3dfa:	0f 8e c0 00 00 00    	jle    3ec0 <timer_thread+0x300>
    3e00:	45 31 e4             	xor    %r12d,%r12d
    int all_empty = 1;
    3e03:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3e09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3e10:	4a 8d 1c e5 00 00 00 00 	lea    0x0(,%r12,8),%rbx
            all_empty = 0;
    3e18:	45 31 f6             	xor    %r14d,%r14d
    3e1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3e20:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3e24:	4b 8d 04 76          	lea    (%r14,%r14,2),%rax
    3e28:	48 c1 e0 07          	shl    $0x7,%rax
    3e2c:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3e30:	31 d2                	xor    %edx,%edx
    3e32:	48 8b 80 e8 00 00 00 	mov    0xe8(%rax),%rax
    3e39:	eb 15                	jmp    3e50 <timer_thread+0x290>
    3e3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3e40:	4d 85 c0             	test   %r8,%r8
    3e43:	7f 1f                	jg     3e64 <timer_thread+0x2a4>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3e45:	83 c2 01             	add    $0x1,%edx
    3e48:	48 83 c0 20          	add    $0x20,%rax
    3e4c:	39 fa                	cmp    %edi,%edx
    3e4e:	74 2a                	je     3e7a <timer_thread+0x2ba>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3e50:	48 8b 08             	mov    (%rax),%rcx
    3e53:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3e57:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3e5b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3e5f:	48 85 c9             	test   %rcx,%rcx
    3e62:	7e dc                	jle    3e40 <timer_thread+0x280>
    3e64:	bf 01 00 00 00       	mov    $0x1,%edi
    3e69:	48 89 ee             	mov    %rbp,%rsi
    3e6c:	31 c0                	xor    %eax,%eax
    3e6e:	e8 dd e5 ff ff       	call   2450 <__printf_chk@plt>
            break;
    3e73:	41 8b 7f 20          	mov    0x20(%r15),%edi
            all_empty = 0;
    3e77:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3e7a:	49 83 c6 01          	add    $0x1,%r14
    3e7e:	44 39 f7             	cmp    %r14d,%edi
    3e81:	7e 0d                	jle    3e90 <timer_thread+0x2d0>
    3e83:	49 8b 47 10          	mov    0x10(%r15),%rax
    3e87:	eb 97                	jmp    3e20 <timer_thread+0x260>
    3e89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3e90:	49 83 c4 01          	add    $0x1,%r12
    3e94:	44 39 e7             	cmp    %r12d,%edi
    3e97:	7e 0d                	jle    3ea6 <timer_thread+0x2e6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3e99:	85 ff                	test   %edi,%edi
    3e9b:	7e 09                	jle    3ea6 <timer_thread+0x2e6>
    3e9d:	49 8b 47 10          	mov    0x10(%r15),%rax
    3ea1:	e9 6a ff ff ff       	jmp    3e10 <timer_thread+0x250>
    if (all_empty == 1) {
    3ea6:	41 83 f9 01          	cmp    $0x1,%r9d
    3eaa:	74 14                	je     3ec0 <timer_thread+0x300>
      nanosleep(&drain , &drainrem);
    3eac:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3eb1:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3eb6:	e8 95 e4 ff ff       	call   2350 <nanosleep@plt>
    3ebb:	e9 c4 fe ff ff       	jmp    3d84 <timer_thread+0x1c4>
    3ec0:	48 8d 3d 8d 31 00 00 	lea    0x318d(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3ec7:	e8 24 e4 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3ecc:	41 8b 47 34          	mov    0x34(%r15),%eax
    3ed0:	85 c0                	test   %eax,%eax
    3ed2:	0f 84 e3 00 00 00    	je     3fbb <timer_thread+0x3fb>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ed8:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3edc:	85 c9                	test   %ecx,%ecx
    3ede:	7e 2d                	jle    3f0d <timer_thread+0x34d>
    3ee0:	49 8b 47 10          	mov    0x10(%r15),%rax
    3ee4:	31 db                	xor    %ebx,%ebx
    3ee6:	48 8d 2d 81 31 00 00 	lea    0x3181(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3eed:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->running = 0;
    3ef0:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3ef4:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3ef8:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3eff:	0f 84 e3 00 00 00    	je     3fe8 <timer_thread+0x428>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3f05:	48 83 c3 01          	add    $0x1,%rbx
    3f09:	39 d9                	cmp    %ebx,%ecx
    3f0b:	7f e3                	jg     3ef0 <timer_thread+0x330>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f0d:	49 63 47 18          	movslq 0x18(%r15),%rax
    3f11:	85 c0                	test   %eax,%eax
    3f13:	0f 8e 8b 00 00 00    	jle    3fa4 <timer_thread+0x3e4>
      for (int y = 0 ; y < data->task_count ; y++) {
    3f19:	41 8b 57 30          	mov    0x30(%r15),%edx
    3f1d:	85 d2                	test   %edx,%edx
    3f1f:	0f 8e 7f 00 00 00    	jle    3fa4 <timer_thread+0x3e4>
    3f25:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
    3f2d:	48 63 c2             	movslq %edx,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3f30:	4d 8b 57 10          	mov    0x10(%r15),%r10
    3f34:	31 c9                	xor    %ecx,%ecx
    3f36:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    3f3a:	48 c1 e0 07          	shl    $0x7,%rax
    3f3e:	4c 8d 88 c0 00 00 00 	lea    0xc0(%rax),%r9
    3f45:	0f 1f 00             	nopl   (%rax)
    3f48:	49 8b 04 0a          	mov    (%r10,%rcx,1),%rax
    3f4c:	48 8b 70 28          	mov    0x28(%rax),%rsi
    3f50:	4a 8d 14 0e          	lea    (%rsi,%r9,1),%rdx
    3f54:	48 8d 86 c0 00 00 00 	lea    0xc0(%rsi),%rax
    3f5b:	48 89 d7             	mov    %rdx,%rdi
    3f5e:	48 29 c7             	sub    %rax,%rdi
    3f61:	81 e7 80 00 00 00    	and    $0x80,%edi
    3f67:	74 17                	je     3f80 <timer_thread+0x3c0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3f69:	48 8d 86 40 02 00 00 	lea    0x240(%rsi),%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3f70:	c7 86 c0 00 00 00 00 00 00 00 	movl   $0x0,0xc0(%rsi)
      for (int y = 0 ; y < data->task_count ; y++) {
    3f7a:	48 39 d0             	cmp    %rdx,%rax
    3f7d:	74 1c                	je     3f9b <timer_thread+0x3db>
    3f7f:	90                   	nop
        data->threads[x]->tasks[y].scheduled = 0;
    3f80:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3f86:	48 05 00 03 00 00    	add    $0x300,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3f8c:	c7 80 80 fe ff ff 00 00 00 00 	movl   $0x0,-0x180(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3f96:	48 39 d0             	cmp    %rdx,%rax
    3f99:	75 e5                	jne    3f80 <timer_thread+0x3c0>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f9b:	48 83 c1 08          	add    $0x8,%rcx
    3f9f:	4c 39 c1             	cmp    %r8,%rcx
    3fa2:	75 a4                	jne    3f48 <timer_thread+0x388>
    asm volatile ("mfence" ::: "memory");
    3fa4:	0f ae f0             	mfence
    3fa7:	48 8d 3d d2 30 00 00 	lea    0x30d2(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3fae:	e8 3d e3 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3fb3:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
    3fbb:	48 8d 3d c5 30 00 00 	lea    0x30c5(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3fc2:	e8 29 e3 ff ff       	call   22f0 <puts@plt>
}
    3fc7:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3fcc:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3fd5:	75 47                	jne    401e <timer_thread+0x45e>
    3fd7:	48 83 c4 58          	add    $0x58,%rsp
    3fdb:	31 c0                	xor    %eax,%eax
    3fdd:	5b                   	pop    %rbx
    3fde:	5d                   	pop    %rbp
    3fdf:	41 5c                	pop    %r12
    3fe1:	41 5d                	pop    %r13
    3fe3:	41 5e                	pop    %r14
    3fe5:	41 5f                	pop    %r15
    3fe7:	c3                   	ret
    3fe8:	48 89 ef             	mov    %rbp,%rdi
    3feb:	e8 00 e3 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3ff0:	49 8b 47 10          	mov    0x10(%r15),%rax
    3ff4:	be 01 00 00 00       	mov    $0x1,%esi
    3ff9:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ffd:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4001:	8b 78 50             	mov    0x50(%rax),%edi
    4004:	e8 f7 e3 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4009:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    400d:	39 d9                	cmp    %ebx,%ecx
    400f:	0f 8e f8 fe ff ff    	jle    3f0d <timer_thread+0x34d>
    4015:	49 8b 47 10          	mov    0x10(%r15),%rax
    4019:	e9 d2 fe ff ff       	jmp    3ef0 <timer_thread+0x330>
}
    401e:	e8 0d e3 ff ff       	call   2330 <__stack_chk_fail@plt>
    4023:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    402e:	66 90                	xchg   %ax,%ax

0000000000004030 <strtolower>:
void strtolower(char *str) {
    4030:	f3 0f 1e fa          	endbr64
    4034:	55                   	push   %rbp
    4035:	53                   	push   %rbx
    4036:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    403a:	48 0f be 1f          	movsbq (%rdi),%rbx
    403e:	84 db                	test   %bl,%bl
    4040:	74 24                	je     4066 <strtolower+0x36>
    4042:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4045:	e8 c6 e4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    404a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4050:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4053:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4057:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    405a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    405d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4062:	84 db                	test   %bl,%bl
    4064:	75 ea                	jne    4050 <strtolower+0x20>
}
    4066:	48 83 c4 08          	add    $0x8,%rsp
    406a:	5b                   	pop    %rbx
    406b:	5d                   	pop    %rbp
    406c:	c3                   	ret
    406d:	0f 1f 00             	nopl   (%rax)

0000000000004070 <zh_malloc>:
void *zh_malloc(size_t size) {
    4070:	f3 0f 1e fa          	endbr64
    4074:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4078:	e8 93 e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    407d:	48 85 c0             	test   %rax,%rax
    4080:	74 05                	je     4087 <zh_malloc+0x17>
}
    4082:	48 83 c4 08          	add    $0x8,%rsp
    4086:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4087:	48 8b 0d 92 5f 00 00 	mov    0x5f92(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    408e:	ba 28 00 00 00       	mov    $0x28,%edx
    4093:	be 01 00 00 00       	mov    $0x1,%esi
    4098:	48 8d 3d 69 33 00 00 	lea    0x3369(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    409f:	e8 1c e4 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    40a4:	bf 01 00 00 00       	mov    $0x1,%edi
    40a9:	e8 f2 e3 ff ff       	call   24a0 <exit@plt>
    40ae:	66 90                	xchg   %ax,%ax

00000000000040b0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    40b0:	f3 0f 1e fa          	endbr64
    40b4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    40b5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    40ba:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    40bd:	e8 9e e2 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    40c2:	48 85 c0             	test   %rax,%rax
    40c5:	74 11                	je     40d8 <get_filename_ext+0x28>
    40c7:	48 39 c3             	cmp    %rax,%rbx
    40ca:	74 0c                	je     40d8 <get_filename_ext+0x28>
    return dot + 1;
    40cc:	48 83 c0 01          	add    $0x1,%rax
}
    40d0:	5b                   	pop    %rbx
    40d1:	c3                   	ret
    40d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    40d8:	48 8d 05 f0 2f 00 00 	lea    0x2ff0(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    40df:	5b                   	pop    %rbx
    40e0:	c3                   	ret
    40e1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    40ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000040f0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    40f0:	f3 0f 1e fa          	endbr64
    40f4:	41 55                	push   %r13
    40f6:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40f9:	48 89 fe             	mov    %rdi,%rsi
    40fc:	41 54                	push   %r12
    40fe:	55                   	push   %rbp
    40ff:	48 89 d5             	mov    %rdx,%rbp
    4102:	ba 00 04 00 00       	mov    $0x400,%edx
    4107:	53                   	push   %rbx
    4108:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    410f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4118:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4120:	31 c0                	xor    %eax,%eax
    4122:	49 89 e4             	mov    %rsp,%r12
    4125:	4c 89 e7             	mov    %r12,%rdi
    4128:	e8 03 e3 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    412d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4132:	84 db                	test   %bl,%bl
    4134:	74 24                	je     415a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4136:	e8 d5 e3 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    413b:	48 8b 08             	mov    (%rax),%rcx
    413e:	4c 89 e0             	mov    %r12,%rax
    4141:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4148:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    414b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    414f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4152:	48 0f be 18          	movsbq (%rax),%rbx
    4156:	84 db                	test   %bl,%bl
    4158:	75 ee                	jne    4148 <send_headers+0x58>
    void *buf = malloc(size);
    415a:	bf 11 00 00 00       	mov    $0x11,%edi
    415f:	e8 ac e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4164:	48 85 c0             	test   %rax,%rax
    4167:	0f 84 7e 04 00 00    	je     45eb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    416d:	66 0f 6f 05 eb 37 00 00 	movdqa 0x37eb(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    4175:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4179:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    417e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4186:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    418a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    418d:	e8 7e e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4192:	48 85 c0             	test   %rax,%rax
    4195:	0f 84 50 04 00 00    	je     45eb <send_headers+0x4fb>
    419b:	66 0f 6f 05 cd 37 00 00 	movdqa 0x37cd(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    41a3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    41a7:	4c 89 e7             	mov    %r12,%rdi
    41aa:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    41b4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    41bc:	0f 11 00             	movups %xmm0,(%rax)
    41bf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    41c3:	be 2e 00 00 00       	mov    $0x2e,%esi
    41c8:	e8 93 e1 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    41cd:	48 85 c0             	test   %rax,%rax
    41d0:	0f 84 ea 02 00 00    	je     44c0 <send_headers+0x3d0>
    41d6:	4c 39 e0             	cmp    %r12,%rax
    41d9:	0f 84 e1 02 00 00    	je     44c0 <send_headers+0x3d0>
    return dot + 1;
    41df:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    41e3:	48 8d 3d b3 2e 00 00 	lea    0x2eb3(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    41ea:	48 89 de             	mov    %rbx,%rsi
    41ed:	e8 be e1 ff ff       	call   23b0 <strcmp@plt>
    41f2:	85 c0                	test   %eax,%eax
    41f4:	75 20                	jne    4216 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    41f6:	66 0f 6f 05 82 37 00 00 	movdqa 0x3782(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    41fe:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4206:	66 0f 6f 05 82 37 00 00 	movdqa 0x3782(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    420e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4216:	48 89 de             	mov    %rbx,%rsi
    4219:	48 8d 3d 81 2e 00 00 	lea    0x2e81(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    4220:	e8 8b e1 ff ff       	call   23b0 <strcmp@plt>
    4225:	85 c0                	test   %eax,%eax
    4227:	75 20                	jne    4249 <send_headers+0x159>
    4229:	66 0f 6f 05 4f 37 00 00 	movdqa 0x374f(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4231:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4239:	66 0f 6f 05 4f 37 00 00 	movdqa 0x374f(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    4241:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4249:	48 89 de             	mov    %rbx,%rsi
    424c:	48 8d 3d 53 2e 00 00 	lea    0x2e53(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    4253:	e8 58 e1 ff ff       	call   23b0 <strcmp@plt>
    4258:	85 c0                	test   %eax,%eax
    425a:	0f 84 10 02 00 00    	je     4470 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4260:	48 89 de             	mov    %rbx,%rsi
    4263:	48 8d 3d 40 2e 00 00 	lea    0x2e40(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    426a:	e8 41 e1 ff ff       	call   23b0 <strcmp@plt>
    426f:	85 c0                	test   %eax,%eax
    4271:	0f 84 a9 02 00 00    	je     4520 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4277:	48 89 de             	mov    %rbx,%rsi
    427a:	48 8d 3d 2d 2e 00 00 	lea    0x2e2d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4281:	e8 2a e1 ff ff       	call   23b0 <strcmp@plt>
    4286:	85 c0                	test   %eax,%eax
    4288:	0f 84 6a 02 00 00    	je     44f8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    428e:	48 89 de             	mov    %rbx,%rsi
    4291:	48 8d 3d 59 2e 00 00 	lea    0x2e59(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4298:	e8 13 e1 ff ff       	call   23b0 <strcmp@plt>
    429d:	85 c0                	test   %eax,%eax
    429f:	0f 84 2b 02 00 00    	je     44d0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    42a5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    42a8:	0f 84 52 01 00 00    	je     4400 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    42ae:	48 89 de             	mov    %rbx,%rsi
    42b1:	48 8d 3d fa 2d 00 00 	lea    0x2dfa(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    42b8:	e8 f3 e0 ff ff       	call   23b0 <strcmp@plt>
    42bd:	85 c0                	test   %eax,%eax
    42bf:	0f 84 ab 02 00 00    	je     4570 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    42c5:	48 89 de             	mov    %rbx,%rsi
    42c8:	48 8d 3d e7 2d 00 00 	lea    0x2de7(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    42cf:	e8 dc e0 ff ff       	call   23b0 <strcmp@plt>
    42d4:	85 c0                	test   %eax,%eax
    42d6:	0f 84 6c 02 00 00    	je     4548 <send_headers+0x458>
    slen = strlen(send_buffer);
    42dc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    42e4:	4c 89 e7             	mov    %r12,%rdi
    42e7:	e8 34 e0 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    42ec:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    42ef:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    42f2:	e8 19 e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    42f7:	48 85 c0             	test   %rax,%rax
    42fa:	0f 84 eb 02 00 00    	je     45eb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4300:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4304:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4308:	83 fb 08             	cmp    $0x8,%ebx
    430b:	0f 83 3f 01 00 00    	jae    4450 <send_headers+0x360>
    4311:	f6 c3 04             	test   $0x4,%bl
    4314:	0f 85 7b 02 00 00    	jne    4595 <send_headers+0x4a5>
    431a:	85 db                	test   %ebx,%ebx
    431c:	74 13                	je     4331 <send_headers+0x241>
    431e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4326:	88 10                	mov    %dl,(%rax)
    4328:	f6 c3 02             	test   $0x2,%bl
    432b:	0f 85 96 02 00 00    	jne    45c7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4331:	4d 89 e8             	mov    %r13,%r8
    4334:	48 8d 0d 7f 2d 00 00 	lea    0x2d7f(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    433b:	4c 89 e7             	mov    %r12,%rdi
    433e:	31 c0                	xor    %eax,%eax
    4340:	ba 00 04 00 00       	mov    $0x400,%edx
    4345:	be 01 00 00 00       	mov    $0x1,%esi
    434a:	e8 d1 e1 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    434f:	4c 89 e7             	mov    %r12,%rdi
    4352:	e8 c9 df ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4357:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    435a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    435d:	e8 ae e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4362:	48 85 c0             	test   %rax,%rax
    4365:	0f 84 80 02 00 00    	je     45eb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    436b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    436f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4373:	83 fb 08             	cmp    $0x8,%ebx
    4376:	0f 83 1c 01 00 00    	jae    4498 <send_headers+0x3a8>
    437c:	f6 c3 04             	test   $0x4,%bl
    437f:	0f 85 29 02 00 00    	jne    45ae <send_headers+0x4be>
    4385:	85 db                	test   %ebx,%ebx
    4387:	74 13                	je     439c <send_headers+0x2ac>
    4389:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4391:	88 10                	mov    %dl,(%rax)
    4393:	f6 c3 02             	test   $0x2,%bl
    4396:	0f 85 3d 02 00 00    	jne    45d9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    439c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    43a1:	bf 02 00 00 00       	mov    $0x2,%edi
    43a6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    43ae:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    43b6:	e8 55 e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    43bb:	48 85 c0             	test   %rax,%rax
    43be:	0f 84 27 02 00 00    	je     45eb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    43c4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    43cc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    43d0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    43d8:	66 89 10             	mov    %dx,(%rax)
}
    43db:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    43e3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    43ec:	0f 85 20 02 00 00    	jne    4612 <send_headers+0x522>
    43f2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    43f9:	5b                   	pop    %rbx
    43fa:	5d                   	pop    %rbp
    43fb:	41 5c                	pop    %r12
    43fd:	41 5d                	pop    %r13
    43ff:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4400:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4404:	0f 85 a4 fe ff ff    	jne    42ae <send_headers+0x1be>
    440a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    440e:	0f 85 9a fe ff ff    	jne    42ae <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4414:	66 0f 6f 05 c4 35 00 00 	movdqa 0x35c4(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    441c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4426:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    442e:	66 0f 6f 05 ba 35 00 00 	movdqa 0x35ba(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    4436:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    443e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4446:	e9 63 fe ff ff       	jmp    42ae <send_headers+0x1be>
    444b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4450:	89 da                	mov    %ebx,%edx
    4452:	48 89 c7             	mov    %rax,%rdi
    4455:	4c 89 e6             	mov    %r12,%rsi
    4458:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    445d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4462:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4465:	c1 e9 03             	shr    $0x3,%ecx
    4468:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    446b:	e9 c1 fe ff ff       	jmp    4331 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4470:	66 0f 6f 05 08 35 00 00 	movdqa 0x3508(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4478:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4480:	66 0f 6f 05 18 35 00 00 	movdqa 0x3518(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4488:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4490:	e9 cb fd ff ff       	jmp    4260 <send_headers+0x170>
    4495:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4498:	89 da                	mov    %ebx,%edx
    449a:	48 89 c7             	mov    %rax,%rdi
    449d:	4c 89 e6             	mov    %r12,%rsi
    44a0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    44a5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    44aa:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    44ad:	c1 e9 03             	shr    $0x3,%ecx
    44b0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    44b3:	e9 e4 fe ff ff       	jmp    439c <send_headers+0x2ac>
    44b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    44c0:	48 8d 1d 08 2c 00 00 	lea    0x2c08(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    44c7:	e9 94 fd ff ff       	jmp    4260 <send_headers+0x170>
    44cc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    44d0:	66 0f 6f 05 e8 34 00 00 	movdqa 0x34e8(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    44d8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44e0:	66 0f 6f 05 e8 34 00 00 	movdqa 0x34e8(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    44e8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44f0:	e9 b0 fd ff ff       	jmp    42a5 <send_headers+0x1b5>
    44f5:	0f 1f 00             	nopl   (%rax)
    44f8:	66 0f 6f 05 c0 34 00 00 	movdqa 0x34c0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4500:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4508:	66 0f 6f 05 c0 34 00 00 	movdqa 0x34c0(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4510:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4518:	e9 71 fd ff ff       	jmp    428e <send_headers+0x19e>
    451d:	0f 1f 00             	nopl   (%rax)
    4520:	66 0f 6f 05 58 34 00 00 	movdqa 0x3458(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4528:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4530:	66 0f 6f 05 78 34 00 00 	movdqa 0x3478(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    4538:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4540:	e9 32 fd ff ff       	jmp    4277 <send_headers+0x187>
    4545:	0f 1f 00             	nopl   (%rax)
    4548:	66 0f 6f 05 70 34 00 00 	movdqa 0x3470(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4550:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4558:	66 0f 6f 05 b0 34 00 00 	movdqa 0x34b0(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4560:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4568:	e9 6f fd ff ff       	jmp    42dc <send_headers+0x1ec>
    456d:	0f 1f 00             	nopl   (%rax)
    4570:	66 0f 6f 05 48 34 00 00 	movdqa 0x3448(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4578:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4580:	66 0f 6f 05 78 34 00 00 	movdqa 0x3478(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4588:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4590:	e9 30 fd ff ff       	jmp    42c5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4595:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    459c:	89 db                	mov    %ebx,%ebx
    459e:	89 10                	mov    %edx,(%rax)
    45a0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    45a5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    45a9:	e9 83 fd ff ff       	jmp    4331 <send_headers+0x241>
    45ae:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    45b5:	89 db                	mov    %ebx,%ebx
    45b7:	89 10                	mov    %edx,(%rax)
    45b9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    45be:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    45c2:	e9 d5 fd ff ff       	jmp    439c <send_headers+0x2ac>
    45c7:	89 db                	mov    %ebx,%ebx
    45c9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    45cf:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    45d4:	e9 58 fd ff ff       	jmp    4331 <send_headers+0x241>
    45d9:	89 db                	mov    %ebx,%ebx
    45db:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    45e1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    45e6:	e9 b1 fd ff ff       	jmp    439c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    45eb:	48 8b 0d 2e 5a 00 00 	mov    0x5a2e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    45f2:	ba 28 00 00 00       	mov    $0x28,%edx
    45f7:	be 01 00 00 00       	mov    $0x1,%esi
    45fc:	48 8d 3d 05 2e 00 00 	lea    0x2e05(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4603:	e8 b8 de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4608:	bf 01 00 00 00       	mov    $0x1,%edi
    460d:	e8 8e de ff ff       	call   24a0 <exit@plt>
}
    4612:	e8 19 dd ff ff       	call   2330 <__stack_chk_fail@plt>
    4617:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004620 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4620:	f3 0f 1e fa          	endbr64
    4624:	41 55                	push   %r13
    4626:	49 89 d5             	mov    %rdx,%r13
    4629:	41 54                	push   %r12
    462b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    462e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4631:	55                   	push   %rbp
    4632:	53                   	push   %rbx
    4633:	48 89 f3             	mov    %rsi,%rbx
    4636:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    463a:	e8 d1 dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    463f:	48 85 c0             	test   %rax,%rax
    4642:	74 6b                	je     46af <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4644:	4c 89 e7             	mov    %r12,%rdi
    4647:	48 89 c5             	mov    %rax,%rbp
    464a:	31 f6                	xor    %esi,%esi
    464c:	31 c0                	xor    %eax,%eax
    464e:	e8 2d de ff ff       	call   2480 <open@plt>
    4653:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4656:	85 c0                	test   %eax,%eax
    4658:	0f 88 f8 de ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    465e:	48 89 da             	mov    %rbx,%rdx
    4661:	48 89 ee             	mov    %rbp,%rsi
    4664:	89 c7                	mov    %eax,%edi
    4666:	e8 25 dd ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    466b:	48 98                	cltq
    466d:	48 39 d8             	cmp    %rbx,%rax
    4670:	7c 1e                	jl     4690 <copy_file_contents+0x70>
    close(fd);
    4672:	44 89 e7             	mov    %r12d,%edi
    4675:	e8 f6 dc ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    467a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    467e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4682:	48 83 c4 08          	add    $0x8,%rsp
    4686:	5b                   	pop    %rbx
    4687:	5d                   	pop    %rbp
    4688:	41 5c                	pop    %r12
    468a:	41 5d                	pop    %r13
    468c:	c3                   	ret
    468d:	0f 1f 00             	nopl   (%rax)
    4690:	48 8b 0d 89 59 00 00 	mov    0x5989(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4697:	ba 1a 00 00 00       	mov    $0x1a,%edx
    469c:	be 01 00 00 00       	mov    $0x1,%esi
    46a1:	48 8d 3d 28 2a 00 00 	lea    0x2a28(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    46a8:	e8 13 de ff ff       	call   24c0 <fwrite@plt>
    46ad:	eb c3                	jmp    4672 <copy_file_contents+0x52>
    46af:	48 8b 0d 6a 59 00 00 	mov    0x596a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    46b6:	ba 28 00 00 00       	mov    $0x28,%edx
    46bb:	be 01 00 00 00       	mov    $0x1,%esi
    46c0:	48 8d 3d 41 2d 00 00 	lea    0x2d41(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    46c7:	e8 f4 dd ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    46cc:	bf 01 00 00 00       	mov    $0x1,%edi
    46d1:	e8 ca dd ff ff       	call   24a0 <exit@plt>
    46d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000046e0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    46e0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    46e4:	8b 46 44             	mov    0x44(%rsi),%eax
    46e7:	48 89 fa             	mov    %rdi,%rdx
    46ea:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    46ed:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    46f3:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    46f6:	48 8b 07             	mov    (%rdi),%rax
    46f9:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    46fc:	f6 c1 02             	test   $0x2,%cl
    46ff:	74 00                	je     4701 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4701:	89 f0                	mov    %esi,%eax
    4703:	44 29 c0             	sub    %r8d,%eax
    4706:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4709:	0f 82 53 de ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    470f:	c1 e9 0a             	shr    $0xa,%ecx
    4712:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4716:	8b 47 44             	mov    0x44(%rdi),%eax
    4719:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    471c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    471f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4722:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4725:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4729:	d3 e0                	shl    %cl,%eax
    472b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    472e:	48 c1 e0 06          	shl    $0x6,%rax
    4732:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4736:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    473c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    473f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4743:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4749:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4751:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4755:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4758:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    475f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4767:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    476b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    476f:	e8 cc db ff ff       	call   2340 <io_uring_submit@plt>
}
    4774:	31 c0                	xor    %eax,%eax
    4776:	48 83 c4 08          	add    $0x8,%rsp
    477a:	c3                   	ret
    477b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004780 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4780:	f3 0f 1e fa          	endbr64
    4784:	41 55                	push   %r13
    4786:	41 89 fd             	mov    %edi,%r13d
    4789:	41 54                	push   %r12
    478b:	55                   	push   %rbp
    478c:	53                   	push   %rbx
    478d:	48 89 f3             	mov    %rsi,%rbx
    4790:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4794:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4797:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    479d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    47a0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    47a3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    47a5:	f6 c1 02             	test   $0x2,%cl
    47a8:	74 00                	je     47aa <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    47aa:	89 c2                	mov    %eax,%edx
    47ac:	29 f2                	sub    %esi,%edx
    47ae:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    47b1:	0f 82 bb dd ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    47b7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    47ba:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    47bd:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    47c0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    47c5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    47c8:	23 6b 58             	and    0x58(%rbx),%ebp
    47cb:	d3 e5                	shl    %cl,%ebp
    47cd:	48 c1 e5 06          	shl    $0x6,%rbp
    47d1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    47d5:	e8 36 dc ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    47da:	be 01 00 00 00       	mov    $0x1,%esi
    47df:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    47e4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    47e7:	e8 b4 db ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    47ec:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    47f1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    47f5:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    47f8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    47fd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4802:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    480b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4813:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4817:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    481b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4822:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    482a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    482e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4836:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    483e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4842:	e8 f9 da ff ff       	call   2340 <io_uring_submit@plt>
}
    4847:	48 83 c4 08          	add    $0x8,%rsp
    484b:	31 c0                	xor    %eax,%eax
    484d:	5b                   	pop    %rbx
    484e:	5d                   	pop    %rbp
    484f:	41 5c                	pop    %r12
    4851:	41 5d                	pop    %r13
    4853:	c3                   	ret
    4854:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    485f:	90                   	nop

0000000000004860 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4860:	f3 0f 1e fa          	endbr64
    4864:	41 56                	push   %r14
    4866:	41 89 f6             	mov    %esi,%r14d
    4869:	41 55                	push   %r13
    486b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    486e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4873:	41 54                	push   %r12
    4875:	55                   	push   %rbp
    4876:	48 89 d5             	mov    %rdx,%rbp
    4879:	53                   	push   %rbx
    void *buf = malloc(size);
    487a:	e8 91 db ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    487f:	48 85 c0             	test   %rax,%rax
    4882:	0f 84 dd 00 00 00    	je     4965 <_send_static_string_content+0x105>
    4888:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    488b:	4c 89 ef             	mov    %r13,%rdi
    488e:	e8 8d da ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4893:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    489a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    489e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    48a1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    48a4:	e8 67 db ff ff       	call   2410 <malloc@plt>
    48a9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    48ac:	48 85 c0             	test   %rax,%rax
    48af:	0f 84 b0 00 00 00    	je     4965 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    48b5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    48b9:	4c 89 e2             	mov    %r12,%rdx
    48bc:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    48bf:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    48c3:	e8 18 db ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    48c8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    48cb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    48d1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    48d4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    48d8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    48da:	f6 c1 02             	test   $0x2,%cl
    48dd:	0f 85 7d 00 00 00    	jne    4960 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    48e3:	89 d0                	mov    %edx,%eax
    48e5:	29 f0                	sub    %esi,%eax
    48e7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    48ea:	0f 82 8c dc ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    48f0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    48f3:	8b 45 44             	mov    0x44(%rbp),%eax
    48f6:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    48f9:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    48fc:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    48ff:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4902:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4908:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    490c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    490e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4911:	48 89 ef             	mov    %rbp,%rdi
    4914:	48 c1 e0 06          	shl    $0x6,%rax
    4918:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    491c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    491f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4923:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4929:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4931:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4935:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4938:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    493f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4947:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    494b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    494f:	5b                   	pop    %rbx
    4950:	5d                   	pop    %rbp
    4951:	41 5c                	pop    %r12
    4953:	41 5d                	pop    %r13
    4955:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4957:	e9 e4 d9 ff ff       	jmp    2340 <io_uring_submit@plt>
    495c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4960:	e9 7e ff ff ff       	jmp    48e3 <_send_static_string_content+0x83>
    4965:	48 8b 0d b4 56 00 00 	mov    0x56b4(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    496c:	ba 28 00 00 00       	mov    $0x28,%edx
    4971:	be 01 00 00 00       	mov    $0x1,%esi
    4976:	48 8d 3d 8b 2a 00 00 	lea    0x2a8b(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    497d:	e8 3e db ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4982:	bf 01 00 00 00       	mov    $0x1,%edi
    4987:	e8 14 db ff ff       	call   24a0 <exit@plt>
    498c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004990 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4990:	f3 0f 1e fa          	endbr64
    4994:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4997:	89 fe                	mov    %edi,%esi
    4999:	48 8b 3d 78 56 00 00 	mov    0x5678(%rip),%rdi        # a018 <unimplemented_content>
    49a0:	e9 bb fe ff ff       	jmp    4860 <_send_static_string_content>
    49a5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000049b0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    49b0:	f3 0f 1e fa          	endbr64
    49b4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    49b7:	89 fe                	mov    %edi,%esi
    49b9:	48 8b 3d 50 56 00 00 	mov    0x5650(%rip),%rdi        # a010 <http_404_content>
    49c0:	e9 9b fe ff ff       	jmp    4860 <_send_static_string_content>
    49c5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000049d0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    49d0:	f3 0f 1e fa          	endbr64
    49d4:	41 56                	push   %r14
    49d6:	41 55                	push   %r13
    49d8:	49 89 d5             	mov    %rdx,%r13
    49db:	41 54                	push   %r12
    49dd:	41 89 f4             	mov    %esi,%r12d
    49e0:	55                   	push   %rbp
    49e1:	48 89 fd             	mov    %rdi,%rbp
    49e4:	53                   	push   %rbx
    49e5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    49ec:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    49f5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    49fd:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    49ff:	e8 1c d9 ff ff       	call   2320 <strlen@plt>
    4a04:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4a09:	48 89 c3             	mov    %rax,%rbx
    4a0c:	0f 84 b6 00 00 00    	je     4ac8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a12:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a17:	48 89 ee             	mov    %rbp,%rsi
    4a1a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4a1e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4a23:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4a2b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a33:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4a3e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a46:	e8 75 d9 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4a4b:	48 89 e6             	mov    %rsp,%rsi
    4a4e:	4c 89 f7             	mov    %r14,%rdi
    4a51:	e8 7a d9 ff ff       	call   23d0 <stat@plt>
    4a56:	83 f8 ff             	cmp    $0xffffffff,%eax
    4a59:	0f 84 d3 00 00 00    	je     4b32 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    4a5f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4a63:	25 00 f0 00 00       	and    $0xf000,%eax
    4a68:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4a6d:	0f 84 f5 00 00 00    	je     4b68 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4a73:	48 8b 3d 96 55 00 00 	mov    0x5596(%rip),%rdi        # a010 <http_404_content>
    4a7a:	4c 89 ea             	mov    %r13,%rdx
    4a7d:	44 89 e6             	mov    %r12d,%esi
    4a80:	e8 db fd ff ff       	call   4860 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4a85:	4c 89 f2             	mov    %r14,%rdx
    4a88:	bf 01 00 00 00       	mov    $0x1,%edi
    4a8d:	31 c0                	xor    %eax,%eax
    4a8f:	48 8d 35 8a 26 00 00 	lea    0x268a(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    4a96:	e8 b5 d9 ff ff       	call   2450 <__printf_chk@plt>
}
    4a9b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4aa3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4aac:	0f 85 20 01 00 00    	jne    4bd2 <handle_get_method+0x202>
    4ab2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4ab9:	5b                   	pop    %rbx
    4aba:	5d                   	pop    %rbp
    4abb:	41 5c                	pop    %r12
    4abd:	41 5d                	pop    %r13
    4abf:	41 5e                	pop    %r14
    4ac1:	c3                   	ret
    4ac2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ac8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4acd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4ad5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4ada:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4add:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4ae5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ae8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4af0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4afb:	e8 c0 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    4b00:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4b05:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4b0a:	48 8d 35 da 25 00 00 	lea    0x25da(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4b11:	48 29 d9             	sub    %rbx,%rcx
    4b14:	ba 0b 00 00 00       	mov    $0xb,%edx
    4b19:	e8 a2 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4b1e:	48 89 e6             	mov    %rsp,%rsi
    4b21:	4c 89 f7             	mov    %r14,%rdi
    4b24:	e8 a7 d8 ff ff       	call   23d0 <stat@plt>
    4b29:	83 f8 ff             	cmp    $0xffffffff,%eax
    4b2c:	0f 85 2d ff ff ff    	jne    4a5f <handle_get_method+0x8f>
    4b32:	4c 89 f2             	mov    %r14,%rdx
    4b35:	48 89 e9             	mov    %rbp,%rcx
    4b38:	48 8d 35 b7 25 00 00 	lea    0x25b7(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    4b3f:	31 c0                	xor    %eax,%eax
    4b41:	bf 01 00 00 00       	mov    $0x1,%edi
    4b46:	e8 05 d9 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    4b4b:	48 8b 3d be 54 00 00 	mov    0x54be(%rip),%rdi        # a010 <http_404_content>
    4b52:	4c 89 ea             	mov    %r13,%rdx
    4b55:	44 89 e6             	mov    %r12d,%esi
    4b58:	e8 03 fd ff ff       	call   4860 <_send_static_string_content>
}
    4b5d:	e9 39 ff ff ff       	jmp    4a9b <handle_get_method+0xcb>
    4b62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4b68:	bf 70 00 00 00       	mov    $0x70,%edi
    4b6d:	e8 9e d8 ff ff       	call   2410 <malloc@plt>
    4b72:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4b75:	48 85 c0             	test   %rax,%rax
    4b78:	74 5d                	je     4bd7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    4b7a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4b7e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4b83:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4b87:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    4b8a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4b91:	e8 5a f5 ff ff       	call   40f0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4b96:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4b9b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4b9f:	4c 89 f7             	mov    %r14,%rdi
    4ba2:	e8 79 fa ff ff       	call   4620 <copy_file_contents>
    4ba7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4bac:	4c 89 f2             	mov    %r14,%rdx
    4baf:	31 c0                	xor    %eax,%eax
    4bb1:	48 8d 35 56 25 00 00 	lea    0x2556(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4bb8:	bf 01 00 00 00       	mov    $0x1,%edi
    4bbd:	e8 8e d8 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    4bc2:	4c 89 ee             	mov    %r13,%rsi
    4bc5:	48 89 df             	mov    %rbx,%rdi
    4bc8:	e8 13 fb ff ff       	call   46e0 <add_write_request>
    4bcd:	e9 c9 fe ff ff       	jmp    4a9b <handle_get_method+0xcb>
}
    4bd2:	e8 59 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4bd7:	48 8b 0d 42 54 00 00 	mov    0x5442(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4bde:	ba 28 00 00 00       	mov    $0x28,%edx
    4be3:	be 01 00 00 00       	mov    $0x1,%esi
    4be8:	48 8d 3d 19 28 00 00 	lea    0x2819(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4bef:	e8 cc d8 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4bf4:	bf 01 00 00 00       	mov    $0x1,%edi
    4bf9:	e8 a2 d8 ff ff       	call   24a0 <exit@plt>
    4bfe:	66 90                	xchg   %ax,%ax

0000000000004c00 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4c00:	f3 0f 1e fa          	endbr64
    4c04:	41 57                	push   %r15
    4c06:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4c08:	4c 8d 35 76 24 00 00 	lea    0x2476(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4c0f:	41 55                	push   %r13
    4c11:	49 89 d5             	mov    %rdx,%r13
    4c14:	41 54                	push   %r12
    4c16:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4c19:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4c1c:	55                   	push   %rbp
    4c1d:	53                   	push   %rbx
    4c1e:	48 83 ec 18          	sub    $0x18,%rsp
    4c22:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4c2b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4c30:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4c32:	49 89 e7             	mov    %rsp,%r15
    4c35:	4c 89 fa             	mov    %r15,%rdx
    4c38:	e8 43 d7 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4c3d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4c41:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4c44:	84 db                	test   %bl,%bl
    4c46:	74 1d                	je     4c65 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4c48:	e8 c3 d8 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4c4d:	48 89 ea             	mov    %rbp,%rdx
    4c50:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4c53:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4c57:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4c5a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    4c5d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4c61:	84 db                	test   %bl,%bl
    4c63:	75 eb                	jne    4c50 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4c65:	4c 89 fa             	mov    %r15,%rdx
    4c68:	4c 89 f6             	mov    %r14,%rsi
    4c6b:	31 ff                	xor    %edi,%edi
    4c6d:	e8 0e d7 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4c72:	48 8d 35 ba 24 00 00 	lea    0x24ba(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4c79:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4c7c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    4c7f:	e8 2c d7 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4c84:	4c 89 ea             	mov    %r13,%rdx
    4c87:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4c8a:	85 c0                	test   %eax,%eax
    4c8c:	75 2a                	jne    4cb8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    4c8e:	48 89 df             	mov    %rbx,%rdi
    4c91:	e8 3a fd ff ff       	call   49d0 <handle_get_method>
}
    4c96:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4c9b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4ca4:	75 20                	jne    4cc6 <handle_http_method+0xc6>
    4ca6:	48 83 c4 18          	add    $0x18,%rsp
    4caa:	5b                   	pop    %rbx
    4cab:	5d                   	pop    %rbp
    4cac:	41 5c                	pop    %r12
    4cae:	41 5d                	pop    %r13
    4cb0:	41 5e                	pop    %r14
    4cb2:	41 5f                	pop    %r15
    4cb4:	c3                   	ret
    4cb5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4cb8:	48 8b 3d 59 53 00 00 	mov    0x5359(%rip),%rdi        # a018 <unimplemented_content>
    4cbf:	e8 9c fb ff ff       	call   4860 <_send_static_string_content>
}
    4cc4:	eb d0                	jmp    4c96 <handle_http_method+0x96>
    4cc6:	e8 65 d6 ff ff       	call   2330 <__stack_chk_fail@plt>
    4ccb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004cd0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4cd0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4cd4:	85 d2                	test   %edx,%edx
    4cd6:	7e 38                	jle    4d10 <get_line+0x40>
    4cd8:	48 63 d2             	movslq %edx,%rdx
    4cdb:	48 83 c7 01          	add    $0x1,%rdi
    4cdf:	48 01 f2             	add    %rsi,%rdx
    4ce2:	eb 11                	jmp    4cf5 <get_line+0x25>
    4ce4:	0f 1f 40 00          	nopl   0x0(%rax)
    4ce8:	48 83 c6 01          	add    $0x1,%rsi
    4cec:	48 83 c7 01          	add    $0x1,%rdi
    4cf0:	48 39 d6             	cmp    %rdx,%rsi
    4cf3:	74 1b                	je     4d10 <get_line+0x40>
        dest[i] = src[i];
    4cf5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4cf9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4cfb:	3c 0d                	cmp    $0xd,%al
    4cfd:	75 e9                	jne    4ce8 <get_line+0x18>
    4cff:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4d02:	75 e4                	jne    4ce8 <get_line+0x18>
            dest[i] = '\0';
    4d04:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4d07:	31 c0                	xor    %eax,%eax
    4d09:	c3                   	ret
    4d0a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4d10:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4d15:	c3                   	ret
    4d16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004d20 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4d20:	f3 0f 1e fa          	endbr64
    4d24:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4d2b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4d2f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4d38:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4d40:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4d42:	49 89 e2             	mov    %rsp,%r10
    4d45:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4d4d:	4c 89 d0             	mov    %r10,%rax
    4d50:	eb 13                	jmp    4d65 <handle_client_request+0x45>
    4d52:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4d58:	48 83 c0 01          	add    $0x1,%rax
    4d5c:	48 83 c1 01          	add    $0x1,%rcx
    4d60:	4c 39 c8             	cmp    %r9,%rax
    4d63:	74 4b                	je     4db0 <handle_client_request+0x90>
        dest[i] = src[i];
    4d65:	44 0f b6 01          	movzbl (%rcx),%r8d
    4d69:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4d6c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4d70:	75 e6                	jne    4d58 <handle_client_request+0x38>
    4d72:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4d76:	75 e0                	jne    4d58 <handle_client_request+0x38>
            dest[i] = '\0';
    4d78:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4d7b:	8b 47 08             	mov    0x8(%rdi),%eax
    4d7e:	48 89 f2             	mov    %rsi,%rdx
    4d81:	4c 89 d7             	mov    %r10,%rdi
    4d84:	89 c6                	mov    %eax,%esi
    4d86:	e8 75 fe ff ff       	call   4c00 <handle_http_method>
}
    4d8b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4d93:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d9c:	75 39                	jne    4dd7 <handle_client_request+0xb7>
    4d9e:	31 c0                	xor    %eax,%eax
    4da0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4da7:	c3                   	ret
    4da8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4db0:	48 8b 0d 69 52 00 00 	mov    0x5269(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4db7:	ba 12 00 00 00       	mov    $0x12,%edx
    4dbc:	be 01 00 00 00       	mov    $0x1,%esi
    4dc1:	48 8d 3d 6f 23 00 00 	lea    0x236f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4dc8:	e8 f3 d6 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4dcd:	bf 01 00 00 00       	mov    $0x1,%edi
    4dd2:	e8 c9 d6 ff ff       	call   24a0 <exit@plt>
}
    4dd7:	e8 54 d5 ff ff       	call   2330 <__stack_chk_fail@plt>
    4ddc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004de0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4de0:	f3 0f 1e fa          	endbr64
    4de4:	55                   	push   %rbp
    4de5:	53                   	push   %rbx
    4de6:	48 89 cb             	mov    %rcx,%rbx
    4de9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4ded:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4df0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4df3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4df9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4dfc:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4dff:	f6 c1 02             	test   $0x2,%cl
    4e02:	74 00                	je     4e04 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4e04:	41 89 c0             	mov    %eax,%r8d
    4e07:	45 29 c8             	sub    %r9d,%r8d
    4e0a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4e0e:	0f 82 78 d7 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4e14:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e17:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4e1a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4e1d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4e20:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4e23:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e27:	d3 e5                	shl    %cl,%ebp
    4e29:	48 c1 e5 06          	shl    $0x6,%rbp
    4e2d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4e31:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4e34:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4e39:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4e40:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4e44:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4e48:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4e50:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4e58:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4e5c:	e8 af d5 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4e61:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4e64:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4e6a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4e6e:	48 83 c4 08          	add    $0x8,%rsp
    4e72:	5b                   	pop    %rbx
    4e73:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4e74:	e9 c7 d4 ff ff       	jmp    2340 <io_uring_submit@plt>
    4e79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004e80 <io_thread>:
void* io_thread(void *arg) {
    4e80:	f3 0f 1e fa          	endbr64
    4e84:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e86:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4e88:	41 56                	push   %r14
    4e8a:	41 55                	push   %r13
    4e8c:	41 54                	push   %r12
    4e8e:	55                   	push   %rbp
    4e8f:	48 89 fd             	mov    %rdi,%rbp
    4e92:	53                   	push   %rbx
    4e93:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4e9a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4ea3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4eab:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4eaf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4eb4:	bf 00 01 00 00       	mov    $0x100,%edi
    4eb9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4ebc:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4ec0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4ec5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4eca:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4ecf:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4ed4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4edc:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4ee1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4ee9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4eee:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4ef6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4efb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4f03:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4f08:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4f10:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4f15:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4f1d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4f25:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4f2d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4f35:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4f3d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4f45:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4f4d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4f55:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4f5d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4f65:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4f6d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4f74:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4f7c:	e8 6f d4 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4f81:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
    4f85:	31 f6                	xor    %esi,%esi
    4f87:	e8 54 d5 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4f8c:	31 d2                	xor    %edx,%edx
    4f8e:	be 01 00 00 00       	mov    $0x1,%esi
    4f93:	bf 02 00 00 00       	mov    $0x2,%edi
    4f98:	e8 93 d5 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4f9d:	83 f8 ff             	cmp    $0xffffffff,%eax
    4fa0:	0f 84 28 d6 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    4fa6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4fab:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4fb1:	89 c7                	mov    %eax,%edi
    4fb3:	41 89 c4             	mov    %eax,%r12d
    4fb6:	ba 02 00 00 00       	mov    $0x2,%edx
    4fbb:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4fc0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4fc8:	e8 33 d3 ff ff       	call   2300 <setsockopt@plt>
    4fcd:	85 c0                	test   %eax,%eax
    4fcf:	0f 88 cd d5 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4fd5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4fda:	ba 10 00 00 00       	mov    $0x10,%edx
    4fdf:	44 89 e7             	mov    %r12d,%edi
    4fe2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4feb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4ff3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4ffb:	e8 60 d4 ff ff       	call   2460 <bind@plt>
    5000:	85 c0                	test   %eax,%eax
    5002:	0f 88 d2 d5 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5008:	be 0a 00 00 00       	mov    $0xa,%esi
    500d:	44 89 e7             	mov    %r12d,%edi
    5010:	e8 0b d4 ff ff       	call   2420 <listen@plt>
    5015:	85 c0                	test   %eax,%eax
    5017:	0f 88 91 d5 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    501d:	ba db 18 00 00       	mov    $0x18db,%edx
    5022:	48 8d 35 53 21 00 00 	lea    0x2153(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    5029:	bf 01 00 00 00       	mov    $0x1,%edi
    502e:	31 c0                	xor    %eax,%eax
    5030:	e8 1b d4 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5035:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    503a:	48 89 d9             	mov    %rbx,%rcx
    503d:	44 89 e7             	mov    %r12d,%edi
    5040:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5045:	48 89 c6             	mov    %rax,%rsi
    5048:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    504d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5052:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    505a:	e8 81 fd ff ff       	call   4de0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    505f:	bf 01 00 00 00       	mov    $0x1,%edi
    5064:	be 10 00 00 00       	mov    $0x10,%esi
    5069:	e8 32 d3 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    506e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5073:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5076:	e8 95 d3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    507b:	48 85 c0             	test   %rax,%rax
    507e:	0f 84 ae 04 00 00    	je     5532 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5084:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5088:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    508f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5096:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    509e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    50a1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    50a6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    50a8:	f6 c1 02             	test   $0x2,%cl
    50ab:	0f 85 0f 04 00 00    	jne    54c0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    50b1:	89 d0                	mov    %edx,%eax
    50b3:	29 f0                	sub    %esi,%eax
    50b5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    50bc:	0f 82 02 d5 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    50c2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    50c5:	48 8d 75 50          	lea    0x50(%rbp),%rsi
	sqe->addr3 = 0;
    50c9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    50cd:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50d0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    50d7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50da:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    50e1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50e8:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    50ea:	8b 55 50             	mov    0x50(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    50ed:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    50f2:	48 c1 e0 06          	shl    $0x6,%rax
    50f6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    50fe:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5104:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5107:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    510f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5113:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    511b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5123:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5127:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    512b:	e8 10 d2 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5130:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5134:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5139:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5141:	0f 85 d7 01 00 00    	jne    531e <io_thread+0x49e>
    5147:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    514c:	4d 89 ce             	mov    %r9,%r14
    514f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5154:	0f 1f 40 00          	nopl   0x0(%rax)
    5158:	48 8d 3d 33 20 00 00 	lea    0x2033(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    515f:	e8 8c d1 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5164:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    516b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5172:	c1 e9 0b             	shr    $0xb,%ecx
    5175:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5178:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5180:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5182:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    518a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    518c:	39 d0                	cmp    %edx,%eax
    518e:	74 36                	je     51c6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5190:	89 f8                	mov    %edi,%eax
    5192:	21 d0                	and    %edx,%eax
    5194:	d3 e0                	shl    %cl,%eax
    5196:	48 c1 e0 04          	shl    $0x4,%rax
    519a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    51a2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    51aa:	0f 85 a8 01 00 00    	jne    5358 <io_thread+0x4d8>
    51b0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    51b4:	0f 85 0e 03 00 00    	jne    54c8 <io_thread+0x648>
			if (cqe->res < 0)
    51ba:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    51bd:	83 c2 01             	add    $0x1,%edx
    51c0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    51c2:	85 c0                	test   %eax,%eax
    51c4:	79 b2                	jns    5178 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    51c6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    51cf:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    51d0:	45 31 c0             	xor    %r8d,%r8d
    51d3:	31 d2                	xor    %edx,%edx
    51d5:	b9 01 00 00 00       	mov    $0x1,%ecx
    51da:	4c 89 f6             	mov    %r14,%rsi
    51dd:	48 89 df             	mov    %rbx,%rdi
    51e0:	e8 5b d2 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    51e5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    51e8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    51ed:	48 83 38 01          	cmpq   $0x1,(%rax)
    51f1:	0f 84 e1 02 00 00    	je     54d8 <io_thread+0x658>
    51f7:	48 8d 3d ba 1f 00 00 	lea    0x1fba(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    51fe:	e8 ed d0 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5203:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5208:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    520b:	45 85 ff             	test   %r15d,%r15d
    520e:	0f 88 82 d3 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    5214:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5217:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    521b:	85 c0                	test   %eax,%eax
    521d:	0f 88 d5 02 00 00    	js     54f8 <io_thread+0x678>
      switch (req->event_type) {
    5223:	41 83 f8 01          	cmp    $0x1,%r8d
    5227:	0f 84 7b 01 00 00    	je     53a8 <io_thread+0x528>
    522d:	41 83 f8 02          	cmp    $0x2,%r8d
    5231:	0f 84 a1 01 00 00    	je     53d8 <io_thread+0x558>
    5237:	45 85 c0             	test   %r8d,%r8d
    523a:	0f 85 50 01 00 00    	jne    5390 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5240:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5245:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    524a:	48 89 d9             	mov    %rbx,%rcx
    524d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5251:	e8 8a fb ff ff       	call   4de0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5256:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    525b:	48 89 de             	mov    %rbx,%rsi
    525e:	8b 78 08             	mov    0x8(%rax),%edi
    5261:	e8 1a f5 ff ff       	call   4780 <add_read_request>
              free(req);
    5266:	4c 89 e7             	mov    %r12,%rdi
    5269:	e8 52 d0 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    526e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5273:	48 85 c0             	test   %rax,%rax
    5276:	0f 85 14 01 00 00    	jne    5390 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    527c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5283:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    528a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    528d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5292:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5294:	f6 c1 02             	test   $0x2,%cl
    5297:	74 00                	je     5299 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5299:	89 d0                	mov    %edx,%eax
    529b:	29 f0                	sub    %esi,%eax
    529d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    52a4:	0f 82 10 d3 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    52aa:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    52ad:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    52b2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    52b6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52b9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    52c0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52c3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    52ca:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52d1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    52d3:	8b 55 50             	mov    0x50(%rbp),%edx
    52d6:	48 c1 e0 06          	shl    $0x6,%rax
    52da:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    52e2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    52e8:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    52eb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    52f3:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    52f7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    52ff:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5307:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    530b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    530f:	e8 2c d0 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5314:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    5318:	0f 84 3a fe ff ff    	je     5158 <io_thread+0x2d8>
    531e:	48 8d 3d cc 1e 00 00 	lea    0x1ecc(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    5325:	e8 c6 cf ff ff       	call   22f0 <puts@plt>
}
    532a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5332:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    533b:	0f 85 18 02 00 00    	jne    5559 <io_thread+0x6d9>
    5341:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5348:	31 c0                	xor    %eax,%eax
    534a:	5b                   	pop    %rbx
    534b:	5d                   	pop    %rbp
    534c:	41 5c                	pop    %r12
    534e:	41 5d                	pop    %r13
    5350:	41 5e                	pop    %r14
    5352:	41 5f                	pop    %r15
    5354:	c3                   	ret
    5355:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5358:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    535d:	48 85 c0             	test   %rax,%rax
    5360:	0f 84 6a fe ff ff    	je     51d0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5366:	48 83 38 01          	cmpq   $0x1,(%rax)
    536a:	0f 84 68 01 00 00    	je     54d8 <io_thread+0x658>
    5370:	48 8d 3d 41 1e 00 00 	lea    0x1e41(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    5377:	e8 74 cf ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    537c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5381:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5384:	e9 8b fe ff ff       	jmp    5214 <io_thread+0x394>
    5389:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5390:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5398:	8b 02                	mov    (%rdx),%eax
    539a:	83 c0 01             	add    $0x1,%eax
    539d:	89 02                	mov    %eax,(%rdx)
}
    539f:	e9 d8 fe ff ff       	jmp    527c <io_thread+0x3fc>
    53a4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    53a8:	85 c0                	test   %eax,%eax
    53aa:	75 74                	jne    5420 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    53ac:	48 8b 0d 6d 4c 00 00 	mov    0x4c6d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    53b3:	ba 0f 00 00 00       	mov    $0xf,%edx
    53b8:	be 01 00 00 00       	mov    $0x1,%esi
    53bd:	48 8d 3d 1d 1e 00 00 	lea    0x1e1d(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    53c4:	e8 f7 d0 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    53c9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    53ce:	e9 a0 fe ff ff       	jmp    5273 <io_thread+0x3f3>
    53d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    53d8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    53dd:	45 31 ff             	xor    %r15d,%r15d
    53e0:	85 c0                	test   %eax,%eax
    53e2:	7e 20                	jle    5404 <io_thread+0x584>
    53e4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    53e8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    53eb:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    53ef:	48 c1 e0 04          	shl    $0x4,%rax
    53f3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    53f8:	e8 c3 ce ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    53fd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5402:	7f e4                	jg     53e8 <io_thread+0x568>
              close(req->client_socket);
    5404:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5409:	e8 62 cf ff ff       	call   2370 <close@plt>
              free(req);
    540e:	4c 89 e7             	mov    %r12,%rdi
    5411:	e8 aa ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5416:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    541b:	e9 53 fe ff ff       	jmp    5273 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5420:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5425:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    542a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5432:	eb 11                	jmp    5445 <io_thread+0x5c5>
    5434:	0f 1f 40 00          	nopl   0x0(%rax)
    5438:	48 83 c0 01          	add    $0x1,%rax
    543c:	48 83 c2 01          	add    $0x1,%rdx
    5440:	48 39 c6             	cmp    %rax,%rsi
    5443:	74 4b                	je     5490 <io_thread+0x610>
        dest[i] = src[i];
    5445:	0f b6 0a             	movzbl (%rdx),%ecx
    5448:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    544a:	80 f9 0d             	cmp    $0xd,%cl
    544d:	75 e9                	jne    5438 <io_thread+0x5b8>
    544f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5453:	75 e3                	jne    5438 <io_thread+0x5b8>
            dest[i] = '\0';
    5455:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5458:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    545d:	48 89 da             	mov    %rbx,%rdx
    5460:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5465:	e8 96 f7 ff ff       	call   4c00 <handle_http_method>
              free(req->iov[0].iov_base);
    546a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    546f:	e8 4c ce ff ff       	call   22c0 <free@plt>
              free(req);
    5474:	4c 89 e7             	mov    %r12,%rdi
    5477:	e8 44 ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    547c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5481:	e9 ed fd ff ff       	jmp    5273 <io_thread+0x3f3>
    5486:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5490:	48 8b 0d 89 4b 00 00 	mov    0x4b89(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5497:	ba 12 00 00 00       	mov    $0x12,%edx
    549c:	be 01 00 00 00       	mov    $0x1,%esi
    54a1:	48 8d 3d 8f 1c 00 00 	lea    0x1c8f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    54a8:	e8 13 d0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    54ad:	bf 01 00 00 00       	mov    $0x1,%edi
    54b2:	e8 e9 cf ff ff       	call   24a0 <exit@plt>
    54b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    54c0:	e9 ec fb ff ff       	jmp    50b1 <io_thread+0x231>
    54c5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    54c8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    54cd:	e9 94 fe ff ff       	jmp    5366 <io_thread+0x4e6>
    54d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    54d8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    54e0:	48 8d 3d bd 1c 00 00 	lea    0x1cbd(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    54e7:	8b 02                	mov    (%rdx),%eax
    54e9:	83 c0 01             	add    $0x1,%eax
    54ec:	89 02                	mov    %eax,(%rdx)
    54ee:	e8 fd cd ff ff       	call   22f0 <puts@plt>
    54f3:	e9 26 fe ff ff       	jmp    531e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    54f8:	f7 d8                	neg    %eax
    54fa:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    54ff:	89 c7                	mov    %eax,%edi
    5501:	e8 fa cf ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5506:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    550b:	be 01 00 00 00       	mov    $0x1,%esi
    5510:	48 8b 3d 09 4b 00 00 	mov    0x4b09(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5517:	48 89 c1             	mov    %rax,%rcx
    551a:	48 8d 15 17 1f 00 00 	lea    0x1f17(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    5521:	31 c0                	xor    %eax,%eax
    5523:	e8 a8 cf ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5528:	bf 01 00 00 00       	mov    $0x1,%edi
    552d:	e8 6e cf ff ff       	call   24a0 <exit@plt>
    5532:	48 8b 0d e7 4a 00 00 	mov    0x4ae7(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5539:	ba 28 00 00 00       	mov    $0x28,%edx
    553e:	be 01 00 00 00       	mov    $0x1,%esi
    5543:	48 8d 3d be 1e 00 00 	lea    0x1ebe(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    554a:	e8 71 cf ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    554f:	bf 01 00 00 00       	mov    $0x1,%edi
    5554:	e8 47 cf ff ff       	call   24a0 <exit@plt>
}
    5559:	e8 d2 cd ff ff       	call   2330 <__stack_chk_fail@plt>
    555e:	66 90                	xchg   %ax,%ax

0000000000005560 <sendm>:
int sendm(struct BarrierTask *data) {
    5560:	f3 0f 1e fa          	endbr64
    5564:	41 57                	push   %r15
    5566:	41 56                	push   %r14
    5568:	41 55                	push   %r13
    556a:	41 54                	push   %r12
    556c:	55                   	push   %rbp
    556d:	53                   	push   %rbx
    556e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5572:	83 bf f8 00 00 00 01 	cmpl   $0x1,0xf8(%rdi)
    5579:	0f 85 99 01 00 00    	jne    5718 <sendm+0x1b8>
    557f:	48 8d b7 00 01 00 00 	lea    0x100(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5586:	8b 87 b4 00 00 00    	mov    0xb4(%rdi),%eax
    558c:	48 89 fa             	mov    %rdi,%rdx
    558f:	31 c9                	xor    %ecx,%ecx
    5591:	48 89 34 24          	mov    %rsi,(%rsp)
    5595:	48 8d b7 08 01 00 00 	lea    0x108(%rdi),%rsi
    559c:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    55a1:	85 c0                	test   %eax,%eax
    55a3:	0f 8e ce 00 00 00    	jle    5677 <sendm+0x117>
    55a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    55b0:	39 8a b0 00 00 00    	cmp    %ecx,0xb0(%rdx)
    55b6:	0f 84 af 00 00 00    	je     566b <sendm+0x10b>
        struct Data *them = data->mailboxes[n].higher;
    55bc:	49 89 ca             	mov    %rcx,%r10
    55bf:	49 c1 e2 05          	shl    $0x5,%r10
    55c3:	4c 03 92 e8 00 00 00 	add    0xe8(%rdx),%r10
    55ca:	4d 8b 5a 08          	mov    0x8(%r10),%r11
        for (; them->messages_count < min;) {
    55ce:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    55d2:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    55d6:	4c 39 cb             	cmp    %r9,%rbx
    55d9:	0f 8d 83 00 00 00    	jge    5662 <sendm+0x102>
    55df:	4c 89 cf             	mov    %r9,%rdi
    55e2:	48 8b aa 88 00 00 00 	mov    0x88(%rdx),%rbp
    55e9:	4d 8b 72 10          	mov    0x10(%r10),%r14
    55ed:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    55f0:	49 8b 33             	mov    (%r11),%rsi
    55f3:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    55f7:	48 83 f8 02          	cmp    $0x2,%rax
    55fb:	0f 86 ff 00 00 00    	jbe    5700 <sendm+0x1a0>
    5601:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5609:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5611:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    5615:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    5619:	4c 39 2c 24          	cmp    %r13,(%rsp)
    561d:	73 71                	jae    5690 <sendm+0x130>
    561f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5624:	4d 39 fc             	cmp    %r15,%r12
    5627:	73 67                	jae    5690 <sendm+0x130>
    5629:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    562d:	49 01 f0             	add    %rsi,%r8
    5630:	48 8b 82 00 01 00 00 	mov    0x100(%rdx),%rax
        for (; them->messages_count < min;) {
    5637:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    563b:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    563f:	49 39 d8             	cmp    %rbx,%r8
    5642:	75 ec                	jne    5630 <sendm+0xd0>
    5644:	0f 1f 40 00          	nopl   0x0(%rax)
    5648:	48 01 fd             	add    %rdi,%rbp
    564b:	4c 01 f7             	add    %r14,%rdi
    564e:	48 89 aa 88 00 00 00 	mov    %rbp,0x88(%rdx)
    5655:	49 89 7a 10          	mov    %rdi,0x10(%r10)
    5659:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    565d:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5662:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5665:	8b 82 b4 00 00 00    	mov    0xb4(%rdx),%eax
    566b:	48 83 c1 01          	add    $0x1,%rcx
    566f:	39 c8                	cmp    %ecx,%eax
    5671:	0f 8f 39 ff ff ff    	jg     55b0 <sendm+0x50>
}
    5677:	48 83 c4 18          	add    $0x18,%rsp
    567b:	31 c0                	xor    %eax,%eax
    567d:	5b                   	pop    %rbx
    567e:	5d                   	pop    %rbp
    567f:	41 5c                	pop    %r12
    5681:	41 5d                	pop    %r13
    5683:	41 5e                	pop    %r14
    5685:	41 5f                	pop    %r15
    5687:	c3                   	ret
    5688:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5690:	49 89 fd             	mov    %rdi,%r13
    5693:	48 8b 82 00 01 00 00 	mov    0x100(%rdx),%rax
    569a:	4d 89 e0             	mov    %r12,%r8
    569d:	49 d1 ed             	shr    %r13
    56a0:	49 c1 e5 04          	shl    $0x4,%r13
    56a4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    56a9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    56ad:	41 83 e5 10          	and    $0x10,%r13d
    56b1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    56b5:	74 11                	je     56c8 <sendm+0x168>
          them->messages[them->messages_count++] = data->message; 
    56b7:	49 83 c0 10          	add    $0x10,%r8
    56bb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    56c0:	4d 39 f8             	cmp    %r15,%r8
    56c3:	74 15                	je     56da <sendm+0x17a>
    56c5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    56c8:	41 0f 11 00          	movups %xmm0,(%r8)
    56cc:	49 83 c0 20          	add    $0x20,%r8
    56d0:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    56d5:	4d 39 f8             	cmp    %r15,%r8
    56d8:	75 ee                	jne    56c8 <sendm+0x168>
    56da:	49 89 f8             	mov    %rdi,%r8
    56dd:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    56e1:	49 01 d8             	add    %rbx,%r8
    56e4:	40 f6 c7 01          	test   $0x1,%dil
    56e8:	0f 84 5a ff ff ff    	je     5648 <sendm+0xe8>
          them->messages[them->messages_count++] = data->message; 
    56ee:	48 8b 82 00 01 00 00 	mov    0x100(%rdx),%rax
    56f5:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    56f9:	e9 4a ff ff ff       	jmp    5648 <sendm+0xe8>
    56fe:	66 90                	xchg   %ax,%ax
    5700:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5708:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5710:	e9 14 ff ff ff       	jmp    5629 <sendm+0xc9>
    5715:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5718:	48 8d 3d e5 1a 00 00 	lea    0x1ae5(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    571f:	e8 cc cb ff ff       	call   22f0 <puts@plt>
    5724:	e9 4e ff ff ff       	jmp    5677 <sendm+0x117>
    5729:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005730 <receive>:
int receive(struct BarrierTask *data) {
    5730:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5734:	8b 87 b4 00 00 00    	mov    0xb4(%rdi),%eax
    573a:	85 c0                	test   %eax,%eax
    573c:	0f 8e f1 00 00 00    	jle    5833 <receive+0x103>
int receive(struct BarrierTask *data) {
    5742:	41 54                	push   %r12
    5744:	48 89 fa             	mov    %rdi,%rdx
    5747:	55                   	push   %rbp
    5748:	31 ed                	xor    %ebp,%ebp
    574a:	53                   	push   %rbx
    574b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5750:	48 89 ee             	mov    %rbp,%rsi
    5753:	48 c1 e6 05          	shl    $0x5,%rsi
    5757:	48 03 b2 e8 00 00 00 	add    0xe8(%rdx),%rsi
    575e:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5761:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    5766:	48 85 ff             	test   %rdi,%rdi
    5769:	0f 8e a1 00 00 00    	jle    5810 <receive+0xe0>
      data->sends++;
    576f:	48 8b 8a f0 00 00 00 	mov    0xf0(%rdx),%rcx
    5776:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    577a:	4c 63 1a             	movslq (%rdx),%r11
    577d:	49 89 c9             	mov    %rcx,%r9
    5780:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5784:	49 f7 d9             	neg    %r9
    5787:	48 01 c7             	add    %rax,%rdi
    578a:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    578e:	4c 8b 8a 88 00 00 00 	mov    0x88(%rdx),%r9
      data->mailboxes[n].received++;
    5795:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    5799:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    579c:	49 29 c8             	sub    %rcx,%r8
    579f:	eb 10                	jmp    57b1 <receive+0x81>
    57a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    57a8:	48 83 c0 01          	add    $0x1,%rax
    57ac:	48 39 c7             	cmp    %rax,%rdi
    57af:	74 5f                	je     5810 <receive+0xe0>
      data->n++;
    57b1:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    57b5:	48 89 82 f0 00 00 00 	mov    %rax,0xf0(%rdx)
      data->n++;
    57bc:	48 89 8a 88 00 00 00 	mov    %rcx,0x88(%rdx)
      data->mailboxes[n].received++;
    57c3:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    57c7:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    57cb:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    57d0:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    57d4:	75 d2                	jne    57a8 <receive+0x78>
    57d6:	48 63 9a b0 00 00 00 	movslq 0xb0(%rdx),%rbx
    57dd:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    57e1:	75 c5                	jne    57a8 <receive+0x78>
    57e3:	bf 01 00 00 00       	mov    $0x1,%edi
    57e8:	b9 01 00 00 00       	mov    $0x1,%ecx
    57ed:	ba 01 00 00 00       	mov    $0x1,%edx
    57f2:	31 c0                	xor    %eax,%eax
    57f4:	48 8d 35 65 1c 00 00 	lea    0x1c65(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    57fb:	e8 50 cc ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5800:	bf 01 00 00 00       	mov    $0x1,%edi
    5805:	e8 96 cc ff ff       	call   24a0 <exit@plt>
    580a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5810:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    5819:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    581c:	48 83 c5 01          	add    $0x1,%rbp
    5820:	39 aa b4 00 00 00    	cmp    %ebp,0xb4(%rdx)
    5826:	0f 8f 24 ff ff ff    	jg     5750 <receive+0x20>
}
    582c:	5b                   	pop    %rbx
    582d:	31 c0                	xor    %eax,%eax
    582f:	5d                   	pop    %rbp
    5830:	41 5c                	pop    %r12
    5832:	c3                   	ret
    5833:	31 c0                	xor    %eax,%eax
    5835:	c3                   	ret
    5836:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005840 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5840:	f3 0f 1e fa          	endbr64
    5844:	41 57                	push   %r15
    5846:	41 56                	push   %r14
    5848:	41 55                	push   %r13
    584a:	41 54                	push   %r12
    584c:	55                   	push   %rbp
    584d:	53                   	push   %rbx
    584e:	48 89 fb             	mov    %rdi,%rbx
    5851:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    5855:	8b 07                	mov    (%rdi),%eax
    5857:	39 87 b0 00 00 00    	cmp    %eax,0xb0(%rdi)
    585d:	0f 84 3d 01 00 00    	je     59a0 <barriered_work+0x160>
    receive(data);
    5863:	e8 c8 fe ff ff       	call   5730 <receive>
    while (data->scheduled == 1) {
    5868:	83 bb c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbx)
    586f:	75 1b                	jne    588c <barriered_work+0x4c>
    5871:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    5878:	48 83 83 88 00 00 00 01 	addq   $0x1,0x88(%rbx)
      asm volatile ("sfence" ::: "memory");
    5880:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5883:	83 bb c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbx)
    588a:	74 ec                	je     5878 <barriered_work+0x38>
  if (data->sending == 1) {
    588c:	83 bb f8 00 00 00 01 	cmpl   $0x1,0xf8(%rbx)
    5893:	0f 85 78 02 00 00    	jne    5b11 <barriered_work+0x2d1>
      for (int n = 0 ; n < data->thread_count; n++) {
    5899:	8b 83 b4 00 00 00    	mov    0xb4(%rbx),%eax
    589f:	85 c0                	test   %eax,%eax
    58a1:	0f 8e 76 02 00 00    	jle    5b1d <barriered_work+0x2dd>
    58a7:	48 8d 8b 00 01 00 00 	lea    0x100(%rbx),%rcx
    58ae:	31 d2                	xor    %edx,%edx
    58b0:	48 89 0c 24          	mov    %rcx,(%rsp)
    58b4:	48 8d 8b 08 01 00 00 	lea    0x108(%rbx),%rcx
    58bb:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    58c0:	39 93 b0 00 00 00    	cmp    %edx,0xb0(%rbx)
    58c6:	0f 84 bf 00 00 00    	je     598b <barriered_work+0x14b>
        struct Data *them = data->mailboxes[n].higher;
    58cc:	49 89 d1             	mov    %rdx,%r9
    58cf:	49 c1 e1 05          	shl    $0x5,%r9
    58d3:	4c 03 8b e8 00 00 00 	add    0xe8(%rbx),%r9
    58da:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    58de:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    58e2:	4d 63 42 10          	movslq 0x10(%r10),%r8
    58e6:	4d 39 c3             	cmp    %r8,%r11
    58e9:	0f 8d 93 00 00 00    	jge    5982 <barriered_work+0x142>
    58ef:	4c 89 c6             	mov    %r8,%rsi
    58f2:	48 8b ab 88 00 00 00 	mov    0x88(%rbx),%rbp
    58f9:	4d 8b 71 10          	mov    0x10(%r9),%r14
    58fd:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5900:	49 8b 0a             	mov    (%r10),%rcx
    5903:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5907:	48 83 f8 02          	cmp    $0x2,%rax
    590b:	0f 86 97 02 00 00    	jbe    5ba8 <barriered_work+0x368>
    5911:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5919:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5921:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5925:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5929:	4c 39 2c 24          	cmp    %r13,(%rsp)
    592d:	0f 83 05 02 00 00    	jae    5b38 <barriered_work+0x2f8>
    5933:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5938:	4d 39 fc             	cmp    %r15,%r12
    593b:	0f 83 f7 01 00 00    	jae    5b38 <barriered_work+0x2f8>
    5941:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5945:	48 01 cf             	add    %rcx,%rdi
    5948:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5950:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
        for (; them->messages_count < min;) {
    5957:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    595b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    595f:	49 39 fb             	cmp    %rdi,%r11
    5962:	75 ec                	jne    5950 <barriered_work+0x110>
    5964:	0f 1f 40 00          	nopl   0x0(%rax)
    5968:	48 01 f5             	add    %rsi,%rbp
    596b:	4c 01 f6             	add    %r14,%rsi
    596e:	48 89 ab 88 00 00 00 	mov    %rbp,0x88(%rbx)
    5975:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5979:	4d 89 42 08          	mov    %r8,0x8(%r10)
    597d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5982:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5985:	8b 83 b4 00 00 00    	mov    0xb4(%rbx),%eax
    598b:	48 83 c2 01          	add    $0x1,%rdx
    598f:	39 d0                	cmp    %edx,%eax
    5991:	0f 8f 29 ff ff ff    	jg     58c0 <barriered_work+0x80>
    5997:	e9 81 01 00 00       	jmp    5b1d <barriered_work+0x2dd>
    599c:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    59a0:	e8 8b fd ff ff       	call   5730 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    59a5:	4c 63 8b b4 00 00 00 	movslq 0xb4(%rbx),%r9
        int t = data->task_index;
    59ac:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    59ae:	45 85 c9             	test   %r9d,%r9d
    59b1:	0f 8e 85 00 00 00    	jle    5a3c <barriered_work+0x1fc>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59b7:	48 8b 93 a8 00 00 00 	mov    0xa8(%rbx),%rdx
    59be:	4c 8b 52 10          	mov    0x10(%rdx),%r10
    59c2:	48 63 d0             	movslq %eax,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
    59c5:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59c8:	4c 8d 1c 52          	lea    (%rdx,%rdx,2),%r11
              int next_task = abs((t + 1) % (data->thread_count));
    59cc:	99                   	cltd
    59cd:	41 f7 f9             	idiv   %r9d
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59d0:	49 c1 e3 07          	shl    $0x7,%r11
    59d4:	4c 89 d7             	mov    %r10,%rdi
    59d7:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
              int next_task = abs((t + 1) % (data->thread_count));
    59db:	89 d0                	mov    %edx,%eax
    59dd:	f7 d8                	neg    %eax
    59df:	0f 48 c2             	cmovs  %edx,%eax
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59e2:	45 31 c0             	xor    %r8d,%r8d
    59e5:	48 98                	cltq
    59e7:	48 8d 2c 40          	lea    (%rax,%rax,2),%rbp
    59eb:	48 c1 e5 07          	shl    $0x7,%rbp
    59ef:	90                   	nop
int barriered_work(struct BarrierTask *data) {
    59f0:	31 c0                	xor    %eax,%eax
    59f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59f8:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    59fc:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    5a00:	48 8b 8c 2a e8 00 00 00 	mov    0xe8(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5a08:	48 8b 17             	mov    (%rdi),%rdx
    5a0b:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    5a0f:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5a12:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5a16:	48 c1 e2 05          	shl    $0x5,%rdx
    5a1a:	4a 03 94 1e e8 00 00 00 	add    0xe8(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5a22:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    5a26:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    5a2a:	49 39 c1             	cmp    %rax,%r9
    5a2d:	75 c9                	jne    59f8 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    5a2f:	48 83 c7 08          	add    $0x8,%rdi
    5a33:	49 83 c0 20          	add    $0x20,%r8
    5a37:	49 39 fc             	cmp    %rdi,%r12
    5a3a:	75 b4                	jne    59f0 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    5a3c:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5a3f:	48 8b b3 d8 00 00 00 	mov    0xd8(%rbx),%rsi
    5a46:	31 ff                	xor    %edi,%edi
    5a48:	48 c1 e6 05          	shl    $0x5,%rsi
    5a4c:	48 03 b3 c8 00 00 00 	add    0xc8(%rbx),%rsi
    5a53:	e8 b8 c8 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5a58:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    while (data->scheduled == 1) {
    5a5f:	83 bb c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5a66:	48 8b 50 38          	mov    0x38(%rax),%rdx
    5a6a:	8b 4a 10             	mov    0x10(%rdx),%ecx
    5a6d:	8d 69 01             	lea    0x1(%rcx),%ebp
    5a70:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5a73:	75 57                	jne    5acc <barriered_work+0x28c>
    5a75:	0f 1f 00             	nopl   (%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a78:	48 63 93 b0 00 00 00 	movslq 0xb0(%rbx),%rdx
    5a7f:	48 8b 40 10          	mov    0x10(%rax),%rax
      data->n++;
    5a83:	48 83 83 88 00 00 00 01 	addq   $0x1,0x88(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a8b:	48 8b 14 d0          	mov    (%rax,%rdx,8),%rdx
    5a8f:	48 63 03             	movslq (%rbx),%rax
    5a92:	48 8d 3c 40          	lea    (%rax,%rax,2),%rdi
    5a96:	48 c1 e7 07          	shl    $0x7,%rdi
    5a9a:	48 03 7a 28          	add    0x28(%rdx),%rdi
    5a9e:	ff 93 a0 00 00 00    	call   *0xa0(%rbx)
      asm volatile ("sfence" ::: "memory");
    5aa4:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5aa7:	83 bb c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    5aae:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    while (data->scheduled == 1) {
    5ab5:	74 c1                	je     5a78 <barriered_work+0x238>
    if (modcount != data->thread->protected_state->modcount) {
    5ab7:	48 8b 40 38          	mov    0x38(%rax),%rax
    5abb:	3b 68 10             	cmp    0x10(%rax),%ebp
    5abe:	74 0c                	je     5acc <barriered_work+0x28c>
    5ac0:	48 8d 3d 49 17 00 00 	lea    0x1749(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    5ac7:	e8 24 c8 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5acc:	48 8b b3 d8 00 00 00 	mov    0xd8(%rbx),%rsi
    5ad3:	31 ff                	xor    %edi,%edi
    5ad5:	48 c1 e6 05          	shl    $0x5,%rsi
    5ad9:	48 03 b3 c8 00 00 00 	add    0xc8(%rbx),%rsi
    5ae0:	48 83 c6 10          	add    $0x10,%rsi
    5ae4:	e8 27 c8 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5ae9:	48 8b 83 d8 00 00 00 	mov    0xd8(%rbx),%rax
    5af0:	48 83 c0 01          	add    $0x1,%rax
    5af4:	48 99                	cqto
    5af6:	48 f7 bb d0 00 00 00 	idivq  0xd0(%rbx)
  if (data->sending == 1) {
    5afd:	83 bb f8 00 00 00 01 	cmpl   $0x1,0xf8(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5b04:	48 89 93 d8 00 00 00 	mov    %rdx,0xd8(%rbx)
  if (data->sending == 1) {
    5b0b:	0f 84 ac 00 00 00    	je     5bbd <barriered_work+0x37d>
    5b11:	48 8d 3d ec 16 00 00 	lea    0x16ec(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5b18:	e8 d3 c7 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5b1d:	0f ae f8             	sfence
}
    5b20:	48 83 c4 18          	add    $0x18,%rsp
    5b24:	31 c0                	xor    %eax,%eax
    5b26:	5b                   	pop    %rbx
    5b27:	5d                   	pop    %rbp
    5b28:	41 5c                	pop    %r12
    5b2a:	41 5d                	pop    %r13
    5b2c:	41 5e                	pop    %r14
    5b2e:	41 5f                	pop    %r15
    5b30:	c3                   	ret
    5b31:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5b38:	49 89 f5             	mov    %rsi,%r13
    5b3b:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
    5b42:	4c 89 e7             	mov    %r12,%rdi
    5b45:	49 d1 ed             	shr    %r13
    5b48:	49 c1 e5 04          	shl    $0x4,%r13
    5b4c:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5b51:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5b55:	41 83 e5 10          	and    $0x10,%r13d
    5b59:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5b5d:	74 11                	je     5b70 <barriered_work+0x330>
          them->messages[them->messages_count++] = data->message; 
    5b5f:	48 83 c7 10          	add    $0x10,%rdi
    5b63:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5b68:	49 39 ff             	cmp    %rdi,%r15
    5b6b:	74 13                	je     5b80 <barriered_work+0x340>
    5b6d:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5b70:	0f 11 07             	movups %xmm0,(%rdi)
    5b73:	48 83 c7 20          	add    $0x20,%rdi
    5b77:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5b7b:	49 39 ff             	cmp    %rdi,%r15
    5b7e:	75 f0                	jne    5b70 <barriered_work+0x330>
    5b80:	48 89 f7             	mov    %rsi,%rdi
    5b83:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5b87:	4c 01 df             	add    %r11,%rdi
    5b8a:	40 f6 c6 01          	test   $0x1,%sil
    5b8e:	0f 84 d4 fd ff ff    	je     5968 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    5b94:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
    5b9b:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5b9f:	e9 c4 fd ff ff       	jmp    5968 <barriered_work+0x128>
    5ba4:	0f 1f 40 00          	nopl   0x0(%rax)
    5ba8:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5bb0:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5bb8:	e9 84 fd ff ff       	jmp    5941 <barriered_work+0x101>
      for (int n = 0 ; n < data->thread_count; n++) {
    5bbd:	48 8d 8b 00 01 00 00 	lea    0x100(%rbx),%rcx
    5bc4:	8b 83 b4 00 00 00    	mov    0xb4(%rbx),%eax
    5bca:	31 d2                	xor    %edx,%edx
    5bcc:	48 89 0c 24          	mov    %rcx,(%rsp)
    5bd0:	48 8d 8b 08 01 00 00 	lea    0x108(%rbx),%rcx
    5bd7:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5bdc:	85 c0                	test   %eax,%eax
    5bde:	0f 8e 39 ff ff ff    	jle    5b1d <barriered_work+0x2dd>
    5be4:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5be8:	39 93 b0 00 00 00    	cmp    %edx,0xb0(%rbx)
    5bee:	0f 84 b7 00 00 00    	je     5cab <barriered_work+0x46b>
        struct Data *them = data->mailboxes[n].higher;
    5bf4:	49 89 d1             	mov    %rdx,%r9
    5bf7:	49 c1 e1 05          	shl    $0x5,%r9
    5bfb:	4c 03 8b e8 00 00 00 	add    0xe8(%rbx),%r9
    5c02:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    5c06:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5c0a:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5c0e:	4d 39 d8             	cmp    %r11,%r8
    5c11:	0f 8e 8b 00 00 00    	jle    5ca2 <barriered_work+0x462>
    5c17:	4c 89 c6             	mov    %r8,%rsi
    5c1a:	48 8b ab 88 00 00 00 	mov    0x88(%rbx),%rbp
    5c21:	4d 8b 71 10          	mov    0x10(%r9),%r14
    5c25:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5c28:	49 8b 0a             	mov    (%r10),%rcx
    5c2b:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5c2f:	48 83 f8 02          	cmp    $0x2,%rax
    5c33:	0f 86 f7 00 00 00    	jbe    5d30 <barriered_work+0x4f0>
    5c39:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5c41:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5c49:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5c4d:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5c51:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5c55:	73 69                	jae    5cc0 <barriered_work+0x480>
    5c57:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5c5c:	4d 39 fc             	cmp    %r15,%r12
    5c5f:	73 5f                	jae    5cc0 <barriered_work+0x480>
    5c61:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5c65:	48 01 cf             	add    %rcx,%rdi
    5c68:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5c70:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
        for (; them->messages_count < min;) {
    5c77:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5c7b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5c7f:	49 39 fb             	cmp    %rdi,%r11
    5c82:	75 ec                	jne    5c70 <barriered_work+0x430>
    5c84:	0f 1f 40 00          	nopl   0x0(%rax)
    5c88:	48 01 f5             	add    %rsi,%rbp
    5c8b:	4c 01 f6             	add    %r14,%rsi
    5c8e:	48 89 ab 88 00 00 00 	mov    %rbp,0x88(%rbx)
    5c95:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5c99:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5c9d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5ca2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5ca5:	8b 83 b4 00 00 00    	mov    0xb4(%rbx),%eax
    5cab:	48 83 c2 01          	add    $0x1,%rdx
    5caf:	39 d0                	cmp    %edx,%eax
    5cb1:	0f 8f 31 ff ff ff    	jg     5be8 <barriered_work+0x3a8>
    5cb7:	e9 61 fe ff ff       	jmp    5b1d <barriered_work+0x2dd>
    5cbc:	0f 1f 40 00          	nopl   0x0(%rax)
    5cc0:	49 89 f5             	mov    %rsi,%r13
    5cc3:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
    5cca:	4c 89 e7             	mov    %r12,%rdi
    5ccd:	49 d1 ed             	shr    %r13
    5cd0:	49 c1 e5 04          	shl    $0x4,%r13
    5cd4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5cd9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5cdd:	41 83 e5 10          	and    $0x10,%r13d
    5ce1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5ce5:	74 11                	je     5cf8 <barriered_work+0x4b8>
          them->messages[them->messages_count++] = data->message; 
    5ce7:	48 83 c7 10          	add    $0x10,%rdi
    5ceb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5cf0:	4c 39 ff             	cmp    %r15,%rdi
    5cf3:	74 13                	je     5d08 <barriered_work+0x4c8>
    5cf5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5cf8:	0f 11 07             	movups %xmm0,(%rdi)
    5cfb:	48 83 c7 20          	add    $0x20,%rdi
    5cff:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5d03:	4c 39 ff             	cmp    %r15,%rdi
    5d06:	75 f0                	jne    5cf8 <barriered_work+0x4b8>
    5d08:	48 89 f7             	mov    %rsi,%rdi
    5d0b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5d0f:	4c 01 df             	add    %r11,%rdi
    5d12:	40 f6 c6 01          	test   $0x1,%sil
    5d16:	0f 84 6c ff ff ff    	je     5c88 <barriered_work+0x448>
          them->messages[them->messages_count++] = data->message; 
    5d1c:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
    5d23:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5d27:	e9 5c ff ff ff       	jmp    5c88 <barriered_work+0x448>
    5d2c:	0f 1f 40 00          	nopl   0x0(%rax)
    5d30:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5d38:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5d40:	e9 1c ff ff ff       	jmp    5c61 <barriered_work+0x421>
    5d45:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005d50 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5d50:	f3 0f 1e fa          	endbr64
    5d54:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5d58:	48 8b 87 a8 00 00 00 	mov    0xa8(%rdi),%rax
    5d5f:	48 8b 40 40          	mov    0x40(%rax),%rax
    5d63:	48 63 10             	movslq (%rax),%rdx
    5d66:	85 d2                	test   %edx,%edx
    5d68:	7e 2c                	jle    5d96 <barriered_work_ingest+0x46>
    5d6a:	48 8b 40 08          	mov    0x8(%rax),%rax
    5d6e:	48 c1 e2 04          	shl    $0x4,%rdx
    5d72:	48 01 c2             	add    %rax,%rdx
    5d75:	0f 1f 00             	nopl   (%rax)
    if (data->thread->buffers->buffer[x].available == 1) {
    5d78:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5d7c:	75 0f                	jne    5d8d <barriered_work_ingest+0x3d>
      data->ingest_count++;
    5d7e:	48 83 87 e0 00 00 00 01 	addq   $0x1,0xe0(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5d86:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5d8d:	48 83 c0 10          	add    $0x10,%rax
    5d91:	48 39 d0             	cmp    %rdx,%rax
    5d94:	75 e2                	jne    5d78 <barriered_work_ingest+0x28>
  asm volatile ("sfence" ::: "memory");
    5d96:	0f ae f8             	sfence
  barriered_work(data);
    5d99:	e8 a2 fa ff ff       	call   5840 <barriered_work>
}
    5d9e:	31 c0                	xor    %eax,%eax
    5da0:	48 83 c4 08          	add    $0x8,%rsp
    5da4:	c3                   	ret
    5da5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005db0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5db0:	f3 0f 1e fa          	endbr64
}
    5db4:	31 c0                	xor    %eax,%eax
    5db6:	c3                   	ret
    5db7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005dc0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5dc0:	f3 0f 1e fa          	endbr64
    5dc4:	31 c0                	xor    %eax,%eax
    5dc6:	c3                   	ret
    5dc7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005dd0 <after>:
int after(struct timespec left, struct timespec right) {
    5dd0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5dd4:	31 c0                	xor    %eax,%eax
    5dd6:	48 39 d7             	cmp    %rdx,%rdi
    5dd9:	7e 08                	jle    5de3 <after+0x13>
    5ddb:	31 c0                	xor    %eax,%eax
    5ddd:	48 39 ce             	cmp    %rcx,%rsi
    5de0:	0f 9f c0             	setg   %al
}
    5de3:	c3                   	ret
    5de4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5def:	90                   	nop

0000000000005df0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5df0:	f3 0f 1e fa          	endbr64
    5df4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5df9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5dfe:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e00:	48 39 d7             	cmp    %rdx,%rdi
    5e03:	7f 18                	jg     5e1d <within+0x2d>
    5e05:	4d 39 d8             	cmp    %r11,%r8
    5e08:	0f 9e c2             	setle  %dl
    5e0b:	48 39 ce             	cmp    %rcx,%rsi
    5e0e:	0f 9e c0             	setle  %al
    5e11:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e13:	31 c0                	xor    %eax,%eax
    5e15:	4d 39 d1             	cmp    %r10,%r9
    5e18:	0f 9e c0             	setle  %al
    5e1b:	21 d0                	and    %edx,%eax
}
    5e1d:	c3                   	ret
    5e1e:	66 90                	xchg   %ax,%ax

0000000000005e20 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5e20:	f3 0f 1e fa          	endbr64
    5e24:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5e29:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5e2e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5e33:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5e38:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5e3d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5e42:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5e47:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5e4c:	48 39 fe             	cmp    %rdi,%rsi
    5e4f:	7d 2f                	jge    5e80 <overlap+0x60>
    5e51:	48 39 ca             	cmp    %rcx,%rdx
    5e54:	7d 62                	jge    5eb8 <overlap+0x98>
    5e56:	4d 39 da             	cmp    %r11,%r10
    5e59:	7d 0e                	jge    5e69 <overlap+0x49>
    return 1;
    5e5b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e60:	4d 39 c1             	cmp    %r8,%r9
    5e63:	0f 8c 7f 00 00 00    	jl     5ee8 <overlap+0xc8>
  return 0;
    5e69:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e6b:	4d 39 c1             	cmp    %r8,%r9
    5e6e:	7f 4c                	jg     5ebc <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e70:	31 c0                	xor    %eax,%eax
    5e72:	4d 39 da             	cmp    %r11,%r10
    5e75:	0f 9e c0             	setle  %al
    5e78:	c3                   	ret
    5e79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5e80:	7e 4e                	jle    5ed0 <overlap+0xb0>
    5e82:	48 39 ca             	cmp    %rcx,%rdx
    5e85:	7f 39                	jg     5ec0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e87:	75 31                	jne    5eba <overlap+0x9a>
    5e89:	4d 39 c1             	cmp    %r8,%r9
    5e8c:	7c 2c                	jl     5eba <overlap+0x9a>
    return 1;
    5e8e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e93:	4d 39 da             	cmp    %r11,%r10
    5e96:	7d 24                	jge    5ebc <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e98:	48 39 ca             	cmp    %rcx,%rdx
    5e9b:	0f 94 c2             	sete   %dl
    5e9e:	48 39 fe             	cmp    %rdi,%rsi
    5ea1:	0f 94 c0             	sete   %al
    5ea4:	21 c2                	and    %eax,%edx
    5ea6:	31 c0                	xor    %eax,%eax
    5ea8:	4d 39 c1             	cmp    %r8,%r9
    5eab:	0f 94 c0             	sete   %al
    5eae:	21 d0                	and    %edx,%eax
    5eb0:	c3                   	ret
    5eb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5eb8:	74 af                	je     5e69 <overlap+0x49>
  return 0;
    5eba:	31 c0                	xor    %eax,%eax
}
    5ebc:	c3                   	ret
    5ebd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5ec0:	4d 39 da             	cmp    %r11,%r10
    5ec3:	7e c4                	jle    5e89 <overlap+0x69>
    return 1;
    5ec5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5eca:	4d 39 c1             	cmp    %r8,%r9
    5ecd:	7e ba                	jle    5e89 <overlap+0x69>
    5ecf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ed0:	48 39 ca             	cmp    %rcx,%rdx
    5ed3:	7c 94                	jl     5e69 <overlap+0x49>
    5ed5:	4d 39 c1             	cmp    %r8,%r9
    5ed8:	7d b4                	jge    5e8e <overlap+0x6e>
    5eda:	48 39 ca             	cmp    %rcx,%rdx
    5edd:	74 91                	je     5e70 <overlap+0x50>
    5edf:	eb d9                	jmp    5eba <overlap+0x9a>
    5ee1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5ee8:	c3                   	ret
    5ee9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005ef0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5ef0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5ef4:	85 f6                	test   %esi,%esi
    5ef6:	0f 8e 49 03 00 00    	jle    6245 <verify+0x355>
int verify(struct KernelThread *thread_data, int thread_count) {
    5efc:	41 57                	push   %r15
    5efe:	41 89 f7             	mov    %esi,%r15d
    5f01:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5f03:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5f06:	41 55                	push   %r13
    5f08:	41 54                	push   %r12
    5f0a:	55                   	push   %rbp
    5f0b:	53                   	push   %rbx
    5f0c:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5f10:	48 83 ec 48          	sub    $0x48,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5f14:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5f19:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    5f1e:	45 31 e4             	xor    %r12d,%r12d
    5f21:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
      if (z != x)  {
    5f26:	45 39 e6             	cmp    %r12d,%r14d
    5f29:	0f 84 47 02 00 00    	je     6176 <verify+0x286>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5f2f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5f34:	8b 50 08             	mov    0x8(%rax),%edx
    5f37:	85 d2                	test   %edx,%edx
    5f39:	0f 8e 37 02 00 00    	jle    6176 <verify+0x286>
    5f3f:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    5f47:	31 ed                	xor    %ebp,%ebp
    5f49:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    5f4e:	44 89 7c 24 34       	mov    %r15d,0x34(%rsp)
    5f53:	45 89 f7             	mov    %r14d,%r15d
    5f56:	41 89 ee             	mov    %ebp,%r14d
    5f59:	44 89 fa             	mov    %r15d,%edx
    5f5c:	48 8d 35 bd 12 00 00 	lea    0x12bd(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    5f63:	bf 01 00 00 00       	mov    $0x1,%edi
    5f68:	31 c0                	xor    %eax,%eax
    5f6a:	e8 e1 c4 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5f6f:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5f74:	8b 40 08             	mov    0x8(%rax),%eax
    5f77:	85 c0                	test   %eax,%eax
    5f79:	0f 8e cf 01 00 00    	jle    614e <verify+0x25e>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5f7f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5f84:	44 89 74 24 38       	mov    %r14d,0x38(%rsp)
    5f89:	31 db                	xor    %ebx,%ebx
    5f8b:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    5f90:	4c 8b 20             	mov    (%rax),%r12
    5f93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5f98:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    5f9d:	48 8d 04 5b          	lea    (%rbx,%rbx,2),%rax
    5fa1:	4c 8b 3c 24          	mov    (%rsp),%r15
    5fa5:	48 8d 35 89 12 00 00 	lea    0x1289(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5fac:	49 89 c6             	mov    %rax,%r14
    5faf:	bf 01 00 00 00       	mov    $0x1,%edi
    5fb4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5fb8:	49 c1 e6 07          	shl    $0x7,%r14
    5fbc:	4b 8b 8c 3c d8 00 00 00 	mov    0xd8(%r12,%r15,1),%rcx
    5fc4:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    5fc9:	4a 8b 94 30 d8 00 00 00 	mov    0xd8(%rax,%r14,1),%rdx
    5fd1:	31 c0                	xor    %eax,%eax
    5fd3:	e8 78 c4 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5fd8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5fdd:	4c 8b 20             	mov    (%rax),%r12
    5fe0:	4b 83 bc 3c d8 00 00 00 00 	cmpq   $0x0,0xd8(%r12,%r15,1)
    5fe9:	0f 8e 43 01 00 00    	jle    6132 <verify+0x242>
    5fef:	4c 03 75 00          	add    0x0(%rbp),%r14
    5ff3:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5ff8:	ba 01 00 00 00       	mov    $0x1,%edx
    5ffd:	4d 89 f5             	mov    %r14,%r13
    6000:	4d 8b b5 d8 00 00 00 	mov    0xd8(%r13),%r14
    6007:	4d 85 f6             	test   %r14,%r14
    600a:	0f 8e 1d 01 00 00    	jle    612d <verify+0x23d>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6010:	48 89 d5             	mov    %rdx,%rbp
    6013:	48 8b 04 24          	mov    (%rsp),%rax
    6017:	31 db                	xor    %ebx,%ebx
    6019:	4d 89 f2             	mov    %r14,%r10
    601c:	48 c1 e5 05          	shl    $0x5,%rbp
    6020:	48 83 ed 20          	sub    $0x20,%rbp
    6024:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6028:	49 89 ee             	mov    %rbp,%r14
    602b:	48 89 dd             	mov    %rbx,%rbp
    602e:	48 89 d3             	mov    %rdx,%rbx
    6031:	eb 32                	jmp    6065 <verify+0x175>
    6033:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6038:	4c 39 c2             	cmp    %r8,%rdx
    603b:	0f 8d 57 01 00 00    	jge    6198 <verify+0x2a8>
    6041:	4c 39 df             	cmp    %r11,%rdi
    6044:	7e 05                	jle    604b <verify+0x15b>
    6046:	49 39 c1             	cmp    %rax,%r9
    6049:	7c 75                	jl     60c0 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    604b:	4c 39 df             	cmp    %r11,%rdi
    604e:	0f 8d b3 01 00 00    	jge    6207 <verify+0x317>
    6054:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6058:	48 83 c5 01          	add    $0x1,%rbp
    605c:	49 39 ea             	cmp    %rbp,%r10
    605f:	0f 8e a8 00 00 00    	jle    610d <verify+0x21d>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6065:	49 8b 97 c8 00 00 00 	mov    0xc8(%r15),%rdx
    606c:	48 89 e8             	mov    %rbp,%rax
    606f:	48 c1 e0 05          	shl    $0x5,%rax
    6073:	49 03 85 c8 00 00 00 	add    0xc8(%r13),%rax
    607a:	4c 01 f2             	add    %r14,%rdx
    607d:	48 8b 08             	mov    (%rax),%rcx
    6080:	48 8b 78 10          	mov    0x10(%rax),%rdi
    6084:	48 8b 32             	mov    (%rdx),%rsi
    6087:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    608b:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    608f:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    6093:	48 8b 50 08          	mov    0x8(%rax),%rdx
    6097:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    609b:	48 39 f1             	cmp    %rsi,%rcx
    609e:	7c 98                	jl     6038 <verify+0x148>
    60a0:	0f 8e 4a 01 00 00    	jle    61f0 <verify+0x300>
    60a6:	4c 39 c2             	cmp    %r8,%rdx
    60a9:	0f 8f f9 00 00 00    	jg     61a8 <verify+0x2b8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    60af:	75 a7                	jne    6058 <verify+0x168>
    60b1:	4c 39 df             	cmp    %r11,%rdi
    60b4:	7f a2                	jg     6058 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    60b6:	49 39 c1             	cmp    %rax,%r9
    60b9:	7c 9d                	jl     6058 <verify+0x168>
    60bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    60c0:	49 89 c1             	mov    %rax,%r9
    60c3:	48 89 f9             	mov    %rdi,%rcx
    60c6:	48 89 f2             	mov    %rsi,%rdx
    60c9:	bf 01 00 00 00       	mov    $0x1,%edi
    60ce:	48 8d 35 b3 13 00 00 	lea    0x13b3(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    60d5:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60d7:	48 83 c5 01          	add    $0x1,%rbp
    60db:	e8 70 c3 ff ff       	call   2450 <__printf_chk@plt>
    60e0:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    60e5:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    60ea:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60ed:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60f2:	4d 8b 95 d8 00 00 00 	mov    0xd8(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60f9:	4c 8b 20             	mov    (%rax),%r12
    60fc:	48 8b 04 24          	mov    (%rsp),%rax
    6100:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6104:	49 39 ea             	cmp    %rbp,%r10
    6107:	0f 8f 58 ff ff ff    	jg     6065 <verify+0x175>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    610d:	48 89 da             	mov    %rbx,%rdx
    6110:	49 3b 9f d8 00 00 00 	cmp    0xd8(%r15),%rbx
    6117:	7d 14                	jge    612d <verify+0x23d>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6119:	4d 8b b5 d8 00 00 00 	mov    0xd8(%r13),%r14
    6120:	48 83 c2 01          	add    $0x1,%rdx
    6124:	4d 85 f6             	test   %r14,%r14
    6127:	0f 8f e3 fe ff ff    	jg     6010 <verify+0x120>
    612d:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6132:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6137:	48 83 c3 01          	add    $0x1,%rbx
    613b:	39 58 08             	cmp    %ebx,0x8(%rax)
    613e:	0f 8f 54 fe ff ff    	jg     5f98 <verify+0xa8>
    6144:	44 8b 74 24 38       	mov    0x38(%rsp),%r14d
    6149:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    614e:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6153:	48 81 04 24 80 01 00 00 	addq   $0x180,(%rsp)
    615b:	41 83 c6 01          	add    $0x1,%r14d
    615f:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    6163:	0f 8f f0 fd ff ff    	jg     5f59 <verify+0x69>
    6169:	45 89 fe             	mov    %r15d,%r14d
    616c:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    6171:	44 8b 7c 24 34       	mov    0x34(%rsp),%r15d
    for (int z = 0 ; z < thread_count; z++) {
    6176:	48 81 44 24 08 b0 00 00 00 	addq   $0xb0,0x8(%rsp)
    617f:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6184:	41 39 c7             	cmp    %eax,%r15d
    6187:	0f 84 88 00 00 00    	je     6215 <verify+0x325>
    618d:	41 89 c4             	mov    %eax,%r12d
    6190:	e9 91 fd ff ff       	jmp    5f26 <verify+0x36>
    6195:	0f 1f 00             	nopl   (%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6198:	0f 85 ba fe ff ff    	jne    6058 <verify+0x168>
    619e:	e9 a8 fe ff ff       	jmp    604b <verify+0x15b>
    61a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    61a8:	49 39 c1             	cmp    %rax,%r9
    61ab:	7e 09                	jle    61b6 <verify+0x2c6>
    61ad:	4c 39 df             	cmp    %r11,%rdi
    61b0:	0f 8c 0a ff ff ff    	jl     60c0 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    61b6:	4c 39 df             	cmp    %r11,%rdi
    61b9:	0f 8f 99 fe ff ff    	jg     6058 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    61bf:	49 39 c1             	cmp    %rax,%r9
    61c2:	0f 8d f8 fe ff ff    	jge    60c0 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    61c8:	48 39 f1             	cmp    %rsi,%rcx
    61cb:	0f 85 87 fe ff ff    	jne    6058 <verify+0x168>
    61d1:	4c 39 c2             	cmp    %r8,%rdx
    61d4:	0f 85 7e fe ff ff    	jne    6058 <verify+0x168>
    61da:	4c 39 df             	cmp    %r11,%rdi
    61dd:	0f 84 dd fe ff ff    	je     60c0 <verify+0x1d0>
    61e3:	e9 70 fe ff ff       	jmp    6058 <verify+0x168>
    61e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    61f0:	4c 39 c2             	cmp    %r8,%rdx
    61f3:	0f 8c 52 fe ff ff    	jl     604b <verify+0x15b>
    61f9:	4c 39 df             	cmp    %r11,%rdi
    61fc:	7e c1                	jle    61bf <verify+0x2cf>
    61fe:	4c 39 c2             	cmp    %r8,%rdx
    6201:	0f 85 51 fe ff ff    	jne    6058 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6207:	49 39 c1             	cmp    %rax,%r9
    620a:	0f 8f 48 fe ff ff    	jg     6058 <verify+0x168>
    6210:	e9 ab fe ff ff       	jmp    60c0 <verify+0x1d0>
  for (int x = 0 ; x < thread_count; x++) {
    6215:	48 81 44 24 10 b0 00 00 00 	addq   $0xb0,0x10(%rsp)
    621e:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    6223:	41 8d 46 01          	lea    0x1(%r14),%eax
    6227:	45 39 e6             	cmp    %r12d,%r14d
    622a:	74 08                	je     6234 <verify+0x344>
    622c:	41 89 c6             	mov    %eax,%r14d
    622f:	e9 e5 fc ff ff       	jmp    5f19 <verify+0x29>
}
    6234:	48 83 c4 48          	add    $0x48,%rsp
    6238:	31 c0                	xor    %eax,%eax
    623a:	5b                   	pop    %rbx
    623b:	5d                   	pop    %rbp
    623c:	41 5c                	pop    %r12
    623e:	41 5d                	pop    %r13
    6240:	41 5e                	pop    %r14
    6242:	41 5f                	pop    %r15
    6244:	c3                   	ret
    6245:	31 c0                	xor    %eax,%eax
    6247:	c3                   	ret

Disassembly of section .fini:

0000000000006248 <_fini>:
    6248:	f3 0f 1e fa          	endbr64
    624c:	48 83 ec 08          	sub    $0x8,%rsp
    6250:	48 83 c4 08          	add    $0x8,%rsp
    6254:	c3                   	ret
