
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
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    2603:	45 31 e4             	xor    %r12d,%r12d
int main() {
    2606:	55                   	push   %rbp
    2607:	53                   	push   %rbx
    2608:	48 81 ec 98 00 00 00 	sub    $0x98,%rsp
    260f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2618:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    2620:	48 8d 05 09 10 00 00 	lea    0x1009(%rip),%rax        # 3630 <barriered_reset>
    2627:	66 48 0f 6e e8       	movq   %rax,%xmm5
    262c:	0f 16 2d 45 76 00 00 	movhps 0x7645(%rip),%xmm5        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    2633:	0f 29 6c 24 30       	movaps %xmm5,0x30(%rsp)
    2638:	e8 b3 fc ff ff       	call   22f0 <puts@plt>
    263d:	bf 0a 00 00 00       	mov    $0xa,%edi
    2642:	e8 89 fc ff ff       	call   22d0 <putchar@plt>
    2647:	48 8d 3d f0 4b 00 00 	lea    0x4bf0(%rip),%rdi        # 723e <_IO_stdin_used+0x23e>
    264e:	e8 9d fc ff ff       	call   22f0 <puts@plt>
    2653:	ba 06 00 00 00       	mov    $0x6,%edx
    2658:	48 8d 35 fb 4b 00 00 	lea    0x4bfb(%rip),%rsi        # 725a <_IO_stdin_used+0x25a>
    265f:	31 c0                	xor    %eax,%eax
    2661:	bf 01 00 00 00       	mov    $0x1,%edi
    2666:	e8 e5 fd ff ff       	call   2450 <__printf_chk@plt>
    266b:	ba 09 00 00 00       	mov    $0x9,%edx
    2670:	48 8d 35 fd 4b 00 00 	lea    0x4bfd(%rip),%rsi        # 7274 <_IO_stdin_used+0x274>
    2677:	31 c0                	xor    %eax,%eax
    2679:	bf 01 00 00 00       	mov    $0x1,%edi
    267e:	e8 cd fd ff ff       	call   2450 <__printf_chk@plt>
    2683:	ba 01 00 00 00       	mov    $0x1,%edx
    2688:	48 8d 35 f9 4b 00 00 	lea    0x4bf9(%rip),%rsi        # 7288 <_IO_stdin_used+0x288>
    268f:	31 c0                	xor    %eax,%eax
    2691:	bf 01 00 00 00       	mov    $0x1,%edi
    2696:	e8 b5 fd ff ff       	call   2450 <__printf_chk@plt>
    269b:	ba 01 00 00 00       	mov    $0x1,%edx
    26a0:	48 8d 35 f2 4b 00 00 	lea    0x4bf2(%rip),%rsi        # 7299 <_IO_stdin_used+0x299>
    26a7:	31 c0                	xor    %eax,%eax
    26a9:	bf 01 00 00 00       	mov    $0x1,%edi
    26ae:	e8 9d fd ff ff       	call   2450 <__printf_chk@plt>
    26b3:	ba 01 00 00 00       	mov    $0x1,%edx
    26b8:	48 8d 35 f2 4b 00 00 	lea    0x4bf2(%rip),%rsi        # 72b1 <_IO_stdin_used+0x2b1>
    26bf:	31 c0                	xor    %eax,%eax
    26c1:	bf 01 00 00 00       	mov    $0x1,%edi
    26c6:	e8 85 fd ff ff       	call   2450 <__printf_chk@plt>
    26cb:	ba 01 00 00 00       	mov    $0x1,%edx
    26d0:	48 8d 35 41 4e 00 00 	lea    0x4e41(%rip),%rsi        # 7518 <_IO_stdin_used+0x518>
    26d7:	31 c0                	xor    %eax,%eax
    26d9:	bf 01 00 00 00       	mov    $0x1,%edi
    26de:	e8 6d fd ff ff       	call   2450 <__printf_chk@plt>
    26e3:	ba 01 00 00 00       	mov    $0x1,%edx
    26e8:	48 8d 35 59 4e 00 00 	lea    0x4e59(%rip),%rsi        # 7548 <_IO_stdin_used+0x548>
    26ef:	31 c0                	xor    %eax,%eax
    26f1:	bf 01 00 00 00       	mov    $0x1,%edi
    26f6:	e8 55 fd ff ff       	call   2450 <__printf_chk@plt>
    26fb:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2700:	48 8d 35 c6 4b 00 00 	lea    0x4bc6(%rip),%rsi        # 72cd <_IO_stdin_used+0x2cd>
    2707:	31 c0                	xor    %eax,%eax
    2709:	bf 01 00 00 00       	mov    $0x1,%edi
    270e:	e8 3d fd ff ff       	call   2450 <__printf_chk@plt>
    2713:	ba 05 00 00 00       	mov    $0x5,%edx
    2718:	48 8d 35 c8 4b 00 00 	lea    0x4bc8(%rip),%rsi        # 72e7 <_IO_stdin_used+0x2e7>
    271f:	31 c0                	xor    %eax,%eax
    2721:	bf 01 00 00 00       	mov    $0x1,%edi
    2726:	e8 25 fd ff ff       	call   2450 <__printf_chk@plt>
    272b:	48 8d 3d 9c 49 00 00 	lea    0x499c(%rip),%rdi        # 70ce <_IO_stdin_used+0xce>
    2732:	e8 b9 fb ff ff       	call   22f0 <puts@plt>
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    2737:	be 18 00 00 00       	mov    $0x18,%esi
    273c:	bf 06 00 00 00       	mov    $0x6,%edi
    2741:	e8 5a fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2746:	be b0 00 00 00       	mov    $0xb0,%esi
    274b:	bf 09 00 00 00       	mov    $0x9,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    2750:	49 89 c6             	mov    %rax,%r14
    2753:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2758:	e8 43 fc ff ff       	call   23a0 <calloc@plt>
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    275d:	be 10 00 00 00       	mov    $0x10,%esi
    2762:	bf 01 00 00 00       	mov    $0x1,%edi
    2767:	4d 8d 6e e8          	lea    -0x18(%r14),%r13
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    276b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    2770:	45 89 e6             	mov    %r12d,%r14d
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2773:	e8 28 fc ff ff       	call   23a0 <calloc@plt>
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2778:	be 10 00 00 00       	mov    $0x10,%esi
    277d:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    2782:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2788:	48 89 c3             	mov    %rax,%rbx
    278b:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2790:	e8 0b fc ff ff       	call   23a0 <calloc@plt>
    2795:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
  int external_thread_index = 0;
    279a:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27a2:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
    27a6:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
            thread_data[x].tasks[y].run = barriered_work; 
    27ad:	4d 89 d4             	mov    %r10,%r12
    27b0:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    27b5:	4c 89 54 24 60       	mov    %r10,0x60(%rsp)
    27ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    27c0:	43 8d 04 36          	lea    (%r14,%r14,1),%eax
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27c4:	be 08 00 00 00       	mov    $0x8,%esi
    27c9:	bf 02 00 00 00       	mov    $0x2,%edi
    27ce:	45 89 f7             	mov    %r14d,%r15d
    27d1:	44 89 74 24 08       	mov    %r14d,0x8(%rsp)
    27d6:	89 44 24 10          	mov    %eax,0x10(%rsp)
    27da:	e8 c1 fb ff ff       	call   23a0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27df:	be 80 00 00 00       	mov    $0x80,%esi
    27e4:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27e9:	48 89 c3             	mov    %rax,%rbx
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27ec:	e8 af fb ff ff       	call   23a0 <calloc@plt>
    27f1:	48 89 c5             	mov    %rax,%rbp
    if (x % 2 == 1) {
    27f4:	44 89 f0             	mov    %r14d,%eax
    27f7:	41 83 c6 01          	add    $0x1,%r14d
    27fb:	83 e0 01             	and    $0x1,%eax
    27fe:	85 c0                	test   %eax,%eax
    2800:	0f 84 8a 0c 00 00    	je     3490 <main+0xea0>
      my_thread_data[0] = &thread_data[other]; 
    2806:	49 8d 8c 24 50 ff ff ff 	lea    -0xb0(%r12),%rcx
      other = abs(x - 1) % total_threads;
    280e:	44 89 fa             	mov    %r15d,%edx
    2811:	4d 89 e0             	mov    %r12,%r8
    2814:	31 c0                	xor    %eax,%eax
      my_thread_data[0] = &thread_data[other]; 
    2816:	48 89 0b             	mov    %rcx,(%rbx)
    2819:	bf 01 00 00 00       	mov    $0x1,%edi
      other = abs(x - 1) % total_threads;
    281e:	45 8d 7f ff          	lea    -0x1(%r15),%r15d
    2822:	48 8d 35 d2 4a 00 00 	lea    0x4ad2(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
      thread_data[x].thread_index = 1;
    2829:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
      my_thread_data[1] = &thread_data[x]; 
    2831:	4c 89 63 08          	mov    %r12,0x8(%rbx)
    2835:	e8 16 fc ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    283a:	4c 89 e8             	mov    %r13,%rax
    283d:	4d 8d 6d 18          	lea    0x18(%r13),%r13
    2841:	45 8b 04 24          	mov    (%r12),%r8d
    2845:	8b 54 24 08          	mov    0x8(%rsp),%edx
    2849:	49 89 44 24 38       	mov    %rax,0x38(%r12)
    284e:	44 89 f9             	mov    %r15d,%ecx
    2851:	48 8d 35 18 4d 00 00 	lea    0x4d18(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    2858:	bf 01 00 00 00       	mov    $0x1,%edi
    285d:	31 c0                	xor    %eax,%eax
    285f:	e8 ec fb ff ff       	call   2450 <__printf_chk@plt>
    2864:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
    2868:	bf 01 00 00 00       	mov    $0x1,%edi
    286d:	31 c0                	xor    %eax,%eax
    thread_data[x].other = other;
    286f:	45 89 bc 24 a8 00 00 00 	mov    %r15d,0xa8(%r12)
    2877:	44 8b 7c 24 08       	mov    0x8(%rsp),%r15d
    287c:	48 8d 35 1d 4d 00 00 	lea    0x4d1d(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    2883:	44 89 fa             	mov    %r15d,%edx
    2886:	e8 c5 fb ff ff       	call   2450 <__printf_chk@plt>
      CPU_SET(curcpu, sendercpu);
    288b:	0f b6 4c 24 10       	movzbl 0x10(%rsp),%ecx
    2890:	b8 01 00 00 00       	mov    $0x1,%eax
    thread_data[x].threads = my_thread_data;
    2895:	49 89 5c 24 10       	mov    %rbx,0x10(%r12)
    thread_data[x].cpu_set = sendercpu;
    289a:	49 89 ac 24 a0 00 00 00 	mov    %rbp,0xa0(%r12)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28a2:	be 10 00 00 00       	mov    $0x10,%esi
    28a7:	bf 64 00 00 00       	mov    $0x64,%edi
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28ac:	31 db                	xor    %ebx,%ebx
      CPU_SET(curcpu, sendercpu);
    28ae:	48 d3 e0             	shl    %cl,%rax
    28b1:	48 09 45 00          	or     %rax,0x0(%rbp)
    thread_data[x].thread_count = 2;
    28b5:	48 8b 05 84 51 00 00 	mov    0x5184(%rip),%rax        # 7a40 <_IO_stdin_used+0xa40>
    thread_data[x].real_thread_index = x;
    28bc:	45 89 7c 24 04       	mov    %r15d,0x4(%r12)
    thread_data[x].thread_count = 2;
    28c1:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    thread_data[x].task_count = total_barrier_count;
    28c6:	41 c7 44 24 30 03 00 00 00 	movl   $0x3,0x30(%r12)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28cf:	e8 cc fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28d4:	be 10 00 00 00       	mov    $0x10,%esi
    28d9:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28de:	49 89 44 24 58       	mov    %rax,0x58(%r12)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28e3:	e8 b8 fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28e8:	be 28 00 00 00       	mov    $0x28,%esi
    28ed:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    28f2:	66 0f 6f 15 26 51 00 00 	movdqa 0x5126(%rip),%xmm2        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28fa:	49 89 44 24 60       	mov    %rax,0x60(%r12)
    thread_data[x].timestamp_count = 0;
    28ff:	41 0f 11 54 24 70    	movups %xmm2,0x70(%r12)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2905:	e8 96 fa ff ff       	call   23a0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    290a:	be 80 01 00 00       	mov    $0x180,%esi
    290f:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
    2914:	66 0f 6f 1d 04 51 00 00 	movdqa 0x5104(%rip),%xmm3        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    291c:	49 89 84 24 80 00 00 00 	mov    %rax,0x80(%r12)
    thread_data[x].task_timestamp_count = 0;
    2924:	41 0f 11 9c 24 88 00 00 00 	movups %xmm3,0x88(%r12)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    292d:	e8 6e fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    2932:	44 89 74 24 28       	mov    %r14d,0x28(%rsp)
      thread_data[x].tasks = barriers;
    2937:	49 89 44 24 28       	mov    %rax,0x28(%r12)
        thread_data[x].tasks[y].sending = 1;
    293c:	49 89 c6             	mov    %rax,%r14
    293f:	4c 89 6c 24 40       	mov    %r13,0x40(%rsp)
    2944:	4d 89 e5             	mov    %r12,%r13
        thread_data[x].tasks[y].protected = do_protected_write; 
    2947:	4c 63 e3             	movslq %ebx,%r12
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    294a:	be 20 00 00 00       	mov    $0x20,%esi
    294f:	bf 06 00 00 00       	mov    $0x6,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    2954:	4b 8d 2c 64          	lea    (%r12,%r12,2),%rbp
    2958:	48 8d 05 91 0c 00 00 	lea    0xc91(%rip),%rax        # 35f0 <do_protected_write>
    295f:	48 c1 e5 07          	shl    $0x7,%rbp
    2963:	49 01 ee             	add    %rbp,%r14
    2966:	49 89 86 a0 00 00 00 	mov    %rax,0xa0(%r14)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    296d:	e8 2e fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    2972:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    2976:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    297b:	49 89 c7             	mov    %rax,%r15
    297e:	49 89 86 e8 00 00 00 	mov    %rax,0xe8(%r14)
        for (int b = 0 ; b < 2 ; b++) {
    2985:	4c 8d 70 40          	lea    0x40(%rax),%r14
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2989:	be 08 00 00 00       	mov    $0x8,%esi
    298e:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    2993:	49 83 c7 20          	add    $0x20,%r15
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2997:	e8 04 fa ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    299c:	be 08 00 00 00       	mov    $0x8,%esi
    29a1:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29a6:	48 89 c5             	mov    %rax,%rbp
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29a9:	e8 f2 f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29ae:	be 18 00 00 00       	mov    $0x18,%esi
    29b3:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29b8:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29bb:	e8 e0 f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    29c0:	66 0f 6f 05 68 50 00 00 	movdqa 0x5068(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
          mailboxes[b].higher = &data[1];
    29c8:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29cc:	49 89 47 e0          	mov    %rax,-0x20(%r15)
          mailboxes[b].higher = &data[1];
    29d0:	49 89 77 e8          	mov    %rsi,-0x18(%r15)
          data[0].messages = messages;
    29d4:	48 89 28             	mov    %rbp,(%rax)
          data[1].messages = messages2;
    29d7:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    29db:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    29df:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    29e3:	4d 39 f7             	cmp    %r14,%r15
    29e6:	75 a1                	jne    2989 <main+0x399>
        char *message = malloc(sizeof(char) * 256);
    29e8:	be 01 00 00 00       	mov    $0x1,%esi
    29ed:	bf 00 01 00 00       	mov    $0x100,%edi
    29f2:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    29f6:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    29fb:	e8 a0 f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a00:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a05:	49 89 c6             	mov    %rax,%r14
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a08:	44 8d 7b 01          	lea    0x1(%rbx),%r15d
        struct Message *messaged = malloc(sizeof(struct Message));
    2a0c:	e8 ff f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a11:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    2a16:	4c 89 f7             	mov    %r14,%rdi
    2a19:	41 89 d9             	mov    %ebx,%r9d
    2a1c:	ba 00 01 00 00       	mov    $0x100,%edx
    2a21:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2a26:	be 01 00 00 00       	mov    $0x1,%esi
    2a2b:	31 c0                	xor    %eax,%eax
    2a2d:	48 8d 0d 8c 4b 00 00 	lea    0x4b8c(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a34:	e8 e7 fa ff ff       	call   2520 <__sprintf_chk@plt>
        messaged->message = message;
    2a39:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
        messaged->thread_index = thread_data[x].thread_index;
    2a3e:	49 63 45 00          	movslq 0x0(%r13),%rax
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a42:	be 20 00 00 00       	mov    $0x20,%esi
    2a47:	bf 63 00 00 00       	mov    $0x63,%edi
        messaged->message = message;
    2a4c:	4d 89 32             	mov    %r14,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a4f:	4d 8b 75 28          	mov    0x28(%r13),%r14
        messaged->task_index = y;
    2a53:	4d 89 62 10          	mov    %r12,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a57:	4d 8d 24 2e          	lea    (%r14,%rbp,1),%r12
        messaged->thread_index = thread_data[x].thread_index;
    2a5b:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a5f:	45 89 bc 24 08 01 00 00 	mov    %r15d,0x108(%r12)
        thread_data[x].tasks[y].message = messaged;
    2a67:	4d 89 94 24 00 01 00 00 	mov    %r10,0x100(%r12)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a6f:	49 c7 84 24 d0 00 00 00 63 00 00 00 	movq   $0x63,0xd0(%r12)
        messaged->thread_index = thread_data[x].thread_index;
    2a7b:	89 44 24 10          	mov    %eax,0x10(%rsp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a7f:	e8 1c f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a84:	8b 54 24 10          	mov    0x10(%rsp),%edx
        thread_data[x].tasks[y].task_index = y;
    2a88:	41 89 1c 24          	mov    %ebx,(%r12)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a8c:	49 89 84 24 c8 00 00 00 	mov    %rax,0xc8(%r12)
        thread_data[x].tasks[y].available = 1;
    2a94:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2a9e:	49 89 84 24 b8 00 00 00 	mov    %rax,0xb8(%r12)
        thread_data[x].tasks[y].sending = 1;
    2aa6:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2ab0:	49 c7 84 24 d8 00 00 00 00 00 00 00 	movq   $0x0,0xd8(%r12)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2abc:	41 89 94 24 b0 00 00 00 	mov    %edx,0xb0(%r12)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2ac4:	4d 89 ac 24 a8 00 00 00 	mov    %r13,0xa8(%r12)
        thread_data[x].tasks[y].arrived = 0;
    2acc:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
        thread_data[x].tasks[y].thread_count = 2;
    2ad8:	41 c7 84 24 b4 00 00 00 02 00 00 00 	movl   $0x2,0xb4(%r12)
        thread_data[x].tasks[y].sending = 1;
    2ae4:	49 89 84 24 f8 00 00 00 	mov    %rax,0xf8(%r12)
        if (y == barrier_count - 1) {
    2aec:	83 fb 01             	cmp    $0x1,%ebx
    2aef:	0f 84 7b 09 00 00    	je     3470 <main+0xe80>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2af5:	8b 54 24 08          	mov    0x8(%rsp),%edx
    2af9:	39 d3                	cmp    %edx,%ebx
    2afb:	75 63                	jne    2b60 <main+0x570>
    2afd:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    2b01:	85 db                	test   %ebx,%ebx
    2b03:	7f 5b                	jg     2b60 <main+0x570>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2b05:	bf 01 00 00 00       	mov    $0x1,%edi
    2b0a:	48 8d 35 d7 4a 00 00 	lea    0x4ad7(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2b11:	31 c0                	xor    %eax,%eax
    2b13:	e8 38 f9 ff ff       	call   2450 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b18:	48 63 c3             	movslq %ebx,%rax
    2b1b:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b20:	4d 8b 75 28          	mov    0x28(%r13),%r14
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b24:	48 89 c7             	mov    %rax,%rdi
    2b27:	48 c1 e0 04          	shl    $0x4,%rax
    2b2b:	48 01 c8             	add    %rcx,%rax
    2b2e:	49 89 45 40          	mov    %rax,0x40(%r13)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b32:	48 8d 05 37 30 00 00 	lea    0x3037(%rip),%rax        # 5b70 <barriered_work_ingest>
    2b39:	49 89 84 2e 98 00 00 00 	mov    %rax,0x98(%r14,%rbp,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b41:	8d 47 01             	lea    0x1(%rdi),%eax
    2b44:	89 44 24 20          	mov    %eax,0x20(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b48:	41 83 ff 03          	cmp    $0x3,%r15d
    2b4c:	74 27                	je     2b75 <main+0x585>
    2b4e:	bb 01 00 00 00       	mov    $0x1,%ebx
    2b53:	e9 ef fd ff ff       	jmp    2947 <main+0x357>
    2b58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
            thread_data[x].tasks[y].run = barriered_work; 
    2b60:	48 8d 05 f9 2a 00 00 	lea    0x2af9(%rip),%rax        # 5660 <barriered_work>
    2b67:	49 89 84 24 98 00 00 00 	mov    %rax,0x98(%r12)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b6f:	41 83 ff 03          	cmp    $0x3,%r15d
    2b73:	75 d9                	jne    2b4e <main+0x55e>

          }
        }
      }
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b75:	4d 89 f7             	mov    %r14,%r15
    2b78:	4d 89 ec             	mov    %r13,%r12
    2b7b:	44 8b 74 24 28       	mov    0x28(%rsp),%r14d
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b80:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2b8a:	41 c7 87 80 03 00 00 00 00 00 00 	movl   $0x0,0x380(%r15)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b95:	66 0f 6f 64 24 30    	movdqa 0x30(%rsp),%xmm4
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2b9b:	41 c7 87 00 03 00 00 02 00 00 00 	movl   $0x2,0x300(%r15)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2ba6:	4c 8b 6c 24 40       	mov    0x40(%rsp),%r13
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2bab:	49 89 87 b4 03 00 00 	mov    %rax,0x3b4(%r15)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bb2:	41 8b 04 24          	mov    (%r12),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2bb6:	4d 89 a7 a8 03 00 00 	mov    %r12,0x3a8(%r15)
  for (int x = 0 ; x < total_threads ; x++) {
    2bbd:	49 81 c4 b0 00 00 00 	add    $0xb0,%r12
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bc4:	41 89 87 b0 03 00 00 	mov    %eax,0x3b0(%r15)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2bcb:	41 c7 87 fc 03 00 00 06 00 00 00 	movl   $0x6,0x3fc(%r15)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2bd6:	41 c7 87 bc 03 00 00 03 00 00 00 	movl   $0x3,0x3bc(%r15)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2be1:	41 0f 11 a7 98 03 00 00 	movups %xmm4,0x398(%r15)
  for (int x = 0 ; x < total_threads ; x++) {
    2be9:	41 83 fe 09          	cmp    $0x9,%r14d
    2bed:	0f 85 cd fb ff ff    	jne    27c0 <main+0x1d0>
    2bf3:	4c 8b 44 24 60       	mov    0x60(%rsp),%r8
    2bf8:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    2bfd:	31 c0                	xor    %eax,%eax
    2bff:	ba 07 00 00 00       	mov    $0x7,%edx
    2c04:	48 8d 35 0d 47 00 00 	lea    0x470d(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2c0b:	bf 01 00 00 00       	mov    $0x1,%edi
    2c10:	4c 89 44 24 78       	mov    %r8,0x78(%rsp)
    2c15:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2c1a:	e8 31 f8 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c1f:	be 08 00 00 00       	mov    $0x8,%esi
    2c24:	bf 02 00 00 00       	mov    $0x2,%edi
    2c29:	e8 72 f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2c2e:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c33:	bf 09 00 00 00       	mov    $0x9,%edi
    my_thread_data[0] = &thread_data[x]; 
    2c38:	4d 8d b2 d0 04 00 00 	lea    0x4d0(%r10),%r14
    thread_data[n].tasks[0].scheduled = 1;
    2c3f:	4c 89 54 24 40       	mov    %r10,0x40(%rsp)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c44:	4d 8d ba 60 01 00 00 	lea    0x160(%r10),%r15
    thread_data[x].threads = my_thread_data;
    2c4b:	49 89 82 e0 04 00 00 	mov    %rax,0x4e0(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2c52:	49 8d b2 70 03 00 00 	lea    0x370(%r10),%rsi
    2c59:	4d 8d aa b0 00 00 00 	lea    0xb0(%r10),%r13
    my_thread_data[0] = &thread_data[x]; 
    2c60:	4c 89 30             	mov    %r14,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c63:	49 8d 8a c0 02 00 00 	lea    0x2c0(%r10),%rcx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c6a:	4c 89 78 08          	mov    %r15,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c6e:	49 8b 42 28          	mov    0x28(%r10),%rax
    thread_data[x].thread_count = 2;
    2c72:	41 c7 82 e8 04 00 00 02 00 00 00 	movl   $0x2,0x4e8(%r10)
    thread_data[x].thread_index = 0;
    2c7d:	41 c7 82 d0 04 00 00 00 00 00 00 	movl   $0x0,0x4d0(%r10)
    thread_data[x].task_count = total_barrier_count;
    2c88:	41 c7 82 00 05 00 00 03 00 00 00 	movl   $0x3,0x500(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2c93:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2c9d:	49 8b 82 d8 00 00 00 	mov    0xd8(%r10),%rax
    2ca4:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ca9:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2cae:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2cb8:	49 8b 82 88 01 00 00 	mov    0x188(%r10),%rax
    2cbf:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    2cc4:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2cce:	49 8d 82 10 02 00 00 	lea    0x210(%r10),%rax
    2cd5:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2cda:	49 8b 82 38 02 00 00 	mov    0x238(%r10),%rax
    my_thread_data[0] = &thread_data[x]; 
    2ce1:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2ce6:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2cf0:	49 8b 82 e8 02 00 00 	mov    0x2e8(%r10),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2cf7:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2cfc:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
    2d06:	49 8b 82 98 03 00 00 	mov    0x398(%r10),%rax
    2d0d:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    2d12:	c7 80 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d1c:	e8 7f f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d21:	be 38 00 00 00       	mov    $0x38,%esi
    2d26:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d2b:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d2e:	e8 6d f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d33:	be 38 00 00 00       	mov    $0x38,%esi
    2d38:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d3d:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d40:	e8 5b f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d45:	be 38 00 00 00       	mov    $0x38,%esi
    2d4a:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d4f:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d54:	e8 47 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d59:	be 08 00 00 00       	mov    $0x8,%esi
    2d5e:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d63:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d68:	e8 33 f6 ff ff       	call   23a0 <calloc@plt>

  thread_data[thread_count].type = TIMER;
    2d6d:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2d72:	be 08 00 00 00       	mov    $0x8,%esi
    2d77:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d7c:	49 89 c4             	mov    %rax,%r12
  thread_data[thread_count].task_count = total_barrier_count;
    2d7f:	48 8b 05 c2 4c 00 00 	mov    0x4cc2(%rip),%rax        # 7a48 <_IO_stdin_used+0xa48>
  thread_data[thread_count].type = TIMER;
    2d86:	41 c7 82 28 04 00 00 00 00 00 00 	movl   $0x0,0x428(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2d91:	49 89 82 50 04 00 00 	mov    %rax,0x450(%r10)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2d98:	e8 03 f6 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2d9d:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    2da2:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    2da7:	ba 06 00 00 00       	mov    $0x6,%edx
    2dac:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2db1:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2db6:	4c 89 68 08          	mov    %r13,0x8(%rax)
    2dba:	48 89 78 18          	mov    %rdi,0x18(%rax)
    2dbe:	4d 8d aa 20 04 00 00 	lea    0x420(%r10),%r13
    2dc5:	49 8d ba 80 05 00 00 	lea    0x580(%r10),%rdi
    2dcc:	4c 89 10             	mov    %r10,(%rax)
    2dcf:	4c 89 78 10          	mov    %r15,0x10(%rax)
    2dd3:	4c 8d 3d 2e 48 00 00 	lea    0x482e(%rip),%r15        # 7608 <_IO_stdin_used+0x608>
    2dda:	48 89 48 20          	mov    %rcx,0x20(%rax)
    2dde:	48 89 70 28          	mov    %rsi,0x28(%rax)
    2de2:	48 8d 35 3e 45 00 00 	lea    0x453e(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2de9:	4c 89 68 30          	mov    %r13,0x30(%rax)
    2ded:	4c 89 70 38          	mov    %r14,0x38(%rax)
    2df1:	4c 8d 35 a8 08 00 00 	lea    0x8a8(%rip),%r14        # 36a0 <barriered_thread>
    2df8:	48 89 78 40          	mov    %rdi,0x40(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2dfc:	49 89 82 30 04 00 00 	mov    %rax,0x430(%r10)
    2e03:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2e05:	41 c7 82 38 04 00 00 06 00 00 00 	movl   $0x6,0x438(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2e10:	41 c7 82 40 04 00 00 02 00 00 00 	movl   $0x2,0x440(%r10)
  thread_data[thread_count].thread_index = 0;
    2e1b:	41 c7 82 20 04 00 00 00 00 00 00 	movl   $0x0,0x420(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2e26:	48 89 7c 24 40       	mov    %rdi,0x40(%rsp)
    2e2b:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].thread_index = 0;
    2e30:	4c 89 54 24 68       	mov    %r10,0x68(%rsp)
    2e35:	e8 16 f6 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2e3a:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2e41:	4c 89 e9             	mov    %r13,%rcx
    2e44:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
  for (int x = 0 ; x < thread_count ; x++) {
    2e49:	45 31 ed             	xor    %r13d,%r13d
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2e4c:	48 8d 15 8d 0b 00 00 	lea    0xb8d(%rip),%rdx        # 39e0 <timer_thread>
    2e53:	4c 89 e3             	mov    %r12,%rbx
    2e56:	e8 15 f6 ff ff       	call   2470 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2e5b:	4c 89 64 24 70       	mov    %r12,0x70(%rsp)
    2e60:	45 89 ec             	mov    %r13d,%r12d
    2e63:	4c 8b 6c 24 78       	mov    0x78(%rsp),%r13
    2e68:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    thread_data[x].type = WORKER;
    2e70:	41 c7 45 08 01 00 00 00 	movl   $0x1,0x8(%r13)
    2e78:	44 89 e2             	mov    %r12d,%edx
    2e7b:	4c 89 fe             	mov    %r15,%rsi
    2e7e:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2e80:	41 c7 45 34 01 00 00 00 	movl   $0x1,0x34(%r13)
    2e88:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < thread_count ; x++) {
    2e8d:	41 83 c4 01          	add    $0x1,%r12d
    2e91:	e8 ba f5 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2e96:	4c 89 e9             	mov    %r13,%rcx
    2e99:	48 89 ee             	mov    %rbp,%rsi
    2e9c:	48 89 df             	mov    %rbx,%rdi
    2e9f:	4c 89 f2             	mov    %r14,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2ea2:	49 81 c5 b0 00 00 00 	add    $0xb0,%r13
    2ea9:	48 83 c3 08          	add    $0x8,%rbx
    2ead:	48 83 c5 38          	add    $0x38,%rbp
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2eb1:	e8 ba f5 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2eb6:	49 8b 55 f0          	mov    -0x10(%r13),%rdx
    2eba:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    2ebe:	be 08 00 00 00       	mov    $0x8,%esi
    2ec3:	e8 18 f4 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2ec8:	41 83 fc 06          	cmp    $0x6,%r12d
    2ecc:	75 a2                	jne    2e70 <main+0x880>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2ece:	4c 8b 54 24 68       	mov    0x68(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ed3:	be d8 00 00 00       	mov    $0xd8,%esi
    2ed8:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    2edd:	48 8b 1d 6c 4b 00 00 	mov    0x4b6c(%rip),%rbx        # 7a50 <_IO_stdin_used+0xa50>
    thread_data[x].type = IO;
    2ee4:	4c 8b 64 24 70       	mov    0x70(%rsp),%r12
    thread_data[x].task_count = 0;
    2ee9:	49 89 9a 00 05 00 00 	mov    %rbx,0x500(%r10)
    thread_data[x].type = IO;
    2ef0:	41 c7 82 d8 04 00 00 02 00 00 00 	movl   $0x2,0x4d8(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2efb:	e8 a0 f4 ff ff       	call   23a0 <calloc@plt>
    2f00:	4c 8b 54 24 68       	mov    0x68(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f05:	be 00 08 00 00       	mov    $0x800,%esi
    2f0a:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f0c:	49 89 82 18 05 00 00 	mov    %rax,0x518(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f13:	e8 98 f5 ff ff       	call   24b0 <eventfd@plt>
    2f18:	4c 8b 54 24 68       	mov    0x68(%rsp),%r10
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f1d:	be 08 00 00 00       	mov    $0x8,%esi
    2f22:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f27:	41 89 82 20 05 00 00 	mov    %eax,0x520(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f2e:	e8 6d f4 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    2f33:	4c 8b 54 24 68       	mov    0x68(%rsp),%r10
    2f38:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    2f3d:	ba 07 00 00 00       	mov    $0x7,%edx
    2f42:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    2f47:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    2f4c:	48 8d 35 f2 43 00 00 	lea    0x43f2(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    2f53:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    2f58:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    2f5d:	4c 89 10             	mov    %r10,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    2f60:	49 89 82 e0 04 00 00 	mov    %rax,0x4e0(%r10)
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    2f67:	41 c7 82 e8 04 00 00 06 00 00 00 	movl   $0x6,0x4e8(%r10)
    thread_data[x].thread_index = x;
    2f72:	41 c7 82 d0 04 00 00 07 00 00 00 	movl   $0x7,0x4d0(%r10)
      my_thread_data[n] = &thread_data[n]; 
    2f7d:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2f81:	48 89 68 18          	mov    %rbp,0x18(%rax)
    2f85:	4c 89 68 20          	mov    %r13,0x20(%rax)
    2f89:	48 89 78 28          	mov    %rdi,0x28(%rax)
    2f8d:	bf 01 00 00 00       	mov    $0x1,%edi
    2f92:	4c 89 78 10          	mov    %r15,0x10(%rax)
    2f96:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    2f98:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    2f9d:	e8 ae f4 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2fa2:	48 8b 74 24 50       	mov    0x50(%rsp),%rsi
    2fa7:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    2fac:	49 8d 7c 24 38       	lea    0x38(%r12),%rdi
    2fb1:	48 8d 15 e8 1c 00 00 	lea    0x1ce8(%rip),%rdx        # 4ca0 <io_thread>
    2fb8:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2fbf:	e8 ac f4 ff ff       	call   2470 <pthread_create@plt>
    2fc4:	ba 08 00 00 00       	mov    $0x8,%edx
    2fc9:	48 8d 35 8c 43 00 00 	lea    0x438c(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    2fd0:	31 c0                	xor    %eax,%eax
    2fd2:	bf 01 00 00 00       	mov    $0x1,%edi
    2fd7:	e8 74 f4 ff ff       	call   2450 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    2fdc:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    2fe1:	48 8b 44 24 48       	mov    0x48(%rsp),%rax

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2fe6:	be 08 00 00 00       	mov    $0x8,%esi
    2feb:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[x].task_count = 0;
    2ff0:	49 89 9a b0 05 00 00 	mov    %rbx,0x5b0(%r10)
    2ff7:	31 db                	xor    %ebx,%ebx
    thread_data[x].type = EXTERNAL;
    2ff9:	41 c7 82 88 05 00 00 03 00 00 00 	movl   $0x3,0x588(%r10)
    thread_data[x].buffers = &buffers[buffer_index];
    3004:	49 89 82 c0 05 00 00 	mov    %rax,0x5c0(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    300b:	e8 90 f3 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3010:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    3015:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    301a:	48 8d 15 ff 08 00 00 	lea    0x8ff(%rip),%rdx        # 3920 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    3021:	4c 89 70 08          	mov    %r14,0x8(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3025:	48 8b 74 24 60       	mov    0x60(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    302a:	4c 89 10             	mov    %r10,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    302d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
      my_thread_data[n] = &thread_data[n]; 
    3032:	48 89 68 18          	mov    %rbp,0x18(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3036:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    303d:	48 8d 2d 53 43 00 00 	lea    0x4353(%rip),%rbp        # 7397 <_IO_stdin_used+0x397>
      my_thread_data[n] = &thread_data[n]; 
    3044:	4c 89 68 20          	mov    %r13,0x20(%rax)
    3048:	4c 8d ac 24 80 00 00 00 	lea    0x80(%rsp),%r13
    3050:	48 89 78 28          	mov    %rdi,0x28(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3054:	49 8d 7c 24 40       	lea    0x40(%r12),%rdi
    thread_data[x].threads = my_thread_data;
    3059:	49 89 82 90 05 00 00 	mov    %rax,0x590(%r10)
      my_thread_data[n] = &thread_data[n]; 
    3060:	4c 89 78 10          	mov    %r15,0x10(%rax)
    thread_data[x].thread_count = thread_count;
    3064:	48 8b 05 ed 49 00 00 	mov    0x49ed(%rip),%rax        # 7a58 <_IO_stdin_used+0xa58>
    thread_data[x].thread_index = x;
    306b:	41 c7 82 80 05 00 00 08 00 00 00 	movl   $0x8,0x580(%r10)
    thread_data[x].thread_count = thread_count;
    3076:	49 89 82 98 05 00 00 	mov    %rax,0x598(%r10)
    thread_data[x].thread_index = x;
    307d:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3082:	e8 e9 f3 ff ff       	call   2470 <pthread_create@plt>
    3087:	48 8d 3d eb 42 00 00 	lea    0x42eb(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    308e:	e8 5d f2 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3093:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    3098:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    void * result; 
    pthread_join(thread[x], &result);
    30a0:	49 8b 3c dc          	mov    (%r12,%rbx,8),%rdi
    30a4:	4c 89 ee             	mov    %r13,%rsi
    30a7:	e8 44 f4 ff ff       	call   24f0 <pthread_join@plt>
    30ac:	89 da                	mov    %ebx,%edx
    30ae:	48 89 ee             	mov    %rbp,%rsi
    30b1:	bf 01 00 00 00       	mov    $0x1,%edi
    30b6:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    30b8:	48 83 c3 01          	add    $0x1,%rbx
    30bc:	e8 8f f3 ff ff       	call   2450 <__printf_chk@plt>
    30c1:	48 83 fb 09          	cmp    $0x9,%rbx
    30c5:	75 d9                	jne    30a0 <main+0xab0>
    30c7:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    30cc:	4d 89 f2             	mov    %r14,%r10
    30cf:	4d 8d 6e 28          	lea    0x28(%r14),%r13
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    30d3:	31 db                	xor    %ebx,%ebx
  for (int x = 0 ; x < thread_count ; x++) {
    30d5:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
  long sents = 0;
    30dd:	31 ed                	xor    %ebp,%ebp
  long sends = 0;
    30df:	45 31 ff             	xor    %r15d,%r15d
  long ingests = 0;
    30e2:	45 31 c9             	xor    %r9d,%r9d
    30e5:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  long total = 0;
    30ea:	45 31 f6             	xor    %r14d,%r14d
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    30ed:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    30f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    if (x % 2 == 1) {
    30f8:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    30fc:	bf 0a 00 00 00       	mov    $0xa,%edi
    3101:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    3106:	89 c8                	mov    %ecx,%eax
    3108:	41 89 cc             	mov    %ecx,%r12d
      other = (x + 1) % total_threads;
    310b:	83 c1 01             	add    $0x1,%ecx
    if (x % 2 == 1) {
    310e:	83 e0 01             	and    $0x1,%eax
      other = abs(x - 1) % total_threads;
    3111:	41 83 ec 01          	sub    $0x1,%r12d
      other = (x + 1) % total_threads;
    3115:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
      other = abs(x - 1) % total_threads;
    3119:	85 c0                	test   %eax,%eax
    311b:	44 0f 44 e1          	cmove  %ecx,%r12d
    311f:	e8 ac f1 ff ff       	call   22d0 <putchar@plt>
    3124:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3129:	bf 01 00 00 00       	mov    $0x1,%edi
    312e:	48 8d 35 76 42 00 00 	lea    0x4276(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    3135:	48 8b 10             	mov    (%rax),%rdx
    3138:	31 c0                	xor    %eax,%eax
    313a:	e8 11 f3 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    313f:	49 63 55 08          	movslq 0x8(%r13),%rdx
    3143:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3148:	85 d2                	test   %edx,%edx
    314a:	0f 8e a4 03 00 00    	jle    34f4 <main+0xf04>
    3150:	49 8b 45 00          	mov    0x0(%r13),%rax
    3154:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
    long v = 0;
    3158:	31 d2                	xor    %edx,%edx
    315a:	48 c1 e6 07          	shl    $0x7,%rsi
    315e:	48 05 90 00 00 00    	add    $0x90,%rax
    3164:	48 01 c6             	add    %rax,%rsi
    3167:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      v += thread_data[me].tasks[n].v;
    3170:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3173:	48 05 80 01 00 00    	add    $0x180,%rax
    3179:	48 39 f0             	cmp    %rsi,%rax
    317c:	75 f2                	jne    3170 <main+0xb80>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    317e:	4d 63 e4             	movslq %r12d,%r12
    3181:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3186:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    318a:	49 8d 04 44          	lea    (%r12,%rax,2),%rax
    318e:	48 c1 e0 04          	shl    $0x4,%rax
    3192:	48 01 f8             	add    %rdi,%rax
    3195:	48 63 70 30          	movslq 0x30(%rax),%rsi
    3199:	85 f6                	test   %esi,%esi
    319b:	7e 29                	jle    31c6 <main+0xbd6>
      v += thread_data[other].tasks[n].v;
    319d:	48 8b 40 28          	mov    0x28(%rax),%rax
    31a1:	48 8d 34 76          	lea    (%rsi,%rsi,2),%rsi
    31a5:	48 c1 e6 07          	shl    $0x7,%rsi
    31a9:	48 05 90 00 00 00    	add    $0x90,%rax
    31af:	48 01 c6             	add    %rax,%rsi
    31b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    31b8:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    31bb:	48 05 80 01 00 00    	add    $0x180,%rax
    31c1:	48 39 c6             	cmp    %rax,%rsi
    31c4:	75 f2                	jne    31b8 <main+0xbc8>
    31c6:	48 8d 35 f3 41 00 00 	lea    0x41f3(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    31cd:	bf 01 00 00 00       	mov    $0x1,%edi
    31d2:	31 c0                	xor    %eax,%eax
    31d4:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    31d9:	e8 72 f2 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    31de:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    31e3:	bf 01 00 00 00       	mov    $0x1,%edi
    31e8:	48 8b 30             	mov    (%rax),%rsi
    31eb:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    31f5:	48 f7 ee             	imul   %rsi
    31f8:	48 c1 fe 3f          	sar    $0x3f,%rsi
    31fc:	31 c0                	xor    %eax,%eax
    31fe:	48 d1 fa             	sar    %rdx
    3201:	48 29 f2             	sub    %rsi,%rdx
    3204:	48 8d 35 25 44 00 00 	lea    0x4425(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    320b:	e8 40 f2 ff ff       	call   2450 <__printf_chk@plt>
    3210:	bf 0a 00 00 00       	mov    $0xa,%edi
    3215:	e8 b6 f0 ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    321a:	49 63 45 08          	movslq 0x8(%r13),%rax
    321e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3223:	85 c0                	test   %eax,%eax
    3225:	7e 76                	jle    329d <main+0xcad>
    3227:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    322b:	48 8d 34 40          	lea    (%rax,%rax,2),%rsi
    322f:	48 c1 e6 07          	shl    $0x7,%rsi
    3233:	48 8d 97 88 00 00 00 	lea    0x88(%rdi),%rdx
    323a:	48 01 d6             	add    %rdx,%rsi
    323d:	0f 1f 00             	nopl   (%rax)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3240:	48 8b 42 60          	mov    0x60(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    3244:	4c 03 32             	add    (%rdx),%r14
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3247:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
      ingests += thread_data[x].tasks[n].ingest_count;
    324e:	4c 03 8a d8 fe ff ff 	add    -0x128(%rdx),%r9
      sends += thread_data[x].tasks[n].sends;
    3255:	4c 03 ba e8 fe ff ff 	add    -0x118(%rdx),%r15
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    325c:	48 03 68 10          	add    0x10(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3260:	48 03 58 18          	add    0x18(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3264:	48 03 68 30          	add    0x30(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3268:	48 03 58 38          	add    0x38(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    326c:	48 03 68 50          	add    0x50(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3270:	48 03 58 58          	add    0x58(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3274:	48 03 68 70          	add    0x70(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3278:	48 03 58 78          	add    0x78(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    327c:	48 03 a8 90 00 00 00 	add    0x90(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3283:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    328a:	48 03 a8 b0 00 00 00 	add    0xb0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3291:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3298:	48 39 f2             	cmp    %rsi,%rdx
    329b:	75 a3                	jne    3240 <main+0xc50>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    329d:	45 31 e4             	xor    %r12d,%r12d
    32a0:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    32a5:	7e 78                	jle    331f <main+0xd2f>
    32a7:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    32ac:	4c 89 eb             	mov    %r13,%rbx
    32af:	4d 89 e5             	mov    %r12,%r13
    32b2:	4d 89 cc             	mov    %r9,%r12
    32b5:	0f 1f 00             	nopl   (%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    32b8:	48 8b 43 58          	mov    0x58(%rbx),%rax
    32bc:	4b 8d 54 ad 00       	lea    0x0(%r13,%r13,4),%rdx
    32c1:	48 83 ec 08          	sub    $0x8,%rsp
    32c5:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    32ca:	49 83 c5 01          	add    $0x1,%r13
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    32ce:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32d2:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    32dc:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    32e0:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32e4:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    32e7:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    32eb:	4c 2b 01             	sub    (%rcx),%r8
    32ee:	31 c0                	xor    %eax,%eax
    32f0:	8b 49 20             	mov    0x20(%rcx),%ecx
    32f3:	56                   	push   %rsi
    32f4:	48 8d 35 55 43 00 00 	lea    0x4355(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    32fb:	48 c1 ea 12          	shr    $0x12,%rdx
    32ff:	49 89 d1             	mov    %rdx,%r9
    3302:	ba 02 00 00 00       	mov    $0x2,%edx
    3307:	e8 44 f1 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    330c:	58                   	pop    %rax
    330d:	5a                   	pop    %rdx
    330e:	4c 39 6b 68          	cmp    %r13,0x68(%rbx)
    3312:	7f a4                	jg     32b8 <main+0xcc8>
    3314:	49 89 dd             	mov    %rbx,%r13
    3317:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    331c:	4d 89 e1             	mov    %r12,%r9
  for (int x = 0 ; x < thread_count ; x++) {
    331f:	48 83 44 24 10 18    	addq   $0x18,0x10(%rsp)
    3325:	49 81 c5 b0 00 00 00 	add    $0xb0,%r13
    332c:	83 7c 24 08 06       	cmpl   $0x6,0x8(%rsp)
    3331:	0f 85 c1 fd ff ff    	jne    30f8 <main+0xb08>
    3337:	4c 89 f2             	mov    %r14,%rdx
    333a:	bf 01 00 00 00       	mov    $0x1,%edi
    333f:	31 c0                	xor    %eax,%eax
    3341:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    3346:	48 8d 35 80 40 00 00 	lea    0x4080(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    334d:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    3357:	e8 f4 f0 ff ff       	call   2450 <__printf_chk@plt>
    335c:	bf 0a 00 00 00       	mov    $0xa,%edi
    3361:	e8 6a ef ff ff       	call   22d0 <putchar@plt>
    3366:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    336b:	bf 01 00 00 00       	mov    $0x1,%edi
    3370:	48 8d 35 29 43 00 00 	lea    0x4329(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    3377:	48 8b 50 08          	mov    0x8(%rax),%rdx
    337b:	31 c0                	xor    %eax,%eax
    337d:	e8 ce f0 ff ff       	call   2450 <__printf_chk@plt>
    3382:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3387:	bf 01 00 00 00       	mov    $0x1,%edi
    338c:	48 8d 35 35 43 00 00 	lea    0x4335(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    3393:	4c 89 c8             	mov    %r9,%rax
    3396:	49 c1 f9 3f          	sar    $0x3f,%r9
    339a:	49 f7 ec             	imul   %r12
    339d:	31 c0                	xor    %eax,%eax
    339f:	48 d1 fa             	sar    %rdx
    33a2:	4c 29 ca             	sub    %r9,%rdx
    33a5:	e8 a6 f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    33aa:	4c 89 f8             	mov    %r15,%rax
    33ad:	4d 89 fb             	mov    %r15,%r11
    33b0:	bf 01 00 00 00       	mov    $0x1,%edi
    33b5:	49 f7 ec             	imul   %r12
    33b8:	49 c1 fb 3f          	sar    $0x3f,%r11
    33bc:	48 8d 35 35 43 00 00 	lea    0x4335(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    33c3:	31 c0                	xor    %eax,%eax
    33c5:	48 d1 fa             	sar    %rdx
    33c8:	4c 29 da             	sub    %r11,%rdx
    33cb:	e8 80 f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    33d0:	4c 89 f0             	mov    %r14,%rax
    33d3:	4c 89 f1             	mov    %r14,%rcx
    33d6:	bf 01 00 00 00       	mov    $0x1,%edi
    33db:	49 f7 ec             	imul   %r12
    33de:	48 c1 f9 3f          	sar    $0x3f,%rcx
    33e2:	48 8d 35 3f 43 00 00 	lea    0x433f(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    33e9:	31 c0                	xor    %eax,%eax
    33eb:	48 d1 fa             	sar    %rdx
    33ee:	48 29 ca             	sub    %rcx,%rdx
    33f1:	e8 5a f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    33f6:	48 89 e8             	mov    %rbp,%rax
    33f9:	48 c1 fd 3f          	sar    $0x3f,%rbp
    33fd:	48 8d 35 dd 3f 00 00 	lea    0x3fdd(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    3404:	49 f7 ec             	imul   %r12
    3407:	bf 01 00 00 00       	mov    $0x1,%edi
    340c:	31 c0                	xor    %eax,%eax
    340e:	48 d1 fa             	sar    %rdx
    3411:	48 29 ea             	sub    %rbp,%rdx
    3414:	e8 37 f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3419:	48 89 d8             	mov    %rbx,%rax
    341c:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3420:	48 8d 35 cb 3f 00 00 	lea    0x3fcb(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    3427:	49 f7 ec             	imul   %r12
    342a:	bf 01 00 00 00       	mov    $0x1,%edi
    342f:	48 d1 fa             	sar    %rdx
    3432:	48 29 da             	sub    %rbx,%rdx
    3435:	31 c0                	xor    %eax,%eax
    3437:	e8 14 f0 ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    343c:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    3444:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    344d:	0f 85 a8 00 00 00    	jne    34fb <main+0xf0b>
    3453:	48 81 c4 98 00 00 00 	add    $0x98,%rsp
    345a:	31 c0                	xor    %eax,%eax
    345c:	5b                   	pop    %rbx
    345d:	5d                   	pop    %rbp
    345e:	41 5c                	pop    %r12
    3460:	41 5d                	pop    %r13
    3462:	41 5e                	pop    %r14
    3464:	41 5f                	pop    %r15
    3466:	c3                   	ret
    3467:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          thread_data[x].tasks[y].run = barriered_work; 
    3470:	48 8d 05 e9 21 00 00 	lea    0x21e9(%rip),%rax        # 5660 <barriered_work>
    3477:	bb 02 00 00 00       	mov    $0x2,%ebx
    347c:	49 89 84 24 98 00 00 00 	mov    %rax,0x98(%r12)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3484:	e9 be f4 ff ff       	jmp    2947 <main+0x357>
    3489:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      other = (x + 1) % total_threads;
    3490:	45 89 f7             	mov    %r14d,%r15d
      my_thread_data[0] = &thread_data[x]; 
    3493:	4c 89 23             	mov    %r12,(%rbx)
    3496:	4c 89 e1             	mov    %r12,%rcx
    3499:	48 8d 35 69 3e 00 00 	lea    0x3e69(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      other = (x + 1) % total_threads;
    34a0:	4d 69 ff 39 8e e3 38 	imul   $0x38e38e39,%r15,%r15
      thread_data[x].thread_index = 0;
    34a7:	41 c7 04 24 00 00 00 00 	movl   $0x0,(%r12)
    34af:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].protected_state = &protected_state[x];
    34b4:	49 83 c5 18          	add    $0x18,%r13
      other = (x + 1) % total_threads;
    34b8:	49 c1 ef 21          	shr    $0x21,%r15
    34bc:	43 8d 04 ff          	lea    (%r15,%r15,8),%eax
    34c0:	45 89 f7             	mov    %r14d,%r15d
    34c3:	41 29 c7             	sub    %eax,%r15d
      my_thread_data[1] = &thread_data[other]; 
    34c6:	49 63 c7             	movslq %r15d,%rax
    34c9:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    34cd:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    34d1:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    34d6:	8b 54 24 08          	mov    0x8(%rsp),%edx
    34da:	49 c1 e0 04          	shl    $0x4,%r8
    34de:	49 01 c0             	add    %rax,%r8
    34e1:	31 c0                	xor    %eax,%eax
    34e3:	4c 89 43 08          	mov    %r8,0x8(%rbx)
    34e7:	e8 64 ef ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    34ec:	4c 89 e8             	mov    %r13,%rax
    34ef:	e9 4d f3 ff ff       	jmp    2841 <main+0x251>
    long v = 0;
    34f4:	31 d2                	xor    %edx,%edx
    34f6:	e9 83 fc ff ff       	jmp    317e <main+0xb8e>
}
    34fb:	e8 30 ee ff ff       	call   2330 <__stack_chk_fail@plt>

0000000000003500 <_start>:
    3500:	f3 0f 1e fa          	endbr64
    3504:	31 ed                	xor    %ebp,%ebp
    3506:	49 89 d1             	mov    %rdx,%r9
    3509:	5e                   	pop    %rsi
    350a:	48 89 e2             	mov    %rsp,%rdx
    350d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3511:	50                   	push   %rax
    3512:	54                   	push   %rsp
    3513:	45 31 c0             	xor    %r8d,%r8d
    3516:	31 c9                	xor    %ecx,%ecx
    3518:	48 8d 3d d1 f0 ff ff 	lea    -0xf2f(%rip),%rdi        # 25f0 <main>
    351f:	ff 15 b3 6a 00 00    	call   *0x6ab3(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3525:	f4                   	hlt
    3526:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003530 <deregister_tm_clones>:
    3530:	48 8d 3d e9 6a 00 00 	lea    0x6ae9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3537:	48 8d 05 e2 6a 00 00 	lea    0x6ae2(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    353e:	48 39 f8             	cmp    %rdi,%rax
    3541:	74 15                	je     3558 <deregister_tm_clones+0x28>
    3543:	48 8b 05 96 6a 00 00 	mov    0x6a96(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    354a:	48 85 c0             	test   %rax,%rax
    354d:	74 09                	je     3558 <deregister_tm_clones+0x28>
    354f:	ff e0                	jmp    *%rax
    3551:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3558:	c3                   	ret
    3559:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003560 <register_tm_clones>:
    3560:	48 8d 3d b9 6a 00 00 	lea    0x6ab9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3567:	48 8d 35 b2 6a 00 00 	lea    0x6ab2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    356e:	48 29 fe             	sub    %rdi,%rsi
    3571:	48 89 f0             	mov    %rsi,%rax
    3574:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3578:	48 c1 f8 03          	sar    $0x3,%rax
    357c:	48 01 c6             	add    %rax,%rsi
    357f:	48 d1 fe             	sar    %rsi
    3582:	74 14                	je     3598 <register_tm_clones+0x38>
    3584:	48 8b 05 65 6a 00 00 	mov    0x6a65(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    358b:	48 85 c0             	test   %rax,%rax
    358e:	74 08                	je     3598 <register_tm_clones+0x38>
    3590:	ff e0                	jmp    *%rax
    3592:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3598:	c3                   	ret
    3599:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000035a0 <__do_global_dtors_aux>:
    35a0:	f3 0f 1e fa          	endbr64
    35a4:	80 3d 7d 6a 00 00 00 	cmpb   $0x0,0x6a7d(%rip)        # a028 <completed.0>
    35ab:	75 2b                	jne    35d8 <__do_global_dtors_aux+0x38>
    35ad:	55                   	push   %rbp
    35ae:	48 83 3d 42 6a 00 00 00 	cmpq   $0x0,0x6a42(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    35b6:	48 89 e5             	mov    %rsp,%rbp
    35b9:	74 0c                	je     35c7 <__do_global_dtors_aux+0x27>
    35bb:	48 8b 3d 46 6a 00 00 	mov    0x6a46(%rip),%rdi        # a008 <__dso_handle>
    35c2:	e8 e9 ec ff ff       	call   22b0 <__cxa_finalize@plt>
    35c7:	e8 64 ff ff ff       	call   3530 <deregister_tm_clones>
    35cc:	c6 05 55 6a 00 00 01 	movb   $0x1,0x6a55(%rip)        # a028 <completed.0>
    35d3:	5d                   	pop    %rbp
    35d4:	c3                   	ret
    35d5:	0f 1f 00             	nopl   (%rax)
    35d8:	c3                   	ret
    35d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000035e0 <frame_dummy>:
    35e0:	f3 0f 1e fa          	endbr64
    35e4:	e9 77 ff ff ff       	jmp    3560 <register_tm_clones>
    35e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000035f0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    35f0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    35f4:	48 8b 87 a8 00 00 00 	mov    0xa8(%rdi),%rax
    35fb:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    35ff:	48 83 87 90 00 00 00 01 	addq   $0x1,0x90(%rdi)
  if (protected->balance > 0) {
    3607:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    360b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    360f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3616:	48 85 c9             	test   %rcx,%rcx
    3619:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3620:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3624:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3628:	31 c0                	xor    %eax,%eax
    362a:	c3                   	ret
    362b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003630 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3630:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3634:	48 63 87 bc 00 00 00 	movslq 0xbc(%rdi),%rax
    363b:	85 c0                	test   %eax,%eax
    363d:	7e 4f                	jle    368e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    363f:	48 8b 8f a8 00 00 00 	mov    0xa8(%rdi),%rcx
    3646:	48 63 b7 b0 00 00 00 	movslq 0xb0(%rdi),%rsi
    364d:	48 8b 51 10          	mov    0x10(%rcx),%rdx
    3651:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3655:	48 8b 71 28          	mov    0x28(%rcx),%rsi
    3659:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
    365d:	31 c0                	xor    %eax,%eax
    365f:	48 c1 e1 07          	shl    $0x7,%rcx
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3663:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    3667:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3670:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3678:	c7 84 06 b8 00 00 00 01 00 00 00 	movl   $0x1,0xb8(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3683:	48 05 80 01 00 00    	add    $0x180,%rax
    3689:	48 39 c1             	cmp    %rax,%rcx
    368c:	75 e2                	jne    3670 <barriered_reset+0x40>
  asm volatile ("sfence" ::: "memory");
    368e:	0f ae f8             	sfence
}
    3691:	31 c0                	xor    %eax,%eax
    3693:	c3                   	ret
    3694:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    369f:	90                   	nop

00000000000036a0 <barriered_thread>:
void* barriered_thread(void *arg) {
    36a0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    36a4:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    36a8:	0f 85 69 02 00 00    	jne    3917 <barriered_thread+0x277>
void* barriered_thread(void *arg) {
    36ae:	41 54                	push   %r12
  int waiting = 0;
    36b0:	45 31 d2             	xor    %r10d,%r10d
    36b3:	49 89 fc             	mov    %rdi,%r12
void* barriered_thread(void *arg) {
    36b6:	55                   	push   %rbp
    36b7:	53                   	push   %rbx
    if (t >= data->task_count) {
    36b8:	44 8b 47 30          	mov    0x30(%rdi),%r8d
  int t = 0;
    36bc:	31 db                	xor    %ebx,%ebx
    36be:	66 90                	xchg   %ax,%ax
    if (t >= data->task_count) {
    36c0:	44 39 c3             	cmp    %r8d,%ebx
    36c3:	0f 8d 6f 01 00 00    	jge    3838 <barriered_thread+0x198>
    36c9:	48 63 c3             	movslq %ebx,%rax
    36cc:	48 8d 2c 40          	lea    (%rax,%rax,2),%rbp
    36d0:	48 c1 e5 07          	shl    $0x7,%rbp
    36d4:	eb 1d                	jmp    36f3 <barriered_thread+0x53>
    36d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (; t < data->task_count; t++) {
    36e0:	83 c3 01             	add    $0x1,%ebx
    36e3:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    36ea:	44 39 c3             	cmp    %r8d,%ebx
    36ed:	0f 8d 2d 01 00 00    	jge    3820 <barriered_thread+0x180>
      if (data->tasks[t].available == 1) {
    36f3:	49 8b 44 24 28       	mov    0x28(%r12),%rax
    36f8:	48 8d 14 28          	lea    (%rax,%rbp,1),%rdx
    36fc:	83 ba b8 00 00 00 01 	cmpl   $0x1,0xb8(%rdx)
    3703:	75 db                	jne    36e0 <barriered_thread+0x40>
        if (t > 0) {
    3705:	85 db                	test   %ebx,%ebx
    3707:	0f 8e 43 01 00 00    	jle    3850 <barriered_thread+0x1b0>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    370d:	45 8b 4c 24 18       	mov    0x18(%r12),%r9d
          previous = t - 1;
    3712:	8d 4b ff             	lea    -0x1(%rbx),%ecx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3715:	45 85 c9             	test   %r9d,%r9d
    3718:	0f 8e ea 01 00 00    	jle    3908 <barriered_thread+0x268>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    371e:	48 63 c1             	movslq %ecx,%rax
    3721:	8b ba 80 00 00 00    	mov    0x80(%rdx),%edi
    3727:	49 63 d1             	movslq %r9d,%rdx
        int arrived = 0; 
    372a:	45 31 db             	xor    %r11d,%r11d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    372d:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
    3731:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    3736:	48 c1 e1 07          	shl    $0x7,%rcx
    373a:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    373e:	66 90                	xchg   %ax,%ax
    3740:	48 8b 10             	mov    (%rax),%rdx
    3743:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    3747:	3b bc 0a 80 00 00 00 	cmp    0x80(%rdx,%rcx,1),%edi
    374e:	75 04                	jne    3754 <barriered_thread+0xb4>
            arrived++;
    3750:	41 83 c3 01          	add    $0x1,%r11d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3754:	48 83 c0 08          	add    $0x8,%rax
    3758:	48 39 f0             	cmp    %rsi,%rax
    375b:	75 e3                	jne    3740 <barriered_thread+0xa0>
        if (arrived == 0 || arrived == data->thread_count) {
    375d:	45 39 cb             	cmp    %r9d,%r11d
    3760:	74 09                	je     376b <barriered_thread+0xcb>
    3762:	45 85 db             	test   %r11d,%r11d
    3765:	0f 85 b5 00 00 00    	jne    3820 <barriered_thread+0x180>
          if (waiting == 1) {
    376b:	41 83 fa 01          	cmp    $0x1,%r10d
    376f:	0f 84 fb 00 00 00    	je     3870 <barriered_thread+0x1d0>
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    3775:	85 db                	test   %ebx,%ebx
    3777:	75 10                	jne    3789 <barriered_thread+0xe9>
    3779:	49 8b 74 24 70       	mov    0x70(%r12),%rsi
    377e:	49 3b 74 24 78       	cmp    0x78(%r12),%rsi
    3783:	0f 8c 67 01 00 00    	jl     38f0 <barriered_thread+0x250>
    3789:	49 8b 44 24 28       	mov    0x28(%r12),%rax
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    378e:	49 63 0c 24          	movslq (%r12),%rcx
    3792:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
          data->tasks[t].available = 0;
    3797:	48 01 e8             	add    %rbp,%rax
    379a:	c7 80 b8 00 00 00 00 00 00 00 	movl   $0x0,0xb8(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    37a4:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    37a8:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
    37ac:	48 01 ef             	add    %rbp,%rdi
    37af:	ff 90 98 00 00 00    	call   *0x98(%rax)
          data->tasks[t].arrived++;
    37b5:	49 8b 44 24 28       	mov    0x28(%r12),%rax
    37ba:	48 01 e8             	add    %rbp,%rax
    37bd:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    37c4:	41 8b 44 24 30       	mov    0x30(%r12),%eax
          data->iteration_count++;
    37c9:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    37cf:	83 e8 01             	sub    $0x1,%eax
    37d2:	39 d8                	cmp    %ebx,%eax
    37d4:	0f 84 e6 00 00 00    	je     38c0 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    37da:	0f ae f8             	sfence
            data->task_snapshot[data->task_timestamp_count].task = t;
    37dd:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    37e5:	bf 04 00 00 00       	mov    $0x4,%edi
    for (; t < data->task_count; t++) {
    37ea:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
            data->task_snapshot[data->task_timestamp_count].task = t;
    37f1:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    37f5:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    37fd:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3801:	89 5e 20             	mov    %ebx,0x20(%rsi)
    for (; t < data->task_count; t++) {
    3804:	83 c3 01             	add    $0x1,%ebx
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3807:	e8 04 eb ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    380c:	45 8b 44 24 30       	mov    0x30(%r12),%r8d
            waiting = 1;
    3811:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    for (; t < data->task_count; t++) {
    3817:	44 39 c3             	cmp    %r8d,%ebx
    381a:	0f 8c d3 fe ff ff    	jl     36f3 <barriered_thread+0x53>
  while (data->running == 1) {
    3820:	41 8b 44 24 34       	mov    0x34(%r12),%eax
    3825:	83 f8 01             	cmp    $0x1,%eax
    3828:	0f 84 92 fe ff ff    	je     36c0 <barriered_thread+0x20>
}
    382e:	5b                   	pop    %rbx
    382f:	31 c0                	xor    %eax,%eax
    3831:	5d                   	pop    %rbp
    3832:	41 5c                	pop    %r12
    3834:	c3                   	ret
    3835:	0f 1f 00             	nopl   (%rax)
      data->cycles++;
    3838:	49 83 84 24 98 00 00 00 01 	addq   $0x1,0x98(%r12)
    for (; t < data->task_count; t++) {
    3841:	45 85 c0             	test   %r8d,%r8d
    3844:	7e f2                	jle    3838 <barriered_thread+0x198>
    3846:	31 db                	xor    %ebx,%ebx
    3848:	e9 7c fe ff ff       	jmp    36c9 <barriered_thread+0x29>
    384d:	0f 1f 00             	nopl   (%rax)
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3850:	45 8b 4c 24 18       	mov    0x18(%r12),%r9d
          previous = data->task_count - 1;
    3855:	41 8d 48 ff          	lea    -0x1(%r8),%ecx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3859:	45 85 c9             	test   %r9d,%r9d
    385c:	0f 8f bc fe ff ff    	jg     371e <barriered_thread+0x7e>
          if (waiting == 1) {
    3862:	41 83 fa 01          	cmp    $0x1,%r10d
    3866:	0f 85 09 ff ff ff    	jne    3775 <barriered_thread+0xd5>
    386c:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3870:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
    3878:	bf 04 00 00 00       	mov    $0x4,%edi
    387d:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3881:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3889:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    388e:	e8 7d ea ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3893:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
    389b:	48 83 c0 01          	add    $0x1,%rax
    389f:	48 99                	cqto
    38a1:	49 f7 bc 24 90 00 00 00 	idivq  0x90(%r12)
    38a9:	49 89 94 24 88 00 00 00 	mov    %rdx,0x88(%r12)
            waiting = 0; 
    38b1:	e9 bf fe ff ff       	jmp    3775 <barriered_thread+0xd5>
    38b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    38c0:	49 8b 74 24 70       	mov    0x70(%r12),%rsi
    38c5:	49 3b 74 24 78       	cmp    0x78(%r12),%rsi
    38ca:	0f 8d 0a ff ff ff    	jge    37da <barriered_thread+0x13a>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    38d0:	48 c1 e6 04          	shl    $0x4,%rsi
    38d4:	bf 04 00 00 00       	mov    $0x4,%edi
    38d9:	49 03 74 24 60       	add    0x60(%r12),%rsi
    38de:	e8 2d ea ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    38e3:	49 83 44 24 70 01    	addq   $0x1,0x70(%r12)
    38e9:	e9 ec fe ff ff       	jmp    37da <barriered_thread+0x13a>
    38ee:	66 90                	xchg   %ax,%ax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    38f0:	48 c1 e6 04          	shl    $0x4,%rsi
    38f4:	bf 04 00 00 00       	mov    $0x4,%edi
    38f9:	49 03 74 24 58       	add    0x58(%r12),%rsi
    38fe:	e8 0d ea ff ff       	call   2310 <clock_gettime@plt>
    3903:	e9 81 fe ff ff       	jmp    3789 <barriered_thread+0xe9>
          if (waiting == 1) {
    3908:	41 83 fa 01          	cmp    $0x1,%r10d
    390c:	0f 85 7c fe ff ff    	jne    378e <barriered_thread+0xee>
    3912:	e9 59 ff ff ff       	jmp    3870 <barriered_thread+0x1d0>
}
    3917:	31 c0                	xor    %eax,%eax
    3919:	c3                   	ret
    391a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000003920 <external_thread>:
void * external_thread(void *arg) {
    3920:	f3 0f 1e fa          	endbr64
    3924:	41 55                	push   %r13
    3926:	41 54                	push   %r12
    3928:	55                   	push   %rbp
    3929:	53                   	push   %rbx
    392a:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    392e:	66 0f 6f 05 0a 40 00 00 	movdqa 0x400a(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
void * external_thread(void *arg) {
    3936:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    393f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3944:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3946:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
  struct timespec req = {
    394a:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    394e:	75 64                	jne    39b4 <external_thread+0x94>
    3950:	49 89 fd             	mov    %rdi,%r13
    3953:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3958:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    395b:	4c 8d 25 a2 36 00 00 	lea    0x36a2(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    3962:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    nanosleep(&req , &rem);
    3968:	48 89 ee             	mov    %rbp,%rsi
    396b:	48 89 df             	mov    %rbx,%rdi
    396e:	e8 dd e9 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3973:	49 8b 45 40          	mov    0x40(%r13),%rax
    3977:	48 63 10             	movslq (%rax),%rdx
    397a:	85 d2                	test   %edx,%edx
    397c:	7e 2c                	jle    39aa <external_thread+0x8a>
    397e:	48 8b 40 08          	mov    0x8(%rax),%rax
    3982:	48 c1 e2 04          	shl    $0x4,%rdx
    3986:	48 01 c2             	add    %rax,%rdx
    3989:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    3990:	8b 48 08             	mov    0x8(%rax),%ecx
    3993:	85 c9                	test   %ecx,%ecx
    3995:	75 0a                	jne    39a1 <external_thread+0x81>
        data->buffers->buffer[x].data = "Hello world";
    3997:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    399a:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    39a1:	48 83 c0 10          	add    $0x10,%rax
    39a5:	48 39 c2             	cmp    %rax,%rdx
    39a8:	75 e6                	jne    3990 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    39aa:	0f ae f0             	mfence
  while (data->running == 1) {
    39ad:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
    39b2:	74 b4                	je     3968 <external_thread+0x48>
}
    39b4:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    39b9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    39c2:	75 0d                	jne    39d1 <external_thread+0xb1>
    39c4:	48 83 c4 38          	add    $0x38,%rsp
    39c8:	31 c0                	xor    %eax,%eax
    39ca:	5b                   	pop    %rbx
    39cb:	5d                   	pop    %rbp
    39cc:	41 5c                	pop    %r12
    39ce:	41 5d                	pop    %r13
    39d0:	c3                   	ret
    39d1:	e8 5a e9 ff ff       	call   2330 <__stack_chk_fail@plt>
    39d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000039e0 <timer_thread>:
void* timer_thread(void *arg) {
    39e0:	f3 0f 1e fa          	endbr64
    39e4:	41 57                	push   %r15
    39e6:	48 8d 35 23 36 00 00 	lea    0x3623(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    39ed:	49 89 ff             	mov    %rdi,%r15
    39f0:	41 56                	push   %r14
    39f2:	41 55                	push   %r13
    39f4:	41 54                	push   %r12
    39f6:	55                   	push   %rbp
    39f7:	53                   	push   %rbx
    39f8:	48 83 ec 58          	sub    $0x58,%rsp
    39fc:	8b 17                	mov    (%rdi),%edx
    39fe:	bf 01 00 00 00       	mov    $0x1,%edi
    3a03:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3a0c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3a11:	31 c0                	xor    %eax,%eax
    3a13:	e8 38 ea ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3a18:	66 0f 6f 05 20 3f 00 00 	movdqa 0x3f20(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3a20:	ba 88 13 00 00       	mov    $0x1388,%edx
    3a25:	31 c0                	xor    %eax,%eax
    3a27:	48 8d 35 f4 35 00 00 	lea    0x35f4(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3a2e:	bf 01 00 00 00       	mov    $0x1,%edi
    3a33:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3a38:	e8 13 ea ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3a3d:	45 8b 6f 34          	mov    0x34(%r15),%r13d
    3a41:	45 85 ed             	test   %r13d,%r13d
    3a44:	0f 84 a7 00 00 00    	je     3af1 <timer_thread+0x111>
  int n = 0;
    3a4a:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    3a4d:	45 31 ed             	xor    %r13d,%r13d
    3a50:	49 89 e4             	mov    %rsp,%r12
    y++;
    3a53:	31 db                	xor    %ebx,%ebx
    3a55:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    3a5a:	48 89 ef             	mov    %rbp,%rdi
    3a5d:	4c 89 e6             	mov    %r12,%rsi
    n++;
    3a60:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3a64:	e8 e7 e8 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a69:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3a6d:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a71:	85 c0                	test   %eax,%eax
    3a73:	7e 54                	jle    3ac9 <timer_thread+0xe9>
    3a75:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3a79:	4f 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%r8
    3a7e:	49 c1 e0 07          	shl    $0x7,%r8
    3a82:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3a86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3a90:	4c 8b 19             	mov    (%rcx),%r11
    3a93:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a95:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3a99:	99                   	cltd
    3a9a:	41 f7 7b 30          	idivl  0x30(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    3a9e:	49 8b 73 28          	mov    0x28(%r11),%rsi
    3aa2:	48 63 d2             	movslq %edx,%rdx
    3aa5:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
    3aa9:	48 c1 e0 07          	shl    $0x7,%rax
    3aad:	c7 84 06 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rsi,%rax,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3ab8:	42 c7 84 06 c0 00 00 00 00 00 00 00 	movl   $0x0,0xc0(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ac4:	49 39 c9             	cmp    %rcx,%r9
    3ac7:	75 c7                	jne    3a90 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    3ac9:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3acc:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3ad0:	41 8b 57 34          	mov    0x34(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3ad4:	48 8b 00             	mov    (%rax),%rax
    y++;
    3ad7:	39 78 30             	cmp    %edi,0x30(%rax)
    3ada:	0f 4e fb             	cmovle %ebx,%edi
    3add:	4c 63 ef             	movslq %edi,%r13
  while (data->running && n < times) {
    3ae0:	85 d2                	test   %edx,%edx
    3ae2:	74 0d                	je     3af1 <timer_thread+0x111>
    3ae4:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3aeb:	0f 85 69 ff ff ff    	jne    3a5a <timer_thread+0x7a>
    3af1:	48 8d 3d 40 35 00 00 	lea    0x3540(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3af8:	e8 f3 e7 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3afd:	49 63 47 1c          	movslq 0x1c(%r15),%rax
    3b01:	85 c0                	test   %eax,%eax
    3b03:	0f 8e 84 00 00 00    	jle    3b8d <timer_thread+0x1ad>
    for (int y = 0 ; y < data->task_count ; y++) {
    3b09:	41 8b 57 30          	mov    0x30(%r15),%edx
    3b0d:	85 d2                	test   %edx,%edx
    3b0f:	7e 7c                	jle    3b8d <timer_thread+0x1ad>
    3b11:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    3b19:	48 63 c2             	movslq %edx,%rax
      data->threads[x]->tasks[y].sending = 0;
    3b1c:	4d 8b 4f 10          	mov    0x10(%r15),%r9
    3b20:	31 f6                	xor    %esi,%esi
    3b22:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    3b26:	48 c1 e0 07          	shl    $0x7,%rax
    3b2a:	4c 8d 80 f8 00 00 00 	lea    0xf8(%rax),%r8
    3b31:	49 8b 04 31          	mov    (%r9,%rsi,1),%rax
    3b35:	48 8b 78 28          	mov    0x28(%rax),%rdi
    3b39:	4a 8d 14 07          	lea    (%rdi,%r8,1),%rdx
    3b3d:	48 8d 87 f8 00 00 00 	lea    0xf8(%rdi),%rax
    3b44:	49 89 d2             	mov    %rdx,%r10
    3b47:	49 29 c2             	sub    %rax,%r10
    3b4a:	41 81 e2 80 00 00 00 	and    $0x80,%r10d
    3b51:	74 16                	je     3b69 <timer_thread+0x189>
    for (int y = 0 ; y < data->task_count ; y++) {
    3b53:	48 8d 87 78 02 00 00 	lea    0x278(%rdi),%rax
      data->threads[x]->tasks[y].sending = 0;
    3b5a:	c7 87 f8 00 00 00 00 00 00 00 	movl   $0x0,0xf8(%rdi)
    for (int y = 0 ; y < data->task_count ; y++) {
    3b64:	48 39 c2             	cmp    %rax,%rdx
    3b67:	74 1b                	je     3b84 <timer_thread+0x1a4>
      data->threads[x]->tasks[y].sending = 0;
    3b69:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3b6f:	48 05 00 03 00 00    	add    $0x300,%rax
      data->threads[x]->tasks[y].sending = 0;
    3b75:	c7 80 80 fe ff ff 00 00 00 00 	movl   $0x0,-0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3b7f:	48 39 c2             	cmp    %rax,%rdx
    3b82:	75 e5                	jne    3b69 <timer_thread+0x189>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b84:	48 83 c6 08          	add    $0x8,%rsi
    3b88:	48 39 f1             	cmp    %rsi,%rcx
    3b8b:	75 a4                	jne    3b31 <timer_thread+0x151>
  asm volatile ("mfence" ::: "memory");
    3b8d:	0f ae f0             	mfence
  struct timespec drain = {
    3b90:	66 0f 6f 05 b8 3d 00 00 	movdqa 0x3db8(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3b98:	48 8d 2d be 34 00 00 	lea    0x34be(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3b9f:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ba4:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3ba8:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bac:	85 c0                	test   %eax,%eax
    3bae:	7e 50                	jle    3c00 <timer_thread+0x220>
    3bb0:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3bb4:	4d 63 ed             	movslq %r13d,%r13
    3bb7:	4f 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%r8
    3bbc:	49 c1 e0 07          	shl    $0x7,%r8
    3bc0:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3bc4:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3bc8:	48 8b 19             	mov    (%rcx),%rbx
    3bcb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bcd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3bd1:	99                   	cltd
    3bd2:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3bd5:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3bd9:	48 63 c2             	movslq %edx,%rax
    3bdc:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    3be0:	48 c1 e0 07          	shl    $0x7,%rax
    3be4:	c7 84 06 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rsi,%rax,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3bef:	42 c7 84 06 c0 00 00 00 00 00 00 00 	movl   $0x0,0xc0(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bfb:	49 39 c9             	cmp    %rcx,%r9
    3bfe:	75 c8                	jne    3bc8 <timer_thread+0x1e8>
    asm volatile ("mfence" ::: "memory");
    3c00:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3c03:	49 8b 47 10          	mov    0x10(%r15),%rax
    y++;
    3c07:	45 31 ed             	xor    %r13d,%r13d
    if (y >= data->threads[0]->task_count) {
    3c0a:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3c0d:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3c10:	44 0f 4f ef          	cmovg  %edi,%r13d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3c14:	41 8b 7f 20          	mov    0x20(%r15),%edi
    3c18:	85 ff                	test   %edi,%edi
    3c1a:	0f 8e c0 00 00 00    	jle    3ce0 <timer_thread+0x300>
    3c20:	45 31 e4             	xor    %r12d,%r12d
    int all_empty = 1;
    3c23:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3c29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3c30:	4a 8d 1c e5 00 00 00 00 	lea    0x0(,%r12,8),%rbx
            all_empty = 0;
    3c38:	45 31 f6             	xor    %r14d,%r14d
    3c3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3c40:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3c44:	4b 8d 04 76          	lea    (%r14,%r14,2),%rax
    3c48:	48 c1 e0 07          	shl    $0x7,%rax
    3c4c:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3c50:	31 d2                	xor    %edx,%edx
    3c52:	48 8b 80 e8 00 00 00 	mov    0xe8(%rax),%rax
    3c59:	eb 15                	jmp    3c70 <timer_thread+0x290>
    3c5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3c60:	4d 85 c0             	test   %r8,%r8
    3c63:	7f 1f                	jg     3c84 <timer_thread+0x2a4>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3c65:	83 c2 01             	add    $0x1,%edx
    3c68:	48 83 c0 20          	add    $0x20,%rax
    3c6c:	39 fa                	cmp    %edi,%edx
    3c6e:	74 2a                	je     3c9a <timer_thread+0x2ba>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3c70:	48 8b 08             	mov    (%rax),%rcx
    3c73:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3c77:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3c7b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3c7f:	48 85 c9             	test   %rcx,%rcx
    3c82:	7e dc                	jle    3c60 <timer_thread+0x280>
    3c84:	bf 01 00 00 00       	mov    $0x1,%edi
    3c89:	48 89 ee             	mov    %rbp,%rsi
    3c8c:	31 c0                	xor    %eax,%eax
    3c8e:	e8 bd e7 ff ff       	call   2450 <__printf_chk@plt>
            break;
    3c93:	41 8b 7f 20          	mov    0x20(%r15),%edi
            all_empty = 0;
    3c97:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3c9a:	49 83 c6 01          	add    $0x1,%r14
    3c9e:	44 39 f7             	cmp    %r14d,%edi
    3ca1:	7e 0d                	jle    3cb0 <timer_thread+0x2d0>
    3ca3:	49 8b 47 10          	mov    0x10(%r15),%rax
    3ca7:	eb 97                	jmp    3c40 <timer_thread+0x260>
    3ca9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3cb0:	49 83 c4 01          	add    $0x1,%r12
    3cb4:	44 39 e7             	cmp    %r12d,%edi
    3cb7:	7e 0d                	jle    3cc6 <timer_thread+0x2e6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3cb9:	85 ff                	test   %edi,%edi
    3cbb:	7e 09                	jle    3cc6 <timer_thread+0x2e6>
    3cbd:	49 8b 47 10          	mov    0x10(%r15),%rax
    3cc1:	e9 6a ff ff ff       	jmp    3c30 <timer_thread+0x250>
    if (all_empty == 1) {
    3cc6:	41 83 f9 01          	cmp    $0x1,%r9d
    3cca:	74 14                	je     3ce0 <timer_thread+0x300>
      nanosleep(&drain , &drainrem);
    3ccc:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3cd1:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3cd6:	e8 75 e6 ff ff       	call   2350 <nanosleep@plt>
    3cdb:	e9 c4 fe ff ff       	jmp    3ba4 <timer_thread+0x1c4>
    3ce0:	48 8d 3d 6d 33 00 00 	lea    0x336d(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3ce7:	e8 04 e6 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3cec:	41 8b 47 34          	mov    0x34(%r15),%eax
    3cf0:	85 c0                	test   %eax,%eax
    3cf2:	0f 84 e3 00 00 00    	je     3ddb <timer_thread+0x3fb>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3cf8:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3cfc:	85 c9                	test   %ecx,%ecx
    3cfe:	7e 2d                	jle    3d2d <timer_thread+0x34d>
    3d00:	49 8b 47 10          	mov    0x10(%r15),%rax
    3d04:	31 db                	xor    %ebx,%ebx
    3d06:	48 8d 2d 61 33 00 00 	lea    0x3361(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3d0d:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->running = 0;
    3d10:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3d14:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3d18:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3d1f:	0f 84 e3 00 00 00    	je     3e08 <timer_thread+0x428>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d25:	48 83 c3 01          	add    $0x1,%rbx
    3d29:	39 d9                	cmp    %ebx,%ecx
    3d2b:	7f e3                	jg     3d10 <timer_thread+0x330>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d2d:	49 63 47 18          	movslq 0x18(%r15),%rax
    3d31:	85 c0                	test   %eax,%eax
    3d33:	0f 8e 8b 00 00 00    	jle    3dc4 <timer_thread+0x3e4>
      for (int y = 0 ; y < data->task_count ; y++) {
    3d39:	41 8b 57 30          	mov    0x30(%r15),%edx
    3d3d:	85 d2                	test   %edx,%edx
    3d3f:	0f 8e 7f 00 00 00    	jle    3dc4 <timer_thread+0x3e4>
    3d45:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
    3d4d:	48 63 c2             	movslq %edx,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3d50:	4d 8b 57 10          	mov    0x10(%r15),%r10
    3d54:	31 c9                	xor    %ecx,%ecx
    3d56:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    3d5a:	48 c1 e0 07          	shl    $0x7,%rax
    3d5e:	4c 8d 88 c0 00 00 00 	lea    0xc0(%rax),%r9
    3d65:	0f 1f 00             	nopl   (%rax)
    3d68:	49 8b 04 0a          	mov    (%r10,%rcx,1),%rax
    3d6c:	48 8b 70 28          	mov    0x28(%rax),%rsi
    3d70:	4a 8d 14 0e          	lea    (%rsi,%r9,1),%rdx
    3d74:	48 8d 86 c0 00 00 00 	lea    0xc0(%rsi),%rax
    3d7b:	48 89 d7             	mov    %rdx,%rdi
    3d7e:	48 29 c7             	sub    %rax,%rdi
    3d81:	81 e7 80 00 00 00    	and    $0x80,%edi
    3d87:	74 17                	je     3da0 <timer_thread+0x3c0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3d89:	48 8d 86 40 02 00 00 	lea    0x240(%rsi),%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3d90:	c7 86 c0 00 00 00 00 00 00 00 	movl   $0x0,0xc0(%rsi)
      for (int y = 0 ; y < data->task_count ; y++) {
    3d9a:	48 39 d0             	cmp    %rdx,%rax
    3d9d:	74 1c                	je     3dbb <timer_thread+0x3db>
    3d9f:	90                   	nop
        data->threads[x]->tasks[y].scheduled = 0;
    3da0:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3da6:	48 05 00 03 00 00    	add    $0x300,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3dac:	c7 80 80 fe ff ff 00 00 00 00 	movl   $0x0,-0x180(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3db6:	48 39 d0             	cmp    %rdx,%rax
    3db9:	75 e5                	jne    3da0 <timer_thread+0x3c0>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3dbb:	48 83 c1 08          	add    $0x8,%rcx
    3dbf:	4c 39 c1             	cmp    %r8,%rcx
    3dc2:	75 a4                	jne    3d68 <timer_thread+0x388>
    asm volatile ("mfence" ::: "memory");
    3dc4:	0f ae f0             	mfence
    3dc7:	48 8d 3d b2 32 00 00 	lea    0x32b2(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3dce:	e8 1d e5 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3dd3:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
    3ddb:	48 8d 3d a5 32 00 00 	lea    0x32a5(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3de2:	e8 09 e5 ff ff       	call   22f0 <puts@plt>
}
    3de7:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3dec:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3df5:	75 47                	jne    3e3e <timer_thread+0x45e>
    3df7:	48 83 c4 58          	add    $0x58,%rsp
    3dfb:	31 c0                	xor    %eax,%eax
    3dfd:	5b                   	pop    %rbx
    3dfe:	5d                   	pop    %rbp
    3dff:	41 5c                	pop    %r12
    3e01:	41 5d                	pop    %r13
    3e03:	41 5e                	pop    %r14
    3e05:	41 5f                	pop    %r15
    3e07:	c3                   	ret
    3e08:	48 89 ef             	mov    %rbp,%rdi
    3e0b:	e8 e0 e4 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3e10:	49 8b 47 10          	mov    0x10(%r15),%rax
    3e14:	be 01 00 00 00       	mov    $0x1,%esi
    3e19:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3e1d:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3e21:	8b 78 50             	mov    0x50(%rax),%edi
    3e24:	e8 d7 e5 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3e29:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3e2d:	39 d9                	cmp    %ebx,%ecx
    3e2f:	0f 8e f8 fe ff ff    	jle    3d2d <timer_thread+0x34d>
    3e35:	49 8b 47 10          	mov    0x10(%r15),%rax
    3e39:	e9 d2 fe ff ff       	jmp    3d10 <timer_thread+0x330>
}
    3e3e:	e8 ed e4 ff ff       	call   2330 <__stack_chk_fail@plt>
    3e43:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3e4e:	66 90                	xchg   %ax,%ax

0000000000003e50 <strtolower>:
void strtolower(char *str) {
    3e50:	f3 0f 1e fa          	endbr64
    3e54:	55                   	push   %rbp
    3e55:	53                   	push   %rbx
    3e56:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3e5a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3e5e:	84 db                	test   %bl,%bl
    3e60:	74 24                	je     3e86 <strtolower+0x36>
    3e62:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3e65:	e8 a6 e6 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3e6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3e70:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3e73:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3e77:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3e7a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3e7d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3e82:	84 db                	test   %bl,%bl
    3e84:	75 ea                	jne    3e70 <strtolower+0x20>
}
    3e86:	48 83 c4 08          	add    $0x8,%rsp
    3e8a:	5b                   	pop    %rbx
    3e8b:	5d                   	pop    %rbp
    3e8c:	c3                   	ret
    3e8d:	0f 1f 00             	nopl   (%rax)

0000000000003e90 <zh_malloc>:
void *zh_malloc(size_t size) {
    3e90:	f3 0f 1e fa          	endbr64
    3e94:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3e98:	e8 73 e5 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3e9d:	48 85 c0             	test   %rax,%rax
    3ea0:	74 05                	je     3ea7 <zh_malloc+0x17>
}
    3ea2:	48 83 c4 08          	add    $0x8,%rsp
    3ea6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3ea7:	48 8b 0d 72 61 00 00 	mov    0x6172(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    3eae:	ba 28 00 00 00       	mov    $0x28,%edx
    3eb3:	be 01 00 00 00       	mov    $0x1,%esi
    3eb8:	48 8d 3d 49 35 00 00 	lea    0x3549(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    3ebf:	e8 fc e5 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    3ec4:	bf 01 00 00 00       	mov    $0x1,%edi
    3ec9:	e8 d2 e5 ff ff       	call   24a0 <exit@plt>
    3ece:	66 90                	xchg   %ax,%ax

0000000000003ed0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3ed0:	f3 0f 1e fa          	endbr64
    3ed4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    3ed5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3eda:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3edd:	e8 7e e4 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3ee2:	48 85 c0             	test   %rax,%rax
    3ee5:	74 11                	je     3ef8 <get_filename_ext+0x28>
    3ee7:	48 39 c3             	cmp    %rax,%rbx
    3eea:	74 0c                	je     3ef8 <get_filename_ext+0x28>
    return dot + 1;
    3eec:	48 83 c0 01          	add    $0x1,%rax
}
    3ef0:	5b                   	pop    %rbx
    3ef1:	c3                   	ret
    3ef2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    3ef8:	48 8d 05 d0 31 00 00 	lea    0x31d0(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    3eff:	5b                   	pop    %rbx
    3f00:	c3                   	ret
    3f01:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3f0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003f10 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3f10:	f3 0f 1e fa          	endbr64
    3f14:	41 55                	push   %r13
    3f16:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3f19:	48 89 fe             	mov    %rdi,%rsi
    3f1c:	41 54                	push   %r12
    3f1e:	55                   	push   %rbp
    3f1f:	48 89 d5             	mov    %rdx,%rbp
    3f22:	ba 00 04 00 00       	mov    $0x400,%edx
    3f27:	53                   	push   %rbx
    3f28:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3f2f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3f38:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3f40:	31 c0                	xor    %eax,%eax
    3f42:	49 89 e4             	mov    %rsp,%r12
    3f45:	4c 89 e7             	mov    %r12,%rdi
    3f48:	e8 e3 e4 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    3f4d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3f52:	84 db                	test   %bl,%bl
    3f54:	74 24                	je     3f7a <send_headers+0x6a>
        *str = (char)tolower(*str);
    3f56:	e8 b5 e5 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3f5b:	48 8b 08             	mov    (%rax),%rcx
    3f5e:	4c 89 e0             	mov    %r12,%rax
    3f61:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3f68:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3f6b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3f6f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3f72:	48 0f be 18          	movsbq (%rax),%rbx
    3f76:	84 db                	test   %bl,%bl
    3f78:	75 ee                	jne    3f68 <send_headers+0x58>
    void *buf = malloc(size);
    3f7a:	bf 11 00 00 00       	mov    $0x11,%edi
    3f7f:	e8 8c e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3f84:	48 85 c0             	test   %rax,%rax
    3f87:	0f 84 7e 04 00 00    	je     440b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3f8d:	66 0f 6f 05 cb 39 00 00 	movdqa 0x39cb(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    3f95:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    3f99:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3f9e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3fa6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3faa:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3fad:	e8 5e e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3fb2:	48 85 c0             	test   %rax,%rax
    3fb5:	0f 84 50 04 00 00    	je     440b <send_headers+0x4fb>
    3fbb:	66 0f 6f 05 ad 39 00 00 	movdqa 0x39ad(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    3fc3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    3fc7:	4c 89 e7             	mov    %r12,%rdi
    3fca:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3fd4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3fdc:	0f 11 00             	movups %xmm0,(%rax)
    3fdf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3fe3:	be 2e 00 00 00       	mov    $0x2e,%esi
    3fe8:	e8 73 e3 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3fed:	48 85 c0             	test   %rax,%rax
    3ff0:	0f 84 ea 02 00 00    	je     42e0 <send_headers+0x3d0>
    3ff6:	4c 39 e0             	cmp    %r12,%rax
    3ff9:	0f 84 e1 02 00 00    	je     42e0 <send_headers+0x3d0>
    return dot + 1;
    3fff:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4003:	48 8d 3d 93 30 00 00 	lea    0x3093(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    400a:	48 89 de             	mov    %rbx,%rsi
    400d:	e8 9e e3 ff ff       	call   23b0 <strcmp@plt>
    4012:	85 c0                	test   %eax,%eax
    4014:	75 20                	jne    4036 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4016:	66 0f 6f 05 62 39 00 00 	movdqa 0x3962(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    401e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4026:	66 0f 6f 05 62 39 00 00 	movdqa 0x3962(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    402e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4036:	48 89 de             	mov    %rbx,%rsi
    4039:	48 8d 3d 61 30 00 00 	lea    0x3061(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    4040:	e8 6b e3 ff ff       	call   23b0 <strcmp@plt>
    4045:	85 c0                	test   %eax,%eax
    4047:	75 20                	jne    4069 <send_headers+0x159>
    4049:	66 0f 6f 05 2f 39 00 00 	movdqa 0x392f(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4051:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4059:	66 0f 6f 05 2f 39 00 00 	movdqa 0x392f(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    4061:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4069:	48 89 de             	mov    %rbx,%rsi
    406c:	48 8d 3d 33 30 00 00 	lea    0x3033(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    4073:	e8 38 e3 ff ff       	call   23b0 <strcmp@plt>
    4078:	85 c0                	test   %eax,%eax
    407a:	0f 84 10 02 00 00    	je     4290 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4080:	48 89 de             	mov    %rbx,%rsi
    4083:	48 8d 3d 20 30 00 00 	lea    0x3020(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    408a:	e8 21 e3 ff ff       	call   23b0 <strcmp@plt>
    408f:	85 c0                	test   %eax,%eax
    4091:	0f 84 a9 02 00 00    	je     4340 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4097:	48 89 de             	mov    %rbx,%rsi
    409a:	48 8d 3d 0d 30 00 00 	lea    0x300d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    40a1:	e8 0a e3 ff ff       	call   23b0 <strcmp@plt>
    40a6:	85 c0                	test   %eax,%eax
    40a8:	0f 84 6a 02 00 00    	je     4318 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    40ae:	48 89 de             	mov    %rbx,%rsi
    40b1:	48 8d 3d 39 30 00 00 	lea    0x3039(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    40b8:	e8 f3 e2 ff ff       	call   23b0 <strcmp@plt>
    40bd:	85 c0                	test   %eax,%eax
    40bf:	0f 84 2b 02 00 00    	je     42f0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    40c5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    40c8:	0f 84 52 01 00 00    	je     4220 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    40ce:	48 89 de             	mov    %rbx,%rsi
    40d1:	48 8d 3d da 2f 00 00 	lea    0x2fda(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    40d8:	e8 d3 e2 ff ff       	call   23b0 <strcmp@plt>
    40dd:	85 c0                	test   %eax,%eax
    40df:	0f 84 ab 02 00 00    	je     4390 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    40e5:	48 89 de             	mov    %rbx,%rsi
    40e8:	48 8d 3d c7 2f 00 00 	lea    0x2fc7(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    40ef:	e8 bc e2 ff ff       	call   23b0 <strcmp@plt>
    40f4:	85 c0                	test   %eax,%eax
    40f6:	0f 84 6c 02 00 00    	je     4368 <send_headers+0x458>
    slen = strlen(send_buffer);
    40fc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4104:	4c 89 e7             	mov    %r12,%rdi
    4107:	e8 14 e2 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    410c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    410f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4112:	e8 f9 e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4117:	48 85 c0             	test   %rax,%rax
    411a:	0f 84 eb 02 00 00    	je     440b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4120:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4124:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4128:	83 fb 08             	cmp    $0x8,%ebx
    412b:	0f 83 3f 01 00 00    	jae    4270 <send_headers+0x360>
    4131:	f6 c3 04             	test   $0x4,%bl
    4134:	0f 85 7b 02 00 00    	jne    43b5 <send_headers+0x4a5>
    413a:	85 db                	test   %ebx,%ebx
    413c:	74 13                	je     4151 <send_headers+0x241>
    413e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4146:	88 10                	mov    %dl,(%rax)
    4148:	f6 c3 02             	test   $0x2,%bl
    414b:	0f 85 96 02 00 00    	jne    43e7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4151:	4d 89 e8             	mov    %r13,%r8
    4154:	48 8d 0d 5f 2f 00 00 	lea    0x2f5f(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    415b:	4c 89 e7             	mov    %r12,%rdi
    415e:	31 c0                	xor    %eax,%eax
    4160:	ba 00 04 00 00       	mov    $0x400,%edx
    4165:	be 01 00 00 00       	mov    $0x1,%esi
    416a:	e8 b1 e3 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    416f:	4c 89 e7             	mov    %r12,%rdi
    4172:	e8 a9 e1 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4177:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    417a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    417d:	e8 8e e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4182:	48 85 c0             	test   %rax,%rax
    4185:	0f 84 80 02 00 00    	je     440b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    418b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    418f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4193:	83 fb 08             	cmp    $0x8,%ebx
    4196:	0f 83 1c 01 00 00    	jae    42b8 <send_headers+0x3a8>
    419c:	f6 c3 04             	test   $0x4,%bl
    419f:	0f 85 29 02 00 00    	jne    43ce <send_headers+0x4be>
    41a5:	85 db                	test   %ebx,%ebx
    41a7:	74 13                	je     41bc <send_headers+0x2ac>
    41a9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    41b1:	88 10                	mov    %dl,(%rax)
    41b3:	f6 c3 02             	test   $0x2,%bl
    41b6:	0f 85 3d 02 00 00    	jne    43f9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    41bc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    41c1:	bf 02 00 00 00       	mov    $0x2,%edi
    41c6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    41ce:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    41d6:	e8 35 e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    41db:	48 85 c0             	test   %rax,%rax
    41de:	0f 84 27 02 00 00    	je     440b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    41e4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    41ec:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    41f0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    41f8:	66 89 10             	mov    %dx,(%rax)
}
    41fb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4203:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    420c:	0f 85 20 02 00 00    	jne    4432 <send_headers+0x522>
    4212:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4219:	5b                   	pop    %rbx
    421a:	5d                   	pop    %rbp
    421b:	41 5c                	pop    %r12
    421d:	41 5d                	pop    %r13
    421f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4220:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4224:	0f 85 a4 fe ff ff    	jne    40ce <send_headers+0x1be>
    422a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    422e:	0f 85 9a fe ff ff    	jne    40ce <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4234:	66 0f 6f 05 a4 37 00 00 	movdqa 0x37a4(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    423c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4246:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    424e:	66 0f 6f 05 9a 37 00 00 	movdqa 0x379a(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    4256:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    425e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4266:	e9 63 fe ff ff       	jmp    40ce <send_headers+0x1be>
    426b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4270:	89 da                	mov    %ebx,%edx
    4272:	48 89 c7             	mov    %rax,%rdi
    4275:	4c 89 e6             	mov    %r12,%rsi
    4278:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    427d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4282:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4285:	c1 e9 03             	shr    $0x3,%ecx
    4288:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    428b:	e9 c1 fe ff ff       	jmp    4151 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4290:	66 0f 6f 05 e8 36 00 00 	movdqa 0x36e8(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4298:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    42a0:	66 0f 6f 05 f8 36 00 00 	movdqa 0x36f8(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    42a8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    42b0:	e9 cb fd ff ff       	jmp    4080 <send_headers+0x170>
    42b5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    42b8:	89 da                	mov    %ebx,%edx
    42ba:	48 89 c7             	mov    %rax,%rdi
    42bd:	4c 89 e6             	mov    %r12,%rsi
    42c0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    42c5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    42ca:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    42cd:	c1 e9 03             	shr    $0x3,%ecx
    42d0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    42d3:	e9 e4 fe ff ff       	jmp    41bc <send_headers+0x2ac>
    42d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    42e0:	48 8d 1d e8 2d 00 00 	lea    0x2de8(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    42e7:	e9 94 fd ff ff       	jmp    4080 <send_headers+0x170>
    42ec:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    42f0:	66 0f 6f 05 c8 36 00 00 	movdqa 0x36c8(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    42f8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4300:	66 0f 6f 05 c8 36 00 00 	movdqa 0x36c8(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4308:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4310:	e9 b0 fd ff ff       	jmp    40c5 <send_headers+0x1b5>
    4315:	0f 1f 00             	nopl   (%rax)
    4318:	66 0f 6f 05 a0 36 00 00 	movdqa 0x36a0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4320:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4328:	66 0f 6f 05 a0 36 00 00 	movdqa 0x36a0(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4330:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4338:	e9 71 fd ff ff       	jmp    40ae <send_headers+0x19e>
    433d:	0f 1f 00             	nopl   (%rax)
    4340:	66 0f 6f 05 38 36 00 00 	movdqa 0x3638(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4348:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4350:	66 0f 6f 05 58 36 00 00 	movdqa 0x3658(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    4358:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4360:	e9 32 fd ff ff       	jmp    4097 <send_headers+0x187>
    4365:	0f 1f 00             	nopl   (%rax)
    4368:	66 0f 6f 05 50 36 00 00 	movdqa 0x3650(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4370:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4378:	66 0f 6f 05 90 36 00 00 	movdqa 0x3690(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4380:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4388:	e9 6f fd ff ff       	jmp    40fc <send_headers+0x1ec>
    438d:	0f 1f 00             	nopl   (%rax)
    4390:	66 0f 6f 05 28 36 00 00 	movdqa 0x3628(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4398:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    43a0:	66 0f 6f 05 58 36 00 00 	movdqa 0x3658(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    43a8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    43b0:	e9 30 fd ff ff       	jmp    40e5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    43b5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    43bc:	89 db                	mov    %ebx,%ebx
    43be:	89 10                	mov    %edx,(%rax)
    43c0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    43c5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    43c9:	e9 83 fd ff ff       	jmp    4151 <send_headers+0x241>
    43ce:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    43d5:	89 db                	mov    %ebx,%ebx
    43d7:	89 10                	mov    %edx,(%rax)
    43d9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    43de:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    43e2:	e9 d5 fd ff ff       	jmp    41bc <send_headers+0x2ac>
    43e7:	89 db                	mov    %ebx,%ebx
    43e9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    43ef:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    43f4:	e9 58 fd ff ff       	jmp    4151 <send_headers+0x241>
    43f9:	89 db                	mov    %ebx,%ebx
    43fb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4401:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4406:	e9 b1 fd ff ff       	jmp    41bc <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    440b:	48 8b 0d 0e 5c 00 00 	mov    0x5c0e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4412:	ba 28 00 00 00       	mov    $0x28,%edx
    4417:	be 01 00 00 00       	mov    $0x1,%esi
    441c:	48 8d 3d e5 2f 00 00 	lea    0x2fe5(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4423:	e8 98 e0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4428:	bf 01 00 00 00       	mov    $0x1,%edi
    442d:	e8 6e e0 ff ff       	call   24a0 <exit@plt>
}
    4432:	e8 f9 de ff ff       	call   2330 <__stack_chk_fail@plt>
    4437:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004440 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4440:	f3 0f 1e fa          	endbr64
    4444:	41 55                	push   %r13
    4446:	49 89 d5             	mov    %rdx,%r13
    4449:	41 54                	push   %r12
    444b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    444e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4451:	55                   	push   %rbp
    4452:	53                   	push   %rbx
    4453:	48 89 f3             	mov    %rsi,%rbx
    4456:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    445a:	e8 b1 df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    445f:	48 85 c0             	test   %rax,%rax
    4462:	74 6b                	je     44cf <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4464:	4c 89 e7             	mov    %r12,%rdi
    4467:	48 89 c5             	mov    %rax,%rbp
    446a:	31 f6                	xor    %esi,%esi
    446c:	31 c0                	xor    %eax,%eax
    446e:	e8 0d e0 ff ff       	call   2480 <open@plt>
    4473:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4476:	85 c0                	test   %eax,%eax
    4478:	0f 88 d8 e0 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    447e:	48 89 da             	mov    %rbx,%rdx
    4481:	48 89 ee             	mov    %rbp,%rsi
    4484:	89 c7                	mov    %eax,%edi
    4486:	e8 05 df ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    448b:	48 98                	cltq
    448d:	48 39 d8             	cmp    %rbx,%rax
    4490:	7c 1e                	jl     44b0 <copy_file_contents+0x70>
    close(fd);
    4492:	44 89 e7             	mov    %r12d,%edi
    4495:	e8 d6 de ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    449a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    449e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    44a2:	48 83 c4 08          	add    $0x8,%rsp
    44a6:	5b                   	pop    %rbx
    44a7:	5d                   	pop    %rbp
    44a8:	41 5c                	pop    %r12
    44aa:	41 5d                	pop    %r13
    44ac:	c3                   	ret
    44ad:	0f 1f 00             	nopl   (%rax)
    44b0:	48 8b 0d 69 5b 00 00 	mov    0x5b69(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    44b7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    44bc:	be 01 00 00 00       	mov    $0x1,%esi
    44c1:	48 8d 3d 08 2c 00 00 	lea    0x2c08(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    44c8:	e8 f3 df ff ff       	call   24c0 <fwrite@plt>
    44cd:	eb c3                	jmp    4492 <copy_file_contents+0x52>
    44cf:	48 8b 0d 4a 5b 00 00 	mov    0x5b4a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    44d6:	ba 28 00 00 00       	mov    $0x28,%edx
    44db:	be 01 00 00 00       	mov    $0x1,%esi
    44e0:	48 8d 3d 21 2f 00 00 	lea    0x2f21(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    44e7:	e8 d4 df ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    44ec:	bf 01 00 00 00       	mov    $0x1,%edi
    44f1:	e8 aa df ff ff       	call   24a0 <exit@plt>
    44f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004500 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4500:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4504:	8b 46 44             	mov    0x44(%rsi),%eax
    4507:	48 89 fa             	mov    %rdi,%rdx
    450a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    450d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4513:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4516:	48 8b 07             	mov    (%rdi),%rax
    4519:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    451c:	f6 c1 02             	test   $0x2,%cl
    451f:	74 00                	je     4521 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4521:	89 f0                	mov    %esi,%eax
    4523:	44 29 c0             	sub    %r8d,%eax
    4526:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4529:	0f 82 33 e0 ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    452f:	c1 e9 0a             	shr    $0xa,%ecx
    4532:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4536:	8b 47 44             	mov    0x44(%rdi),%eax
    4539:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    453c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    453f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4542:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4545:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4549:	d3 e0                	shl    %cl,%eax
    454b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    454e:	48 c1 e0 06          	shl    $0x6,%rax
    4552:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4556:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    455c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    455f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4563:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4569:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4571:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4575:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4578:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    457f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4587:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    458b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    458f:	e8 ac dd ff ff       	call   2340 <io_uring_submit@plt>
}
    4594:	31 c0                	xor    %eax,%eax
    4596:	48 83 c4 08          	add    $0x8,%rsp
    459a:	c3                   	ret
    459b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000045a0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    45a0:	f3 0f 1e fa          	endbr64
    45a4:	41 55                	push   %r13
    45a6:	41 89 fd             	mov    %edi,%r13d
    45a9:	41 54                	push   %r12
    45ab:	55                   	push   %rbp
    45ac:	53                   	push   %rbx
    45ad:	48 89 f3             	mov    %rsi,%rbx
    45b0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    45b4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    45b7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    45bd:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    45c0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    45c3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    45c5:	f6 c1 02             	test   $0x2,%cl
    45c8:	74 00                	je     45ca <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    45ca:	89 c2                	mov    %eax,%edx
    45cc:	29 f2                	sub    %esi,%edx
    45ce:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    45d1:	0f 82 9b df ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    45d7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    45da:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    45dd:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    45e0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    45e5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    45e8:	23 6b 58             	and    0x58(%rbx),%ebp
    45eb:	d3 e5                	shl    %cl,%ebp
    45ed:	48 c1 e5 06          	shl    $0x6,%rbp
    45f1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    45f5:	e8 16 de ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    45fa:	be 01 00 00 00       	mov    $0x1,%esi
    45ff:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4604:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4607:	e8 94 dd ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    460c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4611:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4615:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4618:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    461d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4622:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    462b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4633:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4637:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    463b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4642:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    464a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    464e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4656:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    465e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4662:	e8 d9 dc ff ff       	call   2340 <io_uring_submit@plt>
}
    4667:	48 83 c4 08          	add    $0x8,%rsp
    466b:	31 c0                	xor    %eax,%eax
    466d:	5b                   	pop    %rbx
    466e:	5d                   	pop    %rbp
    466f:	41 5c                	pop    %r12
    4671:	41 5d                	pop    %r13
    4673:	c3                   	ret
    4674:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    467f:	90                   	nop

0000000000004680 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4680:	f3 0f 1e fa          	endbr64
    4684:	41 56                	push   %r14
    4686:	41 89 f6             	mov    %esi,%r14d
    4689:	41 55                	push   %r13
    468b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    468e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4693:	41 54                	push   %r12
    4695:	55                   	push   %rbp
    4696:	48 89 d5             	mov    %rdx,%rbp
    4699:	53                   	push   %rbx
    void *buf = malloc(size);
    469a:	e8 71 dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    469f:	48 85 c0             	test   %rax,%rax
    46a2:	0f 84 dd 00 00 00    	je     4785 <_send_static_string_content+0x105>
    46a8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    46ab:	4c 89 ef             	mov    %r13,%rdi
    46ae:	e8 6d dc ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    46b3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    46ba:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    46be:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    46c1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    46c4:	e8 47 dd ff ff       	call   2410 <malloc@plt>
    46c9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    46cc:	48 85 c0             	test   %rax,%rax
    46cf:	0f 84 b0 00 00 00    	je     4785 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    46d5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    46d9:	4c 89 e2             	mov    %r12,%rdx
    46dc:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    46df:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    46e3:	e8 f8 dc ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    46e8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    46eb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    46f1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    46f4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    46f8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    46fa:	f6 c1 02             	test   $0x2,%cl
    46fd:	0f 85 7d 00 00 00    	jne    4780 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4703:	89 d0                	mov    %edx,%eax
    4705:	29 f0                	sub    %esi,%eax
    4707:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    470a:	0f 82 6c de ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4710:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4713:	8b 45 44             	mov    0x44(%rbp),%eax
    4716:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4719:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    471c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    471f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4722:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4728:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    472c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    472e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4731:	48 89 ef             	mov    %rbp,%rdi
    4734:	48 c1 e0 06          	shl    $0x6,%rax
    4738:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    473c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    473f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4743:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4749:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4751:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4755:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4758:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    475f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4767:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    476b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    476f:	5b                   	pop    %rbx
    4770:	5d                   	pop    %rbp
    4771:	41 5c                	pop    %r12
    4773:	41 5d                	pop    %r13
    4775:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4777:	e9 c4 db ff ff       	jmp    2340 <io_uring_submit@plt>
    477c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4780:	e9 7e ff ff ff       	jmp    4703 <_send_static_string_content+0x83>
    4785:	48 8b 0d 94 58 00 00 	mov    0x5894(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    478c:	ba 28 00 00 00       	mov    $0x28,%edx
    4791:	be 01 00 00 00       	mov    $0x1,%esi
    4796:	48 8d 3d 6b 2c 00 00 	lea    0x2c6b(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    479d:	e8 1e dd ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    47a2:	bf 01 00 00 00       	mov    $0x1,%edi
    47a7:	e8 f4 dc ff ff       	call   24a0 <exit@plt>
    47ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000047b0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    47b0:	f3 0f 1e fa          	endbr64
    47b4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    47b7:	89 fe                	mov    %edi,%esi
    47b9:	48 8b 3d 58 58 00 00 	mov    0x5858(%rip),%rdi        # a018 <unimplemented_content>
    47c0:	e9 bb fe ff ff       	jmp    4680 <_send_static_string_content>
    47c5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000047d0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    47d0:	f3 0f 1e fa          	endbr64
    47d4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    47d7:	89 fe                	mov    %edi,%esi
    47d9:	48 8b 3d 30 58 00 00 	mov    0x5830(%rip),%rdi        # a010 <http_404_content>
    47e0:	e9 9b fe ff ff       	jmp    4680 <_send_static_string_content>
    47e5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000047f0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    47f0:	f3 0f 1e fa          	endbr64
    47f4:	41 56                	push   %r14
    47f6:	41 55                	push   %r13
    47f8:	49 89 d5             	mov    %rdx,%r13
    47fb:	41 54                	push   %r12
    47fd:	41 89 f4             	mov    %esi,%r12d
    4800:	55                   	push   %rbp
    4801:	48 89 fd             	mov    %rdi,%rbp
    4804:	53                   	push   %rbx
    4805:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    480c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4815:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    481d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    481f:	e8 fc da ff ff       	call   2320 <strlen@plt>
    4824:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4829:	48 89 c3             	mov    %rax,%rbx
    482c:	0f 84 b6 00 00 00    	je     48e8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4832:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4837:	48 89 ee             	mov    %rbp,%rsi
    483a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    483e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4843:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    484b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4853:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    485e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4866:	e8 55 db ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    486b:	48 89 e6             	mov    %rsp,%rsi
    486e:	4c 89 f7             	mov    %r14,%rdi
    4871:	e8 5a db ff ff       	call   23d0 <stat@plt>
    4876:	83 f8 ff             	cmp    $0xffffffff,%eax
    4879:	0f 84 d3 00 00 00    	je     4952 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    487f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4883:	25 00 f0 00 00       	and    $0xf000,%eax
    4888:	3d 00 80 00 00       	cmp    $0x8000,%eax
    488d:	0f 84 f5 00 00 00    	je     4988 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4893:	48 8b 3d 76 57 00 00 	mov    0x5776(%rip),%rdi        # a010 <http_404_content>
    489a:	4c 89 ea             	mov    %r13,%rdx
    489d:	44 89 e6             	mov    %r12d,%esi
    48a0:	e8 db fd ff ff       	call   4680 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    48a5:	4c 89 f2             	mov    %r14,%rdx
    48a8:	bf 01 00 00 00       	mov    $0x1,%edi
    48ad:	31 c0                	xor    %eax,%eax
    48af:	48 8d 35 6a 28 00 00 	lea    0x286a(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    48b6:	e8 95 db ff ff       	call   2450 <__printf_chk@plt>
}
    48bb:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    48c3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    48cc:	0f 85 20 01 00 00    	jne    49f2 <handle_get_method+0x202>
    48d2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    48d9:	5b                   	pop    %rbx
    48da:	5d                   	pop    %rbp
    48db:	41 5c                	pop    %r12
    48dd:	41 5d                	pop    %r13
    48df:	41 5e                	pop    %r14
    48e1:	c3                   	ret
    48e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    48e8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    48ed:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    48f5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    48fa:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    48fd:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4905:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4908:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4910:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    491b:	e8 a0 da ff ff       	call   23c0 <__memcpy_chk@plt>
    4920:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4925:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    492a:	48 8d 35 ba 27 00 00 	lea    0x27ba(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4931:	48 29 d9             	sub    %rbx,%rcx
    4934:	ba 0b 00 00 00       	mov    $0xb,%edx
    4939:	e8 82 da ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    493e:	48 89 e6             	mov    %rsp,%rsi
    4941:	4c 89 f7             	mov    %r14,%rdi
    4944:	e8 87 da ff ff       	call   23d0 <stat@plt>
    4949:	83 f8 ff             	cmp    $0xffffffff,%eax
    494c:	0f 85 2d ff ff ff    	jne    487f <handle_get_method+0x8f>
    4952:	4c 89 f2             	mov    %r14,%rdx
    4955:	48 89 e9             	mov    %rbp,%rcx
    4958:	48 8d 35 97 27 00 00 	lea    0x2797(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    495f:	31 c0                	xor    %eax,%eax
    4961:	bf 01 00 00 00       	mov    $0x1,%edi
    4966:	e8 e5 da ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    496b:	48 8b 3d 9e 56 00 00 	mov    0x569e(%rip),%rdi        # a010 <http_404_content>
    4972:	4c 89 ea             	mov    %r13,%rdx
    4975:	44 89 e6             	mov    %r12d,%esi
    4978:	e8 03 fd ff ff       	call   4680 <_send_static_string_content>
}
    497d:	e9 39 ff ff ff       	jmp    48bb <handle_get_method+0xcb>
    4982:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4988:	bf 70 00 00 00       	mov    $0x70,%edi
    498d:	e8 7e da ff ff       	call   2410 <malloc@plt>
    4992:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4995:	48 85 c0             	test   %rax,%rax
    4998:	74 5d                	je     49f7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    499a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    499e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    49a3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    49a7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    49aa:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    49b1:	e8 5a f5 ff ff       	call   3f10 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    49b6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    49bb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    49bf:	4c 89 f7             	mov    %r14,%rdi
    49c2:	e8 79 fa ff ff       	call   4440 <copy_file_contents>
    49c7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    49cc:	4c 89 f2             	mov    %r14,%rdx
    49cf:	31 c0                	xor    %eax,%eax
    49d1:	48 8d 35 36 27 00 00 	lea    0x2736(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    49d8:	bf 01 00 00 00       	mov    $0x1,%edi
    49dd:	e8 6e da ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    49e2:	4c 89 ee             	mov    %r13,%rsi
    49e5:	48 89 df             	mov    %rbx,%rdi
    49e8:	e8 13 fb ff ff       	call   4500 <add_write_request>
    49ed:	e9 c9 fe ff ff       	jmp    48bb <handle_get_method+0xcb>
}
    49f2:	e8 39 d9 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    49f7:	48 8b 0d 22 56 00 00 	mov    0x5622(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    49fe:	ba 28 00 00 00       	mov    $0x28,%edx
    4a03:	be 01 00 00 00       	mov    $0x1,%esi
    4a08:	48 8d 3d f9 29 00 00 	lea    0x29f9(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4a0f:	e8 ac da ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4a14:	bf 01 00 00 00       	mov    $0x1,%edi
    4a19:	e8 82 da ff ff       	call   24a0 <exit@plt>
    4a1e:	66 90                	xchg   %ax,%ax

0000000000004a20 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4a20:	f3 0f 1e fa          	endbr64
    4a24:	41 57                	push   %r15
    4a26:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4a28:	4c 8d 35 56 26 00 00 	lea    0x2656(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4a2f:	41 55                	push   %r13
    4a31:	49 89 d5             	mov    %rdx,%r13
    4a34:	41 54                	push   %r12
    4a36:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4a39:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4a3c:	55                   	push   %rbp
    4a3d:	53                   	push   %rbx
    4a3e:	48 83 ec 18          	sub    $0x18,%rsp
    4a42:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a4b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4a50:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4a52:	49 89 e7             	mov    %rsp,%r15
    4a55:	4c 89 fa             	mov    %r15,%rdx
    4a58:	e8 23 d9 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4a5d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4a61:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4a64:	84 db                	test   %bl,%bl
    4a66:	74 1d                	je     4a85 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4a68:	e8 a3 da ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4a6d:	48 89 ea             	mov    %rbp,%rdx
    4a70:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4a73:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4a77:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4a7a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    4a7d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4a81:	84 db                	test   %bl,%bl
    4a83:	75 eb                	jne    4a70 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4a85:	4c 89 fa             	mov    %r15,%rdx
    4a88:	4c 89 f6             	mov    %r14,%rsi
    4a8b:	31 ff                	xor    %edi,%edi
    4a8d:	e8 ee d8 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4a92:	48 8d 35 9a 26 00 00 	lea    0x269a(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4a99:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4a9c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    4a9f:	e8 0c d9 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4aa4:	4c 89 ea             	mov    %r13,%rdx
    4aa7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4aaa:	85 c0                	test   %eax,%eax
    4aac:	75 2a                	jne    4ad8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    4aae:	48 89 df             	mov    %rbx,%rdi
    4ab1:	e8 3a fd ff ff       	call   47f0 <handle_get_method>
}
    4ab6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4abb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4ac4:	75 20                	jne    4ae6 <handle_http_method+0xc6>
    4ac6:	48 83 c4 18          	add    $0x18,%rsp
    4aca:	5b                   	pop    %rbx
    4acb:	5d                   	pop    %rbp
    4acc:	41 5c                	pop    %r12
    4ace:	41 5d                	pop    %r13
    4ad0:	41 5e                	pop    %r14
    4ad2:	41 5f                	pop    %r15
    4ad4:	c3                   	ret
    4ad5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4ad8:	48 8b 3d 39 55 00 00 	mov    0x5539(%rip),%rdi        # a018 <unimplemented_content>
    4adf:	e8 9c fb ff ff       	call   4680 <_send_static_string_content>
}
    4ae4:	eb d0                	jmp    4ab6 <handle_http_method+0x96>
    4ae6:	e8 45 d8 ff ff       	call   2330 <__stack_chk_fail@plt>
    4aeb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004af0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4af0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4af4:	85 d2                	test   %edx,%edx
    4af6:	7e 38                	jle    4b30 <get_line+0x40>
    4af8:	48 63 d2             	movslq %edx,%rdx
    4afb:	48 83 c7 01          	add    $0x1,%rdi
    4aff:	48 01 f2             	add    %rsi,%rdx
    4b02:	eb 11                	jmp    4b15 <get_line+0x25>
    4b04:	0f 1f 40 00          	nopl   0x0(%rax)
    4b08:	48 83 c6 01          	add    $0x1,%rsi
    4b0c:	48 83 c7 01          	add    $0x1,%rdi
    4b10:	48 39 d6             	cmp    %rdx,%rsi
    4b13:	74 1b                	je     4b30 <get_line+0x40>
        dest[i] = src[i];
    4b15:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4b19:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4b1b:	3c 0d                	cmp    $0xd,%al
    4b1d:	75 e9                	jne    4b08 <get_line+0x18>
    4b1f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4b22:	75 e4                	jne    4b08 <get_line+0x18>
            dest[i] = '\0';
    4b24:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4b27:	31 c0                	xor    %eax,%eax
    4b29:	c3                   	ret
    4b2a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4b30:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4b35:	c3                   	ret
    4b36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004b40 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4b40:	f3 0f 1e fa          	endbr64
    4b44:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4b4b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4b4f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b58:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4b60:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4b62:	49 89 e2             	mov    %rsp,%r10
    4b65:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4b6d:	4c 89 d0             	mov    %r10,%rax
    4b70:	eb 13                	jmp    4b85 <handle_client_request+0x45>
    4b72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b78:	48 83 c0 01          	add    $0x1,%rax
    4b7c:	48 83 c1 01          	add    $0x1,%rcx
    4b80:	4c 39 c8             	cmp    %r9,%rax
    4b83:	74 4b                	je     4bd0 <handle_client_request+0x90>
        dest[i] = src[i];
    4b85:	44 0f b6 01          	movzbl (%rcx),%r8d
    4b89:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4b8c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4b90:	75 e6                	jne    4b78 <handle_client_request+0x38>
    4b92:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4b96:	75 e0                	jne    4b78 <handle_client_request+0x38>
            dest[i] = '\0';
    4b98:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4b9b:	8b 47 08             	mov    0x8(%rdi),%eax
    4b9e:	48 89 f2             	mov    %rsi,%rdx
    4ba1:	4c 89 d7             	mov    %r10,%rdi
    4ba4:	89 c6                	mov    %eax,%esi
    4ba6:	e8 75 fe ff ff       	call   4a20 <handle_http_method>
}
    4bab:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4bb3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4bbc:	75 39                	jne    4bf7 <handle_client_request+0xb7>
    4bbe:	31 c0                	xor    %eax,%eax
    4bc0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4bc7:	c3                   	ret
    4bc8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4bd0:	48 8b 0d 49 54 00 00 	mov    0x5449(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4bd7:	ba 12 00 00 00       	mov    $0x12,%edx
    4bdc:	be 01 00 00 00       	mov    $0x1,%esi
    4be1:	48 8d 3d 4f 25 00 00 	lea    0x254f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4be8:	e8 d3 d8 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4bed:	bf 01 00 00 00       	mov    $0x1,%edi
    4bf2:	e8 a9 d8 ff ff       	call   24a0 <exit@plt>
}
    4bf7:	e8 34 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
    4bfc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004c00 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4c00:	f3 0f 1e fa          	endbr64
    4c04:	55                   	push   %rbp
    4c05:	53                   	push   %rbx
    4c06:	48 89 cb             	mov    %rcx,%rbx
    4c09:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4c0d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4c10:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4c13:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4c19:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4c1c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4c1f:	f6 c1 02             	test   $0x2,%cl
    4c22:	74 00                	je     4c24 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4c24:	41 89 c0             	mov    %eax,%r8d
    4c27:	45 29 c8             	sub    %r9d,%r8d
    4c2a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4c2e:	0f 82 58 d9 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4c34:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c37:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4c3a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4c3d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4c40:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4c43:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c47:	d3 e5                	shl    %cl,%ebp
    4c49:	48 c1 e5 06          	shl    $0x6,%rbp
    4c4d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4c51:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4c54:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4c59:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4c60:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4c64:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4c68:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4c70:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4c78:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4c7c:	e8 8f d7 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4c81:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4c84:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4c8a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4c8e:	48 83 c4 08          	add    $0x8,%rsp
    4c92:	5b                   	pop    %rbx
    4c93:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4c94:	e9 a7 d6 ff ff       	jmp    2340 <io_uring_submit@plt>
    4c99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004ca0 <io_thread>:
void* io_thread(void *arg) {
    4ca0:	f3 0f 1e fa          	endbr64
    4ca4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4ca6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4ca8:	41 56                	push   %r14
    4caa:	41 55                	push   %r13
    4cac:	41 54                	push   %r12
    4cae:	55                   	push   %rbp
    4caf:	48 89 fd             	mov    %rdi,%rbp
    4cb2:	53                   	push   %rbx
    4cb3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4cba:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4cc3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4ccb:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4ccf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4cd4:	bf 00 01 00 00       	mov    $0x100,%edi
    4cd9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4cdc:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4ce0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4ce5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4cea:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4cef:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4cf4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4cfc:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4d01:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4d09:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4d0e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4d16:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4d1b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4d23:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4d28:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4d30:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4d35:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4d3d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4d45:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4d4d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4d55:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4d5d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4d65:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4d6d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4d75:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4d7d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4d85:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4d8d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4d94:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4d9c:	e8 4f d6 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4da1:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
    4da5:	31 f6                	xor    %esi,%esi
    4da7:	e8 34 d7 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4dac:	31 d2                	xor    %edx,%edx
    4dae:	be 01 00 00 00       	mov    $0x1,%esi
    4db3:	bf 02 00 00 00       	mov    $0x2,%edi
    4db8:	e8 73 d7 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4dbd:	83 f8 ff             	cmp    $0xffffffff,%eax
    4dc0:	0f 84 08 d8 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    4dc6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4dcb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4dd1:	89 c7                	mov    %eax,%edi
    4dd3:	41 89 c4             	mov    %eax,%r12d
    4dd6:	ba 02 00 00 00       	mov    $0x2,%edx
    4ddb:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4de0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4de8:	e8 13 d5 ff ff       	call   2300 <setsockopt@plt>
    4ded:	85 c0                	test   %eax,%eax
    4def:	0f 88 ad d7 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4df5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4dfa:	ba 10 00 00 00       	mov    $0x10,%edx
    4dff:	44 89 e7             	mov    %r12d,%edi
    4e02:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4e0b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4e13:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4e1b:	e8 40 d6 ff ff       	call   2460 <bind@plt>
    4e20:	85 c0                	test   %eax,%eax
    4e22:	0f 88 b2 d7 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4e28:	be 0a 00 00 00       	mov    $0xa,%esi
    4e2d:	44 89 e7             	mov    %r12d,%edi
    4e30:	e8 eb d5 ff ff       	call   2420 <listen@plt>
    4e35:	85 c0                	test   %eax,%eax
    4e37:	0f 88 71 d7 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4e3d:	ba db 18 00 00       	mov    $0x18db,%edx
    4e42:	48 8d 35 33 23 00 00 	lea    0x2333(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4e49:	bf 01 00 00 00       	mov    $0x1,%edi
    4e4e:	31 c0                	xor    %eax,%eax
    4e50:	e8 fb d5 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4e55:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4e5a:	48 89 d9             	mov    %rbx,%rcx
    4e5d:	44 89 e7             	mov    %r12d,%edi
    4e60:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4e65:	48 89 c6             	mov    %rax,%rsi
    4e68:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4e6d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4e72:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4e7a:	e8 81 fd ff ff       	call   4c00 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4e7f:	bf 01 00 00 00       	mov    $0x1,%edi
    4e84:	be 10 00 00 00       	mov    $0x10,%esi
    4e89:	e8 12 d5 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    4e8e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4e93:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4e96:	e8 75 d5 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4e9b:	48 85 c0             	test   %rax,%rax
    4e9e:	0f 84 ae 04 00 00    	je     5352 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    4ea4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4ea8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4eaf:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    4eb6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4ebe:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4ec1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4ec6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4ec8:	f6 c1 02             	test   $0x2,%cl
    4ecb:	0f 85 0f 04 00 00    	jne    52e0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    4ed1:	89 d0                	mov    %edx,%eax
    4ed3:	29 f0                	sub    %esi,%eax
    4ed5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4edc:	0f 82 e2 d6 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4ee2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4ee5:	48 8d 75 50          	lea    0x50(%rbp),%rsi
	sqe->addr3 = 0;
    4ee9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4eed:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ef0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4ef7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4efa:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4f01:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4f08:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4f0a:	8b 55 50             	mov    0x50(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4f0d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4f12:	48 c1 e0 06          	shl    $0x6,%rax
    4f16:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4f1e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4f24:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4f27:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4f2f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4f33:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4f3b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4f43:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4f47:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4f4b:	e8 f0 d3 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4f50:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4f54:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4f59:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4f61:	0f 85 d7 01 00 00    	jne    513e <io_thread+0x49e>
    4f67:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4f6c:	4d 89 ce             	mov    %r9,%r14
    4f6f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4f74:	0f 1f 40 00          	nopl   0x0(%rax)
    4f78:	48 8d 3d 13 22 00 00 	lea    0x2213(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    4f7f:	e8 6c d3 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4f84:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4f8b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4f92:	c1 e9 0b             	shr    $0xb,%ecx
    4f95:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4f98:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4fa0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4fa2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4faa:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4fac:	39 d0                	cmp    %edx,%eax
    4fae:	74 36                	je     4fe6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4fb0:	89 f8                	mov    %edi,%eax
    4fb2:	21 d0                	and    %edx,%eax
    4fb4:	d3 e0                	shl    %cl,%eax
    4fb6:	48 c1 e0 04          	shl    $0x4,%rax
    4fba:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4fc2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4fca:	0f 85 a8 01 00 00    	jne    5178 <io_thread+0x4d8>
    4fd0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4fd4:	0f 85 0e 03 00 00    	jne    52e8 <io_thread+0x648>
			if (cqe->res < 0)
    4fda:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4fdd:	83 c2 01             	add    $0x1,%edx
    4fe0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4fe2:	85 c0                	test   %eax,%eax
    4fe4:	79 b2                	jns    4f98 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    4fe6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    4fef:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4ff0:	45 31 c0             	xor    %r8d,%r8d
    4ff3:	31 d2                	xor    %edx,%edx
    4ff5:	b9 01 00 00 00       	mov    $0x1,%ecx
    4ffa:	4c 89 f6             	mov    %r14,%rsi
    4ffd:	48 89 df             	mov    %rbx,%rdi
    5000:	e8 3b d4 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5005:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5008:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    500d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5011:	0f 84 e1 02 00 00    	je     52f8 <io_thread+0x658>
    5017:	48 8d 3d 9a 21 00 00 	lea    0x219a(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    501e:	e8 cd d2 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5023:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5028:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    502b:	45 85 ff             	test   %r15d,%r15d
    502e:	0f 88 62 d5 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    5034:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5037:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    503b:	85 c0                	test   %eax,%eax
    503d:	0f 88 d5 02 00 00    	js     5318 <io_thread+0x678>
      switch (req->event_type) {
    5043:	41 83 f8 01          	cmp    $0x1,%r8d
    5047:	0f 84 7b 01 00 00    	je     51c8 <io_thread+0x528>
    504d:	41 83 f8 02          	cmp    $0x2,%r8d
    5051:	0f 84 a1 01 00 00    	je     51f8 <io_thread+0x558>
    5057:	45 85 c0             	test   %r8d,%r8d
    505a:	0f 85 50 01 00 00    	jne    51b0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5060:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5065:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    506a:	48 89 d9             	mov    %rbx,%rcx
    506d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5071:	e8 8a fb ff ff       	call   4c00 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5076:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    507b:	48 89 de             	mov    %rbx,%rsi
    507e:	8b 78 08             	mov    0x8(%rax),%edi
    5081:	e8 1a f5 ff ff       	call   45a0 <add_read_request>
              free(req);
    5086:	4c 89 e7             	mov    %r12,%rdi
    5089:	e8 32 d2 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    508e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5093:	48 85 c0             	test   %rax,%rax
    5096:	0f 85 14 01 00 00    	jne    51b0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    509c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    50a3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    50aa:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    50ad:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    50b2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    50b4:	f6 c1 02             	test   $0x2,%cl
    50b7:	74 00                	je     50b9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    50b9:	89 d0                	mov    %edx,%eax
    50bb:	29 f0                	sub    %esi,%eax
    50bd:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    50c4:	0f 82 f0 d4 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    50ca:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    50cd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    50d2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    50d6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50d9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    50e0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50e3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    50ea:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50f1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    50f3:	8b 55 50             	mov    0x50(%rbp),%edx
    50f6:	48 c1 e0 06          	shl    $0x6,%rax
    50fa:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5102:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5108:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    510b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5113:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5117:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    511f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5127:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    512b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    512f:	e8 0c d2 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5134:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    5138:	0f 84 3a fe ff ff    	je     4f78 <io_thread+0x2d8>
    513e:	48 8d 3d ac 20 00 00 	lea    0x20ac(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    5145:	e8 a6 d1 ff ff       	call   22f0 <puts@plt>
}
    514a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5152:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    515b:	0f 85 18 02 00 00    	jne    5379 <io_thread+0x6d9>
    5161:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5168:	31 c0                	xor    %eax,%eax
    516a:	5b                   	pop    %rbx
    516b:	5d                   	pop    %rbp
    516c:	41 5c                	pop    %r12
    516e:	41 5d                	pop    %r13
    5170:	41 5e                	pop    %r14
    5172:	41 5f                	pop    %r15
    5174:	c3                   	ret
    5175:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5178:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    517d:	48 85 c0             	test   %rax,%rax
    5180:	0f 84 6a fe ff ff    	je     4ff0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5186:	48 83 38 01          	cmpq   $0x1,(%rax)
    518a:	0f 84 68 01 00 00    	je     52f8 <io_thread+0x658>
    5190:	48 8d 3d 21 20 00 00 	lea    0x2021(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    5197:	e8 54 d1 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    519c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    51a1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    51a4:	e9 8b fe ff ff       	jmp    5034 <io_thread+0x394>
    51a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    51b0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    51b8:	8b 02                	mov    (%rdx),%eax
    51ba:	83 c0 01             	add    $0x1,%eax
    51bd:	89 02                	mov    %eax,(%rdx)
}
    51bf:	e9 d8 fe ff ff       	jmp    509c <io_thread+0x3fc>
    51c4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    51c8:	85 c0                	test   %eax,%eax
    51ca:	75 74                	jne    5240 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    51cc:	48 8b 0d 4d 4e 00 00 	mov    0x4e4d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    51d3:	ba 0f 00 00 00       	mov    $0xf,%edx
    51d8:	be 01 00 00 00       	mov    $0x1,%esi
    51dd:	48 8d 3d fd 1f 00 00 	lea    0x1ffd(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    51e4:	e8 d7 d2 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    51e9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    51ee:	e9 a0 fe ff ff       	jmp    5093 <io_thread+0x3f3>
    51f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    51f8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    51fd:	45 31 ff             	xor    %r15d,%r15d
    5200:	85 c0                	test   %eax,%eax
    5202:	7e 20                	jle    5224 <io_thread+0x584>
    5204:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5208:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    520b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    520f:	48 c1 e0 04          	shl    $0x4,%rax
    5213:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5218:	e8 a3 d0 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    521d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5222:	7f e4                	jg     5208 <io_thread+0x568>
              close(req->client_socket);
    5224:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5229:	e8 42 d1 ff ff       	call   2370 <close@plt>
              free(req);
    522e:	4c 89 e7             	mov    %r12,%rdi
    5231:	e8 8a d0 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5236:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    523b:	e9 53 fe ff ff       	jmp    5093 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5240:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5245:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    524a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5252:	eb 11                	jmp    5265 <io_thread+0x5c5>
    5254:	0f 1f 40 00          	nopl   0x0(%rax)
    5258:	48 83 c0 01          	add    $0x1,%rax
    525c:	48 83 c2 01          	add    $0x1,%rdx
    5260:	48 39 c6             	cmp    %rax,%rsi
    5263:	74 4b                	je     52b0 <io_thread+0x610>
        dest[i] = src[i];
    5265:	0f b6 0a             	movzbl (%rdx),%ecx
    5268:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    526a:	80 f9 0d             	cmp    $0xd,%cl
    526d:	75 e9                	jne    5258 <io_thread+0x5b8>
    526f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5273:	75 e3                	jne    5258 <io_thread+0x5b8>
            dest[i] = '\0';
    5275:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5278:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    527d:	48 89 da             	mov    %rbx,%rdx
    5280:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5285:	e8 96 f7 ff ff       	call   4a20 <handle_http_method>
              free(req->iov[0].iov_base);
    528a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    528f:	e8 2c d0 ff ff       	call   22c0 <free@plt>
              free(req);
    5294:	4c 89 e7             	mov    %r12,%rdi
    5297:	e8 24 d0 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    529c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    52a1:	e9 ed fd ff ff       	jmp    5093 <io_thread+0x3f3>
    52a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    52b0:	48 8b 0d 69 4d 00 00 	mov    0x4d69(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    52b7:	ba 12 00 00 00       	mov    $0x12,%edx
    52bc:	be 01 00 00 00       	mov    $0x1,%esi
    52c1:	48 8d 3d 6f 1e 00 00 	lea    0x1e6f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    52c8:	e8 f3 d1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    52cd:	bf 01 00 00 00       	mov    $0x1,%edi
    52d2:	e8 c9 d1 ff ff       	call   24a0 <exit@plt>
    52d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    52e0:	e9 ec fb ff ff       	jmp    4ed1 <io_thread+0x231>
    52e5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    52e8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    52ed:	e9 94 fe ff ff       	jmp    5186 <io_thread+0x4e6>
    52f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    52f8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5300:	48 8d 3d 9d 1e 00 00 	lea    0x1e9d(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    5307:	8b 02                	mov    (%rdx),%eax
    5309:	83 c0 01             	add    $0x1,%eax
    530c:	89 02                	mov    %eax,(%rdx)
    530e:	e8 dd cf ff ff       	call   22f0 <puts@plt>
    5313:	e9 26 fe ff ff       	jmp    513e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5318:	f7 d8                	neg    %eax
    531a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    531f:	89 c7                	mov    %eax,%edi
    5321:	e8 da d1 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5326:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    532b:	be 01 00 00 00       	mov    $0x1,%esi
    5330:	48 8b 3d e9 4c 00 00 	mov    0x4ce9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5337:	48 89 c1             	mov    %rax,%rcx
    533a:	48 8d 15 f7 20 00 00 	lea    0x20f7(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    5341:	31 c0                	xor    %eax,%eax
    5343:	e8 88 d1 ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5348:	bf 01 00 00 00       	mov    $0x1,%edi
    534d:	e8 4e d1 ff ff       	call   24a0 <exit@plt>
    5352:	48 8b 0d c7 4c 00 00 	mov    0x4cc7(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5359:	ba 28 00 00 00       	mov    $0x28,%edx
    535e:	be 01 00 00 00       	mov    $0x1,%esi
    5363:	48 8d 3d 9e 20 00 00 	lea    0x209e(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    536a:	e8 51 d1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    536f:	bf 01 00 00 00       	mov    $0x1,%edi
    5374:	e8 27 d1 ff ff       	call   24a0 <exit@plt>
}
    5379:	e8 b2 cf ff ff       	call   2330 <__stack_chk_fail@plt>
    537e:	66 90                	xchg   %ax,%ax

0000000000005380 <sendm>:
int sendm(struct BarrierTask *data) {
    5380:	f3 0f 1e fa          	endbr64
    5384:	41 57                	push   %r15
    5386:	41 56                	push   %r14
    5388:	41 55                	push   %r13
    538a:	41 54                	push   %r12
    538c:	55                   	push   %rbp
    538d:	53                   	push   %rbx
    538e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5392:	83 bf f8 00 00 00 01 	cmpl   $0x1,0xf8(%rdi)
    5399:	0f 85 99 01 00 00    	jne    5538 <sendm+0x1b8>
    539f:	48 8d b7 00 01 00 00 	lea    0x100(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    53a6:	8b 87 b4 00 00 00    	mov    0xb4(%rdi),%eax
    53ac:	48 89 fa             	mov    %rdi,%rdx
    53af:	31 c9                	xor    %ecx,%ecx
    53b1:	48 89 34 24          	mov    %rsi,(%rsp)
    53b5:	48 8d b7 08 01 00 00 	lea    0x108(%rdi),%rsi
    53bc:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    53c1:	85 c0                	test   %eax,%eax
    53c3:	0f 8e ce 00 00 00    	jle    5497 <sendm+0x117>
    53c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    53d0:	39 8a b0 00 00 00    	cmp    %ecx,0xb0(%rdx)
    53d6:	0f 84 af 00 00 00    	je     548b <sendm+0x10b>
        struct Data *them = data->mailboxes[n].higher;
    53dc:	49 89 ca             	mov    %rcx,%r10
    53df:	49 c1 e2 05          	shl    $0x5,%r10
    53e3:	4c 03 92 e8 00 00 00 	add    0xe8(%rdx),%r10
    53ea:	4d 8b 5a 08          	mov    0x8(%r10),%r11
        for (; them->messages_count < min;) {
    53ee:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    53f2:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    53f6:	4c 39 cb             	cmp    %r9,%rbx
    53f9:	0f 8d 83 00 00 00    	jge    5482 <sendm+0x102>
    53ff:	4c 89 cf             	mov    %r9,%rdi
    5402:	48 8b aa 88 00 00 00 	mov    0x88(%rdx),%rbp
    5409:	4d 8b 72 10          	mov    0x10(%r10),%r14
    540d:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    5410:	49 8b 33             	mov    (%r11),%rsi
    5413:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    5417:	48 83 f8 02          	cmp    $0x2,%rax
    541b:	0f 86 ff 00 00 00    	jbe    5520 <sendm+0x1a0>
    5421:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5429:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5431:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    5435:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    5439:	4c 39 2c 24          	cmp    %r13,(%rsp)
    543d:	73 71                	jae    54b0 <sendm+0x130>
    543f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5444:	4d 39 fc             	cmp    %r15,%r12
    5447:	73 67                	jae    54b0 <sendm+0x130>
    5449:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    544d:	49 01 f0             	add    %rsi,%r8
    5450:	48 8b 82 00 01 00 00 	mov    0x100(%rdx),%rax
        for (; them->messages_count < min;) {
    5457:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    545b:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    545f:	49 39 d8             	cmp    %rbx,%r8
    5462:	75 ec                	jne    5450 <sendm+0xd0>
    5464:	0f 1f 40 00          	nopl   0x0(%rax)
    5468:	48 01 fd             	add    %rdi,%rbp
    546b:	4c 01 f7             	add    %r14,%rdi
    546e:	48 89 aa 88 00 00 00 	mov    %rbp,0x88(%rdx)
    5475:	49 89 7a 10          	mov    %rdi,0x10(%r10)
    5479:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    547d:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5482:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5485:	8b 82 b4 00 00 00    	mov    0xb4(%rdx),%eax
    548b:	48 83 c1 01          	add    $0x1,%rcx
    548f:	39 c8                	cmp    %ecx,%eax
    5491:	0f 8f 39 ff ff ff    	jg     53d0 <sendm+0x50>
}
    5497:	48 83 c4 18          	add    $0x18,%rsp
    549b:	31 c0                	xor    %eax,%eax
    549d:	5b                   	pop    %rbx
    549e:	5d                   	pop    %rbp
    549f:	41 5c                	pop    %r12
    54a1:	41 5d                	pop    %r13
    54a3:	41 5e                	pop    %r14
    54a5:	41 5f                	pop    %r15
    54a7:	c3                   	ret
    54a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    54b0:	49 89 fd             	mov    %rdi,%r13
    54b3:	48 8b 82 00 01 00 00 	mov    0x100(%rdx),%rax
    54ba:	4d 89 e0             	mov    %r12,%r8
    54bd:	49 d1 ed             	shr    %r13
    54c0:	49 c1 e5 04          	shl    $0x4,%r13
    54c4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    54c9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    54cd:	41 83 e5 10          	and    $0x10,%r13d
    54d1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    54d5:	74 11                	je     54e8 <sendm+0x168>
          them->messages[them->messages_count++] = data->message; 
    54d7:	49 83 c0 10          	add    $0x10,%r8
    54db:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    54e0:	4d 39 f8             	cmp    %r15,%r8
    54e3:	74 15                	je     54fa <sendm+0x17a>
    54e5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    54e8:	41 0f 11 00          	movups %xmm0,(%r8)
    54ec:	49 83 c0 20          	add    $0x20,%r8
    54f0:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    54f5:	4d 39 f8             	cmp    %r15,%r8
    54f8:	75 ee                	jne    54e8 <sendm+0x168>
    54fa:	49 89 f8             	mov    %rdi,%r8
    54fd:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    5501:	49 01 d8             	add    %rbx,%r8
    5504:	40 f6 c7 01          	test   $0x1,%dil
    5508:	0f 84 5a ff ff ff    	je     5468 <sendm+0xe8>
          them->messages[them->messages_count++] = data->message; 
    550e:	48 8b 82 00 01 00 00 	mov    0x100(%rdx),%rax
    5515:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    5519:	e9 4a ff ff ff       	jmp    5468 <sendm+0xe8>
    551e:	66 90                	xchg   %ax,%ax
    5520:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5528:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5530:	e9 14 ff ff ff       	jmp    5449 <sendm+0xc9>
    5535:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5538:	48 8d 3d c5 1c 00 00 	lea    0x1cc5(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    553f:	e8 ac cd ff ff       	call   22f0 <puts@plt>
    5544:	e9 4e ff ff ff       	jmp    5497 <sendm+0x117>
    5549:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005550 <receive>:
int receive(struct BarrierTask *data) {
    5550:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5554:	8b 87 b4 00 00 00    	mov    0xb4(%rdi),%eax
    555a:	85 c0                	test   %eax,%eax
    555c:	0f 8e f1 00 00 00    	jle    5653 <receive+0x103>
int receive(struct BarrierTask *data) {
    5562:	41 54                	push   %r12
    5564:	48 89 fa             	mov    %rdi,%rdx
    5567:	55                   	push   %rbp
    5568:	31 ed                	xor    %ebp,%ebp
    556a:	53                   	push   %rbx
    556b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5570:	48 89 ee             	mov    %rbp,%rsi
    5573:	48 c1 e6 05          	shl    $0x5,%rsi
    5577:	48 03 b2 e8 00 00 00 	add    0xe8(%rdx),%rsi
    557e:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5581:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    5586:	48 85 ff             	test   %rdi,%rdi
    5589:	0f 8e a1 00 00 00    	jle    5630 <receive+0xe0>
      data->sends++;
    558f:	48 8b 8a f0 00 00 00 	mov    0xf0(%rdx),%rcx
    5596:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    559a:	4c 63 1a             	movslq (%rdx),%r11
    559d:	49 89 c9             	mov    %rcx,%r9
    55a0:	48 8d 41 01          	lea    0x1(%rcx),%rax
    55a4:	49 f7 d9             	neg    %r9
    55a7:	48 01 c7             	add    %rax,%rdi
    55aa:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    55ae:	4c 8b 8a 88 00 00 00 	mov    0x88(%rdx),%r9
      data->mailboxes[n].received++;
    55b5:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    55b9:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    55bc:	49 29 c8             	sub    %rcx,%r8
    55bf:	eb 10                	jmp    55d1 <receive+0x81>
    55c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    55c8:	48 83 c0 01          	add    $0x1,%rax
    55cc:	48 39 c7             	cmp    %rax,%rdi
    55cf:	74 5f                	je     5630 <receive+0xe0>
      data->n++;
    55d1:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    55d5:	48 89 82 f0 00 00 00 	mov    %rax,0xf0(%rdx)
      data->n++;
    55dc:	48 89 8a 88 00 00 00 	mov    %rcx,0x88(%rdx)
      data->mailboxes[n].received++;
    55e3:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    55e7:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    55eb:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    55f0:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    55f4:	75 d2                	jne    55c8 <receive+0x78>
    55f6:	48 63 9a b0 00 00 00 	movslq 0xb0(%rdx),%rbx
    55fd:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5601:	75 c5                	jne    55c8 <receive+0x78>
    5603:	bf 01 00 00 00       	mov    $0x1,%edi
    5608:	b9 01 00 00 00       	mov    $0x1,%ecx
    560d:	ba 01 00 00 00       	mov    $0x1,%edx
    5612:	31 c0                	xor    %eax,%eax
    5614:	48 8d 35 45 1e 00 00 	lea    0x1e45(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    561b:	e8 30 ce ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5620:	bf 01 00 00 00       	mov    $0x1,%edi
    5625:	e8 76 ce ff ff       	call   24a0 <exit@plt>
    562a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5630:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    5639:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    563c:	48 83 c5 01          	add    $0x1,%rbp
    5640:	39 aa b4 00 00 00    	cmp    %ebp,0xb4(%rdx)
    5646:	0f 8f 24 ff ff ff    	jg     5570 <receive+0x20>
}
    564c:	5b                   	pop    %rbx
    564d:	31 c0                	xor    %eax,%eax
    564f:	5d                   	pop    %rbp
    5650:	41 5c                	pop    %r12
    5652:	c3                   	ret
    5653:	31 c0                	xor    %eax,%eax
    5655:	c3                   	ret
    5656:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005660 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5660:	f3 0f 1e fa          	endbr64
    5664:	41 57                	push   %r15
    5666:	41 56                	push   %r14
    5668:	41 55                	push   %r13
    566a:	41 54                	push   %r12
    566c:	55                   	push   %rbp
    566d:	53                   	push   %rbx
    566e:	48 89 fb             	mov    %rdi,%rbx
    5671:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    5675:	8b 07                	mov    (%rdi),%eax
    5677:	39 87 b0 00 00 00    	cmp    %eax,0xb0(%rdi)
    567d:	0f 84 3d 01 00 00    	je     57c0 <barriered_work+0x160>
    receive(data);
    5683:	e8 c8 fe ff ff       	call   5550 <receive>
    while (data->scheduled == 1) {
    5688:	83 bb c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbx)
    568f:	75 1b                	jne    56ac <barriered_work+0x4c>
    5691:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    5698:	48 83 83 88 00 00 00 01 	addq   $0x1,0x88(%rbx)
      asm volatile ("sfence" ::: "memory");
    56a0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    56a3:	83 bb c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbx)
    56aa:	74 ec                	je     5698 <barriered_work+0x38>
  if (data->sending == 1) {
    56ac:	83 bb f8 00 00 00 01 	cmpl   $0x1,0xf8(%rbx)
    56b3:	0f 85 78 02 00 00    	jne    5931 <barriered_work+0x2d1>
      for (int n = 0 ; n < data->thread_count; n++) {
    56b9:	8b 83 b4 00 00 00    	mov    0xb4(%rbx),%eax
    56bf:	85 c0                	test   %eax,%eax
    56c1:	0f 8e 76 02 00 00    	jle    593d <barriered_work+0x2dd>
    56c7:	48 8d 8b 00 01 00 00 	lea    0x100(%rbx),%rcx
    56ce:	31 d2                	xor    %edx,%edx
    56d0:	48 89 0c 24          	mov    %rcx,(%rsp)
    56d4:	48 8d 8b 08 01 00 00 	lea    0x108(%rbx),%rcx
    56db:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    56e0:	39 93 b0 00 00 00    	cmp    %edx,0xb0(%rbx)
    56e6:	0f 84 bf 00 00 00    	je     57ab <barriered_work+0x14b>
        struct Data *them = data->mailboxes[n].higher;
    56ec:	49 89 d1             	mov    %rdx,%r9
    56ef:	49 c1 e1 05          	shl    $0x5,%r9
    56f3:	4c 03 8b e8 00 00 00 	add    0xe8(%rbx),%r9
    56fa:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    56fe:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5702:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5706:	4d 39 c3             	cmp    %r8,%r11
    5709:	0f 8d 93 00 00 00    	jge    57a2 <barriered_work+0x142>
    570f:	4c 89 c6             	mov    %r8,%rsi
    5712:	48 8b ab 88 00 00 00 	mov    0x88(%rbx),%rbp
    5719:	4d 8b 71 10          	mov    0x10(%r9),%r14
    571d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5720:	49 8b 0a             	mov    (%r10),%rcx
    5723:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5727:	48 83 f8 02          	cmp    $0x2,%rax
    572b:	0f 86 97 02 00 00    	jbe    59c8 <barriered_work+0x368>
    5731:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5739:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5741:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5745:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5749:	4c 39 2c 24          	cmp    %r13,(%rsp)
    574d:	0f 83 05 02 00 00    	jae    5958 <barriered_work+0x2f8>
    5753:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5758:	4d 39 fc             	cmp    %r15,%r12
    575b:	0f 83 f7 01 00 00    	jae    5958 <barriered_work+0x2f8>
    5761:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5765:	48 01 cf             	add    %rcx,%rdi
    5768:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5770:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
        for (; them->messages_count < min;) {
    5777:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    577b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    577f:	49 39 fb             	cmp    %rdi,%r11
    5782:	75 ec                	jne    5770 <barriered_work+0x110>
    5784:	0f 1f 40 00          	nopl   0x0(%rax)
    5788:	48 01 f5             	add    %rsi,%rbp
    578b:	4c 01 f6             	add    %r14,%rsi
    578e:	48 89 ab 88 00 00 00 	mov    %rbp,0x88(%rbx)
    5795:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5799:	4d 89 42 08          	mov    %r8,0x8(%r10)
    579d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    57a2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    57a5:	8b 83 b4 00 00 00    	mov    0xb4(%rbx),%eax
    57ab:	48 83 c2 01          	add    $0x1,%rdx
    57af:	39 d0                	cmp    %edx,%eax
    57b1:	0f 8f 29 ff ff ff    	jg     56e0 <barriered_work+0x80>
    57b7:	e9 81 01 00 00       	jmp    593d <barriered_work+0x2dd>
    57bc:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    57c0:	e8 8b fd ff ff       	call   5550 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    57c5:	4c 63 8b b4 00 00 00 	movslq 0xb4(%rbx),%r9
        int t = data->task_index;
    57cc:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    57ce:	45 85 c9             	test   %r9d,%r9d
    57d1:	0f 8e 85 00 00 00    	jle    585c <barriered_work+0x1fc>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    57d7:	48 8b 93 a8 00 00 00 	mov    0xa8(%rbx),%rdx
    57de:	4c 8b 52 10          	mov    0x10(%rdx),%r10
    57e2:	48 63 d0             	movslq %eax,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
    57e5:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    57e8:	4c 8d 1c 52          	lea    (%rdx,%rdx,2),%r11
              int next_task = abs((t + 1) % (data->thread_count));
    57ec:	99                   	cltd
    57ed:	41 f7 f9             	idiv   %r9d
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    57f0:	49 c1 e3 07          	shl    $0x7,%r11
    57f4:	4c 89 d7             	mov    %r10,%rdi
    57f7:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
              int next_task = abs((t + 1) % (data->thread_count));
    57fb:	89 d0                	mov    %edx,%eax
    57fd:	f7 d8                	neg    %eax
    57ff:	0f 48 c2             	cmovs  %edx,%eax
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5802:	45 31 c0             	xor    %r8d,%r8d
    5805:	48 98                	cltq
    5807:	48 8d 2c 40          	lea    (%rax,%rax,2),%rbp
    580b:	48 c1 e5 07          	shl    $0x7,%rbp
    580f:	90                   	nop
int barriered_work(struct BarrierTask *data) {
    5810:	31 c0                	xor    %eax,%eax
    5812:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5818:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    581c:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    5820:	48 8b 8c 2a e8 00 00 00 	mov    0xe8(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5828:	48 8b 17             	mov    (%rdi),%rdx
    582b:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    582f:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5832:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5836:	48 c1 e2 05          	shl    $0x5,%rdx
    583a:	4a 03 94 1e e8 00 00 00 	add    0xe8(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5842:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    5846:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    584a:	49 39 c1             	cmp    %rax,%r9
    584d:	75 c9                	jne    5818 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    584f:	48 83 c7 08          	add    $0x8,%rdi
    5853:	49 83 c0 20          	add    $0x20,%r8
    5857:	49 39 fc             	cmp    %rdi,%r12
    585a:	75 b4                	jne    5810 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    585c:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    585f:	48 8b b3 d8 00 00 00 	mov    0xd8(%rbx),%rsi
    5866:	31 ff                	xor    %edi,%edi
    5868:	48 c1 e6 05          	shl    $0x5,%rsi
    586c:	48 03 b3 c8 00 00 00 	add    0xc8(%rbx),%rsi
    5873:	e8 98 ca ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5878:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    while (data->scheduled == 1) {
    587f:	83 bb c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5886:	48 8b 50 38          	mov    0x38(%rax),%rdx
    588a:	8b 4a 10             	mov    0x10(%rdx),%ecx
    588d:	8d 69 01             	lea    0x1(%rcx),%ebp
    5890:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5893:	75 57                	jne    58ec <barriered_work+0x28c>
    5895:	0f 1f 00             	nopl   (%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5898:	48 63 93 b0 00 00 00 	movslq 0xb0(%rbx),%rdx
    589f:	48 8b 40 10          	mov    0x10(%rax),%rax
      data->n++;
    58a3:	48 83 83 88 00 00 00 01 	addq   $0x1,0x88(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    58ab:	48 8b 14 d0          	mov    (%rax,%rdx,8),%rdx
    58af:	48 63 03             	movslq (%rbx),%rax
    58b2:	48 8d 3c 40          	lea    (%rax,%rax,2),%rdi
    58b6:	48 c1 e7 07          	shl    $0x7,%rdi
    58ba:	48 03 7a 28          	add    0x28(%rdx),%rdi
    58be:	ff 93 a0 00 00 00    	call   *0xa0(%rbx)
      asm volatile ("sfence" ::: "memory");
    58c4:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    58c7:	83 bb c0 00 00 00 01 	cmpl   $0x1,0xc0(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    58ce:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    while (data->scheduled == 1) {
    58d5:	74 c1                	je     5898 <barriered_work+0x238>
    if (modcount != data->thread->protected_state->modcount) {
    58d7:	48 8b 40 38          	mov    0x38(%rax),%rax
    58db:	3b 68 10             	cmp    0x10(%rax),%ebp
    58de:	74 0c                	je     58ec <barriered_work+0x28c>
    58e0:	48 8d 3d 29 19 00 00 	lea    0x1929(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    58e7:	e8 04 ca ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    58ec:	48 8b b3 d8 00 00 00 	mov    0xd8(%rbx),%rsi
    58f3:	31 ff                	xor    %edi,%edi
    58f5:	48 c1 e6 05          	shl    $0x5,%rsi
    58f9:	48 03 b3 c8 00 00 00 	add    0xc8(%rbx),%rsi
    5900:	48 83 c6 10          	add    $0x10,%rsi
    5904:	e8 07 ca ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5909:	48 8b 83 d8 00 00 00 	mov    0xd8(%rbx),%rax
    5910:	48 83 c0 01          	add    $0x1,%rax
    5914:	48 99                	cqto
    5916:	48 f7 bb d0 00 00 00 	idivq  0xd0(%rbx)
  if (data->sending == 1) {
    591d:	83 bb f8 00 00 00 01 	cmpl   $0x1,0xf8(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5924:	48 89 93 d8 00 00 00 	mov    %rdx,0xd8(%rbx)
  if (data->sending == 1) {
    592b:	0f 84 ac 00 00 00    	je     59dd <barriered_work+0x37d>
    5931:	48 8d 3d cc 18 00 00 	lea    0x18cc(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5938:	e8 b3 c9 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    593d:	0f ae f8             	sfence
}
    5940:	48 83 c4 18          	add    $0x18,%rsp
    5944:	31 c0                	xor    %eax,%eax
    5946:	5b                   	pop    %rbx
    5947:	5d                   	pop    %rbp
    5948:	41 5c                	pop    %r12
    594a:	41 5d                	pop    %r13
    594c:	41 5e                	pop    %r14
    594e:	41 5f                	pop    %r15
    5950:	c3                   	ret
    5951:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5958:	49 89 f5             	mov    %rsi,%r13
    595b:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
    5962:	4c 89 e7             	mov    %r12,%rdi
    5965:	49 d1 ed             	shr    %r13
    5968:	49 c1 e5 04          	shl    $0x4,%r13
    596c:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5971:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5975:	41 83 e5 10          	and    $0x10,%r13d
    5979:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    597d:	74 11                	je     5990 <barriered_work+0x330>
          them->messages[them->messages_count++] = data->message; 
    597f:	48 83 c7 10          	add    $0x10,%rdi
    5983:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5988:	49 39 ff             	cmp    %rdi,%r15
    598b:	74 13                	je     59a0 <barriered_work+0x340>
    598d:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5990:	0f 11 07             	movups %xmm0,(%rdi)
    5993:	48 83 c7 20          	add    $0x20,%rdi
    5997:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    599b:	49 39 ff             	cmp    %rdi,%r15
    599e:	75 f0                	jne    5990 <barriered_work+0x330>
    59a0:	48 89 f7             	mov    %rsi,%rdi
    59a3:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    59a7:	4c 01 df             	add    %r11,%rdi
    59aa:	40 f6 c6 01          	test   $0x1,%sil
    59ae:	0f 84 d4 fd ff ff    	je     5788 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    59b4:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
    59bb:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    59bf:	e9 c4 fd ff ff       	jmp    5788 <barriered_work+0x128>
    59c4:	0f 1f 40 00          	nopl   0x0(%rax)
    59c8:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    59d0:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    59d8:	e9 84 fd ff ff       	jmp    5761 <barriered_work+0x101>
      for (int n = 0 ; n < data->thread_count; n++) {
    59dd:	48 8d 8b 00 01 00 00 	lea    0x100(%rbx),%rcx
    59e4:	8b 83 b4 00 00 00    	mov    0xb4(%rbx),%eax
    59ea:	31 d2                	xor    %edx,%edx
    59ec:	48 89 0c 24          	mov    %rcx,(%rsp)
    59f0:	48 8d 8b 08 01 00 00 	lea    0x108(%rbx),%rcx
    59f7:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    59fc:	85 c0                	test   %eax,%eax
    59fe:	0f 8e 39 ff ff ff    	jle    593d <barriered_work+0x2dd>
    5a04:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5a08:	39 93 b0 00 00 00    	cmp    %edx,0xb0(%rbx)
    5a0e:	0f 84 b7 00 00 00    	je     5acb <barriered_work+0x46b>
        struct Data *them = data->mailboxes[n].higher;
    5a14:	49 89 d1             	mov    %rdx,%r9
    5a17:	49 c1 e1 05          	shl    $0x5,%r9
    5a1b:	4c 03 8b e8 00 00 00 	add    0xe8(%rbx),%r9
    5a22:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    5a26:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5a2a:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5a2e:	4d 39 d8             	cmp    %r11,%r8
    5a31:	0f 8e 8b 00 00 00    	jle    5ac2 <barriered_work+0x462>
    5a37:	4c 89 c6             	mov    %r8,%rsi
    5a3a:	48 8b ab 88 00 00 00 	mov    0x88(%rbx),%rbp
    5a41:	4d 8b 71 10          	mov    0x10(%r9),%r14
    5a45:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5a48:	49 8b 0a             	mov    (%r10),%rcx
    5a4b:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5a4f:	48 83 f8 02          	cmp    $0x2,%rax
    5a53:	0f 86 f7 00 00 00    	jbe    5b50 <barriered_work+0x4f0>
    5a59:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5a61:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5a69:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5a6d:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5a71:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5a75:	73 69                	jae    5ae0 <barriered_work+0x480>
    5a77:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5a7c:	4d 39 fc             	cmp    %r15,%r12
    5a7f:	73 5f                	jae    5ae0 <barriered_work+0x480>
    5a81:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5a85:	48 01 cf             	add    %rcx,%rdi
    5a88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5a90:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
        for (; them->messages_count < min;) {
    5a97:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5a9b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5a9f:	49 39 fb             	cmp    %rdi,%r11
    5aa2:	75 ec                	jne    5a90 <barriered_work+0x430>
    5aa4:	0f 1f 40 00          	nopl   0x0(%rax)
    5aa8:	48 01 f5             	add    %rsi,%rbp
    5aab:	4c 01 f6             	add    %r14,%rsi
    5aae:	48 89 ab 88 00 00 00 	mov    %rbp,0x88(%rbx)
    5ab5:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5ab9:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5abd:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5ac2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5ac5:	8b 83 b4 00 00 00    	mov    0xb4(%rbx),%eax
    5acb:	48 83 c2 01          	add    $0x1,%rdx
    5acf:	39 d0                	cmp    %edx,%eax
    5ad1:	0f 8f 31 ff ff ff    	jg     5a08 <barriered_work+0x3a8>
    5ad7:	e9 61 fe ff ff       	jmp    593d <barriered_work+0x2dd>
    5adc:	0f 1f 40 00          	nopl   0x0(%rax)
    5ae0:	49 89 f5             	mov    %rsi,%r13
    5ae3:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
    5aea:	4c 89 e7             	mov    %r12,%rdi
    5aed:	49 d1 ed             	shr    %r13
    5af0:	49 c1 e5 04          	shl    $0x4,%r13
    5af4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5af9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5afd:	41 83 e5 10          	and    $0x10,%r13d
    5b01:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5b05:	74 11                	je     5b18 <barriered_work+0x4b8>
          them->messages[them->messages_count++] = data->message; 
    5b07:	48 83 c7 10          	add    $0x10,%rdi
    5b0b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5b10:	4c 39 ff             	cmp    %r15,%rdi
    5b13:	74 13                	je     5b28 <barriered_work+0x4c8>
    5b15:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5b18:	0f 11 07             	movups %xmm0,(%rdi)
    5b1b:	48 83 c7 20          	add    $0x20,%rdi
    5b1f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5b23:	4c 39 ff             	cmp    %r15,%rdi
    5b26:	75 f0                	jne    5b18 <barriered_work+0x4b8>
    5b28:	48 89 f7             	mov    %rsi,%rdi
    5b2b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5b2f:	4c 01 df             	add    %r11,%rdi
    5b32:	40 f6 c6 01          	test   $0x1,%sil
    5b36:	0f 84 6c ff ff ff    	je     5aa8 <barriered_work+0x448>
          them->messages[them->messages_count++] = data->message; 
    5b3c:	48 8b 83 00 01 00 00 	mov    0x100(%rbx),%rax
    5b43:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5b47:	e9 5c ff ff ff       	jmp    5aa8 <barriered_work+0x448>
    5b4c:	0f 1f 40 00          	nopl   0x0(%rax)
    5b50:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5b58:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5b60:	e9 1c ff ff ff       	jmp    5a81 <barriered_work+0x421>
    5b65:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005b70 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5b70:	f3 0f 1e fa          	endbr64
    5b74:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5b78:	48 8b 87 a8 00 00 00 	mov    0xa8(%rdi),%rax
    5b7f:	48 8b 40 40          	mov    0x40(%rax),%rax
    5b83:	48 63 10             	movslq (%rax),%rdx
    5b86:	85 d2                	test   %edx,%edx
    5b88:	7e 2c                	jle    5bb6 <barriered_work_ingest+0x46>
    5b8a:	48 8b 40 08          	mov    0x8(%rax),%rax
    5b8e:	48 c1 e2 04          	shl    $0x4,%rdx
    5b92:	48 01 c2             	add    %rax,%rdx
    5b95:	0f 1f 00             	nopl   (%rax)
    if (data->thread->buffers->buffer[x].available == 1) {
    5b98:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5b9c:	75 0f                	jne    5bad <barriered_work_ingest+0x3d>
      data->ingest_count++;
    5b9e:	48 83 87 e0 00 00 00 01 	addq   $0x1,0xe0(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5ba6:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5bad:	48 83 c0 10          	add    $0x10,%rax
    5bb1:	48 39 d0             	cmp    %rdx,%rax
    5bb4:	75 e2                	jne    5b98 <barriered_work_ingest+0x28>
  asm volatile ("sfence" ::: "memory");
    5bb6:	0f ae f8             	sfence
  barriered_work(data);
    5bb9:	e8 a2 fa ff ff       	call   5660 <barriered_work>
}
    5bbe:	31 c0                	xor    %eax,%eax
    5bc0:	48 83 c4 08          	add    $0x8,%rsp
    5bc4:	c3                   	ret
    5bc5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005bd0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5bd0:	f3 0f 1e fa          	endbr64
}
    5bd4:	31 c0                	xor    %eax,%eax
    5bd6:	c3                   	ret
    5bd7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005be0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5be0:	f3 0f 1e fa          	endbr64
    5be4:	31 c0                	xor    %eax,%eax
    5be6:	c3                   	ret
    5be7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005bf0 <after>:
int after(struct timespec left, struct timespec right) {
    5bf0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5bf4:	31 c0                	xor    %eax,%eax
    5bf6:	48 39 d7             	cmp    %rdx,%rdi
    5bf9:	7e 08                	jle    5c03 <after+0x13>
    5bfb:	31 c0                	xor    %eax,%eax
    5bfd:	48 39 ce             	cmp    %rcx,%rsi
    5c00:	0f 9f c0             	setg   %al
}
    5c03:	c3                   	ret
    5c04:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5c0f:	90                   	nop

0000000000005c10 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5c10:	f3 0f 1e fa          	endbr64
    5c14:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5c19:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5c1e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5c20:	48 39 d7             	cmp    %rdx,%rdi
    5c23:	7f 18                	jg     5c3d <within+0x2d>
    5c25:	4d 39 d8             	cmp    %r11,%r8
    5c28:	0f 9e c2             	setle  %dl
    5c2b:	48 39 ce             	cmp    %rcx,%rsi
    5c2e:	0f 9e c0             	setle  %al
    5c31:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5c33:	31 c0                	xor    %eax,%eax
    5c35:	4d 39 d1             	cmp    %r10,%r9
    5c38:	0f 9e c0             	setle  %al
    5c3b:	21 d0                	and    %edx,%eax
}
    5c3d:	c3                   	ret
    5c3e:	66 90                	xchg   %ax,%ax

0000000000005c40 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5c40:	f3 0f 1e fa          	endbr64
    5c44:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5c49:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5c4e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5c53:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5c58:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5c5d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5c62:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5c67:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5c6c:	48 39 fe             	cmp    %rdi,%rsi
    5c6f:	7d 2f                	jge    5ca0 <overlap+0x60>
    5c71:	48 39 ca             	cmp    %rcx,%rdx
    5c74:	7d 62                	jge    5cd8 <overlap+0x98>
    5c76:	4d 39 da             	cmp    %r11,%r10
    5c79:	7d 0e                	jge    5c89 <overlap+0x49>
    return 1;
    5c7b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5c80:	4d 39 c1             	cmp    %r8,%r9
    5c83:	0f 8c 7f 00 00 00    	jl     5d08 <overlap+0xc8>
  return 0;
    5c89:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5c8b:	4d 39 c1             	cmp    %r8,%r9
    5c8e:	7f 4c                	jg     5cdc <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5c90:	31 c0                	xor    %eax,%eax
    5c92:	4d 39 da             	cmp    %r11,%r10
    5c95:	0f 9e c0             	setle  %al
    5c98:	c3                   	ret
    5c99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5ca0:	7e 4e                	jle    5cf0 <overlap+0xb0>
    5ca2:	48 39 ca             	cmp    %rcx,%rdx
    5ca5:	7f 39                	jg     5ce0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ca7:	75 31                	jne    5cda <overlap+0x9a>
    5ca9:	4d 39 c1             	cmp    %r8,%r9
    5cac:	7c 2c                	jl     5cda <overlap+0x9a>
    return 1;
    5cae:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5cb3:	4d 39 da             	cmp    %r11,%r10
    5cb6:	7d 24                	jge    5cdc <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5cb8:	48 39 ca             	cmp    %rcx,%rdx
    5cbb:	0f 94 c2             	sete   %dl
    5cbe:	48 39 fe             	cmp    %rdi,%rsi
    5cc1:	0f 94 c0             	sete   %al
    5cc4:	21 c2                	and    %eax,%edx
    5cc6:	31 c0                	xor    %eax,%eax
    5cc8:	4d 39 c1             	cmp    %r8,%r9
    5ccb:	0f 94 c0             	sete   %al
    5cce:	21 d0                	and    %edx,%eax
    5cd0:	c3                   	ret
    5cd1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5cd8:	74 af                	je     5c89 <overlap+0x49>
  return 0;
    5cda:	31 c0                	xor    %eax,%eax
}
    5cdc:	c3                   	ret
    5cdd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5ce0:	4d 39 da             	cmp    %r11,%r10
    5ce3:	7e c4                	jle    5ca9 <overlap+0x69>
    return 1;
    5ce5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5cea:	4d 39 c1             	cmp    %r8,%r9
    5ced:	7e ba                	jle    5ca9 <overlap+0x69>
    5cef:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5cf0:	48 39 ca             	cmp    %rcx,%rdx
    5cf3:	7c 94                	jl     5c89 <overlap+0x49>
    5cf5:	4d 39 c1             	cmp    %r8,%r9
    5cf8:	7d b4                	jge    5cae <overlap+0x6e>
    5cfa:	48 39 ca             	cmp    %rcx,%rdx
    5cfd:	74 91                	je     5c90 <overlap+0x50>
    5cff:	eb d9                	jmp    5cda <overlap+0x9a>
    5d01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5d08:	c3                   	ret
    5d09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005d10 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5d10:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5d14:	85 f6                	test   %esi,%esi
    5d16:	0f 8e 49 03 00 00    	jle    6065 <verify+0x355>
int verify(struct KernelThread *thread_data, int thread_count) {
    5d1c:	41 57                	push   %r15
    5d1e:	41 89 f7             	mov    %esi,%r15d
    5d21:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5d23:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5d26:	41 55                	push   %r13
    5d28:	41 54                	push   %r12
    5d2a:	55                   	push   %rbp
    5d2b:	53                   	push   %rbx
    5d2c:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5d30:	48 83 ec 48          	sub    $0x48,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5d34:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5d39:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    5d3e:	45 31 e4             	xor    %r12d,%r12d
    5d41:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
      if (z != x)  {
    5d46:	45 39 e6             	cmp    %r12d,%r14d
    5d49:	0f 84 47 02 00 00    	je     5f96 <verify+0x286>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5d4f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5d54:	8b 50 08             	mov    0x8(%rax),%edx
    5d57:	85 d2                	test   %edx,%edx
    5d59:	0f 8e 37 02 00 00    	jle    5f96 <verify+0x286>
    5d5f:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    5d67:	31 ed                	xor    %ebp,%ebp
    5d69:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    5d6e:	44 89 7c 24 34       	mov    %r15d,0x34(%rsp)
    5d73:	45 89 f7             	mov    %r14d,%r15d
    5d76:	41 89 ee             	mov    %ebp,%r14d
    5d79:	44 89 fa             	mov    %r15d,%edx
    5d7c:	48 8d 35 9d 14 00 00 	lea    0x149d(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    5d83:	bf 01 00 00 00       	mov    $0x1,%edi
    5d88:	31 c0                	xor    %eax,%eax
    5d8a:	e8 c1 c6 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5d8f:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5d94:	8b 40 08             	mov    0x8(%rax),%eax
    5d97:	85 c0                	test   %eax,%eax
    5d99:	0f 8e cf 01 00 00    	jle    5f6e <verify+0x25e>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5d9f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5da4:	44 89 74 24 38       	mov    %r14d,0x38(%rsp)
    5da9:	31 db                	xor    %ebx,%ebx
    5dab:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    5db0:	4c 8b 20             	mov    (%rax),%r12
    5db3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5db8:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    5dbd:	48 8d 04 5b          	lea    (%rbx,%rbx,2),%rax
    5dc1:	4c 8b 3c 24          	mov    (%rsp),%r15
    5dc5:	48 8d 35 69 14 00 00 	lea    0x1469(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5dcc:	49 89 c6             	mov    %rax,%r14
    5dcf:	bf 01 00 00 00       	mov    $0x1,%edi
    5dd4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5dd8:	49 c1 e6 07          	shl    $0x7,%r14
    5ddc:	4b 8b 8c 3c d8 00 00 00 	mov    0xd8(%r12,%r15,1),%rcx
    5de4:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    5de9:	4a 8b 94 30 d8 00 00 00 	mov    0xd8(%rax,%r14,1),%rdx
    5df1:	31 c0                	xor    %eax,%eax
    5df3:	e8 58 c6 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5df8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5dfd:	4c 8b 20             	mov    (%rax),%r12
    5e00:	4b 83 bc 3c d8 00 00 00 00 	cmpq   $0x0,0xd8(%r12,%r15,1)
    5e09:	0f 8e 43 01 00 00    	jle    5f52 <verify+0x242>
    5e0f:	4c 03 75 00          	add    0x0(%rbp),%r14
    5e13:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5e18:	ba 01 00 00 00       	mov    $0x1,%edx
    5e1d:	4d 89 f5             	mov    %r14,%r13
    5e20:	4d 8b b5 d8 00 00 00 	mov    0xd8(%r13),%r14
    5e27:	4d 85 f6             	test   %r14,%r14
    5e2a:	0f 8e 1d 01 00 00    	jle    5f4d <verify+0x23d>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5e30:	48 89 d5             	mov    %rdx,%rbp
    5e33:	48 8b 04 24          	mov    (%rsp),%rax
    5e37:	31 db                	xor    %ebx,%ebx
    5e39:	4d 89 f2             	mov    %r14,%r10
    5e3c:	48 c1 e5 05          	shl    $0x5,%rbp
    5e40:	48 83 ed 20          	sub    $0x20,%rbp
    5e44:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    5e48:	49 89 ee             	mov    %rbp,%r14
    5e4b:	48 89 dd             	mov    %rbx,%rbp
    5e4e:	48 89 d3             	mov    %rdx,%rbx
    5e51:	eb 32                	jmp    5e85 <verify+0x175>
    5e53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5e58:	4c 39 c2             	cmp    %r8,%rdx
    5e5b:	0f 8d 57 01 00 00    	jge    5fb8 <verify+0x2a8>
    5e61:	4c 39 df             	cmp    %r11,%rdi
    5e64:	7e 05                	jle    5e6b <verify+0x15b>
    5e66:	49 39 c1             	cmp    %rax,%r9
    5e69:	7c 75                	jl     5ee0 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e6b:	4c 39 df             	cmp    %r11,%rdi
    5e6e:	0f 8d b3 01 00 00    	jge    6027 <verify+0x317>
    5e74:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5e78:	48 83 c5 01          	add    $0x1,%rbp
    5e7c:	49 39 ea             	cmp    %rbp,%r10
    5e7f:	0f 8e a8 00 00 00    	jle    5f2d <verify+0x21d>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5e85:	49 8b 97 c8 00 00 00 	mov    0xc8(%r15),%rdx
    5e8c:	48 89 e8             	mov    %rbp,%rax
    5e8f:	48 c1 e0 05          	shl    $0x5,%rax
    5e93:	49 03 85 c8 00 00 00 	add    0xc8(%r13),%rax
    5e9a:	4c 01 f2             	add    %r14,%rdx
    5e9d:	48 8b 08             	mov    (%rax),%rcx
    5ea0:	48 8b 78 10          	mov    0x10(%rax),%rdi
    5ea4:	48 8b 32             	mov    (%rdx),%rsi
    5ea7:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    5eab:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    5eaf:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    5eb3:	48 8b 50 08          	mov    0x8(%rax),%rdx
    5eb7:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    5ebb:	48 39 f1             	cmp    %rsi,%rcx
    5ebe:	7c 98                	jl     5e58 <verify+0x148>
    5ec0:	0f 8e 4a 01 00 00    	jle    6010 <verify+0x300>
    5ec6:	4c 39 c2             	cmp    %r8,%rdx
    5ec9:	0f 8f f9 00 00 00    	jg     5fc8 <verify+0x2b8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ecf:	75 a7                	jne    5e78 <verify+0x168>
    5ed1:	4c 39 df             	cmp    %r11,%rdi
    5ed4:	7f a2                	jg     5e78 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5ed6:	49 39 c1             	cmp    %rax,%r9
    5ed9:	7c 9d                	jl     5e78 <verify+0x168>
    5edb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5ee0:	49 89 c1             	mov    %rax,%r9
    5ee3:	48 89 f9             	mov    %rdi,%rcx
    5ee6:	48 89 f2             	mov    %rsi,%rdx
    5ee9:	bf 01 00 00 00       	mov    $0x1,%edi
    5eee:	48 8d 35 93 15 00 00 	lea    0x1593(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    5ef5:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5ef7:	48 83 c5 01          	add    $0x1,%rbp
    5efb:	e8 50 c5 ff ff       	call   2450 <__printf_chk@plt>
    5f00:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5f05:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    5f0a:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5f0d:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5f12:	4d 8b 95 d8 00 00 00 	mov    0xd8(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5f19:	4c 8b 20             	mov    (%rax),%r12
    5f1c:	48 8b 04 24          	mov    (%rsp),%rax
    5f20:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5f24:	49 39 ea             	cmp    %rbp,%r10
    5f27:	0f 8f 58 ff ff ff    	jg     5e85 <verify+0x175>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5f2d:	48 89 da             	mov    %rbx,%rdx
    5f30:	49 3b 9f d8 00 00 00 	cmp    0xd8(%r15),%rbx
    5f37:	7d 14                	jge    5f4d <verify+0x23d>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5f39:	4d 8b b5 d8 00 00 00 	mov    0xd8(%r13),%r14
    5f40:	48 83 c2 01          	add    $0x1,%rdx
    5f44:	4d 85 f6             	test   %r14,%r14
    5f47:	0f 8f e3 fe ff ff    	jg     5e30 <verify+0x120>
    5f4d:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5f52:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5f57:	48 83 c3 01          	add    $0x1,%rbx
    5f5b:	39 58 08             	cmp    %ebx,0x8(%rax)
    5f5e:	0f 8f 54 fe ff ff    	jg     5db8 <verify+0xa8>
    5f64:	44 8b 74 24 38       	mov    0x38(%rsp),%r14d
    5f69:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5f6e:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5f73:	48 81 04 24 80 01 00 00 	addq   $0x180,(%rsp)
    5f7b:	41 83 c6 01          	add    $0x1,%r14d
    5f7f:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    5f83:	0f 8f f0 fd ff ff    	jg     5d79 <verify+0x69>
    5f89:	45 89 fe             	mov    %r15d,%r14d
    5f8c:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    5f91:	44 8b 7c 24 34       	mov    0x34(%rsp),%r15d
    for (int z = 0 ; z < thread_count; z++) {
    5f96:	48 81 44 24 08 b0 00 00 00 	addq   $0xb0,0x8(%rsp)
    5f9f:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    5fa4:	41 39 c7             	cmp    %eax,%r15d
    5fa7:	0f 84 88 00 00 00    	je     6035 <verify+0x325>
    5fad:	41 89 c4             	mov    %eax,%r12d
    5fb0:	e9 91 fd ff ff       	jmp    5d46 <verify+0x36>
    5fb5:	0f 1f 00             	nopl   (%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5fb8:	0f 85 ba fe ff ff    	jne    5e78 <verify+0x168>
    5fbe:	e9 a8 fe ff ff       	jmp    5e6b <verify+0x15b>
    5fc3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5fc8:	49 39 c1             	cmp    %rax,%r9
    5fcb:	7e 09                	jle    5fd6 <verify+0x2c6>
    5fcd:	4c 39 df             	cmp    %r11,%rdi
    5fd0:	0f 8c 0a ff ff ff    	jl     5ee0 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5fd6:	4c 39 df             	cmp    %r11,%rdi
    5fd9:	0f 8f 99 fe ff ff    	jg     5e78 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5fdf:	49 39 c1             	cmp    %rax,%r9
    5fe2:	0f 8d f8 fe ff ff    	jge    5ee0 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5fe8:	48 39 f1             	cmp    %rsi,%rcx
    5feb:	0f 85 87 fe ff ff    	jne    5e78 <verify+0x168>
    5ff1:	4c 39 c2             	cmp    %r8,%rdx
    5ff4:	0f 85 7e fe ff ff    	jne    5e78 <verify+0x168>
    5ffa:	4c 39 df             	cmp    %r11,%rdi
    5ffd:	0f 84 dd fe ff ff    	je     5ee0 <verify+0x1d0>
    6003:	e9 70 fe ff ff       	jmp    5e78 <verify+0x168>
    6008:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6010:	4c 39 c2             	cmp    %r8,%rdx
    6013:	0f 8c 52 fe ff ff    	jl     5e6b <verify+0x15b>
    6019:	4c 39 df             	cmp    %r11,%rdi
    601c:	7e c1                	jle    5fdf <verify+0x2cf>
    601e:	4c 39 c2             	cmp    %r8,%rdx
    6021:	0f 85 51 fe ff ff    	jne    5e78 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6027:	49 39 c1             	cmp    %rax,%r9
    602a:	0f 8f 48 fe ff ff    	jg     5e78 <verify+0x168>
    6030:	e9 ab fe ff ff       	jmp    5ee0 <verify+0x1d0>
  for (int x = 0 ; x < thread_count; x++) {
    6035:	48 81 44 24 10 b0 00 00 00 	addq   $0xb0,0x10(%rsp)
    603e:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    6043:	41 8d 46 01          	lea    0x1(%r14),%eax
    6047:	45 39 e6             	cmp    %r12d,%r14d
    604a:	74 08                	je     6054 <verify+0x344>
    604c:	41 89 c6             	mov    %eax,%r14d
    604f:	e9 e5 fc ff ff       	jmp    5d39 <verify+0x29>
}
    6054:	48 83 c4 48          	add    $0x48,%rsp
    6058:	31 c0                	xor    %eax,%eax
    605a:	5b                   	pop    %rbx
    605b:	5d                   	pop    %rbp
    605c:	41 5c                	pop    %r12
    605e:	41 5d                	pop    %r13
    6060:	41 5e                	pop    %r14
    6062:	41 5f                	pop    %r15
    6064:	c3                   	ret
    6065:	31 c0                	xor    %eax,%eax
    6067:	c3                   	ret

Disassembly of section .fini:

0000000000006068 <_fini>:
    6068:	f3 0f 1e fa          	endbr64
    606c:	48 83 ec 08          	sub    $0x8,%rsp
    6070:	48 83 c4 08          	add    $0x8,%rsp
    6074:	c3                   	ret
