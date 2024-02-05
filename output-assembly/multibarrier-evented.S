
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
    2556:	48 8d 3d c3 4c 00 00 	lea    0x4cc3(%rip),%rdi        # 7220 <_IO_stdin_used+0x220>
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
    2596:	48 8d 3d 53 4c 00 00 	lea    0x4c53(%rip),%rdi        # 71f0 <_IO_stdin_used+0x1f0>
    259d:	e8 9e ff ff ff       	call   2540 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    25a2:	48 8d 3d cb 4b 00 00 	lea    0x4bcb(%rip),%rdi        # 7174 <_IO_stdin_used+0x174>
    25a9:	e8 92 ff ff ff       	call   2540 <fatal_error>
    fatal_error("listen()");
    25ae:	48 8d 3d df 4b 00 00 	lea    0x4bdf(%rip),%rdi        # 7194 <_IO_stdin_used+0x194>
    25b5:	e8 86 ff ff ff       	call   2540 <fatal_error>
    25ba:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25c2:	0f 0b                	ud2
    25c4:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25cc:	0f 0b                	ud2
      fatal_error("socket()");
    25ce:	48 8d 3d 96 4b 00 00 	lea    0x4b96(%rip),%rdi        # 716b <_IO_stdin_used+0x16b>
    25d5:	e8 66 ff ff ff       	call   2540 <fatal_error>
      fatal_error("bind()");
    25da:	48 8d 3d ac 4b 00 00 	lea    0x4bac(%rip),%rdi        # 718d <_IO_stdin_used+0x18d>
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
    25f6:	48 8d 3d ab 4f 00 00 	lea    0x4fab(%rip),%rdi        # 75a8 <_IO_stdin_used+0x5a8>
    25fd:	41 56                	push   %r14
    25ff:	41 55                	push   %r13
    2601:	41 54                	push   %r12
    2603:	55                   	push   %rbp
    2604:	53                   	push   %rbx
    2605:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
    260c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2615:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    261a:	48 8d 05 8f 12 00 00 	lea    0x128f(%rip),%rax        # 38b0 <barriered_reset>
    2621:	66 48 0f 6e d8       	movq   %rax,%xmm3
    2626:	0f 16 1d 4b 76 00 00 	movhps 0x764b(%rip),%xmm3        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    262d:	0f 29 5c 24 50       	movaps %xmm3,0x50(%rsp)
    2632:	e8 b9 fc ff ff       	call   22f0 <puts@plt>
    2637:	bf 0a 00 00 00       	mov    $0xa,%edi
    263c:	e8 8f fc ff ff       	call   22d0 <putchar@plt>
    2641:	ba 01 00 00 00       	mov    $0x1,%edx
    2646:	48 8d 35 06 4c 00 00 	lea    0x4c06(%rip),%rsi        # 7253 <_IO_stdin_used+0x253>
    264d:	31 c0                	xor    %eax,%eax
    264f:	bf 01 00 00 00       	mov    $0x1,%edi
    2654:	e8 f7 fd ff ff       	call   2450 <__printf_chk@plt>
    2659:	ba 02 00 00 00       	mov    $0x2,%edx
    265e:	48 8d 35 fe 4b 00 00 	lea    0x4bfe(%rip),%rsi        # 7263 <_IO_stdin_used+0x263>
    2665:	31 c0                	xor    %eax,%eax
    2667:	bf 01 00 00 00       	mov    $0x1,%edi
    266c:	e8 df fd ff ff       	call   2450 <__printf_chk@plt>
    2671:	ba 01 00 00 00       	mov    $0x1,%edx
    2676:	48 8d 35 fb 4b 00 00 	lea    0x4bfb(%rip),%rsi        # 7278 <_IO_stdin_used+0x278>
    267d:	31 c0                	xor    %eax,%eax
    267f:	bf 01 00 00 00       	mov    $0x1,%edi
    2684:	e8 c7 fd ff ff       	call   2450 <__printf_chk@plt>
    2689:	ba 02 00 00 00       	mov    $0x2,%edx
    268e:	48 8d 35 f3 4b 00 00 	lea    0x4bf3(%rip),%rsi        # 7288 <_IO_stdin_used+0x288>
    2695:	31 c0                	xor    %eax,%eax
    2697:	bf 01 00 00 00       	mov    $0x1,%edi
    269c:	e8 af fd ff ff       	call   2450 <__printf_chk@plt>
    26a1:	48 8d 3d f6 4b 00 00 	lea    0x4bf6(%rip),%rdi        # 729e <_IO_stdin_used+0x29e>
    26a8:	e8 43 fc ff ff       	call   22f0 <puts@plt>
    26ad:	ba 02 00 00 00       	mov    $0x2,%edx
    26b2:	48 8d 35 01 4c 00 00 	lea    0x4c01(%rip),%rsi        # 72ba <_IO_stdin_used+0x2ba>
    26b9:	31 c0                	xor    %eax,%eax
    26bb:	bf 01 00 00 00       	mov    $0x1,%edi
    26c0:	e8 8b fd ff ff       	call   2450 <__printf_chk@plt>
    26c5:	ba 06 00 00 00       	mov    $0x6,%edx
    26ca:	48 8d 35 03 4c 00 00 	lea    0x4c03(%rip),%rsi        # 72d4 <_IO_stdin_used+0x2d4>
    26d1:	31 c0                	xor    %eax,%eax
    26d3:	bf 01 00 00 00       	mov    $0x1,%edi
    26d8:	e8 73 fd ff ff       	call   2450 <__printf_chk@plt>
    26dd:	ba 01 00 00 00       	mov    $0x1,%edx
    26e2:	48 8d 35 ff 4b 00 00 	lea    0x4bff(%rip),%rsi        # 72e8 <_IO_stdin_used+0x2e8>
    26e9:	31 c0                	xor    %eax,%eax
    26eb:	bf 01 00 00 00       	mov    $0x1,%edi
    26f0:	e8 5b fd ff ff       	call   2450 <__printf_chk@plt>
    26f5:	ba 01 00 00 00       	mov    $0x1,%edx
    26fa:	48 8d 35 f8 4b 00 00 	lea    0x4bf8(%rip),%rsi        # 72f9 <_IO_stdin_used+0x2f9>
    2701:	31 c0                	xor    %eax,%eax
    2703:	bf 01 00 00 00       	mov    $0x1,%edi
    2708:	e8 43 fd ff ff       	call   2450 <__printf_chk@plt>
    270d:	ba 02 00 00 00       	mov    $0x2,%edx
    2712:	48 8d 35 f8 4b 00 00 	lea    0x4bf8(%rip),%rsi        # 7311 <_IO_stdin_used+0x311>
    2719:	31 c0                	xor    %eax,%eax
    271b:	bf 01 00 00 00       	mov    $0x1,%edi
    2720:	e8 2b fd ff ff       	call   2450 <__printf_chk@plt>
    2725:	ba 01 00 00 00       	mov    $0x1,%edx
    272a:	48 8d 35 df 4e 00 00 	lea    0x4edf(%rip),%rsi        # 7610 <_IO_stdin_used+0x610>
    2731:	31 c0                	xor    %eax,%eax
    2733:	bf 01 00 00 00       	mov    $0x1,%edi
    2738:	e8 13 fd ff ff       	call   2450 <__printf_chk@plt>
    273d:	ba 01 00 00 00       	mov    $0x1,%edx
    2742:	48 8d 35 f7 4e 00 00 	lea    0x4ef7(%rip),%rsi        # 7640 <_IO_stdin_used+0x640>
    2749:	31 c0                	xor    %eax,%eax
    274b:	bf 01 00 00 00       	mov    $0x1,%edi
    2750:	e8 fb fc ff ff       	call   2450 <__printf_chk@plt>
    2755:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    275a:	48 8d 35 cc 4b 00 00 	lea    0x4bcc(%rip),%rsi        # 732d <_IO_stdin_used+0x32d>
    2761:	31 c0                	xor    %eax,%eax
    2763:	bf 01 00 00 00       	mov    $0x1,%edi
    2768:	e8 e3 fc ff ff       	call   2450 <__printf_chk@plt>
    276d:	ba 05 00 00 00       	mov    $0x5,%edx
    2772:	48 8d 35 ce 4b 00 00 	lea    0x4bce(%rip),%rsi        # 7347 <_IO_stdin_used+0x347>
    2779:	31 c0                	xor    %eax,%eax
    277b:	bf 01 00 00 00       	mov    $0x1,%edi
    2780:	e8 cb fc ff ff       	call   2450 <__printf_chk@plt>
    2785:	48 8d 3d 63 49 00 00 	lea    0x4963(%rip),%rdi        # 70ef <_IO_stdin_used+0xef>
    278c:	e8 5f fb ff ff       	call   22f0 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2791:	be 18 00 00 00       	mov    $0x18,%esi
    2796:	bf 01 00 00 00       	mov    $0x1,%edi
    279b:	e8 00 fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27a0:	be c0 00 00 00       	mov    $0xc0,%esi
    27a5:	bf 06 00 00 00       	mov    $0x6,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    27aa:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27af:	e8 ec fb ff ff       	call   23a0 <calloc@plt>
    27b4:	ba 02 00 00 00       	mov    $0x2,%edx
    27b9:	bf 01 00 00 00       	mov    $0x1,%edi
    27be:	48 8d 35 96 4b 00 00 	lea    0x4b96(%rip),%rsi        # 735b <_IO_stdin_used+0x35b>
    27c5:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    27ca:	31 c0                	xor    %eax,%eax
    27cc:	e8 7f fc ff ff       	call   2450 <__printf_chk@plt>
    27d1:	ba 04 00 00 00       	mov    $0x4,%edx
    27d6:	48 8d 35 94 4b 00 00 	lea    0x4b94(%rip),%rsi        # 7371 <_IO_stdin_used+0x371>
    27dd:	31 c0                	xor    %eax,%eax
    27df:	bf 01 00 00 00       	mov    $0x1,%edi
    27e4:	e8 67 fc ff ff       	call   2450 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    27e9:	be 10 00 00 00       	mov    $0x10,%esi
    27ee:	bf 04 00 00 00       	mov    $0x4,%edi
    27f3:	e8 a8 fb ff ff       	call   23a0 <calloc@plt>
    27f8:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    27fd:	49 89 c5             	mov    %rax,%r13
    2800:	48 8d 58 40          	lea    0x40(%rax),%rbx
    2804:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2809:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    280e:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2816:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    281b:	49 83 c5 10          	add    $0x10,%r13
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    281f:	e8 7c fb ff ff       	call   23a0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2824:	be 20 00 00 00       	mov    $0x20,%esi
    2829:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    282e:	49 89 45 f8          	mov    %rax,-0x8(%r13)
    2832:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
    2835:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    283f:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2849:	e8 52 fb ff ff       	call   23a0 <calloc@plt>
    284e:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    2855:	4c 39 eb             	cmp    %r13,%rbx
    2858:	75 af                	jne    2809 <main+0x219>
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
        other = abs(x - 1) % total_threads;
        thread_data[x].thread_index = 1;
    285a:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
    285f:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
    2867:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    2870:	49 8d 87 c0 00 00 00 	lea    0xc0(%r15),%rax
    2877:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    287c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2881:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2885:	31 d2                	xor    %edx,%edx
    2887:	bf 01 00 00 00       	mov    $0x1,%edi
    288c:	48 8d 35 d5 4d 00 00 	lea    0x4dd5(%rip),%rsi        # 7668 <_IO_stdin_used+0x668>
    2893:	89 d9                	mov    %ebx,%ecx
    2895:	89 c5                	mov    %eax,%ebp
    2897:	41 89 c6             	mov    %eax,%r14d
    289a:	31 c0                	xor    %eax,%eax
    289c:	e8 af fb ff ff       	call   2450 <__printf_chk@plt>
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    28a1:	be 08 00 00 00       	mov    $0x8,%esi
    28a6:	bf 02 00 00 00       	mov    $0x2,%edi
    28ab:	e8 f0 fa ff ff       	call   23a0 <calloc@plt>
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    28b0:	be 80 00 00 00       	mov    $0x80,%esi
    28b5:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    28ba:	49 89 c4             	mov    %rax,%r12
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    28bd:	e8 de fa ff ff       	call   23a0 <calloc@plt>
    28c2:	49 89 c5             	mov    %rax,%r13
        thread_data[x].thread_index = 1;
    28c5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
      if (x % 2 == 1) {
    28ca:	83 fb 01             	cmp    $0x1,%ebx
    28cd:	0f 84 6b 0e 00 00    	je     373e <main+0x114e>
        other = (x + 1) % total_threads;
        my_thread_data[0] = &thread_data[x]; 
        me_thread = 0;
        my_thread_data[1] = &thread_data[other]; 
        // printf("even %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
        thread_data[x].protected_state = &protected_state[k];
    28d3:	48 8b 7c 24 48       	mov    0x48(%rsp),%rdi
    28d8:	4c 89 64 24 30       	mov    %r12,0x30(%rsp)
        other = (x + 1) % total_threads;
    28dd:	bb 01 00 00 00       	mov    $0x1,%ebx
        thread_data[x].thread_index = 0;
    28e2:	c7 40 04 00 00 00 00 	movl   $0x0,0x4(%rax)
        thread_data[x].protected_state = &protected_state[k];
    28e9:	48 89 78 48          	mov    %rdi,0x48(%rax)
    28ed:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    28f2:	45 8b 47 04          	mov    0x4(%r15),%r8d
    28f6:	89 d9                	mov    %ebx,%ecx
    28f8:	bf 01 00 00 00       	mov    $0x1,%edi
    28fd:	8b 54 24 08          	mov    0x8(%rsp),%edx
    2901:	48 8d 35 90 4d 00 00 	lea    0x4d90(%rip),%rsi        # 7698 <_IO_stdin_used+0x698>
    2908:	49 89 44 24 08       	mov    %rax,0x8(%r12)
    290d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    2912:	49 89 04 24          	mov    %rax,(%r12)
    2916:	31 c0                	xor    %eax,%eax
    2918:	e8 33 fb ff ff       	call   2450 <__printf_chk@plt>
    291d:	44 89 f1             	mov    %r14d,%ecx
    2920:	bf 01 00 00 00       	mov    $0x1,%edi
    2925:	31 c0                	xor    %eax,%eax
      }
      printf("i am %d, other is %d my thread index is %d\n", x, other, thread_data[x].thread_index);
      thread_data[x].other = other;
    2927:	41 89 9f b8 00 00 00 	mov    %ebx,0xb8(%r15)
    292e:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2932:	48 8d 35 8f 4d 00 00 	lea    0x4d8f(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    2939:	89 da                	mov    %ebx,%edx
    293b:	e8 10 fb ff ff       	call   2450 <__printf_chk@plt>
      // for (int j = 0 ; j < cores ; j++) {
        printf("assigning thread %d to core %d\n", x, curcpu);
        if (x < thread_count) {
          CPU_SET(curcpu, sendercpu);
    2940:	89 e9                	mov    %ebp,%ecx
    2942:	b8 01 00 00 00       	mov    $0x1,%eax
        }
        
      // }
      thread_data[x].kind = KERNEL_THREAD;
      thread_data[x].cpu_set = sendercpu;
      thread_data[x].real_thread_index = x;
    2947:	41 89 5f 08          	mov    %ebx,0x8(%r15)
          CPU_SET(curcpu, sendercpu);
    294b:	48 d3 e0             	shl    %cl,%rax
    294e:	49 09 45 00          	or     %rax,0x0(%r13)
      thread_data[x].threads = my_thread_data;
      thread_data[x].all_threads = thread_data;
    2952:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
      thread_data[x].thread_count = 2;
      thread_data[x].total_thread_count = total_threads;
      thread_data[x].task_count = total_barrier_count;
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2957:	be 10 00 00 00       	mov    $0x10,%esi
      thread_data[x].cpu_set = sendercpu;
    295c:	4d 89 af b0 00 00 00 	mov    %r13,0xb0(%r15)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2963:	bf 64 00 00 00       	mov    $0x64,%edi

        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
        thread_data[x].tasks = barriers;
        int assigned = 0;
        // external_thread_index = 0;
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2968:	45 31 ed             	xor    %r13d,%r13d
      thread_data[x].all_threads = thread_data;
    296b:	49 89 47 20          	mov    %rax,0x20(%r15)
      thread_data[x].thread_count = 2;
    296f:	48 8b 05 6a 52 00 00 	mov    0x526a(%rip),%rax        # 7be0 <_IO_stdin_used+0xbe0>
      thread_data[x].kind = KERNEL_THREAD;
    2976:	41 c7 07 5f 00 00 00 	movl   $0x5f,(%r15)
      thread_data[x].threads = my_thread_data;
    297d:	4d 89 67 18          	mov    %r12,0x18(%r15)
      thread_data[x].thread_count = 2;
    2981:	49 89 47 28          	mov    %rax,0x28(%r15)
      thread_data[x].task_count = total_barrier_count;
    2985:	41 c7 47 40 03 00 00 00 	movl   $0x3,0x40(%r15)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    298d:	e8 0e fa ff ff       	call   23a0 <calloc@plt>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2992:	be 10 00 00 00       	mov    $0x10,%esi
    2997:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    299c:	49 89 47 68          	mov    %rax,0x68(%r15)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    29a0:	e8 fb f9 ff ff       	call   23a0 <calloc@plt>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    29a5:	be 28 00 00 00       	mov    $0x28,%esi
    29aa:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].timestamp_count = 0;
    29af:	66 0f 6f 2d f9 51 00 00 	movdqa 0x51f9(%rip),%xmm5        # 7bb0 <_IO_stdin_used+0xbb0>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    29b7:	49 89 47 70          	mov    %rax,0x70(%r15)
      thread_data[x].timestamp_count = 0;
    29bb:	41 0f 11 af 80 00 00 00 	movups %xmm5,0x80(%r15)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    29c3:	e8 d8 f9 ff ff       	call   23a0 <calloc@plt>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    29c8:	be 00 02 00 00       	mov    $0x200,%esi
    29cd:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    29d2:	66 0f 6f 35 d6 51 00 00 	movdqa 0x51d6(%rip),%xmm6        # 7bb0 <_IO_stdin_used+0xbb0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    29da:	49 89 87 90 00 00 00 	mov    %rax,0x90(%r15)
      thread_data[x].task_timestamp_count = 0;
    29e1:	41 0f 11 b7 98 00 00 00 	movups %xmm6,0x98(%r15)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    29e9:	e8 b2 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks = barriers;
    29ee:	49 89 47 38          	mov    %rax,0x38(%r15)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    29f2:	48 89 c5             	mov    %rax,%rbp
                t     x
                a       x
                s         x
                k           x
          */
          thread_data[x].tasks[y].protected = do_protected_write; 
    29f5:	49 63 c5             	movslq %r13d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    29f8:	be 38 00 00 00       	mov    $0x38,%esi
    29fd:	bf 02 00 00 00       	mov    $0x2,%edi
          thread_data[x].tasks[y].mailboxes = mailboxes;
          // long messages_limit = 20;/*9999999;*/
          
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2a02:	45 31 e4             	xor    %r12d,%r12d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a05:	48 89 c3             	mov    %rax,%rbx
    2a08:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2a0d:	48 8d 05 5c 0e 00 00 	lea    0xe5c(%rip),%rax        # 3870 <do_protected_write>
    2a14:	48 c1 e3 09          	shl    $0x9,%rbx
    2a18:	48 01 dd             	add    %rbx,%rbp
    2a1b:	48 89 85 20 01 00 00 	mov    %rax,0x120(%rbp)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2a22:	e8 79 f9 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2a27:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    2a2c:	48 89 85 70 01 00 00 	mov    %rax,0x170(%rbp)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2a33:	49 89 c6             	mov    %rax,%r14
    2a36:	44 89 6c 24 28       	mov    %r13d,0x28(%rsp)
            // k is group
            int group_of = b / threads_per_group;
            if (k == group_of) {
              // printf("Creating friend mailbox %d\n", b);
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2a3b:	be 08 00 00 00       	mov    $0x8,%esi
    2a40:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2a45:	49 83 c6 38          	add    $0x38,%r14
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2a49:	e8 52 f9 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2a4e:	be 08 00 00 00       	mov    $0x8,%esi
    2a53:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2a58:	49 89 c5             	mov    %rax,%r13
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2a5b:	e8 40 f9 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2a60:	be 80 01 00 00       	mov    $0x180,%esi
    2a65:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2a6a:	48 89 c3             	mov    %rax,%rbx
              struct Data *data = calloc(2, sizeof(struct Data));
    2a6d:	e8 2e f9 ff ff       	call   23a0 <calloc@plt>
    2a72:	31 c9                	xor    %ecx,%ecx
    2a74:	44 89 e2             	mov    %r12d,%edx
    2a77:	bf 01 00 00 00       	mov    $0x1,%edi
    2a7c:	48 89 c5             	mov    %rax,%rbp

              mailboxes[b].lower = &data[0];
    2a7f:	49 89 46 c8          	mov    %rax,-0x38(%r14)
              mailboxes[b].higher = &data[1];
    2a83:	48 8d 80 80 01 00 00 	lea    0x180(%rax),%rax
    2a8a:	48 8d 35 57 4c 00 00 	lea    0x4c57(%rip),%rsi        # 76e8 <_IO_stdin_used+0x6e8>
    2a91:	49 89 46 d0          	mov    %rax,-0x30(%r14)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2a95:	48 8b 05 44 50 00 00 	mov    0x5044(%rip),%rax        # 7ae0 <_IO_stdin_used+0xae0>
    2a9c:	49 89 46 f8          	mov    %rax,-0x8(%r14)
    2aa0:	31 c0                	xor    %eax,%eax
    2aa2:	e8 a9 f9 ff ff       	call   2450 <__printf_chk@plt>
              }
              printf("Creating friend mailbox %d other is %d\n", b, mailboxes[b].other);
              data[0].messages = messages;
              data[1].messages = messages2;
              data[0].messages_limit = messages_limit;
              data[0].messages_count = 0;
    2aa7:	66 0f 6f 05 11 51 00 00 	movdqa 0x5111(%rip),%xmm0        # 7bc0 <_IO_stdin_used+0xbc0>
              data[0].messages = messages;
    2aaf:	4c 89 6d 00          	mov    %r13,0x0(%rbp)
              data[1].messages = messages2;
    2ab3:	48 89 9d 80 01 00 00 	mov    %rbx,0x180(%rbp)
              data[0].messages_count = 0;
    2aba:	0f 29 85 80 00 00 00 	movaps %xmm0,0x80(%rbp)
              data[1].messages_count = 0;
    2ac1:	0f 29 85 00 02 00 00 	movaps %xmm0,0x200(%rbp)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ac8:	45 85 e4             	test   %r12d,%r12d
    2acb:	75 0b                	jne    2ad8 <main+0x4e8>
    2acd:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    2ad3:	e9 63 ff ff ff       	jmp    2a3b <main+0x44b>
            data[0].messages_count = 0;
            data[1].messages_count = 0;
            data[1].messages_limit = messages_limit;
          }

          char *message = malloc(sizeof(char) * 256);
    2ad8:	be 01 00 00 00       	mov    $0x1,%esi
    2add:	bf 00 01 00 00       	mov    $0x100,%edi
    2ae2:	44 8b 6c 24 28       	mov    0x28(%rsp),%r13d
    2ae7:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    2aec:	e8 af f8 ff ff       	call   23a0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2af1:	bf 18 00 00 00       	mov    $0x18,%edi
          char *message = malloc(sizeof(char) * 256);
    2af6:	48 89 c5             	mov    %rax,%rbp
          struct Message *messaged = malloc(sizeof(struct Message));
    2af9:	e8 12 f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2afe:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    2b03:	48 89 ef             	mov    %rbp,%rdi
    2b06:	45 89 e9             	mov    %r13d,%r9d
    2b09:	ba 00 01 00 00       	mov    $0x100,%edx
    2b0e:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    2b13:	be 01 00 00 00       	mov    $0x1,%esi
    2b18:	31 c0                	xor    %eax,%eax
    2b1a:	48 8d 0d ef 4b 00 00 	lea    0x4bef(%rip),%rcx        # 7710 <_IO_stdin_used+0x710>
    2b21:	e8 fa f9 ff ff       	call   2520 <__sprintf_chk@plt>
          memset(message, '\0', 256);
          sprintf(message, "Sending message from thread %d task %d", x, y);
          messaged->message = message;
    2b26:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
          messaged->task_index = y;
    2b2b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2b30:	be 20 00 00 00       	mov    $0x20,%esi
    2b35:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->task_index = y;
    2b3a:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2b3e:	49 63 47 08          	movslq 0x8(%r15),%rax
          messaged->message = message;
    2b42:	49 89 2a             	mov    %rbp,(%r10)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2b45:	49 8b 6f 38          	mov    0x38(%r15),%rbp
          messaged->thread_index = thread_data[x].real_thread_index;
    2b49:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2b4d:	41 8d 45 01          	lea    0x1(%r13),%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2b51:	48 01 eb             	add    %rbp,%rbx
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2b54:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2b57:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2b5d:	89 83 90 01 00 00    	mov    %eax,0x190(%rbx)
          thread_data[x].tasks[y].message = messaged;
    2b63:	4c 89 93 88 01 00 00 	mov    %r10,0x188(%rbx)
          thread_data[x].tasks[y].sending = 1;
    2b6a:	c7 83 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rbx)
          thread_data[x].tasks[y].snapshot_count = 99;
    2b74:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2b7f:	e8 1c f8 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    2b84:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2b8f:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2b96:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    2b9b:	48 8b 00             	mov    (%rax),%rax
    2b9e:	8b 50 04             	mov    0x4(%rax),%edx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2ba1:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2ba8:	89 93 30 01 00 00    	mov    %edx,0x130(%rbx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2bae:	4c 39 f8             	cmp    %r15,%rax
    2bb1:	0f 85 ba 0b 00 00    	jne    3771 <main+0x1181>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2bb7:	66 0f 6f 15 11 50 00 00 	movdqa 0x5011(%rip),%xmm2        # 7bd0 <_IO_stdin_used+0xbd0>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2bbf:	44 89 6b 04          	mov    %r13d,0x4(%rbx)
          thread_data[x].tasks[y].available = 1;
    2bc3:	48 8b 05 1e 50 00 00 	mov    0x501e(%rip),%rax        # 7be8 <_IO_stdin_used+0xbe8>
          thread_data[x].tasks[y].arrived = 0;
    2bca:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
          thread_data[x].tasks[y].worker_count = thread_count;
    2bd4:	c7 83 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rbx)
          thread_data[x].tasks[y].available = 1;
    2bde:	48 89 83 44 01 00 00 	mov    %rax,0x144(%rbx)
          thread_data[x].tasks[y].thread_count = 2;
    2be5:	0f 11 93 34 01 00 00 	movups %xmm2,0x134(%rbx)
          if (y == barrier_count - 1) {
    2bec:	41 83 fd 01          	cmp    $0x1,%r13d
    2bf0:	0f 84 da 00 00 00    	je     2cd0 <main+0x6e0>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2bf6:	45 85 ed             	test   %r13d,%r13d
    2bf9:	0f 84 bb 00 00 00    	je     2cba <main+0x6ca>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    2bff:	48 8d 05 ea 2f 00 00 	lea    0x2fea(%rip),%rax        # 5bf0 <barriered_work>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2c06:	bf 01 00 00 00       	mov    $0x1,%edi
    2c0b:	be 08 00 00 00       	mov    $0x8,%esi
    for (int d = 0 ; d < threads_per_group ; d++) {
    2c10:	49 81 c7 c0 00 00 00 	add    $0xc0,%r15
               thread_data[x].tasks[y].run = barriered_work; 
    2c17:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        thread_data[x].buffers_count = buffers_per_thread;
    2c1e:	41 c7 47 fc 01 00 00 00 	movl   $0x1,-0x4(%r15)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2c26:	e8 75 f7 ff ff       	call   23a0 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2c2b:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    2c30:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2c35:	49 89 47 90          	mov    %rax,-0x70(%r15)
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2c39:	66 0f 6f 64 24 50    	movdqa 0x50(%rsp),%xmm4
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2c3f:	48 8d 14 fb          	lea    (%rbx,%rdi,8),%rdx
    for (int d = 0 ; d < threads_per_group ; d++) {
    2c43:	48 83 c7 02          	add    $0x2,%rdi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2c47:	48 89 10             	mov    %rdx,(%rax)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2c4a:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    2c4f:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2c54:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2c57:	0f 11 a5 18 05 00 00 	movups %xmm4,0x518(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    2c5e:	c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2c68:	48 89 85 28 05 00 00 	mov    %rax,0x528(%rbp)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2c6f:	c7 85 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rbp)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    2c79:	c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2c83:	41 8b 87 44 ff ff ff 	mov    -0xbc(%r15),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2c8a:	c7 85 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2c94:	89 85 30 05 00 00    	mov    %eax,0x530(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
    2c9a:	48 8b 05 47 4f 00 00 	mov    0x4f47(%rip),%rax        # 7be8 <_IO_stdin_used+0xbe8>
    2ca1:	48 89 85 44 05 00 00 	mov    %rax,0x544(%rbp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2ca8:	8b 44 24 08          	mov    0x8(%rsp),%eax
    2cac:	85 c0                	test   %eax,%eax
    2cae:	75 2f                	jne    2cdf <main+0x6ef>
    2cb0:	44 89 64 24 08       	mov    %r12d,0x8(%rsp)
    2cb5:	e9 c2 fb ff ff       	jmp    287c <main+0x28c>
    2cba:	48 8d 05 bf 31 00 00 	lea    0x31bf(%rip),%rax        # 5e80 <barriered_work_ingest_andwork>
            thread_data[x].tasks[y].run = barriered_work; 
    2cc1:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
    2cc8:	45 89 e5             	mov    %r12d,%r13d
    2ccb:	e9 25 fd ff ff       	jmp    29f5 <main+0x405>
    2cd0:	48 8d 05 19 2f 00 00 	lea    0x2f19(%rip),%rax        # 5bf0 <barriered_work>
    2cd7:	41 bc 02 00 00 00    	mov    $0x2,%r12d
    2cdd:	eb e2                	jmp    2cc1 <main+0x6d1>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2cdf:	48 8d 3d a5 46 00 00 	lea    0x46a5(%rip),%rdi        # 738b <_IO_stdin_used+0x38b>
    2ce6:	e8 05 f6 ff ff       	call   22f0 <puts@plt>
    2ceb:	31 d2                	xor    %edx,%edx
    2ced:	48 8d 35 af 46 00 00 	lea    0x46af(%rip),%rsi        # 73a3 <_IO_stdin_used+0x3a3>
    2cf4:	31 c0                	xor    %eax,%eax
    2cf6:	bf 01 00 00 00       	mov    $0x1,%edi
    2cfb:	e8 50 f7 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    2d00:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    2d05:	44 8b 74 24 08       	mov    0x8(%rsp),%r14d
    2d0a:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    2d12:	4c 8d 68 38          	lea    0x38(%rax),%r13
    2d16:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    2d1b:	4d 89 ef             	mov    %r13,%r15
    2d1e:	8b 54 24 20          	mov    0x20(%rsp),%edx
    2d22:	48 8d 35 84 46 00 00 	lea    0x4684(%rip),%rsi        # 73ad <_IO_stdin_used+0x3ad>
    2d29:	31 c0                	xor    %eax,%eax
    2d2b:	45 31 ed             	xor    %r13d,%r13d
    2d2e:	bf 01 00 00 00       	mov    $0x1,%edi
    2d33:	89 d1                	mov    %edx,%ecx
    2d35:	e8 16 f7 ff ff       	call   2450 <__printf_chk@plt>
    2d3a:	44 89 ea             	mov    %r13d,%edx
    2d3d:	48 8d 35 7b 46 00 00 	lea    0x467b(%rip),%rsi        # 73bf <_IO_stdin_used+0x3bf>
    2d44:	31 c0                	xor    %eax,%eax
    2d46:	4c 89 eb             	mov    %r13,%rbx
    2d49:	bf 01 00 00 00       	mov    $0x1,%edi
    2d4e:	48 c1 e3 09          	shl    $0x9,%rbx
    2d52:	45 31 e4             	xor    %r12d,%r12d
      int x = (k * threads_per_group) + d;
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    2d55:	31 ed                	xor    %ebp,%ebp
    2d57:	e8 f4 f6 ff ff       	call   2450 <__printf_chk@plt>
          char * mailbox_kind = calloc(100, sizeof(char));
    2d5c:	be 01 00 00 00       	mov    $0x1,%esi
    2d61:	bf 64 00 00 00       	mov    $0x64,%edi
    2d66:	e8 35 f6 ff ff       	call   23a0 <calloc@plt>
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    2d6b:	49 8b 37             	mov    (%r15),%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
    2d6e:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    2d71:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    2d79:	4c 01 e0             	add    %r12,%rax
    2d7c:	8b 50 30             	mov    0x30(%rax),%edx
    2d7f:	83 fa 02             	cmp    $0x2,%edx
    2d82:	74 4d                	je     2dd1 <main+0x7e1>
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    2d84:	83 fa 01             	cmp    $0x1,%edx
    2d87:	74 62                	je     2deb <main+0x7fb>
    2d89:	44 8b 40 34          	mov    0x34(%rax),%r8d
    2d8d:	89 ea                	mov    %ebp,%edx
    2d8f:	48 8d 35 34 46 00 00 	lea    0x4634(%rip),%rsi        # 73ca <_IO_stdin_used+0x3ca>
    2d96:	31 c0                	xor    %eax,%eax
    2d98:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    2d9d:	49 83 c4 38          	add    $0x38,%r12
    2da1:	e8 aa f6 ff ff       	call   2450 <__printf_chk@plt>
    2da6:	85 ed                	test   %ebp,%ebp
    2da8:	75 05                	jne    2daf <main+0x7bf>
    2daa:	44 89 f5             	mov    %r14d,%ebp
    2dad:	eb ad                	jmp    2d5c <main+0x76c>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2daf:	49 83 c5 01          	add    $0x1,%r13
    2db3:	49 83 fd 03          	cmp    $0x3,%r13
    2db7:	75 81                	jne    2d3a <main+0x74a>
    for (int d = 0 ; d < threads_per_group ; d++) {
    2db9:	8b 44 24 20          	mov    0x20(%rsp),%eax
    2dbd:	49 81 c7 c0 00 00 00 	add    $0xc0,%r15
    2dc4:	85 c0                	test   %eax,%eax
    2dc6:	75 3d                	jne    2e05 <main+0x815>
    2dc8:	89 6c 24 20          	mov    %ebp,0x20(%rsp)
    2dcc:	e9 4d ff ff ff       	jmp    2d1e <main+0x72e>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2dd1:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    2ddb:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    2dde:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    2de6:	4c 01 e0             	add    %r12,%rax
    2de9:	eb 9e                	jmp    2d89 <main+0x799>
    2deb:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    2df1:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    2df8:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    2e00:	4c 01 e0             	add    %r12,%rax
    2e03:	eb 84                	jmp    2d89 <main+0x799>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2e05:	ba 03 00 00 00       	mov    $0x3,%edx
    2e0a:	48 8d 35 d4 45 00 00 	lea    0x45d4(%rip),%rsi        # 73e5 <_IO_stdin_used+0x3e5>
    2e11:	bf 01 00 00 00       	mov    $0x1,%edi
    2e16:	31 c0                	xor    %eax,%eax
    2e18:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    2e1d:	e8 2e f6 ff ff       	call   2450 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2e22:	be 08 00 00 00       	mov    $0x8,%esi
    2e27:	bf 02 00 00 00       	mov    $0x2,%edi
    2e2c:	e8 6f f5 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2e31:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e36:	be 38 00 00 00       	mov    $0x38,%esi
    2e3b:	bf 06 00 00 00       	mov    $0x6,%edi
    my_thread_data[0] = &thread_data[x]; 
    2e40:	4d 8d a6 40 02 00 00 	lea    0x240(%r14),%r12
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2e47:	4c 89 70 08          	mov    %r14,0x8(%rax)


  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2e4b:	49 8d ae 00 03 00 00 	lea    0x300(%r14),%rbp
    thread_data[x].threads = my_thread_data;
    2e52:	49 89 86 58 02 00 00 	mov    %rax,0x258(%r14)
    my_thread_data[0] = &thread_data[x]; 
    2e59:	4c 89 20             	mov    %r12,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2e5c:	49 8b 46 38          	mov    0x38(%r14),%rax
    thread_data[x].thread_count = 2;
    2e60:	41 c7 86 68 02 00 00 02 00 00 00 	movl   $0x2,0x268(%r14)
    thread_data[x].thread_index = 0;
    2e6b:	41 c7 86 44 02 00 00 00 00 00 00 	movl   $0x0,0x244(%r14)
    thread_data[x].task_count = total_barrier_count;
    2e76:	41 c7 86 80 02 00 00 03 00 00 00 	movl   $0x3,0x280(%r14)
    thread_data[n].tasks[0].scheduled = 1;
    2e81:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    2e8b:	49 8b 86 f8 00 00 00 	mov    0xf8(%r14),%rax
    2e92:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e9c:	e8 ff f4 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ea1:	be 38 00 00 00       	mov    $0x38,%esi
    2ea6:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2eab:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2eae:	e8 ed f4 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2eb3:	be 38 00 00 00       	mov    $0x38,%esi
    2eb8:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ebd:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ec2:	e8 d9 f4 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ec7:	be 38 00 00 00       	mov    $0x38,%esi
    2ecc:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ed1:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ed6:	e8 c5 f4 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2edb:	be 08 00 00 00       	mov    $0x8,%esi
    2ee0:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ee5:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2eea:	e8 b1 f4 ff ff       	call   23a0 <calloc@plt>
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2eef:	be 08 00 00 00       	mov    $0x8,%esi
    2ef4:	bf 06 00 00 00       	mov    $0x6,%edi
  thread_data[timer_threadi].type = TIMER;
    2ef9:	41 c7 86 8c 01 00 00 00 00 00 00 	movl   $0x0,0x18c(%r14)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2f04:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    2f07:	48 8b 05 e2 4c 00 00 	mov    0x4ce2(%rip),%rax        # 7bf0 <_IO_stdin_used+0xbf0>
    2f0e:	49 89 86 c0 01 00 00 	mov    %rax,0x1c0(%r14)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2f15:	e8 86 f4 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[n] = &thread_data[n]; 
    2f1a:	49 8d 96 c0 03 00 00 	lea    0x3c0(%r14),%rdx
    2f21:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    2f26:	49 8d 8e 80 01 00 00 	lea    0x180(%r14),%rcx
    2f2d:	48 89 50 28          	mov    %rdx,0x28(%rax)
  }
  thread_data[timer_threadi].threads = my_thread_data;
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    2f31:	48 8b 15 a8 4c 00 00 	mov    0x4ca8(%rip),%rdx        # 7be0 <_IO_stdin_used+0xbe0>
    2f38:	48 8d 35 b5 44 00 00 	lea    0x44b5(%rip),%rsi        # 73f4 <_IO_stdin_used+0x3f4>
    my_thread_data[n] = &thread_data[n]; 
    2f3f:	4c 89 30             	mov    %r14,(%rax)
    2f42:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2f46:	bf 01 00 00 00       	mov    $0x1,%edi
    2f4b:	48 89 48 10          	mov    %rcx,0x10(%rax)
    2f4f:	4c 89 60 18          	mov    %r12,0x18(%rax)
  thread_data[timer_threadi].threads = my_thread_data;
    2f53:	49 89 86 98 01 00 00 	mov    %rax,0x198(%r14)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    2f5a:	49 89 96 a8 01 00 00 	mov    %rdx,0x1a8(%r14)
    2f61:	ba 02 00 00 00       	mov    $0x2,%edx
    my_thread_data[n] = &thread_data[n]; 
    2f66:	48 89 68 20          	mov    %rbp,0x20(%rax)
    2f6a:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    2f6c:	41 c7 86 b0 01 00 00 02 00 00 00 	movl   $0x2,0x1b0(%r14)
  thread_data[timer_threadi].thread_index = 0;
    2f77:	41 c7 86 84 01 00 00 00 00 00 00 	movl   $0x0,0x184(%r14)
    my_thread_data[n] = &thread_data[n]; 
    2f82:	48 89 4c 24 30       	mov    %rcx,0x30(%rsp)
    2f87:	e8 c4 f4 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    2f8c:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2f91:	48 8d 7b 10          	lea    0x10(%rbx),%rdi
    2f95:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    2f9a:	48 8d 15 8f 0a 00 00 	lea    0xa8f(%rip),%rdx        # 3a30 <timer_thread>
    2fa1:	48 83 c6 70          	add    $0x70,%rsi
    2fa5:	e8 c6 f4 ff ff       	call   2470 <pthread_create@plt>
    2faa:	4c 8d 15 87 47 00 00 	lea    0x4787(%rip),%r10        # 7738 <_IO_stdin_used+0x738>
    2fb1:	31 c9                	xor    %ecx,%ecx
    2fb3:	31 d2                	xor    %edx,%edx
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    2fb5:	41 c7 46 0c 01 00 00 00 	movl   $0x1,0xc(%r14)
    2fbd:	4c 89 d6             	mov    %r10,%rsi
    2fc0:	bf 01 00 00 00       	mov    $0x1,%edi
    2fc5:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    2fc7:	41 c7 46 44 01 00 00 00 	movl   $0x1,0x44(%r14)
    2fcf:	e8 7c f4 ff ff       	call   2450 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2fd4:	4c 89 f1             	mov    %r14,%rcx
    2fd7:	4c 89 fe             	mov    %r15,%rsi
    2fda:	48 89 df             	mov    %rbx,%rdi
    2fdd:	4c 8d 0d ac 27 00 00 	lea    0x27ac(%rip),%r9        # 5790 <barriered_thread>
    2fe4:	4c 89 ca             	mov    %r9,%rdx
    2fe7:	e8 84 f4 ff ff       	call   2470 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2fec:	49 8b 96 b0 00 00 00 	mov    0xb0(%r14),%rdx
    2ff3:	48 8b 3b             	mov    (%rbx),%rdi
    2ff6:	be 08 00 00 00       	mov    $0x8,%esi
    2ffb:	e8 e0 f2 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    3000:	4c 8d 15 31 47 00 00 	lea    0x4731(%rip),%r10        # 7738 <_IO_stdin_used+0x738>
    3007:	31 c9                	xor    %ecx,%ecx
    3009:	31 c0                	xor    %eax,%eax
    300b:	4c 89 d6             	mov    %r10,%rsi
    300e:	ba 01 00 00 00       	mov    $0x1,%edx
    3013:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].type = WORKER;
    3018:	41 c7 86 cc 00 00 00 01 00 00 00 	movl   $0x1,0xcc(%r14)
      thread_data[x].running = 1;
    3023:	41 c7 86 04 01 00 00 01 00 00 00 	movl   $0x1,0x104(%r14)
    302e:	e8 1d f4 ff ff       	call   2450 <__printf_chk@plt>
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3033:	49 8d 77 38          	lea    0x38(%r15),%rsi
    3037:	4c 8b 7c 24 40       	mov    0x40(%rsp),%r15
    303c:	4c 8d 0d 4d 27 00 00 	lea    0x274d(%rip),%r9        # 5790 <barriered_thread>
    3043:	4c 89 ca             	mov    %r9,%rdx
    3046:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    304a:	4c 89 f9             	mov    %r15,%rcx
    304d:	e8 1e f4 ff ff       	call   2470 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3052:	49 8b 96 70 01 00 00 	mov    0x170(%r14),%rdx
    3059:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    305d:	be 08 00 00 00       	mov    $0x8,%esi
    3062:	e8 79 f2 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    3067:	48 8b 3d 8a 4b 00 00 	mov    0x4b8a(%rip),%rdi        # 7bf8 <_IO_stdin_used+0xbf8>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    306e:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    3073:	41 c7 86 4c 02 00 00 02 00 00 00 	movl   $0x2,0x24c(%r14)
    thread_data[x].task_count = 0;
    307e:	49 89 be 80 02 00 00 	mov    %rdi,0x280(%r14)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3085:	bf 01 00 00 00       	mov    $0x1,%edi
    308a:	e8 11 f3 ff ff       	call   23a0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    308f:	31 ff                	xor    %edi,%edi
    3091:	be 00 08 00 00       	mov    $0x800,%esi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3096:	49 89 86 98 02 00 00 	mov    %rax,0x298(%r14)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    309d:	e8 0e f4 ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    30a2:	be 08 00 00 00       	mov    $0x8,%esi
    30a7:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    30ac:	41 89 86 a0 02 00 00 	mov    %eax,0x2a0(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    30b3:	e8 e8 f2 ff ff       	call   23a0 <calloc@plt>
    30b8:	ba 03 00 00 00       	mov    $0x3,%edx
    30bd:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    30c2:	41 c7 86 68 02 00 00 02 00 00 00 	movl   $0x2,0x268(%r14)
      my_thread_data[n] = &thread_data[n]; 
    30cd:	4c 89 30             	mov    %r14,(%rax)
    30d0:	48 8d 35 3b 43 00 00 	lea    0x433b(%rip),%rsi        # 7412 <_IO_stdin_used+0x412>
    30d7:	4c 89 78 08          	mov    %r15,0x8(%rax)
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    30db:	41 bf 04 00 00 00    	mov    $0x4,%r15d
    thread_data[x].threads = my_thread_data;
    30e1:	49 89 86 58 02 00 00 	mov    %rax,0x258(%r14)
    30e8:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    30ea:	41 c7 86 44 02 00 00 03 00 00 00 	movl   $0x3,0x244(%r14)
    30f5:	e8 56 f3 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    30fa:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    30ff:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    3103:	4c 89 e1             	mov    %r12,%rcx
    3106:	48 8d 15 93 1e 00 00 	lea    0x1e93(%rip),%rdx        # 4fa0 <io_thread>
    310d:	4c 8d 63 20          	lea    0x20(%rbx),%r12
    3111:	48 81 c6 a8 00 00 00 	add    $0xa8,%rsi
    3118:	e8 53 f3 ff ff       	call   2470 <pthread_create@plt>
    311d:	31 c0                	xor    %eax,%eax
    311f:	ba 04 00 00 00       	mov    $0x4,%edx
    3124:	48 8d 35 fe 42 00 00 	lea    0x42fe(%rip),%rsi        # 7429 <_IO_stdin_used+0x429>
    312b:	bf 01 00 00 00       	mov    $0x1,%edi
    3130:	e8 1b f3 ff ff       	call   2450 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3135:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    313a:	4c 89 e8             	mov    %r13,%rax
    313d:	49 89 dd             	mov    %rbx,%r13
    3140:	48 89 c3             	mov    %rax,%rbx
    3143:	49 81 c6 e0 00 00 00 	add    $0xe0,%r14
    314a:	44 89 fa             	mov    %r15d,%edx
    314d:	48 8d 35 eb 42 00 00 	lea    0x42eb(%rip),%rsi        # 743f <_IO_stdin_used+0x43f>
    3154:	bf 01 00 00 00       	mov    $0x1,%edi
    3159:	31 c0                	xor    %eax,%eax
    315b:	e8 f0 f2 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3160:	be 08 00 00 00       	mov    $0x8,%esi
    3165:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    316a:	48 8b 05 87 4a 00 00 	mov    0x4a87(%rip),%rax        # 7bf8 <_IO_stdin_used+0xbf8>
    thread_data[x].type = EXTERNAL;
    3171:	c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%rbp)
    thread_data[x].task_count = 0;
    3178:	48 89 45 40          	mov    %rax,0x40(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    317c:	e8 1f f2 ff ff       	call   23a0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3181:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3186:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    318b:	c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3195:	48 89 45 50          	mov    %rax,0x50(%rbp)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3199:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    319c:	bf 02 00 00 00       	mov    $0x2,%edi
    31a1:	e8 fa f1 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    31a6:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31ab:	48 89 e9             	mov    %rbp,%rcx
    31ae:	4c 89 e7             	mov    %r12,%rdi
    thread_data[x].threads = my_thread_data;
    31b1:	48 89 45 18          	mov    %rax,0x18(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31b5:	48 8d 15 64 07 00 00 	lea    0x764(%rip),%rdx        # 3920 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    31bc:	49 83 c4 08          	add    $0x8,%r12
    31c0:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
      my_thread_data[n] = &thread_data[n]; 
    31c7:	48 89 30             	mov    %rsi,(%rax)
    31ca:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    thread_data[x].thread_index = x;
    31cf:	44 89 bd 44 ff ff ff 	mov    %r15d,-0xbc(%rbp)
      my_thread_data[n] = &thread_data[n]; 
    31d6:	48 89 70 08          	mov    %rsi,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    31da:	48 8b 05 ff 49 00 00 	mov    0x49ff(%rip),%rax        # 7be0 <_IO_stdin_used+0xbe0>
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31e1:	4c 89 f6             	mov    %r14,%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    31e4:	49 83 c6 38          	add    $0x38,%r14
    thread_data[x].thread_count = thread_count;
    31e8:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31ef:	e8 7c f2 ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    31f4:	48 83 44 24 60 10    	addq   $0x10,0x60(%rsp)
    31fa:	41 83 ff 04          	cmp    $0x4,%r15d
    31fe:	75 0b                	jne    320b <main+0xc1b>
    3200:	41 bf 05 00 00 00    	mov    $0x5,%r15d
    3206:	e9 3f ff ff ff       	jmp    314a <main+0xb5a>
    320b:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3210:	4c 87 eb             	xchg   %r13,%rbx
    3213:	48 8d 2d 42 42 00 00 	lea    0x4242(%rip),%rbp        # 745c <_IO_stdin_used+0x45c>
    321a:	4c 8d 78 04          	lea    0x4(%rax),%r15
    321e:	4c 8d a0 84 04 00 00 	lea    0x484(%rax),%r12
    3225:	41 8b 4f 04          	mov    0x4(%r15),%ecx
    3229:	41 8b 17             	mov    (%r15),%edx
    322c:	48 89 ee             	mov    %rbp,%rsi
    322f:	bf 01 00 00 00       	mov    $0x1,%edi
    3234:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3236:	49 81 c7 c0 00 00 00 	add    $0xc0,%r15
    323d:	e8 0e f2 ff ff       	call   2450 <__printf_chk@plt>
    3242:	4d 39 e7             	cmp    %r12,%r15
    3245:	75 de                	jne    3225 <main+0xc35>
    3247:	48 8d 3d 21 42 00 00 	lea    0x4221(%rip),%rdi        # 746f <_IO_stdin_used+0x46f>
    324e:	45 31 ff             	xor    %r15d,%r15d
    3251:	4c 8d 64 24 70       	lea    0x70(%rsp),%r12
    3256:	e8 95 f0 ff ff       	call   22f0 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    325b:	48 8d 2d 2b 42 00 00 	lea    0x422b(%rip),%rbp        # 748d <_IO_stdin_used+0x48d>
    void * result; 
    pthread_join(thread[x], &result);
    3262:	4a 8b 3c fb          	mov    (%rbx,%r15,8),%rdi
    3266:	4c 89 e6             	mov    %r12,%rsi
    3269:	e8 82 f2 ff ff       	call   24f0 <pthread_join@plt>
    326e:	44 89 fa             	mov    %r15d,%edx
    3271:	48 89 ee             	mov    %rbp,%rsi
    3274:	bf 01 00 00 00       	mov    $0x1,%edi
    3279:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    327b:	49 83 c7 01          	add    $0x1,%r15
    327f:	e8 cc f1 ff ff       	call   2450 <__printf_chk@plt>
    3284:	49 83 ff 06          	cmp    $0x6,%r15
    3288:	75 d8                	jne    3262 <main+0xc72>
    328a:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    328f:	45 31 d2             	xor    %r10d,%r10d
    3292:	45 31 c9             	xor    %r9d,%r9d
    3295:	31 db                	xor    %ebx,%ebx
    3297:	4c 89 54 24 38       	mov    %r10,0x38(%rsp)
    329c:	45 31 db             	xor    %r11d,%r11d
    329f:	49 89 df             	mov    %rbx,%r15
    32a2:	4d 89 cc             	mov    %r9,%r12
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32a5:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
    32af:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    32b4:	c7 44 24 30 00 00 00 00 	movl   $0x0,0x30(%rsp)
    32bc:	bf 0a 00 00 00       	mov    $0xa,%edi
    32c1:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
      if (x % 2 == 1) {
    32c6:	44 8b 74 24 30       	mov    0x30(%rsp),%r14d
    32cb:	e8 00 f0 ff ff       	call   22d0 <putchar@plt>
    32d0:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    32d5:	bf 01 00 00 00       	mov    $0x1,%edi
    32da:	48 8d 35 c0 41 00 00 	lea    0x41c0(%rip),%rsi        # 74a1 <_IO_stdin_used+0x4a1>
    32e1:	41 83 f6 01          	xor    $0x1,%r14d
    32e5:	48 8b 10             	mov    (%rax),%rdx
    32e8:	31 c0                	xor    %eax,%eax
    32ea:	e8 61 f1 ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    32ef:	41 8b 55 08          	mov    0x8(%r13),%edx
    32f3:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    32f8:	85 d2                	test   %edx,%edx
    32fa:	0f 8e 65 04 00 00    	jle    3765 <main+0x1175>
    3300:	48 63 f2             	movslq %edx,%rsi
    3303:	49 8b 45 00          	mov    0x0(%r13),%rax
      long v = 0;
    3307:	31 d2                	xor    %edx,%edx
    3309:	48 c1 e6 09          	shl    $0x9,%rsi
    330d:	48 01 c6             	add    %rax,%rsi
        v += thread_data[me].tasks[n].v;
    3310:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3317:	48 05 00 02 00 00    	add    $0x200,%rax
    331d:	48 39 f0             	cmp    %rsi,%rax
    3320:	75 ee                	jne    3310 <main+0xd20>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3322:	4c 89 f0             	mov    %r14,%rax
    3325:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    332a:	48 f7 d8             	neg    %rax
    332d:	25 c0 00 00 00       	and    $0xc0,%eax
    3332:	48 01 f8             	add    %rdi,%rax
    3335:	48 63 70 40          	movslq 0x40(%rax),%rsi
    3339:	85 f6                	test   %esi,%esi
    333b:	7e 25                	jle    3362 <main+0xd72>
    333d:	48 8b 40 38          	mov    0x38(%rax),%rax
    3341:	48 c1 e6 09          	shl    $0x9,%rsi
    3345:	48 01 c6             	add    %rax,%rsi
    3348:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3350:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3357:	48 05 00 02 00 00    	add    $0x200,%rax
    335d:	48 39 f0             	cmp    %rsi,%rax
    3360:	75 ee                	jne    3350 <main+0xd60>
    3362:	48 8d 35 4d 41 00 00 	lea    0x414d(%rip),%rsi        # 74b6 <_IO_stdin_used+0x4b6>
    3369:	bf 01 00 00 00       	mov    $0x1,%edi
    336e:	31 c0                	xor    %eax,%eax
    3370:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    3375:	e8 d6 f0 ff ff       	call   2450 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    337a:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    337f:	bf 01 00 00 00       	mov    $0x1,%edi
    3384:	48 8b 30             	mov    (%rax),%rsi
    3387:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3391:	48 f7 ee             	imul   %rsi
    3394:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3398:	31 c0                	xor    %eax,%eax
    339a:	48 d1 fa             	sar    %rdx
    339d:	48 29 f2             	sub    %rsi,%rdx
    33a0:	48 8d 35 c1 43 00 00 	lea    0x43c1(%rip),%rsi        # 7768 <_IO_stdin_used+0x768>
    33a7:	e8 a4 f0 ff ff       	call   2450 <__printf_chk@plt>
    33ac:	bf 0a 00 00 00       	mov    $0xa,%edi
    33b1:	e8 1a ef ff ff       	call   22d0 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    33b6:	41 8b 55 08          	mov    0x8(%r13),%edx
    33ba:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    33bf:	85 d2                	test   %edx,%edx
    33c1:	7e 59                	jle    341c <main+0xe2c>
    33c3:	49 8b 45 00          	mov    0x0(%r13),%rax
    33c7:	48 63 fa             	movslq %edx,%rdi
    33ca:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
    33cf:	48 c1 e7 09          	shl    $0x9,%rdi
    33d3:	48 01 c7             	add    %rax,%rdi
    33d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33e0:	48 8b 90 70 01 00 00 	mov    0x170(%rax),%rdx
        total += thread_data[x].tasks[n].n;
    33e7:	4c 03 b8 08 01 00 00 	add    0x108(%rax),%r15
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    33ee:	48 05 00 02 00 00    	add    $0x200,%rax
        ingests += thread_data[x].tasks[n].ingest_count;
    33f4:	48 03 88 68 ff ff ff 	add    -0x98(%rax),%rcx
        sends += thread_data[x].tasks[n].sends;
    33fb:	4c 03 98 78 ff ff ff 	add    -0x88(%rax),%r11
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3402:	48 03 5a 20          	add    0x20(%rdx),%rbx
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3406:	4c 03 62 28          	add    0x28(%rdx),%r12
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    340a:	48 03 5a 58          	add    0x58(%rdx),%rbx
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    340e:	4c 03 62 60          	add    0x60(%rdx),%r12
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3412:	48 39 f8             	cmp    %rdi,%rax
    3415:	75 c9                	jne    33e0 <main+0xdf0>
    3417:	48 89 4c 24 38       	mov    %rcx,0x38(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    341c:	45 31 f6             	xor    %r14d,%r14d
    341f:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    3424:	0f 8e 84 00 00 00    	jle    34ae <main+0xebe>
    342a:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    342f:	4c 89 ef             	mov    %r13,%rdi
    3432:	4c 89 f0             	mov    %r14,%rax
    3435:	49 89 dd             	mov    %rbx,%r13
    3438:	4d 89 e6             	mov    %r12,%r14
    343b:	48 89 fb             	mov    %rdi,%rbx
    343e:	49 89 c4             	mov    %rax,%r12
    3441:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3448:	48 8b 43 58          	mov    0x58(%rbx),%rax
    344c:	4b 8d 14 a4          	lea    (%r12,%r12,4),%rdx
    3450:	48 83 ec 08          	sub    $0x8,%rsp
    3454:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3459:	49 83 c4 01          	add    $0x1,%r12
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    345d:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3461:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3465:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3469:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    346c:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3470:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3473:	48 f7 e5             	mul    %rbp
    3476:	8b 49 20             	mov    0x20(%rcx),%ecx
    3479:	56                   	push   %rsi
    347a:	31 c0                	xor    %eax,%eax
    347c:	48 8d 35 05 43 00 00 	lea    0x4305(%rip),%rsi        # 7788 <_IO_stdin_used+0x788>
    3483:	48 c1 ea 12          	shr    $0x12,%rdx
    3487:	49 89 d1             	mov    %rdx,%r9
    348a:	ba 02 00 00 00       	mov    $0x2,%edx
    348f:	e8 bc ef ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3494:	41 5b                	pop    %r11
    3496:	58                   	pop    %rax
    3497:	4c 39 63 68          	cmp    %r12,0x68(%rbx)
    349b:	7f ab                	jg     3448 <main+0xe58>
    349d:	48 89 d8             	mov    %rbx,%rax
    34a0:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    34a5:	4c 89 eb             	mov    %r13,%rbx
    34a8:	4d 89 f4             	mov    %r14,%r12
    34ab:	49 89 c5             	mov    %rax,%r13
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    34ae:	41 8b b5 84 00 00 00 	mov    0x84(%r13),%esi
    34b5:	85 f6                	test   %esi,%esi
    34b7:	0f 8e 16 01 00 00    	jle    35d3 <main+0xfe3>
    34bd:	4c 89 7c 24 40       	mov    %r15,0x40(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    34c2:	4d 8b 4d 18          	mov    0x18(%r13),%r9
    34c6:	31 d2                	xor    %edx,%edx
    34c8:	4c 89 5c 24 50       	mov    %r11,0x50(%rsp)
    34cd:	48 89 5c 24 60       	mov    %rbx,0x60(%rsp)
    34d2:	4c 89 64 24 68       	mov    %r12,0x68(%rsp)
    34d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    34e0:	49 8b 04 d1          	mov    (%r9,%rdx,8),%rax
    34e4:	89 d3                	mov    %edx,%ebx
    34e6:	4c 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%r15
    34ee:	44 8b 00             	mov    (%rax),%r8d
    34f1:	45 85 c0             	test   %r8d,%r8d
    34f4:	0f 8e b9 00 00 00    	jle    35b3 <main+0xfc3>
    34fa:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    34ff:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3503:	31 f6                	xor    %esi,%esi
    3505:	0f 1f 00             	nopl   (%rax)
    3508:	49 89 f4             	mov    %rsi,%r12
    350b:	45 31 f6             	xor    %r14d,%r14d
    350e:	49 c1 e4 08          	shl    $0x8,%r12
    3512:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    3516:	8b ba 94 00 00 00    	mov    0x94(%rdx),%edi
    351c:	85 ff                	test   %edi,%edi
    351e:	7e 7a                	jle    359a <main+0xfaa>
    3520:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    3525:	0f 1f 00             	nopl   (%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3528:	4c 89 f1             	mov    %r14,%rcx
    352b:	48 83 ec 08          	sub    $0x8,%rsp
    352f:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3534:	49 83 c6 01          	add    $0x1,%r14
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3538:	48 c1 e1 05          	shl    $0x5,%rcx
    353c:	48 03 8a 88 00 00 00 	add    0x88(%rdx),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3543:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3547:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    354b:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    354e:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3552:	4c 2b 01             	sub    (%rcx),%r8
    3555:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3556:	48 f7 e5             	mul    %rbp
    3559:	89 d9                	mov    %ebx,%ecx
    355b:	48 8d 35 76 42 00 00 	lea    0x4276(%rip),%rsi        # 77d8 <_IO_stdin_used+0x7d8>
    3562:	31 c0                	xor    %eax,%eax
    3564:	48 c1 ea 12          	shr    $0x12,%rdx
    3568:	49 89 d1             	mov    %rdx,%r9
    356b:	ba 02 00 00 00       	mov    $0x2,%edx
    3570:	e8 db ee ff ff       	call   2450 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3575:	4d 8b 4d 18          	mov    0x18(%r13),%r9
    3579:	41 58                	pop    %r8
    357b:	41 5a                	pop    %r10
    357d:	4b 8b 04 39          	mov    (%r9,%r15,1),%rax
    3581:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3585:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    3589:	44 39 b2 94 00 00 00 	cmp    %r14d,0x94(%rdx)
    3590:	7f 96                	jg     3528 <main+0xf38>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3592:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3597:	44 8b 00             	mov    (%rax),%r8d
    359a:	48 83 c6 01          	add    $0x1,%rsi
    359e:	41 39 f0             	cmp    %esi,%r8d
    35a1:	0f 8f 61 ff ff ff    	jg     3508 <main+0xf18>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    35a7:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    35ac:	41 8b b5 84 00 00 00 	mov    0x84(%r13),%esi
    35b3:	48 83 c2 01          	add    $0x1,%rdx
    35b7:	39 d6                	cmp    %edx,%esi
    35b9:	0f 8f 21 ff ff ff    	jg     34e0 <main+0xef0>
    35bf:	4c 8b 7c 24 40       	mov    0x40(%rsp),%r15
    35c4:	4c 8b 5c 24 50       	mov    0x50(%rsp),%r11
    35c9:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
    35ce:	4c 8b 64 24 68       	mov    0x68(%rsp),%r12
    for (int d = 0 ; d < threads_per_group ; d++) {
    35d3:	8b 44 24 30          	mov    0x30(%rsp),%eax
    35d7:	48 83 44 24 28 18    	addq   $0x18,0x28(%rsp)
    35dd:	49 81 c5 c0 00 00 00 	add    $0xc0,%r13
    35e4:	85 c0                	test   %eax,%eax
    35e6:	75 0d                	jne    35f5 <main+0x1005>
    35e8:	8b 44 24 20          	mov    0x20(%rsp),%eax
    35ec:	89 44 24 30          	mov    %eax,0x30(%rsp)
    35f0:	e9 c7 fc ff ff       	jmp    32bc <main+0xccc>
    35f5:	4c 8b 54 24 38       	mov    0x38(%rsp),%r10
    35fa:	4c 89 fa             	mov    %r15,%rdx
    35fd:	bf 01 00 00 00       	mov    $0x1,%edi
    3602:	31 c0                	xor    %eax,%eax
    3604:	48 8d 35 b8 3e 00 00 	lea    0x3eb8(%rip),%rsi        # 74c3 <_IO_stdin_used+0x4c3>
    360b:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3610:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
    361a:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    361f:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    3624:	4c 89 fb             	mov    %r15,%rbx
    3627:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
  printf("Total Requests per second %ld\n", total / DURATION);
    362c:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3630:	e8 1b ee ff ff       	call   2450 <__printf_chk@plt>
    3635:	bf 0a 00 00 00       	mov    $0xa,%edi
    363a:	e8 91 ec ff ff       	call   22d0 <putchar@plt>
    363f:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3644:	bf 01 00 00 00       	mov    $0x1,%edi
    3649:	48 8d 35 e0 41 00 00 	lea    0x41e0(%rip),%rsi        # 7830 <_IO_stdin_used+0x830>
    3650:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3654:	31 c0                	xor    %eax,%eax
    3656:	e8 f5 ed ff ff       	call   2450 <__printf_chk@plt>
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    365b:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    3660:	bf 01 00 00 00       	mov    $0x1,%edi
    3665:	48 8d 35 ec 41 00 00 	lea    0x41ec(%rip),%rsi        # 7858 <_IO_stdin_used+0x858>
    366c:	4c 89 d0             	mov    %r10,%rax
    366f:	49 c1 fa 3f          	sar    $0x3f,%r10
    3673:	48 f7 ed             	imul   %rbp
    3676:	31 c0                	xor    %eax,%eax
    3678:	48 d1 fa             	sar    %rdx
    367b:	4c 29 d2             	sub    %r10,%rdx
    367e:	e8 cd ed ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3683:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    3688:	bf 01 00 00 00       	mov    $0x1,%edi
    368d:	48 8d 35 f4 41 00 00 	lea    0x41f4(%rip),%rsi        # 7888 <_IO_stdin_used+0x888>
    3694:	4c 89 d8             	mov    %r11,%rax
    3697:	49 c1 fb 3f          	sar    $0x3f,%r11
    369b:	48 f7 ed             	imul   %rbp
    369e:	31 c0                	xor    %eax,%eax
    36a0:	48 d1 fa             	sar    %rdx
    36a3:	4c 29 da             	sub    %r11,%rdx
    36a6:	e8 a5 ed ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    36ab:	4c 89 f8             	mov    %r15,%rax
    36ae:	bf 01 00 00 00       	mov    $0x1,%edi
    36b3:	48 8d 35 fe 41 00 00 	lea    0x41fe(%rip),%rsi        # 78b8 <_IO_stdin_used+0x8b8>
    36ba:	48 f7 ed             	imul   %rbp
    36bd:	31 c0                	xor    %eax,%eax
    36bf:	48 d1 fa             	sar    %rdx
    36c2:	48 29 da             	sub    %rbx,%rdx
    36c5:	e8 86 ed ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    36ca:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    36cf:	bf 01 00 00 00       	mov    $0x1,%edi
    36d4:	48 8d 35 fc 3d 00 00 	lea    0x3dfc(%rip),%rsi        # 74d7 <_IO_stdin_used+0x4d7>
    36db:	48 89 c8             	mov    %rcx,%rax
    36de:	48 c1 f9 3f          	sar    $0x3f,%rcx
    36e2:	48 f7 ed             	imul   %rbp
    36e5:	31 c0                	xor    %eax,%eax
    36e7:	48 d1 fa             	sar    %rdx
    36ea:	48 29 ca             	sub    %rcx,%rdx
    36ed:	e8 5e ed ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    36f2:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    36f7:	bf 01 00 00 00       	mov    $0x1,%edi
    36fc:	48 8d 35 e5 3d 00 00 	lea    0x3de5(%rip),%rsi        # 74e8 <_IO_stdin_used+0x4e8>
    3703:	4c 89 c8             	mov    %r9,%rax
    3706:	49 c1 f9 3f          	sar    $0x3f,%r9
    370a:	48 f7 ed             	imul   %rbp
    370d:	48 d1 fa             	sar    %rdx
    3710:	4c 29 ca             	sub    %r9,%rdx
    3713:	31 c0                	xor    %eax,%eax
    3715:	e8 36 ed ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    371a:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    371f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3728:	75 42                	jne    376c <main+0x117c>
    372a:	48 81 c4 88 00 00 00 	add    $0x88,%rsp
    3731:	31 c0                	xor    %eax,%eax
    3733:	5b                   	pop    %rbx
    3734:	5d                   	pop    %rbp
    3735:	41 5c                	pop    %r12
    3737:	41 5d                	pop    %r13
    3739:	41 5e                	pop    %r14
    373b:	41 5f                	pop    %r15
    373d:	c3                   	ret
        thread_data[x].protected_state = &protected_state[k];
    373e:	48 8b 7c 24 48       	mov    0x48(%rsp),%rdi
        other = abs(x - 1) % total_threads;
    3743:	31 db                	xor    %ebx,%ebx
        thread_data[x].thread_index = 1;
    3745:	c7 80 c4 00 00 00 01 00 00 00 	movl   $0x1,0xc4(%rax)
        thread_data[x].protected_state = &protected_state[k];
    374f:	48 89 b8 08 01 00 00 	mov    %rdi,0x108(%rax)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    3756:	49 8d 44 24 08       	lea    0x8(%r12),%rax
    375b:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    3760:	e9 88 f1 ff ff       	jmp    28ed <main+0x2fd>
      long v = 0;
    3765:	31 d2                	xor    %edx,%edx
    3767:	e9 b6 fb ff ff       	jmp    3322 <main+0xd32>
}
    376c:	e8 bf eb ff ff       	call   2330 <__stack_chk_fail@plt>
            exit(1);
    3771:	bf 01 00 00 00       	mov    $0x1,%edi
    3776:	e8 25 ed ff ff       	call   24a0 <exit@plt>
    377b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003780 <_start>:
    3780:	f3 0f 1e fa          	endbr64
    3784:	31 ed                	xor    %ebp,%ebp
    3786:	49 89 d1             	mov    %rdx,%r9
    3789:	5e                   	pop    %rsi
    378a:	48 89 e2             	mov    %rsp,%rdx
    378d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3791:	50                   	push   %rax
    3792:	54                   	push   %rsp
    3793:	45 31 c0             	xor    %r8d,%r8d
    3796:	31 c9                	xor    %ecx,%ecx
    3798:	48 8d 3d 51 ee ff ff 	lea    -0x11af(%rip),%rdi        # 25f0 <main>
    379f:	ff 15 33 68 00 00    	call   *0x6833(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    37a5:	f4                   	hlt
    37a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000037b0 <deregister_tm_clones>:
    37b0:	48 8d 3d 69 68 00 00 	lea    0x6869(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    37b7:	48 8d 05 62 68 00 00 	lea    0x6862(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    37be:	48 39 f8             	cmp    %rdi,%rax
    37c1:	74 15                	je     37d8 <deregister_tm_clones+0x28>
    37c3:	48 8b 05 16 68 00 00 	mov    0x6816(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    37ca:	48 85 c0             	test   %rax,%rax
    37cd:	74 09                	je     37d8 <deregister_tm_clones+0x28>
    37cf:	ff e0                	jmp    *%rax
    37d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    37d8:	c3                   	ret
    37d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037e0 <register_tm_clones>:
    37e0:	48 8d 3d 39 68 00 00 	lea    0x6839(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    37e7:	48 8d 35 32 68 00 00 	lea    0x6832(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    37ee:	48 29 fe             	sub    %rdi,%rsi
    37f1:	48 89 f0             	mov    %rsi,%rax
    37f4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    37f8:	48 c1 f8 03          	sar    $0x3,%rax
    37fc:	48 01 c6             	add    %rax,%rsi
    37ff:	48 d1 fe             	sar    %rsi
    3802:	74 14                	je     3818 <register_tm_clones+0x38>
    3804:	48 8b 05 e5 67 00 00 	mov    0x67e5(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    380b:	48 85 c0             	test   %rax,%rax
    380e:	74 08                	je     3818 <register_tm_clones+0x38>
    3810:	ff e0                	jmp    *%rax
    3812:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3818:	c3                   	ret
    3819:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003820 <__do_global_dtors_aux>:
    3820:	f3 0f 1e fa          	endbr64
    3824:	80 3d fd 67 00 00 00 	cmpb   $0x0,0x67fd(%rip)        # a028 <completed.0>
    382b:	75 2b                	jne    3858 <__do_global_dtors_aux+0x38>
    382d:	55                   	push   %rbp
    382e:	48 83 3d c2 67 00 00 00 	cmpq   $0x0,0x67c2(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3836:	48 89 e5             	mov    %rsp,%rbp
    3839:	74 0c                	je     3847 <__do_global_dtors_aux+0x27>
    383b:	48 8b 3d c6 67 00 00 	mov    0x67c6(%rip),%rdi        # a008 <__dso_handle>
    3842:	e8 69 ea ff ff       	call   22b0 <__cxa_finalize@plt>
    3847:	e8 64 ff ff ff       	call   37b0 <deregister_tm_clones>
    384c:	c6 05 d5 67 00 00 01 	movb   $0x1,0x67d5(%rip)        # a028 <completed.0>
    3853:	5d                   	pop    %rbp
    3854:	c3                   	ret
    3855:	0f 1f 00             	nopl   (%rax)
    3858:	c3                   	ret
    3859:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003860 <frame_dummy>:
    3860:	f3 0f 1e fa          	endbr64
    3864:	e9 77 ff ff ff       	jmp    37e0 <register_tm_clones>
    3869:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003870 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3870:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3874:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    387b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    387f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3887:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    388b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    388f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3896:	48 85 c9             	test   %rcx,%rcx
    3899:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    38a0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    38a4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    38a8:	31 c0                	xor    %eax,%eax
    38aa:	c3                   	ret
    38ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000038b0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    38b0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    38b4:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    38bb:	85 c9                	test   %ecx,%ecx
    38bd:	7e 4f                	jle    390e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    38bf:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    38c6:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    38cd:	48 c1 e1 09          	shl    $0x9,%rcx
    38d1:	48 8b 50 18          	mov    0x18(%rax),%rdx
    38d5:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    38d9:	48 8b 70 38          	mov    0x38(%rax),%rsi
    38dd:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    38df:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    38e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    38e8:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    38f0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    38f8:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3903:	48 05 00 02 00 00    	add    $0x200,%rax
    3909:	48 39 c1             	cmp    %rax,%rcx
    390c:	75 da                	jne    38e8 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    390e:	0f ae f8             	sfence
}
    3911:	31 c0                	xor    %eax,%eax
    3913:	c3                   	ret
    3914:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    391f:	90                   	nop

0000000000003920 <external_thread>:
void * external_thread(void *arg) {
    3920:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3924:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    3928:	0f 85 fb 00 00 00    	jne    3a29 <external_thread+0x109>
void * external_thread(void *arg) {
    392e:	41 57                	push   %r15
    3930:	49 89 ff             	mov    %rdi,%r15
    3933:	41 56                	push   %r14
    3935:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    3937:	4c 8d 2d c6 36 00 00 	lea    0x36c6(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    393e:	41 54                	push   %r12
    3940:	55                   	push   %rbp
    3941:	53                   	push   %rbx
    3942:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    3946:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    394c:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    3950:	85 c9                	test   %ecx,%ecx
    3952:	7e 6e                	jle    39c2 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3954:	45 31 e4             	xor    %r12d,%r12d
    3957:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3960:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    3968:	31 db                	xor    %ebx,%ebx
    396a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    396e:	48 8b 06             	mov    (%rsi),%rax
    3971:	8b 10                	mov    (%rax),%edx
    3973:	85 d2                	test   %edx,%edx
    3975:	7e 2a                	jle    39a1 <external_thread+0x81>
    3977:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    397b:	48 89 dd             	mov    %rbx,%rbp
    397e:	48 c1 e5 08          	shl    $0x8,%rbp
    3982:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    3986:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    398d:	45 85 c0             	test   %r8d,%r8d
    3990:	74 36                	je     39c8 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3992:	48 83 c3 01          	add    $0x1,%rbx
    3996:	39 da                	cmp    %ebx,%edx
    3998:	7f e1                	jg     397b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    399a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    39a1:	49 83 c4 01          	add    $0x1,%r12
    39a5:	44 39 e1             	cmp    %r12d,%ecx
    39a8:	7f b6                	jg     3960 <external_thread+0x40>
  while (data->running == 1) {
    39aa:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    39af:	74 9f                	je     3950 <external_thread+0x30>
}
    39b1:	48 83 c4 08          	add    $0x8,%rsp
    39b5:	31 c0                	xor    %eax,%eax
    39b7:	5b                   	pop    %rbx
    39b8:	5d                   	pop    %rbp
    39b9:	41 5c                	pop    %r12
    39bb:	41 5d                	pop    %r13
    39bd:	41 5e                	pop    %r14
    39bf:	41 5f                	pop    %r15
    39c1:	c3                   	ret
  while (data->running == 1) {
    39c2:	eb fe                	jmp    39c2 <external_thread+0xa2>
    39c4:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    39c8:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    39cb:	48 8b 06             	mov    (%rsi),%rax
    39ce:	48 8b 78 08          	mov    0x8(%rax),%rdi
    39d2:	48 01 ef             	add    %rbp,%rdi
    39d5:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    39dc:	48 c1 e6 05          	shl    $0x5,%rsi
    39e0:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    39e7:	bf 04 00 00 00       	mov    $0x4,%edi
    39ec:	e8 1f e9 ff ff       	call   2310 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    39f1:	49 8b 47 50          	mov    0x50(%r15),%rax
    39f5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    39f9:	48 8b 40 08          	mov    0x8(%rax),%rax
    39fd:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    3a08:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3a0b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    3a0f:	48 83 c3 01          	add    $0x1,%rbx
    3a13:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3a17:	48 8b 06             	mov    (%rsi),%rax
    3a1a:	8b 10                	mov    (%rax),%edx
    3a1c:	39 da                	cmp    %ebx,%edx
    3a1e:	0f 8f 53 ff ff ff    	jg     3977 <external_thread+0x57>
    3a24:	e9 71 ff ff ff       	jmp    399a <external_thread+0x7a>
}
    3a29:	31 c0                	xor    %eax,%eax
    3a2b:	c3                   	ret
    3a2c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003a30 <timer_thread>:
void* timer_thread(void *arg) {
    3a30:	f3 0f 1e fa          	endbr64
    3a34:	41 57                	push   %r15
    3a36:	48 8d 35 d3 35 00 00 	lea    0x35d3(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3a3d:	41 56                	push   %r14
    3a3f:	41 55                	push   %r13
    3a41:	41 54                	push   %r12
    3a43:	55                   	push   %rbp
    3a44:	48 89 fd             	mov    %rdi,%rbp
    3a47:	53                   	push   %rbx
    3a48:	48 83 ec 58          	sub    $0x58,%rsp
    3a4c:	8b 57 04             	mov    0x4(%rdi),%edx
    3a4f:	bf 01 00 00 00       	mov    $0x1,%edi
    3a54:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3a5d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3a62:	31 c0                	xor    %eax,%eax
    3a64:	e8 e7 e9 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3a69:	66 0f 6f 05 5f 40 00 00 	movdqa 0x405f(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    3a71:	ba 88 13 00 00       	mov    $0x1388,%edx
    3a76:	31 c0                	xor    %eax,%eax
    3a78:	48 8d 35 a3 35 00 00 	lea    0x35a3(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3a7f:	bf 01 00 00 00       	mov    $0x1,%edi
    3a84:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3a89:	e8 c2 e9 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3a8e:	44 8b 65 44          	mov    0x44(%rbp),%r12d
    3a92:	45 85 e4             	test   %r12d,%r12d
    3a95:	0f 84 a3 00 00 00    	je     3b3e <timer_thread+0x10e>
  int n = 0;
    3a9b:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    3a9e:	45 31 e4             	xor    %r12d,%r12d
    3aa1:	49 89 e6             	mov    %rsp,%r14
    y++;
    3aa4:	31 db                	xor    %ebx,%ebx
    3aa6:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    3aab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    nanosleep(&preempt , &rem2);
    3ab0:	4c 89 ef             	mov    %r13,%rdi
    3ab3:	4c 89 f6             	mov    %r14,%rsi
    n++;
    3ab6:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3aba:	e8 91 e8 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3abf:	48 63 45 30          	movslq 0x30(%rbp),%rax
    y++;
    3ac3:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3ac8:	85 c0                	test   %eax,%eax
    3aca:	7e 49                	jle    3b15 <timer_thread+0xe5>
    3acc:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3ad0:	49 c1 e4 09          	shl    $0x9,%r12
    3ad4:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3ad8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3ae0:	4c 8b 11             	mov    (%rcx),%r10
    3ae3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3ae5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3ae9:	99                   	cltd
    3aea:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3aee:	49 8b 72 38          	mov    0x38(%r10),%rsi
    3af2:	48 63 d2             	movslq %edx,%rdx
    3af5:	48 c1 e2 09          	shl    $0x9,%rdx
    3af9:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3b04:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3b10:	49 39 c8             	cmp    %rcx,%r8
    3b13:	75 cb                	jne    3ae0 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    3b15:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3b18:	48 8b 45 18          	mov    0x18(%rbp),%rax
  while (data->running && n < times) {
    3b1c:	44 8b 45 44          	mov    0x44(%rbp),%r8d
    if (y >= data->threads[0]->task_count) {
    3b20:	48 8b 00             	mov    (%rax),%rax
    y++;
    3b23:	39 78 40             	cmp    %edi,0x40(%rax)
    3b26:	0f 4e fb             	cmovle %ebx,%edi
    3b29:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3b2c:	45 85 c0             	test   %r8d,%r8d
    3b2f:	74 0d                	je     3b3e <timer_thread+0x10e>
    3b31:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    3b38:	0f 85 72 ff ff ff    	jne    3ab0 <timer_thread+0x80>
    3b3e:	48 8d 3d f3 34 00 00 	lea    0x34f3(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3b45:	e8 a6 e7 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3b4a:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    3b4e:	85 d2                	test   %edx,%edx
    3b50:	7e 73                	jle    3bc5 <timer_thread+0x195>
    for (int y = 0 ; y < data->task_count ; y++) {
    3b52:	48 63 45 40          	movslq 0x40(%rbp),%rax
    3b56:	85 c0                	test   %eax,%eax
    3b58:	7e 6b                	jle    3bc5 <timer_thread+0x195>
    3b5a:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3b5e:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    3b62:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3b6a:	31 c9                	xor    %ecx,%ecx
    3b6c:	48 89 c6             	mov    %rax,%rsi
    3b6f:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3b73:	48 8b 40 38          	mov    0x38(%rax),%rax
    3b77:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    3b7b:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3b81:	74 1d                	je     3ba0 <timer_thread+0x170>
    3b83:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3b8d:	48 05 00 02 00 00    	add    $0x200,%rax
    3b93:	48 39 c2             	cmp    %rax,%rdx
    3b96:	74 24                	je     3bbc <timer_thread+0x18c>
    3b98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->threads[x]->tasks[y].sending = 0;
    3ba0:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3baa:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3bb0:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3bb7:	48 39 c2             	cmp    %rax,%rdx
    3bba:	75 e4                	jne    3ba0 <timer_thread+0x170>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3bbc:	48 83 c1 08          	add    $0x8,%rcx
    3bc0:	48 39 cf             	cmp    %rcx,%rdi
    3bc3:	75 aa                	jne    3b6f <timer_thread+0x13f>
  asm volatile ("mfence" ::: "memory");
    3bc5:	0f ae f0             	mfence
  struct timespec drain = {
    3bc8:	66 0f 6f 05 10 3f 00 00 	movdqa 0x3f10(%rip),%xmm0        # 7ae0 <_IO_stdin_used+0xae0>
    3bd0:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bd5:	48 63 45 28          	movslq 0x28(%rbp),%rax
    y++;
    3bd9:	45 8d 44 24 01       	lea    0x1(%r12),%r8d
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bde:	85 c0                	test   %eax,%eax
    3be0:	7e 4b                	jle    3c2d <timer_thread+0x1fd>
    3be2:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3be6:	4d 63 e4             	movslq %r12d,%r12
    3be9:	49 c1 e4 09          	shl    $0x9,%r12
    3bed:	48 8d 3c c1          	lea    (%rcx,%rax,8),%rdi
    3bf1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3bf8:	48 8b 19             	mov    (%rcx),%rbx
    3bfb:	44 89 c0             	mov    %r8d,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bfe:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3c02:	99                   	cltd
    3c03:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3c06:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    3c0a:	48 63 d2             	movslq %edx,%rdx
    3c0d:	48 c1 e2 09          	shl    $0x9,%rdx
    3c11:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3c1c:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c28:	48 39 cf             	cmp    %rcx,%rdi
    3c2b:	75 cb                	jne    3bf8 <timer_thread+0x1c8>
    asm volatile ("mfence" ::: "memory");
    3c2d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3c30:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3c34:	8b 4d 30             	mov    0x30(%rbp),%ecx
    y++;
    3c37:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3c3a:	48 8b 07             	mov    (%rdi),%rax
    y++;
    3c3d:	44 39 40 40          	cmp    %r8d,0x40(%rax)
    3c41:	45 0f 4f e0          	cmovg  %r8d,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3c45:	85 c9                	test   %ecx,%ecx
    3c47:	0f 8e 0d 01 00 00    	jle    3d5a <timer_thread+0x32a>
    3c4d:	45 31 ff             	xor    %r15d,%r15d
    int all_empty = 1;
    3c50:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    3c56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int y = 0 ; y < 2 ; y++) {
    3c60:	31 db                	xor    %ebx,%ebx
    3c62:	45 89 fd             	mov    %r15d,%r13d
    3c65:	4e 8d 34 fd 00 00 00 00 	lea    0x0(,%r15,8),%r14
    3c6d:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3c6f:	85 c9                	test   %ecx,%ecx
    3c71:	0f 8e 91 00 00 00    	jle    3d08 <timer_thread+0x2d8>
    3c77:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3c7b:	4a 8b 14 37          	mov    (%rdi,%r14,1),%rdx
    3c7f:	48 89 d8             	mov    %rbx,%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3c82:	45 31 c0             	xor    %r8d,%r8d
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3c85:	48 c1 e0 09          	shl    $0x9,%rax
    3c89:	48 03 42 38          	add    0x38(%rdx),%rax
    3c8d:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    3c94:	eb 1c                	jmp    3cb2 <timer_thread+0x282>
    3c96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3ca0:	48 85 d2             	test   %rdx,%rdx
    3ca3:	7f 27                	jg     3ccc <timer_thread+0x29c>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3ca5:	41 83 c0 01          	add    $0x1,%r8d
    3ca9:	48 83 c0 38          	add    $0x38,%rax
    3cad:	41 39 c8             	cmp    %ecx,%r8d
    3cb0:	74 7e                	je     3d30 <timer_thread+0x300>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3cb2:	48 8b 10             	mov    (%rax),%rdx
    3cb5:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    3cbc:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3cc0:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    3cc7:	4d 85 c9             	test   %r9,%r9
    3cca:	7e d4                	jle    3ca0 <timer_thread+0x270>
    3ccc:	48 83 ec 08          	sub    $0x8,%rsp
    3cd0:	89 f1                	mov    %esi,%ecx
    3cd2:	bf 01 00 00 00       	mov    $0x1,%edi
    3cd7:	31 c0                	xor    %eax,%eax
    3cd9:	52                   	push   %rdx
    3cda:	48 8d 35 7c 33 00 00 	lea    0x337c(%rip),%rsi        # 705d <_IO_stdin_used+0x5d>
    3ce1:	44 89 ea             	mov    %r13d,%edx
    3ce4:	e8 67 e7 ff ff       	call   2450 <__printf_chk@plt>
      for (int y = 0 ; y < 2 ; y++) {
    3ce9:	5a                   	pop    %rdx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3cea:	8b 4d 30             	mov    0x30(%rbp),%ecx
      for (int y = 0 ; y < 2 ; y++) {
    3ced:	5e                   	pop    %rsi
    3cee:	48 83 fb 01          	cmp    $0x1,%rbx
    3cf2:	74 54                	je     3d48 <timer_thread+0x318>
    3cf4:	48 83 c3 01          	add    $0x1,%rbx
    3cf8:	45 31 db             	xor    %r11d,%r11d
    3cfb:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3cfd:	85 c9                	test   %ecx,%ecx
    3cff:	0f 8f 72 ff ff ff    	jg     3c77 <timer_thread+0x247>
    3d05:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3d08:	49 83 c7 01          	add    $0x1,%r15
    3d0c:	44 39 f9             	cmp    %r15d,%ecx
    3d0f:	0f 8f 4b ff ff ff    	jg     3c60 <timer_thread+0x230>
    if (all_empty == 1) {
    3d15:	41 83 fb 01          	cmp    $0x1,%r11d
    3d19:	74 3f                	je     3d5a <timer_thread+0x32a>
      nanosleep(&drain , &drainrem);
    3d1b:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3d20:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3d25:	e8 26 e6 ff ff       	call   2350 <nanosleep@plt>
    3d2a:	e9 a6 fe ff ff       	jmp    3bd5 <timer_thread+0x1a5>
    3d2f:	90                   	nop
      for (int y = 0 ; y < 2 ; y++) {
    3d30:	48 83 fb 01          	cmp    $0x1,%rbx
    3d34:	74 d2                	je     3d08 <timer_thread+0x2d8>
    3d36:	48 83 c3 01          	add    $0x1,%rbx
    3d3a:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3d3c:	e9 3a ff ff ff       	jmp    3c7b <timer_thread+0x24b>
    3d41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3d48:	49 83 c7 01          	add    $0x1,%r15
    3d4c:	45 31 db             	xor    %r11d,%r11d
    3d4f:	44 39 f9             	cmp    %r15d,%ecx
    3d52:	0f 8f 08 ff ff ff    	jg     3c60 <timer_thread+0x230>
    3d58:	eb bb                	jmp    3d15 <timer_thread+0x2e5>
    3d5a:	48 8d 3d f3 32 00 00 	lea    0x32f3(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3d61:	e8 8a e5 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3d66:	8b 7d 44             	mov    0x44(%rbp),%edi
    3d69:	85 ff                	test   %edi,%edi
    3d6b:	0f 84 ed 00 00 00    	je     3e5e <timer_thread+0x42e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d71:	8b 45 2c             	mov    0x2c(%rbp),%eax
    3d74:	31 db                	xor    %ebx,%ebx
    3d76:	4c 8d 25 f7 32 00 00 	lea    0x32f7(%rip),%r12        # 7074 <_IO_stdin_used+0x74>
    3d7d:	4c 8d 2d 0b 33 00 00 	lea    0x330b(%rip),%r13        # 708f <_IO_stdin_used+0x8f>
    3d84:	85 c0                	test   %eax,%eax
    3d86:	7e 3b                	jle    3dc3 <timer_thread+0x393>
    3d88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3d90:	31 c0                	xor    %eax,%eax
    3d92:	89 da                	mov    %ebx,%edx
    3d94:	4c 89 e6             	mov    %r12,%rsi
    3d97:	bf 01 00 00 00       	mov    $0x1,%edi
    3d9c:	e8 af e6 ff ff       	call   2450 <__printf_chk@plt>
      data->threads[x]->running = 0;
    3da1:	48 8b 45 18          	mov    0x18(%rbp),%rax
    3da5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    3da9:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    3dad:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    3db4:	0f 84 d1 00 00 00    	je     3e8b <timer_thread+0x45b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3dba:	48 83 c3 01          	add    $0x1,%rbx
    3dbe:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    3dc1:	7f cd                	jg     3d90 <timer_thread+0x360>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3dc3:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    3dc7:	85 d2                	test   %edx,%edx
    3dc9:	7e 7d                	jle    3e48 <timer_thread+0x418>
      for (int y = 0 ; y < data->task_count ; y++) {
    3dcb:	8b 45 40             	mov    0x40(%rbp),%eax
    3dce:	85 c0                	test   %eax,%eax
    3dd0:	7e 76                	jle    3e48 <timer_thread+0x418>
    3dd2:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    3dd5:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    3dd9:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3de1:	31 c9                	xor    %ecx,%ecx
    3de3:	48 c1 e6 09          	shl    $0x9,%rsi
    3de7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3df0:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3df4:	48 8b 40 38          	mov    0x38(%rax),%rax
    3df8:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3dfc:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3e02:	74 1c                	je     3e20 <timer_thread+0x3f0>
    3e04:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3e0e:	48 05 00 02 00 00    	add    $0x200,%rax
    3e14:	48 39 d0             	cmp    %rdx,%rax
    3e17:	74 26                	je     3e3f <timer_thread+0x40f>
    3e19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3e20:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3e2a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3e30:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3e3a:	48 39 d0             	cmp    %rdx,%rax
    3e3d:	75 e1                	jne    3e20 <timer_thread+0x3f0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3e3f:	48 83 c1 08          	add    $0x8,%rcx
    3e43:	48 39 f9             	cmp    %rdi,%rcx
    3e46:	75 a8                	jne    3df0 <timer_thread+0x3c0>
    asm volatile ("mfence" ::: "memory");
    3e48:	0f ae f0             	mfence
    3e4b:	48 8d 3d 4f 32 00 00 	lea    0x324f(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    3e52:	e8 99 e4 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3e57:	c7 45 44 00 00 00 00 	movl   $0x0,0x44(%rbp)
    3e5e:	48 8d 3d 43 32 00 00 	lea    0x3243(%rip),%rdi        # 70a8 <_IO_stdin_used+0xa8>
    3e65:	e8 86 e4 ff ff       	call   22f0 <puts@plt>
}
    3e6a:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3e6f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3e78:	75 40                	jne    3eba <timer_thread+0x48a>
    3e7a:	48 83 c4 58          	add    $0x58,%rsp
    3e7e:	31 c0                	xor    %eax,%eax
    3e80:	5b                   	pop    %rbx
    3e81:	5d                   	pop    %rbp
    3e82:	41 5c                	pop    %r12
    3e84:	41 5d                	pop    %r13
    3e86:	41 5e                	pop    %r14
    3e88:	41 5f                	pop    %r15
    3e8a:	c3                   	ret
    3e8b:	4c 89 ef             	mov    %r13,%rdi
    3e8e:	e8 5d e4 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3e93:	48 8b 45 18          	mov    0x18(%rbp),%rax
    3e97:	be 01 00 00 00       	mov    $0x1,%esi
    3e9c:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ea0:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3ea4:	8b 78 60             	mov    0x60(%rax),%edi
    3ea7:	e8 54 e5 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3eac:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    3eaf:	0f 8f db fe ff ff    	jg     3d90 <timer_thread+0x360>
    3eb5:	e9 09 ff ff ff       	jmp    3dc3 <timer_thread+0x393>
}
    3eba:	e8 71 e4 ff ff       	call   2330 <__stack_chk_fail@plt>
    3ebf:	90                   	nop

0000000000003ec0 <sendm.part.0>:
int sendm(struct BarrierTask *data) {
    3ec0:	41 57                	push   %r15
    3ec2:	41 56                	push   %r14
    3ec4:	41 55                	push   %r13
    3ec6:	41 54                	push   %r12
    3ec8:	55                   	push   %rbp
    3ec9:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    3eca:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    3ed0:	89 44 24 c8          	mov    %eax,-0x38(%rsp)
    3ed4:	85 c0                	test   %eax,%eax
    3ed6:	0f 8e 77 01 00 00    	jle    4053 <sendm.part.0+0x193>
        if (n == data->thread_index) { continue; }
    3edc:	8b 87 30 01 00 00    	mov    0x130(%rdi),%eax
    3ee2:	49 89 fe             	mov    %rdi,%r14
    3ee5:	45 31 e4             	xor    %r12d,%r12d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    3ee8:	45 31 ff             	xor    %r15d,%r15d
        if (n == data->thread_index) { continue; }
    3eeb:	89 44 24 cc          	mov    %eax,-0x34(%rsp)
    3eef:	48 8d 87 88 01 00 00 	lea    0x188(%rdi),%rax
    3ef6:	48 89 44 24 e8       	mov    %rax,-0x18(%rsp)
    3efb:	48 8d 87 90 01 00 00 	lea    0x190(%rdi),%rax
    3f02:	48 89 44 24 f0       	mov    %rax,-0x10(%rsp)
    3f07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3f10:	44 39 7c 24 cc       	cmp    %r15d,-0x34(%rsp)
    3f15:	0f 84 23 01 00 00    	je     403e <sendm.part.0+0x17e>
        struct Data *them = data->mailboxes[n].higher;
    3f1b:	4d 8b 86 70 01 00 00 	mov    0x170(%r14),%r8
    3f22:	4d 01 e0             	add    %r12,%r8
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    3f25:	45 8b 48 30          	mov    0x30(%r8),%r9d
        struct Data *them = data->mailboxes[n].higher;
    3f29:	49 8b 78 08          	mov    0x8(%r8),%rdi
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    3f2d:	41 83 f9 02          	cmp    $0x2,%r9d
    3f31:	0f 84 31 01 00 00    	je     4068 <sendm.part.0+0x1a8>
        for (; them->messages_count < min;) {
    3f37:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    3f3e:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    3f45:	48 39 e9             	cmp    %rbp,%rcx
    3f48:	0f 8d f0 00 00 00    	jge    403e <sendm.part.0+0x17e>
    3f4e:	49 8b 86 08 01 00 00 	mov    0x108(%r14),%rax
    3f55:	48 39 e9             	cmp    %rbp,%rcx
    3f58:	49 89 eb             	mov    %rbp,%r11
          them->messages[them->messages_count++] = data->message; 
    3f5b:	48 8b 17             	mov    (%rdi),%rdx
    3f5e:	41 0f 9c c5          	setl   %r13b
    3f62:	49 29 cb             	sub    %rcx,%r11
    3f65:	48 89 44 24 d0       	mov    %rax,-0x30(%rsp)
    3f6a:	49 8b 40 20          	mov    0x20(%r8),%rax
    3f6e:	49 8d 5b ff          	lea    -0x1(%r11),%rbx
    3f72:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    3f77:	48 89 44 24 d8       	mov    %rax,-0x28(%rsp)
    3f7c:	48 83 fb 02          	cmp    $0x2,%rbx
    3f80:	0f 86 9a 01 00 00    	jbe    4120 <sendm.part.0+0x260>
    3f86:	45 84 ed             	test   %r13b,%r13b
    3f89:	0f 84 91 01 00 00    	je     4120 <sendm.part.0+0x260>
    3f8f:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    3f97:	4a 8d 04 12          	lea    (%rdx,%r10,1),%rax
    3f9b:	48 89 44 24 e0       	mov    %rax,-0x20(%rsp)
    3fa0:	49 89 c3             	mov    %rax,%r11
    3fa3:	48 8d 04 ea          	lea    (%rdx,%rbp,8),%rax
    3fa7:	48 39 44 24 e8       	cmp    %rax,-0x18(%rsp)
    3fac:	0f 83 ce 00 00 00    	jae    4080 <sendm.part.0+0x1c0>
    3fb2:	4c 89 d8             	mov    %r11,%rax
    3fb5:	4c 8b 5c 24 f0       	mov    -0x10(%rsp),%r11
    3fba:	48 89 ce             	mov    %rcx,%rsi
    3fbd:	4c 39 d8             	cmp    %r11,%rax
    3fc0:	0f 83 ba 00 00 00    	jae    4080 <sendm.part.0+0x1c0>
    3fc6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3fd0:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    3fd7:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    3fdb:	48 83 c6 01          	add    $0x1,%rsi
    3fdf:	48 39 f5             	cmp    %rsi,%rbp
    3fe2:	7f ec                	jg     3fd0 <sendm.part.0+0x110>
    3fe4:	0f 1f 40 00          	nopl   0x0(%rax)
    3fe8:	31 f6                	xor    %esi,%esi
    3fea:	45 84 ed             	test   %r13b,%r13b
    3fed:	4c 8b 5c 24 d0       	mov    -0x30(%rsp),%r11
    3ff2:	48 0f 45 f3          	cmovne %rbx,%rsi
    3ff6:	4d 8d 5c 33 01       	lea    0x1(%r11,%rsi,1),%r11
    3ffb:	48 8d 4c 31 01       	lea    0x1(%rcx,%rsi,1),%rcx
    4000:	4d 89 9e 08 01 00 00 	mov    %r11,0x108(%r14)
    4007:	4c 8b 5c 24 d8       	mov    -0x28(%rsp),%r11
    400c:	4d 8d 5c 33 01       	lea    0x1(%r11,%rsi,1),%r11
    4011:	4d 89 58 20          	mov    %r11,0x20(%r8)
    4015:	48 89 8f 80 00 00 00 	mov    %rcx,0x80(%rdi)
    401c:	48 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%rcx
    4024:	bb 00 00 00 00       	mov    $0x0,%ebx
    4029:	48 0f 44 cb          	cmove  %rbx,%rcx
    402d:	4c 01 d2             	add    %r10,%rdx
    4030:	48 89 04 0a          	mov    %rax,(%rdx,%rcx,1)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4034:	41 83 f9 02          	cmp    $0x2,%r9d
    4038:	0f 84 c2 00 00 00    	je     4100 <sendm.part.0+0x240>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    403e:	8b 44 24 c8          	mov    -0x38(%rsp),%eax
    4042:	41 83 c7 01          	add    $0x1,%r15d
    4046:	49 83 c4 38          	add    $0x38,%r12
    404a:	41 39 c7             	cmp    %eax,%r15d
    404d:	0f 85 bd fe ff ff    	jne    3f10 <sendm.part.0+0x50>
      asm volatile ("sfence" ::: "memory");
    4053:	0f ae f8             	sfence
}
    4056:	5b                   	pop    %rbx
    4057:	5d                   	pop    %rbp
    4058:	41 5c                	pop    %r12
    405a:	41 5d                	pop    %r13
    405c:	41 5e                	pop    %r14
    405e:	41 5f                	pop    %r15
    4060:	c3                   	ret
    4061:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4068:	8b 87 00 01 00 00    	mov    0x100(%rdi),%eax
    406e:	83 f8 01             	cmp    $0x1,%eax
    4071:	0f 84 b9 00 00 00    	je     4130 <sendm.part.0+0x270>
        else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    4077:	85 c0                	test   %eax,%eax
    4079:	74 c3                	je     403e <sendm.part.0+0x17e>
    407b:	e9 b7 fe ff ff       	jmp    3f37 <sendm.part.0+0x77>
    4080:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    4085:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    408c:	48 8b 74 24 e0       	mov    -0x20(%rsp),%rsi
    4091:	49 d1 eb             	shr    %r11
    4094:	66 48 0f 6e c0       	movq   %rax,%xmm0
    4099:	4c 89 dd             	mov    %r11,%rbp
    409c:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    40a0:	48 c1 e5 04          	shl    $0x4,%rbp
    40a4:	49 89 eb             	mov    %rbp,%r11
    40a7:	48 01 f5             	add    %rsi,%rbp
    40aa:	41 83 e3 10          	and    $0x10,%r11d
    40ae:	74 11                	je     40c1 <sendm.part.0+0x201>
          them->messages[them->messages_count++] = data->message; 
    40b0:	0f 11 06             	movups %xmm0,(%rsi)
        for (; them->messages_count < min;) {
    40b3:	48 83 c6 10          	add    $0x10,%rsi
    40b7:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    40bc:	48 39 f5             	cmp    %rsi,%rbp
    40bf:	74 1a                	je     40db <sendm.part.0+0x21b>
    40c1:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
          them->messages[them->messages_count++] = data->message; 
    40c6:	0f 11 06             	movups %xmm0,(%rsi)
    40c9:	48 83 c6 20          	add    $0x20,%rsi
    40cd:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
        for (; them->messages_count < min;) {
    40d1:	48 39 f5             	cmp    %rsi,%rbp
    40d4:	75 f0                	jne    40c6 <sendm.part.0+0x206>
    40d6:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    40db:	4c 89 de             	mov    %r11,%rsi
    40de:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    40e2:	48 01 ce             	add    %rcx,%rsi
    40e5:	41 83 e3 01          	and    $0x1,%r11d
    40e9:	0f 84 f9 fe ff ff    	je     3fe8 <sendm.part.0+0x128>
          them->messages[them->messages_count++] = data->message; 
    40ef:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    40f6:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    40fa:	e9 e9 fe ff ff       	jmp    3fe8 <sendm.part.0+0x128>
    40ff:	90                   	nop
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4100:	83 bf 00 01 00 00 01 	cmpl   $0x1,0x100(%rdi)
    4107:	0f 85 31 ff ff ff    	jne    403e <sendm.part.0+0x17e>
          them->available = 0;
    410d:	c7 87 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdi)
    4117:	e9 22 ff ff ff       	jmp    403e <sendm.part.0+0x17e>
    411c:	0f 1f 40 00          	nopl   0x0(%rax)
          them->messages[them->messages_count++] = data->message; 
    4120:	48 89 ce             	mov    %rcx,%rsi
    4123:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    412b:	e9 a0 fe ff ff       	jmp    3fd0 <sendm.part.0+0x110>
        for (; them->messages_count < min;) {
    4130:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    4137:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    413e:	48 39 cd             	cmp    %rcx,%rbp
    4141:	0f 8f 07 fe ff ff    	jg     3f4e <sendm.part.0+0x8e>
    4147:	eb c4                	jmp    410d <sendm.part.0+0x24d>
    4149:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004150 <strtolower>:
void strtolower(char *str) {
    4150:	f3 0f 1e fa          	endbr64
    4154:	55                   	push   %rbp
    4155:	53                   	push   %rbx
    4156:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    415a:	48 0f be 1f          	movsbq (%rdi),%rbx
    415e:	84 db                	test   %bl,%bl
    4160:	74 24                	je     4186 <strtolower+0x36>
    4162:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4165:	e8 a6 e3 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    416a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4170:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4173:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4177:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    417a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    417d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4182:	84 db                	test   %bl,%bl
    4184:	75 ea                	jne    4170 <strtolower+0x20>
}
    4186:	48 83 c4 08          	add    $0x8,%rsp
    418a:	5b                   	pop    %rbx
    418b:	5d                   	pop    %rbp
    418c:	c3                   	ret
    418d:	0f 1f 00             	nopl   (%rax)

0000000000004190 <zh_malloc>:
void *zh_malloc(size_t size) {
    4190:	f3 0f 1e fa          	endbr64
    4194:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4198:	e8 73 e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    419d:	48 85 c0             	test   %rax,%rax
    41a0:	74 05                	je     41a7 <zh_malloc+0x17>
}
    41a2:	48 83 c4 08          	add    $0x8,%rsp
    41a6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    41a7:	48 8b 0d 72 5e 00 00 	mov    0x5e72(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    41ae:	ba 28 00 00 00       	mov    $0x28,%edx
    41b3:	be 01 00 00 00       	mov    $0x1,%esi
    41b8:	48 8d 3d 41 33 00 00 	lea    0x3341(%rip),%rdi        # 7500 <_IO_stdin_used+0x500>
    41bf:	e8 fc e2 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    41c4:	bf 01 00 00 00       	mov    $0x1,%edi
    41c9:	e8 d2 e2 ff ff       	call   24a0 <exit@plt>
    41ce:	66 90                	xchg   %ax,%ax

00000000000041d0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    41d0:	f3 0f 1e fa          	endbr64
    41d4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    41d5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    41da:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    41dd:	e8 7e e1 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    41e2:	48 85 c0             	test   %rax,%rax
    41e5:	74 11                	je     41f8 <get_filename_ext+0x28>
    41e7:	48 39 c3             	cmp    %rax,%rbx
    41ea:	74 0c                	je     41f8 <get_filename_ext+0x28>
    return dot + 1;
    41ec:	48 83 c0 01          	add    $0x1,%rax
}
    41f0:	5b                   	pop    %rbx
    41f1:	c3                   	ret
    41f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    41f8:	48 8d 05 f1 2e 00 00 	lea    0x2ef1(%rip),%rax        # 70f0 <_IO_stdin_used+0xf0>
}
    41ff:	5b                   	pop    %rbx
    4200:	c3                   	ret
    4201:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    420c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004210 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4210:	f3 0f 1e fa          	endbr64
    4214:	41 55                	push   %r13
    4216:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4219:	48 89 fe             	mov    %rdi,%rsi
    421c:	41 54                	push   %r12
    421e:	55                   	push   %rbp
    421f:	48 89 d5             	mov    %rdx,%rbp
    4222:	ba 00 04 00 00       	mov    $0x400,%edx
    4227:	53                   	push   %rbx
    4228:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    422f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4238:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4240:	31 c0                	xor    %eax,%eax
    4242:	49 89 e4             	mov    %rsp,%r12
    4245:	4c 89 e7             	mov    %r12,%rdi
    4248:	e8 e3 e1 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    424d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4252:	84 db                	test   %bl,%bl
    4254:	74 24                	je     427a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4256:	e8 b5 e2 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    425b:	48 8b 08             	mov    (%rax),%rcx
    425e:	4c 89 e0             	mov    %r12,%rax
    4261:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4268:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    426b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    426f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4272:	48 0f be 18          	movsbq (%rax),%rbx
    4276:	84 db                	test   %bl,%bl
    4278:	75 ee                	jne    4268 <send_headers+0x58>
    void *buf = malloc(size);
    427a:	bf 11 00 00 00       	mov    $0x11,%edi
    427f:	e8 8c e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4284:	48 85 c0             	test   %rax,%rax
    4287:	0f 84 7e 04 00 00    	je     470b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    428d:	66 0f 6f 05 5b 38 00 00 	movdqa 0x385b(%rip),%xmm0        # 7af0 <_IO_stdin_used+0xaf0>
    iov[0].iov_base = zh_malloc(slen);
    4295:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4299:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    429e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    42a6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    42aa:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    42ad:	e8 5e e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    42b2:	48 85 c0             	test   %rax,%rax
    42b5:	0f 84 50 04 00 00    	je     470b <send_headers+0x4fb>
    42bb:	66 0f 6f 05 3d 38 00 00 	movdqa 0x383d(%rip),%xmm0        # 7b00 <_IO_stdin_used+0xb00>
    iov[1].iov_base = zh_malloc(slen);
    42c3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    42c7:	4c 89 e7             	mov    %r12,%rdi
    42ca:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    42d4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    42dc:	0f 11 00             	movups %xmm0,(%rax)
    42df:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    42e3:	be 2e 00 00 00       	mov    $0x2e,%esi
    42e8:	e8 73 e0 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    42ed:	48 85 c0             	test   %rax,%rax
    42f0:	0f 84 ea 02 00 00    	je     45e0 <send_headers+0x3d0>
    42f6:	4c 39 e0             	cmp    %r12,%rax
    42f9:	0f 84 e1 02 00 00    	je     45e0 <send_headers+0x3d0>
    return dot + 1;
    42ff:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4303:	48 8d 3d b4 2d 00 00 	lea    0x2db4(%rip),%rdi        # 70be <_IO_stdin_used+0xbe>
    430a:	48 89 de             	mov    %rbx,%rsi
    430d:	e8 9e e0 ff ff       	call   23b0 <strcmp@plt>
    4312:	85 c0                	test   %eax,%eax
    4314:	75 20                	jne    4336 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4316:	66 0f 6f 05 f2 37 00 00 	movdqa 0x37f2(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    431e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4326:	66 0f 6f 05 f2 37 00 00 	movdqa 0x37f2(%rip),%xmm0        # 7b20 <_IO_stdin_used+0xb20>
    432e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4336:	48 89 de             	mov    %rbx,%rsi
    4339:	48 8d 3d 82 2d 00 00 	lea    0x2d82(%rip),%rdi        # 70c2 <_IO_stdin_used+0xc2>
    4340:	e8 6b e0 ff ff       	call   23b0 <strcmp@plt>
    4345:	85 c0                	test   %eax,%eax
    4347:	75 20                	jne    4369 <send_headers+0x159>
    4349:	66 0f 6f 05 bf 37 00 00 	movdqa 0x37bf(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4351:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4359:	66 0f 6f 05 bf 37 00 00 	movdqa 0x37bf(%rip),%xmm0        # 7b20 <_IO_stdin_used+0xb20>
    4361:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4369:	48 89 de             	mov    %rbx,%rsi
    436c:	48 8d 3d 54 2d 00 00 	lea    0x2d54(%rip),%rdi        # 70c7 <_IO_stdin_used+0xc7>
    4373:	e8 38 e0 ff ff       	call   23b0 <strcmp@plt>
    4378:	85 c0                	test   %eax,%eax
    437a:	0f 84 10 02 00 00    	je     4590 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4380:	48 89 de             	mov    %rbx,%rsi
    4383:	48 8d 3d 41 2d 00 00 	lea    0x2d41(%rip),%rdi        # 70cb <_IO_stdin_used+0xcb>
    438a:	e8 21 e0 ff ff       	call   23b0 <strcmp@plt>
    438f:	85 c0                	test   %eax,%eax
    4391:	0f 84 a9 02 00 00    	je     4640 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4397:	48 89 de             	mov    %rbx,%rsi
    439a:	48 8d 3d 2e 2d 00 00 	lea    0x2d2e(%rip),%rdi        # 70cf <_IO_stdin_used+0xcf>
    43a1:	e8 0a e0 ff ff       	call   23b0 <strcmp@plt>
    43a6:	85 c0                	test   %eax,%eax
    43a8:	0f 84 6a 02 00 00    	je     4618 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    43ae:	48 89 de             	mov    %rbx,%rsi
    43b1:	48 8d 3d 5a 2d 00 00 	lea    0x2d5a(%rip),%rdi        # 7112 <_IO_stdin_used+0x112>
    43b8:	e8 f3 df ff ff       	call   23b0 <strcmp@plt>
    43bd:	85 c0                	test   %eax,%eax
    43bf:	0f 84 2b 02 00 00    	je     45f0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    43c5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    43c8:	0f 84 52 01 00 00    	je     4520 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    43ce:	48 89 de             	mov    %rbx,%rsi
    43d1:	48 8d 3d fb 2c 00 00 	lea    0x2cfb(%rip),%rdi        # 70d3 <_IO_stdin_used+0xd3>
    43d8:	e8 d3 df ff ff       	call   23b0 <strcmp@plt>
    43dd:	85 c0                	test   %eax,%eax
    43df:	0f 84 ab 02 00 00    	je     4690 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    43e5:	48 89 de             	mov    %rbx,%rsi
    43e8:	48 8d 3d e8 2c 00 00 	lea    0x2ce8(%rip),%rdi        # 70d7 <_IO_stdin_used+0xd7>
    43ef:	e8 bc df ff ff       	call   23b0 <strcmp@plt>
    43f4:	85 c0                	test   %eax,%eax
    43f6:	0f 84 6c 02 00 00    	je     4668 <send_headers+0x458>
    slen = strlen(send_buffer);
    43fc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4404:	4c 89 e7             	mov    %r12,%rdi
    4407:	e8 14 df ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    440c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    440f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4412:	e8 f9 df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4417:	48 85 c0             	test   %rax,%rax
    441a:	0f 84 eb 02 00 00    	je     470b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4420:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4424:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4428:	83 fb 08             	cmp    $0x8,%ebx
    442b:	0f 83 3f 01 00 00    	jae    4570 <send_headers+0x360>
    4431:	f6 c3 04             	test   $0x4,%bl
    4434:	0f 85 7b 02 00 00    	jne    46b5 <send_headers+0x4a5>
    443a:	85 db                	test   %ebx,%ebx
    443c:	74 13                	je     4451 <send_headers+0x241>
    443e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4446:	88 10                	mov    %dl,(%rax)
    4448:	f6 c3 02             	test   $0x2,%bl
    444b:	0f 85 96 02 00 00    	jne    46e7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4451:	4d 89 e8             	mov    %r13,%r8
    4454:	48 8d 0d 80 2c 00 00 	lea    0x2c80(%rip),%rcx        # 70db <_IO_stdin_used+0xdb>
    445b:	4c 89 e7             	mov    %r12,%rdi
    445e:	31 c0                	xor    %eax,%eax
    4460:	ba 00 04 00 00       	mov    $0x400,%edx
    4465:	be 01 00 00 00       	mov    $0x1,%esi
    446a:	e8 b1 e0 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    446f:	4c 89 e7             	mov    %r12,%rdi
    4472:	e8 a9 de ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4477:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    447a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    447d:	e8 8e df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4482:	48 85 c0             	test   %rax,%rax
    4485:	0f 84 80 02 00 00    	je     470b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    448b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    448f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4493:	83 fb 08             	cmp    $0x8,%ebx
    4496:	0f 83 1c 01 00 00    	jae    45b8 <send_headers+0x3a8>
    449c:	f6 c3 04             	test   $0x4,%bl
    449f:	0f 85 29 02 00 00    	jne    46ce <send_headers+0x4be>
    44a5:	85 db                	test   %ebx,%ebx
    44a7:	74 13                	je     44bc <send_headers+0x2ac>
    44a9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    44b1:	88 10                	mov    %dl,(%rax)
    44b3:	f6 c3 02             	test   $0x2,%bl
    44b6:	0f 85 3d 02 00 00    	jne    46f9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    44bc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    44c1:	bf 02 00 00 00       	mov    $0x2,%edi
    44c6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    44ce:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    44d6:	e8 35 df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    44db:	48 85 c0             	test   %rax,%rax
    44de:	0f 84 27 02 00 00    	je     470b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    44e4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    44ec:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    44f0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    44f8:	66 89 10             	mov    %dx,(%rax)
}
    44fb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4503:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    450c:	0f 85 20 02 00 00    	jne    4732 <send_headers+0x522>
    4512:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4519:	5b                   	pop    %rbx
    451a:	5d                   	pop    %rbp
    451b:	41 5c                	pop    %r12
    451d:	41 5d                	pop    %r13
    451f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4520:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4524:	0f 85 a4 fe ff ff    	jne    43ce <send_headers+0x1be>
    452a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    452e:	0f 85 9a fe ff ff    	jne    43ce <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4534:	66 0f 6f 05 34 36 00 00 	movdqa 0x3634(%rip),%xmm0        # 7b70 <_IO_stdin_used+0xb70>
    453c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4546:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    454e:	66 0f 6f 05 2a 36 00 00 	movdqa 0x362a(%rip),%xmm0        # 7b80 <_IO_stdin_used+0xb80>
    4556:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    455e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4566:	e9 63 fe ff ff       	jmp    43ce <send_headers+0x1be>
    456b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4570:	89 da                	mov    %ebx,%edx
    4572:	48 89 c7             	mov    %rax,%rdi
    4575:	4c 89 e6             	mov    %r12,%rsi
    4578:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    457d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4582:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4585:	c1 e9 03             	shr    $0x3,%ecx
    4588:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    458b:	e9 c1 fe ff ff       	jmp    4451 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4590:	66 0f 6f 05 78 35 00 00 	movdqa 0x3578(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4598:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    45a0:	66 0f 6f 05 88 35 00 00 	movdqa 0x3588(%rip),%xmm0        # 7b30 <_IO_stdin_used+0xb30>
    45a8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    45b0:	e9 cb fd ff ff       	jmp    4380 <send_headers+0x170>
    45b5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    45b8:	89 da                	mov    %ebx,%edx
    45ba:	48 89 c7             	mov    %rax,%rdi
    45bd:	4c 89 e6             	mov    %r12,%rsi
    45c0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    45c5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    45ca:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    45cd:	c1 e9 03             	shr    $0x3,%ecx
    45d0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    45d3:	e9 e4 fe ff ff       	jmp    44bc <send_headers+0x2ac>
    45d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    45e0:	48 8d 1d 09 2b 00 00 	lea    0x2b09(%rip),%rbx        # 70f0 <_IO_stdin_used+0xf0>
    45e7:	e9 94 fd ff ff       	jmp    4380 <send_headers+0x170>
    45ec:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    45f0:	66 0f 6f 05 58 35 00 00 	movdqa 0x3558(%rip),%xmm0        # 7b50 <_IO_stdin_used+0xb50>
    45f8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4600:	66 0f 6f 05 58 35 00 00 	movdqa 0x3558(%rip),%xmm0        # 7b60 <_IO_stdin_used+0xb60>
    4608:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4610:	e9 b0 fd ff ff       	jmp    43c5 <send_headers+0x1b5>
    4615:	0f 1f 00             	nopl   (%rax)
    4618:	66 0f 6f 05 30 35 00 00 	movdqa 0x3530(%rip),%xmm0        # 7b50 <_IO_stdin_used+0xb50>
    4620:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4628:	66 0f 6f 05 30 35 00 00 	movdqa 0x3530(%rip),%xmm0        # 7b60 <_IO_stdin_used+0xb60>
    4630:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4638:	e9 71 fd ff ff       	jmp    43ae <send_headers+0x19e>
    463d:	0f 1f 00             	nopl   (%rax)
    4640:	66 0f 6f 05 c8 34 00 00 	movdqa 0x34c8(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4648:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4650:	66 0f 6f 05 e8 34 00 00 	movdqa 0x34e8(%rip),%xmm0        # 7b40 <_IO_stdin_used+0xb40>
    4658:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4660:	e9 32 fd ff ff       	jmp    4397 <send_headers+0x187>
    4665:	0f 1f 00             	nopl   (%rax)
    4668:	66 0f 6f 05 e0 34 00 00 	movdqa 0x34e0(%rip),%xmm0        # 7b50 <_IO_stdin_used+0xb50>
    4670:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4678:	66 0f 6f 05 20 35 00 00 	movdqa 0x3520(%rip),%xmm0        # 7ba0 <_IO_stdin_used+0xba0>
    4680:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4688:	e9 6f fd ff ff       	jmp    43fc <send_headers+0x1ec>
    468d:	0f 1f 00             	nopl   (%rax)
    4690:	66 0f 6f 05 b8 34 00 00 	movdqa 0x34b8(%rip),%xmm0        # 7b50 <_IO_stdin_used+0xb50>
    4698:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    46a0:	66 0f 6f 05 e8 34 00 00 	movdqa 0x34e8(%rip),%xmm0        # 7b90 <_IO_stdin_used+0xb90>
    46a8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    46b0:	e9 30 fd ff ff       	jmp    43e5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    46b5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    46bc:	89 db                	mov    %ebx,%ebx
    46be:	89 10                	mov    %edx,(%rax)
    46c0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    46c5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    46c9:	e9 83 fd ff ff       	jmp    4451 <send_headers+0x241>
    46ce:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    46d5:	89 db                	mov    %ebx,%ebx
    46d7:	89 10                	mov    %edx,(%rax)
    46d9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    46de:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    46e2:	e9 d5 fd ff ff       	jmp    44bc <send_headers+0x2ac>
    46e7:	89 db                	mov    %ebx,%ebx
    46e9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    46ef:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    46f4:	e9 58 fd ff ff       	jmp    4451 <send_headers+0x241>
    46f9:	89 db                	mov    %ebx,%ebx
    46fb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4701:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4706:	e9 b1 fd ff ff       	jmp    44bc <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    470b:	48 8b 0d 0e 59 00 00 	mov    0x590e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4712:	ba 28 00 00 00       	mov    $0x28,%edx
    4717:	be 01 00 00 00       	mov    $0x1,%esi
    471c:	48 8d 3d dd 2d 00 00 	lea    0x2ddd(%rip),%rdi        # 7500 <_IO_stdin_used+0x500>
    4723:	e8 98 dd ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4728:	bf 01 00 00 00       	mov    $0x1,%edi
    472d:	e8 6e dd ff ff       	call   24a0 <exit@plt>
}
    4732:	e8 f9 db ff ff       	call   2330 <__stack_chk_fail@plt>
    4737:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004740 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4740:	f3 0f 1e fa          	endbr64
    4744:	41 55                	push   %r13
    4746:	49 89 d5             	mov    %rdx,%r13
    4749:	41 54                	push   %r12
    474b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    474e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4751:	55                   	push   %rbp
    4752:	53                   	push   %rbx
    4753:	48 89 f3             	mov    %rsi,%rbx
    4756:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    475a:	e8 b1 dc ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    475f:	48 85 c0             	test   %rax,%rax
    4762:	74 6b                	je     47cf <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4764:	4c 89 e7             	mov    %r12,%rdi
    4767:	48 89 c5             	mov    %rax,%rbp
    476a:	31 f6                	xor    %esi,%esi
    476c:	31 c0                	xor    %eax,%eax
    476e:	e8 0d dd ff ff       	call   2480 <open@plt>
    4773:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4776:	85 c0                	test   %eax,%eax
    4778:	0f 88 d8 dd ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    477e:	48 89 da             	mov    %rbx,%rdx
    4781:	48 89 ee             	mov    %rbp,%rsi
    4784:	89 c7                	mov    %eax,%edi
    4786:	e8 05 dc ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    478b:	48 98                	cltq
    478d:	48 39 d8             	cmp    %rbx,%rax
    4790:	7c 1e                	jl     47b0 <copy_file_contents+0x70>
    close(fd);
    4792:	44 89 e7             	mov    %r12d,%edi
    4795:	e8 d6 db ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    479a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    479e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    47a2:	48 83 c4 08          	add    $0x8,%rsp
    47a6:	5b                   	pop    %rbx
    47a7:	5d                   	pop    %rbp
    47a8:	41 5c                	pop    %r12
    47aa:	41 5d                	pop    %r13
    47ac:	c3                   	ret
    47ad:	0f 1f 00             	nopl   (%rax)
    47b0:	48 8b 0d 69 58 00 00 	mov    0x5869(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    47b7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    47bc:	be 01 00 00 00       	mov    $0x1,%esi
    47c1:	48 8d 3d 29 29 00 00 	lea    0x2929(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    47c8:	e8 f3 dc ff ff       	call   24c0 <fwrite@plt>
    47cd:	eb c3                	jmp    4792 <copy_file_contents+0x52>
    47cf:	48 8b 0d 4a 58 00 00 	mov    0x584a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    47d6:	ba 28 00 00 00       	mov    $0x28,%edx
    47db:	be 01 00 00 00       	mov    $0x1,%esi
    47e0:	48 8d 3d 19 2d 00 00 	lea    0x2d19(%rip),%rdi        # 7500 <_IO_stdin_used+0x500>
    47e7:	e8 d4 dc ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    47ec:	bf 01 00 00 00       	mov    $0x1,%edi
    47f1:	e8 aa dc ff ff       	call   24a0 <exit@plt>
    47f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004800 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4800:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4804:	8b 46 44             	mov    0x44(%rsi),%eax
    4807:	48 89 fa             	mov    %rdi,%rdx
    480a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    480d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4813:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4816:	48 8b 07             	mov    (%rdi),%rax
    4819:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    481c:	f6 c1 02             	test   $0x2,%cl
    481f:	74 00                	je     4821 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4821:	89 f0                	mov    %esi,%eax
    4823:	44 29 c0             	sub    %r8d,%eax
    4826:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4829:	0f 82 33 dd ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    482f:	c1 e9 0a             	shr    $0xa,%ecx
    4832:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4836:	8b 47 44             	mov    0x44(%rdi),%eax
    4839:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    483c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    483f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4842:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4845:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4849:	d3 e0                	shl    %cl,%eax
    484b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    484e:	48 c1 e0 06          	shl    $0x6,%rax
    4852:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4856:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    485c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    485f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4863:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4869:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4871:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4875:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4878:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    487f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4887:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    488b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    488f:	e8 ac da ff ff       	call   2340 <io_uring_submit@plt>
}
    4894:	31 c0                	xor    %eax,%eax
    4896:	48 83 c4 08          	add    $0x8,%rsp
    489a:	c3                   	ret
    489b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000048a0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    48a0:	f3 0f 1e fa          	endbr64
    48a4:	41 55                	push   %r13
    48a6:	41 89 fd             	mov    %edi,%r13d
    48a9:	41 54                	push   %r12
    48ab:	55                   	push   %rbp
    48ac:	53                   	push   %rbx
    48ad:	48 89 f3             	mov    %rsi,%rbx
    48b0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    48b4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    48b7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    48bd:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    48c0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    48c3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    48c5:	f6 c1 02             	test   $0x2,%cl
    48c8:	74 00                	je     48ca <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    48ca:	89 c2                	mov    %eax,%edx
    48cc:	29 f2                	sub    %esi,%edx
    48ce:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    48d1:	0f 82 9b dc ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    48d7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    48da:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    48dd:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    48e0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    48e5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    48e8:	23 6b 58             	and    0x58(%rbx),%ebp
    48eb:	d3 e5                	shl    %cl,%ebp
    48ed:	48 c1 e5 06          	shl    $0x6,%rbp
    48f1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    48f5:	e8 16 db ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    48fa:	be 01 00 00 00       	mov    $0x1,%esi
    48ff:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4904:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4907:	e8 94 da ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    490c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4911:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4915:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4918:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    491d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4922:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    492b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4933:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4937:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    493b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4942:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    494a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    494e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4956:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    495e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4962:	e8 d9 d9 ff ff       	call   2340 <io_uring_submit@plt>
}
    4967:	48 83 c4 08          	add    $0x8,%rsp
    496b:	31 c0                	xor    %eax,%eax
    496d:	5b                   	pop    %rbx
    496e:	5d                   	pop    %rbp
    496f:	41 5c                	pop    %r12
    4971:	41 5d                	pop    %r13
    4973:	c3                   	ret
    4974:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    497f:	90                   	nop

0000000000004980 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4980:	f3 0f 1e fa          	endbr64
    4984:	41 56                	push   %r14
    4986:	41 89 f6             	mov    %esi,%r14d
    4989:	41 55                	push   %r13
    498b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    498e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4993:	41 54                	push   %r12
    4995:	55                   	push   %rbp
    4996:	48 89 d5             	mov    %rdx,%rbp
    4999:	53                   	push   %rbx
    void *buf = malloc(size);
    499a:	e8 71 da ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    499f:	48 85 c0             	test   %rax,%rax
    49a2:	0f 84 dd 00 00 00    	je     4a85 <_send_static_string_content+0x105>
    49a8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    49ab:	4c 89 ef             	mov    %r13,%rdi
    49ae:	e8 6d d9 ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    49b3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    49ba:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    49be:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    49c1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    49c4:	e8 47 da ff ff       	call   2410 <malloc@plt>
    49c9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    49cc:	48 85 c0             	test   %rax,%rax
    49cf:	0f 84 b0 00 00 00    	je     4a85 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    49d5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    49d9:	4c 89 e2             	mov    %r12,%rdx
    49dc:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    49df:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    49e3:	e8 f8 d9 ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    49e8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    49eb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    49f1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    49f4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    49f8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    49fa:	f6 c1 02             	test   $0x2,%cl
    49fd:	0f 85 7d 00 00 00    	jne    4a80 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4a03:	89 d0                	mov    %edx,%eax
    4a05:	29 f0                	sub    %esi,%eax
    4a07:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    4a0a:	0f 82 6c db ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4a10:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4a13:	8b 45 44             	mov    0x44(%rbp),%eax
    4a16:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4a19:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    4a1c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4a1f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4a22:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4a28:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4a2c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4a2e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4a31:	48 89 ef             	mov    %rbp,%rdi
    4a34:	48 c1 e0 06          	shl    $0x6,%rax
    4a38:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    4a3c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4a3f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4a43:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4a49:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4a51:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4a55:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4a58:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4a5f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4a67:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    4a6b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    4a6f:	5b                   	pop    %rbx
    4a70:	5d                   	pop    %rbp
    4a71:	41 5c                	pop    %r12
    4a73:	41 5d                	pop    %r13
    4a75:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4a77:	e9 c4 d8 ff ff       	jmp    2340 <io_uring_submit@plt>
    4a7c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4a80:	e9 7e ff ff ff       	jmp    4a03 <_send_static_string_content+0x83>
    4a85:	48 8b 0d 94 55 00 00 	mov    0x5594(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4a8c:	ba 28 00 00 00       	mov    $0x28,%edx
    4a91:	be 01 00 00 00       	mov    $0x1,%esi
    4a96:	48 8d 3d 63 2a 00 00 	lea    0x2a63(%rip),%rdi        # 7500 <_IO_stdin_used+0x500>
    4a9d:	e8 1e da ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4aa2:	bf 01 00 00 00       	mov    $0x1,%edi
    4aa7:	e8 f4 d9 ff ff       	call   24a0 <exit@plt>
    4aac:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004ab0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4ab0:	f3 0f 1e fa          	endbr64
    4ab4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4ab7:	89 fe                	mov    %edi,%esi
    4ab9:	48 8b 3d 58 55 00 00 	mov    0x5558(%rip),%rdi        # a018 <unimplemented_content>
    4ac0:	e9 bb fe ff ff       	jmp    4980 <_send_static_string_content>
    4ac5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004ad0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4ad0:	f3 0f 1e fa          	endbr64
    4ad4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4ad7:	89 fe                	mov    %edi,%esi
    4ad9:	48 8b 3d 30 55 00 00 	mov    0x5530(%rip),%rdi        # a010 <http_404_content>
    4ae0:	e9 9b fe ff ff       	jmp    4980 <_send_static_string_content>
    4ae5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004af0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4af0:	f3 0f 1e fa          	endbr64
    4af4:	41 56                	push   %r14
    4af6:	41 55                	push   %r13
    4af8:	49 89 d5             	mov    %rdx,%r13
    4afb:	41 54                	push   %r12
    4afd:	41 89 f4             	mov    %esi,%r12d
    4b00:	55                   	push   %rbp
    4b01:	48 89 fd             	mov    %rdi,%rbp
    4b04:	53                   	push   %rbx
    4b05:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    4b0c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b15:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    4b1d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    4b1f:	e8 fc d7 ff ff       	call   2320 <strlen@plt>
    4b24:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4b29:	48 89 c3             	mov    %rax,%rbx
    4b2c:	0f 84 b6 00 00 00    	je     4be8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4b32:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4b37:	48 89 ee             	mov    %rbp,%rsi
    4b3a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4b3e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4b43:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4b4b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4b53:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4b5e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4b66:	e8 55 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4b6b:	48 89 e6             	mov    %rsp,%rsi
    4b6e:	4c 89 f7             	mov    %r14,%rdi
    4b71:	e8 5a d8 ff ff       	call   23d0 <stat@plt>
    4b76:	83 f8 ff             	cmp    $0xffffffff,%eax
    4b79:	0f 84 d3 00 00 00    	je     4c52 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    4b7f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4b83:	25 00 f0 00 00       	and    $0xf000,%eax
    4b88:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4b8d:	0f 84 f5 00 00 00    	je     4c88 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4b93:	48 8b 3d 76 54 00 00 	mov    0x5476(%rip),%rdi        # a010 <http_404_content>
    4b9a:	4c 89 ea             	mov    %r13,%rdx
    4b9d:	44 89 e6             	mov    %r12d,%esi
    4ba0:	e8 db fd ff ff       	call   4980 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4ba5:	4c 89 f2             	mov    %r14,%rdx
    4ba8:	bf 01 00 00 00       	mov    $0x1,%edi
    4bad:	31 c0                	xor    %eax,%eax
    4baf:	48 8d 35 8b 25 00 00 	lea    0x258b(%rip),%rsi        # 7141 <_IO_stdin_used+0x141>
    4bb6:	e8 95 d8 ff ff       	call   2450 <__printf_chk@plt>
}
    4bbb:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4bc3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4bcc:	0f 85 20 01 00 00    	jne    4cf2 <handle_get_method+0x202>
    4bd2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4bd9:	5b                   	pop    %rbx
    4bda:	5d                   	pop    %rbp
    4bdb:	41 5c                	pop    %r12
    4bdd:	41 5d                	pop    %r13
    4bdf:	41 5e                	pop    %r14
    4be1:	c3                   	ret
    4be2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4be8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4bed:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4bf5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4bfa:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4bfd:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4c05:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4c08:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4c10:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4c1b:	e8 a0 d7 ff ff       	call   23c0 <__memcpy_chk@plt>
    4c20:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4c25:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4c2a:	48 8d 35 db 24 00 00 	lea    0x24db(%rip),%rsi        # 710c <_IO_stdin_used+0x10c>
    4c31:	48 29 d9             	sub    %rbx,%rcx
    4c34:	ba 0b 00 00 00       	mov    $0xb,%edx
    4c39:	e8 82 d7 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4c3e:	48 89 e6             	mov    %rsp,%rsi
    4c41:	4c 89 f7             	mov    %r14,%rdi
    4c44:	e8 87 d7 ff ff       	call   23d0 <stat@plt>
    4c49:	83 f8 ff             	cmp    $0xffffffff,%eax
    4c4c:	0f 85 2d ff ff ff    	jne    4b7f <handle_get_method+0x8f>
    4c52:	4c 89 f2             	mov    %r14,%rdx
    4c55:	48 89 e9             	mov    %rbp,%rcx
    4c58:	48 8d 35 b8 24 00 00 	lea    0x24b8(%rip),%rsi        # 7117 <_IO_stdin_used+0x117>
    4c5f:	31 c0                	xor    %eax,%eax
    4c61:	bf 01 00 00 00       	mov    $0x1,%edi
    4c66:	e8 e5 d7 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    4c6b:	48 8b 3d 9e 53 00 00 	mov    0x539e(%rip),%rdi        # a010 <http_404_content>
    4c72:	4c 89 ea             	mov    %r13,%rdx
    4c75:	44 89 e6             	mov    %r12d,%esi
    4c78:	e8 03 fd ff ff       	call   4980 <_send_static_string_content>
}
    4c7d:	e9 39 ff ff ff       	jmp    4bbb <handle_get_method+0xcb>
    4c82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4c88:	bf 70 00 00 00       	mov    $0x70,%edi
    4c8d:	e8 7e d7 ff ff       	call   2410 <malloc@plt>
    4c92:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4c95:	48 85 c0             	test   %rax,%rax
    4c98:	74 5d                	je     4cf7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    4c9a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4c9e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4ca3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4ca7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    4caa:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4cb1:	e8 5a f5 ff ff       	call   4210 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4cb6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4cbb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4cbf:	4c 89 f7             	mov    %r14,%rdi
    4cc2:	e8 79 fa ff ff       	call   4740 <copy_file_contents>
    4cc7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4ccc:	4c 89 f2             	mov    %r14,%rdx
    4ccf:	31 c0                	xor    %eax,%eax
    4cd1:	48 8d 35 57 24 00 00 	lea    0x2457(%rip),%rsi        # 712f <_IO_stdin_used+0x12f>
    4cd8:	bf 01 00 00 00       	mov    $0x1,%edi
    4cdd:	e8 6e d7 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    4ce2:	4c 89 ee             	mov    %r13,%rsi
    4ce5:	48 89 df             	mov    %rbx,%rdi
    4ce8:	e8 13 fb ff ff       	call   4800 <add_write_request>
    4ced:	e9 c9 fe ff ff       	jmp    4bbb <handle_get_method+0xcb>
}
    4cf2:	e8 39 d6 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4cf7:	48 8b 0d 22 53 00 00 	mov    0x5322(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4cfe:	ba 28 00 00 00       	mov    $0x28,%edx
    4d03:	be 01 00 00 00       	mov    $0x1,%esi
    4d08:	48 8d 3d f1 27 00 00 	lea    0x27f1(%rip),%rdi        # 7500 <_IO_stdin_used+0x500>
    4d0f:	e8 ac d7 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4d14:	bf 01 00 00 00       	mov    $0x1,%edi
    4d19:	e8 82 d7 ff ff       	call   24a0 <exit@plt>
    4d1e:	66 90                	xchg   %ax,%ax

0000000000004d20 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4d20:	f3 0f 1e fa          	endbr64
    4d24:	41 57                	push   %r15
    4d26:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4d28:	4c 8d 35 77 23 00 00 	lea    0x2377(%rip),%r14        # 70a6 <_IO_stdin_used+0xa6>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4d2f:	41 55                	push   %r13
    4d31:	49 89 d5             	mov    %rdx,%r13
    4d34:	41 54                	push   %r12
    4d36:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4d39:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4d3c:	55                   	push   %rbp
    4d3d:	53                   	push   %rbx
    4d3e:	48 83 ec 18          	sub    $0x18,%rsp
    4d42:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4d4b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4d50:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4d52:	49 89 e7             	mov    %rsp,%r15
    4d55:	4c 89 fa             	mov    %r15,%rdx
    4d58:	e8 23 d6 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4d5d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4d61:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4d64:	84 db                	test   %bl,%bl
    4d66:	74 1d                	je     4d85 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4d68:	e8 a3 d7 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4d6d:	48 89 ea             	mov    %rbp,%rdx
    4d70:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4d73:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4d77:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4d7a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    4d7d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4d81:	84 db                	test   %bl,%bl
    4d83:	75 eb                	jne    4d70 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4d85:	4c 89 fa             	mov    %r15,%rdx
    4d88:	4c 89 f6             	mov    %r14,%rsi
    4d8b:	31 ff                	xor    %edi,%edi
    4d8d:	e8 ee d5 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4d92:	48 8d 35 bb 23 00 00 	lea    0x23bb(%rip),%rsi        # 7154 <_IO_stdin_used+0x154>
    4d99:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4d9c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    4d9f:	e8 0c d6 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4da4:	4c 89 ea             	mov    %r13,%rdx
    4da7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4daa:	85 c0                	test   %eax,%eax
    4dac:	75 2a                	jne    4dd8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    4dae:	48 89 df             	mov    %rbx,%rdi
    4db1:	e8 3a fd ff ff       	call   4af0 <handle_get_method>
}
    4db6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4dbb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4dc4:	75 20                	jne    4de6 <handle_http_method+0xc6>
    4dc6:	48 83 c4 18          	add    $0x18,%rsp
    4dca:	5b                   	pop    %rbx
    4dcb:	5d                   	pop    %rbp
    4dcc:	41 5c                	pop    %r12
    4dce:	41 5d                	pop    %r13
    4dd0:	41 5e                	pop    %r14
    4dd2:	41 5f                	pop    %r15
    4dd4:	c3                   	ret
    4dd5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4dd8:	48 8b 3d 39 52 00 00 	mov    0x5239(%rip),%rdi        # a018 <unimplemented_content>
    4ddf:	e8 9c fb ff ff       	call   4980 <_send_static_string_content>
}
    4de4:	eb d0                	jmp    4db6 <handle_http_method+0x96>
    4de6:	e8 45 d5 ff ff       	call   2330 <__stack_chk_fail@plt>
    4deb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004df0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4df0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4df4:	85 d2                	test   %edx,%edx
    4df6:	7e 38                	jle    4e30 <get_line+0x40>
    4df8:	48 63 d2             	movslq %edx,%rdx
    4dfb:	48 83 c7 01          	add    $0x1,%rdi
    4dff:	48 01 f2             	add    %rsi,%rdx
    4e02:	eb 11                	jmp    4e15 <get_line+0x25>
    4e04:	0f 1f 40 00          	nopl   0x0(%rax)
    4e08:	48 83 c6 01          	add    $0x1,%rsi
    4e0c:	48 83 c7 01          	add    $0x1,%rdi
    4e10:	48 39 d6             	cmp    %rdx,%rsi
    4e13:	74 1b                	je     4e30 <get_line+0x40>
        dest[i] = src[i];
    4e15:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4e19:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4e1b:	3c 0d                	cmp    $0xd,%al
    4e1d:	75 e9                	jne    4e08 <get_line+0x18>
    4e1f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4e22:	75 e4                	jne    4e08 <get_line+0x18>
            dest[i] = '\0';
    4e24:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4e27:	31 c0                	xor    %eax,%eax
    4e29:	c3                   	ret
    4e2a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4e30:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4e35:	c3                   	ret
    4e36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004e40 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4e40:	f3 0f 1e fa          	endbr64
    4e44:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4e4b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4e4f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4e58:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4e60:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4e62:	49 89 e2             	mov    %rsp,%r10
    4e65:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4e6d:	4c 89 d0             	mov    %r10,%rax
    4e70:	eb 13                	jmp    4e85 <handle_client_request+0x45>
    4e72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4e78:	48 83 c0 01          	add    $0x1,%rax
    4e7c:	48 83 c1 01          	add    $0x1,%rcx
    4e80:	4c 39 c8             	cmp    %r9,%rax
    4e83:	74 4b                	je     4ed0 <handle_client_request+0x90>
        dest[i] = src[i];
    4e85:	44 0f b6 01          	movzbl (%rcx),%r8d
    4e89:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4e8c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4e90:	75 e6                	jne    4e78 <handle_client_request+0x38>
    4e92:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4e96:	75 e0                	jne    4e78 <handle_client_request+0x38>
            dest[i] = '\0';
    4e98:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4e9b:	8b 47 08             	mov    0x8(%rdi),%eax
    4e9e:	48 89 f2             	mov    %rsi,%rdx
    4ea1:	4c 89 d7             	mov    %r10,%rdi
    4ea4:	89 c6                	mov    %eax,%esi
    4ea6:	e8 75 fe ff ff       	call   4d20 <handle_http_method>
}
    4eab:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4eb3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4ebc:	75 39                	jne    4ef7 <handle_client_request+0xb7>
    4ebe:	31 c0                	xor    %eax,%eax
    4ec0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4ec7:	c3                   	ret
    4ec8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4ed0:	48 8b 0d 49 51 00 00 	mov    0x5149(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4ed7:	ba 12 00 00 00       	mov    $0x12,%edx
    4edc:	be 01 00 00 00       	mov    $0x1,%esi
    4ee1:	48 8d 3d 70 22 00 00 	lea    0x2270(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    4ee8:	e8 d3 d5 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4eed:	bf 01 00 00 00       	mov    $0x1,%edi
    4ef2:	e8 a9 d5 ff ff       	call   24a0 <exit@plt>
}
    4ef7:	e8 34 d4 ff ff       	call   2330 <__stack_chk_fail@plt>
    4efc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004f00 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4f00:	f3 0f 1e fa          	endbr64
    4f04:	55                   	push   %rbp
    4f05:	53                   	push   %rbx
    4f06:	48 89 cb             	mov    %rcx,%rbx
    4f09:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4f0d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4f10:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4f13:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4f19:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4f1c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4f1f:	f6 c1 02             	test   $0x2,%cl
    4f22:	74 00                	je     4f24 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4f24:	41 89 c0             	mov    %eax,%r8d
    4f27:	45 29 c8             	sub    %r9d,%r8d
    4f2a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4f2e:	0f 82 58 d6 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4f34:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4f37:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4f3a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4f3d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4f40:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4f43:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4f47:	d3 e5                	shl    %cl,%ebp
    4f49:	48 c1 e5 06          	shl    $0x6,%rbp
    4f4d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4f51:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4f54:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4f59:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4f60:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4f64:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4f68:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4f70:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4f78:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4f7c:	e8 8f d4 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4f81:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4f84:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4f8a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4f8e:	48 83 c4 08          	add    $0x8,%rsp
    4f92:	5b                   	pop    %rbx
    4f93:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4f94:	e9 a7 d3 ff ff       	jmp    2340 <io_uring_submit@plt>
    4f99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004fa0 <io_thread>:
void* io_thread(void *arg) {
    4fa0:	f3 0f 1e fa          	endbr64
    4fa4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4fa6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4fa8:	41 56                	push   %r14
    4faa:	41 55                	push   %r13
    4fac:	41 54                	push   %r12
    4fae:	55                   	push   %rbp
    4faf:	48 89 fd             	mov    %rdi,%rbp
    4fb2:	53                   	push   %rbx
    4fb3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4fba:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4fc3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4fcb:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4fcf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4fd4:	bf 00 01 00 00       	mov    $0x100,%edi
    4fd9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4fdc:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4fe0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4fe5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4fea:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4fef:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4ff4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4ffc:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5001:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5009:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    500e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5016:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    501b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5023:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5028:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5030:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5035:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    503d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5045:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    504d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5055:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    505d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5065:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    506d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5075:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    507d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5085:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    508d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5094:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    509c:	e8 4f d3 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    50a1:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    50a5:	31 f6                	xor    %esi,%esi
    50a7:	e8 34 d4 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    50ac:	31 d2                	xor    %edx,%edx
    50ae:	be 01 00 00 00       	mov    $0x1,%esi
    50b3:	bf 02 00 00 00       	mov    $0x2,%edi
    50b8:	e8 73 d4 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    50bd:	83 f8 ff             	cmp    $0xffffffff,%eax
    50c0:	0f 84 08 d5 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    50c6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    50cb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    50d1:	89 c7                	mov    %eax,%edi
    50d3:	41 89 c4             	mov    %eax,%r12d
    50d6:	ba 02 00 00 00       	mov    $0x2,%edx
    50db:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    50e0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    50e8:	e8 13 d2 ff ff       	call   2300 <setsockopt@plt>
    50ed:	85 c0                	test   %eax,%eax
    50ef:	0f 88 ad d4 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    50f5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    50fa:	ba 10 00 00 00       	mov    $0x10,%edx
    50ff:	44 89 e7             	mov    %r12d,%edi
    5102:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    510b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5113:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    511b:	e8 40 d3 ff ff       	call   2460 <bind@plt>
    5120:	85 c0                	test   %eax,%eax
    5122:	0f 88 b2 d4 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5128:	be 0a 00 00 00       	mov    $0xa,%esi
    512d:	44 89 e7             	mov    %r12d,%edi
    5130:	e8 eb d2 ff ff       	call   2420 <listen@plt>
    5135:	85 c0                	test   %eax,%eax
    5137:	0f 88 71 d4 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    513d:	ba db 18 00 00       	mov    $0x18db,%edx
    5142:	48 8d 35 54 20 00 00 	lea    0x2054(%rip),%rsi        # 719d <_IO_stdin_used+0x19d>
    5149:	bf 01 00 00 00       	mov    $0x1,%edi
    514e:	31 c0                	xor    %eax,%eax
    5150:	e8 fb d2 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5155:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    515a:	48 89 d9             	mov    %rbx,%rcx
    515d:	44 89 e7             	mov    %r12d,%edi
    5160:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5165:	48 89 c6             	mov    %rax,%rsi
    5168:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    516d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5172:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    517a:	e8 81 fd ff ff       	call   4f00 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    517f:	bf 01 00 00 00       	mov    $0x1,%edi
    5184:	be 10 00 00 00       	mov    $0x10,%esi
    5189:	e8 12 d2 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    518e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5193:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5196:	e8 75 d2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    519b:	48 85 c0             	test   %rax,%rax
    519e:	0f 84 ae 04 00 00    	je     5652 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    51a4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    51a8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    51af:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    51b6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    51be:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    51c1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    51c6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    51c8:	f6 c1 02             	test   $0x2,%cl
    51cb:	0f 85 0f 04 00 00    	jne    55e0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    51d1:	89 d0                	mov    %edx,%eax
    51d3:	29 f0                	sub    %esi,%eax
    51d5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    51dc:	0f 82 e2 d3 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    51e2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    51e5:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    51e9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    51ed:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    51f0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    51f7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    51fa:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5201:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5208:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    520a:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    520d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5212:	48 c1 e0 06          	shl    $0x6,%rax
    5216:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    521e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5224:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5227:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    522f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5233:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    523b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5243:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5247:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    524b:	e8 f0 d0 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5250:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5254:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5259:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5261:	0f 85 d7 01 00 00    	jne    543e <io_thread+0x49e>
    5267:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    526c:	4d 89 ce             	mov    %r9,%r14
    526f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5274:	0f 1f 40 00          	nopl   0x0(%rax)
    5278:	48 8d 3d 34 1f 00 00 	lea    0x1f34(%rip),%rdi        # 71b3 <_IO_stdin_used+0x1b3>
    527f:	e8 6c d0 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5284:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    528b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5292:	c1 e9 0b             	shr    $0xb,%ecx
    5295:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5298:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    52a0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    52a2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    52aa:	8b 16                	mov    (%rsi),%edx
		if (!available)
    52ac:	39 d0                	cmp    %edx,%eax
    52ae:	74 36                	je     52e6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    52b0:	89 f8                	mov    %edi,%eax
    52b2:	21 d0                	and    %edx,%eax
    52b4:	d3 e0                	shl    %cl,%eax
    52b6:	48 c1 e0 04          	shl    $0x4,%rax
    52ba:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    52c2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    52ca:	0f 85 a8 01 00 00    	jne    5478 <io_thread+0x4d8>
    52d0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    52d4:	0f 85 0e 03 00 00    	jne    55e8 <io_thread+0x648>
			if (cqe->res < 0)
    52da:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    52dd:	83 c2 01             	add    $0x1,%edx
    52e0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    52e2:	85 c0                	test   %eax,%eax
    52e4:	79 b2                	jns    5298 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    52e6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    52ef:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    52f0:	45 31 c0             	xor    %r8d,%r8d
    52f3:	31 d2                	xor    %edx,%edx
    52f5:	b9 01 00 00 00       	mov    $0x1,%ecx
    52fa:	4c 89 f6             	mov    %r14,%rsi
    52fd:	48 89 df             	mov    %rbx,%rdi
    5300:	e8 3b d1 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5305:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5308:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    530d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5311:	0f 84 e1 02 00 00    	je     55f8 <io_thread+0x658>
    5317:	48 8d 3d bb 1e 00 00 	lea    0x1ebb(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    531e:	e8 cd cf ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5323:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5328:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    532b:	45 85 ff             	test   %r15d,%r15d
    532e:	0f 88 62 d2 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    5334:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5337:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    533b:	85 c0                	test   %eax,%eax
    533d:	0f 88 d5 02 00 00    	js     5618 <io_thread+0x678>
      switch (req->event_type) {
    5343:	41 83 f8 01          	cmp    $0x1,%r8d
    5347:	0f 84 7b 01 00 00    	je     54c8 <io_thread+0x528>
    534d:	41 83 f8 02          	cmp    $0x2,%r8d
    5351:	0f 84 a1 01 00 00    	je     54f8 <io_thread+0x558>
    5357:	45 85 c0             	test   %r8d,%r8d
    535a:	0f 85 50 01 00 00    	jne    54b0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5360:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5365:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    536a:	48 89 d9             	mov    %rbx,%rcx
    536d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5371:	e8 8a fb ff ff       	call   4f00 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5376:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    537b:	48 89 de             	mov    %rbx,%rsi
    537e:	8b 78 08             	mov    0x8(%rax),%edi
    5381:	e8 1a f5 ff ff       	call   48a0 <add_read_request>
              free(req);
    5386:	4c 89 e7             	mov    %r12,%rdi
    5389:	e8 32 cf ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    538e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5393:	48 85 c0             	test   %rax,%rax
    5396:	0f 85 14 01 00 00    	jne    54b0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    539c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    53a3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    53aa:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    53ad:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    53b2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    53b4:	f6 c1 02             	test   $0x2,%cl
    53b7:	74 00                	je     53b9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    53b9:	89 d0                	mov    %edx,%eax
    53bb:	29 f0                	sub    %esi,%eax
    53bd:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    53c4:	0f 82 f0 d1 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    53ca:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    53cd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    53d2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    53d6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53d9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    53e0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53e3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    53ea:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53f1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    53f3:	8b 55 60             	mov    0x60(%rbp),%edx
    53f6:	48 c1 e0 06          	shl    $0x6,%rax
    53fa:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5402:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5408:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    540b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5413:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5417:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    541f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5427:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    542b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    542f:	e8 0c cf ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5434:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5438:	0f 84 3a fe ff ff    	je     5278 <io_thread+0x2d8>
    543e:	48 8d 3d cd 1d 00 00 	lea    0x1dcd(%rip),%rdi        # 7212 <_IO_stdin_used+0x212>
    5445:	e8 a6 ce ff ff       	call   22f0 <puts@plt>
}
    544a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5452:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    545b:	0f 85 18 02 00 00    	jne    5679 <io_thread+0x6d9>
    5461:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5468:	31 c0                	xor    %eax,%eax
    546a:	5b                   	pop    %rbx
    546b:	5d                   	pop    %rbp
    546c:	41 5c                	pop    %r12
    546e:	41 5d                	pop    %r13
    5470:	41 5e                	pop    %r14
    5472:	41 5f                	pop    %r15
    5474:	c3                   	ret
    5475:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5478:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    547d:	48 85 c0             	test   %rax,%rax
    5480:	0f 84 6a fe ff ff    	je     52f0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5486:	48 83 38 01          	cmpq   $0x1,(%rax)
    548a:	0f 84 68 01 00 00    	je     55f8 <io_thread+0x658>
    5490:	48 8d 3d 42 1d 00 00 	lea    0x1d42(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    5497:	e8 54 ce ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    549c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    54a1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    54a4:	e9 8b fe ff ff       	jmp    5334 <io_thread+0x394>
    54a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    54b0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    54b8:	8b 02                	mov    (%rdx),%eax
    54ba:	83 c0 01             	add    $0x1,%eax
    54bd:	89 02                	mov    %eax,(%rdx)
}
    54bf:	e9 d8 fe ff ff       	jmp    539c <io_thread+0x3fc>
    54c4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    54c8:	85 c0                	test   %eax,%eax
    54ca:	75 74                	jne    5540 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    54cc:	48 8b 0d 4d 4b 00 00 	mov    0x4b4d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    54d3:	ba 0f 00 00 00       	mov    $0xf,%edx
    54d8:	be 01 00 00 00       	mov    $0x1,%esi
    54dd:	48 8d 3d 1e 1d 00 00 	lea    0x1d1e(%rip),%rdi        # 7202 <_IO_stdin_used+0x202>
    54e4:	e8 d7 cf ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    54e9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    54ee:	e9 a0 fe ff ff       	jmp    5393 <io_thread+0x3f3>
    54f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    54f8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    54fd:	45 31 ff             	xor    %r15d,%r15d
    5500:	85 c0                	test   %eax,%eax
    5502:	7e 20                	jle    5524 <io_thread+0x584>
    5504:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5508:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    550b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    550f:	48 c1 e0 04          	shl    $0x4,%rax
    5513:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5518:	e8 a3 cd ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    551d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5522:	7f e4                	jg     5508 <io_thread+0x568>
              close(req->client_socket);
    5524:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5529:	e8 42 ce ff ff       	call   2370 <close@plt>
              free(req);
    552e:	4c 89 e7             	mov    %r12,%rdi
    5531:	e8 8a cd ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5536:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    553b:	e9 53 fe ff ff       	jmp    5393 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5540:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5545:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    554a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5552:	eb 11                	jmp    5565 <io_thread+0x5c5>
    5554:	0f 1f 40 00          	nopl   0x0(%rax)
    5558:	48 83 c0 01          	add    $0x1,%rax
    555c:	48 83 c2 01          	add    $0x1,%rdx
    5560:	48 39 c6             	cmp    %rax,%rsi
    5563:	74 4b                	je     55b0 <io_thread+0x610>
        dest[i] = src[i];
    5565:	0f b6 0a             	movzbl (%rdx),%ecx
    5568:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    556a:	80 f9 0d             	cmp    $0xd,%cl
    556d:	75 e9                	jne    5558 <io_thread+0x5b8>
    556f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5573:	75 e3                	jne    5558 <io_thread+0x5b8>
            dest[i] = '\0';
    5575:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5578:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    557d:	48 89 da             	mov    %rbx,%rdx
    5580:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5585:	e8 96 f7 ff ff       	call   4d20 <handle_http_method>
              free(req->iov[0].iov_base);
    558a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    558f:	e8 2c cd ff ff       	call   22c0 <free@plt>
              free(req);
    5594:	4c 89 e7             	mov    %r12,%rdi
    5597:	e8 24 cd ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    559c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    55a1:	e9 ed fd ff ff       	jmp    5393 <io_thread+0x3f3>
    55a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    55b0:	48 8b 0d 69 4a 00 00 	mov    0x4a69(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    55b7:	ba 12 00 00 00       	mov    $0x12,%edx
    55bc:	be 01 00 00 00       	mov    $0x1,%esi
    55c1:	48 8d 3d 90 1b 00 00 	lea    0x1b90(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    55c8:	e8 f3 ce ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    55cd:	bf 01 00 00 00       	mov    $0x1,%edi
    55d2:	e8 c9 ce ff ff       	call   24a0 <exit@plt>
    55d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    55e0:	e9 ec fb ff ff       	jmp    51d1 <io_thread+0x231>
    55e5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    55e8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    55ed:	e9 94 fe ff ff       	jmp    5486 <io_thread+0x4e6>
    55f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    55f8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5600:	48 8d 3d be 1b 00 00 	lea    0x1bbe(%rip),%rdi        # 71c5 <_IO_stdin_used+0x1c5>
    5607:	8b 02                	mov    (%rdx),%eax
    5609:	83 c0 01             	add    $0x1,%eax
    560c:	89 02                	mov    %eax,(%rdx)
    560e:	e8 dd cc ff ff       	call   22f0 <puts@plt>
    5613:	e9 26 fe ff ff       	jmp    543e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5618:	f7 d8                	neg    %eax
    561a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    561f:	89 c7                	mov    %eax,%edi
    5621:	e8 da ce ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5626:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    562b:	be 01 00 00 00       	mov    $0x1,%esi
    5630:	48 8b 3d e9 49 00 00 	mov    0x49e9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5637:	48 89 c1             	mov    %rax,%rcx
    563a:	48 8d 15 ef 1e 00 00 	lea    0x1eef(%rip),%rdx        # 7530 <_IO_stdin_used+0x530>
    5641:	31 c0                	xor    %eax,%eax
    5643:	e8 88 ce ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5648:	bf 01 00 00 00       	mov    $0x1,%edi
    564d:	e8 4e ce ff ff       	call   24a0 <exit@plt>
    5652:	48 8b 0d c7 49 00 00 	mov    0x49c7(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5659:	ba 28 00 00 00       	mov    $0x28,%edx
    565e:	be 01 00 00 00       	mov    $0x1,%esi
    5663:	48 8d 3d 96 1e 00 00 	lea    0x1e96(%rip),%rdi        # 7500 <_IO_stdin_used+0x500>
    566a:	e8 51 ce ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    566f:	bf 01 00 00 00       	mov    $0x1,%edi
    5674:	e8 27 ce ff ff       	call   24a0 <exit@plt>
}
    5679:	e8 b2 cc ff ff       	call   2330 <__stack_chk_fail@plt>
    567e:	66 90                	xchg   %ax,%ax

0000000000005680 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5680:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5684:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    568b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5691:	85 c9                	test   %ecx,%ecx
    5693:	0f 8e ea 00 00 00    	jle    5783 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    5699:	41 56                	push   %r14
    569b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    569d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    56a0:	41 54                	push   %r12
    56a2:	49 89 fc             	mov    %rdi,%r12
    56a5:	55                   	push   %rbp
    56a6:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    56a7:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    56ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    56b0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    56b4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    56bc:	31 db                	xor    %ebx,%ebx
    56be:	8b 10                	mov    (%rax),%edx
    56c0:	85 d2                	test   %edx,%edx
    56c2:	7e 26                	jle    56ea <barriered_work_ingest+0x6a>
    56c4:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    56c8:	48 89 dd             	mov    %rbx,%rbp
    56cb:	48 c1 e5 08          	shl    $0x8,%rbp
    56cf:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    56d3:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    56da:	74 24                	je     5700 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    56dc:	48 83 c3 01          	add    $0x1,%rbx
    56e0:	39 da                	cmp    %ebx,%edx
    56e2:	7f e4                	jg     56c8 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    56e4:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    56ea:	49 83 c5 01          	add    $0x1,%r13
    56ee:	44 39 e9             	cmp    %r13d,%ecx
    56f1:	7f bd                	jg     56b0 <barriered_work_ingest+0x30>
}
    56f3:	5b                   	pop    %rbx
    56f4:	31 c0                	xor    %eax,%eax
    56f6:	5d                   	pop    %rbp
    56f7:	41 5c                	pop    %r12
    56f9:	41 5d                	pop    %r13
    56fb:	41 5e                	pop    %r14
    56fd:	c3                   	ret
    56fe:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    5700:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5709:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5710:	bf 04 00 00 00       	mov    $0x4,%edi
    5715:	48 c1 e6 05          	shl    $0x5,%rsi
    5719:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5720:	48 83 c6 10          	add    $0x10,%rsi
    5724:	e8 e7 cb ff ff       	call   2310 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5729:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5731:	48 8b 40 50          	mov    0x50(%rax),%rax
    5735:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5739:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    573d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5747:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    574d:	83 c0 01             	add    $0x1,%eax
    5750:	99                   	cltd
    5751:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5757:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    575d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5760:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5768:	48 83 c3 01          	add    $0x1,%rbx
    576c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5770:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5774:	8b 10                	mov    (%rax),%edx
    5776:	39 da                	cmp    %ebx,%edx
    5778:	0f 8f 46 ff ff ff    	jg     56c4 <barriered_work_ingest+0x44>
    577e:	e9 61 ff ff ff       	jmp    56e4 <barriered_work_ingest+0x64>
}
    5783:	31 c0                	xor    %eax,%eax
    5785:	c3                   	ret
    5786:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005790 <barriered_thread>:
void* barriered_thread(void *arg) {
    5790:	f3 0f 1e fa          	endbr64
    5794:	41 56                	push   %r14
    5796:	41 55                	push   %r13
    5798:	41 54                	push   %r12
  int t = 0;
    579a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    579d:	55                   	push   %rbp
  int waiting = 0;
    579e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    57a0:	53                   	push   %rbx
    57a1:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    57a4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    57a8:	0f 85 74 02 00 00    	jne    5a22 <barriered_thread+0x292>
    if (t >= data->task_count) {
    57ae:	8b 43 40             	mov    0x40(%rbx),%eax
    57b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    57b8:	41 39 c4             	cmp    %eax,%r12d
    57bb:	0f 8d 6f 01 00 00    	jge    5930 <barriered_thread+0x1a0>
    57c1:	49 63 fc             	movslq %r12d,%rdi
    57c4:	48 c1 e7 09          	shl    $0x9,%rdi
    57c8:	49 89 fd             	mov    %rdi,%r13
    57cb:	eb 32                	jmp    57ff <barriered_thread+0x6f>
    57cd:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    57d0:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    57d4:	48 8b 43 18          	mov    0x18(%rbx),%rax
    57d8:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    57dc:	48 8b 78 38          	mov    0x38(%rax),%rdi
    57e0:	4c 01 ef             	add    %r13,%rdi
    57e3:	e8 98 fe ff ff       	call   5680 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    57e8:	8b 43 40             	mov    0x40(%rbx),%eax
    57eb:	41 83 c4 01          	add    $0x1,%r12d
    57ef:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    57f6:	44 39 e0             	cmp    %r12d,%eax
    57f9:	0f 8e 19 02 00 00    	jle    5a18 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    57ff:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5803:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    5807:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    580e:	75 c0                	jne    57d0 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5810:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    5814:	83 e8 01             	sub    $0x1,%eax
    5817:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    581c:	45 85 e4             	test   %r12d,%r12d
    581f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5822:	45 85 c0             	test   %r8d,%r8d
    5825:	0f 8e 2d 01 00 00    	jle    5958 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    582b:	48 63 c8             	movslq %eax,%rcx
    582e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5832:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5835:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    583b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    5842:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    5846:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    5849:	45 31 f6             	xor    %r14d,%r14d
    584c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5850:	48 8b 10             	mov    (%rax),%rdx
    5853:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    5857:	49 01 cb             	add    %rcx,%r11
    585a:	4c 89 da             	mov    %r11,%rdx
    585d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    5864:	75 04                	jne    586a <barriered_thread+0xda>
            arrived++;
    5866:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    586a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    5870:	75 04                	jne    5876 <barriered_thread+0xe6>
            prearrive++;
    5872:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5876:	48 83 c0 08          	add    $0x8,%rax
    587a:	48 39 c6             	cmp    %rax,%rsi
    587d:	75 d1                	jne    5850 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    587f:	45 85 d2             	test   %r10d,%r10d
    5882:	0f 84 c0 00 00 00    	je     5948 <barriered_thread+0x1b8>
    5888:	45 39 d0             	cmp    %r10d,%r8d
    588b:	0f 84 b7 00 00 00    	je     5948 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    5891:	45 85 f6             	test   %r14d,%r14d
    5894:	74 0a                	je     58a0 <barriered_thread+0x110>
    5896:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    589a:	0f 85 ae 01 00 00    	jne    5a4e <barriered_thread+0x2be>
    58a0:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    58a4:	4c 01 ea             	add    %r13,%rdx
    58a7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    58ae:	45 85 e4             	test   %r12d,%r12d
    58b1:	75 14                	jne    58c7 <barriered_thread+0x137>
    58b3:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    58ba:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    58c1:	0f 8c 69 01 00 00    	jl     5a30 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    58c7:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    58cb:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    58cf:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    58d9:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    58dd:	48 8b 78 38          	mov    0x38(%rax),%rdi
    58e1:	4c 01 ef             	add    %r13,%rdi
    58e4:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    58ea:	48 8b 43 38          	mov    0x38(%rbx),%rax
    58ee:	4c 01 e8             	add    %r13,%rax
    58f1:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    58f8:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    58fb:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5900:	83 e8 01             	sub    $0x1,%eax
    5903:	44 39 e0             	cmp    %r12d,%eax
    5906:	0f 84 a4 00 00 00    	je     59b0 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    590c:	0f ae f8             	sfence
          if (waiting == 0) {
    590f:	85 ed                	test   %ebp,%ebp
    5911:	0f 84 d1 00 00 00    	je     59e8 <barriered_thread+0x258>
        int arrived = 0; 
    5917:	bd 01 00 00 00       	mov    $0x1,%ebp
    591c:	e9 c7 fe ff ff       	jmp    57e8 <barriered_thread+0x58>
  while (data->running == 1) {
    5921:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5925:	0f 85 f7 00 00 00    	jne    5a22 <barriered_thread+0x292>
    592b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    5930:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    5938:	85 c0                	test   %eax,%eax
    593a:	7e e5                	jle    5921 <barriered_thread+0x191>
    593c:	45 31 e4             	xor    %r12d,%r12d
    593f:	e9 7d fe ff ff       	jmp    57c1 <barriered_thread+0x31>
    5944:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5948:	83 fd 01             	cmp    $0x1,%ebp
    594b:	74 1b                	je     5968 <barriered_thread+0x1d8>
        int arrived = 0; 
    594d:	31 ed                	xor    %ebp,%ebp
    594f:	e9 3d ff ff ff       	jmp    5891 <barriered_thread+0x101>
    5954:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5958:	83 fd 01             	cmp    $0x1,%ebp
    595b:	0f 85 43 ff ff ff    	jne    58a4 <barriered_thread+0x114>
        int arrived = 0; 
    5961:	45 31 f6             	xor    %r14d,%r14d
    5964:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5968:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    596f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    5974:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5976:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    597a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5981:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    5986:	e8 85 c9 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    598b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5992:	48 83 c0 01          	add    $0x1,%rax
    5996:	48 99                	cqto
    5998:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    599f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    59a6:	e9 e6 fe ff ff       	jmp    5891 <barriered_thread+0x101>
    59ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    59b0:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    59b7:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    59be:	0f 8d 48 ff ff ff    	jge    590c <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    59c4:	48 c1 e6 04          	shl    $0x4,%rsi
    59c8:	bf 04 00 00 00       	mov    $0x4,%edi
    59cd:	48 03 73 70          	add    0x70(%rbx),%rsi
    59d1:	e8 3a c9 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    59d6:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    59de:	e9 29 ff ff ff       	jmp    590c <barriered_thread+0x17c>
    59e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    59e8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    59ef:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    59f4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    59f8:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    59ff:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5a03:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5a07:	e8 04 c9 ff ff       	call   2310 <clock_gettime@plt>
            waiting = 1;
    5a0c:	e9 06 ff ff ff       	jmp    5917 <barriered_thread+0x187>
    5a11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    5a18:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5a1c:	0f 84 96 fd ff ff    	je     57b8 <barriered_thread+0x28>
}
    5a22:	5b                   	pop    %rbx
    5a23:	31 c0                	xor    %eax,%eax
    5a25:	5d                   	pop    %rbp
    5a26:	41 5c                	pop    %r12
    5a28:	41 5d                	pop    %r13
    5a2a:	41 5e                	pop    %r14
    5a2c:	c3                   	ret
    5a2d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    5a30:	48 c1 e6 04          	shl    $0x4,%rsi
    5a34:	bf 04 00 00 00       	mov    $0x4,%edi
    5a39:	48 03 73 68          	add    0x68(%rbx),%rsi
    5a3d:	e8 ce c8 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    5a42:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5a46:	4c 01 ea             	add    %r13,%rdx
    5a49:	e9 79 fe ff ff       	jmp    58c7 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5a4e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5a52:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5a56:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5a5a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5a5e:	4c 01 ef             	add    %r13,%rdi
    5a61:	e8 1a fc ff ff       	call   5680 <barriered_work_ingest>
          break;
    5a66:	e9 39 fd ff ff       	jmp    57a4 <barriered_thread+0x14>
    5a6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005a70 <receive>:
int receive(struct BarrierTask *data) {
    5a70:	f3 0f 1e fa          	endbr64
    5a74:	41 57                	push   %r15
    5a76:	41 56                	push   %r14
    5a78:	41 55                	push   %r13
    5a7a:	41 54                	push   %r12
    5a7c:	55                   	push   %rbp
    5a7d:	53                   	push   %rbx
    5a7e:	48 83 ec 08          	sub    $0x8,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5a82:	48 63 87 40 01 00 00 	movslq 0x140(%rdi),%rax
    5a89:	85 c0                	test   %eax,%eax
    5a8b:	0f 8e 05 01 00 00    	jle    5b96 <receive+0x126>
    5a91:	48 8b b7 70 01 00 00 	mov    0x170(%rdi),%rsi
    5a98:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    5aa0:	48 89 fa             	mov    %rdi,%rdx
    5aa3:	48 29 c1             	sub    %rax,%rcx
    5aa6:	4c 8d 2c ce          	lea    (%rsi,%rcx,8),%r13
    5aaa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5ab0:	44 8b 66 30          	mov    0x30(%rsi),%r12d
    struct Data *me = data->mailboxes[n].lower;
    5ab4:	48 8b 2e             	mov    (%rsi),%rbp
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5ab7:	41 83 fc 02          	cmp    $0x2,%r12d
    5abb:	0f 84 07 01 00 00    	je     5bc8 <receive+0x158>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5ac1:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    5ac8:	48 85 ff             	test   %rdi,%rdi
    5acb:	0f 8e ad 00 00 00    	jle    5b7e <receive+0x10e>
      data->sends++;
    5ad1:	4c 8b 8a 78 01 00 00 	mov    0x178(%rdx),%r9
      data->n++;
    5ad8:	4c 8b 82 08 01 00 00 	mov    0x108(%rdx),%r8
      data->mailboxes[n].received++;
    5adf:	31 c0                	xor    %eax,%eax
    5ae1:	48 8b 4e 28          	mov    0x28(%rsi),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5ae5:	48 8b 5d 00          	mov    0x0(%rbp),%rbx
    5ae9:	4d 8d 51 01          	lea    0x1(%r9),%r10
    5aed:	4c 63 5a 04          	movslq 0x4(%rdx),%r11
    5af1:	4d 8d 48 01          	lea    0x1(%r8),%r9
    5af5:	4c 8d 41 01          	lea    0x1(%rcx),%r8
    5af9:	eb 0e                	jmp    5b09 <receive+0x99>
    5afb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5b00:	48 83 c0 01          	add    $0x1,%rax
    5b04:	48 39 f8             	cmp    %rdi,%rax
    5b07:	7d 6f                	jge    5b78 <receive+0x108>
      data->sends++;
    5b09:	49 8d 0c 02          	lea    (%r10,%rax,1),%rcx
    5b0d:	48 89 8a 78 01 00 00 	mov    %rcx,0x178(%rdx)
      data->n++;
    5b14:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    5b18:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5b1f:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5b23:	48 89 4e 28          	mov    %rcx,0x28(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5b27:	48 8b 0c c3          	mov    (%rbx,%rax,8),%rcx
    5b2b:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5b2f:	75 cf                	jne    5b00 <receive+0x90>
    5b31:	4c 8b b2 28 01 00 00 	mov    0x128(%rdx),%r14
    5b38:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    5b3c:	4d 63 7e 08          	movslq 0x8(%r14),%r15
    5b40:	4c 39 f9             	cmp    %r15,%rcx
    5b43:	75 bb                	jne    5b00 <receive+0x90>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    5b45:	49 63 46 04          	movslq 0x4(%r14),%rax
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5b49:	bf 01 00 00 00       	mov    $0x1,%edi
    5b4e:	ba 01 00 00 00       	mov    $0x1,%edx
    5b53:	48 8d 35 fe 19 00 00 	lea    0x19fe(%rip),%rsi        # 7558 <_IO_stdin_used+0x558>
    5b5a:	48 39 c8             	cmp    %rcx,%rax
    5b5d:	0f 94 c1             	sete   %cl
    5b60:	31 c0                	xor    %eax,%eax
    5b62:	0f b6 c9             	movzbl %cl,%ecx
    5b65:	e8 e6 c8 ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5b6a:	bf 01 00 00 00       	mov    $0x1,%edi
    5b6f:	e8 2c c9 ff ff       	call   24a0 <exit@plt>
    5b74:	0f 1f 40 00          	nopl   0x0(%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5b78:	41 83 fc 02          	cmp    $0x2,%r12d
    5b7c:	74 32                	je     5bb0 <receive+0x140>
    me->messages_count = 0;
    5b7e:	48 c7 85 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rbp)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5b89:	48 83 c6 38          	add    $0x38,%rsi
    5b8d:	49 39 f5             	cmp    %rsi,%r13
    5b90:	0f 85 1a ff ff ff    	jne    5ab0 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    5b96:	0f ae f8             	sfence
}
    5b99:	48 83 c4 08          	add    $0x8,%rsp
    5b9d:	31 c0                	xor    %eax,%eax
    5b9f:	5b                   	pop    %rbx
    5ba0:	5d                   	pop    %rbp
    5ba1:	41 5c                	pop    %r12
    5ba3:	41 5d                	pop    %r13
    5ba5:	41 5e                	pop    %r14
    5ba7:	41 5f                	pop    %r15
    5ba9:	c3                   	ret
    5baa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5bb0:	83 bd 00 01 00 00 01 	cmpl   $0x1,0x100(%rbp)
    5bb7:	75 c5                	jne    5b7e <receive+0x10e>
      me->available = 0;
    5bb9:	c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbp)
    5bc3:	eb b9                	jmp    5b7e <receive+0x10e>
    5bc5:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5bc8:	8b 85 00 01 00 00    	mov    0x100(%rbp),%eax
    5bce:	83 f8 01             	cmp    $0x1,%eax
    5bd1:	74 09                	je     5bdc <receive+0x16c>
    else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 0) {
    5bd3:	85 c0                	test   %eax,%eax
    5bd5:	74 b2                	je     5b89 <receive+0x119>
    5bd7:	e9 e5 fe ff ff       	jmp    5ac1 <receive+0x51>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5bdc:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    5be3:	48 85 ff             	test   %rdi,%rdi
    5be6:	0f 8f e5 fe ff ff    	jg     5ad1 <receive+0x61>
    5bec:	eb cb                	jmp    5bb9 <receive+0x149>
    5bee:	66 90                	xchg   %ax,%ax

0000000000005bf0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5bf0:	f3 0f 1e fa          	endbr64
    5bf4:	41 57                	push   %r15
    5bf6:	41 56                	push   %r14
    5bf8:	41 55                	push   %r13
    5bfa:	41 54                	push   %r12
    5bfc:	55                   	push   %rbp
    5bfd:	53                   	push   %rbx
    5bfe:	48 89 fb             	mov    %rdi,%rbx
    5c01:	48 83 ec 08          	sub    $0x8,%rsp
  if (data->thread_index == data->task_index) {
    5c05:	8b 47 04             	mov    0x4(%rdi),%eax
    5c08:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    5c0e:	74 50                	je     5c60 <barriered_work+0x70>
    receive(data);
    5c10:	e8 5b fe ff ff       	call   5a70 <receive>
    while (data->scheduled == 1) {
    5c15:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    5c1c:	75 16                	jne    5c34 <barriered_work+0x44>
    5c1e:	66 90                	xchg   %ax,%ax
      data->n++;
    5c20:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    5c28:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5c2b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    5c32:	74 ec                	je     5c20 <barriered_work+0x30>
  if (data->sending == 1) {
    5c34:	83 bb 80 01 00 00 01 	cmpl   $0x1,0x180(%rbx)
    5c3b:	75 08                	jne    5c45 <barriered_work+0x55>
    5c3d:	48 89 df             	mov    %rbx,%rdi
    5c40:	e8 7b e2 ff ff       	call   3ec0 <sendm.part.0>
  asm volatile ("sfence" ::: "memory");
    5c45:	0f ae f8             	sfence
}
    5c48:	48 83 c4 08          	add    $0x8,%rsp
    5c4c:	31 c0                	xor    %eax,%eax
    5c4e:	5b                   	pop    %rbx
    5c4f:	5d                   	pop    %rbp
    5c50:	41 5c                	pop    %r12
    5c52:	41 5d                	pop    %r13
    5c54:	41 5e                	pop    %r14
    5c56:	41 5f                	pop    %r15
    5c58:	c3                   	ret
    5c59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      receive(data);
    5c60:	e8 0b fe ff ff       	call   5a70 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    5c65:	8b bb 40 01 00 00    	mov    0x140(%rbx),%edi
        int t = data->task_index;
    5c6b:	8b 43 04             	mov    0x4(%rbx),%eax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    5c6e:	85 ff                	test   %edi,%edi
    5c70:	0f 8e fa 00 00 00    	jle    5d70 <barriered_work+0x180>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    5c76:	4c 63 e0             	movslq %eax,%r12
              int next_task = abs((t + 1) % (data->thread_count));
    5c79:	83 c0 01             	add    $0x1,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    5c7c:	48 8b ab 28 01 00 00 	mov    0x128(%rbx),%rbp
              int next_task = abs((t + 1) % (data->thread_count));
    5c83:	99                   	cltd
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    5c84:	49 c1 e4 09          	shl    $0x9,%r12
              int next_task = abs((t + 1) % (data->thread_count));
    5c88:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    5c8e:	4c 8b 5d 20          	mov    0x20(%rbp),%r11
    5c92:	4d 8d 73 38          	lea    0x38(%r11),%r14
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    5c96:	4d 89 f5             	mov    %r14,%r13
              int next_task = abs((t + 1) % (data->thread_count));
    5c99:	89 d0                	mov    %edx,%eax
    5c9b:	f7 d8                	neg    %eax
    5c9d:	0f 49 d0             	cmovns %eax,%edx
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    5ca0:	45 31 c0             	xor    %r8d,%r8d
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    5ca3:	45 31 d2             	xor    %r10d,%r10d
              int next_task = abs((t + 1) % (data->thread_count));
    5ca6:	4c 63 ca             	movslq %edx,%r9
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    5ca9:	49 c1 e1 09          	shl    $0x9,%r9
    5cad:	0f 1f 00             	nopl   (%rax)
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    5cb0:	49 8b 45 00          	mov    0x0(%r13),%rax
    5cb4:	4c 89 f6             	mov    %r14,%rsi
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    5cb7:	31 d2                	xor    %edx,%edx
    5cb9:	4a 8b 84 20 70 01 00 00 	mov    0x170(%rax,%r12,1),%rax
    5cc1:	eb 4f                	jmp    5d12 <barriered_work+0x122>
    5cc3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                 if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 0 && ((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->available == 0 /*&& ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available == 0 */) {
    5cc8:	44 8b b9 00 01 00 00 	mov    0x100(%rcx),%r15d
    5ccf:	45 85 ff             	test   %r15d,%r15d
    5cd2:	75 2c                	jne    5d00 <barriered_work+0x110>
    5cd4:	4c 8b 38             	mov    (%rax),%r15
    5cd7:	45 8b bf 00 01 00 00 	mov    0x100(%r15),%r15d
    5cde:	45 85 ff             	test   %r15d,%r15d
    5ce1:	75 1d                	jne    5d00 <barriered_work+0x110>
                  if (y == data->thread->real_thread_index || b == data->thread->real_thread_index) {
    5ce3:	44 8b 7d 08          	mov    0x8(%rbp),%r15d
    5ce7:	41 39 d7             	cmp    %edx,%r15d
    5cea:	0f 84 50 01 00 00    	je     5e40 <barriered_work+0x250>
    5cf0:	45 39 d7             	cmp    %r10d,%r15d
    5cf3:	0f 84 47 01 00 00    	je     5e40 <barriered_work+0x250>
    5cf9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    5d00:	83 c2 01             	add    $0x1,%edx
    5d03:	48 83 c0 38          	add    $0x38,%rax
    5d07:	48 81 c6 c0 00 00 00 	add    $0xc0,%rsi
    5d0e:	39 fa                	cmp    %edi,%edx
    5d10:	74 46                	je     5d58 <barriered_work+0x168>
              if (kind == MAILBOX_FRIEND) {
    5d12:	83 78 30 01          	cmpl   $0x1,0x30(%rax)
                  void * _a = data->thread->all_threads[y].tasks[t].mailboxes[b].higher;
    5d16:	48 8b 48 08          	mov    0x8(%rax),%rcx
              if (kind == MAILBOX_FRIEND) {
    5d1a:	75 ac                	jne    5cc8 <barriered_work+0xd8>
                  void * _b = data->thread->all_threads[y].tasks[t].mailboxes[b].lower;
    5d1c:	66 48 0f 6e c9       	movq   %rcx,%xmm1
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    5d21:	48 63 48 34          	movslq 0x34(%rax),%rcx
    5d25:	0f 16 08             	movhps (%rax),%xmm1
    5d28:	48 8d 0c 49          	lea    (%rcx,%rcx,2),%rcx
    5d2c:	48 c1 e1 06          	shl    $0x6,%rcx
    5d30:	49 8b 4c 0b 38       	mov    0x38(%r11,%rcx,1),%rcx
    5d35:	4e 8b bc 09 70 01 00 00 	mov    0x170(%rcx,%r9,1),%r15
    5d3d:	4d 01 c7             	add    %r8,%r15
                  void * _d = data->thread->all_threads[other].tasks[next_task].mailboxes[y].lower;
    5d40:	f3 41 0f 6f 07       	movdqu (%r15),%xmm0
    5d45:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
                  data->thread->all_threads[y].tasks[t].mailboxes[b].lower = _c;
    5d4a:	0f 11 00             	movups %xmm0,(%rax)
                  data->thread->all_threads[other].tasks[next_task].mailboxes[y].lower = _a;
    5d4d:	41 0f 11 0f          	movups %xmm1,(%r15)
    5d51:	eb ad                	jmp    5d00 <barriered_work+0x110>
    5d53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    5d58:	41 83 c2 01          	add    $0x1,%r10d
    5d5c:	49 81 c5 c0 00 00 00 	add    $0xc0,%r13
    5d63:	49 83 c0 38          	add    $0x38,%r8
    5d67:	41 39 fa             	cmp    %edi,%r10d
    5d6a:	0f 85 40 ff ff ff    	jne    5cb0 <barriered_work+0xc0>
      asm volatile ("sfence" ::: "memory");
    5d70:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5d73:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    5d7a:	31 ff                	xor    %edi,%edi
    5d7c:	48 c1 e6 05          	shl    $0x5,%rsi
    5d80:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    5d87:	e8 84 c5 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5d8c:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5d93:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5d9a:	48 8b 50 48          	mov    0x48(%rax),%rdx
    5d9e:	8b 72 10             	mov    0x10(%rdx),%esi
    5da1:	8d 6e 01             	lea    0x1(%rsi),%ebp
    5da4:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5da7:	75 58                	jne    5e01 <barriered_work+0x211>
    5da9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5db0:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    5db7:	48 8b 40 18          	mov    0x18(%rax),%rax
    5dbb:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
      data->n++;
    5dbf:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5dc7:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5dcb:	48 c1 e7 09          	shl    $0x9,%rdi
    5dcf:	48 03 78 38          	add    0x38(%rax),%rdi
    5dd3:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    5dd9:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5ddc:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    5de3:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5dea:	74 c4                	je     5db0 <barriered_work+0x1c0>
    if (modcount != data->thread->protected_state->modcount) {
    5dec:	48 8b 40 48          	mov    0x48(%rax),%rax
    5df0:	3b 68 10             	cmp    0x10(%rax),%ebp
    5df3:	74 0c                	je     5e01 <barriered_work+0x211>
    5df5:	48 8d 3d 29 14 00 00 	lea    0x1429(%rip),%rdi        # 7225 <_IO_stdin_used+0x225>
    5dfc:	e8 ef c4 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5e01:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    5e08:	31 ff                	xor    %edi,%edi
    5e0a:	48 c1 e6 05          	shl    $0x5,%rsi
    5e0e:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    5e15:	48 83 c6 10          	add    $0x10,%rsi
    5e19:	e8 f2 c4 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5e1e:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    5e25:	48 83 c0 01          	add    $0x1,%rax
    5e29:	48 99                	cqto
    5e2b:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    5e32:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    5e39:	e9 f6 fd ff ff       	jmp    5c34 <barriered_work+0x44>
    5e3e:	66 90                	xchg   %ax,%ax
                    void * _c = data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher;
    5e40:	4c 8b 3e             	mov    (%rsi),%r15
    5e43:	4f 8b bc 0f 70 01 00 00 	mov    0x170(%r15,%r9,1),%r15
    5e4b:	f3 43 0f 6f 04 07    	movdqu (%r15,%r8,1),%xmm0
                    void * _d = data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower;
    5e51:	66 0f 6f c8          	movdqa %xmm0,%xmm1
    5e55:	66 0f c6 c8 01       	shufpd $0x1,%xmm0,%xmm1
                    data->thread->all_threads[y].tasks[t].mailboxes[b].lower = _c;
    5e5a:	0f 11 08             	movups %xmm1,(%rax)
                    ((struct Data*)_a)->available = 1;
    5e5d:	c7 81 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rcx)
                    ((struct Data*)_d)->available = 1;
    5e67:	66 48 0f 7e c1       	movq   %xmm0,%rcx
    5e6c:	c7 81 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rcx)
    5e76:	e9 85 fe ff ff       	jmp    5d00 <barriered_work+0x110>
    5e7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005e80 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    5e80:	f3 0f 1e fa          	endbr64
    5e84:	53                   	push   %rbx
    5e85:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    5e88:	e8 f3 f7 ff ff       	call   5680 <barriered_work_ingest>
  barriered_work(data);
    5e8d:	48 89 df             	mov    %rbx,%rdi
}
    5e90:	5b                   	pop    %rbx
  barriered_work(data);
    5e91:	e9 5a fd ff ff       	jmp    5bf0 <barriered_work>
    5e96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005ea0 <sendm>:
int sendm(struct BarrierTask *data) {
    5ea0:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    5ea4:	83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%rdi)
    5eab:	74 03                	je     5eb0 <sendm+0x10>
}
    5ead:	31 c0                	xor    %eax,%eax
    5eaf:	c3                   	ret
int sendm(struct BarrierTask *data) {
    5eb0:	48 83 ec 08          	sub    $0x8,%rsp
    5eb4:	e8 07 e0 ff ff       	call   3ec0 <sendm.part.0>
}
    5eb9:	31 c0                	xor    %eax,%eax
    5ebb:	48 83 c4 08          	add    $0x8,%rsp
    5ebf:	c3                   	ret

0000000000005ec0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5ec0:	f3 0f 1e fa          	endbr64
}
    5ec4:	31 c0                	xor    %eax,%eax
    5ec6:	c3                   	ret
    5ec7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005ed0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5ed0:	f3 0f 1e fa          	endbr64
    5ed4:	31 c0                	xor    %eax,%eax
    5ed6:	c3                   	ret
    5ed7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005ee0 <after>:
int after(struct timespec left, struct timespec right) {
    5ee0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5ee4:	31 c0                	xor    %eax,%eax
    5ee6:	48 39 d7             	cmp    %rdx,%rdi
    5ee9:	7e 08                	jle    5ef3 <after+0x13>
    5eeb:	31 c0                	xor    %eax,%eax
    5eed:	48 39 ce             	cmp    %rcx,%rsi
    5ef0:	0f 9f c0             	setg   %al
}
    5ef3:	c3                   	ret
    5ef4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5eff:	90                   	nop

0000000000005f00 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5f00:	f3 0f 1e fa          	endbr64
    5f04:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5f09:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5f0e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f10:	48 39 d7             	cmp    %rdx,%rdi
    5f13:	7f 18                	jg     5f2d <within+0x2d>
    5f15:	4d 39 d8             	cmp    %r11,%r8
    5f18:	0f 9e c2             	setle  %dl
    5f1b:	48 39 ce             	cmp    %rcx,%rsi
    5f1e:	0f 9e c0             	setle  %al
    5f21:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5f23:	31 c0                	xor    %eax,%eax
    5f25:	4d 39 d1             	cmp    %r10,%r9
    5f28:	0f 9e c0             	setle  %al
    5f2b:	21 d0                	and    %edx,%eax
}
    5f2d:	c3                   	ret
    5f2e:	66 90                	xchg   %ax,%ax

0000000000005f30 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5f30:	f3 0f 1e fa          	endbr64
    5f34:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5f39:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5f3e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5f43:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5f48:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5f4d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5f52:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5f57:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5f5c:	48 39 fe             	cmp    %rdi,%rsi
    5f5f:	7d 2f                	jge    5f90 <overlap+0x60>
    5f61:	48 39 ca             	cmp    %rcx,%rdx
    5f64:	7d 62                	jge    5fc8 <overlap+0x98>
    5f66:	4d 39 da             	cmp    %r11,%r10
    5f69:	7d 0e                	jge    5f79 <overlap+0x49>
    return 1;
    5f6b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5f70:	4d 39 c1             	cmp    %r8,%r9
    5f73:	0f 8c 7f 00 00 00    	jl     5ff8 <overlap+0xc8>
  return 0;
    5f79:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f7b:	4d 39 c1             	cmp    %r8,%r9
    5f7e:	7f 4c                	jg     5fcc <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5f80:	31 c0                	xor    %eax,%eax
    5f82:	4d 39 da             	cmp    %r11,%r10
    5f85:	0f 9e c0             	setle  %al
    5f88:	c3                   	ret
    5f89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5f90:	7e 4e                	jle    5fe0 <overlap+0xb0>
    5f92:	48 39 ca             	cmp    %rcx,%rdx
    5f95:	7f 39                	jg     5fd0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f97:	75 31                	jne    5fca <overlap+0x9a>
    5f99:	4d 39 c1             	cmp    %r8,%r9
    5f9c:	7c 2c                	jl     5fca <overlap+0x9a>
    return 1;
    5f9e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5fa3:	4d 39 da             	cmp    %r11,%r10
    5fa6:	7d 24                	jge    5fcc <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5fa8:	48 39 ca             	cmp    %rcx,%rdx
    5fab:	0f 94 c2             	sete   %dl
    5fae:	48 39 fe             	cmp    %rdi,%rsi
    5fb1:	0f 94 c0             	sete   %al
    5fb4:	21 c2                	and    %eax,%edx
    5fb6:	31 c0                	xor    %eax,%eax
    5fb8:	4d 39 c1             	cmp    %r8,%r9
    5fbb:	0f 94 c0             	sete   %al
    5fbe:	21 d0                	and    %edx,%eax
    5fc0:	c3                   	ret
    5fc1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5fc8:	74 af                	je     5f79 <overlap+0x49>
  return 0;
    5fca:	31 c0                	xor    %eax,%eax
}
    5fcc:	c3                   	ret
    5fcd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5fd0:	4d 39 da             	cmp    %r11,%r10
    5fd3:	7e c4                	jle    5f99 <overlap+0x69>
    return 1;
    5fd5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5fda:	4d 39 c1             	cmp    %r8,%r9
    5fdd:	7e ba                	jle    5f99 <overlap+0x69>
    5fdf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5fe0:	48 39 ca             	cmp    %rcx,%rdx
    5fe3:	7c 94                	jl     5f79 <overlap+0x49>
    5fe5:	4d 39 c1             	cmp    %r8,%r9
    5fe8:	7d b4                	jge    5f9e <overlap+0x6e>
    5fea:	48 39 ca             	cmp    %rcx,%rdx
    5fed:	74 91                	je     5f80 <overlap+0x50>
    5fef:	eb d9                	jmp    5fca <overlap+0x9a>
    5ff1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5ff8:	c3                   	ret
    5ff9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006000 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6000:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6004:	85 f6                	test   %esi,%esi
    6006:	0f 8e 44 03 00 00    	jle    6350 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    600c:	41 57                	push   %r15
    600e:	41 89 f7             	mov    %esi,%r15d
    6011:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6013:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6016:	41 55                	push   %r13
    6018:	41 54                	push   %r12
    601a:	55                   	push   %rbp
    601b:	53                   	push   %rbx
    601c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6020:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6024:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6029:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    602e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6031:	45 39 e6             	cmp    %r12d,%r14d
    6034:	0f 84 4e 02 00 00    	je     6288 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    603a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    603f:	8b 50 08             	mov    0x8(%rax),%edx
    6042:	85 d2                	test   %edx,%edx
    6044:	0f 8e 3e 02 00 00    	jle    6288 <verify+0x288>
    604a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    604f:	31 c9                	xor    %ecx,%ecx
    6051:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    6056:	31 c0                	xor    %eax,%eax
    6058:	44 89 f2             	mov    %r14d,%edx
    605b:	bf 01 00 00 00       	mov    $0x1,%edi
    6060:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6065:	48 8d 35 c9 11 00 00 	lea    0x11c9(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    606c:	e8 df c3 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6071:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6076:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    607b:	8b 40 08             	mov    0x8(%rax),%eax
    607e:	85 c0                	test   %eax,%eax
    6080:	0f 8e e6 01 00 00    	jle    626c <verify+0x26c>
    6086:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6089:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    608e:	31 db                	xor    %ebx,%ebx
    6090:	48 c1 e0 09          	shl    $0x9,%rax
    6094:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6099:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    609e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    60a3:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    60a8:	4c 8b 20             	mov    (%rax),%r12
    60ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    60b0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    60b5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    60ba:	49 89 de             	mov    %rbx,%r14
    60bd:	48 8d 35 86 11 00 00 	lea    0x1186(%rip),%rsi        # 724a <_IO_stdin_used+0x24a>
    60c4:	49 c1 e6 09          	shl    $0x9,%r14
    60c8:	bf 01 00 00 00       	mov    $0x1,%edi
    60cd:	48 8b 45 00          	mov    0x0(%rbp),%rax
    60d1:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    60d9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    60de:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    60e6:	31 c0                	xor    %eax,%eax
    60e8:	e8 63 c3 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60ed:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    60f2:	4c 8b 20             	mov    (%rax),%r12
    60f5:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    60fe:	0f 8e 47 01 00 00    	jle    624b <verify+0x24b>
    6104:	4c 03 75 00          	add    0x0(%rbp),%r14
    6108:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    610d:	ba 01 00 00 00       	mov    $0x1,%edx
    6112:	4d 89 f5             	mov    %r14,%r13
    6115:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    611c:	4d 85 f6             	test   %r14,%r14
    611f:	0f 8e 21 01 00 00    	jle    6246 <verify+0x246>
    6125:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6128:	48 89 d5             	mov    %rdx,%rbp
    612b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6130:	31 db                	xor    %ebx,%ebx
    6132:	4d 89 f2             	mov    %r14,%r10
    6135:	48 c1 e5 05          	shl    $0x5,%rbp
    6139:	48 83 ed 20          	sub    $0x20,%rbp
    613d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6141:	49 89 ee             	mov    %rbp,%r14
    6144:	48 89 dd             	mov    %rbx,%rbp
    6147:	48 89 d3             	mov    %rdx,%rbx
    614a:	eb 31                	jmp    617d <verify+0x17d>
    614c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6150:	4c 39 c2             	cmp    %r8,%rdx
    6153:	0f 8d 57 01 00 00    	jge    62b0 <verify+0x2b0>
    6159:	4c 39 df             	cmp    %r11,%rdi
    615c:	7e 05                	jle    6163 <verify+0x163>
    615e:	49 39 c1             	cmp    %rax,%r9
    6161:	7c 75                	jl     61d8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6163:	4c 39 df             	cmp    %r11,%rdi
    6166:	0f 8d ab 01 00 00    	jge    6317 <verify+0x317>
    616c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6170:	48 83 c5 01          	add    $0x1,%rbp
    6174:	49 39 ea             	cmp    %rbp,%r10
    6177:	0f 8e a9 00 00 00    	jle    6226 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    617d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    6184:	48 89 e8             	mov    %rbp,%rax
    6187:	48 c1 e0 05          	shl    $0x5,%rax
    618b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    6192:	4c 01 f2             	add    %r14,%rdx
    6195:	48 8b 08             	mov    (%rax),%rcx
    6198:	48 8b 78 10          	mov    0x10(%rax),%rdi
    619c:	48 8b 32             	mov    (%rdx),%rsi
    619f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    61a3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    61a7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    61ab:	48 8b 50 08          	mov    0x8(%rax),%rdx
    61af:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    61b3:	48 39 f1             	cmp    %rsi,%rcx
    61b6:	7c 98                	jl     6150 <verify+0x150>
    61b8:	0f 8e 42 01 00 00    	jle    6300 <verify+0x300>
    61be:	4c 39 c2             	cmp    %r8,%rdx
    61c1:	0f 8f f9 00 00 00    	jg     62c0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    61c7:	75 a7                	jne    6170 <verify+0x170>
    61c9:	4c 39 df             	cmp    %r11,%rdi
    61cc:	7f a2                	jg     6170 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    61ce:	49 39 c1             	cmp    %rax,%r9
    61d1:	7c 9d                	jl     6170 <verify+0x170>
    61d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    61d8:	49 89 c1             	mov    %rax,%r9
    61db:	48 89 f9             	mov    %rdi,%rcx
    61de:	48 89 f2             	mov    %rsi,%rdx
    61e1:	bf 01 00 00 00       	mov    $0x1,%edi
    61e6:	48 8d 35 93 13 00 00 	lea    0x1393(%rip),%rsi        # 7580 <_IO_stdin_used+0x580>
    61ed:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    61ef:	48 83 c5 01          	add    $0x1,%rbp
    61f3:	e8 58 c2 ff ff       	call   2450 <__printf_chk@plt>
    61f8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    61fd:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    6202:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6205:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    620a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6211:	4c 8b 20             	mov    (%rax),%r12
    6214:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6219:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    621d:	49 39 ea             	cmp    %rbp,%r10
    6220:	0f 8f 57 ff ff ff    	jg     617d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6226:	48 89 da             	mov    %rbx,%rdx
    6229:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    6230:	7d 14                	jge    6246 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6232:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6239:	48 83 c2 01          	add    $0x1,%rdx
    623d:	4d 85 f6             	test   %r14,%r14
    6240:	0f 8f e2 fe ff ff    	jg     6128 <verify+0x128>
    6246:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    624b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6250:	48 83 c3 01          	add    $0x1,%rbx
    6254:	39 58 08             	cmp    %ebx,0x8(%rax)
    6257:	0f 8f 53 fe ff ff    	jg     60b0 <verify+0xb0>
    625d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6262:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6267:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    626c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6271:	48 83 c1 01          	add    $0x1,%rcx
    6275:	39 48 08             	cmp    %ecx,0x8(%rax)
    6278:	0f 8f d8 fd ff ff    	jg     6056 <verify+0x56>
    627e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6283:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6288:	48 81 44 24 10 c0 00 00 00 	addq   $0xc0,0x10(%rsp)
    6291:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6296:	41 39 c7             	cmp    %eax,%r15d
    6299:	0f 84 86 00 00 00    	je     6325 <verify+0x325>
    629f:	41 89 c4             	mov    %eax,%r12d
    62a2:	e9 8a fd ff ff       	jmp    6031 <verify+0x31>
    62a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    62b0:	0f 85 ba fe ff ff    	jne    6170 <verify+0x170>
    62b6:	e9 a8 fe ff ff       	jmp    6163 <verify+0x163>
    62bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    62c0:	49 39 c1             	cmp    %rax,%r9
    62c3:	7e 09                	jle    62ce <verify+0x2ce>
    62c5:	4c 39 df             	cmp    %r11,%rdi
    62c8:	0f 8c 0a ff ff ff    	jl     61d8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    62ce:	4c 39 df             	cmp    %r11,%rdi
    62d1:	0f 8f 99 fe ff ff    	jg     6170 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    62d7:	49 39 c1             	cmp    %rax,%r9
    62da:	0f 8d f8 fe ff ff    	jge    61d8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    62e0:	48 39 f1             	cmp    %rsi,%rcx
    62e3:	0f 85 87 fe ff ff    	jne    6170 <verify+0x170>
    62e9:	4c 39 c2             	cmp    %r8,%rdx
    62ec:	0f 85 7e fe ff ff    	jne    6170 <verify+0x170>
    62f2:	4c 39 df             	cmp    %r11,%rdi
    62f5:	0f 84 dd fe ff ff    	je     61d8 <verify+0x1d8>
    62fb:	e9 70 fe ff ff       	jmp    6170 <verify+0x170>
    6300:	4c 39 c2             	cmp    %r8,%rdx
    6303:	0f 8c 5a fe ff ff    	jl     6163 <verify+0x163>
    6309:	4c 39 df             	cmp    %r11,%rdi
    630c:	7e c9                	jle    62d7 <verify+0x2d7>
    630e:	4c 39 c2             	cmp    %r8,%rdx
    6311:	0f 85 59 fe ff ff    	jne    6170 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6317:	49 39 c1             	cmp    %rax,%r9
    631a:	0f 8f 50 fe ff ff    	jg     6170 <verify+0x170>
    6320:	e9 b3 fe ff ff       	jmp    61d8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    6325:	48 81 44 24 18 c0 00 00 00 	addq   $0xc0,0x18(%rsp)
    632e:	41 8d 46 01          	lea    0x1(%r14),%eax
    6332:	45 39 e6             	cmp    %r12d,%r14d
    6335:	74 08                	je     633f <verify+0x33f>
    6337:	41 89 c6             	mov    %eax,%r14d
    633a:	e9 ea fc ff ff       	jmp    6029 <verify+0x29>
}
    633f:	48 83 c4 58          	add    $0x58,%rsp
    6343:	31 c0                	xor    %eax,%eax
    6345:	5b                   	pop    %rbx
    6346:	5d                   	pop    %rbp
    6347:	41 5c                	pop    %r12
    6349:	41 5d                	pop    %r13
    634b:	41 5e                	pop    %r14
    634d:	41 5f                	pop    %r15
    634f:	c3                   	ret
    6350:	31 c0                	xor    %eax,%eax
    6352:	c3                   	ret

Disassembly of section .fini:

0000000000006354 <_fini>:
    6354:	f3 0f 1e fa          	endbr64
    6358:	48 83 ec 08          	sub    $0x8,%rsp
    635c:	48 83 c4 08          	add    $0x8,%rsp
    6360:	c3                   	ret
