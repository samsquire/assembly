
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
    25f6:	48 8d 3d db 4e 00 00 	lea    0x4edb(%rip),%rdi        # 74d8 <_IO_stdin_used+0x4d8>
    25fd:	41 56                	push   %r14
    25ff:	41 55                	push   %r13
    2601:	41 54                	push   %r12
    2603:	55                   	push   %rbp
    2604:	53                   	push   %rbx
    2605:	48 81 ec a8 00 00 00 	sub    $0xa8,%rsp
    260c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2615:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
    261d:	48 8d 05 9c 11 00 00 	lea    0x119c(%rip),%rax        # 37c0 <barriered_reset>
    2624:	66 48 0f 6e e8       	movq   %rax,%xmm5
    2629:	0f 16 2d 48 76 00 00 	movhps 0x7648(%rip),%xmm5        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    2630:	0f 29 6c 24 40       	movaps %xmm5,0x40(%rsp)
    2635:	e8 b6 fc ff ff       	call   22f0 <puts@plt>
    263a:	bf 0a 00 00 00       	mov    $0xa,%edi
    263f:	e8 8c fc ff ff       	call   22d0 <putchar@plt>
    2644:	48 8d 3d f3 4b 00 00 	lea    0x4bf3(%rip),%rdi        # 723e <_IO_stdin_used+0x23e>
    264b:	e8 a0 fc ff ff       	call   22f0 <puts@plt>
    2650:	ba 02 00 00 00       	mov    $0x2,%edx
    2655:	48 8d 35 fe 4b 00 00 	lea    0x4bfe(%rip),%rsi        # 725a <_IO_stdin_used+0x25a>
    265c:	31 c0                	xor    %eax,%eax
    265e:	bf 01 00 00 00       	mov    $0x1,%edi
    2663:	e8 e8 fd ff ff       	call   2450 <__printf_chk@plt>
    2668:	ba 10 00 00 00       	mov    $0x10,%edx
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
    26b0:	ba 02 00 00 00       	mov    $0x2,%edx
    26b5:	48 8d 35 f5 4b 00 00 	lea    0x4bf5(%rip),%rsi        # 72b1 <_IO_stdin_used+0x2b1>
    26bc:	31 c0                	xor    %eax,%eax
    26be:	bf 01 00 00 00       	mov    $0x1,%edi
    26c3:	e8 88 fd ff ff       	call   2450 <__printf_chk@plt>
    26c8:	ba 01 00 00 00       	mov    $0x1,%edx
    26cd:	48 8d 35 6c 4e 00 00 	lea    0x4e6c(%rip),%rsi        # 7540 <_IO_stdin_used+0x540>
    26d4:	31 c0                	xor    %eax,%eax
    26d6:	bf 01 00 00 00       	mov    $0x1,%edi
    26db:	e8 70 fd ff ff       	call   2450 <__printf_chk@plt>
    26e0:	ba 01 00 00 00       	mov    $0x1,%edx
    26e5:	48 8d 35 84 4e 00 00 	lea    0x4e84(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
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
    2739:	bf 02 00 00 00       	mov    $0x2,%edi
    273e:	e8 5d fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2743:	be b0 00 00 00       	mov    $0xb0,%esi
    2748:	bf 10 00 00 00       	mov    $0x10,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    274d:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2752:	e8 49 fc ff ff       	call   23a0 <calloc@plt>
    2757:	ba 0c 00 00 00       	mov    $0xc,%edx
    275c:	bf 01 00 00 00       	mov    $0x1,%edi
    2761:	48 8d 35 93 4b 00 00 	lea    0x4b93(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
    2768:	48 89 04 24          	mov    %rax,(%rsp)
    276c:	31 c0                	xor    %eax,%eax
    276e:	e8 dd fc ff ff       	call   2450 <__printf_chk@plt>
    2773:	ba 18 00 00 00       	mov    $0x18,%edx
    2778:	48 8d 35 92 4b 00 00 	lea    0x4b92(%rip),%rsi        # 7311 <_IO_stdin_used+0x311>
    277f:	31 c0                	xor    %eax,%eax
    2781:	bf 01 00 00 00       	mov    $0x1,%edi
    2786:	e8 c5 fc ff ff       	call   2450 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    278b:	be 10 00 00 00       	mov    $0x10,%esi
    2790:	bf 18 00 00 00       	mov    $0x18,%edi
    2795:	e8 06 fc ff ff       	call   23a0 <calloc@plt>
    279a:	4c 8b 34 24          	mov    (%rsp),%r14
    279e:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    27a6:	49 89 c5             	mov    %rax,%r13
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    27a9:	48 8d a8 80 01 00 00 	lea    0x180(%rax),%rbp
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    27b0:	49 89 c4             	mov    %rax,%r12
    27b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27b8:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    27bd:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27c5:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    27ca:	49 83 c4 10          	add    $0x10,%r12
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27ce:	e8 cd fb ff ff       	call   23a0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    27d3:	be 20 00 00 00       	mov    $0x20,%esi
    27d8:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27dd:	49 89 44 24 f8       	mov    %rax,-0x8(%r12)
    27e2:	48 89 c3             	mov    %rax,%rbx
      buffers[x].buffer[y].available = 0;
    27e5:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    27ef:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    27f9:	e8 a2 fb ff ff       	call   23a0 <calloc@plt>
    27fe:	48 89 83 88 00 00 00 	mov    %rax,0x88(%rbx)
  for (int x = 0 ; x < buffers_required; x++) {
    2805:	4c 39 e5             	cmp    %r12,%rbp
    2808:	75 ae                	jne    27b8 <main+0x1c8>
    280a:	4c 89 74 24 60       	mov    %r14,0x60(%rsp)
    280f:	4c 89 eb             	mov    %r13,%rbx
    2812:	45 31 e4             	xor    %r12d,%r12d
    2815:	bf 02 00 00 00       	mov    $0x2,%edi
    }
  }
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
    281a:	c7 44 24 38 00 00 00 00 	movl   $0x0,0x38(%rsp)
    2822:	4d 89 e5             	mov    %r12,%r13
    2825:	4c 89 f5             	mov    %r14,%rbp
    2828:	89 f9                	mov    %edi,%ecx
    282a:	49 89 dc             	mov    %rbx,%r12
    282d:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
    2832:	44 89 6c 24 54       	mov    %r13d,0x54(%rsp)
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2837:	4d 89 e6             	mov    %r12,%r14
    283a:	49 89 ef             	mov    %rbp,%r15
    283d:	4b 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%rax
    2842:	48 89 6c 24 68       	mov    %rbp,0x68(%rsp)
    2847:	44 8d 49 fe          	lea    -0x2(%rcx),%r9d
  int my_buffers = 0;
  int cur_buffer = 0;
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    284b:	48 c1 e0 04          	shl    $0x4,%rax
    284f:	48 89 bc 24 80 00 00 00 	mov    %rdi,0x80(%rsp)
    2857:	48 01 f8             	add    %rdi,%rax
    285a:	89 4c 24 28          	mov    %ecx,0x28(%rsp)
    285e:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2863:	4c 89 6c 24 78       	mov    %r13,0x78(%rsp)
    2868:	4c 89 64 24 70       	mov    %r12,0x70(%rsp)
    286d:	45 89 cc             	mov    %r9d,%r12d
    2870:	8b 54 24 54          	mov    0x54(%rsp),%edx
    2874:	44 89 e1             	mov    %r12d,%ecx
    2877:	48 8d 35 1a 4d 00 00 	lea    0x4d1a(%rip),%rsi        # 7598 <_IO_stdin_used+0x598>
    287e:	31 c0                	xor    %eax,%eax
    2880:	bf 01 00 00 00       	mov    $0x1,%edi
    2885:	e8 c6 fb ff ff       	call   2450 <__printf_chk@plt>
      int x = (k * threads_per_group) + d;
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    288a:	be 08 00 00 00       	mov    $0x8,%esi
    288f:	bf 02 00 00 00       	mov    $0x2,%edi
    2894:	e8 07 fb ff ff       	call   23a0 <calloc@plt>
      int other = -1;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2899:	be 80 00 00 00       	mov    $0x80,%esi
    289e:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    28a3:	48 89 c3             	mov    %rax,%rbx
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    28a6:	e8 f5 fa ff ff       	call   23a0 <calloc@plt>
    28ab:	48 89 c5             	mov    %rax,%rbp
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    28ae:	41 f6 c4 01          	test   $0x1,%r12b
    28b2:	0f 84 95 08 00 00    	je     314d <main+0xb5d>
        other = abs(x - 1) % total_threads;
    28b8:	41 8d 54 24 ff       	lea    -0x1(%r12),%edx
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    28bd:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    28c2:	41 b8 01 00 00 00    	mov    $0x1,%r8d
    28c8:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
        other = abs(x - 1) % total_threads;
    28cc:	49 89 d5             	mov    %rdx,%r13
        my_thread_data[0] = &thread_data[other]; 
    28cf:	48 8d 04 42          	lea    (%rdx,%rax,2),%rax
        my_thread_data[1] = &thread_data[x]; 
        // printf("odd %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
        thread_data[x].protected_state = &protected_state[other];
    28d3:	48 8d 14 52          	lea    (%rdx,%rdx,2),%rdx
        my_thread_data[0] = &thread_data[other]; 
    28d7:	48 c1 e0 04          	shl    $0x4,%rax
    28db:	48 01 f8             	add    %rdi,%rax
        thread_data[x].protected_state = &protected_state[other];
    28de:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
    28e3:	48 8d 34 d7          	lea    (%rdi,%rdx,8),%rsi
    28e7:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
        my_thread_data[1] = &thread_data[x]; 
    28ec:	4c 89 fa             	mov    %r15,%rdx
    28ef:	89 7c 24 20          	mov    %edi,0x20(%rsp)
        thread_data[x].protected_state = &protected_state[other];
    28f3:	49 89 77 38          	mov    %rsi,0x38(%r15)
    28f7:	44 89 e9             	mov    %r13d,%ecx
    28fa:	bf 01 00 00 00       	mov    $0x1,%edi
    28ff:	48 8d 35 c2 4c 00 00 	lea    0x4cc2(%rip),%rsi        # 75c8 <_IO_stdin_used+0x5c8>
    2906:	48 89 53 08          	mov    %rdx,0x8(%rbx)
    290a:	44 89 e2             	mov    %r12d,%edx
    290d:	48 89 03             	mov    %rax,(%rbx)
    2910:	31 c0                	xor    %eax,%eax
        thread_data[x].thread_index = 1;
    2912:	45 89 07             	mov    %r8d,(%r15)
    2915:	e8 36 fb ff ff       	call   2450 <__printf_chk@plt>
    291a:	8b 4c 24 38          	mov    0x38(%rsp),%ecx
    291e:	31 c0                	xor    %eax,%eax
    2920:	44 89 e2             	mov    %r12d,%edx
        my_thread_data[1] = &thread_data[other]; 
        // printf("even %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
        thread_data[x].protected_state = &protected_state[x];
      }
      printf("i am %d, other is %d my thread index is %d\n", x, other, thread_data[x].thread_index);
      thread_data[x].other = other;
    2923:	45 89 af a8 00 00 00 	mov    %r13d,0xa8(%r15)
    292a:	48 8d 35 c7 4c 00 00 	lea    0x4cc7(%rip),%rsi        # 75f8 <_IO_stdin_used+0x5f8>
    2931:	bf 01 00 00 00       	mov    $0x1,%edi
    2936:	e8 15 fb ff ff       	call   2450 <__printf_chk@plt>
      // for (int j = 0 ; j < cores ; j++) {
        printf("assigning thread %d to core %d\n", x, curcpu);
        if (x < thread_count) {
    293b:	41 83 fc 01          	cmp    $0x1,%r12d
    293f:	0f 8f 38 08 00 00    	jg     317d <main+0xb8d>
          CPU_SET(curcpu, sendercpu);
    2945:	48 63 44 24 38       	movslq 0x38(%rsp),%rax
    294a:	48 89 c7             	mov    %rax,%rdi
    294d:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2953:	77 13                	ja     2968 <main+0x378>
    2955:	48 c1 e8 06          	shr    $0x6,%rax
    2959:	ba 01 00 00 00       	mov    $0x1,%edx
    295e:	89 f9                	mov    %edi,%ecx
    2960:	48 d3 e2             	shl    %cl,%rdx
    2963:	48 09 54 c5 00       	or     %rdx,0x0(%rbp,%rax,8)
          curcpu += 2;
    2968:	83 44 24 38 02       	addl   $0x2,0x38(%rsp)
        
      // }
      thread_data[x].cpu_set = sendercpu;
      thread_data[x].real_thread_index = x;
      thread_data[x].threads = my_thread_data;
      thread_data[x].thread_count = 2;
    296d:	48 8b 05 5c 51 00 00 	mov    0x515c(%rip),%rax        # 7ad0 <_IO_stdin_used+0xad0>
      thread_data[x].cpu_set = sendercpu;
    2974:	49 89 af a0 00 00 00 	mov    %rbp,0xa0(%r15)

        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
        thread_data[x].tasks = barriers;
        int assigned = 0;
        // external_thread_index = 0;
        for (int y = 0 ; y < total_barrier_count ; y++) {
    297b:	31 ed                	xor    %ebp,%ebp
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    297d:	be 10 00 00 00       	mov    $0x10,%esi
      thread_data[x].real_thread_index = x;
    2982:	45 89 67 04          	mov    %r12d,0x4(%r15)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2986:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].threads = my_thread_data;
    298b:	49 89 5f 10          	mov    %rbx,0x10(%r15)
      thread_data[x].thread_count = 2;
    298f:	49 89 47 18          	mov    %rax,0x18(%r15)
      thread_data[x].task_count = total_barrier_count;
    2993:	41 c7 47 30 03 00 00 00 	movl   $0x3,0x30(%r15)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    299b:	e8 00 fa ff ff       	call   23a0 <calloc@plt>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    29a0:	be 10 00 00 00       	mov    $0x10,%esi
    29a5:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    29aa:	49 89 47 58          	mov    %rax,0x58(%r15)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    29ae:	e8 ed f9 ff ff       	call   23a0 <calloc@plt>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    29b3:	be 28 00 00 00       	mov    $0x28,%esi
    29b8:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].timestamp_count = 0;
    29bd:	66 0f 6f 1d eb 50 00 00 	movdqa 0x50eb(%rip),%xmm3        # 7ab0 <_IO_stdin_used+0xab0>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    29c5:	49 89 47 60          	mov    %rax,0x60(%r15)
      thread_data[x].timestamp_count = 0;
    29c9:	41 0f 11 5f 70       	movups %xmm3,0x70(%r15)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    29ce:	e8 cd f9 ff ff       	call   23a0 <calloc@plt>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    29d3:	be 00 02 00 00       	mov    $0x200,%esi
    29d8:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    29dd:	66 0f 6f 25 cb 50 00 00 	movdqa 0x50cb(%rip),%xmm4        # 7ab0 <_IO_stdin_used+0xab0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    29e5:	49 89 87 80 00 00 00 	mov    %rax,0x80(%r15)
      thread_data[x].task_timestamp_count = 0;
    29ec:	41 0f 11 a7 88 00 00 00 	movups %xmm4,0x88(%r15)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    29f4:	e8 a7 f9 ff ff       	call   23a0 <calloc@plt>
        for (int y = 0 ; y < total_barrier_count ; y++) {
    29f9:	44 89 64 24 10       	mov    %r12d,0x10(%rsp)
        thread_data[x].tasks = barriers;
    29fe:	49 89 47 28          	mov    %rax,0x28(%r15)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a02:	4c 89 74 24 30       	mov    %r14,0x30(%rsp)
    2a07:	49 89 c6             	mov    %rax,%r14
                t     x
                a       x
                s         x
                k           x
          */
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a0a:	4c 63 ed             	movslq %ebp,%r13
          struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2a0d:	be 20 00 00 00       	mov    $0x20,%esi
    2a12:	bf 02 00 00 00       	mov    $0x2,%edi
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a17:	4c 89 eb             	mov    %r13,%rbx
    2a1a:	48 8d 05 5f 0d 00 00 	lea    0xd5f(%rip),%rax        # 3780 <do_protected_write>
    2a21:	48 c1 e3 09          	shl    $0x9,%rbx
    2a25:	49 01 de             	add    %rbx,%r14
    2a28:	49 89 86 20 01 00 00 	mov    %rax,0x120(%r14)
          struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2a2f:	e8 6c f9 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2a34:	48 89 1c 24          	mov    %rbx,(%rsp)
    2a38:	89 6c 24 08          	mov    %ebp,0x8(%rsp)
    2a3c:	4c 8d 60 40          	lea    0x40(%rax),%r12
    2a40:	49 89 86 68 01 00 00 	mov    %rax,0x168(%r14)
          // long messages_limit = 20;/*9999999;*/
          for (int b = 0 ; b < 2 ; b++) {
    2a47:	49 89 c6             	mov    %rax,%r14
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2a4a:	be 08 00 00 00       	mov    $0x8,%esi
    2a4f:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < 2 ; b++) {
    2a54:	49 83 c6 20          	add    $0x20,%r14
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2a58:	e8 43 f9 ff ff       	call   23a0 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2a5d:	be 08 00 00 00       	mov    $0x8,%esi
    2a62:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2a67:	48 89 c5             	mov    %rax,%rbp
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2a6a:	e8 31 f9 ff ff       	call   23a0 <calloc@plt>
            struct Data *data = calloc(2, sizeof(struct Data));
    2a6f:	be 18 00 00 00       	mov    $0x18,%esi
    2a74:	bf 02 00 00 00       	mov    $0x2,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2a79:	48 89 c3             	mov    %rax,%rbx
            struct Data *data = calloc(2, sizeof(struct Data));
    2a7c:	e8 1f f9 ff ff       	call   23a0 <calloc@plt>
            mailboxes[b].lower = &data[0];
            mailboxes[b].higher = &data[1];
            data[0].messages = messages;
            data[1].messages = messages2;
            data[0].messages_limit = messages_limit;
            data[0].messages_count = 0;
    2a81:	66 0f 6f 05 37 50 00 00 	movdqa 0x5037(%rip),%xmm0        # 7ac0 <_IO_stdin_used+0xac0>
            mailboxes[b].higher = &data[1];
    2a89:	48 8d 70 18          	lea    0x18(%rax),%rsi
            mailboxes[b].lower = &data[0];
    2a8d:	49 89 46 e0          	mov    %rax,-0x20(%r14)
            mailboxes[b].higher = &data[1];
    2a91:	49 89 76 e8          	mov    %rsi,-0x18(%r14)
            data[0].messages = messages;
    2a95:	48 89 28             	mov    %rbp,(%rax)
            data[1].messages = messages2;
    2a98:	48 89 58 18          	mov    %rbx,0x18(%rax)
            data[0].messages_count = 0;
    2a9c:	0f 11 40 08          	movups %xmm0,0x8(%rax)
            data[1].messages_count = 0;
    2aa0:	0f 11 40 20          	movups %xmm0,0x20(%rax)
          for (int b = 0 ; b < 2 ; b++) {
    2aa4:	4d 39 e6             	cmp    %r12,%r14
    2aa7:	75 a1                	jne    2a4a <main+0x45a>
            data[1].messages_limit = messages_limit;
          }

          char *message = malloc(sizeof(char) * 256);
    2aa9:	be 01 00 00 00       	mov    $0x1,%esi
    2aae:	bf 00 01 00 00       	mov    $0x100,%edi
    2ab3:	8b 6c 24 08          	mov    0x8(%rsp),%ebp
    2ab7:	48 8b 1c 24          	mov    (%rsp),%rbx
    2abb:	e8 e0 f8 ff ff       	call   23a0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2ac0:	bf 18 00 00 00       	mov    $0x18,%edi
          char *message = malloc(sizeof(char) * 256);
    2ac5:	49 89 c4             	mov    %rax,%r12
          struct Message *messaged = malloc(sizeof(struct Message));
    2ac8:	e8 43 f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2acd:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
    2ad2:	4c 89 e7             	mov    %r12,%rdi
    2ad5:	41 89 e9             	mov    %ebp,%r9d
    2ad8:	48 89 04 24          	mov    %rax,(%rsp)
    2adc:	48 8d 0d 35 4b 00 00 	lea    0x4b35(%rip),%rcx        # 7618 <_IO_stdin_used+0x618>
    2ae3:	ba 00 01 00 00       	mov    $0x100,%edx
    2ae8:	31 c0                	xor    %eax,%eax
    2aea:	be 01 00 00 00       	mov    $0x1,%esi
    2aef:	e8 2c fa ff ff       	call   2520 <__sprintf_chk@plt>
          memset(message, '\0', 256);
          sprintf(message, "Sending message from thread %d task %d", x, y);
          messaged->message = message;
          messaged->task_index = y;
          messaged->thread_index = thread_data[x].thread_index;
    2af4:	49 63 07             	movslq (%r15),%rax
          messaged->message = message;
    2af7:	4c 8b 14 24          	mov    (%rsp),%r10
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2afb:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2b00:	4d 8b 77 28          	mov    0x28(%r15),%r14
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2b04:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->message = message;
    2b09:	4d 89 22             	mov    %r12,(%r10)
          messaged->thread_index = thread_data[x].thread_index;
    2b0c:	49 89 c4             	mov    %rax,%r12
    2b0f:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2b13:	8d 45 01             	lea    0x1(%rbp),%eax
    2b16:	4c 01 f3             	add    %r14,%rbx
    2b19:	83 e0 01             	and    $0x1,%eax
          messaged->task_index = y;
    2b1c:	4d 89 6a 10          	mov    %r13,0x10(%r10)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2b20:	89 83 88 01 00 00    	mov    %eax,0x188(%rbx)
          thread_data[x].tasks[y].message = messaged;
    2b26:	4c 89 93 80 01 00 00 	mov    %r10,0x180(%rbx)
          thread_data[x].tasks[y].snapshot_count = 99;
    2b2d:	48 c7 83 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2b38:	e8 63 f8 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2b3d:	44 89 a3 30 01 00 00 	mov    %r12d,0x130(%rbx)
          thread_data[x].tasks[y].sending = 1;
    2b44:	48 bf 01 00 00 00 02 00 00 00 	movabs $0x200000001,%rdi
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2b4e:	48 89 83 48 01 00 00 	mov    %rax,0x148(%rbx)
          thread_data[x].tasks[y].thread = &thread_data[x]; 
          thread_data[x].tasks[y].available = 1;
    2b55:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
          thread_data[x].tasks[y].current_snapshot = 0;
    2b5f:	48 c7 83 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%rbx)
          thread_data[x].tasks[y].thread = &thread_data[x]; 
    2b6a:	4c 89 bb 28 01 00 00 	mov    %r15,0x128(%rbx)
          thread_data[x].tasks[y].arrived = 0;
    2b71:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
          thread_data[x].tasks[y].thread_count = 2;
    2b7b:	c7 83 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%rbx)
          thread_data[x].tasks[y].available = 1;
    2b85:	48 89 83 38 01 00 00 	mov    %rax,0x138(%rbx)
          thread_data[x].tasks[y].sending = 1;
    2b8c:	48 89 bb 78 01 00 00 	mov    %rdi,0x178(%rbx)
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2b93:	89 2b                	mov    %ebp,(%rbx)
          if (y == barrier_count - 1) {
    2b95:	83 fd 01             	cmp    $0x1,%ebp
    2b98:	0f 84 a1 05 00 00    	je     313f <main+0xb4f>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2b9e:	85 ed                	test   %ebp,%ebp
    2ba0:	0f 84 81 05 00 00    	je     3127 <main+0xb37>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    2ba6:	48 8d 3d d3 2b 00 00 	lea    0x2bd3(%rip),%rdi        # 5780 <barriered_work>
    2bad:	4d 89 f5             	mov    %r14,%r13
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2bb0:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    2bb5:	44 89 24 24          	mov    %r12d,(%rsp)
    2bb9:	48 89 bb 18 01 00 00 	mov    %rdi,0x118(%rbx)
    2bc0:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2bc5:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].buffers_count = buffers_per_thread;
    2bca:	41 c7 87 ac 00 00 00 01 00 00 00 	movl   $0x1,0xac(%r15)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2bd5:	e8 c6 f7 ff ff       	call   23a0 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2bda:	66 0f 6f 54 24 40    	movdqa 0x40(%rsp),%xmm2
        thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
        thread_data[x].tasks[barrier_count].thread_count = 2; 
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2be0:	8b 0c 24             	mov    (%rsp),%ecx
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2be3:	49 89 47 40          	mov    %rax,0x40(%r15)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2be7:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2bec:	4c 89 30             	mov    %r14,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2bef:	49 83 c6 10          	add    $0x10,%r14
        thread_data[x].tasks[barrier_count].available = 1; 
    2bf3:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
        thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2bfd:	4d 89 bd 28 05 00 00 	mov    %r15,0x528(%r13)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2c04:	49 81 c7 b0 00 00 00 	add    $0xb0,%r15
    2c0b:	48 83 44 24 18 18    	addq   $0x18,0x18(%rsp)
        thread_data[x].tasks[barrier_count].arrived = 0; 
    2c11:	41 c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r13)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2c1c:	41 c7 85 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%r13)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2c27:	41 89 8d 30 05 00 00 	mov    %ecx,0x530(%r13)
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2c2e:	41 c7 85 7c 05 00 00 02 00 00 00 	movl   $0x2,0x57c(%r13)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    2c39:	41 c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r13)
        thread_data[x].tasks[barrier_count].available = 1; 
    2c44:	49 89 85 38 05 00 00 	mov    %rax,0x538(%r13)
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2c4b:	41 0f 11 95 18 05 00 00 	movups %xmm2,0x518(%r13)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2c53:	44 39 64 24 28       	cmp    %r12d,0x28(%rsp)
    2c58:	0f 85 12 fc ff ff    	jne    2870 <main+0x280>
    2c5e:	8b 4c 24 28          	mov    0x28(%rsp),%ecx
    2c62:	48 8b 6c 24 68       	mov    0x68(%rsp),%rbp
    2c67:	4c 8b 64 24 70       	mov    0x70(%rsp),%r12
    2c6c:	4c 8b 6c 24 78       	mov    0x78(%rsp),%r13
  for (int k = 0 ; k < group_count ; k++) {
    2c71:	83 c1 02             	add    $0x2,%ecx
    2c74:	48 81 c5 60 01 00 00 	add    $0x160,%rbp
    2c7b:	49 83 c5 01          	add    $0x1,%r13
    2c7f:	49 83 c4 20          	add    $0x20,%r12
    2c83:	83 f9 0e             	cmp    $0xe,%ecx
    2c86:	0f 85 a1 fb ff ff    	jne    282d <main+0x23d>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2c8c:	4c 8b 5c 24 60       	mov    0x60(%rsp),%r11
    2c91:	ba 0d 00 00 00       	mov    $0xd,%edx
    2c96:	48 8d 35 8e 46 00 00 	lea    0x468e(%rip),%rsi        # 732b <_IO_stdin_used+0x32b>
    2c9d:	31 c0                	xor    %eax,%eax
    2c9f:	bf 01 00 00 00       	mov    $0x1,%edi
    2ca4:	4c 89 1c 24          	mov    %r11,(%rsp)
    2ca8:	e8 a3 f7 ff ff       	call   2450 <__printf_chk@plt>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2cad:	be 08 00 00 00       	mov    $0x8,%esi
    2cb2:	bf 02 00 00 00       	mov    $0x2,%edi
    2cb7:	e8 e4 f6 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2cbc:	4c 8b 1c 24          	mov    (%rsp),%r11
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cc0:	be 38 00 00 00       	mov    $0x38,%esi
    2cc5:	bf 10 00 00 00       	mov    $0x10,%edi
    my_thread_data[0] = &thread_data[x]; 
    2cca:	4d 8d a3 f0 08 00 00 	lea    0x8f0(%r11),%r12
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2cd1:	4c 89 58 08          	mov    %r11,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2cd5:	4d 8d ab b0 00 00 00 	lea    0xb0(%r11),%r13
    thread_data[x].threads = my_thread_data;
    2cdc:	49 89 83 00 09 00 00 	mov    %rax,0x900(%r11)
    my_thread_data[0] = &thread_data[x]; 
    2ce3:	4c 89 20             	mov    %r12,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2ce6:	49 8b 43 28          	mov    0x28(%r11),%rax
    thread_data[x].thread_count = 2;
    2cea:	41 c7 83 08 09 00 00 02 00 00 00 	movl   $0x2,0x908(%r11)
    thread_data[x].thread_index = 0;
    2cf5:	41 c7 83 f0 08 00 00 00 00 00 00 	movl   $0x0,0x8f0(%r11)
    thread_data[x].task_count = total_barrier_count;
    2d00:	41 c7 83 20 09 00 00 03 00 00 00 	movl   $0x3,0x920(%r11)
    thread_data[n].tasks[0].scheduled = 1;
    2d0b:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d15:	49 8b 83 d8 00 00 00 	mov    0xd8(%r11),%rax
    2d1c:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    2d21:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d2b:	e8 70 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d30:	be 38 00 00 00       	mov    $0x38,%esi
    2d35:	bf 10 00 00 00       	mov    $0x10,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d3a:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d3d:	e8 5e f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d42:	be 38 00 00 00       	mov    $0x38,%esi
    2d47:	bf 10 00 00 00       	mov    $0x10,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d4c:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d4f:	e8 4c f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d54:	be 38 00 00 00       	mov    $0x38,%esi
    2d59:	bf 10 00 00 00       	mov    $0x10,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d5e:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d62:	e8 39 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d67:	be 08 00 00 00       	mov    $0x8,%esi
    2d6c:	bf 10 00 00 00       	mov    $0x10,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d71:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d76:	e8 25 f6 ff ff       	call   23a0 <calloc@plt>

  thread_data[thread_count].type = TIMER;
    2d7b:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2d80:	be 08 00 00 00       	mov    $0x8,%esi
    2d85:	bf 10 00 00 00       	mov    $0x10,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d8a:	48 89 c3             	mov    %rax,%rbx
  thread_data[thread_count].task_count = total_barrier_count;
    2d8d:	48 8b 05 44 4d 00 00 	mov    0x4d44(%rip),%rax        # 7ad8 <_IO_stdin_used+0xad8>
  thread_data[thread_count].type = TIMER;
    2d94:	41 c7 83 68 01 00 00 00 00 00 00 	movl   $0x0,0x168(%r11)
  thread_data[thread_count].task_count = total_barrier_count;
    2d9f:	49 89 83 90 01 00 00 	mov    %rax,0x190(%r11)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2da6:	e8 f5 f5 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2dab:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2db0:	bf 01 00 00 00       	mov    $0x1,%edi
    2db5:	48 8d 35 7e 45 00 00 	lea    0x457e(%rip),%rsi        # 733a <_IO_stdin_used+0x33a>
    2dbc:	4c 89 60 68          	mov    %r12,0x68(%rax)
    2dc0:	49 8d 93 10 02 00 00 	lea    0x210(%r11),%rdx
    2dc7:	4d 8d 83 a0 09 00 00 	lea    0x9a0(%r11),%r8
    2dce:	4c 89 18             	mov    %r11,(%rax)
    2dd1:	48 89 50 18          	mov    %rdx,0x18(%rax)
    2dd5:	49 8d 93 c0 02 00 00 	lea    0x2c0(%r11),%rdx
    2ddc:	49 8d 8b 60 01 00 00 	lea    0x160(%r11),%rcx
    2de3:	48 89 50 20          	mov    %rdx,0x20(%rax)
    2de7:	49 8d 93 70 03 00 00 	lea    0x370(%r11),%rdx
    2dee:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2df2:	49 8d 93 20 04 00 00 	lea    0x420(%r11),%rdx
    2df9:	48 89 50 30          	mov    %rdx,0x30(%rax)
    2dfd:	49 8d 93 d0 04 00 00 	lea    0x4d0(%r11),%rdx
    2e04:	48 89 50 38          	mov    %rdx,0x38(%rax)
    2e08:	49 8d 93 80 05 00 00 	lea    0x580(%r11),%rdx
    2e0f:	48 89 50 40          	mov    %rdx,0x40(%rax)
    2e13:	49 8d 93 30 06 00 00 	lea    0x630(%r11),%rdx
    2e1a:	48 89 50 48          	mov    %rdx,0x48(%rax)
    2e1e:	49 8d 93 e0 06 00 00 	lea    0x6e0(%r11),%rdx
    2e25:	48 89 50 50          	mov    %rdx,0x50(%rax)
    2e29:	49 8d 93 90 07 00 00 	lea    0x790(%r11),%rdx
    2e30:	48 89 50 58          	mov    %rdx,0x58(%rax)
    2e34:	49 8d 93 40 08 00 00 	lea    0x840(%r11),%rdx
    2e3b:	48 89 50 60          	mov    %rdx,0x60(%rax)
    2e3f:	49 8d 93 50 0a 00 00 	lea    0xa50(%r11),%rdx
    2e46:	4c 89 40 70          	mov    %r8,0x70(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2e4a:	49 89 83 70 01 00 00 	mov    %rax,0x170(%r11)
    my_thread_data[n] = &thread_data[n]; 
    2e51:	48 89 48 10          	mov    %rcx,0x10(%rax)
    2e55:	48 89 50 78          	mov    %rdx,0x78(%rax)
    2e59:	ba 02 00 00 00       	mov    $0x2,%edx
  thread_data[thread_count].thread_count = thread_count;
    2e5e:	41 c7 83 78 01 00 00 02 00 00 00 	movl   $0x2,0x178(%r11)
  thread_data[thread_count].my_thread_count = 2;
    2e69:	41 c7 83 80 01 00 00 02 00 00 00 	movl   $0x2,0x180(%r11)
  thread_data[thread_count].thread_index = 0;
    2e74:	41 c7 83 60 01 00 00 00 00 00 00 	movl   $0x0,0x160(%r11)
    my_thread_data[n] = &thread_data[n]; 
    2e7f:	4c 89 68 08          	mov    %r13,0x8(%rax)
    2e83:	31 c0                	xor    %eax,%eax
    2e85:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    2e8a:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    2e8f:	e8 bc f5 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2e94:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    2e99:	48 8d 75 70          	lea    0x70(%rbp),%rsi
    2e9d:	48 8d 7b 10          	lea    0x10(%rbx),%rdi
    2ea1:	48 8d 15 98 0a 00 00 	lea    0xa98(%rip),%rdx        # 3940 <timer_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    thread_data[x].type = WORKER;
    thread_data[x].running = 1;
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2ea8:	48 8d 2d f1 24 00 00 	lea    0x24f1(%rip),%rbp        # 53a0 <barriered_thread>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2eaf:	e8 bc f5 ff ff       	call   2470 <pthread_create@plt>
    thread_data[x].type = WORKER;
    2eb4:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2eb9:	31 d2                	xor    %edx,%edx
    2ebb:	31 c0                	xor    %eax,%eax
    2ebd:	4c 8d 0d 7c 47 00 00 	lea    0x477c(%rip),%r9        # 7640 <_IO_stdin_used+0x640>
    2ec4:	bf 01 00 00 00       	mov    $0x1,%edi
    2ec9:	41 c7 43 08 01 00 00 00 	movl   $0x1,0x8(%r11)
    2ed1:	4c 89 ce             	mov    %r9,%rsi
    thread_data[x].running = 1;
    2ed4:	41 c7 43 34 01 00 00 00 	movl   $0x1,0x34(%r11)
    2edc:	e8 6f f5 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2ee1:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2ee6:	48 89 ea             	mov    %rbp,%rdx
    2ee9:	4c 89 fe             	mov    %r15,%rsi
    2eec:	48 89 df             	mov    %rbx,%rdi
    2eef:	e8 7c f5 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2ef4:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2ef9:	48 8b 3b             	mov    (%rbx),%rdi
    2efc:	be 08 00 00 00       	mov    $0x8,%esi
    2f01:	49 8b 93 a0 00 00 00 	mov    0xa0(%r11),%rdx
    2f08:	e8 d3 f3 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    thread_data[x].type = WORKER;
    2f0d:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2f12:	ba 01 00 00 00       	mov    $0x1,%edx
    2f17:	31 c0                	xor    %eax,%eax
    2f19:	4c 8d 0d 20 47 00 00 	lea    0x4720(%rip),%r9        # 7640 <_IO_stdin_used+0x640>
    2f20:	bf 01 00 00 00       	mov    $0x1,%edi
    2f25:	41 c7 83 b8 00 00 00 01 00 00 00 	movl   $0x1,0xb8(%r11)
    2f30:	4c 89 ce             	mov    %r9,%rsi
    thread_data[x].running = 1;
    2f33:	41 c7 83 e4 00 00 00 01 00 00 00 	movl   $0x1,0xe4(%r11)
    2f3e:	e8 0d f5 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2f43:	4c 89 e9             	mov    %r13,%rcx
    2f46:	49 8d 77 38          	lea    0x38(%r15),%rsi
    2f4a:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    2f4e:	48 89 ea             	mov    %rbp,%rdx
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2f51:	41 bf 0e 00 00 00    	mov    $0xe,%r15d
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2f57:	e8 14 f5 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2f5c:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2f61:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    2f65:	be 08 00 00 00       	mov    $0x8,%esi
    2f6a:	49 8b 93 50 01 00 00 	mov    0x150(%r11),%rdx
    2f71:	e8 6a f3 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    thread_data[x].type = IO;
    2f76:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f7b:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].task_count = 0;
    2f80:	4c 8b 35 59 4b 00 00 	mov    0x4b59(%rip),%r14        # 7ae0 <_IO_stdin_used+0xae0>
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f87:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    2f8c:	41 c7 83 f8 08 00 00 02 00 00 00 	movl   $0x2,0x8f8(%r11)
    thread_data[x].task_count = 0;
    2f97:	4d 89 b3 20 09 00 00 	mov    %r14,0x920(%r11)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f9e:	e8 fd f3 ff ff       	call   23a0 <calloc@plt>
    2fa3:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2fa8:	be 00 08 00 00       	mov    $0x800,%esi
    2fad:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2faf:	49 89 83 38 09 00 00 	mov    %rax,0x938(%r11)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2fb6:	e8 f5 f4 ff ff       	call   24b0 <eventfd@plt>
    2fbb:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2fc0:	be 08 00 00 00       	mov    $0x8,%esi
    2fc5:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2fca:	41 89 83 40 09 00 00 	mov    %eax,0x940(%r11)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2fd1:	e8 ca f3 ff ff       	call   23a0 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
    2fd6:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2fdb:	ba 0d 00 00 00       	mov    $0xd,%edx
    2fe0:	48 8d 35 71 43 00 00 	lea    0x4371(%rip),%rsi        # 7358 <_IO_stdin_used+0x358>
    2fe7:	4c 89 68 08          	mov    %r13,0x8(%rax)
    2feb:	bf 01 00 00 00       	mov    $0x1,%edi
    2ff0:	4c 89 18             	mov    %r11,(%rax)
    thread_data[x].threads = my_thread_data;
    2ff3:	49 89 83 00 09 00 00 	mov    %rax,0x900(%r11)
    2ffa:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_count = thread_count;
    2ffc:	41 c7 83 08 09 00 00 02 00 00 00 	movl   $0x2,0x908(%r11)
    thread_data[x].thread_index = x;
    3007:	41 c7 83 f0 08 00 00 0d 00 00 00 	movl   $0xd,0x8f0(%r11)
    3012:	e8 39 f4 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3017:	48 8b 34 24          	mov    (%rsp),%rsi
    301b:	48 8d 7b 68          	lea    0x68(%rbx),%rdi
    301f:	4c 89 e1             	mov    %r12,%rcx
    3022:	48 8d 15 87 1b 00 00 	lea    0x1b87(%rip),%rdx        # 4bb0 <io_thread>
    3029:	4c 8d 63 70          	lea    0x70(%rbx),%r12
    302d:	48 81 c6 d8 02 00 00 	add    $0x2d8,%rsi
    3034:	e8 37 f4 ff ff       	call   2470 <pthread_create@plt>
    3039:	ba 0e 00 00 00       	mov    $0xe,%edx
    303e:	48 8d 35 2a 43 00 00 	lea    0x432a(%rip),%rsi        # 736f <_IO_stdin_used+0x36f>
    3045:	31 c0                	xor    %eax,%eax
    3047:	bf 01 00 00 00       	mov    $0x1,%edi
    304c:	e8 ff f3 ff ff       	call   2450 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3051:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3056:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    305b:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    3060:	4c 89 e3             	mov    %r12,%rbx
    3063:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
    3068:	48 05 10 03 00 00    	add    $0x310,%rax
    306e:	48 89 04 24          	mov    %rax,(%rsp)
    3072:	44 89 fa             	mov    %r15d,%edx
    3075:	48 8d 35 09 43 00 00 	lea    0x4309(%rip),%rsi        # 7385 <_IO_stdin_used+0x385>
    307c:	bf 01 00 00 00       	mov    $0x1,%edi
    3081:	31 c0                	xor    %eax,%eax
    3083:	e8 c8 f3 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    3088:	4c 89 75 30          	mov    %r14,0x30(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    308c:	be 08 00 00 00       	mov    $0x8,%esi
    3091:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = EXTERNAL;
    3096:	c7 45 08 03 00 00 00 	movl   $0x3,0x8(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    309d:	e8 fe f2 ff ff       	call   23a0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    30a2:	48 8b bc 24 88 00 00 00 	mov    0x88(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    30aa:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    30af:	c7 85 ac 00 00 00 01 00 00 00 	movl   $0x1,0xac(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    30b9:	48 89 45 40          	mov    %rax,0x40(%rbp)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    30bd:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    30c0:	bf 02 00 00 00       	mov    $0x2,%edi
    30c5:	e8 d6 f2 ff ff       	call   23a0 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    30ca:	44 89 7d 00          	mov    %r15d,0x0(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    30ce:	48 8b 34 24          	mov    (%rsp),%rsi
    30d2:	48 89 e9             	mov    %rbp,%rcx
    thread_data[x].threads = my_thread_data;
    30d5:	48 89 45 10          	mov    %rax,0x10(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    30d9:	48 89 df             	mov    %rbx,%rdi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    30dc:	48 83 c3 08          	add    $0x8,%rbx
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    30e0:	48 8d 15 49 07 00 00 	lea    0x749(%rip),%rdx        # 3830 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    30e7:	4c 89 20             	mov    %r12,(%rax)
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    30ea:	48 81 c5 b0 00 00 00 	add    $0xb0,%rbp
      my_thread_data[n] = &thread_data[n]; 
    30f1:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    30f5:	48 8b 05 d4 49 00 00 	mov    0x49d4(%rip),%rax        # 7ad0 <_IO_stdin_used+0xad0>
    30fc:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3103:	e8 68 f3 ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3108:	48 83 04 24 38       	addq   $0x38,(%rsp)
    310d:	48 83 84 24 88 00 00 00 10 	addq   $0x10,0x88(%rsp)
    3116:	41 83 ff 0e          	cmp    $0xe,%r15d
    311a:	75 6e                	jne    318a <main+0xb9a>
    311c:	41 bf 0f 00 00 00    	mov    $0xf,%r15d
    3122:	e9 4b ff ff ff       	jmp    3072 <main+0xa82>
    3127:	48 8d 05 52 2b 00 00 	lea    0x2b52(%rip),%rax        # 5c80 <barriered_work_ingest_andwork>
    312e:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    3133:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    313a:	e9 cb f8 ff ff       	jmp    2a0a <main+0x41a>
    313f:	48 8d 05 3a 26 00 00 	lea    0x263a(%rip),%rax        # 5780 <barriered_work>
    3146:	bd 02 00 00 00       	mov    $0x2,%ebp
    314b:	eb e6                	jmp    3133 <main+0xb43>
        other = (x + 1) % total_threads;
    314d:	41 8d 44 24 01       	lea    0x1(%r12),%eax
        thread_data[x].protected_state = &protected_state[x];
    3152:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3157:	45 31 c0             	xor    %r8d,%r8d
        my_thread_data[1] = &thread_data[other]; 
    315a:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    315e:	89 44 24 20          	mov    %eax,0x20(%rsp)
        other = (x + 1) % total_threads;
    3162:	41 89 c5             	mov    %eax,%r13d
        my_thread_data[1] = &thread_data[other]; 
    3165:	48 8d 14 50          	lea    (%rax,%rdx,2),%rdx
    3169:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    316e:	48 c1 e2 04          	shl    $0x4,%rdx
    3172:	48 01 c2             	add    %rax,%rdx
        my_thread_data[0] = &thread_data[x]; 
    3175:	4c 89 f8             	mov    %r15,%rax
    3178:	e9 76 f7 ff ff       	jmp    28f3 <main+0x303>
            CPU_SET(j, sendercpu);
    317d:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
          for (int j = 0 ; j < cores ; j++) {
    3185:	e9 e3 f7 ff ff       	jmp    296d <main+0x37d>
    318a:	48 8d 3d 11 42 00 00 	lea    0x4211(%rip),%rdi        # 73a2 <_IO_stdin_used+0x3a2>
    3191:	4c 89 24 24          	mov    %r12,(%rsp)
    3195:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    319a:	45 31 ed             	xor    %r13d,%r13d
    319d:	e8 4e f1 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    31a2:	4c 8b 34 24          	mov    (%rsp),%r14
    31a6:	4c 8d a4 24 90 00 00 00 	lea    0x90(%rsp),%r12
    31ae:	48 8d 2d 0b 42 00 00 	lea    0x420b(%rip),%rbp        # 73c0 <_IO_stdin_used+0x3c0>
    31b5:	0f 1f 00             	nopl   (%rax)
    void * result; 
    pthread_join(thread[x], &result);
    31b8:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    31bc:	4c 89 e6             	mov    %r12,%rsi
    31bf:	e8 2c f3 ff ff       	call   24f0 <pthread_join@plt>
    31c4:	44 89 ea             	mov    %r13d,%edx
    31c7:	48 89 ee             	mov    %rbp,%rsi
    31ca:	bf 01 00 00 00       	mov    $0x1,%edi
    31cf:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    31d1:	49 83 c5 01          	add    $0x1,%r13
    31d5:	e8 76 f2 ff ff       	call   2450 <__printf_chk@plt>
    31da:	49 83 fd 10          	cmp    $0x10,%r13
    31de:	75 d8                	jne    31b8 <main+0xbc8>
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    31e0:	45 31 c9             	xor    %r9d,%r9d
  for (int x = 0 ; x < thread_count ; x++) {
    31e3:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  long ingests = 0;
    31eb:	45 31 ff             	xor    %r15d,%r15d
  long sents = 0;
    31ee:	31 c9                	xor    %ecx,%ecx
    31f0:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    31f5:	4d 8d 6e 28          	lea    0x28(%r14),%r13
  long total = 0;
    31f9:	31 db                	xor    %ebx,%ebx
    31fb:	4d 89 fc             	mov    %r15,%r12
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    31fe:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
    3208:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    320d:	bf 0a 00 00 00       	mov    $0xa,%edi
    3212:	48 89 0c 24          	mov    %rcx,(%rsp)
    if (x % 2 == 1) {
    3216:	44 8b 74 24 10       	mov    0x10(%rsp),%r14d
    321b:	e8 b0 f0 ff ff       	call   22d0 <putchar@plt>
    3220:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    3228:	bf 01 00 00 00       	mov    $0x1,%edi
    322d:	48 8d 35 a0 41 00 00 	lea    0x41a0(%rip),%rsi        # 73d4 <_IO_stdin_used+0x3d4>
    3234:	41 83 f6 01          	xor    $0x1,%r14d
    3238:	48 8b 10             	mov    (%rax),%rdx
    323b:	31 c0                	xor    %eax,%eax
    323d:	e8 0e f2 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3242:	41 8b 55 08          	mov    0x8(%r13),%edx
    3246:	48 8b 0c 24          	mov    (%rsp),%rcx
    324a:	85 d2                	test   %edx,%edx
    324c:	0f 8e 2e 04 00 00    	jle    3680 <main+0x1090>
    3252:	48 63 f2             	movslq %edx,%rsi
    3255:	49 8b 45 00          	mov    0x0(%r13),%rax
    long v = 0;
    3259:	31 d2                	xor    %edx,%edx
    325b:	48 c1 e6 09          	shl    $0x9,%rsi
    325f:	48 01 c6             	add    %rax,%rsi
    3262:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      v += thread_data[me].tasks[n].v;
    3268:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    326f:	48 05 00 02 00 00    	add    $0x200,%rax
    3275:	48 39 f0             	cmp    %rsi,%rax
    3278:	75 ee                	jne    3268 <main+0xc78>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    327a:	49 63 c6             	movslq %r14d,%rax
    327d:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3282:	48 f7 d8             	neg    %rax
    3285:	25 b0 00 00 00       	and    $0xb0,%eax
    328a:	48 01 f8             	add    %rdi,%rax
    328d:	48 63 70 30          	movslq 0x30(%rax),%rsi
    3291:	85 f6                	test   %esi,%esi
    3293:	7e 1d                	jle    32b2 <main+0xcc2>
    3295:	48 8b 40 28          	mov    0x28(%rax),%rax
    3299:	48 c1 e6 09          	shl    $0x9,%rsi
    329d:	48 01 c6             	add    %rax,%rsi
      v += thread_data[other].tasks[n].v;
    32a0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    32a7:	48 05 00 02 00 00    	add    $0x200,%rax
    32ad:	48 39 f0             	cmp    %rsi,%rax
    32b0:	75 ee                	jne    32a0 <main+0xcb0>
    32b2:	48 8d 35 30 41 00 00 	lea    0x4130(%rip),%rsi        # 73e9 <_IO_stdin_used+0x3e9>
    32b9:	bf 01 00 00 00       	mov    $0x1,%edi
    32be:	31 c0                	xor    %eax,%eax
    32c0:	48 89 0c 24          	mov    %rcx,(%rsp)
    32c4:	e8 87 f1 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    32c9:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    32d1:	bf 01 00 00 00       	mov    $0x1,%edi
    32d6:	48 8b 30             	mov    (%rax),%rsi
    32d9:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    32e3:	48 f7 ee             	imul   %rsi
    32e6:	48 c1 fe 3f          	sar    $0x3f,%rsi
    32ea:	31 c0                	xor    %eax,%eax
    32ec:	48 d1 fa             	sar    %rdx
    32ef:	48 29 f2             	sub    %rsi,%rdx
    32f2:	48 8d 35 6f 43 00 00 	lea    0x436f(%rip),%rsi        # 7668 <_IO_stdin_used+0x668>
    32f9:	e8 52 f1 ff ff       	call   2450 <__printf_chk@plt>
    32fe:	bf 0a 00 00 00       	mov    $0xa,%edi
    3303:	e8 c8 ef ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3308:	41 8b 55 08          	mov    0x8(%r13),%edx
    330c:	48 8b 0c 24          	mov    (%rsp),%rcx
    3310:	85 d2                	test   %edx,%edx
    3312:	7e 58                	jle    336c <main+0xd7c>
    3314:	49 8b 45 00          	mov    0x0(%r13),%rax
    3318:	48 63 fa             	movslq %edx,%rdi
    331b:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    3320:	48 c1 e7 09          	shl    $0x9,%rdi
    3324:	48 01 c7             	add    %rax,%rdi
    3327:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3330:	48 8b 90 68 01 00 00 	mov    0x168(%rax),%rdx
      total += thread_data[x].tasks[n].n;
    3337:	48 03 98 08 01 00 00 	add    0x108(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    333e:	48 05 00 02 00 00    	add    $0x200,%rax
      ingests += thread_data[x].tasks[n].ingest_count;
    3344:	4c 03 a0 60 ff ff ff 	add    -0xa0(%rax),%r12
      sends += thread_data[x].tasks[n].sends;
    334b:	4c 03 b8 70 ff ff ff 	add    -0x90(%rax),%r15
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3352:	48 03 4a 10          	add    0x10(%rdx),%rcx
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3356:	4c 03 52 18          	add    0x18(%rdx),%r10
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    335a:	48 03 4a 30          	add    0x30(%rdx),%rcx
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    335e:	4c 03 52 38          	add    0x38(%rdx),%r10
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3362:	48 39 f8             	cmp    %rdi,%rax
    3365:	75 c9                	jne    3330 <main+0xd40>
    3367:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    336c:	45 31 f6             	xor    %r14d,%r14d
    336f:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    3374:	7e 7e                	jle    33f4 <main+0xe04>
    3376:	48 89 0c 24          	mov    %rcx,(%rsp)
    337a:	4c 89 e8             	mov    %r13,%rax
    337d:	49 89 dd             	mov    %rbx,%r13
    3380:	4c 89 f3             	mov    %r14,%rbx
    3383:	4d 89 e6             	mov    %r12,%r14
    3386:	49 89 c4             	mov    %rax,%r12
    3389:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3390:	49 8b 44 24 58       	mov    0x58(%r12),%rax
    3395:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    3399:	48 83 ec 08          	sub    $0x8,%rsp
    339d:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    33a2:	48 83 c3 01          	add    $0x1,%rbx
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    33a6:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    33aa:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    33ae:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    33b2:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    33b5:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    33b9:	4c 2b 01             	sub    (%rcx),%r8
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    33bc:	48 f7 e5             	mul    %rbp
    33bf:	8b 49 20             	mov    0x20(%rcx),%ecx
    33c2:	56                   	push   %rsi
    33c3:	31 c0                	xor    %eax,%eax
    33c5:	48 8d 35 bc 42 00 00 	lea    0x42bc(%rip),%rsi        # 7688 <_IO_stdin_used+0x688>
    33cc:	48 c1 ea 12          	shr    $0x12,%rdx
    33d0:	49 89 d1             	mov    %rdx,%r9
    33d3:	ba 02 00 00 00       	mov    $0x2,%edx
    33d8:	e8 73 f0 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    33dd:	41 5b                	pop    %r11
    33df:	58                   	pop    %rax
    33e0:	49 39 5c 24 68       	cmp    %rbx,0x68(%r12)
    33e5:	7f a9                	jg     3390 <main+0xda0>
    33e7:	48 8b 0c 24          	mov    (%rsp),%rcx
    33eb:	4c 89 eb             	mov    %r13,%rbx
    33ee:	4d 89 e5             	mov    %r12,%r13
    33f1:	4d 89 f4             	mov    %r14,%r12
      // printf("%ldns per thread\n", (seconds2 / 2));
    }
    // printf("cycles %ld\n", thread_data[x].cycles);

    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    33f4:	41 8b b5 84 00 00 00 	mov    0x84(%r13),%esi
    33fb:	85 f6                	test   %esi,%esi
    33fd:	0f 8e 18 01 00 00    	jle    351b <main+0xf2b>
    3403:	48 89 4c 24 28       	mov    %rcx,0x28(%rsp)
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3408:	4d 8b 4d 18          	mov    0x18(%r13),%r9
    340c:	31 d2                	xor    %edx,%edx
    340e:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    3413:	4c 89 64 24 38       	mov    %r12,0x38(%rsp)
    3418:	4c 89 7c 24 40       	mov    %r15,0x40(%rsp)
    341d:	0f 1f 00             	nopl   (%rax)
    3420:	49 8b 04 d1          	mov    (%r9,%rdx,8),%rax
    3424:	41 89 d7             	mov    %edx,%r15d
    3427:	48 8d 1c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rbx
    342f:	44 8b 00             	mov    (%rax),%r8d
    3432:	45 85 c0             	test   %r8d,%r8d
    3435:	0f 8e c0 00 00 00    	jle    34fb <main+0xf0b>
    343b:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3440:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3444:	31 f6                	xor    %esi,%esi
    3446:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3450:	49 89 f4             	mov    %rsi,%r12
    3453:	45 31 f6             	xor    %r14d,%r14d
    3456:	49 c1 e4 08          	shl    $0x8,%r12
    345a:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    345e:	8b ba 94 00 00 00    	mov    0x94(%rdx),%edi
    3464:	85 ff                	test   %edi,%edi
    3466:	7e 7a                	jle    34e2 <main+0xef2>
    3468:	48 89 34 24          	mov    %rsi,(%rsp)
    346c:	0f 1f 40 00          	nopl   0x0(%rax)
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3470:	4c 89 f1             	mov    %r14,%rcx
    3473:	48 83 ec 08          	sub    $0x8,%rsp
    3477:	bf 01 00 00 00       	mov    $0x1,%edi
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    347c:	49 83 c6 01          	add    $0x1,%r14
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3480:	48 c1 e1 05          	shl    $0x5,%rcx
    3484:	48 03 8a 88 00 00 00 	add    0x88(%rdx),%rcx
	  struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
	  const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
	  const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    348b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    348f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
	  printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3493:	48 89 f0             	mov    %rsi,%rax
	  const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3496:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    349a:	4c 2b 01             	sub    (%rcx),%r8
    349d:	56                   	push   %rsi
	  printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    349e:	48 f7 e5             	mul    %rbp
    34a1:	44 89 f9             	mov    %r15d,%ecx
    34a4:	48 8d 35 2d 42 00 00 	lea    0x422d(%rip),%rsi        # 76d8 <_IO_stdin_used+0x6d8>
    34ab:	31 c0                	xor    %eax,%eax
    34ad:	48 c1 ea 12          	shr    $0x12,%rdx
    34b1:	49 89 d1             	mov    %rdx,%r9
    34b4:	ba 02 00 00 00       	mov    $0x2,%edx
    34b9:	e8 92 ef ff ff       	call   2450 <__printf_chk@plt>
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    34be:	4d 8b 4d 18          	mov    0x18(%r13),%r9
    34c2:	41 58                	pop    %r8
    34c4:	41 5a                	pop    %r10
    34c6:	49 8b 04 19          	mov    (%r9,%rbx,1),%rax
    34ca:	48 8b 48 08          	mov    0x8(%rax),%rcx
    34ce:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    34d2:	44 39 b2 94 00 00 00 	cmp    %r14d,0x94(%rdx)
    34d9:	7f 95                	jg     3470 <main+0xe80>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    34db:	48 8b 34 24          	mov    (%rsp),%rsi
    34df:	44 8b 00             	mov    (%rax),%r8d
    34e2:	48 83 c6 01          	add    $0x1,%rsi
    34e6:	41 39 f0             	cmp    %esi,%r8d
    34e9:	0f 8f 61 ff ff ff    	jg     3450 <main+0xe60>
    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    34ef:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    34f4:	41 8b b5 84 00 00 00 	mov    0x84(%r13),%esi
    34fb:	48 83 c2 01          	add    $0x1,%rdx
    34ff:	39 d6                	cmp    %edx,%esi
    3501:	0f 8f 19 ff ff ff    	jg     3420 <main+0xe30>
    3507:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    350c:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    3511:	4c 8b 64 24 38       	mov    0x38(%rsp),%r12
    3516:	4c 8b 7c 24 40       	mov    0x40(%rsp),%r15
  for (int x = 0 ; x < thread_count ; x++) {
    351b:	8b 44 24 10          	mov    0x10(%rsp),%eax
    351f:	49 81 c5 b0 00 00 00 	add    $0xb0,%r13
    3526:	48 83 84 24 80 00 00 00 18 	addq   $0x18,0x80(%rsp)
    352f:	85 c0                	test   %eax,%eax
    3531:	75 0d                	jne    3540 <main+0xf50>
    3533:	c7 44 24 10 01 00 00 00 	movl   $0x1,0x10(%rsp)
    353b:	e9 cd fc ff ff       	jmp    320d <main+0xc1d>
    3540:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3545:	48 89 da             	mov    %rbx,%rdx
    3548:	bf 01 00 00 00       	mov    $0x1,%edi
    354d:	31 c0                	xor    %eax,%eax
    354f:	48 8d 35 a0 3e 00 00 	lea    0x3ea0(%rip),%rsi        # 73f6 <_IO_stdin_used+0x3f6>
    3556:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    355b:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
    3565:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    356a:	4c 89 3c 24          	mov    %r15,(%rsp)
    356e:	4d 89 e7             	mov    %r12,%r15
    3571:	e8 da ee ff ff       	call   2450 <__printf_chk@plt>
    3576:	bf 0a 00 00 00       	mov    $0xa,%edi
    357b:	49 c1 ff 3f          	sar    $0x3f,%r15
    357f:	e8 4c ed ff ff       	call   22d0 <putchar@plt>
    3584:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    3589:	bf 01 00 00 00       	mov    $0x1,%edi
    358e:	48 8d 35 9b 41 00 00 	lea    0x419b(%rip),%rsi        # 7730 <_IO_stdin_used+0x730>
    3595:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3599:	31 c0                	xor    %eax,%eax
    359b:	e8 b0 ee ff ff       	call   2450 <__printf_chk@plt>
    35a0:	4c 89 e0             	mov    %r12,%rax
    35a3:	bf 01 00 00 00       	mov    $0x1,%edi
    35a8:	48 8d 35 a9 41 00 00 	lea    0x41a9(%rip),%rsi        # 7758 <_IO_stdin_used+0x758>
    35af:	48 f7 ed             	imul   %rbp
    35b2:	31 c0                	xor    %eax,%eax
    35b4:	48 d1 fa             	sar    %rdx
    35b7:	4c 29 fa             	sub    %r15,%rdx
    35ba:	e8 91 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    35bf:	4c 8b 14 24          	mov    (%rsp),%r10
    35c3:	bf 01 00 00 00       	mov    $0x1,%edi
    35c8:	48 8d 35 b9 41 00 00 	lea    0x41b9(%rip),%rsi        # 7788 <_IO_stdin_used+0x788>
    35cf:	4c 89 d0             	mov    %r10,%rax
    35d2:	49 c1 fa 3f          	sar    $0x3f,%r10
    35d6:	48 f7 ed             	imul   %rbp
    35d9:	31 c0                	xor    %eax,%eax
    35db:	48 d1 fa             	sar    %rdx
    35de:	4c 29 d2             	sub    %r10,%rdx
    35e1:	e8 6a ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    35e6:	48 89 d8             	mov    %rbx,%rax
    35e9:	48 c1 fb 3f          	sar    $0x3f,%rbx
    35ed:	48 8d 35 c4 41 00 00 	lea    0x41c4(%rip),%rsi        # 77b8 <_IO_stdin_used+0x7b8>
    35f4:	48 f7 ed             	imul   %rbp
    35f7:	bf 01 00 00 00       	mov    $0x1,%edi
    35fc:	31 c0                	xor    %eax,%eax
    35fe:	48 d1 fa             	sar    %rdx
    3601:	48 29 da             	sub    %rbx,%rdx
    3604:	e8 47 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3609:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    360e:	bf 01 00 00 00       	mov    $0x1,%edi
    3613:	48 8d 35 f0 3d 00 00 	lea    0x3df0(%rip),%rsi        # 740a <_IO_stdin_used+0x40a>
    361a:	48 89 c8             	mov    %rcx,%rax
    361d:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3621:	48 f7 ed             	imul   %rbp
    3624:	31 c0                	xor    %eax,%eax
    3626:	48 d1 fa             	sar    %rdx
    3629:	48 29 ca             	sub    %rcx,%rdx
    362c:	e8 1f ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3631:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3636:	bf 01 00 00 00       	mov    $0x1,%edi
    363b:	48 8d 35 d9 3d 00 00 	lea    0x3dd9(%rip),%rsi        # 741b <_IO_stdin_used+0x41b>
    3642:	4c 89 c8             	mov    %r9,%rax
    3645:	49 c1 f9 3f          	sar    $0x3f,%r9
    3649:	48 f7 ed             	imul   %rbp
    364c:	48 d1 fa             	sar    %rdx
    364f:	4c 29 ca             	sub    %r9,%rdx
    3652:	31 c0                	xor    %eax,%eax
    3654:	e8 f7 ed ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3659:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    3661:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    366a:	75 1b                	jne    3687 <main+0x1097>
    366c:	48 81 c4 a8 00 00 00 	add    $0xa8,%rsp
    3673:	31 c0                	xor    %eax,%eax
    3675:	5b                   	pop    %rbx
    3676:	5d                   	pop    %rbp
    3677:	41 5c                	pop    %r12
    3679:	41 5d                	pop    %r13
    367b:	41 5e                	pop    %r14
    367d:	41 5f                	pop    %r15
    367f:	c3                   	ret
    long v = 0;
    3680:	31 d2                	xor    %edx,%edx
    3682:	e9 f3 fb ff ff       	jmp    327a <main+0xc8a>
}
    3687:	e8 a4 ec ff ff       	call   2330 <__stack_chk_fail@plt>
    368c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003690 <_start>:
    3690:	f3 0f 1e fa          	endbr64
    3694:	31 ed                	xor    %ebp,%ebp
    3696:	49 89 d1             	mov    %rdx,%r9
    3699:	5e                   	pop    %rsi
    369a:	48 89 e2             	mov    %rsp,%rdx
    369d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    36a1:	50                   	push   %rax
    36a2:	54                   	push   %rsp
    36a3:	45 31 c0             	xor    %r8d,%r8d
    36a6:	31 c9                	xor    %ecx,%ecx
    36a8:	48 8d 3d 41 ef ff ff 	lea    -0x10bf(%rip),%rdi        # 25f0 <main>
    36af:	ff 15 23 69 00 00    	call   *0x6923(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    36b5:	f4                   	hlt
    36b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000036c0 <deregister_tm_clones>:
    36c0:	48 8d 3d 59 69 00 00 	lea    0x6959(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    36c7:	48 8d 05 52 69 00 00 	lea    0x6952(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    36ce:	48 39 f8             	cmp    %rdi,%rax
    36d1:	74 15                	je     36e8 <deregister_tm_clones+0x28>
    36d3:	48 8b 05 06 69 00 00 	mov    0x6906(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    36da:	48 85 c0             	test   %rax,%rax
    36dd:	74 09                	je     36e8 <deregister_tm_clones+0x28>
    36df:	ff e0                	jmp    *%rax
    36e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    36e8:	c3                   	ret
    36e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000036f0 <register_tm_clones>:
    36f0:	48 8d 3d 29 69 00 00 	lea    0x6929(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    36f7:	48 8d 35 22 69 00 00 	lea    0x6922(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    36fe:	48 29 fe             	sub    %rdi,%rsi
    3701:	48 89 f0             	mov    %rsi,%rax
    3704:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3708:	48 c1 f8 03          	sar    $0x3,%rax
    370c:	48 01 c6             	add    %rax,%rsi
    370f:	48 d1 fe             	sar    %rsi
    3712:	74 14                	je     3728 <register_tm_clones+0x38>
    3714:	48 8b 05 d5 68 00 00 	mov    0x68d5(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    371b:	48 85 c0             	test   %rax,%rax
    371e:	74 08                	je     3728 <register_tm_clones+0x38>
    3720:	ff e0                	jmp    *%rax
    3722:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3728:	c3                   	ret
    3729:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003730 <__do_global_dtors_aux>:
    3730:	f3 0f 1e fa          	endbr64
    3734:	80 3d ed 68 00 00 00 	cmpb   $0x0,0x68ed(%rip)        # a028 <completed.0>
    373b:	75 2b                	jne    3768 <__do_global_dtors_aux+0x38>
    373d:	55                   	push   %rbp
    373e:	48 83 3d b2 68 00 00 00 	cmpq   $0x0,0x68b2(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3746:	48 89 e5             	mov    %rsp,%rbp
    3749:	74 0c                	je     3757 <__do_global_dtors_aux+0x27>
    374b:	48 8b 3d b6 68 00 00 	mov    0x68b6(%rip),%rdi        # a008 <__dso_handle>
    3752:	e8 59 eb ff ff       	call   22b0 <__cxa_finalize@plt>
    3757:	e8 64 ff ff ff       	call   36c0 <deregister_tm_clones>
    375c:	c6 05 c5 68 00 00 01 	movb   $0x1,0x68c5(%rip)        # a028 <completed.0>
    3763:	5d                   	pop    %rbp
    3764:	c3                   	ret
    3765:	0f 1f 00             	nopl   (%rax)
    3768:	c3                   	ret
    3769:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003770 <frame_dummy>:
    3770:	f3 0f 1e fa          	endbr64
    3774:	e9 77 ff ff ff       	jmp    36f0 <register_tm_clones>
    3779:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003780 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3780:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3784:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    378b:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    378f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3797:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    379b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    379f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    37a6:	48 85 c9             	test   %rcx,%rcx
    37a9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    37b0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    37b4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    37b8:	31 c0                	xor    %eax,%eax
    37ba:	c3                   	ret
    37bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000037c0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    37c0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    37c4:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    37cb:	85 c9                	test   %ecx,%ecx
    37cd:	7e 4f                	jle    381e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    37cf:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    37d6:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    37dd:	48 c1 e1 09          	shl    $0x9,%rcx
    37e1:	48 8b 50 10          	mov    0x10(%rax),%rdx
    37e5:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    37e9:	48 8b 70 28          	mov    0x28(%rax),%rsi
    37ed:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    37ef:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    37f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    37f8:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3800:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3808:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3813:	48 05 00 02 00 00    	add    $0x200,%rax
    3819:	48 39 c1             	cmp    %rax,%rcx
    381c:	75 da                	jne    37f8 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    381e:	0f ae f8             	sfence
}
    3821:	31 c0                	xor    %eax,%eax
    3823:	c3                   	ret
    3824:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    382f:	90                   	nop

0000000000003830 <external_thread>:
void * external_thread(void *arg) {
    3830:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3834:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    3838:	0f 85 fb 00 00 00    	jne    3939 <external_thread+0x109>
void * external_thread(void *arg) {
    383e:	41 57                	push   %r15
    3840:	49 89 ff             	mov    %rdi,%r15
    3843:	41 56                	push   %r14
    3845:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    3847:	4c 8d 2d b6 37 00 00 	lea    0x37b6(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    384e:	41 54                	push   %r12
    3850:	55                   	push   %rbp
    3851:	53                   	push   %rbx
    3852:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    3856:	8b 8f ac 00 00 00    	mov    0xac(%rdi),%ecx
    385c:	48 8b 7f 40          	mov    0x40(%rdi),%rdi
    3860:	85 c9                	test   %ecx,%ecx
    3862:	7e 6e                	jle    38d2 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3864:	45 31 e4             	xor    %r12d,%r12d
    3867:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3870:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    3878:	31 db                	xor    %ebx,%ebx
    387a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    387e:	48 8b 06             	mov    (%rsi),%rax
    3881:	8b 10                	mov    (%rax),%edx
    3883:	85 d2                	test   %edx,%edx
    3885:	7e 2a                	jle    38b1 <external_thread+0x81>
    3887:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    388b:	48 89 dd             	mov    %rbx,%rbp
    388e:	48 c1 e5 08          	shl    $0x8,%rbp
    3892:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    3896:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    389d:	45 85 c0             	test   %r8d,%r8d
    38a0:	74 36                	je     38d8 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    38a2:	48 83 c3 01          	add    $0x1,%rbx
    38a6:	39 da                	cmp    %ebx,%edx
    38a8:	7f e1                	jg     388b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    38aa:	41 8b 8f ac 00 00 00 	mov    0xac(%r15),%ecx
    38b1:	49 83 c4 01          	add    $0x1,%r12
    38b5:	44 39 e1             	cmp    %r12d,%ecx
    38b8:	7f b6                	jg     3870 <external_thread+0x40>
  while (data->running == 1) {
    38ba:	41 83 7f 34 01       	cmpl   $0x1,0x34(%r15)
    38bf:	74 9f                	je     3860 <external_thread+0x30>
}
    38c1:	48 83 c4 08          	add    $0x8,%rsp
    38c5:	31 c0                	xor    %eax,%eax
    38c7:	5b                   	pop    %rbx
    38c8:	5d                   	pop    %rbp
    38c9:	41 5c                	pop    %r12
    38cb:	41 5d                	pop    %r13
    38cd:	41 5e                	pop    %r14
    38cf:	41 5f                	pop    %r15
    38d1:	c3                   	ret
  while (data->running == 1) {
    38d2:	eb fe                	jmp    38d2 <external_thread+0xa2>
    38d4:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    38d8:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    38db:	48 8b 06             	mov    (%rsi),%rax
    38de:	48 8b 78 08          	mov    0x8(%rax),%rdi
    38e2:	48 01 ef             	add    %rbp,%rdi
    38e5:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    38ec:	48 c1 e6 05          	shl    $0x5,%rsi
    38f0:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    38f7:	bf 04 00 00 00       	mov    $0x4,%edi
    38fc:	e8 0f ea ff ff       	call   2310 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    3901:	49 8b 47 40          	mov    0x40(%r15),%rax
    3905:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    3909:	48 8b 40 08          	mov    0x8(%rax),%rax
    390d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    3918:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    391b:	49 8b 7f 40          	mov    0x40(%r15),%rdi
    391f:	48 83 c3 01          	add    $0x1,%rbx
    3923:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3927:	48 8b 06             	mov    (%rsi),%rax
    392a:	8b 10                	mov    (%rax),%edx
    392c:	39 da                	cmp    %ebx,%edx
    392e:	0f 8f 53 ff ff ff    	jg     3887 <external_thread+0x57>
    3934:	e9 71 ff ff ff       	jmp    38aa <external_thread+0x7a>
}
    3939:	31 c0                	xor    %eax,%eax
    393b:	c3                   	ret
    393c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003940 <timer_thread>:
void* timer_thread(void *arg) {
    3940:	f3 0f 1e fa          	endbr64
    3944:	41 57                	push   %r15
    3946:	48 8d 35 c3 36 00 00 	lea    0x36c3(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    394d:	49 89 ff             	mov    %rdi,%r15
    3950:	41 56                	push   %r14
    3952:	41 55                	push   %r13
    3954:	41 54                	push   %r12
    3956:	55                   	push   %rbp
    3957:	53                   	push   %rbx
    3958:	48 83 ec 58          	sub    $0x58,%rsp
    395c:	8b 17                	mov    (%rdi),%edx
    395e:	bf 01 00 00 00       	mov    $0x1,%edi
    3963:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    396c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3971:	31 c0                	xor    %eax,%eax
    3973:	e8 d8 ea ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3978:	66 0f 6f 05 50 40 00 00 	movdqa 0x4050(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    3980:	ba 88 13 00 00       	mov    $0x1388,%edx
    3985:	31 c0                	xor    %eax,%eax
    3987:	48 8d 35 94 36 00 00 	lea    0x3694(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    398e:	bf 01 00 00 00       	mov    $0x1,%edi
    3993:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3998:	e8 b3 ea ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    399d:	45 8b 67 34          	mov    0x34(%r15),%r12d
    39a1:	45 85 e4             	test   %r12d,%r12d
    39a4:	0f 84 9b 00 00 00    	je     3a45 <timer_thread+0x105>
  int n = 0;
    39aa:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    39ad:	45 31 e4             	xor    %r12d,%r12d
    39b0:	49 89 e5             	mov    %rsp,%r13
    y++;
    39b3:	31 db                	xor    %ebx,%ebx
    39b5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    39ba:	48 89 ef             	mov    %rbp,%rdi
    39bd:	4c 89 ee             	mov    %r13,%rsi
    n++;
    39c0:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    39c4:	e8 87 e9 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    39c9:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    39cd:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    39d2:	85 c0                	test   %eax,%eax
    39d4:	7e 47                	jle    3a1d <timer_thread+0xdd>
    39d6:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    39da:	49 c1 e4 09          	shl    $0x9,%r12
    39de:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    39e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    39e8:	4c 8b 11             	mov    (%rcx),%r10
    39eb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    39ed:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    39f1:	99                   	cltd
    39f2:	41 f7 7a 30          	idivl  0x30(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    39f6:	49 8b 72 28          	mov    0x28(%r10),%rsi
    39fa:	48 63 d2             	movslq %edx,%rdx
    39fd:	48 c1 e2 09          	shl    $0x9,%rdx
    3a01:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3a0c:	42 c7 84 26 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a18:	49 39 c8             	cmp    %rcx,%r8
    3a1b:	75 cb                	jne    39e8 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    3a1d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3a20:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3a24:	41 8b 57 34          	mov    0x34(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3a28:	48 8b 00             	mov    (%rax),%rax
    y++;
    3a2b:	39 78 30             	cmp    %edi,0x30(%rax)
    3a2e:	0f 4e fb             	cmovle %ebx,%edi
    3a31:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3a34:	85 d2                	test   %edx,%edx
    3a36:	74 0d                	je     3a45 <timer_thread+0x105>
    3a38:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3a3f:	0f 85 75 ff ff ff    	jne    39ba <timer_thread+0x7a>
    3a45:	48 8d 3d ec 35 00 00 	lea    0x35ec(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3a4c:	e8 9f e8 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3a51:	49 63 57 20          	movslq 0x20(%r15),%rdx
    3a55:	85 d2                	test   %edx,%edx
    3a57:	7e 6b                	jle    3ac4 <timer_thread+0x184>
    for (int y = 0 ; y < data->task_count ; y++) {
    3a59:	49 63 47 30          	movslq 0x30(%r15),%rax
    3a5d:	85 c0                	test   %eax,%eax
    3a5f:	7e 63                	jle    3ac4 <timer_thread+0x184>
    3a61:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3a65:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3a69:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3a71:	31 ff                	xor    %edi,%edi
    3a73:	48 89 c2             	mov    %rax,%rdx
    3a76:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3a7a:	48 8b 40 28          	mov    0x28(%rax),%rax
    3a7e:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3a82:	f6 c6 02             	test   $0x2,%dh
    3a85:	74 15                	je     3a9c <timer_thread+0x15c>
    3a87:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3a91:	48 05 00 02 00 00    	add    $0x200,%rax
    3a97:	48 39 c6             	cmp    %rax,%rsi
    3a9a:	74 1f                	je     3abb <timer_thread+0x17b>
      data->threads[x]->tasks[y].sending = 0;
    3a9c:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3aa6:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3aac:	c7 80 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3ab6:	48 39 c6             	cmp    %rax,%rsi
    3ab9:	75 e1                	jne    3a9c <timer_thread+0x15c>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3abb:	48 83 c7 08          	add    $0x8,%rdi
    3abf:	48 39 f9             	cmp    %rdi,%rcx
    3ac2:	75 b2                	jne    3a76 <timer_thread+0x136>
  asm volatile ("mfence" ::: "memory");
    3ac4:	0f ae f0             	mfence
  struct timespec drain = {
    3ac7:	66 0f 6f 05 11 3f 00 00 	movdqa 0x3f11(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    3acf:	48 8d 2d 87 35 00 00 	lea    0x3587(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3ad6:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3adb:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3adf:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ae4:	85 c0                	test   %eax,%eax
    3ae6:	7e 4c                	jle    3b34 <timer_thread+0x1f4>
    3ae8:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3aec:	4d 63 c4             	movslq %r12d,%r8
    3aef:	49 c1 e0 09          	shl    $0x9,%r8
    3af3:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3af7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3b00:	48 8b 19             	mov    (%rcx),%rbx
    3b03:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b05:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3b09:	99                   	cltd
    3b0a:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3b0d:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3b11:	48 63 d2             	movslq %edx,%rdx
    3b14:	48 c1 e2 09          	shl    $0x9,%rdx
    3b18:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3b23:	42 c7 84 06 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b2f:	4c 39 c9             	cmp    %r9,%rcx
    3b32:	75 cc                	jne    3b00 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    3b34:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3b37:	49 8b 47 10          	mov    0x10(%r15),%rax
    y++;
    3b3b:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3b3e:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3b41:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3b44:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3b48:	41 8b 7f 20          	mov    0x20(%r15),%edi
    3b4c:	85 ff                	test   %edi,%edi
    3b4e:	0f 8e bc 00 00 00    	jle    3c10 <timer_thread+0x2d0>
    3b54:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    3b57:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3b5d:	0f 1f 00             	nopl   (%rax)
    3b60:	4a 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbx
            all_empty = 0;
    3b68:	45 31 f6             	xor    %r14d,%r14d
    3b6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3b70:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3b74:	4c 89 f0             	mov    %r14,%rax
    3b77:	48 c1 e0 09          	shl    $0x9,%rax
    3b7b:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3b7f:	31 d2                	xor    %edx,%edx
    3b81:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3b88:	eb 16                	jmp    3ba0 <timer_thread+0x260>
    3b8a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3b90:	4d 85 c0             	test   %r8,%r8
    3b93:	7f 1f                	jg     3bb4 <timer_thread+0x274>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3b95:	83 c2 01             	add    $0x1,%edx
    3b98:	48 83 c0 20          	add    $0x20,%rax
    3b9c:	39 fa                	cmp    %edi,%edx
    3b9e:	74 2a                	je     3bca <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3ba0:	48 8b 08             	mov    (%rax),%rcx
    3ba3:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3ba7:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3bab:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3baf:	48 85 c9             	test   %rcx,%rcx
    3bb2:	7e dc                	jle    3b90 <timer_thread+0x250>
    3bb4:	bf 01 00 00 00       	mov    $0x1,%edi
    3bb9:	48 89 ee             	mov    %rbp,%rsi
    3bbc:	31 c0                	xor    %eax,%eax
    3bbe:	e8 8d e8 ff ff       	call   2450 <__printf_chk@plt>
            break;
    3bc3:	41 8b 7f 20          	mov    0x20(%r15),%edi
            all_empty = 0;
    3bc7:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3bca:	49 83 c6 01          	add    $0x1,%r14
    3bce:	44 39 f7             	cmp    %r14d,%edi
    3bd1:	7e 0d                	jle    3be0 <timer_thread+0x2a0>
    3bd3:	49 8b 47 10          	mov    0x10(%r15),%rax
    3bd7:	eb 97                	jmp    3b70 <timer_thread+0x230>
    3bd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3be0:	49 83 c5 01          	add    $0x1,%r13
    3be4:	44 39 ef             	cmp    %r13d,%edi
    3be7:	7e 0d                	jle    3bf6 <timer_thread+0x2b6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3be9:	85 ff                	test   %edi,%edi
    3beb:	7e 09                	jle    3bf6 <timer_thread+0x2b6>
    3bed:	49 8b 47 10          	mov    0x10(%r15),%rax
    3bf1:	e9 6a ff ff ff       	jmp    3b60 <timer_thread+0x220>
    if (all_empty == 1) {
    3bf6:	41 83 f9 01          	cmp    $0x1,%r9d
    3bfa:	74 14                	je     3c10 <timer_thread+0x2d0>
      nanosleep(&drain , &drainrem);
    3bfc:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3c01:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3c06:	e8 45 e7 ff ff       	call   2350 <nanosleep@plt>
    3c0b:	e9 cb fe ff ff       	jmp    3adb <timer_thread+0x19b>
    3c10:	48 8d 3d 3d 34 00 00 	lea    0x343d(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3c17:	e8 d4 e6 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3c1c:	41 8b 47 34          	mov    0x34(%r15),%eax
    3c20:	85 c0                	test   %eax,%eax
    3c22:	0f 84 cf 00 00 00    	je     3cf7 <timer_thread+0x3b7>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c28:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3c2c:	85 c9                	test   %ecx,%ecx
    3c2e:	7e 2d                	jle    3c5d <timer_thread+0x31d>
    3c30:	49 8b 47 10          	mov    0x10(%r15),%rax
    3c34:	31 db                	xor    %ebx,%ebx
    3c36:	48 8d 2d 31 34 00 00 	lea    0x3431(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3c3d:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->running = 0;
    3c40:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3c44:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3c48:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3c4f:	0f 84 cf 00 00 00    	je     3d24 <timer_thread+0x3e4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c55:	48 83 c3 01          	add    $0x1,%rbx
    3c59:	39 d9                	cmp    %ebx,%ecx
    3c5b:	7f e3                	jg     3c40 <timer_thread+0x300>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c5d:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3c61:	85 d2                	test   %edx,%edx
    3c63:	7e 7b                	jle    3ce0 <timer_thread+0x3a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3c65:	49 63 47 30          	movslq 0x30(%r15),%rax
    3c69:	85 c0                	test   %eax,%eax
    3c6b:	7e 73                	jle    3ce0 <timer_thread+0x3a0>
    3c6d:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3c71:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3c75:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3c7d:	31 c9                	xor    %ecx,%ecx
    3c7f:	48 89 c6             	mov    %rax,%rsi
    3c82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c88:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3c8c:	48 8b 40 28          	mov    0x28(%rax),%rax
    3c90:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3c94:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3c9a:	74 1c                	je     3cb8 <timer_thread+0x378>
    3c9c:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3ca6:	48 05 00 02 00 00    	add    $0x200,%rax
    3cac:	48 39 d0             	cmp    %rdx,%rax
    3caf:	74 26                	je     3cd7 <timer_thread+0x397>
    3cb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3cb8:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3cc2:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3cc8:	c7 80 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3cd2:	48 39 d0             	cmp    %rdx,%rax
    3cd5:	75 e1                	jne    3cb8 <timer_thread+0x378>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3cd7:	48 83 c1 08          	add    $0x8,%rcx
    3cdb:	48 39 f9             	cmp    %rdi,%rcx
    3cde:	75 a8                	jne    3c88 <timer_thread+0x348>
    asm volatile ("mfence" ::: "memory");
    3ce0:	0f ae f0             	mfence
    3ce3:	48 8d 3d 96 33 00 00 	lea    0x3396(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3cea:	e8 01 e6 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3cef:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
    3cf7:	48 8d 3d 89 33 00 00 	lea    0x3389(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3cfe:	e8 ed e5 ff ff       	call   22f0 <puts@plt>
}
    3d03:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3d08:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3d11:	75 47                	jne    3d5a <timer_thread+0x41a>
    3d13:	48 83 c4 58          	add    $0x58,%rsp
    3d17:	31 c0                	xor    %eax,%eax
    3d19:	5b                   	pop    %rbx
    3d1a:	5d                   	pop    %rbp
    3d1b:	41 5c                	pop    %r12
    3d1d:	41 5d                	pop    %r13
    3d1f:	41 5e                	pop    %r14
    3d21:	41 5f                	pop    %r15
    3d23:	c3                   	ret
    3d24:	48 89 ef             	mov    %rbp,%rdi
    3d27:	e8 c4 e5 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3d2c:	49 8b 47 10          	mov    0x10(%r15),%rax
    3d30:	be 01 00 00 00       	mov    $0x1,%esi
    3d35:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d39:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3d3d:	8b 78 50             	mov    0x50(%rax),%edi
    3d40:	e8 bb e6 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d45:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3d49:	39 d9                	cmp    %ebx,%ecx
    3d4b:	0f 8e 0c ff ff ff    	jle    3c5d <timer_thread+0x31d>
    3d51:	49 8b 47 10          	mov    0x10(%r15),%rax
    3d55:	e9 e6 fe ff ff       	jmp    3c40 <timer_thread+0x300>
}
    3d5a:	e8 d1 e5 ff ff       	call   2330 <__stack_chk_fail@plt>
    3d5f:	90                   	nop

0000000000003d60 <strtolower>:
void strtolower(char *str) {
    3d60:	f3 0f 1e fa          	endbr64
    3d64:	55                   	push   %rbp
    3d65:	53                   	push   %rbx
    3d66:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3d6a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3d6e:	84 db                	test   %bl,%bl
    3d70:	74 24                	je     3d96 <strtolower+0x36>
    3d72:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3d75:	e8 96 e7 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3d7a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3d80:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3d83:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3d87:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3d8a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3d8d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3d92:	84 db                	test   %bl,%bl
    3d94:	75 ea                	jne    3d80 <strtolower+0x20>
}
    3d96:	48 83 c4 08          	add    $0x8,%rsp
    3d9a:	5b                   	pop    %rbx
    3d9b:	5d                   	pop    %rbp
    3d9c:	c3                   	ret
    3d9d:	0f 1f 00             	nopl   (%rax)

0000000000003da0 <zh_malloc>:
void *zh_malloc(size_t size) {
    3da0:	f3 0f 1e fa          	endbr64
    3da4:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3da8:	e8 63 e6 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3dad:	48 85 c0             	test   %rax,%rax
    3db0:	74 05                	je     3db7 <zh_malloc+0x17>
}
    3db2:	48 83 c4 08          	add    $0x8,%rsp
    3db6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3db7:	48 8b 0d 62 62 00 00 	mov    0x6262(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    3dbe:	ba 28 00 00 00       	mov    $0x28,%edx
    3dc3:	be 01 00 00 00       	mov    $0x1,%esi
    3dc8:	48 8d 3d 61 36 00 00 	lea    0x3661(%rip),%rdi        # 7430 <_IO_stdin_used+0x430>
    3dcf:	e8 ec e6 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    3dd4:	bf 01 00 00 00       	mov    $0x1,%edi
    3dd9:	e8 c2 e6 ff ff       	call   24a0 <exit@plt>
    3dde:	66 90                	xchg   %ax,%ax

0000000000003de0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3de0:	f3 0f 1e fa          	endbr64
    3de4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    3de5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3dea:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3ded:	e8 6e e5 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3df2:	48 85 c0             	test   %rax,%rax
    3df5:	74 11                	je     3e08 <get_filename_ext+0x28>
    3df7:	48 39 c3             	cmp    %rax,%rbx
    3dfa:	74 0c                	je     3e08 <get_filename_ext+0x28>
    return dot + 1;
    3dfc:	48 83 c0 01          	add    $0x1,%rax
}
    3e00:	5b                   	pop    %rbx
    3e01:	c3                   	ret
    3e02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    3e08:	48 8d 05 c0 32 00 00 	lea    0x32c0(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    3e0f:	5b                   	pop    %rbx
    3e10:	c3                   	ret
    3e11:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3e1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003e20 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3e20:	f3 0f 1e fa          	endbr64
    3e24:	41 55                	push   %r13
    3e26:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3e29:	48 89 fe             	mov    %rdi,%rsi
    3e2c:	41 54                	push   %r12
    3e2e:	55                   	push   %rbp
    3e2f:	48 89 d5             	mov    %rdx,%rbp
    3e32:	ba 00 04 00 00       	mov    $0x400,%edx
    3e37:	53                   	push   %rbx
    3e38:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3e3f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3e48:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3e50:	31 c0                	xor    %eax,%eax
    3e52:	49 89 e4             	mov    %rsp,%r12
    3e55:	4c 89 e7             	mov    %r12,%rdi
    3e58:	e8 d3 e5 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    3e5d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3e62:	84 db                	test   %bl,%bl
    3e64:	74 24                	je     3e8a <send_headers+0x6a>
        *str = (char)tolower(*str);
    3e66:	e8 a5 e6 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3e6b:	48 8b 08             	mov    (%rax),%rcx
    3e6e:	4c 89 e0             	mov    %r12,%rax
    3e71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3e78:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3e7b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3e7f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3e82:	48 0f be 18          	movsbq (%rax),%rbx
    3e86:	84 db                	test   %bl,%bl
    3e88:	75 ee                	jne    3e78 <send_headers+0x58>
    void *buf = malloc(size);
    3e8a:	bf 11 00 00 00       	mov    $0x11,%edi
    3e8f:	e8 7c e5 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3e94:	48 85 c0             	test   %rax,%rax
    3e97:	0f 84 7e 04 00 00    	je     431b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3e9d:	66 0f 6f 05 4b 3b 00 00 	movdqa 0x3b4b(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    iov[0].iov_base = zh_malloc(slen);
    3ea5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    3ea9:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3eae:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3eb6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3eba:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3ebd:	e8 4e e5 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3ec2:	48 85 c0             	test   %rax,%rax
    3ec5:	0f 84 50 04 00 00    	je     431b <send_headers+0x4fb>
    3ecb:	66 0f 6f 05 2d 3b 00 00 	movdqa 0x3b2d(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    iov[1].iov_base = zh_malloc(slen);
    3ed3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    3ed7:	4c 89 e7             	mov    %r12,%rdi
    3eda:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3ee4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3eec:	0f 11 00             	movups %xmm0,(%rax)
    3eef:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3ef3:	be 2e 00 00 00       	mov    $0x2e,%esi
    3ef8:	e8 63 e4 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3efd:	48 85 c0             	test   %rax,%rax
    3f00:	0f 84 ea 02 00 00    	je     41f0 <send_headers+0x3d0>
    3f06:	4c 39 e0             	cmp    %r12,%rax
    3f09:	0f 84 e1 02 00 00    	je     41f0 <send_headers+0x3d0>
    return dot + 1;
    3f0f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3f13:	48 8d 3d 83 31 00 00 	lea    0x3183(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    3f1a:	48 89 de             	mov    %rbx,%rsi
    3f1d:	e8 8e e4 ff ff       	call   23b0 <strcmp@plt>
    3f22:	85 c0                	test   %eax,%eax
    3f24:	75 20                	jne    3f46 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3f26:	66 0f 6f 05 e2 3a 00 00 	movdqa 0x3ae2(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    3f2e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3f36:	66 0f 6f 05 e2 3a 00 00 	movdqa 0x3ae2(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    3f3e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    3f46:	48 89 de             	mov    %rbx,%rsi
    3f49:	48 8d 3d 51 31 00 00 	lea    0x3151(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    3f50:	e8 5b e4 ff ff       	call   23b0 <strcmp@plt>
    3f55:	85 c0                	test   %eax,%eax
    3f57:	75 20                	jne    3f79 <send_headers+0x159>
    3f59:	66 0f 6f 05 af 3a 00 00 	movdqa 0x3aaf(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    3f61:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3f69:	66 0f 6f 05 af 3a 00 00 	movdqa 0x3aaf(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    3f71:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    3f79:	48 89 de             	mov    %rbx,%rsi
    3f7c:	48 8d 3d 23 31 00 00 	lea    0x3123(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    3f83:	e8 28 e4 ff ff       	call   23b0 <strcmp@plt>
    3f88:	85 c0                	test   %eax,%eax
    3f8a:	0f 84 10 02 00 00    	je     41a0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    3f90:	48 89 de             	mov    %rbx,%rsi
    3f93:	48 8d 3d 10 31 00 00 	lea    0x3110(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    3f9a:	e8 11 e4 ff ff       	call   23b0 <strcmp@plt>
    3f9f:	85 c0                	test   %eax,%eax
    3fa1:	0f 84 a9 02 00 00    	je     4250 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    3fa7:	48 89 de             	mov    %rbx,%rsi
    3faa:	48 8d 3d fd 30 00 00 	lea    0x30fd(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    3fb1:	e8 fa e3 ff ff       	call   23b0 <strcmp@plt>
    3fb6:	85 c0                	test   %eax,%eax
    3fb8:	0f 84 6a 02 00 00    	je     4228 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    3fbe:	48 89 de             	mov    %rbx,%rsi
    3fc1:	48 8d 3d 29 31 00 00 	lea    0x3129(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    3fc8:	e8 e3 e3 ff ff       	call   23b0 <strcmp@plt>
    3fcd:	85 c0                	test   %eax,%eax
    3fcf:	0f 84 2b 02 00 00    	je     4200 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    3fd5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3fd8:	0f 84 52 01 00 00    	je     4130 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    3fde:	48 89 de             	mov    %rbx,%rsi
    3fe1:	48 8d 3d ca 30 00 00 	lea    0x30ca(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    3fe8:	e8 c3 e3 ff ff       	call   23b0 <strcmp@plt>
    3fed:	85 c0                	test   %eax,%eax
    3fef:	0f 84 ab 02 00 00    	je     42a0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    3ff5:	48 89 de             	mov    %rbx,%rsi
    3ff8:	48 8d 3d b7 30 00 00 	lea    0x30b7(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    3fff:	e8 ac e3 ff ff       	call   23b0 <strcmp@plt>
    4004:	85 c0                	test   %eax,%eax
    4006:	0f 84 6c 02 00 00    	je     4278 <send_headers+0x458>
    slen = strlen(send_buffer);
    400c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4014:	4c 89 e7             	mov    %r12,%rdi
    4017:	e8 04 e3 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    401c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    401f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4022:	e8 e9 e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4027:	48 85 c0             	test   %rax,%rax
    402a:	0f 84 eb 02 00 00    	je     431b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4030:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4034:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4038:	83 fb 08             	cmp    $0x8,%ebx
    403b:	0f 83 3f 01 00 00    	jae    4180 <send_headers+0x360>
    4041:	f6 c3 04             	test   $0x4,%bl
    4044:	0f 85 7b 02 00 00    	jne    42c5 <send_headers+0x4a5>
    404a:	85 db                	test   %ebx,%ebx
    404c:	74 13                	je     4061 <send_headers+0x241>
    404e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4056:	88 10                	mov    %dl,(%rax)
    4058:	f6 c3 02             	test   $0x2,%bl
    405b:	0f 85 96 02 00 00    	jne    42f7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4061:	4d 89 e8             	mov    %r13,%r8
    4064:	48 8d 0d 4f 30 00 00 	lea    0x304f(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    406b:	4c 89 e7             	mov    %r12,%rdi
    406e:	31 c0                	xor    %eax,%eax
    4070:	ba 00 04 00 00       	mov    $0x400,%edx
    4075:	be 01 00 00 00       	mov    $0x1,%esi
    407a:	e8 a1 e4 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    407f:	4c 89 e7             	mov    %r12,%rdi
    4082:	e8 99 e2 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4087:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    408a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    408d:	e8 7e e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4092:	48 85 c0             	test   %rax,%rax
    4095:	0f 84 80 02 00 00    	je     431b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    409b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    409f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    40a3:	83 fb 08             	cmp    $0x8,%ebx
    40a6:	0f 83 1c 01 00 00    	jae    41c8 <send_headers+0x3a8>
    40ac:	f6 c3 04             	test   $0x4,%bl
    40af:	0f 85 29 02 00 00    	jne    42de <send_headers+0x4be>
    40b5:	85 db                	test   %ebx,%ebx
    40b7:	74 13                	je     40cc <send_headers+0x2ac>
    40b9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    40c1:	88 10                	mov    %dl,(%rax)
    40c3:	f6 c3 02             	test   $0x2,%bl
    40c6:	0f 85 3d 02 00 00    	jne    4309 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40cc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    40d1:	bf 02 00 00 00       	mov    $0x2,%edi
    40d6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    40de:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    40e6:	e8 25 e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    40eb:	48 85 c0             	test   %rax,%rax
    40ee:	0f 84 27 02 00 00    	je     431b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    40f4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    40fc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4100:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4108:	66 89 10             	mov    %dx,(%rax)
}
    410b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4113:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    411c:	0f 85 20 02 00 00    	jne    4342 <send_headers+0x522>
    4122:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4129:	5b                   	pop    %rbx
    412a:	5d                   	pop    %rbp
    412b:	41 5c                	pop    %r12
    412d:	41 5d                	pop    %r13
    412f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4130:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4134:	0f 85 a4 fe ff ff    	jne    3fde <send_headers+0x1be>
    413a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    413e:	0f 85 9a fe ff ff    	jne    3fde <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4144:	66 0f 6f 05 24 39 00 00 	movdqa 0x3924(%rip),%xmm0        # 7a70 <_IO_stdin_used+0xa70>
    414c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4156:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    415e:	66 0f 6f 05 1a 39 00 00 	movdqa 0x391a(%rip),%xmm0        # 7a80 <_IO_stdin_used+0xa80>
    4166:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    416e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4176:	e9 63 fe ff ff       	jmp    3fde <send_headers+0x1be>
    417b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4180:	89 da                	mov    %ebx,%edx
    4182:	48 89 c7             	mov    %rax,%rdi
    4185:	4c 89 e6             	mov    %r12,%rsi
    4188:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    418d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4192:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4195:	c1 e9 03             	shr    $0x3,%ecx
    4198:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    419b:	e9 c1 fe ff ff       	jmp    4061 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    41a0:	66 0f 6f 05 68 38 00 00 	movdqa 0x3868(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    41a8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41b0:	66 0f 6f 05 78 38 00 00 	movdqa 0x3878(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
    41b8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    41c0:	e9 cb fd ff ff       	jmp    3f90 <send_headers+0x170>
    41c5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    41c8:	89 da                	mov    %ebx,%edx
    41ca:	48 89 c7             	mov    %rax,%rdi
    41cd:	4c 89 e6             	mov    %r12,%rsi
    41d0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    41d5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    41da:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    41dd:	c1 e9 03             	shr    $0x3,%ecx
    41e0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    41e3:	e9 e4 fe ff ff       	jmp    40cc <send_headers+0x2ac>
    41e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    41f0:	48 8d 1d d8 2e 00 00 	lea    0x2ed8(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    41f7:	e9 94 fd ff ff       	jmp    3f90 <send_headers+0x170>
    41fc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4200:	66 0f 6f 05 48 38 00 00 	movdqa 0x3848(%rip),%xmm0        # 7a50 <_IO_stdin_used+0xa50>
    4208:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4210:	66 0f 6f 05 48 38 00 00 	movdqa 0x3848(%rip),%xmm0        # 7a60 <_IO_stdin_used+0xa60>
    4218:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4220:	e9 b0 fd ff ff       	jmp    3fd5 <send_headers+0x1b5>
    4225:	0f 1f 00             	nopl   (%rax)
    4228:	66 0f 6f 05 20 38 00 00 	movdqa 0x3820(%rip),%xmm0        # 7a50 <_IO_stdin_used+0xa50>
    4230:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4238:	66 0f 6f 05 20 38 00 00 	movdqa 0x3820(%rip),%xmm0        # 7a60 <_IO_stdin_used+0xa60>
    4240:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4248:	e9 71 fd ff ff       	jmp    3fbe <send_headers+0x19e>
    424d:	0f 1f 00             	nopl   (%rax)
    4250:	66 0f 6f 05 b8 37 00 00 	movdqa 0x37b8(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4258:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4260:	66 0f 6f 05 d8 37 00 00 	movdqa 0x37d8(%rip),%xmm0        # 7a40 <_IO_stdin_used+0xa40>
    4268:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4270:	e9 32 fd ff ff       	jmp    3fa7 <send_headers+0x187>
    4275:	0f 1f 00             	nopl   (%rax)
    4278:	66 0f 6f 05 d0 37 00 00 	movdqa 0x37d0(%rip),%xmm0        # 7a50 <_IO_stdin_used+0xa50>
    4280:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4288:	66 0f 6f 05 10 38 00 00 	movdqa 0x3810(%rip),%xmm0        # 7aa0 <_IO_stdin_used+0xaa0>
    4290:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4298:	e9 6f fd ff ff       	jmp    400c <send_headers+0x1ec>
    429d:	0f 1f 00             	nopl   (%rax)
    42a0:	66 0f 6f 05 a8 37 00 00 	movdqa 0x37a8(%rip),%xmm0        # 7a50 <_IO_stdin_used+0xa50>
    42a8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    42b0:	66 0f 6f 05 d8 37 00 00 	movdqa 0x37d8(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
    42b8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    42c0:	e9 30 fd ff ff       	jmp    3ff5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    42c5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    42cc:	89 db                	mov    %ebx,%ebx
    42ce:	89 10                	mov    %edx,(%rax)
    42d0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    42d5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    42d9:	e9 83 fd ff ff       	jmp    4061 <send_headers+0x241>
    42de:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    42e5:	89 db                	mov    %ebx,%ebx
    42e7:	89 10                	mov    %edx,(%rax)
    42e9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    42ee:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    42f2:	e9 d5 fd ff ff       	jmp    40cc <send_headers+0x2ac>
    42f7:	89 db                	mov    %ebx,%ebx
    42f9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    42ff:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4304:	e9 58 fd ff ff       	jmp    4061 <send_headers+0x241>
    4309:	89 db                	mov    %ebx,%ebx
    430b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4311:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4316:	e9 b1 fd ff ff       	jmp    40cc <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    431b:	48 8b 0d fe 5c 00 00 	mov    0x5cfe(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4322:	ba 28 00 00 00       	mov    $0x28,%edx
    4327:	be 01 00 00 00       	mov    $0x1,%esi
    432c:	48 8d 3d fd 30 00 00 	lea    0x30fd(%rip),%rdi        # 7430 <_IO_stdin_used+0x430>
    4333:	e8 88 e1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4338:	bf 01 00 00 00       	mov    $0x1,%edi
    433d:	e8 5e e1 ff ff       	call   24a0 <exit@plt>
}
    4342:	e8 e9 df ff ff       	call   2330 <__stack_chk_fail@plt>
    4347:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004350 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4350:	f3 0f 1e fa          	endbr64
    4354:	41 55                	push   %r13
    4356:	49 89 d5             	mov    %rdx,%r13
    4359:	41 54                	push   %r12
    435b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    435e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4361:	55                   	push   %rbp
    4362:	53                   	push   %rbx
    4363:	48 89 f3             	mov    %rsi,%rbx
    4366:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    436a:	e8 a1 e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    436f:	48 85 c0             	test   %rax,%rax
    4372:	74 6b                	je     43df <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4374:	4c 89 e7             	mov    %r12,%rdi
    4377:	48 89 c5             	mov    %rax,%rbp
    437a:	31 f6                	xor    %esi,%esi
    437c:	31 c0                	xor    %eax,%eax
    437e:	e8 fd e0 ff ff       	call   2480 <open@plt>
    4383:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4386:	85 c0                	test   %eax,%eax
    4388:	0f 88 c8 e1 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    438e:	48 89 da             	mov    %rbx,%rdx
    4391:	48 89 ee             	mov    %rbp,%rsi
    4394:	89 c7                	mov    %eax,%edi
    4396:	e8 f5 df ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    439b:	48 98                	cltq
    439d:	48 39 d8             	cmp    %rbx,%rax
    43a0:	7c 1e                	jl     43c0 <copy_file_contents+0x70>
    close(fd);
    43a2:	44 89 e7             	mov    %r12d,%edi
    43a5:	e8 c6 df ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    43aa:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    43ae:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    43b2:	48 83 c4 08          	add    $0x8,%rsp
    43b6:	5b                   	pop    %rbx
    43b7:	5d                   	pop    %rbp
    43b8:	41 5c                	pop    %r12
    43ba:	41 5d                	pop    %r13
    43bc:	c3                   	ret
    43bd:	0f 1f 00             	nopl   (%rax)
    43c0:	48 8b 0d 59 5c 00 00 	mov    0x5c59(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    43c7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    43cc:	be 01 00 00 00       	mov    $0x1,%esi
    43d1:	48 8d 3d f8 2c 00 00 	lea    0x2cf8(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    43d8:	e8 e3 e0 ff ff       	call   24c0 <fwrite@plt>
    43dd:	eb c3                	jmp    43a2 <copy_file_contents+0x52>
    43df:	48 8b 0d 3a 5c 00 00 	mov    0x5c3a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    43e6:	ba 28 00 00 00       	mov    $0x28,%edx
    43eb:	be 01 00 00 00       	mov    $0x1,%esi
    43f0:	48 8d 3d 39 30 00 00 	lea    0x3039(%rip),%rdi        # 7430 <_IO_stdin_used+0x430>
    43f7:	e8 c4 e0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    43fc:	bf 01 00 00 00       	mov    $0x1,%edi
    4401:	e8 9a e0 ff ff       	call   24a0 <exit@plt>
    4406:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004410 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4410:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4414:	8b 46 44             	mov    0x44(%rsi),%eax
    4417:	48 89 fa             	mov    %rdi,%rdx
    441a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    441d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4423:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4426:	48 8b 07             	mov    (%rdi),%rax
    4429:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    442c:	f6 c1 02             	test   $0x2,%cl
    442f:	74 00                	je     4431 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4431:	89 f0                	mov    %esi,%eax
    4433:	44 29 c0             	sub    %r8d,%eax
    4436:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4439:	0f 82 23 e1 ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    443f:	c1 e9 0a             	shr    $0xa,%ecx
    4442:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4446:	8b 47 44             	mov    0x44(%rdi),%eax
    4449:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    444c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    444f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4452:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4455:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4459:	d3 e0                	shl    %cl,%eax
    445b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    445e:	48 c1 e0 06          	shl    $0x6,%rax
    4462:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4466:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    446c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    446f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4473:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4479:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4481:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4485:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4488:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    448f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4497:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    449b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    449f:	e8 9c de ff ff       	call   2340 <io_uring_submit@plt>
}
    44a4:	31 c0                	xor    %eax,%eax
    44a6:	48 83 c4 08          	add    $0x8,%rsp
    44aa:	c3                   	ret
    44ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000044b0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    44b0:	f3 0f 1e fa          	endbr64
    44b4:	41 55                	push   %r13
    44b6:	41 89 fd             	mov    %edi,%r13d
    44b9:	41 54                	push   %r12
    44bb:	55                   	push   %rbp
    44bc:	53                   	push   %rbx
    44bd:	48 89 f3             	mov    %rsi,%rbx
    44c0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    44c4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    44c7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    44cd:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    44d0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    44d3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    44d5:	f6 c1 02             	test   $0x2,%cl
    44d8:	74 00                	je     44da <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    44da:	89 c2                	mov    %eax,%edx
    44dc:	29 f2                	sub    %esi,%edx
    44de:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    44e1:	0f 82 8b e0 ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    44e7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    44ea:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    44ed:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    44f0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    44f5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    44f8:	23 6b 58             	and    0x58(%rbx),%ebp
    44fb:	d3 e5                	shl    %cl,%ebp
    44fd:	48 c1 e5 06          	shl    $0x6,%rbp
    4501:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4505:	e8 06 df ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    450a:	be 01 00 00 00       	mov    $0x1,%esi
    450f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4514:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4517:	e8 84 de ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    451c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4521:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4525:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4528:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    452d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4532:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    453b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4543:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4547:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    454b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4552:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    455a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    455e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4566:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    456e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4572:	e8 c9 dd ff ff       	call   2340 <io_uring_submit@plt>
}
    4577:	48 83 c4 08          	add    $0x8,%rsp
    457b:	31 c0                	xor    %eax,%eax
    457d:	5b                   	pop    %rbx
    457e:	5d                   	pop    %rbp
    457f:	41 5c                	pop    %r12
    4581:	41 5d                	pop    %r13
    4583:	c3                   	ret
    4584:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    458f:	90                   	nop

0000000000004590 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4590:	f3 0f 1e fa          	endbr64
    4594:	41 56                	push   %r14
    4596:	41 89 f6             	mov    %esi,%r14d
    4599:	41 55                	push   %r13
    459b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    459e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    45a3:	41 54                	push   %r12
    45a5:	55                   	push   %rbp
    45a6:	48 89 d5             	mov    %rdx,%rbp
    45a9:	53                   	push   %rbx
    void *buf = malloc(size);
    45aa:	e8 61 de ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    45af:	48 85 c0             	test   %rax,%rax
    45b2:	0f 84 dd 00 00 00    	je     4695 <_send_static_string_content+0x105>
    45b8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    45bb:	4c 89 ef             	mov    %r13,%rdi
    45be:	e8 5d dd ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    45c3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    45ca:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    45ce:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    45d1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    45d4:	e8 37 de ff ff       	call   2410 <malloc@plt>
    45d9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    45dc:	48 85 c0             	test   %rax,%rax
    45df:	0f 84 b0 00 00 00    	je     4695 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    45e5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    45e9:	4c 89 e2             	mov    %r12,%rdx
    45ec:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    45ef:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    45f3:	e8 e8 dd ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    45f8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    45fb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4601:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4604:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4608:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    460a:	f6 c1 02             	test   $0x2,%cl
    460d:	0f 85 7d 00 00 00    	jne    4690 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4613:	89 d0                	mov    %edx,%eax
    4615:	29 f0                	sub    %esi,%eax
    4617:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    461a:	0f 82 5c df ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4620:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4623:	8b 45 44             	mov    0x44(%rbp),%eax
    4626:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4629:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    462c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    462f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4632:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4638:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    463c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    463e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4641:	48 89 ef             	mov    %rbp,%rdi
    4644:	48 c1 e0 06          	shl    $0x6,%rax
    4648:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    464c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    464f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4653:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4659:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4661:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4665:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4668:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    466f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4677:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    467b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    467f:	5b                   	pop    %rbx
    4680:	5d                   	pop    %rbp
    4681:	41 5c                	pop    %r12
    4683:	41 5d                	pop    %r13
    4685:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4687:	e9 b4 dc ff ff       	jmp    2340 <io_uring_submit@plt>
    468c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4690:	e9 7e ff ff ff       	jmp    4613 <_send_static_string_content+0x83>
    4695:	48 8b 0d 84 59 00 00 	mov    0x5984(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    469c:	ba 28 00 00 00       	mov    $0x28,%edx
    46a1:	be 01 00 00 00       	mov    $0x1,%esi
    46a6:	48 8d 3d 83 2d 00 00 	lea    0x2d83(%rip),%rdi        # 7430 <_IO_stdin_used+0x430>
    46ad:	e8 0e de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    46b2:	bf 01 00 00 00       	mov    $0x1,%edi
    46b7:	e8 e4 dd ff ff       	call   24a0 <exit@plt>
    46bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000046c0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    46c0:	f3 0f 1e fa          	endbr64
    46c4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    46c7:	89 fe                	mov    %edi,%esi
    46c9:	48 8b 3d 48 59 00 00 	mov    0x5948(%rip),%rdi        # a018 <unimplemented_content>
    46d0:	e9 bb fe ff ff       	jmp    4590 <_send_static_string_content>
    46d5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000046e0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    46e0:	f3 0f 1e fa          	endbr64
    46e4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    46e7:	89 fe                	mov    %edi,%esi
    46e9:	48 8b 3d 20 59 00 00 	mov    0x5920(%rip),%rdi        # a010 <http_404_content>
    46f0:	e9 9b fe ff ff       	jmp    4590 <_send_static_string_content>
    46f5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004700 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4700:	f3 0f 1e fa          	endbr64
    4704:	41 56                	push   %r14
    4706:	41 55                	push   %r13
    4708:	49 89 d5             	mov    %rdx,%r13
    470b:	41 54                	push   %r12
    470d:	41 89 f4             	mov    %esi,%r12d
    4710:	55                   	push   %rbp
    4711:	48 89 fd             	mov    %rdi,%rbp
    4714:	53                   	push   %rbx
    4715:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    471c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4725:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    472d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    472f:	e8 ec db ff ff       	call   2320 <strlen@plt>
    4734:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4739:	48 89 c3             	mov    %rax,%rbx
    473c:	0f 84 b6 00 00 00    	je     47f8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4742:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4747:	48 89 ee             	mov    %rbp,%rsi
    474a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    474e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4753:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    475b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4763:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    476e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4776:	e8 45 dc ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    477b:	48 89 e6             	mov    %rsp,%rsi
    477e:	4c 89 f7             	mov    %r14,%rdi
    4781:	e8 4a dc ff ff       	call   23d0 <stat@plt>
    4786:	83 f8 ff             	cmp    $0xffffffff,%eax
    4789:	0f 84 d3 00 00 00    	je     4862 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    478f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4793:	25 00 f0 00 00       	and    $0xf000,%eax
    4798:	3d 00 80 00 00       	cmp    $0x8000,%eax
    479d:	0f 84 f5 00 00 00    	je     4898 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    47a3:	48 8b 3d 66 58 00 00 	mov    0x5866(%rip),%rdi        # a010 <http_404_content>
    47aa:	4c 89 ea             	mov    %r13,%rdx
    47ad:	44 89 e6             	mov    %r12d,%esi
    47b0:	e8 db fd ff ff       	call   4590 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    47b5:	4c 89 f2             	mov    %r14,%rdx
    47b8:	bf 01 00 00 00       	mov    $0x1,%edi
    47bd:	31 c0                	xor    %eax,%eax
    47bf:	48 8d 35 5a 29 00 00 	lea    0x295a(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    47c6:	e8 85 dc ff ff       	call   2450 <__printf_chk@plt>
}
    47cb:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    47d3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    47dc:	0f 85 20 01 00 00    	jne    4902 <handle_get_method+0x202>
    47e2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    47e9:	5b                   	pop    %rbx
    47ea:	5d                   	pop    %rbp
    47eb:	41 5c                	pop    %r12
    47ed:	41 5d                	pop    %r13
    47ef:	41 5e                	pop    %r14
    47f1:	c3                   	ret
    47f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    47f8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    47fd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4805:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    480a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    480d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4815:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4818:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4820:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    482b:	e8 90 db ff ff       	call   23c0 <__memcpy_chk@plt>
    4830:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4835:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    483a:	48 8d 35 aa 28 00 00 	lea    0x28aa(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4841:	48 29 d9             	sub    %rbx,%rcx
    4844:	ba 0b 00 00 00       	mov    $0xb,%edx
    4849:	e8 72 db ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    484e:	48 89 e6             	mov    %rsp,%rsi
    4851:	4c 89 f7             	mov    %r14,%rdi
    4854:	e8 77 db ff ff       	call   23d0 <stat@plt>
    4859:	83 f8 ff             	cmp    $0xffffffff,%eax
    485c:	0f 85 2d ff ff ff    	jne    478f <handle_get_method+0x8f>
    4862:	4c 89 f2             	mov    %r14,%rdx
    4865:	48 89 e9             	mov    %rbp,%rcx
    4868:	48 8d 35 87 28 00 00 	lea    0x2887(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    486f:	31 c0                	xor    %eax,%eax
    4871:	bf 01 00 00 00       	mov    $0x1,%edi
    4876:	e8 d5 db ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    487b:	48 8b 3d 8e 57 00 00 	mov    0x578e(%rip),%rdi        # a010 <http_404_content>
    4882:	4c 89 ea             	mov    %r13,%rdx
    4885:	44 89 e6             	mov    %r12d,%esi
    4888:	e8 03 fd ff ff       	call   4590 <_send_static_string_content>
}
    488d:	e9 39 ff ff ff       	jmp    47cb <handle_get_method+0xcb>
    4892:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4898:	bf 70 00 00 00       	mov    $0x70,%edi
    489d:	e8 6e db ff ff       	call   2410 <malloc@plt>
    48a2:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    48a5:	48 85 c0             	test   %rax,%rax
    48a8:	74 5d                	je     4907 <handle_get_method+0x207>
            req->client_socket = client_socket;
    48aa:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    48ae:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    48b3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    48b7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    48ba:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    48c1:	e8 5a f5 ff ff       	call   3e20 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    48c6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    48cb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    48cf:	4c 89 f7             	mov    %r14,%rdi
    48d2:	e8 79 fa ff ff       	call   4350 <copy_file_contents>
    48d7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    48dc:	4c 89 f2             	mov    %r14,%rdx
    48df:	31 c0                	xor    %eax,%eax
    48e1:	48 8d 35 26 28 00 00 	lea    0x2826(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    48e8:	bf 01 00 00 00       	mov    $0x1,%edi
    48ed:	e8 5e db ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    48f2:	4c 89 ee             	mov    %r13,%rsi
    48f5:	48 89 df             	mov    %rbx,%rdi
    48f8:	e8 13 fb ff ff       	call   4410 <add_write_request>
    48fd:	e9 c9 fe ff ff       	jmp    47cb <handle_get_method+0xcb>
}
    4902:	e8 29 da ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4907:	48 8b 0d 12 57 00 00 	mov    0x5712(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    490e:	ba 28 00 00 00       	mov    $0x28,%edx
    4913:	be 01 00 00 00       	mov    $0x1,%esi
    4918:	48 8d 3d 11 2b 00 00 	lea    0x2b11(%rip),%rdi        # 7430 <_IO_stdin_used+0x430>
    491f:	e8 9c db ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4924:	bf 01 00 00 00       	mov    $0x1,%edi
    4929:	e8 72 db ff ff       	call   24a0 <exit@plt>
    492e:	66 90                	xchg   %ax,%ax

0000000000004930 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4930:	f3 0f 1e fa          	endbr64
    4934:	41 57                	push   %r15
    4936:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4938:	4c 8d 35 46 27 00 00 	lea    0x2746(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    493f:	41 55                	push   %r13
    4941:	49 89 d5             	mov    %rdx,%r13
    4944:	41 54                	push   %r12
    4946:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4949:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    494c:	55                   	push   %rbp
    494d:	53                   	push   %rbx
    494e:	48 83 ec 18          	sub    $0x18,%rsp
    4952:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    495b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4960:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4962:	49 89 e7             	mov    %rsp,%r15
    4965:	4c 89 fa             	mov    %r15,%rdx
    4968:	e8 13 da ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    496d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4971:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4974:	84 db                	test   %bl,%bl
    4976:	74 1d                	je     4995 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4978:	e8 93 db ff ff       	call   2510 <__ctype_tolower_loc@plt>
    497d:	48 89 ea             	mov    %rbp,%rdx
    4980:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4983:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4987:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    498a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    498d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4991:	84 db                	test   %bl,%bl
    4993:	75 eb                	jne    4980 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4995:	4c 89 fa             	mov    %r15,%rdx
    4998:	4c 89 f6             	mov    %r14,%rsi
    499b:	31 ff                	xor    %edi,%edi
    499d:	e8 de d9 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    49a2:	48 8d 35 8a 27 00 00 	lea    0x278a(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    49a9:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    49ac:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    49af:	e8 fc d9 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    49b4:	4c 89 ea             	mov    %r13,%rdx
    49b7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    49ba:	85 c0                	test   %eax,%eax
    49bc:	75 2a                	jne    49e8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    49be:	48 89 df             	mov    %rbx,%rdi
    49c1:	e8 3a fd ff ff       	call   4700 <handle_get_method>
}
    49c6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    49cb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    49d4:	75 20                	jne    49f6 <handle_http_method+0xc6>
    49d6:	48 83 c4 18          	add    $0x18,%rsp
    49da:	5b                   	pop    %rbx
    49db:	5d                   	pop    %rbp
    49dc:	41 5c                	pop    %r12
    49de:	41 5d                	pop    %r13
    49e0:	41 5e                	pop    %r14
    49e2:	41 5f                	pop    %r15
    49e4:	c3                   	ret
    49e5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    49e8:	48 8b 3d 29 56 00 00 	mov    0x5629(%rip),%rdi        # a018 <unimplemented_content>
    49ef:	e8 9c fb ff ff       	call   4590 <_send_static_string_content>
}
    49f4:	eb d0                	jmp    49c6 <handle_http_method+0x96>
    49f6:	e8 35 d9 ff ff       	call   2330 <__stack_chk_fail@plt>
    49fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004a00 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4a00:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4a04:	85 d2                	test   %edx,%edx
    4a06:	7e 38                	jle    4a40 <get_line+0x40>
    4a08:	48 63 d2             	movslq %edx,%rdx
    4a0b:	48 83 c7 01          	add    $0x1,%rdi
    4a0f:	48 01 f2             	add    %rsi,%rdx
    4a12:	eb 11                	jmp    4a25 <get_line+0x25>
    4a14:	0f 1f 40 00          	nopl   0x0(%rax)
    4a18:	48 83 c6 01          	add    $0x1,%rsi
    4a1c:	48 83 c7 01          	add    $0x1,%rdi
    4a20:	48 39 d6             	cmp    %rdx,%rsi
    4a23:	74 1b                	je     4a40 <get_line+0x40>
        dest[i] = src[i];
    4a25:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4a29:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4a2b:	3c 0d                	cmp    $0xd,%al
    4a2d:	75 e9                	jne    4a18 <get_line+0x18>
    4a2f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4a32:	75 e4                	jne    4a18 <get_line+0x18>
            dest[i] = '\0';
    4a34:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4a37:	31 c0                	xor    %eax,%eax
    4a39:	c3                   	ret
    4a3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4a40:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4a45:	c3                   	ret
    4a46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004a50 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4a50:	f3 0f 1e fa          	endbr64
    4a54:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4a5b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4a5f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a68:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4a70:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4a72:	49 89 e2             	mov    %rsp,%r10
    4a75:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4a7d:	4c 89 d0             	mov    %r10,%rax
    4a80:	eb 13                	jmp    4a95 <handle_client_request+0x45>
    4a82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4a88:	48 83 c0 01          	add    $0x1,%rax
    4a8c:	48 83 c1 01          	add    $0x1,%rcx
    4a90:	4c 39 c8             	cmp    %r9,%rax
    4a93:	74 4b                	je     4ae0 <handle_client_request+0x90>
        dest[i] = src[i];
    4a95:	44 0f b6 01          	movzbl (%rcx),%r8d
    4a99:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4a9c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4aa0:	75 e6                	jne    4a88 <handle_client_request+0x38>
    4aa2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4aa6:	75 e0                	jne    4a88 <handle_client_request+0x38>
            dest[i] = '\0';
    4aa8:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4aab:	8b 47 08             	mov    0x8(%rdi),%eax
    4aae:	48 89 f2             	mov    %rsi,%rdx
    4ab1:	4c 89 d7             	mov    %r10,%rdi
    4ab4:	89 c6                	mov    %eax,%esi
    4ab6:	e8 75 fe ff ff       	call   4930 <handle_http_method>
}
    4abb:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4ac3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4acc:	75 39                	jne    4b07 <handle_client_request+0xb7>
    4ace:	31 c0                	xor    %eax,%eax
    4ad0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4ad7:	c3                   	ret
    4ad8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4ae0:	48 8b 0d 39 55 00 00 	mov    0x5539(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4ae7:	ba 12 00 00 00       	mov    $0x12,%edx
    4aec:	be 01 00 00 00       	mov    $0x1,%esi
    4af1:	48 8d 3d 3f 26 00 00 	lea    0x263f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4af8:	e8 c3 d9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4afd:	bf 01 00 00 00       	mov    $0x1,%edi
    4b02:	e8 99 d9 ff ff       	call   24a0 <exit@plt>
}
    4b07:	e8 24 d8 ff ff       	call   2330 <__stack_chk_fail@plt>
    4b0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004b10 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4b10:	f3 0f 1e fa          	endbr64
    4b14:	55                   	push   %rbp
    4b15:	53                   	push   %rbx
    4b16:	48 89 cb             	mov    %rcx,%rbx
    4b19:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4b1d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4b20:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4b23:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4b29:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4b2c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4b2f:	f6 c1 02             	test   $0x2,%cl
    4b32:	74 00                	je     4b34 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4b34:	41 89 c0             	mov    %eax,%r8d
    4b37:	45 29 c8             	sub    %r9d,%r8d
    4b3a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4b3e:	0f 82 48 da ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4b44:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4b47:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4b4a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4b4d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4b50:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4b53:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4b57:	d3 e5                	shl    %cl,%ebp
    4b59:	48 c1 e5 06          	shl    $0x6,%rbp
    4b5d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4b61:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4b64:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4b69:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4b70:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4b74:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4b78:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4b80:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4b88:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4b8c:	e8 7f d8 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4b91:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4b94:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4b9a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4b9e:	48 83 c4 08          	add    $0x8,%rsp
    4ba2:	5b                   	pop    %rbx
    4ba3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4ba4:	e9 97 d7 ff ff       	jmp    2340 <io_uring_submit@plt>
    4ba9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004bb0 <io_thread>:
void* io_thread(void *arg) {
    4bb0:	f3 0f 1e fa          	endbr64
    4bb4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4bb6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4bb8:	41 56                	push   %r14
    4bba:	41 55                	push   %r13
    4bbc:	41 54                	push   %r12
    4bbe:	55                   	push   %rbp
    4bbf:	48 89 fd             	mov    %rdi,%rbp
    4bc2:	53                   	push   %rbx
    4bc3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4bca:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4bd3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4bdb:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4bdf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4be4:	bf 00 01 00 00       	mov    $0x100,%edi
    4be9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4bec:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4bf0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4bf5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4bfa:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4bff:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4c04:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4c0c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4c11:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4c19:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4c1e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4c26:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4c2b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4c33:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4c38:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4c40:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4c45:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4c4d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4c55:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4c5d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4c65:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4c6d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4c75:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4c7d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4c85:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4c8d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4c95:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4c9d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4ca4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4cac:	e8 3f d7 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4cb1:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
    4cb5:	31 f6                	xor    %esi,%esi
    4cb7:	e8 24 d8 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4cbc:	31 d2                	xor    %edx,%edx
    4cbe:	be 01 00 00 00       	mov    $0x1,%esi
    4cc3:	bf 02 00 00 00       	mov    $0x2,%edi
    4cc8:	e8 63 d8 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4ccd:	83 f8 ff             	cmp    $0xffffffff,%eax
    4cd0:	0f 84 f8 d8 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    4cd6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4cdb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4ce1:	89 c7                	mov    %eax,%edi
    4ce3:	41 89 c4             	mov    %eax,%r12d
    4ce6:	ba 02 00 00 00       	mov    $0x2,%edx
    4ceb:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4cf0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4cf8:	e8 03 d6 ff ff       	call   2300 <setsockopt@plt>
    4cfd:	85 c0                	test   %eax,%eax
    4cff:	0f 88 9d d8 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4d05:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4d0a:	ba 10 00 00 00       	mov    $0x10,%edx
    4d0f:	44 89 e7             	mov    %r12d,%edi
    4d12:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4d1b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4d23:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4d2b:	e8 30 d7 ff ff       	call   2460 <bind@plt>
    4d30:	85 c0                	test   %eax,%eax
    4d32:	0f 88 a2 d8 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4d38:	be 0a 00 00 00       	mov    $0xa,%esi
    4d3d:	44 89 e7             	mov    %r12d,%edi
    4d40:	e8 db d6 ff ff       	call   2420 <listen@plt>
    4d45:	85 c0                	test   %eax,%eax
    4d47:	0f 88 61 d8 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4d4d:	ba db 18 00 00       	mov    $0x18db,%edx
    4d52:	48 8d 35 23 24 00 00 	lea    0x2423(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4d59:	bf 01 00 00 00       	mov    $0x1,%edi
    4d5e:	31 c0                	xor    %eax,%eax
    4d60:	e8 eb d6 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4d65:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4d6a:	48 89 d9             	mov    %rbx,%rcx
    4d6d:	44 89 e7             	mov    %r12d,%edi
    4d70:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4d75:	48 89 c6             	mov    %rax,%rsi
    4d78:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4d7d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4d82:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4d8a:	e8 81 fd ff ff       	call   4b10 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4d8f:	bf 01 00 00 00       	mov    $0x1,%edi
    4d94:	be 10 00 00 00       	mov    $0x10,%esi
    4d99:	e8 02 d6 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    4d9e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4da3:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4da6:	e8 65 d6 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4dab:	48 85 c0             	test   %rax,%rax
    4dae:	0f 84 ae 04 00 00    	je     5262 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    4db4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4db8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4dbf:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    4dc6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4dce:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4dd1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4dd6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4dd8:	f6 c1 02             	test   $0x2,%cl
    4ddb:	0f 85 0f 04 00 00    	jne    51f0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    4de1:	89 d0                	mov    %edx,%eax
    4de3:	29 f0                	sub    %esi,%eax
    4de5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4dec:	0f 82 d2 d7 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4df2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4df5:	48 8d 75 50          	lea    0x50(%rbp),%rsi
	sqe->addr3 = 0;
    4df9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4dfd:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e00:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e07:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e0a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4e11:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e18:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4e1a:	8b 55 50             	mov    0x50(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4e1d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4e22:	48 c1 e0 06          	shl    $0x6,%rax
    4e26:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4e2e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4e34:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4e37:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4e3f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4e43:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4e4b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4e53:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4e57:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4e5b:	e8 e0 d4 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4e60:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4e64:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4e69:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4e71:	0f 85 d7 01 00 00    	jne    504e <io_thread+0x49e>
    4e77:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4e7c:	4d 89 ce             	mov    %r9,%r14
    4e7f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4e84:	0f 1f 40 00          	nopl   0x0(%rax)
    4e88:	48 8d 3d 03 23 00 00 	lea    0x2303(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    4e8f:	e8 5c d4 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4e94:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4e9b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4ea2:	c1 e9 0b             	shr    $0xb,%ecx
    4ea5:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4ea8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4eb0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4eb2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4eba:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4ebc:	39 d0                	cmp    %edx,%eax
    4ebe:	74 36                	je     4ef6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4ec0:	89 f8                	mov    %edi,%eax
    4ec2:	21 d0                	and    %edx,%eax
    4ec4:	d3 e0                	shl    %cl,%eax
    4ec6:	48 c1 e0 04          	shl    $0x4,%rax
    4eca:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4ed2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4eda:	0f 85 a8 01 00 00    	jne    5088 <io_thread+0x4d8>
    4ee0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4ee4:	0f 85 0e 03 00 00    	jne    51f8 <io_thread+0x648>
			if (cqe->res < 0)
    4eea:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4eed:	83 c2 01             	add    $0x1,%edx
    4ef0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4ef2:	85 c0                	test   %eax,%eax
    4ef4:	79 b2                	jns    4ea8 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    4ef6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    4eff:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4f00:	45 31 c0             	xor    %r8d,%r8d
    4f03:	31 d2                	xor    %edx,%edx
    4f05:	b9 01 00 00 00       	mov    $0x1,%ecx
    4f0a:	4c 89 f6             	mov    %r14,%rsi
    4f0d:	48 89 df             	mov    %rbx,%rdi
    4f10:	e8 2b d5 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    4f15:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    4f18:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f1d:	48 83 38 01          	cmpq   $0x1,(%rax)
    4f21:	0f 84 e1 02 00 00    	je     5208 <io_thread+0x658>
    4f27:	48 8d 3d 8a 22 00 00 	lea    0x228a(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    4f2e:	e8 bd d3 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4f33:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4f38:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4f3b:	45 85 ff             	test   %r15d,%r15d
    4f3e:	0f 88 52 d6 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    4f44:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    4f47:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    4f4b:	85 c0                	test   %eax,%eax
    4f4d:	0f 88 d5 02 00 00    	js     5228 <io_thread+0x678>
      switch (req->event_type) {
    4f53:	41 83 f8 01          	cmp    $0x1,%r8d
    4f57:	0f 84 7b 01 00 00    	je     50d8 <io_thread+0x528>
    4f5d:	41 83 f8 02          	cmp    $0x2,%r8d
    4f61:	0f 84 a1 01 00 00    	je     5108 <io_thread+0x558>
    4f67:	45 85 c0             	test   %r8d,%r8d
    4f6a:	0f 85 50 01 00 00    	jne    50c0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4f70:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    4f75:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    4f7a:	48 89 d9             	mov    %rbx,%rcx
    4f7d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4f81:	e8 8a fb ff ff       	call   4b10 <add_accept_request>
              add_read_request(cqe->res, &ring);
    4f86:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f8b:	48 89 de             	mov    %rbx,%rsi
    4f8e:	8b 78 08             	mov    0x8(%rax),%edi
    4f91:	e8 1a f5 ff ff       	call   44b0 <add_read_request>
              free(req);
    4f96:	4c 89 e7             	mov    %r12,%rdi
    4f99:	e8 22 d3 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4f9e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    4fa3:	48 85 c0             	test   %rax,%rax
    4fa6:	0f 85 14 01 00 00    	jne    50c0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    4fac:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4fb3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4fba:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4fbd:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4fc2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4fc4:	f6 c1 02             	test   $0x2,%cl
    4fc7:	74 00                	je     4fc9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    4fc9:	89 d0                	mov    %edx,%eax
    4fcb:	29 f0                	sub    %esi,%eax
    4fcd:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4fd4:	0f 82 e0 d5 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    4fda:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    4fdd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    4fe2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    4fe6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4fe9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4ff0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ff3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4ffa:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5001:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5003:	8b 55 50             	mov    0x50(%rbp),%edx
    5006:	48 c1 e0 06          	shl    $0x6,%rax
    500a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5012:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5018:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    501b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5023:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5027:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    502f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5037:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    503b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    503f:	e8 fc d2 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5044:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    5048:	0f 84 3a fe ff ff    	je     4e88 <io_thread+0x2d8>
    504e:	48 8d 3d 9c 21 00 00 	lea    0x219c(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    5055:	e8 96 d2 ff ff       	call   22f0 <puts@plt>
}
    505a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5062:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    506b:	0f 85 18 02 00 00    	jne    5289 <io_thread+0x6d9>
    5071:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5078:	31 c0                	xor    %eax,%eax
    507a:	5b                   	pop    %rbx
    507b:	5d                   	pop    %rbp
    507c:	41 5c                	pop    %r12
    507e:	41 5d                	pop    %r13
    5080:	41 5e                	pop    %r14
    5082:	41 5f                	pop    %r15
    5084:	c3                   	ret
    5085:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5088:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    508d:	48 85 c0             	test   %rax,%rax
    5090:	0f 84 6a fe ff ff    	je     4f00 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5096:	48 83 38 01          	cmpq   $0x1,(%rax)
    509a:	0f 84 68 01 00 00    	je     5208 <io_thread+0x658>
    50a0:	48 8d 3d 11 21 00 00 	lea    0x2111(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    50a7:	e8 44 d2 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    50ac:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    50b1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    50b4:	e9 8b fe ff ff       	jmp    4f44 <io_thread+0x394>
    50b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    50c0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    50c8:	8b 02                	mov    (%rdx),%eax
    50ca:	83 c0 01             	add    $0x1,%eax
    50cd:	89 02                	mov    %eax,(%rdx)
}
    50cf:	e9 d8 fe ff ff       	jmp    4fac <io_thread+0x3fc>
    50d4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    50d8:	85 c0                	test   %eax,%eax
    50da:	75 74                	jne    5150 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    50dc:	48 8b 0d 3d 4f 00 00 	mov    0x4f3d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    50e3:	ba 0f 00 00 00       	mov    $0xf,%edx
    50e8:	be 01 00 00 00       	mov    $0x1,%esi
    50ed:	48 8d 3d ed 20 00 00 	lea    0x20ed(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    50f4:	e8 c7 d3 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    50f9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    50fe:	e9 a0 fe ff ff       	jmp    4fa3 <io_thread+0x3f3>
    5103:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5108:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    510d:	45 31 ff             	xor    %r15d,%r15d
    5110:	85 c0                	test   %eax,%eax
    5112:	7e 20                	jle    5134 <io_thread+0x584>
    5114:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5118:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    511b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    511f:	48 c1 e0 04          	shl    $0x4,%rax
    5123:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5128:	e8 93 d1 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    512d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5132:	7f e4                	jg     5118 <io_thread+0x568>
              close(req->client_socket);
    5134:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5139:	e8 32 d2 ff ff       	call   2370 <close@plt>
              free(req);
    513e:	4c 89 e7             	mov    %r12,%rdi
    5141:	e8 7a d1 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5146:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    514b:	e9 53 fe ff ff       	jmp    4fa3 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5150:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5155:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    515a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5162:	eb 11                	jmp    5175 <io_thread+0x5c5>
    5164:	0f 1f 40 00          	nopl   0x0(%rax)
    5168:	48 83 c0 01          	add    $0x1,%rax
    516c:	48 83 c2 01          	add    $0x1,%rdx
    5170:	48 39 c6             	cmp    %rax,%rsi
    5173:	74 4b                	je     51c0 <io_thread+0x610>
        dest[i] = src[i];
    5175:	0f b6 0a             	movzbl (%rdx),%ecx
    5178:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    517a:	80 f9 0d             	cmp    $0xd,%cl
    517d:	75 e9                	jne    5168 <io_thread+0x5b8>
    517f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5183:	75 e3                	jne    5168 <io_thread+0x5b8>
            dest[i] = '\0';
    5185:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5188:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    518d:	48 89 da             	mov    %rbx,%rdx
    5190:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5195:	e8 96 f7 ff ff       	call   4930 <handle_http_method>
              free(req->iov[0].iov_base);
    519a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    519f:	e8 1c d1 ff ff       	call   22c0 <free@plt>
              free(req);
    51a4:	4c 89 e7             	mov    %r12,%rdi
    51a7:	e8 14 d1 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    51ac:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    51b1:	e9 ed fd ff ff       	jmp    4fa3 <io_thread+0x3f3>
    51b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    51c0:	48 8b 0d 59 4e 00 00 	mov    0x4e59(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    51c7:	ba 12 00 00 00       	mov    $0x12,%edx
    51cc:	be 01 00 00 00       	mov    $0x1,%esi
    51d1:	48 8d 3d 5f 1f 00 00 	lea    0x1f5f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    51d8:	e8 e3 d2 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    51dd:	bf 01 00 00 00       	mov    $0x1,%edi
    51e2:	e8 b9 d2 ff ff       	call   24a0 <exit@plt>
    51e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    51f0:	e9 ec fb ff ff       	jmp    4de1 <io_thread+0x231>
    51f5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    51f8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    51fd:	e9 94 fe ff ff       	jmp    5096 <io_thread+0x4e6>
    5202:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5208:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5210:	48 8d 3d 8d 1f 00 00 	lea    0x1f8d(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    5217:	8b 02                	mov    (%rdx),%eax
    5219:	83 c0 01             	add    $0x1,%eax
    521c:	89 02                	mov    %eax,(%rdx)
    521e:	e8 cd d0 ff ff       	call   22f0 <puts@plt>
    5223:	e9 26 fe ff ff       	jmp    504e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5228:	f7 d8                	neg    %eax
    522a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    522f:	89 c7                	mov    %eax,%edi
    5231:	e8 ca d2 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5236:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    523b:	be 01 00 00 00       	mov    $0x1,%esi
    5240:	48 8b 3d d9 4d 00 00 	mov    0x4dd9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5247:	48 89 c1             	mov    %rax,%rcx
    524a:	48 8d 15 0f 22 00 00 	lea    0x220f(%rip),%rdx        # 7460 <_IO_stdin_used+0x460>
    5251:	31 c0                	xor    %eax,%eax
    5253:	e8 78 d2 ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5258:	bf 01 00 00 00       	mov    $0x1,%edi
    525d:	e8 3e d2 ff ff       	call   24a0 <exit@plt>
    5262:	48 8b 0d b7 4d 00 00 	mov    0x4db7(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5269:	ba 28 00 00 00       	mov    $0x28,%edx
    526e:	be 01 00 00 00       	mov    $0x1,%esi
    5273:	48 8d 3d b6 21 00 00 	lea    0x21b6(%rip),%rdi        # 7430 <_IO_stdin_used+0x430>
    527a:	e8 41 d2 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    527f:	bf 01 00 00 00       	mov    $0x1,%edi
    5284:	e8 17 d2 ff ff       	call   24a0 <exit@plt>
}
    5289:	e8 a2 d0 ff ff       	call   2330 <__stack_chk_fail@plt>
    528e:	66 90                	xchg   %ax,%ax

0000000000005290 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5290:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5294:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    529b:	8b 8e ac 00 00 00    	mov    0xac(%rsi),%ecx
    52a1:	85 c9                	test   %ecx,%ecx
    52a3:	0f 8e ea 00 00 00    	jle    5393 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    52a9:	41 56                	push   %r14
    52ab:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    52ad:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    52b0:	41 54                	push   %r12
    52b2:	49 89 fc             	mov    %rdi,%r12
    52b5:	55                   	push   %rbp
    52b6:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    52b7:	48 8b 7e 40          	mov    0x40(%rsi),%rdi
    52bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    52c0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    52c4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    52cc:	31 db                	xor    %ebx,%ebx
    52ce:	8b 10                	mov    (%rax),%edx
    52d0:	85 d2                	test   %edx,%edx
    52d2:	7e 26                	jle    52fa <barriered_work_ingest+0x6a>
    52d4:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    52d8:	48 89 dd             	mov    %rbx,%rbp
    52db:	48 c1 e5 08          	shl    $0x8,%rbp
    52df:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    52e3:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    52ea:	74 24                	je     5310 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    52ec:	48 83 c3 01          	add    $0x1,%rbx
    52f0:	39 da                	cmp    %ebx,%edx
    52f2:	7f e4                	jg     52d8 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    52f4:	8b 8e ac 00 00 00    	mov    0xac(%rsi),%ecx
    52fa:	49 83 c5 01          	add    $0x1,%r13
    52fe:	44 39 e9             	cmp    %r13d,%ecx
    5301:	7f bd                	jg     52c0 <barriered_work_ingest+0x30>
}
    5303:	5b                   	pop    %rbx
    5304:	31 c0                	xor    %eax,%eax
    5306:	5d                   	pop    %rbp
    5307:	41 5c                	pop    %r12
    5309:	41 5d                	pop    %r13
    530b:	41 5e                	pop    %r14
    530d:	c3                   	ret
    530e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    5310:	49 83 84 24 60 01 00 00 01 	addq   $0x1,0x160(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5319:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5320:	bf 04 00 00 00       	mov    $0x4,%edi
    5325:	48 c1 e6 05          	shl    $0x5,%rsi
    5329:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5330:	48 83 c6 10          	add    $0x10,%rsi
    5334:	e8 d7 cf ff ff       	call   2310 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5339:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5341:	48 8b 40 40          	mov    0x40(%rax),%rax
    5345:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5349:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    534d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5357:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    535d:	83 c0 01             	add    $0x1,%eax
    5360:	99                   	cltd
    5361:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5367:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    536d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5370:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5378:	48 83 c3 01          	add    $0x1,%rbx
    537c:	48 8b 7e 40          	mov    0x40(%rsi),%rdi
    5380:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5384:	8b 10                	mov    (%rax),%edx
    5386:	39 da                	cmp    %ebx,%edx
    5388:	0f 8f 46 ff ff ff    	jg     52d4 <barriered_work_ingest+0x44>
    538e:	e9 61 ff ff ff       	jmp    52f4 <barriered_work_ingest+0x64>
}
    5393:	31 c0                	xor    %eax,%eax
    5395:	c3                   	ret
    5396:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000053a0 <barriered_thread>:
void* barriered_thread(void *arg) {
    53a0:	f3 0f 1e fa          	endbr64
    53a4:	41 56                	push   %r14
    53a6:	41 55                	push   %r13
    53a8:	41 54                	push   %r12
  int t = 0;
    53aa:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    53ad:	55                   	push   %rbp
  int waiting = 0;
    53ae:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    53b0:	53                   	push   %rbx
    53b1:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    53b4:	83 7b 34 01          	cmpl   $0x1,0x34(%rbx)
    53b8:	0f 85 64 02 00 00    	jne    5622 <barriered_thread+0x282>
    if (t >= data->task_count) {
    53be:	8b 43 30             	mov    0x30(%rbx),%eax
    53c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    53c8:	41 39 c4             	cmp    %eax,%r12d
    53cb:	0f 8d 67 01 00 00    	jge    5538 <barriered_thread+0x198>
    53d1:	49 63 fc             	movslq %r12d,%rdi
    53d4:	48 c1 e7 09          	shl    $0x9,%rdi
    53d8:	49 89 fd             	mov    %rdi,%r13
    53db:	eb 31                	jmp    540e <barriered_thread+0x6e>
    53dd:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    53e0:	48 63 13             	movslq (%rbx),%rdx
    53e3:	48 8b 43 10          	mov    0x10(%rbx),%rax
    53e7:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    53eb:	48 8b 78 28          	mov    0x28(%rax),%rdi
    53ef:	4c 01 ef             	add    %r13,%rdi
    53f2:	e8 99 fe ff ff       	call   5290 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    53f7:	8b 43 30             	mov    0x30(%rbx),%eax
    53fa:	41 83 c4 01          	add    $0x1,%r12d
    53fe:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    5405:	44 39 e0             	cmp    %r12d,%eax
    5408:	0f 8e 0a 02 00 00    	jle    5618 <barriered_thread+0x278>
      if (data->tasks[t].available == 1) {
    540e:	48 8b 53 28          	mov    0x28(%rbx),%rdx
    5412:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    5416:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    541d:	75 c1                	jne    53e0 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    541f:	44 8b 43 18          	mov    0x18(%rbx),%r8d
          previous = t - 1;
    5423:	83 e8 01             	sub    $0x1,%eax
    5426:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    542b:	45 85 e4             	test   %r12d,%r12d
    542e:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5431:	45 85 c0             	test   %r8d,%r8d
    5434:	0f 8e 26 01 00 00    	jle    5560 <barriered_thread+0x1c0>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    543a:	48 63 c8             	movslq %eax,%rcx
    543d:	48 8b 43 10          	mov    0x10(%rbx),%rax
    5441:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5444:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    544a:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    5451:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    5455:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    5458:	45 31 f6             	xor    %r14d,%r14d
    545b:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    545f:	90                   	nop
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5460:	48 8b 10             	mov    (%rax),%rdx
    5463:	4c 8b 5a 28          	mov    0x28(%rdx),%r11
    5467:	49 01 cb             	add    %rcx,%r11
    546a:	4c 89 da             	mov    %r11,%rdx
    546d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    5474:	75 04                	jne    547a <barriered_thread+0xda>
            arrived++;
    5476:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    547a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    5480:	75 04                	jne    5486 <barriered_thread+0xe6>
            prearrive++;
    5482:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5486:	48 83 c0 08          	add    $0x8,%rax
    548a:	48 39 c6             	cmp    %rax,%rsi
    548d:	75 d1                	jne    5460 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    548f:	45 85 d2             	test   %r10d,%r10d
    5492:	0f 84 b8 00 00 00    	je     5550 <barriered_thread+0x1b0>
    5498:	45 39 d0             	cmp    %r10d,%r8d
    549b:	0f 84 af 00 00 00    	je     5550 <barriered_thread+0x1b0>
        if (arrived == 0 || arrived == data->thread_count) {
    54a1:	45 85 f6             	test   %r14d,%r14d
    54a4:	74 0a                	je     54b0 <barriered_thread+0x110>
    54a6:	44 39 73 18          	cmp    %r14d,0x18(%rbx)
    54aa:	0f 85 9e 01 00 00    	jne    564e <barriered_thread+0x2ae>
    54b0:	48 8b 53 28          	mov    0x28(%rbx),%rdx
          data->tasks[t].prearrive++;
    54b4:	4c 01 ea             	add    %r13,%rdx
    54b7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    54be:	45 85 e4             	test   %r12d,%r12d
    54c1:	75 0e                	jne    54d1 <barriered_thread+0x131>
    54c3:	48 8b 73 70          	mov    0x70(%rbx),%rsi
    54c7:	48 3b 73 78          	cmp    0x78(%rbx),%rsi
    54cb:	0f 8c 5f 01 00 00    	jl     5630 <barriered_thread+0x290>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    54d1:	48 63 0b             	movslq (%rbx),%rcx
    54d4:	48 8b 43 10          	mov    0x10(%rbx),%rax
          data->tasks[t].available = 0;
    54d8:	c7 82 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    54e2:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    54e6:	48 8b 78 28          	mov    0x28(%rax),%rdi
    54ea:	4c 01 ef             	add    %r13,%rdi
    54ed:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    54f3:	48 8b 43 28          	mov    0x28(%rbx),%rax
    54f7:	4c 01 e8             	add    %r13,%rax
    54fa:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5501:	8b 43 30             	mov    0x30(%rbx),%eax
          data->iteration_count++;
    5504:	48 83 43 68 01       	addq   $0x1,0x68(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5509:	83 e8 01             	sub    $0x1,%eax
    550c:	44 39 e0             	cmp    %r12d,%eax
    550f:	0f 84 a3 00 00 00    	je     55b8 <barriered_thread+0x218>
          asm volatile ("sfence" ::: "memory");
    5515:	0f ae f8             	sfence
          if (waiting == 0) {
    5518:	85 ed                	test   %ebp,%ebp
    551a:	0f 84 c8 00 00 00    	je     55e8 <barriered_thread+0x248>
        int arrived = 0; 
    5520:	bd 01 00 00 00       	mov    $0x1,%ebp
    5525:	e9 cd fe ff ff       	jmp    53f7 <barriered_thread+0x57>
  while (data->running == 1) {
    552a:	83 7b 34 01          	cmpl   $0x1,0x34(%rbx)
    552e:	0f 85 ee 00 00 00    	jne    5622 <barriered_thread+0x282>
    5534:	0f 1f 40 00          	nopl   0x0(%rax)
      data->cycles++;
    5538:	48 83 83 98 00 00 00 01 	addq   $0x1,0x98(%rbx)
    for (; t < data->task_count; t++) {
    5540:	85 c0                	test   %eax,%eax
    5542:	7e e6                	jle    552a <barriered_thread+0x18a>
    5544:	45 31 e4             	xor    %r12d,%r12d
    5547:	e9 85 fe ff ff       	jmp    53d1 <barriered_thread+0x31>
    554c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5550:	83 fd 01             	cmp    $0x1,%ebp
    5553:	74 1b                	je     5570 <barriered_thread+0x1d0>
        int arrived = 0; 
    5555:	31 ed                	xor    %ebp,%ebp
    5557:	e9 45 ff ff ff       	jmp    54a1 <barriered_thread+0x101>
    555c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5560:	83 fd 01             	cmp    $0x1,%ebp
    5563:	0f 85 4b ff ff ff    	jne    54b4 <barriered_thread+0x114>
        int arrived = 0; 
    5569:	45 31 f6             	xor    %r14d,%r14d
    556c:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5570:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
    5577:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    557c:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    557e:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5582:	48 8b 83 80 00 00 00 	mov    0x80(%rbx),%rax
    5589:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    558e:	e8 7d cd ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    5593:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
    559a:	48 83 c0 01          	add    $0x1,%rax
    559e:	48 99                	cqto
    55a0:	48 f7 bb 90 00 00 00 	idivq  0x90(%rbx)
    55a7:	48 89 93 88 00 00 00 	mov    %rdx,0x88(%rbx)
            waiting = 0; 
    55ae:	e9 ee fe ff ff       	jmp    54a1 <barriered_thread+0x101>
    55b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    55b8:	48 8b 73 70          	mov    0x70(%rbx),%rsi
    55bc:	48 3b 73 78          	cmp    0x78(%rbx),%rsi
    55c0:	0f 8d 4f ff ff ff    	jge    5515 <barriered_thread+0x175>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    55c6:	48 c1 e6 04          	shl    $0x4,%rsi
    55ca:	bf 04 00 00 00       	mov    $0x4,%edi
    55cf:	48 03 73 60          	add    0x60(%rbx),%rsi
    55d3:	e8 38 cd ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    55d8:	48 83 43 70 01       	addq   $0x1,0x70(%rbx)
    55dd:	e9 33 ff ff ff       	jmp    5515 <barriered_thread+0x175>
    55e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    55e8:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    55ef:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    55f4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    55f8:	48 8b 83 80 00 00 00 	mov    0x80(%rbx),%rax
    55ff:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5603:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5607:	e8 04 cd ff ff       	call   2310 <clock_gettime@plt>
            waiting = 1;
    560c:	e9 0f ff ff ff       	jmp    5520 <barriered_thread+0x180>
    5611:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    5618:	83 7b 34 01          	cmpl   $0x1,0x34(%rbx)
    561c:	0f 84 a6 fd ff ff    	je     53c8 <barriered_thread+0x28>
}
    5622:	5b                   	pop    %rbx
    5623:	31 c0                	xor    %eax,%eax
    5625:	5d                   	pop    %rbp
    5626:	41 5c                	pop    %r12
    5628:	41 5d                	pop    %r13
    562a:	41 5e                	pop    %r14
    562c:	c3                   	ret
    562d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    5630:	48 c1 e6 04          	shl    $0x4,%rsi
    5634:	bf 04 00 00 00       	mov    $0x4,%edi
    5639:	48 03 73 58          	add    0x58(%rbx),%rsi
    563d:	e8 ce cc ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    5642:	48 8b 53 28          	mov    0x28(%rbx),%rdx
    5646:	4c 01 ea             	add    %r13,%rdx
    5649:	e9 83 fe ff ff       	jmp    54d1 <barriered_thread+0x131>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    564e:	48 63 13             	movslq (%rbx),%rdx
    5651:	48 8b 43 10          	mov    0x10(%rbx),%rax
    5655:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5659:	48 8b 78 28          	mov    0x28(%rax),%rdi
    565d:	4c 01 ef             	add    %r13,%rdi
    5660:	e8 2b fc ff ff       	call   5290 <barriered_work_ingest>
          break;
    5665:	e9 4a fd ff ff       	jmp    53b4 <barriered_thread+0x14>
    566a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005670 <receive>:
int receive(struct BarrierTask *data) {
    5670:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5674:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    567a:	85 c0                	test   %eax,%eax
    567c:	0f 8e f1 00 00 00    	jle    5773 <receive+0x103>
int receive(struct BarrierTask *data) {
    5682:	41 54                	push   %r12
    5684:	48 89 fa             	mov    %rdi,%rdx
    5687:	55                   	push   %rbp
    5688:	31 ed                	xor    %ebp,%ebp
    568a:	53                   	push   %rbx
    568b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5690:	48 89 ee             	mov    %rbp,%rsi
    5693:	48 c1 e6 05          	shl    $0x5,%rsi
    5697:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    569e:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    56a1:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    56a6:	48 85 ff             	test   %rdi,%rdi
    56a9:	0f 8e a1 00 00 00    	jle    5750 <receive+0xe0>
      data->sends++;
    56af:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    56b6:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    56ba:	4c 63 1a             	movslq (%rdx),%r11
    56bd:	49 89 c9             	mov    %rcx,%r9
    56c0:	48 8d 41 01          	lea    0x1(%rcx),%rax
    56c4:	49 f7 d9             	neg    %r9
    56c7:	48 01 c7             	add    %rax,%rdi
    56ca:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    56ce:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    56d5:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    56d9:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    56dc:	49 29 c8             	sub    %rcx,%r8
    56df:	eb 10                	jmp    56f1 <receive+0x81>
    56e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    56e8:	48 83 c0 01          	add    $0x1,%rax
    56ec:	48 39 c7             	cmp    %rax,%rdi
    56ef:	74 5f                	je     5750 <receive+0xe0>
      data->n++;
    56f1:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    56f5:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
      data->n++;
    56fc:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5703:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5707:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    570b:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5710:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5714:	75 d2                	jne    56e8 <receive+0x78>
    5716:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    571d:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5721:	75 c5                	jne    56e8 <receive+0x78>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5723:	bf 01 00 00 00       	mov    $0x1,%edi
    5728:	b9 01 00 00 00       	mov    $0x1,%ecx
    572d:	ba 01 00 00 00       	mov    $0x1,%edx
    5732:	31 c0                	xor    %eax,%eax
    5734:	48 8d 35 4d 1d 00 00 	lea    0x1d4d(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    573b:	e8 10 cd ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5740:	bf 01 00 00 00       	mov    $0x1,%edi
    5745:	e8 56 cd ff ff       	call   24a0 <exit@plt>
    574a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5750:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    5759:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    575c:	48 83 c5 01          	add    $0x1,%rbp
    5760:	39 aa 34 01 00 00    	cmp    %ebp,0x134(%rdx)
    5766:	0f 8f 24 ff ff ff    	jg     5690 <receive+0x20>
}
    576c:	5b                   	pop    %rbx
    576d:	31 c0                	xor    %eax,%eax
    576f:	5d                   	pop    %rbp
    5770:	41 5c                	pop    %r12
    5772:	c3                   	ret
    5773:	31 c0                	xor    %eax,%eax
    5775:	c3                   	ret
    5776:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005780 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5780:	f3 0f 1e fa          	endbr64
    5784:	41 57                	push   %r15
    5786:	41 56                	push   %r14
    5788:	41 55                	push   %r13
    578a:	41 54                	push   %r12
    578c:	55                   	push   %rbp
    578d:	53                   	push   %rbx
    578e:	48 89 fb             	mov    %rdi,%rbx
    5791:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    5795:	8b 07                	mov    (%rdi),%eax
    5797:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    579d:	0f 84 3d 01 00 00    	je     58e0 <barriered_work+0x160>
    receive(data);
    57a3:	e8 c8 fe ff ff       	call   5670 <receive>
    while (data->scheduled == 1) {
    57a8:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    57af:	75 1b                	jne    57cc <barriered_work+0x4c>
    57b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    57b8:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    57c0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    57c3:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    57ca:	74 ec                	je     57b8 <barriered_work+0x38>
  if (data->sending == 1) {
    57cc:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    57d3:	0f 85 74 02 00 00    	jne    5a4d <barriered_work+0x2cd>
      for (int n = 0 ; n < data->thread_count; n++) {
    57d9:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    57df:	85 c0                	test   %eax,%eax
    57e1:	0f 8e 72 02 00 00    	jle    5a59 <barriered_work+0x2d9>
    57e7:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    57ee:	31 d2                	xor    %edx,%edx
    57f0:	48 89 0c 24          	mov    %rcx,(%rsp)
    57f4:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    57fb:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    5800:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5806:	0f 84 bf 00 00 00    	je     58cb <barriered_work+0x14b>
        struct Data *them = data->mailboxes[n].higher;
    580c:	49 89 d1             	mov    %rdx,%r9
    580f:	49 c1 e1 05          	shl    $0x5,%r9
    5813:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    581a:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    581e:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5822:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5826:	4d 39 c3             	cmp    %r8,%r11
    5829:	0f 8d 93 00 00 00    	jge    58c2 <barriered_work+0x142>
    582f:	4c 89 c6             	mov    %r8,%rsi
    5832:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5839:	4d 8b 71 10          	mov    0x10(%r9),%r14
    583d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5840:	49 8b 0a             	mov    (%r10),%rcx
    5843:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5847:	48 83 f8 02          	cmp    $0x2,%rax
    584b:	0f 86 8f 02 00 00    	jbe    5ae0 <barriered_work+0x360>
    5851:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5859:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5861:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5865:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5869:	4c 39 2c 24          	cmp    %r13,(%rsp)
    586d:	0f 83 fd 01 00 00    	jae    5a70 <barriered_work+0x2f0>
    5873:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5878:	4d 39 fc             	cmp    %r15,%r12
    587b:	0f 83 ef 01 00 00    	jae    5a70 <barriered_work+0x2f0>
    5881:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5885:	48 01 cf             	add    %rcx,%rdi
    5888:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5890:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5897:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    589b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    589f:	49 39 fb             	cmp    %rdi,%r11
    58a2:	75 ec                	jne    5890 <barriered_work+0x110>
    58a4:	0f 1f 40 00          	nopl   0x0(%rax)
    58a8:	48 01 f5             	add    %rsi,%rbp
    58ab:	4c 01 f6             	add    %r14,%rsi
    58ae:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    58b5:	49 89 71 10          	mov    %rsi,0x10(%r9)
    58b9:	4d 89 42 08          	mov    %r8,0x8(%r10)
    58bd:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    58c2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    58c5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    58cb:	48 83 c2 01          	add    $0x1,%rdx
    58cf:	39 d0                	cmp    %edx,%eax
    58d1:	0f 8f 29 ff ff ff    	jg     5800 <barriered_work+0x80>
    58d7:	e9 7d 01 00 00       	jmp    5a59 <barriered_work+0x2d9>
    58dc:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    58e0:	e8 8b fd ff ff       	call   5670 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    58e5:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    58ec:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    58ee:	45 85 c9             	test   %r9d,%r9d
    58f1:	0f 8e 85 00 00 00    	jle    597c <barriered_work+0x1fc>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    58f7:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    58fe:	4c 63 d8             	movslq %eax,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    5901:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5904:	49 c1 e3 09          	shl    $0x9,%r11
    5908:	4c 8b 52 10          	mov    0x10(%rdx),%r10
              int next_task = abs((t + 1) % (data->thread_count));
    590c:	99                   	cltd
    590d:	41 f7 f9             	idiv   %r9d
    5910:	4c 89 d7             	mov    %r10,%rdi
    5913:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
    5917:	89 d0                	mov    %edx,%eax
    5919:	f7 d8                	neg    %eax
    591b:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    591e:	45 31 c0             	xor    %r8d,%r8d
              int next_task = abs((t + 1) % (data->thread_count));
    5921:	48 63 ea             	movslq %edx,%rbp
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5924:	48 c1 e5 09          	shl    $0x9,%rbp
    5928:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    5930:	31 c0                	xor    %eax,%eax
    5932:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5938:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    593c:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    5940:	48 8b 8c 2a 68 01 00 00 	mov    0x168(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5948:	48 8b 17             	mov    (%rdi),%rdx
    594b:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    594f:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5952:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5956:	48 c1 e2 05          	shl    $0x5,%rdx
    595a:	4a 03 94 1e 68 01 00 00 	add    0x168(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5962:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    5966:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    596a:	49 39 c1             	cmp    %rax,%r9
    596d:	75 c9                	jne    5938 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    596f:	48 83 c7 08          	add    $0x8,%rdi
    5973:	49 83 c0 20          	add    $0x20,%r8
    5977:	49 39 fc             	cmp    %rdi,%r12
    597a:	75 b4                	jne    5930 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    597c:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    597f:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5986:	31 ff                	xor    %edi,%edi
    5988:	48 c1 e6 05          	shl    $0x5,%rsi
    598c:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5993:	e8 78 c9 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5998:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    599f:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    59a6:	48 8b 50 38          	mov    0x38(%rax),%rdx
    59aa:	8b 4a 10             	mov    0x10(%rdx),%ecx
    59ad:	8d 69 01             	lea    0x1(%rcx),%ebp
    59b0:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    59b3:	75 53                	jne    5a08 <barriered_work+0x288>
    59b5:	0f 1f 00             	nopl   (%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    59b8:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    59bf:	48 8b 40 10          	mov    0x10(%rax),%rax
    59c3:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    59c6:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    59ce:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    59d2:	48 c1 e7 09          	shl    $0x9,%rdi
    59d6:	48 03 78 28          	add    0x28(%rax),%rdi
    59da:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    59e0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    59e3:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    59ea:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    59f1:	74 c5                	je     59b8 <barriered_work+0x238>
    if (modcount != data->thread->protected_state->modcount) {
    59f3:	48 8b 40 38          	mov    0x38(%rax),%rax
    59f7:	3b 68 10             	cmp    0x10(%rax),%ebp
    59fa:	74 0c                	je     5a08 <barriered_work+0x288>
    59fc:	48 8d 3d 01 18 00 00 	lea    0x1801(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5a03:	e8 e8 c8 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5a08:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5a0f:	31 ff                	xor    %edi,%edi
    5a11:	48 c1 e6 05          	shl    $0x5,%rsi
    5a15:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5a1c:	48 83 c6 10          	add    $0x10,%rsi
    5a20:	e8 eb c8 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5a25:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    5a2c:	48 83 c0 01          	add    $0x1,%rax
    5a30:	48 99                	cqto
    5a32:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    5a39:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5a40:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    5a47:	0f 84 a8 00 00 00    	je     5af5 <barriered_work+0x375>
    5a4d:	48 8d 3d c0 17 00 00 	lea    0x17c0(%rip),%rdi        # 7214 <_IO_stdin_used+0x214>
    5a54:	e8 97 c8 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5a59:	0f ae f8             	sfence
}
    5a5c:	48 83 c4 18          	add    $0x18,%rsp
    5a60:	31 c0                	xor    %eax,%eax
    5a62:	5b                   	pop    %rbx
    5a63:	5d                   	pop    %rbp
    5a64:	41 5c                	pop    %r12
    5a66:	41 5d                	pop    %r13
    5a68:	41 5e                	pop    %r14
    5a6a:	41 5f                	pop    %r15
    5a6c:	c3                   	ret
    5a6d:	0f 1f 00             	nopl   (%rax)
    5a70:	49 89 f5             	mov    %rsi,%r13
    5a73:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5a7a:	4c 89 e7             	mov    %r12,%rdi
    5a7d:	49 d1 ed             	shr    %r13
    5a80:	49 c1 e5 04          	shl    $0x4,%r13
    5a84:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5a89:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5a8d:	41 83 e5 10          	and    $0x10,%r13d
    5a91:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5a95:	74 11                	je     5aa8 <barriered_work+0x328>
          them->messages[them->messages_count++] = data->message; 
    5a97:	48 83 c7 10          	add    $0x10,%rdi
    5a9b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5aa0:	49 39 ff             	cmp    %rdi,%r15
    5aa3:	74 13                	je     5ab8 <barriered_work+0x338>
    5aa5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5aa8:	0f 11 07             	movups %xmm0,(%rdi)
    5aab:	48 83 c7 20          	add    $0x20,%rdi
    5aaf:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5ab3:	49 39 ff             	cmp    %rdi,%r15
    5ab6:	75 f0                	jne    5aa8 <barriered_work+0x328>
    5ab8:	48 89 f7             	mov    %rsi,%rdi
    5abb:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5abf:	4c 01 df             	add    %r11,%rdi
    5ac2:	40 f6 c6 01          	test   $0x1,%sil
    5ac6:	0f 84 dc fd ff ff    	je     58a8 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    5acc:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5ad3:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5ad7:	e9 cc fd ff ff       	jmp    58a8 <barriered_work+0x128>
    5adc:	0f 1f 40 00          	nopl   0x0(%rax)
    5ae0:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5ae8:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5af0:	e9 8c fd ff ff       	jmp    5881 <barriered_work+0x101>
      for (int n = 0 ; n < data->thread_count; n++) {
    5af5:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    5afc:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5b02:	31 d2                	xor    %edx,%edx
    5b04:	48 89 0c 24          	mov    %rcx,(%rsp)
    5b08:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    5b0f:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5b14:	85 c0                	test   %eax,%eax
    5b16:	0f 8e 3d ff ff ff    	jle    5a59 <barriered_work+0x2d9>
    5b1c:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5b20:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5b26:	0f 84 af 00 00 00    	je     5bdb <barriered_work+0x45b>
        struct Data *them = data->mailboxes[n].higher;
    5b2c:	49 89 d1             	mov    %rdx,%r9
    5b2f:	49 c1 e1 05          	shl    $0x5,%r9
    5b33:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    5b3a:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    5b3e:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5b42:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5b46:	4d 39 d8             	cmp    %r11,%r8
    5b49:	0f 8e 83 00 00 00    	jle    5bd2 <barriered_work+0x452>
    5b4f:	4c 89 c6             	mov    %r8,%rsi
    5b52:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5b59:	4d 8b 71 10          	mov    0x10(%r9),%r14
    5b5d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5b60:	49 8b 0a             	mov    (%r10),%rcx
    5b63:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5b67:	48 83 f8 02          	cmp    $0x2,%rax
    5b6b:	0f 86 ef 00 00 00    	jbe    5c60 <barriered_work+0x4e0>
    5b71:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5b79:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5b81:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5b85:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5b89:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5b8d:	73 61                	jae    5bf0 <barriered_work+0x470>
    5b8f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5b94:	4d 39 fc             	cmp    %r15,%r12
    5b97:	73 57                	jae    5bf0 <barriered_work+0x470>
    5b99:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5b9d:	48 01 cf             	add    %rcx,%rdi
    5ba0:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5ba7:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5bab:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5baf:	49 39 fb             	cmp    %rdi,%r11
    5bb2:	75 ec                	jne    5ba0 <barriered_work+0x420>
    5bb4:	0f 1f 40 00          	nopl   0x0(%rax)
    5bb8:	48 01 f5             	add    %rsi,%rbp
    5bbb:	4c 01 f6             	add    %r14,%rsi
    5bbe:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5bc5:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5bc9:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5bcd:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5bd2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5bd5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5bdb:	48 83 c2 01          	add    $0x1,%rdx
    5bdf:	39 d0                	cmp    %edx,%eax
    5be1:	0f 8f 39 ff ff ff    	jg     5b20 <barriered_work+0x3a0>
    5be7:	e9 6d fe ff ff       	jmp    5a59 <barriered_work+0x2d9>
    5bec:	0f 1f 40 00          	nopl   0x0(%rax)
    5bf0:	49 89 f5             	mov    %rsi,%r13
    5bf3:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5bfa:	4c 89 e7             	mov    %r12,%rdi
    5bfd:	49 d1 ed             	shr    %r13
    5c00:	49 c1 e5 04          	shl    $0x4,%r13
    5c04:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5c09:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5c0d:	41 83 e5 10          	and    $0x10,%r13d
    5c11:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5c15:	74 11                	je     5c28 <barriered_work+0x4a8>
          them->messages[them->messages_count++] = data->message; 
    5c17:	48 83 c7 10          	add    $0x10,%rdi
    5c1b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5c20:	4c 39 ff             	cmp    %r15,%rdi
    5c23:	74 13                	je     5c38 <barriered_work+0x4b8>
    5c25:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5c28:	0f 11 07             	movups %xmm0,(%rdi)
    5c2b:	48 83 c7 20          	add    $0x20,%rdi
    5c2f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5c33:	4c 39 ff             	cmp    %r15,%rdi
    5c36:	75 f0                	jne    5c28 <barriered_work+0x4a8>
    5c38:	48 89 f7             	mov    %rsi,%rdi
    5c3b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5c3f:	4c 01 df             	add    %r11,%rdi
    5c42:	40 f6 c6 01          	test   $0x1,%sil
    5c46:	0f 84 6c ff ff ff    	je     5bb8 <barriered_work+0x438>
          them->messages[them->messages_count++] = data->message; 
    5c4c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5c53:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5c57:	e9 5c ff ff ff       	jmp    5bb8 <barriered_work+0x438>
    5c5c:	0f 1f 40 00          	nopl   0x0(%rax)
    5c60:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5c68:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5c70:	e9 24 ff ff ff       	jmp    5b99 <barriered_work+0x419>
    5c75:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005c80 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    5c80:	f3 0f 1e fa          	endbr64
    5c84:	53                   	push   %rbx
    5c85:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    5c88:	e8 03 f6 ff ff       	call   5290 <barriered_work_ingest>
  barriered_work(data);
    5c8d:	48 89 df             	mov    %rbx,%rdi
}
    5c90:	5b                   	pop    %rbx
  barriered_work(data);
    5c91:	e9 ea fa ff ff       	jmp    5780 <barriered_work>
    5c96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005ca0 <sendm>:
int sendm(struct BarrierTask *data) {
    5ca0:	f3 0f 1e fa          	endbr64
    5ca4:	41 57                	push   %r15
    5ca6:	41 56                	push   %r14
    5ca8:	41 55                	push   %r13
    5caa:	41 54                	push   %r12
    5cac:	55                   	push   %rbp
    5cad:	53                   	push   %rbx
    5cae:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5cb2:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
    5cb9:	0f 85 99 01 00 00    	jne    5e58 <sendm+0x1b8>
    5cbf:	48 8d b7 80 01 00 00 	lea    0x180(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5cc6:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    5ccc:	48 89 fa             	mov    %rdi,%rdx
    5ccf:	31 c9                	xor    %ecx,%ecx
    5cd1:	48 89 34 24          	mov    %rsi,(%rsp)
    5cd5:	48 8d b7 88 01 00 00 	lea    0x188(%rdi),%rsi
    5cdc:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5ce1:	85 c0                	test   %eax,%eax
    5ce3:	0f 8e ce 00 00 00    	jle    5db7 <sendm+0x117>
    5ce9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5cf0:	39 8a 30 01 00 00    	cmp    %ecx,0x130(%rdx)
    5cf6:	0f 84 af 00 00 00    	je     5dab <sendm+0x10b>
        struct Data *them = data->mailboxes[n].higher;
    5cfc:	49 89 ca             	mov    %rcx,%r10
    5cff:	49 c1 e2 05          	shl    $0x5,%r10
    5d03:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
    5d0a:	4d 8b 5a 08          	mov    0x8(%r10),%r11
        for (; them->messages_count < min;) {
    5d0e:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    5d12:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    5d16:	4c 39 cb             	cmp    %r9,%rbx
    5d19:	0f 8d 83 00 00 00    	jge    5da2 <sendm+0x102>
    5d1f:	4c 89 cf             	mov    %r9,%rdi
    5d22:	48 8b aa 08 01 00 00 	mov    0x108(%rdx),%rbp
    5d29:	4d 8b 72 10          	mov    0x10(%r10),%r14
    5d2d:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    5d30:	49 8b 33             	mov    (%r11),%rsi
    5d33:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    5d37:	48 83 f8 02          	cmp    $0x2,%rax
    5d3b:	0f 86 ff 00 00 00    	jbe    5e40 <sendm+0x1a0>
    5d41:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5d49:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5d51:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    5d55:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    5d59:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5d5d:	73 71                	jae    5dd0 <sendm+0x130>
    5d5f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5d64:	4d 39 fc             	cmp    %r15,%r12
    5d67:	73 67                	jae    5dd0 <sendm+0x130>
    5d69:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    5d6d:	49 01 f0             	add    %rsi,%r8
    5d70:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    5d77:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    5d7b:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    5d7f:	49 39 d8             	cmp    %rbx,%r8
    5d82:	75 ec                	jne    5d70 <sendm+0xd0>
    5d84:	0f 1f 40 00          	nopl   0x0(%rax)
    5d88:	48 01 fd             	add    %rdi,%rbp
    5d8b:	4c 01 f7             	add    %r14,%rdi
    5d8e:	48 89 aa 08 01 00 00 	mov    %rbp,0x108(%rdx)
    5d95:	49 89 7a 10          	mov    %rdi,0x10(%r10)
    5d99:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    5d9d:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5da2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5da5:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    5dab:	48 83 c1 01          	add    $0x1,%rcx
    5daf:	39 c8                	cmp    %ecx,%eax
    5db1:	0f 8f 39 ff ff ff    	jg     5cf0 <sendm+0x50>
}
    5db7:	48 83 c4 18          	add    $0x18,%rsp
    5dbb:	31 c0                	xor    %eax,%eax
    5dbd:	5b                   	pop    %rbx
    5dbe:	5d                   	pop    %rbp
    5dbf:	41 5c                	pop    %r12
    5dc1:	41 5d                	pop    %r13
    5dc3:	41 5e                	pop    %r14
    5dc5:	41 5f                	pop    %r15
    5dc7:	c3                   	ret
    5dc8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5dd0:	49 89 fd             	mov    %rdi,%r13
    5dd3:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    5dda:	4d 89 e0             	mov    %r12,%r8
    5ddd:	49 d1 ed             	shr    %r13
    5de0:	49 c1 e5 04          	shl    $0x4,%r13
    5de4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5de9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5ded:	41 83 e5 10          	and    $0x10,%r13d
    5df1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5df5:	74 11                	je     5e08 <sendm+0x168>
          them->messages[them->messages_count++] = data->message; 
    5df7:	49 83 c0 10          	add    $0x10,%r8
    5dfb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5e00:	4d 39 f8             	cmp    %r15,%r8
    5e03:	74 15                	je     5e1a <sendm+0x17a>
    5e05:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5e08:	41 0f 11 00          	movups %xmm0,(%r8)
    5e0c:	49 83 c0 20          	add    $0x20,%r8
    5e10:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    5e15:	4d 39 f8             	cmp    %r15,%r8
    5e18:	75 ee                	jne    5e08 <sendm+0x168>
    5e1a:	49 89 f8             	mov    %rdi,%r8
    5e1d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    5e21:	49 01 d8             	add    %rbx,%r8
    5e24:	40 f6 c7 01          	test   $0x1,%dil
    5e28:	0f 84 5a ff ff ff    	je     5d88 <sendm+0xe8>
          them->messages[them->messages_count++] = data->message; 
    5e2e:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    5e35:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    5e39:	e9 4a ff ff ff       	jmp    5d88 <sendm+0xe8>
    5e3e:	66 90                	xchg   %ax,%ax
    5e40:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5e48:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5e50:	e9 14 ff ff ff       	jmp    5d69 <sendm+0xc9>
    5e55:	0f 1f 00             	nopl   (%rax)
    5e58:	48 8d 3d b5 13 00 00 	lea    0x13b5(%rip),%rdi        # 7214 <_IO_stdin_used+0x214>
    5e5f:	e8 8c c4 ff ff       	call   22f0 <puts@plt>
    5e64:	e9 4e ff ff ff       	jmp    5db7 <sendm+0x117>
    5e69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005e70 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5e70:	f3 0f 1e fa          	endbr64
}
    5e74:	31 c0                	xor    %eax,%eax
    5e76:	c3                   	ret
    5e77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005e80 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5e80:	f3 0f 1e fa          	endbr64
    5e84:	31 c0                	xor    %eax,%eax
    5e86:	c3                   	ret
    5e87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005e90 <after>:
int after(struct timespec left, struct timespec right) {
    5e90:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5e94:	31 c0                	xor    %eax,%eax
    5e96:	48 39 d7             	cmp    %rdx,%rdi
    5e99:	7e 08                	jle    5ea3 <after+0x13>
    5e9b:	31 c0                	xor    %eax,%eax
    5e9d:	48 39 ce             	cmp    %rcx,%rsi
    5ea0:	0f 9f c0             	setg   %al
}
    5ea3:	c3                   	ret
    5ea4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5eaf:	90                   	nop

0000000000005eb0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5eb0:	f3 0f 1e fa          	endbr64
    5eb4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5eb9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5ebe:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ec0:	48 39 d7             	cmp    %rdx,%rdi
    5ec3:	7f 18                	jg     5edd <within+0x2d>
    5ec5:	4d 39 d8             	cmp    %r11,%r8
    5ec8:	0f 9e c2             	setle  %dl
    5ecb:	48 39 ce             	cmp    %rcx,%rsi
    5ece:	0f 9e c0             	setle  %al
    5ed1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5ed3:	31 c0                	xor    %eax,%eax
    5ed5:	4d 39 d1             	cmp    %r10,%r9
    5ed8:	0f 9e c0             	setle  %al
    5edb:	21 d0                	and    %edx,%eax
}
    5edd:	c3                   	ret
    5ede:	66 90                	xchg   %ax,%ax

0000000000005ee0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5ee0:	f3 0f 1e fa          	endbr64
    5ee4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5ee9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5eee:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5ef3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5ef8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5efd:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5f02:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5f07:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5f0c:	48 39 fe             	cmp    %rdi,%rsi
    5f0f:	7d 2f                	jge    5f40 <overlap+0x60>
    5f11:	48 39 ca             	cmp    %rcx,%rdx
    5f14:	7d 62                	jge    5f78 <overlap+0x98>
    5f16:	4d 39 da             	cmp    %r11,%r10
    5f19:	7d 0e                	jge    5f29 <overlap+0x49>
    return 1;
    5f1b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5f20:	4d 39 c1             	cmp    %r8,%r9
    5f23:	0f 8c 7f 00 00 00    	jl     5fa8 <overlap+0xc8>
  return 0;
    5f29:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f2b:	4d 39 c1             	cmp    %r8,%r9
    5f2e:	7f 4c                	jg     5f7c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5f30:	31 c0                	xor    %eax,%eax
    5f32:	4d 39 da             	cmp    %r11,%r10
    5f35:	0f 9e c0             	setle  %al
    5f38:	c3                   	ret
    5f39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5f40:	7e 4e                	jle    5f90 <overlap+0xb0>
    5f42:	48 39 ca             	cmp    %rcx,%rdx
    5f45:	7f 39                	jg     5f80 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f47:	75 31                	jne    5f7a <overlap+0x9a>
    5f49:	4d 39 c1             	cmp    %r8,%r9
    5f4c:	7c 2c                	jl     5f7a <overlap+0x9a>
    return 1;
    5f4e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5f53:	4d 39 da             	cmp    %r11,%r10
    5f56:	7d 24                	jge    5f7c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f58:	48 39 ca             	cmp    %rcx,%rdx
    5f5b:	0f 94 c2             	sete   %dl
    5f5e:	48 39 fe             	cmp    %rdi,%rsi
    5f61:	0f 94 c0             	sete   %al
    5f64:	21 c2                	and    %eax,%edx
    5f66:	31 c0                	xor    %eax,%eax
    5f68:	4d 39 c1             	cmp    %r8,%r9
    5f6b:	0f 94 c0             	sete   %al
    5f6e:	21 d0                	and    %edx,%eax
    5f70:	c3                   	ret
    5f71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5f78:	74 af                	je     5f29 <overlap+0x49>
  return 0;
    5f7a:	31 c0                	xor    %eax,%eax
}
    5f7c:	c3                   	ret
    5f7d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5f80:	4d 39 da             	cmp    %r11,%r10
    5f83:	7e c4                	jle    5f49 <overlap+0x69>
    return 1;
    5f85:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5f8a:	4d 39 c1             	cmp    %r8,%r9
    5f8d:	7e ba                	jle    5f49 <overlap+0x69>
    5f8f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f90:	48 39 ca             	cmp    %rcx,%rdx
    5f93:	7c 94                	jl     5f29 <overlap+0x49>
    5f95:	4d 39 c1             	cmp    %r8,%r9
    5f98:	7d b4                	jge    5f4e <overlap+0x6e>
    5f9a:	48 39 ca             	cmp    %rcx,%rdx
    5f9d:	74 91                	je     5f30 <overlap+0x50>
    5f9f:	eb d9                	jmp    5f7a <overlap+0x9a>
    5fa1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5fa8:	c3                   	ret
    5fa9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005fb0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5fb0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5fb4:	85 f6                	test   %esi,%esi
    5fb6:	0f 8e 44 03 00 00    	jle    6300 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    5fbc:	41 57                	push   %r15
    5fbe:	41 89 f7             	mov    %esi,%r15d
    5fc1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5fc3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5fc6:	41 55                	push   %r13
    5fc8:	41 54                	push   %r12
    5fca:	55                   	push   %rbp
    5fcb:	53                   	push   %rbx
    5fcc:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5fd0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5fd4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5fd9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5fde:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    5fe1:	45 39 e6             	cmp    %r12d,%r14d
    5fe4:	0f 84 4e 02 00 00    	je     6238 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5fea:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5fef:	8b 50 08             	mov    0x8(%rax),%edx
    5ff2:	85 d2                	test   %edx,%edx
    5ff4:	0f 8e 3e 02 00 00    	jle    6238 <verify+0x288>
    5ffa:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    5fff:	31 c9                	xor    %ecx,%ecx
    6001:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    6006:	31 c0                	xor    %eax,%eax
    6008:	44 89 f2             	mov    %r14d,%edx
    600b:	bf 01 00 00 00       	mov    $0x1,%edi
    6010:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6015:	48 8d 35 04 12 00 00 	lea    0x1204(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    601c:	e8 2f c4 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6021:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6026:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    602b:	8b 40 08             	mov    0x8(%rax),%eax
    602e:	85 c0                	test   %eax,%eax
    6030:	0f 8e e6 01 00 00    	jle    621c <verify+0x26c>
    6036:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6039:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    603e:	31 db                	xor    %ebx,%ebx
    6040:	48 c1 e0 09          	shl    $0x9,%rax
    6044:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6049:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    604e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6053:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6058:	4c 8b 20             	mov    (%rax),%r12
    605b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6060:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6065:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    606a:	49 89 de             	mov    %rbx,%r14
    606d:	48 8d 35 c1 11 00 00 	lea    0x11c1(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    6074:	49 c1 e6 09          	shl    $0x9,%r14
    6078:	bf 01 00 00 00       	mov    $0x1,%edi
    607d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6081:	4b 8b 8c 3c 58 01 00 00 	mov    0x158(%r12,%r15,1),%rcx
    6089:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    608e:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    6096:	31 c0                	xor    %eax,%eax
    6098:	e8 b3 c3 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    609d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    60a2:	4c 8b 20             	mov    (%rax),%r12
    60a5:	4b 83 bc 3c 58 01 00 00 00 	cmpq   $0x0,0x158(%r12,%r15,1)
    60ae:	0f 8e 47 01 00 00    	jle    61fb <verify+0x24b>
    60b4:	4c 03 75 00          	add    0x0(%rbp),%r14
    60b8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60bd:	ba 01 00 00 00       	mov    $0x1,%edx
    60c2:	4d 89 f5             	mov    %r14,%r13
    60c5:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    60cc:	4d 85 f6             	test   %r14,%r14
    60cf:	0f 8e 21 01 00 00    	jle    61f6 <verify+0x246>
    60d5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    60d8:	48 89 d5             	mov    %rdx,%rbp
    60db:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    60e0:	31 db                	xor    %ebx,%ebx
    60e2:	4d 89 f2             	mov    %r14,%r10
    60e5:	48 c1 e5 05          	shl    $0x5,%rbp
    60e9:	48 83 ed 20          	sub    $0x20,%rbp
    60ed:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    60f1:	49 89 ee             	mov    %rbp,%r14
    60f4:	48 89 dd             	mov    %rbx,%rbp
    60f7:	48 89 d3             	mov    %rdx,%rbx
    60fa:	eb 31                	jmp    612d <verify+0x17d>
    60fc:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6100:	4c 39 c2             	cmp    %r8,%rdx
    6103:	0f 8d 57 01 00 00    	jge    6260 <verify+0x2b0>
    6109:	4c 39 df             	cmp    %r11,%rdi
    610c:	7e 05                	jle    6113 <verify+0x163>
    610e:	49 39 c1             	cmp    %rax,%r9
    6111:	7c 75                	jl     6188 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6113:	4c 39 df             	cmp    %r11,%rdi
    6116:	0f 8d ab 01 00 00    	jge    62c7 <verify+0x317>
    611c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6120:	48 83 c5 01          	add    $0x1,%rbp
    6124:	49 39 ea             	cmp    %rbp,%r10
    6127:	0f 8e a9 00 00 00    	jle    61d6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    612d:	49 8b 97 48 01 00 00 	mov    0x148(%r15),%rdx
    6134:	48 89 e8             	mov    %rbp,%rax
    6137:	48 c1 e0 05          	shl    $0x5,%rax
    613b:	49 03 85 48 01 00 00 	add    0x148(%r13),%rax
    6142:	4c 01 f2             	add    %r14,%rdx
    6145:	48 8b 08             	mov    (%rax),%rcx
    6148:	48 8b 78 10          	mov    0x10(%rax),%rdi
    614c:	48 8b 32             	mov    (%rdx),%rsi
    614f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6153:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6157:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    615b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    615f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6163:	48 39 f1             	cmp    %rsi,%rcx
    6166:	7c 98                	jl     6100 <verify+0x150>
    6168:	0f 8e 42 01 00 00    	jle    62b0 <verify+0x300>
    616e:	4c 39 c2             	cmp    %r8,%rdx
    6171:	0f 8f f9 00 00 00    	jg     6270 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6177:	75 a7                	jne    6120 <verify+0x170>
    6179:	4c 39 df             	cmp    %r11,%rdi
    617c:	7f a2                	jg     6120 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    617e:	49 39 c1             	cmp    %rax,%r9
    6181:	7c 9d                	jl     6120 <verify+0x170>
    6183:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6188:	49 89 c1             	mov    %rax,%r9
    618b:	48 89 f9             	mov    %rdi,%rcx
    618e:	48 89 f2             	mov    %rsi,%rdx
    6191:	bf 01 00 00 00       	mov    $0x1,%edi
    6196:	48 8d 35 13 13 00 00 	lea    0x1313(%rip),%rsi        # 74b0 <_IO_stdin_used+0x4b0>
    619d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    619f:	48 83 c5 01          	add    $0x1,%rbp
    61a3:	e8 a8 c2 ff ff       	call   2450 <__printf_chk@plt>
    61a8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    61ad:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    61b2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    61b5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    61ba:	4d 8b 95 58 01 00 00 	mov    0x158(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    61c1:	4c 8b 20             	mov    (%rax),%r12
    61c4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    61c9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    61cd:	49 39 ea             	cmp    %rbp,%r10
    61d0:	0f 8f 57 ff ff ff    	jg     612d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    61d6:	48 89 da             	mov    %rbx,%rdx
    61d9:	49 3b 9f 58 01 00 00 	cmp    0x158(%r15),%rbx
    61e0:	7d 14                	jge    61f6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    61e2:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    61e9:	48 83 c2 01          	add    $0x1,%rdx
    61ed:	4d 85 f6             	test   %r14,%r14
    61f0:	0f 8f e2 fe ff ff    	jg     60d8 <verify+0x128>
    61f6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    61fb:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6200:	48 83 c3 01          	add    $0x1,%rbx
    6204:	39 58 08             	cmp    %ebx,0x8(%rax)
    6207:	0f 8f 53 fe ff ff    	jg     6060 <verify+0xb0>
    620d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6212:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6217:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    621c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6221:	48 83 c1 01          	add    $0x1,%rcx
    6225:	39 48 08             	cmp    %ecx,0x8(%rax)
    6228:	0f 8f d8 fd ff ff    	jg     6006 <verify+0x56>
    622e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6233:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6238:	48 81 44 24 10 b0 00 00 00 	addq   $0xb0,0x10(%rsp)
    6241:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6246:	41 39 c7             	cmp    %eax,%r15d
    6249:	0f 84 86 00 00 00    	je     62d5 <verify+0x325>
    624f:	41 89 c4             	mov    %eax,%r12d
    6252:	e9 8a fd ff ff       	jmp    5fe1 <verify+0x31>
    6257:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6260:	0f 85 ba fe ff ff    	jne    6120 <verify+0x170>
    6266:	e9 a8 fe ff ff       	jmp    6113 <verify+0x163>
    626b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6270:	49 39 c1             	cmp    %rax,%r9
    6273:	7e 09                	jle    627e <verify+0x2ce>
    6275:	4c 39 df             	cmp    %r11,%rdi
    6278:	0f 8c 0a ff ff ff    	jl     6188 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    627e:	4c 39 df             	cmp    %r11,%rdi
    6281:	0f 8f 99 fe ff ff    	jg     6120 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6287:	49 39 c1             	cmp    %rax,%r9
    628a:	0f 8d f8 fe ff ff    	jge    6188 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6290:	48 39 f1             	cmp    %rsi,%rcx
    6293:	0f 85 87 fe ff ff    	jne    6120 <verify+0x170>
    6299:	4c 39 c2             	cmp    %r8,%rdx
    629c:	0f 85 7e fe ff ff    	jne    6120 <verify+0x170>
    62a2:	4c 39 df             	cmp    %r11,%rdi
    62a5:	0f 84 dd fe ff ff    	je     6188 <verify+0x1d8>
    62ab:	e9 70 fe ff ff       	jmp    6120 <verify+0x170>
    62b0:	4c 39 c2             	cmp    %r8,%rdx
    62b3:	0f 8c 5a fe ff ff    	jl     6113 <verify+0x163>
    62b9:	4c 39 df             	cmp    %r11,%rdi
    62bc:	7e c9                	jle    6287 <verify+0x2d7>
    62be:	4c 39 c2             	cmp    %r8,%rdx
    62c1:	0f 85 59 fe ff ff    	jne    6120 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    62c7:	49 39 c1             	cmp    %rax,%r9
    62ca:	0f 8f 50 fe ff ff    	jg     6120 <verify+0x170>
    62d0:	e9 b3 fe ff ff       	jmp    6188 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    62d5:	48 81 44 24 18 b0 00 00 00 	addq   $0xb0,0x18(%rsp)
    62de:	41 8d 46 01          	lea    0x1(%r14),%eax
    62e2:	45 39 e6             	cmp    %r12d,%r14d
    62e5:	74 08                	je     62ef <verify+0x33f>
    62e7:	41 89 c6             	mov    %eax,%r14d
    62ea:	e9 ea fc ff ff       	jmp    5fd9 <verify+0x29>
}
    62ef:	48 83 c4 58          	add    $0x58,%rsp
    62f3:	31 c0                	xor    %eax,%eax
    62f5:	5b                   	pop    %rbx
    62f6:	5d                   	pop    %rbp
    62f7:	41 5c                	pop    %r12
    62f9:	41 5d                	pop    %r13
    62fb:	41 5e                	pop    %r14
    62fd:	41 5f                	pop    %r15
    62ff:	c3                   	ret
    6300:	31 c0                	xor    %eax,%eax
    6302:	c3                   	ret

Disassembly of section .fini:

0000000000006304 <_fini>:
    6304:	f3 0f 1e fa          	endbr64
    6308:	48 83 ec 08          	sub    $0x8,%rsp
    630c:	48 83 c4 08          	add    $0x8,%rsp
    6310:	c3                   	ret
