
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
    25f6:	48 8d 3d 8b 4f 00 00 	lea    0x4f8b(%rip),%rdi        # 7588 <_IO_stdin_used+0x588>
    25fd:	41 56                	push   %r14
    25ff:	41 55                	push   %r13
    2601:	41 54                	push   %r12
    2603:	55                   	push   %rbp
    2604:	53                   	push   %rbx
    2605:	48 81 ec a8 00 00 00 	sub    $0xa8,%rsp
    260c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2615:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
    261d:	48 8d 05 bc 16 00 00 	lea    0x16bc(%rip),%rax        # 3ce0 <barriered_reset>
    2624:	66 48 0f 6e d8       	movq   %rax,%xmm3
    2629:	0f 16 1d 48 76 00 00 	movhps 0x7648(%rip),%xmm3        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    2630:	0f 29 5c 24 50       	movaps %xmm3,0x50(%rsp)
    2635:	e8 b6 fc ff ff       	call   22f0 <puts@plt>
    263a:	bf 0a 00 00 00       	mov    $0xa,%edi
    263f:	e8 8c fc ff ff       	call   22d0 <putchar@plt>
    2644:	ba 02 00 00 00       	mov    $0x2,%edx
    2649:	48 8d 35 03 4c 00 00 	lea    0x4c03(%rip),%rsi        # 7253 <_IO_stdin_used+0x253>
    2650:	31 c0                	xor    %eax,%eax
    2652:	bf 01 00 00 00       	mov    $0x1,%edi
    2657:	e8 f4 fd ff ff       	call   2450 <__printf_chk@plt>
    265c:	ba 04 00 00 00       	mov    $0x4,%edx
    2661:	48 8d 35 fb 4b 00 00 	lea    0x4bfb(%rip),%rsi        # 7263 <_IO_stdin_used+0x263>
    2668:	31 c0                	xor    %eax,%eax
    266a:	bf 01 00 00 00       	mov    $0x1,%edi
    266f:	e8 dc fd ff ff       	call   2450 <__printf_chk@plt>
    2674:	ba 02 00 00 00       	mov    $0x2,%edx
    2679:	48 8d 35 f8 4b 00 00 	lea    0x4bf8(%rip),%rsi        # 7278 <_IO_stdin_used+0x278>
    2680:	31 c0                	xor    %eax,%eax
    2682:	bf 01 00 00 00       	mov    $0x1,%edi
    2687:	e8 c4 fd ff ff       	call   2450 <__printf_chk@plt>
    268c:	ba 02 00 00 00       	mov    $0x2,%edx
    2691:	48 8d 35 f0 4b 00 00 	lea    0x4bf0(%rip),%rsi        # 7288 <_IO_stdin_used+0x288>
    2698:	31 c0                	xor    %eax,%eax
    269a:	bf 01 00 00 00       	mov    $0x1,%edi
    269f:	e8 ac fd ff ff       	call   2450 <__printf_chk@plt>
    26a4:	48 8d 3d f3 4b 00 00 	lea    0x4bf3(%rip),%rdi        # 729e <_IO_stdin_used+0x29e>
    26ab:	e8 40 fc ff ff       	call   22f0 <puts@plt>
    26b0:	ba 02 00 00 00       	mov    $0x2,%edx
    26b5:	48 8d 35 fe 4b 00 00 	lea    0x4bfe(%rip),%rsi        # 72ba <_IO_stdin_used+0x2ba>
    26bc:	31 c0                	xor    %eax,%eax
    26be:	bf 01 00 00 00       	mov    $0x1,%edi
    26c3:	e8 88 fd ff ff       	call   2450 <__printf_chk@plt>
    26c8:	ba 08 00 00 00       	mov    $0x8,%edx
    26cd:	48 8d 35 00 4c 00 00 	lea    0x4c00(%rip),%rsi        # 72d4 <_IO_stdin_used+0x2d4>
    26d4:	31 c0                	xor    %eax,%eax
    26d6:	bf 01 00 00 00       	mov    $0x1,%edi
    26db:	e8 70 fd ff ff       	call   2450 <__printf_chk@plt>
    26e0:	ba 01 00 00 00       	mov    $0x1,%edx
    26e5:	48 8d 35 fc 4b 00 00 	lea    0x4bfc(%rip),%rsi        # 72e8 <_IO_stdin_used+0x2e8>
    26ec:	31 c0                	xor    %eax,%eax
    26ee:	bf 01 00 00 00       	mov    $0x1,%edi
    26f3:	e8 58 fd ff ff       	call   2450 <__printf_chk@plt>
    26f8:	ba 01 00 00 00       	mov    $0x1,%edx
    26fd:	48 8d 35 f5 4b 00 00 	lea    0x4bf5(%rip),%rsi        # 72f9 <_IO_stdin_used+0x2f9>
    2704:	31 c0                	xor    %eax,%eax
    2706:	bf 01 00 00 00       	mov    $0x1,%edi
    270b:	e8 40 fd ff ff       	call   2450 <__printf_chk@plt>
    2710:	ba 02 00 00 00       	mov    $0x2,%edx
    2715:	48 8d 35 f5 4b 00 00 	lea    0x4bf5(%rip),%rsi        # 7311 <_IO_stdin_used+0x311>
    271c:	31 c0                	xor    %eax,%eax
    271e:	bf 01 00 00 00       	mov    $0x1,%edi
    2723:	e8 28 fd ff ff       	call   2450 <__printf_chk@plt>
    2728:	ba 01 00 00 00       	mov    $0x1,%edx
    272d:	48 8d 35 bc 4e 00 00 	lea    0x4ebc(%rip),%rsi        # 75f0 <_IO_stdin_used+0x5f0>
    2734:	31 c0                	xor    %eax,%eax
    2736:	bf 01 00 00 00       	mov    $0x1,%edi
    273b:	e8 10 fd ff ff       	call   2450 <__printf_chk@plt>
    2740:	ba 01 00 00 00       	mov    $0x1,%edx
    2745:	48 8d 35 d4 4e 00 00 	lea    0x4ed4(%rip),%rsi        # 7620 <_IO_stdin_used+0x620>
    274c:	31 c0                	xor    %eax,%eax
    274e:	bf 01 00 00 00       	mov    $0x1,%edi
    2753:	e8 f8 fc ff ff       	call   2450 <__printf_chk@plt>
    2758:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    275d:	48 8d 35 c9 4b 00 00 	lea    0x4bc9(%rip),%rsi        # 732d <_IO_stdin_used+0x32d>
    2764:	31 c0                	xor    %eax,%eax
    2766:	bf 01 00 00 00       	mov    $0x1,%edi
    276b:	e8 e0 fc ff ff       	call   2450 <__printf_chk@plt>
    2770:	ba 05 00 00 00       	mov    $0x5,%edx
    2775:	48 8d 35 cb 4b 00 00 	lea    0x4bcb(%rip),%rsi        # 7347 <_IO_stdin_used+0x347>
    277c:	31 c0                	xor    %eax,%eax
    277e:	bf 01 00 00 00       	mov    $0x1,%edi
    2783:	e8 c8 fc ff ff       	call   2450 <__printf_chk@plt>
    2788:	48 8d 3d 60 49 00 00 	lea    0x4960(%rip),%rdi        # 70ef <_IO_stdin_used+0xef>
    278f:	e8 5c fb ff ff       	call   22f0 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2794:	be 18 00 00 00       	mov    $0x18,%esi
    2799:	bf 02 00 00 00       	mov    $0x2,%edi
    279e:	e8 fd fb ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27a3:	be c0 00 00 00       	mov    $0xc0,%esi
    27a8:	bf 08 00 00 00       	mov    $0x8,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    27ad:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27b2:	e8 e9 fb ff ff       	call   23a0 <calloc@plt>
    27b7:	ba 04 00 00 00       	mov    $0x4,%edx
    27bc:	bf 01 00 00 00       	mov    $0x1,%edi
    27c1:	48 8d 35 93 4b 00 00 	lea    0x4b93(%rip),%rsi        # 735b <_IO_stdin_used+0x35b>
    27c8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    27cd:	31 c0                	xor    %eax,%eax
    27cf:	e8 7c fc ff ff       	call   2450 <__printf_chk@plt>
    27d4:	ba 08 00 00 00       	mov    $0x8,%edx
    27d9:	48 8d 35 91 4b 00 00 	lea    0x4b91(%rip),%rsi        # 7371 <_IO_stdin_used+0x371>
    27e0:	31 c0                	xor    %eax,%eax
    27e2:	bf 01 00 00 00       	mov    $0x1,%edi
    27e7:	e8 64 fc ff ff       	call   2450 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    27ec:	be 10 00 00 00       	mov    $0x10,%esi
    27f1:	bf 08 00 00 00       	mov    $0x8,%edi
    27f6:	e8 a5 fb ff ff       	call   23a0 <calloc@plt>
    27fb:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2800:	48 89 c3             	mov    %rax,%rbx
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    2803:	48 8d a8 80 00 00 00 	lea    0x80(%rax),%rbp
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    280a:	49 89 c5             	mov    %rax,%r13
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    280d:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    2812:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    281a:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    281f:	49 83 c5 10          	add    $0x10,%r13
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2823:	e8 78 fb ff ff       	call   23a0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2828:	be 20 00 00 00       	mov    $0x20,%esi
    282d:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2832:	49 89 45 f8          	mov    %rax,-0x8(%r13)
    2836:	49 89 c4             	mov    %rax,%r12
      buffers[x].buffer[y].available = 0;
    2839:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2843:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    284d:	e8 4e fb ff ff       	call   23a0 <calloc@plt>
    2852:	49 89 84 24 88 00 00 00 	mov    %rax,0x88(%r12)
  for (int x = 0 ; x < buffers_required; x++) {
    285a:	49 39 ed             	cmp    %rbp,%r13
    285d:	75 ae                	jne    280d <main+0x21d>
    285f:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    2864:	b8 03 00 00 00       	mov    $0x3,%eax
    2869:	45 31 e4             	xor    %r12d,%r12d
    286c:	49 89 de             	mov    %rbx,%r14
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
    286f:	c7 44 24 40 00 00 00 00 	movl   $0x0,0x40(%rsp)
  int curcpu = 0;
    2877:	c7 44 24 30 00 00 00 00 	movl   $0x0,0x30(%rsp)
    287f:	48 63 54 24 40       	movslq 0x40(%rsp),%rdx
    2884:	4d 89 e1             	mov    %r12,%r9
    2887:	89 44 24 48          	mov    %eax,0x48(%rsp)
    288b:	43 8d 2c 24          	lea    (%r12,%r12,1),%ebp
    288f:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    2894:	49 f7 d9             	neg    %r9
    2897:	48 89 7c 24 68       	mov    %rdi,0x68(%rsp)
    289c:	48 c1 e2 04          	shl    $0x4,%rdx
    28a0:	4c 89 b4 24 80 00 00 00 	mov    %r14,0x80(%rsp)
    28a8:	41 81 e1 80 01 00 00 	and    $0x180,%r9d
    28af:	49 8d 34 16          	lea    (%r14,%rdx,1),%rsi
    28b3:	44 89 64 24 78       	mov    %r12d,0x78(%rsp)
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    28b8:	49 01 d9             	add    %rbx,%r9
    28bb:	8d 58 fe             	lea    -0x2(%rax),%ebx
    28be:	4c 89 a4 24 88 00 00 00 	mov    %r12,0x88(%rsp)
    28c6:	49 89 f4             	mov    %rsi,%r12
    28c9:	8b 54 24 78          	mov    0x78(%rsp),%edx
    28cd:	89 e9                	mov    %ebp,%ecx
    28cf:	48 8d 35 72 4d 00 00 	lea    0x4d72(%rip),%rsi        # 7648 <_IO_stdin_used+0x648>
    28d6:	31 c0                	xor    %eax,%eax
    28d8:	bf 01 00 00 00       	mov    $0x1,%edi
    28dd:	4c 89 0c 24          	mov    %r9,(%rsp)
    28e1:	e8 6a fb ff ff       	call   2450 <__printf_chk@plt>
      int x = (k * threads_per_group) + d;
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    28e6:	be 08 00 00 00       	mov    $0x8,%esi
    28eb:	bf 02 00 00 00       	mov    $0x2,%edi
    28f0:	e8 ab fa ff ff       	call   23a0 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    28f5:	be 80 00 00 00       	mov    $0x80,%esi
    28fa:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    28ff:	49 89 c5             	mov    %rax,%r13
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2902:	e8 99 fa ff ff       	call   23a0 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2907:	40 f6 c5 01          	test   $0x1,%bpl
    290b:	4c 8b 0c 24          	mov    (%rsp),%r9
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    290f:	49 89 c6             	mov    %rax,%r14
      if (x % 2 == 1) {
    2912:	0f 84 9a 06 00 00    	je     2fb2 <main+0x9c2>
        other = abs(x - 1) % total_threads;
    2918:	8d 45 ff             	lea    -0x1(%rbp),%eax
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    291b:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
        my_thread_data[1] = &thread_data[x]; 
    2920:	4c 89 ca             	mov    %r9,%rdx
    2923:	41 b8 01 00 00 00    	mov    $0x1,%r8d
        other = abs(x - 1) % total_threads;
    2929:	49 89 c7             	mov    %rax,%r15
        my_thread_data[0] = &thread_data[other]; 
    292c:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    2930:	48 c1 e0 06          	shl    $0x6,%rax
    2934:	48 01 f8             	add    %rdi,%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2937:	49 8d 7d 08          	lea    0x8(%r13),%rdi
    293b:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    2940:	48 8b 7c 24 68       	mov    0x68(%rsp),%rdi
        thread_data[x].thread_index = 1;
    2945:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2949:	44 89 f9             	mov    %r15d,%ecx
    294c:	48 8d 35 25 4d 00 00 	lea    0x4d25(%rip),%rsi        # 7678 <_IO_stdin_used+0x678>
    2953:	49 89 55 08          	mov    %rdx,0x8(%r13)
    2957:	89 ea                	mov    %ebp,%edx
        thread_data[x].protected_state = &protected_state[k];
    2959:	49 89 79 48          	mov    %rdi,0x48(%r9)
    295d:	bf 01 00 00 00       	mov    $0x1,%edi
    2962:	49 89 45 00          	mov    %rax,0x0(%r13)
    2966:	31 c0                	xor    %eax,%eax
    2968:	4c 89 0c 24          	mov    %r9,(%rsp)
    296c:	e8 df fa ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].other = other;
    2971:	4c 8b 0c 24          	mov    (%rsp),%r9
    2975:	8b 4c 24 30          	mov    0x30(%rsp),%ecx
    2979:	31 c0                	xor    %eax,%eax
    297b:	89 ea                	mov    %ebp,%edx
    297d:	48 8d 35 24 4d 00 00 	lea    0x4d24(%rip),%rsi        # 76a8 <_IO_stdin_used+0x6a8>
    2984:	bf 01 00 00 00       	mov    $0x1,%edi
    2989:	45 89 b9 b8 00 00 00 	mov    %r15d,0xb8(%r9)
    2990:	e8 bb fa ff ff       	call   2450 <__printf_chk@plt>
        if (x < thread_count) {
    2995:	83 fd 01             	cmp    $0x1,%ebp
    2998:	4c 8b 0c 24          	mov    (%rsp),%r9
    299c:	0f 8f 61 07 00 00    	jg     3103 <main+0xb13>
          CPU_SET(curcpu, sendercpu);
    29a2:	48 63 44 24 30       	movslq 0x30(%rsp),%rax
    29a7:	48 89 c7             	mov    %rax,%rdi
    29aa:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    29b0:	77 12                	ja     29c4 <main+0x3d4>
    29b2:	48 c1 e8 06          	shr    $0x6,%rax
    29b6:	ba 01 00 00 00       	mov    $0x1,%edx
    29bb:	89 f9                	mov    %edi,%ecx
    29bd:	48 d3 e2             	shl    %cl,%rdx
    29c0:	49 09 14 c6          	or     %rdx,(%r14,%rax,8)
          curcpu += 2;
    29c4:	83 44 24 30 02       	addl   $0x2,0x30(%rsp)
      thread_data[x].all_threads = thread_data;
    29c9:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    29ce:	4d 89 69 18          	mov    %r13,0x18(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    29d2:	be 10 00 00 00       	mov    $0x10,%esi
    29d7:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].cpu_set = sendercpu;
    29dc:	4d 89 b1 b0 00 00 00 	mov    %r14,0xb0(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    29e3:	45 31 ed             	xor    %r13d,%r13d
      thread_data[x].all_threads = thread_data;
    29e6:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].thread_count = 2;
    29ea:	48 8b 05 af 51 00 00 	mov    0x51af(%rip),%rax        # 7ba0 <_IO_stdin_used+0xba0>
      thread_data[x].kind = KERNEL_THREAD;
    29f1:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].real_thread_index = x;
    29f8:	41 89 69 08          	mov    %ebp,0x8(%r9)
      thread_data[x].thread_count = 2;
    29fc:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].task_count = total_barrier_count;
    2a00:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
    2a08:	4c 89 0c 24          	mov    %r9,(%rsp)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a0c:	e8 8f f9 ff ff       	call   23a0 <calloc@plt>
    2a11:	4c 8b 0c 24          	mov    (%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a15:	be 10 00 00 00       	mov    $0x10,%esi
    2a1a:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a1f:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a23:	e8 78 f9 ff ff       	call   23a0 <calloc@plt>
    2a28:	4c 8b 0c 24          	mov    (%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a2c:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2a31:	66 0f 6f 3d 37 51 00 00 	movdqa 0x5137(%rip),%xmm7        # 7b70 <_IO_stdin_used+0xb70>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a39:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a3e:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2a42:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a4a:	e8 51 f9 ff ff       	call   23a0 <calloc@plt>
    2a4f:	4c 8b 0c 24          	mov    (%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a53:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_timestamp_count = 0;
    2a58:	66 0f 6f 1d 10 51 00 00 	movdqa 0x5110(%rip),%xmm3        # 7b70 <_IO_stdin_used+0xb70>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a60:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a65:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2a6c:	41 0f 11 99 98 00 00 00 	movups %xmm3,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a74:	e8 27 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks = barriers;
    2a79:	4c 8b 0c 24          	mov    (%rsp),%r9
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a7d:	4c 89 64 24 70       	mov    %r12,0x70(%rsp)
    2a82:	49 89 c4             	mov    %rax,%r12
        thread_data[x].tasks = barriers;
    2a85:	49 89 41 38          	mov    %rax,0x38(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a89:	4d 89 ce             	mov    %r9,%r14
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a8c:	49 63 c5             	movslq %r13d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2a8f:	be 28 00 00 00       	mov    $0x28,%esi
    2a94:	bf 04 00 00 00       	mov    $0x4,%edi
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a99:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2a9e:	48 c1 e0 09          	shl    $0x9,%rax
    2aa2:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    2aa6:	48 89 04 24          	mov    %rax,(%rsp)
    2aaa:	48 8d 05 ef 11 00 00 	lea    0x11ef(%rip),%rax        # 3ca0 <do_protected_write>
    2ab1:	49 89 87 20 01 00 00 	mov    %rax,0x120(%r15)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2ab8:	e8 e3 f8 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2abd:	49 89 87 70 01 00 00 	mov    %rax,0x170(%r15)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2ac4:	49 89 c4             	mov    %rax,%r12
            if ( b == x || b == x + 1) {
    2ac7:	85 ed                	test   %ebp,%ebp
    2ac9:	0f 84 a2 03 00 00    	je     2e71 <main+0x881>
    2acf:	83 fd 01             	cmp    $0x1,%ebp
    2ad2:	0f 84 00 05 00 00    	je     2fd8 <main+0x9e8>
    2ad8:	83 fd 02             	cmp    $0x2,%ebp
    2adb:	0f 84 2e 06 00 00    	je     310f <main+0xb1f>
    2ae1:	ba 03 00 00 00       	mov    $0x3,%edx
    2ae6:	48 8d 35 9e 48 00 00 	lea    0x489e(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
    2aed:	bf 01 00 00 00       	mov    $0x1,%edi
    2af2:	31 c0                	xor    %eax,%eax
    2af4:	e8 57 f9 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2af9:	be 08 00 00 00       	mov    $0x8,%esi
    2afe:	bf 01 00 00 00       	mov    $0x1,%edi
    2b03:	e8 98 f8 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b08:	be 08 00 00 00       	mov    $0x8,%esi
    2b0d:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b12:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b17:	e8 84 f8 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2b1c:	be 80 01 00 00       	mov    $0x180,%esi
    2b21:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b26:	49 89 c7             	mov    %rax,%r15
              struct Data *data = calloc(2, sizeof(struct Data));
    2b29:	e8 72 f8 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    2b2e:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
              data[0].messages_count = 0;
    2b33:	66 0f 6f 25 45 50 00 00 	movdqa 0x5045(%rip),%xmm4        # 7b80 <_IO_stdin_used+0xb80>
              mailboxes[b].kind = MAILBOX_FRIEND;
    2b3b:	41 c7 84 24 98 00 00 00 01 00 00 00 	movl   $0x1,0x98(%r12)
              mailboxes[b].higher = &data[1];
    2b47:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    2b4e:	49 89 44 24 78       	mov    %rax,0x78(%r12)
              mailboxes[b].higher = &data[1];
    2b53:	49 89 b4 24 80 00 00 00 	mov    %rsi,0x80(%r12)
              data[0].messages = messages;
    2b5b:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    2b5e:	4c 89 b8 80 01 00 00 	mov    %r15,0x180(%rax)
              data[0].messages_count = 0;
    2b65:	0f 29 a0 80 00 00 00 	movaps %xmm4,0x80(%rax)
              data[1].messages_count = 0;
    2b6c:	0f 29 a0 00 02 00 00 	movaps %xmm4,0x200(%rax)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2b73:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    2b78:	45 31 ff             	xor    %r15d,%r15d
    2b7b:	41 89 de             	mov    %ebx,%r14d
    2b7e:	44 89 6c 24 28       	mov    %r13d,0x28(%rsp)
    2b83:	41 89 ed             	mov    %ebp,%r13d
            if (b == x || b == x + 1) { continue; }
    2b86:	45 39 ef             	cmp    %r13d,%r15d
    2b89:	0f 84 9f 00 00 00    	je     2c2e <main+0x63e>
    2b8f:	45 39 f7             	cmp    %r14d,%r15d
    2b92:	0f 84 96 00 00 00    	je     2c2e <main+0x63e>
    2b98:	44 89 fa             	mov    %r15d,%edx
    2b9b:	48 8d 35 05 48 00 00 	lea    0x4805(%rip),%rsi        # 73a7 <_IO_stdin_used+0x3a7>
    2ba2:	bf 01 00 00 00       	mov    $0x1,%edi
    2ba7:	31 c0                	xor    %eax,%eax
    2ba9:	e8 a2 f8 ff ff       	call   2450 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2bae:	be 08 00 00 00       	mov    $0x8,%esi
    2bb3:	bf 01 00 00 00       	mov    $0x1,%edi
    2bb8:	e8 e3 f7 ff ff       	call   23a0 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2bbd:	be 08 00 00 00       	mov    $0x8,%esi
    2bc2:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2bc7:	48 89 c5             	mov    %rax,%rbp
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2bca:	e8 d1 f7 ff ff       	call   23a0 <calloc@plt>
            struct Data *data = calloc(2, sizeof(struct Data));
    2bcf:	be 80 01 00 00       	mov    $0x180,%esi
    2bd4:	bf 02 00 00 00       	mov    $0x2,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2bd9:	48 89 c3             	mov    %rax,%rbx
            struct Data *data = calloc(2, sizeof(struct Data));
    2bdc:	e8 bf f7 ff ff       	call   23a0 <calloc@plt>
            data[0].messages_count = 0;
    2be1:	66 0f 6f 05 97 4f 00 00 	movdqa 0x4f97(%rip),%xmm0        # 7b80 <_IO_stdin_used+0xb80>
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2be9:	41 c7 44 24 20 02 00 00 00 	movl   $0x2,0x20(%r12)
            mailboxes[b].higher = &data[1];
    2bf2:	48 8d 90 80 01 00 00 	lea    0x180(%rax),%rdx
            mailboxes[b].lower = &data[0];
    2bf9:	49 89 04 24          	mov    %rax,(%r12)
            mailboxes[b].higher = &data[1];
    2bfd:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
            data[0].available = 0;
    2c02:	c7 80 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rax)
            data[0].messages = messages;
    2c0c:	48 89 28             	mov    %rbp,(%rax)
            data[1].messages = messages2;
    2c0f:	48 89 98 80 01 00 00 	mov    %rbx,0x180(%rax)
            data[1].available = 0;
    2c16:	c7 80 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rax)
            data[0].messages_count = 0;
    2c20:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
            data[1].messages_count = 0;
    2c27:	0f 29 80 00 02 00 00 	movaps %xmm0,0x200(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c2e:	41 83 c7 01          	add    $0x1,%r15d
    2c32:	49 83 c4 28          	add    $0x28,%r12
    2c36:	41 83 ff 04          	cmp    $0x4,%r15d
    2c3a:	0f 85 46 ff ff ff    	jne    2b86 <main+0x596>
          char *message = malloc(sizeof(char) * 256);
    2c40:	be 01 00 00 00       	mov    $0x1,%esi
    2c45:	bf 00 01 00 00       	mov    $0x100,%edi
    2c4a:	44 89 ed             	mov    %r13d,%ebp
    2c4d:	44 89 f3             	mov    %r14d,%ebx
    2c50:	44 8b 6c 24 28       	mov    0x28(%rsp),%r13d
    2c55:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    2c5a:	e8 41 f7 ff ff       	call   23a0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2c5f:	bf 18 00 00 00       	mov    $0x18,%edi
          char *message = malloc(sizeof(char) * 256);
    2c64:	49 89 c4             	mov    %rax,%r12
          struct Message *messaged = malloc(sizeof(struct Message));
    2c67:	e8 a4 f7 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2c6c:	ba 00 01 00 00       	mov    $0x100,%edx
    2c71:	4c 89 e7             	mov    %r12,%rdi
    2c74:	45 89 e9             	mov    %r13d,%r9d
    2c77:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2c7c:	41 89 e8             	mov    %ebp,%r8d
    2c7f:	be 01 00 00 00       	mov    $0x1,%esi
    2c84:	31 c0                	xor    %eax,%eax
    2c86:	48 8d 0d 3b 4a 00 00 	lea    0x4a3b(%rip),%rcx        # 76c8 <_IO_stdin_used+0x6c8>
    2c8d:	e8 8e f8 ff ff       	call   2520 <__sprintf_chk@plt>
          messaged->message = message;
    2c92:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
          messaged->task_index = y;
    2c97:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2c9c:	be 20 00 00 00       	mov    $0x20,%esi
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2ca1:	4c 8b 3c 24          	mov    (%rsp),%r15
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2ca5:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->task_index = y;
    2caa:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2cae:	49 63 46 08          	movslq 0x8(%r14),%rax
          messaged->message = message;
    2cb2:	4d 89 22             	mov    %r12,(%r10)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2cb5:	4d 8b 66 38          	mov    0x38(%r14),%r12
          messaged->thread_index = thread_data[x].real_thread_index;
    2cb9:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2cbd:	41 8d 45 01          	lea    0x1(%r13),%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2cc1:	4d 01 e7             	add    %r12,%r15
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2cc4:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2cc7:	41 c7 07 41 00 00 00 	movl   $0x41,(%r15)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2cce:	41 89 87 90 01 00 00 	mov    %eax,0x190(%r15)
          thread_data[x].tasks[y].message = messaged;
    2cd5:	4d 89 97 88 01 00 00 	mov    %r10,0x188(%r15)
          thread_data[x].tasks[y].sending = 1;
    2cdc:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
          thread_data[x].tasks[y].snapshot_count = 99;
    2ce7:	49 c7 87 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%r15)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2cf2:	e8 a9 f6 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    2cf7:	49 c7 87 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%r15)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2d02:	49 89 87 50 01 00 00 	mov    %rax,0x150(%r15)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2d09:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    2d0e:	48 8b 00             	mov    (%rax),%rax
    2d11:	8b 50 04             	mov    0x4(%rax),%edx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2d14:	49 89 87 28 01 00 00 	mov    %rax,0x128(%r15)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2d1b:	41 89 97 30 01 00 00 	mov    %edx,0x130(%r15)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2d22:	4c 39 f0             	cmp    %r14,%rax
    2d25:	0f 85 6b 0e 00 00    	jne    3b96 <main+0x15a6>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2d2b:	66 0f 6f 15 5d 4e 00 00 	movdqa 0x4e5d(%rip),%xmm2        # 7b90 <_IO_stdin_used+0xb90>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2d33:	45 89 6f 04          	mov    %r13d,0x4(%r15)
          thread_data[x].tasks[y].available = 1;
    2d37:	48 8b 05 6a 4e 00 00 	mov    0x4e6a(%rip),%rax        # 7ba8 <_IO_stdin_used+0xba8>
          thread_data[x].tasks[y].arrived = 0;
    2d3e:	41 c7 87 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r15)
          thread_data[x].tasks[y].worker_count = thread_count;
    2d49:	41 c7 87 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%r15)
          thread_data[x].tasks[y].available = 1;
    2d54:	49 89 87 44 01 00 00 	mov    %rax,0x144(%r15)
          thread_data[x].tasks[y].thread_count = 2;
    2d5b:	41 0f 11 97 34 01 00 00 	movups %xmm2,0x134(%r15)
          if (y == barrier_count - 1) {
    2d63:	41 83 fd 01          	cmp    $0x1,%r13d
    2d67:	0f 84 36 02 00 00    	je     2fa3 <main+0x9b3>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2d6d:	45 85 ed             	test   %r13d,%r13d
    2d70:	0f 84 14 02 00 00    	je     2f8a <main+0x99a>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    2d76:	4d 89 f1             	mov    %r14,%r9
    2d79:	48 8d 05 a0 32 00 00 	lea    0x32a0(%rip),%rax        # 6020 <barriered_work>
    2d80:	4d 89 e6             	mov    %r12,%r14
    for (int d = 0 ; d < threads_per_group ; d++) {
    2d83:	83 c5 01             	add    $0x1,%ebp
               thread_data[x].tasks[y].run = barriered_work; 
    2d86:	49 89 87 18 01 00 00 	mov    %rax,0x118(%r15)
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2d8d:	be 08 00 00 00       	mov    $0x8,%esi
    2d92:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    2d97:	83 c3 01             	add    $0x1,%ebx
        thread_data[x].buffers_count = buffers_per_thread;
    2d9a:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
               thread_data[x].tasks[y].run = barriered_work; 
    2da5:	4c 8b 64 24 70       	mov    0x70(%rsp),%r12
        thread_data[x].buffers_count = buffers_per_thread;
    2daa:	4c 89 0c 24          	mov    %r9,(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2dae:	e8 ed f5 ff ff       	call   23a0 <calloc@plt>
    2db3:	4c 8b 0c 24          	mov    (%rsp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2db7:	66 0f 6f 74 24 50    	movdqa 0x50(%rsp),%xmm6
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2dbd:	4c 89 20             	mov    %r12,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2dc0:	49 83 c4 10          	add    $0x10,%r12
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2dc4:	49 89 41 50          	mov    %rax,0x50(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2dc8:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    2dcd:	49 81 c1 c0 00 00 00 	add    $0xc0,%r9
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2dd4:	83 44 24 40 01       	addl   $0x1,0x40(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2dd9:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2ddc:	41 0f 11 b6 18 05 00 00 	movups %xmm6,0x518(%r14)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    2de4:	41 c7 86 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r14)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2def:	49 89 86 28 05 00 00 	mov    %rax,0x528(%r14)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2df6:	41 c7 86 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r14)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    2e01:	41 c7 86 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r14)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2e0c:	41 8b 81 44 ff ff ff 	mov    -0xbc(%r9),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2e13:	41 c7 86 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r14)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2e1e:	41 89 86 30 05 00 00 	mov    %eax,0x530(%r14)
        thread_data[x].tasks[barrier_count].available = 1; 
    2e25:	48 8b 05 7c 4d 00 00 	mov    0x4d7c(%rip),%rax        # 7ba8 <_IO_stdin_used+0xba8>
    2e2c:	49 89 86 44 05 00 00 	mov    %rax,0x544(%r14)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e33:	39 5c 24 48          	cmp    %ebx,0x48(%rsp)
    2e37:	0f 85 8c fa ff ff    	jne    28c9 <main+0x2d9>
    2e3d:	8b 44 24 48          	mov    0x48(%rsp),%eax
    2e41:	48 8b 7c 24 68       	mov    0x68(%rsp),%rdi
    2e46:	4c 8b a4 24 88 00 00 00 	mov    0x88(%rsp),%r12
  for (int k = 0 ; k < group_count ; k++) {
    2e4e:	4c 8b b4 24 80 00 00 00 	mov    0x80(%rsp),%r14
    2e56:	83 c0 02             	add    $0x2,%eax
    2e59:	48 83 c7 18          	add    $0x18,%rdi
    2e5d:	4d 85 e4             	test   %r12,%r12
    2e60:	0f 85 41 03 00 00    	jne    31a7 <main+0xbb7>
    2e66:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    2e6c:	e9 0e fa ff ff       	jmp    287f <main+0x28f>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2e71:	31 d2                	xor    %edx,%edx
    2e73:	48 8d 35 11 45 00 00 	lea    0x4511(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
    2e7a:	bf 01 00 00 00       	mov    $0x1,%edi
    2e7f:	31 c0                	xor    %eax,%eax
    2e81:	e8 ca f5 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e86:	be 08 00 00 00       	mov    $0x8,%esi
    2e8b:	bf 01 00 00 00       	mov    $0x1,%edi
    2e90:	e8 0b f5 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e95:	be 08 00 00 00       	mov    $0x8,%esi
    2e9a:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e9f:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ea4:	e8 f7 f4 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2ea9:	be 80 01 00 00       	mov    $0x180,%esi
    2eae:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2eb3:	49 89 c7             	mov    %rax,%r15
              struct Data *data = calloc(2, sizeof(struct Data));
    2eb6:	e8 e5 f4 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    2ebb:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    2ec0:	ba 01 00 00 00       	mov    $0x1,%edx
              data[0].messages_count = 0;
    2ec5:	66 0f 6f 25 b3 4c 00 00 	movdqa 0x4cb3(%rip),%xmm4        # 7b80 <_IO_stdin_used+0xb80>
              mailboxes[b].higher = &data[1];
    2ecd:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              data[1].messages = messages2;
    2ed4:	4c 89 b8 80 01 00 00 	mov    %r15,0x180(%rax)
    2edb:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages = messages;
    2ee0:	48 89 08             	mov    %rcx,(%rax)
              mailboxes[b].lower = &data[0];
    2ee3:	49 89 04 24          	mov    %rax,(%r12)
              mailboxes[b].higher = &data[1];
    2ee7:	49 89 74 24 08       	mov    %rsi,0x8(%r12)
    2eec:	48 8d 35 98 44 00 00 	lea    0x4498(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
              mailboxes[b].kind = MAILBOX_FRIEND;
    2ef3:	41 c7 44 24 20 01 00 00 00 	movl   $0x1,0x20(%r12)
              data[0].messages_count = 0;
    2efc:	0f 29 a0 80 00 00 00 	movaps %xmm4,0x80(%rax)
              data[1].messages_count = 0;
    2f03:	0f 29 a0 00 02 00 00 	movaps %xmm4,0x200(%rax)
    2f0a:	31 c0                	xor    %eax,%eax
    2f0c:	e8 3f f5 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f11:	be 08 00 00 00       	mov    $0x8,%esi
    2f16:	bf 01 00 00 00       	mov    $0x1,%edi
    2f1b:	e8 80 f4 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f20:	be 08 00 00 00       	mov    $0x8,%esi
    2f25:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f2a:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f2f:	e8 6c f4 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2f34:	be 80 01 00 00       	mov    $0x180,%esi
    2f39:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f3e:	49 89 c7             	mov    %rax,%r15
              struct Data *data = calloc(2, sizeof(struct Data));
    2f41:	e8 5a f4 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    2f46:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
              data[0].messages_count = 0;
    2f4b:	66 0f 6f 35 2d 4c 00 00 	movdqa 0x4c2d(%rip),%xmm6        # 7b80 <_IO_stdin_used+0xb80>
              mailboxes[b].kind = MAILBOX_FRIEND;
    2f53:	41 c7 44 24 48 01 00 00 00 	movl   $0x1,0x48(%r12)
              mailboxes[b].higher = &data[1];
    2f5c:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    2f63:	49 89 44 24 28       	mov    %rax,0x28(%r12)
              mailboxes[b].higher = &data[1];
    2f68:	49 89 74 24 30       	mov    %rsi,0x30(%r12)
              data[0].messages = messages;
    2f6d:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    2f70:	4c 89 b8 80 01 00 00 	mov    %r15,0x180(%rax)
              data[0].messages_count = 0;
    2f77:	0f 29 b0 80 00 00 00 	movaps %xmm6,0x80(%rax)
              data[1].messages_count = 0;
    2f7e:	0f 29 b0 00 02 00 00 	movaps %xmm6,0x200(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2f85:	e9 e9 fb ff ff       	jmp    2b73 <main+0x583>
    2f8a:	48 8d 05 5f 33 00 00 	lea    0x335f(%rip),%rax        # 62f0 <barriered_work_ingest_andwork>
    2f91:	41 bd 01 00 00 00    	mov    $0x1,%r13d
            thread_data[x].tasks[y].run = barriered_work; 
    2f97:	49 89 87 18 01 00 00 	mov    %rax,0x118(%r15)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2f9e:	e9 e9 fa ff ff       	jmp    2a8c <main+0x49c>
    2fa3:	48 8d 05 76 30 00 00 	lea    0x3076(%rip),%rax        # 6020 <barriered_work>
    2faa:	41 bd 02 00 00 00    	mov    $0x2,%r13d
    2fb0:	eb e5                	jmp    2f97 <main+0x9a7>
        my_thread_data[1] = &thread_data[other]; 
    2fb2:	48 63 c3             	movslq %ebx,%rax
    2fb5:	4c 89 6c 24 20       	mov    %r13,0x20(%rsp)
        other = (x + 1) % total_threads;
    2fba:	41 89 df             	mov    %ebx,%r15d
        my_thread_data[1] = &thread_data[other]; 
    2fbd:	45 31 c0             	xor    %r8d,%r8d
    2fc0:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
    2fc4:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    2fc9:	48 c1 e2 06          	shl    $0x6,%rdx
    2fcd:	48 01 c2             	add    %rax,%rdx
        my_thread_data[0] = &thread_data[x]; 
    2fd0:	4c 89 c8             	mov    %r9,%rax
    2fd3:	e9 68 f9 ff ff       	jmp    2940 <main+0x350>
    2fd8:	ba 01 00 00 00       	mov    $0x1,%edx
    2fdd:	48 8d 35 a7 43 00 00 	lea    0x43a7(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
    2fe4:	bf 01 00 00 00       	mov    $0x1,%edi
    2fe9:	31 c0                	xor    %eax,%eax
    2feb:	e8 60 f4 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ff0:	be 08 00 00 00       	mov    $0x8,%esi
    2ff5:	bf 01 00 00 00       	mov    $0x1,%edi
    2ffa:	e8 a1 f3 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2fff:	be 08 00 00 00       	mov    $0x8,%esi
    3004:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3009:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    300e:	e8 8d f3 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    3013:	be 80 01 00 00       	mov    $0x180,%esi
    3018:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    301d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    3022:	e8 79 f3 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    3027:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
              data[1].messages = messages2;
    302c:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    3031:	41 c7 44 24 48 01 00 00 00 	movl   $0x1,0x48(%r12)
              mailboxes[b].higher = &data[1];
    303a:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    3041:	49 89 44 24 28       	mov    %rax,0x28(%r12)
    3046:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages_count = 0;
    304b:	66 0f 6f 25 2d 4b 00 00 	movdqa 0x4b2d(%rip),%xmm4        # 7b80 <_IO_stdin_used+0xb80>
              data[0].messages = messages;
    3053:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    3056:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
    305d:	ba 02 00 00 00       	mov    $0x2,%edx
              mailboxes[b].higher = &data[1];
    3062:	49 89 74 24 30       	mov    %rsi,0x30(%r12)
    3067:	48 8d 35 1d 43 00 00 	lea    0x431d(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
              data[0].messages_count = 0;
    306e:	0f 29 a0 80 00 00 00 	movaps %xmm4,0x80(%rax)
              data[1].messages_count = 0;
    3075:	0f 29 a0 00 02 00 00 	movaps %xmm4,0x200(%rax)
    307c:	31 c0                	xor    %eax,%eax
    307e:	e8 cd f3 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3083:	be 08 00 00 00       	mov    $0x8,%esi
    3088:	bf 01 00 00 00       	mov    $0x1,%edi
    308d:	e8 0e f3 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3092:	be 08 00 00 00       	mov    $0x8,%esi
    3097:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    309c:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    30a1:	e8 fa f2 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    30a6:	be 80 01 00 00       	mov    $0x180,%esi
    30ab:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    30b0:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    30b5:	e8 e6 f2 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    30ba:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
              data[1].messages = messages2;
    30bf:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    30c4:	41 c7 44 24 70 01 00 00 00 	movl   $0x1,0x70(%r12)
              data[0].messages_count = 0;
    30cd:	66 0f 6f 35 ab 4a 00 00 	movdqa 0x4aab(%rip),%xmm6        # 7b80 <_IO_stdin_used+0xb80>
              mailboxes[b].higher = &data[1];
    30d5:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    30dc:	49 89 44 24 50       	mov    %rax,0x50(%r12)
              mailboxes[b].higher = &data[1];
    30e1:	49 89 74 24 58       	mov    %rsi,0x58(%r12)
              data[0].messages = messages;
    30e6:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    30e9:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
              data[0].messages_count = 0;
    30f0:	0f 29 b0 80 00 00 00 	movaps %xmm6,0x80(%rax)
              data[1].messages_count = 0;
    30f7:	0f 29 b0 00 02 00 00 	movaps %xmm6,0x200(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    30fe:	e9 70 fa ff ff       	jmp    2b73 <main+0x583>
            CPU_SET(j, sendercpu);
    3103:	49 81 0e ff 0f 00 00 	orq    $0xfff,(%r14)
          for (int j = 0 ; j < cores ; j++) {
    310a:	e9 ba f8 ff ff       	jmp    29c9 <main+0x3d9>
    310f:	ba 02 00 00 00       	mov    $0x2,%edx
    3114:	48 8d 35 70 42 00 00 	lea    0x4270(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
    311b:	bf 01 00 00 00       	mov    $0x1,%edi
    3120:	31 c0                	xor    %eax,%eax
    3122:	e8 29 f3 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3127:	be 08 00 00 00       	mov    $0x8,%esi
    312c:	bf 01 00 00 00       	mov    $0x1,%edi
    3131:	e8 6a f2 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3136:	be 08 00 00 00       	mov    $0x8,%esi
    313b:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3140:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3145:	e8 56 f2 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    314a:	be 80 01 00 00       	mov    $0x180,%esi
    314f:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3154:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    3159:	e8 42 f2 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    315e:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
              data[1].messages = messages2;
    3163:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    3168:	41 c7 44 24 70 01 00 00 00 	movl   $0x1,0x70(%r12)
              data[0].messages_count = 0;
    3171:	66 0f 6f 3d 07 4a 00 00 	movdqa 0x4a07(%rip),%xmm7        # 7b80 <_IO_stdin_used+0xb80>
              mailboxes[b].higher = &data[1];
    3179:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    3180:	49 89 44 24 50       	mov    %rax,0x50(%r12)
              mailboxes[b].higher = &data[1];
    3185:	49 89 74 24 58       	mov    %rsi,0x58(%r12)
              data[0].messages = messages;
    318a:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    318d:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
              data[0].messages_count = 0;
    3194:	0f 29 b8 80 00 00 00 	movaps %xmm7,0x80(%rax)
              data[1].messages_count = 0;
    319b:	0f 29 b8 00 02 00 00 	movaps %xmm7,0x200(%rax)
            if ( b == x || b == x + 1) {
    31a2:	e9 3a f9 ff ff       	jmp    2ae1 <main+0x4f1>
    31a7:	ba 05 00 00 00       	mov    $0x5,%edx
    31ac:	48 8d 35 12 42 00 00 	lea    0x4212(%rip),%rsi        # 73c5 <_IO_stdin_used+0x3c5>
    31b3:	bf 01 00 00 00       	mov    $0x1,%edi
    31b8:	31 c0                	xor    %eax,%eax
    31ba:	4c 89 64 24 48       	mov    %r12,0x48(%rsp)
    31bf:	e8 8c f2 ff ff       	call   2450 <__printf_chk@plt>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    31c4:	be 08 00 00 00       	mov    $0x8,%esi
    31c9:	bf 02 00 00 00       	mov    $0x2,%edi
    31ce:	e8 cd f1 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    31d3:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    31d8:	be 38 00 00 00       	mov    $0x38,%esi
    31dd:	bf 08 00 00 00       	mov    $0x8,%edi
    my_thread_data[0] = &thread_data[x]; 
    31e2:	4d 8d ae c0 03 00 00 	lea    0x3c0(%r14),%r13
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    31e9:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    31ed:	4d 8d a6 c0 00 00 00 	lea    0xc0(%r14),%r12
    thread_data[x].threads = my_thread_data;
    31f4:	49 89 86 d8 03 00 00 	mov    %rax,0x3d8(%r14)
    my_thread_data[0] = &thread_data[x]; 
    31fb:	4c 89 28             	mov    %r13,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    31fe:	49 8b 46 38          	mov    0x38(%r14),%rax
    thread_data[x].thread_count = 2;
    3202:	41 c7 86 e8 03 00 00 02 00 00 00 	movl   $0x2,0x3e8(%r14)
    thread_data[x].thread_index = 0;
    320d:	41 c7 86 c4 03 00 00 00 00 00 00 	movl   $0x0,0x3c4(%r14)
    thread_data[x].task_count = total_barrier_count;
    3218:	41 c7 86 00 04 00 00 03 00 00 00 	movl   $0x3,0x400(%r14)
    thread_data[n].tasks[0].scheduled = 1;
    3223:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    322d:	49 8b 86 f8 00 00 00 	mov    0xf8(%r14),%rax
    3234:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    323e:	e8 5d f1 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3243:	be 38 00 00 00       	mov    $0x38,%esi
    3248:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    324d:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3250:	e8 4b f1 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3255:	be 38 00 00 00       	mov    $0x38,%esi
    325a:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    325f:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3262:	e8 39 f1 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3267:	be 38 00 00 00       	mov    $0x38,%esi
    326c:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3271:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3276:	e8 25 f1 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    327b:	be 08 00 00 00       	mov    $0x8,%esi
    3280:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3285:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    328a:	e8 11 f1 ff ff       	call   23a0 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    328f:	be 08 00 00 00       	mov    $0x8,%esi
    3294:	bf 08 00 00 00       	mov    $0x8,%edi
  thread_data[timer_threadi].type = TIMER;
    3299:	41 c7 86 0c 03 00 00 00 00 00 00 	movl   $0x0,0x30c(%r14)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    32a4:	49 89 c7             	mov    %rax,%r15
    32a7:	48 89 04 24          	mov    %rax,(%rsp)
  thread_data[timer_threadi].task_count = total_barrier_count;
    32ab:	48 8b 05 fe 48 00 00 	mov    0x48fe(%rip),%rax        # 7bb0 <_IO_stdin_used+0xbb0>
    32b2:	49 89 86 40 03 00 00 	mov    %rax,0x340(%r14)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    32b9:	e8 e2 f0 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    32be:	49 8d 96 80 01 00 00 	lea    0x180(%r14),%rdx
    32c5:	49 8d 8e 00 03 00 00 	lea    0x300(%r14),%rcx
  }
  thread_data[timer_threadi].threads = my_thread_data;
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    32cc:	41 c7 86 30 03 00 00 04 00 00 00 	movl   $0x4,0x330(%r14)
    my_thread_data[n] = &thread_data[n]; 
    32d7:	48 89 50 10          	mov    %rdx,0x10(%rax)
    32db:	49 8d 96 40 02 00 00 	lea    0x240(%r14),%rdx
    32e2:	49 8d be 80 04 00 00 	lea    0x480(%r14),%rdi
    32e9:	48 89 50 18          	mov    %rdx,0x18(%rax)
    32ed:	49 8d 96 40 05 00 00 	lea    0x540(%r14),%rdx
    32f4:	48 8d 35 d9 40 00 00 	lea    0x40d9(%rip),%rsi        # 73d4 <_IO_stdin_used+0x3d4>
    32fb:	48 89 48 20          	mov    %rcx,0x20(%rax)
    32ff:	4c 89 68 28          	mov    %r13,0x28(%rax)
    3303:	48 89 78 30          	mov    %rdi,0x30(%rax)
    3307:	48 89 50 38          	mov    %rdx,0x38(%rax)
    330b:	ba 04 00 00 00       	mov    $0x4,%edx
    3310:	4c 89 30             	mov    %r14,(%rax)
    3313:	4c 89 60 08          	mov    %r12,0x8(%rax)
  thread_data[timer_threadi].threads = my_thread_data;
    3317:	49 89 86 18 03 00 00 	mov    %rax,0x318(%r14)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    331e:	48 8b 05 93 48 00 00 	mov    0x4893(%rip),%rax        # 7bb8 <_IO_stdin_used+0xbb8>
  thread_data[timer_threadi].thread_index = 0;
    3325:	41 c7 86 04 03 00 00 00 00 00 00 	movl   $0x0,0x304(%r14)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3330:	49 89 86 28 03 00 00 	mov    %rax,0x328(%r14)
    3337:	31 c0                	xor    %eax,%eax
    my_thread_data[n] = &thread_data[n]; 
    3339:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
    333e:	bf 01 00 00 00       	mov    $0x1,%edi
    3343:	48 89 4c 24 28       	mov    %rcx,0x28(%rsp)
    3348:	e8 03 f1 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    334d:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3352:	49 8d 7f 20          	lea    0x20(%r15),%rdi
    3356:	48 8d 15 03 0b 00 00 	lea    0xb03(%rip),%rdx        # 3e60 <timer_thread>
    335d:	48 8d b5 e0 00 00 00 	lea    0xe0(%rbp),%rsi
    3364:	e8 07 f1 ff ff       	call   2470 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    3369:	4c 89 64 24 30       	mov    %r12,0x30(%rsp)
    336e:	45 31 c9             	xor    %r9d,%r9d
    3371:	4c 89 f9             	mov    %r15,%rcx
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3374:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    337a:	48 89 d8             	mov    %rbx,%rax
    337d:	4c 89 f2             	mov    %r14,%rdx
    3380:	45 89 cf             	mov    %r9d,%r15d
    3383:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    3388:	45 89 d5             	mov    %r10d,%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    338b:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    3390:	47 8d 34 3f          	lea    (%r15,%r15,1),%r14d
  int curcpu = 0;
    3394:	49 89 c4             	mov    %rax,%r12
    3397:	48 89 cd             	mov    %rcx,%rbp
    339a:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    339f:	48 89 d3             	mov    %rdx,%rbx
    33a2:	48 89 54 24 68       	mov    %rdx,0x68(%rsp)
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    33a7:	c7 43 0c 01 00 00 00 	movl   $0x1,0xc(%rbx)
    33ae:	44 89 f2             	mov    %r14d,%edx
    33b1:	44 89 f9             	mov    %r15d,%ecx
    33b4:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    33b6:	c7 43 44 01 00 00 00 	movl   $0x1,0x44(%rbx)
    33bd:	48 8d 35 2c 43 00 00 	lea    0x432c(%rip),%rsi        # 76f0 <_IO_stdin_used+0x6f0>
    33c4:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    33c9:	41 83 c6 01          	add    $0x1,%r14d
    33cd:	e8 7e f0 ff ff       	call   2450 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    33d2:	48 89 d9             	mov    %rbx,%rcx
    33d5:	4c 89 e6             	mov    %r12,%rsi
    33d8:	48 89 ef             	mov    %rbp,%rdi
    33db:	48 8d 15 de 27 00 00 	lea    0x27de(%rip),%rdx        # 5bc0 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    33e2:	48 81 c3 c0 00 00 00 	add    $0xc0,%rbx
    33e9:	48 83 c5 08          	add    $0x8,%rbp
    33ed:	49 83 c4 38          	add    $0x38,%r12
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    33f1:	e8 7a f0 ff ff       	call   2470 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    33f6:	48 8b 53 f0          	mov    -0x10(%rbx),%rdx
    33fa:	48 8b 7d f8          	mov    -0x8(%rbp),%rdi
    33fe:	be 08 00 00 00       	mov    $0x8,%esi
    3403:	e8 d8 ee ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3408:	45 39 f5             	cmp    %r14d,%r13d
    340b:	75 9a                	jne    33a7 <main+0xdb7>
  for (int k = 0 ; k < group_count ; k++) {
    340d:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3412:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    3417:	41 83 c5 02          	add    $0x2,%r13d
    341b:	48 8b 54 24 68       	mov    0x68(%rsp),%rdx
    3420:	48 83 c1 10          	add    $0x10,%rcx
    3424:	48 83 c0 70          	add    $0x70,%rax
    3428:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
    342f:	45 85 ff             	test   %r15d,%r15d
    3432:	75 0b                	jne    343f <main+0xe4f>
    3434:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    343a:	e9 4c ff ff ff       	jmp    338b <main+0xd9b>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    343f:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3444:	be d8 00 00 00       	mov    $0xd8,%esi
    3449:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    344e:	48 8b 1d 6b 47 00 00 	mov    0x476b(%rip),%rbx        # 7bc0 <_IO_stdin_used+0xbc0>
    thread_data[x].type = IO;
    3455:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    345a:	4c 8b 64 24 30       	mov    0x30(%rsp),%r12
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    345f:	bd 06 00 00 00       	mov    $0x6,%ebp
    thread_data[x].type = IO;
    3464:	41 c7 86 cc 03 00 00 02 00 00 00 	movl   $0x2,0x3cc(%r14)
    thread_data[x].task_count = 0;
    346f:	49 89 9e 00 04 00 00 	mov    %rbx,0x400(%r14)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3476:	e8 25 ef ff ff       	call   23a0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    347b:	be 00 08 00 00       	mov    $0x800,%esi
    3480:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3482:	49 89 86 18 04 00 00 	mov    %rax,0x418(%r14)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3489:	e8 22 f0 ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    348e:	be 08 00 00 00       	mov    $0x8,%esi
    3493:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3498:	41 89 86 20 04 00 00 	mov    %eax,0x420(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    349f:	e8 fc ee ff ff       	call   23a0 <calloc@plt>
    34a4:	ba 05 00 00 00       	mov    $0x5,%edx
    34a9:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].thread_count = thread_count;
    34ae:	41 c7 86 e8 03 00 00 02 00 00 00 	movl   $0x2,0x3e8(%r14)
      my_thread_data[n] = &thread_data[n]; 
    34b9:	4c 89 30             	mov    %r14,(%rax)
    34bc:	48 8d 35 2f 3f 00 00 	lea    0x3f2f(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    thread_data[x].threads = my_thread_data;
    34c3:	49 89 86 d8 03 00 00 	mov    %rax,0x3d8(%r14)
      my_thread_data[n] = &thread_data[n]; 
    34ca:	4c 89 60 08          	mov    %r12,0x8(%rax)
    34ce:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    34d0:	41 c7 86 c4 03 00 00 05 00 00 00 	movl   $0x5,0x3c4(%r14)
    34db:	e8 70 ef ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    34e0:	4c 8b 3c 24          	mov    (%rsp),%r15
    34e4:	4c 89 e9             	mov    %r13,%rcx
    34e7:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    34ec:	48 8d 15 dd 1e 00 00 	lea    0x1edd(%rip),%rdx        # 53d0 <io_thread>
    34f3:	49 8d 7f 28          	lea    0x28(%r15),%rdi
    34f7:	48 81 c6 18 01 00 00 	add    $0x118,%rsi
    34fe:	49 83 c7 30          	add    $0x30,%r15
    3502:	e8 69 ef ff ff       	call   2470 <pthread_create@plt>
    3507:	ba 06 00 00 00       	mov    $0x6,%edx
    350c:	48 8d 35 f6 3e 00 00 	lea    0x3ef6(%rip),%rsi        # 7409 <_IO_stdin_used+0x409>
    3513:	31 c0                	xor    %eax,%eax
    3515:	bf 01 00 00 00       	mov    $0x1,%edi
    351a:	e8 31 ef ff ff       	call   2450 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    351f:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    3524:	4c 89 f8             	mov    %r15,%rax
    3527:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    352c:	49 81 c6 50 01 00 00 	add    $0x150,%r14
    3533:	4d 89 f7             	mov    %r14,%r15
    3536:	41 89 ee             	mov    %ebp,%r14d
    3539:	48 89 c5             	mov    %rax,%rbp
    353c:	44 89 f2             	mov    %r14d,%edx
    353f:	48 8d 35 d9 3e 00 00 	lea    0x3ed9(%rip),%rsi        # 741f <_IO_stdin_used+0x41f>
    3546:	bf 01 00 00 00       	mov    $0x1,%edi
    354b:	31 c0                	xor    %eax,%eax
    354d:	e8 fe ee ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    3552:	49 89 5d 40          	mov    %rbx,0x40(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3556:	be 08 00 00 00       	mov    $0x8,%esi
    355b:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = EXTERNAL;
    3560:	41 c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3568:	e8 33 ee ff ff       	call   23a0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    356d:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3572:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3577:	41 c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3582:	49 89 45 50          	mov    %rax,0x50(%r13)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3586:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3589:	bf 02 00 00 00       	mov    $0x2,%edi
    358e:	e8 0d ee ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3593:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3598:	4c 89 e9             	mov    %r13,%rcx
    359b:	48 89 ef             	mov    %rbp,%rdi
    thread_data[x].threads = my_thread_data;
    359e:	49 89 45 18          	mov    %rax,0x18(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    35a2:	48 8d 15 a7 07 00 00 	lea    0x7a7(%rip),%rdx        # 3d50 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    35a9:	48 83 c5 08          	add    $0x8,%rbp
    35ad:	49 81 c5 c0 00 00 00 	add    $0xc0,%r13
      my_thread_data[n] = &thread_data[n]; 
    35b4:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    35b7:	4c 89 fe             	mov    %r15,%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    35ba:	49 83 c7 38          	add    $0x38,%r15
      my_thread_data[n] = &thread_data[n]; 
    35be:	4c 89 60 08          	mov    %r12,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    35c2:	48 8b 05 d7 45 00 00 	mov    0x45d7(%rip),%rax        # 7ba0 <_IO_stdin_used+0xba0>
    thread_data[x].thread_index = x;
    35c9:	45 89 b5 44 ff ff ff 	mov    %r14d,-0xbc(%r13)
    thread_data[x].thread_count = thread_count;
    35d0:	49 89 85 68 ff ff ff 	mov    %rax,-0x98(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    35d7:	e8 94 ee ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    35dc:	48 83 44 24 60 10    	addq   $0x10,0x60(%rsp)
    35e2:	41 83 fe 06          	cmp    $0x6,%r14d
    35e6:	75 0b                	jne    35f3 <main+0x1003>
    35e8:	41 be 07 00 00 00    	mov    $0x7,%r14d
    35ee:	e9 49 ff ff ff       	jmp    353c <main+0xf4c>
    35f3:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    35f8:	48 8d 2d 3d 3e 00 00 	lea    0x3e3d(%rip),%rbp        # 743c <_IO_stdin_used+0x43c>
    35ff:	4c 8d 68 04          	lea    0x4(%rax),%r13
    3603:	4c 8d a0 04 06 00 00 	lea    0x604(%rax),%r12
    360a:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    360e:	41 8b 55 00          	mov    0x0(%r13),%edx
    3612:	48 89 ee             	mov    %rbp,%rsi
    3615:	bf 01 00 00 00       	mov    $0x1,%edi
    361a:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    361c:	49 81 c5 c0 00 00 00 	add    $0xc0,%r13
    3623:	e8 28 ee ff ff       	call   2450 <__printf_chk@plt>
    3628:	4d 39 ec             	cmp    %r13,%r12
    362b:	75 dd                	jne    360a <main+0x101a>
    362d:	48 8d 3d 1b 3e 00 00 	lea    0x3e1b(%rip),%rdi        # 744f <_IO_stdin_used+0x44f>
    3634:	45 31 ed             	xor    %r13d,%r13d
    3637:	4c 8d a4 24 90 00 00 00 	lea    0x90(%rsp),%r12
    363f:	e8 ac ec ff ff       	call   22f0 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3644:	48 8b 1c 24          	mov    (%rsp),%rbx
    3648:	48 8d 2d 1e 3e 00 00 	lea    0x3e1e(%rip),%rbp        # 746d <_IO_stdin_used+0x46d>
    void * result; 
    pthread_join(thread[x], &result);
    364f:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    3653:	4c 89 e6             	mov    %r12,%rsi
    3656:	e8 95 ee ff ff       	call   24f0 <pthread_join@plt>
    365b:	44 89 ea             	mov    %r13d,%edx
    365e:	48 89 ee             	mov    %rbp,%rsi
    3661:	bf 01 00 00 00       	mov    $0x1,%edi
    3666:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3668:	49 83 c5 01          	add    $0x1,%r13
    366c:	e8 df ed ff ff       	call   2450 <__printf_chk@plt>
    3671:	49 83 fd 08          	cmp    $0x8,%r13
    3675:	75 d8                	jne    364f <main+0x105f>
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
    3677:	45 31 c9             	xor    %r9d,%r9d
  long sends = 0;
    367a:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    3682:	31 ed                	xor    %ebp,%ebp
  long sents = 0;
    3684:	45 31 db             	xor    %r11d,%r11d
  long total = 0;
    3687:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    3690:	49 89 ed             	mov    %rbp,%r13
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3693:	48 bb db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbx
    369d:	4c 89 4c 24 28       	mov    %r9,0x28(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    36a2:	4c 89 e8             	mov    %r13,%rax
    36a5:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    36aa:	4c 89 6c 24 50       	mov    %r13,0x50(%rsp)
    36af:	49 89 ec             	mov    %rbp,%r12
    36b2:	48 f7 d8             	neg    %rax
    36b5:	4c 8b 3c 24          	mov    (%rsp),%r15
    36b9:	4c 89 dd             	mov    %r11,%rbp
    36bc:	49 89 c6             	mov    %rax,%r14
    36bf:	83 e0 30             	and    $0x30,%eax
    36c2:	41 81 e6 80 01 00 00 	and    $0x180,%r14d
    36c9:	49 01 fe             	add    %rdi,%r14
    36cc:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    36d1:	48 01 f8             	add    %rdi,%rax
    36d4:	43 8d 7c 2d 00       	lea    0x0(%r13,%r13,1),%edi
    36d9:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    36de:	8d 47 ff             	lea    -0x1(%rdi),%eax
    36e1:	89 44 24 30          	mov    %eax,0x30(%rsp)
    36e5:	89 7c 24 60          	mov    %edi,0x60(%rsp)
      int x = (k * threads_per_group) + d;
    36e9:	8b 7c 24 30          	mov    0x30(%rsp),%edi
    36ed:	89 f8                	mov    %edi,%eax
    36ef:	89 7c 24 40          	mov    %edi,0x40(%rsp)
    36f3:	83 c7 01             	add    $0x1,%edi
    36f6:	89 fe                	mov    %edi,%esi
    36f8:	89 7c 24 30          	mov    %edi,0x30(%rsp)
        other = abs(x - 1) % total_threads;
    36fc:	89 c7                	mov    %eax,%edi
    36fe:	8d 40 02             	lea    0x2(%rax),%eax
    3701:	83 e6 01             	and    $0x1,%esi
    3704:	0f 45 c7             	cmovne %edi,%eax
    3707:	bf 0a 00 00 00       	mov    $0xa,%edi
    370c:	4c 63 e8             	movslq %eax,%r13
    370f:	e8 bc eb ff ff       	call   22d0 <putchar@plt>
    3714:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    3719:	bf 01 00 00 00       	mov    $0x1,%edi
    371e:	48 8d 35 5c 3d 00 00 	lea    0x3d5c(%rip),%rsi        # 7481 <_IO_stdin_used+0x481>
    3725:	48 8b 10             	mov    (%rax),%rdx
    3728:	31 c0                	xor    %eax,%eax
    372a:	e8 21 ed ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    372f:	41 8b 56 40          	mov    0x40(%r14),%edx
    3733:	85 d2                	test   %edx,%edx
    3735:	0f 8e 54 04 00 00    	jle    3b8f <main+0x159f>
    373b:	48 63 f2             	movslq %edx,%rsi
    373e:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    3742:	31 d2                	xor    %edx,%edx
    3744:	48 c1 e6 09          	shl    $0x9,%rsi
    3748:	48 01 c6             	add    %rax,%rsi
    374b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    3750:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3757:	48 05 00 02 00 00    	add    $0x200,%rax
    375d:	48 39 f0             	cmp    %rsi,%rax
    3760:	75 ee                	jne    3750 <main+0x1160>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3762:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    3767:	4b 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%rax
    376c:	48 c1 e0 06          	shl    $0x6,%rax
    3770:	48 01 f8             	add    %rdi,%rax
    3773:	48 63 70 40          	movslq 0x40(%rax),%rsi
    3777:	85 f6                	test   %esi,%esi
    3779:	7e 27                	jle    37a2 <main+0x11b2>
    377b:	48 8b 40 38          	mov    0x38(%rax),%rax
    377f:	48 c1 e6 09          	shl    $0x9,%rsi
    3783:	48 01 c6             	add    %rax,%rsi
    3786:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3790:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3797:	48 05 00 02 00 00    	add    $0x200,%rax
    379d:	48 39 f0             	cmp    %rsi,%rax
    37a0:	75 ee                	jne    3790 <main+0x11a0>
    37a2:	48 8d 35 ed 3c 00 00 	lea    0x3ced(%rip),%rsi        # 7496 <_IO_stdin_used+0x496>
    37a9:	bf 01 00 00 00       	mov    $0x1,%edi
    37ae:	31 c0                	xor    %eax,%eax
    37b0:	e8 9b ec ff ff       	call   2450 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    37b5:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    37ba:	bf 01 00 00 00       	mov    $0x1,%edi
    37bf:	48 8b 30             	mov    (%rax),%rsi
    37c2:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    37cc:	48 f7 ee             	imul   %rsi
    37cf:	48 c1 fe 3f          	sar    $0x3f,%rsi
    37d3:	31 c0                	xor    %eax,%eax
    37d5:	48 d1 fa             	sar    %rdx
    37d8:	48 29 f2             	sub    %rsi,%rdx
    37db:	48 8d 35 3e 3f 00 00 	lea    0x3f3e(%rip),%rsi        # 7720 <_IO_stdin_used+0x720>
    37e2:	e8 69 ec ff ff       	call   2450 <__printf_chk@plt>
    37e7:	bf 0a 00 00 00       	mov    $0xa,%edi
    37ec:	e8 df ea ff ff       	call   22d0 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    37f1:	41 8b 56 40          	mov    0x40(%r14),%edx
    37f5:	85 d2                	test   %edx,%edx
    37f7:	7e 60                	jle    3859 <main+0x1269>
    37f9:	49 8b 46 38          	mov    0x38(%r14),%rax
    37fd:	48 63 f2             	movslq %edx,%rsi
    3800:	4c 8b 5c 24 28       	mov    0x28(%rsp),%r11
    3805:	48 c1 e6 09          	shl    $0x9,%rsi
    3809:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    380e:	48 01 c6             	add    %rax,%rsi
    3811:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3818:	48 8b 90 70 01 00 00 	mov    0x170(%rax),%rdx
        total += thread_data[x].tasks[n].n;
    381f:	48 03 88 08 01 00 00 	add    0x108(%rax),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3826:	48 05 00 02 00 00    	add    $0x200,%rax
        ingests += thread_data[x].tasks[n].ingest_count;
    382c:	4c 03 98 68 ff ff ff 	add    -0x98(%rax),%r11
        sends += thread_data[x].tasks[n].sends;
    3833:	4c 03 b8 78 ff ff ff 	add    -0x88(%rax),%r15
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    383a:	48 03 6a 10          	add    0x10(%rdx),%rbp
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    383e:	4c 03 62 18          	add    0x18(%rdx),%r12
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3842:	48 03 6a 38          	add    0x38(%rdx),%rbp
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3846:	4c 03 62 40          	add    0x40(%rdx),%r12
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    384a:	48 39 f0             	cmp    %rsi,%rax
    384d:	75 c9                	jne    3818 <main+0x1228>
    384f:	4c 89 5c 24 28       	mov    %r11,0x28(%rsp)
    3854:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3859:	45 31 ed             	xor    %r13d,%r13d
    385c:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    3864:	0f 8e 81 00 00 00    	jle    38eb <main+0x12fb>
    386a:	48 89 ef             	mov    %rbp,%rdi
    386d:	4c 89 f0             	mov    %r14,%rax
    3870:	4c 89 ed             	mov    %r13,%rbp
    3873:	4d 89 e6             	mov    %r12,%r14
    3876:	49 89 fd             	mov    %rdi,%r13
    3879:	49 89 c4             	mov    %rax,%r12
    387c:	0f 1f 40 00          	nopl   0x0(%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3880:	48 8d 54 ad 00       	lea    0x0(%rbp,%rbp,4),%rdx
    3885:	48 83 ec 08          	sub    $0x8,%rsp
    3889:	bf 01 00 00 00       	mov    $0x1,%edi
    388e:	49 8b 84 24 90 00 00 00 	mov    0x90(%r12),%rax
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3896:	48 83 c5 01          	add    $0x1,%rbp
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    389a:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    389e:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    38a2:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    38a6:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    38a9:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    38ad:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    38b0:	48 f7 e3             	mul    %rbx
    38b3:	8b 49 20             	mov    0x20(%rcx),%ecx
    38b6:	56                   	push   %rsi
    38b7:	31 c0                	xor    %eax,%eax
    38b9:	48 8d 35 80 3e 00 00 	lea    0x3e80(%rip),%rsi        # 7740 <_IO_stdin_used+0x740>
    38c0:	48 c1 ea 12          	shr    $0x12,%rdx
    38c4:	49 89 d1             	mov    %rdx,%r9
    38c7:	ba 02 00 00 00       	mov    $0x2,%edx
    38cc:	e8 7f eb ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    38d1:	41 58                	pop    %r8
    38d3:	41 59                	pop    %r9
    38d5:	49 39 ac 24 a0 00 00 00 	cmp    %rbp,0xa0(%r12)
    38dd:	7f a1                	jg     3880 <main+0x1290>
    38df:	4c 89 e0             	mov    %r12,%rax
    38e2:	4c 89 ed             	mov    %r13,%rbp
    38e5:	4d 89 f4             	mov    %r14,%r12
    38e8:	49 89 c6             	mov    %rax,%r14
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    38eb:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    38f2:	85 f6                	test   %esi,%esi
    38f4:	0f 8e 0a 01 00 00    	jle    3a04 <main+0x1414>
    38fa:	48 89 6c 24 68       	mov    %rbp,0x68(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    38ff:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    3903:	31 d2                	xor    %edx,%edx
    3905:	4c 89 7c 24 70       	mov    %r15,0x70(%rsp)
    390a:	4c 89 64 24 78       	mov    %r12,0x78(%rsp)
    390f:	90                   	nop
    3910:	49 8b 04 d1          	mov    (%r9,%rdx,8),%rax
    3914:	41 89 d7             	mov    %edx,%r15d
    3917:	48 8d 2c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rbp
    391f:	44 8b 00             	mov    (%rax),%r8d
    3922:	45 85 c0             	test   %r8d,%r8d
    3925:	0f 8e be 00 00 00    	jle    39e9 <main+0x13f9>
    392b:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3930:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3934:	31 c0                	xor    %eax,%eax
    3936:	48 89 c6             	mov    %rax,%rsi
    3939:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3940:	49 89 f4             	mov    %rsi,%r12
    3943:	45 31 ed             	xor    %r13d,%r13d
    3946:	49 c1 e4 08          	shl    $0x8,%r12
    394a:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    394e:	8b 82 94 00 00 00    	mov    0x94(%rdx),%eax
    3954:	85 c0                	test   %eax,%eax
    3956:	7e 78                	jle    39d0 <main+0x13e0>
    3958:	48 89 34 24          	mov    %rsi,(%rsp)
    395c:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3960:	4c 89 e9             	mov    %r13,%rcx
    3963:	48 83 ec 08          	sub    $0x8,%rsp
    3967:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    396c:	49 83 c5 01          	add    $0x1,%r13
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3970:	48 c1 e1 05          	shl    $0x5,%rcx
    3974:	48 03 8a 88 00 00 00 	add    0x88(%rdx),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    397b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    397f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3983:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3986:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    398a:	4c 2b 01             	sub    (%rcx),%r8
    398d:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    398e:	48 f7 e3             	mul    %rbx
    3991:	44 89 f9             	mov    %r15d,%ecx
    3994:	48 8d 35 f5 3d 00 00 	lea    0x3df5(%rip),%rsi        # 7790 <_IO_stdin_used+0x790>
    399b:	31 c0                	xor    %eax,%eax
    399d:	48 c1 ea 12          	shr    $0x12,%rdx
    39a1:	49 89 d1             	mov    %rdx,%r9
    39a4:	ba 02 00 00 00       	mov    $0x2,%edx
    39a9:	e8 a2 ea ff ff       	call   2450 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    39ae:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    39b2:	5e                   	pop    %rsi
    39b3:	5f                   	pop    %rdi
    39b4:	49 8b 04 29          	mov    (%r9,%rbp,1),%rax
    39b8:	48 8b 48 08          	mov    0x8(%rax),%rcx
    39bc:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    39c0:	44 39 aa 94 00 00 00 	cmp    %r13d,0x94(%rdx)
    39c7:	7f 97                	jg     3960 <main+0x1370>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    39c9:	48 8b 34 24          	mov    (%rsp),%rsi
    39cd:	44 8b 00             	mov    (%rax),%r8d
    39d0:	48 83 c6 01          	add    $0x1,%rsi
    39d4:	41 39 f0             	cmp    %esi,%r8d
    39d7:	0f 8f 63 ff ff ff    	jg     3940 <main+0x1350>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    39dd:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    39e2:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    39e9:	48 83 c2 01          	add    $0x1,%rdx
    39ed:	39 d6                	cmp    %edx,%esi
    39ef:	0f 8f 1b ff ff ff    	jg     3910 <main+0x1320>
    39f5:	48 8b 6c 24 68       	mov    0x68(%rsp),%rbp
    39fa:	4c 8b 7c 24 70       	mov    0x70(%rsp),%r15
    39ff:	4c 8b 64 24 78       	mov    0x78(%rsp),%r12
    for (int d = 0 ; d < threads_per_group ; d++) {
    3a04:	48 83 44 24 20 18    	addq   $0x18,0x20(%rsp)
    3a0a:	8b 7c 24 40          	mov    0x40(%rsp),%edi
    3a0e:	49 81 c6 c0 00 00 00 	add    $0xc0,%r14
    3a15:	39 7c 24 60          	cmp    %edi,0x60(%rsp)
    3a19:	0f 85 ca fc ff ff    	jne    36e9 <main+0x10f9>
  for (int k = 0 ; k < group_count ; k++) {
    3a1f:	4c 8b 6c 24 50       	mov    0x50(%rsp),%r13
    3a24:	49 89 eb             	mov    %rbp,%r11
    3a27:	4c 89 3c 24          	mov    %r15,(%rsp)
    3a2b:	4c 89 e5             	mov    %r12,%rbp
    3a2e:	4d 85 ed             	test   %r13,%r13
    3a31:	75 0a                	jne    3a3d <main+0x144d>
    3a33:	4c 8b 6c 24 48       	mov    0x48(%rsp),%r13
    3a38:	e9 65 fc ff ff       	jmp    36a2 <main+0x10b2>
    3a3d:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
    3a42:	4c 8b 4c 24 28       	mov    0x28(%rsp),%r9
    3a47:	48 8d 35 55 3a 00 00 	lea    0x3a55(%rip),%rsi        # 74a3 <_IO_stdin_used+0x4a3>
    3a4e:	31 c0                	xor    %eax,%eax
    3a50:	bf 01 00 00 00       	mov    $0x1,%edi
    3a55:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3a5a:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    3a64:	4c 89 fa             	mov    %r15,%rdx
    3a67:	4c 89 4c 24 20       	mov    %r9,0x20(%rsp)
    3a6c:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
    3a71:	e8 da e9 ff ff       	call   2450 <__printf_chk@plt>
    3a76:	bf 0a 00 00 00       	mov    $0xa,%edi
    3a7b:	e8 50 e8 ff ff       	call   22d0 <putchar@plt>
    3a80:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3a85:	bf 01 00 00 00       	mov    $0x1,%edi
    3a8a:	48 8d 35 57 3d 00 00 	lea    0x3d57(%rip),%rsi        # 77e8 <_IO_stdin_used+0x7e8>
    3a91:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3a95:	31 c0                	xor    %eax,%eax
    3a97:	e8 b4 e9 ff ff       	call   2450 <__printf_chk@plt>
    3a9c:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    3aa1:	bf 01 00 00 00       	mov    $0x1,%edi
    3aa6:	48 8d 35 63 3d 00 00 	lea    0x3d63(%rip),%rsi        # 7810 <_IO_stdin_used+0x810>
    3aad:	4c 89 c8             	mov    %r9,%rax
    3ab0:	49 c1 f9 3f          	sar    $0x3f,%r9
    3ab4:	48 f7 eb             	imul   %rbx
    3ab7:	31 c0                	xor    %eax,%eax
    3ab9:	48 d1 fa             	sar    %rdx
    3abc:	4c 29 ca             	sub    %r9,%rdx
    3abf:	e8 8c e9 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3ac4:	48 8b 04 24          	mov    (%rsp),%rax
    3ac8:	bf 01 00 00 00       	mov    $0x1,%edi
    3acd:	48 8d 35 6c 3d 00 00 	lea    0x3d6c(%rip),%rsi        # 7840 <_IO_stdin_used+0x840>
    3ad4:	48 f7 eb             	imul   %rbx
    3ad7:	48 8b 04 24          	mov    (%rsp),%rax
    3adb:	48 c1 f8 3f          	sar    $0x3f,%rax
    3adf:	48 d1 fa             	sar    %rdx
    3ae2:	48 29 c2             	sub    %rax,%rdx
    3ae5:	31 c0                	xor    %eax,%eax
    3ae7:	e8 64 e9 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3aec:	4c 89 f8             	mov    %r15,%rax
    3aef:	bf 01 00 00 00       	mov    $0x1,%edi
    3af4:	48 8d 35 75 3d 00 00 	lea    0x3d75(%rip),%rsi        # 7870 <_IO_stdin_used+0x870>
    3afb:	48 f7 eb             	imul   %rbx
    3afe:	4c 89 f8             	mov    %r15,%rax
    3b01:	48 c1 f8 3f          	sar    $0x3f,%rax
    3b05:	48 d1 fa             	sar    %rdx
    3b08:	48 29 c2             	sub    %rax,%rdx
    3b0b:	31 c0                	xor    %eax,%eax
    3b0d:	e8 3e e9 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3b12:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    3b17:	bf 01 00 00 00       	mov    $0x1,%edi
    3b1c:	48 8d 35 94 39 00 00 	lea    0x3994(%rip),%rsi        # 74b7 <_IO_stdin_used+0x4b7>
    3b23:	4c 89 d8             	mov    %r11,%rax
    3b26:	48 f7 eb             	imul   %rbx
    3b29:	4c 89 d8             	mov    %r11,%rax
    3b2c:	48 c1 f8 3f          	sar    $0x3f,%rax
    3b30:	48 d1 fa             	sar    %rdx
    3b33:	48 29 c2             	sub    %rax,%rdx
    3b36:	31 c0                	xor    %eax,%eax
    3b38:	e8 13 e9 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3b3d:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    3b42:	bf 01 00 00 00       	mov    $0x1,%edi
    3b47:	48 8d 35 7a 39 00 00 	lea    0x397a(%rip),%rsi        # 74c8 <_IO_stdin_used+0x4c8>
    3b4e:	4c 89 d0             	mov    %r10,%rax
    3b51:	48 f7 eb             	imul   %rbx
    3b54:	4c 89 d0             	mov    %r10,%rax
    3b57:	48 c1 f8 3f          	sar    $0x3f,%rax
    3b5b:	48 d1 fa             	sar    %rdx
    3b5e:	48 29 c2             	sub    %rax,%rdx
    3b61:	31 c0                	xor    %eax,%eax
    3b63:	e8 e8 e8 ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3b68:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    3b70:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3b79:	75 25                	jne    3ba0 <main+0x15b0>
    3b7b:	48 81 c4 a8 00 00 00 	add    $0xa8,%rsp
    3b82:	31 c0                	xor    %eax,%eax
    3b84:	5b                   	pop    %rbx
    3b85:	5d                   	pop    %rbp
    3b86:	41 5c                	pop    %r12
    3b88:	41 5d                	pop    %r13
    3b8a:	41 5e                	pop    %r14
    3b8c:	41 5f                	pop    %r15
    3b8e:	c3                   	ret
      long v = 0;
    3b8f:	31 d2                	xor    %edx,%edx
    3b91:	e9 cc fb ff ff       	jmp    3762 <main+0x1172>
            exit(1);
    3b96:	bf 01 00 00 00       	mov    $0x1,%edi
    3b9b:	e8 00 e9 ff ff       	call   24a0 <exit@plt>
}
    3ba0:	e8 8b e7 ff ff       	call   2330 <__stack_chk_fail@plt>
    3ba5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3baf:	90                   	nop

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
    3bc8:	48 8d 3d 21 ea ff ff 	lea    -0x15df(%rip),%rdi        # 25f0 <main>
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
    3c72:	e8 39 e6 ff ff       	call   22b0 <__cxa_finalize@plt>
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
    3e1c:	e8 ef e4 ff ff       	call   2310 <clock_gettime@plt>
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
    3e94:	e8 b7 e5 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3e99:	66 0f 6f 05 ef 3b 00 00 	movdqa 0x3bef(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
    3ea1:	ba 88 13 00 00       	mov    $0x1388,%edx
    3ea6:	31 c0                	xor    %eax,%eax
    3ea8:	48 8d 35 73 31 00 00 	lea    0x3173(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3eaf:	bf 01 00 00 00       	mov    $0x1,%edi
    3eb4:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3eb9:	e8 92 e5 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3ebe:	44 8b 65 44          	mov    0x44(%rbp),%r12d
    3ec2:	45 85 e4             	test   %r12d,%r12d
    3ec5:	0f 84 a3 00 00 00    	je     3f6e <timer_thread+0x10e>
  int n = 0;
    3ecb:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    3ece:	45 31 e4             	xor    %r12d,%r12d
    3ed1:	49 89 e6             	mov    %rsp,%r14
    y++;
    3ed4:	31 db                	xor    %ebx,%ebx
    3ed6:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    3edb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    nanosleep(&preempt , &rem2);
    3ee0:	4c 89 ef             	mov    %r13,%rdi
    3ee3:	4c 89 f6             	mov    %r14,%rsi
    n++;
    3ee6:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3eea:	e8 61 e4 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3eef:	48 63 45 30          	movslq 0x30(%rbp),%rax
    y++;
    3ef3:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3ef8:	85 c0                	test   %eax,%eax
    3efa:	7e 49                	jle    3f45 <timer_thread+0xe5>
    3efc:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3f00:	49 c1 e4 09          	shl    $0x9,%r12
    3f04:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3f08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3f10:	4c 8b 11             	mov    (%rcx),%r10
    3f13:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f15:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3f19:	99                   	cltd
    3f1a:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3f1e:	49 8b 72 38          	mov    0x38(%r10),%rsi
    3f22:	48 63 d2             	movslq %edx,%rdx
    3f25:	48 c1 e2 09          	shl    $0x9,%rdx
    3f29:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3f34:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f40:	49 39 c8             	cmp    %rcx,%r8
    3f43:	75 cb                	jne    3f10 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    3f45:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3f48:	48 8b 45 18          	mov    0x18(%rbp),%rax
  while (data->running && n < times) {
    3f4c:	44 8b 45 44          	mov    0x44(%rbp),%r8d
    if (y >= data->threads[0]->task_count) {
    3f50:	48 8b 00             	mov    (%rax),%rax
    y++;
    3f53:	39 78 40             	cmp    %edi,0x40(%rax)
    3f56:	0f 4e fb             	cmovle %ebx,%edi
    3f59:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3f5c:	45 85 c0             	test   %r8d,%r8d
    3f5f:	74 0d                	je     3f6e <timer_thread+0x10e>
    3f61:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    3f68:	0f 85 72 ff ff ff    	jne    3ee0 <timer_thread+0x80>
    3f6e:	48 8d 3d c3 30 00 00 	lea    0x30c3(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3f75:	e8 76 e3 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f7a:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    3f7e:	85 d2                	test   %edx,%edx
    3f80:	7e 73                	jle    3ff5 <timer_thread+0x195>
    for (int y = 0 ; y < data->task_count ; y++) {
    3f82:	48 63 45 40          	movslq 0x40(%rbp),%rax
    3f86:	85 c0                	test   %eax,%eax
    3f88:	7e 6b                	jle    3ff5 <timer_thread+0x195>
    3f8a:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3f8e:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    3f92:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3f9a:	31 c9                	xor    %ecx,%ecx
    3f9c:	48 89 c6             	mov    %rax,%rsi
    3f9f:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3fa3:	48 8b 40 38          	mov    0x38(%rax),%rax
    3fa7:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    3fab:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3fb1:	74 1d                	je     3fd0 <timer_thread+0x170>
    3fb3:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3fbd:	48 05 00 02 00 00    	add    $0x200,%rax
    3fc3:	48 39 c2             	cmp    %rax,%rdx
    3fc6:	74 24                	je     3fec <timer_thread+0x18c>
    3fc8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->threads[x]->tasks[y].sending = 0;
    3fd0:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3fda:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3fe0:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3fe7:	48 39 c2             	cmp    %rax,%rdx
    3fea:	75 e4                	jne    3fd0 <timer_thread+0x170>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3fec:	48 83 c1 08          	add    $0x8,%rcx
    3ff0:	48 39 cf             	cmp    %rcx,%rdi
    3ff3:	75 aa                	jne    3f9f <timer_thread+0x13f>
  asm volatile ("mfence" ::: "memory");
    3ff5:	0f ae f0             	mfence
  struct timespec drain = {
    3ff8:	66 0f 6f 05 a0 3a 00 00 	movdqa 0x3aa0(%rip),%xmm0        # 7aa0 <_IO_stdin_used+0xaa0>
    4000:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4005:	48 63 45 28          	movslq 0x28(%rbp),%rax
    y++;
    4009:	45 8d 44 24 01       	lea    0x1(%r12),%r8d
    for (int x = 0 ; x < data->thread_count ; x++) {
    400e:	85 c0                	test   %eax,%eax
    4010:	7e 4b                	jle    405d <timer_thread+0x1fd>
    4012:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4016:	4d 63 e4             	movslq %r12d,%r12
    4019:	49 c1 e4 09          	shl    $0x9,%r12
    401d:	48 8d 3c c1          	lea    (%rcx,%rax,8),%rdi
    4021:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4028:	48 8b 19             	mov    (%rcx),%rbx
    402b:	44 89 c0             	mov    %r8d,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    402e:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4032:	99                   	cltd
    4033:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4036:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    403a:	48 63 d2             	movslq %edx,%rdx
    403d:	48 c1 e2 09          	shl    $0x9,%rdx
    4041:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    404c:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4058:	48 39 cf             	cmp    %rcx,%rdi
    405b:	75 cb                	jne    4028 <timer_thread+0x1c8>
    asm volatile ("mfence" ::: "memory");
    405d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4060:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4064:	8b 4d 30             	mov    0x30(%rbp),%ecx
    y++;
    4067:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    406a:	48 8b 07             	mov    (%rdi),%rax
    y++;
    406d:	44 39 40 40          	cmp    %r8d,0x40(%rax)
    4071:	45 0f 4f e0          	cmovg  %r8d,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4075:	85 c9                	test   %ecx,%ecx
    4077:	0f 8e 0d 01 00 00    	jle    418a <timer_thread+0x32a>
    407d:	45 31 ff             	xor    %r15d,%r15d
    int all_empty = 1;
    4080:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    4086:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int y = 0 ; y < 2 ; y++) {
    4090:	31 db                	xor    %ebx,%ebx
    4092:	45 89 fd             	mov    %r15d,%r13d
    4095:	4e 8d 34 fd 00 00 00 00 	lea    0x0(,%r15,8),%r14
    409d:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    409f:	85 c9                	test   %ecx,%ecx
    40a1:	0f 8e 91 00 00 00    	jle    4138 <timer_thread+0x2d8>
    40a7:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    40ab:	4a 8b 14 37          	mov    (%rdi,%r14,1),%rdx
    40af:	48 89 d8             	mov    %rbx,%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    40b2:	45 31 c0             	xor    %r8d,%r8d
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    40b5:	48 c1 e0 09          	shl    $0x9,%rax
    40b9:	48 03 42 38          	add    0x38(%rdx),%rax
    40bd:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    40c4:	eb 1c                	jmp    40e2 <timer_thread+0x282>
    40c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    40d0:	48 85 d2             	test   %rdx,%rdx
    40d3:	7f 27                	jg     40fc <timer_thread+0x29c>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    40d5:	41 83 c0 01          	add    $0x1,%r8d
    40d9:	48 83 c0 28          	add    $0x28,%rax
    40dd:	41 39 c8             	cmp    %ecx,%r8d
    40e0:	74 7e                	je     4160 <timer_thread+0x300>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    40e2:	48 8b 10             	mov    (%rax),%rdx
    40e5:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    40ec:	48 8b 50 08          	mov    0x8(%rax),%rdx
    40f0:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    40f7:	4d 85 c9             	test   %r9,%r9
    40fa:	7e d4                	jle    40d0 <timer_thread+0x270>
    40fc:	48 83 ec 08          	sub    $0x8,%rsp
    4100:	89 f1                	mov    %esi,%ecx
    4102:	bf 01 00 00 00       	mov    $0x1,%edi
    4107:	31 c0                	xor    %eax,%eax
    4109:	52                   	push   %rdx
    410a:	48 8d 35 4c 2f 00 00 	lea    0x2f4c(%rip),%rsi        # 705d <_IO_stdin_used+0x5d>
    4111:	44 89 ea             	mov    %r13d,%edx
    4114:	e8 37 e3 ff ff       	call   2450 <__printf_chk@plt>
      for (int y = 0 ; y < 2 ; y++) {
    4119:	5a                   	pop    %rdx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    411a:	8b 4d 30             	mov    0x30(%rbp),%ecx
      for (int y = 0 ; y < 2 ; y++) {
    411d:	5e                   	pop    %rsi
    411e:	48 83 fb 01          	cmp    $0x1,%rbx
    4122:	74 54                	je     4178 <timer_thread+0x318>
    4124:	48 83 c3 01          	add    $0x1,%rbx
    4128:	45 31 db             	xor    %r11d,%r11d
    412b:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    412d:	85 c9                	test   %ecx,%ecx
    412f:	0f 8f 72 ff ff ff    	jg     40a7 <timer_thread+0x247>
    4135:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4138:	49 83 c7 01          	add    $0x1,%r15
    413c:	44 39 f9             	cmp    %r15d,%ecx
    413f:	0f 8f 4b ff ff ff    	jg     4090 <timer_thread+0x230>
    if (all_empty == 1) {
    4145:	41 83 fb 01          	cmp    $0x1,%r11d
    4149:	74 3f                	je     418a <timer_thread+0x32a>
      nanosleep(&drain , &drainrem);
    414b:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4150:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4155:	e8 f6 e1 ff ff       	call   2350 <nanosleep@plt>
    415a:	e9 a6 fe ff ff       	jmp    4005 <timer_thread+0x1a5>
    415f:	90                   	nop
      for (int y = 0 ; y < 2 ; y++) {
    4160:	48 83 fb 01          	cmp    $0x1,%rbx
    4164:	74 d2                	je     4138 <timer_thread+0x2d8>
    4166:	48 83 c3 01          	add    $0x1,%rbx
    416a:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    416c:	e9 3a ff ff ff       	jmp    40ab <timer_thread+0x24b>
    4171:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4178:	49 83 c7 01          	add    $0x1,%r15
    417c:	45 31 db             	xor    %r11d,%r11d
    417f:	44 39 f9             	cmp    %r15d,%ecx
    4182:	0f 8f 08 ff ff ff    	jg     4090 <timer_thread+0x230>
    4188:	eb bb                	jmp    4145 <timer_thread+0x2e5>
    418a:	48 8d 3d c3 2e 00 00 	lea    0x2ec3(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    4191:	e8 5a e1 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    4196:	8b 7d 44             	mov    0x44(%rbp),%edi
    4199:	85 ff                	test   %edi,%edi
    419b:	0f 84 ed 00 00 00    	je     428e <timer_thread+0x42e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    41a1:	8b 45 2c             	mov    0x2c(%rbp),%eax
    41a4:	31 db                	xor    %ebx,%ebx
    41a6:	4c 8d 25 c7 2e 00 00 	lea    0x2ec7(%rip),%r12        # 7074 <_IO_stdin_used+0x74>
    41ad:	4c 8d 2d db 2e 00 00 	lea    0x2edb(%rip),%r13        # 708f <_IO_stdin_used+0x8f>
    41b4:	85 c0                	test   %eax,%eax
    41b6:	7e 3b                	jle    41f3 <timer_thread+0x393>
    41b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    41c0:	31 c0                	xor    %eax,%eax
    41c2:	89 da                	mov    %ebx,%edx
    41c4:	4c 89 e6             	mov    %r12,%rsi
    41c7:	bf 01 00 00 00       	mov    $0x1,%edi
    41cc:	e8 7f e2 ff ff       	call   2450 <__printf_chk@plt>
      data->threads[x]->running = 0;
    41d1:	48 8b 45 18          	mov    0x18(%rbp),%rax
    41d5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    41d9:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    41dd:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    41e4:	0f 84 d1 00 00 00    	je     42bb <timer_thread+0x45b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    41ea:	48 83 c3 01          	add    $0x1,%rbx
    41ee:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    41f1:	7f cd                	jg     41c0 <timer_thread+0x360>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    41f3:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    41f7:	85 d2                	test   %edx,%edx
    41f9:	7e 7d                	jle    4278 <timer_thread+0x418>
      for (int y = 0 ; y < data->task_count ; y++) {
    41fb:	8b 45 40             	mov    0x40(%rbp),%eax
    41fe:	85 c0                	test   %eax,%eax
    4200:	7e 76                	jle    4278 <timer_thread+0x418>
    4202:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4205:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    4209:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4211:	31 c9                	xor    %ecx,%ecx
    4213:	48 c1 e6 09          	shl    $0x9,%rsi
    4217:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4220:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4224:	48 8b 40 38          	mov    0x38(%rax),%rax
    4228:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    422c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4232:	74 1c                	je     4250 <timer_thread+0x3f0>
    4234:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    423e:	48 05 00 02 00 00    	add    $0x200,%rax
    4244:	48 39 d0             	cmp    %rdx,%rax
    4247:	74 26                	je     426f <timer_thread+0x40f>
    4249:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4250:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    425a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4260:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    426a:	48 39 d0             	cmp    %rdx,%rax
    426d:	75 e1                	jne    4250 <timer_thread+0x3f0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    426f:	48 83 c1 08          	add    $0x8,%rcx
    4273:	48 39 f9             	cmp    %rdi,%rcx
    4276:	75 a8                	jne    4220 <timer_thread+0x3c0>
    asm volatile ("mfence" ::: "memory");
    4278:	0f ae f0             	mfence
    427b:	48 8d 3d 1f 2e 00 00 	lea    0x2e1f(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    4282:	e8 69 e0 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    4287:	c7 45 44 00 00 00 00 	movl   $0x0,0x44(%rbp)
    428e:	48 8d 3d 13 2e 00 00 	lea    0x2e13(%rip),%rdi        # 70a8 <_IO_stdin_used+0xa8>
    4295:	e8 56 e0 ff ff       	call   22f0 <puts@plt>
}
    429a:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    429f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    42a8:	75 40                	jne    42ea <timer_thread+0x48a>
    42aa:	48 83 c4 58          	add    $0x58,%rsp
    42ae:	31 c0                	xor    %eax,%eax
    42b0:	5b                   	pop    %rbx
    42b1:	5d                   	pop    %rbp
    42b2:	41 5c                	pop    %r12
    42b4:	41 5d                	pop    %r13
    42b6:	41 5e                	pop    %r14
    42b8:	41 5f                	pop    %r15
    42ba:	c3                   	ret
    42bb:	4c 89 ef             	mov    %r13,%rdi
    42be:	e8 2d e0 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    42c3:	48 8b 45 18          	mov    0x18(%rbp),%rax
    42c7:	be 01 00 00 00       	mov    $0x1,%esi
    42cc:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    42d0:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    42d4:	8b 78 60             	mov    0x60(%rax),%edi
    42d7:	e8 24 e1 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    42dc:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    42df:	0f 8f db fe ff ff    	jg     41c0 <timer_thread+0x360>
    42e5:	e9 09 ff ff ff       	jmp    41f3 <timer_thread+0x393>
}
    42ea:	e8 41 e0 ff ff       	call   2330 <__stack_chk_fail@plt>
    42ef:	90                   	nop

00000000000042f0 <sendm.part.0>:
int sendm(struct BarrierTask *data) {
    42f0:	41 57                	push   %r15
    42f2:	41 56                	push   %r14
    42f4:	41 55                	push   %r13
    42f6:	41 54                	push   %r12
    42f8:	55                   	push   %rbp
    42f9:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    42fa:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    4300:	89 44 24 c8          	mov    %eax,-0x38(%rsp)
    4304:	85 c0                	test   %eax,%eax
    4306:	0f 8e 77 01 00 00    	jle    4483 <sendm.part.0+0x193>
        if (n == data->thread_index) { continue; }
    430c:	8b 87 30 01 00 00    	mov    0x130(%rdi),%eax
    4312:	49 89 fe             	mov    %rdi,%r14
    4315:	45 31 e4             	xor    %r12d,%r12d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    4318:	45 31 ff             	xor    %r15d,%r15d
        if (n == data->thread_index) { continue; }
    431b:	89 44 24 cc          	mov    %eax,-0x34(%rsp)
    431f:	48 8d 87 88 01 00 00 	lea    0x188(%rdi),%rax
    4326:	48 89 44 24 e8       	mov    %rax,-0x18(%rsp)
    432b:	48 8d 87 90 01 00 00 	lea    0x190(%rdi),%rax
    4332:	48 89 44 24 f0       	mov    %rax,-0x10(%rsp)
    4337:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4340:	44 39 7c 24 cc       	cmp    %r15d,-0x34(%rsp)
    4345:	0f 84 23 01 00 00    	je     446e <sendm.part.0+0x17e>
        struct Data *them = data->mailboxes[n].higher;
    434b:	4d 8b 86 70 01 00 00 	mov    0x170(%r14),%r8
    4352:	4d 01 e0             	add    %r12,%r8
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4355:	45 8b 48 20          	mov    0x20(%r8),%r9d
        struct Data *them = data->mailboxes[n].higher;
    4359:	49 8b 78 08          	mov    0x8(%r8),%rdi
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    435d:	41 83 f9 02          	cmp    $0x2,%r9d
    4361:	0f 84 31 01 00 00    	je     4498 <sendm.part.0+0x1a8>
        for (; them->messages_count < min;) {
    4367:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    436e:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    4375:	48 39 e9             	cmp    %rbp,%rcx
    4378:	0f 8d f0 00 00 00    	jge    446e <sendm.part.0+0x17e>
    437e:	49 8b 86 08 01 00 00 	mov    0x108(%r14),%rax
    4385:	48 39 e9             	cmp    %rbp,%rcx
    4388:	49 89 eb             	mov    %rbp,%r11
          them->messages[them->messages_count++] = data->message; 
    438b:	48 8b 17             	mov    (%rdi),%rdx
    438e:	41 0f 9c c5          	setl   %r13b
    4392:	49 29 cb             	sub    %rcx,%r11
    4395:	48 89 44 24 d0       	mov    %rax,-0x30(%rsp)
    439a:	49 8b 40 10          	mov    0x10(%r8),%rax
    439e:	49 8d 5b ff          	lea    -0x1(%r11),%rbx
    43a2:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    43a7:	48 89 44 24 d8       	mov    %rax,-0x28(%rsp)
    43ac:	48 83 fb 02          	cmp    $0x2,%rbx
    43b0:	0f 86 9a 01 00 00    	jbe    4550 <sendm.part.0+0x260>
    43b6:	45 84 ed             	test   %r13b,%r13b
    43b9:	0f 84 91 01 00 00    	je     4550 <sendm.part.0+0x260>
    43bf:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    43c7:	4a 8d 04 12          	lea    (%rdx,%r10,1),%rax
    43cb:	48 89 44 24 e0       	mov    %rax,-0x20(%rsp)
    43d0:	49 89 c3             	mov    %rax,%r11
    43d3:	48 8d 04 ea          	lea    (%rdx,%rbp,8),%rax
    43d7:	48 39 44 24 e8       	cmp    %rax,-0x18(%rsp)
    43dc:	0f 83 ce 00 00 00    	jae    44b0 <sendm.part.0+0x1c0>
    43e2:	4c 89 d8             	mov    %r11,%rax
    43e5:	4c 8b 5c 24 f0       	mov    -0x10(%rsp),%r11
    43ea:	48 89 ce             	mov    %rcx,%rsi
    43ed:	4c 39 d8             	cmp    %r11,%rax
    43f0:	0f 83 ba 00 00 00    	jae    44b0 <sendm.part.0+0x1c0>
    43f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4400:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    4407:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    440b:	48 83 c6 01          	add    $0x1,%rsi
    440f:	48 39 f5             	cmp    %rsi,%rbp
    4412:	7f ec                	jg     4400 <sendm.part.0+0x110>
    4414:	0f 1f 40 00          	nopl   0x0(%rax)
    4418:	31 f6                	xor    %esi,%esi
    441a:	45 84 ed             	test   %r13b,%r13b
    441d:	4c 8b 5c 24 d0       	mov    -0x30(%rsp),%r11
    4422:	48 0f 45 f3          	cmovne %rbx,%rsi
    4426:	4d 8d 5c 33 01       	lea    0x1(%r11,%rsi,1),%r11
    442b:	48 8d 4c 31 01       	lea    0x1(%rcx,%rsi,1),%rcx
    4430:	4d 89 9e 08 01 00 00 	mov    %r11,0x108(%r14)
    4437:	4c 8b 5c 24 d8       	mov    -0x28(%rsp),%r11
    443c:	4d 8d 5c 33 01       	lea    0x1(%r11,%rsi,1),%r11
    4441:	4d 89 58 10          	mov    %r11,0x10(%r8)
    4445:	48 89 8f 80 00 00 00 	mov    %rcx,0x80(%rdi)
    444c:	48 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%rcx
    4454:	bb 00 00 00 00       	mov    $0x0,%ebx
    4459:	48 0f 44 cb          	cmove  %rbx,%rcx
    445d:	4c 01 d2             	add    %r10,%rdx
    4460:	48 89 04 0a          	mov    %rax,(%rdx,%rcx,1)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4464:	41 83 f9 02          	cmp    $0x2,%r9d
    4468:	0f 84 c2 00 00 00    	je     4530 <sendm.part.0+0x240>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    446e:	8b 44 24 c8          	mov    -0x38(%rsp),%eax
    4472:	41 83 c7 01          	add    $0x1,%r15d
    4476:	49 83 c4 28          	add    $0x28,%r12
    447a:	41 39 c7             	cmp    %eax,%r15d
    447d:	0f 85 bd fe ff ff    	jne    4340 <sendm.part.0+0x50>
      asm volatile ("sfence" ::: "memory");
    4483:	0f ae f8             	sfence
}
    4486:	5b                   	pop    %rbx
    4487:	5d                   	pop    %rbp
    4488:	41 5c                	pop    %r12
    448a:	41 5d                	pop    %r13
    448c:	41 5e                	pop    %r14
    448e:	41 5f                	pop    %r15
    4490:	c3                   	ret
    4491:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4498:	8b 87 00 01 00 00    	mov    0x100(%rdi),%eax
    449e:	83 f8 01             	cmp    $0x1,%eax
    44a1:	0f 84 b9 00 00 00    	je     4560 <sendm.part.0+0x270>
        else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    44a7:	85 c0                	test   %eax,%eax
    44a9:	74 c3                	je     446e <sendm.part.0+0x17e>
    44ab:	e9 b7 fe ff ff       	jmp    4367 <sendm.part.0+0x77>
    44b0:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    44b5:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    44bc:	48 8b 74 24 e0       	mov    -0x20(%rsp),%rsi
    44c1:	49 d1 eb             	shr    %r11
    44c4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    44c9:	4c 89 dd             	mov    %r11,%rbp
    44cc:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    44d0:	48 c1 e5 04          	shl    $0x4,%rbp
    44d4:	49 89 eb             	mov    %rbp,%r11
    44d7:	48 01 f5             	add    %rsi,%rbp
    44da:	41 83 e3 10          	and    $0x10,%r11d
    44de:	74 11                	je     44f1 <sendm.part.0+0x201>
          them->messages[them->messages_count++] = data->message; 
    44e0:	0f 11 06             	movups %xmm0,(%rsi)
        for (; them->messages_count < min;) {
    44e3:	48 83 c6 10          	add    $0x10,%rsi
    44e7:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    44ec:	48 39 f5             	cmp    %rsi,%rbp
    44ef:	74 1a                	je     450b <sendm.part.0+0x21b>
    44f1:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
          them->messages[them->messages_count++] = data->message; 
    44f6:	0f 11 06             	movups %xmm0,(%rsi)
    44f9:	48 83 c6 20          	add    $0x20,%rsi
    44fd:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
        for (; them->messages_count < min;) {
    4501:	48 39 f5             	cmp    %rsi,%rbp
    4504:	75 f0                	jne    44f6 <sendm.part.0+0x206>
    4506:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    450b:	4c 89 de             	mov    %r11,%rsi
    450e:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    4512:	48 01 ce             	add    %rcx,%rsi
    4515:	41 83 e3 01          	and    $0x1,%r11d
    4519:	0f 84 f9 fe ff ff    	je     4418 <sendm.part.0+0x128>
          them->messages[them->messages_count++] = data->message; 
    451f:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    4526:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    452a:	e9 e9 fe ff ff       	jmp    4418 <sendm.part.0+0x128>
    452f:	90                   	nop
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4530:	83 bf 00 01 00 00 01 	cmpl   $0x1,0x100(%rdi)
    4537:	0f 85 31 ff ff ff    	jne    446e <sendm.part.0+0x17e>
          them->available = 0;
    453d:	c7 87 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdi)
    4547:	e9 22 ff ff ff       	jmp    446e <sendm.part.0+0x17e>
    454c:	0f 1f 40 00          	nopl   0x0(%rax)
          them->messages[them->messages_count++] = data->message; 
    4550:	48 89 ce             	mov    %rcx,%rsi
    4553:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    455b:	e9 a0 fe ff ff       	jmp    4400 <sendm.part.0+0x110>
        for (; them->messages_count < min;) {
    4560:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    4567:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    456e:	48 39 cd             	cmp    %rcx,%rbp
    4571:	0f 8f 07 fe ff ff    	jg     437e <sendm.part.0+0x8e>
    4577:	eb c4                	jmp    453d <sendm.part.0+0x24d>
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
    4595:	e8 76 df ff ff       	call   2510 <__ctype_tolower_loc@plt>
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
    45c8:	e8 43 de ff ff       	call   2410 <malloc@plt>
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
    45e8:	48 8d 3d f1 2e 00 00 	lea    0x2ef1(%rip),%rdi        # 74e0 <_IO_stdin_used+0x4e0>
    45ef:	e8 cc de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    45f4:	bf 01 00 00 00       	mov    $0x1,%edi
    45f9:	e8 a2 de ff ff       	call   24a0 <exit@plt>
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
    460d:	e8 4e dd ff ff       	call   2360 <strrchr@plt>
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
    4678:	e8 b3 dd ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    467d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4682:	84 db                	test   %bl,%bl
    4684:	74 24                	je     46aa <send_headers+0x6a>
        *str = (char)tolower(*str);
    4686:	e8 85 de ff ff       	call   2510 <__ctype_tolower_loc@plt>
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
    46af:	e8 5c dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    46b4:	48 85 c0             	test   %rax,%rax
    46b7:	0f 84 7e 04 00 00    	je     4b3b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    46bd:	66 0f 6f 05 eb 33 00 00 	movdqa 0x33eb(%rip),%xmm0        # 7ab0 <_IO_stdin_used+0xab0>
    iov[0].iov_base = zh_malloc(slen);
    46c5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    46c9:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    46ce:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    46d6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    46da:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    46dd:	e8 2e dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    46e2:	48 85 c0             	test   %rax,%rax
    46e5:	0f 84 50 04 00 00    	je     4b3b <send_headers+0x4fb>
    46eb:	66 0f 6f 05 cd 33 00 00 	movdqa 0x33cd(%rip),%xmm0        # 7ac0 <_IO_stdin_used+0xac0>
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
    4718:	e8 43 dc ff ff       	call   2360 <strrchr@plt>
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
    473d:	e8 6e dc ff ff       	call   23b0 <strcmp@plt>
    4742:	85 c0                	test   %eax,%eax
    4744:	75 20                	jne    4766 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4746:	66 0f 6f 05 82 33 00 00 	movdqa 0x3382(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    474e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4756:	66 0f 6f 05 82 33 00 00 	movdqa 0x3382(%rip),%xmm0        # 7ae0 <_IO_stdin_used+0xae0>
    475e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4766:	48 89 de             	mov    %rbx,%rsi
    4769:	48 8d 3d 52 29 00 00 	lea    0x2952(%rip),%rdi        # 70c2 <_IO_stdin_used+0xc2>
    4770:	e8 3b dc ff ff       	call   23b0 <strcmp@plt>
    4775:	85 c0                	test   %eax,%eax
    4777:	75 20                	jne    4799 <send_headers+0x159>
    4779:	66 0f 6f 05 4f 33 00 00 	movdqa 0x334f(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    4781:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4789:	66 0f 6f 05 4f 33 00 00 	movdqa 0x334f(%rip),%xmm0        # 7ae0 <_IO_stdin_used+0xae0>
    4791:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4799:	48 89 de             	mov    %rbx,%rsi
    479c:	48 8d 3d 24 29 00 00 	lea    0x2924(%rip),%rdi        # 70c7 <_IO_stdin_used+0xc7>
    47a3:	e8 08 dc ff ff       	call   23b0 <strcmp@plt>
    47a8:	85 c0                	test   %eax,%eax
    47aa:	0f 84 10 02 00 00    	je     49c0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    47b0:	48 89 de             	mov    %rbx,%rsi
    47b3:	48 8d 3d 11 29 00 00 	lea    0x2911(%rip),%rdi        # 70cb <_IO_stdin_used+0xcb>
    47ba:	e8 f1 db ff ff       	call   23b0 <strcmp@plt>
    47bf:	85 c0                	test   %eax,%eax
    47c1:	0f 84 a9 02 00 00    	je     4a70 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    47c7:	48 89 de             	mov    %rbx,%rsi
    47ca:	48 8d 3d fe 28 00 00 	lea    0x28fe(%rip),%rdi        # 70cf <_IO_stdin_used+0xcf>
    47d1:	e8 da db ff ff       	call   23b0 <strcmp@plt>
    47d6:	85 c0                	test   %eax,%eax
    47d8:	0f 84 6a 02 00 00    	je     4a48 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    47de:	48 89 de             	mov    %rbx,%rsi
    47e1:	48 8d 3d 2a 29 00 00 	lea    0x292a(%rip),%rdi        # 7112 <_IO_stdin_used+0x112>
    47e8:	e8 c3 db ff ff       	call   23b0 <strcmp@plt>
    47ed:	85 c0                	test   %eax,%eax
    47ef:	0f 84 2b 02 00 00    	je     4a20 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    47f5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    47f8:	0f 84 52 01 00 00    	je     4950 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    47fe:	48 89 de             	mov    %rbx,%rsi
    4801:	48 8d 3d cb 28 00 00 	lea    0x28cb(%rip),%rdi        # 70d3 <_IO_stdin_used+0xd3>
    4808:	e8 a3 db ff ff       	call   23b0 <strcmp@plt>
    480d:	85 c0                	test   %eax,%eax
    480f:	0f 84 ab 02 00 00    	je     4ac0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4815:	48 89 de             	mov    %rbx,%rsi
    4818:	48 8d 3d b8 28 00 00 	lea    0x28b8(%rip),%rdi        # 70d7 <_IO_stdin_used+0xd7>
    481f:	e8 8c db ff ff       	call   23b0 <strcmp@plt>
    4824:	85 c0                	test   %eax,%eax
    4826:	0f 84 6c 02 00 00    	je     4a98 <send_headers+0x458>
    slen = strlen(send_buffer);
    482c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4834:	4c 89 e7             	mov    %r12,%rdi
    4837:	e8 e4 da ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    483c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    483f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4842:	e8 c9 db ff ff       	call   2410 <malloc@plt>
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
    489a:	e8 81 dc ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    489f:	4c 89 e7             	mov    %r12,%rdi
    48a2:	e8 79 da ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    48a7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    48aa:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    48ad:	e8 5e db ff ff       	call   2410 <malloc@plt>
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
    4906:	e8 05 db ff ff       	call   2410 <malloc@plt>
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
    4964:	66 0f 6f 05 c4 31 00 00 	movdqa 0x31c4(%rip),%xmm0        # 7b30 <_IO_stdin_used+0xb30>
    496c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4976:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    497e:	66 0f 6f 05 ba 31 00 00 	movdqa 0x31ba(%rip),%xmm0        # 7b40 <_IO_stdin_used+0xb40>
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
    49c0:	66 0f 6f 05 08 31 00 00 	movdqa 0x3108(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    49c8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    49d0:	66 0f 6f 05 18 31 00 00 	movdqa 0x3118(%rip),%xmm0        # 7af0 <_IO_stdin_used+0xaf0>
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
    4a20:	66 0f 6f 05 e8 30 00 00 	movdqa 0x30e8(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4a28:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a30:	66 0f 6f 05 e8 30 00 00 	movdqa 0x30e8(%rip),%xmm0        # 7b20 <_IO_stdin_used+0xb20>
    4a38:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a40:	e9 b0 fd ff ff       	jmp    47f5 <send_headers+0x1b5>
    4a45:	0f 1f 00             	nopl   (%rax)
    4a48:	66 0f 6f 05 c0 30 00 00 	movdqa 0x30c0(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4a50:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a58:	66 0f 6f 05 c0 30 00 00 	movdqa 0x30c0(%rip),%xmm0        # 7b20 <_IO_stdin_used+0xb20>
    4a60:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a68:	e9 71 fd ff ff       	jmp    47de <send_headers+0x19e>
    4a6d:	0f 1f 00             	nopl   (%rax)
    4a70:	66 0f 6f 05 58 30 00 00 	movdqa 0x3058(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    4a78:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a80:	66 0f 6f 05 78 30 00 00 	movdqa 0x3078(%rip),%xmm0        # 7b00 <_IO_stdin_used+0xb00>
    4a88:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a90:	e9 32 fd ff ff       	jmp    47c7 <send_headers+0x187>
    4a95:	0f 1f 00             	nopl   (%rax)
    4a98:	66 0f 6f 05 70 30 00 00 	movdqa 0x3070(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4aa0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4aa8:	66 0f 6f 05 b0 30 00 00 	movdqa 0x30b0(%rip),%xmm0        # 7b60 <_IO_stdin_used+0xb60>
    4ab0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4ab8:	e9 6f fd ff ff       	jmp    482c <send_headers+0x1ec>
    4abd:	0f 1f 00             	nopl   (%rax)
    4ac0:	66 0f 6f 05 48 30 00 00 	movdqa 0x3048(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4ac8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ad0:	66 0f 6f 05 78 30 00 00 	movdqa 0x3078(%rip),%xmm0        # 7b50 <_IO_stdin_used+0xb50>
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
    4b4c:	48 8d 3d 8d 29 00 00 	lea    0x298d(%rip),%rdi        # 74e0 <_IO_stdin_used+0x4e0>
    4b53:	e8 68 d9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4b58:	bf 01 00 00 00       	mov    $0x1,%edi
    4b5d:	e8 3e d9 ff ff       	call   24a0 <exit@plt>
}
    4b62:	e8 c9 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
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
    4b8a:	e8 81 d8 ff ff       	call   2410 <malloc@plt>
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
    4b9e:	e8 dd d8 ff ff       	call   2480 <open@plt>
    4ba3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4ba6:	85 c0                	test   %eax,%eax
    4ba8:	0f 88 a8 d9 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4bae:	48 89 da             	mov    %rbx,%rdx
    4bb1:	48 89 ee             	mov    %rbp,%rsi
    4bb4:	89 c7                	mov    %eax,%edi
    4bb6:	e8 d5 d7 ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    4bbb:	48 98                	cltq
    4bbd:	48 39 d8             	cmp    %rbx,%rax
    4bc0:	7c 1e                	jl     4be0 <copy_file_contents+0x70>
    close(fd);
    4bc2:	44 89 e7             	mov    %r12d,%edi
    4bc5:	e8 a6 d7 ff ff       	call   2370 <close@plt>
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
    4bf8:	e8 c3 d8 ff ff       	call   24c0 <fwrite@plt>
    4bfd:	eb c3                	jmp    4bc2 <copy_file_contents+0x52>
    4bff:	48 8b 0d 1a 54 00 00 	mov    0x541a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c06:	ba 28 00 00 00       	mov    $0x28,%edx
    4c0b:	be 01 00 00 00       	mov    $0x1,%esi
    4c10:	48 8d 3d c9 28 00 00 	lea    0x28c9(%rip),%rdi        # 74e0 <_IO_stdin_used+0x4e0>
    4c17:	e8 a4 d8 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4c1c:	bf 01 00 00 00       	mov    $0x1,%edi
    4c21:	e8 7a d8 ff ff       	call   24a0 <exit@plt>
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
    4c59:	0f 82 03 d9 ff ff    	jb     2562 <add_write_request.cold>
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
    4cbf:	e8 7c d6 ff ff       	call   2340 <io_uring_submit@plt>
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
    4d01:	0f 82 6b d8 ff ff    	jb     2572 <add_read_request.cold>
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
    4d25:	e8 e6 d6 ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    4d2a:	be 01 00 00 00       	mov    $0x1,%esi
    4d2f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4d34:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4d37:	e8 64 d6 ff ff       	call   23a0 <calloc@plt>
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
    4d92:	e8 a9 d5 ff ff       	call   2340 <io_uring_submit@plt>
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
    4dca:	e8 41 d6 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4dcf:	48 85 c0             	test   %rax,%rax
    4dd2:	0f 84 dd 00 00 00    	je     4eb5 <_send_static_string_content+0x105>
    4dd8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    4ddb:	4c 89 ef             	mov    %r13,%rdi
    4dde:	e8 3d d5 ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4de3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    4dea:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    4dee:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4df1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4df4:	e8 17 d6 ff ff       	call   2410 <malloc@plt>
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
    4e13:	e8 c8 d5 ff ff       	call   23e0 <memcpy@plt>
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
    4e3a:	0f 82 3c d7 ff ff    	jb     257c <_send_static_string_content.cold>
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
    4ea7:	e9 94 d4 ff ff       	jmp    2340 <io_uring_submit@plt>
    4eac:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4eb0:	e9 7e ff ff ff       	jmp    4e33 <_send_static_string_content+0x83>
    4eb5:	48 8b 0d 64 51 00 00 	mov    0x5164(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4ebc:	ba 28 00 00 00       	mov    $0x28,%edx
    4ec1:	be 01 00 00 00       	mov    $0x1,%esi
    4ec6:	48 8d 3d 13 26 00 00 	lea    0x2613(%rip),%rdi        # 74e0 <_IO_stdin_used+0x4e0>
    4ecd:	e8 ee d5 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4ed2:	bf 01 00 00 00       	mov    $0x1,%edi
    4ed7:	e8 c4 d5 ff ff       	call   24a0 <exit@plt>
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
    4f4f:	e8 cc d3 ff ff       	call   2320 <strlen@plt>
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
    4f96:	e8 25 d4 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4f9b:	48 89 e6             	mov    %rsp,%rsi
    4f9e:	4c 89 f7             	mov    %r14,%rdi
    4fa1:	e8 2a d4 ff ff       	call   23d0 <stat@plt>
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
    4fe6:	e8 65 d4 ff ff       	call   2450 <__printf_chk@plt>
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
    504b:	e8 70 d3 ff ff       	call   23c0 <__memcpy_chk@plt>
    5050:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5055:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    505a:	48 8d 35 ab 20 00 00 	lea    0x20ab(%rip),%rsi        # 710c <_IO_stdin_used+0x10c>
    5061:	48 29 d9             	sub    %rbx,%rcx
    5064:	ba 0b 00 00 00       	mov    $0xb,%edx
    5069:	e8 52 d3 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    506e:	48 89 e6             	mov    %rsp,%rsi
    5071:	4c 89 f7             	mov    %r14,%rdi
    5074:	e8 57 d3 ff ff       	call   23d0 <stat@plt>
    5079:	83 f8 ff             	cmp    $0xffffffff,%eax
    507c:	0f 85 2d ff ff ff    	jne    4faf <handle_get_method+0x8f>
    5082:	4c 89 f2             	mov    %r14,%rdx
    5085:	48 89 e9             	mov    %rbp,%rcx
    5088:	48 8d 35 88 20 00 00 	lea    0x2088(%rip),%rsi        # 7117 <_IO_stdin_used+0x117>
    508f:	31 c0                	xor    %eax,%eax
    5091:	bf 01 00 00 00       	mov    $0x1,%edi
    5096:	e8 b5 d3 ff ff       	call   2450 <__printf_chk@plt>
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
    50bd:	e8 4e d3 ff ff       	call   2410 <malloc@plt>
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
    510d:	e8 3e d3 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    5112:	4c 89 ee             	mov    %r13,%rsi
    5115:	48 89 df             	mov    %rbx,%rdi
    5118:	e8 13 fb ff ff       	call   4c30 <add_write_request>
    511d:	e9 c9 fe ff ff       	jmp    4feb <handle_get_method+0xcb>
}
    5122:	e8 09 d2 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5127:	48 8b 0d f2 4e 00 00 	mov    0x4ef2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    512e:	ba 28 00 00 00       	mov    $0x28,%edx
    5133:	be 01 00 00 00       	mov    $0x1,%esi
    5138:	48 8d 3d a1 23 00 00 	lea    0x23a1(%rip),%rdi        # 74e0 <_IO_stdin_used+0x4e0>
    513f:	e8 7c d3 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5144:	bf 01 00 00 00       	mov    $0x1,%edi
    5149:	e8 52 d3 ff ff       	call   24a0 <exit@plt>
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
    5188:	e8 f3 d1 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    518d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    5191:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    5194:	84 db                	test   %bl,%bl
    5196:	74 1d                	je     51b5 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    5198:	e8 73 d3 ff ff       	call   2510 <__ctype_tolower_loc@plt>
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
    51bd:	e8 be d1 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    51c2:	48 8d 35 8b 1f 00 00 	lea    0x1f8b(%rip),%rsi        # 7154 <_IO_stdin_used+0x154>
    51c9:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    51cc:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    51cf:	e8 dc d1 ff ff       	call   23b0 <strcmp@plt>
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
    5216:	e8 15 d1 ff ff       	call   2330 <__stack_chk_fail@plt>
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
    5318:	e8 a3 d1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    531d:	bf 01 00 00 00       	mov    $0x1,%edi
    5322:	e8 79 d1 ff ff       	call   24a0 <exit@plt>
}
    5327:	e8 04 d0 ff ff       	call   2330 <__stack_chk_fail@plt>
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
    535e:	0f 82 28 d2 ff ff    	jb     258c <add_accept_request.cold>
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
    53ac:	e8 5f d0 ff ff       	call   2410 <malloc@plt>
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
    53c4:	e9 77 cf ff ff       	jmp    2340 <io_uring_submit@plt>
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
    54cc:	e8 1f cf ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    54d1:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    54d5:	31 f6                	xor    %esi,%esi
    54d7:	e8 04 d0 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    54dc:	31 d2                	xor    %edx,%edx
    54de:	be 01 00 00 00       	mov    $0x1,%esi
    54e3:	bf 02 00 00 00       	mov    $0x2,%edi
    54e8:	e8 43 d0 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    54ed:	83 f8 ff             	cmp    $0xffffffff,%eax
    54f0:	0f 84 d8 d0 ff ff    	je     25ce <io_thread.cold+0x38>
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
    5518:	e8 e3 cd ff ff       	call   2300 <setsockopt@plt>
    551d:	85 c0                	test   %eax,%eax
    551f:	0f 88 7d d0 ff ff    	js     25a2 <io_thread.cold+0xc>
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
    554b:	e8 10 cf ff ff       	call   2460 <bind@plt>
    5550:	85 c0                	test   %eax,%eax
    5552:	0f 88 82 d0 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5558:	be 0a 00 00 00       	mov    $0xa,%esi
    555d:	44 89 e7             	mov    %r12d,%edi
    5560:	e8 bb ce ff ff       	call   2420 <listen@plt>
    5565:	85 c0                	test   %eax,%eax
    5567:	0f 88 41 d0 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    556d:	ba db 18 00 00       	mov    $0x18db,%edx
    5572:	48 8d 35 24 1c 00 00 	lea    0x1c24(%rip),%rsi        # 719d <_IO_stdin_used+0x19d>
    5579:	bf 01 00 00 00       	mov    $0x1,%edi
    557e:	31 c0                	xor    %eax,%eax
    5580:	e8 cb ce ff ff       	call   2450 <__printf_chk@plt>
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
    55b9:	e8 e2 cd ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    55be:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    55c3:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    55c6:	e8 45 ce ff ff       	call   2410 <malloc@plt>
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
    560c:	0f 82 b2 cf ff ff    	jb     25c4 <io_thread.cold+0x2e>
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
    567b:	e8 c0 cc ff ff       	call   2340 <io_uring_submit@plt>
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
    56af:	e8 3c cc ff ff       	call   22f0 <puts@plt>
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
    5730:	e8 0b cd ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5735:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5738:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    573d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5741:	0f 84 e1 02 00 00    	je     5a28 <io_thread+0x658>
    5747:	48 8d 3d 8b 1a 00 00 	lea    0x1a8b(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    574e:	e8 9d cb ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5753:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5758:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    575b:	45 85 ff             	test   %r15d,%r15d
    575e:	0f 88 32 ce ff ff    	js     2596 <io_thread.cold>
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
    57b9:	e8 02 cb ff ff       	call   22c0 <free@plt>
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
    57f4:	0f 82 c0 cd ff ff    	jb     25ba <io_thread.cold+0x24>
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
    585f:	e8 dc ca ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5864:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5868:	0f 84 3a fe ff ff    	je     56a8 <io_thread+0x2d8>
    586e:	48 8d 3d 9d 19 00 00 	lea    0x199d(%rip),%rdi        # 7212 <_IO_stdin_used+0x212>
    5875:	e8 76 ca ff ff       	call   22f0 <puts@plt>
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
    58c7:	e8 24 ca ff ff       	call   22f0 <puts@plt>
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
    5914:	e8 a7 cb ff ff       	call   24c0 <fwrite@plt>
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
    5948:	e8 73 c9 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    594d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5952:	7f e4                	jg     5938 <io_thread+0x568>
              close(req->client_socket);
    5954:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5959:	e8 12 ca ff ff       	call   2370 <close@plt>
              free(req);
    595e:	4c 89 e7             	mov    %r12,%rdi
    5961:	e8 5a c9 ff ff       	call   22c0 <free@plt>
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
    59bf:	e8 fc c8 ff ff       	call   22c0 <free@plt>
              free(req);
    59c4:	4c 89 e7             	mov    %r12,%rdi
    59c7:	e8 f4 c8 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    59cc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    59d1:	e9 ed fd ff ff       	jmp    57c3 <io_thread+0x3f3>
    59d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    59e0:	48 8b 0d 39 46 00 00 	mov    0x4639(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    59e7:	ba 12 00 00 00       	mov    $0x12,%edx
    59ec:	be 01 00 00 00       	mov    $0x1,%esi
    59f1:	48 8d 3d 60 17 00 00 	lea    0x1760(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    59f8:	e8 c3 ca ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    59fd:	bf 01 00 00 00       	mov    $0x1,%edi
    5a02:	e8 99 ca ff ff       	call   24a0 <exit@plt>
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
    5a3e:	e8 ad c8 ff ff       	call   22f0 <puts@plt>
    5a43:	e9 26 fe ff ff       	jmp    586e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5a48:	f7 d8                	neg    %eax
    5a4a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5a4f:	89 c7                	mov    %eax,%edi
    5a51:	e8 aa ca ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5a56:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5a5b:	be 01 00 00 00       	mov    $0x1,%esi
    5a60:	48 8b 3d b9 45 00 00 	mov    0x45b9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5a67:	48 89 c1             	mov    %rax,%rcx
    5a6a:	48 8d 15 9f 1a 00 00 	lea    0x1a9f(%rip),%rdx        # 7510 <_IO_stdin_used+0x510>
    5a71:	31 c0                	xor    %eax,%eax
    5a73:	e8 58 ca ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5a78:	bf 01 00 00 00       	mov    $0x1,%edi
    5a7d:	e8 1e ca ff ff       	call   24a0 <exit@plt>
    5a82:	48 8b 0d 97 45 00 00 	mov    0x4597(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5a89:	ba 28 00 00 00       	mov    $0x28,%edx
    5a8e:	be 01 00 00 00       	mov    $0x1,%esi
    5a93:	48 8d 3d 46 1a 00 00 	lea    0x1a46(%rip),%rdi        # 74e0 <_IO_stdin_used+0x4e0>
    5a9a:	e8 21 ca ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5a9f:	bf 01 00 00 00       	mov    $0x1,%edi
    5aa4:	e8 f7 c9 ff ff       	call   24a0 <exit@plt>
}
    5aa9:	e8 82 c8 ff ff       	call   2330 <__stack_chk_fail@plt>
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
    5b54:	e8 b7 c7 ff ff       	call   2310 <clock_gettime@plt>
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
    5db6:	e8 55 c5 ff ff       	call   2310 <clock_gettime@plt>
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
    5e01:	e8 0a c5 ff ff       	call   2310 <clock_gettime@plt>
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
    5e37:	e8 d4 c4 ff ff       	call   2310 <clock_gettime@plt>
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
    5e6d:	e8 9e c4 ff ff       	call   2310 <clock_gettime@plt>
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
    5eae:	48 83 ec 08          	sub    $0x8,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5eb2:	48 63 87 40 01 00 00 	movslq 0x140(%rdi),%rax
    5eb9:	85 c0                	test   %eax,%eax
    5ebb:	0f 8e fd 00 00 00    	jle    5fbe <receive+0x11e>
    5ec1:	48 8b b7 70 01 00 00 	mov    0x170(%rdi),%rsi
    5ec8:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    5ecc:	48 89 fa             	mov    %rdi,%rdx
    5ecf:	4c 8d 2c c6          	lea    (%rsi,%rax,8),%r13
    5ed3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5ed8:	44 8b 66 20          	mov    0x20(%rsi),%r12d
    struct Data *me = data->mailboxes[n].lower;
    5edc:	48 8b 2e             	mov    (%rsi),%rbp
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5edf:	41 83 fc 02          	cmp    $0x2,%r12d
    5ee3:	0f 84 07 01 00 00    	je     5ff0 <receive+0x150>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5ee9:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    5ef0:	48 85 ff             	test   %rdi,%rdi
    5ef3:	0f 8e ad 00 00 00    	jle    5fa6 <receive+0x106>
      data->sends++;
    5ef9:	4c 8b 8a 78 01 00 00 	mov    0x178(%rdx),%r9
      data->n++;
    5f00:	4c 8b 82 08 01 00 00 	mov    0x108(%rdx),%r8
      data->mailboxes[n].received++;
    5f07:	31 c0                	xor    %eax,%eax
    5f09:	48 8b 4e 18          	mov    0x18(%rsi),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5f0d:	48 8b 5d 00          	mov    0x0(%rbp),%rbx
    5f11:	4d 8d 51 01          	lea    0x1(%r9),%r10
    5f15:	4c 63 5a 04          	movslq 0x4(%rdx),%r11
    5f19:	4d 8d 48 01          	lea    0x1(%r8),%r9
    5f1d:	4c 8d 41 01          	lea    0x1(%rcx),%r8
    5f21:	eb 0e                	jmp    5f31 <receive+0x91>
    5f23:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5f28:	48 83 c0 01          	add    $0x1,%rax
    5f2c:	48 39 f8             	cmp    %rdi,%rax
    5f2f:	7d 6f                	jge    5fa0 <receive+0x100>
      data->sends++;
    5f31:	49 8d 0c 02          	lea    (%r10,%rax,1),%rcx
    5f35:	48 89 8a 78 01 00 00 	mov    %rcx,0x178(%rdx)
      data->n++;
    5f3c:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    5f40:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5f47:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5f4b:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5f4f:	48 8b 0c c3          	mov    (%rbx,%rax,8),%rcx
    5f53:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5f57:	75 cf                	jne    5f28 <receive+0x88>
    5f59:	4c 8b b2 28 01 00 00 	mov    0x128(%rdx),%r14
    5f60:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    5f64:	4d 63 7e 08          	movslq 0x8(%r14),%r15
    5f68:	4c 39 f9             	cmp    %r15,%rcx
    5f6b:	75 bb                	jne    5f28 <receive+0x88>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    5f6d:	49 63 46 04          	movslq 0x4(%r14),%rax
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5f71:	bf 01 00 00 00       	mov    $0x1,%edi
    5f76:	ba 01 00 00 00       	mov    $0x1,%edx
    5f7b:	48 8d 35 b6 15 00 00 	lea    0x15b6(%rip),%rsi        # 7538 <_IO_stdin_used+0x538>
    5f82:	48 39 c8             	cmp    %rcx,%rax
    5f85:	0f 94 c1             	sete   %cl
    5f88:	31 c0                	xor    %eax,%eax
    5f8a:	0f b6 c9             	movzbl %cl,%ecx
    5f8d:	e8 be c4 ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5f92:	bf 01 00 00 00       	mov    $0x1,%edi
    5f97:	e8 04 c5 ff ff       	call   24a0 <exit@plt>
    5f9c:	0f 1f 40 00          	nopl   0x0(%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5fa0:	41 83 fc 02          	cmp    $0x2,%r12d
    5fa4:	74 32                	je     5fd8 <receive+0x138>
    me->messages_count = 0;
    5fa6:	48 c7 85 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rbp)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5fb1:	48 83 c6 28          	add    $0x28,%rsi
    5fb5:	49 39 f5             	cmp    %rsi,%r13
    5fb8:	0f 85 1a ff ff ff    	jne    5ed8 <receive+0x38>
  asm volatile ("sfence" ::: "memory");
    5fbe:	0f ae f8             	sfence
}
    5fc1:	48 83 c4 08          	add    $0x8,%rsp
    5fc5:	31 c0                	xor    %eax,%eax
    5fc7:	5b                   	pop    %rbx
    5fc8:	5d                   	pop    %rbp
    5fc9:	41 5c                	pop    %r12
    5fcb:	41 5d                	pop    %r13
    5fcd:	41 5e                	pop    %r14
    5fcf:	41 5f                	pop    %r15
    5fd1:	c3                   	ret
    5fd2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5fd8:	83 bd 00 01 00 00 01 	cmpl   $0x1,0x100(%rbp)
    5fdf:	75 c5                	jne    5fa6 <receive+0x106>
      me->available = 0;
    5fe1:	c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbp)
    5feb:	eb b9                	jmp    5fa6 <receive+0x106>
    5fed:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5ff0:	8b 85 00 01 00 00    	mov    0x100(%rbp),%eax
    5ff6:	83 f8 01             	cmp    $0x1,%eax
    5ff9:	74 09                	je     6004 <receive+0x164>
    else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 0) {
    5ffb:	85 c0                	test   %eax,%eax
    5ffd:	74 b2                	je     5fb1 <receive+0x111>
    5fff:	e9 e5 fe ff ff       	jmp    5ee9 <receive+0x49>
    for (int x = 0 ; x < me->messages_count ; x++) {
    6004:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    600b:	48 85 ff             	test   %rdi,%rdi
    600e:	0f 8f e5 fe ff ff    	jg     5ef9 <receive+0x59>
    6014:	eb cb                	jmp    5fe1 <receive+0x141>
    6016:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006020 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    6020:	f3 0f 1e fa          	endbr64
    6024:	41 57                	push   %r15
    6026:	41 56                	push   %r14
    6028:	41 55                	push   %r13
    602a:	41 54                	push   %r12
    602c:	55                   	push   %rbp
    602d:	53                   	push   %rbx
    602e:	48 89 fb             	mov    %rdi,%rbx
    6031:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    6035:	8b 47 04             	mov    0x4(%rdi),%eax
    6038:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    603e:	74 50                	je     6090 <barriered_work+0x70>
    receive(data);
    6040:	e8 5b fe ff ff       	call   5ea0 <receive>
    while (data->scheduled == 1) {
    6045:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    604c:	75 16                	jne    6064 <barriered_work+0x44>
    604e:	66 90                	xchg   %ax,%ax
      data->n++;
    6050:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    6058:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    605b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6062:	74 ec                	je     6050 <barriered_work+0x30>
  if (data->sending == 1) {
    6064:	83 bb 80 01 00 00 01 	cmpl   $0x1,0x180(%rbx)
    606b:	75 08                	jne    6075 <barriered_work+0x55>
    606d:	48 89 df             	mov    %rbx,%rdi
    6070:	e8 7b e2 ff ff       	call   42f0 <sendm.part.0>
  asm volatile ("sfence" ::: "memory");
    6075:	0f ae f8             	sfence
}
    6078:	48 83 c4 18          	add    $0x18,%rsp
    607c:	31 c0                	xor    %eax,%eax
    607e:	5b                   	pop    %rbx
    607f:	5d                   	pop    %rbp
    6080:	41 5c                	pop    %r12
    6082:	41 5d                	pop    %r13
    6084:	41 5e                	pop    %r14
    6086:	41 5f                	pop    %r15
    6088:	c3                   	ret
    6089:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      receive(data);
    6090:	e8 0b fe ff ff       	call   5ea0 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6095:	8b 8b 40 01 00 00    	mov    0x140(%rbx),%ecx
        int t = data->task_index;
    609b:	8b 43 04             	mov    0x4(%rbx),%eax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    609e:	85 c9                	test   %ecx,%ecx
    60a0:	0f 8e 75 01 00 00    	jle    621b <barriered_work+0x1fb>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    60a6:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    60ad:	4c 63 d0             	movslq %eax,%r10
              int next_task = abs((t + 1) % (data->thread_count));
    60b0:	83 c0 01             	add    $0x1,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    60b3:	49 c1 e2 09          	shl    $0x9,%r10
    60b7:	48 8b 72 20          	mov    0x20(%rdx),%rsi
              int next_task = abs((t + 1) % (data->thread_count));
    60bb:	99                   	cltd
    60bc:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    60c2:	4c 8d 66 38          	lea    0x38(%rsi),%r12
                 if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 0 && ((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available == 0) {
    60c6:	4d 89 e0             	mov    %r12,%r8
              int next_task = abs((t + 1) % (data->thread_count));
    60c9:	89 d0                	mov    %edx,%eax
    60cb:	f7 d8                	neg    %eax
    60cd:	0f 49 d0             	cmovns %eax,%edx
    60d0:	48 63 c1             	movslq %ecx,%rax
                 if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 0 && ((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available == 0) {
    60d3:	31 ff                	xor    %edi,%edi
    60d5:	4c 8d 1c 80          	lea    (%rax,%rax,4),%r11
              int next_task = abs((t + 1) % (data->thread_count));
    60d9:	4c 63 ca             	movslq %edx,%r9
    60dc:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
    60e0:	49 c1 e3 03          	shl    $0x3,%r11
    60e4:	48 c1 e2 06          	shl    $0x6,%rdx
                 if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 0 && ((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available == 0) {
    60e8:	49 c1 e1 09          	shl    $0x9,%r9
    60ec:	48 8d 6c 16 38       	lea    0x38(%rsi,%rdx,1),%rbp
    60f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    60f8:	49 8b 00             	mov    (%r8),%rax
    60fb:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    6100:	4c 89 e1             	mov    %r12,%rcx
    6103:	4d 89 d7             	mov    %r10,%r15
    6106:	4a 8b 84 10 70 01 00 00 	mov    0x170(%rax,%r10,1),%rax
    610e:	4a 8d 34 18          	lea    (%rax,%r11,1),%rsi
    6112:	e9 a1 00 00 00       	jmp    61b8 <barriered_work+0x198>
    6117:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
                 if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 0 && ((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available == 0) {
    6120:	44 8b b2 00 01 00 00 	mov    0x100(%rdx),%r14d
    6127:	45 85 f6             	test   %r14d,%r14d
    612a:	75 7c                	jne    61a8 <barriered_work+0x188>
    612c:	4c 8b 10             	mov    (%rax),%r10
    612f:	45 8b aa 00 01 00 00 	mov    0x100(%r10),%r13d
    6136:	45 85 ed             	test   %r13d,%r13d
    6139:	75 6d                	jne    61a8 <barriered_work+0x188>
    613b:	4c 8b 29             	mov    (%rcx),%r13
    613e:	4f 8b b4 0d 70 01 00 00 	mov    0x170(%r13,%r9,1),%r14
    6146:	49 01 fe             	add    %rdi,%r14
    6149:	4d 89 f5             	mov    %r14,%r13
    614c:	4d 8b 76 08          	mov    0x8(%r14),%r14
    6150:	45 8b 86 00 01 00 00 	mov    0x100(%r14),%r8d
    6157:	45 85 c0             	test   %r8d,%r8d
    615a:	75 4c                	jne    61a8 <barriered_work+0x188>
    615c:	4d 8b 45 00          	mov    0x0(%r13),%r8
    6160:	41 83 b8 00 01 00 00 00 	cmpl   $0x0,0x100(%r8)
    6168:	75 3e                	jne    61a8 <barriered_work+0x188>
                  data->thread->all_threads[y].tasks[t].mailboxes[b].lower = _c;
    616a:	66 49 0f 6e c6       	movq   %r14,%xmm0
    616f:	66 49 0f 6e e0       	movq   %r8,%xmm4
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = _a;
    6174:	66 49 0f 6e da       	movq   %r10,%xmm3
                  data->thread->all_threads[y].tasks[t].mailboxes[b].lower = _c;
    6179:	66 0f 6c c4          	punpcklqdq %xmm4,%xmm0
    617d:	0f 11 00             	movups %xmm0,(%rax)
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = _a;
    6180:	66 48 0f 6e c2       	movq   %rdx,%xmm0
    6185:	66 0f 6c c3          	punpcklqdq %xmm3,%xmm0
    6189:	41 0f 11 45 00       	movups %xmm0,0x0(%r13)
                  ((struct Data*)_a)->available = 1;
    618e:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
                  ((struct Data*)_c)->available = 1;
    6198:	41 c7 86 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r14)
    61a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    61a8:	48 83 c0 28          	add    $0x28,%rax
    61ac:	48 81 c1 c0 00 00 00 	add    $0xc0,%rcx
    61b3:	48 39 f0             	cmp    %rsi,%rax
    61b6:	74 47                	je     61ff <barriered_work+0x1df>
              if (kind == MAILBOX_FRIEND) {
    61b8:	83 78 20 01          	cmpl   $0x1,0x20(%rax)
                  void * _a = data->thread->all_threads[y].tasks[t].mailboxes[b].higher;
    61bc:	48 8b 50 08          	mov    0x8(%rax),%rdx
              if (kind == MAILBOX_FRIEND) {
    61c0:	0f 85 5a ff ff ff    	jne    6120 <barriered_work+0x100>
                  void * _b = data->thread->all_threads[y].tasks[t].mailboxes[b].lower;
    61c6:	66 48 0f 6e ca       	movq   %rdx,%xmm1
                  void * _c = data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher;
    61cb:	48 8b 11             	mov    (%rcx),%rdx
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    61ce:	48 83 c0 28          	add    $0x28,%rax
    61d2:	48 81 c1 c0 00 00 00 	add    $0xc0,%rcx
    61d9:	0f 16 48 d8          	movhps -0x28(%rax),%xmm1
                  void * _c = data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher;
    61dd:	4e 8b b4 0a 70 01 00 00 	mov    0x170(%rdx,%r9,1),%r14
    61e5:	49 01 fe             	add    %rdi,%r14
                  void * _d = data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower;
    61e8:	f3 41 0f 6f 06       	movdqu (%r14),%xmm0
    61ed:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
                  data->thread->all_threads[y].tasks[t].mailboxes[b].lower = _c;
    61f2:	0f 11 40 d8          	movups %xmm0,-0x28(%rax)
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = _a;
    61f6:	41 0f 11 0e          	movups %xmm1,(%r14)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    61fa:	48 39 f0             	cmp    %rsi,%rax
    61fd:	75 b9                	jne    61b8 <barriered_work+0x198>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    61ff:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    6204:	4d 89 fa             	mov    %r15,%r10
    6207:	48 83 c7 28          	add    $0x28,%rdi
    620b:	49 81 c0 c0 00 00 00 	add    $0xc0,%r8
    6212:	49 39 e8             	cmp    %rbp,%r8
    6215:	0f 85 dd fe ff ff    	jne    60f8 <barriered_work+0xd8>
      asm volatile ("sfence" ::: "memory");
    621b:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    621e:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6225:	31 ff                	xor    %edi,%edi
    6227:	48 c1 e6 05          	shl    $0x5,%rsi
    622b:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6232:	e8 d9 c0 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6237:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    623e:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    6245:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6249:	8b 72 10             	mov    0x10(%rdx),%esi
    624c:	8d 6e 01             	lea    0x1(%rsi),%ebp
    624f:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    6252:	75 55                	jne    62a9 <barriered_work+0x289>
    6254:	0f 1f 40 00          	nopl   0x0(%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6258:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    625f:	48 8b 40 18          	mov    0x18(%rax),%rax
    6263:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
      data->n++;
    6267:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    626f:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6273:	48 c1 e7 09          	shl    $0x9,%rdi
    6277:	48 03 78 38          	add    0x38(%rax),%rdi
    627b:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    6281:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6284:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    628b:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    6292:	74 c4                	je     6258 <barriered_work+0x238>
    if (modcount != data->thread->protected_state->modcount) {
    6294:	48 8b 40 48          	mov    0x48(%rax),%rax
    6298:	3b 68 10             	cmp    0x10(%rax),%ebp
    629b:	74 0c                	je     62a9 <barriered_work+0x289>
    629d:	48 8d 3d 81 0f 00 00 	lea    0xf81(%rip),%rdi        # 7225 <_IO_stdin_used+0x225>
    62a4:	e8 47 c0 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    62a9:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    62b0:	31 ff                	xor    %edi,%edi
    62b2:	48 c1 e6 05          	shl    $0x5,%rsi
    62b6:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    62bd:	48 83 c6 10          	add    $0x10,%rsi
    62c1:	e8 4a c0 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    62c6:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    62cd:	48 83 c0 01          	add    $0x1,%rax
    62d1:	48 99                	cqto
    62d3:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    62da:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    62e1:	e9 7e fd ff ff       	jmp    6064 <barriered_work+0x44>
    62e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000062f0 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    62f0:	f3 0f 1e fa          	endbr64
    62f4:	53                   	push   %rbx
    62f5:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    62f8:	e8 b3 f7 ff ff       	call   5ab0 <barriered_work_ingest>
  barriered_work(data);
    62fd:	48 89 df             	mov    %rbx,%rdi
}
    6300:	5b                   	pop    %rbx
  barriered_work(data);
    6301:	e9 1a fd ff ff       	jmp    6020 <barriered_work>
    6306:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006310 <sendm>:
int sendm(struct BarrierTask *data) {
    6310:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    6314:	83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%rdi)
    631b:	74 03                	je     6320 <sendm+0x10>
}
    631d:	31 c0                	xor    %eax,%eax
    631f:	c3                   	ret
int sendm(struct BarrierTask *data) {
    6320:	48 83 ec 08          	sub    $0x8,%rsp
    6324:	e8 c7 df ff ff       	call   42f0 <sendm.part.0>
}
    6329:	31 c0                	xor    %eax,%eax
    632b:	48 83 c4 08          	add    $0x8,%rsp
    632f:	c3                   	ret

0000000000006330 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6330:	f3 0f 1e fa          	endbr64
}
    6334:	31 c0                	xor    %eax,%eax
    6336:	c3                   	ret
    6337:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006340 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6340:	f3 0f 1e fa          	endbr64
    6344:	31 c0                	xor    %eax,%eax
    6346:	c3                   	ret
    6347:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006350 <after>:
int after(struct timespec left, struct timespec right) {
    6350:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6354:	31 c0                	xor    %eax,%eax
    6356:	48 39 d7             	cmp    %rdx,%rdi
    6359:	7e 08                	jle    6363 <after+0x13>
    635b:	31 c0                	xor    %eax,%eax
    635d:	48 39 ce             	cmp    %rcx,%rsi
    6360:	0f 9f c0             	setg   %al
}
    6363:	c3                   	ret
    6364:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    636f:	90                   	nop

0000000000006370 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6370:	f3 0f 1e fa          	endbr64
    6374:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6379:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    637e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6380:	48 39 d7             	cmp    %rdx,%rdi
    6383:	7f 18                	jg     639d <within+0x2d>
    6385:	4d 39 d8             	cmp    %r11,%r8
    6388:	0f 9e c2             	setle  %dl
    638b:	48 39 ce             	cmp    %rcx,%rsi
    638e:	0f 9e c0             	setle  %al
    6391:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6393:	31 c0                	xor    %eax,%eax
    6395:	4d 39 d1             	cmp    %r10,%r9
    6398:	0f 9e c0             	setle  %al
    639b:	21 d0                	and    %edx,%eax
}
    639d:	c3                   	ret
    639e:	66 90                	xchg   %ax,%ax

00000000000063a0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    63a0:	f3 0f 1e fa          	endbr64
    63a4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    63a9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    63ae:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    63b3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    63b8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    63bd:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    63c2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    63c7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    63cc:	48 39 fe             	cmp    %rdi,%rsi
    63cf:	7d 2f                	jge    6400 <overlap+0x60>
    63d1:	48 39 ca             	cmp    %rcx,%rdx
    63d4:	7d 62                	jge    6438 <overlap+0x98>
    63d6:	4d 39 da             	cmp    %r11,%r10
    63d9:	7d 0e                	jge    63e9 <overlap+0x49>
    return 1;
    63db:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    63e0:	4d 39 c1             	cmp    %r8,%r9
    63e3:	0f 8c 7f 00 00 00    	jl     6468 <overlap+0xc8>
  return 0;
    63e9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    63eb:	4d 39 c1             	cmp    %r8,%r9
    63ee:	7f 4c                	jg     643c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    63f0:	31 c0                	xor    %eax,%eax
    63f2:	4d 39 da             	cmp    %r11,%r10
    63f5:	0f 9e c0             	setle  %al
    63f8:	c3                   	ret
    63f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6400:	7e 4e                	jle    6450 <overlap+0xb0>
    6402:	48 39 ca             	cmp    %rcx,%rdx
    6405:	7f 39                	jg     6440 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6407:	75 31                	jne    643a <overlap+0x9a>
    6409:	4d 39 c1             	cmp    %r8,%r9
    640c:	7c 2c                	jl     643a <overlap+0x9a>
    return 1;
    640e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6413:	4d 39 da             	cmp    %r11,%r10
    6416:	7d 24                	jge    643c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6418:	48 39 ca             	cmp    %rcx,%rdx
    641b:	0f 94 c2             	sete   %dl
    641e:	48 39 fe             	cmp    %rdi,%rsi
    6421:	0f 94 c0             	sete   %al
    6424:	21 c2                	and    %eax,%edx
    6426:	31 c0                	xor    %eax,%eax
    6428:	4d 39 c1             	cmp    %r8,%r9
    642b:	0f 94 c0             	sete   %al
    642e:	21 d0                	and    %edx,%eax
    6430:	c3                   	ret
    6431:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6438:	74 af                	je     63e9 <overlap+0x49>
  return 0;
    643a:	31 c0                	xor    %eax,%eax
}
    643c:	c3                   	ret
    643d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6440:	4d 39 da             	cmp    %r11,%r10
    6443:	7e c4                	jle    6409 <overlap+0x69>
    return 1;
    6445:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    644a:	4d 39 c1             	cmp    %r8,%r9
    644d:	7e ba                	jle    6409 <overlap+0x69>
    644f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6450:	48 39 ca             	cmp    %rcx,%rdx
    6453:	7c 94                	jl     63e9 <overlap+0x49>
    6455:	4d 39 c1             	cmp    %r8,%r9
    6458:	7d b4                	jge    640e <overlap+0x6e>
    645a:	48 39 ca             	cmp    %rcx,%rdx
    645d:	74 91                	je     63f0 <overlap+0x50>
    645f:	eb d9                	jmp    643a <overlap+0x9a>
    6461:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6468:	c3                   	ret
    6469:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006470 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6470:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6474:	85 f6                	test   %esi,%esi
    6476:	0f 8e 44 03 00 00    	jle    67c0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    647c:	41 57                	push   %r15
    647e:	41 89 f7             	mov    %esi,%r15d
    6481:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6483:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6486:	41 55                	push   %r13
    6488:	41 54                	push   %r12
    648a:	55                   	push   %rbp
    648b:	53                   	push   %rbx
    648c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6490:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6494:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6499:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    649e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    64a1:	45 39 e6             	cmp    %r12d,%r14d
    64a4:	0f 84 4e 02 00 00    	je     66f8 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    64aa:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    64af:	8b 50 08             	mov    0x8(%rax),%edx
    64b2:	85 d2                	test   %edx,%edx
    64b4:	0f 8e 3e 02 00 00    	jle    66f8 <verify+0x288>
    64ba:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    64bf:	31 c9                	xor    %ecx,%ecx
    64c1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    64c6:	31 c0                	xor    %eax,%eax
    64c8:	44 89 f2             	mov    %r14d,%edx
    64cb:	bf 01 00 00 00       	mov    $0x1,%edi
    64d0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    64d5:	48 8d 35 59 0d 00 00 	lea    0xd59(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    64dc:	e8 6f bf ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    64e1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    64e6:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    64eb:	8b 40 08             	mov    0x8(%rax),%eax
    64ee:	85 c0                	test   %eax,%eax
    64f0:	0f 8e e6 01 00 00    	jle    66dc <verify+0x26c>
    64f6:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    64f9:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    64fe:	31 db                	xor    %ebx,%ebx
    6500:	48 c1 e0 09          	shl    $0x9,%rax
    6504:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6509:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    650e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6513:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6518:	4c 8b 20             	mov    (%rax),%r12
    651b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6520:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6525:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    652a:	49 89 de             	mov    %rbx,%r14
    652d:	48 8d 35 16 0d 00 00 	lea    0xd16(%rip),%rsi        # 724a <_IO_stdin_used+0x24a>
    6534:	49 c1 e6 09          	shl    $0x9,%r14
    6538:	bf 01 00 00 00       	mov    $0x1,%edi
    653d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6541:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    6549:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    654e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    6556:	31 c0                	xor    %eax,%eax
    6558:	e8 f3 be ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    655d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6562:	4c 8b 20             	mov    (%rax),%r12
    6565:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    656e:	0f 8e 47 01 00 00    	jle    66bb <verify+0x24b>
    6574:	4c 03 75 00          	add    0x0(%rbp),%r14
    6578:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    657d:	ba 01 00 00 00       	mov    $0x1,%edx
    6582:	4d 89 f5             	mov    %r14,%r13
    6585:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    658c:	4d 85 f6             	test   %r14,%r14
    658f:	0f 8e 21 01 00 00    	jle    66b6 <verify+0x246>
    6595:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6598:	48 89 d5             	mov    %rdx,%rbp
    659b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    65a0:	31 db                	xor    %ebx,%ebx
    65a2:	4d 89 f2             	mov    %r14,%r10
    65a5:	48 c1 e5 05          	shl    $0x5,%rbp
    65a9:	48 83 ed 20          	sub    $0x20,%rbp
    65ad:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    65b1:	49 89 ee             	mov    %rbp,%r14
    65b4:	48 89 dd             	mov    %rbx,%rbp
    65b7:	48 89 d3             	mov    %rdx,%rbx
    65ba:	eb 31                	jmp    65ed <verify+0x17d>
    65bc:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    65c0:	4c 39 c2             	cmp    %r8,%rdx
    65c3:	0f 8d 57 01 00 00    	jge    6720 <verify+0x2b0>
    65c9:	4c 39 df             	cmp    %r11,%rdi
    65cc:	7e 05                	jle    65d3 <verify+0x163>
    65ce:	49 39 c1             	cmp    %rax,%r9
    65d1:	7c 75                	jl     6648 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    65d3:	4c 39 df             	cmp    %r11,%rdi
    65d6:	0f 8d ab 01 00 00    	jge    6787 <verify+0x317>
    65dc:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    65e0:	48 83 c5 01          	add    $0x1,%rbp
    65e4:	49 39 ea             	cmp    %rbp,%r10
    65e7:	0f 8e a9 00 00 00    	jle    6696 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    65ed:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    65f4:	48 89 e8             	mov    %rbp,%rax
    65f7:	48 c1 e0 05          	shl    $0x5,%rax
    65fb:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    6602:	4c 01 f2             	add    %r14,%rdx
    6605:	48 8b 08             	mov    (%rax),%rcx
    6608:	48 8b 78 10          	mov    0x10(%rax),%rdi
    660c:	48 8b 32             	mov    (%rdx),%rsi
    660f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6613:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6617:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    661b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    661f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6623:	48 39 f1             	cmp    %rsi,%rcx
    6626:	7c 98                	jl     65c0 <verify+0x150>
    6628:	0f 8e 42 01 00 00    	jle    6770 <verify+0x300>
    662e:	4c 39 c2             	cmp    %r8,%rdx
    6631:	0f 8f f9 00 00 00    	jg     6730 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6637:	75 a7                	jne    65e0 <verify+0x170>
    6639:	4c 39 df             	cmp    %r11,%rdi
    663c:	7f a2                	jg     65e0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    663e:	49 39 c1             	cmp    %rax,%r9
    6641:	7c 9d                	jl     65e0 <verify+0x170>
    6643:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6648:	49 89 c1             	mov    %rax,%r9
    664b:	48 89 f9             	mov    %rdi,%rcx
    664e:	48 89 f2             	mov    %rsi,%rdx
    6651:	bf 01 00 00 00       	mov    $0x1,%edi
    6656:	48 8d 35 03 0f 00 00 	lea    0xf03(%rip),%rsi        # 7560 <_IO_stdin_used+0x560>
    665d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    665f:	48 83 c5 01          	add    $0x1,%rbp
    6663:	e8 e8 bd ff ff       	call   2450 <__printf_chk@plt>
    6668:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    666d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    6672:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6675:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    667a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6681:	4c 8b 20             	mov    (%rax),%r12
    6684:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6689:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    668d:	49 39 ea             	cmp    %rbp,%r10
    6690:	0f 8f 57 ff ff ff    	jg     65ed <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6696:	48 89 da             	mov    %rbx,%rdx
    6699:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    66a0:	7d 14                	jge    66b6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    66a2:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    66a9:	48 83 c2 01          	add    $0x1,%rdx
    66ad:	4d 85 f6             	test   %r14,%r14
    66b0:	0f 8f e2 fe ff ff    	jg     6598 <verify+0x128>
    66b6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    66bb:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    66c0:	48 83 c3 01          	add    $0x1,%rbx
    66c4:	39 58 08             	cmp    %ebx,0x8(%rax)
    66c7:	0f 8f 53 fe ff ff    	jg     6520 <verify+0xb0>
    66cd:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    66d2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    66d7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    66dc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    66e1:	48 83 c1 01          	add    $0x1,%rcx
    66e5:	39 48 08             	cmp    %ecx,0x8(%rax)
    66e8:	0f 8f d8 fd ff ff    	jg     64c6 <verify+0x56>
    66ee:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    66f3:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    66f8:	48 81 44 24 10 c0 00 00 00 	addq   $0xc0,0x10(%rsp)
    6701:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6706:	41 39 c7             	cmp    %eax,%r15d
    6709:	0f 84 86 00 00 00    	je     6795 <verify+0x325>
    670f:	41 89 c4             	mov    %eax,%r12d
    6712:	e9 8a fd ff ff       	jmp    64a1 <verify+0x31>
    6717:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6720:	0f 85 ba fe ff ff    	jne    65e0 <verify+0x170>
    6726:	e9 a8 fe ff ff       	jmp    65d3 <verify+0x163>
    672b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6730:	49 39 c1             	cmp    %rax,%r9
    6733:	7e 09                	jle    673e <verify+0x2ce>
    6735:	4c 39 df             	cmp    %r11,%rdi
    6738:	0f 8c 0a ff ff ff    	jl     6648 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    673e:	4c 39 df             	cmp    %r11,%rdi
    6741:	0f 8f 99 fe ff ff    	jg     65e0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6747:	49 39 c1             	cmp    %rax,%r9
    674a:	0f 8d f8 fe ff ff    	jge    6648 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6750:	48 39 f1             	cmp    %rsi,%rcx
    6753:	0f 85 87 fe ff ff    	jne    65e0 <verify+0x170>
    6759:	4c 39 c2             	cmp    %r8,%rdx
    675c:	0f 85 7e fe ff ff    	jne    65e0 <verify+0x170>
    6762:	4c 39 df             	cmp    %r11,%rdi
    6765:	0f 84 dd fe ff ff    	je     6648 <verify+0x1d8>
    676b:	e9 70 fe ff ff       	jmp    65e0 <verify+0x170>
    6770:	4c 39 c2             	cmp    %r8,%rdx
    6773:	0f 8c 5a fe ff ff    	jl     65d3 <verify+0x163>
    6779:	4c 39 df             	cmp    %r11,%rdi
    677c:	7e c9                	jle    6747 <verify+0x2d7>
    677e:	4c 39 c2             	cmp    %r8,%rdx
    6781:	0f 85 59 fe ff ff    	jne    65e0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6787:	49 39 c1             	cmp    %rax,%r9
    678a:	0f 8f 50 fe ff ff    	jg     65e0 <verify+0x170>
    6790:	e9 b3 fe ff ff       	jmp    6648 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    6795:	48 81 44 24 18 c0 00 00 00 	addq   $0xc0,0x18(%rsp)
    679e:	41 8d 46 01          	lea    0x1(%r14),%eax
    67a2:	45 39 e6             	cmp    %r12d,%r14d
    67a5:	74 08                	je     67af <verify+0x33f>
    67a7:	41 89 c6             	mov    %eax,%r14d
    67aa:	e9 ea fc ff ff       	jmp    6499 <verify+0x29>
}
    67af:	48 83 c4 58          	add    $0x58,%rsp
    67b3:	31 c0                	xor    %eax,%eax
    67b5:	5b                   	pop    %rbx
    67b6:	5d                   	pop    %rbp
    67b7:	41 5c                	pop    %r12
    67b9:	41 5d                	pop    %r13
    67bb:	41 5e                	pop    %r14
    67bd:	41 5f                	pop    %r15
    67bf:	c3                   	ret
    67c0:	31 c0                	xor    %eax,%eax
    67c2:	c3                   	ret

Disassembly of section .fini:

00000000000067c4 <_fini>:
    67c4:	f3 0f 1e fa          	endbr64
    67c8:	48 83 ec 08          	sub    $0x8,%rsp
    67cc:	48 83 c4 08          	add    $0x8,%rsp
    67d0:	c3                   	ret
