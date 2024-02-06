
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
    25f6:	48 8d 3d 1b 50 00 00 	lea    0x501b(%rip),%rdi        # 7618 <_IO_stdin_used+0x618>
    25fd:	41 56                	push   %r14
    25ff:	41 55                	push   %r13
    2601:	41 54                	push   %r12
    2603:	55                   	push   %rbp
    2604:	53                   	push   %rbx
    2605:	48 81 ec c8 00 00 00 	sub    $0xc8,%rsp
    260c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2615:	48 89 84 24 b8 00 00 00 	mov    %rax,0xb8(%rsp)
    261d:	48 8d 05 3c 17 00 00 	lea    0x173c(%rip),%rax        # 3d60 <barriered_reset>
    2624:	66 48 0f 6e d8       	movq   %rax,%xmm3
    2629:	0f 16 1d 48 76 00 00 	movhps 0x7648(%rip),%xmm3        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    2630:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    2638:	e8 b3 fc ff ff       	call   22f0 <puts@plt>
    263d:	bf 0a 00 00 00       	mov    $0xa,%edi
    2642:	e8 89 fc ff ff       	call   22d0 <putchar@plt>
    2647:	ba 01 00 00 00       	mov    $0x1,%edx
    264c:	48 8d 35 00 4c 00 00 	lea    0x4c00(%rip),%rsi        # 7253 <_IO_stdin_used+0x253>
    2653:	31 c0                	xor    %eax,%eax
    2655:	bf 01 00 00 00       	mov    $0x1,%edi
    265a:	e8 f1 fd ff ff       	call   2450 <__printf_chk@plt>
    265f:	ba 04 00 00 00       	mov    $0x4,%edx
    2664:	48 8d 35 f8 4b 00 00 	lea    0x4bf8(%rip),%rsi        # 7263 <_IO_stdin_used+0x263>
    266b:	31 c0                	xor    %eax,%eax
    266d:	bf 01 00 00 00       	mov    $0x1,%edi
    2672:	e8 d9 fd ff ff       	call   2450 <__printf_chk@plt>
    2677:	ba 02 00 00 00       	mov    $0x2,%edx
    267c:	48 8d 35 f5 4b 00 00 	lea    0x4bf5(%rip),%rsi        # 7278 <_IO_stdin_used+0x278>
    2683:	31 c0                	xor    %eax,%eax
    2685:	bf 01 00 00 00       	mov    $0x1,%edi
    268a:	e8 c1 fd ff ff       	call   2450 <__printf_chk@plt>
    268f:	ba 02 00 00 00       	mov    $0x2,%edx
    2694:	48 8d 35 ed 4b 00 00 	lea    0x4bed(%rip),%rsi        # 7288 <_IO_stdin_used+0x288>
    269b:	31 c0                	xor    %eax,%eax
    269d:	bf 01 00 00 00       	mov    $0x1,%edi
    26a2:	e8 a9 fd ff ff       	call   2450 <__printf_chk@plt>
    26a7:	48 8d 3d f0 4b 00 00 	lea    0x4bf0(%rip),%rdi        # 729e <_IO_stdin_used+0x29e>
    26ae:	e8 3d fc ff ff       	call   22f0 <puts@plt>
    26b3:	ba 02 00 00 00       	mov    $0x2,%edx
    26b8:	48 8d 35 fb 4b 00 00 	lea    0x4bfb(%rip),%rsi        # 72ba <_IO_stdin_used+0x2ba>
    26bf:	31 c0                	xor    %eax,%eax
    26c1:	bf 01 00 00 00       	mov    $0x1,%edi
    26c6:	e8 85 fd ff ff       	call   2450 <__printf_chk@plt>
    26cb:	ba 08 00 00 00       	mov    $0x8,%edx
    26d0:	48 8d 35 fd 4b 00 00 	lea    0x4bfd(%rip),%rsi        # 72d4 <_IO_stdin_used+0x2d4>
    26d7:	31 c0                	xor    %eax,%eax
    26d9:	bf 01 00 00 00       	mov    $0x1,%edi
    26de:	e8 6d fd ff ff       	call   2450 <__printf_chk@plt>
    26e3:	ba 01 00 00 00       	mov    $0x1,%edx
    26e8:	48 8d 35 f9 4b 00 00 	lea    0x4bf9(%rip),%rsi        # 72e8 <_IO_stdin_used+0x2e8>
    26ef:	31 c0                	xor    %eax,%eax
    26f1:	bf 01 00 00 00       	mov    $0x1,%edi
    26f6:	e8 55 fd ff ff       	call   2450 <__printf_chk@plt>
    26fb:	ba 01 00 00 00       	mov    $0x1,%edx
    2700:	48 8d 35 f2 4b 00 00 	lea    0x4bf2(%rip),%rsi        # 72f9 <_IO_stdin_used+0x2f9>
    2707:	31 c0                	xor    %eax,%eax
    2709:	bf 01 00 00 00       	mov    $0x1,%edi
    270e:	e8 3d fd ff ff       	call   2450 <__printf_chk@plt>
    2713:	ba 02 00 00 00       	mov    $0x2,%edx
    2718:	48 8d 35 f2 4b 00 00 	lea    0x4bf2(%rip),%rsi        # 7311 <_IO_stdin_used+0x311>
    271f:	31 c0                	xor    %eax,%eax
    2721:	bf 01 00 00 00       	mov    $0x1,%edi
    2726:	e8 25 fd ff ff       	call   2450 <__printf_chk@plt>
    272b:	ba 01 00 00 00       	mov    $0x1,%edx
    2730:	48 8d 35 49 4f 00 00 	lea    0x4f49(%rip),%rsi        # 7680 <_IO_stdin_used+0x680>
    2737:	31 c0                	xor    %eax,%eax
    2739:	bf 01 00 00 00       	mov    $0x1,%edi
    273e:	e8 0d fd ff ff       	call   2450 <__printf_chk@plt>
    2743:	ba 01 00 00 00       	mov    $0x1,%edx
    2748:	48 8d 35 61 4f 00 00 	lea    0x4f61(%rip),%rsi        # 76b0 <_IO_stdin_used+0x6b0>
    274f:	31 c0                	xor    %eax,%eax
    2751:	bf 01 00 00 00       	mov    $0x1,%edi
    2756:	e8 f5 fc ff ff       	call   2450 <__printf_chk@plt>
    275b:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2760:	48 8d 35 c6 4b 00 00 	lea    0x4bc6(%rip),%rsi        # 732d <_IO_stdin_used+0x32d>
    2767:	31 c0                	xor    %eax,%eax
    2769:	bf 01 00 00 00       	mov    $0x1,%edi
    276e:	e8 dd fc ff ff       	call   2450 <__printf_chk@plt>
    2773:	ba 05 00 00 00       	mov    $0x5,%edx
    2778:	48 8d 35 c8 4b 00 00 	lea    0x4bc8(%rip),%rsi        # 7347 <_IO_stdin_used+0x347>
    277f:	31 c0                	xor    %eax,%eax
    2781:	bf 01 00 00 00       	mov    $0x1,%edi
    2786:	e8 c5 fc ff ff       	call   2450 <__printf_chk@plt>
    278b:	48 8d 3d 5d 49 00 00 	lea    0x495d(%rip),%rdi        # 70ef <_IO_stdin_used+0xef>
    2792:	e8 59 fb ff ff       	call   22f0 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2797:	be 18 00 00 00       	mov    $0x18,%esi
    279c:	bf 02 00 00 00       	mov    $0x2,%edi
    27a1:	e8 fa fb ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27a6:	be c0 00 00 00       	mov    $0xc0,%esi
    27ab:	bf 08 00 00 00       	mov    $0x8,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    27b0:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27b5:	e8 e6 fb ff ff       	call   23a0 <calloc@plt>
    27ba:	ba 04 00 00 00       	mov    $0x4,%edx
    27bf:	bf 01 00 00 00       	mov    $0x1,%edi
    27c4:	48 8d 35 90 4b 00 00 	lea    0x4b90(%rip),%rsi        # 735b <_IO_stdin_used+0x35b>
    27cb:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    27d0:	31 c0                	xor    %eax,%eax
    27d2:	e8 79 fc ff ff       	call   2450 <__printf_chk@plt>
    27d7:	ba 08 00 00 00       	mov    $0x8,%edx
    27dc:	48 8d 35 8e 4b 00 00 	lea    0x4b8e(%rip),%rsi        # 7371 <_IO_stdin_used+0x371>
    27e3:	31 c0                	xor    %eax,%eax
    27e5:	bf 01 00 00 00       	mov    $0x1,%edi
    27ea:	e8 61 fc ff ff       	call   2450 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    27ef:	be 10 00 00 00       	mov    $0x10,%esi
    27f4:	bf 08 00 00 00       	mov    $0x8,%edi
    27f9:	e8 a2 fb ff ff       	call   23a0 <calloc@plt>
    27fe:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    2803:	49 89 c6             	mov    %rax,%r14
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    2806:	48 8d 98 80 00 00 00 	lea    0x80(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    280d:	49 89 c5             	mov    %rax,%r13
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2810:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    2815:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    281d:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2822:	49 83 c5 10          	add    $0x10,%r13
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2826:	e8 75 fb ff ff       	call   23a0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    282b:	be 20 00 00 00       	mov    $0x20,%esi
    2830:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2835:	49 89 45 f8          	mov    %rax,-0x8(%r13)
    2839:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
    283c:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2846:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2850:	e8 4b fb ff ff       	call   23a0 <calloc@plt>
    2855:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    285c:	49 39 dd             	cmp    %rbx,%r13
    285f:	75 af                	jne    2810 <main+0x220>
    2861:	48 8b 74 24 58       	mov    0x58(%rsp),%rsi
    2866:	ba 01 00 00 00       	mov    $0x1,%edx
    286b:	45 31 ff             	xor    %r15d,%r15d
    286e:	4c 89 f3             	mov    %r14,%rbx
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
    2871:	c7 44 24 50 00 00 00 00 	movl   $0x0,0x50(%rsp)
  int curcpu = 0;
    2879:	c7 44 24 48 00 00 00 00 	movl   $0x0,0x48(%rsp)
    2881:	4d 89 f9             	mov    %r15,%r9
    2884:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    2889:	44 89 7c 24 38       	mov    %r15d,0x38(%rsp)
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    288e:	49 f7 d9             	neg    %r9
    2891:	48 89 b4 24 90 00 00 00 	mov    %rsi,0x90(%rsp)
    2899:	41 81 e1 80 01 00 00 	and    $0x180,%r9d
    28a0:	48 89 9c 24 a8 00 00 00 	mov    %rbx,0xa8(%rsp)
    28a8:	49 01 c1             	add    %rax,%r9
    28ab:	48 63 44 24 50       	movslq 0x50(%rsp),%rax
    28b0:	48 c1 e0 04          	shl    $0x4,%rax
    28b4:	4c 8d 2c 03          	lea    (%rbx,%rax,1),%r13
    28b8:	8d 42 fe             	lea    -0x2(%rdx),%eax
    28bb:	89 d3                	mov    %edx,%ebx
    28bd:	89 04 24             	mov    %eax,(%rsp)
    28c0:	44 8b 04 24          	mov    (%rsp),%r8d
    28c4:	8b 54 24 38          	mov    0x38(%rsp),%edx
    28c8:	bf 01 00 00 00       	mov    $0x1,%edi
    28cd:	31 c0                	xor    %eax,%eax
    28cf:	48 8d 35 02 4e 00 00 	lea    0x4e02(%rip),%rsi        # 76d8 <_IO_stdin_used+0x6d8>
    28d6:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      int x = (k * threads_per_group) + d;
    28db:	44 89 44 24 60       	mov    %r8d,0x60(%rsp)
    28e0:	45 89 c6             	mov    %r8d,%r14d
    28e3:	41 83 c0 01          	add    $0x1,%r8d
    28e7:	44 89 c1             	mov    %r8d,%ecx
    28ea:	44 89 04 24          	mov    %r8d,(%rsp)
    28ee:	e8 5d fb ff ff       	call   2450 <__printf_chk@plt>
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    28f3:	be 08 00 00 00       	mov    $0x8,%esi
    28f8:	bf 02 00 00 00       	mov    $0x2,%edi
    28fd:	e8 9e fa ff ff       	call   23a0 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2902:	be 80 00 00 00       	mov    $0x80,%esi
    2907:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    290c:	48 89 c5             	mov    %rax,%rbp
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    290f:	e8 8c fa ff ff       	call   23a0 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2914:	44 8b 04 24          	mov    (%rsp),%r8d
    2918:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    291d:	49 89 c4             	mov    %rax,%r12
      if (x % 2 == 1) {
    2920:	41 83 e0 01          	and    $0x1,%r8d
    2924:	44 89 44 24 40       	mov    %r8d,0x40(%rsp)
    2929:	0f 84 5b 07 00 00    	je     308a <main+0xa9a>
        other = abs(x - 1) % total_threads;
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    292f:	44 89 f0             	mov    %r14d,%eax
    2932:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
        other = abs(x - 1) % total_threads;
    2937:	44 89 f1             	mov    %r14d,%ecx
        my_thread_data[1] = &thread_data[x]; 
    293a:	4c 89 ca             	mov    %r9,%rdx
        my_thread_data[0] = &thread_data[other]; 
    293d:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    2941:	48 c1 e0 06          	shl    $0x6,%rax
    2945:	48 01 f8             	add    %rdi,%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2948:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
    294c:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    2951:	48 8b bc 24 90 00 00 00 	mov    0x90(%rsp),%rdi
    2959:	44 8b 34 24          	mov    (%rsp),%r14d
        thread_data[x].thread_index = 1;
    295d:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2961:	48 8d 35 a0 4d 00 00 	lea    0x4da0(%rip),%rsi        # 7708 <_IO_stdin_used+0x708>
    2968:	48 89 55 08          	mov    %rdx,0x8(%rbp)
        thread_data[x].protected_state = &protected_state[k];
    296c:	49 89 79 48          	mov    %rdi,0x48(%r9)
    2970:	44 89 f2             	mov    %r14d,%edx
    2973:	bf 01 00 00 00       	mov    $0x1,%edi
    2978:	48 89 45 00          	mov    %rax,0x0(%rbp)
    297c:	31 c0                	xor    %eax,%eax
    297e:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    2983:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2987:	e8 c4 fa ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].other = other;
    298c:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2990:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    2995:	31 c0                	xor    %eax,%eax
    2997:	44 89 f2             	mov    %r14d,%edx
    299a:	48 8d 35 97 4d 00 00 	lea    0x4d97(%rip),%rsi        # 7738 <_IO_stdin_used+0x738>
    29a1:	bf 01 00 00 00       	mov    $0x1,%edi
    29a6:	41 89 89 b8 00 00 00 	mov    %ecx,0xb8(%r9)
    29ad:	8b 4c 24 48          	mov    0x48(%rsp),%ecx
    29b1:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    29b6:	e8 95 fa ff ff       	call   2450 <__printf_chk@plt>
        if (x < thread_count) {
    29bb:	41 83 fe 01          	cmp    $0x1,%r14d
    29bf:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    29c4:	0f 8f ea 06 00 00    	jg     30b4 <main+0xac4>
          CPU_SET(curcpu, sendercpu);
    29ca:	48 63 44 24 48       	movslq 0x48(%rsp),%rax
    29cf:	48 89 c7             	mov    %rax,%rdi
    29d2:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    29d8:	77 12                	ja     29ec <main+0x3fc>
    29da:	48 c1 e8 06          	shr    $0x6,%rax
    29de:	ba 01 00 00 00       	mov    $0x1,%edx
    29e3:	89 f9                	mov    %edi,%ecx
    29e5:	48 d3 e2             	shl    %cl,%rdx
    29e8:	49 09 14 c4          	or     %rdx,(%r12,%rax,8)
          curcpu += 2;
    29ec:	83 44 24 48 02       	addl   $0x2,0x48(%rsp)
      thread_data[x].real_thread_index = x;
    29f1:	8b 04 24             	mov    (%rsp),%eax
      thread_data[x].threads = my_thread_data;
    29f4:	49 89 69 18          	mov    %rbp,0x18(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    29f8:	be 10 00 00 00       	mov    $0x10,%esi
    29fd:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].kind = KERNEL_THREAD;
    2a02:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a09:	31 ed                	xor    %ebp,%ebp
      thread_data[x].real_thread_index = x;
    2a0b:	41 89 41 08          	mov    %eax,0x8(%r9)
      thread_data[x].all_threads = thread_data;
    2a0f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
      thread_data[x].cpu_set = sendercpu;
    2a14:	4d 89 a1 b0 00 00 00 	mov    %r12,0xb0(%r9)
      thread_data[x].all_threads = thread_data;
    2a1b:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].thread_count = 2;
    2a1f:	48 8b 05 3a 52 00 00 	mov    0x523a(%rip),%rax        # 7c60 <_IO_stdin_used+0xc60>
      thread_data[x].task_count = total_barrier_count;
    2a26:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].thread_count = 2;
    2a2e:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].task_count = total_barrier_count;
    2a32:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a37:	e8 64 f9 ff ff       	call   23a0 <calloc@plt>
    2a3c:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a41:	be 10 00 00 00       	mov    $0x10,%esi
    2a46:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a4b:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a4f:	e8 4c f9 ff ff       	call   23a0 <calloc@plt>
    2a54:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a59:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2a5e:	66 0f 6f 2d ca 51 00 00 	movdqa 0x51ca(%rip),%xmm5        # 7c30 <_IO_stdin_used+0xc30>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a66:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a6b:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2a6f:	41 0f 11 a9 80 00 00 00 	movups %xmm5,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a77:	e8 24 f9 ff ff       	call   23a0 <calloc@plt>
    2a7c:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a81:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_timestamp_count = 0;
    2a86:	66 0f 6f 35 a2 51 00 00 	movdqa 0x51a2(%rip),%xmm6        # 7c30 <_IO_stdin_used+0xc30>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a8e:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a93:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2a9a:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2aa2:	e8 f9 f8 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks = barriers;
    2aa7:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
              data[0].messages_count = 0;
    2aac:	4c 89 ac 24 98 00 00 00 	mov    %r13,0x98(%rsp)
    2ab4:	89 9c 24 a4 00 00 00 	mov    %ebx,0xa4(%rsp)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2abb:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks = barriers;
    2abe:	49 89 41 38          	mov    %rax,0x38(%r9)
              data[0].messages_count = 0;
    2ac2:	4c 89 4c 24 30       	mov    %r9,0x30(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2ac7:	48 63 c5             	movslq %ebp,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2aca:	be 48 00 00 00       	mov    $0x48,%esi
    2acf:	bf 04 00 00 00       	mov    $0x4,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ad4:	45 31 ed             	xor    %r13d,%r13d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2ad7:	48 89 c3             	mov    %rax,%rbx
    2ada:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2adf:	48 8d 05 3a 12 00 00 	lea    0x123a(%rip),%rax        # 3d20 <do_protected_write>
    2ae6:	48 c1 e3 09          	shl    $0x9,%rbx
    2aea:	4c 8d 24 1a          	lea    (%rdx,%rbx,1),%r12
    2aee:	49 89 84 24 20 01 00 00 	mov    %rax,0x120(%r12)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2af6:	e8 a5 f8 ff ff       	call   23a0 <calloc@plt>
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2afb:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2b00:	49 89 84 24 70 01 00 00 	mov    %rax,0x170(%r12)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2b08:	49 89 c6             	mov    %rax,%r14
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2b0b:	49 89 c4             	mov    %rax,%r12
    2b0e:	8b 44 24 40          	mov    0x40(%rsp),%eax
    2b12:	85 c0                	test   %eax,%eax
    2b14:	0f 84 9e 03 00 00    	je     2eb8 <main+0x8c8>
            int group_of = b / threads_per_group;
    2b1a:	44 89 eb             	mov    %r13d,%ebx
    2b1d:	31 c0                	xor    %eax,%eax
    2b1f:	44 89 ea             	mov    %r13d,%edx
    2b22:	bf 01 00 00 00       	mov    $0x1,%edi
    2b27:	d1 fb                	sar    %ebx
    2b29:	48 8d 35 5b 48 00 00 	lea    0x485b(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
    2b30:	89 d9                	mov    %ebx,%ecx
    2b32:	e8 19 f9 ff ff       	call   2450 <__printf_chk@plt>
            if (k == group_of) {
    2b37:	44 39 fb             	cmp    %r15d,%ebx
    2b3a:	0f 84 b1 03 00 00    	je     2ef1 <main+0x901>
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2b40:	41 83 c5 01          	add    $0x1,%r13d
    2b44:	49 83 c4 48          	add    $0x48,%r12
    2b48:	41 83 fd 04          	cmp    $0x4,%r13d
    2b4c:	75 cc                	jne    2b1a <main+0x52a>
    2b4e:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    2b53:	89 6c 24 28          	mov    %ebp,0x28(%rsp)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2b57:	45 31 e4             	xor    %r12d,%r12d
    2b5a:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    2b5f:	4c 89 fb             	mov    %r15,%rbx
            int group_of = b / threads_per_group;
    2b62:	44 89 e0             	mov    %r12d,%eax
    2b65:	d1 f8                	sar    %eax
            if (k == group_of) {
    2b67:	39 d8                	cmp    %ebx,%eax
    2b69:	0f 84 de 00 00 00    	je     2c4d <main+0x65d>
    2b6f:	44 89 e2             	mov    %r12d,%edx
    2b72:	48 8d 35 22 48 00 00 	lea    0x4822(%rip),%rsi        # 739b <_IO_stdin_used+0x39b>
    2b79:	bf 01 00 00 00       	mov    $0x1,%edi
    2b7e:	31 c0                	xor    %eax,%eax
    2b80:	e8 cb f8 ff ff       	call   2450 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b85:	be 08 00 00 00       	mov    $0x8,%esi
    2b8a:	bf 01 00 00 00       	mov    $0x1,%edi
    2b8f:	e8 0c f8 ff ff       	call   23a0 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b94:	be 08 00 00 00       	mov    $0x8,%esi
    2b99:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b9e:	48 89 c5             	mov    %rax,%rbp
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ba1:	e8 fa f7 ff ff       	call   23a0 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    2ba6:	be 80 03 00 00       	mov    $0x380,%esi
    2bab:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2bb0:	49 89 c7             	mov    %rax,%r15
            struct Data *data = calloc(3, sizeof(struct Data));
    2bb3:	e8 e8 f7 ff ff       	call   23a0 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    2bb8:	be 80 03 00 00       	mov    $0x380,%esi
    2bbd:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    2bc2:	49 89 c5             	mov    %rax,%r13
            struct Data **stack = calloc(3, sizeof(struct Data));
    2bc5:	e8 d6 f7 ff ff       	call   23a0 <calloc@plt>
            mailboxes[b].higher = &data[1];
    2bca:	49 8d b5 80 03 00 00 	lea    0x380(%r13),%rsi
            mailboxes[b].lower = &data[0];
    2bd1:	4d 89 2e             	mov    %r13,(%r14)
            data[0].messages_count = 0;
    2bd4:	66 0f 6f 0d 64 50 00 00 	movdqa 0x5064(%rip),%xmm1        # 7c40 <_IO_stdin_used+0xc40>
            mailboxes[b].my_lower = &data[0];
    2bdc:	4d 89 6e 20          	mov    %r13,0x20(%r14)
            mailboxes[b].higher = &data[1];
    2be0:	49 89 76 08          	mov    %rsi,0x8(%r14)
            data[0].finished_reading = 1;
    2be4:	41 c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r13)
            mailboxes[b].my_higher = &data[1];
    2bef:	49 89 76 28          	mov    %rsi,0x28(%r14)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2bf3:	41 c7 46 40 02 00 00 00 	movl   $0x2,0x40(%r14)
            stack[0] = mailboxes[b].lower;
    2bfb:	4c 89 28             	mov    %r13,(%rax)
            stack[1] = mailboxes[b].higher;
    2bfe:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    2c02:	49 89 46 18          	mov    %rax,0x18(%r14)
            data[0].available_sending = 1;
    2c06:	41 c7 85 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r13)
            data[0].available_receiving = 0;
    2c11:	41 c7 85 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r13)
            data[0].messages = messages;
    2c1c:	49 89 6d 00          	mov    %rbp,0x0(%r13)
            data[1].messages = messages2;
    2c20:	4d 89 bd 80 03 00 00 	mov    %r15,0x380(%r13)
            data[1].available_sending = 1;
    2c27:	41 c7 85 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r13)
            data[1].available_receiving = 0;
    2c32:	41 c7 85 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r13)
            data[0].messages_count = 0;
    2c3d:	41 0f 29 8d 80 00 00 00 	movaps %xmm1,0x80(%r13)
            data[1].messages_count = 0;
    2c45:	41 0f 29 8d 00 04 00 00 	movaps %xmm1,0x400(%r13)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c4d:	41 83 c4 01          	add    $0x1,%r12d
    2c51:	49 83 c6 48          	add    $0x48,%r14
    2c55:	41 83 fc 04          	cmp    $0x4,%r12d
    2c59:	0f 85 03 ff ff ff    	jne    2b62 <main+0x572>
          char *message = malloc(sizeof(char) * 256);
    2c5f:	be 01 00 00 00       	mov    $0x1,%esi
    2c64:	bf 00 01 00 00       	mov    $0x100,%edi
    2c69:	8b 6c 24 28          	mov    0x28(%rsp),%ebp
    2c6d:	49 89 df             	mov    %rbx,%r15
    2c70:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    2c75:	e8 26 f7 ff ff       	call   23a0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2c7a:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    2c7f:	49 89 c4             	mov    %rax,%r12
          struct Message *messaged = malloc(sizeof(struct Message));
    2c82:	e8 89 f7 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2c87:	48 83 ec 08          	sub    $0x8,%rsp
    2c8b:	41 89 e9             	mov    %ebp,%r9d
    2c8e:	4c 89 e7             	mov    %r12,%rdi
    2c91:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    2c96:	44 8b 74 24 40       	mov    0x40(%rsp),%r14d
    2c9b:	ba 00 01 00 00       	mov    $0x100,%edx
    2ca0:	31 c0                	xor    %eax,%eax
    2ca2:	48 8d 0d d7 4a 00 00 	lea    0x4ad7(%rip),%rcx        # 7780 <_IO_stdin_used+0x780>
    2ca9:	be 01 00 00 00       	mov    $0x1,%esi
    2cae:	41 56                	push   %r14
    2cb0:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
    2cb5:	e8 66 f8 ff ff       	call   2520 <__sprintf_chk@plt>
          messaged->message = message;
    2cba:	4c 8b 54 24 28       	mov    0x28(%rsp),%r10
          messaged->task_index = y;
    2cbf:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
          messaged->group = k;
    2cc4:	44 89 f7             	mov    %r14d,%edi
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2cc7:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->group = k;
    2ccc:	45 89 72 18          	mov    %r14d,0x18(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2cd0:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
          messaged->task_index = y;
    2cd5:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2cd9:	49 63 46 08          	movslq 0x8(%r14),%rax
          thread_data[x].tasks[y].group = k;
    2cdd:	49 8b 56 38          	mov    0x38(%r14),%rdx
          messaged->message = message;
    2ce1:	4d 89 22             	mov    %r12,(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2ce4:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2ce8:	8d 45 01             	lea    0x1(%rbp),%eax
          thread_data[x].tasks[y].group = k;
    2ceb:	48 01 d3             	add    %rdx,%rbx
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2cee:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].group = k;
    2cf1:	89 bb 94 01 00 00    	mov    %edi,0x194(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2cf7:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].message = messaged;
    2cfc:	4c 89 93 88 01 00 00 	mov    %r10,0x188(%rbx)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2d03:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2d09:	89 83 90 01 00 00    	mov    %eax,0x190(%rbx)
          thread_data[x].tasks[y].sending = 1;
    2d0f:	c7 83 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rbx)
          thread_data[x].tasks[y].snapshot_count = 99;
    2d19:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
          thread_data[x].tasks[y].group = k;
    2d24:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2d29:	e8 72 f6 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    2d2e:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2d39:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2d40:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    2d45:	48 8b 00             	mov    (%rax),%rax
    2d48:	8b 48 04             	mov    0x4(%rax),%ecx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2d4b:	4c 39 f0             	cmp    %r14,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2d4e:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2d55:	89 8b 30 01 00 00    	mov    %ecx,0x130(%rbx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2d5b:	41 5a                	pop    %r10
    2d5d:	41 5b                	pop    %r11
    2d5f:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    2d64:	0f 85 a8 0e 00 00    	jne    3c12 <main+0x1622>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2d6a:	66 0f 6f 05 de 4e 00 00 	movdqa 0x4ede(%rip),%xmm0        # 7c50 <_IO_stdin_used+0xc50>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2d72:	89 6b 04             	mov    %ebp,0x4(%rbx)
          thread_data[x].tasks[y].available = 1;
    2d75:	48 8b 0d ec 4e 00 00 	mov    0x4eec(%rip),%rcx        # 7c68 <_IO_stdin_used+0xc68>
          thread_data[x].tasks[y].arrived = 0;
    2d7c:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
          thread_data[x].tasks[y].worker_count = thread_count;
    2d86:	c7 83 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rbx)
          thread_data[x].tasks[y].available = 1;
    2d90:	48 89 8b 44 01 00 00 	mov    %rcx,0x144(%rbx)
          thread_data[x].tasks[y].thread_count = 2;
    2d97:	0f 11 83 34 01 00 00 	movups %xmm0,0x134(%rbx)
          if (y == barrier_count - 1) {
    2d9e:	83 fd 01             	cmp    $0x1,%ebp
    2da1:	0f 84 d5 02 00 00    	je     307c <main+0xa8c>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2da7:	85 ed                	test   %ebp,%ebp
    2da9:	0f 84 b5 02 00 00    	je     3064 <main+0xa74>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    2daf:	4c 8b 4c 24 30       	mov    0x30(%rsp),%r9
    2db4:	49 89 dc             	mov    %rbx,%r12
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2db7:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    2dbc:	48 8d 05 0d 33 00 00 	lea    0x330d(%rip),%rax        # 60d0 <barriered_work>
    2dc3:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2dcb:	bf 01 00 00 00       	mov    $0x1,%edi
               thread_data[x].tasks[y].run = barriered_work; 
    2dd0:	4c 8b ac 24 98 00 00 00 	mov    0x98(%rsp),%r13
    2dd8:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    2ddd:	8b 9c 24 a4 00 00 00 	mov    0xa4(%rsp),%ebx
        thread_data[x].buffers_count = buffers_per_thread;
    2de4:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    2def:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2df4:	e8 a7 f5 ff ff       	call   23a0 <calloc@plt>
    2df9:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2dfe:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2e03:	4c 89 28             	mov    %r13,(%rax)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
        thread_data[x].tasks[barrier_count].available = 1; 
    2e06:	48 8b 0d 5b 4e 00 00 	mov    0x4e5b(%rip),%rcx        # 7c68 <_IO_stdin_used+0xc68>
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e0d:	49 83 c5 10          	add    $0x10,%r13
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2e11:	49 89 41 50          	mov    %rax,0x50(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2e15:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e1a:	49 81 c1 c0 00 00 00 	add    $0xc0,%r9
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2e21:	66 0f 6f a4 24 80 00 00 00 	movdqa 0x80(%rsp),%xmm4
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2e2a:	83 44 24 50 01       	addl   $0x1,0x50(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2e2f:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].arrived = 0; 
    2e32:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2e3c:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2e46:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    2e4d:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2e57:	41 8b 81 44 ff ff ff 	mov    -0xbc(%r9),%eax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2e5e:	0f 11 a2 18 05 00 00 	movups %xmm4,0x518(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2e65:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2e6b:	c7 82 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
    2e75:	48 89 8a 44 05 00 00 	mov    %rcx,0x544(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e7c:	39 1c 24             	cmp    %ebx,(%rsp)
    2e7f:	0f 85 3b fa ff ff    	jne    28c0 <main+0x2d0>
    2e85:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
  for (int k = 0 ; k < group_count ; k++) {
    2e8d:	89 da                	mov    %ebx,%edx
    2e8f:	48 8b 9c 24 a8 00 00 00 	mov    0xa8(%rsp),%rbx
    2e97:	83 c2 02             	add    $0x2,%edx
    2e9a:	48 83 c6 18          	add    $0x18,%rsi
    2e9e:	4d 85 ff             	test   %r15,%r15
    2ea1:	0f 85 1a 02 00 00    	jne    30c1 <main+0xad1>
    2ea7:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    2ead:	e9 cf f9 ff ff       	jmp    2881 <main+0x291>
    2eb2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            int group_of = b / threads_per_group;
    2eb8:	44 89 eb             	mov    %r13d,%ebx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2ebb:	31 c0                	xor    %eax,%eax
    2ebd:	44 89 ea             	mov    %r13d,%edx
    2ec0:	bf 01 00 00 00       	mov    $0x1,%edi
    2ec5:	d1 fb                	sar    %ebx
    2ec7:	48 8d 35 bd 44 00 00 	lea    0x44bd(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
    2ece:	89 d9                	mov    %ebx,%ecx
    2ed0:	e8 7b f5 ff ff       	call   2450 <__printf_chk@plt>
            if (k == group_of) {
    2ed5:	44 39 fb             	cmp    %r15d,%ebx
    2ed8:	0f 84 cd 00 00 00    	je     2fab <main+0x9bb>
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ede:	41 83 c5 01          	add    $0x1,%r13d
    2ee2:	49 83 c4 48          	add    $0x48,%r12
    2ee6:	41 83 fd 04          	cmp    $0x4,%r13d
    2eea:	75 cc                	jne    2eb8 <main+0x8c8>
    2eec:	e9 5d fc ff ff       	jmp    2b4e <main+0x55e>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ef1:	be 08 00 00 00       	mov    $0x8,%esi
    2ef6:	bf 01 00 00 00       	mov    $0x1,%edi
    2efb:	e8 a0 f4 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f00:	be 08 00 00 00       	mov    $0x8,%esi
    2f05:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f0a:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f0f:	e8 8c f4 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2f14:	be 80 03 00 00       	mov    $0x380,%esi
    2f19:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f1e:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2f23:	e8 78 f4 ff ff       	call   23a0 <calloc@plt>
    2f28:	44 89 ea             	mov    %r13d,%edx
    2f2b:	bf 01 00 00 00       	mov    $0x1,%edi
              mailboxes[b].kind = MAILBOX_FRIEND;
    2f30:	41 c7 44 24 40 01 00 00 00 	movl   $0x1,0x40(%r12)
              struct Data *data = calloc(3, sizeof(struct Data));
    2f39:	49 89 c0             	mov    %rax,%r8
              mailboxes[b].lower = &data[0];
    2f3c:	49 89 04 24          	mov    %rax,(%r12)
              mailboxes[b].higher = &data[1];
    2f40:	48 8d 80 80 03 00 00 	lea    0x380(%rax),%rax
    2f47:	48 8d 35 0a 48 00 00 	lea    0x480a(%rip),%rsi        # 7758 <_IO_stdin_used+0x758>
    2f4e:	49 89 44 24 08       	mov    %rax,0x8(%r12)
              data[0].finished_reading = 1;
    2f53:	8b 44 24 60          	mov    0x60(%rsp),%eax
    2f57:	41 c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r8)
    2f62:	41 89 44 24 44       	mov    %eax,0x44(%r12)
    2f67:	89 c1                	mov    %eax,%ecx
    2f69:	31 c0                	xor    %eax,%eax
    2f6b:	4c 89 44 24 28       	mov    %r8,0x28(%rsp)
    2f70:	e8 db f4 ff ff       	call   2450 <__printf_chk@plt>
              data[0].messages = messages;
    2f75:	4c 8b 44 24 28       	mov    0x28(%rsp),%r8
    2f7a:	4c 8b 54 24 70       	mov    0x70(%rsp),%r10
              data[0].messages_count = 0;
    2f7f:	66 0f 6f 25 b9 4c 00 00 	movdqa 0x4cb9(%rip),%xmm4        # 7c40 <_IO_stdin_used+0xc40>
              data[1].messages = messages2;
    2f87:	4c 8b 4c 24 68       	mov    0x68(%rsp),%r9
              data[0].messages = messages;
    2f8c:	4d 89 10             	mov    %r10,(%r8)
              data[1].messages = messages2;
    2f8f:	4d 89 88 80 03 00 00 	mov    %r9,0x380(%r8)
              data[0].messages_count = 0;
    2f96:	41 0f 29 a0 80 00 00 00 	movaps %xmm4,0x80(%r8)
              data[1].messages_count = 0;
    2f9e:	41 0f 29 a0 00 04 00 00 	movaps %xmm4,0x400(%r8)
    2fa6:	e9 95 fb ff ff       	jmp    2b40 <main+0x550>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2fab:	be 08 00 00 00       	mov    $0x8,%esi
    2fb0:	bf 01 00 00 00       	mov    $0x1,%edi
    2fb5:	e8 e6 f3 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2fba:	be 08 00 00 00       	mov    $0x8,%esi
    2fbf:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2fc4:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2fc9:	e8 d2 f3 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2fce:	be 80 03 00 00       	mov    $0x380,%esi
    2fd3:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2fd8:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2fdd:	e8 be f3 ff ff       	call   23a0 <calloc@plt>
    2fe2:	44 89 ea             	mov    %r13d,%edx
    2fe5:	bf 01 00 00 00       	mov    $0x1,%edi
              mailboxes[b].kind = MAILBOX_FRIEND;
    2fea:	41 c7 44 24 40 01 00 00 00 	movl   $0x1,0x40(%r12)
              struct Data *data = calloc(3, sizeof(struct Data));
    2ff3:	49 89 c0             	mov    %rax,%r8
              mailboxes[b].lower = &data[0];
    2ff6:	49 89 04 24          	mov    %rax,(%r12)
              mailboxes[b].higher = &data[1];
    2ffa:	48 8d 80 80 03 00 00 	lea    0x380(%rax),%rax
    3001:	48 8d 35 50 47 00 00 	lea    0x4750(%rip),%rsi        # 7758 <_IO_stdin_used+0x758>
    3008:	49 89 44 24 08       	mov    %rax,0x8(%r12)
              data[0].finished_reading = 1;
    300d:	8b 04 24             	mov    (%rsp),%eax
    3010:	41 c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r8)
    301b:	41 89 44 24 44       	mov    %eax,0x44(%r12)
    3020:	89 c1                	mov    %eax,%ecx
    3022:	31 c0                	xor    %eax,%eax
    3024:	4c 89 44 24 28       	mov    %r8,0x28(%rsp)
    3029:	e8 22 f4 ff ff       	call   2450 <__printf_chk@plt>
              data[0].messages = messages;
    302e:	4c 8b 44 24 28       	mov    0x28(%rsp),%r8
    3033:	4c 8b 54 24 70       	mov    0x70(%rsp),%r10
              data[0].messages_count = 0;
    3038:	66 0f 6f 35 00 4c 00 00 	movdqa 0x4c00(%rip),%xmm6        # 7c40 <_IO_stdin_used+0xc40>
              data[1].messages = messages2;
    3040:	4c 8b 4c 24 68       	mov    0x68(%rsp),%r9
              data[0].messages = messages;
    3045:	4d 89 10             	mov    %r10,(%r8)
              data[1].messages = messages2;
    3048:	4d 89 88 80 03 00 00 	mov    %r9,0x380(%r8)
              data[0].messages_count = 0;
    304f:	41 0f 29 b0 80 00 00 00 	movaps %xmm6,0x80(%r8)
              data[1].messages_count = 0;
    3057:	41 0f 29 b0 00 04 00 00 	movaps %xmm6,0x400(%r8)
    305f:	e9 7a fe ff ff       	jmp    2ede <main+0x8ee>
    3064:	48 8d 05 45 35 00 00 	lea    0x3545(%rip),%rax        # 65b0 <barriered_work_ingest_andwork>
    306b:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    3070:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    3077:	e9 4b fa ff ff       	jmp    2ac7 <main+0x4d7>
    307c:	48 8d 05 4d 30 00 00 	lea    0x304d(%rip),%rax        # 60d0 <barriered_work>
    3083:	bd 02 00 00 00       	mov    $0x2,%ebp
    3088:	eb e6                	jmp    3070 <main+0xa80>
        other = (x + 1) % total_threads;
    308a:	8b 44 24 60          	mov    0x60(%rsp),%eax
        my_thread_data[1] = &thread_data[other]; 
    308e:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    3093:	45 31 c0             	xor    %r8d,%r8d
        other = (x + 1) % total_threads;
    3096:	83 c0 02             	add    $0x2,%eax
        my_thread_data[1] = &thread_data[other]; 
    3099:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
        other = (x + 1) % total_threads;
    309d:	48 89 c1             	mov    %rax,%rcx
        my_thread_data[1] = &thread_data[other]; 
    30a0:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    30a5:	48 c1 e2 06          	shl    $0x6,%rdx
    30a9:	48 01 c2             	add    %rax,%rdx
        my_thread_data[0] = &thread_data[x]; 
    30ac:	4c 89 c8             	mov    %r9,%rax
    30af:	e9 9d f8 ff ff       	jmp    2951 <main+0x361>
            CPU_SET(j, sendercpu);
    30b4:	49 81 0c 24 ff 0f 00 00 	orq    $0xfff,(%r12)
          for (int j = 0 ; j < cores ; j++) {
    30bc:	e9 30 f9 ff ff       	jmp    29f1 <main+0x401>
    30c1:	48 8d 3d f1 42 00 00 	lea    0x42f1(%rip),%rdi        # 73b9 <_IO_stdin_used+0x3b9>
    30c8:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    30cd:	45 31 ed             	xor    %r13d,%r13d
    30d0:	4c 8d 25 21 43 00 00 	lea    0x4321(%rip),%r12        # 73f8 <_IO_stdin_used+0x3f8>
    30d7:	e8 14 f2 ff ff       	call   22f0 <puts@plt>
    30dc:	44 89 ea             	mov    %r13d,%edx
    30df:	48 8d 35 eb 42 00 00 	lea    0x42eb(%rip),%rsi        # 73d1 <_IO_stdin_used+0x3d1>
    30e6:	31 c0                	xor    %eax,%eax
    30e8:	4c 89 ed             	mov    %r13,%rbp
    30eb:	bf 01 00 00 00       	mov    $0x1,%edi
    30f0:	48 f7 dd             	neg    %rbp
    30f3:	43 8d 5c 2d 00       	lea    0x0(%r13,%r13,1),%ebx
    30f8:	45 31 ff             	xor    %r15d,%r15d
    30fb:	e8 50 f3 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    3100:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3105:	81 e5 80 01 00 00    	and    $0x180,%ebp
    310b:	48 01 c5             	add    %rax,%rbp
      int x = (k * threads_per_group) + d;
    310e:	41 8d 0c 1f          	lea    (%r15,%rbx,1),%ecx
    3112:	44 89 fa             	mov    %r15d,%edx
    3115:	48 8d 35 bf 42 00 00 	lea    0x42bf(%rip),%rsi        # 73db <_IO_stdin_used+0x3db>
    311c:	31 c0                	xor    %eax,%eax
    311e:	bf 01 00 00 00       	mov    $0x1,%edi
    3123:	45 31 f6             	xor    %r14d,%r14d
    3126:	e8 25 f3 ff ff       	call   2450 <__printf_chk@plt>
    312b:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
    3130:	4c 89 f1             	mov    %r14,%rcx
    3133:	89 5c 24 20          	mov    %ebx,0x20(%rsp)
    3137:	89 ca                	mov    %ecx,%edx
    3139:	48 8d 35 ad 42 00 00 	lea    0x42ad(%rip),%rsi        # 73ed <_IO_stdin_used+0x3ed>
    3140:	bf 01 00 00 00       	mov    $0x1,%edi
    3145:	31 c0                	xor    %eax,%eax
    3147:	48 89 0c 24          	mov    %rcx,(%rsp)
    314b:	45 31 ed             	xor    %r13d,%r13d
    314e:	e8 fd f2 ff ff       	call   2450 <__printf_chk@plt>
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3153:	48 8b 1c 24          	mov    (%rsp),%rbx
    3157:	48 c1 e3 09          	shl    $0x9,%rbx
          char * mailbox_kind = calloc(100, sizeof(char));
    315b:	be 01 00 00 00       	mov    $0x1,%esi
    3160:	bf 64 00 00 00       	mov    $0x64,%edi
    3165:	45 89 ee             	mov    %r13d,%r14d
    3168:	e8 33 f2 ff ff       	call   23a0 <calloc@plt>
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    316d:	4c 8b 45 38          	mov    0x38(%rbp),%r8
          char * mailbox_kind = calloc(100, sizeof(char));
    3171:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3174:	4b 8d 44 ed 00       	lea    0x0(%r13,%r13,8),%rax
    3179:	49 8b b4 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rsi
    3181:	48 c1 e0 03          	shl    $0x3,%rax
    3185:	48 01 c6             	add    %rax,%rsi
    3188:	8b 7e 40             	mov    0x40(%rsi),%edi
    318b:	83 ff 02             	cmp    $0x2,%edi
    318e:	74 57                	je     31e7 <main+0xbf7>
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    3190:	83 ff 01             	cmp    $0x1,%edi
    3193:	74 6c                	je     3201 <main+0xc11>
    3195:	44 8b 46 44          	mov    0x44(%rsi),%r8d
    3199:	44 89 f2             	mov    %r14d,%edx
    319c:	4c 89 e6             	mov    %r12,%rsi
    319f:	bf 01 00 00 00       	mov    $0x1,%edi
    31a4:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    31a6:	49 83 c5 01          	add    $0x1,%r13
    31aa:	e8 a1 f2 ff ff       	call   2450 <__printf_chk@plt>
    31af:	49 83 fd 04          	cmp    $0x4,%r13
    31b3:	75 a6                	jne    315b <main+0xb6b>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    31b5:	48 8b 0c 24          	mov    (%rsp),%rcx
    31b9:	48 83 c1 01          	add    $0x1,%rcx
    31bd:	48 83 f9 03          	cmp    $0x3,%rcx
    31c1:	0f 85 70 ff ff ff    	jne    3137 <main+0xb47>
    for (int d = 0 ; d < threads_per_group ; d++) {
    31c7:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    31cc:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    31d0:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
    31d7:	45 85 ff             	test   %r15d,%r15d
    31da:	75 42                	jne    321e <main+0xc2e>
    31dc:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    31e2:	e9 27 ff ff ff       	jmp    310e <main+0xb1e>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    31e7:	48 bf 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rdi
    31f1:	48 89 39             	mov    %rdi,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    31f4:	49 03 84 18 70 01 00 00 	add    0x170(%r8,%rbx,1),%rax
    31fc:	48 89 c6             	mov    %rax,%rsi
    31ff:	eb 94                	jmp    3195 <main+0xba5>
    3201:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3207:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    320e:	49 03 84 18 70 01 00 00 	add    0x170(%r8,%rbx,1),%rax
    3216:	48 89 c6             	mov    %rax,%rsi
    3219:	e9 77 ff ff ff       	jmp    3195 <main+0xba5>
  for (int k = 0 ; k < group_count ; k++) {
    321e:	4d 85 ed             	test   %r13,%r13
    3221:	75 0a                	jne    322d <main+0xc3d>
    3223:	4c 8b 6c 24 08       	mov    0x8(%rsp),%r13
    3228:	e9 af fe ff ff       	jmp    30dc <main+0xaec>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    322d:	ba 05 00 00 00       	mov    $0x5,%edx
    3232:	48 8d 35 da 41 00 00 	lea    0x41da(%rip),%rsi        # 7413 <_IO_stdin_used+0x413>
    3239:	bf 01 00 00 00       	mov    $0x1,%edi
    323e:	31 c0                	xor    %eax,%eax
    3240:	4c 89 6c 24 38       	mov    %r13,0x38(%rsp)
    3245:	44 89 7c 24 18       	mov    %r15d,0x18(%rsp)
    324a:	e8 01 f2 ff ff       	call   2450 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    324f:	be 08 00 00 00       	mov    $0x8,%esi
    3254:	bf 02 00 00 00       	mov    $0x2,%edi
    3259:	e8 42 f1 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    325e:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3263:	be 38 00 00 00       	mov    $0x38,%esi
    3268:	bf 08 00 00 00       	mov    $0x8,%edi
    my_thread_data[0] = &thread_data[x]; 
    326d:	4d 8d af c0 03 00 00 	lea    0x3c0(%r15),%r13
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3274:	4c 89 78 08          	mov    %r15,0x8(%rax)


  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    3278:	49 8d af 80 04 00 00 	lea    0x480(%r15),%rbp
    thread_data[x].threads = my_thread_data;
    327f:	49 89 87 d8 03 00 00 	mov    %rax,0x3d8(%r15)
    thread_data[n].tasks[0].scheduled = 1;
    3286:	4d 8d a7 c0 00 00 00 	lea    0xc0(%r15),%r12
    my_thread_data[0] = &thread_data[x]; 
    328d:	4c 89 28             	mov    %r13,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3290:	49 8b 47 38          	mov    0x38(%r15),%rax
    thread_data[x].thread_count = 2;
    3294:	41 c7 87 e8 03 00 00 02 00 00 00 	movl   $0x2,0x3e8(%r15)
    thread_data[x].thread_index = 0;
    329f:	41 c7 87 c4 03 00 00 00 00 00 00 	movl   $0x0,0x3c4(%r15)
    thread_data[x].task_count = total_barrier_count;
    32aa:	41 c7 87 00 04 00 00 03 00 00 00 	movl   $0x3,0x400(%r15)
    thread_data[n].tasks[0].scheduled = 1;
    32b5:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    32bf:	49 8b 87 f8 00 00 00 	mov    0xf8(%r15),%rax
    32c6:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32d0:	e8 cb f0 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32d5:	be 38 00 00 00       	mov    $0x38,%esi
    32da:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32df:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32e4:	e8 b7 f0 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32e9:	be 38 00 00 00       	mov    $0x38,%esi
    32ee:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32f3:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32f6:	e8 a5 f0 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32fb:	be 38 00 00 00       	mov    $0x38,%esi
    3300:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3305:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3309:	e8 92 f0 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    330e:	be 08 00 00 00       	mov    $0x8,%esi
    3313:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3318:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    331d:	e8 7e f0 ff ff       	call   23a0 <calloc@plt>
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3322:	be 08 00 00 00       	mov    $0x8,%esi
    3327:	bf 08 00 00 00       	mov    $0x8,%edi
  thread_data[timer_threadi].type = TIMER;
    332c:	41 c7 87 0c 03 00 00 00 00 00 00 	movl   $0x0,0x30c(%r15)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3337:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    333a:	48 8b 05 2f 49 00 00 	mov    0x492f(%rip),%rax        # 7c70 <_IO_stdin_used+0xc70>
    3341:	49 89 87 40 03 00 00 	mov    %rax,0x340(%r15)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3348:	e8 53 f0 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[n] = &thread_data[n]; 
    334d:	49 8d 97 80 01 00 00 	lea    0x180(%r15),%rdx
    3354:	bf 01 00 00 00       	mov    $0x1,%edi
    3359:	49 8d 8f 00 03 00 00 	lea    0x300(%r15),%rcx
    3360:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3364:	49 8d 97 40 02 00 00 	lea    0x240(%r15),%rdx
    336b:	48 8d 35 b0 40 00 00 	lea    0x40b0(%rip),%rsi        # 7422 <_IO_stdin_used+0x422>
    3372:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3376:	49 8d 97 40 05 00 00 	lea    0x540(%r15),%rdx
    337d:	48 89 48 20          	mov    %rcx,0x20(%rax)
    3381:	4c 89 68 28          	mov    %r13,0x28(%rax)
    3385:	48 89 68 30          	mov    %rbp,0x30(%rax)
    3389:	48 89 50 38          	mov    %rdx,0x38(%rax)
    338d:	ba 04 00 00 00       	mov    $0x4,%edx
    3392:	4c 89 38             	mov    %r15,(%rax)
    3395:	4c 89 60 08          	mov    %r12,0x8(%rax)
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3399:	49 89 87 18 03 00 00 	mov    %rax,0x318(%r15)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    33a0:	48 8b 05 d1 48 00 00 	mov    0x48d1(%rip),%rax        # 7c78 <_IO_stdin_used+0xc78>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    33a7:	41 c7 87 30 03 00 00 04 00 00 00 	movl   $0x4,0x330(%r15)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    33b2:	49 89 87 28 03 00 00 	mov    %rax,0x328(%r15)
    33b9:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    33bb:	41 c7 87 04 03 00 00 00 00 00 00 	movl   $0x0,0x304(%r15)
    my_thread_data[n] = &thread_data[n]; 
    33c6:	48 89 4c 24 28       	mov    %rcx,0x28(%rsp)
    33cb:	e8 80 f0 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    33d0:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    33d5:	48 8d 15 04 0b 00 00 	lea    0xb04(%rip),%rdx        # 3ee0 <timer_thread>
    33dc:	49 8d b6 e0 00 00 00 	lea    0xe0(%r14),%rsi
    33e3:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
    33e7:	e8 84 f0 ff ff       	call   2470 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    33ec:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    33f1:	45 31 d2             	xor    %r10d,%r10d
    33f4:	48 89 d9             	mov    %rbx,%rcx
    33f7:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    33fc:	4c 89 fa             	mov    %r15,%rdx
    33ff:	41 b9 02 00 00 00    	mov    $0x2,%r9d
    3405:	4c 89 64 24 40       	mov    %r12,0x40(%rsp)
    340a:	4c 89 6c 24 20       	mov    %r13,0x20(%rsp)
    340f:	49 89 c5             	mov    %rax,%r13
    3412:	48 89 6c 24 28       	mov    %rbp,0x28(%rsp)
    3417:	44 89 d5             	mov    %r10d,%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    341a:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    341f:	4d 89 ec             	mov    %r13,%r12
    3422:	8d 5c 2d 00          	lea    0x0(%rbp,%rbp,1),%ebx
    3426:	49 89 cf             	mov    %rcx,%r15
    3429:	48 89 54 24 60       	mov    %rdx,0x60(%rsp)
    342e:	49 89 d6             	mov    %rdx,%r14
    3431:	4c 89 6c 24 48       	mov    %r13,0x48(%rsp)
    3436:	45 89 cd             	mov    %r9d,%r13d
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    3439:	41 c7 46 0c 01 00 00 00 	movl   $0x1,0xc(%r14)
    3441:	89 da                	mov    %ebx,%edx
    3443:	89 e9                	mov    %ebp,%ecx
    3445:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    3447:	41 c7 46 44 01 00 00 00 	movl   $0x1,0x44(%r14)
    344f:	48 8d 35 5a 43 00 00 	lea    0x435a(%rip),%rsi        # 77b0 <_IO_stdin_used+0x7b0>
    3456:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    345b:	83 c3 01             	add    $0x1,%ebx
    345e:	e8 ed ef ff ff       	call   2450 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3463:	4c 89 f1             	mov    %r14,%rcx
    3466:	4c 89 e6             	mov    %r12,%rsi
    3469:	4c 89 ff             	mov    %r15,%rdi
    346c:	48 8d 15 9d 27 00 00 	lea    0x279d(%rip),%rdx        # 5c10 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3473:	49 81 c6 c0 00 00 00 	add    $0xc0,%r14
    347a:	49 83 c7 08          	add    $0x8,%r15
    347e:	49 83 c4 38          	add    $0x38,%r12
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3482:	e8 e9 ef ff ff       	call   2470 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3487:	49 8b 56 f0          	mov    -0x10(%r14),%rdx
    348b:	49 8b 7f f8          	mov    -0x8(%r15),%rdi
    348f:	be 08 00 00 00       	mov    $0x8,%esi
    3494:	e8 47 ee ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3499:	44 39 eb             	cmp    %r13d,%ebx
    349c:	75 9b                	jne    3439 <main+0xe49>
  for (int k = 0 ; k < group_count ; k++) {
    349e:	45 89 e9             	mov    %r13d,%r9d
    34a1:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    34a6:	48 8b 54 24 60       	mov    0x60(%rsp),%rdx
    34ab:	4c 8b 6c 24 48       	mov    0x48(%rsp),%r13
    34b0:	41 83 c1 02          	add    $0x2,%r9d
    34b4:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
    34bb:	48 83 c1 10          	add    $0x10,%rcx
    34bf:	49 83 c5 70          	add    $0x70,%r13
    34c3:	85 ed                	test   %ebp,%ebp
    34c5:	75 09                	jne    34d0 <main+0xee0>
    34c7:	8b 6c 24 18          	mov    0x18(%rsp),%ebp
    34cb:	e9 4a ff ff ff       	jmp    341a <main+0xe2a>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    34d0:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    34d5:	be d8 00 00 00       	mov    $0xd8,%esi
    34da:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    34df:	4c 8b 35 9a 47 00 00 	mov    0x479a(%rip),%r14        # 7c80 <_IO_stdin_used+0xc80>
    thread_data[x].type = IO;
    34e6:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    34eb:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    34f0:	41 c7 87 cc 03 00 00 02 00 00 00 	movl   $0x2,0x3cc(%r15)
    34fb:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    thread_data[x].task_count = 0;
    3500:	4d 89 b7 00 04 00 00 	mov    %r14,0x400(%r15)
    thread_data[x].type = IO;
    3507:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    350c:	e8 8f ee ff ff       	call   23a0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3511:	be 00 08 00 00       	mov    $0x800,%esi
    3516:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3518:	49 89 87 18 04 00 00 	mov    %rax,0x418(%r15)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    351f:	e8 8c ef ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3524:	be 08 00 00 00       	mov    $0x8,%esi
    3529:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    352e:	41 89 87 20 04 00 00 	mov    %eax,0x420(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3535:	e8 66 ee ff ff       	call   23a0 <calloc@plt>
    353a:	ba 05 00 00 00       	mov    $0x5,%edx
    353f:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3544:	41 c7 87 e8 03 00 00 02 00 00 00 	movl   $0x2,0x3e8(%r15)
      my_thread_data[n] = &thread_data[n]; 
    354f:	4c 89 38             	mov    %r15,(%rax)
    3552:	48 8d 35 e7 3e 00 00 	lea    0x3ee7(%rip),%rsi        # 7440 <_IO_stdin_used+0x440>
    thread_data[x].threads = my_thread_data;
    3559:	49 89 87 d8 03 00 00 	mov    %rax,0x3d8(%r15)
      my_thread_data[n] = &thread_data[n]; 
    3560:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3564:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3566:	41 c7 87 c4 03 00 00 05 00 00 00 	movl   $0x5,0x3c4(%r15)
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3571:	41 bf 06 00 00 00    	mov    $0x6,%r15d
    3577:	e8 d4 ee ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    357c:	48 8b 34 24          	mov    (%rsp),%rsi
    3580:	4c 89 e9             	mov    %r13,%rcx
    3583:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
    3587:	48 8d 15 92 1e 00 00 	lea    0x1e92(%rip),%rdx        # 5420 <io_thread>
    358e:	4c 8d 6b 30          	lea    0x30(%rbx),%r13
    3592:	48 81 c6 18 01 00 00 	add    $0x118,%rsi
    3599:	e8 d2 ee ff ff       	call   2470 <pthread_create@plt>
    359e:	ba 06 00 00 00       	mov    $0x6,%edx
    35a3:	48 8d 35 ad 3e 00 00 	lea    0x3ead(%rip),%rsi        # 7457 <_IO_stdin_used+0x457>
    35aa:	31 c0                	xor    %eax,%eax
    35ac:	bf 01 00 00 00       	mov    $0x1,%edi
    35b1:	e8 9a ee ff ff       	call   2450 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    35b6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    35bb:	48 05 50 01 00 00    	add    $0x150,%rax
    35c1:	48 89 04 24          	mov    %rax,(%rsp)
    35c5:	44 89 fa             	mov    %r15d,%edx
    35c8:	48 8d 35 9e 3e 00 00 	lea    0x3e9e(%rip),%rsi        # 746d <_IO_stdin_used+0x46d>
    35cf:	bf 01 00 00 00       	mov    $0x1,%edi
    35d4:	31 c0                	xor    %eax,%eax
    35d6:	e8 75 ee ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    35db:	4c 89 75 40          	mov    %r14,0x40(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    35df:	be 08 00 00 00       	mov    $0x8,%esi
    35e4:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = EXTERNAL;
    35e9:	c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    35f0:	e8 ab ed ff ff       	call   23a0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    35f5:	48 8b 7c 24 78       	mov    0x78(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    35fa:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    35ff:	c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3609:	48 89 45 50          	mov    %rax,0x50(%rbp)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    360d:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3610:	bf 02 00 00 00       	mov    $0x2,%edi
    3615:	e8 86 ed ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    361a:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    361f:	48 89 e9             	mov    %rbp,%rcx
    3622:	4c 89 ef             	mov    %r13,%rdi
    thread_data[x].threads = my_thread_data;
    3625:	48 89 45 18          	mov    %rax,0x18(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3629:	48 8d 15 a0 07 00 00 	lea    0x7a0(%rip),%rdx        # 3dd0 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3630:	49 83 c5 08          	add    $0x8,%r13
    3634:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
      my_thread_data[n] = &thread_data[n]; 
    363b:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    363e:	48 8b 34 24          	mov    (%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3642:	4c 89 60 08          	mov    %r12,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3646:	48 8b 05 13 46 00 00 	mov    0x4613(%rip),%rax        # 7c60 <_IO_stdin_used+0xc60>
    thread_data[x].thread_index = x;
    364d:	44 89 bd 44 ff ff ff 	mov    %r15d,-0xbc(%rbp)
    thread_data[x].thread_count = thread_count;
    3654:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    365b:	e8 10 ee ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3660:	48 83 44 24 78 10    	addq   $0x10,0x78(%rsp)
    3666:	48 83 04 24 38       	addq   $0x38,(%rsp)
    366b:	41 83 ff 06          	cmp    $0x6,%r15d
    366f:	75 0b                	jne    367c <main+0x108c>
    3671:	41 bf 07 00 00 00    	mov    $0x7,%r15d
    3677:	e9 49 ff ff ff       	jmp    35c5 <main+0xfd5>
    367c:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3681:	48 8d 2d 02 3e 00 00 	lea    0x3e02(%rip),%rbp        # 748a <_IO_stdin_used+0x48a>
    3688:	4c 8d 68 04          	lea    0x4(%rax),%r13
    368c:	4c 8d a0 04 06 00 00 	lea    0x604(%rax),%r12
    3693:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    3697:	41 8b 55 00          	mov    0x0(%r13),%edx
    369b:	48 89 ee             	mov    %rbp,%rsi
    369e:	bf 01 00 00 00       	mov    $0x1,%edi
    36a3:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    36a5:	49 81 c5 c0 00 00 00 	add    $0xc0,%r13
    36ac:	e8 9f ed ff ff       	call   2450 <__printf_chk@plt>
    36b1:	4d 39 ec             	cmp    %r13,%r12
    36b4:	75 dd                	jne    3693 <main+0x10a3>
    36b6:	48 8d 3d e0 3d 00 00 	lea    0x3de0(%rip),%rdi        # 749d <_IO_stdin_used+0x49d>
    36bd:	45 31 ed             	xor    %r13d,%r13d
    36c0:	4c 8d a4 24 b0 00 00 00 	lea    0xb0(%rsp),%r12
    36c8:	e8 23 ec ff ff       	call   22f0 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    36cd:	48 8d 2d e7 3d 00 00 	lea    0x3de7(%rip),%rbp        # 74bb <_IO_stdin_used+0x4bb>
    void * result; 
    pthread_join(thread[x], &result);
    36d4:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    36d8:	4c 89 e6             	mov    %r12,%rsi
    36db:	e8 10 ee ff ff       	call   24f0 <pthread_join@plt>
    36e0:	44 89 ea             	mov    %r13d,%edx
    36e3:	48 89 ee             	mov    %rbp,%rsi
    36e6:	bf 01 00 00 00       	mov    $0x1,%edi
    36eb:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    36ed:	49 83 c5 01          	add    $0x1,%r13
    36f1:	e8 5a ed ff ff       	call   2450 <__printf_chk@plt>
    36f6:	49 83 fd 08          	cmp    $0x8,%r13
    36fa:	75 d8                	jne    36d4 <main+0x10e4>
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
    36fc:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
  long received = 0;
    3704:	45 31 d2             	xor    %r10d,%r10d
    3707:	31 ed                	xor    %ebp,%ebp
  long ingests = 0;
    3709:	45 31 db             	xor    %r11d,%r11d
  long total = 0;
    370c:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    3715:	4c 89 d3             	mov    %r10,%rbx
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3718:	49 bc db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r12
    for (int d = 0 ; d < threads_per_group ; d++) {
    3722:	48 89 e8             	mov    %rbp,%rax
    3725:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    372a:	4c 89 5c 24 28       	mov    %r11,0x28(%rsp)
    372f:	4d 89 d7             	mov    %r10,%r15
    3732:	48 f7 d8             	neg    %rax
    3735:	48 89 6c 24 48       	mov    %rbp,0x48(%rsp)
    373a:	49 89 c6             	mov    %rax,%r14
    373d:	83 e0 30             	and    $0x30,%eax
    3740:	41 81 e6 80 01 00 00 	and    $0x180,%r14d
    3747:	49 01 fe             	add    %rdi,%r14
    374a:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
    374f:	48 01 f8             	add    %rdi,%rax
    3752:	8d 7c 2d 00          	lea    0x0(%rbp,%rbp,1),%edi
    3756:	48 89 dd             	mov    %rbx,%rbp
    3759:	48 8b 1c 24          	mov    (%rsp),%rbx
    375d:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    3762:	8d 47 ff             	lea    -0x1(%rdi),%eax
    3765:	89 44 24 30          	mov    %eax,0x30(%rsp)
    3769:	89 7c 24 50          	mov    %edi,0x50(%rsp)
      int x = (k * threads_per_group) + d;
    376d:	8b 7c 24 30          	mov    0x30(%rsp),%edi
    3771:	89 f8                	mov    %edi,%eax
    3773:	89 7c 24 40          	mov    %edi,0x40(%rsp)
    3777:	83 c7 01             	add    $0x1,%edi
    377a:	89 fe                	mov    %edi,%esi
    377c:	89 7c 24 30          	mov    %edi,0x30(%rsp)
        other = abs(x - 1) % total_threads;
    3780:	89 c7                	mov    %eax,%edi
    3782:	8d 40 02             	lea    0x2(%rax),%eax
    3785:	83 e6 01             	and    $0x1,%esi
    3788:	0f 45 c7             	cmovne %edi,%eax
    378b:	bf 0a 00 00 00       	mov    $0xa,%edi
    3790:	4c 63 e8             	movslq %eax,%r13
    3793:	e8 38 eb ff ff       	call   22d0 <putchar@plt>
    3798:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    379d:	bf 01 00 00 00       	mov    $0x1,%edi
    37a2:	48 8d 35 26 3d 00 00 	lea    0x3d26(%rip),%rsi        # 74cf <_IO_stdin_used+0x4cf>
    37a9:	48 8b 10             	mov    (%rax),%rdx
    37ac:	31 c0                	xor    %eax,%eax
    37ae:	e8 9d ec ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    37b3:	41 8b 56 40          	mov    0x40(%r14),%edx
    37b7:	85 d2                	test   %edx,%edx
    37b9:	0f 8e 4c 04 00 00    	jle    3c0b <main+0x161b>
    37bf:	48 63 f2             	movslq %edx,%rsi
    37c2:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    37c6:	31 d2                	xor    %edx,%edx
    37c8:	48 c1 e6 09          	shl    $0x9,%rsi
    37cc:	48 01 c6             	add    %rax,%rsi
    37cf:	90                   	nop
        v += thread_data[me].tasks[n].v;
    37d0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    37d7:	48 05 00 02 00 00    	add    $0x200,%rax
    37dd:	48 39 f0             	cmp    %rsi,%rax
    37e0:	75 ee                	jne    37d0 <main+0x11e0>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    37e2:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    37e7:	4b 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%rax
    37ec:	48 c1 e0 06          	shl    $0x6,%rax
    37f0:	48 01 f8             	add    %rdi,%rax
    37f3:	48 63 70 40          	movslq 0x40(%rax),%rsi
    37f7:	85 f6                	test   %esi,%esi
    37f9:	7e 27                	jle    3822 <main+0x1232>
    37fb:	48 8b 40 38          	mov    0x38(%rax),%rax
    37ff:	48 c1 e6 09          	shl    $0x9,%rsi
    3803:	48 01 c6             	add    %rax,%rsi
    3806:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3810:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3817:	48 05 00 02 00 00    	add    $0x200,%rax
    381d:	48 39 f0             	cmp    %rsi,%rax
    3820:	75 ee                	jne    3810 <main+0x1220>
    3822:	48 8d 35 bb 3c 00 00 	lea    0x3cbb(%rip),%rsi        # 74e4 <_IO_stdin_used+0x4e4>
    3829:	bf 01 00 00 00       	mov    $0x1,%edi
    382e:	31 c0                	xor    %eax,%eax
    3830:	e8 1b ec ff ff       	call   2450 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3835:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    383a:	bf 01 00 00 00       	mov    $0x1,%edi
    383f:	48 8b 30             	mov    (%rax),%rsi
    3842:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    384c:	48 f7 ee             	imul   %rsi
    384f:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3853:	31 c0                	xor    %eax,%eax
    3855:	48 d1 fa             	sar    %rdx
    3858:	48 29 f2             	sub    %rsi,%rdx
    385b:	48 8d 35 7e 3f 00 00 	lea    0x3f7e(%rip),%rsi        # 77e0 <_IO_stdin_used+0x7e0>
    3862:	e8 e9 eb ff ff       	call   2450 <__printf_chk@plt>
    3867:	bf 0a 00 00 00       	mov    $0xa,%edi
    386c:	e8 5f ea ff ff       	call   22d0 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3871:	41 8b 56 40          	mov    0x40(%r14),%edx
    3875:	85 d2                	test   %edx,%edx
    3877:	7e 63                	jle    38dc <main+0x12ec>
    3879:	49 8b 46 38          	mov    0x38(%r14),%rax
    387d:	48 63 f2             	movslq %edx,%rsi
    3880:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3885:	48 c1 e6 09          	shl    $0x9,%rsi
    3889:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    388e:	48 01 c6             	add    %rax,%rsi
    3891:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3898:	48 8b 90 70 01 00 00 	mov    0x170(%rax),%rdx
        total += thread_data[x].tasks[n].n;
    389f:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    38a6:	48 05 00 02 00 00    	add    $0x200,%rax
        ingests += thread_data[x].tasks[n].ingest_count;
    38ac:	48 03 88 68 ff ff ff 	add    -0x98(%rax),%rcx
        sends += thread_data[x].tasks[n].sends;
    38b3:	4c 03 b8 78 ff ff ff 	add    -0x88(%rax),%r15
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    38ba:	48 03 5a 30          	add    0x30(%rdx),%rbx
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    38be:	48 03 6a 38          	add    0x38(%rdx),%rbp
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    38c2:	48 03 5a 78          	add    0x78(%rdx),%rbx
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    38c6:	48 03 aa 80 00 00 00 	add    0x80(%rdx),%rbp
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    38cd:	48 39 c6             	cmp    %rax,%rsi
    38d0:	75 c6                	jne    3898 <main+0x12a8>
    38d2:	48 89 4c 24 28       	mov    %rcx,0x28(%rsp)
    38d7:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    38dc:	45 31 ed             	xor    %r13d,%r13d
    38df:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    38e7:	7e 7f                	jle    3968 <main+0x1378>
    38e9:	4c 89 ef             	mov    %r13,%rdi
    38ec:	48 89 e8             	mov    %rbp,%rax
    38ef:	49 89 dd             	mov    %rbx,%r13
    38f2:	4c 89 f5             	mov    %r14,%rbp
    38f5:	48 89 fb             	mov    %rdi,%rbx
    38f8:	49 89 c6             	mov    %rax,%r14
    38fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3900:	48 8b 85 90 00 00 00 	mov    0x90(%rbp),%rax
    3907:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    390b:	48 83 ec 08          	sub    $0x8,%rsp
    390f:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3914:	48 83 c3 01          	add    $0x1,%rbx
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3918:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    391c:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3920:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3924:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3927:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    392b:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    392e:	49 f7 e4             	mul    %r12
    3931:	8b 49 20             	mov    0x20(%rcx),%ecx
    3934:	56                   	push   %rsi
    3935:	31 c0                	xor    %eax,%eax
    3937:	48 8d 35 c2 3e 00 00 	lea    0x3ec2(%rip),%rsi        # 7800 <_IO_stdin_used+0x800>
    393e:	48 c1 ea 12          	shr    $0x12,%rdx
    3942:	49 89 d1             	mov    %rdx,%r9
    3945:	ba 02 00 00 00       	mov    $0x2,%edx
    394a:	e8 01 eb ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    394f:	41 58                	pop    %r8
    3951:	41 59                	pop    %r9
    3953:	48 39 9d a0 00 00 00 	cmp    %rbx,0xa0(%rbp)
    395a:	7f a4                	jg     3900 <main+0x1310>
    395c:	4c 89 f0             	mov    %r14,%rax
    395f:	4c 89 eb             	mov    %r13,%rbx
    3962:	49 89 ee             	mov    %rbp,%r14
    3965:	48 89 c5             	mov    %rax,%rbp
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3968:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    396f:	85 f6                	test   %esi,%esi
    3971:	0f 8e 0c 01 00 00    	jle    3a83 <main+0x1493>
    3977:	48 89 5c 24 60       	mov    %rbx,0x60(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    397c:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    3980:	31 d2                	xor    %edx,%edx
    3982:	4c 89 7c 24 68       	mov    %r15,0x68(%rsp)
    3987:	48 89 6c 24 70       	mov    %rbp,0x70(%rsp)
    398c:	0f 1f 40 00          	nopl   0x0(%rax)
    3990:	49 8b 04 d1          	mov    (%r9,%rdx,8),%rax
    3994:	89 d3                	mov    %edx,%ebx
    3996:	4c 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%r15
    399e:	44 8b 00             	mov    (%rax),%r8d
    39a1:	45 85 c0             	test   %r8d,%r8d
    39a4:	0f 8e be 00 00 00    	jle    3a68 <main+0x1478>
    39aa:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    39af:	48 8b 48 08          	mov    0x8(%rax),%rcx
    39b3:	31 c0                	xor    %eax,%eax
    39b5:	48 89 c6             	mov    %rax,%rsi
    39b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    39c0:	48 89 f5             	mov    %rsi,%rbp
    39c3:	45 31 ed             	xor    %r13d,%r13d
    39c6:	48 c1 e5 08          	shl    $0x8,%rbp
    39ca:	48 8d 14 29          	lea    (%rcx,%rbp,1),%rdx
    39ce:	8b 82 94 00 00 00    	mov    0x94(%rdx),%eax
    39d4:	85 c0                	test   %eax,%eax
    39d6:	7e 77                	jle    3a4f <main+0x145f>
    39d8:	48 89 34 24          	mov    %rsi,(%rsp)
    39dc:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    39e0:	4c 89 e9             	mov    %r13,%rcx
    39e3:	48 83 ec 08          	sub    $0x8,%rsp
    39e7:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    39ec:	49 83 c5 01          	add    $0x1,%r13
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    39f0:	48 c1 e1 05          	shl    $0x5,%rcx
    39f4:	48 03 8a 88 00 00 00 	add    0x88(%rdx),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    39fb:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    39ff:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3a03:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3a06:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3a0a:	4c 2b 01             	sub    (%rcx),%r8
    3a0d:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3a0e:	49 f7 e4             	mul    %r12
    3a11:	89 d9                	mov    %ebx,%ecx
    3a13:	48 8d 35 36 3e 00 00 	lea    0x3e36(%rip),%rsi        # 7850 <_IO_stdin_used+0x850>
    3a1a:	31 c0                	xor    %eax,%eax
    3a1c:	48 c1 ea 12          	shr    $0x12,%rdx
    3a20:	49 89 d1             	mov    %rdx,%r9
    3a23:	ba 02 00 00 00       	mov    $0x2,%edx
    3a28:	e8 23 ea ff ff       	call   2450 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3a2d:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    3a31:	5e                   	pop    %rsi
    3a32:	5f                   	pop    %rdi
    3a33:	4b 8b 04 39          	mov    (%r9,%r15,1),%rax
    3a37:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3a3b:	48 8d 14 29          	lea    (%rcx,%rbp,1),%rdx
    3a3f:	44 39 aa 94 00 00 00 	cmp    %r13d,0x94(%rdx)
    3a46:	7f 98                	jg     39e0 <main+0x13f0>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3a48:	48 8b 34 24          	mov    (%rsp),%rsi
    3a4c:	44 8b 00             	mov    (%rax),%r8d
    3a4f:	48 83 c6 01          	add    $0x1,%rsi
    3a53:	41 39 f0             	cmp    %esi,%r8d
    3a56:	0f 8f 64 ff ff ff    	jg     39c0 <main+0x13d0>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3a5c:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    3a61:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    3a68:	48 83 c2 01          	add    $0x1,%rdx
    3a6c:	39 d6                	cmp    %edx,%esi
    3a6e:	0f 8f 1c ff ff ff    	jg     3990 <main+0x13a0>
    3a74:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
    3a79:	4c 8b 7c 24 68       	mov    0x68(%rsp),%r15
    3a7e:	48 8b 6c 24 70       	mov    0x70(%rsp),%rbp
    for (int d = 0 ; d < threads_per_group ; d++) {
    3a83:	48 83 44 24 20 18    	addq   $0x18,0x20(%rsp)
    3a89:	8b 7c 24 50          	mov    0x50(%rsp),%edi
    3a8d:	49 81 c6 c0 00 00 00 	add    $0xc0,%r14
    3a94:	39 7c 24 40          	cmp    %edi,0x40(%rsp)
    3a98:	0f 85 cf fc ff ff    	jne    376d <main+0x117d>
  for (int k = 0 ; k < group_count ; k++) {
    3a9e:	48 89 1c 24          	mov    %rbx,(%rsp)
    3aa2:	48 89 eb             	mov    %rbp,%rbx
    3aa5:	48 8b 6c 24 48       	mov    0x48(%rsp),%rbp
    3aaa:	4d 89 fa             	mov    %r15,%r10
    3aad:	4c 8b 5c 24 28       	mov    0x28(%rsp),%r11
    3ab2:	48 85 ed             	test   %rbp,%rbp
    3ab5:	75 0a                	jne    3ac1 <main+0x14d1>
    3ab7:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
    3abc:	e9 61 fc ff ff       	jmp    3722 <main+0x1132>
    3ac1:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    3ac6:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
    3acb:	48 8d 35 1f 3a 00 00 	lea    0x3a1f(%rip),%rsi        # 74f1 <_IO_stdin_used+0x4f1>
    3ad2:	31 c0                	xor    %eax,%eax
    3ad4:	bf 01 00 00 00       	mov    $0x1,%edi
    3ad9:	4c 89 5c 24 20       	mov    %r11,0x20(%rsp)
    3ade:	4c 89 fa             	mov    %r15,%rdx
    3ae1:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3ae6:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    3af0:	e8 5b e9 ff ff       	call   2450 <__printf_chk@plt>
    3af5:	bf 0a 00 00 00       	mov    $0xa,%edi
    3afa:	e8 d1 e7 ff ff       	call   22d0 <putchar@plt>
    3aff:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    3b04:	bf 01 00 00 00       	mov    $0x1,%edi
    3b09:	48 8d 35 98 3d 00 00 	lea    0x3d98(%rip),%rsi        # 78a8 <_IO_stdin_used+0x8a8>
    3b10:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3b14:	31 c0                	xor    %eax,%eax
    3b16:	e8 35 e9 ff ff       	call   2450 <__printf_chk@plt>
    3b1b:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    3b20:	bf 01 00 00 00       	mov    $0x1,%edi
    3b25:	48 8d 35 a4 3d 00 00 	lea    0x3da4(%rip),%rsi        # 78d0 <_IO_stdin_used+0x8d0>
    3b2c:	4c 89 d8             	mov    %r11,%rax
    3b2f:	49 c1 fb 3f          	sar    $0x3f,%r11
    3b33:	48 f7 eb             	imul   %rbx
    3b36:	31 c0                	xor    %eax,%eax
    3b38:	48 d1 fa             	sar    %rdx
    3b3b:	4c 29 da             	sub    %r11,%rdx
    3b3e:	e8 0d e9 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3b43:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3b48:	bf 01 00 00 00       	mov    $0x1,%edi
    3b4d:	48 8d 35 ac 3d 00 00 	lea    0x3dac(%rip),%rsi        # 7900 <_IO_stdin_used+0x900>
    3b54:	4c 89 c8             	mov    %r9,%rax
    3b57:	49 c1 f9 3f          	sar    $0x3f,%r9
    3b5b:	48 f7 eb             	imul   %rbx
    3b5e:	31 c0                	xor    %eax,%eax
    3b60:	48 d1 fa             	sar    %rdx
    3b63:	4c 29 ca             	sub    %r9,%rdx
    3b66:	e8 e5 e8 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3b6b:	4c 89 f8             	mov    %r15,%rax
    3b6e:	bf 01 00 00 00       	mov    $0x1,%edi
    3b73:	48 8d 35 b6 3d 00 00 	lea    0x3db6(%rip),%rsi        # 7930 <_IO_stdin_used+0x930>
    3b7a:	48 f7 eb             	imul   %rbx
    3b7d:	4c 89 f8             	mov    %r15,%rax
    3b80:	48 c1 f8 3f          	sar    $0x3f,%rax
    3b84:	48 d1 fa             	sar    %rdx
    3b87:	48 29 c2             	sub    %rax,%rdx
    3b8a:	31 c0                	xor    %eax,%eax
    3b8c:	e8 bf e8 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3b91:	48 8b 04 24          	mov    (%rsp),%rax
    3b95:	bf 01 00 00 00       	mov    $0x1,%edi
    3b9a:	48 8d 35 64 39 00 00 	lea    0x3964(%rip),%rsi        # 7505 <_IO_stdin_used+0x505>
    3ba1:	48 f7 eb             	imul   %rbx
    3ba4:	48 8b 04 24          	mov    (%rsp),%rax
    3ba8:	48 c1 f8 3f          	sar    $0x3f,%rax
    3bac:	48 d1 fa             	sar    %rdx
    3baf:	48 29 c2             	sub    %rax,%rdx
    3bb2:	31 c0                	xor    %eax,%eax
    3bb4:	e8 97 e8 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3bb9:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    3bbe:	bf 01 00 00 00       	mov    $0x1,%edi
    3bc3:	48 8d 35 4c 39 00 00 	lea    0x394c(%rip),%rsi        # 7516 <_IO_stdin_used+0x516>
    3bca:	4c 89 d0             	mov    %r10,%rax
    3bcd:	48 f7 eb             	imul   %rbx
    3bd0:	4c 89 d0             	mov    %r10,%rax
    3bd3:	48 c1 f8 3f          	sar    $0x3f,%rax
    3bd7:	48 d1 fa             	sar    %rdx
    3bda:	48 29 c2             	sub    %rax,%rdx
    3bdd:	31 c0                	xor    %eax,%eax
    3bdf:	e8 6c e8 ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3be4:	48 8b 84 24 b8 00 00 00 	mov    0xb8(%rsp),%rax
    3bec:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3bf5:	75 25                	jne    3c1c <main+0x162c>
    3bf7:	48 81 c4 c8 00 00 00 	add    $0xc8,%rsp
    3bfe:	31 c0                	xor    %eax,%eax
    3c00:	5b                   	pop    %rbx
    3c01:	5d                   	pop    %rbp
    3c02:	41 5c                	pop    %r12
    3c04:	41 5d                	pop    %r13
    3c06:	41 5e                	pop    %r14
    3c08:	41 5f                	pop    %r15
    3c0a:	c3                   	ret
      long v = 0;
    3c0b:	31 d2                	xor    %edx,%edx
    3c0d:	e9 d0 fb ff ff       	jmp    37e2 <main+0x11f2>
            exit(1);
    3c12:	bf 01 00 00 00       	mov    $0x1,%edi
    3c17:	e8 84 e8 ff ff       	call   24a0 <exit@plt>
}
    3c1c:	e8 0f e7 ff ff       	call   2330 <__stack_chk_fail@plt>
    3c21:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3c2b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003c30 <_start>:
    3c30:	f3 0f 1e fa          	endbr64
    3c34:	31 ed                	xor    %ebp,%ebp
    3c36:	49 89 d1             	mov    %rdx,%r9
    3c39:	5e                   	pop    %rsi
    3c3a:	48 89 e2             	mov    %rsp,%rdx
    3c3d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3c41:	50                   	push   %rax
    3c42:	54                   	push   %rsp
    3c43:	45 31 c0             	xor    %r8d,%r8d
    3c46:	31 c9                	xor    %ecx,%ecx
    3c48:	48 8d 3d a1 e9 ff ff 	lea    -0x165f(%rip),%rdi        # 25f0 <main>
    3c4f:	ff 15 83 63 00 00    	call   *0x6383(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3c55:	f4                   	hlt
    3c56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003c60 <deregister_tm_clones>:
    3c60:	48 8d 3d b9 63 00 00 	lea    0x63b9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3c67:	48 8d 05 b2 63 00 00 	lea    0x63b2(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    3c6e:	48 39 f8             	cmp    %rdi,%rax
    3c71:	74 15                	je     3c88 <deregister_tm_clones+0x28>
    3c73:	48 8b 05 66 63 00 00 	mov    0x6366(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    3c7a:	48 85 c0             	test   %rax,%rax
    3c7d:	74 09                	je     3c88 <deregister_tm_clones+0x28>
    3c7f:	ff e0                	jmp    *%rax
    3c81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3c88:	c3                   	ret
    3c89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c90 <register_tm_clones>:
    3c90:	48 8d 3d 89 63 00 00 	lea    0x6389(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3c97:	48 8d 35 82 63 00 00 	lea    0x6382(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    3c9e:	48 29 fe             	sub    %rdi,%rsi
    3ca1:	48 89 f0             	mov    %rsi,%rax
    3ca4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3ca8:	48 c1 f8 03          	sar    $0x3,%rax
    3cac:	48 01 c6             	add    %rax,%rsi
    3caf:	48 d1 fe             	sar    %rsi
    3cb2:	74 14                	je     3cc8 <register_tm_clones+0x38>
    3cb4:	48 8b 05 35 63 00 00 	mov    0x6335(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    3cbb:	48 85 c0             	test   %rax,%rax
    3cbe:	74 08                	je     3cc8 <register_tm_clones+0x38>
    3cc0:	ff e0                	jmp    *%rax
    3cc2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3cc8:	c3                   	ret
    3cc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003cd0 <__do_global_dtors_aux>:
    3cd0:	f3 0f 1e fa          	endbr64
    3cd4:	80 3d 4d 63 00 00 00 	cmpb   $0x0,0x634d(%rip)        # a028 <completed.0>
    3cdb:	75 2b                	jne    3d08 <__do_global_dtors_aux+0x38>
    3cdd:	55                   	push   %rbp
    3cde:	48 83 3d 12 63 00 00 00 	cmpq   $0x0,0x6312(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3ce6:	48 89 e5             	mov    %rsp,%rbp
    3ce9:	74 0c                	je     3cf7 <__do_global_dtors_aux+0x27>
    3ceb:	48 8b 3d 16 63 00 00 	mov    0x6316(%rip),%rdi        # a008 <__dso_handle>
    3cf2:	e8 b9 e5 ff ff       	call   22b0 <__cxa_finalize@plt>
    3cf7:	e8 64 ff ff ff       	call   3c60 <deregister_tm_clones>
    3cfc:	c6 05 25 63 00 00 01 	movb   $0x1,0x6325(%rip)        # a028 <completed.0>
    3d03:	5d                   	pop    %rbp
    3d04:	c3                   	ret
    3d05:	0f 1f 00             	nopl   (%rax)
    3d08:	c3                   	ret
    3d09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003d10 <frame_dummy>:
    3d10:	f3 0f 1e fa          	endbr64
    3d14:	e9 77 ff ff ff       	jmp    3c90 <register_tm_clones>
    3d19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003d20 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3d20:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3d24:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3d2b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    3d2f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3d37:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    3d3b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3d3f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3d46:	48 85 c9             	test   %rcx,%rcx
    3d49:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3d50:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3d54:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3d58:	31 c0                	xor    %eax,%eax
    3d5a:	c3                   	ret
    3d5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003d60 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3d60:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3d64:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    3d6b:	85 c9                	test   %ecx,%ecx
    3d6d:	7e 4f                	jle    3dbe <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3d6f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3d76:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    3d7d:	48 c1 e1 09          	shl    $0x9,%rcx
    3d81:	48 8b 50 18          	mov    0x18(%rax),%rdx
    3d85:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3d89:	48 8b 70 38          	mov    0x38(%rax),%rsi
    3d8d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3d8f:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    3d93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3d98:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3da0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3da8:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3db3:	48 05 00 02 00 00    	add    $0x200,%rax
    3db9:	48 39 c1             	cmp    %rax,%rcx
    3dbc:	75 da                	jne    3d98 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    3dbe:	0f ae f8             	sfence
}
    3dc1:	31 c0                	xor    %eax,%eax
    3dc3:	c3                   	ret
    3dc4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3dcf:	90                   	nop

0000000000003dd0 <external_thread>:
void * external_thread(void *arg) {
    3dd0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3dd4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    3dd8:	0f 85 fb 00 00 00    	jne    3ed9 <external_thread+0x109>
void * external_thread(void *arg) {
    3dde:	41 57                	push   %r15
    3de0:	49 89 ff             	mov    %rdi,%r15
    3de3:	41 56                	push   %r14
    3de5:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    3de7:	4c 8d 2d 16 32 00 00 	lea    0x3216(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    3dee:	41 54                	push   %r12
    3df0:	55                   	push   %rbp
    3df1:	53                   	push   %rbx
    3df2:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    3df6:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    3dfc:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    3e00:	85 c9                	test   %ecx,%ecx
    3e02:	7e 6e                	jle    3e72 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3e04:	45 31 e4             	xor    %r12d,%r12d
    3e07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3e10:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    3e18:	31 db                	xor    %ebx,%ebx
    3e1a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3e1e:	48 8b 06             	mov    (%rsi),%rax
    3e21:	8b 10                	mov    (%rax),%edx
    3e23:	85 d2                	test   %edx,%edx
    3e25:	7e 2a                	jle    3e51 <external_thread+0x81>
    3e27:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    3e2b:	48 89 dd             	mov    %rbx,%rbp
    3e2e:	48 c1 e5 08          	shl    $0x8,%rbp
    3e32:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    3e36:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    3e3d:	45 85 c0             	test   %r8d,%r8d
    3e40:	74 36                	je     3e78 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3e42:	48 83 c3 01          	add    $0x1,%rbx
    3e46:	39 da                	cmp    %ebx,%edx
    3e48:	7f e1                	jg     3e2b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    3e4a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    3e51:	49 83 c4 01          	add    $0x1,%r12
    3e55:	44 39 e1             	cmp    %r12d,%ecx
    3e58:	7f b6                	jg     3e10 <external_thread+0x40>
  while (data->running == 1) {
    3e5a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    3e5f:	74 9f                	je     3e00 <external_thread+0x30>
}
    3e61:	48 83 c4 08          	add    $0x8,%rsp
    3e65:	31 c0                	xor    %eax,%eax
    3e67:	5b                   	pop    %rbx
    3e68:	5d                   	pop    %rbp
    3e69:	41 5c                	pop    %r12
    3e6b:	41 5d                	pop    %r13
    3e6d:	41 5e                	pop    %r14
    3e6f:	41 5f                	pop    %r15
    3e71:	c3                   	ret
  while (data->running == 1) {
    3e72:	eb fe                	jmp    3e72 <external_thread+0xa2>
    3e74:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    3e78:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    3e7b:	48 8b 06             	mov    (%rsi),%rax
    3e7e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    3e82:	48 01 ef             	add    %rbp,%rdi
    3e85:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    3e8c:	48 c1 e6 05          	shl    $0x5,%rsi
    3e90:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    3e97:	bf 04 00 00 00       	mov    $0x4,%edi
    3e9c:	e8 6f e4 ff ff       	call   2310 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    3ea1:	49 8b 47 50          	mov    0x50(%r15),%rax
    3ea5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    3ea9:	48 8b 40 08          	mov    0x8(%rax),%rax
    3ead:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    3eb8:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3ebb:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    3ebf:	48 83 c3 01          	add    $0x1,%rbx
    3ec3:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3ec7:	48 8b 06             	mov    (%rsi),%rax
    3eca:	8b 10                	mov    (%rax),%edx
    3ecc:	39 da                	cmp    %ebx,%edx
    3ece:	0f 8f 53 ff ff ff    	jg     3e27 <external_thread+0x57>
    3ed4:	e9 71 ff ff ff       	jmp    3e4a <external_thread+0x7a>
}
    3ed9:	31 c0                	xor    %eax,%eax
    3edb:	c3                   	ret
    3edc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003ee0 <timer_thread>:
void* timer_thread(void *arg) {
    3ee0:	f3 0f 1e fa          	endbr64
    3ee4:	41 57                	push   %r15
    3ee6:	48 8d 35 23 31 00 00 	lea    0x3123(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3eed:	41 56                	push   %r14
    3eef:	41 55                	push   %r13
    3ef1:	41 54                	push   %r12
    3ef3:	55                   	push   %rbp
    3ef4:	48 89 fd             	mov    %rdi,%rbp
    3ef7:	53                   	push   %rbx
    3ef8:	48 83 ec 58          	sub    $0x58,%rsp
    3efc:	8b 57 04             	mov    0x4(%rdi),%edx
    3eff:	bf 01 00 00 00       	mov    $0x1,%edi
    3f04:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3f0d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3f12:	31 c0                	xor    %eax,%eax
    3f14:	e8 37 e5 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3f19:	66 0f 6f 05 2f 3c 00 00 	movdqa 0x3c2f(%rip),%xmm0        # 7b50 <_IO_stdin_used+0xb50>
    3f21:	ba 88 13 00 00       	mov    $0x1388,%edx
    3f26:	31 c0                	xor    %eax,%eax
    3f28:	48 8d 35 f3 30 00 00 	lea    0x30f3(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3f2f:	bf 01 00 00 00       	mov    $0x1,%edi
    3f34:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3f39:	e8 12 e5 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3f3e:	44 8b 65 44          	mov    0x44(%rbp),%r12d
    3f42:	45 85 e4             	test   %r12d,%r12d
    3f45:	0f 84 9b 00 00 00    	je     3fe6 <timer_thread+0x106>
  int n = 0;
    3f4b:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    3f4e:	45 31 e4             	xor    %r12d,%r12d
    3f51:	49 89 e6             	mov    %rsp,%r14
    y++;
    3f54:	31 db                	xor    %ebx,%ebx
    3f56:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    nanosleep(&preempt , &rem2);
    3f5b:	4c 89 ef             	mov    %r13,%rdi
    3f5e:	4c 89 f6             	mov    %r14,%rsi
    n++;
    3f61:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3f65:	e8 e6 e3 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f6a:	48 63 45 30          	movslq 0x30(%rbp),%rax
    y++;
    3f6e:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f73:	85 c0                	test   %eax,%eax
    3f75:	7e 46                	jle    3fbd <timer_thread+0xdd>
    3f77:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3f7b:	49 c1 e4 09          	shl    $0x9,%r12
    3f7f:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3f83:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3f88:	4c 8b 19             	mov    (%rcx),%r11
    3f8b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f8d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3f91:	99                   	cltd
    3f92:	41 f7 7b 40          	idivl  0x40(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    3f96:	49 8b 73 38          	mov    0x38(%r11),%rsi
    3f9a:	48 63 d2             	movslq %edx,%rdx
    3f9d:	48 c1 e2 09          	shl    $0x9,%rdx
    3fa1:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3fac:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3fb8:	49 39 c8             	cmp    %rcx,%r8
    3fbb:	75 cb                	jne    3f88 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    3fbd:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3fc0:	48 8b 45 18          	mov    0x18(%rbp),%rax
  while (data->running && n < times) {
    3fc4:	44 8b 45 44          	mov    0x44(%rbp),%r8d
    if (y >= data->threads[0]->task_count) {
    3fc8:	48 8b 00             	mov    (%rax),%rax
    y++;
    3fcb:	39 78 40             	cmp    %edi,0x40(%rax)
    3fce:	0f 4e fb             	cmovle %ebx,%edi
    3fd1:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3fd4:	45 85 c0             	test   %r8d,%r8d
    3fd7:	74 0d                	je     3fe6 <timer_thread+0x106>
    3fd9:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    3fe0:	0f 85 75 ff ff ff    	jne    3f5b <timer_thread+0x7b>
    3fe6:	48 8d 3d 4b 30 00 00 	lea    0x304b(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3fed:	e8 fe e2 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3ff2:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    3ff6:	85 d2                	test   %edx,%edx
    3ff8:	7e 6b                	jle    4065 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    3ffa:	48 63 45 40          	movslq 0x40(%rbp),%rax
    3ffe:	85 c0                	test   %eax,%eax
    4000:	7e 63                	jle    4065 <timer_thread+0x185>
    4002:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    4006:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    400a:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4012:	31 c9                	xor    %ecx,%ecx
    4014:	48 89 c6             	mov    %rax,%rsi
    4017:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    401b:	48 8b 40 38          	mov    0x38(%rax),%rax
    401f:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4023:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4029:	74 15                	je     4040 <timer_thread+0x160>
    402b:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4035:	48 05 00 02 00 00    	add    $0x200,%rax
    403b:	48 39 c2             	cmp    %rax,%rdx
    403e:	74 1c                	je     405c <timer_thread+0x17c>
      data->threads[x]->tasks[y].sending = 0;
    4040:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    404a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4050:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4057:	48 39 c2             	cmp    %rax,%rdx
    405a:	75 e4                	jne    4040 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    405c:	48 83 c1 08          	add    $0x8,%rcx
    4060:	48 39 cf             	cmp    %rcx,%rdi
    4063:	75 b2                	jne    4017 <timer_thread+0x137>
  asm volatile ("mfence" ::: "memory");
    4065:	0f ae f0             	mfence
  struct timespec drain = {
    4068:	66 0f 6f 05 f0 3a 00 00 	movdqa 0x3af0(%rip),%xmm0        # 7b60 <_IO_stdin_used+0xb60>
    4070:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4075:	48 63 45 28          	movslq 0x28(%rbp),%rax
    y++;
    4079:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    407e:	85 c0                	test   %eax,%eax
    4080:	7e 4a                	jle    40cc <timer_thread+0x1ec>
    4082:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4086:	4d 63 e4             	movslq %r12d,%r12
    4089:	49 c1 e4 09          	shl    $0x9,%r12
    408d:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4091:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4098:	48 8b 19             	mov    (%rcx),%rbx
    409b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    409d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    40a1:	99                   	cltd
    40a2:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    40a5:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    40a9:	48 63 d2             	movslq %edx,%rdx
    40ac:	48 c1 e2 09          	shl    $0x9,%rdx
    40b0:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    40bb:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    40c7:	49 39 c8             	cmp    %rcx,%r8
    40ca:	75 cc                	jne    4098 <timer_thread+0x1b8>
    asm volatile ("mfence" ::: "memory");
    40cc:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    40cf:	48 8b 45 18          	mov    0x18(%rbp),%rax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    40d3:	8b 4d 30             	mov    0x30(%rbp),%ecx
    y++;
    40d6:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    40d9:	48 8b 00             	mov    (%rax),%rax
    y++;
    40dc:	39 78 40             	cmp    %edi,0x40(%rax)
    40df:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    40e3:	85 c9                	test   %ecx,%ecx
    40e5:	0f 8e 16 01 00 00    	jle    4201 <timer_thread+0x321>
    40eb:	31 db                	xor    %ebx,%ebx
    int all_empty = 1;
    40ed:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    40f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int y = 0 ; y < 2 ; y++) {
    40f8:	45 31 f6             	xor    %r14d,%r14d
    40fb:	41 89 dd             	mov    %ebx,%r13d
    40fe:	4c 8d 3c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r15
    4106:	44 89 f6             	mov    %r14d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4109:	85 c9                	test   %ecx,%ecx
    410b:	0f 8e af 00 00 00    	jle    41c0 <timer_thread+0x2e0>
    4111:	4c 89 f7             	mov    %r14,%rdi
      y = 0;
    4114:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4116:	45 31 c0             	xor    %r8d,%r8d
    4119:	48 c1 e7 09          	shl    $0x9,%rdi
    411d:	0f 1f 00             	nopl   (%rax)
          if (x == k) { continue; }
    4120:	41 39 d8             	cmp    %ebx,%r8d
    4123:	74 36                	je     415b <timer_thread+0x27b>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4125:	48 8b 55 18          	mov    0x18(%rbp),%rdx
    4129:	4a 8b 14 3a          	mov    (%rdx,%r15,1),%rdx
    412d:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4131:	4c 8b 94 3a 70 01 00 00 	mov    0x170(%rdx,%rdi,1),%r10
    4139:	49 01 c2             	add    %rax,%r10
    413c:	4d 8b 0a             	mov    (%r10),%r9
    413f:	49 8b 52 08          	mov    0x8(%r10),%rdx
    4143:	4d 8b 89 80 00 00 00 	mov    0x80(%r9),%r9
    414a:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    4151:	4d 85 c9             	test   %r9,%r9
    4154:	7f 2a                	jg     4180 <timer_thread+0x2a0>
    4156:	48 85 d2             	test   %rdx,%rdx
    4159:	7f 25                	jg     4180 <timer_thread+0x2a0>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    415b:	41 83 c0 01          	add    $0x1,%r8d
    415f:	48 83 c0 48          	add    $0x48,%rax
    4163:	41 39 c8             	cmp    %ecx,%r8d
    4166:	75 b8                	jne    4120 <timer_thread+0x240>
      for (int y = 0 ; y < 2 ; y++) {
    4168:	49 83 fe 01          	cmp    $0x1,%r14
    416c:	74 52                	je     41c0 <timer_thread+0x2e0>
    416e:	49 83 c6 01          	add    $0x1,%r14
    4172:	44 89 f6             	mov    %r14d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4175:	eb 9a                	jmp    4111 <timer_thread+0x231>
    4177:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4180:	48 83 ec 08          	sub    $0x8,%rsp
    4184:	89 f1                	mov    %esi,%ecx
    4186:	bf 01 00 00 00       	mov    $0x1,%edi
    418b:	31 c0                	xor    %eax,%eax
    418d:	52                   	push   %rdx
    418e:	48 8d 35 c8 2e 00 00 	lea    0x2ec8(%rip),%rsi        # 705d <_IO_stdin_used+0x5d>
    4195:	44 89 ea             	mov    %r13d,%edx
    4198:	e8 b3 e2 ff ff       	call   2450 <__printf_chk@plt>
      for (int y = 0 ; y < 2 ; y++) {
    419d:	5a                   	pop    %rdx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    419e:	8b 4d 30             	mov    0x30(%rbp),%ecx
      for (int y = 0 ; y < 2 ; y++) {
    41a1:	5e                   	pop    %rsi
    41a2:	49 83 fe 01          	cmp    $0x1,%r14
    41a6:	74 48                	je     41f0 <timer_thread+0x310>
    41a8:	49 83 c6 01          	add    $0x1,%r14
    41ac:	45 31 db             	xor    %r11d,%r11d
    41af:	44 89 f6             	mov    %r14d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    41b2:	85 c9                	test   %ecx,%ecx
    41b4:	0f 8f 57 ff ff ff    	jg     4111 <timer_thread+0x231>
    41ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    41c0:	48 83 c3 01          	add    $0x1,%rbx
    41c4:	39 d9                	cmp    %ebx,%ecx
    41c6:	0f 8f 2c ff ff ff    	jg     40f8 <timer_thread+0x218>
    if (all_empty == 1) {
    41cc:	41 83 fb 01          	cmp    $0x1,%r11d
    41d0:	74 2f                	je     4201 <timer_thread+0x321>
      nanosleep(&drain , &drainrem);
    41d2:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    41d7:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    41dc:	e8 6f e1 ff ff       	call   2350 <nanosleep@plt>
    41e1:	e9 8f fe ff ff       	jmp    4075 <timer_thread+0x195>
    41e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    41f0:	48 83 c3 01          	add    $0x1,%rbx
    41f4:	45 31 db             	xor    %r11d,%r11d
    41f7:	39 d9                	cmp    %ebx,%ecx
    41f9:	0f 8f f9 fe ff ff    	jg     40f8 <timer_thread+0x218>
    41ff:	eb cb                	jmp    41cc <timer_thread+0x2ec>
    4201:	48 8d 3d 4c 2e 00 00 	lea    0x2e4c(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    4208:	e8 e3 e0 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    420d:	8b 7d 44             	mov    0x44(%rbp),%edi
    4210:	85 ff                	test   %edi,%edi
    4212:	0f 84 e6 00 00 00    	je     42fe <timer_thread+0x41e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4218:	8b 45 2c             	mov    0x2c(%rbp),%eax
    421b:	31 db                	xor    %ebx,%ebx
    421d:	4c 8d 25 50 2e 00 00 	lea    0x2e50(%rip),%r12        # 7074 <_IO_stdin_used+0x74>
    4224:	4c 8d 2d 64 2e 00 00 	lea    0x2e64(%rip),%r13        # 708f <_IO_stdin_used+0x8f>
    422b:	85 c0                	test   %eax,%eax
    422d:	7e 34                	jle    4263 <timer_thread+0x383>
    422f:	90                   	nop
    4230:	31 c0                	xor    %eax,%eax
    4232:	89 da                	mov    %ebx,%edx
    4234:	4c 89 e6             	mov    %r12,%rsi
    4237:	bf 01 00 00 00       	mov    $0x1,%edi
    423c:	e8 0f e2 ff ff       	call   2450 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4241:	48 8b 45 18          	mov    0x18(%rbp),%rax
    4245:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4249:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    424d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4254:	0f 84 d1 00 00 00    	je     432b <timer_thread+0x44b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    425a:	48 83 c3 01          	add    $0x1,%rbx
    425e:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    4261:	7f cd                	jg     4230 <timer_thread+0x350>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4263:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    4267:	85 d2                	test   %edx,%edx
    4269:	7e 7d                	jle    42e8 <timer_thread+0x408>
      for (int y = 0 ; y < data->task_count ; y++) {
    426b:	8b 45 40             	mov    0x40(%rbp),%eax
    426e:	85 c0                	test   %eax,%eax
    4270:	7e 76                	jle    42e8 <timer_thread+0x408>
    4272:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4275:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    4279:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4281:	31 c9                	xor    %ecx,%ecx
    4283:	48 c1 e6 09          	shl    $0x9,%rsi
    4287:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4290:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4294:	48 8b 40 38          	mov    0x38(%rax),%rax
    4298:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    429c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    42a2:	74 1c                	je     42c0 <timer_thread+0x3e0>
    42a4:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    42ae:	48 05 00 02 00 00    	add    $0x200,%rax
    42b4:	48 39 c2             	cmp    %rax,%rdx
    42b7:	74 26                	je     42df <timer_thread+0x3ff>
    42b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    42c0:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    42ca:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    42d0:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    42da:	48 39 c2             	cmp    %rax,%rdx
    42dd:	75 e1                	jne    42c0 <timer_thread+0x3e0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    42df:	48 83 c1 08          	add    $0x8,%rcx
    42e3:	48 39 f9             	cmp    %rdi,%rcx
    42e6:	75 a8                	jne    4290 <timer_thread+0x3b0>
    asm volatile ("mfence" ::: "memory");
    42e8:	0f ae f0             	mfence
    42eb:	48 8d 3d af 2d 00 00 	lea    0x2daf(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    42f2:	e8 f9 df ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    42f7:	c7 45 44 00 00 00 00 	movl   $0x0,0x44(%rbp)
    42fe:	48 8d 3d a3 2d 00 00 	lea    0x2da3(%rip),%rdi        # 70a8 <_IO_stdin_used+0xa8>
    4305:	e8 e6 df ff ff       	call   22f0 <puts@plt>
}
    430a:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    430f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4318:	75 40                	jne    435a <timer_thread+0x47a>
    431a:	48 83 c4 58          	add    $0x58,%rsp
    431e:	31 c0                	xor    %eax,%eax
    4320:	5b                   	pop    %rbx
    4321:	5d                   	pop    %rbp
    4322:	41 5c                	pop    %r12
    4324:	41 5d                	pop    %r13
    4326:	41 5e                	pop    %r14
    4328:	41 5f                	pop    %r15
    432a:	c3                   	ret
    432b:	4c 89 ef             	mov    %r13,%rdi
    432e:	e8 bd df ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4333:	48 8b 45 18          	mov    0x18(%rbp),%rax
    4337:	be 01 00 00 00       	mov    $0x1,%esi
    433c:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4340:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4344:	8b 78 60             	mov    0x60(%rax),%edi
    4347:	e8 b4 e0 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    434c:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    434f:	0f 8f db fe ff ff    	jg     4230 <timer_thread+0x350>
    4355:	e9 09 ff ff ff       	jmp    4263 <timer_thread+0x383>
}
    435a:	e8 d1 df ff ff       	call   2330 <__stack_chk_fail@plt>
    435f:	90                   	nop

0000000000004360 <sendm.part.0>:
int sendm(struct BarrierTask *data) {
    4360:	41 57                	push   %r15
    4362:	41 56                	push   %r14
    4364:	41 55                	push   %r13
    4366:	41 54                	push   %r12
    4368:	55                   	push   %rbp
    4369:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    436a:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    4370:	89 44 24 c8          	mov    %eax,-0x38(%rsp)
    4374:	85 c0                	test   %eax,%eax
    4376:	0f 8e 49 01 00 00    	jle    44c5 <sendm.part.0+0x165>
        if (n == data->thread->real_thread_index) { continue; }
    437c:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    4383:	49 89 ff             	mov    %rdi,%r15
    4386:	45 31 e4             	xor    %r12d,%r12d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    4389:	45 31 f6             	xor    %r14d,%r14d
        if (n == data->thread->real_thread_index) { continue; }
    438c:	8b 40 08             	mov    0x8(%rax),%eax
    438f:	89 44 24 cc          	mov    %eax,-0x34(%rsp)
    4393:	48 8d 87 88 01 00 00 	lea    0x188(%rdi),%rax
    439a:	48 89 44 24 e0       	mov    %rax,-0x20(%rsp)
    439f:	48 8d 87 90 01 00 00 	lea    0x190(%rdi),%rax
    43a6:	48 89 44 24 e8       	mov    %rax,-0x18(%rsp)
    43ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    43b0:	44 39 74 24 cc       	cmp    %r14d,-0x34(%rsp)
    43b5:	0f 84 f5 00 00 00    	je     44b0 <sendm.part.0+0x150>
        struct Data *them = data->mailboxes[n].higher;
    43bb:	4d 8b 87 70 01 00 00 	mov    0x170(%r15),%r8
    43c2:	4d 01 e0             	add    %r12,%r8
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    43c5:	45 8b 68 40          	mov    0x40(%r8),%r13d
        struct Data *them = data->mailboxes[n].higher;
    43c9:	4d 8b 48 08          	mov    0x8(%r8),%r9
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    43cd:	41 83 fd 02          	cmp    $0x2,%r13d
    43d1:	0f 84 01 01 00 00    	je     44d8 <sendm.part.0+0x178>
        int min = them->messages_limit;
    43d7:	49 8b 89 88 00 00 00 	mov    0x88(%r9),%rcx
        for (; them->messages_count < min;) {
    43de:	4d 8b 99 80 00 00 00 	mov    0x80(%r9),%r11
        int min = them->messages_limit;
    43e5:	4c 63 d1             	movslq %ecx,%r10
        for (; them->messages_count < min;) {
    43e8:	48 63 c9             	movslq %ecx,%rcx
    43eb:	49 39 cb             	cmp    %rcx,%r11
    43ee:	0f 8d bc 00 00 00    	jge    44b0 <sendm.part.0+0x150>
    43f4:	49 8b 87 08 01 00 00 	mov    0x108(%r15),%rax
    43fb:	4c 89 d6             	mov    %r10,%rsi
          them->messages[them->messages_count++] = data->message; 
    43fe:	49 8b 11             	mov    (%r9),%rdx
    4401:	4c 29 de             	sub    %r11,%rsi
    4404:	48 89 44 24 d0       	mov    %rax,-0x30(%rsp)
    4409:	49 8b 40 30          	mov    0x30(%r8),%rax
    440d:	48 89 44 24 d8       	mov    %rax,-0x28(%rsp)
    4412:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    4416:	48 83 f8 02          	cmp    $0x2,%rax
    441a:	0f 86 58 01 00 00    	jbe    4578 <sendm.part.0+0x218>
    4420:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    4428:	4a 8d 3c d5 00 00 00 00 	lea    0x0(,%r10,8),%rdi
    4430:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
    4434:	48 8d 2c 3a          	lea    (%rdx,%rdi,1),%rbp
    4438:	48 39 6c 24 e0       	cmp    %rbp,-0x20(%rsp)
    443d:	0f 83 c5 00 00 00    	jae    4508 <sendm.part.0+0x1a8>
    4443:	48 8b 6c 24 e8       	mov    -0x18(%rsp),%rbp
    4448:	48 39 eb             	cmp    %rbp,%rbx
    444b:	0f 83 b7 00 00 00    	jae    4508 <sendm.part.0+0x1a8>
    4451:	4c 8d 1c 02          	lea    (%rdx,%rax,1),%r11
    4455:	48 01 d7             	add    %rdx,%rdi
    4458:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4460:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
        for (; them->messages_count < min;) {
    4467:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    446b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    446f:	4c 39 df             	cmp    %r11,%rdi
    4472:	75 ec                	jne    4460 <sendm.part.0+0x100>
    4474:	0f 1f 40 00          	nopl   0x0(%rax)
    4478:	48 8b 7c 24 d0       	mov    -0x30(%rsp),%rdi
    447d:	48 8b 5c 24 d8       	mov    -0x28(%rsp),%rbx
    4482:	48 01 f7             	add    %rsi,%rdi
    4485:	48 01 f3             	add    %rsi,%rbx
    4488:	49 89 bf 08 01 00 00 	mov    %rdi,0x108(%r15)
    448f:	49 89 58 30          	mov    %rbx,0x30(%r8)
    4493:	49 89 89 80 00 00 00 	mov    %rcx,0x80(%r9)
    449a:	4a 89 44 d2 f8       	mov    %rax,-0x8(%rdx,%r10,8)
        if (them->messages_count > 0 && data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    449f:	48 85 c9             	test   %rcx,%rcx
    44a2:	7e 0c                	jle    44b0 <sendm.part.0+0x150>
    44a4:	41 83 fd 02          	cmp    $0x2,%r13d
    44a8:	0f 84 e2 00 00 00    	je     4590 <sendm.part.0+0x230>
    44ae:	66 90                	xchg   %ax,%ax
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    44b0:	8b 44 24 c8          	mov    -0x38(%rsp),%eax
    44b4:	41 83 c6 01          	add    $0x1,%r14d
    44b8:	49 83 c4 48          	add    $0x48,%r12
    44bc:	41 39 c6             	cmp    %eax,%r14d
    44bf:	0f 85 eb fe ff ff    	jne    43b0 <sendm.part.0+0x50>
      asm volatile ("sfence" ::: "memory");
    44c5:	0f ae f8             	sfence
}
    44c8:	5b                   	pop    %rbx
    44c9:	5d                   	pop    %rbp
    44ca:	41 5c                	pop    %r12
    44cc:	41 5d                	pop    %r13
    44ce:	41 5e                	pop    %r14
    44d0:	41 5f                	pop    %r15
    44d2:	c3                   	ret
    44d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    44d8:	41 8b 81 00 01 00 00 	mov    0x100(%r9),%eax
    44df:	85 c0                	test   %eax,%eax
    44e1:	74 cd                	je     44b0 <sendm.part.0+0x150>
        int min = them->messages_limit;
    44e3:	49 8b 89 88 00 00 00 	mov    0x88(%r9),%rcx
        for (; them->messages_count < min;) {
    44ea:	4d 8b 99 80 00 00 00 	mov    0x80(%r9),%r11
        int min = them->messages_limit;
    44f1:	4c 63 d1             	movslq %ecx,%r10
        for (; them->messages_count < min;) {
    44f4:	48 63 c9             	movslq %ecx,%rcx
    44f7:	49 39 cb             	cmp    %rcx,%r11
    44fa:	0f 8c f4 fe ff ff    	jl     43f4 <sendm.part.0+0x94>
    4500:	4c 89 d9             	mov    %r11,%rcx
    4503:	eb 9a                	jmp    449f <sendm.part.0+0x13f>
    4505:	0f 1f 00             	nopl   (%rax)
    4508:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    450f:	48 89 f5             	mov    %rsi,%rbp
    4512:	48 89 df             	mov    %rbx,%rdi
    4515:	48 d1 ed             	shr    %rbp
    4518:	48 c1 e5 04          	shl    $0x4,%rbp
    451c:	66 48 0f 6e c0       	movq   %rax,%xmm0
    4521:	48 89 6c 24 f0       	mov    %rbp,-0x10(%rsp)
    4526:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    452a:	48 01 dd             	add    %rbx,%rbp
    452d:	f6 44 24 f0 10       	testb  $0x10,-0x10(%rsp)
    4532:	74 0c                	je     4540 <sendm.part.0+0x1e0>
          them->messages[them->messages_count++] = data->message; 
    4534:	48 83 c7 10          	add    $0x10,%rdi
    4538:	0f 11 03             	movups %xmm0,(%rbx)
        for (; them->messages_count < min;) {
    453b:	48 39 ef             	cmp    %rbp,%rdi
    453e:	74 10                	je     4550 <sendm.part.0+0x1f0>
          them->messages[them->messages_count++] = data->message; 
    4540:	0f 11 07             	movups %xmm0,(%rdi)
    4543:	48 83 c7 20          	add    $0x20,%rdi
    4547:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    454b:	48 39 ef             	cmp    %rbp,%rdi
    454e:	75 f0                	jne    4540 <sendm.part.0+0x1e0>
    4550:	48 89 f7             	mov    %rsi,%rdi
    4553:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    4557:	4c 01 df             	add    %r11,%rdi
    455a:	40 f6 c6 01          	test   $0x1,%sil
    455e:	0f 84 14 ff ff ff    	je     4478 <sendm.part.0+0x118>
          them->messages[them->messages_count++] = data->message; 
    4564:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    456b:	48 89 04 fa          	mov    %rax,(%rdx,%rdi,8)
        for (; them->messages_count < min;) {
    456f:	e9 04 ff ff ff       	jmp    4478 <sendm.part.0+0x118>
    4574:	0f 1f 40 00          	nopl   0x0(%rax)
    4578:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    4580:	4a 8d 3c d5 00 00 00 00 	lea    0x0(,%r10,8),%rdi
    4588:	e9 c4 fe ff ff       	jmp    4451 <sendm.part.0+0xf1>
    458d:	0f 1f 00             	nopl   (%rax)
        if (them->messages_count > 0 && data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    4590:	41 83 b9 00 01 00 00 01 	cmpl   $0x1,0x100(%r9)
    4598:	0f 85 12 ff ff ff    	jne    44b0 <sendm.part.0+0x150>
          them->available_sending = 0;
    459e:	41 c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r9)
          them->available_receiving = 1;
    45a9:	41 c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r9)
          them->finished_reading = 0;
    45b4:	41 c7 81 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%r9)
    45bf:	e9 ec fe ff ff       	jmp    44b0 <sendm.part.0+0x150>
    45c4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    45cf:	90                   	nop

00000000000045d0 <strtolower>:
void strtolower(char *str) {
    45d0:	f3 0f 1e fa          	endbr64
    45d4:	55                   	push   %rbp
    45d5:	53                   	push   %rbx
    45d6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    45da:	48 0f be 1f          	movsbq (%rdi),%rbx
    45de:	84 db                	test   %bl,%bl
    45e0:	74 24                	je     4606 <strtolower+0x36>
    45e2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    45e5:	e8 26 df ff ff       	call   2510 <__ctype_tolower_loc@plt>
    45ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    45f0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    45f3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    45f7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    45fa:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    45fd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4602:	84 db                	test   %bl,%bl
    4604:	75 ea                	jne    45f0 <strtolower+0x20>
}
    4606:	48 83 c4 08          	add    $0x8,%rsp
    460a:	5b                   	pop    %rbx
    460b:	5d                   	pop    %rbp
    460c:	c3                   	ret
    460d:	0f 1f 00             	nopl   (%rax)

0000000000004610 <zh_malloc>:
void *zh_malloc(size_t size) {
    4610:	f3 0f 1e fa          	endbr64
    4614:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4618:	e8 f3 dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    461d:	48 85 c0             	test   %rax,%rax
    4620:	74 05                	je     4627 <zh_malloc+0x17>
}
    4622:	48 83 c4 08          	add    $0x8,%rsp
    4626:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4627:	48 8b 0d f2 59 00 00 	mov    0x59f2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    462e:	ba 28 00 00 00       	mov    $0x28,%edx
    4633:	be 01 00 00 00       	mov    $0x1,%esi
    4638:	48 8d 3d f1 2e 00 00 	lea    0x2ef1(%rip),%rdi        # 7530 <_IO_stdin_used+0x530>
    463f:	e8 7c de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4644:	bf 01 00 00 00       	mov    $0x1,%edi
    4649:	e8 52 de ff ff       	call   24a0 <exit@plt>
    464e:	66 90                	xchg   %ax,%ax

0000000000004650 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4650:	f3 0f 1e fa          	endbr64
    4654:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4655:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    465a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    465d:	e8 fe dc ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4662:	48 85 c0             	test   %rax,%rax
    4665:	74 11                	je     4678 <get_filename_ext+0x28>
    4667:	48 39 c3             	cmp    %rax,%rbx
    466a:	74 0c                	je     4678 <get_filename_ext+0x28>
    return dot + 1;
    466c:	48 83 c0 01          	add    $0x1,%rax
}
    4670:	5b                   	pop    %rbx
    4671:	c3                   	ret
    4672:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4678:	48 8d 05 71 2a 00 00 	lea    0x2a71(%rip),%rax        # 70f0 <_IO_stdin_used+0xf0>
}
    467f:	5b                   	pop    %rbx
    4680:	c3                   	ret
    4681:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    468c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004690 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4690:	f3 0f 1e fa          	endbr64
    4694:	41 55                	push   %r13
    4696:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4699:	48 89 fe             	mov    %rdi,%rsi
    469c:	41 54                	push   %r12
    469e:	55                   	push   %rbp
    469f:	48 89 d5             	mov    %rdx,%rbp
    46a2:	ba 00 04 00 00       	mov    $0x400,%edx
    46a7:	53                   	push   %rbx
    46a8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    46af:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    46b8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    46c0:	31 c0                	xor    %eax,%eax
    46c2:	49 89 e4             	mov    %rsp,%r12
    46c5:	4c 89 e7             	mov    %r12,%rdi
    46c8:	e8 63 dd ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    46cd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    46d2:	84 db                	test   %bl,%bl
    46d4:	74 24                	je     46fa <send_headers+0x6a>
        *str = (char)tolower(*str);
    46d6:	e8 35 de ff ff       	call   2510 <__ctype_tolower_loc@plt>
    46db:	48 8b 08             	mov    (%rax),%rcx
    46de:	4c 89 e0             	mov    %r12,%rax
    46e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    46e8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    46eb:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    46ef:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    46f2:	48 0f be 18          	movsbq (%rax),%rbx
    46f6:	84 db                	test   %bl,%bl
    46f8:	75 ee                	jne    46e8 <send_headers+0x58>
    void *buf = malloc(size);
    46fa:	bf 11 00 00 00       	mov    $0x11,%edi
    46ff:	e8 0c dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4704:	48 85 c0             	test   %rax,%rax
    4707:	0f 84 7e 04 00 00    	je     4b8b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    470d:	66 0f 6f 05 5b 34 00 00 	movdqa 0x345b(%rip),%xmm0        # 7b70 <_IO_stdin_used+0xb70>
    iov[0].iov_base = zh_malloc(slen);
    4715:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4719:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    471e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4726:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    472a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    472d:	e8 de dc ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4732:	48 85 c0             	test   %rax,%rax
    4735:	0f 84 50 04 00 00    	je     4b8b <send_headers+0x4fb>
    473b:	66 0f 6f 05 3d 34 00 00 	movdqa 0x343d(%rip),%xmm0        # 7b80 <_IO_stdin_used+0xb80>
    iov[1].iov_base = zh_malloc(slen);
    4743:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4747:	4c 89 e7             	mov    %r12,%rdi
    474a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4754:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    475c:	0f 11 00             	movups %xmm0,(%rax)
    475f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4763:	be 2e 00 00 00       	mov    $0x2e,%esi
    4768:	e8 f3 db ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    476d:	48 85 c0             	test   %rax,%rax
    4770:	0f 84 ea 02 00 00    	je     4a60 <send_headers+0x3d0>
    4776:	4c 39 e0             	cmp    %r12,%rax
    4779:	0f 84 e1 02 00 00    	je     4a60 <send_headers+0x3d0>
    return dot + 1;
    477f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4783:	48 8d 3d 34 29 00 00 	lea    0x2934(%rip),%rdi        # 70be <_IO_stdin_used+0xbe>
    478a:	48 89 de             	mov    %rbx,%rsi
    478d:	e8 1e dc ff ff       	call   23b0 <strcmp@plt>
    4792:	85 c0                	test   %eax,%eax
    4794:	75 20                	jne    47b6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4796:	66 0f 6f 05 f2 33 00 00 	movdqa 0x33f2(%rip),%xmm0        # 7b90 <_IO_stdin_used+0xb90>
    479e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    47a6:	66 0f 6f 05 f2 33 00 00 	movdqa 0x33f2(%rip),%xmm0        # 7ba0 <_IO_stdin_used+0xba0>
    47ae:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    47b6:	48 89 de             	mov    %rbx,%rsi
    47b9:	48 8d 3d 02 29 00 00 	lea    0x2902(%rip),%rdi        # 70c2 <_IO_stdin_used+0xc2>
    47c0:	e8 eb db ff ff       	call   23b0 <strcmp@plt>
    47c5:	85 c0                	test   %eax,%eax
    47c7:	75 20                	jne    47e9 <send_headers+0x159>
    47c9:	66 0f 6f 05 bf 33 00 00 	movdqa 0x33bf(%rip),%xmm0        # 7b90 <_IO_stdin_used+0xb90>
    47d1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    47d9:	66 0f 6f 05 bf 33 00 00 	movdqa 0x33bf(%rip),%xmm0        # 7ba0 <_IO_stdin_used+0xba0>
    47e1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    47e9:	48 89 de             	mov    %rbx,%rsi
    47ec:	48 8d 3d d4 28 00 00 	lea    0x28d4(%rip),%rdi        # 70c7 <_IO_stdin_used+0xc7>
    47f3:	e8 b8 db ff ff       	call   23b0 <strcmp@plt>
    47f8:	85 c0                	test   %eax,%eax
    47fa:	0f 84 10 02 00 00    	je     4a10 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4800:	48 89 de             	mov    %rbx,%rsi
    4803:	48 8d 3d c1 28 00 00 	lea    0x28c1(%rip),%rdi        # 70cb <_IO_stdin_used+0xcb>
    480a:	e8 a1 db ff ff       	call   23b0 <strcmp@plt>
    480f:	85 c0                	test   %eax,%eax
    4811:	0f 84 a9 02 00 00    	je     4ac0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4817:	48 89 de             	mov    %rbx,%rsi
    481a:	48 8d 3d ae 28 00 00 	lea    0x28ae(%rip),%rdi        # 70cf <_IO_stdin_used+0xcf>
    4821:	e8 8a db ff ff       	call   23b0 <strcmp@plt>
    4826:	85 c0                	test   %eax,%eax
    4828:	0f 84 6a 02 00 00    	je     4a98 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    482e:	48 89 de             	mov    %rbx,%rsi
    4831:	48 8d 3d da 28 00 00 	lea    0x28da(%rip),%rdi        # 7112 <_IO_stdin_used+0x112>
    4838:	e8 73 db ff ff       	call   23b0 <strcmp@plt>
    483d:	85 c0                	test   %eax,%eax
    483f:	0f 84 2b 02 00 00    	je     4a70 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4845:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4848:	0f 84 52 01 00 00    	je     49a0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    484e:	48 89 de             	mov    %rbx,%rsi
    4851:	48 8d 3d 7b 28 00 00 	lea    0x287b(%rip),%rdi        # 70d3 <_IO_stdin_used+0xd3>
    4858:	e8 53 db ff ff       	call   23b0 <strcmp@plt>
    485d:	85 c0                	test   %eax,%eax
    485f:	0f 84 ab 02 00 00    	je     4b10 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4865:	48 89 de             	mov    %rbx,%rsi
    4868:	48 8d 3d 68 28 00 00 	lea    0x2868(%rip),%rdi        # 70d7 <_IO_stdin_used+0xd7>
    486f:	e8 3c db ff ff       	call   23b0 <strcmp@plt>
    4874:	85 c0                	test   %eax,%eax
    4876:	0f 84 6c 02 00 00    	je     4ae8 <send_headers+0x458>
    slen = strlen(send_buffer);
    487c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4884:	4c 89 e7             	mov    %r12,%rdi
    4887:	e8 94 da ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    488c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    488f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4892:	e8 79 db ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4897:	48 85 c0             	test   %rax,%rax
    489a:	0f 84 eb 02 00 00    	je     4b8b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    48a0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    48a4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    48a8:	83 fb 08             	cmp    $0x8,%ebx
    48ab:	0f 83 3f 01 00 00    	jae    49f0 <send_headers+0x360>
    48b1:	f6 c3 04             	test   $0x4,%bl
    48b4:	0f 85 7b 02 00 00    	jne    4b35 <send_headers+0x4a5>
    48ba:	85 db                	test   %ebx,%ebx
    48bc:	74 13                	je     48d1 <send_headers+0x241>
    48be:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    48c6:	88 10                	mov    %dl,(%rax)
    48c8:	f6 c3 02             	test   $0x2,%bl
    48cb:	0f 85 96 02 00 00    	jne    4b67 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    48d1:	4d 89 e8             	mov    %r13,%r8
    48d4:	48 8d 0d 00 28 00 00 	lea    0x2800(%rip),%rcx        # 70db <_IO_stdin_used+0xdb>
    48db:	4c 89 e7             	mov    %r12,%rdi
    48de:	31 c0                	xor    %eax,%eax
    48e0:	ba 00 04 00 00       	mov    $0x400,%edx
    48e5:	be 01 00 00 00       	mov    $0x1,%esi
    48ea:	e8 31 dc ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    48ef:	4c 89 e7             	mov    %r12,%rdi
    48f2:	e8 29 da ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    48f7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    48fa:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    48fd:	e8 0e db ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4902:	48 85 c0             	test   %rax,%rax
    4905:	0f 84 80 02 00 00    	je     4b8b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    490b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    490f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4913:	83 fb 08             	cmp    $0x8,%ebx
    4916:	0f 83 1c 01 00 00    	jae    4a38 <send_headers+0x3a8>
    491c:	f6 c3 04             	test   $0x4,%bl
    491f:	0f 85 29 02 00 00    	jne    4b4e <send_headers+0x4be>
    4925:	85 db                	test   %ebx,%ebx
    4927:	74 13                	je     493c <send_headers+0x2ac>
    4929:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4931:	88 10                	mov    %dl,(%rax)
    4933:	f6 c3 02             	test   $0x2,%bl
    4936:	0f 85 3d 02 00 00    	jne    4b79 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    493c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4941:	bf 02 00 00 00       	mov    $0x2,%edi
    4946:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    494e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4956:	e8 b5 da ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    495b:	48 85 c0             	test   %rax,%rax
    495e:	0f 84 27 02 00 00    	je     4b8b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4964:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    496c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4970:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4978:	66 89 10             	mov    %dx,(%rax)
}
    497b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4983:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    498c:	0f 85 20 02 00 00    	jne    4bb2 <send_headers+0x522>
    4992:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4999:	5b                   	pop    %rbx
    499a:	5d                   	pop    %rbp
    499b:	41 5c                	pop    %r12
    499d:	41 5d                	pop    %r13
    499f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    49a0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    49a4:	0f 85 a4 fe ff ff    	jne    484e <send_headers+0x1be>
    49aa:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    49ae:	0f 85 9a fe ff ff    	jne    484e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    49b4:	66 0f 6f 05 34 32 00 00 	movdqa 0x3234(%rip),%xmm0        # 7bf0 <_IO_stdin_used+0xbf0>
    49bc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    49c6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    49ce:	66 0f 6f 05 2a 32 00 00 	movdqa 0x322a(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    49d6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    49de:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    49e6:	e9 63 fe ff ff       	jmp    484e <send_headers+0x1be>
    49eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    49f0:	89 da                	mov    %ebx,%edx
    49f2:	48 89 c7             	mov    %rax,%rdi
    49f5:	4c 89 e6             	mov    %r12,%rsi
    49f8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    49fd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4a02:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4a05:	c1 e9 03             	shr    $0x3,%ecx
    4a08:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4a0b:	e9 c1 fe ff ff       	jmp    48d1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a10:	66 0f 6f 05 78 31 00 00 	movdqa 0x3178(%rip),%xmm0        # 7b90 <_IO_stdin_used+0xb90>
    4a18:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a20:	66 0f 6f 05 88 31 00 00 	movdqa 0x3188(%rip),%xmm0        # 7bb0 <_IO_stdin_used+0xbb0>
    4a28:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a30:	e9 cb fd ff ff       	jmp    4800 <send_headers+0x170>
    4a35:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4a38:	89 da                	mov    %ebx,%edx
    4a3a:	48 89 c7             	mov    %rax,%rdi
    4a3d:	4c 89 e6             	mov    %r12,%rsi
    4a40:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4a45:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4a4a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4a4d:	c1 e9 03             	shr    $0x3,%ecx
    4a50:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4a53:	e9 e4 fe ff ff       	jmp    493c <send_headers+0x2ac>
    4a58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4a60:	48 8d 1d 89 26 00 00 	lea    0x2689(%rip),%rbx        # 70f0 <_IO_stdin_used+0xf0>
    4a67:	e9 94 fd ff ff       	jmp    4800 <send_headers+0x170>
    4a6c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a70:	66 0f 6f 05 58 31 00 00 	movdqa 0x3158(%rip),%xmm0        # 7bd0 <_IO_stdin_used+0xbd0>
    4a78:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a80:	66 0f 6f 05 58 31 00 00 	movdqa 0x3158(%rip),%xmm0        # 7be0 <_IO_stdin_used+0xbe0>
    4a88:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a90:	e9 b0 fd ff ff       	jmp    4845 <send_headers+0x1b5>
    4a95:	0f 1f 00             	nopl   (%rax)
    4a98:	66 0f 6f 05 30 31 00 00 	movdqa 0x3130(%rip),%xmm0        # 7bd0 <_IO_stdin_used+0xbd0>
    4aa0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4aa8:	66 0f 6f 05 30 31 00 00 	movdqa 0x3130(%rip),%xmm0        # 7be0 <_IO_stdin_used+0xbe0>
    4ab0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4ab8:	e9 71 fd ff ff       	jmp    482e <send_headers+0x19e>
    4abd:	0f 1f 00             	nopl   (%rax)
    4ac0:	66 0f 6f 05 c8 30 00 00 	movdqa 0x30c8(%rip),%xmm0        # 7b90 <_IO_stdin_used+0xb90>
    4ac8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ad0:	66 0f 6f 05 e8 30 00 00 	movdqa 0x30e8(%rip),%xmm0        # 7bc0 <_IO_stdin_used+0xbc0>
    4ad8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4ae0:	e9 32 fd ff ff       	jmp    4817 <send_headers+0x187>
    4ae5:	0f 1f 00             	nopl   (%rax)
    4ae8:	66 0f 6f 05 e0 30 00 00 	movdqa 0x30e0(%rip),%xmm0        # 7bd0 <_IO_stdin_used+0xbd0>
    4af0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4af8:	66 0f 6f 05 20 31 00 00 	movdqa 0x3120(%rip),%xmm0        # 7c20 <_IO_stdin_used+0xc20>
    4b00:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4b08:	e9 6f fd ff ff       	jmp    487c <send_headers+0x1ec>
    4b0d:	0f 1f 00             	nopl   (%rax)
    4b10:	66 0f 6f 05 b8 30 00 00 	movdqa 0x30b8(%rip),%xmm0        # 7bd0 <_IO_stdin_used+0xbd0>
    4b18:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b20:	66 0f 6f 05 e8 30 00 00 	movdqa 0x30e8(%rip),%xmm0        # 7c10 <_IO_stdin_used+0xc10>
    4b28:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4b30:	e9 30 fd ff ff       	jmp    4865 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4b35:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4b3c:	89 db                	mov    %ebx,%ebx
    4b3e:	89 10                	mov    %edx,(%rax)
    4b40:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4b45:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4b49:	e9 83 fd ff ff       	jmp    48d1 <send_headers+0x241>
    4b4e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4b55:	89 db                	mov    %ebx,%ebx
    4b57:	89 10                	mov    %edx,(%rax)
    4b59:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4b5e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4b62:	e9 d5 fd ff ff       	jmp    493c <send_headers+0x2ac>
    4b67:	89 db                	mov    %ebx,%ebx
    4b69:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4b6f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4b74:	e9 58 fd ff ff       	jmp    48d1 <send_headers+0x241>
    4b79:	89 db                	mov    %ebx,%ebx
    4b7b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4b81:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4b86:	e9 b1 fd ff ff       	jmp    493c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4b8b:	48 8b 0d 8e 54 00 00 	mov    0x548e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4b92:	ba 28 00 00 00       	mov    $0x28,%edx
    4b97:	be 01 00 00 00       	mov    $0x1,%esi
    4b9c:	48 8d 3d 8d 29 00 00 	lea    0x298d(%rip),%rdi        # 7530 <_IO_stdin_used+0x530>
    4ba3:	e8 18 d9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4ba8:	bf 01 00 00 00       	mov    $0x1,%edi
    4bad:	e8 ee d8 ff ff       	call   24a0 <exit@plt>
}
    4bb2:	e8 79 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
    4bb7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004bc0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4bc0:	f3 0f 1e fa          	endbr64
    4bc4:	41 55                	push   %r13
    4bc6:	49 89 d5             	mov    %rdx,%r13
    4bc9:	41 54                	push   %r12
    4bcb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    4bce:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4bd1:	55                   	push   %rbp
    4bd2:	53                   	push   %rbx
    4bd3:	48 89 f3             	mov    %rsi,%rbx
    4bd6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4bda:	e8 31 d8 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4bdf:	48 85 c0             	test   %rax,%rax
    4be2:	74 6b                	je     4c4f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4be4:	4c 89 e7             	mov    %r12,%rdi
    4be7:	48 89 c5             	mov    %rax,%rbp
    4bea:	31 f6                	xor    %esi,%esi
    4bec:	31 c0                	xor    %eax,%eax
    4bee:	e8 8d d8 ff ff       	call   2480 <open@plt>
    4bf3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4bf6:	85 c0                	test   %eax,%eax
    4bf8:	0f 88 58 d9 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4bfe:	48 89 da             	mov    %rbx,%rdx
    4c01:	48 89 ee             	mov    %rbp,%rsi
    4c04:	89 c7                	mov    %eax,%edi
    4c06:	e8 85 d7 ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    4c0b:	48 98                	cltq
    4c0d:	48 39 d8             	cmp    %rbx,%rax
    4c10:	7c 1e                	jl     4c30 <copy_file_contents+0x70>
    close(fd);
    4c12:	44 89 e7             	mov    %r12d,%edi
    4c15:	e8 56 d7 ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    4c1a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    4c1e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4c22:	48 83 c4 08          	add    $0x8,%rsp
    4c26:	5b                   	pop    %rbx
    4c27:	5d                   	pop    %rbp
    4c28:	41 5c                	pop    %r12
    4c2a:	41 5d                	pop    %r13
    4c2c:	c3                   	ret
    4c2d:	0f 1f 00             	nopl   (%rax)
    4c30:	48 8b 0d e9 53 00 00 	mov    0x53e9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c37:	ba 1a 00 00 00       	mov    $0x1a,%edx
    4c3c:	be 01 00 00 00       	mov    $0x1,%esi
    4c41:	48 8d 3d a9 24 00 00 	lea    0x24a9(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4c48:	e8 73 d8 ff ff       	call   24c0 <fwrite@plt>
    4c4d:	eb c3                	jmp    4c12 <copy_file_contents+0x52>
    4c4f:	48 8b 0d ca 53 00 00 	mov    0x53ca(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c56:	ba 28 00 00 00       	mov    $0x28,%edx
    4c5b:	be 01 00 00 00       	mov    $0x1,%esi
    4c60:	48 8d 3d c9 28 00 00 	lea    0x28c9(%rip),%rdi        # 7530 <_IO_stdin_used+0x530>
    4c67:	e8 54 d8 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4c6c:	bf 01 00 00 00       	mov    $0x1,%edi
    4c71:	e8 2a d8 ff ff       	call   24a0 <exit@plt>
    4c76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004c80 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4c80:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4c84:	8b 46 44             	mov    0x44(%rsi),%eax
    4c87:	48 89 fa             	mov    %rdi,%rdx
    4c8a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    4c8d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4c93:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4c96:	48 8b 07             	mov    (%rdi),%rax
    4c99:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4c9c:	f6 c1 02             	test   $0x2,%cl
    4c9f:	74 00                	je     4ca1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4ca1:	89 f0                	mov    %esi,%eax
    4ca3:	44 29 c0             	sub    %r8d,%eax
    4ca6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4ca9:	0f 82 b3 d8 ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4caf:	c1 e9 0a             	shr    $0xa,%ecx
    4cb2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4cb6:	8b 47 44             	mov    0x44(%rdi),%eax
    4cb9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4cbc:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4cbf:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4cc2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4cc5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4cc9:	d3 e0                	shl    %cl,%eax
    4ccb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    4cce:	48 c1 e0 06          	shl    $0x6,%rax
    4cd2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4cd6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    4cdc:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4cdf:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4ce3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4ce9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4cf1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4cf5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4cf8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4cff:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4d07:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    4d0b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    4d0f:	e8 2c d6 ff ff       	call   2340 <io_uring_submit@plt>
}
    4d14:	31 c0                	xor    %eax,%eax
    4d16:	48 83 c4 08          	add    $0x8,%rsp
    4d1a:	c3                   	ret
    4d1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004d20 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4d20:	f3 0f 1e fa          	endbr64
    4d24:	41 55                	push   %r13
    4d26:	41 89 fd             	mov    %edi,%r13d
    4d29:	41 54                	push   %r12
    4d2b:	55                   	push   %rbp
    4d2c:	53                   	push   %rbx
    4d2d:	48 89 f3             	mov    %rsi,%rbx
    4d30:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4d34:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4d37:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    4d3d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4d40:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4d43:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4d45:	f6 c1 02             	test   $0x2,%cl
    4d48:	74 00                	je     4d4a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    4d4a:	89 c2                	mov    %eax,%edx
    4d4c:	29 f2                	sub    %esi,%edx
    4d4e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4d51:	0f 82 1b d8 ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d57:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    4d5a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    4d5d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4d60:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4d65:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d68:	23 6b 58             	and    0x58(%rbx),%ebp
    4d6b:	d3 e5                	shl    %cl,%ebp
    4d6d:	48 c1 e5 06          	shl    $0x6,%rbp
    4d71:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4d75:	e8 96 d6 ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    4d7a:	be 01 00 00 00       	mov    $0x1,%esi
    4d7f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4d84:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4d87:	e8 14 d6 ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    4d8c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4d91:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4d95:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4d98:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4d9d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4da2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    4dab:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4db3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4db7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    4dbb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4dc2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4dca:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    4dce:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4dd6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    4dde:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4de2:	e8 59 d5 ff ff       	call   2340 <io_uring_submit@plt>
}
    4de7:	48 83 c4 08          	add    $0x8,%rsp
    4deb:	31 c0                	xor    %eax,%eax
    4ded:	5b                   	pop    %rbx
    4dee:	5d                   	pop    %rbp
    4def:	41 5c                	pop    %r12
    4df1:	41 5d                	pop    %r13
    4df3:	c3                   	ret
    4df4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4dff:	90                   	nop

0000000000004e00 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4e00:	f3 0f 1e fa          	endbr64
    4e04:	41 56                	push   %r14
    4e06:	41 89 f6             	mov    %esi,%r14d
    4e09:	41 55                	push   %r13
    4e0b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    4e0e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4e13:	41 54                	push   %r12
    4e15:	55                   	push   %rbp
    4e16:	48 89 d5             	mov    %rdx,%rbp
    4e19:	53                   	push   %rbx
    void *buf = malloc(size);
    4e1a:	e8 f1 d5 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4e1f:	48 85 c0             	test   %rax,%rax
    4e22:	0f 84 dd 00 00 00    	je     4f05 <_send_static_string_content+0x105>
    4e28:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    4e2b:	4c 89 ef             	mov    %r13,%rdi
    4e2e:	e8 ed d4 ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4e33:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    4e3a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    4e3e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4e41:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4e44:	e8 c7 d5 ff ff       	call   2410 <malloc@plt>
    4e49:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    4e4c:	48 85 c0             	test   %rax,%rax
    4e4f:	0f 84 b0 00 00 00    	je     4f05 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4e55:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4e59:	4c 89 e2             	mov    %r12,%rdx
    4e5c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    4e5f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4e63:	e8 78 d5 ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4e68:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e6b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4e71:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4e74:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4e78:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4e7a:	f6 c1 02             	test   $0x2,%cl
    4e7d:	0f 85 7d 00 00 00    	jne    4f00 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4e83:	89 d0                	mov    %edx,%eax
    4e85:	29 f0                	sub    %esi,%eax
    4e87:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    4e8a:	0f 82 ec d6 ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4e90:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e93:	8b 45 44             	mov    0x44(%rbp),%eax
    4e96:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4e99:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    4e9c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4e9f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4ea2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4ea8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4eac:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4eae:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4eb1:	48 89 ef             	mov    %rbp,%rdi
    4eb4:	48 c1 e0 06          	shl    $0x6,%rax
    4eb8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    4ebc:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4ebf:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4ec3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4ec9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4ed1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4ed5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4ed8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4edf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4ee7:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    4eeb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    4eef:	5b                   	pop    %rbx
    4ef0:	5d                   	pop    %rbp
    4ef1:	41 5c                	pop    %r12
    4ef3:	41 5d                	pop    %r13
    4ef5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4ef7:	e9 44 d4 ff ff       	jmp    2340 <io_uring_submit@plt>
    4efc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4f00:	e9 7e ff ff ff       	jmp    4e83 <_send_static_string_content+0x83>
    4f05:	48 8b 0d 14 51 00 00 	mov    0x5114(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4f0c:	ba 28 00 00 00       	mov    $0x28,%edx
    4f11:	be 01 00 00 00       	mov    $0x1,%esi
    4f16:	48 8d 3d 13 26 00 00 	lea    0x2613(%rip),%rdi        # 7530 <_IO_stdin_used+0x530>
    4f1d:	e8 9e d5 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4f22:	bf 01 00 00 00       	mov    $0x1,%edi
    4f27:	e8 74 d5 ff ff       	call   24a0 <exit@plt>
    4f2c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004f30 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4f30:	f3 0f 1e fa          	endbr64
    4f34:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4f37:	89 fe                	mov    %edi,%esi
    4f39:	48 8b 3d d8 50 00 00 	mov    0x50d8(%rip),%rdi        # a018 <unimplemented_content>
    4f40:	e9 bb fe ff ff       	jmp    4e00 <_send_static_string_content>
    4f45:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004f50 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4f50:	f3 0f 1e fa          	endbr64
    4f54:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4f57:	89 fe                	mov    %edi,%esi
    4f59:	48 8b 3d b0 50 00 00 	mov    0x50b0(%rip),%rdi        # a010 <http_404_content>
    4f60:	e9 9b fe ff ff       	jmp    4e00 <_send_static_string_content>
    4f65:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004f70 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4f70:	f3 0f 1e fa          	endbr64
    4f74:	41 56                	push   %r14
    4f76:	41 55                	push   %r13
    4f78:	49 89 d5             	mov    %rdx,%r13
    4f7b:	41 54                	push   %r12
    4f7d:	41 89 f4             	mov    %esi,%r12d
    4f80:	55                   	push   %rbp
    4f81:	48 89 fd             	mov    %rdi,%rbp
    4f84:	53                   	push   %rbx
    4f85:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    4f8c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4f95:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    4f9d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    4f9f:	e8 7c d3 ff ff       	call   2320 <strlen@plt>
    4fa4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4fa9:	48 89 c3             	mov    %rax,%rbx
    4fac:	0f 84 b6 00 00 00    	je     5068 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4fb2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4fb7:	48 89 ee             	mov    %rbp,%rsi
    4fba:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4fbe:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4fc3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4fcb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4fd3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4fde:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4fe6:	e8 d5 d3 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4feb:	48 89 e6             	mov    %rsp,%rsi
    4fee:	4c 89 f7             	mov    %r14,%rdi
    4ff1:	e8 da d3 ff ff       	call   23d0 <stat@plt>
    4ff6:	83 f8 ff             	cmp    $0xffffffff,%eax
    4ff9:	0f 84 d3 00 00 00    	je     50d2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    4fff:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5003:	25 00 f0 00 00       	and    $0xf000,%eax
    5008:	3d 00 80 00 00       	cmp    $0x8000,%eax
    500d:	0f 84 f5 00 00 00    	je     5108 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    5013:	48 8b 3d f6 4f 00 00 	mov    0x4ff6(%rip),%rdi        # a010 <http_404_content>
    501a:	4c 89 ea             	mov    %r13,%rdx
    501d:	44 89 e6             	mov    %r12d,%esi
    5020:	e8 db fd ff ff       	call   4e00 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5025:	4c 89 f2             	mov    %r14,%rdx
    5028:	bf 01 00 00 00       	mov    $0x1,%edi
    502d:	31 c0                	xor    %eax,%eax
    502f:	48 8d 35 0b 21 00 00 	lea    0x210b(%rip),%rsi        # 7141 <_IO_stdin_used+0x141>
    5036:	e8 15 d4 ff ff       	call   2450 <__printf_chk@plt>
}
    503b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5043:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    504c:	0f 85 20 01 00 00    	jne    5172 <handle_get_method+0x202>
    5052:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5059:	5b                   	pop    %rbx
    505a:	5d                   	pop    %rbp
    505b:	41 5c                	pop    %r12
    505d:	41 5d                	pop    %r13
    505f:	41 5e                	pop    %r14
    5061:	c3                   	ret
    5062:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5068:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    506d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5075:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    507a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    507d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5085:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5088:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5090:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    509b:	e8 20 d3 ff ff       	call   23c0 <__memcpy_chk@plt>
    50a0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    50a5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    50aa:	48 8d 35 5b 20 00 00 	lea    0x205b(%rip),%rsi        # 710c <_IO_stdin_used+0x10c>
    50b1:	48 29 d9             	sub    %rbx,%rcx
    50b4:	ba 0b 00 00 00       	mov    $0xb,%edx
    50b9:	e8 02 d3 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    50be:	48 89 e6             	mov    %rsp,%rsi
    50c1:	4c 89 f7             	mov    %r14,%rdi
    50c4:	e8 07 d3 ff ff       	call   23d0 <stat@plt>
    50c9:	83 f8 ff             	cmp    $0xffffffff,%eax
    50cc:	0f 85 2d ff ff ff    	jne    4fff <handle_get_method+0x8f>
    50d2:	4c 89 f2             	mov    %r14,%rdx
    50d5:	48 89 e9             	mov    %rbp,%rcx
    50d8:	48 8d 35 38 20 00 00 	lea    0x2038(%rip),%rsi        # 7117 <_IO_stdin_used+0x117>
    50df:	31 c0                	xor    %eax,%eax
    50e1:	bf 01 00 00 00       	mov    $0x1,%edi
    50e6:	e8 65 d3 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    50eb:	48 8b 3d 1e 4f 00 00 	mov    0x4f1e(%rip),%rdi        # a010 <http_404_content>
    50f2:	4c 89 ea             	mov    %r13,%rdx
    50f5:	44 89 e6             	mov    %r12d,%esi
    50f8:	e8 03 fd ff ff       	call   4e00 <_send_static_string_content>
}
    50fd:	e9 39 ff ff ff       	jmp    503b <handle_get_method+0xcb>
    5102:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5108:	bf 70 00 00 00       	mov    $0x70,%edi
    510d:	e8 fe d2 ff ff       	call   2410 <malloc@plt>
    5112:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5115:	48 85 c0             	test   %rax,%rax
    5118:	74 5d                	je     5177 <handle_get_method+0x207>
            req->client_socket = client_socket;
    511a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    511e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5123:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5127:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    512a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    5131:	e8 5a f5 ff ff       	call   4690 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5136:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    513b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    513f:	4c 89 f7             	mov    %r14,%rdi
    5142:	e8 79 fa ff ff       	call   4bc0 <copy_file_contents>
    5147:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    514c:	4c 89 f2             	mov    %r14,%rdx
    514f:	31 c0                	xor    %eax,%eax
    5151:	48 8d 35 d7 1f 00 00 	lea    0x1fd7(%rip),%rsi        # 712f <_IO_stdin_used+0x12f>
    5158:	bf 01 00 00 00       	mov    $0x1,%edi
    515d:	e8 ee d2 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    5162:	4c 89 ee             	mov    %r13,%rsi
    5165:	48 89 df             	mov    %rbx,%rdi
    5168:	e8 13 fb ff ff       	call   4c80 <add_write_request>
    516d:	e9 c9 fe ff ff       	jmp    503b <handle_get_method+0xcb>
}
    5172:	e8 b9 d1 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5177:	48 8b 0d a2 4e 00 00 	mov    0x4ea2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    517e:	ba 28 00 00 00       	mov    $0x28,%edx
    5183:	be 01 00 00 00       	mov    $0x1,%esi
    5188:	48 8d 3d a1 23 00 00 	lea    0x23a1(%rip),%rdi        # 7530 <_IO_stdin_used+0x530>
    518f:	e8 2c d3 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5194:	bf 01 00 00 00       	mov    $0x1,%edi
    5199:	e8 02 d3 ff ff       	call   24a0 <exit@plt>
    519e:	66 90                	xchg   %ax,%ax

00000000000051a0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    51a0:	f3 0f 1e fa          	endbr64
    51a4:	41 57                	push   %r15
    51a6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    51a8:	4c 8d 35 f7 1e 00 00 	lea    0x1ef7(%rip),%r14        # 70a6 <_IO_stdin_used+0xa6>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    51af:	41 55                	push   %r13
    51b1:	49 89 d5             	mov    %rdx,%r13
    51b4:	41 54                	push   %r12
    51b6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    51b9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    51bc:	55                   	push   %rbp
    51bd:	53                   	push   %rbx
    51be:	48 83 ec 18          	sub    $0x18,%rsp
    51c2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    51cb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    51d0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    51d2:	49 89 e7             	mov    %rsp,%r15
    51d5:	4c 89 fa             	mov    %r15,%rdx
    51d8:	e8 a3 d1 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    51dd:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    51e1:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    51e4:	84 db                	test   %bl,%bl
    51e6:	74 1d                	je     5205 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    51e8:	e8 23 d3 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    51ed:	48 89 ea             	mov    %rbp,%rdx
    51f0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    51f3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    51f7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    51fa:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    51fd:	48 0f be 1a          	movsbq (%rdx),%rbx
    5201:	84 db                	test   %bl,%bl
    5203:	75 eb                	jne    51f0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    5205:	4c 89 fa             	mov    %r15,%rdx
    5208:	4c 89 f6             	mov    %r14,%rsi
    520b:	31 ff                	xor    %edi,%edi
    520d:	e8 6e d1 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5212:	48 8d 35 3b 1f 00 00 	lea    0x1f3b(%rip),%rsi        # 7154 <_IO_stdin_used+0x154>
    5219:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    521c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    521f:	e8 8c d1 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    5224:	4c 89 ea             	mov    %r13,%rdx
    5227:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    522a:	85 c0                	test   %eax,%eax
    522c:	75 2a                	jne    5258 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    522e:	48 89 df             	mov    %rbx,%rdi
    5231:	e8 3a fd ff ff       	call   4f70 <handle_get_method>
}
    5236:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    523b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5244:	75 20                	jne    5266 <handle_http_method+0xc6>
    5246:	48 83 c4 18          	add    $0x18,%rsp
    524a:	5b                   	pop    %rbx
    524b:	5d                   	pop    %rbp
    524c:	41 5c                	pop    %r12
    524e:	41 5d                	pop    %r13
    5250:	41 5e                	pop    %r14
    5252:	41 5f                	pop    %r15
    5254:	c3                   	ret
    5255:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5258:	48 8b 3d b9 4d 00 00 	mov    0x4db9(%rip),%rdi        # a018 <unimplemented_content>
    525f:	e8 9c fb ff ff       	call   4e00 <_send_static_string_content>
}
    5264:	eb d0                	jmp    5236 <handle_http_method+0x96>
    5266:	e8 c5 d0 ff ff       	call   2330 <__stack_chk_fail@plt>
    526b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005270 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5270:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5274:	85 d2                	test   %edx,%edx
    5276:	7e 38                	jle    52b0 <get_line+0x40>
    5278:	48 63 d2             	movslq %edx,%rdx
    527b:	48 83 c7 01          	add    $0x1,%rdi
    527f:	48 01 f2             	add    %rsi,%rdx
    5282:	eb 11                	jmp    5295 <get_line+0x25>
    5284:	0f 1f 40 00          	nopl   0x0(%rax)
    5288:	48 83 c6 01          	add    $0x1,%rsi
    528c:	48 83 c7 01          	add    $0x1,%rdi
    5290:	48 39 d6             	cmp    %rdx,%rsi
    5293:	74 1b                	je     52b0 <get_line+0x40>
        dest[i] = src[i];
    5295:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5299:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    529b:	3c 0d                	cmp    $0xd,%al
    529d:	75 e9                	jne    5288 <get_line+0x18>
    529f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    52a2:	75 e4                	jne    5288 <get_line+0x18>
            dest[i] = '\0';
    52a4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    52a7:	31 c0                	xor    %eax,%eax
    52a9:	c3                   	ret
    52aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    52b0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    52b5:	c3                   	ret
    52b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000052c0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    52c0:	f3 0f 1e fa          	endbr64
    52c4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    52cb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    52cf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    52d8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    52e0:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    52e2:	49 89 e2             	mov    %rsp,%r10
    52e5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    52ed:	4c 89 d0             	mov    %r10,%rax
    52f0:	eb 13                	jmp    5305 <handle_client_request+0x45>
    52f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    52f8:	48 83 c0 01          	add    $0x1,%rax
    52fc:	48 83 c1 01          	add    $0x1,%rcx
    5300:	4c 39 c8             	cmp    %r9,%rax
    5303:	74 4b                	je     5350 <handle_client_request+0x90>
        dest[i] = src[i];
    5305:	44 0f b6 01          	movzbl (%rcx),%r8d
    5309:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    530c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5310:	75 e6                	jne    52f8 <handle_client_request+0x38>
    5312:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5316:	75 e0                	jne    52f8 <handle_client_request+0x38>
            dest[i] = '\0';
    5318:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    531b:	8b 47 08             	mov    0x8(%rdi),%eax
    531e:	48 89 f2             	mov    %rsi,%rdx
    5321:	4c 89 d7             	mov    %r10,%rdi
    5324:	89 c6                	mov    %eax,%esi
    5326:	e8 75 fe ff ff       	call   51a0 <handle_http_method>
}
    532b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5333:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    533c:	75 39                	jne    5377 <handle_client_request+0xb7>
    533e:	31 c0                	xor    %eax,%eax
    5340:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5347:	c3                   	ret
    5348:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5350:	48 8b 0d c9 4c 00 00 	mov    0x4cc9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5357:	ba 12 00 00 00       	mov    $0x12,%edx
    535c:	be 01 00 00 00       	mov    $0x1,%esi
    5361:	48 8d 3d f0 1d 00 00 	lea    0x1df0(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    5368:	e8 53 d1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    536d:	bf 01 00 00 00       	mov    $0x1,%edi
    5372:	e8 29 d1 ff ff       	call   24a0 <exit@plt>
}
    5377:	e8 b4 cf ff ff       	call   2330 <__stack_chk_fail@plt>
    537c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005380 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5380:	f3 0f 1e fa          	endbr64
    5384:	55                   	push   %rbp
    5385:	53                   	push   %rbx
    5386:	48 89 cb             	mov    %rcx,%rbx
    5389:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    538d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5390:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5393:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5399:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    539c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    539f:	f6 c1 02             	test   $0x2,%cl
    53a2:	74 00                	je     53a4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    53a4:	41 89 c0             	mov    %eax,%r8d
    53a7:	45 29 c8             	sub    %r9d,%r8d
    53aa:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    53ae:	0f 82 d8 d1 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    53b4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53b7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    53ba:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    53bd:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    53c0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    53c3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53c7:	d3 e5                	shl    %cl,%ebp
    53c9:	48 c1 e5 06          	shl    $0x6,%rbp
    53cd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    53d1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    53d4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    53d9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    53e0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    53e4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    53e8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    53f0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    53f8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    53fc:	e8 0f d0 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    5401:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5404:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    540a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    540e:	48 83 c4 08          	add    $0x8,%rsp
    5412:	5b                   	pop    %rbx
    5413:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5414:	e9 27 cf ff ff       	jmp    2340 <io_uring_submit@plt>
    5419:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005420 <io_thread>:
void* io_thread(void *arg) {
    5420:	f3 0f 1e fa          	endbr64
    5424:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5426:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5428:	41 56                	push   %r14
    542a:	41 55                	push   %r13
    542c:	41 54                	push   %r12
    542e:	55                   	push   %rbp
    542f:	48 89 fd             	mov    %rdi,%rbp
    5432:	53                   	push   %rbx
    5433:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    543a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5443:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    544b:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    544f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5454:	bf 00 01 00 00       	mov    $0x100,%edi
    5459:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    545c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5460:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5465:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    546a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    546f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5474:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    547c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5481:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5489:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    548e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5496:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    549b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    54a3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    54a8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    54b0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    54b5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    54bd:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    54c5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    54cd:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    54d5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    54dd:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    54e5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    54ed:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    54f5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    54fd:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5505:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    550d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5514:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    551c:	e8 cf ce ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5521:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5525:	31 f6                	xor    %esi,%esi
    5527:	e8 b4 cf ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    552c:	31 d2                	xor    %edx,%edx
    552e:	be 01 00 00 00       	mov    $0x1,%esi
    5533:	bf 02 00 00 00       	mov    $0x2,%edi
    5538:	e8 f3 cf ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    553d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5540:	0f 84 88 d0 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    5546:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    554b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5551:	89 c7                	mov    %eax,%edi
    5553:	41 89 c4             	mov    %eax,%r12d
    5556:	ba 02 00 00 00       	mov    $0x2,%edx
    555b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5560:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5568:	e8 93 cd ff ff       	call   2300 <setsockopt@plt>
    556d:	85 c0                	test   %eax,%eax
    556f:	0f 88 2d d0 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5575:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    557a:	ba 10 00 00 00       	mov    $0x10,%edx
    557f:	44 89 e7             	mov    %r12d,%edi
    5582:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    558b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5593:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    559b:	e8 c0 ce ff ff       	call   2460 <bind@plt>
    55a0:	85 c0                	test   %eax,%eax
    55a2:	0f 88 32 d0 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    55a8:	be 0a 00 00 00       	mov    $0xa,%esi
    55ad:	44 89 e7             	mov    %r12d,%edi
    55b0:	e8 6b ce ff ff       	call   2420 <listen@plt>
    55b5:	85 c0                	test   %eax,%eax
    55b7:	0f 88 f1 cf ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    55bd:	ba db 18 00 00       	mov    $0x18db,%edx
    55c2:	48 8d 35 d4 1b 00 00 	lea    0x1bd4(%rip),%rsi        # 719d <_IO_stdin_used+0x19d>
    55c9:	bf 01 00 00 00       	mov    $0x1,%edi
    55ce:	31 c0                	xor    %eax,%eax
    55d0:	e8 7b ce ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    55d5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    55da:	48 89 d9             	mov    %rbx,%rcx
    55dd:	44 89 e7             	mov    %r12d,%edi
    55e0:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    55e5:	48 89 c6             	mov    %rax,%rsi
    55e8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    55ed:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    55f2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    55fa:	e8 81 fd ff ff       	call   5380 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    55ff:	bf 01 00 00 00       	mov    $0x1,%edi
    5604:	be 10 00 00 00       	mov    $0x10,%esi
    5609:	e8 92 cd ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    560e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5613:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5616:	e8 f5 cd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    561b:	48 85 c0             	test   %rax,%rax
    561e:	0f 84 ae 04 00 00    	je     5ad2 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5624:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5628:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    562f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5636:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    563e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5641:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5646:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5648:	f6 c1 02             	test   $0x2,%cl
    564b:	0f 85 0f 04 00 00    	jne    5a60 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5651:	89 d0                	mov    %edx,%eax
    5653:	29 f0                	sub    %esi,%eax
    5655:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    565c:	0f 82 62 cf ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5662:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5665:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5669:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    566d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5670:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5677:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    567a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5681:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5688:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    568a:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    568d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5692:	48 c1 e0 06          	shl    $0x6,%rax
    5696:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    569e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    56a4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    56a7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    56af:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    56b3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    56bb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    56c3:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    56c7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    56cb:	e8 70 cc ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    56d0:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    56d4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    56d9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    56e1:	0f 85 d7 01 00 00    	jne    58be <io_thread+0x49e>
    56e7:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    56ec:	4d 89 ce             	mov    %r9,%r14
    56ef:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    56f4:	0f 1f 40 00          	nopl   0x0(%rax)
    56f8:	48 8d 3d b4 1a 00 00 	lea    0x1ab4(%rip),%rdi        # 71b3 <_IO_stdin_used+0x1b3>
    56ff:	e8 ec cb ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5704:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    570b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5712:	c1 e9 0b             	shr    $0xb,%ecx
    5715:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5718:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5720:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5722:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    572a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    572c:	39 d0                	cmp    %edx,%eax
    572e:	74 36                	je     5766 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5730:	89 f8                	mov    %edi,%eax
    5732:	21 d0                	and    %edx,%eax
    5734:	d3 e0                	shl    %cl,%eax
    5736:	48 c1 e0 04          	shl    $0x4,%rax
    573a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5742:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    574a:	0f 85 a8 01 00 00    	jne    58f8 <io_thread+0x4d8>
    5750:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5754:	0f 85 0e 03 00 00    	jne    5a68 <io_thread+0x648>
			if (cqe->res < 0)
    575a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    575d:	83 c2 01             	add    $0x1,%edx
    5760:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5762:	85 c0                	test   %eax,%eax
    5764:	79 b2                	jns    5718 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5766:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    576f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5770:	45 31 c0             	xor    %r8d,%r8d
    5773:	31 d2                	xor    %edx,%edx
    5775:	b9 01 00 00 00       	mov    $0x1,%ecx
    577a:	4c 89 f6             	mov    %r14,%rsi
    577d:	48 89 df             	mov    %rbx,%rdi
    5780:	e8 bb cc ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5785:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5788:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    578d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5791:	0f 84 e1 02 00 00    	je     5a78 <io_thread+0x658>
    5797:	48 8d 3d 3b 1a 00 00 	lea    0x1a3b(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    579e:	e8 4d cb ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    57a3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    57a8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    57ab:	45 85 ff             	test   %r15d,%r15d
    57ae:	0f 88 e2 cd ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    57b4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    57b7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    57bb:	85 c0                	test   %eax,%eax
    57bd:	0f 88 d5 02 00 00    	js     5a98 <io_thread+0x678>
      switch (req->event_type) {
    57c3:	41 83 f8 01          	cmp    $0x1,%r8d
    57c7:	0f 84 7b 01 00 00    	je     5948 <io_thread+0x528>
    57cd:	41 83 f8 02          	cmp    $0x2,%r8d
    57d1:	0f 84 a1 01 00 00    	je     5978 <io_thread+0x558>
    57d7:	45 85 c0             	test   %r8d,%r8d
    57da:	0f 85 50 01 00 00    	jne    5930 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    57e0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    57e5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    57ea:	48 89 d9             	mov    %rbx,%rcx
    57ed:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    57f1:	e8 8a fb ff ff       	call   5380 <add_accept_request>
              add_read_request(cqe->res, &ring);
    57f6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    57fb:	48 89 de             	mov    %rbx,%rsi
    57fe:	8b 78 08             	mov    0x8(%rax),%edi
    5801:	e8 1a f5 ff ff       	call   4d20 <add_read_request>
              free(req);
    5806:	4c 89 e7             	mov    %r12,%rdi
    5809:	e8 b2 ca ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    580e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5813:	48 85 c0             	test   %rax,%rax
    5816:	0f 85 14 01 00 00    	jne    5930 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    581c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5823:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    582a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    582d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5832:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5834:	f6 c1 02             	test   $0x2,%cl
    5837:	74 00                	je     5839 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5839:	89 d0                	mov    %edx,%eax
    583b:	29 f0                	sub    %esi,%eax
    583d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5844:	0f 82 70 cd ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    584a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    584d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5852:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5856:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5859:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5860:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5863:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    586a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5871:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5873:	8b 55 60             	mov    0x60(%rbp),%edx
    5876:	48 c1 e0 06          	shl    $0x6,%rax
    587a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5882:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5888:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    588b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5893:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5897:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    589f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    58a7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    58ab:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    58af:	e8 8c ca ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    58b4:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    58b8:	0f 84 3a fe ff ff    	je     56f8 <io_thread+0x2d8>
    58be:	48 8d 3d 4d 19 00 00 	lea    0x194d(%rip),%rdi        # 7212 <_IO_stdin_used+0x212>
    58c5:	e8 26 ca ff ff       	call   22f0 <puts@plt>
}
    58ca:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    58d2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    58db:	0f 85 18 02 00 00    	jne    5af9 <io_thread+0x6d9>
    58e1:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    58e8:	31 c0                	xor    %eax,%eax
    58ea:	5b                   	pop    %rbx
    58eb:	5d                   	pop    %rbp
    58ec:	41 5c                	pop    %r12
    58ee:	41 5d                	pop    %r13
    58f0:	41 5e                	pop    %r14
    58f2:	41 5f                	pop    %r15
    58f4:	c3                   	ret
    58f5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    58f8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    58fd:	48 85 c0             	test   %rax,%rax
    5900:	0f 84 6a fe ff ff    	je     5770 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5906:	48 83 38 01          	cmpq   $0x1,(%rax)
    590a:	0f 84 68 01 00 00    	je     5a78 <io_thread+0x658>
    5910:	48 8d 3d c2 18 00 00 	lea    0x18c2(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    5917:	e8 d4 c9 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    591c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5921:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5924:	e9 8b fe ff ff       	jmp    57b4 <io_thread+0x394>
    5929:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5930:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5938:	8b 02                	mov    (%rdx),%eax
    593a:	83 c0 01             	add    $0x1,%eax
    593d:	89 02                	mov    %eax,(%rdx)
}
    593f:	e9 d8 fe ff ff       	jmp    581c <io_thread+0x3fc>
    5944:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5948:	85 c0                	test   %eax,%eax
    594a:	75 74                	jne    59c0 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    594c:	48 8b 0d cd 46 00 00 	mov    0x46cd(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5953:	ba 0f 00 00 00       	mov    $0xf,%edx
    5958:	be 01 00 00 00       	mov    $0x1,%esi
    595d:	48 8d 3d 9e 18 00 00 	lea    0x189e(%rip),%rdi        # 7202 <_IO_stdin_used+0x202>
    5964:	e8 57 cb ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5969:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    596e:	e9 a0 fe ff ff       	jmp    5813 <io_thread+0x3f3>
    5973:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5978:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    597d:	45 31 ff             	xor    %r15d,%r15d
    5980:	85 c0                	test   %eax,%eax
    5982:	7e 20                	jle    59a4 <io_thread+0x584>
    5984:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5988:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    598b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    598f:	48 c1 e0 04          	shl    $0x4,%rax
    5993:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5998:	e8 23 c9 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    599d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    59a2:	7f e4                	jg     5988 <io_thread+0x568>
              close(req->client_socket);
    59a4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    59a9:	e8 c2 c9 ff ff       	call   2370 <close@plt>
              free(req);
    59ae:	4c 89 e7             	mov    %r12,%rdi
    59b1:	e8 0a c9 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    59b6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    59bb:	e9 53 fe ff ff       	jmp    5813 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    59c0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    59c5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    59ca:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    59d2:	eb 11                	jmp    59e5 <io_thread+0x5c5>
    59d4:	0f 1f 40 00          	nopl   0x0(%rax)
    59d8:	48 83 c0 01          	add    $0x1,%rax
    59dc:	48 83 c2 01          	add    $0x1,%rdx
    59e0:	48 39 c6             	cmp    %rax,%rsi
    59e3:	74 4b                	je     5a30 <io_thread+0x610>
        dest[i] = src[i];
    59e5:	0f b6 0a             	movzbl (%rdx),%ecx
    59e8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    59ea:	80 f9 0d             	cmp    $0xd,%cl
    59ed:	75 e9                	jne    59d8 <io_thread+0x5b8>
    59ef:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    59f3:	75 e3                	jne    59d8 <io_thread+0x5b8>
            dest[i] = '\0';
    59f5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    59f8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    59fd:	48 89 da             	mov    %rbx,%rdx
    5a00:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5a05:	e8 96 f7 ff ff       	call   51a0 <handle_http_method>
              free(req->iov[0].iov_base);
    5a0a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    5a0f:	e8 ac c8 ff ff       	call   22c0 <free@plt>
              free(req);
    5a14:	4c 89 e7             	mov    %r12,%rdi
    5a17:	e8 a4 c8 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5a1c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5a21:	e9 ed fd ff ff       	jmp    5813 <io_thread+0x3f3>
    5a26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5a30:	48 8b 0d e9 45 00 00 	mov    0x45e9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5a37:	ba 12 00 00 00       	mov    $0x12,%edx
    5a3c:	be 01 00 00 00       	mov    $0x1,%esi
    5a41:	48 8d 3d 10 17 00 00 	lea    0x1710(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    5a48:	e8 73 ca ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5a4d:	bf 01 00 00 00       	mov    $0x1,%edi
    5a52:	e8 49 ca ff ff       	call   24a0 <exit@plt>
    5a57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5a60:	e9 ec fb ff ff       	jmp    5651 <io_thread+0x231>
    5a65:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5a68:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    5a6d:	e9 94 fe ff ff       	jmp    5906 <io_thread+0x4e6>
    5a72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5a78:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5a80:	48 8d 3d 3e 17 00 00 	lea    0x173e(%rip),%rdi        # 71c5 <_IO_stdin_used+0x1c5>
    5a87:	8b 02                	mov    (%rdx),%eax
    5a89:	83 c0 01             	add    $0x1,%eax
    5a8c:	89 02                	mov    %eax,(%rdx)
    5a8e:	e8 5d c8 ff ff       	call   22f0 <puts@plt>
    5a93:	e9 26 fe ff ff       	jmp    58be <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5a98:	f7 d8                	neg    %eax
    5a9a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5a9f:	89 c7                	mov    %eax,%edi
    5aa1:	e8 5a ca ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5aa6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5aab:	be 01 00 00 00       	mov    $0x1,%esi
    5ab0:	48 8b 3d 69 45 00 00 	mov    0x4569(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5ab7:	48 89 c1             	mov    %rax,%rcx
    5aba:	48 8d 15 9f 1a 00 00 	lea    0x1a9f(%rip),%rdx        # 7560 <_IO_stdin_used+0x560>
    5ac1:	31 c0                	xor    %eax,%eax
    5ac3:	e8 08 ca ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5ac8:	bf 01 00 00 00       	mov    $0x1,%edi
    5acd:	e8 ce c9 ff ff       	call   24a0 <exit@plt>
    5ad2:	48 8b 0d 47 45 00 00 	mov    0x4547(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5ad9:	ba 28 00 00 00       	mov    $0x28,%edx
    5ade:	be 01 00 00 00       	mov    $0x1,%esi
    5ae3:	48 8d 3d 46 1a 00 00 	lea    0x1a46(%rip),%rdi        # 7530 <_IO_stdin_used+0x530>
    5aea:	e8 d1 c9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5aef:	bf 01 00 00 00       	mov    $0x1,%edi
    5af4:	e8 a7 c9 ff ff       	call   24a0 <exit@plt>
}
    5af9:	e8 32 c8 ff ff       	call   2330 <__stack_chk_fail@plt>
    5afe:	66 90                	xchg   %ax,%ax

0000000000005b00 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5b00:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5b04:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5b0b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5b11:	85 c9                	test   %ecx,%ecx
    5b13:	0f 8e ea 00 00 00    	jle    5c03 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    5b19:	41 56                	push   %r14
    5b1b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5b1d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    5b20:	41 54                	push   %r12
    5b22:	49 89 fc             	mov    %rdi,%r12
    5b25:	55                   	push   %rbp
    5b26:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5b27:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5b2b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5b30:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    5b34:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    5b3c:	31 db                	xor    %ebx,%ebx
    5b3e:	8b 10                	mov    (%rax),%edx
    5b40:	85 d2                	test   %edx,%edx
    5b42:	7e 26                	jle    5b6a <barriered_work_ingest+0x6a>
    5b44:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    5b48:	48 89 dd             	mov    %rbx,%rbp
    5b4b:	48 c1 e5 08          	shl    $0x8,%rbp
    5b4f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    5b53:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    5b5a:	74 24                	je     5b80 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5b5c:	48 83 c3 01          	add    $0x1,%rbx
    5b60:	39 da                	cmp    %ebx,%edx
    5b62:	7f e4                	jg     5b48 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5b64:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5b6a:	49 83 c5 01          	add    $0x1,%r13
    5b6e:	44 39 e9             	cmp    %r13d,%ecx
    5b71:	7f bd                	jg     5b30 <barriered_work_ingest+0x30>
}
    5b73:	5b                   	pop    %rbx
    5b74:	31 c0                	xor    %eax,%eax
    5b76:	5d                   	pop    %rbp
    5b77:	41 5c                	pop    %r12
    5b79:	41 5d                	pop    %r13
    5b7b:	41 5e                	pop    %r14
    5b7d:	c3                   	ret
    5b7e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    5b80:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5b89:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5b90:	bf 04 00 00 00       	mov    $0x4,%edi
    5b95:	48 c1 e6 05          	shl    $0x5,%rsi
    5b99:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5ba0:	48 83 c6 10          	add    $0x10,%rsi
    5ba4:	e8 67 c7 ff ff       	call   2310 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5ba9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5bb1:	48 8b 40 50          	mov    0x50(%rax),%rax
    5bb5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5bb9:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    5bbd:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5bc7:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    5bcd:	83 c0 01             	add    $0x1,%eax
    5bd0:	99                   	cltd
    5bd1:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5bd7:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    5bdd:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5be0:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5be8:	48 83 c3 01          	add    $0x1,%rbx
    5bec:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5bf0:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5bf4:	8b 10                	mov    (%rax),%edx
    5bf6:	39 da                	cmp    %ebx,%edx
    5bf8:	0f 8f 46 ff ff ff    	jg     5b44 <barriered_work_ingest+0x44>
    5bfe:	e9 61 ff ff ff       	jmp    5b64 <barriered_work_ingest+0x64>
}
    5c03:	31 c0                	xor    %eax,%eax
    5c05:	c3                   	ret
    5c06:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005c10 <barriered_thread>:
void* barriered_thread(void *arg) {
    5c10:	f3 0f 1e fa          	endbr64
    5c14:	41 56                	push   %r14
    5c16:	41 55                	push   %r13
    5c18:	41 54                	push   %r12
  int t = 0;
    5c1a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    5c1d:	55                   	push   %rbp
  int waiting = 0;
    5c1e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    5c20:	53                   	push   %rbx
    5c21:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    5c24:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5c28:	0f 85 74 02 00 00    	jne    5ea2 <barriered_thread+0x292>
    if (t >= data->task_count) {
    5c2e:	8b 43 40             	mov    0x40(%rbx),%eax
    5c31:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5c38:	41 39 c4             	cmp    %eax,%r12d
    5c3b:	0f 8d 6f 01 00 00    	jge    5db0 <barriered_thread+0x1a0>
    5c41:	49 63 fc             	movslq %r12d,%rdi
    5c44:	48 c1 e7 09          	shl    $0x9,%rdi
    5c48:	49 89 fd             	mov    %rdi,%r13
    5c4b:	eb 32                	jmp    5c7f <barriered_thread+0x6f>
    5c4d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5c50:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5c54:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5c58:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5c5c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5c60:	4c 01 ef             	add    %r13,%rdi
    5c63:	e8 98 fe ff ff       	call   5b00 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    5c68:	8b 43 40             	mov    0x40(%rbx),%eax
    5c6b:	41 83 c4 01          	add    $0x1,%r12d
    5c6f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    5c76:	44 39 e0             	cmp    %r12d,%eax
    5c79:	0f 8e 19 02 00 00    	jle    5e98 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    5c7f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5c83:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    5c87:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    5c8e:	75 c0                	jne    5c50 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5c90:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    5c94:	83 e8 01             	sub    $0x1,%eax
    5c97:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    5c9c:	45 85 e4             	test   %r12d,%r12d
    5c9f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5ca2:	45 85 c0             	test   %r8d,%r8d
    5ca5:	0f 8e 2d 01 00 00    	jle    5dd8 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5cab:	48 63 c8             	movslq %eax,%rcx
    5cae:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5cb2:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5cb5:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5cbb:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    5cc2:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    5cc6:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    5cc9:	45 31 f6             	xor    %r14d,%r14d
    5ccc:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5cd0:	48 8b 10             	mov    (%rax),%rdx
    5cd3:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    5cd7:	49 01 cb             	add    %rcx,%r11
    5cda:	4c 89 da             	mov    %r11,%rdx
    5cdd:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    5ce4:	75 04                	jne    5cea <barriered_thread+0xda>
            arrived++;
    5ce6:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5cea:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    5cf0:	75 04                	jne    5cf6 <barriered_thread+0xe6>
            prearrive++;
    5cf2:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5cf6:	48 83 c0 08          	add    $0x8,%rax
    5cfa:	48 39 c6             	cmp    %rax,%rsi
    5cfd:	75 d1                	jne    5cd0 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    5cff:	45 85 d2             	test   %r10d,%r10d
    5d02:	0f 84 c0 00 00 00    	je     5dc8 <barriered_thread+0x1b8>
    5d08:	45 39 d0             	cmp    %r10d,%r8d
    5d0b:	0f 84 b7 00 00 00    	je     5dc8 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    5d11:	45 85 f6             	test   %r14d,%r14d
    5d14:	74 0a                	je     5d20 <barriered_thread+0x110>
    5d16:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    5d1a:	0f 85 ae 01 00 00    	jne    5ece <barriered_thread+0x2be>
    5d20:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    5d24:	4c 01 ea             	add    %r13,%rdx
    5d27:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    5d2e:	45 85 e4             	test   %r12d,%r12d
    5d31:	75 14                	jne    5d47 <barriered_thread+0x137>
    5d33:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5d3a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5d41:	0f 8c 69 01 00 00    	jl     5eb0 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5d47:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    5d4b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    5d4f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5d59:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    5d5d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5d61:	4c 01 ef             	add    %r13,%rdi
    5d64:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    5d6a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    5d6e:	4c 01 e8             	add    %r13,%rax
    5d71:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5d78:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    5d7b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5d80:	83 e8 01             	sub    $0x1,%eax
    5d83:	44 39 e0             	cmp    %r12d,%eax
    5d86:	0f 84 a4 00 00 00    	je     5e30 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    5d8c:	0f ae f8             	sfence
          if (waiting == 0) {
    5d8f:	85 ed                	test   %ebp,%ebp
    5d91:	0f 84 d1 00 00 00    	je     5e68 <barriered_thread+0x258>
        int arrived = 0; 
    5d97:	bd 01 00 00 00       	mov    $0x1,%ebp
    5d9c:	e9 c7 fe ff ff       	jmp    5c68 <barriered_thread+0x58>
  while (data->running == 1) {
    5da1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5da5:	0f 85 f7 00 00 00    	jne    5ea2 <barriered_thread+0x292>
    5dab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    5db0:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    5db8:	85 c0                	test   %eax,%eax
    5dba:	7e e5                	jle    5da1 <barriered_thread+0x191>
    5dbc:	45 31 e4             	xor    %r12d,%r12d
    5dbf:	e9 7d fe ff ff       	jmp    5c41 <barriered_thread+0x31>
    5dc4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5dc8:	83 fd 01             	cmp    $0x1,%ebp
    5dcb:	74 1b                	je     5de8 <barriered_thread+0x1d8>
        int arrived = 0; 
    5dcd:	31 ed                	xor    %ebp,%ebp
    5dcf:	e9 3d ff ff ff       	jmp    5d11 <barriered_thread+0x101>
    5dd4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5dd8:	83 fd 01             	cmp    $0x1,%ebp
    5ddb:	0f 85 43 ff ff ff    	jne    5d24 <barriered_thread+0x114>
        int arrived = 0; 
    5de1:	45 31 f6             	xor    %r14d,%r14d
    5de4:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5de8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5def:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    5df4:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5df6:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5dfa:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5e01:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    5e06:	e8 05 c5 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    5e0b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5e12:	48 83 c0 01          	add    $0x1,%rax
    5e16:	48 99                	cqto
    5e18:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    5e1f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    5e26:	e9 e6 fe ff ff       	jmp    5d11 <barriered_thread+0x101>
    5e2b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5e30:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5e37:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5e3e:	0f 8d 48 ff ff ff    	jge    5d8c <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    5e44:	48 c1 e6 04          	shl    $0x4,%rsi
    5e48:	bf 04 00 00 00       	mov    $0x4,%edi
    5e4d:	48 03 73 70          	add    0x70(%rbx),%rsi
    5e51:	e8 ba c4 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    5e56:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    5e5e:	e9 29 ff ff ff       	jmp    5d8c <barriered_thread+0x17c>
    5e63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    5e68:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5e6f:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    5e74:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5e78:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5e7f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5e83:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5e87:	e8 84 c4 ff ff       	call   2310 <clock_gettime@plt>
            waiting = 1;
    5e8c:	e9 06 ff ff ff       	jmp    5d97 <barriered_thread+0x187>
    5e91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    5e98:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5e9c:	0f 84 96 fd ff ff    	je     5c38 <barriered_thread+0x28>
}
    5ea2:	5b                   	pop    %rbx
    5ea3:	31 c0                	xor    %eax,%eax
    5ea5:	5d                   	pop    %rbp
    5ea6:	41 5c                	pop    %r12
    5ea8:	41 5d                	pop    %r13
    5eaa:	41 5e                	pop    %r14
    5eac:	c3                   	ret
    5ead:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    5eb0:	48 c1 e6 04          	shl    $0x4,%rsi
    5eb4:	bf 04 00 00 00       	mov    $0x4,%edi
    5eb9:	48 03 73 68          	add    0x68(%rbx),%rsi
    5ebd:	e8 4e c4 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    5ec2:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5ec6:	4c 01 ea             	add    %r13,%rdx
    5ec9:	e9 79 fe ff ff       	jmp    5d47 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5ece:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5ed2:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5ed6:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5eda:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5ede:	4c 01 ef             	add    %r13,%rdi
    5ee1:	e8 1a fc ff ff       	call   5b00 <barriered_work_ingest>
          break;
    5ee6:	e9 39 fd ff ff       	jmp    5c24 <barriered_thread+0x14>
    5eeb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005ef0 <receive>:
int receive(struct BarrierTask *data) {
    5ef0:	f3 0f 1e fa          	endbr64
    5ef4:	41 57                	push   %r15
    5ef6:	41 56                	push   %r14
    5ef8:	41 55                	push   %r13
    5efa:	41 54                	push   %r12
    5efc:	55                   	push   %rbp
    5efd:	53                   	push   %rbx
    5efe:	48 83 ec 18          	sub    $0x18,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5f02:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    5f08:	89 04 24             	mov    %eax,(%rsp)
    5f0b:	85 c0                	test   %eax,%eax
    5f0d:	0f 8e 11 01 00 00    	jle    6024 <receive+0x134>
    if (n == data->thread->real_thread_index) { continue; }
    5f13:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5f1a:	48 89 fa             	mov    %rdi,%rdx
    5f1d:	45 31 f6             	xor    %r14d,%r14d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5f20:	31 ed                	xor    %ebp,%ebp
    if (n == data->thread->real_thread_index) { continue; }
    5f22:	4c 63 68 08          	movslq 0x8(%rax),%r13
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5f26:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    if (n == data->thread->real_thread_index) { continue; }
    5f2b:	44 89 6c 24 04       	mov    %r13d,0x4(%rsp)
    5f30:	39 6c 24 04          	cmp    %ebp,0x4(%rsp)
    5f34:	0f 84 d8 00 00 00    	je     6012 <receive+0x122>
    struct Data *me = data->mailboxes[n].lower;
    5f3a:	48 8b b2 70 01 00 00 	mov    0x170(%rdx),%rsi
    5f41:	4c 01 f6             	add    %r14,%rsi
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    5f44:	44 8b 7e 40          	mov    0x40(%rsi),%r15d
    struct Data *me = data->mailboxes[n].lower;
    5f48:	4c 8b 26             	mov    (%rsi),%r12
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    5f4b:	41 83 ff 02          	cmp    $0x2,%r15d
    5f4f:	0f 84 2b 01 00 00    	je     6080 <receive+0x190>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5f55:	49 8b bc 24 80 00 00 00 	mov    0x80(%r12),%rdi
    5f5d:	48 85 ff             	test   %rdi,%rdi
    5f60:	0f 8e 45 01 00 00    	jle    60ab <receive+0x1bb>
      data->sends++;
    5f66:	48 8b 8a 78 01 00 00 	mov    0x178(%rdx),%rcx
      data->n++;
    5f6d:	4c 8b 82 08 01 00 00 	mov    0x108(%rdx),%r8
      data->mailboxes[n].received++;
    5f74:	31 c0                	xor    %eax,%eax
      if (me->messages[x]->group == data->group) {
    5f76:	49 8b 1c 24          	mov    (%r12),%rbx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5f7a:	4c 63 5a 04          	movslq 0x4(%rdx),%r11
    5f7e:	4c 8d 51 01          	lea    0x1(%rcx),%r10
    5f82:	48 8b 4e 38          	mov    0x38(%rsi),%rcx
    5f86:	4d 8d 48 01          	lea    0x1(%r8),%r9
    5f8a:	4c 8d 41 01          	lea    0x1(%rcx),%r8
    5f8e:	eb 09                	jmp    5f99 <receive+0xa9>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5f90:	48 83 c0 01          	add    $0x1,%rax
    5f94:	48 39 f8             	cmp    %rdi,%rax
    5f97:	7d 67                	jge    6000 <receive+0x110>
      data->sends++;
    5f99:	49 8d 0c 02          	lea    (%r10,%rax,1),%rcx
    5f9d:	48 89 8a 78 01 00 00 	mov    %rcx,0x178(%rdx)
      data->n++;
    5fa4:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    5fa8:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5faf:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5fb3:	48 89 4e 38          	mov    %rcx,0x38(%rsi)
      if (me->messages[x]->group == data->group) {
    5fb7:	48 8b 0c c3          	mov    (%rbx,%rax,8),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5fbb:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5fbf:	75 cf                	jne    5f90 <receive+0xa0>
    5fc1:	4c 39 69 08          	cmp    %r13,0x8(%rcx)
    5fc5:	75 c9                	jne    5f90 <receive+0xa0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    5fc7:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5fcc:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5fce:	bf 01 00 00 00       	mov    $0x1,%edi
    5fd3:	ba 01 00 00 00       	mov    $0x1,%edx
    5fd8:	48 8d 35 a9 15 00 00 	lea    0x15a9(%rip),%rsi        # 7588 <_IO_stdin_used+0x588>
    5fdf:	48 63 40 04          	movslq 0x4(%rax),%rax
    5fe3:	4c 39 e8             	cmp    %r13,%rax
    5fe6:	0f 94 c1             	sete   %cl
    5fe9:	31 c0                	xor    %eax,%eax
    5feb:	e8 60 c4 ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5ff0:	bf 01 00 00 00       	mov    $0x1,%edi
    5ff5:	e8 a6 c4 ff ff       	call   24a0 <exit@plt>
    5ffa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    6000:	49 c7 84 24 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%r12)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    600c:	41 83 ff 02          	cmp    $0x2,%r15d
    6010:	74 2e                	je     6040 <receive+0x150>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6012:	8b 04 24             	mov    (%rsp),%eax
    6015:	83 c5 01             	add    $0x1,%ebp
    6018:	49 83 c6 48          	add    $0x48,%r14
    601c:	39 c5                	cmp    %eax,%ebp
    601e:	0f 85 0c ff ff ff    	jne    5f30 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    6024:	0f ae f8             	sfence
}
    6027:	48 83 c4 18          	add    $0x18,%rsp
    602b:	31 c0                	xor    %eax,%eax
    602d:	5b                   	pop    %rbx
    602e:	5d                   	pop    %rbp
    602f:	41 5c                	pop    %r12
    6031:	41 5d                	pop    %r13
    6033:	41 5e                	pop    %r14
    6035:	41 5f                	pop    %r15
    6037:	c3                   	ret
    6038:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    6040:	41 8b 84 24 00 02 00 00 	mov    0x200(%r12),%eax
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    6048:	83 f8 01             	cmp    $0x1,%eax
    604b:	75 c5                	jne    6012 <receive+0x122>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    604d:	8b 04 24             	mov    (%rsp),%eax
    6050:	83 c5 01             	add    $0x1,%ebp
      me->available_reading = 0;
    6053:	41 c7 84 24 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%r12)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    605f:	49 83 c6 48          	add    $0x48,%r14
      me->finished_reading = 1;
    6063:	41 c7 84 24 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r12)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    606f:	39 c5                	cmp    %eax,%ebp
    6071:	0f 85 b9 fe ff ff    	jne    5f30 <receive+0x40>
    6077:	eb ab                	jmp    6024 <receive+0x134>
    6079:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    6080:	41 8b 84 24 00 02 00 00 	mov    0x200(%r12),%eax
    6088:	85 c0                	test   %eax,%eax
    608a:	74 86                	je     6012 <receive+0x122>
    for (int x = 0 ; x < me->messages_count ; x++) {
    608c:	49 8b bc 24 80 00 00 00 	mov    0x80(%r12),%rdi
    6094:	48 85 ff             	test   %rdi,%rdi
    6097:	0f 8f c9 fe ff ff    	jg     5f66 <receive+0x76>
    me->messages_count = 0;
    609d:	49 c7 84 24 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%r12)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    60a9:	eb 9d                	jmp    6048 <receive+0x158>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    60ab:	8b 04 24             	mov    (%rsp),%eax
    60ae:	83 c5 01             	add    $0x1,%ebp
    60b1:	49 83 c6 48          	add    $0x48,%r14
    me->messages_count = 0;
    60b5:	49 c7 84 24 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%r12)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    60c1:	39 c5                	cmp    %eax,%ebp
    60c3:	0f 85 67 fe ff ff    	jne    5f30 <receive+0x40>
    60c9:	e9 56 ff ff ff       	jmp    6024 <receive+0x134>
    60ce:	66 90                	xchg   %ax,%ax

00000000000060d0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    60d0:	f3 0f 1e fa          	endbr64
    60d4:	41 57                	push   %r15
    60d6:	49 89 ff             	mov    %rdi,%r15
    60d9:	41 56                	push   %r14
    60db:	41 55                	push   %r13
    60dd:	41 54                	push   %r12
    60df:	55                   	push   %rbp
    60e0:	53                   	push   %rbx
    60e1:	48 83 ec 58          	sub    $0x58,%rsp
  if (data->thread_index == data->task_index) {
    60e5:	8b 47 04             	mov    0x4(%rdi),%eax
    60e8:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    60ee:	74 50                	je     6140 <barriered_work+0x70>
    receive(data);
    60f0:	e8 fb fd ff ff       	call   5ef0 <receive>
    while (data->scheduled == 1) {
    60f5:	41 83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r15)
    60fd:	75 16                	jne    6115 <barriered_work+0x45>
    60ff:	90                   	nop
      data->n++;
    6100:	49 83 87 08 01 00 00 01 	addq   $0x1,0x108(%r15)
      asm volatile ("sfence" ::: "memory");
    6108:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    610b:	41 83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r15)
    6113:	74 eb                	je     6100 <barriered_work+0x30>
  if (data->sending == 1) {
    6115:	41 83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%r15)
    611d:	75 08                	jne    6127 <barriered_work+0x57>
    611f:	4c 89 ff             	mov    %r15,%rdi
    6122:	e8 39 e2 ff ff       	call   4360 <sendm.part.0>
  asm volatile ("sfence" ::: "memory");
    6127:	0f ae f8             	sfence
}
    612a:	48 83 c4 58          	add    $0x58,%rsp
    612e:	31 c0                	xor    %eax,%eax
    6130:	5b                   	pop    %rbx
    6131:	5d                   	pop    %rbp
    6132:	41 5c                	pop    %r12
    6134:	41 5d                	pop    %r13
    6136:	41 5e                	pop    %r14
    6138:	41 5f                	pop    %r15
    613a:	c3                   	ret
    613b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      receive(data);
    6140:	e8 ab fd ff ff       	call   5ef0 <receive>
        int t = data->task_index;
    6145:	49 63 57 04          	movslq 0x4(%r15),%rdx
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6149:	41 8b bf 40 01 00 00 	mov    0x140(%r15),%edi
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6150:	31 ed                	xor    %ebp,%ebp
        int t = data->task_index;
    6152:	48 89 d0             	mov    %rdx,%rax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6155:	48 c1 e2 09          	shl    $0x9,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
    6159:	44 8d 48 01          	lea    0x1(%rax),%r9d
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    615d:	49 89 d0             	mov    %rdx,%r8
    6160:	45 89 ca             	mov    %r9d,%r10d
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6163:	85 ff                	test   %edi,%edi
    6165:	0f 8e dd 00 00 00    	jle    6248 <barriered_work+0x178>
    616b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6170:	89 6c 24 48          	mov    %ebp,0x48(%rsp)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6174:	85 ff                	test   %edi,%edi
    6176:	0f 8e cc 00 00 00    	jle    6248 <barriered_work+0x178>
    617c:	4c 8d 6c 6d 00       	lea    0x0(%rbp,%rbp,2),%r13
    6181:	48 8d 44 ed 00       	lea    0x0(%rbp,%rbp,8),%rax
              int next_task = abs((t + 1) % (data->thread_count));
    6186:	48 89 6c 24 08       	mov    %rbp,0x8(%rsp)
    618b:	31 db                	xor    %ebx,%ebx
    618d:	41 8b 8f 34 01 00 00 	mov    0x134(%r15),%ecx
    6194:	49 c1 e5 06          	shl    $0x6,%r13
    6198:	4c 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%r14
    61a0:	eb 19                	jmp    61bb <barriered_work+0xeb>
    61a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    61a8:	41 39 5c 24 08       	cmp    %ebx,0x8(%r12)
    61ad:	0f 84 6d 01 00 00    	je     6320 <barriered_work+0x250>
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    61b3:	48 83 c3 01          	add    $0x1,%rbx
    61b7:	39 df                	cmp    %ebx,%edi
    61b9:	7e 79                	jle    6234 <barriered_work+0x164>
              int next_task = abs((t + 1) % (data->thread_count));
    61bb:	44 89 d0             	mov    %r10d,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    61be:	4d 8b a7 28 01 00 00 	mov    0x128(%r15),%r12
    61c5:	48 8d 2c db          	lea    (%rbx,%rbx,8),%rbp
              int next_task = abs((t + 1) % (data->thread_count));
    61c9:	99                   	cltd
    61ca:	f7 f9                	idiv   %ecx
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    61cc:	4d 8b 4c 24 20       	mov    0x20(%r12),%r9
              int next_task = abs((t + 1) % (data->thread_count));
    61d1:	89 d0                	mov    %edx,%eax
    61d3:	f7 d8                	neg    %eax
    61d5:	0f 49 d0             	cmovns %eax,%edx
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    61d8:	4b 8b 44 29 38       	mov    0x38(%r9,%r13,1),%rax
    61dd:	48 c1 e5 03          	shl    $0x3,%rbp
    61e1:	4a 8b b4 00 70 01 00 00 	mov    0x170(%rax,%r8,1),%rsi
    61e9:	48 01 ee             	add    %rbp,%rsi
              if (kind == MAILBOX_FRIEND) {
    61ec:	83 7e 40 01          	cmpl   $0x1,0x40(%rsi)
    61f0:	75 b6                	jne    61a8 <barriered_work+0xd8>
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    61f2:	48 63 46 44          	movslq 0x44(%rsi),%rax
    61f6:	48 63 d2             	movslq %edx,%rdx
                  void * _a = data->thread->all_threads[y].tasks[t].mailboxes[b].higher;
    61f9:	f3 0f 6f 06          	movdqu (%rsi),%xmm0
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    61fd:	48 83 c3 01          	add    $0x1,%rbx
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    6201:	48 c1 e2 09          	shl    $0x9,%rdx
    6205:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
                  void * _b = data->thread->all_threads[y].tasks[t].mailboxes[b].lower;
    6209:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    620e:	48 c1 e0 06          	shl    $0x6,%rax
    6212:	49 03 54 01 38       	add    0x38(%r9,%rax,1),%rdx
    6217:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
    621e:	4c 01 f0             	add    %r14,%rax
                  void * _d = data->thread->all_threads[other].tasks[next_task].mailboxes[y].lower;
    6221:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    6225:	66 0f c6 c9 01       	shufpd $0x1,%xmm1,%xmm1
                  data->thread->all_threads[y].tasks[t].mailboxes[b].lower = _c;
    622a:	0f 11 0e             	movups %xmm1,(%rsi)
                  data->thread->all_threads[other].tasks[next_task].mailboxes[y].lower = _a;
    622d:	0f 11 00             	movups %xmm0,(%rax)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6230:	39 df                	cmp    %ebx,%edi
    6232:	7f 87                	jg     61bb <barriered_work+0xeb>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6234:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    6239:	48 83 c5 01          	add    $0x1,%rbp
    623d:	39 ef                	cmp    %ebp,%edi
    623f:	0f 8f 2b ff ff ff    	jg     6170 <barriered_work+0xa0>
    6245:	0f 1f 00             	nopl   (%rax)
      asm volatile ("sfence" ::: "memory");
    6248:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    624b:	49 8b b7 60 01 00 00 	mov    0x160(%r15),%rsi
    6252:	31 ff                	xor    %edi,%edi
    6254:	48 c1 e6 05          	shl    $0x5,%rsi
    6258:	49 03 b7 50 01 00 00 	add    0x150(%r15),%rsi
    625f:	e8 ac c0 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6264:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    while (data->scheduled == 1) {
    626b:	41 83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r15)
    int modcount = ++data->thread->protected_state->modcount;
    6273:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6277:	8b 4a 10             	mov    0x10(%rdx),%ecx
    627a:	8d 59 01             	lea    0x1(%rcx),%ebx
    627d:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    6280:	75 59                	jne    62db <barriered_work+0x20b>
    6282:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6288:	49 63 97 30 01 00 00 	movslq 0x130(%r15),%rdx
    628f:	48 8b 40 18          	mov    0x18(%rax),%rax
    6293:	49 63 7f 04          	movslq 0x4(%r15),%rdi
      data->n++;
    6297:	49 83 87 08 01 00 00 01 	addq   $0x1,0x108(%r15)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    629f:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    62a3:	48 c1 e7 09          	shl    $0x9,%rdi
    62a7:	48 03 78 38          	add    0x38(%rax),%rdi
    62ab:	41 ff 97 20 01 00 00 	call   *0x120(%r15)
      asm volatile ("sfence" ::: "memory");
    62b2:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    62b5:	41 83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r15)
    if (modcount != data->thread->protected_state->modcount) {
    62bd:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    while (data->scheduled == 1) {
    62c4:	74 c2                	je     6288 <barriered_work+0x1b8>
    if (modcount != data->thread->protected_state->modcount) {
    62c6:	48 8b 40 48          	mov    0x48(%rax),%rax
    62ca:	3b 58 10             	cmp    0x10(%rax),%ebx
    62cd:	74 0c                	je     62db <barriered_work+0x20b>
    62cf:	48 8d 3d 4f 0f 00 00 	lea    0xf4f(%rip),%rdi        # 7225 <_IO_stdin_used+0x225>
    62d6:	e8 15 c0 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    62db:	49 8b b7 60 01 00 00 	mov    0x160(%r15),%rsi
    62e2:	31 ff                	xor    %edi,%edi
    62e4:	48 c1 e6 05          	shl    $0x5,%rsi
    62e8:	49 03 b7 50 01 00 00 	add    0x150(%r15),%rsi
    62ef:	48 83 c6 10          	add    $0x10,%rsi
    62f3:	e8 18 c0 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    62f8:	49 8b 87 60 01 00 00 	mov    0x160(%r15),%rax
    62ff:	48 83 c0 01          	add    $0x1,%rax
    6303:	48 99                	cqto
    6305:	49 f7 bf 58 01 00 00 	idivq  0x158(%r15)
    630c:	49 89 97 60 01 00 00 	mov    %rdx,0x160(%r15)
    6313:	e9 fd fd ff ff       	jmp    6115 <barriered_work+0x45>
    6318:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6320:	48 8d 34 5b          	lea    (%rbx,%rbx,2),%rsi
    6324:	48 c1 e6 06          	shl    $0x6,%rsi
    6328:	49 89 f3             	mov    %rsi,%r11
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    632b:	49 8b 74 31 38       	mov    0x38(%r9,%rsi,1),%rsi
    6330:	4e 8b 8c 06 70 01 00 00 	mov    0x170(%rsi,%r8,1),%r9
    6338:	43 83 7c 31 40 02    	cmpl   $0x2,0x40(%r9,%r14,1)
    633e:	0f 85 6f fe ff ff    	jne    61b3 <barriered_work+0xe3>
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    6344:	85 c9                	test   %ecx,%ecx
    6346:	7e 5f                	jle    63a7 <barriered_work+0x2d7>
    6348:	4c 63 e1             	movslq %ecx,%r12
                      all_finished = 0;
    634b:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    6350:	49 c1 e4 09          	shl    $0x9,%r12
    6354:	4c 89 44 24 20       	mov    %r8,0x20(%rsp)
    6359:	4e 8d 0c 26          	lea    (%rsi,%r12,1),%r9
    635d:	45 31 e4             	xor    %r12d,%r12d
    6360:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    6365:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
                  int all_finished = 1;
    636a:	41 b9 01 00 00 00    	mov    $0x1,%r9d
                    if (((struct Data*)data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->finished_reading == 0 || ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->finished_reading == 0) {
    6370:	48 8b 86 70 01 00 00 	mov    0x170(%rsi),%rax
    6377:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
                      all_finished = 0;
    637b:	8b 80 00 03 00 00    	mov    0x300(%rax),%eax
    6381:	85 c0                	test   %eax,%eax
    6383:	45 0f 44 cc          	cmove  %r12d,%r9d
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    6387:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    638e:	49 39 f0             	cmp    %rsi,%r8
    6391:	75 dd                	jne    6370 <barriered_work+0x2a0>
                   if (all_finished == 1 && ((struct Data*) data->thread->all_threads[y].tasks[next_task].mailboxes[b].higher)->available_receiving == 1/*&& ((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available == 0 */) {
    6393:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6398:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    639d:	41 83 f9 01          	cmp    $0x1,%r9d
    63a1:	0f 85 0c fe ff ff    	jne    61b3 <barriered_work+0xe3>
    63a7:	48 63 d2             	movslq %edx,%rdx
    63aa:	48 c1 e2 09          	shl    $0x9,%rdx
    63ae:	48 8b 84 10 70 01 00 00 	mov    0x170(%rax,%rdx,1),%rax
    63b6:	49 89 d4             	mov    %rdx,%r12
    63b9:	48 8b 44 28 08       	mov    0x8(%rax,%rbp,1),%rax
    63be:	83 b8 80 01 00 00 01 	cmpl   $0x1,0x180(%rax)
    63c5:	0f 85 e8 fd ff ff    	jne    61b3 <barriered_work+0xe3>
    63cb:	8b 4c 24 48          	mov    0x48(%rsp),%ecx
    63cf:	89 da                	mov    %ebx,%edx
    63d1:	48 8d 35 d8 11 00 00 	lea    0x11d8(%rip),%rsi        # 75b0 <_IO_stdin_used+0x5b0>
    63d8:	31 c0                	xor    %eax,%eax
    63da:	bf 01 00 00 00       	mov    $0x1,%edi
    63df:	44 89 54 24 4c       	mov    %r10d,0x4c(%rsp)
    63e4:	4c 89 44 24 20       	mov    %r8,0x20(%rsp)
    63e9:	4c 89 5c 24 40       	mov    %r11,0x40(%rsp)
    63ee:	e8 5d c0 ff ff       	call   2450 <__printf_chk@plt>
                      void * left2 = data->thread->all_threads[b].tasks[next_task].mailboxes[y].stack[0];
    63f3:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    63f8:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
                      ((struct Data*)data->thread->all_threads[y].tasks[next_task].mailboxes[b].higher)->available_receiving = 0;
    63fd:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6404:	44 8b 54 24 4c       	mov    0x4c(%rsp),%r10d
                      ((struct Data*)data->thread->all_threads[y].tasks[next_task].mailboxes[b].higher)->available_receiving = 0;
    6409:	48 8b 40 20          	mov    0x20(%rax),%rax
    640d:	4a 8b 4c 28 38       	mov    0x38(%rax,%r13,1),%rcx
                      void * left2 = data->thread->all_threads[b].tasks[next_task].mailboxes[y].stack[0];
    6412:	4a 8b 44 18 38       	mov    0x38(%rax,%r11,1),%rax
                      ((struct Data*)data->thread->all_threads[y].tasks[next_task].mailboxes[b].higher)->available_receiving = 0;
    6417:	4a 8b bc 21 70 01 00 00 	mov    0x170(%rcx,%r12,1),%rdi
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    641f:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
                      void * left2 = data->thread->all_threads[b].tasks[next_task].mailboxes[y].stack[0];
    6424:	4e 8b 8c 20 70 01 00 00 	mov    0x170(%rax,%r12,1),%r9
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    642c:	4a 8b 84 00 70 01 00 00 	mov    0x170(%rax,%r8,1),%rax
                      ((struct Data*)data->thread->all_threads[y].tasks[next_task].mailboxes[b].higher)->available_receiving = 0;
    6434:	48 01 ef             	add    %rbp,%rdi
    6437:	48 8b 57 08          	mov    0x8(%rdi),%rdx
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    643b:	4a 8b 44 30 18       	mov    0x18(%rax,%r14,1),%rax
                      ((struct Data*)data->thread->all_threads[y].tasks[next_task].mailboxes[b].higher)->available_receiving = 0;
    6440:	48 89 7c 24 18       	mov    %rdi,0x18(%rsp)
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    6445:	48 89 cf             	mov    %rcx,%rdi
    6448:	48 89 e9             	mov    %rbp,%rcx
    644b:	4a 03 8c 07 70 01 00 00 	add    0x170(%rdi,%r8,1),%rcx
                      void * left2 = data->thread->all_threads[b].tasks[next_task].mailboxes[y].stack[0];
    6453:	4d 01 f1             	add    %r14,%r9
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    6456:	48 8b 79 18          	mov    0x18(%rcx),%rdi
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    645a:	4c 8b 60 08          	mov    0x8(%rax),%r12
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    645e:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
                      ((struct Data*)data->thread->all_threads[y].tasks[next_task].mailboxes[b].higher)->available_receiving = 0;
    6463:	c7 82 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rdx)
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    646d:	48 8b 37             	mov    (%rdi),%rsi
    6470:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
                      void * right = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1];
    6475:	48 8b 7f 08          	mov    0x8(%rdi),%rdi
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    6479:	48 89 74 24 30       	mov    %rsi,0x30(%rsp)
                      ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available_swapping = 0;
    647e:	49 8b 71 08          	mov    0x8(%r9),%rsi
                      void * right = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1];
    6482:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    6487:	48 8b 38             	mov    (%rax),%rdi
                      ((struct Data*)data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available_receiving = 0;
    648a:	48 8b 41 08          	mov    0x8(%rcx),%rax
                      for (int nn = 0; nn < data->thread_count; nn++) {
    648e:	41 8b 8f 34 01 00 00 	mov    0x134(%r15),%ecx
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    6495:	48 89 7c 24 40       	mov    %rdi,0x40(%rsp)
                      struct Data* d = ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower);
    649a:	49 8b 39             	mov    (%r9),%rdi
                      ((struct Data*)data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available_receiving = 0;
    649d:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    64a7:	85 c9                	test   %ecx,%ecx
                      ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available_swapping = 0;
    64a9:	c7 86 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rsi)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    64b3:	7e 3d                	jle    64f2 <barriered_work+0x422>
    64b5:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    64ba:	48 63 f1             	movslq %ecx,%rsi
    64bd:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    64c2:	48 c1 e6 09          	shl    $0x9,%rsi
    64c6:	48 01 c6             	add    %rax,%rsi
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].higher = d;
    64c9:	48 8b 90 70 01 00 00 	mov    0x170(%rax),%rdx
                      for (int nn = 0; nn < data->thread_count; nn++) {
    64d0:	48 05 00 02 00 00    	add    $0x200,%rax
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].higher = d;
    64d6:	48 89 7c 2a 08       	mov    %rdi,0x8(%rdx,%rbp,1)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    64db:	48 39 f0             	cmp    %rsi,%rax
    64de:	75 e9                	jne    64c9 <barriered_work+0x3f9>
                      ((struct Data*)data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available_sending = 1;
    64e0:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    64e5:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
                      ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available_sending = 1;
    64ea:	49 8b 71 08          	mov    0x8(%r9),%rsi
                      ((struct Data*)data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available_sending = 1;
    64ee:	48 8b 40 08          	mov    0x8(%rax),%rax
                      ((struct Data*)data->thread->all_threads[y].tasks[next_task].mailboxes[b].lower)->available_reading = 1;
    64f2:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
                      data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = a;
    64f7:	49 89 11             	mov    %rdx,(%r9)
                      ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available_reading = 1;
    64fa:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                      ((struct Data*)data->thread->all_threads[y].tasks[next_task].mailboxes[b].lower)->available_reading = 1;
    6504:	48 8b 17             	mov    (%rdi),%rdx
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0] = right;
    6507:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
                      ((struct Data*)data->thread->all_threads[y].tasks[next_task].mailboxes[b].lower)->available_reading = 1;
    650c:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                      ((struct Data*)data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available_sending = 1;
    6516:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0] = right;
    6520:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
                      ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available_sending = 1;
    6525:	c7 86 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rsi)
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0] = right;
    652f:	48 89 38             	mov    %rdi,(%rax)
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1] = left;
    6532:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    6539:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    653e:	48 8b 40 20          	mov    0x20(%rax),%rax
    6542:	4a 8b 44 28 38       	mov    0x38(%rax,%r13,1),%rax
    6547:	4a 8b 84 00 70 01 00 00 	mov    0x170(%rax,%r8,1),%rax
    654f:	48 8b 44 28 18       	mov    0x18(%rax,%rbp,1),%rax
    6554:	48 89 78 08          	mov    %rdi,0x8(%rax)
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0] = right3;
    6558:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1] = left3;
    655f:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0] = right3;
    6564:	48 8b 40 20          	mov    0x20(%rax),%rax
    6568:	4a 8b 44 18 38       	mov    0x38(%rax,%r11,1),%rax
    656d:	4a 8b 84 00 70 01 00 00 	mov    0x170(%rax,%r8,1),%rax
    6575:	4a 8b 44 30 18       	mov    0x18(%rax,%r14,1),%rax
    657a:	4c 89 20             	mov    %r12,(%rax)
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1] = left3;
    657d:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    6584:	48 8b 40 20          	mov    0x20(%rax),%rax
    6588:	4a 8b 44 18 38       	mov    0x38(%rax,%r11,1),%rax
    658d:	4a 8b 84 00 70 01 00 00 	mov    0x170(%rax,%r8,1),%rax
    6595:	4a 8b 44 30 18       	mov    0x18(%rax,%r14,1),%rax
    659a:	48 89 78 08          	mov    %rdi,0x8(%rax)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    659e:	41 8b bf 40 01 00 00 	mov    0x140(%r15),%edi
    65a5:	e9 09 fc ff ff       	jmp    61b3 <barriered_work+0xe3>
    65aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000065b0 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    65b0:	f3 0f 1e fa          	endbr64
    65b4:	53                   	push   %rbx
    65b5:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    65b8:	e8 43 f5 ff ff       	call   5b00 <barriered_work_ingest>
  barriered_work(data);
    65bd:	48 89 df             	mov    %rbx,%rdi
}
    65c0:	5b                   	pop    %rbx
  barriered_work(data);
    65c1:	e9 0a fb ff ff       	jmp    60d0 <barriered_work>
    65c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000065d0 <sendm>:
int sendm(struct BarrierTask *data) {
    65d0:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    65d4:	83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%rdi)
    65db:	74 03                	je     65e0 <sendm+0x10>
}
    65dd:	31 c0                	xor    %eax,%eax
    65df:	c3                   	ret
int sendm(struct BarrierTask *data) {
    65e0:	48 83 ec 08          	sub    $0x8,%rsp
    65e4:	e8 77 dd ff ff       	call   4360 <sendm.part.0>
}
    65e9:	31 c0                	xor    %eax,%eax
    65eb:	48 83 c4 08          	add    $0x8,%rsp
    65ef:	c3                   	ret

00000000000065f0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    65f0:	f3 0f 1e fa          	endbr64
}
    65f4:	31 c0                	xor    %eax,%eax
    65f6:	c3                   	ret
    65f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006600 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6600:	f3 0f 1e fa          	endbr64
    6604:	31 c0                	xor    %eax,%eax
    6606:	c3                   	ret
    6607:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006610 <after>:
int after(struct timespec left, struct timespec right) {
    6610:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6614:	31 c0                	xor    %eax,%eax
    6616:	48 39 d7             	cmp    %rdx,%rdi
    6619:	7e 08                	jle    6623 <after+0x13>
    661b:	31 c0                	xor    %eax,%eax
    661d:	48 39 ce             	cmp    %rcx,%rsi
    6620:	0f 9f c0             	setg   %al
}
    6623:	c3                   	ret
    6624:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    662f:	90                   	nop

0000000000006630 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6630:	f3 0f 1e fa          	endbr64
    6634:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6639:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    663e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6640:	48 39 d7             	cmp    %rdx,%rdi
    6643:	7f 18                	jg     665d <within+0x2d>
    6645:	4d 39 d8             	cmp    %r11,%r8
    6648:	0f 9e c2             	setle  %dl
    664b:	48 39 ce             	cmp    %rcx,%rsi
    664e:	0f 9e c0             	setle  %al
    6651:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6653:	31 c0                	xor    %eax,%eax
    6655:	4d 39 d1             	cmp    %r10,%r9
    6658:	0f 9e c0             	setle  %al
    665b:	21 d0                	and    %edx,%eax
}
    665d:	c3                   	ret
    665e:	66 90                	xchg   %ax,%ax

0000000000006660 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6660:	f3 0f 1e fa          	endbr64
    6664:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6669:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    666e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6673:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6678:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    667d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6682:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6687:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    668c:	48 39 fe             	cmp    %rdi,%rsi
    668f:	7d 2f                	jge    66c0 <overlap+0x60>
    6691:	48 39 ca             	cmp    %rcx,%rdx
    6694:	7d 62                	jge    66f8 <overlap+0x98>
    6696:	4d 39 da             	cmp    %r11,%r10
    6699:	7d 0e                	jge    66a9 <overlap+0x49>
    return 1;
    669b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    66a0:	4d 39 c1             	cmp    %r8,%r9
    66a3:	0f 8c 7f 00 00 00    	jl     6728 <overlap+0xc8>
  return 0;
    66a9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    66ab:	4d 39 c1             	cmp    %r8,%r9
    66ae:	7f 4c                	jg     66fc <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    66b0:	31 c0                	xor    %eax,%eax
    66b2:	4d 39 da             	cmp    %r11,%r10
    66b5:	0f 9e c0             	setle  %al
    66b8:	c3                   	ret
    66b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    66c0:	7e 4e                	jle    6710 <overlap+0xb0>
    66c2:	48 39 ca             	cmp    %rcx,%rdx
    66c5:	7f 39                	jg     6700 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    66c7:	75 31                	jne    66fa <overlap+0x9a>
    66c9:	4d 39 c1             	cmp    %r8,%r9
    66cc:	7c 2c                	jl     66fa <overlap+0x9a>
    return 1;
    66ce:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    66d3:	4d 39 da             	cmp    %r11,%r10
    66d6:	7d 24                	jge    66fc <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    66d8:	48 39 ca             	cmp    %rcx,%rdx
    66db:	0f 94 c2             	sete   %dl
    66de:	48 39 fe             	cmp    %rdi,%rsi
    66e1:	0f 94 c0             	sete   %al
    66e4:	21 c2                	and    %eax,%edx
    66e6:	31 c0                	xor    %eax,%eax
    66e8:	4d 39 c1             	cmp    %r8,%r9
    66eb:	0f 94 c0             	sete   %al
    66ee:	21 d0                	and    %edx,%eax
    66f0:	c3                   	ret
    66f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    66f8:	74 af                	je     66a9 <overlap+0x49>
  return 0;
    66fa:	31 c0                	xor    %eax,%eax
}
    66fc:	c3                   	ret
    66fd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6700:	4d 39 da             	cmp    %r11,%r10
    6703:	7e c4                	jle    66c9 <overlap+0x69>
    return 1;
    6705:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    670a:	4d 39 c1             	cmp    %r8,%r9
    670d:	7e ba                	jle    66c9 <overlap+0x69>
    670f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6710:	48 39 ca             	cmp    %rcx,%rdx
    6713:	7c 94                	jl     66a9 <overlap+0x49>
    6715:	4d 39 c1             	cmp    %r8,%r9
    6718:	7d b4                	jge    66ce <overlap+0x6e>
    671a:	48 39 ca             	cmp    %rcx,%rdx
    671d:	74 91                	je     66b0 <overlap+0x50>
    671f:	eb d9                	jmp    66fa <overlap+0x9a>
    6721:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6728:	c3                   	ret
    6729:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006730 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6730:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6734:	85 f6                	test   %esi,%esi
    6736:	0f 8e 44 03 00 00    	jle    6a80 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    673c:	41 57                	push   %r15
    673e:	41 89 f7             	mov    %esi,%r15d
    6741:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6743:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6746:	41 55                	push   %r13
    6748:	41 54                	push   %r12
    674a:	55                   	push   %rbp
    674b:	53                   	push   %rbx
    674c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6750:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6754:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6759:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    675e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6761:	45 39 e6             	cmp    %r12d,%r14d
    6764:	0f 84 4e 02 00 00    	je     69b8 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    676a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    676f:	8b 50 08             	mov    0x8(%rax),%edx
    6772:	85 d2                	test   %edx,%edx
    6774:	0f 8e 3e 02 00 00    	jle    69b8 <verify+0x288>
    677a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    677f:	31 c9                	xor    %ecx,%ecx
    6781:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    6786:	31 c0                	xor    %eax,%eax
    6788:	44 89 f2             	mov    %r14d,%edx
    678b:	bf 01 00 00 00       	mov    $0x1,%edi
    6790:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6795:	48 8d 35 99 0a 00 00 	lea    0xa99(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    679c:	e8 af bc ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    67a1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    67a6:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    67ab:	8b 40 08             	mov    0x8(%rax),%eax
    67ae:	85 c0                	test   %eax,%eax
    67b0:	0f 8e e6 01 00 00    	jle    699c <verify+0x26c>
    67b6:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    67b9:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    67be:	31 db                	xor    %ebx,%ebx
    67c0:	48 c1 e0 09          	shl    $0x9,%rax
    67c4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    67c9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    67ce:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    67d3:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    67d8:	4c 8b 20             	mov    (%rax),%r12
    67db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    67e0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    67e5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    67ea:	49 89 de             	mov    %rbx,%r14
    67ed:	48 8d 35 56 0a 00 00 	lea    0xa56(%rip),%rsi        # 724a <_IO_stdin_used+0x24a>
    67f4:	49 c1 e6 09          	shl    $0x9,%r14
    67f8:	bf 01 00 00 00       	mov    $0x1,%edi
    67fd:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6801:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    6809:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    680e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    6816:	31 c0                	xor    %eax,%eax
    6818:	e8 33 bc ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    681d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6822:	4c 8b 20             	mov    (%rax),%r12
    6825:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    682e:	0f 8e 47 01 00 00    	jle    697b <verify+0x24b>
    6834:	4c 03 75 00          	add    0x0(%rbp),%r14
    6838:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    683d:	ba 01 00 00 00       	mov    $0x1,%edx
    6842:	4d 89 f5             	mov    %r14,%r13
    6845:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    684c:	4d 85 f6             	test   %r14,%r14
    684f:	0f 8e 21 01 00 00    	jle    6976 <verify+0x246>
    6855:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6858:	48 89 d5             	mov    %rdx,%rbp
    685b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6860:	31 db                	xor    %ebx,%ebx
    6862:	4d 89 f2             	mov    %r14,%r10
    6865:	48 c1 e5 05          	shl    $0x5,%rbp
    6869:	48 83 ed 20          	sub    $0x20,%rbp
    686d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6871:	49 89 ee             	mov    %rbp,%r14
    6874:	48 89 dd             	mov    %rbx,%rbp
    6877:	48 89 d3             	mov    %rdx,%rbx
    687a:	eb 31                	jmp    68ad <verify+0x17d>
    687c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6880:	4c 39 c2             	cmp    %r8,%rdx
    6883:	0f 8d 57 01 00 00    	jge    69e0 <verify+0x2b0>
    6889:	4c 39 df             	cmp    %r11,%rdi
    688c:	7e 05                	jle    6893 <verify+0x163>
    688e:	49 39 c1             	cmp    %rax,%r9
    6891:	7c 75                	jl     6908 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6893:	4c 39 df             	cmp    %r11,%rdi
    6896:	0f 8d ab 01 00 00    	jge    6a47 <verify+0x317>
    689c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    68a0:	48 83 c5 01          	add    $0x1,%rbp
    68a4:	49 39 ea             	cmp    %rbp,%r10
    68a7:	0f 8e a9 00 00 00    	jle    6956 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    68ad:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    68b4:	48 89 e8             	mov    %rbp,%rax
    68b7:	48 c1 e0 05          	shl    $0x5,%rax
    68bb:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    68c2:	4c 01 f2             	add    %r14,%rdx
    68c5:	48 8b 08             	mov    (%rax),%rcx
    68c8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    68cc:	48 8b 32             	mov    (%rdx),%rsi
    68cf:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    68d3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    68d7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    68db:	48 8b 50 08          	mov    0x8(%rax),%rdx
    68df:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    68e3:	48 39 f1             	cmp    %rsi,%rcx
    68e6:	7c 98                	jl     6880 <verify+0x150>
    68e8:	0f 8e 42 01 00 00    	jle    6a30 <verify+0x300>
    68ee:	4c 39 c2             	cmp    %r8,%rdx
    68f1:	0f 8f f9 00 00 00    	jg     69f0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    68f7:	75 a7                	jne    68a0 <verify+0x170>
    68f9:	4c 39 df             	cmp    %r11,%rdi
    68fc:	7f a2                	jg     68a0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    68fe:	49 39 c1             	cmp    %rax,%r9
    6901:	7c 9d                	jl     68a0 <verify+0x170>
    6903:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6908:	49 89 c1             	mov    %rax,%r9
    690b:	48 89 f9             	mov    %rdi,%rcx
    690e:	48 89 f2             	mov    %rsi,%rdx
    6911:	bf 01 00 00 00       	mov    $0x1,%edi
    6916:	48 8d 35 d3 0c 00 00 	lea    0xcd3(%rip),%rsi        # 75f0 <_IO_stdin_used+0x5f0>
    691d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    691f:	48 83 c5 01          	add    $0x1,%rbp
    6923:	e8 28 bb ff ff       	call   2450 <__printf_chk@plt>
    6928:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    692d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    6932:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6935:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    693a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6941:	4c 8b 20             	mov    (%rax),%r12
    6944:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6949:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    694d:	49 39 ea             	cmp    %rbp,%r10
    6950:	0f 8f 57 ff ff ff    	jg     68ad <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6956:	48 89 da             	mov    %rbx,%rdx
    6959:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    6960:	7d 14                	jge    6976 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6962:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6969:	48 83 c2 01          	add    $0x1,%rdx
    696d:	4d 85 f6             	test   %r14,%r14
    6970:	0f 8f e2 fe ff ff    	jg     6858 <verify+0x128>
    6976:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    697b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6980:	48 83 c3 01          	add    $0x1,%rbx
    6984:	39 58 08             	cmp    %ebx,0x8(%rax)
    6987:	0f 8f 53 fe ff ff    	jg     67e0 <verify+0xb0>
    698d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6992:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6997:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    699c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    69a1:	48 83 c1 01          	add    $0x1,%rcx
    69a5:	39 48 08             	cmp    %ecx,0x8(%rax)
    69a8:	0f 8f d8 fd ff ff    	jg     6786 <verify+0x56>
    69ae:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    69b3:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    69b8:	48 81 44 24 10 c0 00 00 00 	addq   $0xc0,0x10(%rsp)
    69c1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    69c6:	41 39 c7             	cmp    %eax,%r15d
    69c9:	0f 84 86 00 00 00    	je     6a55 <verify+0x325>
    69cf:	41 89 c4             	mov    %eax,%r12d
    69d2:	e9 8a fd ff ff       	jmp    6761 <verify+0x31>
    69d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    69e0:	0f 85 ba fe ff ff    	jne    68a0 <verify+0x170>
    69e6:	e9 a8 fe ff ff       	jmp    6893 <verify+0x163>
    69eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    69f0:	49 39 c1             	cmp    %rax,%r9
    69f3:	7e 09                	jle    69fe <verify+0x2ce>
    69f5:	4c 39 df             	cmp    %r11,%rdi
    69f8:	0f 8c 0a ff ff ff    	jl     6908 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    69fe:	4c 39 df             	cmp    %r11,%rdi
    6a01:	0f 8f 99 fe ff ff    	jg     68a0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6a07:	49 39 c1             	cmp    %rax,%r9
    6a0a:	0f 8d f8 fe ff ff    	jge    6908 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6a10:	48 39 f1             	cmp    %rsi,%rcx
    6a13:	0f 85 87 fe ff ff    	jne    68a0 <verify+0x170>
    6a19:	4c 39 c2             	cmp    %r8,%rdx
    6a1c:	0f 85 7e fe ff ff    	jne    68a0 <verify+0x170>
    6a22:	4c 39 df             	cmp    %r11,%rdi
    6a25:	0f 84 dd fe ff ff    	je     6908 <verify+0x1d8>
    6a2b:	e9 70 fe ff ff       	jmp    68a0 <verify+0x170>
    6a30:	4c 39 c2             	cmp    %r8,%rdx
    6a33:	0f 8c 5a fe ff ff    	jl     6893 <verify+0x163>
    6a39:	4c 39 df             	cmp    %r11,%rdi
    6a3c:	7e c9                	jle    6a07 <verify+0x2d7>
    6a3e:	4c 39 c2             	cmp    %r8,%rdx
    6a41:	0f 85 59 fe ff ff    	jne    68a0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6a47:	49 39 c1             	cmp    %rax,%r9
    6a4a:	0f 8f 50 fe ff ff    	jg     68a0 <verify+0x170>
    6a50:	e9 b3 fe ff ff       	jmp    6908 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    6a55:	48 81 44 24 18 c0 00 00 00 	addq   $0xc0,0x18(%rsp)
    6a5e:	41 8d 46 01          	lea    0x1(%r14),%eax
    6a62:	45 39 e6             	cmp    %r12d,%r14d
    6a65:	74 08                	je     6a6f <verify+0x33f>
    6a67:	41 89 c6             	mov    %eax,%r14d
    6a6a:	e9 ea fc ff ff       	jmp    6759 <verify+0x29>
}
    6a6f:	48 83 c4 58          	add    $0x58,%rsp
    6a73:	31 c0                	xor    %eax,%eax
    6a75:	5b                   	pop    %rbx
    6a76:	5d                   	pop    %rbp
    6a77:	41 5c                	pop    %r12
    6a79:	41 5d                	pop    %r13
    6a7b:	41 5e                	pop    %r14
    6a7d:	41 5f                	pop    %r15
    6a7f:	c3                   	ret
    6a80:	31 c0                	xor    %eax,%eax
    6a82:	c3                   	ret

Disassembly of section .fini:

0000000000006a84 <_fini>:
    6a84:	f3 0f 1e fa          	endbr64
    6a88:	48 83 ec 08          	sub    $0x8,%rsp
    6a8c:	48 83 c4 08          	add    $0x8,%rsp
    6a90:	c3                   	ret
