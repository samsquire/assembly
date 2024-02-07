
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
    25f6:	48 8d 3d 83 50 00 00 	lea    0x5083(%rip),%rdi        # 7680 <_IO_stdin_used+0x680>
    25fd:	41 56                	push   %r14
    25ff:	41 55                	push   %r13
    2601:	41 54                	push   %r12
    2603:	55                   	push   %rbp
    2604:	53                   	push   %rbx
    2605:	48 81 ec d8 00 00 00 	sub    $0xd8,%rsp
    260c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2615:	48 89 84 24 c8 00 00 00 	mov    %rax,0xc8(%rsp)
    261d:	48 8d 05 8c 1a 00 00 	lea    0x1a8c(%rip),%rax        # 40b0 <barriered_reset>
    2624:	66 48 0f 6e f0       	movq   %rax,%xmm6
    2629:	0f 16 35 48 76 00 00 	movhps 0x7648(%rip),%xmm6        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    2630:	0f 29 b4 24 80 00 00 00 	movaps %xmm6,0x80(%rsp)
    2638:	e8 b3 fc ff ff       	call   22f0 <puts@plt>
    263d:	bf 0a 00 00 00       	mov    $0xa,%edi
    2642:	e8 89 fc ff ff       	call   22d0 <putchar@plt>
    2647:	ba 01 00 00 00       	mov    $0x1,%edx
    264c:	48 8d 35 1b 4c 00 00 	lea    0x4c1b(%rip),%rsi        # 726e <_IO_stdin_used+0x26e>
    2653:	31 c0                	xor    %eax,%eax
    2655:	bf 01 00 00 00       	mov    $0x1,%edi
    265a:	e8 f1 fd ff ff       	call   2450 <__printf_chk@plt>
    265f:	ba 04 00 00 00       	mov    $0x4,%edx
    2664:	48 8d 35 13 4c 00 00 	lea    0x4c13(%rip),%rsi        # 727e <_IO_stdin_used+0x27e>
    266b:	31 c0                	xor    %eax,%eax
    266d:	bf 01 00 00 00       	mov    $0x1,%edi
    2672:	e8 d9 fd ff ff       	call   2450 <__printf_chk@plt>
    2677:	ba 02 00 00 00       	mov    $0x2,%edx
    267c:	48 8d 35 10 4c 00 00 	lea    0x4c10(%rip),%rsi        # 7293 <_IO_stdin_used+0x293>
    2683:	31 c0                	xor    %eax,%eax
    2685:	bf 01 00 00 00       	mov    $0x1,%edi
    268a:	e8 c1 fd ff ff       	call   2450 <__printf_chk@plt>
    268f:	ba 02 00 00 00       	mov    $0x2,%edx
    2694:	48 8d 35 08 4c 00 00 	lea    0x4c08(%rip),%rsi        # 72a3 <_IO_stdin_used+0x2a3>
    269b:	31 c0                	xor    %eax,%eax
    269d:	bf 01 00 00 00       	mov    $0x1,%edi
    26a2:	e8 a9 fd ff ff       	call   2450 <__printf_chk@plt>
    26a7:	48 8d 3d 0b 4c 00 00 	lea    0x4c0b(%rip),%rdi        # 72b9 <_IO_stdin_used+0x2b9>
    26ae:	e8 3d fc ff ff       	call   22f0 <puts@plt>
    26b3:	ba 02 00 00 00       	mov    $0x2,%edx
    26b8:	48 8d 35 16 4c 00 00 	lea    0x4c16(%rip),%rsi        # 72d5 <_IO_stdin_used+0x2d5>
    26bf:	31 c0                	xor    %eax,%eax
    26c1:	bf 01 00 00 00       	mov    $0x1,%edi
    26c6:	e8 85 fd ff ff       	call   2450 <__printf_chk@plt>
    26cb:	ba 08 00 00 00       	mov    $0x8,%edx
    26d0:	48 8d 35 18 4c 00 00 	lea    0x4c18(%rip),%rsi        # 72ef <_IO_stdin_used+0x2ef>
    26d7:	31 c0                	xor    %eax,%eax
    26d9:	bf 01 00 00 00       	mov    $0x1,%edi
    26de:	e8 6d fd ff ff       	call   2450 <__printf_chk@plt>
    26e3:	ba 01 00 00 00       	mov    $0x1,%edx
    26e8:	48 8d 35 14 4c 00 00 	lea    0x4c14(%rip),%rsi        # 7303 <_IO_stdin_used+0x303>
    26ef:	31 c0                	xor    %eax,%eax
    26f1:	bf 01 00 00 00       	mov    $0x1,%edi
    26f6:	e8 55 fd ff ff       	call   2450 <__printf_chk@plt>
    26fb:	ba 01 00 00 00       	mov    $0x1,%edx
    2700:	48 8d 35 0d 4c 00 00 	lea    0x4c0d(%rip),%rsi        # 7314 <_IO_stdin_used+0x314>
    2707:	31 c0                	xor    %eax,%eax
    2709:	bf 01 00 00 00       	mov    $0x1,%edi
    270e:	e8 3d fd ff ff       	call   2450 <__printf_chk@plt>
    2713:	ba 02 00 00 00       	mov    $0x2,%edx
    2718:	48 8d 35 0d 4c 00 00 	lea    0x4c0d(%rip),%rsi        # 732c <_IO_stdin_used+0x32c>
    271f:	31 c0                	xor    %eax,%eax
    2721:	bf 01 00 00 00       	mov    $0x1,%edi
    2726:	e8 25 fd ff ff       	call   2450 <__printf_chk@plt>
    272b:	ba 01 00 00 00       	mov    $0x1,%edx
    2730:	48 8d 35 b1 4f 00 00 	lea    0x4fb1(%rip),%rsi        # 76e8 <_IO_stdin_used+0x6e8>
    2737:	31 c0                	xor    %eax,%eax
    2739:	bf 01 00 00 00       	mov    $0x1,%edi
    273e:	e8 0d fd ff ff       	call   2450 <__printf_chk@plt>
    2743:	ba 01 00 00 00       	mov    $0x1,%edx
    2748:	48 8d 35 c9 4f 00 00 	lea    0x4fc9(%rip),%rsi        # 7718 <_IO_stdin_used+0x718>
    274f:	31 c0                	xor    %eax,%eax
    2751:	bf 01 00 00 00       	mov    $0x1,%edi
    2756:	e8 f5 fc ff ff       	call   2450 <__printf_chk@plt>
    275b:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2760:	48 8d 35 e1 4b 00 00 	lea    0x4be1(%rip),%rsi        # 7348 <_IO_stdin_used+0x348>
    2767:	31 c0                	xor    %eax,%eax
    2769:	bf 01 00 00 00       	mov    $0x1,%edi
    276e:	e8 dd fc ff ff       	call   2450 <__printf_chk@plt>
    2773:	ba 05 00 00 00       	mov    $0x5,%edx
    2778:	48 8d 35 e3 4b 00 00 	lea    0x4be3(%rip),%rsi        # 7362 <_IO_stdin_used+0x362>
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
    27a6:	be c8 00 00 00       	mov    $0xc8,%esi
    27ab:	bf 08 00 00 00       	mov    $0x8,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    27b0:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27b5:	e8 e6 fb ff ff       	call   23a0 <calloc@plt>
    27ba:	ba 04 00 00 00       	mov    $0x4,%edx
    27bf:	bf 01 00 00 00       	mov    $0x1,%edi
    27c4:	48 8d 35 ab 4b 00 00 	lea    0x4bab(%rip),%rsi        # 7376 <_IO_stdin_used+0x376>
    27cb:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    27d0:	31 c0                	xor    %eax,%eax
    27d2:	e8 79 fc ff ff       	call   2450 <__printf_chk@plt>
    27d7:	ba 08 00 00 00       	mov    $0x8,%edx
    27dc:	48 8d 35 a9 4b 00 00 	lea    0x4ba9(%rip),%rsi        # 738c <_IO_stdin_used+0x38c>
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
    2803:	49 89 c4             	mov    %rax,%r12
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
    2861:	48 8b 74 24 70       	mov    0x70(%rsp),%rsi
    2866:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    286b:	4c 89 e0             	mov    %r12,%rax
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
  for (int k = 0 ; k < group_count ; k++) {
    286e:	45 31 f6             	xor    %r14d,%r14d
  int cur_buffer = 0;
    2871:	c7 44 24 58 00 00 00 00 	movl   $0x0,0x58(%rsp)
  for (int x = 0 ; x < buffers_required; x++) {
    2879:	ba 03 00 00 00       	mov    $0x3,%edx
    287e:	45 89 f7             	mov    %r14d,%r15d
    2881:	48 89 b4 24 98 00 00 00 	mov    %rsi,0x98(%rsp)
    2889:	49 89 dc             	mov    %rbx,%r12
  int curcpu = 0;
    288c:	c7 84 24 a8 00 00 00 00 00 00 00 	movl   $0x0,0xa8(%rsp)
    2897:	48 89 9c 24 90 00 00 00 	mov    %rbx,0x90(%rsp)
    289f:	48 89 c3             	mov    %rax,%rbx
    for (int d = 0 ; d < threads_per_group ; d++) {
    28a2:	48 63 44 24 58       	movslq 0x58(%rsp),%rax
    28a7:	4c 89 a4 24 b0 00 00 00 	mov    %r12,0xb0(%rsp)
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    28af:	4d 89 e1             	mov    %r12,%r9
    28b2:	48 89 b4 24 a0 00 00 00 	mov    %rsi,0xa0(%rsp)
    28ba:	48 c1 e0 04          	shl    $0x4,%rax
    28be:	48 89 9c 24 b8 00 00 00 	mov    %rbx,0xb8(%rsp)
    28c6:	4c 8d 34 03          	lea    (%rbx,%rax,1),%r14
    28ca:	8d 42 fe             	lea    -0x2(%rdx),%eax
    28cd:	89 44 24 18          	mov    %eax,0x18(%rsp)
    28d1:	4c 89 74 24 50       	mov    %r14,0x50(%rsp)
    28d6:	41 89 d6             	mov    %edx,%r14d
    28d9:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
    28dd:	44 89 fa             	mov    %r15d,%edx
    28e0:	48 8d 35 59 4e 00 00 	lea    0x4e59(%rip),%rsi        # 7740 <_IO_stdin_used+0x740>
    28e7:	31 c0                	xor    %eax,%eax
    28e9:	bf 01 00 00 00       	mov    $0x1,%edi
    28ee:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      int x = (k * threads_per_group) + d;
    28f3:	44 8d 63 ff          	lea    -0x1(%rbx),%r12d
    28f7:	44 89 e1             	mov    %r12d,%ecx
    28fa:	e8 51 fb ff ff       	call   2450 <__printf_chk@plt>
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    28ff:	be 08 00 00 00       	mov    $0x8,%esi
    2904:	bf 02 00 00 00       	mov    $0x2,%edi
    2909:	e8 92 fa ff ff       	call   23a0 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    290e:	be 80 00 00 00       	mov    $0x80,%esi
    2913:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2918:	48 89 c5             	mov    %rax,%rbp
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    291b:	e8 80 fa ff ff       	call   23a0 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2920:	45 89 e0             	mov    %r12d,%r8d
    2923:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2928:	41 83 e0 01          	and    $0x1,%r8d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    292c:	49 89 c5             	mov    %rax,%r13
      if (x % 2 == 1) {
    292f:	44 89 44 24 48       	mov    %r8d,0x48(%rsp)
    2934:	0f 84 38 08 00 00    	je     3172 <main+0xb82>
        other = abs(x - 1) % total_threads;
    293a:	8d 43 fe             	lea    -0x2(%rbx),%eax
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    293d:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
        my_thread_data[1] = &thread_data[x]; 
    2942:	4c 89 ca             	mov    %r9,%rdx
        other = abs(x - 1) % total_threads;
    2945:	48 89 c3             	mov    %rax,%rbx
        my_thread_data[0] = &thread_data[other]; 
    2948:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    294c:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    2950:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2954:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
    2958:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    295d:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
        thread_data[x].thread_index = 1;
    2965:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2969:	89 d9                	mov    %ebx,%ecx
    296b:	48 8d 35 fe 4d 00 00 	lea    0x4dfe(%rip),%rsi        # 7770 <_IO_stdin_used+0x770>
    2972:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    2976:	44 89 e2             	mov    %r12d,%edx
        thread_data[x].protected_state = &protected_state[k];
    2979:	49 89 79 48          	mov    %rdi,0x48(%r9)
    297d:	bf 01 00 00 00       	mov    $0x1,%edi
    2982:	48 89 45 00          	mov    %rax,0x0(%rbp)
    2986:	31 c0                	xor    %eax,%eax
    2988:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    298d:	e8 be fa ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].other = other;
    2992:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2997:	31 c0                	xor    %eax,%eax
    2999:	44 89 e2             	mov    %r12d,%edx
    299c:	8b 8c 24 a8 00 00 00 	mov    0xa8(%rsp),%ecx
    29a3:	48 8d 35 f6 4d 00 00 	lea    0x4df6(%rip),%rsi        # 77a0 <_IO_stdin_used+0x7a0>
    29aa:	bf 01 00 00 00       	mov    $0x1,%edi
    29af:	41 89 99 b8 00 00 00 	mov    %ebx,0xb8(%r9)
    29b6:	e8 95 fa ff ff       	call   2450 <__printf_chk@plt>
        if (x < thread_count) {
    29bb:	41 83 fc 01          	cmp    $0x1,%r12d
    29bf:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    29c4:	0f 8f cf 07 00 00    	jg     3199 <main+0xba9>
          CPU_SET(curcpu, sendercpu);
    29ca:	48 63 84 24 a8 00 00 00 	movslq 0xa8(%rsp),%rax
    29d2:	48 89 c7             	mov    %rax,%rdi
    29d5:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    29db:	77 13                	ja     29f0 <main+0x400>
    29dd:	48 c1 e8 06          	shr    $0x6,%rax
    29e1:	ba 01 00 00 00       	mov    $0x1,%edx
    29e6:	89 f9                	mov    %edi,%ecx
    29e8:	48 d3 e2             	shl    %cl,%rdx
    29eb:	49 09 54 c5 00       	or     %rdx,0x0(%r13,%rax,8)
          curcpu += 2;
    29f0:	83 84 24 a8 00 00 00 02 	addl   $0x2,0xa8(%rsp)
      thread_data[x].all_threads = thread_data;
    29f8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    29fd:	49 89 69 18          	mov    %rbp,0x18(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a01:	be 10 00 00 00       	mov    $0x10,%esi
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a06:	31 ed                	xor    %ebp,%ebp
      thread_data[x].kind = KERNEL_THREAD;
    2a08:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a0f:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].all_threads = thread_data;
    2a14:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2a18:	48 8b 05 91 52 00 00 	mov    0x5291(%rip),%rax        # 7cb0 <_IO_stdin_used+0xcb0>
      thread_data[x].cpu_set = sendercpu;
    2a1f:	4d 89 a9 b0 00 00 00 	mov    %r13,0xb0(%r9)
      thread_data[x].group_count = group_count;
    2a26:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
      thread_data[x].thread_count = 2;
    2a2d:	48 8b 05 8c 52 00 00 	mov    0x528c(%rip),%rax        # 7cc0 <_IO_stdin_used+0xcc0>
      thread_data[x].real_thread_index = x;
    2a34:	45 89 61 08          	mov    %r12d,0x8(%r9)
      thread_data[x].thread_count = 2;
    2a38:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].task_count = total_barrier_count;
    2a3c:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
    2a44:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a49:	e8 52 f9 ff ff       	call   23a0 <calloc@plt>
    2a4e:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a53:	be 10 00 00 00       	mov    $0x10,%esi
    2a58:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a5d:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a61:	e8 3a f9 ff ff       	call   23a0 <calloc@plt>
    2a66:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a6b:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2a70:	66 0f 6f 3d 18 52 00 00 	movdqa 0x5218(%rip),%xmm7        # 7c90 <_IO_stdin_used+0xc90>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a78:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a7d:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2a81:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a89:	e8 12 f9 ff ff       	call   23a0 <calloc@plt>
    2a8e:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a93:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_timestamp_count = 0;
    2a98:	66 0f 6f 35 f0 51 00 00 	movdqa 0x51f0(%rip),%xmm6        # 7c90 <_IO_stdin_used+0xc90>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2aa0:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2aa5:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2aac:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2ab4:	e8 e7 f8 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks = barriers;
    2ab9:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
              data[0].messages_count = 0;
    2abe:	44 89 b4 24 ac 00 00 00 	mov    %r14d,0xac(%rsp)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2ac6:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks = barriers;
    2ac9:	49 89 41 38          	mov    %rax,0x38(%r9)
              data[0].messages_count = 0;
    2acd:	4c 89 4c 24 40       	mov    %r9,0x40(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2ad2:	4c 63 ed             	movslq %ebp,%r13
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2ad5:	be 38 00 00 00       	mov    $0x38,%esi
    2ada:	bf 04 00 00 00       	mov    $0x4,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2adf:	45 31 f6             	xor    %r14d,%r14d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2ae2:	4c 89 e8             	mov    %r13,%rax
    2ae5:	48 c1 e0 09          	shl    $0x9,%rax
    2ae9:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
    2aed:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    2af2:	48 8d 05 77 15 00 00 	lea    0x1577(%rip),%rax        # 4070 <do_protected_write>
    2af9:	48 89 83 20 01 00 00 	mov    %rax,0x120(%rbx)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2b00:	e8 9b f8 ff ff       	call   23a0 <calloc@plt>
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2b05:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    2b0a:	45 89 f5             	mov    %r14d,%r13d
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2b0d:	48 89 83 70 01 00 00 	mov    %rax,0x170(%rbx)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2b14:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2b17:	48 89 c3             	mov    %rax,%rbx
    2b1a:	8b 44 24 48          	mov    0x48(%rsp),%eax
    2b1e:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    2b23:	85 c0                	test   %eax,%eax
    2b25:	0f 84 05 04 00 00    	je     2f30 <main+0x940>
            int group_of = b / threads_per_group;
    2b2b:	45 89 ee             	mov    %r13d,%r14d
    2b2e:	31 c0                	xor    %eax,%eax
    2b30:	44 89 ea             	mov    %r13d,%edx
    2b33:	bf 01 00 00 00       	mov    $0x1,%edi
    2b38:	41 d1 fe             	sar    %r14d
    2b3b:	48 8d 35 64 48 00 00 	lea    0x4864(%rip),%rsi        # 73a6 <_IO_stdin_used+0x3a6>
    2b42:	44 89 f1             	mov    %r14d,%ecx
    2b45:	e8 06 f9 ff ff       	call   2450 <__printf_chk@plt>
            if (k == group_of) {
    2b4a:	45 39 f7             	cmp    %r14d,%r15d
    2b4d:	0f 84 18 04 00 00    	je     2f6b <main+0x97b>
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2b53:	41 83 c5 01          	add    $0x1,%r13d
    2b57:	48 83 c3 38          	add    $0x38,%rbx
    2b5b:	41 83 fd 04          	cmp    $0x4,%r13d
    2b5f:	75 ca                	jne    2b2b <main+0x53b>
    2b61:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    2b66:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    2b6b:	44 89 7c 24 08       	mov    %r15d,0x8(%rsp)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2b70:	31 db                	xor    %ebx,%ebx
    2b72:	41 89 ef             	mov    %ebp,%r15d
    2b75:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    2b7a:	48 89 cd             	mov    %rcx,%rbp
    2b7d:	45 89 e5             	mov    %r12d,%r13d
            int group_of = b / threads_per_group;
    2b80:	89 d8                	mov    %ebx,%eax
    2b82:	d1 f8                	sar    %eax
            if (k == group_of) {
    2b84:	39 44 24 08          	cmp    %eax,0x8(%rsp)
    2b88:	0f 84 23 01 00 00    	je     2cb1 <main+0x6c1>
    2b8e:	89 da                	mov    %ebx,%edx
    2b90:	48 8d 35 1f 48 00 00 	lea    0x481f(%rip),%rsi        # 73b6 <_IO_stdin_used+0x3b6>
    2b97:	bf 01 00 00 00       	mov    $0x1,%edi
    2b9c:	31 c0                	xor    %eax,%eax
    2b9e:	e8 ad f8 ff ff       	call   2450 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ba3:	be 08 00 00 00       	mov    $0x8,%esi
    2ba8:	bf 01 00 00 00       	mov    $0x1,%edi
    2bad:	e8 ee f7 ff ff       	call   23a0 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2bb2:	be 08 00 00 00       	mov    $0x8,%esi
    2bb7:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2bbc:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2bc1:	e8 da f7 ff ff       	call   23a0 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    2bc6:	be 80 03 00 00       	mov    $0x380,%esi
    2bcb:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2bd0:	49 89 c4             	mov    %rax,%r12
            struct Data *data = calloc(3, sizeof(struct Data));
    2bd3:	e8 c8 f7 ff ff       	call   23a0 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    2bd8:	be 80 03 00 00       	mov    $0x380,%esi
    2bdd:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    2be2:	49 89 c6             	mov    %rax,%r14
            struct Data **stack = calloc(3, sizeof(struct Data));
    2be5:	e8 b6 f7 ff ff       	call   23a0 <calloc@plt>
            data[0].messages = messages;
    2bea:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
            mailboxes[b].lower = &data[0];
    2bef:	4c 89 75 00          	mov    %r14,0x0(%rbp)
            mailboxes[b].higher = &data[1];
    2bf3:	49 8d b6 80 03 00 00 	lea    0x380(%r14),%rsi
            data[0].messages_count = 0;
    2bfa:	66 0f 6f 25 9e 50 00 00 	movdqa 0x509e(%rip),%xmm4        # 7ca0 <_IO_stdin_used+0xca0>
            data[0].a = x;
    2c02:	45 89 ae 1c 03 00 00 	mov    %r13d,0x31c(%r14)
            data[0].kind = MAILBOX_LOWER;
    2c09:	41 c7 86 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r14)
            data[0].b = y;
    2c14:	45 89 be 20 03 00 00 	mov    %r15d,0x320(%r14)
            data[0].c = b;
    2c1b:	41 89 9e 24 03 00 00 	mov    %ebx,0x324(%r14)
            data[1].kind = MAILBOX_HIGHER;
    2c22:	41 c7 86 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r14)
            data[1].a = x;
    2c2d:	45 89 ae 9c 06 00 00 	mov    %r13d,0x69c(%r14)
            data[1].b = y;
    2c34:	45 89 be a0 06 00 00 	mov    %r15d,0x6a0(%r14)
            data[1].c = b;
    2c3b:	41 89 9e a4 06 00 00 	mov    %ebx,0x6a4(%r14)
            mailboxes[b].my_lower = &data[0];
    2c42:	4c 89 75 20          	mov    %r14,0x20(%rbp)
            mailboxes[b].higher = &data[1];
    2c46:	48 89 75 08          	mov    %rsi,0x8(%rbp)
            data[0].finished_reading = 1;
    2c4a:	41 c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r14)
            mailboxes[b].my_higher = &data[1];
    2c55:	48 89 75 28          	mov    %rsi,0x28(%rbp)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2c59:	c7 45 30 02 00 00 00 	movl   $0x2,0x30(%rbp)
            stack[0] = mailboxes[b].lower;
    2c60:	4c 89 30             	mov    %r14,(%rax)
            stack[1] = mailboxes[b].higher;
    2c63:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    2c67:	48 89 45 18          	mov    %rax,0x18(%rbp)
            data[0].available_sending = 1;
    2c6b:	41 c7 86 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r14)
            data[0].available_receiving = 0;
    2c76:	41 c7 86 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r14)
            data[0].messages = messages;
    2c81:	49 89 16             	mov    %rdx,(%r14)
            data[1].messages = messages2;
    2c84:	4d 89 a6 80 03 00 00 	mov    %r12,0x380(%r14)
            data[1].available_sending = 1;
    2c8b:	41 c7 86 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r14)
            data[1].available_receiving = 0;
    2c96:	41 c7 86 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r14)
            data[0].messages_count = 0;
    2ca1:	41 0f 29 a6 80 00 00 00 	movaps %xmm4,0x80(%r14)
            data[1].messages_count = 0;
    2ca9:	41 0f 29 a6 00 04 00 00 	movaps %xmm4,0x400(%r14)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2cb1:	83 c3 01             	add    $0x1,%ebx
    2cb4:	48 83 c5 38          	add    $0x38,%rbp
    2cb8:	83 fb 04             	cmp    $0x4,%ebx
    2cbb:	0f 85 bf fe ff ff    	jne    2b80 <main+0x590>
          char *message = malloc(sizeof(char) * 256);
    2cc1:	be 01 00 00 00       	mov    $0x1,%esi
    2cc6:	bf 00 01 00 00       	mov    $0x100,%edi
    2ccb:	44 89 fd             	mov    %r15d,%ebp
    2cce:	45 89 ec             	mov    %r13d,%r12d
    2cd1:	44 8b 7c 24 08       	mov    0x8(%rsp),%r15d
    2cd6:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    2cdb:	e8 c0 f6 ff ff       	call   23a0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2ce0:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    2ce5:	48 89 c3             	mov    %rax,%rbx
          struct Message *messaged = malloc(sizeof(struct Message));
    2ce8:	e8 23 f7 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2ced:	48 83 ec 08          	sub    $0x8,%rsp
    2cf1:	48 89 df             	mov    %rbx,%rdi
    2cf4:	41 89 e9             	mov    %ebp,%r9d
    2cf7:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2cfc:	45 89 e0             	mov    %r12d,%r8d
    2cff:	ba 00 01 00 00       	mov    $0x100,%edx
    2d04:	31 c0                	xor    %eax,%eax
    2d06:	41 57                	push   %r15
    2d08:	48 8d 0d d9 4a 00 00 	lea    0x4ad9(%rip),%rcx        # 77e8 <_IO_stdin_used+0x7e8>
    2d0f:	be 01 00 00 00       	mov    $0x1,%esi
    2d14:	e8 07 f8 ff ff       	call   2520 <__sprintf_chk@plt>
          messaged->message = message;
    2d19:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2d1e:	be 20 00 00 00       	mov    $0x20,%esi
    2d23:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->message = message;
    2d28:	49 89 1a             	mov    %rbx,(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2d2b:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
          messaged->task_index = y;
    2d30:	4d 89 6a 10          	mov    %r13,0x10(%r10)
          thread_data[x].tasks[y].group = k;
    2d34:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
          messaged->thread_index = thread_data[x].real_thread_index;
    2d39:	48 63 43 08          	movslq 0x8(%rbx),%rax
          thread_data[x].tasks[y].group = k;
    2d3d:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          messaged->group = k;
    2d41:	45 89 7a 18          	mov    %r15d,0x18(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2d45:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2d49:	8d 45 01             	lea    0x1(%rbp),%eax
          thread_data[x].tasks[y].group = k;
    2d4c:	49 01 d5             	add    %rdx,%r13
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2d4f:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].group = k;
    2d52:	45 89 bd 94 01 00 00 	mov    %r15d,0x194(%r13)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2d59:	41 c7 45 00 41 00 00 00 	movl   $0x41,0x0(%r13)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2d61:	41 89 85 90 01 00 00 	mov    %eax,0x190(%r13)
          thread_data[x].tasks[y].message = messaged;
    2d68:	4d 89 95 88 01 00 00 	mov    %r10,0x188(%r13)
          thread_data[x].tasks[y].sending = 1;
    2d6f:	41 c7 85 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r13)
          thread_data[x].tasks[y].snapshot_count = 99;
    2d7a:	49 c7 85 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%r13)
          thread_data[x].tasks[y].group = k;
    2d85:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2d8a:	e8 11 f6 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    2d8f:	49 c7 85 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%r13)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2d9a:	49 89 85 50 01 00 00 	mov    %rax,0x150(%r13)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2da1:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2da6:	48 8b 00             	mov    (%rax),%rax
    2da9:	8b 48 04             	mov    0x4(%rax),%ecx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2dac:	48 39 d8             	cmp    %rbx,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2daf:	49 89 85 28 01 00 00 	mov    %rax,0x128(%r13)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2db6:	41 89 8d 30 01 00 00 	mov    %ecx,0x130(%r13)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2dbd:	41 5b                	pop    %r11
    2dbf:	41 5e                	pop    %r14
    2dc1:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    2dc6:	0f 85 99 11 00 00    	jne    3f65 <main+0x1975>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2dcc:	66 0f 6f 05 dc 4e 00 00 	movdqa 0x4edc(%rip),%xmm0        # 7cb0 <_IO_stdin_used+0xcb0>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2dd4:	41 89 6d 04          	mov    %ebp,0x4(%r13)
          thread_data[x].tasks[y].available = 1;
    2dd8:	48 8b 1d e9 4e 00 00 	mov    0x4ee9(%rip),%rbx        # 7cc8 <_IO_stdin_used+0xcc8>
          thread_data[x].tasks[y].arrived = 0;
    2ddf:	41 c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r13)
          thread_data[x].tasks[y].worker_count = thread_count;
    2dea:	41 c7 85 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%r13)
          thread_data[x].tasks[y].available = 1;
    2df5:	49 89 9d 44 01 00 00 	mov    %rbx,0x144(%r13)
          thread_data[x].tasks[y].thread_count = 2;
    2dfc:	41 0f 11 85 34 01 00 00 	movups %xmm0,0x134(%r13)
          if (y == barrier_count - 1) {
    2e04:	83 fd 01             	cmp    $0x1,%ebp
    2e07:	0f 84 57 03 00 00    	je     3164 <main+0xb74>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2e0d:	85 ed                	test   %ebp,%ebp
    2e0f:	0f 84 37 03 00 00    	je     314c <main+0xb5c>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    2e15:	4c 8b 4c 24 40       	mov    0x40(%rsp),%r9
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2e1a:	bf 01 00 00 00       	mov    $0x1,%edi
    2e1f:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    2e24:	48 8d 05 15 36 00 00 	lea    0x3615(%rip),%rax        # 6440 <barriered_work>
    2e2b:	49 89 85 18 01 00 00 	mov    %rax,0x118(%r13)
    2e32:	44 8b b4 24 ac 00 00 00 	mov    0xac(%rsp),%r14d
        thread_data[x].buffers_count = buffers_per_thread;
    2e3a:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
               thread_data[x].tasks[y].run = barriered_work; 
    2e45:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
        thread_data[x].buffers_count = buffers_per_thread;
    2e4a:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2e4f:	e8 4c f5 ff ff       	call   23a0 <calloc@plt>
    2e54:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2e59:	48 8b 7c 24 50       	mov    0x50(%rsp),%rdi
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2e5e:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e63:	83 44 24 18 01       	addl   $0x1,0x18(%rsp)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2e68:	48 89 38             	mov    %rdi,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e6b:	48 83 c7 10          	add    $0x10,%rdi
    2e6f:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2e76:	66 0f 6f b4 24 80 00 00 00 	movdqa 0x80(%rsp),%xmm6
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2e7f:	49 89 41 88          	mov    %rax,-0x78(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2e83:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2e88:	83 44 24 58 01       	addl   $0x1,0x58(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2e8d:	48 8b 00             	mov    (%rax),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e90:	48 89 7c 24 50       	mov    %rdi,0x50(%rsp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    2e95:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2e9f:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2ea6:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    2eb0:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2eba:	41 8b 81 3c ff ff ff 	mov    -0xc4(%r9),%eax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2ec1:	0f 11 b2 18 05 00 00 	movups %xmm6,0x518(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2ec8:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2ece:	8b 44 24 18          	mov    0x18(%rsp),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2ed2:	c7 82 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
    2edc:	48 89 9a 44 05 00 00 	mov    %rbx,0x544(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2ee3:	41 39 c6             	cmp    %eax,%r14d
    2ee6:	0f 85 ed f9 ff ff    	jne    28d9 <main+0x2e9>
    2eec:	4c 8b a4 24 b0 00 00 00 	mov    0xb0(%rsp),%r12
    2ef4:	48 8b b4 24 a0 00 00 00 	mov    0xa0(%rsp),%rsi
    2efc:	44 89 f2             	mov    %r14d,%edx
    2eff:	48 8b 9c 24 b8 00 00 00 	mov    0xb8(%rsp),%rbx
  for (int k = 0 ; k < group_count ; k++) {
    2f07:	83 c2 02             	add    $0x2,%edx
    2f0a:	48 83 c6 18          	add    $0x18,%rsi
    2f0e:	49 81 c4 90 01 00 00 	add    $0x190,%r12
    2f15:	45 85 ff             	test   %r15d,%r15d
    2f18:	0f 85 88 02 00 00    	jne    31a6 <main+0xbb6>
    2f1e:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    2f24:	e9 79 f9 ff ff       	jmp    28a2 <main+0x2b2>
    2f29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            int group_of = b / threads_per_group;
    2f30:	45 89 ee             	mov    %r13d,%r14d
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2f33:	31 c0                	xor    %eax,%eax
    2f35:	44 89 ea             	mov    %r13d,%edx
    2f38:	bf 01 00 00 00       	mov    $0x1,%edi
    2f3d:	41 d1 fe             	sar    %r14d
    2f40:	48 8d 35 5f 44 00 00 	lea    0x445f(%rip),%rsi        # 73a6 <_IO_stdin_used+0x3a6>
    2f47:	44 89 f1             	mov    %r14d,%ecx
    2f4a:	e8 01 f5 ff ff       	call   2450 <__printf_chk@plt>
            if (k == group_of) {
    2f4f:	45 39 f7             	cmp    %r14d,%r15d
    2f52:	0f 84 04 01 00 00    	je     305c <main+0xa6c>
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2f58:	41 83 c5 01          	add    $0x1,%r13d
    2f5c:	48 83 c3 38          	add    $0x38,%rbx
    2f60:	41 83 fd 04          	cmp    $0x4,%r13d
    2f64:	75 ca                	jne    2f30 <main+0x940>
    2f66:	e9 f6 fb ff ff       	jmp    2b61 <main+0x571>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f6b:	be 08 00 00 00       	mov    $0x8,%esi
    2f70:	bf 01 00 00 00       	mov    $0x1,%edi
    2f75:	e8 26 f4 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f7a:	be 08 00 00 00       	mov    $0x8,%esi
    2f7f:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f84:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f89:	e8 12 f4 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2f8e:	be 80 03 00 00       	mov    $0x380,%esi
    2f93:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f98:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2f9d:	e8 fe f3 ff ff       	call   23a0 <calloc@plt>
              mailboxes[b].kind = MAILBOX_FRIEND;
    2fa2:	c7 43 30 01 00 00 00 	movl   $0x1,0x30(%rbx)
    2fa9:	44 89 ea             	mov    %r13d,%edx
    2fac:	48 8d 35 0d 48 00 00 	lea    0x480d(%rip),%rsi        # 77c0 <_IO_stdin_used+0x7c0>
              data[0].a = x;
    2fb3:	44 89 a0 1c 03 00 00 	mov    %r12d,0x31c(%rax)
              struct Data *data = calloc(3, sizeof(struct Data));
    2fba:	49 89 c0             	mov    %rax,%r8
    2fbd:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].kind = MAILBOX_LOWER;
    2fc2:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].b = y;
    2fcc:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].c = b;
    2fd2:	44 89 a8 24 03 00 00 	mov    %r13d,0x324(%rax)
              data[1].kind = MAILBOX_HIGHER;
    2fd9:	c7 80 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%rax)
              data[1].a = x;
    2fe3:	44 89 a0 9c 06 00 00 	mov    %r12d,0x69c(%rax)
              data[1].b = y;
    2fea:	89 a8 a0 06 00 00    	mov    %ebp,0x6a0(%rax)
              data[1].c = b;
    2ff0:	44 89 a8 a4 06 00 00 	mov    %r13d,0x6a4(%rax)
              mailboxes[b].lower = &data[0];
    2ff7:	48 89 03             	mov    %rax,(%rbx)
              mailboxes[b].higher = &data[1];
    2ffa:	48 8d 80 80 03 00 00 	lea    0x380(%rax),%rax
    3001:	48 89 43 08          	mov    %rax,0x8(%rbx)
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    3005:	8b 44 24 18          	mov    0x18(%rsp),%eax
              data[0].finished_reading = 1;
    3009:	41 c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r8)
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    3014:	8d 48 fe             	lea    -0x2(%rax),%ecx
    3017:	31 c0                	xor    %eax,%eax
              data[0].finished_reading = 1;
    3019:	4c 89 44 24 30       	mov    %r8,0x30(%rsp)
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    301e:	89 4b 34             	mov    %ecx,0x34(%rbx)
    3021:	e8 2a f4 ff ff       	call   2450 <__printf_chk@plt>
              data[0].messages = messages;
    3026:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
    302b:	4c 8b 54 24 68       	mov    0x68(%rsp),%r10
              data[0].messages_count = 0;
    3030:	66 0f 6f 3d 68 4c 00 00 	movdqa 0x4c68(%rip),%xmm7        # 7ca0 <_IO_stdin_used+0xca0>
              data[1].messages = messages2;
    3038:	4c 8b 4c 24 60       	mov    0x60(%rsp),%r9
              data[0].messages = messages;
    303d:	4d 89 10             	mov    %r10,(%r8)
              data[1].messages = messages2;
    3040:	4d 89 88 80 03 00 00 	mov    %r9,0x380(%r8)
              data[0].messages_count = 0;
    3047:	41 0f 29 b8 80 00 00 00 	movaps %xmm7,0x80(%r8)
              data[1].messages_count = 0;
    304f:	41 0f 29 b8 00 04 00 00 	movaps %xmm7,0x400(%r8)
    3057:	e9 f7 fa ff ff       	jmp    2b53 <main+0x563>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    305c:	be 08 00 00 00       	mov    $0x8,%esi
    3061:	bf 01 00 00 00       	mov    $0x1,%edi
    3066:	e8 35 f3 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    306b:	be 08 00 00 00       	mov    $0x8,%esi
    3070:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3075:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    307a:	e8 21 f3 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    307f:	be 80 03 00 00       	mov    $0x380,%esi
    3084:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3089:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    308e:	e8 0d f3 ff ff       	call   23a0 <calloc@plt>
              mailboxes[b].kind = MAILBOX_FRIEND;
    3093:	c7 43 30 01 00 00 00 	movl   $0x1,0x30(%rbx)
    309a:	44 89 ea             	mov    %r13d,%edx
    309d:	48 8d 35 1c 47 00 00 	lea    0x471c(%rip),%rsi        # 77c0 <_IO_stdin_used+0x7c0>
              data[0].a = x;
    30a4:	44 89 a0 1c 03 00 00 	mov    %r12d,0x31c(%rax)
              struct Data *data = calloc(3, sizeof(struct Data));
    30ab:	49 89 c0             	mov    %rax,%r8
    30ae:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].kind = MAILBOX_LOWER;
    30b3:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].b = y;
    30bd:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].c = b;
    30c3:	44 89 a8 24 03 00 00 	mov    %r13d,0x324(%rax)
              data[1].kind = MAILBOX_HIGHER;
    30ca:	c7 80 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%rax)
              data[1].a = x;
    30d4:	44 89 a0 9c 06 00 00 	mov    %r12d,0x69c(%rax)
              data[1].b = y;
    30db:	89 a8 a0 06 00 00    	mov    %ebp,0x6a0(%rax)
              data[1].c = b;
    30e1:	44 89 a8 a4 06 00 00 	mov    %r13d,0x6a4(%rax)
              mailboxes[b].lower = &data[0];
    30e8:	48 89 03             	mov    %rax,(%rbx)
              mailboxes[b].higher = &data[1];
    30eb:	48 8d 80 80 03 00 00 	lea    0x380(%rax),%rax
    30f2:	48 89 43 08          	mov    %rax,0x8(%rbx)
              data[0].finished_reading = 1;
    30f6:	8b 44 24 18          	mov    0x18(%rsp),%eax
    30fa:	41 c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r8)
    3105:	89 43 34             	mov    %eax,0x34(%rbx)
    3108:	89 c1                	mov    %eax,%ecx
    310a:	31 c0                	xor    %eax,%eax
    310c:	4c 89 44 24 30       	mov    %r8,0x30(%rsp)
    3111:	e8 3a f3 ff ff       	call   2450 <__printf_chk@plt>
              data[0].messages = messages;
    3116:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
    311b:	4c 8b 54 24 68       	mov    0x68(%rsp),%r10
              data[0].messages_count = 0;
    3120:	66 0f 6f 35 78 4b 00 00 	movdqa 0x4b78(%rip),%xmm6        # 7ca0 <_IO_stdin_used+0xca0>
              data[1].messages = messages2;
    3128:	4c 8b 4c 24 60       	mov    0x60(%rsp),%r9
              data[0].messages = messages;
    312d:	4d 89 10             	mov    %r10,(%r8)
              data[1].messages = messages2;
    3130:	4d 89 88 80 03 00 00 	mov    %r9,0x380(%r8)
              data[0].messages_count = 0;
    3137:	41 0f 29 b0 80 00 00 00 	movaps %xmm6,0x80(%r8)
              data[1].messages_count = 0;
    313f:	41 0f 29 b0 00 04 00 00 	movaps %xmm6,0x400(%r8)
    3147:	e9 0c fe ff ff       	jmp    2f58 <main+0x968>
    314c:	48 8d 05 bd 38 00 00 	lea    0x38bd(%rip),%rax        # 6a10 <barriered_work_ingest_andwork>
    3153:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    3158:	49 89 85 18 01 00 00 	mov    %rax,0x118(%r13)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    315f:	e9 6e f9 ff ff       	jmp    2ad2 <main+0x4e2>
    3164:	48 8d 05 d5 32 00 00 	lea    0x32d5(%rip),%rax        # 6440 <barriered_work>
    316b:	bd 02 00 00 00       	mov    $0x2,%ebp
    3170:	eb e6                	jmp    3158 <main+0xb68>
        other = (x + 1) % total_threads;
    3172:	8b 44 24 18          	mov    0x18(%rsp),%eax
        my_thread_data[1] = &thread_data[other]; 
    3176:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    317b:	48 89 6c 24 28       	mov    %rbp,0x28(%rsp)
    3180:	45 31 c0             	xor    %r8d,%r8d
        other = (x + 1) % total_threads;
    3183:	89 c3                	mov    %eax,%ebx
        my_thread_data[1] = &thread_data[other]; 
    3185:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3189:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    318d:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
        my_thread_data[0] = &thread_data[x]; 
    3191:	4c 89 c8             	mov    %r9,%rax
    3194:	e9 c4 f7 ff ff       	jmp    295d <main+0x36d>
            CPU_SET(j, sendercpu);
    3199:	49 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%r13)
          for (int j = 0 ; j < cores ; j++) {
    31a1:	e9 52 f8 ff ff       	jmp    29f8 <main+0x408>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(200, sizeof(struct Data*)); 
    31a6:	be 08 00 00 00       	mov    $0x8,%esi
    31ab:	bf c8 00 00 00       	mov    $0xc8,%edi
    31b0:	45 89 fe             	mov    %r15d,%r14d
  int datas_size = 0; 
    31b3:	31 ed                	xor    %ebp,%ebp
  struct Data ** cdatas = calloc(200, sizeof(struct Data*)); 
    31b5:	e8 e6 f1 ff ff       	call   23a0 <calloc@plt>
    31ba:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    31bf:	49 89 c5             	mov    %rax,%r13
    31c2:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    31c4:	49 89 d1             	mov    %rdx,%r9
    31c7:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    31c9:	45 8b 51 40          	mov    0x40(%r9),%r10d
    31cd:	45 85 d2             	test   %r10d,%r10d
    31d0:	7e 73                	jle    3245 <main+0xc55>
    31d2:	49 8b 79 38          	mov    0x38(%r9),%rdi
    31d6:	4d 63 c2             	movslq %r10d,%r8
    31d9:	48 63 cd             	movslq %ebp,%rcx
    31dc:	49 c1 e0 09          	shl    $0x9,%r8
    31e0:	49 8d 74 cd 00       	lea    0x0(%r13,%rcx,8),%rsi
    31e5:	49 01 f8             	add    %rdi,%r8
    31e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    31f0:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    31f7:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    31fe:	48 83 c6 40          	add    $0x40,%rsi
    3202:	f3 0f 7e 51 38       	movq   0x38(%rcx),%xmm2
    3207:	f3 0f 7e 49 70       	movq   0x70(%rcx),%xmm1
    320c:	f3 0f 7e 81 a8 00 00 00 	movq   0xa8(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3214:	f3 0f 7e 19          	movq   (%rcx),%xmm3
    3218:	0f 16 51 40          	movhps 0x40(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    321c:	0f 16 49 78          	movhps 0x78(%rcx),%xmm1
    3220:	0f 16 81 b0 00 00 00 	movhps 0xb0(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3227:	0f 16 59 08          	movhps 0x8(%rcx),%xmm3
    322b:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    322f:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3233:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3237:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    323b:	49 39 f8             	cmp    %rdi,%r8
    323e:	75 b0                	jne    31f0 <main+0xc00>
    3240:	42 8d 6c d5 00       	lea    0x0(%rbp,%r10,8),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    3245:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
    324c:	85 db                	test   %ebx,%ebx
    324e:	75 08                	jne    3258 <main+0xc68>
    3250:	44 89 f3             	mov    %r14d,%ebx
    3253:	e9 71 ff ff ff       	jmp    31c9 <main+0xbd9>
  for (int k = 0 ; k < group_count ; k++) {
    3258:	83 c0 02             	add    $0x2,%eax
    325b:	48 81 c2 90 01 00 00 	add    $0x190,%rdx
    3262:	83 f8 04             	cmp    $0x4,%eax
    3265:	0f 85 59 ff ff ff    	jne    31c4 <main+0xbd4>
    326b:	48 8d 3d 62 41 00 00 	lea    0x4162(%rip),%rdi        # 73d4 <_IO_stdin_used+0x3d4>
    3272:	e8 79 f0 ff ff       	call   22f0 <puts@plt>
        }
      }
    }
  }
  printf("Mailboxes list mlist\n");
  for (int x = 0 ; x < datas_size; x++) {
    3277:	85 ed                	test   %ebp,%ebp
    3279:	7e 45                	jle    32c0 <main+0xcd0>
    327b:	48 63 ed             	movslq %ebp,%rbp
    327e:	4d 8d 64 ed 00       	lea    0x0(%r13,%rbp,8),%r12
    3283:	48 8d 2d 77 41 00 00 	lea    0x4177(%rip),%rbp        # 7401 <_IO_stdin_used+0x401>
    printf("mailbox %d %d %d %d\n", cdatas[x]->kind, cdatas[x]->a, cdatas[x]->b, cdatas[x]->c);
    328a:	49 8b 45 00          	mov    0x0(%r13),%rax
    328e:	48 89 ee             	mov    %rbp,%rsi
    3291:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < datas_size; x++) {
    3296:	49 83 c5 08          	add    $0x8,%r13
    329a:	8b 88 1c 03 00 00    	mov    0x31c(%rax),%ecx
    32a0:	8b 90 18 03 00 00    	mov    0x318(%rax),%edx
    32a6:	44 8b 88 24 03 00 00 	mov    0x324(%rax),%r9d
    32ad:	44 8b 80 20 03 00 00 	mov    0x320(%rax),%r8d
    32b4:	31 c0                	xor    %eax,%eax
    32b6:	e8 95 f1 ff ff       	call   2450 <__printf_chk@plt>
    32bb:	4d 39 ec             	cmp    %r13,%r12
    32be:	75 ca                	jne    328a <main+0xc9a>
    32c0:	48 8d 3d 22 41 00 00 	lea    0x4122(%rip),%rdi        # 73e9 <_IO_stdin_used+0x3e9>
  } 

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    32c7:	45 31 e4             	xor    %r12d,%r12d
    32ca:	4c 8d 35 6c 41 00 00 	lea    0x416c(%rip),%r14        # 743d <_IO_stdin_used+0x43d>
    32d1:	e8 1a f0 ff ff       	call   22f0 <puts@plt>
    32d6:	4c 8b 7c 24 38       	mov    0x38(%rsp),%r15
    32db:	44 89 e2             	mov    %r12d,%edx
    32de:	48 8d 35 31 41 00 00 	lea    0x4131(%rip),%rsi        # 7416 <_IO_stdin_used+0x416>
    32e5:	31 c0                	xor    %eax,%eax
    32e7:	89 54 24 08          	mov    %edx,0x8(%rsp)
    32eb:	4d 89 fc             	mov    %r15,%r12
    32ee:	bf 01 00 00 00       	mov    $0x1,%edi
    32f3:	e8 58 f1 ff ff       	call   2450 <__printf_chk@plt>
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    32f8:	8b 54 24 08          	mov    0x8(%rsp),%edx
    32fc:	4c 89 7c 24 18       	mov    %r15,0x18(%rsp)
    3301:	41 89 df             	mov    %ebx,%r15d
    3304:	44 8d 2c 12          	lea    (%rdx,%rdx,1),%r13d
    3308:	31 d2                	xor    %edx,%edx
    330a:	44 89 6c 24 10       	mov    %r13d,0x10(%rsp)
      int x = (k * threads_per_group) + d;
    330f:	8b 44 24 10          	mov    0x10(%rsp),%eax
    3313:	bf 01 00 00 00       	mov    $0x1,%edi
    3318:	89 54 24 28          	mov    %edx,0x28(%rsp)
    331c:	45 31 ed             	xor    %r13d,%r13d
    331f:	48 8d 35 fa 40 00 00 	lea    0x40fa(%rip),%rsi        # 7420 <_IO_stdin_used+0x420>
    3326:	8d 0c 02             	lea    (%rdx,%rax,1),%ecx
    3329:	31 c0                	xor    %eax,%eax
    332b:	e8 20 f1 ff ff       	call   2450 <__printf_chk@plt>
    3330:	44 89 7c 24 20       	mov    %r15d,0x20(%rsp)
    3335:	44 89 ea             	mov    %r13d,%edx
    3338:	48 8d 35 f3 40 00 00 	lea    0x40f3(%rip),%rsi        # 7432 <_IO_stdin_used+0x432>
    333f:	31 c0                	xor    %eax,%eax
    3341:	4c 89 ed             	mov    %r13,%rbp
    3344:	bf 01 00 00 00       	mov    $0x1,%edi
    3349:	48 c1 e5 09          	shl    $0x9,%rbp
    334d:	45 31 ff             	xor    %r15d,%r15d
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3350:	31 db                	xor    %ebx,%ebx
    3352:	e8 f9 f0 ff ff       	call   2450 <__printf_chk@plt>
          char * mailbox_kind = calloc(100, sizeof(char));
    3357:	be 01 00 00 00       	mov    $0x1,%esi
    335c:	bf 64 00 00 00       	mov    $0x64,%edi
    3361:	e8 3a f0 ff ff       	call   23a0 <calloc@plt>
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3366:	49 8b 74 24 38       	mov    0x38(%r12),%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
    336b:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    336e:	48 8b 84 2e 70 01 00 00 	mov    0x170(%rsi,%rbp,1),%rax
    3376:	4c 01 f8             	add    %r15,%rax
    3379:	8b 50 30             	mov    0x30(%rax),%edx
    337c:	83 fa 02             	cmp    $0x2,%edx
    337f:	74 4c                	je     33cd <main+0xddd>
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    3381:	83 fa 01             	cmp    $0x1,%edx
    3384:	74 61                	je     33e7 <main+0xdf7>
    3386:	44 8b 40 34          	mov    0x34(%rax),%r8d
    338a:	89 da                	mov    %ebx,%edx
    338c:	4c 89 f6             	mov    %r14,%rsi
    338f:	bf 01 00 00 00       	mov    $0x1,%edi
    3394:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3396:	83 c3 01             	add    $0x1,%ebx
    3399:	49 83 c7 38          	add    $0x38,%r15
    339d:	e8 ae f0 ff ff       	call   2450 <__printf_chk@plt>
    33a2:	83 fb 04             	cmp    $0x4,%ebx
    33a5:	75 b0                	jne    3357 <main+0xd67>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    33a7:	49 83 c5 01          	add    $0x1,%r13
    33ab:	49 83 fd 03          	cmp    $0x3,%r13
    33af:	75 84                	jne    3335 <main+0xd45>
    for (int d = 0 ; d < threads_per_group ; d++) {
    33b1:	8b 54 24 28          	mov    0x28(%rsp),%edx
    33b5:	44 8b 7c 24 20       	mov    0x20(%rsp),%r15d
    33ba:	49 81 c4 c8 00 00 00 	add    $0xc8,%r12
    33c1:	85 d2                	test   %edx,%edx
    33c3:	75 3c                	jne    3401 <main+0xe11>
    33c5:	44 89 fa             	mov    %r15d,%edx
    33c8:	e9 42 ff ff ff       	jmp    330f <main+0xd1f>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    33cd:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    33d7:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    33da:	48 8b 84 2e 70 01 00 00 	mov    0x170(%rsi,%rbp,1),%rax
    33e2:	4c 01 f8             	add    %r15,%rax
    33e5:	eb 9f                	jmp    3386 <main+0xd96>
    33e7:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    33ed:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    33f4:	48 8b 84 2e 70 01 00 00 	mov    0x170(%rsi,%rbp,1),%rax
    33fc:	4c 01 f8             	add    %r15,%rax
    33ff:	eb 85                	jmp    3386 <main+0xd96>
  for (int k = 0 ; k < group_count ; k++) {
    3401:	44 89 fb             	mov    %r15d,%ebx
    3404:	89 d5                	mov    %edx,%ebp
    3406:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
    340b:	8b 54 24 08          	mov    0x8(%rsp),%edx
    340f:	49 81 c7 90 01 00 00 	add    $0x190,%r15
    3416:	85 d2                	test   %edx,%edx
    3418:	75 07                	jne    3421 <main+0xe31>
    341a:	89 ea                	mov    %ebp,%edx
    341c:	e9 bd fe ff ff       	jmp    32de <main+0xcee>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3421:	41 89 d4             	mov    %edx,%r12d
    3424:	48 8d 35 2d 40 00 00 	lea    0x402d(%rip),%rsi        # 7458 <_IO_stdin_used+0x458>
    342b:	ba 05 00 00 00       	mov    $0x5,%edx
    3430:	31 c0                	xor    %eax,%eax
    3432:	bf 01 00 00 00       	mov    $0x1,%edi
    3437:	e8 14 f0 ff ff       	call   2450 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    343c:	be 08 00 00 00       	mov    $0x8,%esi
    3441:	bf 02 00 00 00       	mov    $0x2,%edi
    3446:	e8 55 ef ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    344b:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3450:	be 38 00 00 00       	mov    $0x38,%esi
    my_thread_data[0] = &thread_data[x]; 
    3455:	4c 8d bf e8 03 00 00 	lea    0x3e8(%rdi),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    345c:	48 89 78 08          	mov    %rdi,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3460:	4c 8d b7 c8 00 00 00 	lea    0xc8(%rdi),%r14
    thread_data[x].threads = my_thread_data;
    3467:	48 89 87 00 04 00 00 	mov    %rax,0x400(%rdi)
    my_thread_data[0] = &thread_data[x]; 
    346e:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3471:	48 8b 47 38          	mov    0x38(%rdi),%rax
    thread_data[x].thread_count = 2;
    3475:	c7 87 10 04 00 00 02 00 00 00 	movl   $0x2,0x410(%rdi)
    thread_data[x].thread_index = 0;
    347f:	c7 87 ec 03 00 00 00 00 00 00 	movl   $0x0,0x3ec(%rdi)
    thread_data[x].task_count = total_barrier_count;
    3489:	c7 87 28 04 00 00 03 00 00 00 	movl   $0x3,0x428(%rdi)
    thread_data[n].tasks[0].scheduled = 1;
    3493:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    349d:	48 8b 87 00 01 00 00 	mov    0x100(%rdi),%rax
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34a4:	bf 08 00 00 00       	mov    $0x8,%edi
    thread_data[n].tasks[0].scheduled = 1;
    34a9:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34b3:	e8 e8 ee ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34b8:	be 38 00 00 00       	mov    $0x38,%esi
    34bd:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34c2:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34c5:	e8 d6 ee ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34ca:	be 38 00 00 00       	mov    $0x38,%esi
    34cf:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34d4:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34d7:	e8 c4 ee ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34dc:	be 38 00 00 00       	mov    $0x38,%esi
    34e1:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34e6:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34eb:	e8 b0 ee ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    34f0:	be 08 00 00 00       	mov    $0x8,%esi
    34f5:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34fa:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    34ff:	e8 9c ee ff ff       	call   23a0 <calloc@plt>


  int timer_threadi = group_count * thread_count;
  thread_data[timer_threadi].type = TIMER;
    3504:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3509:	be 08 00 00 00       	mov    $0x8,%esi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    350e:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    3511:	48 8b 05 b8 47 00 00 	mov    0x47b8(%rip),%rax        # 7cd0 <_IO_stdin_used+0xcd0>
  thread_data[timer_threadi].type = TIMER;
    3518:	c7 87 2c 03 00 00 00 00 00 00 	movl   $0x0,0x32c(%rdi)
  thread_data[timer_threadi].task_count = total_barrier_count;
    3522:	48 89 87 60 03 00 00 	mov    %rax,0x360(%rdi)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3529:	bf 08 00 00 00       	mov    $0x8,%edi
    352e:	e8 6d ee ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    3533:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3538:	4c 89 78 28          	mov    %r15,0x28(%rax)
    353c:	48 8d 97 90 01 00 00 	lea    0x190(%rdi),%rdx
    3543:	48 8d 8f 20 03 00 00 	lea    0x320(%rdi),%rcx
    354a:	48 89 38             	mov    %rdi,(%rax)
    354d:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3551:	48 8d 97 58 02 00 00 	lea    0x258(%rdi),%rdx
    3558:	48 8d b7 b0 04 00 00 	lea    0x4b0(%rdi),%rsi
    355f:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3563:	48 8d 97 78 05 00 00 	lea    0x578(%rdi),%rdx
    356a:	48 89 48 20          	mov    %rcx,0x20(%rax)
    356e:	48 89 70 30          	mov    %rsi,0x30(%rax)
    3572:	48 89 50 38          	mov    %rdx,0x38(%rax)
    3576:	ba 04 00 00 00       	mov    $0x4,%edx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    357b:	48 89 87 38 03 00 00 	mov    %rax,0x338(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    3582:	4c 89 70 08          	mov    %r14,0x8(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3586:	48 8b 05 4b 47 00 00 	mov    0x474b(%rip),%rax        # 7cd8 <_IO_stdin_used+0xcd8>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    358d:	c7 87 50 03 00 00 04 00 00 00 	movl   $0x4,0x350(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3597:	48 89 87 48 03 00 00 	mov    %rax,0x348(%rdi)
    359e:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    35a0:	c7 87 24 03 00 00 00 00 00 00 	movl   $0x0,0x324(%rdi)
    35aa:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    35af:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    35b4:	48 8d 35 ac 3e 00 00 	lea    0x3eac(%rip),%rsi        # 7467 <_IO_stdin_used+0x467>
    35bb:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    35c0:	e8 8b ee ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    35c5:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    35ca:	48 8d b5 e0 00 00 00 	lea    0xe0(%rbp),%rsi
  for (int k = 0 ; k < group_count ; k++) {
    35d1:	31 ed                	xor    %ebp,%ebp
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    35d3:	48 8d 15 56 0c 00 00 	lea    0xc56(%rip),%rdx        # 4230 <timer_thread>
    35da:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
    35de:	e8 8d ee ff ff       	call   2470 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    35e3:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    35e8:	44 89 e6             	mov    %r12d,%esi
    35eb:	48 89 d9             	mov    %rbx,%rcx
    35ee:	4c 89 74 24 30       	mov    %r14,0x30(%rsp)
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    35f3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    35f8:	4c 89 e8             	mov    %r13,%rax
    35fb:	41 89 ec             	mov    %ebp,%r12d
    35fe:	41 b9 02 00 00 00    	mov    $0x2,%r9d
    3604:	4c 89 7c 24 20       	mov    %r15,0x20(%rsp)
    3609:	45 89 cf             	mov    %r9d,%r15d
    for (int d = 0 ; d < threads_per_group ; d++) {
    360c:	89 74 24 40          	mov    %esi,0x40(%rsp)
    3610:	43 8d 2c 24          	lea    (%r12,%r12,1),%ebp
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3614:	49 89 c6             	mov    %rax,%r14
    3617:	48 89 cb             	mov    %rcx,%rbx
    361a:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    361f:	49 89 d5             	mov    %rdx,%r13
    3622:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    3627:	48 89 54 24 58       	mov    %rdx,0x58(%rsp)
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    362c:	41 c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%r13)
    3634:	89 ea                	mov    %ebp,%edx
    3636:	44 89 e1             	mov    %r12d,%ecx
    3639:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    363b:	41 c7 45 44 01 00 00 00 	movl   $0x1,0x44(%r13)
    3643:	48 8d 35 ce 41 00 00 	lea    0x41ce(%rip),%rsi        # 7818 <_IO_stdin_used+0x818>
    364a:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    364f:	83 c5 01             	add    $0x1,%ebp
    3652:	e8 f9 ed ff ff       	call   2450 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3657:	4c 89 e9             	mov    %r13,%rcx
    365a:	4c 89 f6             	mov    %r14,%rsi
    365d:	48 89 df             	mov    %rbx,%rdi
    3660:	48 8d 15 29 29 00 00 	lea    0x2929(%rip),%rdx        # 5f90 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3667:	49 81 c5 c8 00 00 00 	add    $0xc8,%r13
    366e:	48 83 c3 08          	add    $0x8,%rbx
    3672:	49 83 c6 38          	add    $0x38,%r14
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3676:	e8 f5 ed ff ff       	call   2470 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    367b:	49 8b 55 e8          	mov    -0x18(%r13),%rdx
    367f:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    3683:	be 08 00 00 00       	mov    $0x8,%esi
    3688:	e8 53 ec ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    368d:	41 39 ef             	cmp    %ebp,%r15d
    3690:	75 9a                	jne    362c <main+0x103c>
  for (int k = 0 ; k < group_count ; k++) {
    3692:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3697:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    369c:	41 83 c7 02          	add    $0x2,%r15d
    36a0:	48 8b 54 24 58       	mov    0x58(%rsp),%rdx
    36a5:	8b 74 24 40          	mov    0x40(%rsp),%esi
    36a9:	48 83 c1 10          	add    $0x10,%rcx
    36ad:	48 83 c0 70          	add    $0x70,%rax
    36b1:	48 81 c2 90 01 00 00 	add    $0x190,%rdx
    36b8:	45 85 e4             	test   %r12d,%r12d
    36bb:	75 08                	jne    36c5 <main+0x10d5>
    36bd:	41 89 f4             	mov    %esi,%r12d
    36c0:	e9 47 ff ff ff       	jmp    360c <main+0x101c>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    36c5:	48 8b 05 14 46 00 00 	mov    0x4614(%rip),%rax        # 7ce0 <_IO_stdin_used+0xce0>
    thread_data[x].type = IO;
    36cc:	44 89 e5             	mov    %r12d,%ebp
    36cf:	4c 8b 64 24 38       	mov    0x38(%rsp),%r12

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    36d4:	be d8 00 00 00       	mov    $0xd8,%esi
    36d9:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    36de:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
    36e3:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    thread_data[x].task_count = 0;
    36e8:	49 89 84 24 28 04 00 00 	mov    %rax,0x428(%r12)
    thread_data[x].type = IO;
    36f0:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    36f5:	41 c7 84 24 f4 03 00 00 02 00 00 00 	movl   $0x2,0x3f4(%r12)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3701:	e8 9a ec ff ff       	call   23a0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3706:	be 00 08 00 00       	mov    $0x800,%esi
    370b:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    370d:	49 89 84 24 40 04 00 00 	mov    %rax,0x440(%r12)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3715:	e8 96 ed ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    371a:	be 08 00 00 00       	mov    $0x8,%esi
    371f:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3724:	41 89 84 24 48 04 00 00 	mov    %eax,0x448(%r12)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    372c:	e8 6f ec ff ff       	call   23a0 <calloc@plt>
    3731:	ba 05 00 00 00       	mov    $0x5,%edx
    3736:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    373b:	41 c7 84 24 10 04 00 00 02 00 00 00 	movl   $0x2,0x410(%r12)
      my_thread_data[n] = &thread_data[n]; 
    3747:	4c 89 20             	mov    %r12,(%rax)
    374a:	48 8d 35 34 3d 00 00 	lea    0x3d34(%rip),%rsi        # 7485 <_IO_stdin_used+0x485>
    thread_data[x].threads = my_thread_data;
    3751:	49 89 84 24 00 04 00 00 	mov    %rax,0x400(%r12)
      my_thread_data[n] = &thread_data[n]; 
    3759:	4c 89 70 08          	mov    %r14,0x8(%rax)
    375d:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    375f:	41 c7 84 24 ec 03 00 00 05 00 00 00 	movl   $0x5,0x3ec(%r12)
    376b:	4c 8d 63 30          	lea    0x30(%rbx),%r12
    376f:	e8 dc ec ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3774:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3779:	4c 89 f9             	mov    %r15,%rcx
    377c:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
    3780:	48 8d 15 19 20 00 00 	lea    0x2019(%rip),%rdx        # 57a0 <io_thread>
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3787:	41 bf 06 00 00 00    	mov    $0x6,%r15d
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    378d:	48 81 c6 18 01 00 00 	add    $0x118,%rsi
    3794:	e8 d7 ec ff ff       	call   2470 <pthread_create@plt>
    3799:	ba 06 00 00 00       	mov    $0x6,%edx
    379e:	48 8d 35 f7 3c 00 00 	lea    0x3cf7(%rip),%rsi        # 749c <_IO_stdin_used+0x49c>
    37a5:	31 c0                	xor    %eax,%eax
    37a7:	bf 01 00 00 00       	mov    $0x1,%edi
    37ac:	e8 9f ec ff ff       	call   2450 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    37b1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    37b6:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    37bb:	48 05 50 01 00 00    	add    $0x150,%rax
    37c1:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    37c6:	44 89 fa             	mov    %r15d,%edx
    37c9:	48 8d 35 e2 3c 00 00 	lea    0x3ce2(%rip),%rsi        # 74b2 <_IO_stdin_used+0x4b2>
    37d0:	bf 01 00 00 00       	mov    $0x1,%edi
    37d5:	31 c0                	xor    %eax,%eax
    37d7:	e8 74 ec ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    37dc:	be 08 00 00 00       	mov    $0x8,%esi
    37e1:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    37e6:	48 8b 05 f3 44 00 00 	mov    0x44f3(%rip),%rax        # 7ce0 <_IO_stdin_used+0xce0>
    thread_data[x].type = EXTERNAL;
    37ed:	41 c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%r13)
    thread_data[x].task_count = 0;
    37f5:	49 89 45 40          	mov    %rax,0x40(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    37f9:	e8 a2 eb ff ff       	call   23a0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    37fe:	48 8b 7c 24 78       	mov    0x78(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3803:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3808:	41 c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3813:	49 89 45 50          	mov    %rax,0x50(%r13)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3817:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    381a:	bf 02 00 00 00       	mov    $0x2,%edi
    381f:	e8 7c eb ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3824:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3829:	4c 89 e9             	mov    %r13,%rcx
    382c:	4c 89 e7             	mov    %r12,%rdi
    thread_data[x].threads = my_thread_data;
    382f:	49 89 45 18          	mov    %rax,0x18(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3833:	48 8d 15 e6 08 00 00 	lea    0x8e6(%rip),%rdx        # 4120 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    383a:	49 83 c4 08          	add    $0x8,%r12
    383e:	49 81 c5 c8 00 00 00 	add    $0xc8,%r13
      my_thread_data[n] = &thread_data[n]; 
    3845:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3848:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    384d:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3851:	48 8b 05 68 44 00 00 	mov    0x4468(%rip),%rax        # 7cc0 <_IO_stdin_used+0xcc0>
    thread_data[x].thread_index = x;
    3858:	45 89 bd 3c ff ff ff 	mov    %r15d,-0xc4(%r13)
    thread_data[x].thread_count = thread_count;
    385f:	49 89 85 60 ff ff ff 	mov    %rax,-0xa0(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3866:	e8 05 ec ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    386b:	48 83 44 24 78 10    	addq   $0x10,0x78(%rsp)
    3871:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3877:	41 83 ff 06          	cmp    $0x6,%r15d
    387b:	75 0b                	jne    3888 <main+0x1298>
    387d:	41 bf 07 00 00 00    	mov    $0x7,%r15d
    3883:	e9 3e ff ff ff       	jmp    37c6 <main+0x11d6>
    3888:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    388d:	4c 8d 25 3b 3c 00 00 	lea    0x3c3b(%rip),%r12        # 74cf <_IO_stdin_used+0x4cf>
    3894:	4c 8d 70 04          	lea    0x4(%rax),%r14
    3898:	4c 8d a8 44 06 00 00 	lea    0x644(%rax),%r13
    389f:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    38a3:	41 8b 16             	mov    (%r14),%edx
    38a6:	4c 89 e6             	mov    %r12,%rsi
    38a9:	bf 01 00 00 00       	mov    $0x1,%edi
    38ae:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    38b0:	49 81 c6 c8 00 00 00 	add    $0xc8,%r14
    38b7:	e8 94 eb ff ff       	call   2450 <__printf_chk@plt>
    38bc:	4d 39 f5             	cmp    %r14,%r13
    38bf:	75 de                	jne    389f <main+0x12af>
    38c1:	48 8d 3d 1a 3c 00 00 	lea    0x3c1a(%rip),%rdi        # 74e2 <_IO_stdin_used+0x4e2>
    38c8:	45 31 f6             	xor    %r14d,%r14d
    38cb:	4c 8d ac 24 c0 00 00 00 	lea    0xc0(%rsp),%r13
    38d3:	e8 18 ea ff ff       	call   22f0 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    38d8:	4c 8d 25 21 3c 00 00 	lea    0x3c21(%rip),%r12        # 7500 <_IO_stdin_used+0x500>
    void * result; 
    pthread_join(thread[x], &result);
    38df:	4a 8b 3c f3          	mov    (%rbx,%r14,8),%rdi
    38e3:	4c 89 ee             	mov    %r13,%rsi
    38e6:	e8 05 ec ff ff       	call   24f0 <pthread_join@plt>
    38eb:	44 89 f2             	mov    %r14d,%edx
    38ee:	4c 89 e6             	mov    %r12,%rsi
    38f1:	bf 01 00 00 00       	mov    $0x1,%edi
    38f6:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    38f8:	49 83 c6 01          	add    $0x1,%r14
    38fc:	e8 4f eb ff ff       	call   2450 <__printf_chk@plt>
    3901:	49 83 fe 08          	cmp    $0x8,%r14
    3905:	75 d8                	jne    38df <main+0x12ef>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(200, sizeof(struct Data*)); 
    3907:	be 08 00 00 00       	mov    $0x8,%esi
    390c:	bf c8 00 00 00       	mov    $0xc8,%edi
  int datas2_size = 0; 
    3911:	45 31 e4             	xor    %r12d,%r12d
  struct Data ** datas = calloc(200, sizeof(struct Data*)); 
    3914:	e8 87 ea ff ff       	call   23a0 <calloc@plt>
    3919:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    391e:	48 89 c3             	mov    %rax,%rbx
    3921:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3923:	49 89 d1             	mov    %rdx,%r9
    3926:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3929:	45 8b 51 40          	mov    0x40(%r9),%r10d
    392d:	45 85 d2             	test   %r10d,%r10d
    3930:	7e 72                	jle    39a4 <main+0x13b4>
    3932:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3936:	4d 63 c2             	movslq %r10d,%r8
    3939:	49 63 cc             	movslq %r12d,%rcx
    393c:	49 c1 e0 09          	shl    $0x9,%r8
    3940:	48 8d 34 cb          	lea    (%rbx,%rcx,8),%rsi
    3944:	49 01 f8             	add    %rdi,%r8
    3947:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3950:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3957:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    395e:	48 83 c6 40          	add    $0x40,%rsi
    3962:	f3 0f 7e 51 38       	movq   0x38(%rcx),%xmm2
    3967:	f3 0f 7e 49 70       	movq   0x70(%rcx),%xmm1
    396c:	f3 0f 7e 81 a8 00 00 00 	movq   0xa8(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3974:	f3 0f 7e 19          	movq   (%rcx),%xmm3
    3978:	0f 16 51 40          	movhps 0x40(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    397c:	0f 16 49 78          	movhps 0x78(%rcx),%xmm1
    3980:	0f 16 81 b0 00 00 00 	movhps 0xb0(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3987:	0f 16 59 08          	movhps 0x8(%rcx),%xmm3
    398b:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    398f:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3993:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3997:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    399b:	49 39 f8             	cmp    %rdi,%r8
    399e:	75 b0                	jne    3950 <main+0x1360>
    39a0:	47 8d 24 d4          	lea    (%r12,%r10,8),%r12d
    for (int d = 0 ; d < threads_per_group ; d++) {
    39a4:	49 81 c1 c8 00 00 00 	add    $0xc8,%r9
    39ab:	45 85 db             	test   %r11d,%r11d
    39ae:	75 08                	jne    39b8 <main+0x13c8>
    39b0:	41 89 eb             	mov    %ebp,%r11d
    39b3:	e9 71 ff ff ff       	jmp    3929 <main+0x1339>
  for (int k = 0 ; k < group_count ; k++) {
    39b8:	83 c0 02             	add    $0x2,%eax
    39bb:	48 81 c2 90 01 00 00 	add    $0x190,%rdx
    39c2:	83 f8 04             	cmp    $0x4,%eax
    39c5:	0f 85 58 ff ff ff    	jne    3923 <main+0x1333>
    39cb:	48 8d 3d 42 3b 00 00 	lea    0x3b42(%rip),%rdi        # 7514 <_IO_stdin_used+0x514>
    39d2:	e8 19 e9 ff ff       	call   22f0 <puts@plt>
        }
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  for (int x = 0 ; x < datas2_size; x++) {
    39d7:	45 85 e4             	test   %r12d,%r12d
    39da:	7e 43                	jle    3a1f <main+0x142f>
    39dc:	4d 63 e4             	movslq %r12d,%r12
    39df:	48 8d 2d 1b 3a 00 00 	lea    0x3a1b(%rip),%rbp        # 7401 <_IO_stdin_used+0x401>
    39e6:	4e 8d 24 e3          	lea    (%rbx,%r12,8),%r12
    printf("mailbox %d %d %d %d\n", datas[x]->kind, datas[x]->a, datas[x]->b, datas[x]->c);
    39ea:	48 8b 03             	mov    (%rbx),%rax
    39ed:	48 89 ee             	mov    %rbp,%rsi
    39f0:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    39f5:	48 83 c3 08          	add    $0x8,%rbx
    39f9:	8b 88 1c 03 00 00    	mov    0x31c(%rax),%ecx
    39ff:	8b 90 18 03 00 00    	mov    0x318(%rax),%edx
    3a05:	44 8b 88 24 03 00 00 	mov    0x324(%rax),%r9d
    3a0c:	44 8b 80 20 03 00 00 	mov    0x320(%rax),%r8d
    3a13:	31 c0                	xor    %eax,%eax
    3a15:	e8 36 ea ff ff       	call   2450 <__printf_chk@plt>
    3a1a:	4c 39 e3             	cmp    %r12,%rbx
    3a1d:	75 cb                	jne    39ea <main+0x13fa>
  } 

  long total = 0;
  long ingests = 0;
  long sends = 0;
    3a1f:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3a28:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
  long received = 0;
    3a2d:	45 31 ed             	xor    %r13d,%r13d
  long sents = 0;
    3a30:	45 31 e4             	xor    %r12d,%r12d
  long ingests = 0;
    3a33:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3a3c:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  long total = 0;
    3a46:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  int datas2_size = 0; 
    3a4f:	48 8b bc 24 98 00 00 00 	mov    0x98(%rsp),%rdi
    3a57:	89 44 24 10          	mov    %eax,0x10(%rsp)
    3a5b:	83 c0 02             	add    $0x2,%eax
    3a5e:	89 44 24 48          	mov    %eax,0x48(%rsp)
    3a62:	4c 8b bc 24 90 00 00 00 	mov    0x90(%rsp),%r15
    3a6a:	48 89 7c 24 40       	mov    %rdi,0x40(%rsp)
      int x = (k * threads_per_group) + d;
    3a6f:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    3a73:	89 f8                	mov    %edi,%eax
    3a75:	83 c7 01             	add    $0x1,%edi
        other = abs(x - 1) % total_threads;
    3a78:	8d 50 02             	lea    0x2(%rax),%edx
    3a7b:	89 7c 24 10          	mov    %edi,0x10(%rsp)
    3a7f:	83 e7 01             	and    $0x1,%edi
    3a82:	bf 0a 00 00 00       	mov    $0xa,%edi
    3a87:	0f 44 c2             	cmove  %edx,%eax
    3a8a:	48 63 d8             	movslq %eax,%rbx
    3a8d:	e8 3e e8 ff ff       	call   22d0 <putchar@plt>
    3a92:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3a97:	bf 01 00 00 00       	mov    $0x1,%edi
    3a9c:	48 8d 35 89 3a 00 00 	lea    0x3a89(%rip),%rsi        # 752c <_IO_stdin_used+0x52c>
    3aa3:	48 8b 10             	mov    (%rax),%rdx
    3aa6:	31 c0                	xor    %eax,%eax
    3aa8:	e8 a3 e9 ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3aad:	41 8b 57 40          	mov    0x40(%r15),%edx
    3ab1:	85 d2                	test   %edx,%edx
    3ab3:	0f 8e a5 04 00 00    	jle    3f5e <main+0x196e>
    3ab9:	48 63 ca             	movslq %edx,%rcx
    3abc:	49 8b 47 38          	mov    0x38(%r15),%rax
      long v = 0;
    3ac0:	31 d2                	xor    %edx,%edx
    3ac2:	48 c1 e1 09          	shl    $0x9,%rcx
    3ac6:	48 01 c1             	add    %rax,%rcx
    3ac9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        v += thread_data[me].tasks[n].v;
    3ad0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3ad7:	48 05 00 02 00 00    	add    $0x200,%rax
    3add:	48 39 c8             	cmp    %rcx,%rax
    3ae0:	75 ee                	jne    3ad0 <main+0x14e0>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3ae2:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3ae7:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    3aeb:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3aef:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3af3:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3af7:	85 c9                	test   %ecx,%ecx
    3af9:	7e 27                	jle    3b22 <main+0x1532>
    3afb:	48 8b 40 38          	mov    0x38(%rax),%rax
    3aff:	48 c1 e1 09          	shl    $0x9,%rcx
    3b03:	48 01 c1             	add    %rax,%rcx
    3b06:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3b10:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3b17:	48 05 00 02 00 00    	add    $0x200,%rax
    3b1d:	48 39 c8             	cmp    %rcx,%rax
    3b20:	75 ee                	jne    3b10 <main+0x1520>
    3b22:	48 8d 35 18 3a 00 00 	lea    0x3a18(%rip),%rsi        # 7541 <_IO_stdin_used+0x541>
    3b29:	bf 01 00 00 00       	mov    $0x1,%edi
    3b2e:	31 c0                	xor    %eax,%eax
    3b30:	e8 1b e9 ff ff       	call   2450 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3b35:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3b3a:	bf 01 00 00 00       	mov    $0x1,%edi
    3b3f:	48 8d 35 02 3d 00 00 	lea    0x3d02(%rip),%rsi        # 7848 <_IO_stdin_used+0x848>
    3b46:	48 8b 08             	mov    (%rax),%rcx
    3b49:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3b53:	48 f7 e9             	imul   %rcx
    3b56:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3b5a:	31 c0                	xor    %eax,%eax
    3b5c:	48 d1 fa             	sar    %rdx
    3b5f:	48 29 ca             	sub    %rcx,%rdx
    3b62:	e8 e9 e8 ff ff       	call   2450 <__printf_chk@plt>
    3b67:	bf 0a 00 00 00       	mov    $0xa,%edi
    3b6c:	e8 5f e7 ff ff       	call   22d0 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3b71:	45 8b 57 40          	mov    0x40(%r15),%r10d
    3b75:	45 85 d2             	test   %r10d,%r10d
    3b78:	0f 8e f1 00 00 00    	jle    3c6f <main+0x167f>
        total += thread_data[x].tasks[n].n;
    3b7e:	49 8b 57 38          	mov    0x38(%r15),%rdx
    3b82:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    3b87:	31 c9                	xor    %ecx,%ecx
    3b89:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    3b8e:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    3b93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3b98:	49 89 ce             	mov    %rcx,%r14
    3b9b:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
        sends += thread_data[x].tasks[n].sends;
    3b9f:	31 db                	xor    %ebx,%ebx
    3ba1:	49 c1 e6 09          	shl    $0x9,%r14
    3ba5:	48 89 4c 24 30       	mov    %rcx,0x30(%rsp)
        total += thread_data[x].tasks[n].n;
    3baa:	4c 01 f2             	add    %r14,%rdx
    3bad:	48 03 b2 08 01 00 00 	add    0x108(%rdx),%rsi
        ingests += thread_data[x].tasks[n].ingest_count;
    3bb4:	4c 03 82 68 01 00 00 	add    0x168(%rdx),%r8
        sends += thread_data[x].tasks[n].sends;
    3bbb:	48 03 ba 78 01 00 00 	add    0x178(%rdx),%rdi
    3bc2:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    3bc7:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    3bcc:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    3bd1:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    3bd5:	8b 54 24 10          	mov    0x10(%rsp),%edx
    3bd9:	41 89 d8             	mov    %ebx,%r8d
    3bdc:	bf 01 00 00 00       	mov    $0x1,%edi
    3be1:	48 8d 35 66 39 00 00 	lea    0x3966(%rip),%rsi        # 754e <_IO_stdin_used+0x54e>
    3be8:	31 c0                	xor    %eax,%eax
    3bea:	e8 61 e8 ff ff       	call   2450 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3bef:	49 8b 57 38          	mov    0x38(%r15),%rdx
    3bf3:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    3bfb:	48 29 d8             	sub    %rbx,%rax
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3bfe:	48 83 c3 01          	add    $0x1,%rbx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3c02:	4a 8b 8c 32 70 01 00 00 	mov    0x170(%rdx,%r14,1),%rcx
    3c0a:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    3c0e:	48 8b 08             	mov    (%rax),%rcx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3c11:	48 8b 40 08          	mov    0x8(%rax),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3c15:	4c 8b 89 08 03 00 00 	mov    0x308(%rcx),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3c1c:	4c 8b 91 10 03 00 00 	mov    0x310(%rcx),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3c23:	4d 01 e1             	add    %r12,%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3c26:	4d 01 ea             	add    %r13,%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3c29:	4c 03 88 08 03 00 00 	add    0x308(%rax),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3c30:	4c 03 90 10 03 00 00 	add    0x310(%rax),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3c37:	4d 89 cc             	mov    %r9,%r12
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3c3a:	4d 89 d5             	mov    %r10,%r13
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3c3d:	48 83 fb 04          	cmp    $0x4,%rbx
    3c41:	75 8e                	jne    3bd1 <main+0x15e1>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c43:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    3c48:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    3c4d:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    3c52:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    3c57:	48 83 c1 01          	add    $0x1,%rcx
    3c5b:	41 39 4f 40          	cmp    %ecx,0x40(%r15)
    3c5f:	0f 8f 33 ff ff ff    	jg     3b98 <main+0x15a8>
    3c65:	4c 89 44 24 20       	mov    %r8,0x20(%rsp)
    3c6a:	48 89 74 24 30       	mov    %rsi,0x30(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3c6f:	45 31 f6             	xor    %r14d,%r14d
    3c72:	49 83 bf a0 00 00 00 00 	cmpq   $0x0,0xa0(%r15)
    3c7a:	48 8d 1d e7 3b 00 00 	lea    0x3be7(%rip),%rbx        # 7868 <_IO_stdin_used+0x868>
    3c81:	7e 5d                	jle    3ce0 <main+0x16f0>
    3c83:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3c88:	49 8b 87 90 00 00 00 	mov    0x90(%r15),%rax
    3c8f:	4b 8d 14 b6          	lea    (%r14,%r14,4),%rdx
    3c93:	48 83 ec 08          	sub    $0x8,%rsp
    3c97:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3c9c:	49 83 c6 01          	add    $0x1,%r14
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3ca0:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3ca4:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3ca8:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3cac:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3caf:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3cb3:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3cb6:	48 f7 e5             	mul    %rbp
    3cb9:	8b 49 20             	mov    0x20(%rcx),%ecx
    3cbc:	56                   	push   %rsi
    3cbd:	31 c0                	xor    %eax,%eax
    3cbf:	48 89 de             	mov    %rbx,%rsi
    3cc2:	48 c1 ea 12          	shr    $0x12,%rdx
    3cc6:	49 89 d1             	mov    %rdx,%r9
    3cc9:	ba 02 00 00 00       	mov    $0x2,%edx
    3cce:	e8 7d e7 ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3cd3:	41 58                	pop    %r8
    3cd5:	41 59                	pop    %r9
    3cd7:	4d 39 b7 a0 00 00 00 	cmp    %r14,0xa0(%r15)
    3cde:	7f a8                	jg     3c88 <main+0x1698>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3ce0:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    3ce7:	85 c9                	test   %ecx,%ecx
    3ce9:	0f 8e f7 00 00 00    	jle    3de6 <main+0x17f6>
    3cef:	4c 89 64 24 50       	mov    %r12,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3cf4:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    3cf8:	31 db                	xor    %ebx,%ebx
    3cfa:	4c 89 6c 24 58       	mov    %r13,0x58(%rsp)
    3cff:	90                   	nop
    3d00:	49 8b 04 d9          	mov    (%r9,%rbx,8),%rax
    3d04:	41 89 dc             	mov    %ebx,%r12d
    3d07:	4c 8d 2c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r13
    3d0f:	8b 30                	mov    (%rax),%esi
    3d11:	85 f6                	test   %esi,%esi
    3d13:	0f 8e b7 00 00 00    	jle    3dd0 <main+0x17e0>
    3d19:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3d1e:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3d22:	31 ff                	xor    %edi,%edi
    3d24:	0f 1f 40 00          	nopl   0x0(%rax)
    3d28:	48 89 fb             	mov    %rdi,%rbx
    3d2b:	45 31 f6             	xor    %r14d,%r14d
    3d2e:	48 c1 e3 08          	shl    $0x8,%rbx
    3d32:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    3d36:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    3d3c:	85 d2                	test   %edx,%edx
    3d3e:	7e 78                	jle    3db8 <main+0x17c8>
    3d40:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    3d45:	0f 1f 00             	nopl   (%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3d48:	4c 89 f1             	mov    %r14,%rcx
    3d4b:	48 83 ec 08          	sub    $0x8,%rsp
    3d4f:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3d54:	49 83 c6 01          	add    $0x1,%r14
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3d58:	48 c1 e1 05          	shl    $0x5,%rcx
    3d5c:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3d63:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3d67:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3d6b:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3d6e:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3d72:	4c 2b 01             	sub    (%rcx),%r8
    3d75:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3d76:	48 f7 e5             	mul    %rbp
    3d79:	44 89 e1             	mov    %r12d,%ecx
    3d7c:	48 8d 35 35 3b 00 00 	lea    0x3b35(%rip),%rsi        # 78b8 <_IO_stdin_used+0x8b8>
    3d83:	31 c0                	xor    %eax,%eax
    3d85:	48 c1 ea 12          	shr    $0x12,%rdx
    3d89:	49 89 d1             	mov    %rdx,%r9
    3d8c:	ba 02 00 00 00       	mov    $0x2,%edx
    3d91:	e8 ba e6 ff ff       	call   2450 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3d96:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    3d9a:	5e                   	pop    %rsi
    3d9b:	5f                   	pop    %rdi
    3d9c:	4b 8b 14 29          	mov    (%r9,%r13,1),%rdx
    3da0:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    3da4:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    3da8:	44 39 b0 94 00 00 00 	cmp    %r14d,0x94(%rax)
    3daf:	7f 97                	jg     3d48 <main+0x1758>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3db1:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    3db6:	8b 32                	mov    (%rdx),%esi
    3db8:	48 83 c7 01          	add    $0x1,%rdi
    3dbc:	39 fe                	cmp    %edi,%esi
    3dbe:	0f 8f 64 ff ff ff    	jg     3d28 <main+0x1738>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3dc4:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    3dc9:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    3dd0:	48 83 c3 01          	add    $0x1,%rbx
    3dd4:	39 d9                	cmp    %ebx,%ecx
    3dd6:	0f 8f 24 ff ff ff    	jg     3d00 <main+0x1710>
    3ddc:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    3de1:	4c 8b 6c 24 58       	mov    0x58(%rsp),%r13
    for (int d = 0 ; d < threads_per_group ; d++) {
    3de6:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    3dec:	8b 7c 24 48          	mov    0x48(%rsp),%edi
    3df0:	49 81 c7 c8 00 00 00 	add    $0xc8,%r15
    3df7:	39 7c 24 10          	cmp    %edi,0x10(%rsp)
    3dfb:	0f 85 6e fc ff ff    	jne    3a6f <main+0x147f>
  for (int k = 0 ; k < group_count ; k++) {
    3e01:	48 83 84 24 98 00 00 00 30 	addq   $0x30,0x98(%rsp)
    3e0a:	b8 01 00 00 00       	mov    $0x1,%eax
    3e0f:	48 81 84 24 90 00 00 00 90 01 00 00 	addq   $0x190,0x90(%rsp)
    3e1b:	83 7c 24 10 03       	cmpl   $0x3,0x10(%rsp)
    3e20:	0f 85 29 fc ff ff    	jne    3a4f <main+0x145f>
    3e26:	4c 8b 7c 24 30       	mov    0x30(%rsp),%r15
    3e2b:	48 8d 35 2c 37 00 00 	lea    0x372c(%rip),%rsi        # 755e <_IO_stdin_used+0x55e>
    3e32:	bf 01 00 00 00       	mov    $0x1,%edi
    3e37:	31 c0                	xor    %eax,%eax
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3e39:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    3e43:	4c 89 fa             	mov    %r15,%rdx
    3e46:	e8 05 e6 ff ff       	call   2450 <__printf_chk@plt>
    3e4b:	bf 0a 00 00 00       	mov    $0xa,%edi
    3e50:	e8 7b e4 ff ff       	call   22d0 <putchar@plt>
    3e55:	48 8b 7c 24 70       	mov    0x70(%rsp),%rdi
    3e5a:	48 8d 35 af 3a 00 00 	lea    0x3aaf(%rip),%rsi        # 7910 <_IO_stdin_used+0x910>
    3e61:	31 c0                	xor    %eax,%eax
    3e63:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    3e67:	bf 01 00 00 00       	mov    $0x1,%edi
    3e6c:	e8 df e5 ff ff       	call   2450 <__printf_chk@plt>
    3e71:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    3e76:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3e7b:	48 8d 35 b6 3a 00 00 	lea    0x3ab6(%rip),%rsi        # 7938 <_IO_stdin_used+0x938>
    3e82:	48 f7 eb             	imul   %rbx
    3e85:	48 c1 ff 3f          	sar    $0x3f,%rdi
    3e89:	31 c0                	xor    %eax,%eax
    3e8b:	48 d1 fa             	sar    %rdx
    3e8e:	48 29 fa             	sub    %rdi,%rdx
    3e91:	bf 01 00 00 00       	mov    $0x1,%edi
    3e96:	e8 b5 e5 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3e9b:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3ea0:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    3ea5:	48 8d 35 bc 3a 00 00 	lea    0x3abc(%rip),%rsi        # 7968 <_IO_stdin_used+0x968>
    3eac:	48 f7 eb             	imul   %rbx
    3eaf:	48 c1 ff 3f          	sar    $0x3f,%rdi
    3eb3:	31 c0                	xor    %eax,%eax
    3eb5:	48 d1 fa             	sar    %rdx
    3eb8:	48 29 fa             	sub    %rdi,%rdx
    3ebb:	bf 01 00 00 00       	mov    $0x1,%edi
    3ec0:	e8 8b e5 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3ec5:	4c 89 f8             	mov    %r15,%rax
    3ec8:	4c 89 ff             	mov    %r15,%rdi
    3ecb:	48 8d 35 c6 3a 00 00 	lea    0x3ac6(%rip),%rsi        # 7998 <_IO_stdin_used+0x998>
    3ed2:	48 f7 eb             	imul   %rbx
    3ed5:	48 c1 ff 3f          	sar    $0x3f,%rdi
    3ed9:	31 c0                	xor    %eax,%eax
    3edb:	48 d1 fa             	sar    %rdx
    3ede:	48 29 fa             	sub    %rdi,%rdx
    3ee1:	bf 01 00 00 00       	mov    $0x1,%edi
    3ee6:	e8 65 e5 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3eeb:	4c 89 e0             	mov    %r12,%rax
    3eee:	bf 01 00 00 00       	mov    $0x1,%edi
    3ef3:	48 8d 35 78 36 00 00 	lea    0x3678(%rip),%rsi        # 7572 <_IO_stdin_used+0x572>
    3efa:	48 f7 eb             	imul   %rbx
    3efd:	4c 89 e0             	mov    %r12,%rax
    3f00:	48 c1 f8 3f          	sar    $0x3f,%rax
    3f04:	48 d1 fa             	sar    %rdx
    3f07:	48 29 c2             	sub    %rax,%rdx
    3f0a:	31 c0                	xor    %eax,%eax
    3f0c:	e8 3f e5 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3f11:	4c 89 e8             	mov    %r13,%rax
    3f14:	bf 01 00 00 00       	mov    $0x1,%edi
    3f19:	48 8d 35 63 36 00 00 	lea    0x3663(%rip),%rsi        # 7583 <_IO_stdin_used+0x583>
    3f20:	48 f7 eb             	imul   %rbx
    3f23:	4c 89 e8             	mov    %r13,%rax
    3f26:	48 c1 f8 3f          	sar    $0x3f,%rax
    3f2a:	48 d1 fa             	sar    %rdx
    3f2d:	48 29 c2             	sub    %rax,%rdx
    3f30:	31 c0                	xor    %eax,%eax
    3f32:	e8 19 e5 ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3f37:	48 8b 84 24 c8 00 00 00 	mov    0xc8(%rsp),%rax
    3f3f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3f48:	75 25                	jne    3f6f <main+0x197f>
    3f4a:	48 81 c4 d8 00 00 00 	add    $0xd8,%rsp
    3f51:	31 c0                	xor    %eax,%eax
    3f53:	5b                   	pop    %rbx
    3f54:	5d                   	pop    %rbp
    3f55:	41 5c                	pop    %r12
    3f57:	41 5d                	pop    %r13
    3f59:	41 5e                	pop    %r14
    3f5b:	41 5f                	pop    %r15
    3f5d:	c3                   	ret
      long v = 0;
    3f5e:	31 d2                	xor    %edx,%edx
    3f60:	e9 7d fb ff ff       	jmp    3ae2 <main+0x14f2>
            exit(1);
    3f65:	bf 01 00 00 00       	mov    $0x1,%edi
    3f6a:	e8 31 e5 ff ff       	call   24a0 <exit@plt>
}
    3f6f:	e8 bc e3 ff ff       	call   2330 <__stack_chk_fail@plt>
    3f74:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3f7e:	66 90                	xchg   %ax,%ax

0000000000003f80 <_start>:
    3f80:	f3 0f 1e fa          	endbr64
    3f84:	31 ed                	xor    %ebp,%ebp
    3f86:	49 89 d1             	mov    %rdx,%r9
    3f89:	5e                   	pop    %rsi
    3f8a:	48 89 e2             	mov    %rsp,%rdx
    3f8d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3f91:	50                   	push   %rax
    3f92:	54                   	push   %rsp
    3f93:	45 31 c0             	xor    %r8d,%r8d
    3f96:	31 c9                	xor    %ecx,%ecx
    3f98:	48 8d 3d 51 e6 ff ff 	lea    -0x19af(%rip),%rdi        # 25f0 <main>
    3f9f:	ff 15 33 60 00 00    	call   *0x6033(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3fa5:	f4                   	hlt
    3fa6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003fb0 <deregister_tm_clones>:
    3fb0:	48 8d 3d 69 60 00 00 	lea    0x6069(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3fb7:	48 8d 05 62 60 00 00 	lea    0x6062(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    3fbe:	48 39 f8             	cmp    %rdi,%rax
    3fc1:	74 15                	je     3fd8 <deregister_tm_clones+0x28>
    3fc3:	48 8b 05 16 60 00 00 	mov    0x6016(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    3fca:	48 85 c0             	test   %rax,%rax
    3fcd:	74 09                	je     3fd8 <deregister_tm_clones+0x28>
    3fcf:	ff e0                	jmp    *%rax
    3fd1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3fd8:	c3                   	ret
    3fd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003fe0 <register_tm_clones>:
    3fe0:	48 8d 3d 39 60 00 00 	lea    0x6039(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3fe7:	48 8d 35 32 60 00 00 	lea    0x6032(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    3fee:	48 29 fe             	sub    %rdi,%rsi
    3ff1:	48 89 f0             	mov    %rsi,%rax
    3ff4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3ff8:	48 c1 f8 03          	sar    $0x3,%rax
    3ffc:	48 01 c6             	add    %rax,%rsi
    3fff:	48 d1 fe             	sar    %rsi
    4002:	74 14                	je     4018 <register_tm_clones+0x38>
    4004:	48 8b 05 e5 5f 00 00 	mov    0x5fe5(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    400b:	48 85 c0             	test   %rax,%rax
    400e:	74 08                	je     4018 <register_tm_clones+0x38>
    4010:	ff e0                	jmp    *%rax
    4012:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4018:	c3                   	ret
    4019:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004020 <__do_global_dtors_aux>:
    4020:	f3 0f 1e fa          	endbr64
    4024:	80 3d fd 5f 00 00 00 	cmpb   $0x0,0x5ffd(%rip)        # a028 <completed.0>
    402b:	75 2b                	jne    4058 <__do_global_dtors_aux+0x38>
    402d:	55                   	push   %rbp
    402e:	48 83 3d c2 5f 00 00 00 	cmpq   $0x0,0x5fc2(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    4036:	48 89 e5             	mov    %rsp,%rbp
    4039:	74 0c                	je     4047 <__do_global_dtors_aux+0x27>
    403b:	48 8b 3d c6 5f 00 00 	mov    0x5fc6(%rip),%rdi        # a008 <__dso_handle>
    4042:	e8 69 e2 ff ff       	call   22b0 <__cxa_finalize@plt>
    4047:	e8 64 ff ff ff       	call   3fb0 <deregister_tm_clones>
    404c:	c6 05 d5 5f 00 00 01 	movb   $0x1,0x5fd5(%rip)        # a028 <completed.0>
    4053:	5d                   	pop    %rbp
    4054:	c3                   	ret
    4055:	0f 1f 00             	nopl   (%rax)
    4058:	c3                   	ret
    4059:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004060 <frame_dummy>:
    4060:	f3 0f 1e fa          	endbr64
    4064:	e9 77 ff ff ff       	jmp    3fe0 <register_tm_clones>
    4069:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004070 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    4070:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    4074:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    407b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    407f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    4087:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    408b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    408f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4096:	48 85 c9             	test   %rcx,%rcx
    4099:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    40a0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    40a4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    40a8:	31 c0                	xor    %eax,%eax
    40aa:	c3                   	ret
    40ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000040b0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    40b0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    40b4:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    40bb:	85 c9                	test   %ecx,%ecx
    40bd:	7e 4f                	jle    410e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    40bf:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    40c6:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    40cd:	48 c1 e1 09          	shl    $0x9,%rcx
    40d1:	48 8b 50 18          	mov    0x18(%rax),%rdx
    40d5:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    40d9:	48 8b 70 38          	mov    0x38(%rax),%rsi
    40dd:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    40df:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    40e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    40e8:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    40f0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    40f8:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    4103:	48 05 00 02 00 00    	add    $0x200,%rax
    4109:	48 39 c1             	cmp    %rax,%rcx
    410c:	75 da                	jne    40e8 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    410e:	0f ae f8             	sfence
}
    4111:	31 c0                	xor    %eax,%eax
    4113:	c3                   	ret
    4114:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    411f:	90                   	nop

0000000000004120 <external_thread>:
void * external_thread(void *arg) {
    4120:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    4124:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    4128:	0f 85 fb 00 00 00    	jne    4229 <external_thread+0x109>
void * external_thread(void *arg) {
    412e:	41 57                	push   %r15
    4130:	49 89 ff             	mov    %rdi,%r15
    4133:	41 56                	push   %r14
    4135:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    4137:	4c 8d 2d c6 2e 00 00 	lea    0x2ec6(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    413e:	41 54                	push   %r12
    4140:	55                   	push   %rbp
    4141:	53                   	push   %rbx
    4142:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    4146:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    414c:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    4150:	85 c9                	test   %ecx,%ecx
    4152:	7e 6e                	jle    41c2 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4154:	45 31 e4             	xor    %r12d,%r12d
    4157:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4160:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    4168:	31 db                	xor    %ebx,%ebx
    416a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    416e:	48 8b 06             	mov    (%rsi),%rax
    4171:	8b 10                	mov    (%rax),%edx
    4173:	85 d2                	test   %edx,%edx
    4175:	7e 2a                	jle    41a1 <external_thread+0x81>
    4177:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    417b:	48 89 dd             	mov    %rbx,%rbp
    417e:	48 c1 e5 08          	shl    $0x8,%rbp
    4182:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4186:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    418d:	45 85 c0             	test   %r8d,%r8d
    4190:	74 36                	je     41c8 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4192:	48 83 c3 01          	add    $0x1,%rbx
    4196:	39 da                	cmp    %ebx,%edx
    4198:	7f e1                	jg     417b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    419a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    41a1:	49 83 c4 01          	add    $0x1,%r12
    41a5:	44 39 e1             	cmp    %r12d,%ecx
    41a8:	7f b6                	jg     4160 <external_thread+0x40>
  while (data->running == 1) {
    41aa:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    41af:	74 9f                	je     4150 <external_thread+0x30>
}
    41b1:	48 83 c4 08          	add    $0x8,%rsp
    41b5:	31 c0                	xor    %eax,%eax
    41b7:	5b                   	pop    %rbx
    41b8:	5d                   	pop    %rbp
    41b9:	41 5c                	pop    %r12
    41bb:	41 5d                	pop    %r13
    41bd:	41 5e                	pop    %r14
    41bf:	41 5f                	pop    %r15
    41c1:	c3                   	ret
  while (data->running == 1) {
    41c2:	eb fe                	jmp    41c2 <external_thread+0xa2>
    41c4:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    41c8:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    41cb:	48 8b 06             	mov    (%rsi),%rax
    41ce:	48 8b 78 08          	mov    0x8(%rax),%rdi
    41d2:	48 01 ef             	add    %rbp,%rdi
    41d5:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    41dc:	48 c1 e6 05          	shl    $0x5,%rsi
    41e0:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    41e7:	bf 04 00 00 00       	mov    $0x4,%edi
    41ec:	e8 1f e1 ff ff       	call   2310 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    41f1:	49 8b 47 50          	mov    0x50(%r15),%rax
    41f5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    41f9:	48 8b 40 08          	mov    0x8(%rax),%rax
    41fd:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    4208:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    420b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    420f:	48 83 c3 01          	add    $0x1,%rbx
    4213:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    4217:	48 8b 06             	mov    (%rsi),%rax
    421a:	8b 10                	mov    (%rax),%edx
    421c:	39 da                	cmp    %ebx,%edx
    421e:	0f 8f 53 ff ff ff    	jg     4177 <external_thread+0x57>
    4224:	e9 71 ff ff ff       	jmp    419a <external_thread+0x7a>
}
    4229:	31 c0                	xor    %eax,%eax
    422b:	c3                   	ret
    422c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004230 <timer_thread>:
void* timer_thread(void *arg) {
    4230:	f3 0f 1e fa          	endbr64
    4234:	41 57                	push   %r15
    4236:	48 8d 35 d3 2d 00 00 	lea    0x2dd3(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    423d:	41 56                	push   %r14
    423f:	41 55                	push   %r13
    4241:	41 54                	push   %r12
    4243:	55                   	push   %rbp
    4244:	48 89 fd             	mov    %rdi,%rbp
    4247:	53                   	push   %rbx
    4248:	48 83 ec 58          	sub    $0x58,%rsp
    424c:	8b 57 04             	mov    0x4(%rdi),%edx
    424f:	bf 01 00 00 00       	mov    $0x1,%edi
    4254:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    425d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    4262:	31 c0                	xor    %eax,%eax
    4264:	e8 e7 e1 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    4269:	66 0f 6f 05 3f 39 00 00 	movdqa 0x393f(%rip),%xmm0        # 7bb0 <_IO_stdin_used+0xbb0>
    4271:	ba 88 13 00 00       	mov    $0x1388,%edx
    4276:	31 c0                	xor    %eax,%eax
    4278:	48 8d 35 a3 2d 00 00 	lea    0x2da3(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    427f:	bf 01 00 00 00       	mov    $0x1,%edi
    4284:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    4289:	e8 c2 e1 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    428e:	44 8b 65 44          	mov    0x44(%rbp),%r12d
    4292:	45 85 e4             	test   %r12d,%r12d
    4295:	0f 84 9b 00 00 00    	je     4336 <timer_thread+0x106>
  int n = 0;
    429b:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    429e:	45 31 e4             	xor    %r12d,%r12d
    42a1:	49 89 e6             	mov    %rsp,%r14
    y++;
    42a4:	31 db                	xor    %ebx,%ebx
    42a6:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    nanosleep(&preempt , &rem2);
    42ab:	4c 89 ef             	mov    %r13,%rdi
    42ae:	4c 89 f6             	mov    %r14,%rsi
    n++;
    42b1:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    42b5:	e8 96 e0 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    42ba:	48 63 45 30          	movslq 0x30(%rbp),%rax
    y++;
    42be:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    42c3:	85 c0                	test   %eax,%eax
    42c5:	7e 46                	jle    430d <timer_thread+0xdd>
    42c7:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    42cb:	49 c1 e4 09          	shl    $0x9,%r12
    42cf:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    42d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    42d8:	4c 8b 19             	mov    (%rcx),%r11
    42db:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    42dd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    42e1:	99                   	cltd
    42e2:	41 f7 7b 40          	idivl  0x40(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    42e6:	49 8b 73 38          	mov    0x38(%r11),%rsi
    42ea:	48 63 d2             	movslq %edx,%rdx
    42ed:	48 c1 e2 09          	shl    $0x9,%rdx
    42f1:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    42fc:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4308:	49 39 c8             	cmp    %rcx,%r8
    430b:	75 cb                	jne    42d8 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    430d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4310:	48 8b 45 18          	mov    0x18(%rbp),%rax
  while (data->running && n < times) {
    4314:	44 8b 45 44          	mov    0x44(%rbp),%r8d
    if (y >= data->threads[0]->task_count) {
    4318:	48 8b 00             	mov    (%rax),%rax
    y++;
    431b:	39 78 40             	cmp    %edi,0x40(%rax)
    431e:	0f 4e fb             	cmovle %ebx,%edi
    4321:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    4324:	45 85 c0             	test   %r8d,%r8d
    4327:	74 0d                	je     4336 <timer_thread+0x106>
    4329:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    4330:	0f 85 75 ff ff ff    	jne    42ab <timer_thread+0x7b>
    4336:	48 8d 3d fb 2c 00 00 	lea    0x2cfb(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    433d:	e8 ae df ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    4342:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    4346:	85 d2                	test   %edx,%edx
    4348:	7e 6b                	jle    43b5 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    434a:	48 63 45 40          	movslq 0x40(%rbp),%rax
    434e:	85 c0                	test   %eax,%eax
    4350:	7e 63                	jle    43b5 <timer_thread+0x185>
    4352:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    4356:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    435a:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4362:	31 c9                	xor    %ecx,%ecx
    4364:	48 89 c6             	mov    %rax,%rsi
    4367:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    436b:	48 8b 40 38          	mov    0x38(%rax),%rax
    436f:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4373:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4379:	74 15                	je     4390 <timer_thread+0x160>
    437b:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4385:	48 05 00 02 00 00    	add    $0x200,%rax
    438b:	48 39 c2             	cmp    %rax,%rdx
    438e:	74 1c                	je     43ac <timer_thread+0x17c>
      data->threads[x]->tasks[y].sending = 0;
    4390:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    439a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    43a0:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    43a7:	48 39 c2             	cmp    %rax,%rdx
    43aa:	75 e4                	jne    4390 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    43ac:	48 83 c1 08          	add    $0x8,%rcx
    43b0:	48 39 cf             	cmp    %rcx,%rdi
    43b3:	75 b2                	jne    4367 <timer_thread+0x137>
  asm volatile ("mfence" ::: "memory");
    43b5:	0f ae f0             	mfence
  struct timespec drain = {
    43b8:	66 0f 6f 05 00 38 00 00 	movdqa 0x3800(%rip),%xmm0        # 7bc0 <_IO_stdin_used+0xbc0>
    43c0:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    43c5:	48 63 45 28          	movslq 0x28(%rbp),%rax
    y++;
    43c9:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    43ce:	85 c0                	test   %eax,%eax
    43d0:	7e 4a                	jle    441c <timer_thread+0x1ec>
    43d2:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    43d6:	4d 63 e4             	movslq %r12d,%r12
    43d9:	49 c1 e4 09          	shl    $0x9,%r12
    43dd:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    43e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    43e8:	48 8b 19             	mov    (%rcx),%rbx
    43eb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    43ed:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    43f1:	99                   	cltd
    43f2:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    43f5:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    43f9:	48 63 d2             	movslq %edx,%rdx
    43fc:	48 c1 e2 09          	shl    $0x9,%rdx
    4400:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    440b:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4417:	49 39 c8             	cmp    %rcx,%r8
    441a:	75 cc                	jne    43e8 <timer_thread+0x1b8>
    asm volatile ("mfence" ::: "memory");
    441c:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    441f:	48 8b 45 18          	mov    0x18(%rbp),%rax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4423:	8b 4d 30             	mov    0x30(%rbp),%ecx
    y++;
    4426:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    4429:	48 8b 00             	mov    (%rax),%rax
    y++;
    442c:	39 78 40             	cmp    %edi,0x40(%rax)
    442f:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4433:	85 c9                	test   %ecx,%ecx
    4435:	0f 8e 16 01 00 00    	jle    4551 <timer_thread+0x321>
    443b:	31 db                	xor    %ebx,%ebx
    int all_empty = 1;
    443d:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    4443:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int y = 0 ; y < 2 ; y++) {
    4448:	45 31 f6             	xor    %r14d,%r14d
    444b:	41 89 dd             	mov    %ebx,%r13d
    444e:	4c 8d 3c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r15
    4456:	44 89 f6             	mov    %r14d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4459:	85 c9                	test   %ecx,%ecx
    445b:	0f 8e af 00 00 00    	jle    4510 <timer_thread+0x2e0>
    4461:	4c 89 f7             	mov    %r14,%rdi
      y = 0;
    4464:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4466:	45 31 c0             	xor    %r8d,%r8d
    4469:	48 c1 e7 09          	shl    $0x9,%rdi
    446d:	0f 1f 00             	nopl   (%rax)
          if (x == k) { continue; }
    4470:	41 39 d8             	cmp    %ebx,%r8d
    4473:	74 36                	je     44ab <timer_thread+0x27b>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4475:	48 8b 55 18          	mov    0x18(%rbp),%rdx
    4479:	4a 8b 14 3a          	mov    (%rdx,%r15,1),%rdx
    447d:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4481:	4c 8b 94 3a 70 01 00 00 	mov    0x170(%rdx,%rdi,1),%r10
    4489:	49 01 c2             	add    %rax,%r10
    448c:	4d 8b 0a             	mov    (%r10),%r9
    448f:	49 8b 52 08          	mov    0x8(%r10),%rdx
    4493:	4d 8b 89 80 00 00 00 	mov    0x80(%r9),%r9
    449a:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    44a1:	4d 85 c9             	test   %r9,%r9
    44a4:	7f 2a                	jg     44d0 <timer_thread+0x2a0>
    44a6:	48 85 d2             	test   %rdx,%rdx
    44a9:	7f 25                	jg     44d0 <timer_thread+0x2a0>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    44ab:	41 83 c0 01          	add    $0x1,%r8d
    44af:	48 83 c0 38          	add    $0x38,%rax
    44b3:	41 39 c8             	cmp    %ecx,%r8d
    44b6:	75 b8                	jne    4470 <timer_thread+0x240>
      for (int y = 0 ; y < 2 ; y++) {
    44b8:	49 83 fe 01          	cmp    $0x1,%r14
    44bc:	74 52                	je     4510 <timer_thread+0x2e0>
    44be:	49 83 c6 01          	add    $0x1,%r14
    44c2:	44 89 f6             	mov    %r14d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    44c5:	eb 9a                	jmp    4461 <timer_thread+0x231>
    44c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    44d0:	48 83 ec 08          	sub    $0x8,%rsp
    44d4:	89 f1                	mov    %esi,%ecx
    44d6:	bf 01 00 00 00       	mov    $0x1,%edi
    44db:	31 c0                	xor    %eax,%eax
    44dd:	52                   	push   %rdx
    44de:	48 8d 35 78 2b 00 00 	lea    0x2b78(%rip),%rsi        # 705d <_IO_stdin_used+0x5d>
    44e5:	44 89 ea             	mov    %r13d,%edx
    44e8:	e8 63 df ff ff       	call   2450 <__printf_chk@plt>
      for (int y = 0 ; y < 2 ; y++) {
    44ed:	5a                   	pop    %rdx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    44ee:	8b 4d 30             	mov    0x30(%rbp),%ecx
      for (int y = 0 ; y < 2 ; y++) {
    44f1:	5e                   	pop    %rsi
    44f2:	49 83 fe 01          	cmp    $0x1,%r14
    44f6:	74 48                	je     4540 <timer_thread+0x310>
    44f8:	49 83 c6 01          	add    $0x1,%r14
    44fc:	45 31 db             	xor    %r11d,%r11d
    44ff:	44 89 f6             	mov    %r14d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4502:	85 c9                	test   %ecx,%ecx
    4504:	0f 8f 57 ff ff ff    	jg     4461 <timer_thread+0x231>
    450a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4510:	48 83 c3 01          	add    $0x1,%rbx
    4514:	39 d9                	cmp    %ebx,%ecx
    4516:	0f 8f 2c ff ff ff    	jg     4448 <timer_thread+0x218>
    if (all_empty == 1) {
    451c:	41 83 fb 01          	cmp    $0x1,%r11d
    4520:	74 2f                	je     4551 <timer_thread+0x321>
      nanosleep(&drain , &drainrem);
    4522:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4527:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    452c:	e8 1f de ff ff       	call   2350 <nanosleep@plt>
    4531:	e9 8f fe ff ff       	jmp    43c5 <timer_thread+0x195>
    4536:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4540:	48 83 c3 01          	add    $0x1,%rbx
    4544:	45 31 db             	xor    %r11d,%r11d
    4547:	39 d9                	cmp    %ebx,%ecx
    4549:	0f 8f f9 fe ff ff    	jg     4448 <timer_thread+0x218>
    454f:	eb cb                	jmp    451c <timer_thread+0x2ec>
    4551:	48 8d 3d fc 2a 00 00 	lea    0x2afc(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    4558:	e8 93 dd ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    455d:	8b 7d 44             	mov    0x44(%rbp),%edi
    4560:	85 ff                	test   %edi,%edi
    4562:	0f 84 e6 00 00 00    	je     464e <timer_thread+0x41e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4568:	8b 45 2c             	mov    0x2c(%rbp),%eax
    456b:	31 db                	xor    %ebx,%ebx
    456d:	4c 8d 25 00 2b 00 00 	lea    0x2b00(%rip),%r12        # 7074 <_IO_stdin_used+0x74>
    4574:	4c 8d 2d 14 2b 00 00 	lea    0x2b14(%rip),%r13        # 708f <_IO_stdin_used+0x8f>
    457b:	85 c0                	test   %eax,%eax
    457d:	7e 34                	jle    45b3 <timer_thread+0x383>
    457f:	90                   	nop
    4580:	31 c0                	xor    %eax,%eax
    4582:	89 da                	mov    %ebx,%edx
    4584:	4c 89 e6             	mov    %r12,%rsi
    4587:	bf 01 00 00 00       	mov    $0x1,%edi
    458c:	e8 bf de ff ff       	call   2450 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4591:	48 8b 45 18          	mov    0x18(%rbp),%rax
    4595:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4599:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    459d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    45a4:	0f 84 d1 00 00 00    	je     467b <timer_thread+0x44b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    45aa:	48 83 c3 01          	add    $0x1,%rbx
    45ae:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    45b1:	7f cd                	jg     4580 <timer_thread+0x350>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    45b3:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    45b7:	85 d2                	test   %edx,%edx
    45b9:	7e 7d                	jle    4638 <timer_thread+0x408>
      for (int y = 0 ; y < data->task_count ; y++) {
    45bb:	8b 45 40             	mov    0x40(%rbp),%eax
    45be:	85 c0                	test   %eax,%eax
    45c0:	7e 76                	jle    4638 <timer_thread+0x408>
    45c2:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    45c5:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    45c9:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    45d1:	31 c9                	xor    %ecx,%ecx
    45d3:	48 c1 e6 09          	shl    $0x9,%rsi
    45d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    45e0:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    45e4:	48 8b 40 38          	mov    0x38(%rax),%rax
    45e8:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    45ec:	f7 c6 00 02 00 00    	test   $0x200,%esi
    45f2:	74 1c                	je     4610 <timer_thread+0x3e0>
    45f4:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    45fe:	48 05 00 02 00 00    	add    $0x200,%rax
    4604:	48 39 c2             	cmp    %rax,%rdx
    4607:	74 26                	je     462f <timer_thread+0x3ff>
    4609:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4610:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    461a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4620:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    462a:	48 39 c2             	cmp    %rax,%rdx
    462d:	75 e1                	jne    4610 <timer_thread+0x3e0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    462f:	48 83 c1 08          	add    $0x8,%rcx
    4633:	48 39 f9             	cmp    %rdi,%rcx
    4636:	75 a8                	jne    45e0 <timer_thread+0x3b0>
    asm volatile ("mfence" ::: "memory");
    4638:	0f ae f0             	mfence
    463b:	48 8d 3d 5f 2a 00 00 	lea    0x2a5f(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    4642:	e8 a9 dc ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    4647:	c7 45 44 00 00 00 00 	movl   $0x0,0x44(%rbp)
    464e:	48 8d 3d 53 2a 00 00 	lea    0x2a53(%rip),%rdi        # 70a8 <_IO_stdin_used+0xa8>
    4655:	e8 96 dc ff ff       	call   22f0 <puts@plt>
}
    465a:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    465f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4668:	75 40                	jne    46aa <timer_thread+0x47a>
    466a:	48 83 c4 58          	add    $0x58,%rsp
    466e:	31 c0                	xor    %eax,%eax
    4670:	5b                   	pop    %rbx
    4671:	5d                   	pop    %rbp
    4672:	41 5c                	pop    %r12
    4674:	41 5d                	pop    %r13
    4676:	41 5e                	pop    %r14
    4678:	41 5f                	pop    %r15
    467a:	c3                   	ret
    467b:	4c 89 ef             	mov    %r13,%rdi
    467e:	e8 6d dc ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4683:	48 8b 45 18          	mov    0x18(%rbp),%rax
    4687:	be 01 00 00 00       	mov    $0x1,%esi
    468c:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4690:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4694:	8b 78 60             	mov    0x60(%rax),%edi
    4697:	e8 64 dd ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    469c:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    469f:	0f 8f db fe ff ff    	jg     4580 <timer_thread+0x350>
    46a5:	e9 09 ff ff ff       	jmp    45b3 <timer_thread+0x383>
}
    46aa:	e8 81 dc ff ff       	call   2330 <__stack_chk_fail@plt>
    46af:	90                   	nop

00000000000046b0 <sendm.part.0>:
int sendm(struct BarrierTask *data) {
    46b0:	41 57                	push   %r15
    46b2:	41 56                	push   %r14
    46b4:	41 55                	push   %r13
    46b6:	41 54                	push   %r12
    46b8:	55                   	push   %rbp
    46b9:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    46ba:	8b af 40 01 00 00    	mov    0x140(%rdi),%ebp
    46c0:	85 ed                	test   %ebp,%ebp
    46c2:	0f 8e 7a 01 00 00    	jle    4842 <sendm.part.0+0x192>
        if (n == data->thread->real_thread_index) { continue; }
    46c8:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    46cf:	49 89 ff             	mov    %rdi,%r15
    46d2:	45 31 f6             	xor    %r14d,%r14d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    46d5:	45 31 ed             	xor    %r13d,%r13d
    46d8:	41 89 ec             	mov    %ebp,%r12d
        if (n == data->thread->real_thread_index) { continue; }
    46db:	8b 40 08             	mov    0x8(%rax),%eax
    46de:	89 44 24 cc          	mov    %eax,-0x34(%rsp)
    46e2:	48 8d 87 88 01 00 00 	lea    0x188(%rdi),%rax
    46e9:	48 89 44 24 e8       	mov    %rax,-0x18(%rsp)
    46ee:	48 8d 87 90 01 00 00 	lea    0x190(%rdi),%rax
    46f5:	48 89 44 24 f0       	mov    %rax,-0x10(%rsp)
    46fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4700:	44 39 6c 24 cc       	cmp    %r13d,-0x34(%rsp)
    4705:	0f 84 26 01 00 00    	je     4831 <sendm.part.0+0x181>
        struct Data *them = data->mailboxes[n].higher;
    470b:	49 8b 87 70 01 00 00 	mov    0x170(%r15),%rax
    4712:	4c 01 f0             	add    %r14,%rax
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    4715:	44 8b 40 30          	mov    0x30(%rax),%r8d
        struct Data *them = data->mailboxes[n].higher;
    4719:	48 8b 48 08          	mov    0x8(%rax),%rcx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    471d:	41 83 f8 02          	cmp    $0x2,%r8d
    4721:	0f 84 29 01 00 00    	je     4850 <sendm.part.0+0x1a0>
        for (; them->messages_count < min;) {
    4727:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    472e:	48 63 a9 88 00 00 00 	movslq 0x88(%rcx),%rbp
    4735:	48 39 ee             	cmp    %rbp,%rsi
    4738:	0f 8d f3 00 00 00    	jge    4831 <sendm.part.0+0x181>
    473e:	49 8b 87 08 01 00 00 	mov    0x108(%r15),%rax
    4745:	48 39 ee             	cmp    %rbp,%rsi
    4748:	49 89 eb             	mov    %rbp,%r11
          them->messages[them->messages_count++] = data->message; 
    474b:	48 8b 11             	mov    (%rcx),%rdx
    474e:	41 0f 9c c1          	setl   %r9b
    4752:	49 29 f3             	sub    %rsi,%r11
    4755:	48 89 44 24 d0       	mov    %rax,-0x30(%rsp)
    475a:	48 8b 81 08 03 00 00 	mov    0x308(%rcx),%rax
    4761:	49 8d 5b ff          	lea    -0x1(%r11),%rbx
    4765:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    476a:	48 89 44 24 d8       	mov    %rax,-0x28(%rsp)
    476f:	48 83 fb 02          	cmp    $0x2,%rbx
    4773:	0f 86 a7 01 00 00    	jbe    4920 <sendm.part.0+0x270>
    4779:	45 84 c9             	test   %r9b,%r9b
    477c:	0f 84 9e 01 00 00    	je     4920 <sendm.part.0+0x270>
    4782:	4c 8d 14 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r10
    478a:	4a 8d 04 12          	lea    (%rdx,%r10,1),%rax
    478e:	48 89 44 24 e0       	mov    %rax,-0x20(%rsp)
    4793:	49 89 c3             	mov    %rax,%r11
    4796:	48 8d 04 ea          	lea    (%rdx,%rbp,8),%rax
    479a:	48 39 44 24 e8       	cmp    %rax,-0x18(%rsp)
    479f:	0f 83 cb 00 00 00    	jae    4870 <sendm.part.0+0x1c0>
    47a5:	4c 89 d8             	mov    %r11,%rax
    47a8:	4c 8b 5c 24 f0       	mov    -0x10(%rsp),%r11
    47ad:	48 89 f7             	mov    %rsi,%rdi
    47b0:	4c 39 d8             	cmp    %r11,%rax
    47b3:	0f 83 b7 00 00 00    	jae    4870 <sendm.part.0+0x1c0>
    47b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    47c0:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    47c7:	48 89 04 fa          	mov    %rax,(%rdx,%rdi,8)
        for (; them->messages_count < min;) {
    47cb:	48 83 c7 01          	add    $0x1,%rdi
    47cf:	48 39 fd             	cmp    %rdi,%rbp
    47d2:	7f ec                	jg     47c0 <sendm.part.0+0x110>
    47d4:	0f 1f 40 00          	nopl   0x0(%rax)
    47d8:	31 ff                	xor    %edi,%edi
    47da:	45 84 c9             	test   %r9b,%r9b
    47dd:	4c 8b 5c 24 d0       	mov    -0x30(%rsp),%r11
    47e2:	48 0f 45 fb          	cmovne %rbx,%rdi
    47e6:	4d 8d 5c 3b 01       	lea    0x1(%r11,%rdi,1),%r11
    47eb:	48 8d 74 3e 01       	lea    0x1(%rsi,%rdi,1),%rsi
    47f0:	4d 89 9f 08 01 00 00 	mov    %r11,0x108(%r15)
    47f7:	4c 8b 5c 24 d8       	mov    -0x28(%rsp),%r11
    47fc:	48 89 b1 80 00 00 00 	mov    %rsi,0x80(%rcx)
    4803:	48 8d 34 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rsi
    480b:	bb 00 00 00 00       	mov    $0x0,%ebx
    4810:	48 0f 44 f3          	cmove  %rbx,%rsi
    4814:	4d 8d 5c 3b 01       	lea    0x1(%r11,%rdi,1),%r11
    4819:	4c 01 d2             	add    %r10,%rdx
    481c:	4c 89 99 08 03 00 00 	mov    %r11,0x308(%rcx)
    4823:	48 89 04 32          	mov    %rax,(%rdx,%rsi,1)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    4827:	41 83 f8 02          	cmp    $0x2,%r8d
    482b:	0f 84 bf 00 00 00    	je     48f0 <sendm.part.0+0x240>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    4831:	41 83 c5 01          	add    $0x1,%r13d
    4835:	49 83 c6 38          	add    $0x38,%r14
    4839:	45 39 e5             	cmp    %r12d,%r13d
    483c:	0f 85 be fe ff ff    	jne    4700 <sendm.part.0+0x50>
      asm volatile ("sfence" ::: "memory");
    4842:	0f ae f8             	sfence
}
    4845:	5b                   	pop    %rbx
    4846:	5d                   	pop    %rbp
    4847:	41 5c                	pop    %r12
    4849:	41 5d                	pop    %r13
    484b:	41 5e                	pop    %r14
    484d:	41 5f                	pop    %r15
    484f:	c3                   	ret
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    4850:	8b 81 00 01 00 00    	mov    0x100(%rcx),%eax
    4856:	83 f8 01             	cmp    $0x1,%eax
    4859:	0f 84 d1 00 00 00    	je     4930 <sendm.part.0+0x280>
        else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    485f:	85 c0                	test   %eax,%eax
    4861:	74 ce                	je     4831 <sendm.part.0+0x181>
    4863:	e9 bf fe ff ff       	jmp    4727 <sendm.part.0+0x77>
    4868:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4870:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    4875:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    487c:	48 8b 7c 24 e0       	mov    -0x20(%rsp),%rdi
    4881:	49 d1 eb             	shr    %r11
    4884:	66 48 0f 6e c0       	movq   %rax,%xmm0
    4889:	4c 89 dd             	mov    %r11,%rbp
    488c:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    4890:	48 c1 e5 04          	shl    $0x4,%rbp
    4894:	49 89 eb             	mov    %rbp,%r11
    4897:	48 01 fd             	add    %rdi,%rbp
    489a:	41 83 e3 10          	and    $0x10,%r11d
    489e:	74 11                	je     48b1 <sendm.part.0+0x201>
          them->messages[them->messages_count++] = data->message; 
    48a0:	0f 11 07             	movups %xmm0,(%rdi)
        for (; them->messages_count < min;) {
    48a3:	48 83 c7 10          	add    $0x10,%rdi
    48a7:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    48ac:	48 39 fd             	cmp    %rdi,%rbp
    48af:	74 1a                	je     48cb <sendm.part.0+0x21b>
    48b1:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
          them->messages[them->messages_count++] = data->message; 
    48b6:	0f 11 07             	movups %xmm0,(%rdi)
    48b9:	48 83 c7 20          	add    $0x20,%rdi
    48bd:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    48c1:	48 39 fd             	cmp    %rdi,%rbp
    48c4:	75 f0                	jne    48b6 <sendm.part.0+0x206>
    48c6:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    48cb:	4c 89 df             	mov    %r11,%rdi
    48ce:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    48d2:	48 01 f7             	add    %rsi,%rdi
    48d5:	41 83 e3 01          	and    $0x1,%r11d
    48d9:	0f 84 f9 fe ff ff    	je     47d8 <sendm.part.0+0x128>
          them->messages[them->messages_count++] = data->message; 
    48df:	49 8b 87 88 01 00 00 	mov    0x188(%r15),%rax
    48e6:	48 89 04 fa          	mov    %rax,(%rdx,%rdi,8)
        for (; them->messages_count < min;) {
    48ea:	e9 e9 fe ff ff       	jmp    47d8 <sendm.part.0+0x128>
    48ef:	90                   	nop
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available_sending == 1) {
    48f0:	83 b9 00 01 00 00 01 	cmpl   $0x1,0x100(%rcx)
    48f7:	0f 85 34 ff ff ff    	jne    4831 <sendm.part.0+0x181>
          them->available_sending = 0;
    48fd:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
          them->available_receiving = 1;
    4907:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
          them->finished_reading = 0;
    4911:	c7 81 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rcx)
    491b:	e9 11 ff ff ff       	jmp    4831 <sendm.part.0+0x181>
          them->messages[them->messages_count++] = data->message; 
    4920:	48 89 f7             	mov    %rsi,%rdi
    4923:	4c 8d 14 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r10
    492b:	e9 90 fe ff ff       	jmp    47c0 <sendm.part.0+0x110>
        for (; them->messages_count < min;) {
    4930:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    4937:	48 63 a9 88 00 00 00 	movslq 0x88(%rcx),%rbp
    493e:	48 39 f5             	cmp    %rsi,%rbp
    4941:	0f 8f f7 fd ff ff    	jg     473e <sendm.part.0+0x8e>
    4947:	eb b4                	jmp    48fd <sendm.part.0+0x24d>
    4949:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004950 <strtolower>:
void strtolower(char *str) {
    4950:	f3 0f 1e fa          	endbr64
    4954:	55                   	push   %rbp
    4955:	53                   	push   %rbx
    4956:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    495a:	48 0f be 1f          	movsbq (%rdi),%rbx
    495e:	84 db                	test   %bl,%bl
    4960:	74 24                	je     4986 <strtolower+0x36>
    4962:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4965:	e8 a6 db ff ff       	call   2510 <__ctype_tolower_loc@plt>
    496a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4970:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4973:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4977:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    497a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    497d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4982:	84 db                	test   %bl,%bl
    4984:	75 ea                	jne    4970 <strtolower+0x20>
}
    4986:	48 83 c4 08          	add    $0x8,%rsp
    498a:	5b                   	pop    %rbx
    498b:	5d                   	pop    %rbp
    498c:	c3                   	ret
    498d:	0f 1f 00             	nopl   (%rax)

0000000000004990 <zh_malloc>:
void *zh_malloc(size_t size) {
    4990:	f3 0f 1e fa          	endbr64
    4994:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4998:	e8 73 da ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    499d:	48 85 c0             	test   %rax,%rax
    49a0:	74 05                	je     49a7 <zh_malloc+0x17>
}
    49a2:	48 83 c4 08          	add    $0x8,%rsp
    49a6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    49a7:	48 8b 0d 72 56 00 00 	mov    0x5672(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    49ae:	ba 28 00 00 00       	mov    $0x28,%edx
    49b3:	be 01 00 00 00       	mov    $0x1,%esi
    49b8:	48 8d 3d d9 2b 00 00 	lea    0x2bd9(%rip),%rdi        # 7598 <_IO_stdin_used+0x598>
    49bf:	e8 fc da ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    49c4:	bf 01 00 00 00       	mov    $0x1,%edi
    49c9:	e8 d2 da ff ff       	call   24a0 <exit@plt>
    49ce:	66 90                	xchg   %ax,%ax

00000000000049d0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    49d0:	f3 0f 1e fa          	endbr64
    49d4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    49d5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    49da:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    49dd:	e8 7e d9 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    49e2:	48 85 c0             	test   %rax,%rax
    49e5:	74 11                	je     49f8 <get_filename_ext+0x28>
    49e7:	48 39 c3             	cmp    %rax,%rbx
    49ea:	74 0c                	je     49f8 <get_filename_ext+0x28>
    return dot + 1;
    49ec:	48 83 c0 01          	add    $0x1,%rax
}
    49f0:	5b                   	pop    %rbx
    49f1:	c3                   	ret
    49f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    49f8:	48 8d 05 f1 26 00 00 	lea    0x26f1(%rip),%rax        # 70f0 <_IO_stdin_used+0xf0>
}
    49ff:	5b                   	pop    %rbx
    4a00:	c3                   	ret
    4a01:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4a0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a10 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4a10:	f3 0f 1e fa          	endbr64
    4a14:	41 55                	push   %r13
    4a16:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a19:	48 89 fe             	mov    %rdi,%rsi
    4a1c:	41 54                	push   %r12
    4a1e:	55                   	push   %rbp
    4a1f:	48 89 d5             	mov    %rdx,%rbp
    4a22:	ba 00 04 00 00       	mov    $0x400,%edx
    4a27:	53                   	push   %rbx
    4a28:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4a2f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a38:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4a40:	31 c0                	xor    %eax,%eax
    4a42:	49 89 e4             	mov    %rsp,%r12
    4a45:	4c 89 e7             	mov    %r12,%rdi
    4a48:	e8 e3 d9 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    4a4d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4a52:	84 db                	test   %bl,%bl
    4a54:	74 24                	je     4a7a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4a56:	e8 b5 da ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4a5b:	48 8b 08             	mov    (%rax),%rcx
    4a5e:	4c 89 e0             	mov    %r12,%rax
    4a61:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4a68:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4a6b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4a6f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4a72:	48 0f be 18          	movsbq (%rax),%rbx
    4a76:	84 db                	test   %bl,%bl
    4a78:	75 ee                	jne    4a68 <send_headers+0x58>
    void *buf = malloc(size);
    4a7a:	bf 11 00 00 00       	mov    $0x11,%edi
    4a7f:	e8 8c d9 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4a84:	48 85 c0             	test   %rax,%rax
    4a87:	0f 84 7e 04 00 00    	je     4f0b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4a8d:	66 0f 6f 05 3b 31 00 00 	movdqa 0x313b(%rip),%xmm0        # 7bd0 <_IO_stdin_used+0xbd0>
    iov[0].iov_base = zh_malloc(slen);
    4a95:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4a99:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4a9e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4aa6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4aaa:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4aad:	e8 5e d9 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4ab2:	48 85 c0             	test   %rax,%rax
    4ab5:	0f 84 50 04 00 00    	je     4f0b <send_headers+0x4fb>
    4abb:	66 0f 6f 05 1d 31 00 00 	movdqa 0x311d(%rip),%xmm0        # 7be0 <_IO_stdin_used+0xbe0>
    iov[1].iov_base = zh_malloc(slen);
    4ac3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4ac7:	4c 89 e7             	mov    %r12,%rdi
    4aca:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4ad4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4adc:	0f 11 00             	movups %xmm0,(%rax)
    4adf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4ae3:	be 2e 00 00 00       	mov    $0x2e,%esi
    4ae8:	e8 73 d8 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4aed:	48 85 c0             	test   %rax,%rax
    4af0:	0f 84 ea 02 00 00    	je     4de0 <send_headers+0x3d0>
    4af6:	4c 39 e0             	cmp    %r12,%rax
    4af9:	0f 84 e1 02 00 00    	je     4de0 <send_headers+0x3d0>
    return dot + 1;
    4aff:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4b03:	48 8d 3d b4 25 00 00 	lea    0x25b4(%rip),%rdi        # 70be <_IO_stdin_used+0xbe>
    4b0a:	48 89 de             	mov    %rbx,%rsi
    4b0d:	e8 9e d8 ff ff       	call   23b0 <strcmp@plt>
    4b12:	85 c0                	test   %eax,%eax
    4b14:	75 20                	jne    4b36 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4b16:	66 0f 6f 05 d2 30 00 00 	movdqa 0x30d2(%rip),%xmm0        # 7bf0 <_IO_stdin_used+0xbf0>
    4b1e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b26:	66 0f 6f 05 d2 30 00 00 	movdqa 0x30d2(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    4b2e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4b36:	48 89 de             	mov    %rbx,%rsi
    4b39:	48 8d 3d 82 25 00 00 	lea    0x2582(%rip),%rdi        # 70c2 <_IO_stdin_used+0xc2>
    4b40:	e8 6b d8 ff ff       	call   23b0 <strcmp@plt>
    4b45:	85 c0                	test   %eax,%eax
    4b47:	75 20                	jne    4b69 <send_headers+0x159>
    4b49:	66 0f 6f 05 9f 30 00 00 	movdqa 0x309f(%rip),%xmm0        # 7bf0 <_IO_stdin_used+0xbf0>
    4b51:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b59:	66 0f 6f 05 9f 30 00 00 	movdqa 0x309f(%rip),%xmm0        # 7c00 <_IO_stdin_used+0xc00>
    4b61:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4b69:	48 89 de             	mov    %rbx,%rsi
    4b6c:	48 8d 3d 54 25 00 00 	lea    0x2554(%rip),%rdi        # 70c7 <_IO_stdin_used+0xc7>
    4b73:	e8 38 d8 ff ff       	call   23b0 <strcmp@plt>
    4b78:	85 c0                	test   %eax,%eax
    4b7a:	0f 84 10 02 00 00    	je     4d90 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4b80:	48 89 de             	mov    %rbx,%rsi
    4b83:	48 8d 3d 41 25 00 00 	lea    0x2541(%rip),%rdi        # 70cb <_IO_stdin_used+0xcb>
    4b8a:	e8 21 d8 ff ff       	call   23b0 <strcmp@plt>
    4b8f:	85 c0                	test   %eax,%eax
    4b91:	0f 84 a9 02 00 00    	je     4e40 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4b97:	48 89 de             	mov    %rbx,%rsi
    4b9a:	48 8d 3d 2e 25 00 00 	lea    0x252e(%rip),%rdi        # 70cf <_IO_stdin_used+0xcf>
    4ba1:	e8 0a d8 ff ff       	call   23b0 <strcmp@plt>
    4ba6:	85 c0                	test   %eax,%eax
    4ba8:	0f 84 6a 02 00 00    	je     4e18 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4bae:	48 89 de             	mov    %rbx,%rsi
    4bb1:	48 8d 3d 5a 25 00 00 	lea    0x255a(%rip),%rdi        # 7112 <_IO_stdin_used+0x112>
    4bb8:	e8 f3 d7 ff ff       	call   23b0 <strcmp@plt>
    4bbd:	85 c0                	test   %eax,%eax
    4bbf:	0f 84 2b 02 00 00    	je     4df0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4bc5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4bc8:	0f 84 52 01 00 00    	je     4d20 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4bce:	48 89 de             	mov    %rbx,%rsi
    4bd1:	48 8d 3d fb 24 00 00 	lea    0x24fb(%rip),%rdi        # 70d3 <_IO_stdin_used+0xd3>
    4bd8:	e8 d3 d7 ff ff       	call   23b0 <strcmp@plt>
    4bdd:	85 c0                	test   %eax,%eax
    4bdf:	0f 84 ab 02 00 00    	je     4e90 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4be5:	48 89 de             	mov    %rbx,%rsi
    4be8:	48 8d 3d e8 24 00 00 	lea    0x24e8(%rip),%rdi        # 70d7 <_IO_stdin_used+0xd7>
    4bef:	e8 bc d7 ff ff       	call   23b0 <strcmp@plt>
    4bf4:	85 c0                	test   %eax,%eax
    4bf6:	0f 84 6c 02 00 00    	je     4e68 <send_headers+0x458>
    slen = strlen(send_buffer);
    4bfc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4c04:	4c 89 e7             	mov    %r12,%rdi
    4c07:	e8 14 d7 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4c0c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4c0f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4c12:	e8 f9 d7 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4c17:	48 85 c0             	test   %rax,%rax
    4c1a:	0f 84 eb 02 00 00    	je     4f0b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4c20:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4c24:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4c28:	83 fb 08             	cmp    $0x8,%ebx
    4c2b:	0f 83 3f 01 00 00    	jae    4d70 <send_headers+0x360>
    4c31:	f6 c3 04             	test   $0x4,%bl
    4c34:	0f 85 7b 02 00 00    	jne    4eb5 <send_headers+0x4a5>
    4c3a:	85 db                	test   %ebx,%ebx
    4c3c:	74 13                	je     4c51 <send_headers+0x241>
    4c3e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4c46:	88 10                	mov    %dl,(%rax)
    4c48:	f6 c3 02             	test   $0x2,%bl
    4c4b:	0f 85 96 02 00 00    	jne    4ee7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4c51:	4d 89 e8             	mov    %r13,%r8
    4c54:	48 8d 0d 80 24 00 00 	lea    0x2480(%rip),%rcx        # 70db <_IO_stdin_used+0xdb>
    4c5b:	4c 89 e7             	mov    %r12,%rdi
    4c5e:	31 c0                	xor    %eax,%eax
    4c60:	ba 00 04 00 00       	mov    $0x400,%edx
    4c65:	be 01 00 00 00       	mov    $0x1,%esi
    4c6a:	e8 b1 d8 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4c6f:	4c 89 e7             	mov    %r12,%rdi
    4c72:	e8 a9 d6 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4c77:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4c7a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4c7d:	e8 8e d7 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4c82:	48 85 c0             	test   %rax,%rax
    4c85:	0f 84 80 02 00 00    	je     4f0b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4c8b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4c8f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4c93:	83 fb 08             	cmp    $0x8,%ebx
    4c96:	0f 83 1c 01 00 00    	jae    4db8 <send_headers+0x3a8>
    4c9c:	f6 c3 04             	test   $0x4,%bl
    4c9f:	0f 85 29 02 00 00    	jne    4ece <send_headers+0x4be>
    4ca5:	85 db                	test   %ebx,%ebx
    4ca7:	74 13                	je     4cbc <send_headers+0x2ac>
    4ca9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4cb1:	88 10                	mov    %dl,(%rax)
    4cb3:	f6 c3 02             	test   $0x2,%bl
    4cb6:	0f 85 3d 02 00 00    	jne    4ef9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4cbc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4cc1:	bf 02 00 00 00       	mov    $0x2,%edi
    4cc6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4cce:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4cd6:	e8 35 d7 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4cdb:	48 85 c0             	test   %rax,%rax
    4cde:	0f 84 27 02 00 00    	je     4f0b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ce4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4cec:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4cf0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4cf8:	66 89 10             	mov    %dx,(%rax)
}
    4cfb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4d03:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d0c:	0f 85 20 02 00 00    	jne    4f32 <send_headers+0x522>
    4d12:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4d19:	5b                   	pop    %rbx
    4d1a:	5d                   	pop    %rbp
    4d1b:	41 5c                	pop    %r12
    4d1d:	41 5d                	pop    %r13
    4d1f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4d20:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4d24:	0f 85 a4 fe ff ff    	jne    4bce <send_headers+0x1be>
    4d2a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4d2e:	0f 85 9a fe ff ff    	jne    4bce <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d34:	66 0f 6f 05 14 2f 00 00 	movdqa 0x2f14(%rip),%xmm0        # 7c50 <_IO_stdin_used+0xc50>
    4d3c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4d46:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4d4e:	66 0f 6f 05 0a 2f 00 00 	movdqa 0x2f0a(%rip),%xmm0        # 7c60 <_IO_stdin_used+0xc60>
    4d56:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4d5e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4d66:	e9 63 fe ff ff       	jmp    4bce <send_headers+0x1be>
    4d6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4d70:	89 da                	mov    %ebx,%edx
    4d72:	48 89 c7             	mov    %rax,%rdi
    4d75:	4c 89 e6             	mov    %r12,%rsi
    4d78:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4d7d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4d82:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4d85:	c1 e9 03             	shr    $0x3,%ecx
    4d88:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4d8b:	e9 c1 fe ff ff       	jmp    4c51 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d90:	66 0f 6f 05 58 2e 00 00 	movdqa 0x2e58(%rip),%xmm0        # 7bf0 <_IO_stdin_used+0xbf0>
    4d98:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4da0:	66 0f 6f 05 68 2e 00 00 	movdqa 0x2e68(%rip),%xmm0        # 7c10 <_IO_stdin_used+0xc10>
    4da8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4db0:	e9 cb fd ff ff       	jmp    4b80 <send_headers+0x170>
    4db5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4db8:	89 da                	mov    %ebx,%edx
    4dba:	48 89 c7             	mov    %rax,%rdi
    4dbd:	4c 89 e6             	mov    %r12,%rsi
    4dc0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4dc5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4dca:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4dcd:	c1 e9 03             	shr    $0x3,%ecx
    4dd0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4dd3:	e9 e4 fe ff ff       	jmp    4cbc <send_headers+0x2ac>
    4dd8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4de0:	48 8d 1d 09 23 00 00 	lea    0x2309(%rip),%rbx        # 70f0 <_IO_stdin_used+0xf0>
    4de7:	e9 94 fd ff ff       	jmp    4b80 <send_headers+0x170>
    4dec:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4df0:	66 0f 6f 05 38 2e 00 00 	movdqa 0x2e38(%rip),%xmm0        # 7c30 <_IO_stdin_used+0xc30>
    4df8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e00:	66 0f 6f 05 38 2e 00 00 	movdqa 0x2e38(%rip),%xmm0        # 7c40 <_IO_stdin_used+0xc40>
    4e08:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e10:	e9 b0 fd ff ff       	jmp    4bc5 <send_headers+0x1b5>
    4e15:	0f 1f 00             	nopl   (%rax)
    4e18:	66 0f 6f 05 10 2e 00 00 	movdqa 0x2e10(%rip),%xmm0        # 7c30 <_IO_stdin_used+0xc30>
    4e20:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e28:	66 0f 6f 05 10 2e 00 00 	movdqa 0x2e10(%rip),%xmm0        # 7c40 <_IO_stdin_used+0xc40>
    4e30:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e38:	e9 71 fd ff ff       	jmp    4bae <send_headers+0x19e>
    4e3d:	0f 1f 00             	nopl   (%rax)
    4e40:	66 0f 6f 05 a8 2d 00 00 	movdqa 0x2da8(%rip),%xmm0        # 7bf0 <_IO_stdin_used+0xbf0>
    4e48:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e50:	66 0f 6f 05 c8 2d 00 00 	movdqa 0x2dc8(%rip),%xmm0        # 7c20 <_IO_stdin_used+0xc20>
    4e58:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e60:	e9 32 fd ff ff       	jmp    4b97 <send_headers+0x187>
    4e65:	0f 1f 00             	nopl   (%rax)
    4e68:	66 0f 6f 05 c0 2d 00 00 	movdqa 0x2dc0(%rip),%xmm0        # 7c30 <_IO_stdin_used+0xc30>
    4e70:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e78:	66 0f 6f 05 00 2e 00 00 	movdqa 0x2e00(%rip),%xmm0        # 7c80 <_IO_stdin_used+0xc80>
    4e80:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4e88:	e9 6f fd ff ff       	jmp    4bfc <send_headers+0x1ec>
    4e8d:	0f 1f 00             	nopl   (%rax)
    4e90:	66 0f 6f 05 98 2d 00 00 	movdqa 0x2d98(%rip),%xmm0        # 7c30 <_IO_stdin_used+0xc30>
    4e98:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ea0:	66 0f 6f 05 c8 2d 00 00 	movdqa 0x2dc8(%rip),%xmm0        # 7c70 <_IO_stdin_used+0xc70>
    4ea8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4eb0:	e9 30 fd ff ff       	jmp    4be5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4eb5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4ebc:	89 db                	mov    %ebx,%ebx
    4ebe:	89 10                	mov    %edx,(%rax)
    4ec0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4ec5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4ec9:	e9 83 fd ff ff       	jmp    4c51 <send_headers+0x241>
    4ece:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4ed5:	89 db                	mov    %ebx,%ebx
    4ed7:	89 10                	mov    %edx,(%rax)
    4ed9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4ede:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4ee2:	e9 d5 fd ff ff       	jmp    4cbc <send_headers+0x2ac>
    4ee7:	89 db                	mov    %ebx,%ebx
    4ee9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4eef:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4ef4:	e9 58 fd ff ff       	jmp    4c51 <send_headers+0x241>
    4ef9:	89 db                	mov    %ebx,%ebx
    4efb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4f01:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4f06:	e9 b1 fd ff ff       	jmp    4cbc <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4f0b:	48 8b 0d 0e 51 00 00 	mov    0x510e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4f12:	ba 28 00 00 00       	mov    $0x28,%edx
    4f17:	be 01 00 00 00       	mov    $0x1,%esi
    4f1c:	48 8d 3d 75 26 00 00 	lea    0x2675(%rip),%rdi        # 7598 <_IO_stdin_used+0x598>
    4f23:	e8 98 d5 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4f28:	bf 01 00 00 00       	mov    $0x1,%edi
    4f2d:	e8 6e d5 ff ff       	call   24a0 <exit@plt>
}
    4f32:	e8 f9 d3 ff ff       	call   2330 <__stack_chk_fail@plt>
    4f37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004f40 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4f40:	f3 0f 1e fa          	endbr64
    4f44:	41 55                	push   %r13
    4f46:	49 89 d5             	mov    %rdx,%r13
    4f49:	41 54                	push   %r12
    4f4b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    4f4e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4f51:	55                   	push   %rbp
    4f52:	53                   	push   %rbx
    4f53:	48 89 f3             	mov    %rsi,%rbx
    4f56:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4f5a:	e8 b1 d4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4f5f:	48 85 c0             	test   %rax,%rax
    4f62:	74 6b                	je     4fcf <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4f64:	4c 89 e7             	mov    %r12,%rdi
    4f67:	48 89 c5             	mov    %rax,%rbp
    4f6a:	31 f6                	xor    %esi,%esi
    4f6c:	31 c0                	xor    %eax,%eax
    4f6e:	e8 0d d5 ff ff       	call   2480 <open@plt>
    4f73:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4f76:	85 c0                	test   %eax,%eax
    4f78:	0f 88 d8 d5 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4f7e:	48 89 da             	mov    %rbx,%rdx
    4f81:	48 89 ee             	mov    %rbp,%rsi
    4f84:	89 c7                	mov    %eax,%edi
    4f86:	e8 05 d4 ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    4f8b:	48 98                	cltq
    4f8d:	48 39 d8             	cmp    %rbx,%rax
    4f90:	7c 1e                	jl     4fb0 <copy_file_contents+0x70>
    close(fd);
    4f92:	44 89 e7             	mov    %r12d,%edi
    4f95:	e8 d6 d3 ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    4f9a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    4f9e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4fa2:	48 83 c4 08          	add    $0x8,%rsp
    4fa6:	5b                   	pop    %rbx
    4fa7:	5d                   	pop    %rbp
    4fa8:	41 5c                	pop    %r12
    4faa:	41 5d                	pop    %r13
    4fac:	c3                   	ret
    4fad:	0f 1f 00             	nopl   (%rax)
    4fb0:	48 8b 0d 69 50 00 00 	mov    0x5069(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4fb7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    4fbc:	be 01 00 00 00       	mov    $0x1,%esi
    4fc1:	48 8d 3d 29 21 00 00 	lea    0x2129(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4fc8:	e8 f3 d4 ff ff       	call   24c0 <fwrite@plt>
    4fcd:	eb c3                	jmp    4f92 <copy_file_contents+0x52>
    4fcf:	48 8b 0d 4a 50 00 00 	mov    0x504a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4fd6:	ba 28 00 00 00       	mov    $0x28,%edx
    4fdb:	be 01 00 00 00       	mov    $0x1,%esi
    4fe0:	48 8d 3d b1 25 00 00 	lea    0x25b1(%rip),%rdi        # 7598 <_IO_stdin_used+0x598>
    4fe7:	e8 d4 d4 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4fec:	bf 01 00 00 00       	mov    $0x1,%edi
    4ff1:	e8 aa d4 ff ff       	call   24a0 <exit@plt>
    4ff6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005000 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    5000:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    5004:	8b 46 44             	mov    0x44(%rsi),%eax
    5007:	48 89 fa             	mov    %rdi,%rdx
    500a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    500d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5013:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    5016:	48 8b 07             	mov    (%rdi),%rax
    5019:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    501c:	f6 c1 02             	test   $0x2,%cl
    501f:	74 00                	je     5021 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    5021:	89 f0                	mov    %esi,%eax
    5023:	44 29 c0             	sub    %r8d,%eax
    5026:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    5029:	0f 82 33 d5 ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    502f:	c1 e9 0a             	shr    $0xa,%ecx
    5032:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5036:	8b 47 44             	mov    0x44(%rdi),%eax
    5039:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    503c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    503f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    5042:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    5045:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5049:	d3 e0                	shl    %cl,%eax
    504b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    504e:	48 c1 e0 06          	shl    $0x6,%rax
    5052:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    5056:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    505c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    505f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    5063:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5069:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5071:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    5075:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    5078:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    507f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5087:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    508b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    508f:	e8 ac d2 ff ff       	call   2340 <io_uring_submit@plt>
}
    5094:	31 c0                	xor    %eax,%eax
    5096:	48 83 c4 08          	add    $0x8,%rsp
    509a:	c3                   	ret
    509b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000050a0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    50a0:	f3 0f 1e fa          	endbr64
    50a4:	41 55                	push   %r13
    50a6:	41 89 fd             	mov    %edi,%r13d
    50a9:	41 54                	push   %r12
    50ab:	55                   	push   %rbp
    50ac:	53                   	push   %rbx
    50ad:	48 89 f3             	mov    %rsi,%rbx
    50b0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    50b4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    50b7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    50bd:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    50c0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    50c3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    50c5:	f6 c1 02             	test   $0x2,%cl
    50c8:	74 00                	je     50ca <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    50ca:	89 c2                	mov    %eax,%edx
    50cc:	29 f2                	sub    %esi,%edx
    50ce:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    50d1:	0f 82 9b d4 ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50d7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    50da:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    50dd:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    50e0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    50e5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50e8:	23 6b 58             	and    0x58(%rbx),%ebp
    50eb:	d3 e5                	shl    %cl,%ebp
    50ed:	48 c1 e5 06          	shl    $0x6,%rbp
    50f1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    50f5:	e8 16 d3 ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    50fa:	be 01 00 00 00       	mov    $0x1,%esi
    50ff:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5104:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    5107:	e8 94 d2 ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    510c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    5111:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    5115:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    5118:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    511d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    5122:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    512b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    5133:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    5137:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    513b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    5142:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    514a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    514e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    5156:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    515e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    5162:	e8 d9 d1 ff ff       	call   2340 <io_uring_submit@plt>
}
    5167:	48 83 c4 08          	add    $0x8,%rsp
    516b:	31 c0                	xor    %eax,%eax
    516d:	5b                   	pop    %rbx
    516e:	5d                   	pop    %rbp
    516f:	41 5c                	pop    %r12
    5171:	41 5d                	pop    %r13
    5173:	c3                   	ret
    5174:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    517f:	90                   	nop

0000000000005180 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5180:	f3 0f 1e fa          	endbr64
    5184:	41 56                	push   %r14
    5186:	41 89 f6             	mov    %esi,%r14d
    5189:	41 55                	push   %r13
    518b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    518e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5193:	41 54                	push   %r12
    5195:	55                   	push   %rbp
    5196:	48 89 d5             	mov    %rdx,%rbp
    5199:	53                   	push   %rbx
    void *buf = malloc(size);
    519a:	e8 71 d2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    519f:	48 85 c0             	test   %rax,%rax
    51a2:	0f 84 dd 00 00 00    	je     5285 <_send_static_string_content+0x105>
    51a8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    51ab:	4c 89 ef             	mov    %r13,%rdi
    51ae:	e8 6d d1 ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    51b3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    51ba:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    51be:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    51c1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    51c4:	e8 47 d2 ff ff       	call   2410 <malloc@plt>
    51c9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    51cc:	48 85 c0             	test   %rax,%rax
    51cf:	0f 84 b0 00 00 00    	je     5285 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    51d5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    51d9:	4c 89 e2             	mov    %r12,%rdx
    51dc:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    51df:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    51e3:	e8 f8 d1 ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    51e8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    51eb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    51f1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    51f4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    51f8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    51fa:	f6 c1 02             	test   $0x2,%cl
    51fd:	0f 85 7d 00 00 00    	jne    5280 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    5203:	89 d0                	mov    %edx,%eax
    5205:	29 f0                	sub    %esi,%eax
    5207:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    520a:	0f 82 6c d3 ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5210:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5213:	8b 45 44             	mov    0x44(%rbp),%eax
    5216:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    5219:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    521c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    521f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    5222:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    5228:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    522c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    522e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    5231:	48 89 ef             	mov    %rbp,%rdi
    5234:	48 c1 e0 06          	shl    $0x6,%rax
    5238:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    523c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    523f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    5243:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5249:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5251:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    5255:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    5258:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    525f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5267:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    526b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    526f:	5b                   	pop    %rbx
    5270:	5d                   	pop    %rbp
    5271:	41 5c                	pop    %r12
    5273:	41 5d                	pop    %r13
    5275:	41 5e                	pop    %r14
    io_uring_submit(ring);
    5277:	e9 c4 d0 ff ff       	jmp    2340 <io_uring_submit@plt>
    527c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    5280:	e9 7e ff ff ff       	jmp    5203 <_send_static_string_content+0x83>
    5285:	48 8b 0d 94 4d 00 00 	mov    0x4d94(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    528c:	ba 28 00 00 00       	mov    $0x28,%edx
    5291:	be 01 00 00 00       	mov    $0x1,%esi
    5296:	48 8d 3d fb 22 00 00 	lea    0x22fb(%rip),%rdi        # 7598 <_IO_stdin_used+0x598>
    529d:	e8 1e d2 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    52a2:	bf 01 00 00 00       	mov    $0x1,%edi
    52a7:	e8 f4 d1 ff ff       	call   24a0 <exit@plt>
    52ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000052b0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    52b0:	f3 0f 1e fa          	endbr64
    52b4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    52b7:	89 fe                	mov    %edi,%esi
    52b9:	48 8b 3d 58 4d 00 00 	mov    0x4d58(%rip),%rdi        # a018 <unimplemented_content>
    52c0:	e9 bb fe ff ff       	jmp    5180 <_send_static_string_content>
    52c5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000052d0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    52d0:	f3 0f 1e fa          	endbr64
    52d4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    52d7:	89 fe                	mov    %edi,%esi
    52d9:	48 8b 3d 30 4d 00 00 	mov    0x4d30(%rip),%rdi        # a010 <http_404_content>
    52e0:	e9 9b fe ff ff       	jmp    5180 <_send_static_string_content>
    52e5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000052f0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    52f0:	f3 0f 1e fa          	endbr64
    52f4:	41 56                	push   %r14
    52f6:	41 55                	push   %r13
    52f8:	49 89 d5             	mov    %rdx,%r13
    52fb:	41 54                	push   %r12
    52fd:	41 89 f4             	mov    %esi,%r12d
    5300:	55                   	push   %rbp
    5301:	48 89 fd             	mov    %rdi,%rbp
    5304:	53                   	push   %rbx
    5305:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    530c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5315:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    531d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    531f:	e8 fc cf ff ff       	call   2320 <strlen@plt>
    5324:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    5329:	48 89 c3             	mov    %rax,%rbx
    532c:	0f 84 b6 00 00 00    	je     53e8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5332:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5337:	48 89 ee             	mov    %rbp,%rsi
    533a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    533e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5343:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    534b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5353:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    535e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5366:	e8 55 d0 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    536b:	48 89 e6             	mov    %rsp,%rsi
    536e:	4c 89 f7             	mov    %r14,%rdi
    5371:	e8 5a d0 ff ff       	call   23d0 <stat@plt>
    5376:	83 f8 ff             	cmp    $0xffffffff,%eax
    5379:	0f 84 d3 00 00 00    	je     5452 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    537f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5383:	25 00 f0 00 00       	and    $0xf000,%eax
    5388:	3d 00 80 00 00       	cmp    $0x8000,%eax
    538d:	0f 84 f5 00 00 00    	je     5488 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    5393:	48 8b 3d 76 4c 00 00 	mov    0x4c76(%rip),%rdi        # a010 <http_404_content>
    539a:	4c 89 ea             	mov    %r13,%rdx
    539d:	44 89 e6             	mov    %r12d,%esi
    53a0:	e8 db fd ff ff       	call   5180 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    53a5:	4c 89 f2             	mov    %r14,%rdx
    53a8:	bf 01 00 00 00       	mov    $0x1,%edi
    53ad:	31 c0                	xor    %eax,%eax
    53af:	48 8d 35 8b 1d 00 00 	lea    0x1d8b(%rip),%rsi        # 7141 <_IO_stdin_used+0x141>
    53b6:	e8 95 d0 ff ff       	call   2450 <__printf_chk@plt>
}
    53bb:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    53c3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    53cc:	0f 85 20 01 00 00    	jne    54f2 <handle_get_method+0x202>
    53d2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    53d9:	5b                   	pop    %rbx
    53da:	5d                   	pop    %rbp
    53db:	41 5c                	pop    %r12
    53dd:	41 5d                	pop    %r13
    53df:	41 5e                	pop    %r14
    53e1:	c3                   	ret
    53e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    53e8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    53ed:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    53f5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    53fa:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    53fd:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5405:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5408:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5410:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    541b:	e8 a0 cf ff ff       	call   23c0 <__memcpy_chk@plt>
    5420:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5425:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    542a:	48 8d 35 db 1c 00 00 	lea    0x1cdb(%rip),%rsi        # 710c <_IO_stdin_used+0x10c>
    5431:	48 29 d9             	sub    %rbx,%rcx
    5434:	ba 0b 00 00 00       	mov    $0xb,%edx
    5439:	e8 82 cf ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    543e:	48 89 e6             	mov    %rsp,%rsi
    5441:	4c 89 f7             	mov    %r14,%rdi
    5444:	e8 87 cf ff ff       	call   23d0 <stat@plt>
    5449:	83 f8 ff             	cmp    $0xffffffff,%eax
    544c:	0f 85 2d ff ff ff    	jne    537f <handle_get_method+0x8f>
    5452:	4c 89 f2             	mov    %r14,%rdx
    5455:	48 89 e9             	mov    %rbp,%rcx
    5458:	48 8d 35 b8 1c 00 00 	lea    0x1cb8(%rip),%rsi        # 7117 <_IO_stdin_used+0x117>
    545f:	31 c0                	xor    %eax,%eax
    5461:	bf 01 00 00 00       	mov    $0x1,%edi
    5466:	e8 e5 cf ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    546b:	48 8b 3d 9e 4b 00 00 	mov    0x4b9e(%rip),%rdi        # a010 <http_404_content>
    5472:	4c 89 ea             	mov    %r13,%rdx
    5475:	44 89 e6             	mov    %r12d,%esi
    5478:	e8 03 fd ff ff       	call   5180 <_send_static_string_content>
}
    547d:	e9 39 ff ff ff       	jmp    53bb <handle_get_method+0xcb>
    5482:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5488:	bf 70 00 00 00       	mov    $0x70,%edi
    548d:	e8 7e cf ff ff       	call   2410 <malloc@plt>
    5492:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5495:	48 85 c0             	test   %rax,%rax
    5498:	74 5d                	je     54f7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    549a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    549e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    54a3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    54a7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    54aa:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    54b1:	e8 5a f5 ff ff       	call   4a10 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    54b6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    54bb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    54bf:	4c 89 f7             	mov    %r14,%rdi
    54c2:	e8 79 fa ff ff       	call   4f40 <copy_file_contents>
    54c7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    54cc:	4c 89 f2             	mov    %r14,%rdx
    54cf:	31 c0                	xor    %eax,%eax
    54d1:	48 8d 35 57 1c 00 00 	lea    0x1c57(%rip),%rsi        # 712f <_IO_stdin_used+0x12f>
    54d8:	bf 01 00 00 00       	mov    $0x1,%edi
    54dd:	e8 6e cf ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    54e2:	4c 89 ee             	mov    %r13,%rsi
    54e5:	48 89 df             	mov    %rbx,%rdi
    54e8:	e8 13 fb ff ff       	call   5000 <add_write_request>
    54ed:	e9 c9 fe ff ff       	jmp    53bb <handle_get_method+0xcb>
}
    54f2:	e8 39 ce ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    54f7:	48 8b 0d 22 4b 00 00 	mov    0x4b22(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    54fe:	ba 28 00 00 00       	mov    $0x28,%edx
    5503:	be 01 00 00 00       	mov    $0x1,%esi
    5508:	48 8d 3d 89 20 00 00 	lea    0x2089(%rip),%rdi        # 7598 <_IO_stdin_used+0x598>
    550f:	e8 ac cf ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5514:	bf 01 00 00 00       	mov    $0x1,%edi
    5519:	e8 82 cf ff ff       	call   24a0 <exit@plt>
    551e:	66 90                	xchg   %ax,%ax

0000000000005520 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5520:	f3 0f 1e fa          	endbr64
    5524:	41 57                	push   %r15
    5526:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5528:	4c 8d 35 77 1b 00 00 	lea    0x1b77(%rip),%r14        # 70a6 <_IO_stdin_used+0xa6>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    552f:	41 55                	push   %r13
    5531:	49 89 d5             	mov    %rdx,%r13
    5534:	41 54                	push   %r12
    5536:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    5539:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    553c:	55                   	push   %rbp
    553d:	53                   	push   %rbx
    553e:	48 83 ec 18          	sub    $0x18,%rsp
    5542:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    554b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5550:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5552:	49 89 e7             	mov    %rsp,%r15
    5555:	4c 89 fa             	mov    %r15,%rdx
    5558:	e8 23 ce ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    555d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    5561:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    5564:	84 db                	test   %bl,%bl
    5566:	74 1d                	je     5585 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    5568:	e8 a3 cf ff ff       	call   2510 <__ctype_tolower_loc@plt>
    556d:	48 89 ea             	mov    %rbp,%rdx
    5570:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    5573:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    5577:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    557a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    557d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5581:	84 db                	test   %bl,%bl
    5583:	75 eb                	jne    5570 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    5585:	4c 89 fa             	mov    %r15,%rdx
    5588:	4c 89 f6             	mov    %r14,%rsi
    558b:	31 ff                	xor    %edi,%edi
    558d:	e8 ee cd ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5592:	48 8d 35 bb 1b 00 00 	lea    0x1bbb(%rip),%rsi        # 7154 <_IO_stdin_used+0x154>
    5599:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    559c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    559f:	e8 0c ce ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    55a4:	4c 89 ea             	mov    %r13,%rdx
    55a7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    55aa:	85 c0                	test   %eax,%eax
    55ac:	75 2a                	jne    55d8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    55ae:	48 89 df             	mov    %rbx,%rdi
    55b1:	e8 3a fd ff ff       	call   52f0 <handle_get_method>
}
    55b6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    55bb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    55c4:	75 20                	jne    55e6 <handle_http_method+0xc6>
    55c6:	48 83 c4 18          	add    $0x18,%rsp
    55ca:	5b                   	pop    %rbx
    55cb:	5d                   	pop    %rbp
    55cc:	41 5c                	pop    %r12
    55ce:	41 5d                	pop    %r13
    55d0:	41 5e                	pop    %r14
    55d2:	41 5f                	pop    %r15
    55d4:	c3                   	ret
    55d5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    55d8:	48 8b 3d 39 4a 00 00 	mov    0x4a39(%rip),%rdi        # a018 <unimplemented_content>
    55df:	e8 9c fb ff ff       	call   5180 <_send_static_string_content>
}
    55e4:	eb d0                	jmp    55b6 <handle_http_method+0x96>
    55e6:	e8 45 cd ff ff       	call   2330 <__stack_chk_fail@plt>
    55eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000055f0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    55f0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    55f4:	85 d2                	test   %edx,%edx
    55f6:	7e 38                	jle    5630 <get_line+0x40>
    55f8:	48 63 d2             	movslq %edx,%rdx
    55fb:	48 83 c7 01          	add    $0x1,%rdi
    55ff:	48 01 f2             	add    %rsi,%rdx
    5602:	eb 11                	jmp    5615 <get_line+0x25>
    5604:	0f 1f 40 00          	nopl   0x0(%rax)
    5608:	48 83 c6 01          	add    $0x1,%rsi
    560c:	48 83 c7 01          	add    $0x1,%rdi
    5610:	48 39 d6             	cmp    %rdx,%rsi
    5613:	74 1b                	je     5630 <get_line+0x40>
        dest[i] = src[i];
    5615:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5619:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    561b:	3c 0d                	cmp    $0xd,%al
    561d:	75 e9                	jne    5608 <get_line+0x18>
    561f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5622:	75 e4                	jne    5608 <get_line+0x18>
            dest[i] = '\0';
    5624:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5627:	31 c0                	xor    %eax,%eax
    5629:	c3                   	ret
    562a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5630:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5635:	c3                   	ret
    5636:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005640 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    5640:	f3 0f 1e fa          	endbr64
    5644:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    564b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    564f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5658:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5660:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5662:	49 89 e2             	mov    %rsp,%r10
    5665:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    566d:	4c 89 d0             	mov    %r10,%rax
    5670:	eb 13                	jmp    5685 <handle_client_request+0x45>
    5672:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5678:	48 83 c0 01          	add    $0x1,%rax
    567c:	48 83 c1 01          	add    $0x1,%rcx
    5680:	4c 39 c8             	cmp    %r9,%rax
    5683:	74 4b                	je     56d0 <handle_client_request+0x90>
        dest[i] = src[i];
    5685:	44 0f b6 01          	movzbl (%rcx),%r8d
    5689:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    568c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5690:	75 e6                	jne    5678 <handle_client_request+0x38>
    5692:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5696:	75 e0                	jne    5678 <handle_client_request+0x38>
            dest[i] = '\0';
    5698:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    569b:	8b 47 08             	mov    0x8(%rdi),%eax
    569e:	48 89 f2             	mov    %rsi,%rdx
    56a1:	4c 89 d7             	mov    %r10,%rdi
    56a4:	89 c6                	mov    %eax,%esi
    56a6:	e8 75 fe ff ff       	call   5520 <handle_http_method>
}
    56ab:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    56b3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    56bc:	75 39                	jne    56f7 <handle_client_request+0xb7>
    56be:	31 c0                	xor    %eax,%eax
    56c0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    56c7:	c3                   	ret
    56c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    56d0:	48 8b 0d 49 49 00 00 	mov    0x4949(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    56d7:	ba 12 00 00 00       	mov    $0x12,%edx
    56dc:	be 01 00 00 00       	mov    $0x1,%esi
    56e1:	48 8d 3d 70 1a 00 00 	lea    0x1a70(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    56e8:	e8 d3 cd ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    56ed:	bf 01 00 00 00       	mov    $0x1,%edi
    56f2:	e8 a9 cd ff ff       	call   24a0 <exit@plt>
}
    56f7:	e8 34 cc ff ff       	call   2330 <__stack_chk_fail@plt>
    56fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005700 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5700:	f3 0f 1e fa          	endbr64
    5704:	55                   	push   %rbp
    5705:	53                   	push   %rbx
    5706:	48 89 cb             	mov    %rcx,%rbx
    5709:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    570d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5710:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5713:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5719:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    571c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    571f:	f6 c1 02             	test   $0x2,%cl
    5722:	74 00                	je     5724 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    5724:	41 89 c0             	mov    %eax,%r8d
    5727:	45 29 c8             	sub    %r9d,%r8d
    572a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    572e:	0f 82 58 ce ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5734:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5737:	8b 6b 44             	mov    0x44(%rbx),%ebp
    573a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    573d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5740:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5743:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5747:	d3 e5                	shl    %cl,%ebp
    5749:	48 c1 e5 06          	shl    $0x6,%rbp
    574d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5751:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5754:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5759:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5760:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5764:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5768:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    5770:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    5778:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    577c:	e8 8f cc ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    5781:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5784:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    578a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    578e:	48 83 c4 08          	add    $0x8,%rsp
    5792:	5b                   	pop    %rbx
    5793:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5794:	e9 a7 cb ff ff       	jmp    2340 <io_uring_submit@plt>
    5799:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000057a0 <io_thread>:
void* io_thread(void *arg) {
    57a0:	f3 0f 1e fa          	endbr64
    57a4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    57a6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    57a8:	41 56                	push   %r14
    57aa:	41 55                	push   %r13
    57ac:	41 54                	push   %r12
    57ae:	55                   	push   %rbp
    57af:	48 89 fd             	mov    %rdi,%rbp
    57b2:	53                   	push   %rbx
    57b3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    57ba:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    57c3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    57cb:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    57cf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    57d4:	bf 00 01 00 00       	mov    $0x100,%edi
    57d9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    57dc:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    57e0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    57e5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    57ea:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    57ef:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    57f4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    57fc:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5801:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5809:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    580e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5816:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    581b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5823:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5828:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5830:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5835:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    583d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5845:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    584d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5855:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    585d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5865:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    586d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5875:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    587d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5885:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    588d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5894:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    589c:	e8 4f cb ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    58a1:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    58a5:	31 f6                	xor    %esi,%esi
    58a7:	e8 34 cc ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    58ac:	31 d2                	xor    %edx,%edx
    58ae:	be 01 00 00 00       	mov    $0x1,%esi
    58b3:	bf 02 00 00 00       	mov    $0x2,%edi
    58b8:	e8 73 cc ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    58bd:	83 f8 ff             	cmp    $0xffffffff,%eax
    58c0:	0f 84 08 cd ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    58c6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    58cb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    58d1:	89 c7                	mov    %eax,%edi
    58d3:	41 89 c4             	mov    %eax,%r12d
    58d6:	ba 02 00 00 00       	mov    $0x2,%edx
    58db:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    58e0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    58e8:	e8 13 ca ff ff       	call   2300 <setsockopt@plt>
    58ed:	85 c0                	test   %eax,%eax
    58ef:	0f 88 ad cc ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    58f5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    58fa:	ba 10 00 00 00       	mov    $0x10,%edx
    58ff:	44 89 e7             	mov    %r12d,%edi
    5902:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    590b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5913:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    591b:	e8 40 cb ff ff       	call   2460 <bind@plt>
    5920:	85 c0                	test   %eax,%eax
    5922:	0f 88 b2 cc ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5928:	be 0a 00 00 00       	mov    $0xa,%esi
    592d:	44 89 e7             	mov    %r12d,%edi
    5930:	e8 eb ca ff ff       	call   2420 <listen@plt>
    5935:	85 c0                	test   %eax,%eax
    5937:	0f 88 71 cc ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    593d:	ba db 18 00 00       	mov    $0x18db,%edx
    5942:	48 8d 35 54 18 00 00 	lea    0x1854(%rip),%rsi        # 719d <_IO_stdin_used+0x19d>
    5949:	bf 01 00 00 00       	mov    $0x1,%edi
    594e:	31 c0                	xor    %eax,%eax
    5950:	e8 fb ca ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5955:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    595a:	48 89 d9             	mov    %rbx,%rcx
    595d:	44 89 e7             	mov    %r12d,%edi
    5960:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5965:	48 89 c6             	mov    %rax,%rsi
    5968:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    596d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5972:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    597a:	e8 81 fd ff ff       	call   5700 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    597f:	bf 01 00 00 00       	mov    $0x1,%edi
    5984:	be 10 00 00 00       	mov    $0x10,%esi
    5989:	e8 12 ca ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    598e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5993:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5996:	e8 75 ca ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    599b:	48 85 c0             	test   %rax,%rax
    599e:	0f 84 ae 04 00 00    	je     5e52 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    59a4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    59a8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    59af:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    59b6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    59be:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    59c1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    59c6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    59c8:	f6 c1 02             	test   $0x2,%cl
    59cb:	0f 85 0f 04 00 00    	jne    5de0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    59d1:	89 d0                	mov    %edx,%eax
    59d3:	29 f0                	sub    %esi,%eax
    59d5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    59dc:	0f 82 e2 cb ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    59e2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    59e5:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    59e9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    59ed:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    59f0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    59f7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    59fa:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5a01:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a08:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5a0a:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5a0d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5a12:	48 c1 e0 06          	shl    $0x6,%rax
    5a16:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5a1e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5a24:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5a27:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5a2f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5a33:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5a3b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5a43:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5a47:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5a4b:	e8 f0 c8 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5a50:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5a54:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5a59:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5a61:	0f 85 d7 01 00 00    	jne    5c3e <io_thread+0x49e>
    5a67:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5a6c:	4d 89 ce             	mov    %r9,%r14
    5a6f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5a74:	0f 1f 40 00          	nopl   0x0(%rax)
    5a78:	48 8d 3d 34 17 00 00 	lea    0x1734(%rip),%rdi        # 71b3 <_IO_stdin_used+0x1b3>
    5a7f:	e8 6c c8 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5a84:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5a8b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5a92:	c1 e9 0b             	shr    $0xb,%ecx
    5a95:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5a98:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5aa0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5aa2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5aaa:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5aac:	39 d0                	cmp    %edx,%eax
    5aae:	74 36                	je     5ae6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5ab0:	89 f8                	mov    %edi,%eax
    5ab2:	21 d0                	and    %edx,%eax
    5ab4:	d3 e0                	shl    %cl,%eax
    5ab6:	48 c1 e0 04          	shl    $0x4,%rax
    5aba:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5ac2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5aca:	0f 85 a8 01 00 00    	jne    5c78 <io_thread+0x4d8>
    5ad0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5ad4:	0f 85 0e 03 00 00    	jne    5de8 <io_thread+0x648>
			if (cqe->res < 0)
    5ada:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5add:	83 c2 01             	add    $0x1,%edx
    5ae0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5ae2:	85 c0                	test   %eax,%eax
    5ae4:	79 b2                	jns    5a98 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5ae6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    5aef:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5af0:	45 31 c0             	xor    %r8d,%r8d
    5af3:	31 d2                	xor    %edx,%edx
    5af5:	b9 01 00 00 00       	mov    $0x1,%ecx
    5afa:	4c 89 f6             	mov    %r14,%rsi
    5afd:	48 89 df             	mov    %rbx,%rdi
    5b00:	e8 3b c9 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5b05:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5b08:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5b0d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5b11:	0f 84 e1 02 00 00    	je     5df8 <io_thread+0x658>
    5b17:	48 8d 3d bb 16 00 00 	lea    0x16bb(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    5b1e:	e8 cd c7 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5b23:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5b28:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5b2b:	45 85 ff             	test   %r15d,%r15d
    5b2e:	0f 88 62 ca ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    5b34:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5b37:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    5b3b:	85 c0                	test   %eax,%eax
    5b3d:	0f 88 d5 02 00 00    	js     5e18 <io_thread+0x678>
      switch (req->event_type) {
    5b43:	41 83 f8 01          	cmp    $0x1,%r8d
    5b47:	0f 84 7b 01 00 00    	je     5cc8 <io_thread+0x528>
    5b4d:	41 83 f8 02          	cmp    $0x2,%r8d
    5b51:	0f 84 a1 01 00 00    	je     5cf8 <io_thread+0x558>
    5b57:	45 85 c0             	test   %r8d,%r8d
    5b5a:	0f 85 50 01 00 00    	jne    5cb0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5b60:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5b65:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5b6a:	48 89 d9             	mov    %rbx,%rcx
    5b6d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5b71:	e8 8a fb ff ff       	call   5700 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5b76:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5b7b:	48 89 de             	mov    %rbx,%rsi
    5b7e:	8b 78 08             	mov    0x8(%rax),%edi
    5b81:	e8 1a f5 ff ff       	call   50a0 <add_read_request>
              free(req);
    5b86:	4c 89 e7             	mov    %r12,%rdi
    5b89:	e8 32 c7 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5b8e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5b93:	48 85 c0             	test   %rax,%rax
    5b96:	0f 85 14 01 00 00    	jne    5cb0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    5b9c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5ba3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5baa:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5bad:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5bb2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5bb4:	f6 c1 02             	test   $0x2,%cl
    5bb7:	74 00                	je     5bb9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5bb9:	89 d0                	mov    %edx,%eax
    5bbb:	29 f0                	sub    %esi,%eax
    5bbd:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5bc4:	0f 82 f0 c9 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5bca:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    5bcd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5bd2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5bd6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5bd9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5be0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5be3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5bea:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5bf1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5bf3:	8b 55 60             	mov    0x60(%rbp),%edx
    5bf6:	48 c1 e0 06          	shl    $0x6,%rax
    5bfa:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5c02:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5c08:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5c0b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5c13:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5c17:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5c1f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5c27:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5c2b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5c2f:	e8 0c c7 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5c34:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5c38:	0f 84 3a fe ff ff    	je     5a78 <io_thread+0x2d8>
    5c3e:	48 8d 3d cd 15 00 00 	lea    0x15cd(%rip),%rdi        # 7212 <_IO_stdin_used+0x212>
    5c45:	e8 a6 c6 ff ff       	call   22f0 <puts@plt>
}
    5c4a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5c52:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5c5b:	0f 85 18 02 00 00    	jne    5e79 <io_thread+0x6d9>
    5c61:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5c68:	31 c0                	xor    %eax,%eax
    5c6a:	5b                   	pop    %rbx
    5c6b:	5d                   	pop    %rbp
    5c6c:	41 5c                	pop    %r12
    5c6e:	41 5d                	pop    %r13
    5c70:	41 5e                	pop    %r14
    5c72:	41 5f                	pop    %r15
    5c74:	c3                   	ret
    5c75:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5c78:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5c7d:	48 85 c0             	test   %rax,%rax
    5c80:	0f 84 6a fe ff ff    	je     5af0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5c86:	48 83 38 01          	cmpq   $0x1,(%rax)
    5c8a:	0f 84 68 01 00 00    	je     5df8 <io_thread+0x658>
    5c90:	48 8d 3d 42 15 00 00 	lea    0x1542(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    5c97:	e8 54 c6 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5c9c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5ca1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5ca4:	e9 8b fe ff ff       	jmp    5b34 <io_thread+0x394>
    5ca9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5cb0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5cb8:	8b 02                	mov    (%rdx),%eax
    5cba:	83 c0 01             	add    $0x1,%eax
    5cbd:	89 02                	mov    %eax,(%rdx)
}
    5cbf:	e9 d8 fe ff ff       	jmp    5b9c <io_thread+0x3fc>
    5cc4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5cc8:	85 c0                	test   %eax,%eax
    5cca:	75 74                	jne    5d40 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5ccc:	48 8b 0d 4d 43 00 00 	mov    0x434d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5cd3:	ba 0f 00 00 00       	mov    $0xf,%edx
    5cd8:	be 01 00 00 00       	mov    $0x1,%esi
    5cdd:	48 8d 3d 1e 15 00 00 	lea    0x151e(%rip),%rdi        # 7202 <_IO_stdin_used+0x202>
    5ce4:	e8 d7 c7 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5ce9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5cee:	e9 a0 fe ff ff       	jmp    5b93 <io_thread+0x3f3>
    5cf3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5cf8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5cfd:	45 31 ff             	xor    %r15d,%r15d
    5d00:	85 c0                	test   %eax,%eax
    5d02:	7e 20                	jle    5d24 <io_thread+0x584>
    5d04:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5d08:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5d0b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    5d0f:	48 c1 e0 04          	shl    $0x4,%rax
    5d13:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5d18:	e8 a3 c5 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5d1d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5d22:	7f e4                	jg     5d08 <io_thread+0x568>
              close(req->client_socket);
    5d24:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5d29:	e8 42 c6 ff ff       	call   2370 <close@plt>
              free(req);
    5d2e:	4c 89 e7             	mov    %r12,%rdi
    5d31:	e8 8a c5 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5d36:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5d3b:	e9 53 fe ff ff       	jmp    5b93 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5d40:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5d45:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5d4a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5d52:	eb 11                	jmp    5d65 <io_thread+0x5c5>
    5d54:	0f 1f 40 00          	nopl   0x0(%rax)
    5d58:	48 83 c0 01          	add    $0x1,%rax
    5d5c:	48 83 c2 01          	add    $0x1,%rdx
    5d60:	48 39 c6             	cmp    %rax,%rsi
    5d63:	74 4b                	je     5db0 <io_thread+0x610>
        dest[i] = src[i];
    5d65:	0f b6 0a             	movzbl (%rdx),%ecx
    5d68:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5d6a:	80 f9 0d             	cmp    $0xd,%cl
    5d6d:	75 e9                	jne    5d58 <io_thread+0x5b8>
    5d6f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5d73:	75 e3                	jne    5d58 <io_thread+0x5b8>
            dest[i] = '\0';
    5d75:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5d78:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    5d7d:	48 89 da             	mov    %rbx,%rdx
    5d80:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5d85:	e8 96 f7 ff ff       	call   5520 <handle_http_method>
              free(req->iov[0].iov_base);
    5d8a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    5d8f:	e8 2c c5 ff ff       	call   22c0 <free@plt>
              free(req);
    5d94:	4c 89 e7             	mov    %r12,%rdi
    5d97:	e8 24 c5 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5d9c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5da1:	e9 ed fd ff ff       	jmp    5b93 <io_thread+0x3f3>
    5da6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5db0:	48 8b 0d 69 42 00 00 	mov    0x4269(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5db7:	ba 12 00 00 00       	mov    $0x12,%edx
    5dbc:	be 01 00 00 00       	mov    $0x1,%esi
    5dc1:	48 8d 3d 90 13 00 00 	lea    0x1390(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    5dc8:	e8 f3 c6 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5dcd:	bf 01 00 00 00       	mov    $0x1,%edi
    5dd2:	e8 c9 c6 ff ff       	call   24a0 <exit@plt>
    5dd7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5de0:	e9 ec fb ff ff       	jmp    59d1 <io_thread+0x231>
    5de5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5de8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    5ded:	e9 94 fe ff ff       	jmp    5c86 <io_thread+0x4e6>
    5df2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5df8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5e00:	48 8d 3d be 13 00 00 	lea    0x13be(%rip),%rdi        # 71c5 <_IO_stdin_used+0x1c5>
    5e07:	8b 02                	mov    (%rdx),%eax
    5e09:	83 c0 01             	add    $0x1,%eax
    5e0c:	89 02                	mov    %eax,(%rdx)
    5e0e:	e8 dd c4 ff ff       	call   22f0 <puts@plt>
    5e13:	e9 26 fe ff ff       	jmp    5c3e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5e18:	f7 d8                	neg    %eax
    5e1a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5e1f:	89 c7                	mov    %eax,%edi
    5e21:	e8 da c6 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5e26:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5e2b:	be 01 00 00 00       	mov    $0x1,%esi
    5e30:	48 8b 3d e9 41 00 00 	mov    0x41e9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5e37:	48 89 c1             	mov    %rax,%rcx
    5e3a:	48 8d 15 87 17 00 00 	lea    0x1787(%rip),%rdx        # 75c8 <_IO_stdin_used+0x5c8>
    5e41:	31 c0                	xor    %eax,%eax
    5e43:	e8 88 c6 ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5e48:	bf 01 00 00 00       	mov    $0x1,%edi
    5e4d:	e8 4e c6 ff ff       	call   24a0 <exit@plt>
    5e52:	48 8b 0d c7 41 00 00 	mov    0x41c7(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5e59:	ba 28 00 00 00       	mov    $0x28,%edx
    5e5e:	be 01 00 00 00       	mov    $0x1,%esi
    5e63:	48 8d 3d 2e 17 00 00 	lea    0x172e(%rip),%rdi        # 7598 <_IO_stdin_used+0x598>
    5e6a:	e8 51 c6 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5e6f:	bf 01 00 00 00       	mov    $0x1,%edi
    5e74:	e8 27 c6 ff ff       	call   24a0 <exit@plt>
}
    5e79:	e8 b2 c4 ff ff       	call   2330 <__stack_chk_fail@plt>
    5e7e:	66 90                	xchg   %ax,%ax

0000000000005e80 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5e80:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5e84:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5e8b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5e91:	85 c9                	test   %ecx,%ecx
    5e93:	0f 8e ea 00 00 00    	jle    5f83 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    5e99:	41 56                	push   %r14
    5e9b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5e9d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    5ea0:	41 54                	push   %r12
    5ea2:	49 89 fc             	mov    %rdi,%r12
    5ea5:	55                   	push   %rbp
    5ea6:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5ea7:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5eab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5eb0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    5eb4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    5ebc:	31 db                	xor    %ebx,%ebx
    5ebe:	8b 10                	mov    (%rax),%edx
    5ec0:	85 d2                	test   %edx,%edx
    5ec2:	7e 26                	jle    5eea <barriered_work_ingest+0x6a>
    5ec4:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    5ec8:	48 89 dd             	mov    %rbx,%rbp
    5ecb:	48 c1 e5 08          	shl    $0x8,%rbp
    5ecf:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    5ed3:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    5eda:	74 24                	je     5f00 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5edc:	48 83 c3 01          	add    $0x1,%rbx
    5ee0:	39 da                	cmp    %ebx,%edx
    5ee2:	7f e4                	jg     5ec8 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5ee4:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5eea:	49 83 c5 01          	add    $0x1,%r13
    5eee:	44 39 e9             	cmp    %r13d,%ecx
    5ef1:	7f bd                	jg     5eb0 <barriered_work_ingest+0x30>
}
    5ef3:	5b                   	pop    %rbx
    5ef4:	31 c0                	xor    %eax,%eax
    5ef6:	5d                   	pop    %rbp
    5ef7:	41 5c                	pop    %r12
    5ef9:	41 5d                	pop    %r13
    5efb:	41 5e                	pop    %r14
    5efd:	c3                   	ret
    5efe:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    5f00:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5f09:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5f10:	bf 04 00 00 00       	mov    $0x4,%edi
    5f15:	48 c1 e6 05          	shl    $0x5,%rsi
    5f19:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5f20:	48 83 c6 10          	add    $0x10,%rsi
    5f24:	e8 e7 c3 ff ff       	call   2310 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5f29:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5f31:	48 8b 40 50          	mov    0x50(%rax),%rax
    5f35:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5f39:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    5f3d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5f47:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    5f4d:	83 c0 01             	add    $0x1,%eax
    5f50:	99                   	cltd
    5f51:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5f57:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    5f5d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5f60:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5f68:	48 83 c3 01          	add    $0x1,%rbx
    5f6c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5f70:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5f74:	8b 10                	mov    (%rax),%edx
    5f76:	39 da                	cmp    %ebx,%edx
    5f78:	0f 8f 46 ff ff ff    	jg     5ec4 <barriered_work_ingest+0x44>
    5f7e:	e9 61 ff ff ff       	jmp    5ee4 <barriered_work_ingest+0x64>
}
    5f83:	31 c0                	xor    %eax,%eax
    5f85:	c3                   	ret
    5f86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005f90 <barriered_thread>:
void* barriered_thread(void *arg) {
    5f90:	f3 0f 1e fa          	endbr64
    5f94:	41 56                	push   %r14
    5f96:	41 55                	push   %r13
    5f98:	41 54                	push   %r12
  int t = 0;
    5f9a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    5f9d:	55                   	push   %rbp
  int waiting = 0;
    5f9e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    5fa0:	53                   	push   %rbx
    5fa1:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    5fa4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5fa8:	0f 85 74 02 00 00    	jne    6222 <barriered_thread+0x292>
    if (t >= data->task_count) {
    5fae:	8b 43 40             	mov    0x40(%rbx),%eax
    5fb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5fb8:	41 39 c4             	cmp    %eax,%r12d
    5fbb:	0f 8d 6f 01 00 00    	jge    6130 <barriered_thread+0x1a0>
    5fc1:	49 63 fc             	movslq %r12d,%rdi
    5fc4:	48 c1 e7 09          	shl    $0x9,%rdi
    5fc8:	49 89 fd             	mov    %rdi,%r13
    5fcb:	eb 32                	jmp    5fff <barriered_thread+0x6f>
    5fcd:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5fd0:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5fd4:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5fd8:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5fdc:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5fe0:	4c 01 ef             	add    %r13,%rdi
    5fe3:	e8 98 fe ff ff       	call   5e80 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    5fe8:	8b 43 40             	mov    0x40(%rbx),%eax
    5feb:	41 83 c4 01          	add    $0x1,%r12d
    5fef:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    5ff6:	44 39 e0             	cmp    %r12d,%eax
    5ff9:	0f 8e 19 02 00 00    	jle    6218 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    5fff:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6003:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    6007:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    600e:	75 c0                	jne    5fd0 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6010:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    6014:	83 e8 01             	sub    $0x1,%eax
    6017:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    601c:	45 85 e4             	test   %r12d,%r12d
    601f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6022:	45 85 c0             	test   %r8d,%r8d
    6025:	0f 8e 2d 01 00 00    	jle    6158 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    602b:	48 63 c8             	movslq %eax,%rcx
    602e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6032:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    6035:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    603b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    6042:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    6046:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    6049:	45 31 f6             	xor    %r14d,%r14d
    604c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6050:	48 8b 10             	mov    (%rax),%rdx
    6053:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6057:	49 01 cb             	add    %rcx,%r11
    605a:	4c 89 da             	mov    %r11,%rdx
    605d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6064:	75 04                	jne    606a <barriered_thread+0xda>
            arrived++;
    6066:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    606a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    6070:	75 04                	jne    6076 <barriered_thread+0xe6>
            prearrive++;
    6072:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6076:	48 83 c0 08          	add    $0x8,%rax
    607a:	48 39 c6             	cmp    %rax,%rsi
    607d:	75 d1                	jne    6050 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    607f:	45 85 d2             	test   %r10d,%r10d
    6082:	0f 84 c0 00 00 00    	je     6148 <barriered_thread+0x1b8>
    6088:	45 39 d0             	cmp    %r10d,%r8d
    608b:	0f 84 b7 00 00 00    	je     6148 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    6091:	45 85 f6             	test   %r14d,%r14d
    6094:	74 0a                	je     60a0 <barriered_thread+0x110>
    6096:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    609a:	0f 85 ae 01 00 00    	jne    624e <barriered_thread+0x2be>
    60a0:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    60a4:	4c 01 ea             	add    %r13,%rdx
    60a7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    60ae:	45 85 e4             	test   %r12d,%r12d
    60b1:	75 14                	jne    60c7 <barriered_thread+0x137>
    60b3:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    60ba:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    60c1:	0f 8c 69 01 00 00    	jl     6230 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    60c7:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    60cb:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    60cf:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    60d9:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    60dd:	48 8b 78 38          	mov    0x38(%rax),%rdi
    60e1:	4c 01 ef             	add    %r13,%rdi
    60e4:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    60ea:	48 8b 43 38          	mov    0x38(%rbx),%rax
    60ee:	4c 01 e8             	add    %r13,%rax
    60f1:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    60f8:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    60fb:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6100:	83 e8 01             	sub    $0x1,%eax
    6103:	44 39 e0             	cmp    %r12d,%eax
    6106:	0f 84 a4 00 00 00    	je     61b0 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    610c:	0f ae f8             	sfence
          if (waiting == 0) {
    610f:	85 ed                	test   %ebp,%ebp
    6111:	0f 84 d1 00 00 00    	je     61e8 <barriered_thread+0x258>
        int arrived = 0; 
    6117:	bd 01 00 00 00       	mov    $0x1,%ebp
    611c:	e9 c7 fe ff ff       	jmp    5fe8 <barriered_thread+0x58>
  while (data->running == 1) {
    6121:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6125:	0f 85 f7 00 00 00    	jne    6222 <barriered_thread+0x292>
    612b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    6130:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    6138:	85 c0                	test   %eax,%eax
    613a:	7e e5                	jle    6121 <barriered_thread+0x191>
    613c:	45 31 e4             	xor    %r12d,%r12d
    613f:	e9 7d fe ff ff       	jmp    5fc1 <barriered_thread+0x31>
    6144:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6148:	83 fd 01             	cmp    $0x1,%ebp
    614b:	74 1b                	je     6168 <barriered_thread+0x1d8>
        int arrived = 0; 
    614d:	31 ed                	xor    %ebp,%ebp
    614f:	e9 3d ff ff ff       	jmp    6091 <barriered_thread+0x101>
    6154:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6158:	83 fd 01             	cmp    $0x1,%ebp
    615b:	0f 85 43 ff ff ff    	jne    60a4 <barriered_thread+0x114>
        int arrived = 0; 
    6161:	45 31 f6             	xor    %r14d,%r14d
    6164:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    6168:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    616f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    6174:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    6176:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    617a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6181:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    6186:	e8 85 c1 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    618b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6192:	48 83 c0 01          	add    $0x1,%rax
    6196:	48 99                	cqto
    6198:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    619f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    61a6:	e9 e6 fe ff ff       	jmp    6091 <barriered_thread+0x101>
    61ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    61b0:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    61b7:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    61be:	0f 8d 48 ff ff ff    	jge    610c <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    61c4:	48 c1 e6 04          	shl    $0x4,%rsi
    61c8:	bf 04 00 00 00       	mov    $0x4,%edi
    61cd:	48 03 73 70          	add    0x70(%rbx),%rsi
    61d1:	e8 3a c1 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    61d6:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    61de:	e9 29 ff ff ff       	jmp    610c <barriered_thread+0x17c>
    61e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    61e8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    61ef:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    61f4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    61f8:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    61ff:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    6203:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    6207:	e8 04 c1 ff ff       	call   2310 <clock_gettime@plt>
            waiting = 1;
    620c:	e9 06 ff ff ff       	jmp    6117 <barriered_thread+0x187>
    6211:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    6218:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    621c:	0f 84 96 fd ff ff    	je     5fb8 <barriered_thread+0x28>
}
    6222:	5b                   	pop    %rbx
    6223:	31 c0                	xor    %eax,%eax
    6225:	5d                   	pop    %rbp
    6226:	41 5c                	pop    %r12
    6228:	41 5d                	pop    %r13
    622a:	41 5e                	pop    %r14
    622c:	c3                   	ret
    622d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    6230:	48 c1 e6 04          	shl    $0x4,%rsi
    6234:	bf 04 00 00 00       	mov    $0x4,%edi
    6239:	48 03 73 68          	add    0x68(%rbx),%rsi
    623d:	e8 ce c0 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    6242:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6246:	4c 01 ea             	add    %r13,%rdx
    6249:	e9 79 fe ff ff       	jmp    60c7 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    624e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6252:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6256:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    625a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    625e:	4c 01 ef             	add    %r13,%rdi
    6261:	e8 1a fc ff ff       	call   5e80 <barriered_work_ingest>
          break;
    6266:	e9 39 fd ff ff       	jmp    5fa4 <barriered_thread+0x14>
    626b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006270 <receive>:
int receive(struct BarrierTask *data) {
    6270:	f3 0f 1e fa          	endbr64
    6274:	41 57                	push   %r15
    6276:	41 56                	push   %r14
    6278:	41 55                	push   %r13
    627a:	41 54                	push   %r12
    627c:	55                   	push   %rbp
    627d:	53                   	push   %rbx
    627e:	48 83 ec 18          	sub    $0x18,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6282:	44 8b b7 40 01 00 00 	mov    0x140(%rdi),%r14d
    6289:	45 85 f6             	test   %r14d,%r14d
    628c:	0f 8e 17 01 00 00    	jle    63a9 <receive+0x139>
    if (n == data->thread->real_thread_index) { continue; }
    6292:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    6299:	48 89 f9             	mov    %rdi,%rcx
    629c:	45 31 e4             	xor    %r12d,%r12d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    629f:	31 db                	xor    %ebx,%ebx
    if (n == data->thread->real_thread_index) { continue; }
    62a1:	48 63 68 08          	movslq 0x8(%rax),%rbp
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    62a5:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    if (n == data->thread->real_thread_index) { continue; }
    62aa:	49 89 ef             	mov    %rbp,%r15
    62ad:	0f 1f 00             	nopl   (%rax)
    62b0:	41 39 df             	cmp    %ebx,%r15d
    62b3:	0f 84 e0 00 00 00    	je     6399 <receive+0x129>
    struct Data *me = data->mailboxes[n].lower;
    62b9:	48 8b 81 70 01 00 00 	mov    0x170(%rcx),%rax
    62c0:	4c 01 e0             	add    %r12,%rax
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    62c3:	44 8b 68 30          	mov    0x30(%rax),%r13d
    struct Data *me = data->mailboxes[n].lower;
    62c7:	48 8b 10             	mov    (%rax),%rdx
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    62ca:	41 83 fd 02          	cmp    $0x2,%r13d
    62ce:	0f 84 24 01 00 00    	je     63f8 <receive+0x188>
    for (int x = 0 ; x < me->messages_count ; x++) {
    62d4:	48 83 ba 80 00 00 00 00 	cmpq   $0x0,0x80(%rdx)
    62dc:	0f 8e 3b 01 00 00    	jle    641d <receive+0x1ad>
      data->sends++;
    62e2:	4c 8b 81 78 01 00 00 	mov    0x178(%rcx),%r8
      data->n++;
    62e9:	48 8b b9 08 01 00 00 	mov    0x108(%rcx),%rdi
      me->received++;
    62f0:	31 c0                	xor    %eax,%eax
    62f2:	48 8b b2 10 03 00 00 	mov    0x310(%rdx),%rsi
      if (me->messages[x]->group == data->group) {
    62f9:	4c 8b 1a             	mov    (%rdx),%r11
    62fc:	4d 8d 48 01          	lea    0x1(%r8),%r9
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    6300:	4c 63 51 04          	movslq 0x4(%rcx),%r10
    6304:	4c 8d 47 01          	lea    0x1(%rdi),%r8
    6308:	48 8d 7e 01          	lea    0x1(%rsi),%rdi
    630c:	eb 0f                	jmp    631d <receive+0xad>
    630e:	66 90                	xchg   %ax,%ax
    for (int x = 0 ; x < me->messages_count ; x++) {
    6310:	48 83 c0 01          	add    $0x1,%rax
    6314:	48 39 82 80 00 00 00 	cmp    %rax,0x80(%rdx)
    631b:	7e 6b                	jle    6388 <receive+0x118>
      data->sends++;
    631d:	49 8d 34 01          	lea    (%r9,%rax,1),%rsi
    6321:	48 89 b1 78 01 00 00 	mov    %rsi,0x178(%rcx)
      data->n++;
    6328:	49 8d 34 00          	lea    (%r8,%rax,1),%rsi
    632c:	48 89 b1 08 01 00 00 	mov    %rsi,0x108(%rcx)
      me->received++;
    6333:	48 8d 34 07          	lea    (%rdi,%rax,1),%rsi
    6337:	48 89 b2 10 03 00 00 	mov    %rsi,0x310(%rdx)
      if (me->messages[x]->group == data->group) {
    633e:	49 8b 34 c3          	mov    (%r11,%rax,8),%rsi
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    6342:	4c 39 56 10          	cmp    %r10,0x10(%rsi)
    6346:	75 c8                	jne    6310 <receive+0xa0>
    6348:	48 39 6e 08          	cmp    %rbp,0x8(%rsi)
    634c:	75 c2                	jne    6310 <receive+0xa0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    634e:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6353:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6355:	bf 01 00 00 00       	mov    $0x1,%edi
    635a:	ba 01 00 00 00       	mov    $0x1,%edx
    635f:	48 8d 35 8a 12 00 00 	lea    0x128a(%rip),%rsi        # 75f0 <_IO_stdin_used+0x5f0>
    6366:	48 63 40 04          	movslq 0x4(%rax),%rax
    636a:	48 39 e8             	cmp    %rbp,%rax
    636d:	0f 94 c1             	sete   %cl
    6370:	31 c0                	xor    %eax,%eax
    6372:	e8 d9 c0 ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    6377:	bf 01 00 00 00       	mov    $0x1,%edi
    637c:	e8 1f c1 ff ff       	call   24a0 <exit@plt>
    6381:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    me->messages_count = 0;
    6388:	48 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rdx)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    6393:	41 83 fd 02          	cmp    $0x2,%r13d
    6397:	74 27                	je     63c0 <receive+0x150>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6399:	83 c3 01             	add    $0x1,%ebx
    639c:	49 83 c4 38          	add    $0x38,%r12
    63a0:	44 39 f3             	cmp    %r14d,%ebx
    63a3:	0f 85 07 ff ff ff    	jne    62b0 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    63a9:	0f ae f8             	sfence
}
    63ac:	48 83 c4 18          	add    $0x18,%rsp
    63b0:	31 c0                	xor    %eax,%eax
    63b2:	5b                   	pop    %rbx
    63b3:	5d                   	pop    %rbp
    63b4:	41 5c                	pop    %r12
    63b6:	41 5d                	pop    %r13
    63b8:	41 5e                	pop    %r14
    63ba:	41 5f                	pop    %r15
    63bc:	c3                   	ret
    63bd:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    63c0:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    63c6:	83 f8 01             	cmp    $0x1,%eax
    63c9:	75 ce                	jne    6399 <receive+0x129>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    63cb:	83 c3 01             	add    $0x1,%ebx
    63ce:	49 83 c4 38          	add    $0x38,%r12
      me->available_reading = 0;
    63d2:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    63dc:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    63e6:	44 39 f3             	cmp    %r14d,%ebx
    63e9:	0f 85 c1 fe ff ff    	jne    62b0 <receive+0x40>
    63ef:	eb b8                	jmp    63a9 <receive+0x139>
    63f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    63f8:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    63fe:	85 c0                	test   %eax,%eax
    6400:	74 97                	je     6399 <receive+0x129>
    for (int x = 0 ; x < me->messages_count ; x++) {
    6402:	48 83 ba 80 00 00 00 00 	cmpq   $0x0,0x80(%rdx)
    640a:	0f 8f d2 fe ff ff    	jg     62e2 <receive+0x72>
    me->messages_count = 0;
    6410:	48 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rdx)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available_reading == 1) {
    641b:	eb a9                	jmp    63c6 <receive+0x156>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    641d:	83 c3 01             	add    $0x1,%ebx
    6420:	49 83 c4 38          	add    $0x38,%r12
    me->messages_count = 0;
    6424:	48 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    642f:	44 39 f3             	cmp    %r14d,%ebx
    6432:	0f 85 78 fe ff ff    	jne    62b0 <receive+0x40>
    6438:	e9 6c ff ff ff       	jmp    63a9 <receive+0x139>
    643d:	0f 1f 00             	nopl   (%rax)

0000000000006440 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    6440:	f3 0f 1e fa          	endbr64
    6444:	41 57                	push   %r15
    6446:	41 56                	push   %r14
    6448:	41 55                	push   %r13
    644a:	41 54                	push   %r12
    644c:	55                   	push   %rbp
    644d:	48 89 fd             	mov    %rdi,%rbp
    6450:	53                   	push   %rbx
    6451:	48 83 ec 48          	sub    $0x48,%rsp
  if (data->thread_index == data->task_index) {
    6455:	8b 47 04             	mov    0x4(%rdi),%eax
    6458:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    645e:	74 49                	je     64a9 <barriered_work+0x69>
    receive(data);
    6460:	e8 0b fe ff ff       	call   6270 <receive>
    while (data->scheduled == 1) {
    6465:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    646c:	75 16                	jne    6484 <barriered_work+0x44>
    646e:	66 90                	xchg   %ax,%ax
      data->n++;
    6470:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      asm volatile ("sfence" ::: "memory");
    6478:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    647b:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    6482:	74 ec                	je     6470 <barriered_work+0x30>
  if (data->sending == 1) {
    6484:	83 bd 80 01 00 00 01 	cmpl   $0x1,0x180(%rbp)
    648b:	75 08                	jne    6495 <barriered_work+0x55>
    648d:	48 89 ef             	mov    %rbp,%rdi
    6490:	e8 1b e2 ff ff       	call   46b0 <sendm.part.0>
  asm volatile ("sfence" ::: "memory");
    6495:	0f ae f8             	sfence
}
    6498:	48 83 c4 48          	add    $0x48,%rsp
    649c:	31 c0                	xor    %eax,%eax
    649e:	5b                   	pop    %rbx
    649f:	5d                   	pop    %rbp
    64a0:	41 5c                	pop    %r12
    64a2:	41 5d                	pop    %r13
    64a4:	41 5e                	pop    %r14
    64a6:	41 5f                	pop    %r15
    64a8:	c3                   	ret
       receive(data);
    64a9:	e8 c2 fd ff ff       	call   6270 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    64ae:	8b b5 40 01 00 00    	mov    0x140(%rbp),%esi
        int t = data->task_index;
    64b4:	8b 45 04             	mov    0x4(%rbp),%eax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    64b7:	85 f6                	test   %esi,%esi
    64b9:	0f 8e 18 04 00 00    	jle    68d7 <barriered_work+0x497>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    64bf:	4c 63 e0             	movslq %eax,%r12
              int next_task = abs((t + 1) % (data->thread_count));
    64c2:	83 c0 01             	add    $0x1,%eax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    64c5:	45 31 ff             	xor    %r15d,%r15d
    64c8:	89 f7                	mov    %esi,%edi
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    64ca:	48 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%rsp)
    64d3:	45 89 f8             	mov    %r15d,%r8d
    64d6:	49 c1 e4 09          	shl    $0x9,%r12
    64da:	49 89 ef             	mov    %rbp,%r15
    64dd:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
              int next_task = abs((t + 1) % (data->thread_count));
    64e6:	89 44 24 2c          	mov    %eax,0x2c(%rsp)
    64ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    64f0:	4d 8b 9f 28 01 00 00 	mov    0x128(%r15),%r11
    64f7:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    64fc:	31 db                	xor    %ebx,%ebx
    64fe:	eb 0c                	jmp    650c <barriered_work+0xcc>
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6500:	48 83 c3 01          	add    $0x1,%rbx
    6504:	39 df                	cmp    %ebx,%edi
    6506:	0f 8e b4 02 00 00    	jle    67c0 <barriered_work+0x380>
              if (y == b) { continue; }
    650c:	44 39 c3             	cmp    %r8d,%ebx
    650f:	74 ef                	je     6500 <barriered_work+0xc0>
              int next_task = abs((t + 1) % (data->thread_count));
    6511:	49 63 97 34 01 00 00 	movslq 0x134(%r15),%rdx
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    6518:	41 39 5b 08          	cmp    %ebx,0x8(%r11)
    651c:	75 e2                	jne    6500 <barriered_work+0xc0>
    651e:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    6522:	49 8b 4b 20          	mov    0x20(%r11),%rcx
    6526:	48 8d 2c 80          	lea    (%rax,%rax,4),%rbp
    652a:	48 c1 e5 03          	shl    $0x3,%rbp
    652e:	48 8b 44 29 38       	mov    0x38(%rcx,%rbp,1),%rax
    6533:	4a 8b 84 20 70 01 00 00 	mov    0x170(%rax,%r12,1),%rax
    653b:	42 83 7c 30 30 02    	cmpl   $0x2,0x30(%rax,%r14,1)
    6541:	75 bd                	jne    6500 <barriered_work+0xc0>
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    6543:	4c 8d 2c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r13
    654b:	49 29 dd             	sub    %rbx,%r13
    654e:	49 c1 e5 03          	shl    $0x3,%r13
    6552:	85 d2                	test   %edx,%edx
    6554:	7e 46                	jle    659c <barriered_work+0x15c>
    6556:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    655b:	48 c1 e2 09          	shl    $0x9,%rdx
                      all_wrote = 0;
    655f:	45 31 c9             	xor    %r9d,%r9d
    6562:	48 8b 44 01 38       	mov    0x38(%rcx,%rax,1),%rax
                  int all_wrote = 1;
    6567:	b9 01 00 00 00       	mov    $0x1,%ecx
    656c:	48 01 c2             	add    %rax,%rdx
    656f:	90                   	nop
                    if (((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving == 0) {
    6570:	48 8b b0 70 01 00 00 	mov    0x170(%rax),%rsi
    6577:	4a 8b 74 2e 08       	mov    0x8(%rsi,%r13,1),%rsi
                      all_wrote = 0;
    657c:	8b b6 80 01 00 00    	mov    0x180(%rsi),%esi
    6582:	85 f6                	test   %esi,%esi
    6584:	41 0f 44 c9          	cmove  %r9d,%ecx
                  for (int nn = 0 ; nn < data->thread_count; nn++) {
    6588:	48 05 00 02 00 00    	add    $0x200,%rax
    658e:	48 39 c2             	cmp    %rax,%rdx
    6591:	75 dd                	jne    6570 <barriered_work+0x130>
                  if (all_finished == 1 && all_wrote == 1 /*&& ((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available == 0 */) {
    6593:	83 f9 01             	cmp    $0x1,%ecx
    6596:	0f 85 64 ff ff ff    	jne    6500 <barriered_work+0xc0>
    659c:	44 89 c1             	mov    %r8d,%ecx
    659f:	31 c0                	xor    %eax,%eax
    65a1:	89 da                	mov    %ebx,%edx
    65a3:	bf 01 00 00 00       	mov    $0x1,%edi
    65a8:	48 8d 35 69 10 00 00 	lea    0x1069(%rip),%rsi        # 7618 <_IO_stdin_used+0x618>
    65af:	44 89 04 24          	mov    %r8d,(%rsp)
    65b3:	e8 98 be ff ff       	call   2450 <__printf_chk@plt>
                      for (int nn = 0 ; nn < data->thread_count; nn++) {
    65b8:	49 63 87 34 01 00 00 	movslq 0x134(%r15),%rax
    65bf:	44 8b 04 24          	mov    (%rsp),%r8d
    65c3:	85 c0                	test   %eax,%eax
    65c5:	0f 8e d3 03 00 00    	jle    699e <barriered_work+0x55e>
                        ((struct Data*)data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving = 0;
    65cb:	49 8b 97 28 01 00 00 	mov    0x128(%r15),%rdx
    65d2:	48 89 c6             	mov    %rax,%rsi
    65d5:	48 c1 e6 09          	shl    $0x9,%rsi
    65d9:	4c 8b 4a 20          	mov    0x20(%rdx),%r9
    65dd:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    65e2:	4d 8b 54 11 38       	mov    0x38(%r9,%rdx,1),%r10
    65e7:	4c 89 d2             	mov    %r10,%rdx
    65ea:	4c 01 d6             	add    %r10,%rsi
    65ed:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
                      for (int nn = 0 ; nn < data->thread_count; nn++) {
    65f4:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
                        ((struct Data*)data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_receiving = 0;
    65fb:	4a 8b 4c 29 08       	mov    0x8(%rcx,%r13,1),%rcx
    6600:	c7 81 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rcx)
                      for (int nn = 0 ; nn < data->thread_count; nn++) {
    660a:	48 39 f2             	cmp    %rsi,%rdx
    660d:	75 de                	jne    65ed <barriered_work+0x1ad>
                      void * left2 = data->thread->all_threads[b].tasks[next_task].mailboxes[y].stack[0];
    660f:	4d 8b 5c 29 38       	mov    0x38(%r9,%rbp,1),%r11
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    6614:	4b 8b 94 22 70 01 00 00 	mov    0x170(%r10,%r12,1),%rdx
    661c:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    6621:	48 c1 e0 09          	shl    $0x9,%rax
    6625:	4a 8b 4c 2a 18       	mov    0x18(%rdx,%r13,1),%rcx
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    662a:	4b 8b 94 23 70 01 00 00 	mov    0x170(%r11,%r12,1),%rdx
    6632:	4a 8b 54 32 18       	mov    0x18(%rdx,%r14,1),%rdx
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    6637:	48 8b 31             	mov    (%rcx),%rsi
                      void * right = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1];
    663a:	48 89 4c 24 30       	mov    %rcx,0x30(%rsp)
    663f:	48 8b 79 08          	mov    0x8(%rcx),%rdi
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    6643:	4c 8b 0a             	mov    (%rdx),%r9
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    6646:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    664a:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    664f:	4c 89 0c 24          	mov    %r9,(%rsp)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6653:	4c 8d 88 70 01 00 00 	lea    0x170(%rax),%r9
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    665a:	b8 70 01 00 00       	mov    $0x170,%eax
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].lower = data->thread->all_threads[b].tasks[nn].mailboxes[y].higher ;
    665f:	49 8b 14 03          	mov    (%r11,%rax,1),%rdx
                        void * ynnblow = data->thread->all_threads[y].tasks[nn].mailboxes[b].lower;
    6663:	4d 8b 24 02          	mov    (%r10,%rax,1),%r12
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6667:	48 05 00 02 00 00    	add    $0x200,%rax
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].lower = data->thread->all_threads[b].tasks[nn].mailboxes[y].higher ;
    666d:	4c 01 f2             	add    %r14,%rdx
                        void * ynnblow = data->thread->all_threads[y].tasks[nn].mailboxes[b].lower;
    6670:	4d 01 ec             	add    %r13,%r12
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].lower = data->thread->all_threads[b].tasks[nn].mailboxes[y].higher ;
    6673:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
                        void * yynnbhigh = data->thread->all_threads[y].tasks[nn].mailboxes[b].higher;
    6677:	f3 41 0f 6f 04 24    	movdqu (%r12),%xmm0
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].lower = data->thread->all_threads[b].tasks[nn].mailboxes[y].higher ;
    667d:	49 89 0c 24          	mov    %rcx,(%r12)
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].higher = data->thread->all_threads[b].tasks[nn].mailboxes[y].lower ;
    6681:	48 8b 0a             	mov    (%rdx),%rcx
                        void * ynnblow = data->thread->all_threads[y].tasks[nn].mailboxes[b].lower;
    6684:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
                        data->thread->all_threads[y].tasks[nn].mailboxes[b].higher = data->thread->all_threads[b].tasks[nn].mailboxes[y].lower ;
    6689:	49 89 4c 24 08       	mov    %rcx,0x8(%r12)
                        data->thread->all_threads[b].tasks[nn].mailboxes[y].lower = yynnbhigh;
    668e:	0f 11 02             	movups %xmm0,(%rdx)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6691:	49 39 c1             	cmp    %rax,%r9
    6694:	75 c9                	jne    665f <barriered_work+0x21f>
    6696:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    669b:	48 89 5c 24 38       	mov    %rbx,0x38(%rsp)
    66a0:	b8 70 01 00 00       	mov    $0x170,%eax
    66a5:	44 89 44 24 30       	mov    %r8d,0x30(%rsp)
    66aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_reading = 0;
    66b0:	4d 8b 04 03          	mov    (%r11,%rax,1),%r8
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_reading = 0;
    66b4:	49 8b 14 02          	mov    (%r10,%rax,1),%rdx
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_reading = 0;
    66b8:	4d 01 f0             	add    %r14,%r8
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_reading = 0;
    66bb:	4c 01 ea             	add    %r13,%rdx
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_reading = 0;
    66be:	4d 8b 60 08          	mov    0x8(%r8),%r12
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_reading = 0;
    66c2:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->available_reading = 1;
    66c6:	4d 8b 00             	mov    (%r8),%r8
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].lower)->available_reading = 1;
    66c9:	48 8b 12             	mov    (%rdx),%rdx
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_reading = 0;
    66cc:	41 c7 84 24 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%r12)
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_reading = 0;
    66d8:	c7 83 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rbx)
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->available_reading = 1;
    66e2:	41 c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%r8)
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].lower)->available_reading = 1;
    66ed:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                        ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_sending = 1;
    66f7:	41 c7 84 24 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r12)
                        ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_sending = 1;
    6703:	c7 83 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rbx)
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    670d:	49 39 d0             	cmp    %rdx,%r8
    6710:	0f 84 d8 02 00 00    	je     69ee <barriered_work+0x5ae>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6716:	48 05 00 02 00 00    	add    $0x200,%rax
    671c:	49 39 c1             	cmp    %rax,%r9
    671f:	75 8f                	jne    66b0 <barriered_work+0x270>
    6721:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
    6726:	44 8b 44 24 30       	mov    0x30(%rsp),%r8d
    672b:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0] = right;
    6730:	48 89 39             	mov    %rdi,(%rcx)
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1] = left;
    6733:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    673a:	48 83 c3 01          	add    $0x1,%rbx
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1] = left;
    673e:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6743:	41 8b bf 40 01 00 00 	mov    0x140(%r15),%edi
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1] = left;
    674a:	48 8b 40 20          	mov    0x20(%rax),%rax
    674e:	48 8b 44 10 38       	mov    0x38(%rax,%rdx,1),%rax
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0] = right3;
    6753:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
                      data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1] = left;
    6758:	4a 8b 84 20 70 01 00 00 	mov    0x170(%rax,%r12,1),%rax
    6760:	4a 8b 44 28 18       	mov    0x18(%rax,%r13,1),%rax
    6765:	48 89 70 08          	mov    %rsi,0x8(%rax)
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0] = right3;
    6769:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    6770:	48 8b 40 20          	mov    0x20(%rax),%rax
    6774:	48 8b 44 28 38       	mov    0x38(%rax,%rbp,1),%rax
    6779:	4a 8b 84 20 70 01 00 00 	mov    0x170(%rax,%r12,1),%rax
    6781:	4a 8b 44 30 18       	mov    0x18(%rax,%r14,1),%rax
    6786:	48 89 10             	mov    %rdx,(%rax)
                      data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1] = left3;
    6789:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    6790:	48 8b 14 24          	mov    (%rsp),%rdx
    6794:	48 8b 40 20          	mov    0x20(%rax),%rax
    6798:	48 8b 44 28 38       	mov    0x38(%rax,%rbp,1),%rax
    679d:	4a 8b 84 20 70 01 00 00 	mov    0x170(%rax,%r12,1),%rax
    67a5:	4a 8b 44 30 18       	mov    0x18(%rax,%r14,1),%rax
    67aa:	48 89 50 08          	mov    %rdx,0x8(%rax)
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    67ae:	4d 8b 9f 28 01 00 00 	mov    0x128(%r15),%r11
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    67b5:	39 df                	cmp    %ebx,%edi
    67b7:	0f 8f 4f fd ff ff    	jg     650c <barriered_work+0xcc>
    67bd:	0f 1f 00             	nopl   (%rax)
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    67c0:	45 8b b3 c4 00 00 00 	mov    0xc4(%r11),%r14d
          int k = data->group;
    67c7:	41 8b 87 94 01 00 00 	mov    0x194(%r15),%eax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    67ce:	45 85 f6             	test   %r14d,%r14d
    67d1:	0f 8e e0 00 00 00    	jle    68b7 <barriered_work+0x477>
            int y = (k * data->thread->threads_per_group) + d;
    67d7:	41 0f af c6          	imul   %r14d,%eax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    67db:	44 89 44 24 18       	mov    %r8d,0x18(%rsp)
    67e0:	45 31 d2             	xor    %r10d,%r10d
    67e3:	89 7c 24 20          	mov    %edi,0x20(%rsp)
    67e7:	48 98                	cltq
    67e9:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    67ed:	48 8d 1c 92          	lea    (%rdx,%rdx,4),%rbx
    67f1:	48 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%rdx
    67f9:	48 29 c2             	sub    %rax,%rdx
    67fc:	48 c1 e3 03          	shl    $0x3,%rbx
    6800:	4c 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%r9
    6808:	4c 89 0c 24          	mov    %r9,(%rsp)
            int y = (k * data->thread->threads_per_group) + d;
    680c:	4d 89 cd             	mov    %r9,%r13
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    680f:	44 8b 4c 24 2c       	mov    0x2c(%rsp),%r9d
    6814:	0f 1f 40 00          	nopl   0x0(%rax)
    6818:	48 8b 34 24          	mov    (%rsp),%rsi
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    681c:	31 c9                	xor    %ecx,%ecx
    681e:	66 90                	xchg   %ax,%ax
              if (b == y) { continue; } 
    6820:	41 39 ca             	cmp    %ecx,%r10d
    6823:	74 65                	je     688a <barriered_work+0x44a>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6825:	4d 8b 43 20          	mov    0x20(%r11),%r8
    6829:	49 8b 44 18 38       	mov    0x38(%r8,%rbx,1),%rax
    682e:	4a 8b bc 20 70 01 00 00 	mov    0x170(%rax,%r12,1),%rdi
    6836:	48 01 f7             	add    %rsi,%rdi
              if (kind == MAILBOX_FRIEND) {
    6839:	83 7f 30 01          	cmpl   $0x1,0x30(%rdi)
    683d:	75 4b                	jne    688a <barriered_work+0x44a>
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    683f:	48 63 47 34          	movslq 0x34(%rdi),%rax
                  void * _a = data->thread->all_threads[y].tasks[t].mailboxes[b].higher;
    6843:	f3 0f 6f 07          	movdqu (%rdi),%xmm0
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    6847:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
                  void * _b = data->thread->all_threads[y].tasks[t].mailboxes[b].lower;
    684b:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    6850:	48 8d 2c 80          	lea    (%rax,%rax,4),%rbp
              int next_task = abs((t + 1) % (data->thread_count));
    6854:	44 89 c8             	mov    %r9d,%eax
    6857:	99                   	cltd
    6858:	41 f7 bf 34 01 00 00 	idivl  0x134(%r15)
    685f:	89 d0                	mov    %edx,%eax
    6861:	f7 d8                	neg    %eax
    6863:	0f 48 c2             	cmovs  %edx,%eax
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    6866:	48 98                	cltq
    6868:	48 c1 e0 09          	shl    $0x9,%rax
    686c:	49 03 44 e8 38       	add    0x38(%r8,%rbp,8),%rax
    6871:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
                  void * _d = data->thread->all_threads[other].tasks[next_task].mailboxes[y].lower;
    6878:	f3 42 0f 6f 0c 28    	movdqu (%rax,%r13,1),%xmm1
    687e:	66 0f c6 c9 01       	shufpd $0x1,%xmm1,%xmm1
                  data->thread->all_threads[y].tasks[t].mailboxes[b].lower = _c;
    6883:	0f 11 0f             	movups %xmm1,(%rdi)
                  data->thread->all_threads[other].tasks[next_task].mailboxes[b].lower = _a;
    6886:	0f 11 04 30          	movups %xmm0,(%rax,%rsi,1)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    688a:	83 c1 01             	add    $0x1,%ecx
    688d:	48 83 c6 38          	add    $0x38,%rsi
    6891:	44 39 f1             	cmp    %r14d,%ecx
    6894:	7c 8a                	jl     6820 <barriered_work+0x3e0>
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6896:	41 83 c2 01          	add    $0x1,%r10d
    689a:	48 81 c3 c8 00 00 00 	add    $0xc8,%rbx
    68a1:	49 83 c5 38          	add    $0x38,%r13
    68a5:	45 39 f2             	cmp    %r14d,%r10d
    68a8:	0f 8c 6a ff ff ff    	jl     6818 <barriered_work+0x3d8>
    68ae:	44 8b 44 24 18       	mov    0x18(%rsp),%r8d
    68b3:	8b 7c 24 20          	mov    0x20(%rsp),%edi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    68b7:	41 83 c0 01          	add    $0x1,%r8d
    68bb:	41 39 f8             	cmp    %edi,%r8d
    68be:	7d 14                	jge    68d4 <barriered_work+0x494>
    68c0:	48 81 44 24 10 c8 00 00 00 	addq   $0xc8,0x10(%rsp)
    68c9:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    68cf:	e9 1c fc ff ff       	jmp    64f0 <barriered_work+0xb0>
    68d4:	4c 89 fd             	mov    %r15,%rbp
      asm volatile ("sfence" ::: "memory");
    68d7:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    68da:	48 8b b5 60 01 00 00 	mov    0x160(%rbp),%rsi
    68e1:	31 ff                	xor    %edi,%edi
    68e3:	48 c1 e6 05          	shl    $0x5,%rsi
    68e7:	48 03 b5 50 01 00 00 	add    0x150(%rbp),%rsi
    68ee:	e8 1d ba ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    68f3:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    68fa:	48 8b 50 48          	mov    0x48(%rax),%rdx
    68fe:	8b 5a 10             	mov    0x10(%rdx),%ebx
    6901:	83 c3 01             	add    $0x1,%ebx
    while (data->scheduled == 1) {
    6904:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    int modcount = ++data->thread->protected_state->modcount;
    690b:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    690e:	75 51                	jne    6961 <barriered_work+0x521>
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6910:	48 63 95 30 01 00 00 	movslq 0x130(%rbp),%rdx
    6917:	48 8b 40 18          	mov    0x18(%rax),%rax
    691b:	48 63 7d 04          	movslq 0x4(%rbp),%rdi
      data->n++;
    691f:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6927:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    692b:	48 c1 e7 09          	shl    $0x9,%rdi
    692f:	48 03 78 38          	add    0x38(%rax),%rdi
    6933:	ff 95 20 01 00 00    	call   *0x120(%rbp)
      asm volatile ("sfence" ::: "memory");
    6939:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    693c:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    if (modcount != data->thread->protected_state->modcount) {
    6943:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    while (data->scheduled == 1) {
    694a:	74 c4                	je     6910 <barriered_work+0x4d0>
    if (modcount != data->thread->protected_state->modcount) {
    694c:	48 8b 40 48          	mov    0x48(%rax),%rax
    6950:	3b 58 10             	cmp    0x10(%rax),%ebx
    6953:	74 0c                	je     6961 <barriered_work+0x521>
    6955:	48 8d 3d e4 08 00 00 	lea    0x8e4(%rip),%rdi        # 7240 <_IO_stdin_used+0x240>
    695c:	e8 8f b9 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6961:	48 8b b5 60 01 00 00 	mov    0x160(%rbp),%rsi
    6968:	31 ff                	xor    %edi,%edi
    696a:	48 c1 e6 05          	shl    $0x5,%rsi
    696e:	48 03 b5 50 01 00 00 	add    0x150(%rbp),%rsi
    6975:	48 83 c6 10          	add    $0x10,%rsi
    6979:	e8 92 b9 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    697e:	48 8b 85 60 01 00 00 	mov    0x160(%rbp),%rax
    6985:	48 83 c0 01          	add    $0x1,%rax
    6989:	48 99                	cqto
    698b:	48 f7 bd 58 01 00 00 	idivq  0x158(%rbp)
    6992:	48 89 95 60 01 00 00 	mov    %rdx,0x160(%rbp)
    6999:	e9 e6 fa ff ff       	jmp    6484 <barriered_work+0x44>
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    699e:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    69a5:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    69aa:	48 8b 40 20          	mov    0x20(%rax),%rax
    69ae:	48 8b 54 10 38       	mov    0x38(%rax,%rdx,1),%rdx
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    69b3:	48 8b 44 28 38       	mov    0x38(%rax,%rbp,1),%rax
    69b8:	4a 8b 84 20 70 01 00 00 	mov    0x170(%rax,%r12,1),%rax
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    69c0:	4a 8b 94 22 70 01 00 00 	mov    0x170(%rdx,%r12,1),%rdx
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    69c8:	4a 8b 44 30 18       	mov    0x18(%rax,%r14,1),%rax
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    69cd:	4a 8b 4c 2a 18       	mov    0x18(%rdx,%r13,1),%rcx
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    69d2:	48 8b 10             	mov    (%rax),%rdx
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    69d5:	48 8b 40 08          	mov    0x8(%rax),%rax
                      void * left = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[0];
    69d9:	48 8b 31             	mov    (%rcx),%rsi
                      void * right = data->thread->all_threads[y].tasks[t].mailboxes[b].stack[1];
    69dc:	48 8b 79 08          	mov    0x8(%rcx),%rdi
                      void * left3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[0];
    69e0:	48 89 14 24          	mov    %rdx,(%rsp)
                      void * right3 = data->thread->all_threads[b].tasks[t].mailboxes[y].stack[1];
    69e4:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    69e9:	e9 42 fd ff ff       	jmp    6730 <barriered_work+0x2f0>
    69ee:	bf 01 00 00 00       	mov    $0x1,%edi
    69f3:	48 8d 35 2b 08 00 00 	lea    0x82b(%rip),%rsi        # 7225 <_IO_stdin_used+0x225>
    69fa:	31 c0                	xor    %eax,%eax
    69fc:	e8 4f ba ff ff       	call   2450 <__printf_chk@plt>
                          exit(1);
    6a01:	bf 01 00 00 00       	mov    $0x1,%edi
    6a06:	e8 95 ba ff ff       	call   24a0 <exit@plt>
    6a0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006a10 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6a10:	f3 0f 1e fa          	endbr64
    6a14:	53                   	push   %rbx
    6a15:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6a18:	e8 63 f4 ff ff       	call   5e80 <barriered_work_ingest>
  barriered_work(data);
    6a1d:	48 89 df             	mov    %rbx,%rdi
}
    6a20:	5b                   	pop    %rbx
  barriered_work(data);
    6a21:	e9 1a fa ff ff       	jmp    6440 <barriered_work>
    6a26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006a30 <sendm>:
int sendm(struct BarrierTask *data) {
    6a30:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    6a34:	83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%rdi)
    6a3b:	74 03                	je     6a40 <sendm+0x10>
}
    6a3d:	31 c0                	xor    %eax,%eax
    6a3f:	c3                   	ret
int sendm(struct BarrierTask *data) {
    6a40:	48 83 ec 08          	sub    $0x8,%rsp
    6a44:	e8 67 dc ff ff       	call   46b0 <sendm.part.0>
}
    6a49:	31 c0                	xor    %eax,%eax
    6a4b:	48 83 c4 08          	add    $0x8,%rsp
    6a4f:	c3                   	ret

0000000000006a50 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6a50:	f3 0f 1e fa          	endbr64
}
    6a54:	31 c0                	xor    %eax,%eax
    6a56:	c3                   	ret
    6a57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006a60 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6a60:	f3 0f 1e fa          	endbr64
    6a64:	31 c0                	xor    %eax,%eax
    6a66:	c3                   	ret
    6a67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006a70 <after>:
int after(struct timespec left, struct timespec right) {
    6a70:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6a74:	31 c0                	xor    %eax,%eax
    6a76:	48 39 d7             	cmp    %rdx,%rdi
    6a79:	7e 08                	jle    6a83 <after+0x13>
    6a7b:	31 c0                	xor    %eax,%eax
    6a7d:	48 39 ce             	cmp    %rcx,%rsi
    6a80:	0f 9f c0             	setg   %al
}
    6a83:	c3                   	ret
    6a84:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6a8f:	90                   	nop

0000000000006a90 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6a90:	f3 0f 1e fa          	endbr64
    6a94:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6a99:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    6a9e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6aa0:	48 39 d7             	cmp    %rdx,%rdi
    6aa3:	7f 18                	jg     6abd <within+0x2d>
    6aa5:	4d 39 d8             	cmp    %r11,%r8
    6aa8:	0f 9e c2             	setle  %dl
    6aab:	48 39 ce             	cmp    %rcx,%rsi
    6aae:	0f 9e c0             	setle  %al
    6ab1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6ab3:	31 c0                	xor    %eax,%eax
    6ab5:	4d 39 d1             	cmp    %r10,%r9
    6ab8:	0f 9e c0             	setle  %al
    6abb:	21 d0                	and    %edx,%eax
}
    6abd:	c3                   	ret
    6abe:	66 90                	xchg   %ax,%ax

0000000000006ac0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6ac0:	f3 0f 1e fa          	endbr64
    6ac4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6ac9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    6ace:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6ad3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6ad8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    6add:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6ae2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6ae7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    6aec:	48 39 fe             	cmp    %rdi,%rsi
    6aef:	7d 2f                	jge    6b20 <overlap+0x60>
    6af1:	48 39 ca             	cmp    %rcx,%rdx
    6af4:	7d 62                	jge    6b58 <overlap+0x98>
    6af6:	4d 39 da             	cmp    %r11,%r10
    6af9:	7d 0e                	jge    6b09 <overlap+0x49>
    return 1;
    6afb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6b00:	4d 39 c1             	cmp    %r8,%r9
    6b03:	0f 8c 7f 00 00 00    	jl     6b88 <overlap+0xc8>
  return 0;
    6b09:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6b0b:	4d 39 c1             	cmp    %r8,%r9
    6b0e:	7f 4c                	jg     6b5c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6b10:	31 c0                	xor    %eax,%eax
    6b12:	4d 39 da             	cmp    %r11,%r10
    6b15:	0f 9e c0             	setle  %al
    6b18:	c3                   	ret
    6b19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6b20:	7e 4e                	jle    6b70 <overlap+0xb0>
    6b22:	48 39 ca             	cmp    %rcx,%rdx
    6b25:	7f 39                	jg     6b60 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6b27:	75 31                	jne    6b5a <overlap+0x9a>
    6b29:	4d 39 c1             	cmp    %r8,%r9
    6b2c:	7c 2c                	jl     6b5a <overlap+0x9a>
    return 1;
    6b2e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6b33:	4d 39 da             	cmp    %r11,%r10
    6b36:	7d 24                	jge    6b5c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6b38:	48 39 ca             	cmp    %rcx,%rdx
    6b3b:	0f 94 c2             	sete   %dl
    6b3e:	48 39 fe             	cmp    %rdi,%rsi
    6b41:	0f 94 c0             	sete   %al
    6b44:	21 c2                	and    %eax,%edx
    6b46:	31 c0                	xor    %eax,%eax
    6b48:	4d 39 c1             	cmp    %r8,%r9
    6b4b:	0f 94 c0             	sete   %al
    6b4e:	21 d0                	and    %edx,%eax
    6b50:	c3                   	ret
    6b51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6b58:	74 af                	je     6b09 <overlap+0x49>
  return 0;
    6b5a:	31 c0                	xor    %eax,%eax
}
    6b5c:	c3                   	ret
    6b5d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6b60:	4d 39 da             	cmp    %r11,%r10
    6b63:	7e c4                	jle    6b29 <overlap+0x69>
    return 1;
    6b65:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6b6a:	4d 39 c1             	cmp    %r8,%r9
    6b6d:	7e ba                	jle    6b29 <overlap+0x69>
    6b6f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6b70:	48 39 ca             	cmp    %rcx,%rdx
    6b73:	7c 94                	jl     6b09 <overlap+0x49>
    6b75:	4d 39 c1             	cmp    %r8,%r9
    6b78:	7d b4                	jge    6b2e <overlap+0x6e>
    6b7a:	48 39 ca             	cmp    %rcx,%rdx
    6b7d:	74 91                	je     6b10 <overlap+0x50>
    6b7f:	eb d9                	jmp    6b5a <overlap+0x9a>
    6b81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6b88:	c3                   	ret
    6b89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006b90 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6b90:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6b94:	85 f6                	test   %esi,%esi
    6b96:	0f 8e 44 03 00 00    	jle    6ee0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    6b9c:	41 57                	push   %r15
    6b9e:	41 89 f7             	mov    %esi,%r15d
    6ba1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6ba3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6ba6:	41 55                	push   %r13
    6ba8:	41 54                	push   %r12
    6baa:	55                   	push   %rbp
    6bab:	53                   	push   %rbx
    6bac:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6bb0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6bb4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6bb9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    6bbe:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6bc1:	45 39 e6             	cmp    %r12d,%r14d
    6bc4:	0f 84 4e 02 00 00    	je     6e18 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6bca:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6bcf:	8b 50 08             	mov    0x8(%rax),%edx
    6bd2:	85 d2                	test   %edx,%edx
    6bd4:	0f 8e 3e 02 00 00    	jle    6e18 <verify+0x288>
    6bda:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    6bdf:	31 c9                	xor    %ecx,%ecx
    6be1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    6be6:	31 c0                	xor    %eax,%eax
    6be8:	44 89 f2             	mov    %r14d,%edx
    6beb:	bf 01 00 00 00       	mov    $0x1,%edi
    6bf0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6bf5:	48 8d 35 54 06 00 00 	lea    0x654(%rip),%rsi        # 7250 <_IO_stdin_used+0x250>
    6bfc:	e8 4f b8 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6c01:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6c06:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    6c0b:	8b 40 08             	mov    0x8(%rax),%eax
    6c0e:	85 c0                	test   %eax,%eax
    6c10:	0f 8e e6 01 00 00    	jle    6dfc <verify+0x26c>
    6c16:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6c19:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    6c1e:	31 db                	xor    %ebx,%ebx
    6c20:	48 c1 e0 09          	shl    $0x9,%rax
    6c24:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6c29:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    6c2e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6c33:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6c38:	4c 8b 20             	mov    (%rax),%r12
    6c3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6c40:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6c45:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    6c4a:	49 89 de             	mov    %rbx,%r14
    6c4d:	48 8d 35 11 06 00 00 	lea    0x611(%rip),%rsi        # 7265 <_IO_stdin_used+0x265>
    6c54:	49 c1 e6 09          	shl    $0x9,%r14
    6c58:	bf 01 00 00 00       	mov    $0x1,%edi
    6c5d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6c61:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    6c69:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    6c6e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    6c76:	31 c0                	xor    %eax,%eax
    6c78:	e8 d3 b7 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6c7d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6c82:	4c 8b 20             	mov    (%rax),%r12
    6c85:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    6c8e:	0f 8e 47 01 00 00    	jle    6ddb <verify+0x24b>
    6c94:	4c 03 75 00          	add    0x0(%rbp),%r14
    6c98:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6c9d:	ba 01 00 00 00       	mov    $0x1,%edx
    6ca2:	4d 89 f5             	mov    %r14,%r13
    6ca5:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6cac:	4d 85 f6             	test   %r14,%r14
    6caf:	0f 8e 21 01 00 00    	jle    6dd6 <verify+0x246>
    6cb5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6cb8:	48 89 d5             	mov    %rdx,%rbp
    6cbb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6cc0:	31 db                	xor    %ebx,%ebx
    6cc2:	4d 89 f2             	mov    %r14,%r10
    6cc5:	48 c1 e5 05          	shl    $0x5,%rbp
    6cc9:	48 83 ed 20          	sub    $0x20,%rbp
    6ccd:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6cd1:	49 89 ee             	mov    %rbp,%r14
    6cd4:	48 89 dd             	mov    %rbx,%rbp
    6cd7:	48 89 d3             	mov    %rdx,%rbx
    6cda:	eb 31                	jmp    6d0d <verify+0x17d>
    6cdc:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6ce0:	4c 39 c2             	cmp    %r8,%rdx
    6ce3:	0f 8d 57 01 00 00    	jge    6e40 <verify+0x2b0>
    6ce9:	4c 39 df             	cmp    %r11,%rdi
    6cec:	7e 05                	jle    6cf3 <verify+0x163>
    6cee:	49 39 c1             	cmp    %rax,%r9
    6cf1:	7c 75                	jl     6d68 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6cf3:	4c 39 df             	cmp    %r11,%rdi
    6cf6:	0f 8d ab 01 00 00    	jge    6ea7 <verify+0x317>
    6cfc:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6d00:	48 83 c5 01          	add    $0x1,%rbp
    6d04:	49 39 ea             	cmp    %rbp,%r10
    6d07:	0f 8e a9 00 00 00    	jle    6db6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6d0d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    6d14:	48 89 e8             	mov    %rbp,%rax
    6d17:	48 c1 e0 05          	shl    $0x5,%rax
    6d1b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    6d22:	4c 01 f2             	add    %r14,%rdx
    6d25:	48 8b 08             	mov    (%rax),%rcx
    6d28:	48 8b 78 10          	mov    0x10(%rax),%rdi
    6d2c:	48 8b 32             	mov    (%rdx),%rsi
    6d2f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6d33:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6d37:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    6d3b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    6d3f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6d43:	48 39 f1             	cmp    %rsi,%rcx
    6d46:	7c 98                	jl     6ce0 <verify+0x150>
    6d48:	0f 8e 42 01 00 00    	jle    6e90 <verify+0x300>
    6d4e:	4c 39 c2             	cmp    %r8,%rdx
    6d51:	0f 8f f9 00 00 00    	jg     6e50 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6d57:	75 a7                	jne    6d00 <verify+0x170>
    6d59:	4c 39 df             	cmp    %r11,%rdi
    6d5c:	7f a2                	jg     6d00 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6d5e:	49 39 c1             	cmp    %rax,%r9
    6d61:	7c 9d                	jl     6d00 <verify+0x170>
    6d63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6d68:	49 89 c1             	mov    %rax,%r9
    6d6b:	48 89 f9             	mov    %rdi,%rcx
    6d6e:	48 89 f2             	mov    %rsi,%rdx
    6d71:	bf 01 00 00 00       	mov    $0x1,%edi
    6d76:	48 8d 35 db 08 00 00 	lea    0x8db(%rip),%rsi        # 7658 <_IO_stdin_used+0x658>
    6d7d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6d7f:	48 83 c5 01          	add    $0x1,%rbp
    6d83:	e8 c8 b6 ff ff       	call   2450 <__printf_chk@plt>
    6d88:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6d8d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    6d92:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6d95:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6d9a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6da1:	4c 8b 20             	mov    (%rax),%r12
    6da4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6da9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6dad:	49 39 ea             	cmp    %rbp,%r10
    6db0:	0f 8f 57 ff ff ff    	jg     6d0d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6db6:	48 89 da             	mov    %rbx,%rdx
    6db9:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    6dc0:	7d 14                	jge    6dd6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6dc2:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6dc9:	48 83 c2 01          	add    $0x1,%rdx
    6dcd:	4d 85 f6             	test   %r14,%r14
    6dd0:	0f 8f e2 fe ff ff    	jg     6cb8 <verify+0x128>
    6dd6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6ddb:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6de0:	48 83 c3 01          	add    $0x1,%rbx
    6de4:	39 58 08             	cmp    %ebx,0x8(%rax)
    6de7:	0f 8f 53 fe ff ff    	jg     6c40 <verify+0xb0>
    6ded:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6df2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6df7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6dfc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6e01:	48 83 c1 01          	add    $0x1,%rcx
    6e05:	39 48 08             	cmp    %ecx,0x8(%rax)
    6e08:	0f 8f d8 fd ff ff    	jg     6be6 <verify+0x56>
    6e0e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6e13:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6e18:	48 81 44 24 10 c8 00 00 00 	addq   $0xc8,0x10(%rsp)
    6e21:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6e26:	41 39 c7             	cmp    %eax,%r15d
    6e29:	0f 84 86 00 00 00    	je     6eb5 <verify+0x325>
    6e2f:	41 89 c4             	mov    %eax,%r12d
    6e32:	e9 8a fd ff ff       	jmp    6bc1 <verify+0x31>
    6e37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6e40:	0f 85 ba fe ff ff    	jne    6d00 <verify+0x170>
    6e46:	e9 a8 fe ff ff       	jmp    6cf3 <verify+0x163>
    6e4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6e50:	49 39 c1             	cmp    %rax,%r9
    6e53:	7e 09                	jle    6e5e <verify+0x2ce>
    6e55:	4c 39 df             	cmp    %r11,%rdi
    6e58:	0f 8c 0a ff ff ff    	jl     6d68 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6e5e:	4c 39 df             	cmp    %r11,%rdi
    6e61:	0f 8f 99 fe ff ff    	jg     6d00 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6e67:	49 39 c1             	cmp    %rax,%r9
    6e6a:	0f 8d f8 fe ff ff    	jge    6d68 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6e70:	48 39 f1             	cmp    %rsi,%rcx
    6e73:	0f 85 87 fe ff ff    	jne    6d00 <verify+0x170>
    6e79:	4c 39 c2             	cmp    %r8,%rdx
    6e7c:	0f 85 7e fe ff ff    	jne    6d00 <verify+0x170>
    6e82:	4c 39 df             	cmp    %r11,%rdi
    6e85:	0f 84 dd fe ff ff    	je     6d68 <verify+0x1d8>
    6e8b:	e9 70 fe ff ff       	jmp    6d00 <verify+0x170>
    6e90:	4c 39 c2             	cmp    %r8,%rdx
    6e93:	0f 8c 5a fe ff ff    	jl     6cf3 <verify+0x163>
    6e99:	4c 39 df             	cmp    %r11,%rdi
    6e9c:	7e c9                	jle    6e67 <verify+0x2d7>
    6e9e:	4c 39 c2             	cmp    %r8,%rdx
    6ea1:	0f 85 59 fe ff ff    	jne    6d00 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6ea7:	49 39 c1             	cmp    %rax,%r9
    6eaa:	0f 8f 50 fe ff ff    	jg     6d00 <verify+0x170>
    6eb0:	e9 b3 fe ff ff       	jmp    6d68 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    6eb5:	48 81 44 24 18 c8 00 00 00 	addq   $0xc8,0x18(%rsp)
    6ebe:	41 8d 46 01          	lea    0x1(%r14),%eax
    6ec2:	45 39 e6             	cmp    %r12d,%r14d
    6ec5:	74 08                	je     6ecf <verify+0x33f>
    6ec7:	41 89 c6             	mov    %eax,%r14d
    6eca:	e9 ea fc ff ff       	jmp    6bb9 <verify+0x29>
}
    6ecf:	48 83 c4 58          	add    $0x58,%rsp
    6ed3:	31 c0                	xor    %eax,%eax
    6ed5:	5b                   	pop    %rbx
    6ed6:	5d                   	pop    %rbp
    6ed7:	41 5c                	pop    %r12
    6ed9:	41 5d                	pop    %r13
    6edb:	41 5e                	pop    %r14
    6edd:	41 5f                	pop    %r15
    6edf:	c3                   	ret
    6ee0:	31 c0                	xor    %eax,%eax
    6ee2:	c3                   	ret

Disassembly of section .fini:

0000000000006ee4 <_fini>:
    6ee4:	f3 0f 1e fa          	endbr64
    6ee8:	48 83 ec 08          	sub    $0x8,%rsp
    6eec:	48 83 c4 08          	add    $0x8,%rsp
    6ef0:	c3                   	ret
