
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
    25f6:	48 8d 3d 53 4f 00 00 	lea    0x4f53(%rip),%rdi        # 7550 <_IO_stdin_used+0x550>
    25fd:	41 56                	push   %r14
    25ff:	41 55                	push   %r13
    2601:	41 54                	push   %r12
    2603:	55                   	push   %rbp
    2604:	53                   	push   %rbx
    2605:	48 81 ec b8 00 00 00 	sub    $0xb8,%rsp
    260c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2615:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
    261d:	48 8d 05 fc 18 00 00 	lea    0x18fc(%rip),%rax        # 3f20 <barriered_reset>
    2624:	66 48 0f 6e d8       	movq   %rax,%xmm3
    2629:	0f 16 1d 48 76 00 00 	movhps 0x7648(%rip),%xmm3        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    2630:	0f 29 5c 24 50       	movaps %xmm3,0x50(%rsp)
    2635:	e8 b6 fc ff ff       	call   22f0 <puts@plt>
    263a:	bf 0a 00 00 00       	mov    $0xa,%edi
    263f:	e8 8c fc ff ff       	call   22d0 <putchar@plt>
    2644:	ba 06 00 00 00       	mov    $0x6,%edx
    2649:	48 8d 35 03 4c 00 00 	lea    0x4c03(%rip),%rsi        # 7253 <_IO_stdin_used+0x253>
    2650:	31 c0                	xor    %eax,%eax
    2652:	bf 01 00 00 00       	mov    $0x1,%edi
    2657:	e8 f4 fd ff ff       	call   2450 <__printf_chk@plt>
    265c:	48 8d 3d 05 4c 00 00 	lea    0x4c05(%rip),%rdi        # 7268 <_IO_stdin_used+0x268>
    2663:	e8 88 fc ff ff       	call   22f0 <puts@plt>
    2668:	ba 02 00 00 00       	mov    $0x2,%edx
    266d:	48 8d 35 10 4c 00 00 	lea    0x4c10(%rip),%rsi        # 7284 <_IO_stdin_used+0x284>
    2674:	31 c0                	xor    %eax,%eax
    2676:	bf 01 00 00 00       	mov    $0x1,%edi
    267b:	e8 d0 fd ff ff       	call   2450 <__printf_chk@plt>
    2680:	ba 0a 00 00 00       	mov    $0xa,%edx
    2685:	48 8d 35 12 4c 00 00 	lea    0x4c12(%rip),%rsi        # 729e <_IO_stdin_used+0x29e>
    268c:	31 c0                	xor    %eax,%eax
    268e:	bf 01 00 00 00       	mov    $0x1,%edi
    2693:	e8 b8 fd ff ff       	call   2450 <__printf_chk@plt>
    2698:	ba 01 00 00 00       	mov    $0x1,%edx
    269d:	48 8d 35 0e 4c 00 00 	lea    0x4c0e(%rip),%rsi        # 72b2 <_IO_stdin_used+0x2b2>
    26a4:	31 c0                	xor    %eax,%eax
    26a6:	bf 01 00 00 00       	mov    $0x1,%edi
    26ab:	e8 a0 fd ff ff       	call   2450 <__printf_chk@plt>
    26b0:	ba 01 00 00 00       	mov    $0x1,%edx
    26b5:	48 8d 35 07 4c 00 00 	lea    0x4c07(%rip),%rsi        # 72c3 <_IO_stdin_used+0x2c3>
    26bc:	31 c0                	xor    %eax,%eax
    26be:	bf 01 00 00 00       	mov    $0x1,%edi
    26c3:	e8 88 fd ff ff       	call   2450 <__printf_chk@plt>
    26c8:	ba 02 00 00 00       	mov    $0x2,%edx
    26cd:	48 8d 35 07 4c 00 00 	lea    0x4c07(%rip),%rsi        # 72db <_IO_stdin_used+0x2db>
    26d4:	31 c0                	xor    %eax,%eax
    26d6:	bf 01 00 00 00       	mov    $0x1,%edi
    26db:	e8 70 fd ff ff       	call   2450 <__printf_chk@plt>
    26e0:	ba 01 00 00 00       	mov    $0x1,%edx
    26e5:	48 8d 35 cc 4e 00 00 	lea    0x4ecc(%rip),%rsi        # 75b8 <_IO_stdin_used+0x5b8>
    26ec:	31 c0                	xor    %eax,%eax
    26ee:	bf 01 00 00 00       	mov    $0x1,%edi
    26f3:	e8 58 fd ff ff       	call   2450 <__printf_chk@plt>
    26f8:	ba 01 00 00 00       	mov    $0x1,%edx
    26fd:	48 8d 35 e4 4e 00 00 	lea    0x4ee4(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2704:	31 c0                	xor    %eax,%eax
    2706:	bf 01 00 00 00       	mov    $0x1,%edi
    270b:	e8 40 fd ff ff       	call   2450 <__printf_chk@plt>
    2710:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2715:	48 8d 35 db 4b 00 00 	lea    0x4bdb(%rip),%rsi        # 72f7 <_IO_stdin_used+0x2f7>
    271c:	31 c0                	xor    %eax,%eax
    271e:	bf 01 00 00 00       	mov    $0x1,%edi
    2723:	e8 28 fd ff ff       	call   2450 <__printf_chk@plt>
    2728:	ba 05 00 00 00       	mov    $0x5,%edx
    272d:	48 8d 35 dd 4b 00 00 	lea    0x4bdd(%rip),%rsi        # 7311 <_IO_stdin_used+0x311>
    2734:	31 c0                	xor    %eax,%eax
    2736:	bf 01 00 00 00       	mov    $0x1,%edi
    273b:	e8 10 fd ff ff       	call   2450 <__printf_chk@plt>
    2740:	48 8d 3d a8 49 00 00 	lea    0x49a8(%rip),%rdi        # 70ef <_IO_stdin_used+0xef>
    2747:	e8 a4 fb ff ff       	call   22f0 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    274c:	be 18 00 00 00       	mov    $0x18,%esi
    2751:	bf 03 00 00 00       	mov    $0x3,%edi
    2756:	e8 45 fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    275b:	be c0 00 00 00       	mov    $0xc0,%esi
    2760:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2765:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    276a:	e8 31 fc ff ff       	call   23a0 <calloc@plt>
    276f:	ba 06 00 00 00       	mov    $0x6,%edx
    2774:	bf 01 00 00 00       	mov    $0x1,%edi
    2779:	48 8d 35 a5 4b 00 00 	lea    0x4ba5(%rip),%rsi        # 7325 <_IO_stdin_used+0x325>
    2780:	48 89 04 24          	mov    %rax,(%rsp)
    2784:	31 c0                	xor    %eax,%eax
    2786:	e8 c5 fc ff ff       	call   2450 <__printf_chk@plt>
    278b:	ba 0c 00 00 00       	mov    $0xc,%edx
    2790:	48 8d 35 a4 4b 00 00 	lea    0x4ba4(%rip),%rsi        # 733b <_IO_stdin_used+0x33b>
    2797:	31 c0                	xor    %eax,%eax
    2799:	bf 01 00 00 00       	mov    $0x1,%edi
    279e:	e8 ad fc ff ff       	call   2450 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    27a3:	be 10 00 00 00       	mov    $0x10,%esi
    27a8:	bf 0c 00 00 00       	mov    $0xc,%edi
    27ad:	e8 ee fb ff ff       	call   23a0 <calloc@plt>
    27b2:	4c 8b 34 24          	mov    (%rsp),%r14
    27b6:	49 89 c7             	mov    %rax,%r15
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    27b9:	49 89 c4             	mov    %rax,%r12
    27bc:	48 8d 98 c0 00 00 00 	lea    0xc0(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    27c3:	49 89 c5             	mov    %rax,%r13
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27c6:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    27cb:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27d3:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    27d8:	49 83 c5 10          	add    $0x10,%r13
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27dc:	e8 bf fb ff ff       	call   23a0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    27e1:	be 20 00 00 00       	mov    $0x20,%esi
    27e6:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27eb:	49 89 45 f8          	mov    %rax,-0x8(%r13)
    27ef:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
    27f2:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    27fc:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2806:	e8 95 fb ff ff       	call   23a0 <calloc@plt>
    280b:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    2812:	49 39 dd             	cmp    %rbx,%r13
    2815:	75 af                	jne    27c6 <main+0x1d6>
    2817:	4d 89 f3             	mov    %r14,%r11
    281a:	4c 8b 74 24 48       	mov    0x48(%rsp),%r14
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
    281f:	c7 44 24 38 00 00 00 00 	movl   $0x0,0x38(%rsp)
  for (int x = 0 ; x < buffers_required; x++) {
    2827:	45 31 ed             	xor    %r13d,%r13d
  int curcpu = 0;
    282a:	c7 44 24 30 00 00 00 00 	movl   $0x0,0x30(%rsp)
    2832:	4c 89 74 24 40       	mov    %r14,0x40(%rsp)
    2837:	4c 89 f6             	mov    %r14,%rsi
    283a:	4c 89 a4 24 88 00 00 00 	mov    %r12,0x88(%rsp)
    2842:	4d 89 fc             	mov    %r15,%r12
    2845:	43 8d 6c 2d 00       	lea    0x0(%r13,%r13,1),%ebp
    284a:	48 63 44 24 38       	movslq 0x38(%rsp),%rax
    284f:	4f 8d 4c 6d 00       	lea    0x0(%r13,%r13,2),%r9
    2854:	44 89 ac 24 84 00 00 00 	mov    %r13d,0x84(%rsp)
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    285c:	8d 7d 03             	lea    0x3(%rbp),%edi
    285f:	49 c1 e1 07          	shl    $0x7,%r9
    2863:	4c 89 5c 24 60       	mov    %r11,0x60(%rsp)
    2868:	48 c1 e0 04          	shl    $0x4,%rax
    286c:	89 7c 24 68          	mov    %edi,0x68(%rsp)
    2870:	4f 8d 3c 19          	lea    (%r9,%r11,1),%r15
    2874:	4c 89 ac 24 90 00 00 00 	mov    %r13,0x90(%rsp)
    287c:	49 8d 1c 04          	lea    (%r12,%rax,1),%rbx
    2880:	8d 45 01             	lea    0x1(%rbp),%eax
    2883:	4d 89 f9             	mov    %r15,%r9
    2886:	48 89 74 24 70       	mov    %rsi,0x70(%rsp)
    288b:	4c 89 5c 24 28       	mov    %r11,0x28(%rsp)
    2890:	4c 89 a4 24 98 00 00 00 	mov    %r12,0x98(%rsp)
    2898:	41 89 c4             	mov    %eax,%r12d
    289b:	8b 94 24 84 00 00 00 	mov    0x84(%rsp),%edx
    28a2:	89 e9                	mov    %ebp,%ecx
    28a4:	bf 01 00 00 00       	mov    $0x1,%edi
    28a9:	31 c0                	xor    %eax,%eax
    28ab:	48 8d 35 5e 4d 00 00 	lea    0x4d5e(%rip),%rsi        # 7610 <_IO_stdin_used+0x610>
    28b2:	4c 89 0c 24          	mov    %r9,(%rsp)
    28b6:	e8 95 fb ff ff       	call   2450 <__printf_chk@plt>
      int x = (k * threads_per_group) + d;
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    28bb:	be 08 00 00 00       	mov    $0x8,%esi
    28c0:	bf 02 00 00 00       	mov    $0x2,%edi
    28c5:	e8 d6 fa ff ff       	call   23a0 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    28ca:	be 80 00 00 00       	mov    $0x80,%esi
    28cf:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    28d4:	49 89 c5             	mov    %rax,%r13
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    28d7:	e8 c4 fa ff ff       	call   23a0 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    28dc:	40 f6 c5 01          	test   $0x1,%bpl
    28e0:	4c 8b 0c 24          	mov    (%rsp),%r9
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    28e4:	49 89 c6             	mov    %rax,%r14
      if (x % 2 == 1) {
    28e7:	0f 84 d8 0b 00 00    	je     34c5 <main+0xed5>
        other = abs(x - 1) % total_threads;
    28ed:	8d 45 ff             	lea    -0x1(%rbp),%eax
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    28f0:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
        my_thread_data[1] = &thread_data[x]; 
    28f5:	4c 89 ca             	mov    %r9,%rdx
    28f8:	41 b8 01 00 00 00    	mov    $0x1,%r8d
        other = abs(x - 1) % total_threads;
    28fe:	49 89 c7             	mov    %rax,%r15
        my_thread_data[0] = &thread_data[other]; 
    2901:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    2905:	48 c1 e0 06          	shl    $0x6,%rax
    2909:	48 01 f8             	add    %rdi,%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    290c:	49 8d 7d 08          	lea    0x8(%r13),%rdi
    2910:	48 89 7c 24 18       	mov    %rdi,0x18(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    2915:	48 8b 7c 24 70       	mov    0x70(%rsp),%rdi
        thread_data[x].thread_index = 1;
    291a:	45 89 41 04          	mov    %r8d,0x4(%r9)
    291e:	44 89 f9             	mov    %r15d,%ecx
    2921:	48 8d 35 18 4d 00 00 	lea    0x4d18(%rip),%rsi        # 7640 <_IO_stdin_used+0x640>
    2928:	49 89 55 08          	mov    %rdx,0x8(%r13)
    292c:	89 ea                	mov    %ebp,%edx
        thread_data[x].protected_state = &protected_state[k];
    292e:	49 89 79 48          	mov    %rdi,0x48(%r9)
    2932:	bf 01 00 00 00       	mov    $0x1,%edi
    2937:	49 89 45 00          	mov    %rax,0x0(%r13)
    293b:	31 c0                	xor    %eax,%eax
    293d:	4c 89 0c 24          	mov    %r9,(%rsp)
    2941:	e8 0a fb ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].other = other;
    2946:	4c 8b 0c 24          	mov    (%rsp),%r9
    294a:	8b 4c 24 30          	mov    0x30(%rsp),%ecx
    294e:	31 c0                	xor    %eax,%eax
    2950:	89 ea                	mov    %ebp,%edx
    2952:	48 8d 35 17 4d 00 00 	lea    0x4d17(%rip),%rsi        # 7670 <_IO_stdin_used+0x670>
    2959:	bf 01 00 00 00       	mov    $0x1,%edi
    295e:	45 89 b9 b8 00 00 00 	mov    %r15d,0xb8(%r9)
    2965:	e8 e6 fa ff ff       	call   2450 <__printf_chk@plt>
        if (x < thread_count) {
    296a:	83 fd 01             	cmp    $0x1,%ebp
    296d:	4c 8b 0c 24          	mov    (%rsp),%r9
    2971:	0f 8f f2 0e 00 00    	jg     3869 <main+0x1279>
          CPU_SET(curcpu, sendercpu);
    2977:	48 63 44 24 30       	movslq 0x30(%rsp),%rax
    297c:	48 89 c7             	mov    %rax,%rdi
    297f:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2985:	77 12                	ja     2999 <main+0x3a9>
    2987:	48 c1 e8 06          	shr    $0x6,%rax
    298b:	ba 01 00 00 00       	mov    $0x1,%edx
    2990:	89 f9                	mov    %edi,%ecx
    2992:	48 d3 e2             	shl    %cl,%rdx
    2995:	49 09 14 c6          	or     %rdx,(%r14,%rax,8)
          curcpu += 2;
    2999:	83 44 24 30 02       	addl   $0x2,0x30(%rsp)
      thread_data[x].all_threads = thread_data;
    299e:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    29a3:	4d 89 69 18          	mov    %r13,0x18(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    29a7:	be 10 00 00 00       	mov    $0x10,%esi
    29ac:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].cpu_set = sendercpu;
    29b1:	4d 89 b1 b0 00 00 00 	mov    %r14,0xb0(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    29b8:	45 31 ed             	xor    %r13d,%r13d
      thread_data[x].all_threads = thread_data;
    29bb:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].thread_count = 2;
    29bf:	48 8b 05 9a 51 00 00 	mov    0x519a(%rip),%rax        # 7b60 <_IO_stdin_used+0xb60>
      thread_data[x].kind = KERNEL_THREAD;
    29c6:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].real_thread_index = x;
    29cd:	41 89 69 08          	mov    %ebp,0x8(%r9)
      thread_data[x].thread_count = 2;
    29d1:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].task_count = total_barrier_count;
    29d5:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
    29dd:	4c 89 0c 24          	mov    %r9,(%rsp)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    29e1:	e8 ba f9 ff ff       	call   23a0 <calloc@plt>
    29e6:	4c 8b 0c 24          	mov    (%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    29ea:	be 10 00 00 00       	mov    $0x10,%esi
    29ef:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    29f4:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    29f8:	e8 a3 f9 ff ff       	call   23a0 <calloc@plt>
    29fd:	4c 8b 0c 24          	mov    (%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a01:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2a06:	66 0f 6f 3d 22 51 00 00 	movdqa 0x5122(%rip),%xmm7        # 7b30 <_IO_stdin_used+0xb30>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a0e:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a13:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2a17:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a1f:	e8 7c f9 ff ff       	call   23a0 <calloc@plt>
    2a24:	4c 8b 0c 24          	mov    (%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a28:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_timestamp_count = 0;
    2a2d:	66 0f 6f 1d fb 50 00 00 	movdqa 0x50fb(%rip),%xmm3        # 7b30 <_IO_stdin_used+0xb30>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a35:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a3a:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2a41:	41 0f 11 99 98 00 00 00 	movups %xmm3,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a49:	e8 52 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks = barriers;
    2a4e:	4c 8b 0c 24          	mov    (%rsp),%r9
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a52:	48 89 5c 24 78       	mov    %rbx,0x78(%rsp)
    2a57:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks = barriers;
    2a5a:	49 89 41 38          	mov    %rax,0x38(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a5e:	4d 89 ce             	mov    %r9,%r14
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a61:	49 63 c5             	movslq %r13d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2a64:	be 28 00 00 00       	mov    $0x28,%esi
    2a69:	bf 06 00 00 00       	mov    $0x6,%edi
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a6e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2a73:	48 c1 e0 09          	shl    $0x9,%rax
    2a77:	4c 8d 3c 02          	lea    (%rdx,%rax,1),%r15
    2a7b:	48 89 04 24          	mov    %rax,(%rsp)
    2a7f:	48 8d 05 5a 14 00 00 	lea    0x145a(%rip),%rax        # 3ee0 <do_protected_write>
    2a86:	49 89 87 20 01 00 00 	mov    %rax,0x120(%r15)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2a8d:	e8 0e f9 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2a92:	49 89 87 70 01 00 00 	mov    %rax,0x170(%r15)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2a99:	48 89 c3             	mov    %rax,%rbx
            if ( b == x || b == x + 1) {
    2a9c:	85 ed                	test   %ebp,%ebp
    2a9e:	0f 84 e8 08 00 00    	je     338c <main+0xd9c>
    2aa4:	83 fd 01             	cmp    $0x1,%ebp
    2aa7:	0f 84 99 0c 00 00    	je     3746 <main+0x1156>
    2aad:	83 fd 02             	cmp    $0x2,%ebp
    2ab0:	0f 84 67 0b 00 00    	je     361d <main+0x102d>
    2ab6:	83 fd 03             	cmp    $0x3,%ebp
    2ab9:	0f 84 2c 0a 00 00    	je     34eb <main+0xefb>
    2abf:	83 fd 04             	cmp    $0x4,%ebp
    2ac2:	0f 85 98 00 00 00    	jne    2b60 <main+0x570>
    2ac8:	ba 04 00 00 00       	mov    $0x4,%edx
    2acd:	48 8d 35 81 48 00 00 	lea    0x4881(%rip),%rsi        # 7355 <_IO_stdin_used+0x355>
    2ad4:	bf 01 00 00 00       	mov    $0x1,%edi
    2ad9:	31 c0                	xor    %eax,%eax
    2adb:	e8 70 f9 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ae0:	be 08 00 00 00       	mov    $0x8,%esi
    2ae5:	bf 01 00 00 00       	mov    $0x1,%edi
    2aea:	e8 b1 f8 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2aef:	be 08 00 00 00       	mov    $0x8,%esi
    2af4:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2af9:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2afe:	e8 9d f8 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2b03:	be 80 01 00 00       	mov    $0x180,%esi
    2b08:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b0d:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    2b12:	e8 89 f8 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    2b17:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
              data[1].messages = messages2;
    2b1c:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    2b21:	c7 83 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rbx)
              mailboxes[b].higher = &data[1];
    2b2b:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              data[0].messages_count = 0;
    2b32:	66 0f 6f 3d 06 50 00 00 	movdqa 0x5006(%rip),%xmm7        # 7b40 <_IO_stdin_used+0xb40>
              mailboxes[b].lower = &data[0];
    2b3a:	48 89 83 a0 00 00 00 	mov    %rax,0xa0(%rbx)
              mailboxes[b].higher = &data[1];
    2b41:	48 89 b3 a8 00 00 00 	mov    %rsi,0xa8(%rbx)
              data[0].messages = messages;
    2b48:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    2b4b:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
              data[0].messages_count = 0;
    2b52:	0f 29 b8 80 00 00 00 	movaps %xmm7,0x80(%rax)
              data[1].messages_count = 0;
    2b59:	0f 29 b8 00 02 00 00 	movaps %xmm7,0x200(%rax)
    2b60:	ba 05 00 00 00       	mov    $0x5,%edx
    2b65:	48 8d 35 e9 47 00 00 	lea    0x47e9(%rip),%rsi        # 7355 <_IO_stdin_used+0x355>
    2b6c:	bf 01 00 00 00       	mov    $0x1,%edi
    2b71:	31 c0                	xor    %eax,%eax
    2b73:	e8 d8 f8 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b78:	be 08 00 00 00       	mov    $0x8,%esi
    2b7d:	bf 01 00 00 00       	mov    $0x1,%edi
    2b82:	e8 19 f8 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b87:	be 08 00 00 00       	mov    $0x8,%esi
    2b8c:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b91:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b96:	e8 05 f8 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2b9b:	be 80 01 00 00       	mov    $0x180,%esi
    2ba0:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ba5:	49 89 c7             	mov    %rax,%r15
              struct Data *data = calloc(2, sizeof(struct Data));
    2ba8:	e8 f3 f7 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    2bad:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
              data[0].messages_count = 0;
    2bb2:	66 0f 6f 25 86 4f 00 00 	movdqa 0x4f86(%rip),%xmm4        # 7b40 <_IO_stdin_used+0xb40>
              mailboxes[b].kind = MAILBOX_FRIEND;
    2bba:	c7 83 e8 00 00 00 01 00 00 00 	movl   $0x1,0xe8(%rbx)
              data[1].messages = messages2;
    2bc4:	4c 89 b8 80 01 00 00 	mov    %r15,0x180(%rax)
              mailboxes[b].higher = &data[1];
    2bcb:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              data[0].messages = messages;
    2bd2:	48 89 08             	mov    %rcx,(%rax)
              mailboxes[b].lower = &data[0];
    2bd5:	48 89 83 c8 00 00 00 	mov    %rax,0xc8(%rbx)
              mailboxes[b].higher = &data[1];
    2bdc:	48 89 b3 d0 00 00 00 	mov    %rsi,0xd0(%rbx)
              data[0].messages_count = 0;
    2be3:	0f 29 a0 80 00 00 00 	movaps %xmm4,0x80(%rax)
              data[1].messages_count = 0;
    2bea:	0f 29 a0 00 02 00 00 	movaps %xmm4,0x200(%rax)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2bf1:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
    2bf6:	45 31 ff             	xor    %r15d,%r15d
    2bf9:	44 89 6c 24 20       	mov    %r13d,0x20(%rsp)
    2bfe:	41 89 ed             	mov    %ebp,%r13d
    2c01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            if (b == x || b == x + 1) { continue; }
    2c08:	45 39 fd             	cmp    %r15d,%r13d
    2c0b:	0f 84 9b 00 00 00    	je     2cac <main+0x6bc>
    2c11:	45 39 fc             	cmp    %r15d,%r12d
    2c14:	0f 84 92 00 00 00    	je     2cac <main+0x6bc>
    2c1a:	44 89 fa             	mov    %r15d,%edx
    2c1d:	48 8d 35 4d 47 00 00 	lea    0x474d(%rip),%rsi        # 7371 <_IO_stdin_used+0x371>
    2c24:	bf 01 00 00 00       	mov    $0x1,%edi
    2c29:	31 c0                	xor    %eax,%eax
    2c2b:	e8 20 f8 ff ff       	call   2450 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2c30:	be 08 00 00 00       	mov    $0x8,%esi
    2c35:	bf 01 00 00 00       	mov    $0x1,%edi
    2c3a:	e8 61 f7 ff ff       	call   23a0 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2c3f:	be 08 00 00 00       	mov    $0x8,%esi
    2c44:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2c49:	49 89 c6             	mov    %rax,%r14
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2c4c:	e8 4f f7 ff ff       	call   23a0 <calloc@plt>
            struct Data *data = calloc(2, sizeof(struct Data));
    2c51:	be 80 01 00 00       	mov    $0x180,%esi
    2c56:	bf 02 00 00 00       	mov    $0x2,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2c5b:	48 89 c5             	mov    %rax,%rbp
            struct Data *data = calloc(2, sizeof(struct Data));
    2c5e:	e8 3d f7 ff ff       	call   23a0 <calloc@plt>
            data[0].messages_count = 0;
    2c63:	66 0f 6f 05 d5 4e 00 00 	movdqa 0x4ed5(%rip),%xmm0        # 7b40 <_IO_stdin_used+0xb40>
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2c6b:	c7 43 20 02 00 00 00 	movl   $0x2,0x20(%rbx)
            mailboxes[b].higher = &data[1];
    2c72:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
            mailboxes[b].lower = &data[0];
    2c79:	48 89 03             	mov    %rax,(%rbx)
            mailboxes[b].higher = &data[1];
    2c7c:	48 89 73 08          	mov    %rsi,0x8(%rbx)
            data[0].available = 0;
    2c80:	c7 80 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rax)
            data[0].messages = messages;
    2c8a:	4c 89 30             	mov    %r14,(%rax)
            data[1].messages = messages2;
    2c8d:	48 89 a8 80 01 00 00 	mov    %rbp,0x180(%rax)
            data[1].available = 0;
    2c94:	c7 80 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rax)
            data[0].messages_count = 0;
    2c9e:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
            data[1].messages_count = 0;
    2ca5:	0f 29 80 00 02 00 00 	movaps %xmm0,0x200(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2cac:	41 83 c7 01          	add    $0x1,%r15d
    2cb0:	48 83 c3 28          	add    $0x28,%rbx
    2cb4:	41 83 ff 06          	cmp    $0x6,%r15d
    2cb8:	0f 85 4a ff ff ff    	jne    2c08 <main+0x618>
          char *message = malloc(sizeof(char) * 256);
    2cbe:	be 01 00 00 00       	mov    $0x1,%esi
    2cc3:	bf 00 01 00 00       	mov    $0x100,%edi
    2cc8:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    2ccd:	44 89 ed             	mov    %r13d,%ebp
    2cd0:	44 8b 6c 24 20       	mov    0x20(%rsp),%r13d
    2cd5:	e8 c6 f6 ff ff       	call   23a0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2cda:	bf 18 00 00 00       	mov    $0x18,%edi
          char *message = malloc(sizeof(char) * 256);
    2cdf:	48 89 c3             	mov    %rax,%rbx
          struct Message *messaged = malloc(sizeof(struct Message));
    2ce2:	e8 29 f7 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2ce7:	48 89 df             	mov    %rbx,%rdi
    2cea:	45 89 e9             	mov    %r13d,%r9d
    2ced:	41 89 e8             	mov    %ebp,%r8d
    2cf0:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2cf5:	48 8d 0d 94 49 00 00 	lea    0x4994(%rip),%rcx        # 7690 <_IO_stdin_used+0x690>
    2cfc:	ba 00 01 00 00       	mov    $0x100,%edx
    2d01:	31 c0                	xor    %eax,%eax
    2d03:	be 01 00 00 00       	mov    $0x1,%esi
    2d08:	e8 13 f8 ff ff       	call   2520 <__sprintf_chk@plt>
          messaged->message = message;
    2d0d:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
          messaged->task_index = y;
    2d12:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2d17:	be 20 00 00 00       	mov    $0x20,%esi
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2d1c:	49 8b 56 38          	mov    0x38(%r14),%rdx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2d20:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->task_index = y;
    2d25:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].thread_index;
    2d29:	49 63 46 04          	movslq 0x4(%r14),%rax
          messaged->message = message;
    2d2d:	49 89 1a             	mov    %rbx,(%r10)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2d30:	48 8b 1c 24          	mov    (%rsp),%rbx
          messaged->thread_index = thread_data[x].thread_index;
    2d34:	49 89 42 08          	mov    %rax,0x8(%r10)
    2d38:	49 89 c7             	mov    %rax,%r15
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2d3b:	41 8d 45 01          	lea    0x1(%r13),%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2d3f:	48 01 d3             	add    %rdx,%rbx
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2d42:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2d45:	48 89 14 24          	mov    %rdx,(%rsp)
    2d49:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2d4f:	89 83 90 01 00 00    	mov    %eax,0x190(%rbx)
          thread_data[x].tasks[y].message = messaged;
    2d55:	4c 89 93 88 01 00 00 	mov    %r10,0x188(%rbx)
          thread_data[x].tasks[y].sending = 1;
    2d5c:	c7 83 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rbx)
          thread_data[x].tasks[y].snapshot_count = 99;
    2d66:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2d71:	e8 2a f6 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2d76:	48 8b 14 24          	mov    (%rsp),%rdx
          thread_data[x].tasks[y].current_snapshot = 0;
    2d7a:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2d85:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2d8c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    2d91:	48 8b 00             	mov    (%rax),%rax
    2d94:	8b 48 04             	mov    0x4(%rax),%ecx
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2d97:	4c 39 f0             	cmp    %r14,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2d9a:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2da1:	89 8b 30 01 00 00    	mov    %ecx,0x130(%rbx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2da7:	0f 85 34 10 00 00    	jne    3de1 <main+0x17f1>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2dad:	66 0f 6f 15 9b 4d 00 00 	movdqa 0x4d9b(%rip),%xmm2        # 7b50 <_IO_stdin_used+0xb50>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2db5:	44 89 6b 04          	mov    %r13d,0x4(%rbx)
          thread_data[x].tasks[y].available = 1;
    2db9:	48 8b 05 a8 4d 00 00 	mov    0x4da8(%rip),%rax        # 7b68 <_IO_stdin_used+0xb68>
          thread_data[x].tasks[y].arrived = 0;
    2dc0:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
          thread_data[x].tasks[y].worker_count = thread_count;
    2dca:	c7 83 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rbx)
          thread_data[x].tasks[y].available = 1;
    2dd4:	48 89 83 44 01 00 00 	mov    %rax,0x144(%rbx)
          thread_data[x].tasks[y].thread_count = 2;
    2ddb:	0f 11 93 34 01 00 00 	movups %xmm2,0x134(%rbx)
          if (y == barrier_count - 1) {
    2de2:	41 83 fd 01          	cmp    $0x1,%r13d
    2de6:	0f 84 ca 06 00 00    	je     34b6 <main+0xec6>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2dec:	45 85 ed             	test   %r13d,%r13d
    2def:	0f 84 a8 06 00 00    	je     349d <main+0xead>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    2df5:	4d 89 f1             	mov    %r14,%r9
    2df8:	48 8d 05 51 34 00 00 	lea    0x3451(%rip),%rax        # 6250 <barriered_work>
    2dff:	49 89 d6             	mov    %rdx,%r14
    2e02:	48 89 da             	mov    %rbx,%rdx
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2e05:	be 08 00 00 00       	mov    $0x8,%esi
        thread_data[x].buffers_count = buffers_per_thread;
    2e0a:	4c 89 0c 24          	mov    %r9,(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e0e:	41 83 c4 01          	add    $0x1,%r12d
    2e12:	83 c5 01             	add    $0x1,%ebp
               thread_data[x].tasks[y].run = barriered_work; 
    2e15:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2e1c:	bf 01 00 00 00       	mov    $0x1,%edi
               thread_data[x].tasks[y].run = barriered_work; 
    2e21:	48 8b 5c 24 78       	mov    0x78(%rsp),%rbx
        thread_data[x].buffers_count = buffers_per_thread;
    2e26:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2e31:	e8 6a f5 ff ff       	call   23a0 <calloc@plt>
    2e36:	4c 8b 0c 24          	mov    (%rsp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2e3a:	66 0f 6f 74 24 50    	movdqa 0x50(%rsp),%xmm6
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2e40:	48 89 18             	mov    %rbx,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e43:	48 83 c3 10          	add    $0x10,%rbx
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2e47:	49 89 41 50          	mov    %rax,0x50(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2e4b:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e50:	49 81 c1 c0 00 00 00 	add    $0xc0,%r9
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2e57:	83 44 24 38 01       	addl   $0x1,0x38(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2e5c:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2e5f:	41 0f 11 b6 18 05 00 00 	movups %xmm6,0x518(%r14)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    2e67:	41 c7 86 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r14)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2e72:	49 89 86 28 05 00 00 	mov    %rax,0x528(%r14)
        thread_data[x].tasks[barrier_count].available = 1; 
    2e79:	48 8b 05 e8 4c 00 00 	mov    0x4ce8(%rip),%rax        # 7b68 <_IO_stdin_used+0xb68>
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2e80:	41 c7 86 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r14)
        thread_data[x].tasks[barrier_count].available = 1; 
    2e8b:	49 89 86 44 05 00 00 	mov    %rax,0x544(%r14)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e92:	8b 44 24 68          	mov    0x68(%rsp),%eax
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    2e96:	41 c7 86 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r14)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2ea1:	45 89 be 30 05 00 00 	mov    %r15d,0x530(%r14)
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2ea8:	41 c7 86 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r14)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2eb3:	41 39 c4             	cmp    %eax,%r12d
    2eb6:	0f 85 df f9 ff ff    	jne    289b <main+0x2ab>
    2ebc:	4c 8b ac 24 90 00 00 00 	mov    0x90(%rsp),%r13
    2ec4:	48 8b 74 24 70       	mov    0x70(%rsp),%rsi
    2ec9:	4c 8b 5c 24 28       	mov    0x28(%rsp),%r11
    2ece:	4c 8b a4 24 98 00 00 00 	mov    0x98(%rsp),%r12
  for (int k = 0 ; k < group_count ; k++) {
    2ed6:	49 83 c5 01          	add    $0x1,%r13
    2eda:	48 83 c6 18          	add    $0x18,%rsi
    2ede:	49 83 fd 03          	cmp    $0x3,%r13
    2ee2:	0f 85 5d f9 ff ff    	jne    2845 <main+0x255>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2ee8:	ba 07 00 00 00       	mov    $0x7,%edx
    2eed:	bf 01 00 00 00       	mov    $0x1,%edi
    2ef2:	31 c0                	xor    %eax,%eax
    2ef4:	4c 89 1c 24          	mov    %r11,(%rsp)
    2ef8:	48 8d 35 90 44 00 00 	lea    0x4490(%rip),%rsi        # 738f <_IO_stdin_used+0x38f>
    2eff:	4c 8b a4 24 88 00 00 00 	mov    0x88(%rsp),%r12
    2f07:	e8 44 f5 ff ff       	call   2450 <__printf_chk@plt>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2f0c:	be 08 00 00 00       	mov    $0x8,%esi
    2f11:	bf 02 00 00 00       	mov    $0x2,%edi
    2f16:	e8 85 f4 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2f1b:	4c 8b 1c 24          	mov    (%rsp),%r11
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2f1f:	be 38 00 00 00       	mov    $0x38,%esi
    2f24:	bf 0a 00 00 00       	mov    $0xa,%edi
    my_thread_data[0] = &thread_data[x]; 
    2f29:	4d 8d b3 40 05 00 00 	lea    0x540(%r11),%r14
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2f30:	4c 89 58 08          	mov    %r11,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2f34:	4d 8d ab c0 00 00 00 	lea    0xc0(%r11),%r13
    thread_data[x].threads = my_thread_data;
    2f3b:	49 89 83 58 05 00 00 	mov    %rax,0x558(%r11)
    my_thread_data[0] = &thread_data[x]; 
    2f42:	4c 89 30             	mov    %r14,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2f45:	49 8b 43 38          	mov    0x38(%r11),%rax
    thread_data[x].thread_count = 2;
    2f49:	41 c7 83 68 05 00 00 02 00 00 00 	movl   $0x2,0x568(%r11)
    thread_data[x].thread_index = 0;
    2f54:	41 c7 83 44 05 00 00 00 00 00 00 	movl   $0x0,0x544(%r11)
    thread_data[x].task_count = total_barrier_count;
    2f5f:	41 c7 83 80 05 00 00 03 00 00 00 	movl   $0x3,0x580(%r11)
    thread_data[n].tasks[0].scheduled = 1;
    2f6a:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    2f74:	49 8b 83 f8 00 00 00 	mov    0xf8(%r11),%rax
    2f7b:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    2f80:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2f8a:	e8 11 f4 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2f8f:	be 38 00 00 00       	mov    $0x38,%esi
    2f94:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2f99:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2f9d:	e8 fe f3 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2fa2:	be 38 00 00 00       	mov    $0x38,%esi
    2fa7:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2fac:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2faf:	e8 ec f3 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2fb4:	be 38 00 00 00       	mov    $0x38,%esi
    2fb9:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2fbe:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2fc3:	e8 d8 f3 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2fc8:	be 08 00 00 00       	mov    $0x8,%esi
    2fcd:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2fd2:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2fd7:	e8 c4 f3 ff ff       	call   23a0 <calloc@plt>


  int timer_threadi = group_count * thread_count;
  thread_data[timer_threadi].type = TIMER;
    2fdc:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2fe1:	be 08 00 00 00       	mov    $0x8,%esi
    2fe6:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2feb:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    2fee:	48 8b 05 7b 4b 00 00 	mov    0x4b7b(%rip),%rax        # 7b70 <_IO_stdin_used+0xb70>
  thread_data[timer_threadi].type = TIMER;
    2ff5:	41 c7 83 8c 04 00 00 00 00 00 00 	movl   $0x0,0x48c(%r11)
  thread_data[timer_threadi].task_count = total_barrier_count;
    3000:	49 89 83 c0 04 00 00 	mov    %rax,0x4c0(%r11)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3007:	e8 94 f3 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    300c:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    3011:	bf 01 00 00 00       	mov    $0x1,%edi
    3016:	48 8d 35 81 43 00 00 	lea    0x4381(%rip),%rsi        # 739e <_IO_stdin_used+0x39e>
    301d:	4c 89 70 38          	mov    %r14,0x38(%rax)
    3021:	49 8d 93 80 01 00 00 	lea    0x180(%r11),%rdx
    3028:	49 8d 8b 80 04 00 00 	lea    0x480(%r11),%rcx
    302f:	4c 89 18             	mov    %r11,(%rax)
    3032:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3036:	49 8d 93 40 02 00 00 	lea    0x240(%r11),%rdx
    303d:	4d 8d bb 00 06 00 00 	lea    0x600(%r11),%r15
    3044:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3048:	49 8d 93 00 03 00 00 	lea    0x300(%r11),%rdx
    304f:	48 89 50 20          	mov    %rdx,0x20(%rax)
    3053:	49 8d 93 c0 03 00 00 	lea    0x3c0(%r11),%rdx
    305a:	48 89 50 28          	mov    %rdx,0x28(%rax)
    305e:	49 8d 93 c0 06 00 00 	lea    0x6c0(%r11),%rdx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3065:	49 89 83 98 04 00 00 	mov    %rax,0x498(%r11)
    my_thread_data[n] = &thread_data[n]; 
    306c:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3070:	4c 89 78 40          	mov    %r15,0x40(%rax)
    3074:	48 89 50 48          	mov    %rdx,0x48(%rax)
    3078:	ba 06 00 00 00       	mov    $0x6,%edx
    307d:	4c 89 68 08          	mov    %r13,0x8(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3081:	48 8b 05 f0 4a 00 00 	mov    0x4af0(%rip),%rax        # 7b78 <_IO_stdin_used+0xb78>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3088:	41 c7 83 b0 04 00 00 06 00 00 00 	movl   $0x6,0x4b0(%r11)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3093:	49 89 83 a8 04 00 00 	mov    %rax,0x4a8(%r11)
    309a:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    309c:	41 c7 83 84 04 00 00 00 00 00 00 	movl   $0x0,0x484(%r11)
    my_thread_data[n] = &thread_data[n]; 
    30a7:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    30ac:	e8 9f f3 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    30b1:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    30b6:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    30ba:	48 8d 15 df 0f 00 00 	lea    0xfdf(%rip),%rdx        # 40a0 <timer_thread>
    30c1:	48 8d b5 50 01 00 00 	lea    0x150(%rbp),%rsi
    30c8:	e8 a3 f3 ff ff       	call   2470 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    30cd:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    30d2:	45 31 c0             	xor    %r8d,%r8d
    30d5:	48 89 d9             	mov    %rbx,%rcx
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    30d8:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    30dd:	48 8b 04 24          	mov    (%rsp),%rax
    30e1:	4c 89 64 24 38       	mov    %r12,0x38(%rsp)
    30e6:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    30ec:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    30f1:	45 89 d6             	mov    %r10d,%r14d
    30f4:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    30f9:	4c 89 da             	mov    %r11,%rdx
    30fc:	44 89 c3             	mov    %r8d,%ebx
    30ff:	4c 89 7c 24 30       	mov    %r15,0x30(%rsp)
    3104:	49 89 c7             	mov    %rax,%r15
  int curcpu = 0;
    3107:	4c 89 3c 24          	mov    %r15,(%rsp)
    310b:	44 8d 2c 1b          	lea    (%rbx,%rbx,1),%r13d
    310f:	49 89 cc             	mov    %rcx,%r12
    3112:	48 89 d5             	mov    %rdx,%rbp
    3115:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    311a:	48 89 54 24 68       	mov    %rdx,0x68(%rsp)
    311f:	4c 89 5c 24 70       	mov    %r11,0x70(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    3124:	c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%rbp)
    312b:	44 89 ea             	mov    %r13d,%edx
    312e:	89 d9                	mov    %ebx,%ecx
    3130:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    3132:	c7 45 44 01 00 00 00 	movl   $0x1,0x44(%rbp)
    3139:	48 8d 35 78 45 00 00 	lea    0x4578(%rip),%rsi        # 76b8 <_IO_stdin_used+0x6b8>
    3140:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    3145:	41 83 c5 01          	add    $0x1,%r13d
    3149:	e8 02 f3 ff ff       	call   2450 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    314e:	48 8b 34 24          	mov    (%rsp),%rsi
    3152:	48 89 e9             	mov    %rbp,%rcx
    3155:	4c 89 e7             	mov    %r12,%rdi
    3158:	48 8d 15 91 2c 00 00 	lea    0x2c91(%rip),%rdx        # 5df0 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    315f:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
    3166:	49 83 c4 08          	add    $0x8,%r12
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    316a:	e8 01 f3 ff ff       	call   2470 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    316f:	48 8b 55 f0          	mov    -0x10(%rbp),%rdx
    3173:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
    3178:	be 08 00 00 00       	mov    $0x8,%esi
    317d:	e8 5e f1 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3182:	48 83 04 24 38       	addq   $0x38,(%rsp)
    3187:	45 39 ee             	cmp    %r13d,%r14d
    318a:	75 98                	jne    3124 <main+0xb34>
  for (int k = 0 ; k < group_count ; k++) {
    318c:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    3191:	83 c3 01             	add    $0x1,%ebx
    3194:	49 83 c7 70          	add    $0x70,%r15
    3198:	41 83 c6 02          	add    $0x2,%r14d
    319c:	48 8b 54 24 68       	mov    0x68(%rsp),%rdx
    31a1:	4c 8b 5c 24 70       	mov    0x70(%rsp),%r11
    31a6:	48 83 c1 10          	add    $0x10,%rcx
    31aa:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
    31b1:	83 fb 03             	cmp    $0x3,%ebx
    31b4:	0f 85 4d ff ff ff    	jne    3107 <main+0xb17>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    31ba:	48 8b 05 bf 49 00 00 	mov    0x49bf(%rip),%rax        # 7b80 <_IO_stdin_used+0xb80>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    31c1:	be d8 00 00 00       	mov    $0xd8,%esi
    31c6:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    31cb:	41 c7 83 4c 05 00 00 02 00 00 00 	movl   $0x2,0x54c(%r11)
    31d6:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    31db:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    thread_data[x].task_count = 0;
    31e0:	4c 89 1c 24          	mov    %r11,(%rsp)
    31e4:	49 89 83 80 05 00 00 	mov    %rax,0x580(%r11)
    thread_data[x].type = IO;
    31eb:	4c 8b 7c 24 30       	mov    0x30(%rsp),%r15
    31f0:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    31f5:	4c 8b 64 24 38       	mov    0x38(%rsp),%r12
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    31fa:	4c 89 fd             	mov    %r15,%rbp
    31fd:	49 89 df             	mov    %rbx,%r15
    3200:	e8 9b f1 ff ff       	call   23a0 <calloc@plt>
    3205:	4c 8b 1c 24          	mov    (%rsp),%r11
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3209:	be 00 08 00 00       	mov    $0x800,%esi
    320e:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3210:	49 89 83 98 05 00 00 	mov    %rax,0x598(%r11)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3217:	e8 94 f2 ff ff       	call   24b0 <eventfd@plt>
    321c:	4c 8b 1c 24          	mov    (%rsp),%r11
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3220:	be 08 00 00 00       	mov    $0x8,%esi
    3225:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    322a:	41 89 83 a0 05 00 00 	mov    %eax,0x5a0(%r11)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3231:	e8 6a f1 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3236:	4c 8b 1c 24          	mov    (%rsp),%r11
    323a:	ba 07 00 00 00       	mov    $0x7,%edx
    323f:	48 8d 35 76 41 00 00 	lea    0x4176(%rip),%rsi        # 73bc <_IO_stdin_used+0x3bc>
    3246:	4c 89 68 08          	mov    %r13,0x8(%rax)
    324a:	bf 01 00 00 00       	mov    $0x1,%edi
    324f:	4c 89 18             	mov    %r11,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    3252:	49 89 83 58 05 00 00 	mov    %rax,0x558(%r11)
    3259:	31 c0                	xor    %eax,%eax
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    325b:	41 c7 83 68 05 00 00 02 00 00 00 	movl   $0x2,0x568(%r11)
    thread_data[x].thread_index = x;
    3266:	41 c7 83 44 05 00 00 07 00 00 00 	movl   $0x7,0x544(%r11)
    3271:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    3276:	e8 d5 f1 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    327b:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3280:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3284:	4c 89 f1             	mov    %r14,%rcx
    3287:	48 8d 15 72 23 00 00 	lea    0x2372(%rip),%rdx        # 5600 <io_thread>
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    328e:	41 be 08 00 00 00    	mov    $0x8,%r14d
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3294:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    329b:	e8 d0 f1 ff ff       	call   2470 <pthread_create@plt>
    32a0:	ba 08 00 00 00       	mov    $0x8,%edx
    32a5:	48 8d 35 27 41 00 00 	lea    0x4127(%rip),%rsi        # 73d3 <_IO_stdin_used+0x3d3>
    32ac:	31 c0                	xor    %eax,%eax
    32ae:	bf 01 00 00 00       	mov    $0x1,%edi
    32b3:	e8 98 f1 ff ff       	call   2450 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    32b8:	48 8d 43 40          	lea    0x40(%rbx),%rax
    32bc:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    32c1:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    32c6:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    32cb:	48 05 c0 01 00 00    	add    $0x1c0,%rax
    32d1:	48 89 04 24          	mov    %rax,(%rsp)
    32d5:	44 89 f2             	mov    %r14d,%edx
    32d8:	48 8d 35 0a 41 00 00 	lea    0x410a(%rip),%rsi        # 73e9 <_IO_stdin_used+0x3e9>
    32df:	bf 01 00 00 00       	mov    $0x1,%edi
    32e4:	31 c0                	xor    %eax,%eax
    32e6:	e8 65 f1 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    32eb:	be 08 00 00 00       	mov    $0x8,%esi
    32f0:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    32f5:	48 8b 05 84 48 00 00 	mov    0x4884(%rip),%rax        # 7b80 <_IO_stdin_used+0xb80>
    thread_data[x].type = EXTERNAL;
    32fc:	c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%rbp)
    thread_data[x].task_count = 0;
    3303:	48 89 45 40          	mov    %rax,0x40(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3307:	e8 94 f0 ff ff       	call   23a0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    330c:	be 08 00 00 00       	mov    $0x8,%esi
    3311:	bf 02 00 00 00       	mov    $0x2,%edi
	  thread_data[x].buffers_count = 1;
    3316:	c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3320:	48 89 45 50          	mov    %rax,0x50(%rbp)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3324:	4c 89 20             	mov    %r12,(%rax)
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3327:	49 83 c4 10          	add    $0x10,%r12
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    332b:	e8 70 f0 ff ff       	call   23a0 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    3330:	44 89 75 04          	mov    %r14d,0x4(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3334:	48 8b 34 24          	mov    (%rsp),%rsi
    3338:	48 89 e9             	mov    %rbp,%rcx
    thread_data[x].threads = my_thread_data;
    333b:	48 89 45 18          	mov    %rax,0x18(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    333f:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    3344:	48 8d 15 45 0c 00 00 	lea    0xc45(%rip),%rdx        # 3f90 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    334b:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
      my_thread_data[n] = &thread_data[n]; 
    3352:	48 89 18             	mov    %rbx,(%rax)
    3355:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3359:	48 8b 05 00 48 00 00 	mov    0x4800(%rip),%rax        # 7b60 <_IO_stdin_used+0xb60>
    3360:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3367:	e8 04 f1 ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    336c:	48 83 44 24 08 08    	addq   $0x8,0x8(%rsp)
    3372:	48 83 04 24 38       	addq   $0x38,(%rsp)
    3377:	41 83 fe 08          	cmp    $0x8,%r14d
    337b:	0f 85 f4 04 00 00    	jne    3875 <main+0x1285>
    3381:	41 be 09 00 00 00    	mov    $0x9,%r14d
    3387:	e9 49 ff ff ff       	jmp    32d5 <main+0xce5>
    338c:	31 d2                	xor    %edx,%edx
    338e:	48 8d 35 c0 3f 00 00 	lea    0x3fc0(%rip),%rsi        # 7355 <_IO_stdin_used+0x355>
    3395:	bf 01 00 00 00       	mov    $0x1,%edi
    339a:	31 c0                	xor    %eax,%eax
    339c:	e8 af f0 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    33a1:	be 08 00 00 00       	mov    $0x8,%esi
    33a6:	bf 01 00 00 00       	mov    $0x1,%edi
    33ab:	e8 f0 ef ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    33b0:	be 08 00 00 00       	mov    $0x8,%esi
    33b5:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    33ba:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    33bf:	e8 dc ef ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    33c4:	be 80 01 00 00       	mov    $0x180,%esi
    33c9:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    33ce:	49 89 c7             	mov    %rax,%r15
              struct Data *data = calloc(2, sizeof(struct Data));
    33d1:	e8 ca ef ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    33d6:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    33db:	ba 01 00 00 00       	mov    $0x1,%edx
              data[0].messages_count = 0;
    33e0:	66 0f 6f 25 58 47 00 00 	movdqa 0x4758(%rip),%xmm4        # 7b40 <_IO_stdin_used+0xb40>
              mailboxes[b].higher = &data[1];
    33e8:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    33ef:	48 89 03             	mov    %rax,(%rbx)
    33f2:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages = messages;
    33f7:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    33fa:	4c 89 b8 80 01 00 00 	mov    %r15,0x180(%rax)
              mailboxes[b].higher = &data[1];
    3401:	48 89 73 08          	mov    %rsi,0x8(%rbx)
    3405:	48 8d 35 49 3f 00 00 	lea    0x3f49(%rip),%rsi        # 7355 <_IO_stdin_used+0x355>
              mailboxes[b].kind = MAILBOX_FRIEND;
    340c:	c7 43 20 01 00 00 00 	movl   $0x1,0x20(%rbx)
              data[0].messages_count = 0;
    3413:	0f 29 a0 80 00 00 00 	movaps %xmm4,0x80(%rax)
              data[1].messages_count = 0;
    341a:	0f 29 a0 00 02 00 00 	movaps %xmm4,0x200(%rax)
    3421:	31 c0                	xor    %eax,%eax
    3423:	e8 28 f0 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3428:	be 08 00 00 00       	mov    $0x8,%esi
    342d:	bf 01 00 00 00       	mov    $0x1,%edi
    3432:	e8 69 ef ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3437:	be 08 00 00 00       	mov    $0x8,%esi
    343c:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3441:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3446:	e8 55 ef ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    344b:	be 80 01 00 00       	mov    $0x180,%esi
    3450:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3455:	49 89 c7             	mov    %rax,%r15
              struct Data *data = calloc(2, sizeof(struct Data));
    3458:	e8 43 ef ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    345d:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
              data[0].messages_count = 0;
    3462:	66 0f 6f 35 d6 46 00 00 	movdqa 0x46d6(%rip),%xmm6        # 7b40 <_IO_stdin_used+0xb40>
              mailboxes[b].kind = MAILBOX_FRIEND;
    346a:	c7 43 48 01 00 00 00 	movl   $0x1,0x48(%rbx)
              mailboxes[b].higher = &data[1];
    3471:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    3478:	48 89 43 28          	mov    %rax,0x28(%rbx)
              mailboxes[b].higher = &data[1];
    347c:	48 89 73 30          	mov    %rsi,0x30(%rbx)
              data[0].messages = messages;
    3480:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    3483:	4c 89 b8 80 01 00 00 	mov    %r15,0x180(%rax)
              data[0].messages_count = 0;
    348a:	0f 29 b0 80 00 00 00 	movaps %xmm6,0x80(%rax)
              data[1].messages_count = 0;
    3491:	0f 29 b0 00 02 00 00 	movaps %xmm6,0x200(%rax)
            if ( b == x || b == x + 1) {
    3498:	e9 54 f7 ff ff       	jmp    2bf1 <main+0x601>
    349d:	48 8d 05 cc 2f 00 00 	lea    0x2fcc(%rip),%rax        # 6470 <barriered_work_ingest_andwork>
    34a4:	41 bd 01 00 00 00    	mov    $0x1,%r13d
            thread_data[x].tasks[y].run = barriered_work; 
    34aa:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    34b1:	e9 ab f5 ff ff       	jmp    2a61 <main+0x471>
    34b6:	48 8d 05 93 2d 00 00 	lea    0x2d93(%rip),%rax        # 6250 <barriered_work>
    34bd:	41 bd 02 00 00 00    	mov    $0x2,%r13d
    34c3:	eb e5                	jmp    34aa <main+0xeba>
        my_thread_data[1] = &thread_data[other]; 
    34c5:	49 63 c4             	movslq %r12d,%rax
    34c8:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
        other = (x + 1) % total_threads;
    34cd:	45 89 e7             	mov    %r12d,%r15d
        my_thread_data[1] = &thread_data[other]; 
    34d0:	45 31 c0             	xor    %r8d,%r8d
    34d3:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
    34d7:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    34dc:	48 c1 e2 06          	shl    $0x6,%rdx
    34e0:	48 01 c2             	add    %rax,%rdx
        my_thread_data[0] = &thread_data[x]; 
    34e3:	4c 89 c8             	mov    %r9,%rax
    34e6:	e9 2a f4 ff ff       	jmp    2915 <main+0x325>
    34eb:	ba 03 00 00 00       	mov    $0x3,%edx
    34f0:	48 8d 35 5e 3e 00 00 	lea    0x3e5e(%rip),%rsi        # 7355 <_IO_stdin_used+0x355>
    34f7:	bf 01 00 00 00       	mov    $0x1,%edi
    34fc:	31 c0                	xor    %eax,%eax
    34fe:	e8 4d ef ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3503:	be 08 00 00 00       	mov    $0x8,%esi
    3508:	bf 01 00 00 00       	mov    $0x1,%edi
    350d:	e8 8e ee ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3512:	be 08 00 00 00       	mov    $0x8,%esi
    3517:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    351c:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3521:	e8 7a ee ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    3526:	be 80 01 00 00       	mov    $0x180,%esi
    352b:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3530:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    3535:	e8 66 ee ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    353a:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
              data[1].messages = messages2;
    353f:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    3544:	c7 83 98 00 00 00 01 00 00 00 	movl   $0x1,0x98(%rbx)
              mailboxes[b].higher = &data[1];
    354e:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    3555:	48 89 43 78          	mov    %rax,0x78(%rbx)
    3559:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages_count = 0;
    355e:	66 0f 6f 25 da 45 00 00 	movdqa 0x45da(%rip),%xmm4        # 7b40 <_IO_stdin_used+0xb40>
              data[0].messages = messages;
    3566:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    3569:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
    3570:	ba 04 00 00 00       	mov    $0x4,%edx
              mailboxes[b].higher = &data[1];
    3575:	48 89 b3 80 00 00 00 	mov    %rsi,0x80(%rbx)
    357c:	48 8d 35 d2 3d 00 00 	lea    0x3dd2(%rip),%rsi        # 7355 <_IO_stdin_used+0x355>
              data[0].messages_count = 0;
    3583:	0f 29 a0 80 00 00 00 	movaps %xmm4,0x80(%rax)
              data[1].messages_count = 0;
    358a:	0f 29 a0 00 02 00 00 	movaps %xmm4,0x200(%rax)
    3591:	31 c0                	xor    %eax,%eax
    3593:	e8 b8 ee ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3598:	be 08 00 00 00       	mov    $0x8,%esi
    359d:	bf 01 00 00 00       	mov    $0x1,%edi
    35a2:	e8 f9 ed ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    35a7:	be 08 00 00 00       	mov    $0x8,%esi
    35ac:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    35b1:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    35b6:	e8 e5 ed ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    35bb:	be 80 01 00 00       	mov    $0x180,%esi
    35c0:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    35c5:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    35ca:	e8 d1 ed ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    35cf:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
              data[1].messages = messages2;
    35d4:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    35d9:	c7 83 c0 00 00 00 01 00 00 00 	movl   $0x1,0xc0(%rbx)
              data[0].messages_count = 0;
    35e3:	66 0f 6f 35 55 45 00 00 	movdqa 0x4555(%rip),%xmm6        # 7b40 <_IO_stdin_used+0xb40>
              mailboxes[b].higher = &data[1];
    35eb:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    35f2:	48 89 83 a0 00 00 00 	mov    %rax,0xa0(%rbx)
              mailboxes[b].higher = &data[1];
    35f9:	48 89 b3 a8 00 00 00 	mov    %rsi,0xa8(%rbx)
              data[0].messages = messages;
    3600:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    3603:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
              data[0].messages_count = 0;
    360a:	0f 29 b0 80 00 00 00 	movaps %xmm6,0x80(%rax)
              data[1].messages_count = 0;
    3611:	0f 29 b0 00 02 00 00 	movaps %xmm6,0x200(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3618:	e9 d4 f5 ff ff       	jmp    2bf1 <main+0x601>
    361d:	ba 02 00 00 00       	mov    $0x2,%edx
    3622:	48 8d 35 2c 3d 00 00 	lea    0x3d2c(%rip),%rsi        # 7355 <_IO_stdin_used+0x355>
    3629:	bf 01 00 00 00       	mov    $0x1,%edi
    362e:	31 c0                	xor    %eax,%eax
    3630:	e8 1b ee ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3635:	be 08 00 00 00       	mov    $0x8,%esi
    363a:	bf 01 00 00 00       	mov    $0x1,%edi
    363f:	e8 5c ed ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3644:	be 08 00 00 00       	mov    $0x8,%esi
    3649:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    364e:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3653:	e8 48 ed ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    3658:	be 80 01 00 00       	mov    $0x180,%esi
    365d:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3662:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    3667:	e8 34 ed ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    366c:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
              data[1].messages = messages2;
    3671:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    3676:	c7 43 70 01 00 00 00 	movl   $0x1,0x70(%rbx)
              mailboxes[b].higher = &data[1];
    367d:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    3684:	48 89 43 50          	mov    %rax,0x50(%rbx)
    3688:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages_count = 0;
    368d:	66 0f 6f 1d ab 44 00 00 	movdqa 0x44ab(%rip),%xmm3        # 7b40 <_IO_stdin_used+0xb40>
              data[0].messages = messages;
    3695:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    3698:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
    369f:	ba 03 00 00 00       	mov    $0x3,%edx
              mailboxes[b].higher = &data[1];
    36a4:	48 89 73 58          	mov    %rsi,0x58(%rbx)
    36a8:	48 8d 35 a6 3c 00 00 	lea    0x3ca6(%rip),%rsi        # 7355 <_IO_stdin_used+0x355>
              data[0].messages_count = 0;
    36af:	0f 29 98 80 00 00 00 	movaps %xmm3,0x80(%rax)
              data[1].messages_count = 0;
    36b6:	0f 29 98 00 02 00 00 	movaps %xmm3,0x200(%rax)
    36bd:	31 c0                	xor    %eax,%eax
    36bf:	e8 8c ed ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    36c4:	be 08 00 00 00       	mov    $0x8,%esi
    36c9:	bf 01 00 00 00       	mov    $0x1,%edi
    36ce:	e8 cd ec ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    36d3:	be 08 00 00 00       	mov    $0x8,%esi
    36d8:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    36dd:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    36e2:	e8 b9 ec ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    36e7:	be 80 01 00 00       	mov    $0x180,%esi
    36ec:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    36f1:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    36f6:	e8 a5 ec ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    36fb:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
              data[1].messages = messages2;
    3700:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    3705:	c7 83 98 00 00 00 01 00 00 00 	movl   $0x1,0x98(%rbx)
              data[0].messages_count = 0;
    370f:	66 0f 6f 25 29 44 00 00 	movdqa 0x4429(%rip),%xmm4        # 7b40 <_IO_stdin_used+0xb40>
              mailboxes[b].higher = &data[1];
    3717:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    371e:	48 89 43 78          	mov    %rax,0x78(%rbx)
              mailboxes[b].higher = &data[1];
    3722:	48 89 b3 80 00 00 00 	mov    %rsi,0x80(%rbx)
              data[0].messages = messages;
    3729:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    372c:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
              data[0].messages_count = 0;
    3733:	0f 29 a0 80 00 00 00 	movaps %xmm4,0x80(%rax)
              data[1].messages_count = 0;
    373a:	0f 29 a0 00 02 00 00 	movaps %xmm4,0x200(%rax)
            if ( b == x || b == x + 1) {
    3741:	e9 ab f4 ff ff       	jmp    2bf1 <main+0x601>
    3746:	ba 01 00 00 00       	mov    $0x1,%edx
    374b:	48 8d 35 03 3c 00 00 	lea    0x3c03(%rip),%rsi        # 7355 <_IO_stdin_used+0x355>
    3752:	bf 01 00 00 00       	mov    $0x1,%edi
    3757:	31 c0                	xor    %eax,%eax
    3759:	e8 f2 ec ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    375e:	be 08 00 00 00       	mov    $0x8,%esi
    3763:	bf 01 00 00 00       	mov    $0x1,%edi
    3768:	e8 33 ec ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    376d:	be 08 00 00 00       	mov    $0x8,%esi
    3772:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3777:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    377c:	e8 1f ec ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    3781:	be 80 01 00 00       	mov    $0x180,%esi
    3786:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    378b:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    3790:	e8 0b ec ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    3795:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
              data[1].messages = messages2;
    379a:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    379f:	c7 43 48 01 00 00 00 	movl   $0x1,0x48(%rbx)
              mailboxes[b].higher = &data[1];
    37a6:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    37ad:	48 89 43 28          	mov    %rax,0x28(%rbx)
    37b1:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages_count = 0;
    37b6:	66 0f 6f 35 82 43 00 00 	movdqa 0x4382(%rip),%xmm6        # 7b40 <_IO_stdin_used+0xb40>
              data[0].messages = messages;
    37be:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    37c1:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
    37c8:	ba 02 00 00 00       	mov    $0x2,%edx
              mailboxes[b].higher = &data[1];
    37cd:	48 89 73 30          	mov    %rsi,0x30(%rbx)
    37d1:	48 8d 35 7d 3b 00 00 	lea    0x3b7d(%rip),%rsi        # 7355 <_IO_stdin_used+0x355>
              data[0].messages_count = 0;
    37d8:	0f 29 b0 80 00 00 00 	movaps %xmm6,0x80(%rax)
              data[1].messages_count = 0;
    37df:	0f 29 b0 00 02 00 00 	movaps %xmm6,0x200(%rax)
    37e6:	31 c0                	xor    %eax,%eax
    37e8:	e8 63 ec ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    37ed:	be 08 00 00 00       	mov    $0x8,%esi
    37f2:	bf 01 00 00 00       	mov    $0x1,%edi
    37f7:	e8 a4 eb ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    37fc:	be 08 00 00 00       	mov    $0x8,%esi
    3801:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3806:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    380b:	e8 90 eb ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    3810:	be 80 01 00 00       	mov    $0x180,%esi
    3815:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    381a:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    381f:	e8 7c eb ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    3824:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
              data[0].messages_count = 0;
    3829:	66 0f 6f 1d 0f 43 00 00 	movdqa 0x430f(%rip),%xmm3        # 7b40 <_IO_stdin_used+0xb40>
              mailboxes[b].kind = MAILBOX_FRIEND;
    3831:	c7 43 70 01 00 00 00 	movl   $0x1,0x70(%rbx)
              data[1].messages = messages2;
    3838:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
              mailboxes[b].higher = &data[1];
    383d:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    3844:	48 89 43 50          	mov    %rax,0x50(%rbx)
              mailboxes[b].higher = &data[1];
    3848:	48 89 73 58          	mov    %rsi,0x58(%rbx)
              data[0].messages = messages;
    384c:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    384f:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
              data[0].messages_count = 0;
    3856:	0f 29 98 80 00 00 00 	movaps %xmm3,0x80(%rax)
              data[1].messages_count = 0;
    385d:	0f 29 98 00 02 00 00 	movaps %xmm3,0x200(%rax)
            if ( b == x || b == x + 1) {
    3864:	e9 88 f3 ff ff       	jmp    2bf1 <main+0x601>
            CPU_SET(j, sendercpu);
    3869:	49 81 0e ff 0f 00 00 	orq    $0xfff,(%r14)
          for (int j = 0 ; j < cores ; j++) {
    3870:	e9 29 f1 ff ff       	jmp    299e <main+0x3ae>
    3875:	49 89 db             	mov    %rbx,%r11
    3878:	48 8d 2d 87 3b 00 00 	lea    0x3b87(%rip),%rbp        # 7406 <_IO_stdin_used+0x406>
    387f:	4c 89 fb             	mov    %r15,%rbx
    3882:	4d 8d 6b 04          	lea    0x4(%r11),%r13
    3886:	4d 8d a3 84 07 00 00 	lea    0x784(%r11),%r12
    388d:	4d 89 de             	mov    %r11,%r14
    3890:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    3894:	41 8b 55 00          	mov    0x0(%r13),%edx
    3898:	48 89 ee             	mov    %rbp,%rsi
    389b:	bf 01 00 00 00       	mov    $0x1,%edi
    38a0:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    38a2:	49 81 c5 c0 00 00 00 	add    $0xc0,%r13
    38a9:	e8 a2 eb ff ff       	call   2450 <__printf_chk@plt>
    38ae:	4d 39 e5             	cmp    %r12,%r13
    38b1:	75 dd                	jne    3890 <main+0x12a0>
    38b3:	48 8d 3d 5f 3b 00 00 	lea    0x3b5f(%rip),%rdi        # 7419 <_IO_stdin_used+0x419>
    38ba:	4c 89 34 24          	mov    %r14,(%rsp)
    38be:	45 31 ed             	xor    %r13d,%r13d
    38c1:	4c 8d a4 24 a0 00 00 00 	lea    0xa0(%rsp),%r12
    38c9:	e8 22 ea ff ff       	call   22f0 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    38ce:	4c 8b 34 24          	mov    (%rsp),%r14
    38d2:	48 8d 2d 5e 3b 00 00 	lea    0x3b5e(%rip),%rbp        # 7437 <_IO_stdin_used+0x437>
    void * result; 
    pthread_join(thread[x], &result);
    38d9:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    38dd:	4c 89 e6             	mov    %r12,%rsi
    38e0:	e8 0b ec ff ff       	call   24f0 <pthread_join@plt>
    38e5:	44 89 ea             	mov    %r13d,%edx
    38e8:	48 89 ee             	mov    %rbp,%rsi
    38eb:	bf 01 00 00 00       	mov    $0x1,%edi
    38f0:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    38f2:	49 83 c5 01          	add    $0x1,%r13
    38f6:	e8 55 eb ff ff       	call   2450 <__printf_chk@plt>
    38fb:	49 83 fd 0a          	cmp    $0xa,%r13
    38ff:	75 d8                	jne    38d9 <main+0x12e9>
    3901:	4c 89 74 24 38       	mov    %r14,0x38(%rsp)
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    3906:	45 31 d2             	xor    %r10d,%r10d
  long ingests = 0;
    3909:	45 31 c0             	xor    %r8d,%r8d
  long total = 0;
    390c:	31 c9                	xor    %ecx,%ecx
    390e:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
    3913:	4d 89 d7             	mov    %r10,%r15
    3916:	4c 89 c3             	mov    %r8,%rbx
    3919:	49 89 cd             	mov    %rcx,%r13
  long sents = 0;
    391c:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3925:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  long sends = 0;
    392f:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    3938:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    393d:	4c 8b 74 24 60       	mov    0x60(%rsp),%r14
    3942:	89 44 24 20          	mov    %eax,0x20(%rsp)
    3946:	83 c0 02             	add    $0x2,%eax
    3949:	89 44 24 30          	mov    %eax,0x30(%rsp)
    394d:	4d 89 ec             	mov    %r13,%r12
    3950:	4d 89 fd             	mov    %r15,%r13
    3953:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
      int x = (k * threads_per_group) + d;
    3958:	8b 7c 24 20          	mov    0x20(%rsp),%edi
    395c:	89 f8                	mov    %edi,%eax
    395e:	83 c7 01             	add    $0x1,%edi
        other = abs(x - 1) % total_threads;
    3961:	8d 50 02             	lea    0x2(%rax),%edx
    3964:	89 7c 24 20          	mov    %edi,0x20(%rsp)
    3968:	83 e7 01             	and    $0x1,%edi
    396b:	bf 0a 00 00 00       	mov    $0xa,%edi
    3970:	0f 44 c2             	cmove  %edx,%eax
    3973:	4c 63 f8             	movslq %eax,%r15
    3976:	e8 55 e9 ff ff       	call   22d0 <putchar@plt>
    397b:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3980:	bf 01 00 00 00       	mov    $0x1,%edi
    3985:	48 8d 35 bf 3a 00 00 	lea    0x3abf(%rip),%rsi        # 744b <_IO_stdin_used+0x44b>
    398c:	48 8b 10             	mov    (%rax),%rdx
    398f:	31 c0                	xor    %eax,%eax
    3991:	e8 ba ea ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3996:	41 8b 56 40          	mov    0x40(%r14),%edx
    399a:	85 d2                	test   %edx,%edx
    399c:	0f 8e 38 04 00 00    	jle    3dda <main+0x17ea>
    39a2:	48 63 f2             	movslq %edx,%rsi
    39a5:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    39a9:	31 d2                	xor    %edx,%edx
    39ab:	48 c1 e6 09          	shl    $0x9,%rsi
    39af:	48 01 c6             	add    %rax,%rsi
    39b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    39b8:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    39bf:	48 05 00 02 00 00    	add    $0x200,%rax
    39c5:	48 39 f0             	cmp    %rsi,%rax
    39c8:	75 ee                	jne    39b8 <main+0x13c8>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    39ca:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    39cf:	4b 8d 04 7f          	lea    (%r15,%r15,2),%rax
    39d3:	48 c1 e0 06          	shl    $0x6,%rax
    39d7:	48 01 f8             	add    %rdi,%rax
    39da:	48 63 70 40          	movslq 0x40(%rax),%rsi
    39de:	85 f6                	test   %esi,%esi
    39e0:	7e 20                	jle    3a02 <main+0x1412>
    39e2:	48 8b 40 38          	mov    0x38(%rax),%rax
    39e6:	48 c1 e6 09          	shl    $0x9,%rsi
    39ea:	48 01 c6             	add    %rax,%rsi
    39ed:	0f 1f 00             	nopl   (%rax)
        v += thread_data[other].tasks[n].v;
    39f0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    39f7:	48 05 00 02 00 00    	add    $0x200,%rax
    39fd:	48 39 f0             	cmp    %rsi,%rax
    3a00:	75 ee                	jne    39f0 <main+0x1400>
    3a02:	48 8d 35 57 3a 00 00 	lea    0x3a57(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    3a09:	bf 01 00 00 00       	mov    $0x1,%edi
    3a0e:	31 c0                	xor    %eax,%eax
    3a10:	e8 3b ea ff ff       	call   2450 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3a15:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3a1a:	bf 01 00 00 00       	mov    $0x1,%edi
    3a1f:	48 8b 30             	mov    (%rax),%rsi
    3a22:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3a2c:	48 f7 ee             	imul   %rsi
    3a2f:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3a33:	31 c0                	xor    %eax,%eax
    3a35:	48 d1 fa             	sar    %rdx
    3a38:	48 29 f2             	sub    %rsi,%rdx
    3a3b:	48 8d 35 a6 3c 00 00 	lea    0x3ca6(%rip),%rsi        # 76e8 <_IO_stdin_used+0x6e8>
    3a42:	e8 09 ea ff ff       	call   2450 <__printf_chk@plt>
    3a47:	bf 0a 00 00 00       	mov    $0xa,%edi
    3a4c:	e8 7f e8 ff ff       	call   22d0 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3a51:	41 8b 56 40          	mov    0x40(%r14),%edx
    3a55:	85 d2                	test   %edx,%edx
    3a57:	7e 60                	jle    3ab9 <main+0x14c9>
    3a59:	49 8b 46 38          	mov    0x38(%r14),%rax
    3a5d:	48 63 fa             	movslq %edx,%rdi
    3a60:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    3a65:	48 c1 e7 09          	shl    $0x9,%rdi
    3a69:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    3a6e:	48 01 c7             	add    %rax,%rdi
    3a71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3a78:	48 8b 90 70 01 00 00 	mov    0x170(%rax),%rdx
        total += thread_data[x].tasks[n].n;
    3a7f:	4c 03 a0 08 01 00 00 	add    0x108(%rax),%r12
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3a86:	48 05 00 02 00 00    	add    $0x200,%rax
        ingests += thread_data[x].tasks[n].ingest_count;
    3a8c:	48 03 98 68 ff ff ff 	add    -0x98(%rax),%rbx
        sends += thread_data[x].tasks[n].sends;
    3a93:	4c 03 90 78 ff ff ff 	add    -0x88(%rax),%r10
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3a9a:	48 03 4a 10          	add    0x10(%rdx),%rcx
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3a9e:	4c 03 6a 18          	add    0x18(%rdx),%r13
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3aa2:	48 03 4a 38          	add    0x38(%rdx),%rcx
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3aa6:	4c 03 6a 40          	add    0x40(%rdx),%r13
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3aaa:	48 39 f8             	cmp    %rdi,%rax
    3aad:	75 c9                	jne    3a78 <main+0x1488>
    3aaf:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    3ab4:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3ab9:	45 31 ff             	xor    %r15d,%r15d
    3abc:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    3ac4:	7e 79                	jle    3b3f <main+0x154f>
    3ac6:	4c 89 f0             	mov    %r14,%rax
    3ac9:	49 89 de             	mov    %rbx,%r14
    3acc:	4c 89 fb             	mov    %r15,%rbx
    3acf:	4d 89 e7             	mov    %r12,%r15
    3ad2:	49 89 c4             	mov    %rax,%r12
    3ad5:	0f 1f 00             	nopl   (%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3ad8:	49 8b 84 24 90 00 00 00 	mov    0x90(%r12),%rax
    3ae0:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    3ae4:	48 83 ec 08          	sub    $0x8,%rsp
    3ae8:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3aed:	48 83 c3 01          	add    $0x1,%rbx
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3af1:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3af5:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3af9:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3afd:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3b00:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3b04:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3b07:	48 f7 e5             	mul    %rbp
    3b0a:	8b 49 20             	mov    0x20(%rcx),%ecx
    3b0d:	56                   	push   %rsi
    3b0e:	31 c0                	xor    %eax,%eax
    3b10:	48 8d 35 f1 3b 00 00 	lea    0x3bf1(%rip),%rsi        # 7708 <_IO_stdin_used+0x708>
    3b17:	48 c1 ea 12          	shr    $0x12,%rdx
    3b1b:	49 89 d1             	mov    %rdx,%r9
    3b1e:	ba 02 00 00 00       	mov    $0x2,%edx
    3b23:	e8 28 e9 ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3b28:	41 58                	pop    %r8
    3b2a:	41 59                	pop    %r9
    3b2c:	49 39 9c 24 a0 00 00 00 	cmp    %rbx,0xa0(%r12)
    3b34:	7f a2                	jg     3ad8 <main+0x14e8>
    3b36:	4c 89 f3             	mov    %r14,%rbx
    3b39:	4d 89 e6             	mov    %r12,%r14
    3b3c:	4d 89 fc             	mov    %r15,%r12
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3b3f:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    3b46:	85 f6                	test   %esi,%esi
    3b48:	0f 8e 06 01 00 00    	jle    3c54 <main+0x1664>
    3b4e:	4c 89 6c 24 50       	mov    %r13,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3b53:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    3b57:	31 d2                	xor    %edx,%edx
    3b59:	48 89 5c 24 68       	mov    %rbx,0x68(%rsp)
    3b5e:	4c 89 64 24 70       	mov    %r12,0x70(%rsp)
    3b63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3b68:	49 8b 04 d1          	mov    (%r9,%rdx,8),%rax
    3b6c:	41 89 d5             	mov    %edx,%r13d
    3b6f:	48 8d 1c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rbx
    3b77:	44 8b 00             	mov    (%rax),%r8d
    3b7a:	45 85 c0             	test   %r8d,%r8d
    3b7d:	0f 8e b6 00 00 00    	jle    3c39 <main+0x1649>
    3b83:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3b88:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3b8c:	31 f6                	xor    %esi,%esi
    3b8e:	66 90                	xchg   %ax,%ax
    3b90:	49 89 f4             	mov    %rsi,%r12
    3b93:	45 31 ff             	xor    %r15d,%r15d
    3b96:	49 c1 e4 08          	shl    $0x8,%r12
    3b9a:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    3b9e:	8b 82 94 00 00 00    	mov    0x94(%rdx),%eax
    3ba4:	85 c0                	test   %eax,%eax
    3ba6:	7e 78                	jle    3c20 <main+0x1630>
    3ba8:	48 89 34 24          	mov    %rsi,(%rsp)
    3bac:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3bb0:	4c 89 f9             	mov    %r15,%rcx
    3bb3:	48 83 ec 08          	sub    $0x8,%rsp
    3bb7:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3bbc:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3bc0:	48 c1 e1 05          	shl    $0x5,%rcx
    3bc4:	48 03 8a 88 00 00 00 	add    0x88(%rdx),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3bcb:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3bcf:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3bd3:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3bd6:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3bda:	4c 2b 01             	sub    (%rcx),%r8
    3bdd:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3bde:	48 f7 e5             	mul    %rbp
    3be1:	44 89 e9             	mov    %r13d,%ecx
    3be4:	48 8d 35 6d 3b 00 00 	lea    0x3b6d(%rip),%rsi        # 7758 <_IO_stdin_used+0x758>
    3beb:	31 c0                	xor    %eax,%eax
    3bed:	48 c1 ea 12          	shr    $0x12,%rdx
    3bf1:	49 89 d1             	mov    %rdx,%r9
    3bf4:	ba 02 00 00 00       	mov    $0x2,%edx
    3bf9:	e8 52 e8 ff ff       	call   2450 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3bfe:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    3c02:	5e                   	pop    %rsi
    3c03:	5f                   	pop    %rdi
    3c04:	49 8b 04 19          	mov    (%r9,%rbx,1),%rax
    3c08:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3c0c:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    3c10:	44 39 ba 94 00 00 00 	cmp    %r15d,0x94(%rdx)
    3c17:	7f 97                	jg     3bb0 <main+0x15c0>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3c19:	48 8b 34 24          	mov    (%rsp),%rsi
    3c1d:	44 8b 00             	mov    (%rax),%r8d
    3c20:	48 83 c6 01          	add    $0x1,%rsi
    3c24:	41 39 f0             	cmp    %esi,%r8d
    3c27:	0f 8f 63 ff ff ff    	jg     3b90 <main+0x15a0>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3c2d:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    3c32:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    3c39:	48 83 c2 01          	add    $0x1,%rdx
    3c3d:	39 d6                	cmp    %edx,%esi
    3c3f:	0f 8f 23 ff ff ff    	jg     3b68 <main+0x1578>
    3c45:	4c 8b 6c 24 50       	mov    0x50(%rsp),%r13
    3c4a:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
    3c4f:	4c 8b 64 24 70       	mov    0x70(%rsp),%r12
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c54:	48 83 44 24 28 18    	addq   $0x18,0x28(%rsp)
    3c5a:	8b 7c 24 30          	mov    0x30(%rsp),%edi
    3c5e:	49 81 c6 c0 00 00 00 	add    $0xc0,%r14
    3c65:	39 7c 24 20          	cmp    %edi,0x20(%rsp)
    3c69:	0f 85 e9 fc ff ff    	jne    3958 <main+0x1368>
  for (int k = 0 ; k < group_count ; k++) {
    3c6f:	8b 44 24 20          	mov    0x20(%rsp),%eax
    3c73:	4d 89 ef             	mov    %r13,%r15
    3c76:	48 83 44 24 40 30    	addq   $0x30,0x40(%rsp)
    3c7c:	4d 89 e5             	mov    %r12,%r13
    3c7f:	48 81 44 24 60 80 01 00 00 	addq   $0x180,0x60(%rsp)
    3c88:	83 f8 05             	cmp    $0x5,%eax
    3c8b:	0f 85 a7 fc ff ff    	jne    3938 <main+0x1348>
    3c91:	4c 89 e2             	mov    %r12,%rdx
    3c94:	48 8d 35 d2 37 00 00 	lea    0x37d2(%rip),%rsi        # 746d <_IO_stdin_used+0x46d>
    3c9b:	31 c0                	xor    %eax,%eax
    3c9d:	4c 89 24 24          	mov    %r12,(%rsp)
    3ca1:	bf 01 00 00 00       	mov    $0x1,%edi
    3ca6:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3cab:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    3cb5:	4c 89 7c 24 20       	mov    %r15,0x20(%rsp)
    3cba:	e8 91 e7 ff ff       	call   2450 <__printf_chk@plt>
    3cbf:	bf 0a 00 00 00       	mov    $0xa,%edi
    3cc4:	e8 07 e6 ff ff       	call   22d0 <putchar@plt>
    3cc9:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3cce:	bf 01 00 00 00       	mov    $0x1,%edi
    3cd3:	48 8d 35 d6 3a 00 00 	lea    0x3ad6(%rip),%rsi        # 77b0 <_IO_stdin_used+0x7b0>
    3cda:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3cde:	31 c0                	xor    %eax,%eax
    3ce0:	e8 6b e7 ff ff       	call   2450 <__printf_chk@plt>
    3ce5:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    3cea:	bf 01 00 00 00       	mov    $0x1,%edi
    3cef:	48 8d 35 e2 3a 00 00 	lea    0x3ae2(%rip),%rsi        # 77d8 <_IO_stdin_used+0x7d8>
    3cf6:	4c 89 c0             	mov    %r8,%rax
    3cf9:	49 c1 f8 3f          	sar    $0x3f,%r8
    3cfd:	48 f7 eb             	imul   %rbx
    3d00:	31 c0                	xor    %eax,%eax
    3d02:	48 d1 fa             	sar    %rdx
    3d05:	4c 29 c2             	sub    %r8,%rdx
    3d08:	e8 43 e7 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3d0d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3d12:	bf 01 00 00 00       	mov    $0x1,%edi
    3d17:	48 8d 35 ea 3a 00 00 	lea    0x3aea(%rip),%rsi        # 7808 <_IO_stdin_used+0x808>
    3d1e:	48 f7 eb             	imul   %rbx
    3d21:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3d26:	48 c1 f8 3f          	sar    $0x3f,%rax
    3d2a:	48 d1 fa             	sar    %rdx
    3d2d:	48 29 c2             	sub    %rax,%rdx
    3d30:	31 c0                	xor    %eax,%eax
    3d32:	e8 19 e7 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3d37:	48 8b 0c 24          	mov    (%rsp),%rcx
    3d3b:	bf 01 00 00 00       	mov    $0x1,%edi
    3d40:	48 8d 35 f1 3a 00 00 	lea    0x3af1(%rip),%rsi        # 7838 <_IO_stdin_used+0x838>
    3d47:	48 89 c8             	mov    %rcx,%rax
    3d4a:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3d4e:	48 f7 eb             	imul   %rbx
    3d51:	31 c0                	xor    %eax,%eax
    3d53:	48 d1 fa             	sar    %rdx
    3d56:	48 29 ca             	sub    %rcx,%rdx
    3d59:	e8 f2 e6 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3d5e:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3d63:	bf 01 00 00 00       	mov    $0x1,%edi
    3d68:	48 8d 35 12 37 00 00 	lea    0x3712(%rip),%rsi        # 7481 <_IO_stdin_used+0x481>
    3d6f:	48 f7 eb             	imul   %rbx
    3d72:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3d77:	48 c1 f8 3f          	sar    $0x3f,%rax
    3d7b:	48 d1 fa             	sar    %rdx
    3d7e:	48 29 c2             	sub    %rax,%rdx
    3d81:	31 c0                	xor    %eax,%eax
    3d83:	e8 c8 e6 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3d88:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    3d8d:	bf 01 00 00 00       	mov    $0x1,%edi
    3d92:	48 8d 35 f9 36 00 00 	lea    0x36f9(%rip),%rsi        # 7492 <_IO_stdin_used+0x492>
    3d99:	4c 89 d0             	mov    %r10,%rax
    3d9c:	48 f7 eb             	imul   %rbx
    3d9f:	4c 89 d0             	mov    %r10,%rax
    3da2:	48 c1 f8 3f          	sar    $0x3f,%rax
    3da6:	48 d1 fa             	sar    %rdx
    3da9:	48 29 c2             	sub    %rax,%rdx
    3dac:	31 c0                	xor    %eax,%eax
    3dae:	e8 9d e6 ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3db3:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    3dbb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3dc4:	75 25                	jne    3deb <main+0x17fb>
    3dc6:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    3dcd:	31 c0                	xor    %eax,%eax
    3dcf:	5b                   	pop    %rbx
    3dd0:	5d                   	pop    %rbp
    3dd1:	41 5c                	pop    %r12
    3dd3:	41 5d                	pop    %r13
    3dd5:	41 5e                	pop    %r14
    3dd7:	41 5f                	pop    %r15
    3dd9:	c3                   	ret
      long v = 0;
    3dda:	31 d2                	xor    %edx,%edx
    3ddc:	e9 e9 fb ff ff       	jmp    39ca <main+0x13da>
            exit(1);
    3de1:	bf 01 00 00 00       	mov    $0x1,%edi
    3de6:	e8 b5 e6 ff ff       	call   24a0 <exit@plt>
}
    3deb:	e8 40 e5 ff ff       	call   2330 <__stack_chk_fail@plt>

0000000000003df0 <_start>:
    3df0:	f3 0f 1e fa          	endbr64
    3df4:	31 ed                	xor    %ebp,%ebp
    3df6:	49 89 d1             	mov    %rdx,%r9
    3df9:	5e                   	pop    %rsi
    3dfa:	48 89 e2             	mov    %rsp,%rdx
    3dfd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3e01:	50                   	push   %rax
    3e02:	54                   	push   %rsp
    3e03:	45 31 c0             	xor    %r8d,%r8d
    3e06:	31 c9                	xor    %ecx,%ecx
    3e08:	48 8d 3d e1 e7 ff ff 	lea    -0x181f(%rip),%rdi        # 25f0 <main>
    3e0f:	ff 15 c3 61 00 00    	call   *0x61c3(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3e15:	f4                   	hlt
    3e16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003e20 <deregister_tm_clones>:
    3e20:	48 8d 3d f9 61 00 00 	lea    0x61f9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3e27:	48 8d 05 f2 61 00 00 	lea    0x61f2(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    3e2e:	48 39 f8             	cmp    %rdi,%rax
    3e31:	74 15                	je     3e48 <deregister_tm_clones+0x28>
    3e33:	48 8b 05 a6 61 00 00 	mov    0x61a6(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    3e3a:	48 85 c0             	test   %rax,%rax
    3e3d:	74 09                	je     3e48 <deregister_tm_clones+0x28>
    3e3f:	ff e0                	jmp    *%rax
    3e41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3e48:	c3                   	ret
    3e49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003e50 <register_tm_clones>:
    3e50:	48 8d 3d c9 61 00 00 	lea    0x61c9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3e57:	48 8d 35 c2 61 00 00 	lea    0x61c2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    3e5e:	48 29 fe             	sub    %rdi,%rsi
    3e61:	48 89 f0             	mov    %rsi,%rax
    3e64:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3e68:	48 c1 f8 03          	sar    $0x3,%rax
    3e6c:	48 01 c6             	add    %rax,%rsi
    3e6f:	48 d1 fe             	sar    %rsi
    3e72:	74 14                	je     3e88 <register_tm_clones+0x38>
    3e74:	48 8b 05 75 61 00 00 	mov    0x6175(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    3e7b:	48 85 c0             	test   %rax,%rax
    3e7e:	74 08                	je     3e88 <register_tm_clones+0x38>
    3e80:	ff e0                	jmp    *%rax
    3e82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3e88:	c3                   	ret
    3e89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003e90 <__do_global_dtors_aux>:
    3e90:	f3 0f 1e fa          	endbr64
    3e94:	80 3d 8d 61 00 00 00 	cmpb   $0x0,0x618d(%rip)        # a028 <completed.0>
    3e9b:	75 2b                	jne    3ec8 <__do_global_dtors_aux+0x38>
    3e9d:	55                   	push   %rbp
    3e9e:	48 83 3d 52 61 00 00 00 	cmpq   $0x0,0x6152(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3ea6:	48 89 e5             	mov    %rsp,%rbp
    3ea9:	74 0c                	je     3eb7 <__do_global_dtors_aux+0x27>
    3eab:	48 8b 3d 56 61 00 00 	mov    0x6156(%rip),%rdi        # a008 <__dso_handle>
    3eb2:	e8 f9 e3 ff ff       	call   22b0 <__cxa_finalize@plt>
    3eb7:	e8 64 ff ff ff       	call   3e20 <deregister_tm_clones>
    3ebc:	c6 05 65 61 00 00 01 	movb   $0x1,0x6165(%rip)        # a028 <completed.0>
    3ec3:	5d                   	pop    %rbp
    3ec4:	c3                   	ret
    3ec5:	0f 1f 00             	nopl   (%rax)
    3ec8:	c3                   	ret
    3ec9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003ed0 <frame_dummy>:
    3ed0:	f3 0f 1e fa          	endbr64
    3ed4:	e9 77 ff ff ff       	jmp    3e50 <register_tm_clones>
    3ed9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003ee0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3ee0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3ee4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3eeb:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    3eef:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3ef7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    3efb:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3eff:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3f06:	48 85 c9             	test   %rcx,%rcx
    3f09:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3f10:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3f14:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3f18:	31 c0                	xor    %eax,%eax
    3f1a:	c3                   	ret
    3f1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003f20 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3f20:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3f24:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    3f2b:	85 c9                	test   %ecx,%ecx
    3f2d:	7e 4f                	jle    3f7e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3f2f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3f36:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    3f3d:	48 c1 e1 09          	shl    $0x9,%rcx
    3f41:	48 8b 50 18          	mov    0x18(%rax),%rdx
    3f45:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3f49:	48 8b 70 38          	mov    0x38(%rax),%rsi
    3f4d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3f4f:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    3f53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3f58:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3f60:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3f68:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3f73:	48 05 00 02 00 00    	add    $0x200,%rax
    3f79:	48 39 c1             	cmp    %rax,%rcx
    3f7c:	75 da                	jne    3f58 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    3f7e:	0f ae f8             	sfence
}
    3f81:	31 c0                	xor    %eax,%eax
    3f83:	c3                   	ret
    3f84:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3f8f:	90                   	nop

0000000000003f90 <external_thread>:
void * external_thread(void *arg) {
    3f90:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3f94:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    3f98:	0f 85 fb 00 00 00    	jne    4099 <external_thread+0x109>
void * external_thread(void *arg) {
    3f9e:	41 57                	push   %r15
    3fa0:	49 89 ff             	mov    %rdi,%r15
    3fa3:	41 56                	push   %r14
    3fa5:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    3fa7:	4c 8d 2d 56 30 00 00 	lea    0x3056(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    3fae:	41 54                	push   %r12
    3fb0:	55                   	push   %rbp
    3fb1:	53                   	push   %rbx
    3fb2:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    3fb6:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    3fbc:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    3fc0:	85 c9                	test   %ecx,%ecx
    3fc2:	7e 6e                	jle    4032 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3fc4:	45 31 e4             	xor    %r12d,%r12d
    3fc7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3fd0:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    3fd8:	31 db                	xor    %ebx,%ebx
    3fda:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3fde:	48 8b 06             	mov    (%rsi),%rax
    3fe1:	8b 10                	mov    (%rax),%edx
    3fe3:	85 d2                	test   %edx,%edx
    3fe5:	7e 2a                	jle    4011 <external_thread+0x81>
    3fe7:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    3feb:	48 89 dd             	mov    %rbx,%rbp
    3fee:	48 c1 e5 08          	shl    $0x8,%rbp
    3ff2:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    3ff6:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    3ffd:	45 85 c0             	test   %r8d,%r8d
    4000:	74 36                	je     4038 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4002:	48 83 c3 01          	add    $0x1,%rbx
    4006:	39 da                	cmp    %ebx,%edx
    4008:	7f e1                	jg     3feb <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    400a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    4011:	49 83 c4 01          	add    $0x1,%r12
    4015:	44 39 e1             	cmp    %r12d,%ecx
    4018:	7f b6                	jg     3fd0 <external_thread+0x40>
  while (data->running == 1) {
    401a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    401f:	74 9f                	je     3fc0 <external_thread+0x30>
}
    4021:	48 83 c4 08          	add    $0x8,%rsp
    4025:	31 c0                	xor    %eax,%eax
    4027:	5b                   	pop    %rbx
    4028:	5d                   	pop    %rbp
    4029:	41 5c                	pop    %r12
    402b:	41 5d                	pop    %r13
    402d:	41 5e                	pop    %r14
    402f:	41 5f                	pop    %r15
    4031:	c3                   	ret
  while (data->running == 1) {
    4032:	eb fe                	jmp    4032 <external_thread+0xa2>
    4034:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    4038:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    403b:	48 8b 06             	mov    (%rsi),%rax
    403e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4042:	48 01 ef             	add    %rbp,%rdi
    4045:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    404c:	48 c1 e6 05          	shl    $0x5,%rsi
    4050:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4057:	bf 04 00 00 00       	mov    $0x4,%edi
    405c:	e8 af e2 ff ff       	call   2310 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    4061:	49 8b 47 50          	mov    0x50(%r15),%rax
    4065:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    4069:	48 8b 40 08          	mov    0x8(%rax),%rax
    406d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    4078:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    407b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    407f:	48 83 c3 01          	add    $0x1,%rbx
    4083:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    4087:	48 8b 06             	mov    (%rsi),%rax
    408a:	8b 10                	mov    (%rax),%edx
    408c:	39 da                	cmp    %ebx,%edx
    408e:	0f 8f 53 ff ff ff    	jg     3fe7 <external_thread+0x57>
    4094:	e9 71 ff ff ff       	jmp    400a <external_thread+0x7a>
}
    4099:	31 c0                	xor    %eax,%eax
    409b:	c3                   	ret
    409c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000040a0 <timer_thread>:
void* timer_thread(void *arg) {
    40a0:	f3 0f 1e fa          	endbr64
    40a4:	41 57                	push   %r15
    40a6:	48 8d 35 63 2f 00 00 	lea    0x2f63(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    40ad:	41 56                	push   %r14
    40af:	41 55                	push   %r13
    40b1:	41 54                	push   %r12
    40b3:	55                   	push   %rbp
    40b4:	48 89 fd             	mov    %rdi,%rbp
    40b7:	53                   	push   %rbx
    40b8:	48 83 ec 58          	sub    $0x58,%rsp
    40bc:	8b 57 04             	mov    0x4(%rdi),%edx
    40bf:	bf 01 00 00 00       	mov    $0x1,%edi
    40c4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    40cd:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    40d2:	31 c0                	xor    %eax,%eax
    40d4:	e8 77 e3 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    40d9:	66 0f 6f 05 6f 39 00 00 	movdqa 0x396f(%rip),%xmm0        # 7a50 <_IO_stdin_used+0xa50>
    40e1:	ba 88 13 00 00       	mov    $0x1388,%edx
    40e6:	31 c0                	xor    %eax,%eax
    40e8:	48 8d 35 33 2f 00 00 	lea    0x2f33(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    40ef:	bf 01 00 00 00       	mov    $0x1,%edi
    40f4:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    40f9:	e8 52 e3 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    40fe:	44 8b 65 44          	mov    0x44(%rbp),%r12d
    4102:	45 85 e4             	test   %r12d,%r12d
    4105:	0f 84 a3 00 00 00    	je     41ae <timer_thread+0x10e>
  int n = 0;
    410b:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    410e:	45 31 e4             	xor    %r12d,%r12d
    4111:	49 89 e6             	mov    %rsp,%r14
    y++;
    4114:	31 db                	xor    %ebx,%ebx
    4116:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    411b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    nanosleep(&preempt , &rem2);
    4120:	4c 89 ef             	mov    %r13,%rdi
    4123:	4c 89 f6             	mov    %r14,%rsi
    n++;
    4126:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    412a:	e8 21 e2 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    412f:	48 63 45 30          	movslq 0x30(%rbp),%rax
    y++;
    4133:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4138:	85 c0                	test   %eax,%eax
    413a:	7e 49                	jle    4185 <timer_thread+0xe5>
    413c:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4140:	49 c1 e4 09          	shl    $0x9,%r12
    4144:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4148:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    4150:	4c 8b 11             	mov    (%rcx),%r10
    4153:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4155:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4159:	99                   	cltd
    415a:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    415e:	49 8b 72 38          	mov    0x38(%r10),%rsi
    4162:	48 63 d2             	movslq %edx,%rdx
    4165:	48 c1 e2 09          	shl    $0x9,%rdx
    4169:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4174:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4180:	49 39 c8             	cmp    %rcx,%r8
    4183:	75 cb                	jne    4150 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    4185:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4188:	48 8b 45 18          	mov    0x18(%rbp),%rax
  while (data->running && n < times) {
    418c:	44 8b 45 44          	mov    0x44(%rbp),%r8d
    if (y >= data->threads[0]->task_count) {
    4190:	48 8b 00             	mov    (%rax),%rax
    y++;
    4193:	39 78 40             	cmp    %edi,0x40(%rax)
    4196:	0f 4e fb             	cmovle %ebx,%edi
    4199:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    419c:	45 85 c0             	test   %r8d,%r8d
    419f:	74 0d                	je     41ae <timer_thread+0x10e>
    41a1:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    41a8:	0f 85 72 ff ff ff    	jne    4120 <timer_thread+0x80>
    41ae:	48 8d 3d 83 2e 00 00 	lea    0x2e83(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    41b5:	e8 36 e1 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    41ba:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    41be:	85 d2                	test   %edx,%edx
    41c0:	7e 73                	jle    4235 <timer_thread+0x195>
    for (int y = 0 ; y < data->task_count ; y++) {
    41c2:	48 63 45 40          	movslq 0x40(%rbp),%rax
    41c6:	85 c0                	test   %eax,%eax
    41c8:	7e 6b                	jle    4235 <timer_thread+0x195>
    41ca:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    41ce:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    41d2:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    41da:	31 c9                	xor    %ecx,%ecx
    41dc:	48 89 c6             	mov    %rax,%rsi
    41df:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    41e3:	48 8b 40 38          	mov    0x38(%rax),%rax
    41e7:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    41eb:	f7 c6 00 02 00 00    	test   $0x200,%esi
    41f1:	74 1d                	je     4210 <timer_thread+0x170>
    41f3:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    41fd:	48 05 00 02 00 00    	add    $0x200,%rax
    4203:	48 39 c2             	cmp    %rax,%rdx
    4206:	74 24                	je     422c <timer_thread+0x18c>
    4208:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->threads[x]->tasks[y].sending = 0;
    4210:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    421a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4220:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4227:	48 39 c2             	cmp    %rax,%rdx
    422a:	75 e4                	jne    4210 <timer_thread+0x170>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    422c:	48 83 c1 08          	add    $0x8,%rcx
    4230:	48 39 cf             	cmp    %rcx,%rdi
    4233:	75 aa                	jne    41df <timer_thread+0x13f>
  asm volatile ("mfence" ::: "memory");
    4235:	0f ae f0             	mfence
  struct timespec drain = {
    4238:	66 0f 6f 05 20 38 00 00 	movdqa 0x3820(%rip),%xmm0        # 7a60 <_IO_stdin_used+0xa60>
    4240:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4245:	48 63 45 28          	movslq 0x28(%rbp),%rax
    y++;
    4249:	45 8d 44 24 01       	lea    0x1(%r12),%r8d
    for (int x = 0 ; x < data->thread_count ; x++) {
    424e:	85 c0                	test   %eax,%eax
    4250:	7e 4b                	jle    429d <timer_thread+0x1fd>
    4252:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4256:	4d 63 e4             	movslq %r12d,%r12
    4259:	49 c1 e4 09          	shl    $0x9,%r12
    425d:	48 8d 3c c1          	lea    (%rcx,%rax,8),%rdi
    4261:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4268:	48 8b 19             	mov    (%rcx),%rbx
    426b:	44 89 c0             	mov    %r8d,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    426e:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4272:	99                   	cltd
    4273:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4276:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    427a:	48 63 d2             	movslq %edx,%rdx
    427d:	48 c1 e2 09          	shl    $0x9,%rdx
    4281:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    428c:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4298:	48 39 cf             	cmp    %rcx,%rdi
    429b:	75 cb                	jne    4268 <timer_thread+0x1c8>
    asm volatile ("mfence" ::: "memory");
    429d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    42a0:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    42a4:	8b 4d 30             	mov    0x30(%rbp),%ecx
    y++;
    42a7:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    42aa:	48 8b 07             	mov    (%rdi),%rax
    y++;
    42ad:	44 39 40 40          	cmp    %r8d,0x40(%rax)
    42b1:	45 0f 4f e0          	cmovg  %r8d,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    42b5:	85 c9                	test   %ecx,%ecx
    42b7:	0f 8e 0d 01 00 00    	jle    43ca <timer_thread+0x32a>
    42bd:	45 31 ff             	xor    %r15d,%r15d
    int all_empty = 1;
    42c0:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    42c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int y = 0 ; y < 2 ; y++) {
    42d0:	31 db                	xor    %ebx,%ebx
    42d2:	45 89 fd             	mov    %r15d,%r13d
    42d5:	4e 8d 34 fd 00 00 00 00 	lea    0x0(,%r15,8),%r14
    42dd:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    42df:	85 c9                	test   %ecx,%ecx
    42e1:	0f 8e 91 00 00 00    	jle    4378 <timer_thread+0x2d8>
    42e7:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    42eb:	4a 8b 14 37          	mov    (%rdi,%r14,1),%rdx
    42ef:	48 89 d8             	mov    %rbx,%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    42f2:	45 31 c0             	xor    %r8d,%r8d
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    42f5:	48 c1 e0 09          	shl    $0x9,%rax
    42f9:	48 03 42 38          	add    0x38(%rdx),%rax
    42fd:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    4304:	eb 1c                	jmp    4322 <timer_thread+0x282>
    4306:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4310:	48 85 d2             	test   %rdx,%rdx
    4313:	7f 27                	jg     433c <timer_thread+0x29c>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4315:	41 83 c0 01          	add    $0x1,%r8d
    4319:	48 83 c0 28          	add    $0x28,%rax
    431d:	41 39 c8             	cmp    %ecx,%r8d
    4320:	74 7e                	je     43a0 <timer_thread+0x300>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4322:	48 8b 10             	mov    (%rax),%rdx
    4325:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    432c:	48 8b 50 08          	mov    0x8(%rax),%rdx
    4330:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    4337:	4d 85 c9             	test   %r9,%r9
    433a:	7e d4                	jle    4310 <timer_thread+0x270>
    433c:	48 83 ec 08          	sub    $0x8,%rsp
    4340:	89 f1                	mov    %esi,%ecx
    4342:	bf 01 00 00 00       	mov    $0x1,%edi
    4347:	31 c0                	xor    %eax,%eax
    4349:	52                   	push   %rdx
    434a:	48 8d 35 0c 2d 00 00 	lea    0x2d0c(%rip),%rsi        # 705d <_IO_stdin_used+0x5d>
    4351:	44 89 ea             	mov    %r13d,%edx
    4354:	e8 f7 e0 ff ff       	call   2450 <__printf_chk@plt>
      for (int y = 0 ; y < 2 ; y++) {
    4359:	5a                   	pop    %rdx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    435a:	8b 4d 30             	mov    0x30(%rbp),%ecx
      for (int y = 0 ; y < 2 ; y++) {
    435d:	5e                   	pop    %rsi
    435e:	48 83 fb 01          	cmp    $0x1,%rbx
    4362:	74 54                	je     43b8 <timer_thread+0x318>
    4364:	48 83 c3 01          	add    $0x1,%rbx
    4368:	45 31 db             	xor    %r11d,%r11d
    436b:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    436d:	85 c9                	test   %ecx,%ecx
    436f:	0f 8f 72 ff ff ff    	jg     42e7 <timer_thread+0x247>
    4375:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4378:	49 83 c7 01          	add    $0x1,%r15
    437c:	44 39 f9             	cmp    %r15d,%ecx
    437f:	0f 8f 4b ff ff ff    	jg     42d0 <timer_thread+0x230>
    if (all_empty == 1) {
    4385:	41 83 fb 01          	cmp    $0x1,%r11d
    4389:	74 3f                	je     43ca <timer_thread+0x32a>
      nanosleep(&drain , &drainrem);
    438b:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4390:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4395:	e8 b6 df ff ff       	call   2350 <nanosleep@plt>
    439a:	e9 a6 fe ff ff       	jmp    4245 <timer_thread+0x1a5>
    439f:	90                   	nop
      for (int y = 0 ; y < 2 ; y++) {
    43a0:	48 83 fb 01          	cmp    $0x1,%rbx
    43a4:	74 d2                	je     4378 <timer_thread+0x2d8>
    43a6:	48 83 c3 01          	add    $0x1,%rbx
    43aa:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    43ac:	e9 3a ff ff ff       	jmp    42eb <timer_thread+0x24b>
    43b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    43b8:	49 83 c7 01          	add    $0x1,%r15
    43bc:	45 31 db             	xor    %r11d,%r11d
    43bf:	44 39 f9             	cmp    %r15d,%ecx
    43c2:	0f 8f 08 ff ff ff    	jg     42d0 <timer_thread+0x230>
    43c8:	eb bb                	jmp    4385 <timer_thread+0x2e5>
    43ca:	48 8d 3d 83 2c 00 00 	lea    0x2c83(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    43d1:	e8 1a df ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    43d6:	8b 7d 44             	mov    0x44(%rbp),%edi
    43d9:	85 ff                	test   %edi,%edi
    43db:	0f 84 ed 00 00 00    	je     44ce <timer_thread+0x42e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    43e1:	8b 45 2c             	mov    0x2c(%rbp),%eax
    43e4:	31 db                	xor    %ebx,%ebx
    43e6:	4c 8d 25 87 2c 00 00 	lea    0x2c87(%rip),%r12        # 7074 <_IO_stdin_used+0x74>
    43ed:	4c 8d 2d 9b 2c 00 00 	lea    0x2c9b(%rip),%r13        # 708f <_IO_stdin_used+0x8f>
    43f4:	85 c0                	test   %eax,%eax
    43f6:	7e 3b                	jle    4433 <timer_thread+0x393>
    43f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4400:	31 c0                	xor    %eax,%eax
    4402:	89 da                	mov    %ebx,%edx
    4404:	4c 89 e6             	mov    %r12,%rsi
    4407:	bf 01 00 00 00       	mov    $0x1,%edi
    440c:	e8 3f e0 ff ff       	call   2450 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4411:	48 8b 45 18          	mov    0x18(%rbp),%rax
    4415:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4419:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    441d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4424:	0f 84 d1 00 00 00    	je     44fb <timer_thread+0x45b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    442a:	48 83 c3 01          	add    $0x1,%rbx
    442e:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    4431:	7f cd                	jg     4400 <timer_thread+0x360>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4433:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    4437:	85 d2                	test   %edx,%edx
    4439:	7e 7d                	jle    44b8 <timer_thread+0x418>
      for (int y = 0 ; y < data->task_count ; y++) {
    443b:	8b 45 40             	mov    0x40(%rbp),%eax
    443e:	85 c0                	test   %eax,%eax
    4440:	7e 76                	jle    44b8 <timer_thread+0x418>
    4442:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4445:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    4449:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4451:	31 c9                	xor    %ecx,%ecx
    4453:	48 c1 e6 09          	shl    $0x9,%rsi
    4457:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4460:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4464:	48 8b 40 38          	mov    0x38(%rax),%rax
    4468:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    446c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4472:	74 1c                	je     4490 <timer_thread+0x3f0>
    4474:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    447e:	48 05 00 02 00 00    	add    $0x200,%rax
    4484:	48 39 d0             	cmp    %rdx,%rax
    4487:	74 26                	je     44af <timer_thread+0x40f>
    4489:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4490:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    449a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    44a0:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    44aa:	48 39 d0             	cmp    %rdx,%rax
    44ad:	75 e1                	jne    4490 <timer_thread+0x3f0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    44af:	48 83 c1 08          	add    $0x8,%rcx
    44b3:	48 39 f9             	cmp    %rdi,%rcx
    44b6:	75 a8                	jne    4460 <timer_thread+0x3c0>
    asm volatile ("mfence" ::: "memory");
    44b8:	0f ae f0             	mfence
    44bb:	48 8d 3d df 2b 00 00 	lea    0x2bdf(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    44c2:	e8 29 de ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    44c7:	c7 45 44 00 00 00 00 	movl   $0x0,0x44(%rbp)
    44ce:	48 8d 3d d3 2b 00 00 	lea    0x2bd3(%rip),%rdi        # 70a8 <_IO_stdin_used+0xa8>
    44d5:	e8 16 de ff ff       	call   22f0 <puts@plt>
}
    44da:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    44df:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    44e8:	75 40                	jne    452a <timer_thread+0x48a>
    44ea:	48 83 c4 58          	add    $0x58,%rsp
    44ee:	31 c0                	xor    %eax,%eax
    44f0:	5b                   	pop    %rbx
    44f1:	5d                   	pop    %rbp
    44f2:	41 5c                	pop    %r12
    44f4:	41 5d                	pop    %r13
    44f6:	41 5e                	pop    %r14
    44f8:	41 5f                	pop    %r15
    44fa:	c3                   	ret
    44fb:	4c 89 ef             	mov    %r13,%rdi
    44fe:	e8 ed dd ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4503:	48 8b 45 18          	mov    0x18(%rbp),%rax
    4507:	be 01 00 00 00       	mov    $0x1,%esi
    450c:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4510:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4514:	8b 78 60             	mov    0x60(%rax),%edi
    4517:	e8 e4 de ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    451c:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    451f:	0f 8f db fe ff ff    	jg     4400 <timer_thread+0x360>
    4525:	e9 09 ff ff ff       	jmp    4433 <timer_thread+0x393>
}
    452a:	e8 01 de ff ff       	call   2330 <__stack_chk_fail@plt>
    452f:	90                   	nop

0000000000004530 <sendm.part.0>:
int sendm(struct BarrierTask *data) {
    4530:	41 57                	push   %r15
    4532:	41 56                	push   %r14
    4534:	41 55                	push   %r13
    4536:	41 54                	push   %r12
    4538:	55                   	push   %rbp
    4539:	53                   	push   %rbx
    453a:	48 8d 9f 88 01 00 00 	lea    0x188(%rdi),%rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    4541:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    4547:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    454c:	48 8d 9f 90 01 00 00 	lea    0x190(%rdi),%rbx
    4553:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    4558:	85 c0                	test   %eax,%eax
    455a:	0f 8e 59 01 00 00    	jle    46b9 <sendm.part.0+0x189>
    4560:	49 89 fe             	mov    %rdi,%r14
    4563:	45 31 e4             	xor    %r12d,%r12d
    4566:	45 31 ff             	xor    %r15d,%r15d
    4569:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    4570:	45 39 be 30 01 00 00 	cmp    %r15d,0x130(%r14)
    4577:	0f 84 2b 01 00 00    	je     46a8 <sendm.part.0+0x178>
        struct Data *them = data->mailboxes[n].higher;
    457d:	4d 8b 86 70 01 00 00 	mov    0x170(%r14),%r8
    4584:	4d 01 e0             	add    %r12,%r8
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4587:	45 8b 48 20          	mov    0x20(%r8),%r9d
        struct Data *them = data->mailboxes[n].higher;
    458b:	49 8b 78 08          	mov    0x8(%r8),%rdi
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    458f:	41 83 f9 02          	cmp    $0x2,%r9d
    4593:	0f 84 2f 01 00 00    	je     46c8 <sendm.part.0+0x198>
        for (; them->messages_count < min;) {
    4599:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    45a0:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    45a7:	48 39 e9             	cmp    %rbp,%rcx
    45aa:	0f 8d ee 00 00 00    	jge    469e <sendm.part.0+0x16e>
    45b0:	49 8b 86 08 01 00 00 	mov    0x108(%r14),%rax
    45b7:	48 39 e9             	cmp    %rbp,%rcx
    45ba:	49 89 eb             	mov    %rbp,%r11
          them->messages[them->messages_count++] = data->message; 
    45bd:	48 8b 17             	mov    (%rdi),%rdx
    45c0:	41 0f 9c c5          	setl   %r13b
    45c4:	49 29 cb             	sub    %rcx,%r11
    45c7:	48 89 44 24 d0       	mov    %rax,-0x30(%rsp)
    45cc:	49 8b 40 10          	mov    0x10(%r8),%rax
    45d0:	49 8d 5b ff          	lea    -0x1(%r11),%rbx
    45d4:	4c 89 5c 24 c8       	mov    %r11,-0x38(%rsp)
    45d9:	48 89 44 24 d8       	mov    %rax,-0x28(%rsp)
    45de:	48 83 fb 02          	cmp    $0x2,%rbx
    45e2:	0f 86 98 01 00 00    	jbe    4780 <sendm.part.0+0x250>
    45e8:	45 84 ed             	test   %r13b,%r13b
    45eb:	0f 84 8f 01 00 00    	je     4780 <sendm.part.0+0x250>
    45f1:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    45f9:	4a 8d 04 12          	lea    (%rdx,%r10,1),%rax
    45fd:	48 89 44 24 e0       	mov    %rax,-0x20(%rsp)
    4602:	49 89 c3             	mov    %rax,%r11
    4605:	48 8d 04 ea          	lea    (%rdx,%rbp,8),%rax
    4609:	48 39 44 24 e8       	cmp    %rax,-0x18(%rsp)
    460e:	0f 83 cc 00 00 00    	jae    46e0 <sendm.part.0+0x1b0>
    4614:	4c 89 d8             	mov    %r11,%rax
    4617:	4c 8b 5c 24 f0       	mov    -0x10(%rsp),%r11
    461c:	48 89 ce             	mov    %rcx,%rsi
    461f:	4c 39 d8             	cmp    %r11,%rax
    4622:	0f 83 b8 00 00 00    	jae    46e0 <sendm.part.0+0x1b0>
    4628:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4630:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    4637:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    463b:	48 83 c6 01          	add    $0x1,%rsi
    463f:	48 39 f5             	cmp    %rsi,%rbp
    4642:	7f ec                	jg     4630 <sendm.part.0+0x100>
    4644:	0f 1f 40 00          	nopl   0x0(%rax)
    4648:	31 f6                	xor    %esi,%esi
    464a:	45 84 ed             	test   %r13b,%r13b
    464d:	4c 8b 5c 24 d0       	mov    -0x30(%rsp),%r11
    4652:	48 0f 45 f3          	cmovne %rbx,%rsi
    4656:	4d 8d 5c 33 01       	lea    0x1(%r11,%rsi,1),%r11
    465b:	48 8d 4c 31 01       	lea    0x1(%rcx,%rsi,1),%rcx
    4660:	4d 89 9e 08 01 00 00 	mov    %r11,0x108(%r14)
    4667:	4c 8b 5c 24 d8       	mov    -0x28(%rsp),%r11
    466c:	4d 8d 5c 33 01       	lea    0x1(%r11,%rsi,1),%r11
    4671:	4d 89 58 10          	mov    %r11,0x10(%r8)
    4675:	48 89 8f 80 00 00 00 	mov    %rcx,0x80(%rdi)
    467c:	48 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%rcx
    4684:	bb 00 00 00 00       	mov    $0x0,%ebx
    4689:	48 0f 44 cb          	cmove  %rbx,%rcx
    468d:	4c 01 d2             	add    %r10,%rdx
    4690:	48 89 04 0a          	mov    %rax,(%rdx,%rcx,1)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4694:	41 83 f9 02          	cmp    $0x2,%r9d
    4698:	0f 84 c2 00 00 00    	je     4760 <sendm.part.0+0x230>
        asm volatile ("sfence" ::: "memory");
    469e:	0f ae f8             	sfence
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    46a1:	41 8b 86 40 01 00 00 	mov    0x140(%r14),%eax
    46a8:	41 83 c7 01          	add    $0x1,%r15d
    46ac:	49 83 c4 28          	add    $0x28,%r12
    46b0:	41 39 c7             	cmp    %eax,%r15d
    46b3:	0f 8c b7 fe ff ff    	jl     4570 <sendm.part.0+0x40>
}
    46b9:	5b                   	pop    %rbx
    46ba:	5d                   	pop    %rbp
    46bb:	41 5c                	pop    %r12
    46bd:	41 5d                	pop    %r13
    46bf:	41 5e                	pop    %r14
    46c1:	41 5f                	pop    %r15
    46c3:	c3                   	ret
    46c4:	0f 1f 40 00          	nopl   0x0(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    46c8:	8b 97 00 01 00 00    	mov    0x100(%rdi),%edx
    46ce:	83 fa 01             	cmp    $0x1,%edx
    46d1:	0f 84 b9 00 00 00    	je     4790 <sendm.part.0+0x260>
        else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    46d7:	85 d2                	test   %edx,%edx
    46d9:	74 cd                	je     46a8 <sendm.part.0+0x178>
    46db:	e9 b9 fe ff ff       	jmp    4599 <sendm.part.0+0x69>
    46e0:	4c 8b 5c 24 c8       	mov    -0x38(%rsp),%r11
    46e5:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    46ec:	48 8b 74 24 e0       	mov    -0x20(%rsp),%rsi
    46f1:	49 d1 eb             	shr    %r11
    46f4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    46f9:	4c 89 dd             	mov    %r11,%rbp
    46fc:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    4700:	48 c1 e5 04          	shl    $0x4,%rbp
    4704:	49 89 eb             	mov    %rbp,%r11
    4707:	48 01 f5             	add    %rsi,%rbp
    470a:	41 83 e3 10          	and    $0x10,%r11d
    470e:	74 11                	je     4721 <sendm.part.0+0x1f1>
          them->messages[them->messages_count++] = data->message; 
    4710:	0f 11 06             	movups %xmm0,(%rsi)
        for (; them->messages_count < min;) {
    4713:	48 83 c6 10          	add    $0x10,%rsi
    4717:	4c 8b 5c 24 c8       	mov    -0x38(%rsp),%r11
    471c:	48 39 f5             	cmp    %rsi,%rbp
    471f:	74 1a                	je     473b <sendm.part.0+0x20b>
    4721:	4c 8b 5c 24 c8       	mov    -0x38(%rsp),%r11
          them->messages[them->messages_count++] = data->message; 
    4726:	0f 11 06             	movups %xmm0,(%rsi)
    4729:	48 83 c6 20          	add    $0x20,%rsi
    472d:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
        for (; them->messages_count < min;) {
    4731:	48 39 f5             	cmp    %rsi,%rbp
    4734:	75 f0                	jne    4726 <sendm.part.0+0x1f6>
    4736:	4c 89 5c 24 c8       	mov    %r11,-0x38(%rsp)
    473b:	4c 89 de             	mov    %r11,%rsi
    473e:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    4742:	48 01 ce             	add    %rcx,%rsi
    4745:	41 83 e3 01          	and    $0x1,%r11d
    4749:	0f 84 f9 fe ff ff    	je     4648 <sendm.part.0+0x118>
          them->messages[them->messages_count++] = data->message; 
    474f:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    4756:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    475a:	e9 e9 fe ff ff       	jmp    4648 <sendm.part.0+0x118>
    475f:	90                   	nop
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4760:	83 bf 00 01 00 00 01 	cmpl   $0x1,0x100(%rdi)
    4767:	0f 85 31 ff ff ff    	jne    469e <sendm.part.0+0x16e>
          them->available = 0;
    476d:	c7 87 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdi)
    4777:	e9 22 ff ff ff       	jmp    469e <sendm.part.0+0x16e>
    477c:	0f 1f 40 00          	nopl   0x0(%rax)
          them->messages[them->messages_count++] = data->message; 
    4780:	48 89 ce             	mov    %rcx,%rsi
    4783:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    478b:	e9 a0 fe ff ff       	jmp    4630 <sendm.part.0+0x100>
        for (; them->messages_count < min;) {
    4790:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    4797:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    479e:	48 39 cd             	cmp    %rcx,%rbp
    47a1:	0f 8f 09 fe ff ff    	jg     45b0 <sendm.part.0+0x80>
    47a7:	eb c4                	jmp    476d <sendm.part.0+0x23d>
    47a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000047b0 <strtolower>:
void strtolower(char *str) {
    47b0:	f3 0f 1e fa          	endbr64
    47b4:	55                   	push   %rbp
    47b5:	53                   	push   %rbx
    47b6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    47ba:	48 0f be 1f          	movsbq (%rdi),%rbx
    47be:	84 db                	test   %bl,%bl
    47c0:	74 24                	je     47e6 <strtolower+0x36>
    47c2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    47c5:	e8 46 dd ff ff       	call   2510 <__ctype_tolower_loc@plt>
    47ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    47d0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    47d3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    47d7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    47da:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    47dd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    47e2:	84 db                	test   %bl,%bl
    47e4:	75 ea                	jne    47d0 <strtolower+0x20>
}
    47e6:	48 83 c4 08          	add    $0x8,%rsp
    47ea:	5b                   	pop    %rbx
    47eb:	5d                   	pop    %rbp
    47ec:	c3                   	ret
    47ed:	0f 1f 00             	nopl   (%rax)

00000000000047f0 <zh_malloc>:
void *zh_malloc(size_t size) {
    47f0:	f3 0f 1e fa          	endbr64
    47f4:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    47f8:	e8 13 dc ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    47fd:	48 85 c0             	test   %rax,%rax
    4800:	74 05                	je     4807 <zh_malloc+0x17>
}
    4802:	48 83 c4 08          	add    $0x8,%rsp
    4806:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4807:	48 8b 0d 12 58 00 00 	mov    0x5812(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    480e:	ba 28 00 00 00       	mov    $0x28,%edx
    4813:	be 01 00 00 00       	mov    $0x1,%esi
    4818:	48 8d 3d 89 2c 00 00 	lea    0x2c89(%rip),%rdi        # 74a8 <_IO_stdin_used+0x4a8>
    481f:	e8 9c dc ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4824:	bf 01 00 00 00       	mov    $0x1,%edi
    4829:	e8 72 dc ff ff       	call   24a0 <exit@plt>
    482e:	66 90                	xchg   %ax,%ax

0000000000004830 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4830:	f3 0f 1e fa          	endbr64
    4834:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4835:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    483a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    483d:	e8 1e db ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4842:	48 85 c0             	test   %rax,%rax
    4845:	74 11                	je     4858 <get_filename_ext+0x28>
    4847:	48 39 c3             	cmp    %rax,%rbx
    484a:	74 0c                	je     4858 <get_filename_ext+0x28>
    return dot + 1;
    484c:	48 83 c0 01          	add    $0x1,%rax
}
    4850:	5b                   	pop    %rbx
    4851:	c3                   	ret
    4852:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4858:	48 8d 05 91 28 00 00 	lea    0x2891(%rip),%rax        # 70f0 <_IO_stdin_used+0xf0>
}
    485f:	5b                   	pop    %rbx
    4860:	c3                   	ret
    4861:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    486c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004870 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4870:	f3 0f 1e fa          	endbr64
    4874:	41 55                	push   %r13
    4876:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4879:	48 89 fe             	mov    %rdi,%rsi
    487c:	41 54                	push   %r12
    487e:	55                   	push   %rbp
    487f:	48 89 d5             	mov    %rdx,%rbp
    4882:	ba 00 04 00 00       	mov    $0x400,%edx
    4887:	53                   	push   %rbx
    4888:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    488f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4898:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    48a0:	31 c0                	xor    %eax,%eax
    48a2:	49 89 e4             	mov    %rsp,%r12
    48a5:	4c 89 e7             	mov    %r12,%rdi
    48a8:	e8 83 db ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    48ad:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    48b2:	84 db                	test   %bl,%bl
    48b4:	74 24                	je     48da <send_headers+0x6a>
        *str = (char)tolower(*str);
    48b6:	e8 55 dc ff ff       	call   2510 <__ctype_tolower_loc@plt>
    48bb:	48 8b 08             	mov    (%rax),%rcx
    48be:	4c 89 e0             	mov    %r12,%rax
    48c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    48c8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    48cb:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    48cf:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    48d2:	48 0f be 18          	movsbq (%rax),%rbx
    48d6:	84 db                	test   %bl,%bl
    48d8:	75 ee                	jne    48c8 <send_headers+0x58>
    void *buf = malloc(size);
    48da:	bf 11 00 00 00       	mov    $0x11,%edi
    48df:	e8 2c db ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    48e4:	48 85 c0             	test   %rax,%rax
    48e7:	0f 84 7e 04 00 00    	je     4d6b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    48ed:	66 0f 6f 05 7b 31 00 00 	movdqa 0x317b(%rip),%xmm0        # 7a70 <_IO_stdin_used+0xa70>
    iov[0].iov_base = zh_malloc(slen);
    48f5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    48f9:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    48fe:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4906:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    490a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    490d:	e8 fe da ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4912:	48 85 c0             	test   %rax,%rax
    4915:	0f 84 50 04 00 00    	je     4d6b <send_headers+0x4fb>
    491b:	66 0f 6f 05 5d 31 00 00 	movdqa 0x315d(%rip),%xmm0        # 7a80 <_IO_stdin_used+0xa80>
    iov[1].iov_base = zh_malloc(slen);
    4923:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4927:	4c 89 e7             	mov    %r12,%rdi
    492a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4934:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    493c:	0f 11 00             	movups %xmm0,(%rax)
    493f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4943:	be 2e 00 00 00       	mov    $0x2e,%esi
    4948:	e8 13 da ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    494d:	48 85 c0             	test   %rax,%rax
    4950:	0f 84 ea 02 00 00    	je     4c40 <send_headers+0x3d0>
    4956:	4c 39 e0             	cmp    %r12,%rax
    4959:	0f 84 e1 02 00 00    	je     4c40 <send_headers+0x3d0>
    return dot + 1;
    495f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4963:	48 8d 3d 54 27 00 00 	lea    0x2754(%rip),%rdi        # 70be <_IO_stdin_used+0xbe>
    496a:	48 89 de             	mov    %rbx,%rsi
    496d:	e8 3e da ff ff       	call   23b0 <strcmp@plt>
    4972:	85 c0                	test   %eax,%eax
    4974:	75 20                	jne    4996 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4976:	66 0f 6f 05 12 31 00 00 	movdqa 0x3112(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
    497e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4986:	66 0f 6f 05 12 31 00 00 	movdqa 0x3112(%rip),%xmm0        # 7aa0 <_IO_stdin_used+0xaa0>
    498e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4996:	48 89 de             	mov    %rbx,%rsi
    4999:	48 8d 3d 22 27 00 00 	lea    0x2722(%rip),%rdi        # 70c2 <_IO_stdin_used+0xc2>
    49a0:	e8 0b da ff ff       	call   23b0 <strcmp@plt>
    49a5:	85 c0                	test   %eax,%eax
    49a7:	75 20                	jne    49c9 <send_headers+0x159>
    49a9:	66 0f 6f 05 df 30 00 00 	movdqa 0x30df(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
    49b1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    49b9:	66 0f 6f 05 df 30 00 00 	movdqa 0x30df(%rip),%xmm0        # 7aa0 <_IO_stdin_used+0xaa0>
    49c1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    49c9:	48 89 de             	mov    %rbx,%rsi
    49cc:	48 8d 3d f4 26 00 00 	lea    0x26f4(%rip),%rdi        # 70c7 <_IO_stdin_used+0xc7>
    49d3:	e8 d8 d9 ff ff       	call   23b0 <strcmp@plt>
    49d8:	85 c0                	test   %eax,%eax
    49da:	0f 84 10 02 00 00    	je     4bf0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    49e0:	48 89 de             	mov    %rbx,%rsi
    49e3:	48 8d 3d e1 26 00 00 	lea    0x26e1(%rip),%rdi        # 70cb <_IO_stdin_used+0xcb>
    49ea:	e8 c1 d9 ff ff       	call   23b0 <strcmp@plt>
    49ef:	85 c0                	test   %eax,%eax
    49f1:	0f 84 a9 02 00 00    	je     4ca0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    49f7:	48 89 de             	mov    %rbx,%rsi
    49fa:	48 8d 3d ce 26 00 00 	lea    0x26ce(%rip),%rdi        # 70cf <_IO_stdin_used+0xcf>
    4a01:	e8 aa d9 ff ff       	call   23b0 <strcmp@plt>
    4a06:	85 c0                	test   %eax,%eax
    4a08:	0f 84 6a 02 00 00    	je     4c78 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4a0e:	48 89 de             	mov    %rbx,%rsi
    4a11:	48 8d 3d fa 26 00 00 	lea    0x26fa(%rip),%rdi        # 7112 <_IO_stdin_used+0x112>
    4a18:	e8 93 d9 ff ff       	call   23b0 <strcmp@plt>
    4a1d:	85 c0                	test   %eax,%eax
    4a1f:	0f 84 2b 02 00 00    	je     4c50 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4a25:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4a28:	0f 84 52 01 00 00    	je     4b80 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4a2e:	48 89 de             	mov    %rbx,%rsi
    4a31:	48 8d 3d 9b 26 00 00 	lea    0x269b(%rip),%rdi        # 70d3 <_IO_stdin_used+0xd3>
    4a38:	e8 73 d9 ff ff       	call   23b0 <strcmp@plt>
    4a3d:	85 c0                	test   %eax,%eax
    4a3f:	0f 84 ab 02 00 00    	je     4cf0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4a45:	48 89 de             	mov    %rbx,%rsi
    4a48:	48 8d 3d 88 26 00 00 	lea    0x2688(%rip),%rdi        # 70d7 <_IO_stdin_used+0xd7>
    4a4f:	e8 5c d9 ff ff       	call   23b0 <strcmp@plt>
    4a54:	85 c0                	test   %eax,%eax
    4a56:	0f 84 6c 02 00 00    	je     4cc8 <send_headers+0x458>
    slen = strlen(send_buffer);
    4a5c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4a64:	4c 89 e7             	mov    %r12,%rdi
    4a67:	e8 b4 d8 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4a6c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4a6f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4a72:	e8 99 d9 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4a77:	48 85 c0             	test   %rax,%rax
    4a7a:	0f 84 eb 02 00 00    	je     4d6b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4a80:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4a84:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4a88:	83 fb 08             	cmp    $0x8,%ebx
    4a8b:	0f 83 3f 01 00 00    	jae    4bd0 <send_headers+0x360>
    4a91:	f6 c3 04             	test   $0x4,%bl
    4a94:	0f 85 7b 02 00 00    	jne    4d15 <send_headers+0x4a5>
    4a9a:	85 db                	test   %ebx,%ebx
    4a9c:	74 13                	je     4ab1 <send_headers+0x241>
    4a9e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4aa6:	88 10                	mov    %dl,(%rax)
    4aa8:	f6 c3 02             	test   $0x2,%bl
    4aab:	0f 85 96 02 00 00    	jne    4d47 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4ab1:	4d 89 e8             	mov    %r13,%r8
    4ab4:	48 8d 0d 20 26 00 00 	lea    0x2620(%rip),%rcx        # 70db <_IO_stdin_used+0xdb>
    4abb:	4c 89 e7             	mov    %r12,%rdi
    4abe:	31 c0                	xor    %eax,%eax
    4ac0:	ba 00 04 00 00       	mov    $0x400,%edx
    4ac5:	be 01 00 00 00       	mov    $0x1,%esi
    4aca:	e8 51 da ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4acf:	4c 89 e7             	mov    %r12,%rdi
    4ad2:	e8 49 d8 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4ad7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4ada:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4add:	e8 2e d9 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4ae2:	48 85 c0             	test   %rax,%rax
    4ae5:	0f 84 80 02 00 00    	je     4d6b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4aeb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4aef:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4af3:	83 fb 08             	cmp    $0x8,%ebx
    4af6:	0f 83 1c 01 00 00    	jae    4c18 <send_headers+0x3a8>
    4afc:	f6 c3 04             	test   $0x4,%bl
    4aff:	0f 85 29 02 00 00    	jne    4d2e <send_headers+0x4be>
    4b05:	85 db                	test   %ebx,%ebx
    4b07:	74 13                	je     4b1c <send_headers+0x2ac>
    4b09:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4b11:	88 10                	mov    %dl,(%rax)
    4b13:	f6 c3 02             	test   $0x2,%bl
    4b16:	0f 85 3d 02 00 00    	jne    4d59 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4b1c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4b21:	bf 02 00 00 00       	mov    $0x2,%edi
    4b26:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4b2e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4b36:	e8 d5 d8 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4b3b:	48 85 c0             	test   %rax,%rax
    4b3e:	0f 84 27 02 00 00    	je     4d6b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4b44:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4b4c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4b50:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4b58:	66 89 10             	mov    %dx,(%rax)
}
    4b5b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4b63:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b6c:	0f 85 20 02 00 00    	jne    4d92 <send_headers+0x522>
    4b72:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4b79:	5b                   	pop    %rbx
    4b7a:	5d                   	pop    %rbp
    4b7b:	41 5c                	pop    %r12
    4b7d:	41 5d                	pop    %r13
    4b7f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4b80:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4b84:	0f 85 a4 fe ff ff    	jne    4a2e <send_headers+0x1be>
    4b8a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4b8e:	0f 85 9a fe ff ff    	jne    4a2e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4b94:	66 0f 6f 05 54 2f 00 00 	movdqa 0x2f54(%rip),%xmm0        # 7af0 <_IO_stdin_used+0xaf0>
    4b9c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4ba6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4bae:	66 0f 6f 05 4a 2f 00 00 	movdqa 0x2f4a(%rip),%xmm0        # 7b00 <_IO_stdin_used+0xb00>
    4bb6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4bbe:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4bc6:	e9 63 fe ff ff       	jmp    4a2e <send_headers+0x1be>
    4bcb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4bd0:	89 da                	mov    %ebx,%edx
    4bd2:	48 89 c7             	mov    %rax,%rdi
    4bd5:	4c 89 e6             	mov    %r12,%rsi
    4bd8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4bdd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4be2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4be5:	c1 e9 03             	shr    $0x3,%ecx
    4be8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4beb:	e9 c1 fe ff ff       	jmp    4ab1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4bf0:	66 0f 6f 05 98 2e 00 00 	movdqa 0x2e98(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
    4bf8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4c00:	66 0f 6f 05 a8 2e 00 00 	movdqa 0x2ea8(%rip),%xmm0        # 7ab0 <_IO_stdin_used+0xab0>
    4c08:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4c10:	e9 cb fd ff ff       	jmp    49e0 <send_headers+0x170>
    4c15:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4c18:	89 da                	mov    %ebx,%edx
    4c1a:	48 89 c7             	mov    %rax,%rdi
    4c1d:	4c 89 e6             	mov    %r12,%rsi
    4c20:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4c25:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4c2a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4c2d:	c1 e9 03             	shr    $0x3,%ecx
    4c30:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4c33:	e9 e4 fe ff ff       	jmp    4b1c <send_headers+0x2ac>
    4c38:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4c40:	48 8d 1d a9 24 00 00 	lea    0x24a9(%rip),%rbx        # 70f0 <_IO_stdin_used+0xf0>
    4c47:	e9 94 fd ff ff       	jmp    49e0 <send_headers+0x170>
    4c4c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4c50:	66 0f 6f 05 78 2e 00 00 	movdqa 0x2e78(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    4c58:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4c60:	66 0f 6f 05 78 2e 00 00 	movdqa 0x2e78(%rip),%xmm0        # 7ae0 <_IO_stdin_used+0xae0>
    4c68:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4c70:	e9 b0 fd ff ff       	jmp    4a25 <send_headers+0x1b5>
    4c75:	0f 1f 00             	nopl   (%rax)
    4c78:	66 0f 6f 05 50 2e 00 00 	movdqa 0x2e50(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    4c80:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4c88:	66 0f 6f 05 50 2e 00 00 	movdqa 0x2e50(%rip),%xmm0        # 7ae0 <_IO_stdin_used+0xae0>
    4c90:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4c98:	e9 71 fd ff ff       	jmp    4a0e <send_headers+0x19e>
    4c9d:	0f 1f 00             	nopl   (%rax)
    4ca0:	66 0f 6f 05 e8 2d 00 00 	movdqa 0x2de8(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
    4ca8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4cb0:	66 0f 6f 05 08 2e 00 00 	movdqa 0x2e08(%rip),%xmm0        # 7ac0 <_IO_stdin_used+0xac0>
    4cb8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4cc0:	e9 32 fd ff ff       	jmp    49f7 <send_headers+0x187>
    4cc5:	0f 1f 00             	nopl   (%rax)
    4cc8:	66 0f 6f 05 00 2e 00 00 	movdqa 0x2e00(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    4cd0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4cd8:	66 0f 6f 05 40 2e 00 00 	movdqa 0x2e40(%rip),%xmm0        # 7b20 <_IO_stdin_used+0xb20>
    4ce0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4ce8:	e9 6f fd ff ff       	jmp    4a5c <send_headers+0x1ec>
    4ced:	0f 1f 00             	nopl   (%rax)
    4cf0:	66 0f 6f 05 d8 2d 00 00 	movdqa 0x2dd8(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    4cf8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4d00:	66 0f 6f 05 08 2e 00 00 	movdqa 0x2e08(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4d08:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4d10:	e9 30 fd ff ff       	jmp    4a45 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4d15:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4d1c:	89 db                	mov    %ebx,%ebx
    4d1e:	89 10                	mov    %edx,(%rax)
    4d20:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4d25:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4d29:	e9 83 fd ff ff       	jmp    4ab1 <send_headers+0x241>
    4d2e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4d35:	89 db                	mov    %ebx,%ebx
    4d37:	89 10                	mov    %edx,(%rax)
    4d39:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4d3e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4d42:	e9 d5 fd ff ff       	jmp    4b1c <send_headers+0x2ac>
    4d47:	89 db                	mov    %ebx,%ebx
    4d49:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4d4f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4d54:	e9 58 fd ff ff       	jmp    4ab1 <send_headers+0x241>
    4d59:	89 db                	mov    %ebx,%ebx
    4d5b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4d61:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4d66:	e9 b1 fd ff ff       	jmp    4b1c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4d6b:	48 8b 0d ae 52 00 00 	mov    0x52ae(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4d72:	ba 28 00 00 00       	mov    $0x28,%edx
    4d77:	be 01 00 00 00       	mov    $0x1,%esi
    4d7c:	48 8d 3d 25 27 00 00 	lea    0x2725(%rip),%rdi        # 74a8 <_IO_stdin_used+0x4a8>
    4d83:	e8 38 d7 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4d88:	bf 01 00 00 00       	mov    $0x1,%edi
    4d8d:	e8 0e d7 ff ff       	call   24a0 <exit@plt>
}
    4d92:	e8 99 d5 ff ff       	call   2330 <__stack_chk_fail@plt>
    4d97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004da0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4da0:	f3 0f 1e fa          	endbr64
    4da4:	41 55                	push   %r13
    4da6:	49 89 d5             	mov    %rdx,%r13
    4da9:	41 54                	push   %r12
    4dab:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    4dae:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4db1:	55                   	push   %rbp
    4db2:	53                   	push   %rbx
    4db3:	48 89 f3             	mov    %rsi,%rbx
    4db6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4dba:	e8 51 d6 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4dbf:	48 85 c0             	test   %rax,%rax
    4dc2:	74 6b                	je     4e2f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4dc4:	4c 89 e7             	mov    %r12,%rdi
    4dc7:	48 89 c5             	mov    %rax,%rbp
    4dca:	31 f6                	xor    %esi,%esi
    4dcc:	31 c0                	xor    %eax,%eax
    4dce:	e8 ad d6 ff ff       	call   2480 <open@plt>
    4dd3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4dd6:	85 c0                	test   %eax,%eax
    4dd8:	0f 88 78 d7 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4dde:	48 89 da             	mov    %rbx,%rdx
    4de1:	48 89 ee             	mov    %rbp,%rsi
    4de4:	89 c7                	mov    %eax,%edi
    4de6:	e8 a5 d5 ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    4deb:	48 98                	cltq
    4ded:	48 39 d8             	cmp    %rbx,%rax
    4df0:	7c 1e                	jl     4e10 <copy_file_contents+0x70>
    close(fd);
    4df2:	44 89 e7             	mov    %r12d,%edi
    4df5:	e8 76 d5 ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    4dfa:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    4dfe:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4e02:	48 83 c4 08          	add    $0x8,%rsp
    4e06:	5b                   	pop    %rbx
    4e07:	5d                   	pop    %rbp
    4e08:	41 5c                	pop    %r12
    4e0a:	41 5d                	pop    %r13
    4e0c:	c3                   	ret
    4e0d:	0f 1f 00             	nopl   (%rax)
    4e10:	48 8b 0d 09 52 00 00 	mov    0x5209(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4e17:	ba 1a 00 00 00       	mov    $0x1a,%edx
    4e1c:	be 01 00 00 00       	mov    $0x1,%esi
    4e21:	48 8d 3d c9 22 00 00 	lea    0x22c9(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4e28:	e8 93 d6 ff ff       	call   24c0 <fwrite@plt>
    4e2d:	eb c3                	jmp    4df2 <copy_file_contents+0x52>
    4e2f:	48 8b 0d ea 51 00 00 	mov    0x51ea(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4e36:	ba 28 00 00 00       	mov    $0x28,%edx
    4e3b:	be 01 00 00 00       	mov    $0x1,%esi
    4e40:	48 8d 3d 61 26 00 00 	lea    0x2661(%rip),%rdi        # 74a8 <_IO_stdin_used+0x4a8>
    4e47:	e8 74 d6 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4e4c:	bf 01 00 00 00       	mov    $0x1,%edi
    4e51:	e8 4a d6 ff ff       	call   24a0 <exit@plt>
    4e56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004e60 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4e60:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4e64:	8b 46 44             	mov    0x44(%rsi),%eax
    4e67:	48 89 fa             	mov    %rdi,%rdx
    4e6a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    4e6d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4e73:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4e76:	48 8b 07             	mov    (%rdi),%rax
    4e79:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4e7c:	f6 c1 02             	test   $0x2,%cl
    4e7f:	74 00                	je     4e81 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4e81:	89 f0                	mov    %esi,%eax
    4e83:	44 29 c0             	sub    %r8d,%eax
    4e86:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4e89:	0f 82 d3 d6 ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4e8f:	c1 e9 0a             	shr    $0xa,%ecx
    4e92:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e96:	8b 47 44             	mov    0x44(%rdi),%eax
    4e99:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e9c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4e9f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4ea2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4ea5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ea9:	d3 e0                	shl    %cl,%eax
    4eab:	8b 4a 04             	mov    0x4(%rdx),%ecx
    4eae:	48 c1 e0 06          	shl    $0x6,%rax
    4eb2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4eb6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    4ebc:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4ebf:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4ec3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4ec9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4ed1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4ed5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4ed8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4edf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4ee7:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    4eeb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    4eef:	e8 4c d4 ff ff       	call   2340 <io_uring_submit@plt>
}
    4ef4:	31 c0                	xor    %eax,%eax
    4ef6:	48 83 c4 08          	add    $0x8,%rsp
    4efa:	c3                   	ret
    4efb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004f00 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4f00:	f3 0f 1e fa          	endbr64
    4f04:	41 55                	push   %r13
    4f06:	41 89 fd             	mov    %edi,%r13d
    4f09:	41 54                	push   %r12
    4f0b:	55                   	push   %rbp
    4f0c:	53                   	push   %rbx
    4f0d:	48 89 f3             	mov    %rsi,%rbx
    4f10:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4f14:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4f17:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    4f1d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4f20:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4f23:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4f25:	f6 c1 02             	test   $0x2,%cl
    4f28:	74 00                	je     4f2a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    4f2a:	89 c2                	mov    %eax,%edx
    4f2c:	29 f2                	sub    %esi,%edx
    4f2e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4f31:	0f 82 3b d6 ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4f37:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    4f3a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    4f3d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4f40:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4f45:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4f48:	23 6b 58             	and    0x58(%rbx),%ebp
    4f4b:	d3 e5                	shl    %cl,%ebp
    4f4d:	48 c1 e5 06          	shl    $0x6,%rbp
    4f51:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4f55:	e8 b6 d4 ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    4f5a:	be 01 00 00 00       	mov    $0x1,%esi
    4f5f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4f64:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4f67:	e8 34 d4 ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    4f6c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4f71:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4f75:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4f78:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4f7d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4f82:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    4f8b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4f93:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4f97:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    4f9b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4fa2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4faa:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    4fae:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4fb6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    4fbe:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4fc2:	e8 79 d3 ff ff       	call   2340 <io_uring_submit@plt>
}
    4fc7:	48 83 c4 08          	add    $0x8,%rsp
    4fcb:	31 c0                	xor    %eax,%eax
    4fcd:	5b                   	pop    %rbx
    4fce:	5d                   	pop    %rbp
    4fcf:	41 5c                	pop    %r12
    4fd1:	41 5d                	pop    %r13
    4fd3:	c3                   	ret
    4fd4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4fdf:	90                   	nop

0000000000004fe0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4fe0:	f3 0f 1e fa          	endbr64
    4fe4:	41 56                	push   %r14
    4fe6:	41 89 f6             	mov    %esi,%r14d
    4fe9:	41 55                	push   %r13
    4feb:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    4fee:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4ff3:	41 54                	push   %r12
    4ff5:	55                   	push   %rbp
    4ff6:	48 89 d5             	mov    %rdx,%rbp
    4ff9:	53                   	push   %rbx
    void *buf = malloc(size);
    4ffa:	e8 11 d4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4fff:	48 85 c0             	test   %rax,%rax
    5002:	0f 84 dd 00 00 00    	je     50e5 <_send_static_string_content+0x105>
    5008:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    500b:	4c 89 ef             	mov    %r13,%rdi
    500e:	e8 0d d3 ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    5013:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    501a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    501e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    5021:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    5024:	e8 e7 d3 ff ff       	call   2410 <malloc@plt>
    5029:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    502c:	48 85 c0             	test   %rax,%rax
    502f:	0f 84 b0 00 00 00    	je     50e5 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    5035:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5039:	4c 89 e2             	mov    %r12,%rdx
    503c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    503f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    5043:	e8 98 d3 ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5048:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    504b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5051:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5054:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5058:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    505a:	f6 c1 02             	test   $0x2,%cl
    505d:	0f 85 7d 00 00 00    	jne    50e0 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    5063:	89 d0                	mov    %edx,%eax
    5065:	29 f0                	sub    %esi,%eax
    5067:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    506a:	0f 82 0c d5 ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5070:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5073:	8b 45 44             	mov    0x44(%rbp),%eax
    5076:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    5079:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    507c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    507f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    5082:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    5088:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    508c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    508e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    5091:	48 89 ef             	mov    %rbp,%rdi
    5094:	48 c1 e0 06          	shl    $0x6,%rax
    5098:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    509c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    509f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    50a3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    50a9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    50b1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    50b5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    50b8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    50bf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    50c7:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    50cb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    50cf:	5b                   	pop    %rbx
    50d0:	5d                   	pop    %rbp
    50d1:	41 5c                	pop    %r12
    50d3:	41 5d                	pop    %r13
    50d5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    50d7:	e9 64 d2 ff ff       	jmp    2340 <io_uring_submit@plt>
    50dc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    50e0:	e9 7e ff ff ff       	jmp    5063 <_send_static_string_content+0x83>
    50e5:	48 8b 0d 34 4f 00 00 	mov    0x4f34(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    50ec:	ba 28 00 00 00       	mov    $0x28,%edx
    50f1:	be 01 00 00 00       	mov    $0x1,%esi
    50f6:	48 8d 3d ab 23 00 00 	lea    0x23ab(%rip),%rdi        # 74a8 <_IO_stdin_used+0x4a8>
    50fd:	e8 be d3 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5102:	bf 01 00 00 00       	mov    $0x1,%edi
    5107:	e8 94 d3 ff ff       	call   24a0 <exit@plt>
    510c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005110 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    5110:	f3 0f 1e fa          	endbr64
    5114:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5117:	89 fe                	mov    %edi,%esi
    5119:	48 8b 3d f8 4e 00 00 	mov    0x4ef8(%rip),%rdi        # a018 <unimplemented_content>
    5120:	e9 bb fe ff ff       	jmp    4fe0 <_send_static_string_content>
    5125:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005130 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    5130:	f3 0f 1e fa          	endbr64
    5134:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    5137:	89 fe                	mov    %edi,%esi
    5139:	48 8b 3d d0 4e 00 00 	mov    0x4ed0(%rip),%rdi        # a010 <http_404_content>
    5140:	e9 9b fe ff ff       	jmp    4fe0 <_send_static_string_content>
    5145:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005150 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    5150:	f3 0f 1e fa          	endbr64
    5154:	41 56                	push   %r14
    5156:	41 55                	push   %r13
    5158:	49 89 d5             	mov    %rdx,%r13
    515b:	41 54                	push   %r12
    515d:	41 89 f4             	mov    %esi,%r12d
    5160:	55                   	push   %rbp
    5161:	48 89 fd             	mov    %rdi,%rbp
    5164:	53                   	push   %rbx
    5165:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    516c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5175:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    517d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    517f:	e8 9c d1 ff ff       	call   2320 <strlen@plt>
    5184:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    5189:	48 89 c3             	mov    %rax,%rbx
    518c:	0f 84 b6 00 00 00    	je     5248 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5192:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5197:	48 89 ee             	mov    %rbp,%rsi
    519a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    519e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    51a3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    51ab:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    51b3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    51be:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    51c6:	e8 f5 d1 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    51cb:	48 89 e6             	mov    %rsp,%rsi
    51ce:	4c 89 f7             	mov    %r14,%rdi
    51d1:	e8 fa d1 ff ff       	call   23d0 <stat@plt>
    51d6:	83 f8 ff             	cmp    $0xffffffff,%eax
    51d9:	0f 84 d3 00 00 00    	je     52b2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    51df:	8b 44 24 18          	mov    0x18(%rsp),%eax
    51e3:	25 00 f0 00 00       	and    $0xf000,%eax
    51e8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    51ed:	0f 84 f5 00 00 00    	je     52e8 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    51f3:	48 8b 3d 16 4e 00 00 	mov    0x4e16(%rip),%rdi        # a010 <http_404_content>
    51fa:	4c 89 ea             	mov    %r13,%rdx
    51fd:	44 89 e6             	mov    %r12d,%esi
    5200:	e8 db fd ff ff       	call   4fe0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5205:	4c 89 f2             	mov    %r14,%rdx
    5208:	bf 01 00 00 00       	mov    $0x1,%edi
    520d:	31 c0                	xor    %eax,%eax
    520f:	48 8d 35 2b 1f 00 00 	lea    0x1f2b(%rip),%rsi        # 7141 <_IO_stdin_used+0x141>
    5216:	e8 35 d2 ff ff       	call   2450 <__printf_chk@plt>
}
    521b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5223:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    522c:	0f 85 20 01 00 00    	jne    5352 <handle_get_method+0x202>
    5232:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5239:	5b                   	pop    %rbx
    523a:	5d                   	pop    %rbp
    523b:	41 5c                	pop    %r12
    523d:	41 5d                	pop    %r13
    523f:	41 5e                	pop    %r14
    5241:	c3                   	ret
    5242:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5248:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    524d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5255:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    525a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    525d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5265:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5268:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5270:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    527b:	e8 40 d1 ff ff       	call   23c0 <__memcpy_chk@plt>
    5280:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5285:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    528a:	48 8d 35 7b 1e 00 00 	lea    0x1e7b(%rip),%rsi        # 710c <_IO_stdin_used+0x10c>
    5291:	48 29 d9             	sub    %rbx,%rcx
    5294:	ba 0b 00 00 00       	mov    $0xb,%edx
    5299:	e8 22 d1 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    529e:	48 89 e6             	mov    %rsp,%rsi
    52a1:	4c 89 f7             	mov    %r14,%rdi
    52a4:	e8 27 d1 ff ff       	call   23d0 <stat@plt>
    52a9:	83 f8 ff             	cmp    $0xffffffff,%eax
    52ac:	0f 85 2d ff ff ff    	jne    51df <handle_get_method+0x8f>
    52b2:	4c 89 f2             	mov    %r14,%rdx
    52b5:	48 89 e9             	mov    %rbp,%rcx
    52b8:	48 8d 35 58 1e 00 00 	lea    0x1e58(%rip),%rsi        # 7117 <_IO_stdin_used+0x117>
    52bf:	31 c0                	xor    %eax,%eax
    52c1:	bf 01 00 00 00       	mov    $0x1,%edi
    52c6:	e8 85 d1 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    52cb:	48 8b 3d 3e 4d 00 00 	mov    0x4d3e(%rip),%rdi        # a010 <http_404_content>
    52d2:	4c 89 ea             	mov    %r13,%rdx
    52d5:	44 89 e6             	mov    %r12d,%esi
    52d8:	e8 03 fd ff ff       	call   4fe0 <_send_static_string_content>
}
    52dd:	e9 39 ff ff ff       	jmp    521b <handle_get_method+0xcb>
    52e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    52e8:	bf 70 00 00 00       	mov    $0x70,%edi
    52ed:	e8 1e d1 ff ff       	call   2410 <malloc@plt>
    52f2:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    52f5:	48 85 c0             	test   %rax,%rax
    52f8:	74 5d                	je     5357 <handle_get_method+0x207>
            req->client_socket = client_socket;
    52fa:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    52fe:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5303:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5307:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    530a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    5311:	e8 5a f5 ff ff       	call   4870 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5316:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    531b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    531f:	4c 89 f7             	mov    %r14,%rdi
    5322:	e8 79 fa ff ff       	call   4da0 <copy_file_contents>
    5327:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    532c:	4c 89 f2             	mov    %r14,%rdx
    532f:	31 c0                	xor    %eax,%eax
    5331:	48 8d 35 f7 1d 00 00 	lea    0x1df7(%rip),%rsi        # 712f <_IO_stdin_used+0x12f>
    5338:	bf 01 00 00 00       	mov    $0x1,%edi
    533d:	e8 0e d1 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    5342:	4c 89 ee             	mov    %r13,%rsi
    5345:	48 89 df             	mov    %rbx,%rdi
    5348:	e8 13 fb ff ff       	call   4e60 <add_write_request>
    534d:	e9 c9 fe ff ff       	jmp    521b <handle_get_method+0xcb>
}
    5352:	e8 d9 cf ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5357:	48 8b 0d c2 4c 00 00 	mov    0x4cc2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    535e:	ba 28 00 00 00       	mov    $0x28,%edx
    5363:	be 01 00 00 00       	mov    $0x1,%esi
    5368:	48 8d 3d 39 21 00 00 	lea    0x2139(%rip),%rdi        # 74a8 <_IO_stdin_used+0x4a8>
    536f:	e8 4c d1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5374:	bf 01 00 00 00       	mov    $0x1,%edi
    5379:	e8 22 d1 ff ff       	call   24a0 <exit@plt>
    537e:	66 90                	xchg   %ax,%ax

0000000000005380 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5380:	f3 0f 1e fa          	endbr64
    5384:	41 57                	push   %r15
    5386:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5388:	4c 8d 35 17 1d 00 00 	lea    0x1d17(%rip),%r14        # 70a6 <_IO_stdin_used+0xa6>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    538f:	41 55                	push   %r13
    5391:	49 89 d5             	mov    %rdx,%r13
    5394:	41 54                	push   %r12
    5396:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    5399:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    539c:	55                   	push   %rbp
    539d:	53                   	push   %rbx
    539e:	48 83 ec 18          	sub    $0x18,%rsp
    53a2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    53ab:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    53b0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    53b2:	49 89 e7             	mov    %rsp,%r15
    53b5:	4c 89 fa             	mov    %r15,%rdx
    53b8:	e8 c3 cf ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    53bd:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    53c1:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    53c4:	84 db                	test   %bl,%bl
    53c6:	74 1d                	je     53e5 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    53c8:	e8 43 d1 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    53cd:	48 89 ea             	mov    %rbp,%rdx
    53d0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    53d3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    53d7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    53da:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    53dd:	48 0f be 1a          	movsbq (%rdx),%rbx
    53e1:	84 db                	test   %bl,%bl
    53e3:	75 eb                	jne    53d0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    53e5:	4c 89 fa             	mov    %r15,%rdx
    53e8:	4c 89 f6             	mov    %r14,%rsi
    53eb:	31 ff                	xor    %edi,%edi
    53ed:	e8 8e cf ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    53f2:	48 8d 35 5b 1d 00 00 	lea    0x1d5b(%rip),%rsi        # 7154 <_IO_stdin_used+0x154>
    53f9:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    53fc:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    53ff:	e8 ac cf ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    5404:	4c 89 ea             	mov    %r13,%rdx
    5407:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    540a:	85 c0                	test   %eax,%eax
    540c:	75 2a                	jne    5438 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    540e:	48 89 df             	mov    %rbx,%rdi
    5411:	e8 3a fd ff ff       	call   5150 <handle_get_method>
}
    5416:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    541b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5424:	75 20                	jne    5446 <handle_http_method+0xc6>
    5426:	48 83 c4 18          	add    $0x18,%rsp
    542a:	5b                   	pop    %rbx
    542b:	5d                   	pop    %rbp
    542c:	41 5c                	pop    %r12
    542e:	41 5d                	pop    %r13
    5430:	41 5e                	pop    %r14
    5432:	41 5f                	pop    %r15
    5434:	c3                   	ret
    5435:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5438:	48 8b 3d d9 4b 00 00 	mov    0x4bd9(%rip),%rdi        # a018 <unimplemented_content>
    543f:	e8 9c fb ff ff       	call   4fe0 <_send_static_string_content>
}
    5444:	eb d0                	jmp    5416 <handle_http_method+0x96>
    5446:	e8 e5 ce ff ff       	call   2330 <__stack_chk_fail@plt>
    544b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005450 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5450:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5454:	85 d2                	test   %edx,%edx
    5456:	7e 38                	jle    5490 <get_line+0x40>
    5458:	48 63 d2             	movslq %edx,%rdx
    545b:	48 83 c7 01          	add    $0x1,%rdi
    545f:	48 01 f2             	add    %rsi,%rdx
    5462:	eb 11                	jmp    5475 <get_line+0x25>
    5464:	0f 1f 40 00          	nopl   0x0(%rax)
    5468:	48 83 c6 01          	add    $0x1,%rsi
    546c:	48 83 c7 01          	add    $0x1,%rdi
    5470:	48 39 d6             	cmp    %rdx,%rsi
    5473:	74 1b                	je     5490 <get_line+0x40>
        dest[i] = src[i];
    5475:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5479:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    547b:	3c 0d                	cmp    $0xd,%al
    547d:	75 e9                	jne    5468 <get_line+0x18>
    547f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5482:	75 e4                	jne    5468 <get_line+0x18>
            dest[i] = '\0';
    5484:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5487:	31 c0                	xor    %eax,%eax
    5489:	c3                   	ret
    548a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5490:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5495:	c3                   	ret
    5496:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000054a0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    54a0:	f3 0f 1e fa          	endbr64
    54a4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    54ab:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    54af:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    54b8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    54c0:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    54c2:	49 89 e2             	mov    %rsp,%r10
    54c5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    54cd:	4c 89 d0             	mov    %r10,%rax
    54d0:	eb 13                	jmp    54e5 <handle_client_request+0x45>
    54d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    54d8:	48 83 c0 01          	add    $0x1,%rax
    54dc:	48 83 c1 01          	add    $0x1,%rcx
    54e0:	4c 39 c8             	cmp    %r9,%rax
    54e3:	74 4b                	je     5530 <handle_client_request+0x90>
        dest[i] = src[i];
    54e5:	44 0f b6 01          	movzbl (%rcx),%r8d
    54e9:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    54ec:	41 80 f8 0d          	cmp    $0xd,%r8b
    54f0:	75 e6                	jne    54d8 <handle_client_request+0x38>
    54f2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    54f6:	75 e0                	jne    54d8 <handle_client_request+0x38>
            dest[i] = '\0';
    54f8:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    54fb:	8b 47 08             	mov    0x8(%rdi),%eax
    54fe:	48 89 f2             	mov    %rsi,%rdx
    5501:	4c 89 d7             	mov    %r10,%rdi
    5504:	89 c6                	mov    %eax,%esi
    5506:	e8 75 fe ff ff       	call   5380 <handle_http_method>
}
    550b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5513:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    551c:	75 39                	jne    5557 <handle_client_request+0xb7>
    551e:	31 c0                	xor    %eax,%eax
    5520:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5527:	c3                   	ret
    5528:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5530:	48 8b 0d e9 4a 00 00 	mov    0x4ae9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5537:	ba 12 00 00 00       	mov    $0x12,%edx
    553c:	be 01 00 00 00       	mov    $0x1,%esi
    5541:	48 8d 3d 10 1c 00 00 	lea    0x1c10(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    5548:	e8 73 cf ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    554d:	bf 01 00 00 00       	mov    $0x1,%edi
    5552:	e8 49 cf ff ff       	call   24a0 <exit@plt>
}
    5557:	e8 d4 cd ff ff       	call   2330 <__stack_chk_fail@plt>
    555c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005560 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5560:	f3 0f 1e fa          	endbr64
    5564:	55                   	push   %rbp
    5565:	53                   	push   %rbx
    5566:	48 89 cb             	mov    %rcx,%rbx
    5569:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    556d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5570:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5573:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5579:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    557c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    557f:	f6 c1 02             	test   $0x2,%cl
    5582:	74 00                	je     5584 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    5584:	41 89 c0             	mov    %eax,%r8d
    5587:	45 29 c8             	sub    %r9d,%r8d
    558a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    558e:	0f 82 f8 cf ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5594:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5597:	8b 6b 44             	mov    0x44(%rbx),%ebp
    559a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    559d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    55a0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    55a3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    55a7:	d3 e5                	shl    %cl,%ebp
    55a9:	48 c1 e5 06          	shl    $0x6,%rbp
    55ad:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    55b1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    55b4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    55b9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    55c0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    55c4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    55c8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    55d0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    55d8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    55dc:	e8 2f ce ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    55e1:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    55e4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    55ea:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    55ee:	48 83 c4 08          	add    $0x8,%rsp
    55f2:	5b                   	pop    %rbx
    55f3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    55f4:	e9 47 cd ff ff       	jmp    2340 <io_uring_submit@plt>
    55f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005600 <io_thread>:
void* io_thread(void *arg) {
    5600:	f3 0f 1e fa          	endbr64
    5604:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5606:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5608:	41 56                	push   %r14
    560a:	41 55                	push   %r13
    560c:	41 54                	push   %r12
    560e:	55                   	push   %rbp
    560f:	48 89 fd             	mov    %rdi,%rbp
    5612:	53                   	push   %rbx
    5613:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    561a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5623:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    562b:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    562f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5634:	bf 00 01 00 00       	mov    $0x100,%edi
    5639:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    563c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5640:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5645:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    564a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    564f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5654:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    565c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5661:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5669:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    566e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5676:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    567b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5683:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5688:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5690:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5695:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    569d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    56a5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    56ad:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    56b5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    56bd:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    56c5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    56cd:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    56d5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    56dd:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    56e5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    56ed:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    56f4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    56fc:	e8 ef cc ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5701:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5705:	31 f6                	xor    %esi,%esi
    5707:	e8 d4 cd ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    570c:	31 d2                	xor    %edx,%edx
    570e:	be 01 00 00 00       	mov    $0x1,%esi
    5713:	bf 02 00 00 00       	mov    $0x2,%edi
    5718:	e8 13 ce ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    571d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5720:	0f 84 a8 ce ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    5726:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    572b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5731:	89 c7                	mov    %eax,%edi
    5733:	41 89 c4             	mov    %eax,%r12d
    5736:	ba 02 00 00 00       	mov    $0x2,%edx
    573b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5740:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5748:	e8 b3 cb ff ff       	call   2300 <setsockopt@plt>
    574d:	85 c0                	test   %eax,%eax
    574f:	0f 88 4d ce ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5755:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    575a:	ba 10 00 00 00       	mov    $0x10,%edx
    575f:	44 89 e7             	mov    %r12d,%edi
    5762:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    576b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5773:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    577b:	e8 e0 cc ff ff       	call   2460 <bind@plt>
    5780:	85 c0                	test   %eax,%eax
    5782:	0f 88 52 ce ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5788:	be 0a 00 00 00       	mov    $0xa,%esi
    578d:	44 89 e7             	mov    %r12d,%edi
    5790:	e8 8b cc ff ff       	call   2420 <listen@plt>
    5795:	85 c0                	test   %eax,%eax
    5797:	0f 88 11 ce ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    579d:	ba db 18 00 00       	mov    $0x18db,%edx
    57a2:	48 8d 35 f4 19 00 00 	lea    0x19f4(%rip),%rsi        # 719d <_IO_stdin_used+0x19d>
    57a9:	bf 01 00 00 00       	mov    $0x1,%edi
    57ae:	31 c0                	xor    %eax,%eax
    57b0:	e8 9b cc ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    57b5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    57ba:	48 89 d9             	mov    %rbx,%rcx
    57bd:	44 89 e7             	mov    %r12d,%edi
    57c0:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    57c5:	48 89 c6             	mov    %rax,%rsi
    57c8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    57cd:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    57d2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    57da:	e8 81 fd ff ff       	call   5560 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    57df:	bf 01 00 00 00       	mov    $0x1,%edi
    57e4:	be 10 00 00 00       	mov    $0x10,%esi
    57e9:	e8 b2 cb ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    57ee:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    57f3:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    57f6:	e8 15 cc ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    57fb:	48 85 c0             	test   %rax,%rax
    57fe:	0f 84 ae 04 00 00    	je     5cb2 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5804:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5808:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    580f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5816:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    581e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5821:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5826:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5828:	f6 c1 02             	test   $0x2,%cl
    582b:	0f 85 0f 04 00 00    	jne    5c40 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5831:	89 d0                	mov    %edx,%eax
    5833:	29 f0                	sub    %esi,%eax
    5835:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    583c:	0f 82 82 cd ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5842:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5845:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5849:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    584d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5850:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5857:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    585a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5861:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5868:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    586a:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    586d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5872:	48 c1 e0 06          	shl    $0x6,%rax
    5876:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    587e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5884:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5887:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    588f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5893:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    589b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    58a3:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    58a7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    58ab:	e8 90 ca ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    58b0:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    58b4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    58b9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    58c1:	0f 85 d7 01 00 00    	jne    5a9e <io_thread+0x49e>
    58c7:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    58cc:	4d 89 ce             	mov    %r9,%r14
    58cf:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    58d4:	0f 1f 40 00          	nopl   0x0(%rax)
    58d8:	48 8d 3d d4 18 00 00 	lea    0x18d4(%rip),%rdi        # 71b3 <_IO_stdin_used+0x1b3>
    58df:	e8 0c ca ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    58e4:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    58eb:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    58f2:	c1 e9 0b             	shr    $0xb,%ecx
    58f5:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    58f8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5900:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5902:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    590a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    590c:	39 d0                	cmp    %edx,%eax
    590e:	74 36                	je     5946 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5910:	89 f8                	mov    %edi,%eax
    5912:	21 d0                	and    %edx,%eax
    5914:	d3 e0                	shl    %cl,%eax
    5916:	48 c1 e0 04          	shl    $0x4,%rax
    591a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5922:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    592a:	0f 85 a8 01 00 00    	jne    5ad8 <io_thread+0x4d8>
    5930:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5934:	0f 85 0e 03 00 00    	jne    5c48 <io_thread+0x648>
			if (cqe->res < 0)
    593a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    593d:	83 c2 01             	add    $0x1,%edx
    5940:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5942:	85 c0                	test   %eax,%eax
    5944:	79 b2                	jns    58f8 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5946:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    594f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5950:	45 31 c0             	xor    %r8d,%r8d
    5953:	31 d2                	xor    %edx,%edx
    5955:	b9 01 00 00 00       	mov    $0x1,%ecx
    595a:	4c 89 f6             	mov    %r14,%rsi
    595d:	48 89 df             	mov    %rbx,%rdi
    5960:	e8 db ca ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5965:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5968:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    596d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5971:	0f 84 e1 02 00 00    	je     5c58 <io_thread+0x658>
    5977:	48 8d 3d 5b 18 00 00 	lea    0x185b(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    597e:	e8 6d c9 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5983:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5988:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    598b:	45 85 ff             	test   %r15d,%r15d
    598e:	0f 88 02 cc ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    5994:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5997:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    599b:	85 c0                	test   %eax,%eax
    599d:	0f 88 d5 02 00 00    	js     5c78 <io_thread+0x678>
      switch (req->event_type) {
    59a3:	41 83 f8 01          	cmp    $0x1,%r8d
    59a7:	0f 84 7b 01 00 00    	je     5b28 <io_thread+0x528>
    59ad:	41 83 f8 02          	cmp    $0x2,%r8d
    59b1:	0f 84 a1 01 00 00    	je     5b58 <io_thread+0x558>
    59b7:	45 85 c0             	test   %r8d,%r8d
    59ba:	0f 85 50 01 00 00    	jne    5b10 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    59c0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    59c5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    59ca:	48 89 d9             	mov    %rbx,%rcx
    59cd:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    59d1:	e8 8a fb ff ff       	call   5560 <add_accept_request>
              add_read_request(cqe->res, &ring);
    59d6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    59db:	48 89 de             	mov    %rbx,%rsi
    59de:	8b 78 08             	mov    0x8(%rax),%edi
    59e1:	e8 1a f5 ff ff       	call   4f00 <add_read_request>
              free(req);
    59e6:	4c 89 e7             	mov    %r12,%rdi
    59e9:	e8 d2 c8 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    59ee:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    59f3:	48 85 c0             	test   %rax,%rax
    59f6:	0f 85 14 01 00 00    	jne    5b10 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    59fc:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5a03:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5a0a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5a0d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5a12:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5a14:	f6 c1 02             	test   $0x2,%cl
    5a17:	74 00                	je     5a19 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5a19:	89 d0                	mov    %edx,%eax
    5a1b:	29 f0                	sub    %esi,%eax
    5a1d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5a24:	0f 82 90 cb ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5a2a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    5a2d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5a32:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5a36:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a39:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5a40:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a43:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5a4a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a51:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5a53:	8b 55 60             	mov    0x60(%rbp),%edx
    5a56:	48 c1 e0 06          	shl    $0x6,%rax
    5a5a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5a62:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5a68:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5a6b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5a73:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5a77:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5a7f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5a87:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5a8b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5a8f:	e8 ac c8 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5a94:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5a98:	0f 84 3a fe ff ff    	je     58d8 <io_thread+0x2d8>
    5a9e:	48 8d 3d 6d 17 00 00 	lea    0x176d(%rip),%rdi        # 7212 <_IO_stdin_used+0x212>
    5aa5:	e8 46 c8 ff ff       	call   22f0 <puts@plt>
}
    5aaa:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5ab2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5abb:	0f 85 18 02 00 00    	jne    5cd9 <io_thread+0x6d9>
    5ac1:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5ac8:	31 c0                	xor    %eax,%eax
    5aca:	5b                   	pop    %rbx
    5acb:	5d                   	pop    %rbp
    5acc:	41 5c                	pop    %r12
    5ace:	41 5d                	pop    %r13
    5ad0:	41 5e                	pop    %r14
    5ad2:	41 5f                	pop    %r15
    5ad4:	c3                   	ret
    5ad5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5ad8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5add:	48 85 c0             	test   %rax,%rax
    5ae0:	0f 84 6a fe ff ff    	je     5950 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5ae6:	48 83 38 01          	cmpq   $0x1,(%rax)
    5aea:	0f 84 68 01 00 00    	je     5c58 <io_thread+0x658>
    5af0:	48 8d 3d e2 16 00 00 	lea    0x16e2(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    5af7:	e8 f4 c7 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5afc:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5b01:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5b04:	e9 8b fe ff ff       	jmp    5994 <io_thread+0x394>
    5b09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5b10:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5b18:	8b 02                	mov    (%rdx),%eax
    5b1a:	83 c0 01             	add    $0x1,%eax
    5b1d:	89 02                	mov    %eax,(%rdx)
}
    5b1f:	e9 d8 fe ff ff       	jmp    59fc <io_thread+0x3fc>
    5b24:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5b28:	85 c0                	test   %eax,%eax
    5b2a:	75 74                	jne    5ba0 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5b2c:	48 8b 0d ed 44 00 00 	mov    0x44ed(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5b33:	ba 0f 00 00 00       	mov    $0xf,%edx
    5b38:	be 01 00 00 00       	mov    $0x1,%esi
    5b3d:	48 8d 3d be 16 00 00 	lea    0x16be(%rip),%rdi        # 7202 <_IO_stdin_used+0x202>
    5b44:	e8 77 c9 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5b49:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5b4e:	e9 a0 fe ff ff       	jmp    59f3 <io_thread+0x3f3>
    5b53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5b58:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5b5d:	45 31 ff             	xor    %r15d,%r15d
    5b60:	85 c0                	test   %eax,%eax
    5b62:	7e 20                	jle    5b84 <io_thread+0x584>
    5b64:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5b68:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5b6b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    5b6f:	48 c1 e0 04          	shl    $0x4,%rax
    5b73:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5b78:	e8 43 c7 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5b7d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5b82:	7f e4                	jg     5b68 <io_thread+0x568>
              close(req->client_socket);
    5b84:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5b89:	e8 e2 c7 ff ff       	call   2370 <close@plt>
              free(req);
    5b8e:	4c 89 e7             	mov    %r12,%rdi
    5b91:	e8 2a c7 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5b96:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5b9b:	e9 53 fe ff ff       	jmp    59f3 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5ba0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5ba5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5baa:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5bb2:	eb 11                	jmp    5bc5 <io_thread+0x5c5>
    5bb4:	0f 1f 40 00          	nopl   0x0(%rax)
    5bb8:	48 83 c0 01          	add    $0x1,%rax
    5bbc:	48 83 c2 01          	add    $0x1,%rdx
    5bc0:	48 39 c6             	cmp    %rax,%rsi
    5bc3:	74 4b                	je     5c10 <io_thread+0x610>
        dest[i] = src[i];
    5bc5:	0f b6 0a             	movzbl (%rdx),%ecx
    5bc8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5bca:	80 f9 0d             	cmp    $0xd,%cl
    5bcd:	75 e9                	jne    5bb8 <io_thread+0x5b8>
    5bcf:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5bd3:	75 e3                	jne    5bb8 <io_thread+0x5b8>
            dest[i] = '\0';
    5bd5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5bd8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    5bdd:	48 89 da             	mov    %rbx,%rdx
    5be0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5be5:	e8 96 f7 ff ff       	call   5380 <handle_http_method>
              free(req->iov[0].iov_base);
    5bea:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    5bef:	e8 cc c6 ff ff       	call   22c0 <free@plt>
              free(req);
    5bf4:	4c 89 e7             	mov    %r12,%rdi
    5bf7:	e8 c4 c6 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5bfc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5c01:	e9 ed fd ff ff       	jmp    59f3 <io_thread+0x3f3>
    5c06:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5c10:	48 8b 0d 09 44 00 00 	mov    0x4409(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5c17:	ba 12 00 00 00       	mov    $0x12,%edx
    5c1c:	be 01 00 00 00       	mov    $0x1,%esi
    5c21:	48 8d 3d 30 15 00 00 	lea    0x1530(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    5c28:	e8 93 c8 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5c2d:	bf 01 00 00 00       	mov    $0x1,%edi
    5c32:	e8 69 c8 ff ff       	call   24a0 <exit@plt>
    5c37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5c40:	e9 ec fb ff ff       	jmp    5831 <io_thread+0x231>
    5c45:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5c48:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    5c4d:	e9 94 fe ff ff       	jmp    5ae6 <io_thread+0x4e6>
    5c52:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5c58:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5c60:	48 8d 3d 5e 15 00 00 	lea    0x155e(%rip),%rdi        # 71c5 <_IO_stdin_used+0x1c5>
    5c67:	8b 02                	mov    (%rdx),%eax
    5c69:	83 c0 01             	add    $0x1,%eax
    5c6c:	89 02                	mov    %eax,(%rdx)
    5c6e:	e8 7d c6 ff ff       	call   22f0 <puts@plt>
    5c73:	e9 26 fe ff ff       	jmp    5a9e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5c78:	f7 d8                	neg    %eax
    5c7a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5c7f:	89 c7                	mov    %eax,%edi
    5c81:	e8 7a c8 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5c86:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5c8b:	be 01 00 00 00       	mov    $0x1,%esi
    5c90:	48 8b 3d 89 43 00 00 	mov    0x4389(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5c97:	48 89 c1             	mov    %rax,%rcx
    5c9a:	48 8d 15 37 18 00 00 	lea    0x1837(%rip),%rdx        # 74d8 <_IO_stdin_used+0x4d8>
    5ca1:	31 c0                	xor    %eax,%eax
    5ca3:	e8 28 c8 ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5ca8:	bf 01 00 00 00       	mov    $0x1,%edi
    5cad:	e8 ee c7 ff ff       	call   24a0 <exit@plt>
    5cb2:	48 8b 0d 67 43 00 00 	mov    0x4367(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5cb9:	ba 28 00 00 00       	mov    $0x28,%edx
    5cbe:	be 01 00 00 00       	mov    $0x1,%esi
    5cc3:	48 8d 3d de 17 00 00 	lea    0x17de(%rip),%rdi        # 74a8 <_IO_stdin_used+0x4a8>
    5cca:	e8 f1 c7 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5ccf:	bf 01 00 00 00       	mov    $0x1,%edi
    5cd4:	e8 c7 c7 ff ff       	call   24a0 <exit@plt>
}
    5cd9:	e8 52 c6 ff ff       	call   2330 <__stack_chk_fail@plt>
    5cde:	66 90                	xchg   %ax,%ax

0000000000005ce0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5ce0:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5ce4:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5ceb:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5cf1:	85 c9                	test   %ecx,%ecx
    5cf3:	0f 8e ea 00 00 00    	jle    5de3 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    5cf9:	41 56                	push   %r14
    5cfb:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5cfd:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    5d00:	41 54                	push   %r12
    5d02:	49 89 fc             	mov    %rdi,%r12
    5d05:	55                   	push   %rbp
    5d06:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5d07:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5d0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5d10:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    5d14:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    5d1c:	31 db                	xor    %ebx,%ebx
    5d1e:	8b 10                	mov    (%rax),%edx
    5d20:	85 d2                	test   %edx,%edx
    5d22:	7e 26                	jle    5d4a <barriered_work_ingest+0x6a>
    5d24:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    5d28:	48 89 dd             	mov    %rbx,%rbp
    5d2b:	48 c1 e5 08          	shl    $0x8,%rbp
    5d2f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    5d33:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    5d3a:	74 24                	je     5d60 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5d3c:	48 83 c3 01          	add    $0x1,%rbx
    5d40:	39 da                	cmp    %ebx,%edx
    5d42:	7f e4                	jg     5d28 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5d44:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5d4a:	49 83 c5 01          	add    $0x1,%r13
    5d4e:	44 39 e9             	cmp    %r13d,%ecx
    5d51:	7f bd                	jg     5d10 <barriered_work_ingest+0x30>
}
    5d53:	5b                   	pop    %rbx
    5d54:	31 c0                	xor    %eax,%eax
    5d56:	5d                   	pop    %rbp
    5d57:	41 5c                	pop    %r12
    5d59:	41 5d                	pop    %r13
    5d5b:	41 5e                	pop    %r14
    5d5d:	c3                   	ret
    5d5e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    5d60:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5d69:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5d70:	bf 04 00 00 00       	mov    $0x4,%edi
    5d75:	48 c1 e6 05          	shl    $0x5,%rsi
    5d79:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5d80:	48 83 c6 10          	add    $0x10,%rsi
    5d84:	e8 87 c5 ff ff       	call   2310 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5d89:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5d91:	48 8b 40 50          	mov    0x50(%rax),%rax
    5d95:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5d99:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    5d9d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5da7:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    5dad:	83 c0 01             	add    $0x1,%eax
    5db0:	99                   	cltd
    5db1:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5db7:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    5dbd:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5dc0:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5dc8:	48 83 c3 01          	add    $0x1,%rbx
    5dcc:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5dd0:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5dd4:	8b 10                	mov    (%rax),%edx
    5dd6:	39 da                	cmp    %ebx,%edx
    5dd8:	0f 8f 46 ff ff ff    	jg     5d24 <barriered_work_ingest+0x44>
    5dde:	e9 61 ff ff ff       	jmp    5d44 <barriered_work_ingest+0x64>
}
    5de3:	31 c0                	xor    %eax,%eax
    5de5:	c3                   	ret
    5de6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005df0 <barriered_thread>:
void* barriered_thread(void *arg) {
    5df0:	f3 0f 1e fa          	endbr64
    5df4:	41 56                	push   %r14
    5df6:	41 55                	push   %r13
    5df8:	41 54                	push   %r12
  int t = 0;
    5dfa:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    5dfd:	55                   	push   %rbp
  int waiting = 0;
    5dfe:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    5e00:	53                   	push   %rbx
    5e01:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    5e04:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5e08:	0f 85 74 02 00 00    	jne    6082 <barriered_thread+0x292>
    if (t >= data->task_count) {
    5e0e:	8b 43 40             	mov    0x40(%rbx),%eax
    5e11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5e18:	41 39 c4             	cmp    %eax,%r12d
    5e1b:	0f 8d 6f 01 00 00    	jge    5f90 <barriered_thread+0x1a0>
    5e21:	49 63 fc             	movslq %r12d,%rdi
    5e24:	48 c1 e7 09          	shl    $0x9,%rdi
    5e28:	49 89 fd             	mov    %rdi,%r13
    5e2b:	eb 32                	jmp    5e5f <barriered_thread+0x6f>
    5e2d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5e30:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5e34:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5e38:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5e3c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5e40:	4c 01 ef             	add    %r13,%rdi
    5e43:	e8 98 fe ff ff       	call   5ce0 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    5e48:	8b 43 40             	mov    0x40(%rbx),%eax
    5e4b:	41 83 c4 01          	add    $0x1,%r12d
    5e4f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    5e56:	44 39 e0             	cmp    %r12d,%eax
    5e59:	0f 8e 19 02 00 00    	jle    6078 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    5e5f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5e63:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    5e67:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    5e6e:	75 c0                	jne    5e30 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5e70:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    5e74:	83 e8 01             	sub    $0x1,%eax
    5e77:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    5e7c:	45 85 e4             	test   %r12d,%r12d
    5e7f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5e82:	45 85 c0             	test   %r8d,%r8d
    5e85:	0f 8e 2d 01 00 00    	jle    5fb8 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5e8b:	48 63 c8             	movslq %eax,%rcx
    5e8e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5e92:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5e95:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5e9b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    5ea2:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    5ea6:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    5ea9:	45 31 f6             	xor    %r14d,%r14d
    5eac:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5eb0:	48 8b 10             	mov    (%rax),%rdx
    5eb3:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    5eb7:	49 01 cb             	add    %rcx,%r11
    5eba:	4c 89 da             	mov    %r11,%rdx
    5ebd:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    5ec4:	75 04                	jne    5eca <barriered_thread+0xda>
            arrived++;
    5ec6:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5eca:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    5ed0:	75 04                	jne    5ed6 <barriered_thread+0xe6>
            prearrive++;
    5ed2:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5ed6:	48 83 c0 08          	add    $0x8,%rax
    5eda:	48 39 c6             	cmp    %rax,%rsi
    5edd:	75 d1                	jne    5eb0 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    5edf:	45 85 d2             	test   %r10d,%r10d
    5ee2:	0f 84 c0 00 00 00    	je     5fa8 <barriered_thread+0x1b8>
    5ee8:	45 39 d0             	cmp    %r10d,%r8d
    5eeb:	0f 84 b7 00 00 00    	je     5fa8 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    5ef1:	45 85 f6             	test   %r14d,%r14d
    5ef4:	74 0a                	je     5f00 <barriered_thread+0x110>
    5ef6:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    5efa:	0f 85 ae 01 00 00    	jne    60ae <barriered_thread+0x2be>
    5f00:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    5f04:	4c 01 ea             	add    %r13,%rdx
    5f07:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    5f0e:	45 85 e4             	test   %r12d,%r12d
    5f11:	75 14                	jne    5f27 <barriered_thread+0x137>
    5f13:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5f1a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5f21:	0f 8c 69 01 00 00    	jl     6090 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5f27:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    5f2b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    5f2f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5f39:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    5f3d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5f41:	4c 01 ef             	add    %r13,%rdi
    5f44:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    5f4a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    5f4e:	4c 01 e8             	add    %r13,%rax
    5f51:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5f58:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    5f5b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5f60:	83 e8 01             	sub    $0x1,%eax
    5f63:	44 39 e0             	cmp    %r12d,%eax
    5f66:	0f 84 a4 00 00 00    	je     6010 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    5f6c:	0f ae f8             	sfence
          if (waiting == 0) {
    5f6f:	85 ed                	test   %ebp,%ebp
    5f71:	0f 84 d1 00 00 00    	je     6048 <barriered_thread+0x258>
        int arrived = 0; 
    5f77:	bd 01 00 00 00       	mov    $0x1,%ebp
    5f7c:	e9 c7 fe ff ff       	jmp    5e48 <barriered_thread+0x58>
  while (data->running == 1) {
    5f81:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5f85:	0f 85 f7 00 00 00    	jne    6082 <barriered_thread+0x292>
    5f8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    5f90:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    5f98:	85 c0                	test   %eax,%eax
    5f9a:	7e e5                	jle    5f81 <barriered_thread+0x191>
    5f9c:	45 31 e4             	xor    %r12d,%r12d
    5f9f:	e9 7d fe ff ff       	jmp    5e21 <barriered_thread+0x31>
    5fa4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5fa8:	83 fd 01             	cmp    $0x1,%ebp
    5fab:	74 1b                	je     5fc8 <barriered_thread+0x1d8>
        int arrived = 0; 
    5fad:	31 ed                	xor    %ebp,%ebp
    5faf:	e9 3d ff ff ff       	jmp    5ef1 <barriered_thread+0x101>
    5fb4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5fb8:	83 fd 01             	cmp    $0x1,%ebp
    5fbb:	0f 85 43 ff ff ff    	jne    5f04 <barriered_thread+0x114>
        int arrived = 0; 
    5fc1:	45 31 f6             	xor    %r14d,%r14d
    5fc4:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5fc8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5fcf:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    5fd4:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5fd6:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5fda:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5fe1:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    5fe6:	e8 25 c3 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    5feb:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5ff2:	48 83 c0 01          	add    $0x1,%rax
    5ff6:	48 99                	cqto
    5ff8:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    5fff:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    6006:	e9 e6 fe ff ff       	jmp    5ef1 <barriered_thread+0x101>
    600b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6010:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6017:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    601e:	0f 8d 48 ff ff ff    	jge    5f6c <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    6024:	48 c1 e6 04          	shl    $0x4,%rsi
    6028:	bf 04 00 00 00       	mov    $0x4,%edi
    602d:	48 03 73 70          	add    0x70(%rbx),%rsi
    6031:	e8 da c2 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    6036:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    603e:	e9 29 ff ff ff       	jmp    5f6c <barriered_thread+0x17c>
    6043:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    6048:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    604f:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    6054:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6058:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    605f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    6063:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    6067:	e8 a4 c2 ff ff       	call   2310 <clock_gettime@plt>
            waiting = 1;
    606c:	e9 06 ff ff ff       	jmp    5f77 <barriered_thread+0x187>
    6071:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    6078:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    607c:	0f 84 96 fd ff ff    	je     5e18 <barriered_thread+0x28>
}
    6082:	5b                   	pop    %rbx
    6083:	31 c0                	xor    %eax,%eax
    6085:	5d                   	pop    %rbp
    6086:	41 5c                	pop    %r12
    6088:	41 5d                	pop    %r13
    608a:	41 5e                	pop    %r14
    608c:	c3                   	ret
    608d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    6090:	48 c1 e6 04          	shl    $0x4,%rsi
    6094:	bf 04 00 00 00       	mov    $0x4,%edi
    6099:	48 03 73 68          	add    0x68(%rbx),%rsi
    609d:	e8 6e c2 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    60a2:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    60a6:	4c 01 ea             	add    %r13,%rdx
    60a9:	e9 79 fe ff ff       	jmp    5f27 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    60ae:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    60b2:	48 8b 43 18          	mov    0x18(%rbx),%rax
    60b6:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    60ba:	48 8b 78 38          	mov    0x38(%rax),%rdi
    60be:	4c 01 ef             	add    %r13,%rdi
    60c1:	e8 1a fc ff ff       	call   5ce0 <barriered_work_ingest>
          break;
    60c6:	e9 39 fd ff ff       	jmp    5e04 <barriered_thread+0x14>
    60cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000060d0 <receive>:
int receive(struct BarrierTask *data) {
    60d0:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    60d4:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    60da:	85 c0                	test   %eax,%eax
    60dc:	0f 8e 5c 01 00 00    	jle    623e <receive+0x16e>
int receive(struct BarrierTask *data) {
    60e2:	41 57                	push   %r15
    60e4:	48 89 fa             	mov    %rdi,%rdx
    60e7:	41 56                	push   %r14
    60e9:	41 55                	push   %r13
    60eb:	45 31 ed             	xor    %r13d,%r13d
    60ee:	41 54                	push   %r12
    60f0:	45 31 e4             	xor    %r12d,%r12d
    60f3:	55                   	push   %rbp
    60f4:	53                   	push   %rbx
    60f5:	48 83 ec 08          	sub    $0x8,%rsp
    60f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    struct Data *me = data->mailboxes[n].lower;
    6100:	48 8b b2 70 01 00 00 	mov    0x170(%rdx),%rsi
    6107:	4c 01 ee             	add    %r13,%rsi
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    610a:	44 8b 76 20          	mov    0x20(%rsi),%r14d
    struct Data *me = data->mailboxes[n].lower;
    610e:	48 8b 2e             	mov    (%rsi),%rbp
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    6111:	41 83 fe 02          	cmp    $0x2,%r14d
    6115:	0f 84 fd 00 00 00    	je     6218 <receive+0x148>
    for (int x = 0 ; x < me->messages_count ; x++) {
    611b:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    6122:	48 85 ff             	test   %rdi,%rdi
    6125:	0f 8e 9b 00 00 00    	jle    61c6 <receive+0xf6>
      data->sends++;
    612b:	4c 8b 8a 78 01 00 00 	mov    0x178(%rdx),%r9
      data->n++;
    6132:	4c 8b 82 08 01 00 00 	mov    0x108(%rdx),%r8
      data->mailboxes[n].received++;
    6139:	31 c0                	xor    %eax,%eax
    613b:	48 8b 4e 18          	mov    0x18(%rsi),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    613f:	48 8b 5d 00          	mov    0x0(%rbp),%rbx
    6143:	4d 8d 51 01          	lea    0x1(%r9),%r10
    6147:	4c 63 5a 04          	movslq 0x4(%rdx),%r11
    614b:	4d 8d 48 01          	lea    0x1(%r8),%r9
    614f:	4c 8d 41 01          	lea    0x1(%rcx),%r8
    6153:	eb 0c                	jmp    6161 <receive+0x91>
    6155:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    6158:	48 83 c0 01          	add    $0x1,%rax
    615c:	48 39 f8             	cmp    %rdi,%rax
    615f:	7d 5f                	jge    61c0 <receive+0xf0>
      data->sends++;
    6161:	49 8d 0c 02          	lea    (%r10,%rax,1),%rcx
    6165:	48 89 8a 78 01 00 00 	mov    %rcx,0x178(%rdx)
      data->n++;
    616c:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    6170:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    6177:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    617b:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    617f:	48 8b 0c c3          	mov    (%rbx,%rax,8),%rcx
    6183:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    6187:	75 cf                	jne    6158 <receive+0x88>
    6189:	4c 63 ba 30 01 00 00 	movslq 0x130(%rdx),%r15
    6190:	4c 39 79 08          	cmp    %r15,0x8(%rcx)
    6194:	75 c2                	jne    6158 <receive+0x88>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6196:	bf 01 00 00 00       	mov    $0x1,%edi
    619b:	b9 01 00 00 00       	mov    $0x1,%ecx
    61a0:	ba 01 00 00 00       	mov    $0x1,%edx
    61a5:	31 c0                	xor    %eax,%eax
    61a7:	48 8d 35 52 13 00 00 	lea    0x1352(%rip),%rsi        # 7500 <_IO_stdin_used+0x500>
    61ae:	e8 9d c2 ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    61b3:	bf 01 00 00 00       	mov    $0x1,%edi
    61b8:	e8 e3 c2 ff ff       	call   24a0 <exit@plt>
    61bd:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    61c0:	41 83 fe 02          	cmp    $0x2,%r14d
    61c4:	74 3a                	je     6200 <receive+0x130>
    me->messages_count = 0;
    61c6:	48 c7 85 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rbp)
    asm volatile ("sfence" ::: "memory");
    61d1:	0f ae f8             	sfence
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    61d4:	8b 82 40 01 00 00    	mov    0x140(%rdx),%eax
    61da:	41 83 c4 01          	add    $0x1,%r12d
    61de:	49 83 c5 28          	add    $0x28,%r13
    61e2:	41 39 c4             	cmp    %eax,%r12d
    61e5:	0f 8c 15 ff ff ff    	jl     6100 <receive+0x30>
}
    61eb:	48 83 c4 08          	add    $0x8,%rsp
    61ef:	31 c0                	xor    %eax,%eax
    61f1:	5b                   	pop    %rbx
    61f2:	5d                   	pop    %rbp
    61f3:	41 5c                	pop    %r12
    61f5:	41 5d                	pop    %r13
    61f7:	41 5e                	pop    %r14
    61f9:	41 5f                	pop    %r15
    61fb:	c3                   	ret
    61fc:	0f 1f 40 00          	nopl   0x0(%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    6200:	83 bd 00 01 00 00 01 	cmpl   $0x1,0x100(%rbp)
    6207:	75 bd                	jne    61c6 <receive+0xf6>
      me->available = 0;
    6209:	c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbp)
    6213:	eb b1                	jmp    61c6 <receive+0xf6>
    6215:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    6218:	8b 8d 00 01 00 00    	mov    0x100(%rbp),%ecx
    621e:	83 f9 01             	cmp    $0x1,%ecx
    6221:	74 09                	je     622c <receive+0x15c>
    else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 0) {
    6223:	85 c9                	test   %ecx,%ecx
    6225:	74 b3                	je     61da <receive+0x10a>
    6227:	e9 ef fe ff ff       	jmp    611b <receive+0x4b>
    for (int x = 0 ; x < me->messages_count ; x++) {
    622c:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    6233:	48 85 ff             	test   %rdi,%rdi
    6236:	0f 8f ef fe ff ff    	jg     612b <receive+0x5b>
    623c:	eb cb                	jmp    6209 <receive+0x139>
}
    623e:	31 c0                	xor    %eax,%eax
    6240:	c3                   	ret
    6241:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    624c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006250 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    6250:	f3 0f 1e fa          	endbr64
    6254:	41 56                	push   %r14
    6256:	55                   	push   %rbp
    6257:	53                   	push   %rbx
    6258:	48 89 fb             	mov    %rdi,%rbx
  if (data->thread_index == data->task_index) {
    625b:	8b 47 04             	mov    0x4(%rdi),%eax
    625e:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    6264:	74 4a                	je     62b0 <barriered_work+0x60>
    receive(data);
    6266:	e8 65 fe ff ff       	call   60d0 <receive>
    while (data->scheduled == 1) {
    626b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6272:	75 18                	jne    628c <barriered_work+0x3c>
    6274:	0f 1f 40 00          	nopl   0x0(%rax)
      data->n++;
    6278:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    6280:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6283:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    628a:	74 ec                	je     6278 <barriered_work+0x28>
  if (data->sending == 1) {
    628c:	83 bb 80 01 00 00 01 	cmpl   $0x1,0x180(%rbx)
    6293:	75 08                	jne    629d <barriered_work+0x4d>
    6295:	48 89 df             	mov    %rbx,%rdi
    6298:	e8 93 e2 ff ff       	call   4530 <sendm.part.0>
  asm volatile ("sfence" ::: "memory");
    629d:	0f ae f8             	sfence
}
    62a0:	31 c0                	xor    %eax,%eax
    62a2:	5b                   	pop    %rbx
    62a3:	5d                   	pop    %rbp
    62a4:	41 5e                	pop    %r14
    62a6:	c3                   	ret
    62a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      receive(data);
    62b0:	e8 1b fe ff ff       	call   60d0 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    62b5:	48 63 8b 40 01 00 00 	movslq 0x140(%rbx),%rcx
        int t = data->task_index;
    62bc:	8b 43 04             	mov    0x4(%rbx),%eax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    62bf:	85 c9                	test   %ecx,%ecx
    62c1:	0f 8e d6 00 00 00    	jle    639d <barriered_work+0x14d>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    62c7:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    62ce:	4c 63 d0             	movslq %eax,%r10
              int next_task = abs((t + 1) % (data->thread_count));
    62d1:	83 c0 01             	add    $0x1,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    62d4:	49 c1 e2 09          	shl    $0x9,%r10
    62d8:	48 8b 72 20          	mov    0x20(%rdx),%rsi
              int next_task = abs((t + 1) % (data->thread_count));
    62dc:	99                   	cltd
    62dd:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    62e3:	48 8d 6e 38          	lea    0x38(%rsi),%rbp
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    62e7:	49 89 eb             	mov    %rbp,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    62ea:	89 d0                	mov    %edx,%eax
    62ec:	f7 d8                	neg    %eax
    62ee:	0f 49 d0             	cmovns %eax,%edx
    62f1:	48 8d 04 49          	lea    (%rcx,%rcx,2),%rax
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    62f5:	45 31 c0             	xor    %r8d,%r8d
    62f8:	48 c1 e0 06          	shl    $0x6,%rax
              int next_task = abs((t + 1) % (data->thread_count));
    62fc:	4c 63 ca             	movslq %edx,%r9
    62ff:	48 8d 74 06 38       	lea    0x38(%rsi,%rax,1),%rsi
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    6304:	49 c1 e1 09          	shl    $0x9,%r9
    6308:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6310:	49 8b 03             	mov    (%r11),%rax
    6313:	48 89 ea             	mov    %rbp,%rdx
    6316:	4a 8b 84 10 70 01 00 00 	mov    0x170(%rax,%r10,1),%rax
    631e:	48 83 c0 08          	add    $0x8,%rax
    6322:	eb 3d                	jmp    6361 <barriered_work+0x111>
    6324:	0f 1f 40 00          	nopl   0x0(%rax)
                 if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 0) {
    6328:	8b b9 00 01 00 00    	mov    0x100(%rcx),%edi
    632e:	85 ff                	test   %edi,%edi
    6330:	75 1f                	jne    6351 <barriered_work+0x101>
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    6332:	48 8b 3a             	mov    (%rdx),%rdi
    6335:	4e 8b b4 0f 70 01 00 00 	mov    0x170(%rdi,%r9,1),%r14
    633d:	4d 01 c6             	add    %r8,%r14
    6340:	49 89 0e             	mov    %rcx,(%r14)
                  ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available = 1;
    6343:	49 8b 4e 08          	mov    0x8(%r14),%rcx
    6347:	c7 81 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rcx)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6351:	48 81 c2 c0 00 00 00 	add    $0xc0,%rdx
    6358:	48 83 c0 28          	add    $0x28,%rax
    635c:	48 39 d6             	cmp    %rdx,%rsi
    635f:	74 28                	je     6389 <barriered_work+0x139>
              if (kind == MAILBOX_FRIEND) {
    6361:	83 78 18 01          	cmpl   $0x1,0x18(%rax)
                tmp = data->thread->all_threads[y].tasks[t].mailboxes[b].higher; 
    6365:	48 8b 08             	mov    (%rax),%rcx
              if (kind == MAILBOX_FRIEND) {
    6368:	75 be                	jne    6328 <barriered_work+0xd8>
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    636a:	48 8b 3a             	mov    (%rdx),%rdi
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    636d:	48 81 c2 c0 00 00 00 	add    $0xc0,%rdx
    6374:	48 83 c0 28          	add    $0x28,%rax
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    6378:	4a 8b bc 0f 70 01 00 00 	mov    0x170(%rdi,%r9,1),%rdi
    6380:	4a 89 0c 07          	mov    %rcx,(%rdi,%r8,1)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6384:	48 39 d6             	cmp    %rdx,%rsi
    6387:	75 d8                	jne    6361 <barriered_work+0x111>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6389:	49 81 c3 c0 00 00 00 	add    $0xc0,%r11
    6390:	49 83 c0 28          	add    $0x28,%r8
    6394:	4c 39 de             	cmp    %r11,%rsi
    6397:	0f 85 73 ff ff ff    	jne    6310 <barriered_work+0xc0>
      asm volatile ("sfence" ::: "memory");
    639d:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    63a0:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    63a7:	31 ff                	xor    %edi,%edi
    63a9:	48 c1 e6 05          	shl    $0x5,%rsi
    63ad:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    63b4:	e8 57 bf ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    63b9:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    63c0:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    63c7:	48 8b 50 48          	mov    0x48(%rax),%rdx
    63cb:	8b 72 10             	mov    0x10(%rdx),%esi
    63ce:	8d 6e 01             	lea    0x1(%rsi),%ebp
    63d1:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    63d4:	75 5b                	jne    6431 <barriered_work+0x1e1>
    63d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    63e0:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    63e7:	48 8b 40 18          	mov    0x18(%rax),%rax
    63eb:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
      data->n++;
    63ef:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    63f7:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    63fb:	48 c1 e7 09          	shl    $0x9,%rdi
    63ff:	48 03 78 38          	add    0x38(%rax),%rdi
    6403:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    6409:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    640c:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    6413:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    641a:	74 c4                	je     63e0 <barriered_work+0x190>
    if (modcount != data->thread->protected_state->modcount) {
    641c:	48 8b 40 48          	mov    0x48(%rax),%rax
    6420:	3b 68 10             	cmp    0x10(%rax),%ebp
    6423:	74 0c                	je     6431 <barriered_work+0x1e1>
    6425:	48 8d 3d f9 0d 00 00 	lea    0xdf9(%rip),%rdi        # 7225 <_IO_stdin_used+0x225>
    642c:	e8 bf be ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6431:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6438:	31 ff                	xor    %edi,%edi
    643a:	48 c1 e6 05          	shl    $0x5,%rsi
    643e:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6445:	48 83 c6 10          	add    $0x10,%rsi
    6449:	e8 c2 be ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    644e:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6455:	48 83 c0 01          	add    $0x1,%rax
    6459:	48 99                	cqto
    645b:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6462:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    6469:	e9 1e fe ff ff       	jmp    628c <barriered_work+0x3c>
    646e:	66 90                	xchg   %ax,%ax

0000000000006470 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6470:	f3 0f 1e fa          	endbr64
    6474:	53                   	push   %rbx
    6475:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6478:	e8 63 f8 ff ff       	call   5ce0 <barriered_work_ingest>
  barriered_work(data);
    647d:	48 89 df             	mov    %rbx,%rdi
}
    6480:	5b                   	pop    %rbx
  barriered_work(data);
    6481:	e9 ca fd ff ff       	jmp    6250 <barriered_work>
    6486:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006490 <sendm>:
int sendm(struct BarrierTask *data) {
    6490:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    6494:	83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%rdi)
    649b:	74 03                	je     64a0 <sendm+0x10>
}
    649d:	31 c0                	xor    %eax,%eax
    649f:	c3                   	ret
int sendm(struct BarrierTask *data) {
    64a0:	48 83 ec 08          	sub    $0x8,%rsp
    64a4:	e8 87 e0 ff ff       	call   4530 <sendm.part.0>
}
    64a9:	31 c0                	xor    %eax,%eax
    64ab:	48 83 c4 08          	add    $0x8,%rsp
    64af:	c3                   	ret

00000000000064b0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    64b0:	f3 0f 1e fa          	endbr64
}
    64b4:	31 c0                	xor    %eax,%eax
    64b6:	c3                   	ret
    64b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000064c0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    64c0:	f3 0f 1e fa          	endbr64
    64c4:	31 c0                	xor    %eax,%eax
    64c6:	c3                   	ret
    64c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000064d0 <after>:
int after(struct timespec left, struct timespec right) {
    64d0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    64d4:	31 c0                	xor    %eax,%eax
    64d6:	48 39 d7             	cmp    %rdx,%rdi
    64d9:	7e 08                	jle    64e3 <after+0x13>
    64db:	31 c0                	xor    %eax,%eax
    64dd:	48 39 ce             	cmp    %rcx,%rsi
    64e0:	0f 9f c0             	setg   %al
}
    64e3:	c3                   	ret
    64e4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    64ef:	90                   	nop

00000000000064f0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    64f0:	f3 0f 1e fa          	endbr64
    64f4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    64f9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    64fe:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6500:	48 39 d7             	cmp    %rdx,%rdi
    6503:	7f 18                	jg     651d <within+0x2d>
    6505:	4d 39 d8             	cmp    %r11,%r8
    6508:	0f 9e c2             	setle  %dl
    650b:	48 39 ce             	cmp    %rcx,%rsi
    650e:	0f 9e c0             	setle  %al
    6511:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6513:	31 c0                	xor    %eax,%eax
    6515:	4d 39 d1             	cmp    %r10,%r9
    6518:	0f 9e c0             	setle  %al
    651b:	21 d0                	and    %edx,%eax
}
    651d:	c3                   	ret
    651e:	66 90                	xchg   %ax,%ax

0000000000006520 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6520:	f3 0f 1e fa          	endbr64
    6524:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6529:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    652e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6533:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6538:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    653d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6542:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6547:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    654c:	48 39 fe             	cmp    %rdi,%rsi
    654f:	7d 2f                	jge    6580 <overlap+0x60>
    6551:	48 39 ca             	cmp    %rcx,%rdx
    6554:	7d 62                	jge    65b8 <overlap+0x98>
    6556:	4d 39 da             	cmp    %r11,%r10
    6559:	7d 0e                	jge    6569 <overlap+0x49>
    return 1;
    655b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6560:	4d 39 c1             	cmp    %r8,%r9
    6563:	0f 8c 7f 00 00 00    	jl     65e8 <overlap+0xc8>
  return 0;
    6569:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    656b:	4d 39 c1             	cmp    %r8,%r9
    656e:	7f 4c                	jg     65bc <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6570:	31 c0                	xor    %eax,%eax
    6572:	4d 39 da             	cmp    %r11,%r10
    6575:	0f 9e c0             	setle  %al
    6578:	c3                   	ret
    6579:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6580:	7e 4e                	jle    65d0 <overlap+0xb0>
    6582:	48 39 ca             	cmp    %rcx,%rdx
    6585:	7f 39                	jg     65c0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6587:	75 31                	jne    65ba <overlap+0x9a>
    6589:	4d 39 c1             	cmp    %r8,%r9
    658c:	7c 2c                	jl     65ba <overlap+0x9a>
    return 1;
    658e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6593:	4d 39 da             	cmp    %r11,%r10
    6596:	7d 24                	jge    65bc <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6598:	48 39 ca             	cmp    %rcx,%rdx
    659b:	0f 94 c2             	sete   %dl
    659e:	48 39 fe             	cmp    %rdi,%rsi
    65a1:	0f 94 c0             	sete   %al
    65a4:	21 c2                	and    %eax,%edx
    65a6:	31 c0                	xor    %eax,%eax
    65a8:	4d 39 c1             	cmp    %r8,%r9
    65ab:	0f 94 c0             	sete   %al
    65ae:	21 d0                	and    %edx,%eax
    65b0:	c3                   	ret
    65b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    65b8:	74 af                	je     6569 <overlap+0x49>
  return 0;
    65ba:	31 c0                	xor    %eax,%eax
}
    65bc:	c3                   	ret
    65bd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    65c0:	4d 39 da             	cmp    %r11,%r10
    65c3:	7e c4                	jle    6589 <overlap+0x69>
    return 1;
    65c5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    65ca:	4d 39 c1             	cmp    %r8,%r9
    65cd:	7e ba                	jle    6589 <overlap+0x69>
    65cf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    65d0:	48 39 ca             	cmp    %rcx,%rdx
    65d3:	7c 94                	jl     6569 <overlap+0x49>
    65d5:	4d 39 c1             	cmp    %r8,%r9
    65d8:	7d b4                	jge    658e <overlap+0x6e>
    65da:	48 39 ca             	cmp    %rcx,%rdx
    65dd:	74 91                	je     6570 <overlap+0x50>
    65df:	eb d9                	jmp    65ba <overlap+0x9a>
    65e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    65e8:	c3                   	ret
    65e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000065f0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    65f0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    65f4:	85 f6                	test   %esi,%esi
    65f6:	0f 8e 44 03 00 00    	jle    6940 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    65fc:	41 57                	push   %r15
    65fe:	41 89 f7             	mov    %esi,%r15d
    6601:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6603:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6606:	41 55                	push   %r13
    6608:	41 54                	push   %r12
    660a:	55                   	push   %rbp
    660b:	53                   	push   %rbx
    660c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6610:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6614:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6619:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    661e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6621:	45 39 e6             	cmp    %r12d,%r14d
    6624:	0f 84 4e 02 00 00    	je     6878 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    662a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    662f:	8b 50 08             	mov    0x8(%rax),%edx
    6632:	85 d2                	test   %edx,%edx
    6634:	0f 8e 3e 02 00 00    	jle    6878 <verify+0x288>
    663a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    663f:	31 c9                	xor    %ecx,%ecx
    6641:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    6646:	31 c0                	xor    %eax,%eax
    6648:	44 89 f2             	mov    %r14d,%edx
    664b:	bf 01 00 00 00       	mov    $0x1,%edi
    6650:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6655:	48 8d 35 d9 0b 00 00 	lea    0xbd9(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    665c:	e8 ef bd ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6661:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6666:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    666b:	8b 40 08             	mov    0x8(%rax),%eax
    666e:	85 c0                	test   %eax,%eax
    6670:	0f 8e e6 01 00 00    	jle    685c <verify+0x26c>
    6676:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6679:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    667e:	31 db                	xor    %ebx,%ebx
    6680:	48 c1 e0 09          	shl    $0x9,%rax
    6684:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6689:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    668e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6693:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6698:	4c 8b 20             	mov    (%rax),%r12
    669b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    66a0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    66a5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    66aa:	49 89 de             	mov    %rbx,%r14
    66ad:	48 8d 35 96 0b 00 00 	lea    0xb96(%rip),%rsi        # 724a <_IO_stdin_used+0x24a>
    66b4:	49 c1 e6 09          	shl    $0x9,%r14
    66b8:	bf 01 00 00 00       	mov    $0x1,%edi
    66bd:	48 8b 45 00          	mov    0x0(%rbp),%rax
    66c1:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    66c9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    66ce:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    66d6:	31 c0                	xor    %eax,%eax
    66d8:	e8 73 bd ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    66dd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    66e2:	4c 8b 20             	mov    (%rax),%r12
    66e5:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    66ee:	0f 8e 47 01 00 00    	jle    683b <verify+0x24b>
    66f4:	4c 03 75 00          	add    0x0(%rbp),%r14
    66f8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    66fd:	ba 01 00 00 00       	mov    $0x1,%edx
    6702:	4d 89 f5             	mov    %r14,%r13
    6705:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    670c:	4d 85 f6             	test   %r14,%r14
    670f:	0f 8e 21 01 00 00    	jle    6836 <verify+0x246>
    6715:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6718:	48 89 d5             	mov    %rdx,%rbp
    671b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6720:	31 db                	xor    %ebx,%ebx
    6722:	4d 89 f2             	mov    %r14,%r10
    6725:	48 c1 e5 05          	shl    $0x5,%rbp
    6729:	48 83 ed 20          	sub    $0x20,%rbp
    672d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6731:	49 89 ee             	mov    %rbp,%r14
    6734:	48 89 dd             	mov    %rbx,%rbp
    6737:	48 89 d3             	mov    %rdx,%rbx
    673a:	eb 31                	jmp    676d <verify+0x17d>
    673c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6740:	4c 39 c2             	cmp    %r8,%rdx
    6743:	0f 8d 57 01 00 00    	jge    68a0 <verify+0x2b0>
    6749:	4c 39 df             	cmp    %r11,%rdi
    674c:	7e 05                	jle    6753 <verify+0x163>
    674e:	49 39 c1             	cmp    %rax,%r9
    6751:	7c 75                	jl     67c8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6753:	4c 39 df             	cmp    %r11,%rdi
    6756:	0f 8d ab 01 00 00    	jge    6907 <verify+0x317>
    675c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6760:	48 83 c5 01          	add    $0x1,%rbp
    6764:	49 39 ea             	cmp    %rbp,%r10
    6767:	0f 8e a9 00 00 00    	jle    6816 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    676d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    6774:	48 89 e8             	mov    %rbp,%rax
    6777:	48 c1 e0 05          	shl    $0x5,%rax
    677b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    6782:	4c 01 f2             	add    %r14,%rdx
    6785:	48 8b 08             	mov    (%rax),%rcx
    6788:	48 8b 78 10          	mov    0x10(%rax),%rdi
    678c:	48 8b 32             	mov    (%rdx),%rsi
    678f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6793:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6797:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    679b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    679f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    67a3:	48 39 f1             	cmp    %rsi,%rcx
    67a6:	7c 98                	jl     6740 <verify+0x150>
    67a8:	0f 8e 42 01 00 00    	jle    68f0 <verify+0x300>
    67ae:	4c 39 c2             	cmp    %r8,%rdx
    67b1:	0f 8f f9 00 00 00    	jg     68b0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    67b7:	75 a7                	jne    6760 <verify+0x170>
    67b9:	4c 39 df             	cmp    %r11,%rdi
    67bc:	7f a2                	jg     6760 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    67be:	49 39 c1             	cmp    %rax,%r9
    67c1:	7c 9d                	jl     6760 <verify+0x170>
    67c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    67c8:	49 89 c1             	mov    %rax,%r9
    67cb:	48 89 f9             	mov    %rdi,%rcx
    67ce:	48 89 f2             	mov    %rsi,%rdx
    67d1:	bf 01 00 00 00       	mov    $0x1,%edi
    67d6:	48 8d 35 4b 0d 00 00 	lea    0xd4b(%rip),%rsi        # 7528 <_IO_stdin_used+0x528>
    67dd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    67df:	48 83 c5 01          	add    $0x1,%rbp
    67e3:	e8 68 bc ff ff       	call   2450 <__printf_chk@plt>
    67e8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    67ed:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    67f2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    67f5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    67fa:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6801:	4c 8b 20             	mov    (%rax),%r12
    6804:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6809:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    680d:	49 39 ea             	cmp    %rbp,%r10
    6810:	0f 8f 57 ff ff ff    	jg     676d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6816:	48 89 da             	mov    %rbx,%rdx
    6819:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    6820:	7d 14                	jge    6836 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6822:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6829:	48 83 c2 01          	add    $0x1,%rdx
    682d:	4d 85 f6             	test   %r14,%r14
    6830:	0f 8f e2 fe ff ff    	jg     6718 <verify+0x128>
    6836:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    683b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6840:	48 83 c3 01          	add    $0x1,%rbx
    6844:	39 58 08             	cmp    %ebx,0x8(%rax)
    6847:	0f 8f 53 fe ff ff    	jg     66a0 <verify+0xb0>
    684d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6852:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6857:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    685c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6861:	48 83 c1 01          	add    $0x1,%rcx
    6865:	39 48 08             	cmp    %ecx,0x8(%rax)
    6868:	0f 8f d8 fd ff ff    	jg     6646 <verify+0x56>
    686e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6873:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6878:	48 81 44 24 10 c0 00 00 00 	addq   $0xc0,0x10(%rsp)
    6881:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6886:	41 39 c7             	cmp    %eax,%r15d
    6889:	0f 84 86 00 00 00    	je     6915 <verify+0x325>
    688f:	41 89 c4             	mov    %eax,%r12d
    6892:	e9 8a fd ff ff       	jmp    6621 <verify+0x31>
    6897:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    68a0:	0f 85 ba fe ff ff    	jne    6760 <verify+0x170>
    68a6:	e9 a8 fe ff ff       	jmp    6753 <verify+0x163>
    68ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    68b0:	49 39 c1             	cmp    %rax,%r9
    68b3:	7e 09                	jle    68be <verify+0x2ce>
    68b5:	4c 39 df             	cmp    %r11,%rdi
    68b8:	0f 8c 0a ff ff ff    	jl     67c8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    68be:	4c 39 df             	cmp    %r11,%rdi
    68c1:	0f 8f 99 fe ff ff    	jg     6760 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    68c7:	49 39 c1             	cmp    %rax,%r9
    68ca:	0f 8d f8 fe ff ff    	jge    67c8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    68d0:	48 39 f1             	cmp    %rsi,%rcx
    68d3:	0f 85 87 fe ff ff    	jne    6760 <verify+0x170>
    68d9:	4c 39 c2             	cmp    %r8,%rdx
    68dc:	0f 85 7e fe ff ff    	jne    6760 <verify+0x170>
    68e2:	4c 39 df             	cmp    %r11,%rdi
    68e5:	0f 84 dd fe ff ff    	je     67c8 <verify+0x1d8>
    68eb:	e9 70 fe ff ff       	jmp    6760 <verify+0x170>
    68f0:	4c 39 c2             	cmp    %r8,%rdx
    68f3:	0f 8c 5a fe ff ff    	jl     6753 <verify+0x163>
    68f9:	4c 39 df             	cmp    %r11,%rdi
    68fc:	7e c9                	jle    68c7 <verify+0x2d7>
    68fe:	4c 39 c2             	cmp    %r8,%rdx
    6901:	0f 85 59 fe ff ff    	jne    6760 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6907:	49 39 c1             	cmp    %rax,%r9
    690a:	0f 8f 50 fe ff ff    	jg     6760 <verify+0x170>
    6910:	e9 b3 fe ff ff       	jmp    67c8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    6915:	48 81 44 24 18 c0 00 00 00 	addq   $0xc0,0x18(%rsp)
    691e:	41 8d 46 01          	lea    0x1(%r14),%eax
    6922:	45 39 e6             	cmp    %r12d,%r14d
    6925:	74 08                	je     692f <verify+0x33f>
    6927:	41 89 c6             	mov    %eax,%r14d
    692a:	e9 ea fc ff ff       	jmp    6619 <verify+0x29>
}
    692f:	48 83 c4 58          	add    $0x58,%rsp
    6933:	31 c0                	xor    %eax,%eax
    6935:	5b                   	pop    %rbx
    6936:	5d                   	pop    %rbp
    6937:	41 5c                	pop    %r12
    6939:	41 5d                	pop    %r13
    693b:	41 5e                	pop    %r14
    693d:	41 5f                	pop    %r15
    693f:	c3                   	ret
    6940:	31 c0                	xor    %eax,%eax
    6942:	c3                   	ret

Disassembly of section .fini:

0000000000006944 <_fini>:
    6944:	f3 0f 1e fa          	endbr64
    6948:	48 83 ec 08          	sub    $0x8,%rsp
    694c:	48 83 c4 08          	add    $0x8,%rsp
    6950:	c3                   	ret
