
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
    25f6:	48 8d 3d d3 4f 00 00 	lea    0x4fd3(%rip),%rdi        # 75d0 <_IO_stdin_used+0x5d0>
    25fd:	41 56                	push   %r14
    25ff:	41 55                	push   %r13
    2601:	41 54                	push   %r12
    2603:	55                   	push   %rbp
    2604:	53                   	push   %rbx
    2605:	48 81 ec b8 00 00 00 	sub    $0xb8,%rsp
    260c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2615:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
    261d:	48 8d 05 5c 17 00 00 	lea    0x175c(%rip),%rax        # 3d80 <barriered_reset>
    2624:	66 48 0f 6e f8       	movq   %rax,%xmm7
    2629:	0f 16 3d 48 76 00 00 	movhps 0x7648(%rip),%xmm7        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    2630:	0f 29 7c 24 60       	movaps %xmm7,0x60(%rsp)
    2635:	e8 b6 fc ff ff       	call   22f0 <puts@plt>
    263a:	bf 0a 00 00 00       	mov    $0xa,%edi
    263f:	e8 8c fc ff ff       	call   22d0 <putchar@plt>
    2644:	ba 02 00 00 00       	mov    $0x2,%edx
    2649:	48 8d 35 14 4c 00 00 	lea    0x4c14(%rip),%rsi        # 7264 <_IO_stdin_used+0x264>
    2650:	31 c0                	xor    %eax,%eax
    2652:	bf 01 00 00 00       	mov    $0x1,%edi
    2657:	e8 f4 fd ff ff       	call   2450 <__printf_chk@plt>
    265c:	ba 04 00 00 00       	mov    $0x4,%edx
    2661:	48 8d 35 0c 4c 00 00 	lea    0x4c0c(%rip),%rsi        # 7274 <_IO_stdin_used+0x274>
    2668:	31 c0                	xor    %eax,%eax
    266a:	bf 01 00 00 00       	mov    $0x1,%edi
    266f:	e8 dc fd ff ff       	call   2450 <__printf_chk@plt>
    2674:	ba 02 00 00 00       	mov    $0x2,%edx
    2679:	48 8d 35 09 4c 00 00 	lea    0x4c09(%rip),%rsi        # 7289 <_IO_stdin_used+0x289>
    2680:	31 c0                	xor    %eax,%eax
    2682:	bf 01 00 00 00       	mov    $0x1,%edi
    2687:	e8 c4 fd ff ff       	call   2450 <__printf_chk@plt>
    268c:	ba 02 00 00 00       	mov    $0x2,%edx
    2691:	48 8d 35 01 4c 00 00 	lea    0x4c01(%rip),%rsi        # 7299 <_IO_stdin_used+0x299>
    2698:	31 c0                	xor    %eax,%eax
    269a:	bf 01 00 00 00       	mov    $0x1,%edi
    269f:	e8 ac fd ff ff       	call   2450 <__printf_chk@plt>
    26a4:	48 8d 3d 04 4c 00 00 	lea    0x4c04(%rip),%rdi        # 72af <_IO_stdin_used+0x2af>
    26ab:	e8 40 fc ff ff       	call   22f0 <puts@plt>
    26b0:	ba 02 00 00 00       	mov    $0x2,%edx
    26b5:	48 8d 35 0f 4c 00 00 	lea    0x4c0f(%rip),%rsi        # 72cb <_IO_stdin_used+0x2cb>
    26bc:	31 c0                	xor    %eax,%eax
    26be:	bf 01 00 00 00       	mov    $0x1,%edi
    26c3:	e8 88 fd ff ff       	call   2450 <__printf_chk@plt>
    26c8:	ba 08 00 00 00       	mov    $0x8,%edx
    26cd:	48 8d 35 11 4c 00 00 	lea    0x4c11(%rip),%rsi        # 72e5 <_IO_stdin_used+0x2e5>
    26d4:	31 c0                	xor    %eax,%eax
    26d6:	bf 01 00 00 00       	mov    $0x1,%edi
    26db:	e8 70 fd ff ff       	call   2450 <__printf_chk@plt>
    26e0:	ba 01 00 00 00       	mov    $0x1,%edx
    26e5:	48 8d 35 0d 4c 00 00 	lea    0x4c0d(%rip),%rsi        # 72f9 <_IO_stdin_used+0x2f9>
    26ec:	31 c0                	xor    %eax,%eax
    26ee:	bf 01 00 00 00       	mov    $0x1,%edi
    26f3:	e8 58 fd ff ff       	call   2450 <__printf_chk@plt>
    26f8:	ba 01 00 00 00       	mov    $0x1,%edx
    26fd:	48 8d 35 06 4c 00 00 	lea    0x4c06(%rip),%rsi        # 730a <_IO_stdin_used+0x30a>
    2704:	31 c0                	xor    %eax,%eax
    2706:	bf 01 00 00 00       	mov    $0x1,%edi
    270b:	e8 40 fd ff ff       	call   2450 <__printf_chk@plt>
    2710:	ba 02 00 00 00       	mov    $0x2,%edx
    2715:	48 8d 35 06 4c 00 00 	lea    0x4c06(%rip),%rsi        # 7322 <_IO_stdin_used+0x322>
    271c:	31 c0                	xor    %eax,%eax
    271e:	bf 01 00 00 00       	mov    $0x1,%edi
    2723:	e8 28 fd ff ff       	call   2450 <__printf_chk@plt>
    2728:	ba 01 00 00 00       	mov    $0x1,%edx
    272d:	48 8d 35 04 4f 00 00 	lea    0x4f04(%rip),%rsi        # 7638 <_IO_stdin_used+0x638>
    2734:	31 c0                	xor    %eax,%eax
    2736:	bf 01 00 00 00       	mov    $0x1,%edi
    273b:	e8 10 fd ff ff       	call   2450 <__printf_chk@plt>
    2740:	ba 01 00 00 00       	mov    $0x1,%edx
    2745:	48 8d 35 1c 4f 00 00 	lea    0x4f1c(%rip),%rsi        # 7668 <_IO_stdin_used+0x668>
    274c:	31 c0                	xor    %eax,%eax
    274e:	bf 01 00 00 00       	mov    $0x1,%edi
    2753:	e8 f8 fc ff ff       	call   2450 <__printf_chk@plt>
    2758:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    275d:	48 8d 35 da 4b 00 00 	lea    0x4bda(%rip),%rsi        # 733e <_IO_stdin_used+0x33e>
    2764:	31 c0                	xor    %eax,%eax
    2766:	bf 01 00 00 00       	mov    $0x1,%edi
    276b:	e8 e0 fc ff ff       	call   2450 <__printf_chk@plt>
    2770:	ba 05 00 00 00       	mov    $0x5,%edx
    2775:	48 8d 35 dc 4b 00 00 	lea    0x4bdc(%rip),%rsi        # 7358 <_IO_stdin_used+0x358>
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
    27ad:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27b2:	e8 e9 fb ff ff       	call   23a0 <calloc@plt>
    27b7:	ba 04 00 00 00       	mov    $0x4,%edx
    27bc:	bf 01 00 00 00       	mov    $0x1,%edi
    27c1:	48 8d 35 a4 4b 00 00 	lea    0x4ba4(%rip),%rsi        # 736c <_IO_stdin_used+0x36c>
    27c8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    27cd:	31 c0                	xor    %eax,%eax
    27cf:	e8 7c fc ff ff       	call   2450 <__printf_chk@plt>
    27d4:	ba 08 00 00 00       	mov    $0x8,%edx
    27d9:	48 8d 35 a2 4b 00 00 	lea    0x4ba2(%rip),%rsi        # 7382 <_IO_stdin_used+0x382>
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
    27fb:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
    2803:	48 89 c5             	mov    %rax,%rbp
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    2806:	48 8d 98 80 00 00 00 	lea    0x80(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    280d:	49 89 c4             	mov    %rax,%r12
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2810:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    2815:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    281d:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2822:	49 83 c4 10          	add    $0x10,%r12
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2826:	e8 75 fb ff ff       	call   23a0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    282b:	be 20 00 00 00       	mov    $0x20,%esi
    2830:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2835:	49 89 44 24 f8       	mov    %rax,-0x8(%r12)
    283a:	49 89 c5             	mov    %rax,%r13
      buffers[x].buffer[y].available = 0;
    283d:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2847:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2851:	e8 4a fb ff ff       	call   23a0 <calloc@plt>
    2856:	49 89 85 88 00 00 00 	mov    %rax,0x88(%r13)
  for (int x = 0 ; x < buffers_required; x++) {
    285d:	49 39 dc             	cmp    %rbx,%r12
    2860:	75 ae                	jne    2810 <main+0x220>
    2862:	4c 8b 5c 24 58       	mov    0x58(%rsp),%r11
    }
  }
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
    2867:	45 31 e4             	xor    %r12d,%r12d
  for (int x = 0 ; x < buffers_required; x++) {
    286a:	b8 01 00 00 00       	mov    $0x1,%eax
    286f:	48 89 eb             	mov    %rbp,%rbx
    2872:	48 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%rsp)
    287b:	44 89 e1             	mov    %r12d,%ecx
  int my_buffers = 0;
  int cur_buffer = 0;
    287e:	c7 44 24 50 00 00 00 00 	movl   $0x0,0x50(%rsp)
    2886:	4c 89 df             	mov    %r11,%rdi
    2889:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    288e:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2893:	89 44 24 70          	mov    %eax,0x70(%rsp)
    2897:	89 cd                	mov    %ecx,%ebp
    2899:	48 89 7c 24 78       	mov    %rdi,0x78(%rsp)
    289e:	48 89 f2             	mov    %rsi,%rdx
    28a1:	89 b4 24 8c 00 00 00 	mov    %esi,0x8c(%rsp)
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    28a8:	41 89 f4             	mov    %esi,%r12d
    28ab:	48 f7 da             	neg    %rdx
    28ae:	48 89 9c 24 98 00 00 00 	mov    %rbx,0x98(%rsp)
    28b6:	81 e2 80 01 00 00    	and    $0x180,%edx
    28bc:	4e 8d 3c 1a          	lea    (%rdx,%r11,1),%r15
    28c0:	48 63 54 24 50       	movslq 0x50(%rsp),%rdx
    28c5:	4d 89 f9             	mov    %r15,%r9
    28c8:	48 c1 e2 04          	shl    $0x4,%rdx
    28cc:	4c 8d 34 13          	lea    (%rbx,%rdx,1),%r14
    28d0:	8d 50 fe             	lea    -0x2(%rax),%edx
    28d3:	89 14 24             	mov    %edx,(%rsp)
    28d6:	4d 89 f7             	mov    %r14,%r15
    28d9:	44 8b 04 24          	mov    (%rsp),%r8d
    28dd:	bf 01 00 00 00       	mov    $0x1,%edi
    28e2:	31 c0                	xor    %eax,%eax
    28e4:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    28e9:	8b 94 24 8c 00 00 00 	mov    0x8c(%rsp),%edx
    28f0:	48 8d 35 99 4d 00 00 	lea    0x4d99(%rip),%rsi        # 7690 <_IO_stdin_used+0x690>
    28f7:	44 89 44 24 40       	mov    %r8d,0x40(%rsp)
    28fc:	45 89 c6             	mov    %r8d,%r14d
    28ff:	41 83 c0 01          	add    $0x1,%r8d
    2903:	44 89 c1             	mov    %r8d,%ecx
    2906:	44 89 04 24          	mov    %r8d,(%rsp)
    290a:	e8 41 fb ff ff       	call   2450 <__printf_chk@plt>
      int x = (k * threads_per_group) + d;
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    290f:	be 08 00 00 00       	mov    $0x8,%esi
    2914:	bf 02 00 00 00       	mov    $0x2,%edi
    2919:	e8 82 fa ff ff       	call   23a0 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    291e:	be 80 00 00 00       	mov    $0x80,%esi
    2923:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2928:	48 89 c3             	mov    %rax,%rbx
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    292b:	e8 70 fa ff ff       	call   23a0 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2930:	44 8b 04 24          	mov    (%rsp),%r8d
    2934:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2939:	49 89 c5             	mov    %rax,%r13
      if (x % 2 == 1) {
    293c:	41 83 e0 01          	and    $0x1,%r8d
    2940:	44 89 44 24 48       	mov    %r8d,0x48(%rsp)
    2945:	0f 84 6b 07 00 00    	je     30b6 <main+0xac6>
        other = abs(x - 1) % total_threads;
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    294b:	44 89 f0             	mov    %r14d,%eax
    294e:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
        other = abs(x - 1) % total_threads;
    2953:	44 89 f1             	mov    %r14d,%ecx
        my_thread_data[1] = &thread_data[x]; 
    2956:	4c 89 ca             	mov    %r9,%rdx
        my_thread_data[0] = &thread_data[other]; 
    2959:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    295d:	48 c1 e0 06          	shl    $0x6,%rax
    2961:	48 01 f8             	add    %rdi,%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2964:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    2968:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    296d:	48 8b 7c 24 78       	mov    0x78(%rsp),%rdi
    2972:	44 8b 34 24          	mov    (%rsp),%r14d
        thread_data[x].thread_index = 1;
    2976:	45 89 41 04          	mov    %r8d,0x4(%r9)
    297a:	48 8d 35 3f 4d 00 00 	lea    0x4d3f(%rip),%rsi        # 76c0 <_IO_stdin_used+0x6c0>
    2981:	48 89 53 08          	mov    %rdx,0x8(%rbx)
        thread_data[x].protected_state = &protected_state[k];
    2985:	49 89 79 48          	mov    %rdi,0x48(%r9)
    2989:	44 89 f2             	mov    %r14d,%edx
    298c:	bf 01 00 00 00       	mov    $0x1,%edi
    2991:	48 89 03             	mov    %rax,(%rbx)
    2994:	31 c0                	xor    %eax,%eax
    2996:	4c 89 4c 24 20       	mov    %r9,0x20(%rsp)
    299b:	89 4c 24 18          	mov    %ecx,0x18(%rsp)
    299f:	e8 ac fa ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].other = other;
    29a4:	8b 4c 24 18          	mov    0x18(%rsp),%ecx
    29a8:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    29ad:	31 c0                	xor    %eax,%eax
    29af:	44 89 f2             	mov    %r14d,%edx
    29b2:	48 8d 35 37 4d 00 00 	lea    0x4d37(%rip),%rsi        # 76f0 <_IO_stdin_used+0x6f0>
    29b9:	bf 01 00 00 00       	mov    $0x1,%edi
    29be:	41 89 89 b8 00 00 00 	mov    %ecx,0xb8(%r9)
    29c5:	89 e9                	mov    %ebp,%ecx
    29c7:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    29cc:	e8 7f fa ff ff       	call   2450 <__printf_chk@plt>
        if (x < thread_count) {
    29d1:	41 83 fe 01          	cmp    $0x1,%r14d
    29d5:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    29da:	0f 8f 00 07 00 00    	jg     30e0 <main+0xaf0>
          CPU_SET(curcpu, sendercpu);
    29e0:	48 63 c5             	movslq %ebp,%rax
    29e3:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    29e9:	77 13                	ja     29fe <main+0x40e>
    29eb:	48 c1 e8 06          	shr    $0x6,%rax
    29ef:	ba 01 00 00 00       	mov    $0x1,%edx
    29f4:	89 e9                	mov    %ebp,%ecx
    29f6:	48 d3 e2             	shl    %cl,%rdx
    29f9:	49 09 54 c5 00       	or     %rdx,0x0(%r13,%rax,8)
          curcpu += 2;
    29fe:	83 c5 02             	add    $0x2,%ebp
      thread_data[x].real_thread_index = x;
    2a01:	8b 04 24             	mov    (%rsp),%eax
      thread_data[x].cpu_set = sendercpu;
    2a04:	4d 89 a9 b0 00 00 00 	mov    %r13,0xb0(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a0b:	45 31 ed             	xor    %r13d,%r13d
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a0e:	be 10 00 00 00       	mov    $0x10,%esi
      thread_data[x].kind = KERNEL_THREAD;
    2a13:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a1a:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].real_thread_index = x;
    2a1f:	41 89 41 08          	mov    %eax,0x8(%r9)
      thread_data[x].all_threads = thread_data;
    2a23:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    2a28:	49 89 59 18          	mov    %rbx,0x18(%r9)
      thread_data[x].all_threads = thread_data;
    2a2c:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].thread_count = 2;
    2a30:	48 8b 05 d9 51 00 00 	mov    0x51d9(%rip),%rax        # 7c10 <_IO_stdin_used+0xc10>
      thread_data[x].task_count = total_barrier_count;
    2a37:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].thread_count = 2;
    2a3f:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].task_count = total_barrier_count;
    2a43:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a48:	e8 53 f9 ff ff       	call   23a0 <calloc@plt>
    2a4d:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a52:	be 10 00 00 00       	mov    $0x10,%esi
    2a57:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a5c:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a60:	e8 3b f9 ff ff       	call   23a0 <calloc@plt>
    2a65:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a6a:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2a6f:	66 0f 6f 1d 69 51 00 00 	movdqa 0x5169(%rip),%xmm3        # 7be0 <_IO_stdin_used+0xbe0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a77:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a7c:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2a80:	41 0f 11 99 80 00 00 00 	movups %xmm3,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a88:	e8 13 f9 ff ff       	call   23a0 <calloc@plt>
    2a8d:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a92:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_timestamp_count = 0;
    2a97:	66 0f 6f 25 41 51 00 00 	movdqa 0x5141(%rip),%xmm4        # 7be0 <_IO_stdin_used+0xbe0>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a9f:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2aa4:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2aab:	41 0f 11 a1 98 00 00 00 	movups %xmm4,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2ab3:	e8 e8 f8 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks = barriers;
    2ab8:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2abd:	4c 89 bc 24 80 00 00 00 	mov    %r15,0x80(%rsp)
    2ac5:	89 ac 24 88 00 00 00 	mov    %ebp,0x88(%rsp)
    2acc:	48 89 c5             	mov    %rax,%rbp
        thread_data[x].tasks = barriers;
    2acf:	49 89 41 38          	mov    %rax,0x38(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2ad3:	4d 89 ce             	mov    %r9,%r14
          thread_data[x].tasks[y].protected = do_protected_write; 
    2ad6:	49 63 c5             	movslq %r13d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2ad9:	be 28 00 00 00       	mov    $0x28,%esi
    2ade:	bf 04 00 00 00       	mov    $0x4,%edi
          thread_data[x].tasks[y].protected = do_protected_write; 
    2ae3:	48 89 c3             	mov    %rax,%rbx
    2ae6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2aeb:	48 8d 05 4e 12 00 00 	lea    0x124e(%rip),%rax        # 3d40 <do_protected_write>
    2af2:	48 c1 e3 09          	shl    $0x9,%rbx
    2af6:	4c 8d 7c 1d 00       	lea    0x0(%rbp,%rbx,1),%r15
    2afb:	49 89 87 20 01 00 00 	mov    %rax,0x120(%r15)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2b02:	e8 99 f8 ff ff       	call   23a0 <calloc@plt>
            if (k == group_of) {
    2b07:	48 83 7c 24 08 00    	cmpq   $0x0,0x8(%rsp)
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b0d:	be 08 00 00 00       	mov    $0x8,%esi
    2b12:	bf 01 00 00 00       	mov    $0x1,%edi
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2b17:	49 89 87 70 01 00 00 	mov    %rax,0x170(%r15)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2b1e:	48 89 c5             	mov    %rax,%rbp
            if (k == group_of) {
    2b21:	0f 84 53 04 00 00    	je     2f7a <main+0x98a>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b27:	e8 74 f8 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b2c:	be 08 00 00 00       	mov    $0x8,%esi
    2b31:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b36:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b3b:	e8 60 f8 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2b40:	be 80 01 00 00       	mov    $0x180,%esi
    2b45:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b4a:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    2b4f:	e8 4c f8 ff ff       	call   23a0 <calloc@plt>
                mailboxes[b].other = abs((x) % mailboxes_needed);
    2b54:	44 8b 5c 24 48       	mov    0x48(%rsp),%r11d
    2b59:	8b 0c 24             	mov    (%rsp),%ecx
              mailboxes[b].kind = MAILBOX_FRIEND;
    2b5c:	c7 45 70 01 00 00 00 	movl   $0x1,0x70(%rbp)
              struct Data *data = calloc(2, sizeof(struct Data));
    2b63:	49 89 c7             	mov    %rax,%r15
              mailboxes[b].lower = &data[0];
    2b66:	48 89 45 50          	mov    %rax,0x50(%rbp)
              mailboxes[b].higher = &data[1];
    2b6a:	48 8d 80 80 01 00 00 	lea    0x180(%rax),%rax
    2b71:	ba 02 00 00 00       	mov    $0x2,%edx
                mailboxes[b].other = abs((x) % mailboxes_needed);
    2b76:	45 85 db             	test   %r11d,%r11d
    2b79:	0f 45 4c 24 40       	cmovne 0x40(%rsp),%ecx
              mailboxes[b].higher = &data[1];
    2b7e:	48 89 45 58          	mov    %rax,0x58(%rbp)
    2b82:	48 8d 35 87 4b 00 00 	lea    0x4b87(%rip),%rsi        # 7710 <_IO_stdin_used+0x710>
    2b89:	bf 01 00 00 00       	mov    $0x1,%edi
    2b8e:	31 c0                	xor    %eax,%eax
    2b90:	89 4d 74             	mov    %ecx,0x74(%rbp)
    2b93:	89 4c 24 38          	mov    %ecx,0x38(%rsp)
    2b97:	e8 b4 f8 ff ff       	call   2450 <__printf_chk@plt>
              data[0].messages = messages;
    2b9c:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
              data[1].messages = messages2;
    2ba1:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ba6:	be 08 00 00 00       	mov    $0x8,%esi
              data[0].messages_count = 0;
    2bab:	66 0f 6f 1d 3d 50 00 00 	movdqa 0x503d(%rip),%xmm3        # 7bf0 <_IO_stdin_used+0xbf0>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2bb3:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages = messages;
    2bb8:	4d 89 17             	mov    %r10,(%r15)
              data[1].messages = messages2;
    2bbb:	4d 89 8f 80 01 00 00 	mov    %r9,0x180(%r15)
              data[0].messages_count = 0;
    2bc2:	41 0f 29 9f 80 00 00 00 	movaps %xmm3,0x80(%r15)
              data[1].messages_count = 0;
    2bca:	41 0f 29 9f 00 02 00 00 	movaps %xmm3,0x200(%r15)
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2bd2:	e8 c9 f7 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2bd7:	be 08 00 00 00       	mov    $0x8,%esi
    2bdc:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2be1:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2be6:	e8 b5 f7 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2beb:	be 80 01 00 00       	mov    $0x180,%esi
    2bf0:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2bf5:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    2bfa:	e8 a1 f7 ff ff       	call   23a0 <calloc@plt>
    2bff:	8b 4c 24 38          	mov    0x38(%rsp),%ecx
    2c03:	ba 03 00 00 00       	mov    $0x3,%edx
              mailboxes[b].kind = MAILBOX_FRIEND;
    2c08:	c7 85 98 00 00 00 01 00 00 00 	movl   $0x1,0x98(%rbp)
              struct Data *data = calloc(2, sizeof(struct Data));
    2c12:	49 89 c7             	mov    %rax,%r15
              mailboxes[b].lower = &data[0];
    2c15:	48 89 45 78          	mov    %rax,0x78(%rbp)
    2c19:	bf 01 00 00 00       	mov    $0x1,%edi
              mailboxes[b].higher = &data[1];
    2c1e:	48 8d 80 80 01 00 00 	lea    0x180(%rax),%rax
    2c25:	48 89 85 80 00 00 00 	mov    %rax,0x80(%rbp)
    2c2c:	48 8d 35 dd 4a 00 00 	lea    0x4add(%rip),%rsi        # 7710 <_IO_stdin_used+0x710>
    2c33:	31 c0                	xor    %eax,%eax
    2c35:	89 8d 9c 00 00 00    	mov    %ecx,0x9c(%rbp)
    2c3b:	e8 10 f8 ff ff       	call   2450 <__printf_chk@plt>
              data[0].messages = messages;
    2c40:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
              data[1].messages = messages2;
    2c45:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
              data[0].messages_count = 0;
    2c4a:	66 0f 6f 2d 9e 4f 00 00 	movdqa 0x4f9e(%rip),%xmm5        # 7bf0 <_IO_stdin_used+0xbf0>
              data[0].messages = messages;
    2c52:	4d 89 17             	mov    %r10,(%r15)
              data[1].messages = messages2;
    2c55:	4d 89 8f 80 01 00 00 	mov    %r9,0x180(%r15)
              data[0].messages_count = 0;
    2c5c:	41 0f 29 af 80 00 00 00 	movaps %xmm5,0x80(%r15)
              data[1].messages_count = 0;
    2c64:	41 0f 29 af 00 02 00 00 	movaps %xmm5,0x200(%r15)
                mailboxes[b].other = abs((x) % mailboxes_needed);
    2c6c:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    2c71:	45 31 ff             	xor    %r15d,%r15d
    2c74:	44 89 6c 24 30       	mov    %r13d,0x30(%rsp)
            int group_of = b / threads_per_group;
    2c79:	44 89 f8             	mov    %r15d,%eax
    2c7c:	d1 f8                	sar    %eax
            if (k == group_of) {
    2c7e:	41 39 c4             	cmp    %eax,%r12d
    2c81:	0f 84 93 00 00 00    	je     2d1a <main+0x72a>
    2c87:	44 89 fa             	mov    %r15d,%edx
    2c8a:	48 8d 35 0b 47 00 00 	lea    0x470b(%rip),%rsi        # 739c <_IO_stdin_used+0x39c>
    2c91:	bf 01 00 00 00       	mov    $0x1,%edi
    2c96:	31 c0                	xor    %eax,%eax
    2c98:	e8 b3 f7 ff ff       	call   2450 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2c9d:	be 08 00 00 00       	mov    $0x8,%esi
    2ca2:	bf 01 00 00 00       	mov    $0x1,%edi
    2ca7:	e8 f4 f6 ff ff       	call   23a0 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2cac:	be 08 00 00 00       	mov    $0x8,%esi
    2cb1:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2cb6:	49 89 c5             	mov    %rax,%r13
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2cb9:	e8 e2 f6 ff ff       	call   23a0 <calloc@plt>
            struct Data *data = calloc(2, sizeof(struct Data));
    2cbe:	be 80 01 00 00       	mov    $0x180,%esi
    2cc3:	bf 02 00 00 00       	mov    $0x2,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2cc8:	48 89 c3             	mov    %rax,%rbx
            struct Data *data = calloc(2, sizeof(struct Data));
    2ccb:	e8 d0 f6 ff ff       	call   23a0 <calloc@plt>
            data[0].messages_count = 0;
    2cd0:	66 0f 6f 05 18 4f 00 00 	movdqa 0x4f18(%rip),%xmm0        # 7bf0 <_IO_stdin_used+0xbf0>
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2cd8:	c7 45 20 02 00 00 00 	movl   $0x2,0x20(%rbp)
            mailboxes[b].higher = &data[1];
    2cdf:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
            mailboxes[b].lower = &data[0];
    2ce6:	48 89 45 00          	mov    %rax,0x0(%rbp)
            mailboxes[b].higher = &data[1];
    2cea:	48 89 75 08          	mov    %rsi,0x8(%rbp)
            data[0].available = 0;
    2cee:	c7 80 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rax)
            data[0].messages = messages;
    2cf8:	4c 89 28             	mov    %r13,(%rax)
            data[1].messages = messages2;
    2cfb:	48 89 98 80 01 00 00 	mov    %rbx,0x180(%rax)
            data[1].available = 0;
    2d02:	c7 80 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rax)
            data[0].messages_count = 0;
    2d0c:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
            data[1].messages_count = 0;
    2d13:	0f 29 80 00 02 00 00 	movaps %xmm0,0x200(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d1a:	41 83 c7 01          	add    $0x1,%r15d
    2d1e:	48 83 c5 28          	add    $0x28,%rbp
    2d22:	41 83 ff 04          	cmp    $0x4,%r15d
    2d26:	0f 85 4d ff ff ff    	jne    2c79 <main+0x689>
          char *message = malloc(sizeof(char) * 256);
    2d2c:	be 01 00 00 00       	mov    $0x1,%esi
    2d31:	bf 00 01 00 00       	mov    $0x100,%edi
    2d36:	44 8b 6c 24 30       	mov    0x30(%rsp),%r13d
    2d3b:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    2d40:	e8 5b f6 ff ff       	call   23a0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2d45:	bf 18 00 00 00       	mov    $0x18,%edi
          char *message = malloc(sizeof(char) * 256);
    2d4a:	48 89 c5             	mov    %rax,%rbp
          struct Message *messaged = malloc(sizeof(struct Message));
    2d4d:	e8 be f6 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2d52:	44 8b 04 24          	mov    (%rsp),%r8d
    2d56:	48 89 ef             	mov    %rbp,%rdi
    2d59:	45 89 e9             	mov    %r13d,%r9d
    2d5c:	ba 00 01 00 00       	mov    $0x100,%edx
    2d61:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    2d66:	be 01 00 00 00       	mov    $0x1,%esi
    2d6b:	31 c0                	xor    %eax,%eax
    2d6d:	48 8d 0d c4 49 00 00 	lea    0x49c4(%rip),%rcx        # 7738 <_IO_stdin_used+0x738>
    2d74:	e8 a7 f7 ff ff       	call   2520 <__sprintf_chk@plt>
          messaged->message = message;
    2d79:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
          messaged->task_index = y;
    2d7e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2d83:	be 20 00 00 00       	mov    $0x20,%esi
    2d88:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->task_index = y;
    2d8d:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2d91:	49 63 46 08          	movslq 0x8(%r14),%rax
          messaged->message = message;
    2d95:	49 89 2a             	mov    %rbp,(%r10)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2d98:	49 8b 6e 38          	mov    0x38(%r14),%rbp
          messaged->thread_index = thread_data[x].real_thread_index;
    2d9c:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2da0:	41 8d 45 01          	lea    0x1(%r13),%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2da4:	48 01 eb             	add    %rbp,%rbx
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2da7:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2daa:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2db0:	89 83 90 01 00 00    	mov    %eax,0x190(%rbx)
          thread_data[x].tasks[y].message = messaged;
    2db6:	4c 89 93 88 01 00 00 	mov    %r10,0x188(%rbx)
          thread_data[x].tasks[y].sending = 1;
    2dbd:	c7 83 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rbx)
          thread_data[x].tasks[y].snapshot_count = 99;
    2dc7:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2dd2:	e8 c9 f5 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    2dd7:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2de2:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2de9:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    2dee:	48 8b 00             	mov    (%rax),%rax
    2df1:	8b 50 04             	mov    0x4(%rax),%edx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2df4:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2dfb:	89 93 30 01 00 00    	mov    %edx,0x130(%rbx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2e01:	4c 39 f0             	cmp    %r14,%rax
    2e04:	0f 85 2b 0e 00 00    	jne    3c35 <main+0x1645>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2e0a:	66 0f 6f 15 ee 4d 00 00 	movdqa 0x4dee(%rip),%xmm2        # 7c00 <_IO_stdin_used+0xc00>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2e12:	44 89 6b 04          	mov    %r13d,0x4(%rbx)
          thread_data[x].tasks[y].available = 1;
    2e16:	48 8b 05 fb 4d 00 00 	mov    0x4dfb(%rip),%rax        # 7c18 <_IO_stdin_used+0xc18>
          thread_data[x].tasks[y].arrived = 0;
    2e1d:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
          thread_data[x].tasks[y].worker_count = thread_count;
    2e27:	c7 83 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rbx)
          thread_data[x].tasks[y].available = 1;
    2e31:	48 89 83 44 01 00 00 	mov    %rax,0x144(%rbx)
          thread_data[x].tasks[y].thread_count = 2;
    2e38:	0f 11 93 34 01 00 00 	movups %xmm2,0x134(%rbx)
          if (y == barrier_count - 1) {
    2e3f:	41 83 fd 01          	cmp    $0x1,%r13d
    2e43:	0f 84 22 01 00 00    	je     2f6b <main+0x97b>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2e49:	45 85 ed             	test   %r13d,%r13d
    2e4c:	0f 84 00 01 00 00    	je     2f52 <main+0x962>
               thread_data[x].tasks[y].run = barriered_work; 
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2e52:	bf 01 00 00 00       	mov    $0x1,%edi
               thread_data[x].tasks[y].run = barriered_work; 
    2e57:	48 8d 05 62 32 00 00 	lea    0x3262(%rip),%rax        # 60c0 <barriered_work>
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2e5e:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    2e63:	4c 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%r15
    2e6b:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        thread_data[x].buffers_count = buffers_per_thread;
    2e72:	41 c7 86 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r14)
               thread_data[x].tasks[y].run = barriered_work; 
    2e7d:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    2e82:	8b ac 24 88 00 00 00 	mov    0x88(%rsp),%ebp
        thread_data[x].buffers_count = buffers_per_thread;
    2e89:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2e8e:	e8 0d f5 ff ff       	call   23a0 <calloc@plt>
    2e93:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2e98:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
    2e9d:	66 0f 6f 7c 24 60    	movdqa 0x60(%rsp),%xmm7
    for (int d = 0 ; d < threads_per_group ; d++) {
    2ea3:	8b 7c 24 70          	mov    0x70(%rsp),%edi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2ea7:	4c 89 38             	mov    %r15,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2eaa:	49 83 c7 10          	add    $0x10,%r15
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2eae:	49 89 41 50          	mov    %rax,0x50(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2eb2:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    2eb7:	49 81 c1 c0 00 00 00 	add    $0xc0,%r9
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2ebe:	83 44 24 50 01       	addl   $0x1,0x50(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2ec3:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2ec6:	0f 11 ba 18 05 00 00 	movups %xmm7,0x518(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    2ecd:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2ed7:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2ede:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    2ee8:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2ef2:	41 8b 81 44 ff ff ff 	mov    -0xbc(%r9),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2ef9:	c7 82 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2f03:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
    2f09:	48 8b 05 08 4d 00 00 	mov    0x4d08(%rip),%rax        # 7c18 <_IO_stdin_used+0xc18>
    2f10:	48 89 82 44 05 00 00 	mov    %rax,0x544(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2f17:	39 3c 24             	cmp    %edi,(%rsp)
    2f1a:	0f 85 b9 f9 ff ff    	jne    28d9 <main+0x2e9>
    2f20:	89 f8                	mov    %edi,%eax
    2f22:	48 8b 7c 24 78       	mov    0x78(%rsp),%rdi
    2f27:	48 8b 9c 24 98 00 00 00 	mov    0x98(%rsp),%rbx
  for (int k = 0 ; k < group_count ; k++) {
    2f2f:	89 e9                	mov    %ebp,%ecx
    2f31:	83 c0 02             	add    $0x2,%eax
    2f34:	48 83 c7 18          	add    $0x18,%rdi
    2f38:	48 83 7c 24 08 00    	cmpq   $0x0,0x8(%rsp)
    2f3e:	0f 85 a9 01 00 00    	jne    30ed <main+0xafd>
    2f44:	48 c7 44 24 08 01 00 00 00 	movq   $0x1,0x8(%rsp)
    2f4d:	e9 37 f9 ff ff       	jmp    2889 <main+0x299>
    2f52:	48 8d 05 a7 34 00 00 	lea    0x34a7(%rip),%rax        # 6400 <barriered_work_ingest_andwork>
    2f59:	41 bd 01 00 00 00    	mov    $0x1,%r13d
            thread_data[x].tasks[y].run = barriered_work; 
    2f5f:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2f66:	e9 6b fb ff ff       	jmp    2ad6 <main+0x4e6>
    2f6b:	48 8d 05 4e 31 00 00 	lea    0x314e(%rip),%rax        # 60c0 <barriered_work>
    2f72:	41 bd 02 00 00 00    	mov    $0x2,%r13d
    2f78:	eb e5                	jmp    2f5f <main+0x96f>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f7a:	e8 21 f4 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f7f:	be 08 00 00 00       	mov    $0x8,%esi
    2f84:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f89:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f8e:	e8 0d f4 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2f93:	be 80 01 00 00       	mov    $0x180,%esi
    2f98:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f9d:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    2fa2:	e8 f9 f3 ff ff       	call   23a0 <calloc@plt>
                mailboxes[b].other = abs((x) % mailboxes_needed);
    2fa7:	8b 0c 24             	mov    (%rsp),%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2faa:	bf 01 00 00 00       	mov    $0x1,%edi
              mailboxes[b].kind = MAILBOX_FRIEND;
    2faf:	c7 45 20 01 00 00 00 	movl   $0x1,0x20(%rbp)
              struct Data *data = calloc(2, sizeof(struct Data));
    2fb6:	49 89 c7             	mov    %rax,%r15
              mailboxes[b].lower = &data[0];
    2fb9:	48 89 45 00          	mov    %rax,0x0(%rbp)
              mailboxes[b].higher = &data[1];
    2fbd:	48 8d 80 80 01 00 00 	lea    0x180(%rax),%rax
    2fc4:	48 8d 35 45 47 00 00 	lea    0x4745(%rip),%rsi        # 7710 <_IO_stdin_used+0x710>
    2fcb:	48 89 45 08          	mov    %rax,0x8(%rbp)
                mailboxes[b].other = abs((x) % mailboxes_needed);
    2fcf:	8b 44 24 48          	mov    0x48(%rsp),%eax
    2fd3:	85 c0                	test   %eax,%eax
    2fd5:	0f 45 4c 24 40       	cmovne 0x40(%rsp),%ecx
    2fda:	31 d2                	xor    %edx,%edx
    2fdc:	31 c0                	xor    %eax,%eax
    2fde:	89 4d 24             	mov    %ecx,0x24(%rbp)
    2fe1:	89 4c 24 38          	mov    %ecx,0x38(%rsp)
    2fe5:	e8 66 f4 ff ff       	call   2450 <__printf_chk@plt>
              data[0].messages = messages;
    2fea:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
              data[1].messages = messages2;
    2fef:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ff4:	be 08 00 00 00       	mov    $0x8,%esi
              data[0].messages_count = 0;
    2ff9:	66 0f 6f 2d ef 4b 00 00 	movdqa 0x4bef(%rip),%xmm5        # 7bf0 <_IO_stdin_used+0xbf0>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3001:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages = messages;
    3006:	4d 89 17             	mov    %r10,(%r15)
              data[1].messages = messages2;
    3009:	4d 89 8f 80 01 00 00 	mov    %r9,0x180(%r15)
              data[0].messages_count = 0;
    3010:	41 0f 29 af 80 00 00 00 	movaps %xmm5,0x80(%r15)
              data[1].messages_count = 0;
    3018:	41 0f 29 af 00 02 00 00 	movaps %xmm5,0x200(%r15)
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3020:	e8 7b f3 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3025:	be 08 00 00 00       	mov    $0x8,%esi
    302a:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    302f:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3034:	e8 67 f3 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    3039:	be 80 01 00 00       	mov    $0x180,%esi
    303e:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3043:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    3048:	e8 53 f3 ff ff       	call   23a0 <calloc@plt>
    304d:	8b 4c 24 38          	mov    0x38(%rsp),%ecx
              mailboxes[b].kind = MAILBOX_FRIEND;
    3051:	c7 45 48 01 00 00 00 	movl   $0x1,0x48(%rbp)
    3058:	ba 01 00 00 00       	mov    $0x1,%edx
              struct Data *data = calloc(2, sizeof(struct Data));
    305d:	49 89 c7             	mov    %rax,%r15
              mailboxes[b].lower = &data[0];
    3060:	48 89 45 28          	mov    %rax,0x28(%rbp)
    3064:	bf 01 00 00 00       	mov    $0x1,%edi
              mailboxes[b].higher = &data[1];
    3069:	48 8d 80 80 01 00 00 	lea    0x180(%rax),%rax
    3070:	48 89 45 30          	mov    %rax,0x30(%rbp)
    3074:	48 8d 35 95 46 00 00 	lea    0x4695(%rip),%rsi        # 7710 <_IO_stdin_used+0x710>
    307b:	31 c0                	xor    %eax,%eax
    307d:	89 4d 4c             	mov    %ecx,0x4c(%rbp)
    3080:	e8 cb f3 ff ff       	call   2450 <__printf_chk@plt>
              data[0].messages = messages;
    3085:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
              data[1].messages = messages2;
    308a:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
              data[0].messages_count = 0;
    308f:	66 0f 6f 3d 59 4b 00 00 	movdqa 0x4b59(%rip),%xmm7        # 7bf0 <_IO_stdin_used+0xbf0>
              data[0].messages = messages;
    3097:	4d 89 17             	mov    %r10,(%r15)
              data[1].messages = messages2;
    309a:	4d 89 8f 80 01 00 00 	mov    %r9,0x180(%r15)
              data[0].messages_count = 0;
    30a1:	41 0f 29 bf 80 00 00 00 	movaps %xmm7,0x80(%r15)
              data[1].messages_count = 0;
    30a9:	41 0f 29 bf 00 02 00 00 	movaps %xmm7,0x200(%r15)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    30b1:	e9 b6 fb ff ff       	jmp    2c6c <main+0x67c>
        other = (x + 1) % total_threads;
    30b6:	8b 44 24 40          	mov    0x40(%rsp),%eax
        my_thread_data[1] = &thread_data[other]; 
    30ba:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    30bf:	45 31 c0             	xor    %r8d,%r8d
        other = (x + 1) % total_threads;
    30c2:	83 c0 02             	add    $0x2,%eax
        my_thread_data[1] = &thread_data[other]; 
    30c5:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
        other = (x + 1) % total_threads;
    30c9:	48 89 c1             	mov    %rax,%rcx
        my_thread_data[1] = &thread_data[other]; 
    30cc:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    30d1:	48 c1 e2 06          	shl    $0x6,%rdx
    30d5:	48 01 c2             	add    %rax,%rdx
        my_thread_data[0] = &thread_data[x]; 
    30d8:	4c 89 c8             	mov    %r9,%rax
    30db:	e9 8d f8 ff ff       	jmp    296d <main+0x37d>
            CPU_SET(j, sendercpu);
    30e0:	49 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%r13)
          for (int j = 0 ; j < cores ; j++) {
    30e8:	e9 14 f9 ff ff       	jmp    2a01 <main+0x411>
    30ed:	48 8d 3d c6 42 00 00 	lea    0x42c6(%rip),%rdi        # 73ba <_IO_stdin_used+0x3ba>
    30f4:	45 31 ed             	xor    %r13d,%r13d
    30f7:	4c 8d 25 fb 42 00 00 	lea    0x42fb(%rip),%r12        # 73f9 <_IO_stdin_used+0x3f9>
    30fe:	e8 ed f1 ff ff       	call   22f0 <puts@plt>
    3103:	44 89 ea             	mov    %r13d,%edx
    3106:	48 8d 35 c5 42 00 00 	lea    0x42c5(%rip),%rsi        # 73d2 <_IO_stdin_used+0x3d2>
    310d:	31 c0                	xor    %eax,%eax
    310f:	4c 89 ed             	mov    %r13,%rbp
    3112:	bf 01 00 00 00       	mov    $0x1,%edi
    3117:	48 f7 dd             	neg    %rbp
    311a:	47 8d 74 2d 00       	lea    0x0(%r13,%r13,1),%r14d
  }
  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    311f:	31 db                	xor    %ebx,%ebx
    3121:	e8 2a f3 ff ff       	call   2450 <__printf_chk@plt>
    3126:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    312b:	81 e5 80 01 00 00    	and    $0x180,%ebp
    3131:	45 89 f7             	mov    %r14d,%r15d
    3134:	48 01 c5             	add    %rax,%rbp
      int x = (k * threads_per_group) + d;
    3137:	42 8d 0c 3b          	lea    (%rbx,%r15,1),%ecx
    313b:	89 da                	mov    %ebx,%edx
    313d:	48 8d 35 98 42 00 00 	lea    0x4298(%rip),%rsi        # 73dc <_IO_stdin_used+0x3dc>
    3144:	31 c0                	xor    %eax,%eax
    3146:	bf 01 00 00 00       	mov    $0x1,%edi
    314b:	45 31 f6             	xor    %r14d,%r14d
    314e:	e8 fd f2 ff ff       	call   2450 <__printf_chk@plt>
    3153:	4c 89 2c 24          	mov    %r13,(%rsp)
    3157:	89 5c 24 18          	mov    %ebx,0x18(%rsp)
    315b:	44 89 7c 24 20       	mov    %r15d,0x20(%rsp)
    3160:	44 89 f2             	mov    %r14d,%edx
    3163:	48 8d 35 84 42 00 00 	lea    0x4284(%rip),%rsi        # 73ee <_IO_stdin_used+0x3ee>
    316a:	31 c0                	xor    %eax,%eax
    316c:	4c 89 f3             	mov    %r14,%rbx
    316f:	bf 01 00 00 00       	mov    $0x1,%edi
    3174:	48 c1 e3 09          	shl    $0x9,%rbx
    3178:	45 31 ff             	xor    %r15d,%r15d
    317b:	e8 d0 f2 ff ff       	call   2450 <__printf_chk@plt>
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
          char * mailbox_kind = calloc(100, sizeof(char));
    3180:	be 01 00 00 00       	mov    $0x1,%esi
    3185:	bf 64 00 00 00       	mov    $0x64,%edi
    318a:	45 89 fd             	mov    %r15d,%r13d
    318d:	e8 0e f2 ff ff       	call   23a0 <calloc@plt>
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3192:	4b 8d 34 bf          	lea    (%r15,%r15,4),%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
    3196:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3199:	48 8b 45 38          	mov    0x38(%rbp),%rax
    319d:	4c 8b 94 18 70 01 00 00 	mov    0x170(%rax,%rbx,1),%r10
    31a5:	49 8d 34 f2          	lea    (%r10,%rsi,8),%rsi
    31a9:	8b 46 20             	mov    0x20(%rsi),%eax
    31ac:	83 f8 02             	cmp    $0x2,%eax
    31af:	74 4d                	je     31fe <main+0xc0e>
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    31b1:	83 f8 01             	cmp    $0x1,%eax
    31b4:	74 57                	je     320d <main+0xc1d>
    31b6:	44 89 ea             	mov    %r13d,%edx
    31b9:	4c 89 e6             	mov    %r12,%rsi
    31bc:	bf 01 00 00 00       	mov    $0x1,%edi
    31c1:	31 c0                	xor    %eax,%eax
    31c3:	e8 88 f2 ff ff       	call   2450 <__printf_chk@plt>
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    31c8:	49 83 c7 01          	add    $0x1,%r15
    31cc:	49 83 ff 04          	cmp    $0x4,%r15
    31d0:	75 ae                	jne    3180 <main+0xb90>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    31d2:	49 83 c6 01          	add    $0x1,%r14
    31d6:	49 83 fe 03          	cmp    $0x3,%r14
    31da:	75 84                	jne    3160 <main+0xb70>
    for (int d = 0 ; d < threads_per_group ; d++) {
    31dc:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
    31e0:	4c 8b 2c 24          	mov    (%rsp),%r13
    31e4:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
    31eb:	44 8b 7c 24 20       	mov    0x20(%rsp),%r15d
    31f0:	85 db                	test   %ebx,%ebx
    31f2:	75 28                	jne    321c <main+0xc2c>
    31f4:	bb 01 00 00 00       	mov    $0x1,%ebx
    31f9:	e9 39 ff ff ff       	jmp    3137 <main+0xb47>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    31fe:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    3208:	48 89 01             	mov    %rax,(%rcx)
    320b:	eb a9                	jmp    31b6 <main+0xbc6>
    320d:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3213:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    321a:	eb 9a                	jmp    31b6 <main+0xbc6>
  for (int k = 0 ; k < group_count ; k++) {
    321c:	4d 85 ed             	test   %r13,%r13
    321f:	75 0a                	jne    322b <main+0xc3b>
    3221:	4c 8b 6c 24 08       	mov    0x8(%rsp),%r13
    3226:	e9 d8 fe ff ff       	jmp    3103 <main+0xb13>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    322b:	ba 05 00 00 00       	mov    $0x5,%edx
    3230:	bf 01 00 00 00       	mov    $0x1,%edi
    3235:	31 c0                	xor    %eax,%eax
    3237:	41 89 df             	mov    %ebx,%r15d
    323a:	48 8d 35 ca 41 00 00 	lea    0x41ca(%rip),%rsi        # 740b <_IO_stdin_used+0x40b>
    3241:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    3246:	e8 05 f2 ff ff       	call   2450 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    324b:	be 08 00 00 00       	mov    $0x8,%esi
    3250:	bf 02 00 00 00       	mov    $0x2,%edi
    3255:	e8 46 f1 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    325a:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    325f:	be 38 00 00 00       	mov    $0x38,%esi
    3264:	bf 08 00 00 00       	mov    $0x8,%edi
    my_thread_data[0] = &thread_data[x]; 
    3269:	4d 8d ae c0 03 00 00 	lea    0x3c0(%r14),%r13
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3270:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3274:	4d 8d a6 c0 00 00 00 	lea    0xc0(%r14),%r12
    thread_data[x].threads = my_thread_data;
    327b:	49 89 86 d8 03 00 00 	mov    %rax,0x3d8(%r14)
    my_thread_data[0] = &thread_data[x]; 
    3282:	4c 89 28             	mov    %r13,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3285:	49 8b 46 38          	mov    0x38(%r14),%rax
    thread_data[x].thread_count = 2;
    3289:	41 c7 86 e8 03 00 00 02 00 00 00 	movl   $0x2,0x3e8(%r14)
    thread_data[x].thread_index = 0;
    3294:	41 c7 86 c4 03 00 00 00 00 00 00 	movl   $0x0,0x3c4(%r14)
    thread_data[x].task_count = total_barrier_count;
    329f:	41 c7 86 00 04 00 00 03 00 00 00 	movl   $0x3,0x400(%r14)
    thread_data[n].tasks[0].scheduled = 1;
    32aa:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    32b4:	49 8b 86 f8 00 00 00 	mov    0xf8(%r14),%rax
    32bb:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32c5:	e8 d6 f0 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32ca:	be 38 00 00 00       	mov    $0x38,%esi
    32cf:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32d4:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32d8:	e8 c3 f0 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32dd:	be 38 00 00 00       	mov    $0x38,%esi
    32e2:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32e7:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32ea:	e8 b1 f0 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32ef:	be 38 00 00 00       	mov    $0x38,%esi
    32f4:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32f9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    32fe:	e8 9d f0 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3303:	be 08 00 00 00       	mov    $0x8,%esi
    3308:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    330d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3312:	e8 89 f0 ff ff       	call   23a0 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3317:	be 08 00 00 00       	mov    $0x8,%esi
    331c:	bf 08 00 00 00       	mov    $0x8,%edi
  thread_data[timer_threadi].type = TIMER;
    3321:	41 c7 86 0c 03 00 00 00 00 00 00 	movl   $0x0,0x30c(%r14)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    332c:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    332f:	48 8b 05 ea 48 00 00 	mov    0x48ea(%rip),%rax        # 7c20 <_IO_stdin_used+0xc20>
    3336:	49 89 86 40 03 00 00 	mov    %rax,0x340(%r14)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    333d:	e8 5e f0 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    3342:	49 8d 96 80 01 00 00 	lea    0x180(%r14),%rdx
    3349:	4c 89 f7             	mov    %r14,%rdi
    334c:	49 8d 8e 00 03 00 00 	lea    0x300(%r14),%rcx
    3353:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3357:	49 8d 96 40 02 00 00 	lea    0x240(%r14),%rdx
    335e:	48 8d 35 b5 40 00 00 	lea    0x40b5(%rip),%rsi        # 741a <_IO_stdin_used+0x41a>
    3365:	4c 89 30             	mov    %r14,(%rax)
    3368:	4d 8d b6 80 04 00 00 	lea    0x480(%r14),%r14
    336f:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3373:	48 8d 97 40 05 00 00 	lea    0x540(%rdi),%rdx
    337a:	48 89 48 20          	mov    %rcx,0x20(%rax)
    337e:	4c 89 68 28          	mov    %r13,0x28(%rax)
    3382:	4c 89 70 30          	mov    %r14,0x30(%rax)
    3386:	48 89 50 38          	mov    %rdx,0x38(%rax)
    338a:	ba 04 00 00 00       	mov    $0x4,%edx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    338f:	48 89 87 18 03 00 00 	mov    %rax,0x318(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    3396:	4c 89 60 08          	mov    %r12,0x8(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    339a:	48 8b 05 87 48 00 00 	mov    0x4887(%rip),%rax        # 7c28 <_IO_stdin_used+0xc28>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    33a1:	c7 87 30 03 00 00 04 00 00 00 	movl   $0x4,0x330(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    33ab:	48 89 87 28 03 00 00 	mov    %rax,0x328(%rdi)
    33b2:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    33b4:	c7 87 04 03 00 00 00 00 00 00 	movl   $0x0,0x304(%rdi)
    33be:	48 89 7c 24 10       	mov    %rdi,0x10(%rsp)
    33c3:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    33c8:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    33cd:	e8 7e f0 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    33d2:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    33d7:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
    33db:	48 8d 15 1e 0b 00 00 	lea    0xb1e(%rip),%rdx        # 3f00 <timer_thread>
    33e2:	48 8d b5 e0 00 00 00 	lea    0xe0(%rbp),%rsi
    33e9:	e8 82 f0 ff ff       	call   2470 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    33ee:	48 8b 04 24          	mov    (%rsp),%rax
    33f2:	44 89 ff             	mov    %r15d,%edi
    33f5:	45 31 d2             	xor    %r10d,%r10d
    33f8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    33fd:	41 b9 02 00 00 00    	mov    $0x2,%r9d
    3403:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    3408:	48 89 d9             	mov    %rbx,%rcx
    340b:	4c 89 64 24 40       	mov    %r12,0x40(%rsp)
    3410:	49 89 c7             	mov    %rax,%r15
    3413:	89 f8                	mov    %edi,%eax
    3415:	4c 89 6c 24 20       	mov    %r13,0x20(%rsp)
    341a:	45 89 d5             	mov    %r10d,%r13d
    341d:	4c 89 74 24 38       	mov    %r14,0x38(%rsp)
    3422:	45 89 ce             	mov    %r9d,%r14d
    3425:	4c 89 3c 24          	mov    %r15,(%rsp)
    3429:	47 8d 64 2d 00       	lea    0x0(%r13,%r13,1),%r12d
    342e:	48 89 cb             	mov    %rcx,%rbx
    3431:	48 89 d5             	mov    %rdx,%rbp
    3434:	48 89 4c 24 48       	mov    %rcx,0x48(%rsp)
    3439:	48 89 54 24 50       	mov    %rdx,0x50(%rsp)
    343e:	89 44 24 70          	mov    %eax,0x70(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    3442:	c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%rbp)
    3449:	44 89 e2             	mov    %r12d,%edx
    344c:	44 89 e9             	mov    %r13d,%ecx
    344f:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    3451:	c7 45 44 01 00 00 00 	movl   $0x1,0x44(%rbp)
    3458:	48 8d 35 01 43 00 00 	lea    0x4301(%rip),%rsi        # 7760 <_IO_stdin_used+0x760>
    345f:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    3464:	41 83 c4 01          	add    $0x1,%r12d
    3468:	e8 e3 ef ff ff       	call   2450 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    346d:	48 8b 34 24          	mov    (%rsp),%rsi
    3471:	48 89 e9             	mov    %rbp,%rcx
    3474:	48 89 df             	mov    %rbx,%rdi
    3477:	48 8d 15 e2 27 00 00 	lea    0x27e2(%rip),%rdx        # 5c60 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    347e:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
    3485:	48 83 c3 08          	add    $0x8,%rbx
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3489:	e8 e2 ef ff ff       	call   2470 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    348e:	48 8b 55 f0          	mov    -0x10(%rbp),%rdx
    3492:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    3496:	be 08 00 00 00       	mov    $0x8,%esi
    349b:	e8 40 ee ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    34a0:	48 83 04 24 38       	addq   $0x38,(%rsp)
    34a5:	45 39 e6             	cmp    %r12d,%r14d
    34a8:	75 98                	jne    3442 <main+0xe52>
  for (int k = 0 ; k < group_count ; k++) {
    34aa:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    34af:	8b 44 24 70          	mov    0x70(%rsp),%eax
    34b3:	49 83 c7 70          	add    $0x70,%r15
    34b7:	41 83 c6 02          	add    $0x2,%r14d
    34bb:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
    34c0:	48 83 c1 10          	add    $0x10,%rcx
    34c4:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
    34cb:	45 85 ed             	test   %r13d,%r13d
    34ce:	75 08                	jne    34d8 <main+0xee8>
    34d0:	41 89 c5             	mov    %eax,%r13d
    34d3:	e9 4d ff ff ff       	jmp    3425 <main+0xe35>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    34d8:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    34dd:	be d8 00 00 00       	mov    $0xd8,%esi
    34e2:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    34e7:	48 8b 05 42 47 00 00 	mov    0x4742(%rip),%rax        # 7c30 <_IO_stdin_used+0xc30>
    thread_data[x].type = IO;
    34ee:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    34f3:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    34f8:	41 c7 87 cc 03 00 00 02 00 00 00 	movl   $0x2,0x3cc(%r15)
    3503:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    thread_data[x].task_count = 0;
    3508:	49 89 87 00 04 00 00 	mov    %rax,0x400(%r15)
    thread_data[x].type = IO;
    350f:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3514:	4c 89 f5             	mov    %r14,%rbp
    3517:	49 89 de             	mov    %rbx,%r14
    351a:	e8 81 ee ff ff       	call   23a0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    351f:	be 00 08 00 00       	mov    $0x800,%esi
    3524:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3526:	49 89 87 18 04 00 00 	mov    %rax,0x418(%r15)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    352d:	e8 7e ef ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3532:	be 08 00 00 00       	mov    $0x8,%esi
    3537:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    353c:	41 89 87 20 04 00 00 	mov    %eax,0x420(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3543:	e8 58 ee ff ff       	call   23a0 <calloc@plt>
    3548:	ba 05 00 00 00       	mov    $0x5,%edx
    354d:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3552:	41 c7 87 e8 03 00 00 02 00 00 00 	movl   $0x2,0x3e8(%r15)
      my_thread_data[n] = &thread_data[n]; 
    355d:	4c 89 38             	mov    %r15,(%rax)
    3560:	48 8d 35 d1 3e 00 00 	lea    0x3ed1(%rip),%rsi        # 7438 <_IO_stdin_used+0x438>
    thread_data[x].threads = my_thread_data;
    3567:	49 89 87 d8 03 00 00 	mov    %rax,0x3d8(%r15)
      my_thread_data[n] = &thread_data[n]; 
    356e:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3572:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3574:	41 c7 87 c4 03 00 00 05 00 00 00 	movl   $0x5,0x3c4(%r15)
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    357f:	41 bf 06 00 00 00    	mov    $0x6,%r15d
    3585:	e8 c6 ee ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    358a:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    358f:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
    3593:	4c 89 e9             	mov    %r13,%rcx
    3596:	48 8d 15 d3 1e 00 00 	lea    0x1ed3(%rip),%rdx        # 5470 <io_thread>
    359d:	4c 8d 6b 30          	lea    0x30(%rbx),%r13
    35a1:	48 81 c6 18 01 00 00 	add    $0x118,%rsi
    35a8:	e8 c3 ee ff ff       	call   2470 <pthread_create@plt>
    35ad:	ba 06 00 00 00       	mov    $0x6,%edx
    35b2:	48 8d 35 96 3e 00 00 	lea    0x3e96(%rip),%rsi        # 744f <_IO_stdin_used+0x44f>
    35b9:	31 c0                	xor    %eax,%eax
    35bb:	bf 01 00 00 00       	mov    $0x1,%edi
    35c0:	e8 8b ee ff ff       	call   2450 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    35c5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    35ca:	48 8b 9c 24 90 00 00 00 	mov    0x90(%rsp),%rbx
    35d2:	48 05 50 01 00 00    	add    $0x150,%rax
    35d8:	48 89 04 24          	mov    %rax,(%rsp)
    35dc:	44 89 fa             	mov    %r15d,%edx
    35df:	48 8d 35 7f 3e 00 00 	lea    0x3e7f(%rip),%rsi        # 7465 <_IO_stdin_used+0x465>
    35e6:	bf 01 00 00 00       	mov    $0x1,%edi
    35eb:	31 c0                	xor    %eax,%eax
    35ed:	e8 5e ee ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    35f2:	be 08 00 00 00       	mov    $0x8,%esi
    35f7:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    35fc:	48 8b 05 2d 46 00 00 	mov    0x462d(%rip),%rax        # 7c30 <_IO_stdin_used+0xc30>
    thread_data[x].type = EXTERNAL;
    3603:	c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%rbp)
    thread_data[x].task_count = 0;
    360a:	48 89 45 40          	mov    %rax,0x40(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    360e:	e8 8d ed ff ff       	call   23a0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3613:	be 08 00 00 00       	mov    $0x8,%esi
    3618:	bf 02 00 00 00       	mov    $0x2,%edi
	  thread_data[x].buffers_count = 1;
    361d:	c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3627:	48 89 45 50          	mov    %rax,0x50(%rbp)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    362b:	48 89 18             	mov    %rbx,(%rax)
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    362e:	48 83 c3 10          	add    $0x10,%rbx
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3632:	e8 69 ed ff ff       	call   23a0 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    3637:	44 89 7d 04          	mov    %r15d,0x4(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    363b:	48 8b 34 24          	mov    (%rsp),%rsi
    363f:	48 89 e9             	mov    %rbp,%rcx
      my_thread_data[n] = &thread_data[n]; 
    3642:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    thread_data[x].threads = my_thread_data;
    3647:	48 89 45 18          	mov    %rax,0x18(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    364b:	48 8d 15 9e 07 00 00 	lea    0x79e(%rip),%rdx        # 3df0 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3652:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
      my_thread_data[n] = &thread_data[n]; 
    3659:	4c 89 60 08          	mov    %r12,0x8(%rax)
    365d:	48 89 38             	mov    %rdi,(%rax)
    thread_data[x].thread_count = thread_count;
    3660:	48 8b 05 a9 45 00 00 	mov    0x45a9(%rip),%rax        # 7c10 <_IO_stdin_used+0xc10>
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3667:	4c 89 ef             	mov    %r13,%rdi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    366a:	49 83 c5 08          	add    $0x8,%r13
    thread_data[x].thread_count = thread_count;
    366e:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3675:	e8 f6 ed ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    367a:	48 83 04 24 38       	addq   $0x38,(%rsp)
    367f:	41 83 ff 06          	cmp    $0x6,%r15d
    3683:	75 0b                	jne    3690 <main+0x10a0>
    3685:	41 bf 07 00 00 00    	mov    $0x7,%r15d
    368b:	e9 4c ff ff ff       	jmp    35dc <main+0xfec>
    3690:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3695:	4c 89 f3             	mov    %r14,%rbx
    3698:	48 8d 2d e3 3d 00 00 	lea    0x3de3(%rip),%rbp        # 7482 <_IO_stdin_used+0x482>
    369f:	4c 8d 68 04          	lea    0x4(%rax),%r13
    36a3:	4c 8d a0 04 06 00 00 	lea    0x604(%rax),%r12
    36aa:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    36ae:	41 8b 55 00          	mov    0x0(%r13),%edx
    36b2:	48 89 ee             	mov    %rbp,%rsi
    36b5:	bf 01 00 00 00       	mov    $0x1,%edi
    36ba:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    36bc:	49 81 c5 c0 00 00 00 	add    $0xc0,%r13
    36c3:	e8 88 ed ff ff       	call   2450 <__printf_chk@plt>
    36c8:	4d 39 ec             	cmp    %r13,%r12
    36cb:	75 dd                	jne    36aa <main+0x10ba>
    36cd:	48 8d 3d c1 3d 00 00 	lea    0x3dc1(%rip),%rdi        # 7495 <_IO_stdin_used+0x495>
    36d4:	45 31 ed             	xor    %r13d,%r13d
    36d7:	4c 8d a4 24 a0 00 00 00 	lea    0xa0(%rsp),%r12
    36df:	e8 0c ec ff ff       	call   22f0 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    36e4:	48 8d 2d c8 3d 00 00 	lea    0x3dc8(%rip),%rbp        # 74b3 <_IO_stdin_used+0x4b3>
    void * result; 
    pthread_join(thread[x], &result);
    36eb:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    36ef:	4c 89 e6             	mov    %r12,%rsi
    36f2:	e8 f9 ed ff ff       	call   24f0 <pthread_join@plt>
    36f7:	44 89 ea             	mov    %r13d,%edx
    36fa:	48 89 ee             	mov    %rbp,%rsi
    36fd:	bf 01 00 00 00       	mov    $0x1,%edi
    3702:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3704:	49 83 c5 01          	add    $0x1,%r13
    3708:	e8 43 ed ff ff       	call   2450 <__printf_chk@plt>
    370d:	49 83 fd 08          	cmp    $0x8,%r13
    3711:	75 d8                	jne    36eb <main+0x10fb>
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
    3713:	45 31 c9             	xor    %r9d,%r9d
  long sents = 0;
    3716:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
  long received = 0;
    371e:	45 31 d2             	xor    %r10d,%r10d
    3721:	31 ed                	xor    %ebp,%ebp
    3723:	4c 89 4c 24 20       	mov    %r9,0x20(%rsp)
  long ingests = 0;
    3728:	45 31 db             	xor    %r11d,%r11d
  long total = 0;
    372b:	31 f6                	xor    %esi,%esi
    372d:	4c 89 d3             	mov    %r10,%rbx
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3730:	49 bc db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r12
    for (int d = 0 ; d < threads_per_group ; d++) {
    373a:	48 89 e8             	mov    %rbp,%rax
    373d:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    3742:	48 89 6c 24 40       	mov    %rbp,0x40(%rsp)
    3747:	49 89 df             	mov    %rbx,%r15
    374a:	48 f7 d8             	neg    %rax
    374d:	48 89 f3             	mov    %rsi,%rbx
    3750:	49 89 c6             	mov    %rax,%r14
    3753:	83 e0 30             	and    $0x30,%eax
    3756:	41 81 e6 80 01 00 00 	and    $0x180,%r14d
    375d:	49 01 fe             	add    %rdi,%r14
    3760:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
    3765:	48 01 f8             	add    %rdi,%rax
    3768:	8d 7c 2d 00          	lea    0x0(%rbp,%rbp,1),%edi
    376c:	48 8b 2c 24          	mov    (%rsp),%rbp
    3770:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    3775:	8d 47 ff             	lea    -0x1(%rdi),%eax
    3778:	89 44 24 28          	mov    %eax,0x28(%rsp)
    377c:	89 7c 24 48          	mov    %edi,0x48(%rsp)
    3780:	8b 7c 24 28          	mov    0x28(%rsp),%edi
    3784:	4c 89 1c 24          	mov    %r11,(%rsp)
      int x = (k * threads_per_group) + d;
    3788:	89 f8                	mov    %edi,%eax
    378a:	89 7c 24 38          	mov    %edi,0x38(%rsp)
    378e:	83 c7 01             	add    $0x1,%edi
    3791:	89 fe                	mov    %edi,%esi
    3793:	89 7c 24 28          	mov    %edi,0x28(%rsp)
        other = abs(x - 1) % total_threads;
    3797:	89 c7                	mov    %eax,%edi
    3799:	8d 40 02             	lea    0x2(%rax),%eax
    379c:	83 e6 01             	and    $0x1,%esi
    379f:	0f 45 c7             	cmovne %edi,%eax
    37a2:	bf 0a 00 00 00       	mov    $0xa,%edi
    37a7:	4c 63 e8             	movslq %eax,%r13
    37aa:	e8 21 eb ff ff       	call   22d0 <putchar@plt>
    37af:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    37b4:	bf 01 00 00 00       	mov    $0x1,%edi
    37b9:	48 8d 35 07 3d 00 00 	lea    0x3d07(%rip),%rsi        # 74c7 <_IO_stdin_used+0x4c7>
    37c0:	48 8b 10             	mov    (%rax),%rdx
    37c3:	31 c0                	xor    %eax,%eax
    37c5:	e8 86 ec ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    37ca:	41 8b 56 40          	mov    0x40(%r14),%edx
    37ce:	4c 8b 1c 24          	mov    (%rsp),%r11
    37d2:	85 d2                	test   %edx,%edx
    37d4:	0f 8e 54 04 00 00    	jle    3c2e <main+0x163e>
    37da:	48 63 f2             	movslq %edx,%rsi
    37dd:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    37e1:	31 d2                	xor    %edx,%edx
    37e3:	48 c1 e6 09          	shl    $0x9,%rsi
    37e7:	48 01 c6             	add    %rax,%rsi
    37ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    37f0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    37f7:	48 05 00 02 00 00    	add    $0x200,%rax
    37fd:	48 39 f0             	cmp    %rsi,%rax
    3800:	75 ee                	jne    37f0 <main+0x1200>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3802:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    3807:	4b 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%rax
    380c:	48 c1 e0 06          	shl    $0x6,%rax
    3810:	48 01 f8             	add    %rdi,%rax
    3813:	48 63 70 40          	movslq 0x40(%rax),%rsi
    3817:	85 f6                	test   %esi,%esi
    3819:	7e 27                	jle    3842 <main+0x1252>
    381b:	48 8b 40 38          	mov    0x38(%rax),%rax
    381f:	48 c1 e6 09          	shl    $0x9,%rsi
    3823:	48 01 c6             	add    %rax,%rsi
    3826:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3830:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3837:	48 05 00 02 00 00    	add    $0x200,%rax
    383d:	48 39 f0             	cmp    %rsi,%rax
    3840:	75 ee                	jne    3830 <main+0x1240>
    3842:	48 8d 35 93 3c 00 00 	lea    0x3c93(%rip),%rsi        # 74dc <_IO_stdin_used+0x4dc>
    3849:	bf 01 00 00 00       	mov    $0x1,%edi
    384e:	31 c0                	xor    %eax,%eax
    3850:	4c 89 1c 24          	mov    %r11,(%rsp)
    3854:	e8 f7 eb ff ff       	call   2450 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3859:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    385e:	bf 01 00 00 00       	mov    $0x1,%edi
    3863:	48 8b 30             	mov    (%rax),%rsi
    3866:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3870:	48 f7 ee             	imul   %rsi
    3873:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3877:	31 c0                	xor    %eax,%eax
    3879:	48 d1 fa             	sar    %rdx
    387c:	48 29 f2             	sub    %rsi,%rdx
    387f:	48 8d 35 0a 3f 00 00 	lea    0x3f0a(%rip),%rsi        # 7790 <_IO_stdin_used+0x790>
    3886:	e8 c5 eb ff ff       	call   2450 <__printf_chk@plt>
    388b:	bf 0a 00 00 00       	mov    $0xa,%edi
    3890:	e8 3b ea ff ff       	call   22d0 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3895:	41 8b 56 40          	mov    0x40(%r14),%edx
    3899:	4c 8b 1c 24          	mov    (%rsp),%r11
    389d:	85 d2                	test   %edx,%edx
    389f:	7e 53                	jle    38f4 <main+0x1304>
    38a1:	49 8b 46 38          	mov    0x38(%r14),%rax
    38a5:	48 63 f2             	movslq %edx,%rsi
    38a8:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    38ad:	48 c1 e6 09          	shl    $0x9,%rsi
    38b1:	48 01 c6             	add    %rax,%rsi
    38b4:	0f 1f 40 00          	nopl   0x0(%rax)
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    38b8:	48 8b 90 70 01 00 00 	mov    0x170(%rax),%rdx
        total += thread_data[x].tasks[n].n;
    38bf:	48 03 98 08 01 00 00 	add    0x108(%rax),%rbx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    38c6:	48 05 00 02 00 00    	add    $0x200,%rax
        ingests += thread_data[x].tasks[n].ingest_count;
    38cc:	4c 03 98 68 ff ff ff 	add    -0x98(%rax),%r11
        sends += thread_data[x].tasks[n].sends;
    38d3:	48 03 88 78 ff ff ff 	add    -0x88(%rax),%rcx
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    38da:	48 03 6a 10          	add    0x10(%rdx),%rbp
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    38de:	4c 03 7a 18          	add    0x18(%rdx),%r15
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    38e2:	48 03 6a 38          	add    0x38(%rdx),%rbp
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    38e6:	4c 03 7a 40          	add    0x40(%rdx),%r15
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    38ea:	48 39 f0             	cmp    %rsi,%rax
    38ed:	75 c9                	jne    38b8 <main+0x12c8>
    38ef:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    38f4:	45 31 ed             	xor    %r13d,%r13d
    38f7:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    38ff:	0f 8e 87 00 00 00    	jle    398c <main+0x139c>
    3905:	4c 89 1c 24          	mov    %r11,(%rsp)
    3909:	48 89 df             	mov    %rbx,%rdi
    390c:	4c 89 f0             	mov    %r14,%rax
    390f:	4c 89 eb             	mov    %r13,%rbx
    3912:	49 89 ee             	mov    %rbp,%r14
    3915:	49 89 fd             	mov    %rdi,%r13
    3918:	48 89 c5             	mov    %rax,%rbp
    391b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3920:	48 8b 85 90 00 00 00 	mov    0x90(%rbp),%rax
    3927:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    392b:	48 83 ec 08          	sub    $0x8,%rsp
    392f:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3934:	48 83 c3 01          	add    $0x1,%rbx
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3938:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    393c:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3940:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3944:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3947:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    394b:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    394e:	49 f7 e4             	mul    %r12
    3951:	8b 49 20             	mov    0x20(%rcx),%ecx
    3954:	56                   	push   %rsi
    3955:	31 c0                	xor    %eax,%eax
    3957:	48 8d 35 52 3e 00 00 	lea    0x3e52(%rip),%rsi        # 77b0 <_IO_stdin_used+0x7b0>
    395e:	48 c1 ea 12          	shr    $0x12,%rdx
    3962:	49 89 d1             	mov    %rdx,%r9
    3965:	ba 02 00 00 00       	mov    $0x2,%edx
    396a:	e8 e1 ea ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    396f:	41 58                	pop    %r8
    3971:	41 59                	pop    %r9
    3973:	48 3b 9d a0 00 00 00 	cmp    0xa0(%rbp),%rbx
    397a:	7c a4                	jl     3920 <main+0x1330>
    397c:	48 89 e8             	mov    %rbp,%rax
    397f:	4c 8b 1c 24          	mov    (%rsp),%r11
    3983:	4c 89 f5             	mov    %r14,%rbp
    3986:	4c 89 eb             	mov    %r13,%rbx
    3989:	49 89 c6             	mov    %rax,%r14
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    398c:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    3993:	85 f6                	test   %esi,%esi
    3995:	0f 8e 0d 01 00 00    	jle    3aa8 <main+0x14b8>
    399b:	4c 89 5c 24 50       	mov    %r11,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    39a0:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    39a4:	31 d2                	xor    %edx,%edx
    39a6:	48 89 5c 24 70       	mov    %rbx,0x70(%rsp)
    39ab:	48 89 6c 24 60       	mov    %rbp,0x60(%rsp)
    39b0:	4c 89 7c 24 78       	mov    %r15,0x78(%rsp)
    39b5:	0f 1f 00             	nopl   (%rax)
    39b8:	49 8b 04 d1          	mov    (%r9,%rdx,8),%rax
    39bc:	89 d3                	mov    %edx,%ebx
    39be:	4c 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%r15
    39c6:	44 8b 00             	mov    (%rax),%r8d
    39c9:	45 85 c0             	test   %r8d,%r8d
    39cc:	0f 8e b6 00 00 00    	jle    3a88 <main+0x1498>
    39d2:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    39d7:	48 8b 48 08          	mov    0x8(%rax),%rcx
    39db:	31 c0                	xor    %eax,%eax
    39dd:	48 89 c6             	mov    %rax,%rsi
    39e0:	48 89 f5             	mov    %rsi,%rbp
    39e3:	45 31 ed             	xor    %r13d,%r13d
    39e6:	48 c1 e5 08          	shl    $0x8,%rbp
    39ea:	48 8d 14 29          	lea    (%rcx,%rbp,1),%rdx
    39ee:	8b 82 94 00 00 00    	mov    0x94(%rdx),%eax
    39f4:	85 c0                	test   %eax,%eax
    39f6:	7e 77                	jle    3a6f <main+0x147f>
    39f8:	48 89 34 24          	mov    %rsi,(%rsp)
    39fc:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3a00:	4c 89 e9             	mov    %r13,%rcx
    3a03:	48 83 ec 08          	sub    $0x8,%rsp
    3a07:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3a0c:	49 83 c5 01          	add    $0x1,%r13
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3a10:	48 c1 e1 05          	shl    $0x5,%rcx
    3a14:	48 03 8a 88 00 00 00 	add    0x88(%rdx),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3a1b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3a1f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3a23:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3a26:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3a2a:	4c 2b 01             	sub    (%rcx),%r8
    3a2d:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3a2e:	49 f7 e4             	mul    %r12
    3a31:	89 d9                	mov    %ebx,%ecx
    3a33:	48 8d 35 c6 3d 00 00 	lea    0x3dc6(%rip),%rsi        # 7800 <_IO_stdin_used+0x800>
    3a3a:	31 c0                	xor    %eax,%eax
    3a3c:	48 c1 ea 12          	shr    $0x12,%rdx
    3a40:	49 89 d1             	mov    %rdx,%r9
    3a43:	ba 02 00 00 00       	mov    $0x2,%edx
    3a48:	e8 03 ea ff ff       	call   2450 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3a4d:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    3a51:	5e                   	pop    %rsi
    3a52:	5f                   	pop    %rdi
    3a53:	4b 8b 04 39          	mov    (%r9,%r15,1),%rax
    3a57:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3a5b:	48 8d 14 29          	lea    (%rcx,%rbp,1),%rdx
    3a5f:	44 39 aa 94 00 00 00 	cmp    %r13d,0x94(%rdx)
    3a66:	7f 98                	jg     3a00 <main+0x1410>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3a68:	48 8b 34 24          	mov    (%rsp),%rsi
    3a6c:	44 8b 00             	mov    (%rax),%r8d
    3a6f:	48 83 c6 01          	add    $0x1,%rsi
    3a73:	41 39 f0             	cmp    %esi,%r8d
    3a76:	0f 8f 64 ff ff ff    	jg     39e0 <main+0x13f0>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3a7c:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    3a81:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    3a88:	48 83 c2 01          	add    $0x1,%rdx
    3a8c:	39 d6                	cmp    %edx,%esi
    3a8e:	0f 8f 24 ff ff ff    	jg     39b8 <main+0x13c8>
    3a94:	4c 8b 5c 24 50       	mov    0x50(%rsp),%r11
    3a99:	48 8b 5c 24 70       	mov    0x70(%rsp),%rbx
    3a9e:	48 8b 6c 24 60       	mov    0x60(%rsp),%rbp
    3aa3:	4c 8b 7c 24 78       	mov    0x78(%rsp),%r15
    for (int d = 0 ; d < threads_per_group ; d++) {
    3aa8:	48 83 44 24 18 18    	addq   $0x18,0x18(%rsp)
    3aae:	8b 7c 24 38          	mov    0x38(%rsp),%edi
    3ab2:	49 81 c6 c0 00 00 00 	add    $0xc0,%r14
    3ab9:	39 7c 24 48          	cmp    %edi,0x48(%rsp)
    3abd:	0f 85 bd fc ff ff    	jne    3780 <main+0x1190>
  for (int k = 0 ; k < group_count ; k++) {
    3ac3:	48 89 2c 24          	mov    %rbp,(%rsp)
    3ac7:	48 8b 6c 24 40       	mov    0x40(%rsp),%rbp
    3acc:	48 89 de             	mov    %rbx,%rsi
    3acf:	4c 89 fb             	mov    %r15,%rbx
    3ad2:	48 85 ed             	test   %rbp,%rbp
    3ad5:	75 0a                	jne    3ae1 <main+0x14f1>
    3ad7:	48 8b 6c 24 30       	mov    0x30(%rsp),%rbp
    3adc:	e9 59 fc ff ff       	jmp    373a <main+0x114a>
    3ae1:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    3ae6:	48 89 f2             	mov    %rsi,%rdx
    3ae9:	49 89 f6             	mov    %rsi,%r14
    3aec:	bf 01 00 00 00       	mov    $0x1,%edi
    3af1:	48 8d 35 f1 39 00 00 	lea    0x39f1(%rip),%rsi        # 74e9 <_IO_stdin_used+0x4e9>
    3af8:	31 c0                	xor    %eax,%eax
    3afa:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3aff:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    3b09:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    3b0e:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    3b13:	e8 38 e9 ff ff       	call   2450 <__printf_chk@plt>
    3b18:	bf 0a 00 00 00       	mov    $0xa,%edi
    3b1d:	e8 ae e7 ff ff       	call   22d0 <putchar@plt>
    3b22:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    3b27:	bf 01 00 00 00       	mov    $0x1,%edi
    3b2c:	48 8d 35 25 3d 00 00 	lea    0x3d25(%rip),%rsi        # 7858 <_IO_stdin_used+0x858>
    3b33:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3b37:	31 c0                	xor    %eax,%eax
    3b39:	e8 12 e9 ff ff       	call   2450 <__printf_chk@plt>
    3b3e:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    3b43:	bf 01 00 00 00       	mov    $0x1,%edi
    3b48:	48 8d 35 31 3d 00 00 	lea    0x3d31(%rip),%rsi        # 7880 <_IO_stdin_used+0x880>
    3b4f:	4c 89 d8             	mov    %r11,%rax
    3b52:	49 c1 fb 3f          	sar    $0x3f,%r11
    3b56:	48 f7 eb             	imul   %rbx
    3b59:	31 c0                	xor    %eax,%eax
    3b5b:	48 d1 fa             	sar    %rdx
    3b5e:	4c 29 da             	sub    %r11,%rdx
    3b61:	e8 ea e8 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3b66:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3b6b:	bf 01 00 00 00       	mov    $0x1,%edi
    3b70:	48 8d 35 39 3d 00 00 	lea    0x3d39(%rip),%rsi        # 78b0 <_IO_stdin_used+0x8b0>
    3b77:	4c 89 c8             	mov    %r9,%rax
    3b7a:	49 c1 f9 3f          	sar    $0x3f,%r9
    3b7e:	48 f7 eb             	imul   %rbx
    3b81:	31 c0                	xor    %eax,%eax
    3b83:	48 d1 fa             	sar    %rdx
    3b86:	4c 29 ca             	sub    %r9,%rdx
    3b89:	e8 c2 e8 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3b8e:	4c 89 f0             	mov    %r14,%rax
    3b91:	bf 01 00 00 00       	mov    $0x1,%edi
    3b96:	48 8d 35 43 3d 00 00 	lea    0x3d43(%rip),%rsi        # 78e0 <_IO_stdin_used+0x8e0>
    3b9d:	48 f7 eb             	imul   %rbx
    3ba0:	4c 89 f0             	mov    %r14,%rax
    3ba3:	48 c1 f8 3f          	sar    $0x3f,%rax
    3ba7:	48 d1 fa             	sar    %rdx
    3baa:	48 29 c2             	sub    %rax,%rdx
    3bad:	31 c0                	xor    %eax,%eax
    3baf:	e8 9c e8 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3bb4:	48 8b 04 24          	mov    (%rsp),%rax
    3bb8:	bf 01 00 00 00       	mov    $0x1,%edi
    3bbd:	48 8d 35 39 39 00 00 	lea    0x3939(%rip),%rsi        # 74fd <_IO_stdin_used+0x4fd>
    3bc4:	48 f7 eb             	imul   %rbx
    3bc7:	48 8b 04 24          	mov    (%rsp),%rax
    3bcb:	48 c1 f8 3f          	sar    $0x3f,%rax
    3bcf:	48 d1 fa             	sar    %rdx
    3bd2:	48 29 c2             	sub    %rax,%rdx
    3bd5:	31 c0                	xor    %eax,%eax
    3bd7:	e8 74 e8 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3bdc:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    3be1:	bf 01 00 00 00       	mov    $0x1,%edi
    3be6:	48 8d 35 21 39 00 00 	lea    0x3921(%rip),%rsi        # 750e <_IO_stdin_used+0x50e>
    3bed:	4c 89 d0             	mov    %r10,%rax
    3bf0:	48 f7 eb             	imul   %rbx
    3bf3:	4c 89 d0             	mov    %r10,%rax
    3bf6:	48 c1 f8 3f          	sar    $0x3f,%rax
    3bfa:	48 d1 fa             	sar    %rdx
    3bfd:	48 29 c2             	sub    %rax,%rdx
    3c00:	31 c0                	xor    %eax,%eax
    3c02:	e8 49 e8 ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3c07:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    3c0f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3c18:	75 25                	jne    3c3f <main+0x164f>
    3c1a:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    3c21:	31 c0                	xor    %eax,%eax
    3c23:	5b                   	pop    %rbx
    3c24:	5d                   	pop    %rbp
    3c25:	41 5c                	pop    %r12
    3c27:	41 5d                	pop    %r13
    3c29:	41 5e                	pop    %r14
    3c2b:	41 5f                	pop    %r15
    3c2d:	c3                   	ret
      long v = 0;
    3c2e:	31 d2                	xor    %edx,%edx
    3c30:	e9 cd fb ff ff       	jmp    3802 <main+0x1212>
            exit(1);
    3c35:	bf 01 00 00 00       	mov    $0x1,%edi
    3c3a:	e8 61 e8 ff ff       	call   24a0 <exit@plt>
}
    3c3f:	e8 ec e6 ff ff       	call   2330 <__stack_chk_fail@plt>
    3c44:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3c4e:	66 90                	xchg   %ax,%ax

0000000000003c50 <_start>:
    3c50:	f3 0f 1e fa          	endbr64
    3c54:	31 ed                	xor    %ebp,%ebp
    3c56:	49 89 d1             	mov    %rdx,%r9
    3c59:	5e                   	pop    %rsi
    3c5a:	48 89 e2             	mov    %rsp,%rdx
    3c5d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3c61:	50                   	push   %rax
    3c62:	54                   	push   %rsp
    3c63:	45 31 c0             	xor    %r8d,%r8d
    3c66:	31 c9                	xor    %ecx,%ecx
    3c68:	48 8d 3d 81 e9 ff ff 	lea    -0x167f(%rip),%rdi        # 25f0 <main>
    3c6f:	ff 15 63 63 00 00    	call   *0x6363(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3c75:	f4                   	hlt
    3c76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003c80 <deregister_tm_clones>:
    3c80:	48 8d 3d 99 63 00 00 	lea    0x6399(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3c87:	48 8d 05 92 63 00 00 	lea    0x6392(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    3c8e:	48 39 f8             	cmp    %rdi,%rax
    3c91:	74 15                	je     3ca8 <deregister_tm_clones+0x28>
    3c93:	48 8b 05 46 63 00 00 	mov    0x6346(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    3c9a:	48 85 c0             	test   %rax,%rax
    3c9d:	74 09                	je     3ca8 <deregister_tm_clones+0x28>
    3c9f:	ff e0                	jmp    *%rax
    3ca1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3ca8:	c3                   	ret
    3ca9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003cb0 <register_tm_clones>:
    3cb0:	48 8d 3d 69 63 00 00 	lea    0x6369(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3cb7:	48 8d 35 62 63 00 00 	lea    0x6362(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    3cbe:	48 29 fe             	sub    %rdi,%rsi
    3cc1:	48 89 f0             	mov    %rsi,%rax
    3cc4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3cc8:	48 c1 f8 03          	sar    $0x3,%rax
    3ccc:	48 01 c6             	add    %rax,%rsi
    3ccf:	48 d1 fe             	sar    %rsi
    3cd2:	74 14                	je     3ce8 <register_tm_clones+0x38>
    3cd4:	48 8b 05 15 63 00 00 	mov    0x6315(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    3cdb:	48 85 c0             	test   %rax,%rax
    3cde:	74 08                	je     3ce8 <register_tm_clones+0x38>
    3ce0:	ff e0                	jmp    *%rax
    3ce2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3ce8:	c3                   	ret
    3ce9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003cf0 <__do_global_dtors_aux>:
    3cf0:	f3 0f 1e fa          	endbr64
    3cf4:	80 3d 2d 63 00 00 00 	cmpb   $0x0,0x632d(%rip)        # a028 <completed.0>
    3cfb:	75 2b                	jne    3d28 <__do_global_dtors_aux+0x38>
    3cfd:	55                   	push   %rbp
    3cfe:	48 83 3d f2 62 00 00 00 	cmpq   $0x0,0x62f2(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3d06:	48 89 e5             	mov    %rsp,%rbp
    3d09:	74 0c                	je     3d17 <__do_global_dtors_aux+0x27>
    3d0b:	48 8b 3d f6 62 00 00 	mov    0x62f6(%rip),%rdi        # a008 <__dso_handle>
    3d12:	e8 99 e5 ff ff       	call   22b0 <__cxa_finalize@plt>
    3d17:	e8 64 ff ff ff       	call   3c80 <deregister_tm_clones>
    3d1c:	c6 05 05 63 00 00 01 	movb   $0x1,0x6305(%rip)        # a028 <completed.0>
    3d23:	5d                   	pop    %rbp
    3d24:	c3                   	ret
    3d25:	0f 1f 00             	nopl   (%rax)
    3d28:	c3                   	ret
    3d29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003d30 <frame_dummy>:
    3d30:	f3 0f 1e fa          	endbr64
    3d34:	e9 77 ff ff ff       	jmp    3cb0 <register_tm_clones>
    3d39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003d40 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3d40:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3d44:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3d4b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    3d4f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3d57:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    3d5b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3d5f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3d66:	48 85 c9             	test   %rcx,%rcx
    3d69:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3d70:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3d74:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3d78:	31 c0                	xor    %eax,%eax
    3d7a:	c3                   	ret
    3d7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003d80 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3d80:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3d84:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    3d8b:	85 c9                	test   %ecx,%ecx
    3d8d:	7e 4f                	jle    3dde <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3d8f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3d96:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    3d9d:	48 c1 e1 09          	shl    $0x9,%rcx
    3da1:	48 8b 50 18          	mov    0x18(%rax),%rdx
    3da5:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3da9:	48 8b 70 38          	mov    0x38(%rax),%rsi
    3dad:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3daf:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    3db3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3db8:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3dc0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3dc8:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3dd3:	48 05 00 02 00 00    	add    $0x200,%rax
    3dd9:	48 39 c1             	cmp    %rax,%rcx
    3ddc:	75 da                	jne    3db8 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    3dde:	0f ae f8             	sfence
}
    3de1:	31 c0                	xor    %eax,%eax
    3de3:	c3                   	ret
    3de4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3def:	90                   	nop

0000000000003df0 <external_thread>:
void * external_thread(void *arg) {
    3df0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3df4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    3df8:	0f 85 fb 00 00 00    	jne    3ef9 <external_thread+0x109>
void * external_thread(void *arg) {
    3dfe:	41 57                	push   %r15
    3e00:	49 89 ff             	mov    %rdi,%r15
    3e03:	41 56                	push   %r14
    3e05:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    3e07:	4c 8d 2d f6 31 00 00 	lea    0x31f6(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    3e0e:	41 54                	push   %r12
    3e10:	55                   	push   %rbp
    3e11:	53                   	push   %rbx
    3e12:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    3e16:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    3e1c:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    3e20:	85 c9                	test   %ecx,%ecx
    3e22:	7e 6e                	jle    3e92 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3e24:	45 31 e4             	xor    %r12d,%r12d
    3e27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3e30:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    3e38:	31 db                	xor    %ebx,%ebx
    3e3a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3e3e:	48 8b 06             	mov    (%rsi),%rax
    3e41:	8b 10                	mov    (%rax),%edx
    3e43:	85 d2                	test   %edx,%edx
    3e45:	7e 2a                	jle    3e71 <external_thread+0x81>
    3e47:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    3e4b:	48 89 dd             	mov    %rbx,%rbp
    3e4e:	48 c1 e5 08          	shl    $0x8,%rbp
    3e52:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    3e56:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    3e5d:	45 85 c0             	test   %r8d,%r8d
    3e60:	74 36                	je     3e98 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3e62:	48 83 c3 01          	add    $0x1,%rbx
    3e66:	39 da                	cmp    %ebx,%edx
    3e68:	7f e1                	jg     3e4b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    3e6a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    3e71:	49 83 c4 01          	add    $0x1,%r12
    3e75:	44 39 e1             	cmp    %r12d,%ecx
    3e78:	7f b6                	jg     3e30 <external_thread+0x40>
  while (data->running == 1) {
    3e7a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    3e7f:	74 9f                	je     3e20 <external_thread+0x30>
}
    3e81:	48 83 c4 08          	add    $0x8,%rsp
    3e85:	31 c0                	xor    %eax,%eax
    3e87:	5b                   	pop    %rbx
    3e88:	5d                   	pop    %rbp
    3e89:	41 5c                	pop    %r12
    3e8b:	41 5d                	pop    %r13
    3e8d:	41 5e                	pop    %r14
    3e8f:	41 5f                	pop    %r15
    3e91:	c3                   	ret
  while (data->running == 1) {
    3e92:	eb fe                	jmp    3e92 <external_thread+0xa2>
    3e94:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    3e98:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    3e9b:	48 8b 06             	mov    (%rsi),%rax
    3e9e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    3ea2:	48 01 ef             	add    %rbp,%rdi
    3ea5:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    3eac:	48 c1 e6 05          	shl    $0x5,%rsi
    3eb0:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    3eb7:	bf 04 00 00 00       	mov    $0x4,%edi
    3ebc:	e8 4f e4 ff ff       	call   2310 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    3ec1:	49 8b 47 50          	mov    0x50(%r15),%rax
    3ec5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    3ec9:	48 8b 40 08          	mov    0x8(%rax),%rax
    3ecd:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    3ed8:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3edb:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    3edf:	48 83 c3 01          	add    $0x1,%rbx
    3ee3:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3ee7:	48 8b 06             	mov    (%rsi),%rax
    3eea:	8b 10                	mov    (%rax),%edx
    3eec:	39 da                	cmp    %ebx,%edx
    3eee:	0f 8f 53 ff ff ff    	jg     3e47 <external_thread+0x57>
    3ef4:	e9 71 ff ff ff       	jmp    3e6a <external_thread+0x7a>
}
    3ef9:	31 c0                	xor    %eax,%eax
    3efb:	c3                   	ret
    3efc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003f00 <timer_thread>:
void* timer_thread(void *arg) {
    3f00:	f3 0f 1e fa          	endbr64
    3f04:	41 57                	push   %r15
    3f06:	48 8d 35 03 31 00 00 	lea    0x3103(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3f0d:	41 56                	push   %r14
    3f0f:	41 55                	push   %r13
    3f11:	41 54                	push   %r12
    3f13:	55                   	push   %rbp
    3f14:	48 89 fd             	mov    %rdi,%rbp
    3f17:	53                   	push   %rbx
    3f18:	48 83 ec 58          	sub    $0x58,%rsp
    3f1c:	8b 57 04             	mov    0x4(%rdi),%edx
    3f1f:	bf 01 00 00 00       	mov    $0x1,%edi
    3f24:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3f2d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3f32:	31 c0                	xor    %eax,%eax
    3f34:	e8 17 e5 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3f39:	66 0f 6f 05 bf 3b 00 00 	movdqa 0x3bbf(%rip),%xmm0        # 7b00 <_IO_stdin_used+0xb00>
    3f41:	ba 88 13 00 00       	mov    $0x1388,%edx
    3f46:	31 c0                	xor    %eax,%eax
    3f48:	48 8d 35 d3 30 00 00 	lea    0x30d3(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3f4f:	bf 01 00 00 00       	mov    $0x1,%edi
    3f54:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3f59:	e8 f2 e4 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3f5e:	44 8b 65 44          	mov    0x44(%rbp),%r12d
    3f62:	45 85 e4             	test   %r12d,%r12d
    3f65:	0f 84 a3 00 00 00    	je     400e <timer_thread+0x10e>
  int n = 0;
    3f6b:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    3f6e:	45 31 e4             	xor    %r12d,%r12d
    3f71:	49 89 e6             	mov    %rsp,%r14
    y++;
    3f74:	31 db                	xor    %ebx,%ebx
    3f76:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    3f7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    nanosleep(&preempt , &rem2);
    3f80:	4c 89 ef             	mov    %r13,%rdi
    3f83:	4c 89 f6             	mov    %r14,%rsi
    n++;
    3f86:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3f8a:	e8 c1 e3 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f8f:	48 63 45 30          	movslq 0x30(%rbp),%rax
    y++;
    3f93:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f98:	85 c0                	test   %eax,%eax
    3f9a:	7e 49                	jle    3fe5 <timer_thread+0xe5>
    3f9c:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3fa0:	49 c1 e4 09          	shl    $0x9,%r12
    3fa4:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3fa8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3fb0:	4c 8b 11             	mov    (%rcx),%r10
    3fb3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3fb5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3fb9:	99                   	cltd
    3fba:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3fbe:	49 8b 72 38          	mov    0x38(%r10),%rsi
    3fc2:	48 63 d2             	movslq %edx,%rdx
    3fc5:	48 c1 e2 09          	shl    $0x9,%rdx
    3fc9:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3fd4:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3fe0:	49 39 c8             	cmp    %rcx,%r8
    3fe3:	75 cb                	jne    3fb0 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    3fe5:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3fe8:	48 8b 45 18          	mov    0x18(%rbp),%rax
  while (data->running && n < times) {
    3fec:	44 8b 45 44          	mov    0x44(%rbp),%r8d
    if (y >= data->threads[0]->task_count) {
    3ff0:	48 8b 00             	mov    (%rax),%rax
    y++;
    3ff3:	39 78 40             	cmp    %edi,0x40(%rax)
    3ff6:	0f 4e fb             	cmovle %ebx,%edi
    3ff9:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3ffc:	45 85 c0             	test   %r8d,%r8d
    3fff:	74 0d                	je     400e <timer_thread+0x10e>
    4001:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    4008:	0f 85 72 ff ff ff    	jne    3f80 <timer_thread+0x80>
    400e:	48 8d 3d 23 30 00 00 	lea    0x3023(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    4015:	e8 d6 e2 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    401a:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    401e:	85 d2                	test   %edx,%edx
    4020:	7e 73                	jle    4095 <timer_thread+0x195>
    for (int y = 0 ; y < data->task_count ; y++) {
    4022:	48 63 45 40          	movslq 0x40(%rbp),%rax
    4026:	85 c0                	test   %eax,%eax
    4028:	7e 6b                	jle    4095 <timer_thread+0x195>
    402a:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    402e:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    4032:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    403a:	31 c9                	xor    %ecx,%ecx
    403c:	48 89 c6             	mov    %rax,%rsi
    403f:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4043:	48 8b 40 38          	mov    0x38(%rax),%rax
    4047:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    404b:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4051:	74 1d                	je     4070 <timer_thread+0x170>
    4053:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    405d:	48 05 00 02 00 00    	add    $0x200,%rax
    4063:	48 39 c2             	cmp    %rax,%rdx
    4066:	74 24                	je     408c <timer_thread+0x18c>
    4068:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->threads[x]->tasks[y].sending = 0;
    4070:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    407a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4080:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4087:	48 39 c2             	cmp    %rax,%rdx
    408a:	75 e4                	jne    4070 <timer_thread+0x170>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    408c:	48 83 c1 08          	add    $0x8,%rcx
    4090:	48 39 cf             	cmp    %rcx,%rdi
    4093:	75 aa                	jne    403f <timer_thread+0x13f>
  asm volatile ("mfence" ::: "memory");
    4095:	0f ae f0             	mfence
  struct timespec drain = {
    4098:	66 0f 6f 05 70 3a 00 00 	movdqa 0x3a70(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    40a0:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    40a5:	48 63 45 28          	movslq 0x28(%rbp),%rax
    y++;
    40a9:	45 8d 44 24 01       	lea    0x1(%r12),%r8d
    for (int x = 0 ; x < data->thread_count ; x++) {
    40ae:	85 c0                	test   %eax,%eax
    40b0:	7e 4b                	jle    40fd <timer_thread+0x1fd>
    40b2:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    40b6:	4d 63 e4             	movslq %r12d,%r12
    40b9:	49 c1 e4 09          	shl    $0x9,%r12
    40bd:	48 8d 3c c1          	lea    (%rcx,%rax,8),%rdi
    40c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    40c8:	48 8b 19             	mov    (%rcx),%rbx
    40cb:	44 89 c0             	mov    %r8d,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    40ce:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    40d2:	99                   	cltd
    40d3:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    40d6:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    40da:	48 63 d2             	movslq %edx,%rdx
    40dd:	48 c1 e2 09          	shl    $0x9,%rdx
    40e1:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    40ec:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    40f8:	48 39 cf             	cmp    %rcx,%rdi
    40fb:	75 cb                	jne    40c8 <timer_thread+0x1c8>
    asm volatile ("mfence" ::: "memory");
    40fd:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4100:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4104:	8b 4d 30             	mov    0x30(%rbp),%ecx
    y++;
    4107:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    410a:	48 8b 07             	mov    (%rdi),%rax
    y++;
    410d:	44 39 40 40          	cmp    %r8d,0x40(%rax)
    4111:	45 0f 4f e0          	cmovg  %r8d,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4115:	85 c9                	test   %ecx,%ecx
    4117:	0f 8e 0d 01 00 00    	jle    422a <timer_thread+0x32a>
    411d:	45 31 ff             	xor    %r15d,%r15d
    int all_empty = 1;
    4120:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    4126:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int y = 0 ; y < 2 ; y++) {
    4130:	31 db                	xor    %ebx,%ebx
    4132:	45 89 fd             	mov    %r15d,%r13d
    4135:	4e 8d 34 fd 00 00 00 00 	lea    0x0(,%r15,8),%r14
    413d:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    413f:	85 c9                	test   %ecx,%ecx
    4141:	0f 8e 91 00 00 00    	jle    41d8 <timer_thread+0x2d8>
    4147:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    414b:	4a 8b 14 37          	mov    (%rdi,%r14,1),%rdx
    414f:	48 89 d8             	mov    %rbx,%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4152:	45 31 c0             	xor    %r8d,%r8d
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4155:	48 c1 e0 09          	shl    $0x9,%rax
    4159:	48 03 42 38          	add    0x38(%rdx),%rax
    415d:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    4164:	eb 1c                	jmp    4182 <timer_thread+0x282>
    4166:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4170:	48 85 d2             	test   %rdx,%rdx
    4173:	7f 27                	jg     419c <timer_thread+0x29c>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4175:	41 83 c0 01          	add    $0x1,%r8d
    4179:	48 83 c0 28          	add    $0x28,%rax
    417d:	41 39 c8             	cmp    %ecx,%r8d
    4180:	74 7e                	je     4200 <timer_thread+0x300>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4182:	48 8b 10             	mov    (%rax),%rdx
    4185:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    418c:	48 8b 50 08          	mov    0x8(%rax),%rdx
    4190:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    4197:	4d 85 c9             	test   %r9,%r9
    419a:	7e d4                	jle    4170 <timer_thread+0x270>
    419c:	48 83 ec 08          	sub    $0x8,%rsp
    41a0:	89 f1                	mov    %esi,%ecx
    41a2:	bf 01 00 00 00       	mov    $0x1,%edi
    41a7:	31 c0                	xor    %eax,%eax
    41a9:	52                   	push   %rdx
    41aa:	48 8d 35 ac 2e 00 00 	lea    0x2eac(%rip),%rsi        # 705d <_IO_stdin_used+0x5d>
    41b1:	44 89 ea             	mov    %r13d,%edx
    41b4:	e8 97 e2 ff ff       	call   2450 <__printf_chk@plt>
      for (int y = 0 ; y < 2 ; y++) {
    41b9:	5a                   	pop    %rdx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    41ba:	8b 4d 30             	mov    0x30(%rbp),%ecx
      for (int y = 0 ; y < 2 ; y++) {
    41bd:	5e                   	pop    %rsi
    41be:	48 83 fb 01          	cmp    $0x1,%rbx
    41c2:	74 54                	je     4218 <timer_thread+0x318>
    41c4:	48 83 c3 01          	add    $0x1,%rbx
    41c8:	45 31 db             	xor    %r11d,%r11d
    41cb:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    41cd:	85 c9                	test   %ecx,%ecx
    41cf:	0f 8f 72 ff ff ff    	jg     4147 <timer_thread+0x247>
    41d5:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    41d8:	49 83 c7 01          	add    $0x1,%r15
    41dc:	44 39 f9             	cmp    %r15d,%ecx
    41df:	0f 8f 4b ff ff ff    	jg     4130 <timer_thread+0x230>
    if (all_empty == 1) {
    41e5:	41 83 fb 01          	cmp    $0x1,%r11d
    41e9:	74 3f                	je     422a <timer_thread+0x32a>
      nanosleep(&drain , &drainrem);
    41eb:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    41f0:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    41f5:	e8 56 e1 ff ff       	call   2350 <nanosleep@plt>
    41fa:	e9 a6 fe ff ff       	jmp    40a5 <timer_thread+0x1a5>
    41ff:	90                   	nop
      for (int y = 0 ; y < 2 ; y++) {
    4200:	48 83 fb 01          	cmp    $0x1,%rbx
    4204:	74 d2                	je     41d8 <timer_thread+0x2d8>
    4206:	48 83 c3 01          	add    $0x1,%rbx
    420a:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    420c:	e9 3a ff ff ff       	jmp    414b <timer_thread+0x24b>
    4211:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4218:	49 83 c7 01          	add    $0x1,%r15
    421c:	45 31 db             	xor    %r11d,%r11d
    421f:	44 39 f9             	cmp    %r15d,%ecx
    4222:	0f 8f 08 ff ff ff    	jg     4130 <timer_thread+0x230>
    4228:	eb bb                	jmp    41e5 <timer_thread+0x2e5>
    422a:	48 8d 3d 23 2e 00 00 	lea    0x2e23(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    4231:	e8 ba e0 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    4236:	8b 7d 44             	mov    0x44(%rbp),%edi
    4239:	85 ff                	test   %edi,%edi
    423b:	0f 84 ed 00 00 00    	je     432e <timer_thread+0x42e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4241:	8b 45 2c             	mov    0x2c(%rbp),%eax
    4244:	31 db                	xor    %ebx,%ebx
    4246:	4c 8d 25 27 2e 00 00 	lea    0x2e27(%rip),%r12        # 7074 <_IO_stdin_used+0x74>
    424d:	4c 8d 2d 3b 2e 00 00 	lea    0x2e3b(%rip),%r13        # 708f <_IO_stdin_used+0x8f>
    4254:	85 c0                	test   %eax,%eax
    4256:	7e 3b                	jle    4293 <timer_thread+0x393>
    4258:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4260:	31 c0                	xor    %eax,%eax
    4262:	89 da                	mov    %ebx,%edx
    4264:	4c 89 e6             	mov    %r12,%rsi
    4267:	bf 01 00 00 00       	mov    $0x1,%edi
    426c:	e8 df e1 ff ff       	call   2450 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4271:	48 8b 45 18          	mov    0x18(%rbp),%rax
    4275:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4279:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    427d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4284:	0f 84 d1 00 00 00    	je     435b <timer_thread+0x45b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    428a:	48 83 c3 01          	add    $0x1,%rbx
    428e:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    4291:	7f cd                	jg     4260 <timer_thread+0x360>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4293:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    4297:	85 d2                	test   %edx,%edx
    4299:	7e 7d                	jle    4318 <timer_thread+0x418>
      for (int y = 0 ; y < data->task_count ; y++) {
    429b:	8b 45 40             	mov    0x40(%rbp),%eax
    429e:	85 c0                	test   %eax,%eax
    42a0:	7e 76                	jle    4318 <timer_thread+0x418>
    42a2:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    42a5:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    42a9:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    42b1:	31 c9                	xor    %ecx,%ecx
    42b3:	48 c1 e6 09          	shl    $0x9,%rsi
    42b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    42c0:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    42c4:	48 8b 40 38          	mov    0x38(%rax),%rax
    42c8:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    42cc:	f7 c6 00 02 00 00    	test   $0x200,%esi
    42d2:	74 1c                	je     42f0 <timer_thread+0x3f0>
    42d4:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    42de:	48 05 00 02 00 00    	add    $0x200,%rax
    42e4:	48 39 d0             	cmp    %rdx,%rax
    42e7:	74 26                	je     430f <timer_thread+0x40f>
    42e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    42f0:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    42fa:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4300:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    430a:	48 39 d0             	cmp    %rdx,%rax
    430d:	75 e1                	jne    42f0 <timer_thread+0x3f0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    430f:	48 83 c1 08          	add    $0x8,%rcx
    4313:	48 39 f9             	cmp    %rdi,%rcx
    4316:	75 a8                	jne    42c0 <timer_thread+0x3c0>
    asm volatile ("mfence" ::: "memory");
    4318:	0f ae f0             	mfence
    431b:	48 8d 3d 7f 2d 00 00 	lea    0x2d7f(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    4322:	e8 c9 df ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    4327:	c7 45 44 00 00 00 00 	movl   $0x0,0x44(%rbp)
    432e:	48 8d 3d 73 2d 00 00 	lea    0x2d73(%rip),%rdi        # 70a8 <_IO_stdin_used+0xa8>
    4335:	e8 b6 df ff ff       	call   22f0 <puts@plt>
}
    433a:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    433f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4348:	75 40                	jne    438a <timer_thread+0x48a>
    434a:	48 83 c4 58          	add    $0x58,%rsp
    434e:	31 c0                	xor    %eax,%eax
    4350:	5b                   	pop    %rbx
    4351:	5d                   	pop    %rbp
    4352:	41 5c                	pop    %r12
    4354:	41 5d                	pop    %r13
    4356:	41 5e                	pop    %r14
    4358:	41 5f                	pop    %r15
    435a:	c3                   	ret
    435b:	4c 89 ef             	mov    %r13,%rdi
    435e:	e8 8d df ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4363:	48 8b 45 18          	mov    0x18(%rbp),%rax
    4367:	be 01 00 00 00       	mov    $0x1,%esi
    436c:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4370:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4374:	8b 78 60             	mov    0x60(%rax),%edi
    4377:	e8 84 e0 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    437c:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    437f:	0f 8f db fe ff ff    	jg     4260 <timer_thread+0x360>
    4385:	e9 09 ff ff ff       	jmp    4293 <timer_thread+0x393>
}
    438a:	e8 a1 df ff ff       	call   2330 <__stack_chk_fail@plt>
    438f:	90                   	nop

0000000000004390 <sendm.part.0>:
int sendm(struct BarrierTask *data) {
    4390:	41 57                	push   %r15
    4392:	41 56                	push   %r14
    4394:	41 55                	push   %r13
    4396:	41 54                	push   %r12
    4398:	55                   	push   %rbp
    4399:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    439a:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    43a0:	89 44 24 c8          	mov    %eax,-0x38(%rsp)
    43a4:	85 c0                	test   %eax,%eax
    43a6:	0f 8e 77 01 00 00    	jle    4523 <sendm.part.0+0x193>
        if (n == data->thread_index) { continue; }
    43ac:	8b 87 30 01 00 00    	mov    0x130(%rdi),%eax
    43b2:	49 89 fe             	mov    %rdi,%r14
    43b5:	45 31 e4             	xor    %r12d,%r12d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    43b8:	45 31 ff             	xor    %r15d,%r15d
        if (n == data->thread_index) { continue; }
    43bb:	89 44 24 cc          	mov    %eax,-0x34(%rsp)
    43bf:	48 8d 87 88 01 00 00 	lea    0x188(%rdi),%rax
    43c6:	48 89 44 24 e8       	mov    %rax,-0x18(%rsp)
    43cb:	48 8d 87 90 01 00 00 	lea    0x190(%rdi),%rax
    43d2:	48 89 44 24 f0       	mov    %rax,-0x10(%rsp)
    43d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    43e0:	44 39 7c 24 cc       	cmp    %r15d,-0x34(%rsp)
    43e5:	0f 84 23 01 00 00    	je     450e <sendm.part.0+0x17e>
        struct Data *them = data->mailboxes[n].higher;
    43eb:	4d 8b 86 70 01 00 00 	mov    0x170(%r14),%r8
    43f2:	4d 01 e0             	add    %r12,%r8
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    43f5:	45 8b 48 20          	mov    0x20(%r8),%r9d
        struct Data *them = data->mailboxes[n].higher;
    43f9:	49 8b 78 08          	mov    0x8(%r8),%rdi
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    43fd:	41 83 f9 02          	cmp    $0x2,%r9d
    4401:	0f 84 31 01 00 00    	je     4538 <sendm.part.0+0x1a8>
        for (; them->messages_count < min;) {
    4407:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    440e:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    4415:	48 39 e9             	cmp    %rbp,%rcx
    4418:	0f 8d f0 00 00 00    	jge    450e <sendm.part.0+0x17e>
    441e:	49 8b 86 08 01 00 00 	mov    0x108(%r14),%rax
    4425:	48 39 e9             	cmp    %rbp,%rcx
    4428:	49 89 eb             	mov    %rbp,%r11
          them->messages[them->messages_count++] = data->message; 
    442b:	48 8b 17             	mov    (%rdi),%rdx
    442e:	41 0f 9c c5          	setl   %r13b
    4432:	49 29 cb             	sub    %rcx,%r11
    4435:	48 89 44 24 d0       	mov    %rax,-0x30(%rsp)
    443a:	49 8b 40 10          	mov    0x10(%r8),%rax
    443e:	49 8d 5b ff          	lea    -0x1(%r11),%rbx
    4442:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    4447:	48 89 44 24 d8       	mov    %rax,-0x28(%rsp)
    444c:	48 83 fb 02          	cmp    $0x2,%rbx
    4450:	0f 86 9a 01 00 00    	jbe    45f0 <sendm.part.0+0x260>
    4456:	45 84 ed             	test   %r13b,%r13b
    4459:	0f 84 91 01 00 00    	je     45f0 <sendm.part.0+0x260>
    445f:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    4467:	4a 8d 04 12          	lea    (%rdx,%r10,1),%rax
    446b:	48 89 44 24 e0       	mov    %rax,-0x20(%rsp)
    4470:	49 89 c3             	mov    %rax,%r11
    4473:	48 8d 04 ea          	lea    (%rdx,%rbp,8),%rax
    4477:	48 39 44 24 e8       	cmp    %rax,-0x18(%rsp)
    447c:	0f 83 ce 00 00 00    	jae    4550 <sendm.part.0+0x1c0>
    4482:	4c 89 d8             	mov    %r11,%rax
    4485:	4c 8b 5c 24 f0       	mov    -0x10(%rsp),%r11
    448a:	48 89 ce             	mov    %rcx,%rsi
    448d:	4c 39 d8             	cmp    %r11,%rax
    4490:	0f 83 ba 00 00 00    	jae    4550 <sendm.part.0+0x1c0>
    4496:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    44a0:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    44a7:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    44ab:	48 83 c6 01          	add    $0x1,%rsi
    44af:	48 39 f5             	cmp    %rsi,%rbp
    44b2:	7f ec                	jg     44a0 <sendm.part.0+0x110>
    44b4:	0f 1f 40 00          	nopl   0x0(%rax)
    44b8:	31 f6                	xor    %esi,%esi
    44ba:	45 84 ed             	test   %r13b,%r13b
    44bd:	4c 8b 5c 24 d0       	mov    -0x30(%rsp),%r11
    44c2:	48 0f 45 f3          	cmovne %rbx,%rsi
    44c6:	4d 8d 5c 33 01       	lea    0x1(%r11,%rsi,1),%r11
    44cb:	48 8d 4c 31 01       	lea    0x1(%rcx,%rsi,1),%rcx
    44d0:	4d 89 9e 08 01 00 00 	mov    %r11,0x108(%r14)
    44d7:	4c 8b 5c 24 d8       	mov    -0x28(%rsp),%r11
    44dc:	4d 8d 5c 33 01       	lea    0x1(%r11,%rsi,1),%r11
    44e1:	4d 89 58 10          	mov    %r11,0x10(%r8)
    44e5:	48 89 8f 80 00 00 00 	mov    %rcx,0x80(%rdi)
    44ec:	48 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%rcx
    44f4:	bb 00 00 00 00       	mov    $0x0,%ebx
    44f9:	48 0f 44 cb          	cmove  %rbx,%rcx
    44fd:	4c 01 d2             	add    %r10,%rdx
    4500:	48 89 04 0a          	mov    %rax,(%rdx,%rcx,1)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4504:	41 83 f9 02          	cmp    $0x2,%r9d
    4508:	0f 84 c2 00 00 00    	je     45d0 <sendm.part.0+0x240>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    450e:	8b 44 24 c8          	mov    -0x38(%rsp),%eax
    4512:	41 83 c7 01          	add    $0x1,%r15d
    4516:	49 83 c4 28          	add    $0x28,%r12
    451a:	41 39 c7             	cmp    %eax,%r15d
    451d:	0f 85 bd fe ff ff    	jne    43e0 <sendm.part.0+0x50>
      asm volatile ("sfence" ::: "memory");
    4523:	0f ae f8             	sfence
}
    4526:	5b                   	pop    %rbx
    4527:	5d                   	pop    %rbp
    4528:	41 5c                	pop    %r12
    452a:	41 5d                	pop    %r13
    452c:	41 5e                	pop    %r14
    452e:	41 5f                	pop    %r15
    4530:	c3                   	ret
    4531:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4538:	8b 87 00 01 00 00    	mov    0x100(%rdi),%eax
    453e:	83 f8 01             	cmp    $0x1,%eax
    4541:	0f 84 b9 00 00 00    	je     4600 <sendm.part.0+0x270>
        else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    4547:	85 c0                	test   %eax,%eax
    4549:	74 c3                	je     450e <sendm.part.0+0x17e>
    454b:	e9 b7 fe ff ff       	jmp    4407 <sendm.part.0+0x77>
    4550:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    4555:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    455c:	48 8b 74 24 e0       	mov    -0x20(%rsp),%rsi
    4561:	49 d1 eb             	shr    %r11
    4564:	66 48 0f 6e c0       	movq   %rax,%xmm0
    4569:	4c 89 dd             	mov    %r11,%rbp
    456c:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    4570:	48 c1 e5 04          	shl    $0x4,%rbp
    4574:	49 89 eb             	mov    %rbp,%r11
    4577:	48 01 f5             	add    %rsi,%rbp
    457a:	41 83 e3 10          	and    $0x10,%r11d
    457e:	74 11                	je     4591 <sendm.part.0+0x201>
          them->messages[them->messages_count++] = data->message; 
    4580:	0f 11 06             	movups %xmm0,(%rsi)
        for (; them->messages_count < min;) {
    4583:	48 83 c6 10          	add    $0x10,%rsi
    4587:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    458c:	48 39 f5             	cmp    %rsi,%rbp
    458f:	74 1a                	je     45ab <sendm.part.0+0x21b>
    4591:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
          them->messages[them->messages_count++] = data->message; 
    4596:	0f 11 06             	movups %xmm0,(%rsi)
    4599:	48 83 c6 20          	add    $0x20,%rsi
    459d:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
        for (; them->messages_count < min;) {
    45a1:	48 39 f5             	cmp    %rsi,%rbp
    45a4:	75 f0                	jne    4596 <sendm.part.0+0x206>
    45a6:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    45ab:	4c 89 de             	mov    %r11,%rsi
    45ae:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    45b2:	48 01 ce             	add    %rcx,%rsi
    45b5:	41 83 e3 01          	and    $0x1,%r11d
    45b9:	0f 84 f9 fe ff ff    	je     44b8 <sendm.part.0+0x128>
          them->messages[them->messages_count++] = data->message; 
    45bf:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    45c6:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    45ca:	e9 e9 fe ff ff       	jmp    44b8 <sendm.part.0+0x128>
    45cf:	90                   	nop
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    45d0:	83 bf 00 01 00 00 01 	cmpl   $0x1,0x100(%rdi)
    45d7:	0f 85 31 ff ff ff    	jne    450e <sendm.part.0+0x17e>
          them->available = 0;
    45dd:	c7 87 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdi)
    45e7:	e9 22 ff ff ff       	jmp    450e <sendm.part.0+0x17e>
    45ec:	0f 1f 40 00          	nopl   0x0(%rax)
          them->messages[them->messages_count++] = data->message; 
    45f0:	48 89 ce             	mov    %rcx,%rsi
    45f3:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    45fb:	e9 a0 fe ff ff       	jmp    44a0 <sendm.part.0+0x110>
        for (; them->messages_count < min;) {
    4600:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    4607:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    460e:	48 39 cd             	cmp    %rcx,%rbp
    4611:	0f 8f 07 fe ff ff    	jg     441e <sendm.part.0+0x8e>
    4617:	eb c4                	jmp    45dd <sendm.part.0+0x24d>
    4619:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004620 <strtolower>:
void strtolower(char *str) {
    4620:	f3 0f 1e fa          	endbr64
    4624:	55                   	push   %rbp
    4625:	53                   	push   %rbx
    4626:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    462a:	48 0f be 1f          	movsbq (%rdi),%rbx
    462e:	84 db                	test   %bl,%bl
    4630:	74 24                	je     4656 <strtolower+0x36>
    4632:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4635:	e8 d6 de ff ff       	call   2510 <__ctype_tolower_loc@plt>
    463a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4640:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4643:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4647:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    464a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    464d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4652:	84 db                	test   %bl,%bl
    4654:	75 ea                	jne    4640 <strtolower+0x20>
}
    4656:	48 83 c4 08          	add    $0x8,%rsp
    465a:	5b                   	pop    %rbx
    465b:	5d                   	pop    %rbp
    465c:	c3                   	ret
    465d:	0f 1f 00             	nopl   (%rax)

0000000000004660 <zh_malloc>:
void *zh_malloc(size_t size) {
    4660:	f3 0f 1e fa          	endbr64
    4664:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4668:	e8 a3 dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    466d:	48 85 c0             	test   %rax,%rax
    4670:	74 05                	je     4677 <zh_malloc+0x17>
}
    4672:	48 83 c4 08          	add    $0x8,%rsp
    4676:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4677:	48 8b 0d a2 59 00 00 	mov    0x59a2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    467e:	ba 28 00 00 00       	mov    $0x28,%edx
    4683:	be 01 00 00 00       	mov    $0x1,%esi
    4688:	48 8d 3d 99 2e 00 00 	lea    0x2e99(%rip),%rdi        # 7528 <_IO_stdin_used+0x528>
    468f:	e8 2c de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4694:	bf 01 00 00 00       	mov    $0x1,%edi
    4699:	e8 02 de ff ff       	call   24a0 <exit@plt>
    469e:	66 90                	xchg   %ax,%ax

00000000000046a0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    46a0:	f3 0f 1e fa          	endbr64
    46a4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    46a5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    46aa:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    46ad:	e8 ae dc ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    46b2:	48 85 c0             	test   %rax,%rax
    46b5:	74 11                	je     46c8 <get_filename_ext+0x28>
    46b7:	48 39 c3             	cmp    %rax,%rbx
    46ba:	74 0c                	je     46c8 <get_filename_ext+0x28>
    return dot + 1;
    46bc:	48 83 c0 01          	add    $0x1,%rax
}
    46c0:	5b                   	pop    %rbx
    46c1:	c3                   	ret
    46c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    46c8:	48 8d 05 21 2a 00 00 	lea    0x2a21(%rip),%rax        # 70f0 <_IO_stdin_used+0xf0>
}
    46cf:	5b                   	pop    %rbx
    46d0:	c3                   	ret
    46d1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    46dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000046e0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    46e0:	f3 0f 1e fa          	endbr64
    46e4:	41 55                	push   %r13
    46e6:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    46e9:	48 89 fe             	mov    %rdi,%rsi
    46ec:	41 54                	push   %r12
    46ee:	55                   	push   %rbp
    46ef:	48 89 d5             	mov    %rdx,%rbp
    46f2:	ba 00 04 00 00       	mov    $0x400,%edx
    46f7:	53                   	push   %rbx
    46f8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    46ff:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4708:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4710:	31 c0                	xor    %eax,%eax
    4712:	49 89 e4             	mov    %rsp,%r12
    4715:	4c 89 e7             	mov    %r12,%rdi
    4718:	e8 13 dd ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    471d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4722:	84 db                	test   %bl,%bl
    4724:	74 24                	je     474a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4726:	e8 e5 dd ff ff       	call   2510 <__ctype_tolower_loc@plt>
    472b:	48 8b 08             	mov    (%rax),%rcx
    472e:	4c 89 e0             	mov    %r12,%rax
    4731:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4738:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    473b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    473f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4742:	48 0f be 18          	movsbq (%rax),%rbx
    4746:	84 db                	test   %bl,%bl
    4748:	75 ee                	jne    4738 <send_headers+0x58>
    void *buf = malloc(size);
    474a:	bf 11 00 00 00       	mov    $0x11,%edi
    474f:	e8 bc dc ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4754:	48 85 c0             	test   %rax,%rax
    4757:	0f 84 7e 04 00 00    	je     4bdb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    475d:	66 0f 6f 05 bb 33 00 00 	movdqa 0x33bb(%rip),%xmm0        # 7b20 <_IO_stdin_used+0xb20>
    iov[0].iov_base = zh_malloc(slen);
    4765:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4769:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    476e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4776:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    477a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    477d:	e8 8e dc ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4782:	48 85 c0             	test   %rax,%rax
    4785:	0f 84 50 04 00 00    	je     4bdb <send_headers+0x4fb>
    478b:	66 0f 6f 05 9d 33 00 00 	movdqa 0x339d(%rip),%xmm0        # 7b30 <_IO_stdin_used+0xb30>
    iov[1].iov_base = zh_malloc(slen);
    4793:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4797:	4c 89 e7             	mov    %r12,%rdi
    479a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    47a4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    47ac:	0f 11 00             	movups %xmm0,(%rax)
    47af:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    47b3:	be 2e 00 00 00       	mov    $0x2e,%esi
    47b8:	e8 a3 db ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    47bd:	48 85 c0             	test   %rax,%rax
    47c0:	0f 84 ea 02 00 00    	je     4ab0 <send_headers+0x3d0>
    47c6:	4c 39 e0             	cmp    %r12,%rax
    47c9:	0f 84 e1 02 00 00    	je     4ab0 <send_headers+0x3d0>
    return dot + 1;
    47cf:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    47d3:	48 8d 3d e4 28 00 00 	lea    0x28e4(%rip),%rdi        # 70be <_IO_stdin_used+0xbe>
    47da:	48 89 de             	mov    %rbx,%rsi
    47dd:	e8 ce db ff ff       	call   23b0 <strcmp@plt>
    47e2:	85 c0                	test   %eax,%eax
    47e4:	75 20                	jne    4806 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    47e6:	66 0f 6f 05 52 33 00 00 	movdqa 0x3352(%rip),%xmm0        # 7b40 <_IO_stdin_used+0xb40>
    47ee:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    47f6:	66 0f 6f 05 52 33 00 00 	movdqa 0x3352(%rip),%xmm0        # 7b50 <_IO_stdin_used+0xb50>
    47fe:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4806:	48 89 de             	mov    %rbx,%rsi
    4809:	48 8d 3d b2 28 00 00 	lea    0x28b2(%rip),%rdi        # 70c2 <_IO_stdin_used+0xc2>
    4810:	e8 9b db ff ff       	call   23b0 <strcmp@plt>
    4815:	85 c0                	test   %eax,%eax
    4817:	75 20                	jne    4839 <send_headers+0x159>
    4819:	66 0f 6f 05 1f 33 00 00 	movdqa 0x331f(%rip),%xmm0        # 7b40 <_IO_stdin_used+0xb40>
    4821:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4829:	66 0f 6f 05 1f 33 00 00 	movdqa 0x331f(%rip),%xmm0        # 7b50 <_IO_stdin_used+0xb50>
    4831:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4839:	48 89 de             	mov    %rbx,%rsi
    483c:	48 8d 3d 84 28 00 00 	lea    0x2884(%rip),%rdi        # 70c7 <_IO_stdin_used+0xc7>
    4843:	e8 68 db ff ff       	call   23b0 <strcmp@plt>
    4848:	85 c0                	test   %eax,%eax
    484a:	0f 84 10 02 00 00    	je     4a60 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4850:	48 89 de             	mov    %rbx,%rsi
    4853:	48 8d 3d 71 28 00 00 	lea    0x2871(%rip),%rdi        # 70cb <_IO_stdin_used+0xcb>
    485a:	e8 51 db ff ff       	call   23b0 <strcmp@plt>
    485f:	85 c0                	test   %eax,%eax
    4861:	0f 84 a9 02 00 00    	je     4b10 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4867:	48 89 de             	mov    %rbx,%rsi
    486a:	48 8d 3d 5e 28 00 00 	lea    0x285e(%rip),%rdi        # 70cf <_IO_stdin_used+0xcf>
    4871:	e8 3a db ff ff       	call   23b0 <strcmp@plt>
    4876:	85 c0                	test   %eax,%eax
    4878:	0f 84 6a 02 00 00    	je     4ae8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    487e:	48 89 de             	mov    %rbx,%rsi
    4881:	48 8d 3d 8a 28 00 00 	lea    0x288a(%rip),%rdi        # 7112 <_IO_stdin_used+0x112>
    4888:	e8 23 db ff ff       	call   23b0 <strcmp@plt>
    488d:	85 c0                	test   %eax,%eax
    488f:	0f 84 2b 02 00 00    	je     4ac0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4895:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4898:	0f 84 52 01 00 00    	je     49f0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    489e:	48 89 de             	mov    %rbx,%rsi
    48a1:	48 8d 3d 2b 28 00 00 	lea    0x282b(%rip),%rdi        # 70d3 <_IO_stdin_used+0xd3>
    48a8:	e8 03 db ff ff       	call   23b0 <strcmp@plt>
    48ad:	85 c0                	test   %eax,%eax
    48af:	0f 84 ab 02 00 00    	je     4b60 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    48b5:	48 89 de             	mov    %rbx,%rsi
    48b8:	48 8d 3d 18 28 00 00 	lea    0x2818(%rip),%rdi        # 70d7 <_IO_stdin_used+0xd7>
    48bf:	e8 ec da ff ff       	call   23b0 <strcmp@plt>
    48c4:	85 c0                	test   %eax,%eax
    48c6:	0f 84 6c 02 00 00    	je     4b38 <send_headers+0x458>
    slen = strlen(send_buffer);
    48cc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    48d4:	4c 89 e7             	mov    %r12,%rdi
    48d7:	e8 44 da ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    48dc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    48df:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    48e2:	e8 29 db ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    48e7:	48 85 c0             	test   %rax,%rax
    48ea:	0f 84 eb 02 00 00    	je     4bdb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    48f0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    48f4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    48f8:	83 fb 08             	cmp    $0x8,%ebx
    48fb:	0f 83 3f 01 00 00    	jae    4a40 <send_headers+0x360>
    4901:	f6 c3 04             	test   $0x4,%bl
    4904:	0f 85 7b 02 00 00    	jne    4b85 <send_headers+0x4a5>
    490a:	85 db                	test   %ebx,%ebx
    490c:	74 13                	je     4921 <send_headers+0x241>
    490e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4916:	88 10                	mov    %dl,(%rax)
    4918:	f6 c3 02             	test   $0x2,%bl
    491b:	0f 85 96 02 00 00    	jne    4bb7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4921:	4d 89 e8             	mov    %r13,%r8
    4924:	48 8d 0d b0 27 00 00 	lea    0x27b0(%rip),%rcx        # 70db <_IO_stdin_used+0xdb>
    492b:	4c 89 e7             	mov    %r12,%rdi
    492e:	31 c0                	xor    %eax,%eax
    4930:	ba 00 04 00 00       	mov    $0x400,%edx
    4935:	be 01 00 00 00       	mov    $0x1,%esi
    493a:	e8 e1 db ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    493f:	4c 89 e7             	mov    %r12,%rdi
    4942:	e8 d9 d9 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4947:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    494a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    494d:	e8 be da ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4952:	48 85 c0             	test   %rax,%rax
    4955:	0f 84 80 02 00 00    	je     4bdb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    495b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    495f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4963:	83 fb 08             	cmp    $0x8,%ebx
    4966:	0f 83 1c 01 00 00    	jae    4a88 <send_headers+0x3a8>
    496c:	f6 c3 04             	test   $0x4,%bl
    496f:	0f 85 29 02 00 00    	jne    4b9e <send_headers+0x4be>
    4975:	85 db                	test   %ebx,%ebx
    4977:	74 13                	je     498c <send_headers+0x2ac>
    4979:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4981:	88 10                	mov    %dl,(%rax)
    4983:	f6 c3 02             	test   $0x2,%bl
    4986:	0f 85 3d 02 00 00    	jne    4bc9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    498c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4991:	bf 02 00 00 00       	mov    $0x2,%edi
    4996:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    499e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    49a6:	e8 65 da ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    49ab:	48 85 c0             	test   %rax,%rax
    49ae:	0f 84 27 02 00 00    	je     4bdb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    49b4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    49bc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    49c0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    49c8:	66 89 10             	mov    %dx,(%rax)
}
    49cb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    49d3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    49dc:	0f 85 20 02 00 00    	jne    4c02 <send_headers+0x522>
    49e2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    49e9:	5b                   	pop    %rbx
    49ea:	5d                   	pop    %rbp
    49eb:	41 5c                	pop    %r12
    49ed:	41 5d                	pop    %r13
    49ef:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    49f0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    49f4:	0f 85 a4 fe ff ff    	jne    489e <send_headers+0x1be>
    49fa:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    49fe:	0f 85 9a fe ff ff    	jne    489e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a04:	66 0f 6f 05 94 31 00 00 	movdqa 0x3194(%rip),%xmm0        # 7ba0 <_IO_stdin_used+0xba0>
    4a0c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4a16:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a1e:	66 0f 6f 05 8a 31 00 00 	movdqa 0x318a(%rip),%xmm0        # 7bb0 <_IO_stdin_used+0xbb0>
    4a26:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4a2e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4a36:	e9 63 fe ff ff       	jmp    489e <send_headers+0x1be>
    4a3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4a40:	89 da                	mov    %ebx,%edx
    4a42:	48 89 c7             	mov    %rax,%rdi
    4a45:	4c 89 e6             	mov    %r12,%rsi
    4a48:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4a4d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4a52:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4a55:	c1 e9 03             	shr    $0x3,%ecx
    4a58:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4a5b:	e9 c1 fe ff ff       	jmp    4921 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a60:	66 0f 6f 05 d8 30 00 00 	movdqa 0x30d8(%rip),%xmm0        # 7b40 <_IO_stdin_used+0xb40>
    4a68:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a70:	66 0f 6f 05 e8 30 00 00 	movdqa 0x30e8(%rip),%xmm0        # 7b60 <_IO_stdin_used+0xb60>
    4a78:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a80:	e9 cb fd ff ff       	jmp    4850 <send_headers+0x170>
    4a85:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4a88:	89 da                	mov    %ebx,%edx
    4a8a:	48 89 c7             	mov    %rax,%rdi
    4a8d:	4c 89 e6             	mov    %r12,%rsi
    4a90:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4a95:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4a9a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4a9d:	c1 e9 03             	shr    $0x3,%ecx
    4aa0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4aa3:	e9 e4 fe ff ff       	jmp    498c <send_headers+0x2ac>
    4aa8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4ab0:	48 8d 1d 39 26 00 00 	lea    0x2639(%rip),%rbx        # 70f0 <_IO_stdin_used+0xf0>
    4ab7:	e9 94 fd ff ff       	jmp    4850 <send_headers+0x170>
    4abc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ac0:	66 0f 6f 05 b8 30 00 00 	movdqa 0x30b8(%rip),%xmm0        # 7b80 <_IO_stdin_used+0xb80>
    4ac8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ad0:	66 0f 6f 05 b8 30 00 00 	movdqa 0x30b8(%rip),%xmm0        # 7b90 <_IO_stdin_used+0xb90>
    4ad8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4ae0:	e9 b0 fd ff ff       	jmp    4895 <send_headers+0x1b5>
    4ae5:	0f 1f 00             	nopl   (%rax)
    4ae8:	66 0f 6f 05 90 30 00 00 	movdqa 0x3090(%rip),%xmm0        # 7b80 <_IO_stdin_used+0xb80>
    4af0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4af8:	66 0f 6f 05 90 30 00 00 	movdqa 0x3090(%rip),%xmm0        # 7b90 <_IO_stdin_used+0xb90>
    4b00:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4b08:	e9 71 fd ff ff       	jmp    487e <send_headers+0x19e>
    4b0d:	0f 1f 00             	nopl   (%rax)
    4b10:	66 0f 6f 05 28 30 00 00 	movdqa 0x3028(%rip),%xmm0        # 7b40 <_IO_stdin_used+0xb40>
    4b18:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b20:	66 0f 6f 05 48 30 00 00 	movdqa 0x3048(%rip),%xmm0        # 7b70 <_IO_stdin_used+0xb70>
    4b28:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4b30:	e9 32 fd ff ff       	jmp    4867 <send_headers+0x187>
    4b35:	0f 1f 00             	nopl   (%rax)
    4b38:	66 0f 6f 05 40 30 00 00 	movdqa 0x3040(%rip),%xmm0        # 7b80 <_IO_stdin_used+0xb80>
    4b40:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b48:	66 0f 6f 05 80 30 00 00 	movdqa 0x3080(%rip),%xmm0        # 7bd0 <_IO_stdin_used+0xbd0>
    4b50:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4b58:	e9 6f fd ff ff       	jmp    48cc <send_headers+0x1ec>
    4b5d:	0f 1f 00             	nopl   (%rax)
    4b60:	66 0f 6f 05 18 30 00 00 	movdqa 0x3018(%rip),%xmm0        # 7b80 <_IO_stdin_used+0xb80>
    4b68:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b70:	66 0f 6f 05 48 30 00 00 	movdqa 0x3048(%rip),%xmm0        # 7bc0 <_IO_stdin_used+0xbc0>
    4b78:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4b80:	e9 30 fd ff ff       	jmp    48b5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4b85:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4b8c:	89 db                	mov    %ebx,%ebx
    4b8e:	89 10                	mov    %edx,(%rax)
    4b90:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4b95:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4b99:	e9 83 fd ff ff       	jmp    4921 <send_headers+0x241>
    4b9e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4ba5:	89 db                	mov    %ebx,%ebx
    4ba7:	89 10                	mov    %edx,(%rax)
    4ba9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4bae:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4bb2:	e9 d5 fd ff ff       	jmp    498c <send_headers+0x2ac>
    4bb7:	89 db                	mov    %ebx,%ebx
    4bb9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4bbf:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4bc4:	e9 58 fd ff ff       	jmp    4921 <send_headers+0x241>
    4bc9:	89 db                	mov    %ebx,%ebx
    4bcb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4bd1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4bd6:	e9 b1 fd ff ff       	jmp    498c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4bdb:	48 8b 0d 3e 54 00 00 	mov    0x543e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4be2:	ba 28 00 00 00       	mov    $0x28,%edx
    4be7:	be 01 00 00 00       	mov    $0x1,%esi
    4bec:	48 8d 3d 35 29 00 00 	lea    0x2935(%rip),%rdi        # 7528 <_IO_stdin_used+0x528>
    4bf3:	e8 c8 d8 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4bf8:	bf 01 00 00 00       	mov    $0x1,%edi
    4bfd:	e8 9e d8 ff ff       	call   24a0 <exit@plt>
}
    4c02:	e8 29 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
    4c07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004c10 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4c10:	f3 0f 1e fa          	endbr64
    4c14:	41 55                	push   %r13
    4c16:	49 89 d5             	mov    %rdx,%r13
    4c19:	41 54                	push   %r12
    4c1b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    4c1e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4c21:	55                   	push   %rbp
    4c22:	53                   	push   %rbx
    4c23:	48 89 f3             	mov    %rsi,%rbx
    4c26:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4c2a:	e8 e1 d7 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4c2f:	48 85 c0             	test   %rax,%rax
    4c32:	74 6b                	je     4c9f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4c34:	4c 89 e7             	mov    %r12,%rdi
    4c37:	48 89 c5             	mov    %rax,%rbp
    4c3a:	31 f6                	xor    %esi,%esi
    4c3c:	31 c0                	xor    %eax,%eax
    4c3e:	e8 3d d8 ff ff       	call   2480 <open@plt>
    4c43:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4c46:	85 c0                	test   %eax,%eax
    4c48:	0f 88 08 d9 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4c4e:	48 89 da             	mov    %rbx,%rdx
    4c51:	48 89 ee             	mov    %rbp,%rsi
    4c54:	89 c7                	mov    %eax,%edi
    4c56:	e8 35 d7 ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    4c5b:	48 98                	cltq
    4c5d:	48 39 d8             	cmp    %rbx,%rax
    4c60:	7c 1e                	jl     4c80 <copy_file_contents+0x70>
    close(fd);
    4c62:	44 89 e7             	mov    %r12d,%edi
    4c65:	e8 06 d7 ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    4c6a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    4c6e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4c72:	48 83 c4 08          	add    $0x8,%rsp
    4c76:	5b                   	pop    %rbx
    4c77:	5d                   	pop    %rbp
    4c78:	41 5c                	pop    %r12
    4c7a:	41 5d                	pop    %r13
    4c7c:	c3                   	ret
    4c7d:	0f 1f 00             	nopl   (%rax)
    4c80:	48 8b 0d 99 53 00 00 	mov    0x5399(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c87:	ba 1a 00 00 00       	mov    $0x1a,%edx
    4c8c:	be 01 00 00 00       	mov    $0x1,%esi
    4c91:	48 8d 3d 59 24 00 00 	lea    0x2459(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4c98:	e8 23 d8 ff ff       	call   24c0 <fwrite@plt>
    4c9d:	eb c3                	jmp    4c62 <copy_file_contents+0x52>
    4c9f:	48 8b 0d 7a 53 00 00 	mov    0x537a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4ca6:	ba 28 00 00 00       	mov    $0x28,%edx
    4cab:	be 01 00 00 00       	mov    $0x1,%esi
    4cb0:	48 8d 3d 71 28 00 00 	lea    0x2871(%rip),%rdi        # 7528 <_IO_stdin_used+0x528>
    4cb7:	e8 04 d8 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4cbc:	bf 01 00 00 00       	mov    $0x1,%edi
    4cc1:	e8 da d7 ff ff       	call   24a0 <exit@plt>
    4cc6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004cd0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4cd0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4cd4:	8b 46 44             	mov    0x44(%rsi),%eax
    4cd7:	48 89 fa             	mov    %rdi,%rdx
    4cda:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    4cdd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4ce3:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4ce6:	48 8b 07             	mov    (%rdi),%rax
    4ce9:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4cec:	f6 c1 02             	test   $0x2,%cl
    4cef:	74 00                	je     4cf1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4cf1:	89 f0                	mov    %esi,%eax
    4cf3:	44 29 c0             	sub    %r8d,%eax
    4cf6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4cf9:	0f 82 63 d8 ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4cff:	c1 e9 0a             	shr    $0xa,%ecx
    4d02:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d06:	8b 47 44             	mov    0x44(%rdi),%eax
    4d09:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4d0c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4d0f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4d12:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4d15:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d19:	d3 e0                	shl    %cl,%eax
    4d1b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    4d1e:	48 c1 e0 06          	shl    $0x6,%rax
    4d22:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4d26:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    4d2c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4d2f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4d33:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4d39:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4d41:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4d45:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4d48:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4d4f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4d57:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    4d5b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    4d5f:	e8 dc d5 ff ff       	call   2340 <io_uring_submit@plt>
}
    4d64:	31 c0                	xor    %eax,%eax
    4d66:	48 83 c4 08          	add    $0x8,%rsp
    4d6a:	c3                   	ret
    4d6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004d70 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4d70:	f3 0f 1e fa          	endbr64
    4d74:	41 55                	push   %r13
    4d76:	41 89 fd             	mov    %edi,%r13d
    4d79:	41 54                	push   %r12
    4d7b:	55                   	push   %rbp
    4d7c:	53                   	push   %rbx
    4d7d:	48 89 f3             	mov    %rsi,%rbx
    4d80:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4d84:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4d87:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    4d8d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4d90:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4d93:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4d95:	f6 c1 02             	test   $0x2,%cl
    4d98:	74 00                	je     4d9a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    4d9a:	89 c2                	mov    %eax,%edx
    4d9c:	29 f2                	sub    %esi,%edx
    4d9e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4da1:	0f 82 cb d7 ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4da7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    4daa:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    4dad:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4db0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4db5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4db8:	23 6b 58             	and    0x58(%rbx),%ebp
    4dbb:	d3 e5                	shl    %cl,%ebp
    4dbd:	48 c1 e5 06          	shl    $0x6,%rbp
    4dc1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4dc5:	e8 46 d6 ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    4dca:	be 01 00 00 00       	mov    $0x1,%esi
    4dcf:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4dd4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4dd7:	e8 c4 d5 ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    4ddc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4de1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4de5:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4de8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4ded:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4df2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    4dfb:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4e03:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4e07:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    4e0b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4e12:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4e1a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    4e1e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4e26:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    4e2e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4e32:	e8 09 d5 ff ff       	call   2340 <io_uring_submit@plt>
}
    4e37:	48 83 c4 08          	add    $0x8,%rsp
    4e3b:	31 c0                	xor    %eax,%eax
    4e3d:	5b                   	pop    %rbx
    4e3e:	5d                   	pop    %rbp
    4e3f:	41 5c                	pop    %r12
    4e41:	41 5d                	pop    %r13
    4e43:	c3                   	ret
    4e44:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4e4f:	90                   	nop

0000000000004e50 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4e50:	f3 0f 1e fa          	endbr64
    4e54:	41 56                	push   %r14
    4e56:	41 89 f6             	mov    %esi,%r14d
    4e59:	41 55                	push   %r13
    4e5b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    4e5e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4e63:	41 54                	push   %r12
    4e65:	55                   	push   %rbp
    4e66:	48 89 d5             	mov    %rdx,%rbp
    4e69:	53                   	push   %rbx
    void *buf = malloc(size);
    4e6a:	e8 a1 d5 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4e6f:	48 85 c0             	test   %rax,%rax
    4e72:	0f 84 dd 00 00 00    	je     4f55 <_send_static_string_content+0x105>
    4e78:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    4e7b:	4c 89 ef             	mov    %r13,%rdi
    4e7e:	e8 9d d4 ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4e83:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    4e8a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    4e8e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4e91:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4e94:	e8 77 d5 ff ff       	call   2410 <malloc@plt>
    4e99:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    4e9c:	48 85 c0             	test   %rax,%rax
    4e9f:	0f 84 b0 00 00 00    	je     4f55 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4ea5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4ea9:	4c 89 e2             	mov    %r12,%rdx
    4eac:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    4eaf:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4eb3:	e8 28 d5 ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4eb8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4ebb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4ec1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4ec4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4ec8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4eca:	f6 c1 02             	test   $0x2,%cl
    4ecd:	0f 85 7d 00 00 00    	jne    4f50 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4ed3:	89 d0                	mov    %edx,%eax
    4ed5:	29 f0                	sub    %esi,%eax
    4ed7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    4eda:	0f 82 9c d6 ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4ee0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ee3:	8b 45 44             	mov    0x44(%rbp),%eax
    4ee6:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4ee9:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    4eec:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4eef:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4ef2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4ef8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4efc:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4efe:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4f01:	48 89 ef             	mov    %rbp,%rdi
    4f04:	48 c1 e0 06          	shl    $0x6,%rax
    4f08:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    4f0c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4f0f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4f13:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4f19:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4f21:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4f25:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4f28:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4f2f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4f37:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    4f3b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    4f3f:	5b                   	pop    %rbx
    4f40:	5d                   	pop    %rbp
    4f41:	41 5c                	pop    %r12
    4f43:	41 5d                	pop    %r13
    4f45:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4f47:	e9 f4 d3 ff ff       	jmp    2340 <io_uring_submit@plt>
    4f4c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4f50:	e9 7e ff ff ff       	jmp    4ed3 <_send_static_string_content+0x83>
    4f55:	48 8b 0d c4 50 00 00 	mov    0x50c4(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4f5c:	ba 28 00 00 00       	mov    $0x28,%edx
    4f61:	be 01 00 00 00       	mov    $0x1,%esi
    4f66:	48 8d 3d bb 25 00 00 	lea    0x25bb(%rip),%rdi        # 7528 <_IO_stdin_used+0x528>
    4f6d:	e8 4e d5 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4f72:	bf 01 00 00 00       	mov    $0x1,%edi
    4f77:	e8 24 d5 ff ff       	call   24a0 <exit@plt>
    4f7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004f80 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4f80:	f3 0f 1e fa          	endbr64
    4f84:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4f87:	89 fe                	mov    %edi,%esi
    4f89:	48 8b 3d 88 50 00 00 	mov    0x5088(%rip),%rdi        # a018 <unimplemented_content>
    4f90:	e9 bb fe ff ff       	jmp    4e50 <_send_static_string_content>
    4f95:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004fa0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4fa0:	f3 0f 1e fa          	endbr64
    4fa4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4fa7:	89 fe                	mov    %edi,%esi
    4fa9:	48 8b 3d 60 50 00 00 	mov    0x5060(%rip),%rdi        # a010 <http_404_content>
    4fb0:	e9 9b fe ff ff       	jmp    4e50 <_send_static_string_content>
    4fb5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004fc0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4fc0:	f3 0f 1e fa          	endbr64
    4fc4:	41 56                	push   %r14
    4fc6:	41 55                	push   %r13
    4fc8:	49 89 d5             	mov    %rdx,%r13
    4fcb:	41 54                	push   %r12
    4fcd:	41 89 f4             	mov    %esi,%r12d
    4fd0:	55                   	push   %rbp
    4fd1:	48 89 fd             	mov    %rdi,%rbp
    4fd4:	53                   	push   %rbx
    4fd5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    4fdc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4fe5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    4fed:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    4fef:	e8 2c d3 ff ff       	call   2320 <strlen@plt>
    4ff4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4ff9:	48 89 c3             	mov    %rax,%rbx
    4ffc:	0f 84 b6 00 00 00    	je     50b8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5002:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5007:	48 89 ee             	mov    %rbp,%rsi
    500a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    500e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5013:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    501b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5023:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    502e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5036:	e8 85 d3 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    503b:	48 89 e6             	mov    %rsp,%rsi
    503e:	4c 89 f7             	mov    %r14,%rdi
    5041:	e8 8a d3 ff ff       	call   23d0 <stat@plt>
    5046:	83 f8 ff             	cmp    $0xffffffff,%eax
    5049:	0f 84 d3 00 00 00    	je     5122 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    504f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5053:	25 00 f0 00 00       	and    $0xf000,%eax
    5058:	3d 00 80 00 00       	cmp    $0x8000,%eax
    505d:	0f 84 f5 00 00 00    	je     5158 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    5063:	48 8b 3d a6 4f 00 00 	mov    0x4fa6(%rip),%rdi        # a010 <http_404_content>
    506a:	4c 89 ea             	mov    %r13,%rdx
    506d:	44 89 e6             	mov    %r12d,%esi
    5070:	e8 db fd ff ff       	call   4e50 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5075:	4c 89 f2             	mov    %r14,%rdx
    5078:	bf 01 00 00 00       	mov    $0x1,%edi
    507d:	31 c0                	xor    %eax,%eax
    507f:	48 8d 35 bb 20 00 00 	lea    0x20bb(%rip),%rsi        # 7141 <_IO_stdin_used+0x141>
    5086:	e8 c5 d3 ff ff       	call   2450 <__printf_chk@plt>
}
    508b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5093:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    509c:	0f 85 20 01 00 00    	jne    51c2 <handle_get_method+0x202>
    50a2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    50a9:	5b                   	pop    %rbx
    50aa:	5d                   	pop    %rbp
    50ab:	41 5c                	pop    %r12
    50ad:	41 5d                	pop    %r13
    50af:	41 5e                	pop    %r14
    50b1:	c3                   	ret
    50b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    50b8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    50bd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    50c5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    50ca:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    50cd:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    50d5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    50d8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    50e0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    50eb:	e8 d0 d2 ff ff       	call   23c0 <__memcpy_chk@plt>
    50f0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    50f5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    50fa:	48 8d 35 0b 20 00 00 	lea    0x200b(%rip),%rsi        # 710c <_IO_stdin_used+0x10c>
    5101:	48 29 d9             	sub    %rbx,%rcx
    5104:	ba 0b 00 00 00       	mov    $0xb,%edx
    5109:	e8 b2 d2 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    510e:	48 89 e6             	mov    %rsp,%rsi
    5111:	4c 89 f7             	mov    %r14,%rdi
    5114:	e8 b7 d2 ff ff       	call   23d0 <stat@plt>
    5119:	83 f8 ff             	cmp    $0xffffffff,%eax
    511c:	0f 85 2d ff ff ff    	jne    504f <handle_get_method+0x8f>
    5122:	4c 89 f2             	mov    %r14,%rdx
    5125:	48 89 e9             	mov    %rbp,%rcx
    5128:	48 8d 35 e8 1f 00 00 	lea    0x1fe8(%rip),%rsi        # 7117 <_IO_stdin_used+0x117>
    512f:	31 c0                	xor    %eax,%eax
    5131:	bf 01 00 00 00       	mov    $0x1,%edi
    5136:	e8 15 d3 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    513b:	48 8b 3d ce 4e 00 00 	mov    0x4ece(%rip),%rdi        # a010 <http_404_content>
    5142:	4c 89 ea             	mov    %r13,%rdx
    5145:	44 89 e6             	mov    %r12d,%esi
    5148:	e8 03 fd ff ff       	call   4e50 <_send_static_string_content>
}
    514d:	e9 39 ff ff ff       	jmp    508b <handle_get_method+0xcb>
    5152:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5158:	bf 70 00 00 00       	mov    $0x70,%edi
    515d:	e8 ae d2 ff ff       	call   2410 <malloc@plt>
    5162:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5165:	48 85 c0             	test   %rax,%rax
    5168:	74 5d                	je     51c7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    516a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    516e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5173:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5177:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    517a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    5181:	e8 5a f5 ff ff       	call   46e0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5186:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    518b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    518f:	4c 89 f7             	mov    %r14,%rdi
    5192:	e8 79 fa ff ff       	call   4c10 <copy_file_contents>
    5197:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    519c:	4c 89 f2             	mov    %r14,%rdx
    519f:	31 c0                	xor    %eax,%eax
    51a1:	48 8d 35 87 1f 00 00 	lea    0x1f87(%rip),%rsi        # 712f <_IO_stdin_used+0x12f>
    51a8:	bf 01 00 00 00       	mov    $0x1,%edi
    51ad:	e8 9e d2 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    51b2:	4c 89 ee             	mov    %r13,%rsi
    51b5:	48 89 df             	mov    %rbx,%rdi
    51b8:	e8 13 fb ff ff       	call   4cd0 <add_write_request>
    51bd:	e9 c9 fe ff ff       	jmp    508b <handle_get_method+0xcb>
}
    51c2:	e8 69 d1 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    51c7:	48 8b 0d 52 4e 00 00 	mov    0x4e52(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    51ce:	ba 28 00 00 00       	mov    $0x28,%edx
    51d3:	be 01 00 00 00       	mov    $0x1,%esi
    51d8:	48 8d 3d 49 23 00 00 	lea    0x2349(%rip),%rdi        # 7528 <_IO_stdin_used+0x528>
    51df:	e8 dc d2 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    51e4:	bf 01 00 00 00       	mov    $0x1,%edi
    51e9:	e8 b2 d2 ff ff       	call   24a0 <exit@plt>
    51ee:	66 90                	xchg   %ax,%ax

00000000000051f0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    51f0:	f3 0f 1e fa          	endbr64
    51f4:	41 57                	push   %r15
    51f6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    51f8:	4c 8d 35 a7 1e 00 00 	lea    0x1ea7(%rip),%r14        # 70a6 <_IO_stdin_used+0xa6>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    51ff:	41 55                	push   %r13
    5201:	49 89 d5             	mov    %rdx,%r13
    5204:	41 54                	push   %r12
    5206:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    5209:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    520c:	55                   	push   %rbp
    520d:	53                   	push   %rbx
    520e:	48 83 ec 18          	sub    $0x18,%rsp
    5212:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    521b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5220:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5222:	49 89 e7             	mov    %rsp,%r15
    5225:	4c 89 fa             	mov    %r15,%rdx
    5228:	e8 53 d1 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    522d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    5231:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    5234:	84 db                	test   %bl,%bl
    5236:	74 1d                	je     5255 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    5238:	e8 d3 d2 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    523d:	48 89 ea             	mov    %rbp,%rdx
    5240:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    5243:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    5247:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    524a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    524d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5251:	84 db                	test   %bl,%bl
    5253:	75 eb                	jne    5240 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    5255:	4c 89 fa             	mov    %r15,%rdx
    5258:	4c 89 f6             	mov    %r14,%rsi
    525b:	31 ff                	xor    %edi,%edi
    525d:	e8 1e d1 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5262:	48 8d 35 eb 1e 00 00 	lea    0x1eeb(%rip),%rsi        # 7154 <_IO_stdin_used+0x154>
    5269:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    526c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    526f:	e8 3c d1 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    5274:	4c 89 ea             	mov    %r13,%rdx
    5277:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    527a:	85 c0                	test   %eax,%eax
    527c:	75 2a                	jne    52a8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    527e:	48 89 df             	mov    %rbx,%rdi
    5281:	e8 3a fd ff ff       	call   4fc0 <handle_get_method>
}
    5286:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    528b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5294:	75 20                	jne    52b6 <handle_http_method+0xc6>
    5296:	48 83 c4 18          	add    $0x18,%rsp
    529a:	5b                   	pop    %rbx
    529b:	5d                   	pop    %rbp
    529c:	41 5c                	pop    %r12
    529e:	41 5d                	pop    %r13
    52a0:	41 5e                	pop    %r14
    52a2:	41 5f                	pop    %r15
    52a4:	c3                   	ret
    52a5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    52a8:	48 8b 3d 69 4d 00 00 	mov    0x4d69(%rip),%rdi        # a018 <unimplemented_content>
    52af:	e8 9c fb ff ff       	call   4e50 <_send_static_string_content>
}
    52b4:	eb d0                	jmp    5286 <handle_http_method+0x96>
    52b6:	e8 75 d0 ff ff       	call   2330 <__stack_chk_fail@plt>
    52bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000052c0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    52c0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    52c4:	85 d2                	test   %edx,%edx
    52c6:	7e 38                	jle    5300 <get_line+0x40>
    52c8:	48 63 d2             	movslq %edx,%rdx
    52cb:	48 83 c7 01          	add    $0x1,%rdi
    52cf:	48 01 f2             	add    %rsi,%rdx
    52d2:	eb 11                	jmp    52e5 <get_line+0x25>
    52d4:	0f 1f 40 00          	nopl   0x0(%rax)
    52d8:	48 83 c6 01          	add    $0x1,%rsi
    52dc:	48 83 c7 01          	add    $0x1,%rdi
    52e0:	48 39 d6             	cmp    %rdx,%rsi
    52e3:	74 1b                	je     5300 <get_line+0x40>
        dest[i] = src[i];
    52e5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    52e9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    52eb:	3c 0d                	cmp    $0xd,%al
    52ed:	75 e9                	jne    52d8 <get_line+0x18>
    52ef:	80 3f 0a             	cmpb   $0xa,(%rdi)
    52f2:	75 e4                	jne    52d8 <get_line+0x18>
            dest[i] = '\0';
    52f4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    52f7:	31 c0                	xor    %eax,%eax
    52f9:	c3                   	ret
    52fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5300:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5305:	c3                   	ret
    5306:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005310 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    5310:	f3 0f 1e fa          	endbr64
    5314:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    531b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    531f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5328:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5330:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5332:	49 89 e2             	mov    %rsp,%r10
    5335:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    533d:	4c 89 d0             	mov    %r10,%rax
    5340:	eb 13                	jmp    5355 <handle_client_request+0x45>
    5342:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5348:	48 83 c0 01          	add    $0x1,%rax
    534c:	48 83 c1 01          	add    $0x1,%rcx
    5350:	4c 39 c8             	cmp    %r9,%rax
    5353:	74 4b                	je     53a0 <handle_client_request+0x90>
        dest[i] = src[i];
    5355:	44 0f b6 01          	movzbl (%rcx),%r8d
    5359:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    535c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5360:	75 e6                	jne    5348 <handle_client_request+0x38>
    5362:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5366:	75 e0                	jne    5348 <handle_client_request+0x38>
            dest[i] = '\0';
    5368:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    536b:	8b 47 08             	mov    0x8(%rdi),%eax
    536e:	48 89 f2             	mov    %rsi,%rdx
    5371:	4c 89 d7             	mov    %r10,%rdi
    5374:	89 c6                	mov    %eax,%esi
    5376:	e8 75 fe ff ff       	call   51f0 <handle_http_method>
}
    537b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5383:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    538c:	75 39                	jne    53c7 <handle_client_request+0xb7>
    538e:	31 c0                	xor    %eax,%eax
    5390:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5397:	c3                   	ret
    5398:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    53a0:	48 8b 0d 79 4c 00 00 	mov    0x4c79(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    53a7:	ba 12 00 00 00       	mov    $0x12,%edx
    53ac:	be 01 00 00 00       	mov    $0x1,%esi
    53b1:	48 8d 3d a0 1d 00 00 	lea    0x1da0(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    53b8:	e8 03 d1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    53bd:	bf 01 00 00 00       	mov    $0x1,%edi
    53c2:	e8 d9 d0 ff ff       	call   24a0 <exit@plt>
}
    53c7:	e8 64 cf ff ff       	call   2330 <__stack_chk_fail@plt>
    53cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000053d0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    53d0:	f3 0f 1e fa          	endbr64
    53d4:	55                   	push   %rbp
    53d5:	53                   	push   %rbx
    53d6:	48 89 cb             	mov    %rcx,%rbx
    53d9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    53dd:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    53e0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    53e3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    53e9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    53ec:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    53ef:	f6 c1 02             	test   $0x2,%cl
    53f2:	74 00                	je     53f4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    53f4:	41 89 c0             	mov    %eax,%r8d
    53f7:	45 29 c8             	sub    %r9d,%r8d
    53fa:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    53fe:	0f 82 88 d1 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5404:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5407:	8b 6b 44             	mov    0x44(%rbx),%ebp
    540a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    540d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5410:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5413:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5417:	d3 e5                	shl    %cl,%ebp
    5419:	48 c1 e5 06          	shl    $0x6,%rbp
    541d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5421:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5424:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5429:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5430:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5434:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5438:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    5440:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    5448:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    544c:	e8 bf cf ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    5451:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5454:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    545a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    545e:	48 83 c4 08          	add    $0x8,%rsp
    5462:	5b                   	pop    %rbx
    5463:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5464:	e9 d7 ce ff ff       	jmp    2340 <io_uring_submit@plt>
    5469:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005470 <io_thread>:
void* io_thread(void *arg) {
    5470:	f3 0f 1e fa          	endbr64
    5474:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5476:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5478:	41 56                	push   %r14
    547a:	41 55                	push   %r13
    547c:	41 54                	push   %r12
    547e:	55                   	push   %rbp
    547f:	48 89 fd             	mov    %rdi,%rbp
    5482:	53                   	push   %rbx
    5483:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    548a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5493:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    549b:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    549f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    54a4:	bf 00 01 00 00       	mov    $0x100,%edi
    54a9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    54ac:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    54b0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    54b5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    54ba:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    54bf:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    54c4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    54cc:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    54d1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    54d9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    54de:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    54e6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    54eb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    54f3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    54f8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5500:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5505:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    550d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5515:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    551d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5525:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    552d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5535:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    553d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5545:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    554d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5555:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    555d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5564:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    556c:	e8 7f ce ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5571:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5575:	31 f6                	xor    %esi,%esi
    5577:	e8 64 cf ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    557c:	31 d2                	xor    %edx,%edx
    557e:	be 01 00 00 00       	mov    $0x1,%esi
    5583:	bf 02 00 00 00       	mov    $0x2,%edi
    5588:	e8 a3 cf ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    558d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5590:	0f 84 38 d0 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    5596:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    559b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    55a1:	89 c7                	mov    %eax,%edi
    55a3:	41 89 c4             	mov    %eax,%r12d
    55a6:	ba 02 00 00 00       	mov    $0x2,%edx
    55ab:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    55b0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    55b8:	e8 43 cd ff ff       	call   2300 <setsockopt@plt>
    55bd:	85 c0                	test   %eax,%eax
    55bf:	0f 88 dd cf ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    55c5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    55ca:	ba 10 00 00 00       	mov    $0x10,%edx
    55cf:	44 89 e7             	mov    %r12d,%edi
    55d2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    55db:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    55e3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    55eb:	e8 70 ce ff ff       	call   2460 <bind@plt>
    55f0:	85 c0                	test   %eax,%eax
    55f2:	0f 88 e2 cf ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    55f8:	be 0a 00 00 00       	mov    $0xa,%esi
    55fd:	44 89 e7             	mov    %r12d,%edi
    5600:	e8 1b ce ff ff       	call   2420 <listen@plt>
    5605:	85 c0                	test   %eax,%eax
    5607:	0f 88 a1 cf ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    560d:	ba db 18 00 00       	mov    $0x18db,%edx
    5612:	48 8d 35 84 1b 00 00 	lea    0x1b84(%rip),%rsi        # 719d <_IO_stdin_used+0x19d>
    5619:	bf 01 00 00 00       	mov    $0x1,%edi
    561e:	31 c0                	xor    %eax,%eax
    5620:	e8 2b ce ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5625:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    562a:	48 89 d9             	mov    %rbx,%rcx
    562d:	44 89 e7             	mov    %r12d,%edi
    5630:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5635:	48 89 c6             	mov    %rax,%rsi
    5638:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    563d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5642:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    564a:	e8 81 fd ff ff       	call   53d0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    564f:	bf 01 00 00 00       	mov    $0x1,%edi
    5654:	be 10 00 00 00       	mov    $0x10,%esi
    5659:	e8 42 cd ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    565e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5663:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5666:	e8 a5 cd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    566b:	48 85 c0             	test   %rax,%rax
    566e:	0f 84 ae 04 00 00    	je     5b22 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5674:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5678:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    567f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5686:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    568e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5691:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5696:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5698:	f6 c1 02             	test   $0x2,%cl
    569b:	0f 85 0f 04 00 00    	jne    5ab0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    56a1:	89 d0                	mov    %edx,%eax
    56a3:	29 f0                	sub    %esi,%eax
    56a5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    56ac:	0f 82 12 cf ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    56b2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    56b5:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    56b9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    56bd:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    56c0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    56c7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    56ca:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    56d1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    56d8:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    56da:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    56dd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    56e2:	48 c1 e0 06          	shl    $0x6,%rax
    56e6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    56ee:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    56f4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    56f7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    56ff:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5703:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    570b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5713:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5717:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    571b:	e8 20 cc ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5720:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5724:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5729:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5731:	0f 85 d7 01 00 00    	jne    590e <io_thread+0x49e>
    5737:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    573c:	4d 89 ce             	mov    %r9,%r14
    573f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5744:	0f 1f 40 00          	nopl   0x0(%rax)
    5748:	48 8d 3d 64 1a 00 00 	lea    0x1a64(%rip),%rdi        # 71b3 <_IO_stdin_used+0x1b3>
    574f:	e8 9c cb ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5754:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    575b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5762:	c1 e9 0b             	shr    $0xb,%ecx
    5765:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5768:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5770:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5772:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    577a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    577c:	39 d0                	cmp    %edx,%eax
    577e:	74 36                	je     57b6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5780:	89 f8                	mov    %edi,%eax
    5782:	21 d0                	and    %edx,%eax
    5784:	d3 e0                	shl    %cl,%eax
    5786:	48 c1 e0 04          	shl    $0x4,%rax
    578a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5792:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    579a:	0f 85 a8 01 00 00    	jne    5948 <io_thread+0x4d8>
    57a0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    57a4:	0f 85 0e 03 00 00    	jne    5ab8 <io_thread+0x648>
			if (cqe->res < 0)
    57aa:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    57ad:	83 c2 01             	add    $0x1,%edx
    57b0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    57b2:	85 c0                	test   %eax,%eax
    57b4:	79 b2                	jns    5768 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    57b6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    57bf:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    57c0:	45 31 c0             	xor    %r8d,%r8d
    57c3:	31 d2                	xor    %edx,%edx
    57c5:	b9 01 00 00 00       	mov    $0x1,%ecx
    57ca:	4c 89 f6             	mov    %r14,%rsi
    57cd:	48 89 df             	mov    %rbx,%rdi
    57d0:	e8 6b cc ff ff       	call   2440 <__io_uring_get_cqe@plt>
    57d5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    57d8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    57dd:	48 83 38 01          	cmpq   $0x1,(%rax)
    57e1:	0f 84 e1 02 00 00    	je     5ac8 <io_thread+0x658>
    57e7:	48 8d 3d eb 19 00 00 	lea    0x19eb(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    57ee:	e8 fd ca ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    57f3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    57f8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    57fb:	45 85 ff             	test   %r15d,%r15d
    57fe:	0f 88 92 cd ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    5804:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5807:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    580b:	85 c0                	test   %eax,%eax
    580d:	0f 88 d5 02 00 00    	js     5ae8 <io_thread+0x678>
      switch (req->event_type) {
    5813:	41 83 f8 01          	cmp    $0x1,%r8d
    5817:	0f 84 7b 01 00 00    	je     5998 <io_thread+0x528>
    581d:	41 83 f8 02          	cmp    $0x2,%r8d
    5821:	0f 84 a1 01 00 00    	je     59c8 <io_thread+0x558>
    5827:	45 85 c0             	test   %r8d,%r8d
    582a:	0f 85 50 01 00 00    	jne    5980 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5830:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5835:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    583a:	48 89 d9             	mov    %rbx,%rcx
    583d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5841:	e8 8a fb ff ff       	call   53d0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5846:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    584b:	48 89 de             	mov    %rbx,%rsi
    584e:	8b 78 08             	mov    0x8(%rax),%edi
    5851:	e8 1a f5 ff ff       	call   4d70 <add_read_request>
              free(req);
    5856:	4c 89 e7             	mov    %r12,%rdi
    5859:	e8 62 ca ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    585e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5863:	48 85 c0             	test   %rax,%rax
    5866:	0f 85 14 01 00 00    	jne    5980 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    586c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5873:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    587a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    587d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5882:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5884:	f6 c1 02             	test   $0x2,%cl
    5887:	74 00                	je     5889 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5889:	89 d0                	mov    %edx,%eax
    588b:	29 f0                	sub    %esi,%eax
    588d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5894:	0f 82 20 cd ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    589a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    589d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    58a2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    58a6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    58a9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    58b0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    58b3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    58ba:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    58c1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    58c3:	8b 55 60             	mov    0x60(%rbp),%edx
    58c6:	48 c1 e0 06          	shl    $0x6,%rax
    58ca:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    58d2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    58d8:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    58db:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    58e3:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    58e7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    58ef:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    58f7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    58fb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    58ff:	e8 3c ca ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5904:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5908:	0f 84 3a fe ff ff    	je     5748 <io_thread+0x2d8>
    590e:	48 8d 3d fd 18 00 00 	lea    0x18fd(%rip),%rdi        # 7212 <_IO_stdin_used+0x212>
    5915:	e8 d6 c9 ff ff       	call   22f0 <puts@plt>
}
    591a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5922:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    592b:	0f 85 18 02 00 00    	jne    5b49 <io_thread+0x6d9>
    5931:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5938:	31 c0                	xor    %eax,%eax
    593a:	5b                   	pop    %rbx
    593b:	5d                   	pop    %rbp
    593c:	41 5c                	pop    %r12
    593e:	41 5d                	pop    %r13
    5940:	41 5e                	pop    %r14
    5942:	41 5f                	pop    %r15
    5944:	c3                   	ret
    5945:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5948:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    594d:	48 85 c0             	test   %rax,%rax
    5950:	0f 84 6a fe ff ff    	je     57c0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5956:	48 83 38 01          	cmpq   $0x1,(%rax)
    595a:	0f 84 68 01 00 00    	je     5ac8 <io_thread+0x658>
    5960:	48 8d 3d 72 18 00 00 	lea    0x1872(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    5967:	e8 84 c9 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    596c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5971:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5974:	e9 8b fe ff ff       	jmp    5804 <io_thread+0x394>
    5979:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5980:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5988:	8b 02                	mov    (%rdx),%eax
    598a:	83 c0 01             	add    $0x1,%eax
    598d:	89 02                	mov    %eax,(%rdx)
}
    598f:	e9 d8 fe ff ff       	jmp    586c <io_thread+0x3fc>
    5994:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5998:	85 c0                	test   %eax,%eax
    599a:	75 74                	jne    5a10 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    599c:	48 8b 0d 7d 46 00 00 	mov    0x467d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    59a3:	ba 0f 00 00 00       	mov    $0xf,%edx
    59a8:	be 01 00 00 00       	mov    $0x1,%esi
    59ad:	48 8d 3d 4e 18 00 00 	lea    0x184e(%rip),%rdi        # 7202 <_IO_stdin_used+0x202>
    59b4:	e8 07 cb ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    59b9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    59be:	e9 a0 fe ff ff       	jmp    5863 <io_thread+0x3f3>
    59c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    59c8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    59cd:	45 31 ff             	xor    %r15d,%r15d
    59d0:	85 c0                	test   %eax,%eax
    59d2:	7e 20                	jle    59f4 <io_thread+0x584>
    59d4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    59d8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    59db:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    59df:	48 c1 e0 04          	shl    $0x4,%rax
    59e3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    59e8:	e8 d3 c8 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    59ed:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    59f2:	7f e4                	jg     59d8 <io_thread+0x568>
              close(req->client_socket);
    59f4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    59f9:	e8 72 c9 ff ff       	call   2370 <close@plt>
              free(req);
    59fe:	4c 89 e7             	mov    %r12,%rdi
    5a01:	e8 ba c8 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5a06:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5a0b:	e9 53 fe ff ff       	jmp    5863 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5a10:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5a15:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5a1a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5a22:	eb 11                	jmp    5a35 <io_thread+0x5c5>
    5a24:	0f 1f 40 00          	nopl   0x0(%rax)
    5a28:	48 83 c0 01          	add    $0x1,%rax
    5a2c:	48 83 c2 01          	add    $0x1,%rdx
    5a30:	48 39 c6             	cmp    %rax,%rsi
    5a33:	74 4b                	je     5a80 <io_thread+0x610>
        dest[i] = src[i];
    5a35:	0f b6 0a             	movzbl (%rdx),%ecx
    5a38:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5a3a:	80 f9 0d             	cmp    $0xd,%cl
    5a3d:	75 e9                	jne    5a28 <io_thread+0x5b8>
    5a3f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5a43:	75 e3                	jne    5a28 <io_thread+0x5b8>
            dest[i] = '\0';
    5a45:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5a48:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    5a4d:	48 89 da             	mov    %rbx,%rdx
    5a50:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5a55:	e8 96 f7 ff ff       	call   51f0 <handle_http_method>
              free(req->iov[0].iov_base);
    5a5a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    5a5f:	e8 5c c8 ff ff       	call   22c0 <free@plt>
              free(req);
    5a64:	4c 89 e7             	mov    %r12,%rdi
    5a67:	e8 54 c8 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5a6c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5a71:	e9 ed fd ff ff       	jmp    5863 <io_thread+0x3f3>
    5a76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5a80:	48 8b 0d 99 45 00 00 	mov    0x4599(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5a87:	ba 12 00 00 00       	mov    $0x12,%edx
    5a8c:	be 01 00 00 00       	mov    $0x1,%esi
    5a91:	48 8d 3d c0 16 00 00 	lea    0x16c0(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    5a98:	e8 23 ca ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5a9d:	bf 01 00 00 00       	mov    $0x1,%edi
    5aa2:	e8 f9 c9 ff ff       	call   24a0 <exit@plt>
    5aa7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5ab0:	e9 ec fb ff ff       	jmp    56a1 <io_thread+0x231>
    5ab5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5ab8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    5abd:	e9 94 fe ff ff       	jmp    5956 <io_thread+0x4e6>
    5ac2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5ac8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5ad0:	48 8d 3d ee 16 00 00 	lea    0x16ee(%rip),%rdi        # 71c5 <_IO_stdin_used+0x1c5>
    5ad7:	8b 02                	mov    (%rdx),%eax
    5ad9:	83 c0 01             	add    $0x1,%eax
    5adc:	89 02                	mov    %eax,(%rdx)
    5ade:	e8 0d c8 ff ff       	call   22f0 <puts@plt>
    5ae3:	e9 26 fe ff ff       	jmp    590e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5ae8:	f7 d8                	neg    %eax
    5aea:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5aef:	89 c7                	mov    %eax,%edi
    5af1:	e8 0a ca ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5af6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5afb:	be 01 00 00 00       	mov    $0x1,%esi
    5b00:	48 8b 3d 19 45 00 00 	mov    0x4519(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5b07:	48 89 c1             	mov    %rax,%rcx
    5b0a:	48 8d 15 47 1a 00 00 	lea    0x1a47(%rip),%rdx        # 7558 <_IO_stdin_used+0x558>
    5b11:	31 c0                	xor    %eax,%eax
    5b13:	e8 b8 c9 ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5b18:	bf 01 00 00 00       	mov    $0x1,%edi
    5b1d:	e8 7e c9 ff ff       	call   24a0 <exit@plt>
    5b22:	48 8b 0d f7 44 00 00 	mov    0x44f7(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5b29:	ba 28 00 00 00       	mov    $0x28,%edx
    5b2e:	be 01 00 00 00       	mov    $0x1,%esi
    5b33:	48 8d 3d ee 19 00 00 	lea    0x19ee(%rip),%rdi        # 7528 <_IO_stdin_used+0x528>
    5b3a:	e8 81 c9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5b3f:	bf 01 00 00 00       	mov    $0x1,%edi
    5b44:	e8 57 c9 ff ff       	call   24a0 <exit@plt>
}
    5b49:	e8 e2 c7 ff ff       	call   2330 <__stack_chk_fail@plt>
    5b4e:	66 90                	xchg   %ax,%ax

0000000000005b50 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5b50:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5b54:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5b5b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5b61:	85 c9                	test   %ecx,%ecx
    5b63:	0f 8e ea 00 00 00    	jle    5c53 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    5b69:	41 56                	push   %r14
    5b6b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5b6d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    5b70:	41 54                	push   %r12
    5b72:	49 89 fc             	mov    %rdi,%r12
    5b75:	55                   	push   %rbp
    5b76:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5b77:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5b7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5b80:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    5b84:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    5b8c:	31 db                	xor    %ebx,%ebx
    5b8e:	8b 10                	mov    (%rax),%edx
    5b90:	85 d2                	test   %edx,%edx
    5b92:	7e 26                	jle    5bba <barriered_work_ingest+0x6a>
    5b94:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    5b98:	48 89 dd             	mov    %rbx,%rbp
    5b9b:	48 c1 e5 08          	shl    $0x8,%rbp
    5b9f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    5ba3:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    5baa:	74 24                	je     5bd0 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5bac:	48 83 c3 01          	add    $0x1,%rbx
    5bb0:	39 da                	cmp    %ebx,%edx
    5bb2:	7f e4                	jg     5b98 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5bb4:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5bba:	49 83 c5 01          	add    $0x1,%r13
    5bbe:	44 39 e9             	cmp    %r13d,%ecx
    5bc1:	7f bd                	jg     5b80 <barriered_work_ingest+0x30>
}
    5bc3:	5b                   	pop    %rbx
    5bc4:	31 c0                	xor    %eax,%eax
    5bc6:	5d                   	pop    %rbp
    5bc7:	41 5c                	pop    %r12
    5bc9:	41 5d                	pop    %r13
    5bcb:	41 5e                	pop    %r14
    5bcd:	c3                   	ret
    5bce:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    5bd0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5bd9:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5be0:	bf 04 00 00 00       	mov    $0x4,%edi
    5be5:	48 c1 e6 05          	shl    $0x5,%rsi
    5be9:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5bf0:	48 83 c6 10          	add    $0x10,%rsi
    5bf4:	e8 17 c7 ff ff       	call   2310 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5bf9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5c01:	48 8b 40 50          	mov    0x50(%rax),%rax
    5c05:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5c09:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    5c0d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5c17:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    5c1d:	83 c0 01             	add    $0x1,%eax
    5c20:	99                   	cltd
    5c21:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5c27:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    5c2d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5c30:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5c38:	48 83 c3 01          	add    $0x1,%rbx
    5c3c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5c40:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5c44:	8b 10                	mov    (%rax),%edx
    5c46:	39 da                	cmp    %ebx,%edx
    5c48:	0f 8f 46 ff ff ff    	jg     5b94 <barriered_work_ingest+0x44>
    5c4e:	e9 61 ff ff ff       	jmp    5bb4 <barriered_work_ingest+0x64>
}
    5c53:	31 c0                	xor    %eax,%eax
    5c55:	c3                   	ret
    5c56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005c60 <barriered_thread>:
void* barriered_thread(void *arg) {
    5c60:	f3 0f 1e fa          	endbr64
    5c64:	41 56                	push   %r14
    5c66:	41 55                	push   %r13
    5c68:	41 54                	push   %r12
  int t = 0;
    5c6a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    5c6d:	55                   	push   %rbp
  int waiting = 0;
    5c6e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    5c70:	53                   	push   %rbx
    5c71:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    5c74:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5c78:	0f 85 74 02 00 00    	jne    5ef2 <barriered_thread+0x292>
    if (t >= data->task_count) {
    5c7e:	8b 43 40             	mov    0x40(%rbx),%eax
    5c81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5c88:	41 39 c4             	cmp    %eax,%r12d
    5c8b:	0f 8d 6f 01 00 00    	jge    5e00 <barriered_thread+0x1a0>
    5c91:	49 63 fc             	movslq %r12d,%rdi
    5c94:	48 c1 e7 09          	shl    $0x9,%rdi
    5c98:	49 89 fd             	mov    %rdi,%r13
    5c9b:	eb 32                	jmp    5ccf <barriered_thread+0x6f>
    5c9d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5ca0:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5ca4:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5ca8:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5cac:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5cb0:	4c 01 ef             	add    %r13,%rdi
    5cb3:	e8 98 fe ff ff       	call   5b50 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    5cb8:	8b 43 40             	mov    0x40(%rbx),%eax
    5cbb:	41 83 c4 01          	add    $0x1,%r12d
    5cbf:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    5cc6:	44 39 e0             	cmp    %r12d,%eax
    5cc9:	0f 8e 19 02 00 00    	jle    5ee8 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    5ccf:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5cd3:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    5cd7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    5cde:	75 c0                	jne    5ca0 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5ce0:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    5ce4:	83 e8 01             	sub    $0x1,%eax
    5ce7:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    5cec:	45 85 e4             	test   %r12d,%r12d
    5cef:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5cf2:	45 85 c0             	test   %r8d,%r8d
    5cf5:	0f 8e 2d 01 00 00    	jle    5e28 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5cfb:	48 63 c8             	movslq %eax,%rcx
    5cfe:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5d02:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5d05:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5d0b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    5d12:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    5d16:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    5d19:	45 31 f6             	xor    %r14d,%r14d
    5d1c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5d20:	48 8b 10             	mov    (%rax),%rdx
    5d23:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    5d27:	49 01 cb             	add    %rcx,%r11
    5d2a:	4c 89 da             	mov    %r11,%rdx
    5d2d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    5d34:	75 04                	jne    5d3a <barriered_thread+0xda>
            arrived++;
    5d36:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5d3a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    5d40:	75 04                	jne    5d46 <barriered_thread+0xe6>
            prearrive++;
    5d42:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5d46:	48 83 c0 08          	add    $0x8,%rax
    5d4a:	48 39 c6             	cmp    %rax,%rsi
    5d4d:	75 d1                	jne    5d20 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    5d4f:	45 85 d2             	test   %r10d,%r10d
    5d52:	0f 84 c0 00 00 00    	je     5e18 <barriered_thread+0x1b8>
    5d58:	45 39 d0             	cmp    %r10d,%r8d
    5d5b:	0f 84 b7 00 00 00    	je     5e18 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    5d61:	45 85 f6             	test   %r14d,%r14d
    5d64:	74 0a                	je     5d70 <barriered_thread+0x110>
    5d66:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    5d6a:	0f 85 ae 01 00 00    	jne    5f1e <barriered_thread+0x2be>
    5d70:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    5d74:	4c 01 ea             	add    %r13,%rdx
    5d77:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    5d7e:	45 85 e4             	test   %r12d,%r12d
    5d81:	75 14                	jne    5d97 <barriered_thread+0x137>
    5d83:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5d8a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5d91:	0f 8c 69 01 00 00    	jl     5f00 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5d97:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    5d9b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    5d9f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5da9:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    5dad:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5db1:	4c 01 ef             	add    %r13,%rdi
    5db4:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    5dba:	48 8b 43 38          	mov    0x38(%rbx),%rax
    5dbe:	4c 01 e8             	add    %r13,%rax
    5dc1:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5dc8:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    5dcb:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5dd0:	83 e8 01             	sub    $0x1,%eax
    5dd3:	44 39 e0             	cmp    %r12d,%eax
    5dd6:	0f 84 a4 00 00 00    	je     5e80 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    5ddc:	0f ae f8             	sfence
          if (waiting == 0) {
    5ddf:	85 ed                	test   %ebp,%ebp
    5de1:	0f 84 d1 00 00 00    	je     5eb8 <barriered_thread+0x258>
        int arrived = 0; 
    5de7:	bd 01 00 00 00       	mov    $0x1,%ebp
    5dec:	e9 c7 fe ff ff       	jmp    5cb8 <barriered_thread+0x58>
  while (data->running == 1) {
    5df1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5df5:	0f 85 f7 00 00 00    	jne    5ef2 <barriered_thread+0x292>
    5dfb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    5e00:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    5e08:	85 c0                	test   %eax,%eax
    5e0a:	7e e5                	jle    5df1 <barriered_thread+0x191>
    5e0c:	45 31 e4             	xor    %r12d,%r12d
    5e0f:	e9 7d fe ff ff       	jmp    5c91 <barriered_thread+0x31>
    5e14:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5e18:	83 fd 01             	cmp    $0x1,%ebp
    5e1b:	74 1b                	je     5e38 <barriered_thread+0x1d8>
        int arrived = 0; 
    5e1d:	31 ed                	xor    %ebp,%ebp
    5e1f:	e9 3d ff ff ff       	jmp    5d61 <barriered_thread+0x101>
    5e24:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5e28:	83 fd 01             	cmp    $0x1,%ebp
    5e2b:	0f 85 43 ff ff ff    	jne    5d74 <barriered_thread+0x114>
        int arrived = 0; 
    5e31:	45 31 f6             	xor    %r14d,%r14d
    5e34:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5e38:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5e3f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    5e44:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5e46:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5e4a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5e51:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    5e56:	e8 b5 c4 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    5e5b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5e62:	48 83 c0 01          	add    $0x1,%rax
    5e66:	48 99                	cqto
    5e68:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    5e6f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    5e76:	e9 e6 fe ff ff       	jmp    5d61 <barriered_thread+0x101>
    5e7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5e80:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5e87:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5e8e:	0f 8d 48 ff ff ff    	jge    5ddc <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    5e94:	48 c1 e6 04          	shl    $0x4,%rsi
    5e98:	bf 04 00 00 00       	mov    $0x4,%edi
    5e9d:	48 03 73 70          	add    0x70(%rbx),%rsi
    5ea1:	e8 6a c4 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    5ea6:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    5eae:	e9 29 ff ff ff       	jmp    5ddc <barriered_thread+0x17c>
    5eb3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    5eb8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5ebf:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    5ec4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5ec8:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5ecf:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5ed3:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5ed7:	e8 34 c4 ff ff       	call   2310 <clock_gettime@plt>
            waiting = 1;
    5edc:	e9 06 ff ff ff       	jmp    5de7 <barriered_thread+0x187>
    5ee1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    5ee8:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5eec:	0f 84 96 fd ff ff    	je     5c88 <barriered_thread+0x28>
}
    5ef2:	5b                   	pop    %rbx
    5ef3:	31 c0                	xor    %eax,%eax
    5ef5:	5d                   	pop    %rbp
    5ef6:	41 5c                	pop    %r12
    5ef8:	41 5d                	pop    %r13
    5efa:	41 5e                	pop    %r14
    5efc:	c3                   	ret
    5efd:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    5f00:	48 c1 e6 04          	shl    $0x4,%rsi
    5f04:	bf 04 00 00 00       	mov    $0x4,%edi
    5f09:	48 03 73 68          	add    0x68(%rbx),%rsi
    5f0d:	e8 fe c3 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    5f12:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5f16:	4c 01 ea             	add    %r13,%rdx
    5f19:	e9 79 fe ff ff       	jmp    5d97 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5f1e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5f22:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5f26:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5f2a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5f2e:	4c 01 ef             	add    %r13,%rdi
    5f31:	e8 1a fc ff ff       	call   5b50 <barriered_work_ingest>
          break;
    5f36:	e9 39 fd ff ff       	jmp    5c74 <barriered_thread+0x14>
    5f3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005f40 <receive>:
int receive(struct BarrierTask *data) {
    5f40:	f3 0f 1e fa          	endbr64
    5f44:	41 57                	push   %r15
    5f46:	41 56                	push   %r14
    5f48:	41 55                	push   %r13
    5f4a:	41 54                	push   %r12
    5f4c:	55                   	push   %rbp
    5f4d:	53                   	push   %rbx
    5f4e:	48 83 ec 08          	sub    $0x8,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5f52:	48 63 87 40 01 00 00 	movslq 0x140(%rdi),%rax
    5f59:	85 c0                	test   %eax,%eax
    5f5b:	0f 8e fd 00 00 00    	jle    605e <receive+0x11e>
    5f61:	48 8b b7 70 01 00 00 	mov    0x170(%rdi),%rsi
    5f68:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    5f6c:	48 89 fa             	mov    %rdi,%rdx
    5f6f:	4c 8d 2c c6          	lea    (%rsi,%rax,8),%r13
    5f73:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5f78:	44 8b 66 20          	mov    0x20(%rsi),%r12d
    struct Data *me = data->mailboxes[n].lower;
    5f7c:	48 8b 2e             	mov    (%rsi),%rbp
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5f7f:	41 83 fc 02          	cmp    $0x2,%r12d
    5f83:	0f 84 07 01 00 00    	je     6090 <receive+0x150>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5f89:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    5f90:	48 85 ff             	test   %rdi,%rdi
    5f93:	0f 8e ad 00 00 00    	jle    6046 <receive+0x106>
      data->sends++;
    5f99:	4c 8b 8a 78 01 00 00 	mov    0x178(%rdx),%r9
      data->n++;
    5fa0:	4c 8b 82 08 01 00 00 	mov    0x108(%rdx),%r8
      data->mailboxes[n].received++;
    5fa7:	31 c0                	xor    %eax,%eax
    5fa9:	48 8b 4e 18          	mov    0x18(%rsi),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5fad:	48 8b 5d 00          	mov    0x0(%rbp),%rbx
    5fb1:	4d 8d 51 01          	lea    0x1(%r9),%r10
    5fb5:	4c 63 5a 04          	movslq 0x4(%rdx),%r11
    5fb9:	4d 8d 48 01          	lea    0x1(%r8),%r9
    5fbd:	4c 8d 41 01          	lea    0x1(%rcx),%r8
    5fc1:	eb 0e                	jmp    5fd1 <receive+0x91>
    5fc3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5fc8:	48 83 c0 01          	add    $0x1,%rax
    5fcc:	48 39 f8             	cmp    %rdi,%rax
    5fcf:	7d 6f                	jge    6040 <receive+0x100>
      data->sends++;
    5fd1:	49 8d 0c 02          	lea    (%r10,%rax,1),%rcx
    5fd5:	48 89 8a 78 01 00 00 	mov    %rcx,0x178(%rdx)
      data->n++;
    5fdc:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    5fe0:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5fe7:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5feb:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5fef:	48 8b 0c c3          	mov    (%rbx,%rax,8),%rcx
    5ff3:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5ff7:	75 cf                	jne    5fc8 <receive+0x88>
    5ff9:	4c 8b b2 28 01 00 00 	mov    0x128(%rdx),%r14
    6000:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    6004:	4d 63 7e 08          	movslq 0x8(%r14),%r15
    6008:	4c 39 f9             	cmp    %r15,%rcx
    600b:	75 bb                	jne    5fc8 <receive+0x88>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    600d:	49 63 46 04          	movslq 0x4(%r14),%rax
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6011:	bf 01 00 00 00       	mov    $0x1,%edi
    6016:	ba 01 00 00 00       	mov    $0x1,%edx
    601b:	48 8d 35 5e 15 00 00 	lea    0x155e(%rip),%rsi        # 7580 <_IO_stdin_used+0x580>
    6022:	48 39 c8             	cmp    %rcx,%rax
    6025:	0f 94 c1             	sete   %cl
    6028:	31 c0                	xor    %eax,%eax
    602a:	0f b6 c9             	movzbl %cl,%ecx
    602d:	e8 1e c4 ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    6032:	bf 01 00 00 00       	mov    $0x1,%edi
    6037:	e8 64 c4 ff ff       	call   24a0 <exit@plt>
    603c:	0f 1f 40 00          	nopl   0x0(%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    6040:	41 83 fc 02          	cmp    $0x2,%r12d
    6044:	74 32                	je     6078 <receive+0x138>
    me->messages_count = 0;
    6046:	48 c7 85 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rbp)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6051:	48 83 c6 28          	add    $0x28,%rsi
    6055:	49 39 f5             	cmp    %rsi,%r13
    6058:	0f 85 1a ff ff ff    	jne    5f78 <receive+0x38>
  asm volatile ("sfence" ::: "memory");
    605e:	0f ae f8             	sfence
}
    6061:	48 83 c4 08          	add    $0x8,%rsp
    6065:	31 c0                	xor    %eax,%eax
    6067:	5b                   	pop    %rbx
    6068:	5d                   	pop    %rbp
    6069:	41 5c                	pop    %r12
    606b:	41 5d                	pop    %r13
    606d:	41 5e                	pop    %r14
    606f:	41 5f                	pop    %r15
    6071:	c3                   	ret
    6072:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    6078:	83 bd 00 01 00 00 01 	cmpl   $0x1,0x100(%rbp)
    607f:	75 c5                	jne    6046 <receive+0x106>
      me->available = 0;
    6081:	c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbp)
    608b:	eb b9                	jmp    6046 <receive+0x106>
    608d:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    6090:	8b 85 00 01 00 00    	mov    0x100(%rbp),%eax
    6096:	83 f8 01             	cmp    $0x1,%eax
    6099:	74 09                	je     60a4 <receive+0x164>
    else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 0) {
    609b:	85 c0                	test   %eax,%eax
    609d:	74 b2                	je     6051 <receive+0x111>
    609f:	e9 e5 fe ff ff       	jmp    5f89 <receive+0x49>
    for (int x = 0 ; x < me->messages_count ; x++) {
    60a4:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    60ab:	48 85 ff             	test   %rdi,%rdi
    60ae:	0f 8f e5 fe ff ff    	jg     5f99 <receive+0x59>
    60b4:	eb cb                	jmp    6081 <receive+0x141>
    60b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000060c0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    60c0:	f3 0f 1e fa          	endbr64
    60c4:	41 57                	push   %r15
    60c6:	41 56                	push   %r14
    60c8:	41 55                	push   %r13
    60ca:	41 54                	push   %r12
    60cc:	55                   	push   %rbp
    60cd:	48 89 fd             	mov    %rdi,%rbp
    60d0:	53                   	push   %rbx
    60d1:	48 83 ec 38          	sub    $0x38,%rsp
  if (data->thread_index == data->task_index) {
    60d5:	8b 47 04             	mov    0x4(%rdi),%eax
    60d8:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    60de:	74 50                	je     6130 <barriered_work+0x70>
    receive(data);
    60e0:	e8 5b fe ff ff       	call   5f40 <receive>
    while (data->scheduled == 1) {
    60e5:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    60ec:	75 16                	jne    6104 <barriered_work+0x44>
    60ee:	66 90                	xchg   %ax,%ax
      data->n++;
    60f0:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      asm volatile ("sfence" ::: "memory");
    60f8:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    60fb:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    6102:	74 ec                	je     60f0 <barriered_work+0x30>
  if (data->sending == 1) {
    6104:	83 bd 80 01 00 00 01 	cmpl   $0x1,0x180(%rbp)
    610b:	75 08                	jne    6115 <barriered_work+0x55>
    610d:	48 89 ef             	mov    %rbp,%rdi
    6110:	e8 7b e2 ff ff       	call   4390 <sendm.part.0>
  asm volatile ("sfence" ::: "memory");
    6115:	0f ae f8             	sfence
}
    6118:	48 83 c4 38          	add    $0x38,%rsp
    611c:	31 c0                	xor    %eax,%eax
    611e:	5b                   	pop    %rbx
    611f:	5d                   	pop    %rbp
    6120:	41 5c                	pop    %r12
    6122:	41 5d                	pop    %r13
    6124:	41 5e                	pop    %r14
    6126:	41 5f                	pop    %r15
    6128:	c3                   	ret
    6129:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      receive(data);
    6130:	e8 0b fe ff ff       	call   5f40 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6135:	8b bd 40 01 00 00    	mov    0x140(%rbp),%edi
        int t = data->task_index;
    613b:	8b 45 04             	mov    0x4(%rbp),%eax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    613e:	85 ff                	test   %edi,%edi
    6140:	0f 8e e7 01 00 00    	jle    632d <barriered_work+0x26d>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6146:	48 63 d0             	movslq %eax,%rdx
    6149:	45 31 e4             	xor    %r12d,%r12d
    614c:	44 8d 68 01          	lea    0x1(%rax),%r13d
    6150:	48 c1 e2 09          	shl    $0x9,%rdx
    6154:	4d 89 e6             	mov    %r12,%r14
    6157:	48 89 54 24 20       	mov    %rdx,0x20(%rsp)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    615c:	0f 1f 40 00          	nopl   0x0(%rax)
    6160:	4f 8d 24 76          	lea    (%r14,%r14,2),%r12
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6164:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    6169:	4f 8d 3c b6          	lea    (%r14,%r14,4),%r15
    616d:	31 db                	xor    %ebx,%ebx
    616f:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    6176:	49 c1 e4 06          	shl    $0x6,%r12
    617a:	4c 89 74 24 28       	mov    %r14,0x28(%rsp)
    617f:	49 c1 e7 03          	shl    $0x3,%r15
    6183:	4c 8b 40 20          	mov    0x20(%rax),%r8
    6187:	4b 8b 44 20 38       	mov    0x38(%r8,%r12,1),%rax
    618c:	48 8b b4 08 70 01 00 00 	mov    0x170(%rax,%rcx,1),%rsi
    6194:	e9 ab 00 00 00       	jmp    6244 <barriered_work+0x184>
    6199:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                 if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 0 && ((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available == 0) {
    61a0:	41 8b 89 00 01 00 00 	mov    0x100(%r9),%ecx
    61a7:	85 c9                	test   %ecx,%ecx
    61a9:	0f 85 89 00 00 00    	jne    6238 <barriered_work+0x178>
    61af:	48 8b 0a             	mov    (%rdx),%rcx
    61b2:	44 8b b1 00 01 00 00 	mov    0x100(%rcx),%r14d
    61b9:	45 85 f6             	test   %r14d,%r14d
    61bc:	75 7a                	jne    6238 <barriered_work+0x178>
    61be:	4c 8d 14 5b          	lea    (%rbx,%rbx,2),%r10
    61c2:	48 98                	cltq
    61c4:	49 c1 e2 06          	shl    $0x6,%r10
    61c8:	48 c1 e0 09          	shl    $0x9,%rax
    61cc:	4b 03 44 10 38       	add    0x38(%r8,%r10,1),%rax
    61d1:	4c 8b 98 70 01 00 00 	mov    0x170(%rax),%r11
    61d8:	4d 01 fb             	add    %r15,%r11
    61db:	4d 8b 53 08          	mov    0x8(%r11),%r10
    61df:	4c 89 d8             	mov    %r11,%rax
    61e2:	45 8b 9a 00 01 00 00 	mov    0x100(%r10),%r11d
    61e9:	45 85 db             	test   %r11d,%r11d
    61ec:	75 4a                	jne    6238 <barriered_work+0x178>
    61ee:	4c 8b 18             	mov    (%rax),%r11
    61f1:	45 8b b3 00 01 00 00 	mov    0x100(%r11),%r14d
    61f8:	45 85 f6             	test   %r14d,%r14d
    61fb:	75 3b                	jne    6238 <barriered_work+0x178>
                  data->thread->all_threads[y].tasks[t].mailboxes[b].lower = _c;
    61fd:	66 49 0f 6e c2       	movq   %r10,%xmm0
    6202:	66 49 0f 6e db       	movq   %r11,%xmm3
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = _a;
    6207:	66 48 0f 6e e1       	movq   %rcx,%xmm4
                  data->thread->all_threads[y].tasks[t].mailboxes[b].lower = _c;
    620c:	66 0f 6c c3          	punpcklqdq %xmm3,%xmm0
    6210:	0f 11 02             	movups %xmm0,(%rdx)
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = _a;
    6213:	66 49 0f 6e c1       	movq   %r9,%xmm0
    6218:	66 0f 6c c4          	punpcklqdq %xmm4,%xmm0
    621c:	0f 11 00             	movups %xmm0,(%rax)
                  ((struct Data*)_a)->available = 1;
    621f:	41 c7 81 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r9)
                  ((struct Data*)_c)->available = 1;
    622a:	41 c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r10)
    6235:	0f 1f 00             	nopl   (%rax)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6238:	48 83 c3 01          	add    $0x1,%rbx
    623c:	39 df                	cmp    %ebx,%edi
    623e:	0f 8e d7 00 00 00    	jle    631b <barriered_work+0x25b>
              int next_task = abs((t + 1) % (data->thread_count));
    6244:	44 89 e8             	mov    %r13d,%eax
    6247:	4c 8d 34 9b          	lea    (%rbx,%rbx,4),%r14
    624b:	99                   	cltd
    624c:	f7 bd 34 01 00 00    	idivl  0x134(%rbp)
    6252:	89 d0                	mov    %edx,%eax
    6254:	f7 d8                	neg    %eax
    6256:	0f 48 c2             	cmovs  %edx,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6259:	4a 8d 14 f6          	lea    (%rsi,%r14,8),%rdx
              if (kind == MAILBOX_FRIEND) {
    625d:	83 7a 20 01          	cmpl   $0x1,0x20(%rdx)
                  void * _a = data->thread->all_threads[y].tasks[t].mailboxes[b].higher;
    6261:	4c 8b 4a 08          	mov    0x8(%rdx),%r9
              if (kind == MAILBOX_FRIEND) {
    6265:	0f 85 35 ff ff ff    	jne    61a0 <barriered_work+0xe0>
                  void * _b = data->thread->all_threads[y].tasks[t].mailboxes[b].lower;
    626b:	66 49 0f 6e c9       	movq   %r9,%xmm1
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    6270:	4c 63 c8             	movslq %eax,%r9
    6273:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6278:	48 83 c3 01          	add    $0x1,%rbx
    627c:	0f 16 0a             	movhps (%rdx),%xmm1
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    627f:	48 63 52 24          	movslq 0x24(%rdx),%rdx
    6283:	49 c1 e1 09          	shl    $0x9,%r9
    6287:	48 8d 35 97 0f 00 00 	lea    0xf97(%rip),%rsi        # 7225 <_IO_stdin_used+0x225>
    628e:	4c 89 0c 24          	mov    %r9,(%rsp)
    6292:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
    6296:	0f 29 4c 24 10       	movaps %xmm1,0x10(%rsp)
    629b:	49 c1 e2 06          	shl    $0x6,%r10
    629f:	4b 8b 44 10 38       	mov    0x38(%r8,%r10,1),%rax
    62a4:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    62a9:	4a 8b 84 08 70 01 00 00 	mov    0x170(%rax,%r9,1),%rax
    62b1:	42 8b 54 38 20       	mov    0x20(%rax,%r15,1),%edx
    62b6:	31 c0                	xor    %eax,%eax
    62b8:	e8 93 c1 ff ff       	call   2450 <__printf_chk@plt>
                  void * _c = data->thread->all_threads[other].tasks[next_task].mailboxes[y].higher;
    62bd:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    62c4:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    62c9:	4c 89 f9             	mov    %r15,%rcx
    62cc:	4c 8b 0c 24          	mov    (%rsp),%r9
                  data->thread->all_threads[other].tasks[next_task].mailboxes[y].lower = _a;
    62d0:	66 0f 6f 4c 24 10    	movdqa 0x10(%rsp),%xmm1
                  void * _c = data->thread->all_threads[other].tasks[next_task].mailboxes[y].higher;
    62d6:	4c 8b 40 20          	mov    0x20(%rax),%r8
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    62da:	8b bd 40 01 00 00    	mov    0x140(%rbp),%edi
                  void * _c = data->thread->all_threads[other].tasks[next_task].mailboxes[y].higher;
    62e0:	4b 8b 44 10 38       	mov    0x38(%r8,%r10,1),%rax
                  data->thread->all_threads[y].tasks[t].mailboxes[b].higher = _d;
    62e5:	4b 8b 54 20 38       	mov    0x38(%r8,%r12,1),%rdx
                  void * _c = data->thread->all_threads[other].tasks[next_task].mailboxes[y].higher;
    62ea:	4a 03 8c 08 70 01 00 00 	add    0x170(%rax,%r9,1),%rcx
    62f2:	48 89 c8             	mov    %rcx,%rax
                  data->thread->all_threads[y].tasks[t].mailboxes[b].higher = _d;
    62f5:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
                  void * _d = data->thread->all_threads[other].tasks[next_task].mailboxes[y].lower;
    62fa:	f3 0f 6f 00          	movdqu (%rax),%xmm0
                  data->thread->all_threads[y].tasks[t].mailboxes[b].higher = _d;
    62fe:	48 8b b4 0a 70 01 00 00 	mov    0x170(%rdx,%rcx,1),%rsi
                  void * _d = data->thread->all_threads[other].tasks[next_task].mailboxes[y].lower;
    6306:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
                  data->thread->all_threads[y].tasks[t].mailboxes[b].lower = _c;
    630b:	42 0f 11 04 f6       	movups %xmm0,(%rsi,%r14,8)
                  data->thread->all_threads[other].tasks[next_task].mailboxes[y].lower = _a;
    6310:	0f 11 08             	movups %xmm1,(%rax)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6313:	39 df                	cmp    %ebx,%edi
    6315:	0f 8f 29 ff ff ff    	jg     6244 <barriered_work+0x184>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    631b:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    6320:	49 83 c6 01          	add    $0x1,%r14
    6324:	44 39 f7             	cmp    %r14d,%edi
    6327:	0f 8f 33 fe ff ff    	jg     6160 <barriered_work+0xa0>
      asm volatile ("sfence" ::: "memory");
    632d:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6330:	48 8b b5 60 01 00 00 	mov    0x160(%rbp),%rsi
    6337:	31 ff                	xor    %edi,%edi
    6339:	48 c1 e6 05          	shl    $0x5,%rsi
    633d:	48 03 b5 50 01 00 00 	add    0x150(%rbp),%rsi
    6344:	e8 c7 bf ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6349:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    while (data->scheduled == 1) {
    6350:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    int modcount = ++data->thread->protected_state->modcount;
    6357:	48 8b 50 48          	mov    0x48(%rax),%rdx
    635b:	8b 4a 10             	mov    0x10(%rdx),%ecx
    635e:	8d 59 01             	lea    0x1(%rcx),%ebx
    6361:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    6364:	75 5b                	jne    63c1 <barriered_work+0x301>
    6366:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6370:	48 63 95 30 01 00 00 	movslq 0x130(%rbp),%rdx
    6377:	48 8b 40 18          	mov    0x18(%rax),%rax
    637b:	48 63 7d 04          	movslq 0x4(%rbp),%rdi
      data->n++;
    637f:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6387:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    638b:	48 c1 e7 09          	shl    $0x9,%rdi
    638f:	48 03 78 38          	add    0x38(%rax),%rdi
    6393:	ff 95 20 01 00 00    	call   *0x120(%rbp)
      asm volatile ("sfence" ::: "memory");
    6399:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    639c:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    if (modcount != data->thread->protected_state->modcount) {
    63a3:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    while (data->scheduled == 1) {
    63aa:	74 c4                	je     6370 <barriered_work+0x2b0>
    if (modcount != data->thread->protected_state->modcount) {
    63ac:	48 8b 40 48          	mov    0x48(%rax),%rax
    63b0:	3b 58 10             	cmp    0x10(%rax),%ebx
    63b3:	74 0c                	je     63c1 <barriered_work+0x301>
    63b5:	48 8d 3d 7a 0e 00 00 	lea    0xe7a(%rip),%rdi        # 7236 <_IO_stdin_used+0x236>
    63bc:	e8 2f bf ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    63c1:	48 8b b5 60 01 00 00 	mov    0x160(%rbp),%rsi
    63c8:	31 ff                	xor    %edi,%edi
    63ca:	48 c1 e6 05          	shl    $0x5,%rsi
    63ce:	48 03 b5 50 01 00 00 	add    0x150(%rbp),%rsi
    63d5:	48 83 c6 10          	add    $0x10,%rsi
    63d9:	e8 32 bf ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    63de:	48 8b 85 60 01 00 00 	mov    0x160(%rbp),%rax
    63e5:	48 83 c0 01          	add    $0x1,%rax
    63e9:	48 99                	cqto
    63eb:	48 f7 bd 58 01 00 00 	idivq  0x158(%rbp)
    63f2:	48 89 95 60 01 00 00 	mov    %rdx,0x160(%rbp)
    63f9:	e9 06 fd ff ff       	jmp    6104 <barriered_work+0x44>
    63fe:	66 90                	xchg   %ax,%ax

0000000000006400 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6400:	f3 0f 1e fa          	endbr64
    6404:	53                   	push   %rbx
    6405:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6408:	e8 43 f7 ff ff       	call   5b50 <barriered_work_ingest>
  barriered_work(data);
    640d:	48 89 df             	mov    %rbx,%rdi
}
    6410:	5b                   	pop    %rbx
  barriered_work(data);
    6411:	e9 aa fc ff ff       	jmp    60c0 <barriered_work>
    6416:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006420 <sendm>:
int sendm(struct BarrierTask *data) {
    6420:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    6424:	83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%rdi)
    642b:	74 03                	je     6430 <sendm+0x10>
}
    642d:	31 c0                	xor    %eax,%eax
    642f:	c3                   	ret
int sendm(struct BarrierTask *data) {
    6430:	48 83 ec 08          	sub    $0x8,%rsp
    6434:	e8 57 df ff ff       	call   4390 <sendm.part.0>
}
    6439:	31 c0                	xor    %eax,%eax
    643b:	48 83 c4 08          	add    $0x8,%rsp
    643f:	c3                   	ret

0000000000006440 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6440:	f3 0f 1e fa          	endbr64
}
    6444:	31 c0                	xor    %eax,%eax
    6446:	c3                   	ret
    6447:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006450 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6450:	f3 0f 1e fa          	endbr64
    6454:	31 c0                	xor    %eax,%eax
    6456:	c3                   	ret
    6457:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006460 <after>:
int after(struct timespec left, struct timespec right) {
    6460:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6464:	31 c0                	xor    %eax,%eax
    6466:	48 39 d7             	cmp    %rdx,%rdi
    6469:	7e 08                	jle    6473 <after+0x13>
    646b:	31 c0                	xor    %eax,%eax
    646d:	48 39 ce             	cmp    %rcx,%rsi
    6470:	0f 9f c0             	setg   %al
}
    6473:	c3                   	ret
    6474:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    647f:	90                   	nop

0000000000006480 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6480:	f3 0f 1e fa          	endbr64
    6484:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6489:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    648e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6490:	48 39 d7             	cmp    %rdx,%rdi
    6493:	7f 18                	jg     64ad <within+0x2d>
    6495:	4d 39 d8             	cmp    %r11,%r8
    6498:	0f 9e c2             	setle  %dl
    649b:	48 39 ce             	cmp    %rcx,%rsi
    649e:	0f 9e c0             	setle  %al
    64a1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    64a3:	31 c0                	xor    %eax,%eax
    64a5:	4d 39 d1             	cmp    %r10,%r9
    64a8:	0f 9e c0             	setle  %al
    64ab:	21 d0                	and    %edx,%eax
}
    64ad:	c3                   	ret
    64ae:	66 90                	xchg   %ax,%ax

00000000000064b0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    64b0:	f3 0f 1e fa          	endbr64
    64b4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    64b9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    64be:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    64c3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    64c8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    64cd:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    64d2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    64d7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    64dc:	48 39 fe             	cmp    %rdi,%rsi
    64df:	7d 2f                	jge    6510 <overlap+0x60>
    64e1:	48 39 ca             	cmp    %rcx,%rdx
    64e4:	7d 62                	jge    6548 <overlap+0x98>
    64e6:	4d 39 da             	cmp    %r11,%r10
    64e9:	7d 0e                	jge    64f9 <overlap+0x49>
    return 1;
    64eb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    64f0:	4d 39 c1             	cmp    %r8,%r9
    64f3:	0f 8c 7f 00 00 00    	jl     6578 <overlap+0xc8>
  return 0;
    64f9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    64fb:	4d 39 c1             	cmp    %r8,%r9
    64fe:	7f 4c                	jg     654c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6500:	31 c0                	xor    %eax,%eax
    6502:	4d 39 da             	cmp    %r11,%r10
    6505:	0f 9e c0             	setle  %al
    6508:	c3                   	ret
    6509:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6510:	7e 4e                	jle    6560 <overlap+0xb0>
    6512:	48 39 ca             	cmp    %rcx,%rdx
    6515:	7f 39                	jg     6550 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6517:	75 31                	jne    654a <overlap+0x9a>
    6519:	4d 39 c1             	cmp    %r8,%r9
    651c:	7c 2c                	jl     654a <overlap+0x9a>
    return 1;
    651e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6523:	4d 39 da             	cmp    %r11,%r10
    6526:	7d 24                	jge    654c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6528:	48 39 ca             	cmp    %rcx,%rdx
    652b:	0f 94 c2             	sete   %dl
    652e:	48 39 fe             	cmp    %rdi,%rsi
    6531:	0f 94 c0             	sete   %al
    6534:	21 c2                	and    %eax,%edx
    6536:	31 c0                	xor    %eax,%eax
    6538:	4d 39 c1             	cmp    %r8,%r9
    653b:	0f 94 c0             	sete   %al
    653e:	21 d0                	and    %edx,%eax
    6540:	c3                   	ret
    6541:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6548:	74 af                	je     64f9 <overlap+0x49>
  return 0;
    654a:	31 c0                	xor    %eax,%eax
}
    654c:	c3                   	ret
    654d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6550:	4d 39 da             	cmp    %r11,%r10
    6553:	7e c4                	jle    6519 <overlap+0x69>
    return 1;
    6555:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    655a:	4d 39 c1             	cmp    %r8,%r9
    655d:	7e ba                	jle    6519 <overlap+0x69>
    655f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6560:	48 39 ca             	cmp    %rcx,%rdx
    6563:	7c 94                	jl     64f9 <overlap+0x49>
    6565:	4d 39 c1             	cmp    %r8,%r9
    6568:	7d b4                	jge    651e <overlap+0x6e>
    656a:	48 39 ca             	cmp    %rcx,%rdx
    656d:	74 91                	je     6500 <overlap+0x50>
    656f:	eb d9                	jmp    654a <overlap+0x9a>
    6571:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6578:	c3                   	ret
    6579:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006580 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6580:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6584:	85 f6                	test   %esi,%esi
    6586:	0f 8e 44 03 00 00    	jle    68d0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    658c:	41 57                	push   %r15
    658e:	41 89 f7             	mov    %esi,%r15d
    6591:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6593:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6596:	41 55                	push   %r13
    6598:	41 54                	push   %r12
    659a:	55                   	push   %rbp
    659b:	53                   	push   %rbx
    659c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    65a0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    65a4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    65a9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    65ae:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    65b1:	45 39 e6             	cmp    %r12d,%r14d
    65b4:	0f 84 4e 02 00 00    	je     6808 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    65ba:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    65bf:	8b 50 08             	mov    0x8(%rax),%edx
    65c2:	85 d2                	test   %edx,%edx
    65c4:	0f 8e 3e 02 00 00    	jle    6808 <verify+0x288>
    65ca:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    65cf:	31 c9                	xor    %ecx,%ecx
    65d1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    65d6:	31 c0                	xor    %eax,%eax
    65d8:	44 89 f2             	mov    %r14d,%edx
    65db:	bf 01 00 00 00       	mov    $0x1,%edi
    65e0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    65e5:	48 8d 35 5a 0c 00 00 	lea    0xc5a(%rip),%rsi        # 7246 <_IO_stdin_used+0x246>
    65ec:	e8 5f be ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    65f1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    65f6:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    65fb:	8b 40 08             	mov    0x8(%rax),%eax
    65fe:	85 c0                	test   %eax,%eax
    6600:	0f 8e e6 01 00 00    	jle    67ec <verify+0x26c>
    6606:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6609:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    660e:	31 db                	xor    %ebx,%ebx
    6610:	48 c1 e0 09          	shl    $0x9,%rax
    6614:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6619:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    661e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6623:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6628:	4c 8b 20             	mov    (%rax),%r12
    662b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6630:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6635:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    663a:	49 89 de             	mov    %rbx,%r14
    663d:	48 8d 35 17 0c 00 00 	lea    0xc17(%rip),%rsi        # 725b <_IO_stdin_used+0x25b>
    6644:	49 c1 e6 09          	shl    $0x9,%r14
    6648:	bf 01 00 00 00       	mov    $0x1,%edi
    664d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6651:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    6659:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    665e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    6666:	31 c0                	xor    %eax,%eax
    6668:	e8 e3 bd ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    666d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6672:	4c 8b 20             	mov    (%rax),%r12
    6675:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    667e:	0f 8e 47 01 00 00    	jle    67cb <verify+0x24b>
    6684:	4c 03 75 00          	add    0x0(%rbp),%r14
    6688:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    668d:	ba 01 00 00 00       	mov    $0x1,%edx
    6692:	4d 89 f5             	mov    %r14,%r13
    6695:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    669c:	4d 85 f6             	test   %r14,%r14
    669f:	0f 8e 21 01 00 00    	jle    67c6 <verify+0x246>
    66a5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    66a8:	48 89 d5             	mov    %rdx,%rbp
    66ab:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    66b0:	31 db                	xor    %ebx,%ebx
    66b2:	4d 89 f2             	mov    %r14,%r10
    66b5:	48 c1 e5 05          	shl    $0x5,%rbp
    66b9:	48 83 ed 20          	sub    $0x20,%rbp
    66bd:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    66c1:	49 89 ee             	mov    %rbp,%r14
    66c4:	48 89 dd             	mov    %rbx,%rbp
    66c7:	48 89 d3             	mov    %rdx,%rbx
    66ca:	eb 31                	jmp    66fd <verify+0x17d>
    66cc:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    66d0:	4c 39 c2             	cmp    %r8,%rdx
    66d3:	0f 8d 57 01 00 00    	jge    6830 <verify+0x2b0>
    66d9:	4c 39 df             	cmp    %r11,%rdi
    66dc:	7e 05                	jle    66e3 <verify+0x163>
    66de:	49 39 c1             	cmp    %rax,%r9
    66e1:	7c 75                	jl     6758 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    66e3:	4c 39 df             	cmp    %r11,%rdi
    66e6:	0f 8d ab 01 00 00    	jge    6897 <verify+0x317>
    66ec:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    66f0:	48 83 c5 01          	add    $0x1,%rbp
    66f4:	49 39 ea             	cmp    %rbp,%r10
    66f7:	0f 8e a9 00 00 00    	jle    67a6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    66fd:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    6704:	48 89 e8             	mov    %rbp,%rax
    6707:	48 c1 e0 05          	shl    $0x5,%rax
    670b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    6712:	4c 01 f2             	add    %r14,%rdx
    6715:	48 8b 08             	mov    (%rax),%rcx
    6718:	48 8b 78 10          	mov    0x10(%rax),%rdi
    671c:	48 8b 32             	mov    (%rdx),%rsi
    671f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6723:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6727:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    672b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    672f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6733:	48 39 f1             	cmp    %rsi,%rcx
    6736:	7c 98                	jl     66d0 <verify+0x150>
    6738:	0f 8e 42 01 00 00    	jle    6880 <verify+0x300>
    673e:	4c 39 c2             	cmp    %r8,%rdx
    6741:	0f 8f f9 00 00 00    	jg     6840 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6747:	75 a7                	jne    66f0 <verify+0x170>
    6749:	4c 39 df             	cmp    %r11,%rdi
    674c:	7f a2                	jg     66f0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    674e:	49 39 c1             	cmp    %rax,%r9
    6751:	7c 9d                	jl     66f0 <verify+0x170>
    6753:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6758:	49 89 c1             	mov    %rax,%r9
    675b:	48 89 f9             	mov    %rdi,%rcx
    675e:	48 89 f2             	mov    %rsi,%rdx
    6761:	bf 01 00 00 00       	mov    $0x1,%edi
    6766:	48 8d 35 3b 0e 00 00 	lea    0xe3b(%rip),%rsi        # 75a8 <_IO_stdin_used+0x5a8>
    676d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    676f:	48 83 c5 01          	add    $0x1,%rbp
    6773:	e8 d8 bc ff ff       	call   2450 <__printf_chk@plt>
    6778:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    677d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    6782:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6785:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    678a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6791:	4c 8b 20             	mov    (%rax),%r12
    6794:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6799:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    679d:	49 39 ea             	cmp    %rbp,%r10
    67a0:	0f 8f 57 ff ff ff    	jg     66fd <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    67a6:	48 89 da             	mov    %rbx,%rdx
    67a9:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    67b0:	7d 14                	jge    67c6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    67b2:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    67b9:	48 83 c2 01          	add    $0x1,%rdx
    67bd:	4d 85 f6             	test   %r14,%r14
    67c0:	0f 8f e2 fe ff ff    	jg     66a8 <verify+0x128>
    67c6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    67cb:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    67d0:	48 83 c3 01          	add    $0x1,%rbx
    67d4:	39 58 08             	cmp    %ebx,0x8(%rax)
    67d7:	0f 8f 53 fe ff ff    	jg     6630 <verify+0xb0>
    67dd:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    67e2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    67e7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    67ec:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    67f1:	48 83 c1 01          	add    $0x1,%rcx
    67f5:	39 48 08             	cmp    %ecx,0x8(%rax)
    67f8:	0f 8f d8 fd ff ff    	jg     65d6 <verify+0x56>
    67fe:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6803:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6808:	48 81 44 24 10 c0 00 00 00 	addq   $0xc0,0x10(%rsp)
    6811:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6816:	41 39 c7             	cmp    %eax,%r15d
    6819:	0f 84 86 00 00 00    	je     68a5 <verify+0x325>
    681f:	41 89 c4             	mov    %eax,%r12d
    6822:	e9 8a fd ff ff       	jmp    65b1 <verify+0x31>
    6827:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6830:	0f 85 ba fe ff ff    	jne    66f0 <verify+0x170>
    6836:	e9 a8 fe ff ff       	jmp    66e3 <verify+0x163>
    683b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6840:	49 39 c1             	cmp    %rax,%r9
    6843:	7e 09                	jle    684e <verify+0x2ce>
    6845:	4c 39 df             	cmp    %r11,%rdi
    6848:	0f 8c 0a ff ff ff    	jl     6758 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    684e:	4c 39 df             	cmp    %r11,%rdi
    6851:	0f 8f 99 fe ff ff    	jg     66f0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6857:	49 39 c1             	cmp    %rax,%r9
    685a:	0f 8d f8 fe ff ff    	jge    6758 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6860:	48 39 f1             	cmp    %rsi,%rcx
    6863:	0f 85 87 fe ff ff    	jne    66f0 <verify+0x170>
    6869:	4c 39 c2             	cmp    %r8,%rdx
    686c:	0f 85 7e fe ff ff    	jne    66f0 <verify+0x170>
    6872:	4c 39 df             	cmp    %r11,%rdi
    6875:	0f 84 dd fe ff ff    	je     6758 <verify+0x1d8>
    687b:	e9 70 fe ff ff       	jmp    66f0 <verify+0x170>
    6880:	4c 39 c2             	cmp    %r8,%rdx
    6883:	0f 8c 5a fe ff ff    	jl     66e3 <verify+0x163>
    6889:	4c 39 df             	cmp    %r11,%rdi
    688c:	7e c9                	jle    6857 <verify+0x2d7>
    688e:	4c 39 c2             	cmp    %r8,%rdx
    6891:	0f 85 59 fe ff ff    	jne    66f0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6897:	49 39 c1             	cmp    %rax,%r9
    689a:	0f 8f 50 fe ff ff    	jg     66f0 <verify+0x170>
    68a0:	e9 b3 fe ff ff       	jmp    6758 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    68a5:	48 81 44 24 18 c0 00 00 00 	addq   $0xc0,0x18(%rsp)
    68ae:	41 8d 46 01          	lea    0x1(%r14),%eax
    68b2:	45 39 e6             	cmp    %r12d,%r14d
    68b5:	74 08                	je     68bf <verify+0x33f>
    68b7:	41 89 c6             	mov    %eax,%r14d
    68ba:	e9 ea fc ff ff       	jmp    65a9 <verify+0x29>
}
    68bf:	48 83 c4 58          	add    $0x58,%rsp
    68c3:	31 c0                	xor    %eax,%eax
    68c5:	5b                   	pop    %rbx
    68c6:	5d                   	pop    %rbp
    68c7:	41 5c                	pop    %r12
    68c9:	41 5d                	pop    %r13
    68cb:	41 5e                	pop    %r14
    68cd:	41 5f                	pop    %r15
    68cf:	c3                   	ret
    68d0:	31 c0                	xor    %eax,%eax
    68d2:	c3                   	ret

Disassembly of section .fini:

00000000000068d4 <_fini>:
    68d4:	f3 0f 1e fa          	endbr64
    68d8:	48 83 ec 08          	sub    $0x8,%rsp
    68dc:	48 83 c4 08          	add    $0x8,%rsp
    68e0:	c3                   	ret
