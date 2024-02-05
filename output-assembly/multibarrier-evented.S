
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
    25f6:	48 8d 3d 63 4f 00 00 	lea    0x4f63(%rip),%rdi        # 7560 <_IO_stdin_used+0x560>
    25fd:	41 56                	push   %r14
    25ff:	41 55                	push   %r13
    2601:	41 54                	push   %r12
    2603:	55                   	push   %rbp
    2604:	53                   	push   %rbx
    2605:	48 81 ec b8 00 00 00 	sub    $0xb8,%rsp
    260c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2615:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
    261d:	48 8d 05 2c 16 00 00 	lea    0x162c(%rip),%rax        # 3c50 <barriered_reset>
    2624:	66 48 0f 6e d8       	movq   %rax,%xmm3
    2629:	0f 16 1d 48 76 00 00 	movhps 0x7648(%rip),%xmm3        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    2630:	0f 29 5c 24 60       	movaps %xmm3,0x60(%rsp)
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
    272d:	48 8d 35 94 4e 00 00 	lea    0x4e94(%rip),%rsi        # 75c8 <_IO_stdin_used+0x5c8>
    2734:	31 c0                	xor    %eax,%eax
    2736:	bf 01 00 00 00       	mov    $0x1,%edi
    273b:	e8 10 fd ff ff       	call   2450 <__printf_chk@plt>
    2740:	ba 01 00 00 00       	mov    $0x1,%edx
    2745:	48 8d 35 ac 4e 00 00 	lea    0x4eac(%rip),%rsi        # 75f8 <_IO_stdin_used+0x5f8>
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
    27ad:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27b2:	e8 e9 fb ff ff       	call   23a0 <calloc@plt>
    27b7:	ba 04 00 00 00       	mov    $0x4,%edx
    27bc:	bf 01 00 00 00       	mov    $0x1,%edi
    27c1:	48 8d 35 a4 4b 00 00 	lea    0x4ba4(%rip),%rsi        # 736c <_IO_stdin_used+0x36c>
    27c8:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
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
    27fb:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    2800:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    2805:	49 89 c5             	mov    %rax,%r13
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    2808:	48 8d 98 80 00 00 00 	lea    0x80(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    280f:	49 89 c4             	mov    %rax,%r12
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2812:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    2817:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    281f:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2824:	49 83 c4 10          	add    $0x10,%r12
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2828:	e8 73 fb ff ff       	call   23a0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    282d:	be 20 00 00 00       	mov    $0x20,%esi
    2832:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2837:	49 89 44 24 f8       	mov    %rax,-0x8(%r12)
    283c:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
    283f:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2849:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2853:	e8 48 fb ff ff       	call   23a0 <calloc@plt>
    2858:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    285f:	49 39 dc             	cmp    %rbx,%r12
    2862:	75 ae                	jne    2812 <main+0x222>
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
    2864:	c7 44 24 48 00 00 00 00 	movl   $0x0,0x48(%rsp)
  for (int x = 0 ; x < buffers_required; x++) {
    286c:	4d 89 f3             	mov    %r14,%r11
    286f:	31 db                	xor    %ebx,%ebx
    2871:	4d 89 ec             	mov    %r13,%r12
  int curcpu = 0;
    2874:	c7 44 24 38 00 00 00 00 	movl   $0x0,0x38(%rsp)
  for (int x = 0 ; x < buffers_required; x++) {
    287c:	be 02 00 00 00       	mov    $0x2,%esi
    2881:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    2886:	89 f1                	mov    %esi,%ecx
    2888:	48 63 44 24 48       	movslq 0x48(%rsp),%rax
    288d:	48 89 dd             	mov    %rbx,%rbp
    2890:	89 4c 24 50          	mov    %ecx,0x50(%rsp)
    2894:	44 8d 34 1b          	lea    (%rbx,%rbx,1),%r14d
    2898:	48 f7 dd             	neg    %rbp
    289b:	48 89 7c 24 70       	mov    %rdi,0x70(%rsp)
    28a0:	48 c1 e0 04          	shl    $0x4,%rax
    28a4:	81 e5 80 01 00 00    	and    $0x180,%ebp
    28aa:	89 5c 24 78          	mov    %ebx,0x78(%rsp)
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    28ae:	4d 8d 2c 04          	lea    (%r12,%rax,1),%r13
    28b2:	4c 89 5c 24 30       	mov    %r11,0x30(%rsp)
    28b7:	4c 01 dd             	add    %r11,%rbp
    28ba:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    28bf:	4c 89 a4 24 88 00 00 00 	mov    %r12,0x88(%rsp)
    28c7:	48 89 9c 24 80 00 00 00 	mov    %rbx,0x80(%rsp)
    28cf:	48 89 eb             	mov    %rbp,%rbx
    28d2:	8b 54 24 78          	mov    0x78(%rsp),%edx
    28d6:	44 89 f1             	mov    %r14d,%ecx
    28d9:	48 8d 35 40 4d 00 00 	lea    0x4d40(%rip),%rsi        # 7620 <_IO_stdin_used+0x620>
    28e0:	31 c0                	xor    %eax,%eax
    28e2:	bf 01 00 00 00       	mov    $0x1,%edi
    28e7:	e8 64 fb ff ff       	call   2450 <__printf_chk@plt>
      int x = (k * threads_per_group) + d;
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    28ec:	be 08 00 00 00       	mov    $0x8,%esi
    28f1:	bf 02 00 00 00       	mov    $0x2,%edi
    28f6:	e8 a5 fa ff ff       	call   23a0 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    28fb:	be 80 00 00 00       	mov    $0x80,%esi
    2900:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2905:	49 89 c4             	mov    %rax,%r12
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2908:	e8 93 fa ff ff       	call   23a0 <calloc@plt>
    290d:	49 89 c5             	mov    %rax,%r13
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2910:	41 f6 c6 01          	test   $0x1,%r14b
    2914:	0f 84 81 04 00 00    	je     2d9b <main+0x7ab>
        other = abs(x - 1) % total_threads;
    291a:	41 8d 46 ff          	lea    -0x1(%r14),%eax
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    291e:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
        my_thread_data[1] = &thread_data[x]; 
    2923:	48 89 da             	mov    %rbx,%rdx
    2926:	41 b8 01 00 00 00    	mov    $0x1,%r8d
        other = abs(x - 1) % total_threads;
    292c:	48 89 c5             	mov    %rax,%rbp
        my_thread_data[0] = &thread_data[other]; 
    292f:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    2933:	48 c1 e0 06          	shl    $0x6,%rax
    2937:	48 01 f8             	add    %rdi,%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    293a:	49 8d 7c 24 08       	lea    0x8(%r12),%rdi
    293f:	48 89 7c 24 18       	mov    %rdi,0x18(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    2944:	48 8b 7c 24 70       	mov    0x70(%rsp),%rdi
    2949:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
    294e:	89 e9                	mov    %ebp,%ecx
    2950:	44 89 f2             	mov    %r14d,%edx
    2953:	49 89 04 24          	mov    %rax,(%r12)
    2957:	48 8d 35 f2 4c 00 00 	lea    0x4cf2(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    295e:	31 c0                	xor    %eax,%eax
    2960:	48 89 7b 48          	mov    %rdi,0x48(%rbx)
    2964:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].thread_index = 1;
    2969:	44 89 43 04          	mov    %r8d,0x4(%rbx)
    296d:	e8 de fa ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].other = other;
    2972:	89 ab b8 00 00 00    	mov    %ebp,0xb8(%rbx)
    2978:	31 c0                	xor    %eax,%eax
    297a:	44 89 f2             	mov    %r14d,%edx
    297d:	8b 4c 24 38          	mov    0x38(%rsp),%ecx
    2981:	48 8d 35 f8 4c 00 00 	lea    0x4cf8(%rip),%rsi        # 7680 <_IO_stdin_used+0x680>
    2988:	bf 01 00 00 00       	mov    $0x1,%edi
    298d:	e8 be fa ff ff       	call   2450 <__printf_chk@plt>
        if (x < thread_count) {
    2992:	41 83 fe 01          	cmp    $0x1,%r14d
    2996:	0f 8f 26 04 00 00    	jg     2dc2 <main+0x7d2>
          CPU_SET(curcpu, sendercpu);
    299c:	48 63 44 24 38       	movslq 0x38(%rsp),%rax
    29a1:	48 89 c7             	mov    %rax,%rdi
    29a4:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    29aa:	77 13                	ja     29bf <main+0x3cf>
    29ac:	48 c1 e8 06          	shr    $0x6,%rax
    29b0:	ba 01 00 00 00       	mov    $0x1,%edx
    29b5:	89 f9                	mov    %edi,%ecx
    29b7:	48 d3 e2             	shl    %cl,%rdx
    29ba:	49 09 54 c5 00       	or     %rdx,0x0(%r13,%rax,8)
          curcpu += 2;
    29bf:	83 44 24 38 02       	addl   $0x2,0x38(%rsp)
      thread_data[x].all_threads = thread_data;
    29c4:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
      thread_data[x].cpu_set = sendercpu;
    29c9:	4c 89 ab b0 00 00 00 	mov    %r13,0xb0(%rbx)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    29d0:	be 10 00 00 00       	mov    $0x10,%esi
        for (int y = 0 ; y < total_barrier_count ; y++) {
    29d5:	45 31 ed             	xor    %r13d,%r13d
      thread_data[x].kind = KERNEL_THREAD;
    29d8:	c7 03 5f 00 00 00    	movl   $0x5f,(%rbx)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    29de:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].all_threads = thread_data;
    29e3:	48 89 43 20          	mov    %rax,0x20(%rbx)
      thread_data[x].thread_count = 2;
    29e7:	48 8b 05 b2 51 00 00 	mov    0x51b2(%rip),%rax        # 7ba0 <_IO_stdin_used+0xba0>
      thread_data[x].real_thread_index = x;
    29ee:	44 89 73 08          	mov    %r14d,0x8(%rbx)
      thread_data[x].threads = my_thread_data;
    29f2:	4c 89 63 18          	mov    %r12,0x18(%rbx)
      thread_data[x].thread_count = 2;
    29f6:	48 89 43 28          	mov    %rax,0x28(%rbx)
      thread_data[x].task_count = total_barrier_count;
    29fa:	c7 43 40 03 00 00 00 	movl   $0x3,0x40(%rbx)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a01:	e8 9a f9 ff ff       	call   23a0 <calloc@plt>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a06:	be 10 00 00 00       	mov    $0x10,%esi
    2a0b:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a10:	48 89 43 68          	mov    %rax,0x68(%rbx)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a14:	e8 87 f9 ff ff       	call   23a0 <calloc@plt>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a19:	be 28 00 00 00       	mov    $0x28,%esi
    2a1e:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].timestamp_count = 0;
    2a23:	66 0f 6f 2d 45 51 00 00 	movdqa 0x5145(%rip),%xmm5        # 7b70 <_IO_stdin_used+0xb70>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a2b:	48 89 43 70          	mov    %rax,0x70(%rbx)
      thread_data[x].timestamp_count = 0;
    2a2f:	0f 11 ab 80 00 00 00 	movups %xmm5,0x80(%rbx)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a36:	e8 65 f9 ff ff       	call   23a0 <calloc@plt>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a3b:	be 00 02 00 00       	mov    $0x200,%esi
    2a40:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2a45:	66 0f 6f 35 23 51 00 00 	movdqa 0x5123(%rip),%xmm6        # 7b70 <_IO_stdin_used+0xb70>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a4d:	48 89 83 90 00 00 00 	mov    %rax,0x90(%rbx)
      thread_data[x].task_timestamp_count = 0;
    2a54:	0f 11 b3 98 00 00 00 	movups %xmm6,0x98(%rbx)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a5b:	e8 40 f9 ff ff       	call   23a0 <calloc@plt>
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a60:	44 89 74 24 08       	mov    %r14d,0x8(%rsp)
        thread_data[x].tasks = barriers;
    2a65:	48 89 43 38          	mov    %rax,0x38(%rbx)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a69:	48 89 c5             	mov    %rax,%rbp
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a6c:	4d 63 fd             	movslq %r13d,%r15
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2a6f:	be 28 00 00 00       	mov    $0x28,%esi
    2a74:	bf 04 00 00 00       	mov    $0x4,%edi
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a79:	4d 89 fc             	mov    %r15,%r12
    2a7c:	48 8d 05 8d 11 00 00 	lea    0x118d(%rip),%rax        # 3c10 <do_protected_write>
    2a83:	49 c1 e4 09          	shl    $0x9,%r12
    2a87:	4c 01 e5             	add    %r12,%rbp
    2a8a:	48 89 85 20 01 00 00 	mov    %rax,0x120(%rbp)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2a91:	e8 0a f9 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2a96:	48 89 85 70 01 00 00 	mov    %rax,0x170(%rbp)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2a9d:	49 89 c0             	mov    %rax,%r8
            if ( y == x) {
    2aa0:	48 89 c5             	mov    %rax,%rbp
    2aa3:	4c 8d b0 a0 00 00 00 	lea    0xa0(%rax),%r14
    2aaa:	8b 44 24 08          	mov    0x8(%rsp),%eax
    2aae:	41 39 c5             	cmp    %eax,%r13d
    2ab1:	0f 84 18 03 00 00    	je     2dcf <main+0x7df>
    2ab7:	4c 89 64 24 10       	mov    %r12,0x10(%rsp)
    2abc:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ac1:	be 08 00 00 00       	mov    $0x8,%esi
    2ac6:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2acb:	48 83 c5 28          	add    $0x28,%rbp
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2acf:	e8 cc f8 ff ff       	call   23a0 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ad4:	be 08 00 00 00       	mov    $0x8,%esi
    2ad9:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ade:	49 89 c4             	mov    %rax,%r12
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ae1:	e8 ba f8 ff ff       	call   23a0 <calloc@plt>
            struct Data *data = calloc(2, sizeof(struct Data));
    2ae6:	be 80 01 00 00       	mov    $0x180,%esi
    2aeb:	bf 02 00 00 00       	mov    $0x2,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2af0:	48 89 c3             	mov    %rax,%rbx
            struct Data *data = calloc(2, sizeof(struct Data));
    2af3:	e8 a8 f8 ff ff       	call   23a0 <calloc@plt>
            data[0].messages_count = 0;
    2af8:	66 0f 6f 05 80 50 00 00 	movdqa 0x5080(%rip),%xmm0        # 7b80 <_IO_stdin_used+0xb80>
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2b00:	c7 45 f8 02 00 00 00 	movl   $0x2,-0x8(%rbp)
            mailboxes[b].higher = &data[1];
    2b07:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
            mailboxes[b].lower = &data[0];
    2b0e:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
            mailboxes[b].higher = &data[1];
    2b12:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
            data[0].available = 0;
    2b16:	c7 80 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rax)
            data[0].messages = messages;
    2b20:	4c 89 20             	mov    %r12,(%rax)
            data[1].messages = messages2;
    2b23:	48 89 98 80 01 00 00 	mov    %rbx,0x180(%rax)
            data[1].available = 0;
    2b2a:	c7 80 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rax)
            data[0].messages_count = 0;
    2b34:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
            data[1].messages_count = 0;
    2b3b:	0f 29 80 00 02 00 00 	movaps %xmm0,0x200(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2b42:	49 39 ee             	cmp    %rbp,%r14
    2b45:	0f 85 76 ff ff ff    	jne    2ac1 <main+0x4d1>
    2b4b:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
    2b50:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
          char *message = malloc(sizeof(char) * 256);
    2b55:	be 01 00 00 00       	mov    $0x1,%esi
    2b5a:	bf 00 01 00 00       	mov    $0x100,%edi
    2b5f:	e8 3c f8 ff ff       	call   23a0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2b64:	bf 18 00 00 00       	mov    $0x18,%edi
          char *message = malloc(sizeof(char) * 256);
    2b69:	48 89 c5             	mov    %rax,%rbp
          struct Message *messaged = malloc(sizeof(struct Message));
    2b6c:	e8 9f f8 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2b71:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    2b76:	48 89 ef             	mov    %rbp,%rdi
    2b79:	45 89 e9             	mov    %r13d,%r9d
    2b7c:	ba 00 01 00 00       	mov    $0x100,%edx
    2b81:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2b86:	be 01 00 00 00       	mov    $0x1,%esi
    2b8b:	31 c0                	xor    %eax,%eax
    2b8d:	48 8d 0d 34 4b 00 00 	lea    0x4b34(%rip),%rcx        # 76c8 <_IO_stdin_used+0x6c8>
    2b94:	e8 87 f9 ff ff       	call   2520 <__sprintf_chk@plt>
          messaged->message = message;
    2b99:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
          messaged->thread_index = thread_data[x].real_thread_index;
    2b9e:	48 63 43 08          	movslq 0x8(%rbx),%rax
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2ba2:	be 20 00 00 00       	mov    $0x20,%esi
    2ba7:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->message = message;
    2bac:	49 89 2a             	mov    %rbp,(%r10)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2baf:	48 8b 6b 38          	mov    0x38(%rbx),%rbp
          messaged->thread_index = thread_data[x].real_thread_index;
    2bb3:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2bb7:	41 8d 45 01          	lea    0x1(%r13),%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2bbb:	49 01 ec             	add    %rbp,%r12
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2bbe:	83 e0 01             	and    $0x1,%eax
          messaged->task_index = y;
    2bc1:	4d 89 7a 10          	mov    %r15,0x10(%r10)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2bc5:	41 c7 04 24 41 00 00 00 	movl   $0x41,(%r12)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2bcd:	41 89 84 24 90 01 00 00 	mov    %eax,0x190(%r12)
          thread_data[x].tasks[y].message = messaged;
    2bd5:	4d 89 94 24 88 01 00 00 	mov    %r10,0x188(%r12)
          thread_data[x].tasks[y].sending = 1;
    2bdd:	41 c7 84 24 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r12)
          thread_data[x].tasks[y].snapshot_count = 99;
    2be9:	49 c7 84 24 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%r12)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2bf5:	e8 a6 f7 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    2bfa:	49 c7 84 24 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%r12)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2c06:	49 89 84 24 50 01 00 00 	mov    %rax,0x150(%r12)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2c0e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    2c13:	48 8b 00             	mov    (%rax),%rax
    2c16:	8b 50 04             	mov    0x4(%rax),%edx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2c19:	49 89 84 24 28 01 00 00 	mov    %rax,0x128(%r12)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2c21:	41 89 94 24 30 01 00 00 	mov    %edx,0x130(%r12)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2c29:	48 39 d8             	cmp    %rbx,%rax
    2c2c:	0f 85 d1 0e 00 00    	jne    3b03 <main+0x1513>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2c32:	66 0f 6f 15 56 4f 00 00 	movdqa 0x4f56(%rip),%xmm2        # 7b90 <_IO_stdin_used+0xb90>
          thread_data[x].tasks[y].available = 1;
    2c3a:	48 8b 05 67 4f 00 00 	mov    0x4f67(%rip),%rax        # 7ba8 <_IO_stdin_used+0xba8>
          thread_data[x].tasks[y].arrived = 0;
    2c41:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
    2c4d:	41 c7 84 24 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%r12)
          thread_data[x].tasks[y].available = 1;
    2c59:	49 89 84 24 44 01 00 00 	mov    %rax,0x144(%r12)
          thread_data[x].tasks[y].task_index = y;
    2c61:	45 89 6c 24 04       	mov    %r13d,0x4(%r12)
          thread_data[x].tasks[y].thread_count = 2;
    2c66:	41 0f 11 94 24 34 01 00 00 	movups %xmm2,0x134(%r12)
          if (y == barrier_count - 1) {
    2c6f:	41 83 fd 01          	cmp    $0x1,%r13d
    2c73:	0f 84 13 01 00 00    	je     2d8c <main+0x79c>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2c79:	45 85 ed             	test   %r13d,%r13d
    2c7c:	0f 84 f0 00 00 00    	je     2d72 <main+0x782>
               thread_data[x].tasks[y].run = barriered_work; 
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2c82:	bf 01 00 00 00       	mov    $0x1,%edi
    2c87:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    2c8c:	48 8d 05 fd 32 00 00 	lea    0x32fd(%rip),%rax        # 5f90 <barriered_work>
    2c93:	44 8b 74 24 08       	mov    0x8(%rsp),%r14d
    2c98:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2ca0:	48 81 c3 c0 00 00 00 	add    $0xc0,%rbx
        thread_data[x].buffers_count = buffers_per_thread;
    2ca7:	c7 43 fc 01 00 00 00 	movl   $0x1,-0x4(%rbx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2cae:	41 83 c6 01          	add    $0x1,%r14d
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2cb2:	e8 e9 f6 ff ff       	call   23a0 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2cb7:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2cbc:	66 0f 6f 64 24 60    	movdqa 0x60(%rsp),%xmm4
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2cc2:	48 89 43 90          	mov    %rax,-0x70(%rbx)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2cc6:	48 89 38             	mov    %rdi,(%rax)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2cc9:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    2cce:	48 83 c7 10          	add    $0x10,%rdi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2cd2:	83 44 24 48 01       	addl   $0x1,0x48(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2cd7:	48 8b 00             	mov    (%rax),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    2cda:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    2cdf:	c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2ce9:	48 89 85 28 05 00 00 	mov    %rax,0x528(%rbp)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2cf0:	c7 85 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rbp)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    2cfa:	c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2d04:	8b 83 44 ff ff ff    	mov    -0xbc(%rbx),%eax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2d0a:	0f 11 a5 18 05 00 00 	movups %xmm4,0x518(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2d11:	89 85 30 05 00 00    	mov    %eax,0x530(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
    2d17:	48 8b 05 8a 4e 00 00 	mov    0x4e8a(%rip),%rax        # 7ba8 <_IO_stdin_used+0xba8>
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2d1e:	c7 85 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
    2d28:	48 89 85 44 05 00 00 	mov    %rax,0x544(%rbp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2d2f:	44 39 74 24 50       	cmp    %r14d,0x50(%rsp)
    2d34:	0f 85 98 fb ff ff    	jne    28d2 <main+0x2e2>
    2d3a:	8b 4c 24 50          	mov    0x50(%rsp),%ecx
    2d3e:	48 8b 7c 24 70       	mov    0x70(%rsp),%rdi
    2d43:	48 8b 9c 24 80 00 00 00 	mov    0x80(%rsp),%rbx
    2d4b:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    2d50:	4c 8b a4 24 88 00 00 00 	mov    0x88(%rsp),%r12
  for (int k = 0 ; k < group_count ; k++) {
    2d58:	83 c1 02             	add    $0x2,%ecx
    2d5b:	48 83 c7 18          	add    $0x18,%rdi
    2d5f:	48 85 db             	test   %rbx,%rbx
    2d62:	0f 85 50 03 00 00    	jne    30b8 <main+0xac8>
    2d68:	bb 01 00 00 00       	mov    $0x1,%ebx
    2d6d:	e9 16 fb ff ff       	jmp    2888 <main+0x298>
    2d72:	48 8d 05 57 35 00 00 	lea    0x3557(%rip),%rax        # 62d0 <barriered_work_ingest_andwork>
    2d79:	41 bd 01 00 00 00    	mov    $0x1,%r13d
            thread_data[x].tasks[y].run = barriered_work; 
    2d7f:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2d87:	e9 e0 fc ff ff       	jmp    2a6c <main+0x47c>
    2d8c:	48 8d 05 fd 31 00 00 	lea    0x31fd(%rip),%rax        # 5f90 <barriered_work>
    2d93:	41 bd 02 00 00 00    	mov    $0x2,%r13d
    2d99:	eb e4                	jmp    2d7f <main+0x78f>
        other = (x + 1) % total_threads;
    2d9b:	41 8d 46 01          	lea    0x1(%r14),%eax
        my_thread_data[1] = &thread_data[other]; 
    2d9f:	4c 89 64 24 18       	mov    %r12,0x18(%rsp)
    2da4:	45 31 c0             	xor    %r8d,%r8d
    2da7:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
        other = (x + 1) % total_threads;
    2dab:	48 89 c5             	mov    %rax,%rbp
        my_thread_data[1] = &thread_data[other]; 
    2dae:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    2db3:	48 c1 e2 06          	shl    $0x6,%rdx
    2db7:	48 01 c2             	add    %rax,%rdx
        my_thread_data[0] = &thread_data[x]; 
    2dba:	48 89 d8             	mov    %rbx,%rax
    2dbd:	e9 82 fb ff ff       	jmp    2944 <main+0x354>
            CPU_SET(j, sendercpu);
    2dc2:	49 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%r13)
          for (int j = 0 ; j < cores ; j++) {
    2dca:	e9 f5 fb ff ff       	jmp    29c4 <main+0x3d4>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2dcf:	be 08 00 00 00       	mov    $0x8,%esi
    2dd4:	bf 01 00 00 00       	mov    $0x1,%edi
    2dd9:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2dde:	4c 8d 35 bb 48 00 00 	lea    0x48bb(%rip),%r14        # 76a0 <_IO_stdin_used+0x6a0>
    2de5:	e8 b6 f5 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2dea:	be 08 00 00 00       	mov    $0x8,%esi
    2def:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2df4:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2dfc:	e8 9f f5 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2e01:	be 80 01 00 00       	mov    $0x180,%esi
    2e06:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e0b:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    2e13:	e8 88 f5 ff ff       	call   23a0 <calloc@plt>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2e18:	41 f6 c5 01          	test   $0x1,%r13b
    2e1c:	41 8d 4d 01          	lea    0x1(%r13),%ecx
    2e20:	4c 89 f6             	mov    %r14,%rsi
              mailboxes[b].lower = &data[0];
    2e23:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
              struct Data *data = calloc(2, sizeof(struct Data));
    2e28:	49 89 c1             	mov    %rax,%r9
    2e2b:	bf 01 00 00 00       	mov    $0x1,%edi
              mailboxes[b].higher = &data[1];
    2e30:	4c 89 4c 24 20       	mov    %r9,0x20(%rsp)
              mailboxes[b].lower = &data[0];
    2e35:	49 89 00             	mov    %rax,(%r8)
              mailboxes[b].higher = &data[1];
    2e38:	48 8d 80 80 01 00 00 	lea    0x180(%rax),%rax
    2e3f:	49 89 40 08          	mov    %rax,0x8(%r8)
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2e43:	41 8d 45 ff          	lea    -0x1(%r13),%eax
    2e47:	0f 44 c1             	cmove  %ecx,%eax
              mailboxes[b].kind = MAILBOX_FRIEND;
    2e4a:	41 c7 40 20 01 00 00 00 	movl   $0x1,0x20(%r8)
    2e52:	31 d2                	xor    %edx,%edx
    2e54:	41 89 40 24          	mov    %eax,0x24(%r8)
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2e58:	89 c5                	mov    %eax,%ebp
    2e5a:	89 c1                	mov    %eax,%ecx
    2e5c:	31 c0                	xor    %eax,%eax
    2e5e:	e8 ed f5 ff ff       	call   2450 <__printf_chk@plt>
              data[0].messages = messages;
    2e63:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    2e68:	4c 8b 9c 24 98 00 00 00 	mov    0x98(%rsp),%r11
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e70:	be 08 00 00 00       	mov    $0x8,%esi
              data[1].messages = messages2;
    2e75:	4c 8b 94 24 90 00 00 00 	mov    0x90(%rsp),%r10
              data[0].messages_count = 0;
    2e7d:	66 0f 6f 3d fb 4c 00 00 	movdqa 0x4cfb(%rip),%xmm7        # 7b80 <_IO_stdin_used+0xb80>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e85:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages = messages;
    2e8a:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2e8d:	4d 89 91 80 01 00 00 	mov    %r10,0x180(%r9)
              data[0].messages_count = 0;
    2e94:	41 0f 29 b9 80 00 00 00 	movaps %xmm7,0x80(%r9)
              data[1].messages_count = 0;
    2e9c:	41 0f 29 b9 00 02 00 00 	movaps %xmm7,0x200(%r9)
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ea4:	e8 f7 f4 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ea9:	be 08 00 00 00       	mov    $0x8,%esi
    2eae:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2eb3:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ebb:	e8 e0 f4 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2ec0:	be 80 01 00 00       	mov    $0x180,%esi
    2ec5:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2eca:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    2ed2:	e8 c9 f4 ff ff       	call   23a0 <calloc@plt>
              mailboxes[b].lower = &data[0];
    2ed7:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    2edc:	89 e9                	mov    %ebp,%ecx
    2ede:	4c 89 f6             	mov    %r14,%rsi
              struct Data *data = calloc(2, sizeof(struct Data));
    2ee1:	49 89 c1             	mov    %rax,%r9
    2ee4:	ba 01 00 00 00       	mov    $0x1,%edx
    2ee9:	bf 01 00 00 00       	mov    $0x1,%edi
              mailboxes[b].lower = &data[0];
    2eee:	49 89 40 28          	mov    %rax,0x28(%r8)
              mailboxes[b].higher = &data[1];
    2ef2:	48 8d 80 80 01 00 00 	lea    0x180(%rax),%rax
    2ef9:	49 89 40 30          	mov    %rax,0x30(%r8)
    2efd:	31 c0                	xor    %eax,%eax
              mailboxes[b].kind = MAILBOX_FRIEND;
    2eff:	41 c7 40 48 01 00 00 00 	movl   $0x1,0x48(%r8)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2f07:	41 89 68 4c          	mov    %ebp,0x4c(%r8)
              mailboxes[b].higher = &data[1];
    2f0b:	4c 89 4c 24 20       	mov    %r9,0x20(%rsp)
    2f10:	e8 3b f5 ff ff       	call   2450 <__printf_chk@plt>
              data[0].messages = messages;
    2f15:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    2f1a:	4c 8b 9c 24 98 00 00 00 	mov    0x98(%rsp),%r11
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f22:	be 08 00 00 00       	mov    $0x8,%esi
              data[1].messages = messages2;
    2f27:	4c 8b 94 24 90 00 00 00 	mov    0x90(%rsp),%r10
              data[0].messages_count = 0;
    2f2f:	66 0f 6f 35 49 4c 00 00 	movdqa 0x4c49(%rip),%xmm6        # 7b80 <_IO_stdin_used+0xb80>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f37:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages = messages;
    2f3c:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2f3f:	4d 89 91 80 01 00 00 	mov    %r10,0x180(%r9)
              data[0].messages_count = 0;
    2f46:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    2f4e:	41 0f 29 b1 00 02 00 00 	movaps %xmm6,0x200(%r9)
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f56:	e8 45 f4 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f5b:	be 08 00 00 00       	mov    $0x8,%esi
    2f60:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f65:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f6d:	e8 2e f4 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2f72:	be 80 01 00 00       	mov    $0x180,%esi
    2f77:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f7c:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    2f84:	e8 17 f4 ff ff       	call   23a0 <calloc@plt>
              mailboxes[b].lower = &data[0];
    2f89:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    2f8e:	89 e9                	mov    %ebp,%ecx
    2f90:	4c 89 f6             	mov    %r14,%rsi
              struct Data *data = calloc(2, sizeof(struct Data));
    2f93:	49 89 c1             	mov    %rax,%r9
    2f96:	ba 02 00 00 00       	mov    $0x2,%edx
    2f9b:	bf 01 00 00 00       	mov    $0x1,%edi
              mailboxes[b].lower = &data[0];
    2fa0:	49 89 40 50          	mov    %rax,0x50(%r8)
              mailboxes[b].higher = &data[1];
    2fa4:	48 8d 80 80 01 00 00 	lea    0x180(%rax),%rax
    2fab:	49 89 40 58          	mov    %rax,0x58(%r8)
    2faf:	31 c0                	xor    %eax,%eax
              mailboxes[b].kind = MAILBOX_FRIEND;
    2fb1:	41 c7 40 70 01 00 00 00 	movl   $0x1,0x70(%r8)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2fb9:	41 89 68 74          	mov    %ebp,0x74(%r8)
              mailboxes[b].higher = &data[1];
    2fbd:	4c 89 4c 24 20       	mov    %r9,0x20(%rsp)
    2fc2:	e8 89 f4 ff ff       	call   2450 <__printf_chk@plt>
              data[0].messages = messages;
    2fc7:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    2fcc:	4c 8b 9c 24 98 00 00 00 	mov    0x98(%rsp),%r11
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2fd4:	be 08 00 00 00       	mov    $0x8,%esi
              data[1].messages = messages2;
    2fd9:	4c 8b 94 24 90 00 00 00 	mov    0x90(%rsp),%r10
              data[0].messages_count = 0;
    2fe1:	66 0f 6f 25 97 4b 00 00 	movdqa 0x4b97(%rip),%xmm4        # 7b80 <_IO_stdin_used+0xb80>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2fe9:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages = messages;
    2fee:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2ff1:	4d 89 91 80 01 00 00 	mov    %r10,0x180(%r9)
              data[0].messages_count = 0;
    2ff8:	41 0f 29 a1 80 00 00 00 	movaps %xmm4,0x80(%r9)
              data[1].messages_count = 0;
    3000:	41 0f 29 a1 00 02 00 00 	movaps %xmm4,0x200(%r9)
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3008:	e8 93 f3 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    300d:	be 08 00 00 00       	mov    $0x8,%esi
    3012:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3017:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    301f:	e8 7c f3 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    3024:	be 80 01 00 00       	mov    $0x180,%esi
    3029:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    302e:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    3033:	e8 68 f3 ff ff       	call   23a0 <calloc@plt>
              mailboxes[b].lower = &data[0];
    3038:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    303d:	89 e9                	mov    %ebp,%ecx
    303f:	4c 89 f6             	mov    %r14,%rsi
              struct Data *data = calloc(2, sizeof(struct Data));
    3042:	49 89 c1             	mov    %rax,%r9
    3045:	ba 03 00 00 00       	mov    $0x3,%edx
    304a:	bf 01 00 00 00       	mov    $0x1,%edi
              mailboxes[b].lower = &data[0];
    304f:	49 89 40 78          	mov    %rax,0x78(%r8)
              mailboxes[b].higher = &data[1];
    3053:	48 8d 80 80 01 00 00 	lea    0x180(%rax),%rax
    305a:	49 89 80 80 00 00 00 	mov    %rax,0x80(%r8)
    3061:	31 c0                	xor    %eax,%eax
              mailboxes[b].kind = MAILBOX_FRIEND;
    3063:	41 c7 80 98 00 00 00 01 00 00 00 	movl   $0x1,0x98(%r8)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    306e:	41 89 a8 9c 00 00 00 	mov    %ebp,0x9c(%r8)
              mailboxes[b].higher = &data[1];
    3075:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    307a:	e8 d1 f3 ff ff       	call   2450 <__printf_chk@plt>
              data[0].messages = messages;
    307f:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
              data[1].messages = messages2;
    3084:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
              data[0].messages_count = 0;
    3089:	66 0f 6f 35 ef 4a 00 00 	movdqa 0x4aef(%rip),%xmm6        # 7b80 <_IO_stdin_used+0xb80>
              data[0].messages = messages;
    3091:	4c 8b 9c 24 90 00 00 00 	mov    0x90(%rsp),%r11
              data[1].messages = messages2;
    3099:	4d 89 91 80 01 00 00 	mov    %r10,0x180(%r9)
              data[0].messages = messages;
    30a0:	4d 89 19             	mov    %r11,(%r9)
              data[0].messages_count = 0;
    30a3:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    30ab:	41 0f 29 b1 00 02 00 00 	movaps %xmm6,0x200(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    30b3:	e9 9d fa ff ff       	jmp    2b55 <main+0x565>
    30b8:	ba 05 00 00 00       	mov    $0x5,%edx
    30bd:	48 8d 35 d8 42 00 00 	lea    0x42d8(%rip),%rsi        # 739c <_IO_stdin_used+0x39c>
    30c4:	bf 01 00 00 00       	mov    $0x1,%edi
    30c9:	31 c0                	xor    %eax,%eax
    30cb:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    30d0:	48 89 5c 24 48       	mov    %rbx,0x48(%rsp)
    30d5:	e8 76 f3 ff ff       	call   2450 <__printf_chk@plt>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    30da:	be 08 00 00 00       	mov    $0x8,%esi
    30df:	bf 02 00 00 00       	mov    $0x2,%edi
    30e4:	e8 b7 f2 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    30e9:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    30ee:	be 38 00 00 00       	mov    $0x38,%esi
    30f3:	bf 08 00 00 00       	mov    $0x8,%edi
    my_thread_data[0] = &thread_data[x]; 
    30f8:	4d 8d b3 c0 03 00 00 	lea    0x3c0(%r11),%r14
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    30ff:	4c 89 58 08          	mov    %r11,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3103:	4d 8d ab c0 00 00 00 	lea    0xc0(%r11),%r13
    thread_data[x].threads = my_thread_data;
    310a:	49 89 83 d8 03 00 00 	mov    %rax,0x3d8(%r11)
    my_thread_data[0] = &thread_data[x]; 
    3111:	4c 89 30             	mov    %r14,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3114:	49 8b 43 38          	mov    0x38(%r11),%rax
    thread_data[x].thread_count = 2;
    3118:	41 c7 83 e8 03 00 00 02 00 00 00 	movl   $0x2,0x3e8(%r11)
    thread_data[x].thread_index = 0;
    3123:	41 c7 83 c4 03 00 00 00 00 00 00 	movl   $0x0,0x3c4(%r11)
    thread_data[x].task_count = total_barrier_count;
    312e:	41 c7 83 00 04 00 00 03 00 00 00 	movl   $0x3,0x400(%r11)
    thread_data[n].tasks[0].scheduled = 1;
    3139:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3143:	49 8b 83 f8 00 00 00 	mov    0xf8(%r11),%rax
    314a:	4c 89 5c 24 20       	mov    %r11,0x20(%rsp)
    314f:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3159:	e8 42 f2 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    315e:	be 38 00 00 00       	mov    $0x38,%esi
    3163:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3168:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    316b:	e8 30 f2 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3170:	be 38 00 00 00       	mov    $0x38,%esi
    3175:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    317a:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    317d:	e8 1e f2 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3182:	be 38 00 00 00       	mov    $0x38,%esi
    3187:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    318c:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3191:	e8 0a f2 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3196:	be 08 00 00 00       	mov    $0x8,%esi
    319b:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    31a0:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    31a5:	e8 f6 f1 ff ff       	call   23a0 <calloc@plt>


  int timer_threadi = group_count * thread_count;
  thread_data[timer_threadi].type = TIMER;
    31aa:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    31af:	be 08 00 00 00       	mov    $0x8,%esi
    31b4:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    31b9:	48 89 c5             	mov    %rax,%rbp
    31bc:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  thread_data[timer_threadi].task_count = total_barrier_count;
    31c1:	48 8b 05 e8 49 00 00 	mov    0x49e8(%rip),%rax        # 7bb0 <_IO_stdin_used+0xbb0>
  thread_data[timer_threadi].type = TIMER;
    31c8:	41 c7 83 0c 03 00 00 00 00 00 00 	movl   $0x0,0x30c(%r11)
  thread_data[timer_threadi].task_count = total_barrier_count;
    31d3:	49 89 83 40 03 00 00 	mov    %rax,0x340(%r11)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    31da:	e8 c1 f1 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    31df:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    31e4:	bf 01 00 00 00       	mov    $0x1,%edi
    31e9:	48 8d 35 bb 41 00 00 	lea    0x41bb(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    31f0:	4c 89 70 28          	mov    %r14,0x28(%rax)
    31f4:	49 8d 93 80 01 00 00 	lea    0x180(%r11),%rdx
    31fb:	49 8d 8b 00 03 00 00 	lea    0x300(%r11),%rcx
    3202:	4c 89 18             	mov    %r11,(%rax)
    3205:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3209:	49 8d 93 40 02 00 00 	lea    0x240(%r11),%rdx
    3210:	4d 8d a3 80 04 00 00 	lea    0x480(%r11),%r12
    3217:	48 89 50 18          	mov    %rdx,0x18(%rax)
    321b:	49 8d 93 40 05 00 00 	lea    0x540(%r11),%rdx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3222:	49 89 83 18 03 00 00 	mov    %rax,0x318(%r11)
    my_thread_data[n] = &thread_data[n]; 
    3229:	48 89 48 20          	mov    %rcx,0x20(%rax)
    322d:	4c 89 60 30          	mov    %r12,0x30(%rax)
    3231:	48 89 50 38          	mov    %rdx,0x38(%rax)
    3235:	ba 04 00 00 00       	mov    $0x4,%edx
    323a:	4c 89 68 08          	mov    %r13,0x8(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    323e:	48 8b 05 73 49 00 00 	mov    0x4973(%rip),%rax        # 7bb8 <_IO_stdin_used+0xbb8>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3245:	41 c7 83 30 03 00 00 04 00 00 00 	movl   $0x4,0x330(%r11)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3250:	49 89 83 28 03 00 00 	mov    %rax,0x328(%r11)
    3257:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    3259:	41 c7 83 04 03 00 00 00 00 00 00 	movl   $0x0,0x304(%r11)
    my_thread_data[n] = &thread_data[n]; 
    3264:	48 89 4c 24 28       	mov    %rcx,0x28(%rsp)
    3269:	e8 e2 f1 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    326e:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3273:	48 8d 15 56 0b 00 00 	lea    0xb56(%rip),%rdx        # 3dd0 <timer_thread>
    327a:	48 8d b3 e0 00 00 00 	lea    0xe0(%rbx),%rsi
    3281:	48 8d 7d 20          	lea    0x20(%rbp),%rdi
    3285:	e8 e6 f1 ff ff       	call   2470 <pthread_create@plt>
    328a:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
  for (int k = 0 ; k < group_count ; k++) {
    328f:	45 31 c9             	xor    %r9d,%r9d
    3292:	48 89 e9             	mov    %rbp,%rcx
    3295:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    329a:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    32a0:	4c 89 f8             	mov    %r15,%rax
    32a3:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    32a8:	4c 89 da             	mov    %r11,%rdx
    32ab:	45 89 d6             	mov    %r10d,%r14d
    32ae:	4c 89 64 24 28       	mov    %r12,0x28(%rsp)
    32b3:	45 89 cc             	mov    %r9d,%r12d
    for (int d = 0 ; d < threads_per_group ; d++) {
    32b6:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    32bb:	47 8d 3c 24          	lea    (%r12,%r12,1),%r15d
  int curcpu = 0;
    32bf:	49 89 c5             	mov    %rax,%r13
    32c2:	48 89 cd             	mov    %rcx,%rbp
    32c5:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    32ca:	48 89 d3             	mov    %rdx,%rbx
    32cd:	48 89 54 24 60       	mov    %rdx,0x60(%rsp)
    32d2:	4c 89 5c 24 70       	mov    %r11,0x70(%rsp)
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    32d7:	c7 43 0c 01 00 00 00 	movl   $0x1,0xc(%rbx)
    32de:	44 89 fa             	mov    %r15d,%edx
    32e1:	44 89 e1             	mov    %r12d,%ecx
    32e4:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    32e6:	c7 43 44 01 00 00 00 	movl   $0x1,0x44(%rbx)
    32ed:	48 8d 35 fc 43 00 00 	lea    0x43fc(%rip),%rsi        # 76f0 <_IO_stdin_used+0x6f0>
    32f4:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    32f9:	41 83 c7 01          	add    $0x1,%r15d
    32fd:	e8 4e f1 ff ff       	call   2450 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3302:	48 89 d9             	mov    %rbx,%rcx
    3305:	4c 89 ee             	mov    %r13,%rsi
    3308:	48 89 ef             	mov    %rbp,%rdi
    330b:	48 8d 15 1e 28 00 00 	lea    0x281e(%rip),%rdx        # 5b30 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3312:	48 81 c3 c0 00 00 00 	add    $0xc0,%rbx
    3319:	48 83 c5 08          	add    $0x8,%rbp
    331d:	49 83 c5 38          	add    $0x38,%r13
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3321:	e8 4a f1 ff ff       	call   2470 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3326:	48 8b 53 f0          	mov    -0x10(%rbx),%rdx
    332a:	48 8b 7d f8          	mov    -0x8(%rbp),%rdi
    332e:	be 08 00 00 00       	mov    $0x8,%esi
    3333:	e8 a8 ef ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3338:	45 39 fe             	cmp    %r15d,%r14d
    333b:	75 9a                	jne    32d7 <main+0xce7>
  for (int k = 0 ; k < group_count ; k++) {
    333d:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3342:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    3347:	41 83 c6 02          	add    $0x2,%r14d
    334b:	48 8b 54 24 60       	mov    0x60(%rsp),%rdx
    3350:	4c 8b 5c 24 70       	mov    0x70(%rsp),%r11
    3355:	48 83 c1 10          	add    $0x10,%rcx
    3359:	48 83 c0 70          	add    $0x70,%rax
    335d:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
    3364:	45 85 e4             	test   %r12d,%r12d
    3367:	75 0b                	jne    3374 <main+0xd84>
    3369:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    336f:	e9 42 ff ff ff       	jmp    32b6 <main+0xcc6>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3374:	be d8 00 00 00       	mov    $0xd8,%esi
    3379:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    337e:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
    thread_data[x].task_count = 0;
    3383:	48 8b 1d 36 48 00 00 	mov    0x4836(%rip),%rbx        # 7bc0 <_IO_stdin_used+0xbc0>
    thread_data[x].type = IO;
    338a:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    338f:	4c 8b 64 24 28       	mov    0x28(%rsp),%r12
    thread_data[x].task_count = 0;
    3394:	4c 89 5c 24 20       	mov    %r11,0x20(%rsp)
    thread_data[x].type = IO;
    3399:	41 c7 83 cc 03 00 00 02 00 00 00 	movl   $0x2,0x3cc(%r11)
    thread_data[x].task_count = 0;
    33a4:	49 89 9b 00 04 00 00 	mov    %rbx,0x400(%r11)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    33ab:	e8 f0 ef ff ff       	call   23a0 <calloc@plt>
    33b0:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    33b5:	be 00 08 00 00       	mov    $0x800,%esi
    33ba:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    33bc:	49 89 83 18 04 00 00 	mov    %rax,0x418(%r11)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    33c3:	e8 e8 f0 ff ff       	call   24b0 <eventfd@plt>
    33c8:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    33cd:	be 08 00 00 00       	mov    $0x8,%esi
    33d2:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    33d7:	41 89 83 20 04 00 00 	mov    %eax,0x420(%r11)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    33de:	e8 bd ef ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    33e3:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    33e8:	ba 05 00 00 00       	mov    $0x5,%edx
    33ed:	48 8d 35 d5 3f 00 00 	lea    0x3fd5(%rip),%rsi        # 73c9 <_IO_stdin_used+0x3c9>
    33f4:	4c 89 68 08          	mov    %r13,0x8(%rax)
    33f8:	bf 01 00 00 00       	mov    $0x1,%edi
    33fd:	4c 89 18             	mov    %r11,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    3400:	49 89 83 d8 03 00 00 	mov    %rax,0x3d8(%r11)
    3407:	31 c0                	xor    %eax,%eax
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3409:	41 c7 83 e8 03 00 00 02 00 00 00 	movl   $0x2,0x3e8(%r11)
    thread_data[x].thread_index = x;
    3414:	41 c7 83 c4 03 00 00 05 00 00 00 	movl   $0x5,0x3c4(%r11)
    341f:	e8 2c f0 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3424:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    3429:	4c 89 f1             	mov    %r14,%rcx
    342c:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    3431:	48 8d 15 08 1f 00 00 	lea    0x1f08(%rip),%rdx        # 5340 <io_thread>
    3438:	49 8d 7f 28          	lea    0x28(%r15),%rdi
    343c:	48 81 c6 18 01 00 00 	add    $0x118,%rsi
    3443:	4d 8d 77 30          	lea    0x30(%r15),%r14
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3447:	41 bf 06 00 00 00    	mov    $0x6,%r15d
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    344d:	e8 1e f0 ff ff       	call   2470 <pthread_create@plt>
    3452:	ba 06 00 00 00       	mov    $0x6,%edx
    3457:	48 8d 35 82 3f 00 00 	lea    0x3f82(%rip),%rsi        # 73e0 <_IO_stdin_used+0x3e0>
    345e:	31 c0                	xor    %eax,%eax
    3460:	bf 01 00 00 00       	mov    $0x1,%edi
    3465:	e8 e6 ef ff ff       	call   2450 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    346a:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    346f:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    3474:	4c 89 e8             	mov    %r13,%rax
    3477:	4d 89 f5             	mov    %r14,%r13
    347a:	49 89 c6             	mov    %rax,%r14
    347d:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    3482:	48 81 c5 50 01 00 00 	add    $0x150,%rbp
    3489:	44 89 fa             	mov    %r15d,%edx
    348c:	48 8d 35 63 3f 00 00 	lea    0x3f63(%rip),%rsi        # 73f6 <_IO_stdin_used+0x3f6>
    3493:	bf 01 00 00 00       	mov    $0x1,%edi
    3498:	31 c0                	xor    %eax,%eax
    349a:	e8 b1 ef ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    349f:	49 89 5c 24 40       	mov    %rbx,0x40(%r12)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    34a4:	be 08 00 00 00       	mov    $0x8,%esi
    34a9:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = EXTERNAL;
    34ae:	41 c7 44 24 0c 03 00 00 00 	movl   $0x3,0xc(%r12)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    34b7:	e8 e4 ee ff ff       	call   23a0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    34bc:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    34c1:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    34c6:	41 c7 84 24 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r12)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    34d2:	49 89 44 24 50       	mov    %rax,0x50(%r12)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    34d7:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    34da:	bf 02 00 00 00       	mov    $0x2,%edi
    34df:	e8 bc ee ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    34e4:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    34e9:	4c 89 e1             	mov    %r12,%rcx
    34ec:	4c 89 ef             	mov    %r13,%rdi
    thread_data[x].threads = my_thread_data;
    34ef:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    34f4:	48 8d 15 c5 07 00 00 	lea    0x7c5(%rip),%rdx        # 3cc0 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    34fb:	49 83 c5 08          	add    $0x8,%r13
    34ff:	49 81 c4 c0 00 00 00 	add    $0xc0,%r12
      my_thread_data[n] = &thread_data[n]; 
    3506:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3509:	48 89 ee             	mov    %rbp,%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    350c:	48 83 c5 38          	add    $0x38,%rbp
      my_thread_data[n] = &thread_data[n]; 
    3510:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3514:	48 8b 05 85 46 00 00 	mov    0x4685(%rip),%rax        # 7ba0 <_IO_stdin_used+0xba0>
    thread_data[x].thread_index = x;
    351b:	45 89 bc 24 44 ff ff ff 	mov    %r15d,-0xbc(%r12)
    thread_data[x].thread_count = thread_count;
    3523:	49 89 84 24 68 ff ff ff 	mov    %rax,-0x98(%r12)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    352b:	e8 40 ef ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3530:	48 83 44 24 58 10    	addq   $0x10,0x58(%rsp)
    3536:	41 83 ff 06          	cmp    $0x6,%r15d
    353a:	75 0b                	jne    3547 <main+0xf57>
    353c:	41 bf 07 00 00 00    	mov    $0x7,%r15d
    3542:	e9 42 ff ff ff       	jmp    3489 <main+0xe99>
    3547:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    354c:	4c 8d 25 c0 3e 00 00 	lea    0x3ec0(%rip),%r12        # 7413 <_IO_stdin_used+0x413>
    3553:	4d 8d 73 04          	lea    0x4(%r11),%r14
    3557:	4d 8d ab 04 06 00 00 	lea    0x604(%r11),%r13
    355e:	4c 89 db             	mov    %r11,%rbx
    3561:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    3565:	41 8b 16             	mov    (%r14),%edx
    3568:	4c 89 e6             	mov    %r12,%rsi
    356b:	bf 01 00 00 00       	mov    $0x1,%edi
    3570:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3572:	49 81 c6 c0 00 00 00 	add    $0xc0,%r14
    3579:	e8 d2 ee ff ff       	call   2450 <__printf_chk@plt>
    357e:	4d 39 f5             	cmp    %r14,%r13
    3581:	75 de                	jne    3561 <main+0xf71>
    3583:	48 8d 3d 9c 3e 00 00 	lea    0x3e9c(%rip),%rdi        # 7426 <_IO_stdin_used+0x426>
    358a:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    358f:	45 31 f6             	xor    %r14d,%r14d
    3592:	4c 8d ac 24 a0 00 00 00 	lea    0xa0(%rsp),%r13
    359a:	e8 51 ed ff ff       	call   22f0 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    359f:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    35a4:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    35a9:	4c 8d 25 94 3e 00 00 	lea    0x3e94(%rip),%r12        # 7444 <_IO_stdin_used+0x444>
    void * result; 
    pthread_join(thread[x], &result);
    35b0:	4a 8b 3c f3          	mov    (%rbx,%r14,8),%rdi
    35b4:	4c 89 ee             	mov    %r13,%rsi
    35b7:	e8 34 ef ff ff       	call   24f0 <pthread_join@plt>
    35bc:	44 89 f2             	mov    %r14d,%edx
    35bf:	4c 89 e6             	mov    %r12,%rsi
    35c2:	bf 01 00 00 00       	mov    $0x1,%edi
    35c7:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    35c9:	49 83 c6 01          	add    $0x1,%r14
    35cd:	e8 7e ee ff ff       	call   2450 <__printf_chk@plt>
    35d2:	49 83 fe 08          	cmp    $0x8,%r14
    35d6:	75 d8                	jne    35b0 <main+0xfc0>
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    35d8:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
    35e1:	49 89 eb             	mov    %rbp,%r11
  long ingests = 0;
    35e4:	45 31 c9             	xor    %r9d,%r9d
    35e7:	31 ed                	xor    %ebp,%ebp
  long sents = 0;
    35e9:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    35f2:	4c 89 cb             	mov    %r9,%rbx
    35f5:	4c 89 df             	mov    %r11,%rdi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    35f8:	49 bc db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r12
  long sends = 0;
    3602:	48 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%rsp)
  long total = 0;
    360b:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3614:	48 89 e8             	mov    %rbp,%rax
    3617:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    361c:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
    3621:	49 89 df             	mov    %rbx,%r15
    3624:	48 f7 d8             	neg    %rax
    3627:	48 89 6c 24 60       	mov    %rbp,0x60(%rsp)
    362c:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    3631:	49 89 c6             	mov    %rax,%r14
    3634:	83 e0 30             	and    $0x30,%eax
    3637:	48 01 f0             	add    %rsi,%rax
    363a:	41 81 e6 80 01 00 00 	and    $0x180,%r14d
    3641:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3646:	8d 44 2d 00          	lea    0x0(%rbp,%rbp,1),%eax
    364a:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    364f:	49 01 fe             	add    %rdi,%r14
    3652:	89 44 24 58          	mov    %eax,0x58(%rsp)
    3656:	83 e8 01             	sub    $0x1,%eax
    3659:	89 44 24 30          	mov    %eax,0x30(%rsp)
      int x = (k * threads_per_group) + d;
    365d:	8b 7c 24 30          	mov    0x30(%rsp),%edi
    3661:	89 f8                	mov    %edi,%eax
    3663:	89 7c 24 50          	mov    %edi,0x50(%rsp)
    3667:	83 c7 01             	add    $0x1,%edi
    366a:	89 fe                	mov    %edi,%esi
    366c:	89 7c 24 30          	mov    %edi,0x30(%rsp)
        other = abs(x - 1) % total_threads;
    3670:	89 c7                	mov    %eax,%edi
    3672:	8d 40 02             	lea    0x2(%rax),%eax
    3675:	83 e6 01             	and    $0x1,%esi
    3678:	0f 45 c7             	cmovne %edi,%eax
    367b:	bf 0a 00 00 00       	mov    $0xa,%edi
    3680:	4c 63 e8             	movslq %eax,%r13
    3683:	e8 48 ec ff ff       	call   22d0 <putchar@plt>
    3688:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    368d:	bf 01 00 00 00       	mov    $0x1,%edi
    3692:	48 8d 35 bf 3d 00 00 	lea    0x3dbf(%rip),%rsi        # 7458 <_IO_stdin_used+0x458>
    3699:	48 8b 10             	mov    (%rax),%rdx
    369c:	31 c0                	xor    %eax,%eax
    369e:	e8 ad ed ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    36a3:	41 8b 56 40          	mov    0x40(%r14),%edx
    36a7:	85 d2                	test   %edx,%edx
    36a9:	0f 8e 4d 04 00 00    	jle    3afc <main+0x150c>
    36af:	48 63 f2             	movslq %edx,%rsi
    36b2:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    36b6:	31 d2                	xor    %edx,%edx
    36b8:	48 c1 e6 09          	shl    $0x9,%rsi
    36bc:	48 01 c6             	add    %rax,%rsi
    36bf:	90                   	nop
        v += thread_data[me].tasks[n].v;
    36c0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    36c7:	48 05 00 02 00 00    	add    $0x200,%rax
    36cd:	48 39 f0             	cmp    %rsi,%rax
    36d0:	75 ee                	jne    36c0 <main+0x10d0>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    36d2:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    36d7:	4b 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%rax
    36dc:	48 c1 e0 06          	shl    $0x6,%rax
    36e0:	48 01 f8             	add    %rdi,%rax
    36e3:	48 63 70 40          	movslq 0x40(%rax),%rsi
    36e7:	85 f6                	test   %esi,%esi
    36e9:	7e 27                	jle    3712 <main+0x1122>
    36eb:	48 8b 40 38          	mov    0x38(%rax),%rax
    36ef:	48 c1 e6 09          	shl    $0x9,%rsi
    36f3:	48 01 c6             	add    %rax,%rsi
    36f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3700:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3707:	48 05 00 02 00 00    	add    $0x200,%rax
    370d:	48 39 f0             	cmp    %rsi,%rax
    3710:	75 ee                	jne    3700 <main+0x1110>
    3712:	48 8d 35 54 3d 00 00 	lea    0x3d54(%rip),%rsi        # 746d <_IO_stdin_used+0x46d>
    3719:	bf 01 00 00 00       	mov    $0x1,%edi
    371e:	31 c0                	xor    %eax,%eax
    3720:	e8 2b ed ff ff       	call   2450 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3725:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    372a:	bf 01 00 00 00       	mov    $0x1,%edi
    372f:	48 8b 30             	mov    (%rax),%rsi
    3732:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    373c:	48 f7 ee             	imul   %rsi
    373f:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3743:	31 c0                	xor    %eax,%eax
    3745:	48 d1 fa             	sar    %rdx
    3748:	48 29 f2             	sub    %rsi,%rdx
    374b:	48 8d 35 ce 3f 00 00 	lea    0x3fce(%rip),%rsi        # 7720 <_IO_stdin_used+0x720>
    3752:	e8 f9 ec ff ff       	call   2450 <__printf_chk@plt>
    3757:	bf 0a 00 00 00       	mov    $0xa,%edi
    375c:	e8 6f eb ff ff       	call   22d0 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3761:	41 8b 56 40          	mov    0x40(%r14),%edx
    3765:	85 d2                	test   %edx,%edx
    3767:	7e 60                	jle    37c9 <main+0x11d9>
    3769:	49 8b 46 38          	mov    0x38(%r14),%rax
    376d:	48 63 f2             	movslq %edx,%rsi
    3770:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    3775:	48 c1 e6 09          	shl    $0x9,%rsi
    3779:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    377e:	48 01 c6             	add    %rax,%rsi
    3781:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3788:	48 8b 90 70 01 00 00 	mov    0x170(%rax),%rdx
        total += thread_data[x].tasks[n].n;
    378f:	48 03 88 08 01 00 00 	add    0x108(%rax),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3796:	48 05 00 02 00 00    	add    $0x200,%rax
        ingests += thread_data[x].tasks[n].ingest_count;
    379c:	4c 03 b8 68 ff ff ff 	add    -0x98(%rax),%r15
        sends += thread_data[x].tasks[n].sends;
    37a3:	48 03 98 78 ff ff ff 	add    -0x88(%rax),%rbx
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    37aa:	4c 03 52 10          	add    0x10(%rdx),%r10
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    37ae:	48 03 6a 18          	add    0x18(%rdx),%rbp
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    37b2:	4c 03 52 38          	add    0x38(%rdx),%r10
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    37b6:	48 03 6a 40          	add    0x40(%rdx),%rbp
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    37ba:	48 39 f0             	cmp    %rsi,%rax
    37bd:	75 c9                	jne    3788 <main+0x1198>
    37bf:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    37c4:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    37c9:	45 31 ed             	xor    %r13d,%r13d
    37cc:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    37d4:	0f 8e 7e 00 00 00    	jle    3858 <main+0x1268>
    37da:	48 89 df             	mov    %rbx,%rdi
    37dd:	4c 89 f0             	mov    %r14,%rax
    37e0:	4c 89 eb             	mov    %r13,%rbx
    37e3:	49 89 ee             	mov    %rbp,%r14
    37e6:	49 89 fd             	mov    %rdi,%r13
    37e9:	48 89 c5             	mov    %rax,%rbp
    37ec:	0f 1f 40 00          	nopl   0x0(%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    37f0:	48 8b 85 90 00 00 00 	mov    0x90(%rbp),%rax
    37f7:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    37fb:	48 83 ec 08          	sub    $0x8,%rsp
    37ff:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3804:	48 83 c3 01          	add    $0x1,%rbx
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3808:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    380c:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3810:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3814:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3817:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    381b:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    381e:	49 f7 e4             	mul    %r12
    3821:	8b 49 20             	mov    0x20(%rcx),%ecx
    3824:	56                   	push   %rsi
    3825:	31 c0                	xor    %eax,%eax
    3827:	48 8d 35 12 3f 00 00 	lea    0x3f12(%rip),%rsi        # 7740 <_IO_stdin_used+0x740>
    382e:	48 c1 ea 12          	shr    $0x12,%rdx
    3832:	49 89 d1             	mov    %rdx,%r9
    3835:	ba 02 00 00 00       	mov    $0x2,%edx
    383a:	e8 11 ec ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    383f:	41 58                	pop    %r8
    3841:	41 59                	pop    %r9
    3843:	48 39 9d a0 00 00 00 	cmp    %rbx,0xa0(%rbp)
    384a:	7f a4                	jg     37f0 <main+0x1200>
    384c:	48 89 e8             	mov    %rbp,%rax
    384f:	4c 89 eb             	mov    %r13,%rbx
    3852:	4c 89 f5             	mov    %r14,%rbp
    3855:	49 89 c6             	mov    %rax,%r14
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3858:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    385f:	85 f6                	test   %esi,%esi
    3861:	0f 8e 11 01 00 00    	jle    3978 <main+0x1388>
    3867:	4c 89 7c 24 70       	mov    %r15,0x70(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    386c:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    3870:	31 d2                	xor    %edx,%edx
    3872:	48 89 5c 24 78       	mov    %rbx,0x78(%rsp)
    3877:	48 89 ac 24 80 00 00 00 	mov    %rbp,0x80(%rsp)
    387f:	90                   	nop
    3880:	49 8b 04 d1          	mov    (%r9,%rdx,8),%rax
    3884:	41 89 d7             	mov    %edx,%r15d
    3887:	48 8d 1c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rbx
    388f:	44 8b 00             	mov    (%rax),%r8d
    3892:	45 85 c0             	test   %r8d,%r8d
    3895:	0f 8e bf 00 00 00    	jle    395a <main+0x136a>
    389b:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    38a0:	48 8b 48 08          	mov    0x8(%rax),%rcx
    38a4:	31 c0                	xor    %eax,%eax
    38a6:	48 89 c6             	mov    %rax,%rsi
    38a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    38b0:	48 89 f5             	mov    %rsi,%rbp
    38b3:	45 31 ed             	xor    %r13d,%r13d
    38b6:	48 c1 e5 08          	shl    $0x8,%rbp
    38ba:	48 8d 14 29          	lea    (%rcx,%rbp,1),%rdx
    38be:	8b 82 94 00 00 00    	mov    0x94(%rdx),%eax
    38c4:	85 c0                	test   %eax,%eax
    38c6:	7e 79                	jle    3941 <main+0x1351>
    38c8:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    38cd:	0f 1f 00             	nopl   (%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    38d0:	4c 89 e9             	mov    %r13,%rcx
    38d3:	48 83 ec 08          	sub    $0x8,%rsp
    38d7:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    38dc:	49 83 c5 01          	add    $0x1,%r13
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    38e0:	48 c1 e1 05          	shl    $0x5,%rcx
    38e4:	48 03 8a 88 00 00 00 	add    0x88(%rdx),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    38eb:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    38ef:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    38f3:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    38f6:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    38fa:	4c 2b 01             	sub    (%rcx),%r8
    38fd:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    38fe:	49 f7 e4             	mul    %r12
    3901:	44 89 f9             	mov    %r15d,%ecx
    3904:	48 8d 35 85 3e 00 00 	lea    0x3e85(%rip),%rsi        # 7790 <_IO_stdin_used+0x790>
    390b:	31 c0                	xor    %eax,%eax
    390d:	48 c1 ea 12          	shr    $0x12,%rdx
    3911:	49 89 d1             	mov    %rdx,%r9
    3914:	ba 02 00 00 00       	mov    $0x2,%edx
    3919:	e8 32 eb ff ff       	call   2450 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    391e:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    3922:	5e                   	pop    %rsi
    3923:	5f                   	pop    %rdi
    3924:	49 8b 04 19          	mov    (%r9,%rbx,1),%rax
    3928:	48 8b 48 08          	mov    0x8(%rax),%rcx
    392c:	48 8d 14 29          	lea    (%rcx,%rbp,1),%rdx
    3930:	44 39 aa 94 00 00 00 	cmp    %r13d,0x94(%rdx)
    3937:	7f 97                	jg     38d0 <main+0x12e0>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3939:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    393e:	44 8b 00             	mov    (%rax),%r8d
    3941:	48 83 c6 01          	add    $0x1,%rsi
    3945:	41 39 f0             	cmp    %esi,%r8d
    3948:	0f 8f 62 ff ff ff    	jg     38b0 <main+0x12c0>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    394e:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    3953:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    395a:	48 83 c2 01          	add    $0x1,%rdx
    395e:	39 d6                	cmp    %edx,%esi
    3960:	0f 8f 1a ff ff ff    	jg     3880 <main+0x1290>
    3966:	4c 8b 7c 24 70       	mov    0x70(%rsp),%r15
    396b:	48 8b 5c 24 78       	mov    0x78(%rsp),%rbx
    3970:	48 8b ac 24 80 00 00 00 	mov    0x80(%rsp),%rbp
    for (int d = 0 ; d < threads_per_group ; d++) {
    3978:	48 83 44 24 28 18    	addq   $0x18,0x28(%rsp)
    397e:	8b 7c 24 58          	mov    0x58(%rsp),%edi
    3982:	49 81 c6 c0 00 00 00 	add    $0xc0,%r14
    3989:	39 7c 24 50          	cmp    %edi,0x50(%rsp)
    398d:	0f 85 ca fc ff ff    	jne    365d <main+0x106d>
  for (int k = 0 ; k < group_count ; k++) {
    3993:	48 89 6c 24 10       	mov    %rbp,0x10(%rsp)
    3998:	48 8b 6c 24 60       	mov    0x60(%rsp),%rbp
    399d:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    39a2:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    39a7:	4c 89 fb             	mov    %r15,%rbx
    39aa:	48 85 ed             	test   %rbp,%rbp
    39ad:	75 0a                	jne    39b9 <main+0x13c9>
    39af:	48 8b 6c 24 48       	mov    0x48(%rsp),%rbp
    39b4:	e9 5b fc ff ff       	jmp    3614 <main+0x1024>
    39b9:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    39be:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
    39c3:	48 8d 35 b0 3a 00 00 	lea    0x3ab0(%rip),%rsi        # 747a <_IO_stdin_used+0x47a>
    39ca:	31 c0                	xor    %eax,%eax
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    39cc:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    39d6:	bf 01 00 00 00       	mov    $0x1,%edi
    39db:	4c 89 fa             	mov    %r15,%rdx
    39de:	e8 6d ea ff ff       	call   2450 <__printf_chk@plt>
    39e3:	bf 0a 00 00 00       	mov    $0xa,%edi
    39e8:	e8 e3 e8 ff ff       	call   22d0 <putchar@plt>
    39ed:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    39f2:	bf 01 00 00 00       	mov    $0x1,%edi
    39f7:	48 8d 35 ea 3d 00 00 	lea    0x3dea(%rip),%rsi        # 77e8 <_IO_stdin_used+0x7e8>
    39fe:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3a02:	31 c0                	xor    %eax,%eax
    3a04:	e8 47 ea ff ff       	call   2450 <__printf_chk@plt>
    3a09:	4c 8b 4c 24 28       	mov    0x28(%rsp),%r9
    3a0e:	bf 01 00 00 00       	mov    $0x1,%edi
    3a13:	48 8d 35 f6 3d 00 00 	lea    0x3df6(%rip),%rsi        # 7810 <_IO_stdin_used+0x810>
    3a1a:	4c 89 c8             	mov    %r9,%rax
    3a1d:	49 c1 f9 3f          	sar    $0x3f,%r9
    3a21:	48 f7 eb             	imul   %rbx
    3a24:	31 c0                	xor    %eax,%eax
    3a26:	48 d1 fa             	sar    %rdx
    3a29:	4c 29 ca             	sub    %r9,%rdx
    3a2c:	e8 1f ea ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3a31:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3a36:	bf 01 00 00 00       	mov    $0x1,%edi
    3a3b:	48 8d 35 fe 3d 00 00 	lea    0x3dfe(%rip),%rsi        # 7840 <_IO_stdin_used+0x840>
    3a42:	48 f7 eb             	imul   %rbx
    3a45:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3a4a:	48 c1 f8 3f          	sar    $0x3f,%rax
    3a4e:	48 d1 fa             	sar    %rdx
    3a51:	48 29 c2             	sub    %rax,%rdx
    3a54:	31 c0                	xor    %eax,%eax
    3a56:	e8 f5 e9 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3a5b:	4c 89 f8             	mov    %r15,%rax
    3a5e:	bf 01 00 00 00       	mov    $0x1,%edi
    3a63:	48 8d 35 06 3e 00 00 	lea    0x3e06(%rip),%rsi        # 7870 <_IO_stdin_used+0x870>
    3a6a:	48 f7 eb             	imul   %rbx
    3a6d:	4c 89 f8             	mov    %r15,%rax
    3a70:	48 c1 f8 3f          	sar    $0x3f,%rax
    3a74:	48 d1 fa             	sar    %rdx
    3a77:	48 29 c2             	sub    %rax,%rdx
    3a7a:	31 c0                	xor    %eax,%eax
    3a7c:	e8 cf e9 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3a81:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3a86:	bf 01 00 00 00       	mov    $0x1,%edi
    3a8b:	48 8d 35 fc 39 00 00 	lea    0x39fc(%rip),%rsi        # 748e <_IO_stdin_used+0x48e>
    3a92:	48 f7 eb             	imul   %rbx
    3a95:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3a9a:	48 c1 f8 3f          	sar    $0x3f,%rax
    3a9e:	48 d1 fa             	sar    %rdx
    3aa1:	48 29 c2             	sub    %rax,%rdx
    3aa4:	31 c0                	xor    %eax,%eax
    3aa6:	e8 a5 e9 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3aab:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3ab0:	bf 01 00 00 00       	mov    $0x1,%edi
    3ab5:	48 8d 35 e3 39 00 00 	lea    0x39e3(%rip),%rsi        # 749f <_IO_stdin_used+0x49f>
    3abc:	48 f7 eb             	imul   %rbx
    3abf:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3ac4:	48 c1 f8 3f          	sar    $0x3f,%rax
    3ac8:	48 d1 fa             	sar    %rdx
    3acb:	48 29 c2             	sub    %rax,%rdx
    3ace:	31 c0                	xor    %eax,%eax
    3ad0:	e8 7b e9 ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3ad5:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    3add:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3ae6:	75 25                	jne    3b0d <main+0x151d>
    3ae8:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    3aef:	31 c0                	xor    %eax,%eax
    3af1:	5b                   	pop    %rbx
    3af2:	5d                   	pop    %rbp
    3af3:	41 5c                	pop    %r12
    3af5:	41 5d                	pop    %r13
    3af7:	41 5e                	pop    %r14
    3af9:	41 5f                	pop    %r15
    3afb:	c3                   	ret
      long v = 0;
    3afc:	31 d2                	xor    %edx,%edx
    3afe:	e9 cf fb ff ff       	jmp    36d2 <main+0x10e2>
            exit(1);
    3b03:	bf 01 00 00 00       	mov    $0x1,%edi
    3b08:	e8 93 e9 ff ff       	call   24a0 <exit@plt>
}
    3b0d:	e8 1e e8 ff ff       	call   2330 <__stack_chk_fail@plt>
    3b12:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3b1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003b20 <_start>:
    3b20:	f3 0f 1e fa          	endbr64
    3b24:	31 ed                	xor    %ebp,%ebp
    3b26:	49 89 d1             	mov    %rdx,%r9
    3b29:	5e                   	pop    %rsi
    3b2a:	48 89 e2             	mov    %rsp,%rdx
    3b2d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3b31:	50                   	push   %rax
    3b32:	54                   	push   %rsp
    3b33:	45 31 c0             	xor    %r8d,%r8d
    3b36:	31 c9                	xor    %ecx,%ecx
    3b38:	48 8d 3d b1 ea ff ff 	lea    -0x154f(%rip),%rdi        # 25f0 <main>
    3b3f:	ff 15 93 64 00 00    	call   *0x6493(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3b45:	f4                   	hlt
    3b46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003b50 <deregister_tm_clones>:
    3b50:	48 8d 3d c9 64 00 00 	lea    0x64c9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3b57:	48 8d 05 c2 64 00 00 	lea    0x64c2(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    3b5e:	48 39 f8             	cmp    %rdi,%rax
    3b61:	74 15                	je     3b78 <deregister_tm_clones+0x28>
    3b63:	48 8b 05 76 64 00 00 	mov    0x6476(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    3b6a:	48 85 c0             	test   %rax,%rax
    3b6d:	74 09                	je     3b78 <deregister_tm_clones+0x28>
    3b6f:	ff e0                	jmp    *%rax
    3b71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3b78:	c3                   	ret
    3b79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003b80 <register_tm_clones>:
    3b80:	48 8d 3d 99 64 00 00 	lea    0x6499(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3b87:	48 8d 35 92 64 00 00 	lea    0x6492(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    3b8e:	48 29 fe             	sub    %rdi,%rsi
    3b91:	48 89 f0             	mov    %rsi,%rax
    3b94:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3b98:	48 c1 f8 03          	sar    $0x3,%rax
    3b9c:	48 01 c6             	add    %rax,%rsi
    3b9f:	48 d1 fe             	sar    %rsi
    3ba2:	74 14                	je     3bb8 <register_tm_clones+0x38>
    3ba4:	48 8b 05 45 64 00 00 	mov    0x6445(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    3bab:	48 85 c0             	test   %rax,%rax
    3bae:	74 08                	je     3bb8 <register_tm_clones+0x38>
    3bb0:	ff e0                	jmp    *%rax
    3bb2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3bb8:	c3                   	ret
    3bb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003bc0 <__do_global_dtors_aux>:
    3bc0:	f3 0f 1e fa          	endbr64
    3bc4:	80 3d 5d 64 00 00 00 	cmpb   $0x0,0x645d(%rip)        # a028 <completed.0>
    3bcb:	75 2b                	jne    3bf8 <__do_global_dtors_aux+0x38>
    3bcd:	55                   	push   %rbp
    3bce:	48 83 3d 22 64 00 00 00 	cmpq   $0x0,0x6422(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3bd6:	48 89 e5             	mov    %rsp,%rbp
    3bd9:	74 0c                	je     3be7 <__do_global_dtors_aux+0x27>
    3bdb:	48 8b 3d 26 64 00 00 	mov    0x6426(%rip),%rdi        # a008 <__dso_handle>
    3be2:	e8 c9 e6 ff ff       	call   22b0 <__cxa_finalize@plt>
    3be7:	e8 64 ff ff ff       	call   3b50 <deregister_tm_clones>
    3bec:	c6 05 35 64 00 00 01 	movb   $0x1,0x6435(%rip)        # a028 <completed.0>
    3bf3:	5d                   	pop    %rbp
    3bf4:	c3                   	ret
    3bf5:	0f 1f 00             	nopl   (%rax)
    3bf8:	c3                   	ret
    3bf9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c00 <frame_dummy>:
    3c00:	f3 0f 1e fa          	endbr64
    3c04:	e9 77 ff ff ff       	jmp    3b80 <register_tm_clones>
    3c09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c10 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3c10:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3c14:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3c1b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    3c1f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3c27:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    3c2b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3c2f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3c36:	48 85 c9             	test   %rcx,%rcx
    3c39:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3c40:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3c44:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3c48:	31 c0                	xor    %eax,%eax
    3c4a:	c3                   	ret
    3c4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003c50 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3c50:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3c54:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    3c5b:	85 c9                	test   %ecx,%ecx
    3c5d:	7e 4f                	jle    3cae <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3c5f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3c66:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    3c6d:	48 c1 e1 09          	shl    $0x9,%rcx
    3c71:	48 8b 50 18          	mov    0x18(%rax),%rdx
    3c75:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3c79:	48 8b 70 38          	mov    0x38(%rax),%rsi
    3c7d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3c7f:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    3c83:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3c88:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3c90:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3c98:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3ca3:	48 05 00 02 00 00    	add    $0x200,%rax
    3ca9:	48 39 c1             	cmp    %rax,%rcx
    3cac:	75 da                	jne    3c88 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    3cae:	0f ae f8             	sfence
}
    3cb1:	31 c0                	xor    %eax,%eax
    3cb3:	c3                   	ret
    3cb4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3cbf:	90                   	nop

0000000000003cc0 <external_thread>:
void * external_thread(void *arg) {
    3cc0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3cc4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    3cc8:	0f 85 fb 00 00 00    	jne    3dc9 <external_thread+0x109>
void * external_thread(void *arg) {
    3cce:	41 57                	push   %r15
    3cd0:	49 89 ff             	mov    %rdi,%r15
    3cd3:	41 56                	push   %r14
    3cd5:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    3cd7:	4c 8d 2d 26 33 00 00 	lea    0x3326(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    3cde:	41 54                	push   %r12
    3ce0:	55                   	push   %rbp
    3ce1:	53                   	push   %rbx
    3ce2:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    3ce6:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    3cec:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    3cf0:	85 c9                	test   %ecx,%ecx
    3cf2:	7e 6e                	jle    3d62 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3cf4:	45 31 e4             	xor    %r12d,%r12d
    3cf7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3d00:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    3d08:	31 db                	xor    %ebx,%ebx
    3d0a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3d0e:	48 8b 06             	mov    (%rsi),%rax
    3d11:	8b 10                	mov    (%rax),%edx
    3d13:	85 d2                	test   %edx,%edx
    3d15:	7e 2a                	jle    3d41 <external_thread+0x81>
    3d17:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    3d1b:	48 89 dd             	mov    %rbx,%rbp
    3d1e:	48 c1 e5 08          	shl    $0x8,%rbp
    3d22:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    3d26:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    3d2d:	45 85 c0             	test   %r8d,%r8d
    3d30:	74 36                	je     3d68 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3d32:	48 83 c3 01          	add    $0x1,%rbx
    3d36:	39 da                	cmp    %ebx,%edx
    3d38:	7f e1                	jg     3d1b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    3d3a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    3d41:	49 83 c4 01          	add    $0x1,%r12
    3d45:	44 39 e1             	cmp    %r12d,%ecx
    3d48:	7f b6                	jg     3d00 <external_thread+0x40>
  while (data->running == 1) {
    3d4a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    3d4f:	74 9f                	je     3cf0 <external_thread+0x30>
}
    3d51:	48 83 c4 08          	add    $0x8,%rsp
    3d55:	31 c0                	xor    %eax,%eax
    3d57:	5b                   	pop    %rbx
    3d58:	5d                   	pop    %rbp
    3d59:	41 5c                	pop    %r12
    3d5b:	41 5d                	pop    %r13
    3d5d:	41 5e                	pop    %r14
    3d5f:	41 5f                	pop    %r15
    3d61:	c3                   	ret
  while (data->running == 1) {
    3d62:	eb fe                	jmp    3d62 <external_thread+0xa2>
    3d64:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    3d68:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    3d6b:	48 8b 06             	mov    (%rsi),%rax
    3d6e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    3d72:	48 01 ef             	add    %rbp,%rdi
    3d75:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    3d7c:	48 c1 e6 05          	shl    $0x5,%rsi
    3d80:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    3d87:	bf 04 00 00 00       	mov    $0x4,%edi
    3d8c:	e8 7f e5 ff ff       	call   2310 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    3d91:	49 8b 47 50          	mov    0x50(%r15),%rax
    3d95:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    3d99:	48 8b 40 08          	mov    0x8(%rax),%rax
    3d9d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    3da8:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3dab:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    3daf:	48 83 c3 01          	add    $0x1,%rbx
    3db3:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3db7:	48 8b 06             	mov    (%rsi),%rax
    3dba:	8b 10                	mov    (%rax),%edx
    3dbc:	39 da                	cmp    %ebx,%edx
    3dbe:	0f 8f 53 ff ff ff    	jg     3d17 <external_thread+0x57>
    3dc4:	e9 71 ff ff ff       	jmp    3d3a <external_thread+0x7a>
}
    3dc9:	31 c0                	xor    %eax,%eax
    3dcb:	c3                   	ret
    3dcc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003dd0 <timer_thread>:
void* timer_thread(void *arg) {
    3dd0:	f3 0f 1e fa          	endbr64
    3dd4:	41 57                	push   %r15
    3dd6:	48 8d 35 33 32 00 00 	lea    0x3233(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3ddd:	41 56                	push   %r14
    3ddf:	41 55                	push   %r13
    3de1:	41 54                	push   %r12
    3de3:	55                   	push   %rbp
    3de4:	48 89 fd             	mov    %rdi,%rbp
    3de7:	53                   	push   %rbx
    3de8:	48 83 ec 58          	sub    $0x58,%rsp
    3dec:	8b 57 04             	mov    0x4(%rdi),%edx
    3def:	bf 01 00 00 00       	mov    $0x1,%edi
    3df4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3dfd:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3e02:	31 c0                	xor    %eax,%eax
    3e04:	e8 47 e6 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3e09:	66 0f 6f 05 7f 3c 00 00 	movdqa 0x3c7f(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
    3e11:	ba 88 13 00 00       	mov    $0x1388,%edx
    3e16:	31 c0                	xor    %eax,%eax
    3e18:	48 8d 35 03 32 00 00 	lea    0x3203(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3e1f:	bf 01 00 00 00       	mov    $0x1,%edi
    3e24:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3e29:	e8 22 e6 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3e2e:	44 8b 65 44          	mov    0x44(%rbp),%r12d
    3e32:	45 85 e4             	test   %r12d,%r12d
    3e35:	0f 84 a3 00 00 00    	je     3ede <timer_thread+0x10e>
  int n = 0;
    3e3b:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    3e3e:	45 31 e4             	xor    %r12d,%r12d
    3e41:	49 89 e6             	mov    %rsp,%r14
    y++;
    3e44:	31 db                	xor    %ebx,%ebx
    3e46:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    3e4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    nanosleep(&preempt , &rem2);
    3e50:	4c 89 ef             	mov    %r13,%rdi
    3e53:	4c 89 f6             	mov    %r14,%rsi
    n++;
    3e56:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3e5a:	e8 f1 e4 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3e5f:	48 63 45 30          	movslq 0x30(%rbp),%rax
    y++;
    3e63:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3e68:	85 c0                	test   %eax,%eax
    3e6a:	7e 49                	jle    3eb5 <timer_thread+0xe5>
    3e6c:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3e70:	49 c1 e4 09          	shl    $0x9,%r12
    3e74:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3e78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3e80:	4c 8b 11             	mov    (%rcx),%r10
    3e83:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3e85:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3e89:	99                   	cltd
    3e8a:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3e8e:	49 8b 72 38          	mov    0x38(%r10),%rsi
    3e92:	48 63 d2             	movslq %edx,%rdx
    3e95:	48 c1 e2 09          	shl    $0x9,%rdx
    3e99:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3ea4:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3eb0:	49 39 c8             	cmp    %rcx,%r8
    3eb3:	75 cb                	jne    3e80 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    3eb5:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3eb8:	48 8b 45 18          	mov    0x18(%rbp),%rax
  while (data->running && n < times) {
    3ebc:	44 8b 45 44          	mov    0x44(%rbp),%r8d
    if (y >= data->threads[0]->task_count) {
    3ec0:	48 8b 00             	mov    (%rax),%rax
    y++;
    3ec3:	39 78 40             	cmp    %edi,0x40(%rax)
    3ec6:	0f 4e fb             	cmovle %ebx,%edi
    3ec9:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3ecc:	45 85 c0             	test   %r8d,%r8d
    3ecf:	74 0d                	je     3ede <timer_thread+0x10e>
    3ed1:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    3ed8:	0f 85 72 ff ff ff    	jne    3e50 <timer_thread+0x80>
    3ede:	48 8d 3d 53 31 00 00 	lea    0x3153(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3ee5:	e8 06 e4 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3eea:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    3eee:	85 d2                	test   %edx,%edx
    3ef0:	7e 73                	jle    3f65 <timer_thread+0x195>
    for (int y = 0 ; y < data->task_count ; y++) {
    3ef2:	48 63 45 40          	movslq 0x40(%rbp),%rax
    3ef6:	85 c0                	test   %eax,%eax
    3ef8:	7e 6b                	jle    3f65 <timer_thread+0x195>
    3efa:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3efe:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    3f02:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3f0a:	31 c9                	xor    %ecx,%ecx
    3f0c:	48 89 c6             	mov    %rax,%rsi
    3f0f:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3f13:	48 8b 40 38          	mov    0x38(%rax),%rax
    3f17:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    3f1b:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3f21:	74 1d                	je     3f40 <timer_thread+0x170>
    3f23:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3f2d:	48 05 00 02 00 00    	add    $0x200,%rax
    3f33:	48 39 c2             	cmp    %rax,%rdx
    3f36:	74 24                	je     3f5c <timer_thread+0x18c>
    3f38:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->threads[x]->tasks[y].sending = 0;
    3f40:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3f4a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3f50:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3f57:	48 39 c2             	cmp    %rax,%rdx
    3f5a:	75 e4                	jne    3f40 <timer_thread+0x170>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f5c:	48 83 c1 08          	add    $0x8,%rcx
    3f60:	48 39 cf             	cmp    %rcx,%rdi
    3f63:	75 aa                	jne    3f0f <timer_thread+0x13f>
  asm volatile ("mfence" ::: "memory");
    3f65:	0f ae f0             	mfence
  struct timespec drain = {
    3f68:	66 0f 6f 05 30 3b 00 00 	movdqa 0x3b30(%rip),%xmm0        # 7aa0 <_IO_stdin_used+0xaa0>
    3f70:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f75:	48 63 45 28          	movslq 0x28(%rbp),%rax
    y++;
    3f79:	45 8d 44 24 01       	lea    0x1(%r12),%r8d
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f7e:	85 c0                	test   %eax,%eax
    3f80:	7e 4b                	jle    3fcd <timer_thread+0x1fd>
    3f82:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3f86:	4d 63 e4             	movslq %r12d,%r12
    3f89:	49 c1 e4 09          	shl    $0x9,%r12
    3f8d:	48 8d 3c c1          	lea    (%rcx,%rax,8),%rdi
    3f91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3f98:	48 8b 19             	mov    (%rcx),%rbx
    3f9b:	44 89 c0             	mov    %r8d,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f9e:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3fa2:	99                   	cltd
    3fa3:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3fa6:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    3faa:	48 63 d2             	movslq %edx,%rdx
    3fad:	48 c1 e2 09          	shl    $0x9,%rdx
    3fb1:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3fbc:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3fc8:	48 39 cf             	cmp    %rcx,%rdi
    3fcb:	75 cb                	jne    3f98 <timer_thread+0x1c8>
    asm volatile ("mfence" ::: "memory");
    3fcd:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3fd0:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3fd4:	8b 4d 30             	mov    0x30(%rbp),%ecx
    y++;
    3fd7:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3fda:	48 8b 07             	mov    (%rdi),%rax
    y++;
    3fdd:	44 39 40 40          	cmp    %r8d,0x40(%rax)
    3fe1:	45 0f 4f e0          	cmovg  %r8d,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3fe5:	85 c9                	test   %ecx,%ecx
    3fe7:	0f 8e 0d 01 00 00    	jle    40fa <timer_thread+0x32a>
    3fed:	45 31 ff             	xor    %r15d,%r15d
    int all_empty = 1;
    3ff0:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    3ff6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int y = 0 ; y < 2 ; y++) {
    4000:	31 db                	xor    %ebx,%ebx
    4002:	45 89 fd             	mov    %r15d,%r13d
    4005:	4e 8d 34 fd 00 00 00 00 	lea    0x0(,%r15,8),%r14
    400d:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    400f:	85 c9                	test   %ecx,%ecx
    4011:	0f 8e 91 00 00 00    	jle    40a8 <timer_thread+0x2d8>
    4017:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    401b:	4a 8b 14 37          	mov    (%rdi,%r14,1),%rdx
    401f:	48 89 d8             	mov    %rbx,%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4022:	45 31 c0             	xor    %r8d,%r8d
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4025:	48 c1 e0 09          	shl    $0x9,%rax
    4029:	48 03 42 38          	add    0x38(%rdx),%rax
    402d:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    4034:	eb 1c                	jmp    4052 <timer_thread+0x282>
    4036:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4040:	48 85 d2             	test   %rdx,%rdx
    4043:	7f 27                	jg     406c <timer_thread+0x29c>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4045:	41 83 c0 01          	add    $0x1,%r8d
    4049:	48 83 c0 28          	add    $0x28,%rax
    404d:	41 39 c8             	cmp    %ecx,%r8d
    4050:	74 7e                	je     40d0 <timer_thread+0x300>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4052:	48 8b 10             	mov    (%rax),%rdx
    4055:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    405c:	48 8b 50 08          	mov    0x8(%rax),%rdx
    4060:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    4067:	4d 85 c9             	test   %r9,%r9
    406a:	7e d4                	jle    4040 <timer_thread+0x270>
    406c:	48 83 ec 08          	sub    $0x8,%rsp
    4070:	89 f1                	mov    %esi,%ecx
    4072:	bf 01 00 00 00       	mov    $0x1,%edi
    4077:	31 c0                	xor    %eax,%eax
    4079:	52                   	push   %rdx
    407a:	48 8d 35 dc 2f 00 00 	lea    0x2fdc(%rip),%rsi        # 705d <_IO_stdin_used+0x5d>
    4081:	44 89 ea             	mov    %r13d,%edx
    4084:	e8 c7 e3 ff ff       	call   2450 <__printf_chk@plt>
      for (int y = 0 ; y < 2 ; y++) {
    4089:	5a                   	pop    %rdx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    408a:	8b 4d 30             	mov    0x30(%rbp),%ecx
      for (int y = 0 ; y < 2 ; y++) {
    408d:	5e                   	pop    %rsi
    408e:	48 83 fb 01          	cmp    $0x1,%rbx
    4092:	74 54                	je     40e8 <timer_thread+0x318>
    4094:	48 83 c3 01          	add    $0x1,%rbx
    4098:	45 31 db             	xor    %r11d,%r11d
    409b:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    409d:	85 c9                	test   %ecx,%ecx
    409f:	0f 8f 72 ff ff ff    	jg     4017 <timer_thread+0x247>
    40a5:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    40a8:	49 83 c7 01          	add    $0x1,%r15
    40ac:	44 39 f9             	cmp    %r15d,%ecx
    40af:	0f 8f 4b ff ff ff    	jg     4000 <timer_thread+0x230>
    if (all_empty == 1) {
    40b5:	41 83 fb 01          	cmp    $0x1,%r11d
    40b9:	74 3f                	je     40fa <timer_thread+0x32a>
      nanosleep(&drain , &drainrem);
    40bb:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    40c0:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    40c5:	e8 86 e2 ff ff       	call   2350 <nanosleep@plt>
    40ca:	e9 a6 fe ff ff       	jmp    3f75 <timer_thread+0x1a5>
    40cf:	90                   	nop
      for (int y = 0 ; y < 2 ; y++) {
    40d0:	48 83 fb 01          	cmp    $0x1,%rbx
    40d4:	74 d2                	je     40a8 <timer_thread+0x2d8>
    40d6:	48 83 c3 01          	add    $0x1,%rbx
    40da:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    40dc:	e9 3a ff ff ff       	jmp    401b <timer_thread+0x24b>
    40e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    40e8:	49 83 c7 01          	add    $0x1,%r15
    40ec:	45 31 db             	xor    %r11d,%r11d
    40ef:	44 39 f9             	cmp    %r15d,%ecx
    40f2:	0f 8f 08 ff ff ff    	jg     4000 <timer_thread+0x230>
    40f8:	eb bb                	jmp    40b5 <timer_thread+0x2e5>
    40fa:	48 8d 3d 53 2f 00 00 	lea    0x2f53(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    4101:	e8 ea e1 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    4106:	8b 7d 44             	mov    0x44(%rbp),%edi
    4109:	85 ff                	test   %edi,%edi
    410b:	0f 84 ed 00 00 00    	je     41fe <timer_thread+0x42e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4111:	8b 45 2c             	mov    0x2c(%rbp),%eax
    4114:	31 db                	xor    %ebx,%ebx
    4116:	4c 8d 25 57 2f 00 00 	lea    0x2f57(%rip),%r12        # 7074 <_IO_stdin_used+0x74>
    411d:	4c 8d 2d 6b 2f 00 00 	lea    0x2f6b(%rip),%r13        # 708f <_IO_stdin_used+0x8f>
    4124:	85 c0                	test   %eax,%eax
    4126:	7e 3b                	jle    4163 <timer_thread+0x393>
    4128:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4130:	31 c0                	xor    %eax,%eax
    4132:	89 da                	mov    %ebx,%edx
    4134:	4c 89 e6             	mov    %r12,%rsi
    4137:	bf 01 00 00 00       	mov    $0x1,%edi
    413c:	e8 0f e3 ff ff       	call   2450 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4141:	48 8b 45 18          	mov    0x18(%rbp),%rax
    4145:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4149:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    414d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4154:	0f 84 d1 00 00 00    	je     422b <timer_thread+0x45b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    415a:	48 83 c3 01          	add    $0x1,%rbx
    415e:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    4161:	7f cd                	jg     4130 <timer_thread+0x360>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4163:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    4167:	85 d2                	test   %edx,%edx
    4169:	7e 7d                	jle    41e8 <timer_thread+0x418>
      for (int y = 0 ; y < data->task_count ; y++) {
    416b:	8b 45 40             	mov    0x40(%rbp),%eax
    416e:	85 c0                	test   %eax,%eax
    4170:	7e 76                	jle    41e8 <timer_thread+0x418>
    4172:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4175:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    4179:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4181:	31 c9                	xor    %ecx,%ecx
    4183:	48 c1 e6 09          	shl    $0x9,%rsi
    4187:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4190:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4194:	48 8b 40 38          	mov    0x38(%rax),%rax
    4198:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    419c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    41a2:	74 1c                	je     41c0 <timer_thread+0x3f0>
    41a4:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    41ae:	48 05 00 02 00 00    	add    $0x200,%rax
    41b4:	48 39 d0             	cmp    %rdx,%rax
    41b7:	74 26                	je     41df <timer_thread+0x40f>
    41b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    41c0:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    41ca:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    41d0:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    41da:	48 39 d0             	cmp    %rdx,%rax
    41dd:	75 e1                	jne    41c0 <timer_thread+0x3f0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    41df:	48 83 c1 08          	add    $0x8,%rcx
    41e3:	48 39 f9             	cmp    %rdi,%rcx
    41e6:	75 a8                	jne    4190 <timer_thread+0x3c0>
    asm volatile ("mfence" ::: "memory");
    41e8:	0f ae f0             	mfence
    41eb:	48 8d 3d af 2e 00 00 	lea    0x2eaf(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    41f2:	e8 f9 e0 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    41f7:	c7 45 44 00 00 00 00 	movl   $0x0,0x44(%rbp)
    41fe:	48 8d 3d a3 2e 00 00 	lea    0x2ea3(%rip),%rdi        # 70a8 <_IO_stdin_used+0xa8>
    4205:	e8 e6 e0 ff ff       	call   22f0 <puts@plt>
}
    420a:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    420f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4218:	75 40                	jne    425a <timer_thread+0x48a>
    421a:	48 83 c4 58          	add    $0x58,%rsp
    421e:	31 c0                	xor    %eax,%eax
    4220:	5b                   	pop    %rbx
    4221:	5d                   	pop    %rbp
    4222:	41 5c                	pop    %r12
    4224:	41 5d                	pop    %r13
    4226:	41 5e                	pop    %r14
    4228:	41 5f                	pop    %r15
    422a:	c3                   	ret
    422b:	4c 89 ef             	mov    %r13,%rdi
    422e:	e8 bd e0 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4233:	48 8b 45 18          	mov    0x18(%rbp),%rax
    4237:	be 01 00 00 00       	mov    $0x1,%esi
    423c:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4240:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4244:	8b 78 60             	mov    0x60(%rax),%edi
    4247:	e8 b4 e1 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    424c:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    424f:	0f 8f db fe ff ff    	jg     4130 <timer_thread+0x360>
    4255:	e9 09 ff ff ff       	jmp    4163 <timer_thread+0x393>
}
    425a:	e8 d1 e0 ff ff       	call   2330 <__stack_chk_fail@plt>
    425f:	90                   	nop

0000000000004260 <sendm.part.0>:
int sendm(struct BarrierTask *data) {
    4260:	41 57                	push   %r15
    4262:	41 56                	push   %r14
    4264:	41 55                	push   %r13
    4266:	41 54                	push   %r12
    4268:	55                   	push   %rbp
    4269:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    426a:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    4270:	89 44 24 c8          	mov    %eax,-0x38(%rsp)
    4274:	85 c0                	test   %eax,%eax
    4276:	0f 8e 77 01 00 00    	jle    43f3 <sendm.part.0+0x193>
        if (n == data->thread_index) { continue; }
    427c:	8b 87 30 01 00 00    	mov    0x130(%rdi),%eax
    4282:	49 89 fe             	mov    %rdi,%r14
    4285:	45 31 e4             	xor    %r12d,%r12d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    4288:	45 31 ff             	xor    %r15d,%r15d
        if (n == data->thread_index) { continue; }
    428b:	89 44 24 cc          	mov    %eax,-0x34(%rsp)
    428f:	48 8d 87 88 01 00 00 	lea    0x188(%rdi),%rax
    4296:	48 89 44 24 e8       	mov    %rax,-0x18(%rsp)
    429b:	48 8d 87 90 01 00 00 	lea    0x190(%rdi),%rax
    42a2:	48 89 44 24 f0       	mov    %rax,-0x10(%rsp)
    42a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    42b0:	44 39 7c 24 cc       	cmp    %r15d,-0x34(%rsp)
    42b5:	0f 84 23 01 00 00    	je     43de <sendm.part.0+0x17e>
        struct Data *them = data->mailboxes[n].higher;
    42bb:	4d 8b 86 70 01 00 00 	mov    0x170(%r14),%r8
    42c2:	4d 01 e0             	add    %r12,%r8
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    42c5:	45 8b 48 20          	mov    0x20(%r8),%r9d
        struct Data *them = data->mailboxes[n].higher;
    42c9:	49 8b 78 08          	mov    0x8(%r8),%rdi
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    42cd:	41 83 f9 02          	cmp    $0x2,%r9d
    42d1:	0f 84 31 01 00 00    	je     4408 <sendm.part.0+0x1a8>
        for (; them->messages_count < min;) {
    42d7:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    42de:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    42e5:	48 39 e9             	cmp    %rbp,%rcx
    42e8:	0f 8d f0 00 00 00    	jge    43de <sendm.part.0+0x17e>
    42ee:	49 8b 86 08 01 00 00 	mov    0x108(%r14),%rax
    42f5:	48 39 e9             	cmp    %rbp,%rcx
    42f8:	49 89 eb             	mov    %rbp,%r11
          them->messages[them->messages_count++] = data->message; 
    42fb:	48 8b 17             	mov    (%rdi),%rdx
    42fe:	41 0f 9c c5          	setl   %r13b
    4302:	49 29 cb             	sub    %rcx,%r11
    4305:	48 89 44 24 d0       	mov    %rax,-0x30(%rsp)
    430a:	49 8b 40 10          	mov    0x10(%r8),%rax
    430e:	49 8d 5b ff          	lea    -0x1(%r11),%rbx
    4312:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    4317:	48 89 44 24 d8       	mov    %rax,-0x28(%rsp)
    431c:	48 83 fb 02          	cmp    $0x2,%rbx
    4320:	0f 86 9a 01 00 00    	jbe    44c0 <sendm.part.0+0x260>
    4326:	45 84 ed             	test   %r13b,%r13b
    4329:	0f 84 91 01 00 00    	je     44c0 <sendm.part.0+0x260>
    432f:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    4337:	4a 8d 04 12          	lea    (%rdx,%r10,1),%rax
    433b:	48 89 44 24 e0       	mov    %rax,-0x20(%rsp)
    4340:	49 89 c3             	mov    %rax,%r11
    4343:	48 8d 04 ea          	lea    (%rdx,%rbp,8),%rax
    4347:	48 39 44 24 e8       	cmp    %rax,-0x18(%rsp)
    434c:	0f 83 ce 00 00 00    	jae    4420 <sendm.part.0+0x1c0>
    4352:	4c 89 d8             	mov    %r11,%rax
    4355:	4c 8b 5c 24 f0       	mov    -0x10(%rsp),%r11
    435a:	48 89 ce             	mov    %rcx,%rsi
    435d:	4c 39 d8             	cmp    %r11,%rax
    4360:	0f 83 ba 00 00 00    	jae    4420 <sendm.part.0+0x1c0>
    4366:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4370:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    4377:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    437b:	48 83 c6 01          	add    $0x1,%rsi
    437f:	48 39 f5             	cmp    %rsi,%rbp
    4382:	7f ec                	jg     4370 <sendm.part.0+0x110>
    4384:	0f 1f 40 00          	nopl   0x0(%rax)
    4388:	31 f6                	xor    %esi,%esi
    438a:	45 84 ed             	test   %r13b,%r13b
    438d:	4c 8b 5c 24 d0       	mov    -0x30(%rsp),%r11
    4392:	48 0f 45 f3          	cmovne %rbx,%rsi
    4396:	4d 8d 5c 33 01       	lea    0x1(%r11,%rsi,1),%r11
    439b:	48 8d 4c 31 01       	lea    0x1(%rcx,%rsi,1),%rcx
    43a0:	4d 89 9e 08 01 00 00 	mov    %r11,0x108(%r14)
    43a7:	4c 8b 5c 24 d8       	mov    -0x28(%rsp),%r11
    43ac:	4d 8d 5c 33 01       	lea    0x1(%r11,%rsi,1),%r11
    43b1:	4d 89 58 10          	mov    %r11,0x10(%r8)
    43b5:	48 89 8f 80 00 00 00 	mov    %rcx,0x80(%rdi)
    43bc:	48 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%rcx
    43c4:	bb 00 00 00 00       	mov    $0x0,%ebx
    43c9:	48 0f 44 cb          	cmove  %rbx,%rcx
    43cd:	4c 01 d2             	add    %r10,%rdx
    43d0:	48 89 04 0a          	mov    %rax,(%rdx,%rcx,1)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    43d4:	41 83 f9 02          	cmp    $0x2,%r9d
    43d8:	0f 84 c2 00 00 00    	je     44a0 <sendm.part.0+0x240>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    43de:	8b 44 24 c8          	mov    -0x38(%rsp),%eax
    43e2:	41 83 c7 01          	add    $0x1,%r15d
    43e6:	49 83 c4 28          	add    $0x28,%r12
    43ea:	41 39 c7             	cmp    %eax,%r15d
    43ed:	0f 85 bd fe ff ff    	jne    42b0 <sendm.part.0+0x50>
      asm volatile ("sfence" ::: "memory");
    43f3:	0f ae f8             	sfence
}
    43f6:	5b                   	pop    %rbx
    43f7:	5d                   	pop    %rbp
    43f8:	41 5c                	pop    %r12
    43fa:	41 5d                	pop    %r13
    43fc:	41 5e                	pop    %r14
    43fe:	41 5f                	pop    %r15
    4400:	c3                   	ret
    4401:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4408:	8b 87 00 01 00 00    	mov    0x100(%rdi),%eax
    440e:	83 f8 01             	cmp    $0x1,%eax
    4411:	0f 84 b9 00 00 00    	je     44d0 <sendm.part.0+0x270>
        else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    4417:	85 c0                	test   %eax,%eax
    4419:	74 c3                	je     43de <sendm.part.0+0x17e>
    441b:	e9 b7 fe ff ff       	jmp    42d7 <sendm.part.0+0x77>
    4420:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    4425:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    442c:	48 8b 74 24 e0       	mov    -0x20(%rsp),%rsi
    4431:	49 d1 eb             	shr    %r11
    4434:	66 48 0f 6e c0       	movq   %rax,%xmm0
    4439:	4c 89 dd             	mov    %r11,%rbp
    443c:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    4440:	48 c1 e5 04          	shl    $0x4,%rbp
    4444:	49 89 eb             	mov    %rbp,%r11
    4447:	48 01 f5             	add    %rsi,%rbp
    444a:	41 83 e3 10          	and    $0x10,%r11d
    444e:	74 11                	je     4461 <sendm.part.0+0x201>
          them->messages[them->messages_count++] = data->message; 
    4450:	0f 11 06             	movups %xmm0,(%rsi)
        for (; them->messages_count < min;) {
    4453:	48 83 c6 10          	add    $0x10,%rsi
    4457:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
    445c:	48 39 f5             	cmp    %rsi,%rbp
    445f:	74 1a                	je     447b <sendm.part.0+0x21b>
    4461:	4c 8b 5c 24 c0       	mov    -0x40(%rsp),%r11
          them->messages[them->messages_count++] = data->message; 
    4466:	0f 11 06             	movups %xmm0,(%rsi)
    4469:	48 83 c6 20          	add    $0x20,%rsi
    446d:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
        for (; them->messages_count < min;) {
    4471:	48 39 f5             	cmp    %rsi,%rbp
    4474:	75 f0                	jne    4466 <sendm.part.0+0x206>
    4476:	4c 89 5c 24 c0       	mov    %r11,-0x40(%rsp)
    447b:	4c 89 de             	mov    %r11,%rsi
    447e:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    4482:	48 01 ce             	add    %rcx,%rsi
    4485:	41 83 e3 01          	and    $0x1,%r11d
    4489:	0f 84 f9 fe ff ff    	je     4388 <sendm.part.0+0x128>
          them->messages[them->messages_count++] = data->message; 
    448f:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    4496:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    449a:	e9 e9 fe ff ff       	jmp    4388 <sendm.part.0+0x128>
    449f:	90                   	nop
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    44a0:	83 bf 00 01 00 00 01 	cmpl   $0x1,0x100(%rdi)
    44a7:	0f 85 31 ff ff ff    	jne    43de <sendm.part.0+0x17e>
          them->available = 0;
    44ad:	c7 87 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdi)
    44b7:	e9 22 ff ff ff       	jmp    43de <sendm.part.0+0x17e>
    44bc:	0f 1f 40 00          	nopl   0x0(%rax)
          them->messages[them->messages_count++] = data->message; 
    44c0:	48 89 ce             	mov    %rcx,%rsi
    44c3:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    44cb:	e9 a0 fe ff ff       	jmp    4370 <sendm.part.0+0x110>
        for (; them->messages_count < min;) {
    44d0:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    44d7:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    44de:	48 39 cd             	cmp    %rcx,%rbp
    44e1:	0f 8f 07 fe ff ff    	jg     42ee <sendm.part.0+0x8e>
    44e7:	eb c4                	jmp    44ad <sendm.part.0+0x24d>
    44e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000044f0 <strtolower>:
void strtolower(char *str) {
    44f0:	f3 0f 1e fa          	endbr64
    44f4:	55                   	push   %rbp
    44f5:	53                   	push   %rbx
    44f6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    44fa:	48 0f be 1f          	movsbq (%rdi),%rbx
    44fe:	84 db                	test   %bl,%bl
    4500:	74 24                	je     4526 <strtolower+0x36>
    4502:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4505:	e8 06 e0 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    450a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4510:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4513:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4517:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    451a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    451d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4522:	84 db                	test   %bl,%bl
    4524:	75 ea                	jne    4510 <strtolower+0x20>
}
    4526:	48 83 c4 08          	add    $0x8,%rsp
    452a:	5b                   	pop    %rbx
    452b:	5d                   	pop    %rbp
    452c:	c3                   	ret
    452d:	0f 1f 00             	nopl   (%rax)

0000000000004530 <zh_malloc>:
void *zh_malloc(size_t size) {
    4530:	f3 0f 1e fa          	endbr64
    4534:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4538:	e8 d3 de ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    453d:	48 85 c0             	test   %rax,%rax
    4540:	74 05                	je     4547 <zh_malloc+0x17>
}
    4542:	48 83 c4 08          	add    $0x8,%rsp
    4546:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4547:	48 8b 0d d2 5a 00 00 	mov    0x5ad2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    454e:	ba 28 00 00 00       	mov    $0x28,%edx
    4553:	be 01 00 00 00       	mov    $0x1,%esi
    4558:	48 8d 3d 59 2f 00 00 	lea    0x2f59(%rip),%rdi        # 74b8 <_IO_stdin_used+0x4b8>
    455f:	e8 5c df ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4564:	bf 01 00 00 00       	mov    $0x1,%edi
    4569:	e8 32 df ff ff       	call   24a0 <exit@plt>
    456e:	66 90                	xchg   %ax,%ax

0000000000004570 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4570:	f3 0f 1e fa          	endbr64
    4574:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4575:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    457a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    457d:	e8 de dd ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4582:	48 85 c0             	test   %rax,%rax
    4585:	74 11                	je     4598 <get_filename_ext+0x28>
    4587:	48 39 c3             	cmp    %rax,%rbx
    458a:	74 0c                	je     4598 <get_filename_ext+0x28>
    return dot + 1;
    458c:	48 83 c0 01          	add    $0x1,%rax
}
    4590:	5b                   	pop    %rbx
    4591:	c3                   	ret
    4592:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4598:	48 8d 05 51 2b 00 00 	lea    0x2b51(%rip),%rax        # 70f0 <_IO_stdin_used+0xf0>
}
    459f:	5b                   	pop    %rbx
    45a0:	c3                   	ret
    45a1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    45ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000045b0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    45b0:	f3 0f 1e fa          	endbr64
    45b4:	41 55                	push   %r13
    45b6:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    45b9:	48 89 fe             	mov    %rdi,%rsi
    45bc:	41 54                	push   %r12
    45be:	55                   	push   %rbp
    45bf:	48 89 d5             	mov    %rdx,%rbp
    45c2:	ba 00 04 00 00       	mov    $0x400,%edx
    45c7:	53                   	push   %rbx
    45c8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    45cf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    45d8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    45e0:	31 c0                	xor    %eax,%eax
    45e2:	49 89 e4             	mov    %rsp,%r12
    45e5:	4c 89 e7             	mov    %r12,%rdi
    45e8:	e8 43 de ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    45ed:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    45f2:	84 db                	test   %bl,%bl
    45f4:	74 24                	je     461a <send_headers+0x6a>
        *str = (char)tolower(*str);
    45f6:	e8 15 df ff ff       	call   2510 <__ctype_tolower_loc@plt>
    45fb:	48 8b 08             	mov    (%rax),%rcx
    45fe:	4c 89 e0             	mov    %r12,%rax
    4601:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4608:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    460b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    460f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4612:	48 0f be 18          	movsbq (%rax),%rbx
    4616:	84 db                	test   %bl,%bl
    4618:	75 ee                	jne    4608 <send_headers+0x58>
    void *buf = malloc(size);
    461a:	bf 11 00 00 00       	mov    $0x11,%edi
    461f:	e8 ec dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4624:	48 85 c0             	test   %rax,%rax
    4627:	0f 84 7e 04 00 00    	je     4aab <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    462d:	66 0f 6f 05 7b 34 00 00 	movdqa 0x347b(%rip),%xmm0        # 7ab0 <_IO_stdin_used+0xab0>
    iov[0].iov_base = zh_malloc(slen);
    4635:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4639:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    463e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4646:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    464a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    464d:	e8 be dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4652:	48 85 c0             	test   %rax,%rax
    4655:	0f 84 50 04 00 00    	je     4aab <send_headers+0x4fb>
    465b:	66 0f 6f 05 5d 34 00 00 	movdqa 0x345d(%rip),%xmm0        # 7ac0 <_IO_stdin_used+0xac0>
    iov[1].iov_base = zh_malloc(slen);
    4663:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4667:	4c 89 e7             	mov    %r12,%rdi
    466a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4674:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    467c:	0f 11 00             	movups %xmm0,(%rax)
    467f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4683:	be 2e 00 00 00       	mov    $0x2e,%esi
    4688:	e8 d3 dc ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    468d:	48 85 c0             	test   %rax,%rax
    4690:	0f 84 ea 02 00 00    	je     4980 <send_headers+0x3d0>
    4696:	4c 39 e0             	cmp    %r12,%rax
    4699:	0f 84 e1 02 00 00    	je     4980 <send_headers+0x3d0>
    return dot + 1;
    469f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    46a3:	48 8d 3d 14 2a 00 00 	lea    0x2a14(%rip),%rdi        # 70be <_IO_stdin_used+0xbe>
    46aa:	48 89 de             	mov    %rbx,%rsi
    46ad:	e8 fe dc ff ff       	call   23b0 <strcmp@plt>
    46b2:	85 c0                	test   %eax,%eax
    46b4:	75 20                	jne    46d6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    46b6:	66 0f 6f 05 12 34 00 00 	movdqa 0x3412(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    46be:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    46c6:	66 0f 6f 05 12 34 00 00 	movdqa 0x3412(%rip),%xmm0        # 7ae0 <_IO_stdin_used+0xae0>
    46ce:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    46d6:	48 89 de             	mov    %rbx,%rsi
    46d9:	48 8d 3d e2 29 00 00 	lea    0x29e2(%rip),%rdi        # 70c2 <_IO_stdin_used+0xc2>
    46e0:	e8 cb dc ff ff       	call   23b0 <strcmp@plt>
    46e5:	85 c0                	test   %eax,%eax
    46e7:	75 20                	jne    4709 <send_headers+0x159>
    46e9:	66 0f 6f 05 df 33 00 00 	movdqa 0x33df(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    46f1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    46f9:	66 0f 6f 05 df 33 00 00 	movdqa 0x33df(%rip),%xmm0        # 7ae0 <_IO_stdin_used+0xae0>
    4701:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4709:	48 89 de             	mov    %rbx,%rsi
    470c:	48 8d 3d b4 29 00 00 	lea    0x29b4(%rip),%rdi        # 70c7 <_IO_stdin_used+0xc7>
    4713:	e8 98 dc ff ff       	call   23b0 <strcmp@plt>
    4718:	85 c0                	test   %eax,%eax
    471a:	0f 84 10 02 00 00    	je     4930 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4720:	48 89 de             	mov    %rbx,%rsi
    4723:	48 8d 3d a1 29 00 00 	lea    0x29a1(%rip),%rdi        # 70cb <_IO_stdin_used+0xcb>
    472a:	e8 81 dc ff ff       	call   23b0 <strcmp@plt>
    472f:	85 c0                	test   %eax,%eax
    4731:	0f 84 a9 02 00 00    	je     49e0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4737:	48 89 de             	mov    %rbx,%rsi
    473a:	48 8d 3d 8e 29 00 00 	lea    0x298e(%rip),%rdi        # 70cf <_IO_stdin_used+0xcf>
    4741:	e8 6a dc ff ff       	call   23b0 <strcmp@plt>
    4746:	85 c0                	test   %eax,%eax
    4748:	0f 84 6a 02 00 00    	je     49b8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    474e:	48 89 de             	mov    %rbx,%rsi
    4751:	48 8d 3d ba 29 00 00 	lea    0x29ba(%rip),%rdi        # 7112 <_IO_stdin_used+0x112>
    4758:	e8 53 dc ff ff       	call   23b0 <strcmp@plt>
    475d:	85 c0                	test   %eax,%eax
    475f:	0f 84 2b 02 00 00    	je     4990 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4765:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4768:	0f 84 52 01 00 00    	je     48c0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    476e:	48 89 de             	mov    %rbx,%rsi
    4771:	48 8d 3d 5b 29 00 00 	lea    0x295b(%rip),%rdi        # 70d3 <_IO_stdin_used+0xd3>
    4778:	e8 33 dc ff ff       	call   23b0 <strcmp@plt>
    477d:	85 c0                	test   %eax,%eax
    477f:	0f 84 ab 02 00 00    	je     4a30 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4785:	48 89 de             	mov    %rbx,%rsi
    4788:	48 8d 3d 48 29 00 00 	lea    0x2948(%rip),%rdi        # 70d7 <_IO_stdin_used+0xd7>
    478f:	e8 1c dc ff ff       	call   23b0 <strcmp@plt>
    4794:	85 c0                	test   %eax,%eax
    4796:	0f 84 6c 02 00 00    	je     4a08 <send_headers+0x458>
    slen = strlen(send_buffer);
    479c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    47a4:	4c 89 e7             	mov    %r12,%rdi
    47a7:	e8 74 db ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    47ac:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    47af:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    47b2:	e8 59 dc ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    47b7:	48 85 c0             	test   %rax,%rax
    47ba:	0f 84 eb 02 00 00    	je     4aab <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    47c0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    47c4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    47c8:	83 fb 08             	cmp    $0x8,%ebx
    47cb:	0f 83 3f 01 00 00    	jae    4910 <send_headers+0x360>
    47d1:	f6 c3 04             	test   $0x4,%bl
    47d4:	0f 85 7b 02 00 00    	jne    4a55 <send_headers+0x4a5>
    47da:	85 db                	test   %ebx,%ebx
    47dc:	74 13                	je     47f1 <send_headers+0x241>
    47de:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    47e6:	88 10                	mov    %dl,(%rax)
    47e8:	f6 c3 02             	test   $0x2,%bl
    47eb:	0f 85 96 02 00 00    	jne    4a87 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    47f1:	4d 89 e8             	mov    %r13,%r8
    47f4:	48 8d 0d e0 28 00 00 	lea    0x28e0(%rip),%rcx        # 70db <_IO_stdin_used+0xdb>
    47fb:	4c 89 e7             	mov    %r12,%rdi
    47fe:	31 c0                	xor    %eax,%eax
    4800:	ba 00 04 00 00       	mov    $0x400,%edx
    4805:	be 01 00 00 00       	mov    $0x1,%esi
    480a:	e8 11 dd ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    480f:	4c 89 e7             	mov    %r12,%rdi
    4812:	e8 09 db ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4817:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    481a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    481d:	e8 ee db ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4822:	48 85 c0             	test   %rax,%rax
    4825:	0f 84 80 02 00 00    	je     4aab <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    482b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    482f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4833:	83 fb 08             	cmp    $0x8,%ebx
    4836:	0f 83 1c 01 00 00    	jae    4958 <send_headers+0x3a8>
    483c:	f6 c3 04             	test   $0x4,%bl
    483f:	0f 85 29 02 00 00    	jne    4a6e <send_headers+0x4be>
    4845:	85 db                	test   %ebx,%ebx
    4847:	74 13                	je     485c <send_headers+0x2ac>
    4849:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4851:	88 10                	mov    %dl,(%rax)
    4853:	f6 c3 02             	test   $0x2,%bl
    4856:	0f 85 3d 02 00 00    	jne    4a99 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    485c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4861:	bf 02 00 00 00       	mov    $0x2,%edi
    4866:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    486e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4876:	e8 95 db ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    487b:	48 85 c0             	test   %rax,%rax
    487e:	0f 84 27 02 00 00    	je     4aab <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4884:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    488c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4890:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4898:	66 89 10             	mov    %dx,(%rax)
}
    489b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    48a3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    48ac:	0f 85 20 02 00 00    	jne    4ad2 <send_headers+0x522>
    48b2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    48b9:	5b                   	pop    %rbx
    48ba:	5d                   	pop    %rbp
    48bb:	41 5c                	pop    %r12
    48bd:	41 5d                	pop    %r13
    48bf:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    48c0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    48c4:	0f 85 a4 fe ff ff    	jne    476e <send_headers+0x1be>
    48ca:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    48ce:	0f 85 9a fe ff ff    	jne    476e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    48d4:	66 0f 6f 05 54 32 00 00 	movdqa 0x3254(%rip),%xmm0        # 7b30 <_IO_stdin_used+0xb30>
    48dc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    48e6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    48ee:	66 0f 6f 05 4a 32 00 00 	movdqa 0x324a(%rip),%xmm0        # 7b40 <_IO_stdin_used+0xb40>
    48f6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    48fe:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4906:	e9 63 fe ff ff       	jmp    476e <send_headers+0x1be>
    490b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4910:	89 da                	mov    %ebx,%edx
    4912:	48 89 c7             	mov    %rax,%rdi
    4915:	4c 89 e6             	mov    %r12,%rsi
    4918:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    491d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4922:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4925:	c1 e9 03             	shr    $0x3,%ecx
    4928:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    492b:	e9 c1 fe ff ff       	jmp    47f1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4930:	66 0f 6f 05 98 31 00 00 	movdqa 0x3198(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    4938:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4940:	66 0f 6f 05 a8 31 00 00 	movdqa 0x31a8(%rip),%xmm0        # 7af0 <_IO_stdin_used+0xaf0>
    4948:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4950:	e9 cb fd ff ff       	jmp    4720 <send_headers+0x170>
    4955:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4958:	89 da                	mov    %ebx,%edx
    495a:	48 89 c7             	mov    %rax,%rdi
    495d:	4c 89 e6             	mov    %r12,%rsi
    4960:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4965:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    496a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    496d:	c1 e9 03             	shr    $0x3,%ecx
    4970:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4973:	e9 e4 fe ff ff       	jmp    485c <send_headers+0x2ac>
    4978:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4980:	48 8d 1d 69 27 00 00 	lea    0x2769(%rip),%rbx        # 70f0 <_IO_stdin_used+0xf0>
    4987:	e9 94 fd ff ff       	jmp    4720 <send_headers+0x170>
    498c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4990:	66 0f 6f 05 78 31 00 00 	movdqa 0x3178(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4998:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    49a0:	66 0f 6f 05 78 31 00 00 	movdqa 0x3178(%rip),%xmm0        # 7b20 <_IO_stdin_used+0xb20>
    49a8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    49b0:	e9 b0 fd ff ff       	jmp    4765 <send_headers+0x1b5>
    49b5:	0f 1f 00             	nopl   (%rax)
    49b8:	66 0f 6f 05 50 31 00 00 	movdqa 0x3150(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    49c0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    49c8:	66 0f 6f 05 50 31 00 00 	movdqa 0x3150(%rip),%xmm0        # 7b20 <_IO_stdin_used+0xb20>
    49d0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    49d8:	e9 71 fd ff ff       	jmp    474e <send_headers+0x19e>
    49dd:	0f 1f 00             	nopl   (%rax)
    49e0:	66 0f 6f 05 e8 30 00 00 	movdqa 0x30e8(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    49e8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    49f0:	66 0f 6f 05 08 31 00 00 	movdqa 0x3108(%rip),%xmm0        # 7b00 <_IO_stdin_used+0xb00>
    49f8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a00:	e9 32 fd ff ff       	jmp    4737 <send_headers+0x187>
    4a05:	0f 1f 00             	nopl   (%rax)
    4a08:	66 0f 6f 05 00 31 00 00 	movdqa 0x3100(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4a10:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a18:	66 0f 6f 05 40 31 00 00 	movdqa 0x3140(%rip),%xmm0        # 7b60 <_IO_stdin_used+0xb60>
    4a20:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4a28:	e9 6f fd ff ff       	jmp    479c <send_headers+0x1ec>
    4a2d:	0f 1f 00             	nopl   (%rax)
    4a30:	66 0f 6f 05 d8 30 00 00 	movdqa 0x30d8(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4a38:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a40:	66 0f 6f 05 08 31 00 00 	movdqa 0x3108(%rip),%xmm0        # 7b50 <_IO_stdin_used+0xb50>
    4a48:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4a50:	e9 30 fd ff ff       	jmp    4785 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4a55:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4a5c:	89 db                	mov    %ebx,%ebx
    4a5e:	89 10                	mov    %edx,(%rax)
    4a60:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4a65:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4a69:	e9 83 fd ff ff       	jmp    47f1 <send_headers+0x241>
    4a6e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4a75:	89 db                	mov    %ebx,%ebx
    4a77:	89 10                	mov    %edx,(%rax)
    4a79:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4a7e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4a82:	e9 d5 fd ff ff       	jmp    485c <send_headers+0x2ac>
    4a87:	89 db                	mov    %ebx,%ebx
    4a89:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4a8f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4a94:	e9 58 fd ff ff       	jmp    47f1 <send_headers+0x241>
    4a99:	89 db                	mov    %ebx,%ebx
    4a9b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4aa1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4aa6:	e9 b1 fd ff ff       	jmp    485c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4aab:	48 8b 0d 6e 55 00 00 	mov    0x556e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4ab2:	ba 28 00 00 00       	mov    $0x28,%edx
    4ab7:	be 01 00 00 00       	mov    $0x1,%esi
    4abc:	48 8d 3d f5 29 00 00 	lea    0x29f5(%rip),%rdi        # 74b8 <_IO_stdin_used+0x4b8>
    4ac3:	e8 f8 d9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4ac8:	bf 01 00 00 00       	mov    $0x1,%edi
    4acd:	e8 ce d9 ff ff       	call   24a0 <exit@plt>
}
    4ad2:	e8 59 d8 ff ff       	call   2330 <__stack_chk_fail@plt>
    4ad7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004ae0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4ae0:	f3 0f 1e fa          	endbr64
    4ae4:	41 55                	push   %r13
    4ae6:	49 89 d5             	mov    %rdx,%r13
    4ae9:	41 54                	push   %r12
    4aeb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    4aee:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4af1:	55                   	push   %rbp
    4af2:	53                   	push   %rbx
    4af3:	48 89 f3             	mov    %rsi,%rbx
    4af6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4afa:	e8 11 d9 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4aff:	48 85 c0             	test   %rax,%rax
    4b02:	74 6b                	je     4b6f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4b04:	4c 89 e7             	mov    %r12,%rdi
    4b07:	48 89 c5             	mov    %rax,%rbp
    4b0a:	31 f6                	xor    %esi,%esi
    4b0c:	31 c0                	xor    %eax,%eax
    4b0e:	e8 6d d9 ff ff       	call   2480 <open@plt>
    4b13:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4b16:	85 c0                	test   %eax,%eax
    4b18:	0f 88 38 da ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4b1e:	48 89 da             	mov    %rbx,%rdx
    4b21:	48 89 ee             	mov    %rbp,%rsi
    4b24:	89 c7                	mov    %eax,%edi
    4b26:	e8 65 d8 ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    4b2b:	48 98                	cltq
    4b2d:	48 39 d8             	cmp    %rbx,%rax
    4b30:	7c 1e                	jl     4b50 <copy_file_contents+0x70>
    close(fd);
    4b32:	44 89 e7             	mov    %r12d,%edi
    4b35:	e8 36 d8 ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    4b3a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    4b3e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4b42:	48 83 c4 08          	add    $0x8,%rsp
    4b46:	5b                   	pop    %rbx
    4b47:	5d                   	pop    %rbp
    4b48:	41 5c                	pop    %r12
    4b4a:	41 5d                	pop    %r13
    4b4c:	c3                   	ret
    4b4d:	0f 1f 00             	nopl   (%rax)
    4b50:	48 8b 0d c9 54 00 00 	mov    0x54c9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4b57:	ba 1a 00 00 00       	mov    $0x1a,%edx
    4b5c:	be 01 00 00 00       	mov    $0x1,%esi
    4b61:	48 8d 3d 89 25 00 00 	lea    0x2589(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4b68:	e8 53 d9 ff ff       	call   24c0 <fwrite@plt>
    4b6d:	eb c3                	jmp    4b32 <copy_file_contents+0x52>
    4b6f:	48 8b 0d aa 54 00 00 	mov    0x54aa(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4b76:	ba 28 00 00 00       	mov    $0x28,%edx
    4b7b:	be 01 00 00 00       	mov    $0x1,%esi
    4b80:	48 8d 3d 31 29 00 00 	lea    0x2931(%rip),%rdi        # 74b8 <_IO_stdin_used+0x4b8>
    4b87:	e8 34 d9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4b8c:	bf 01 00 00 00       	mov    $0x1,%edi
    4b91:	e8 0a d9 ff ff       	call   24a0 <exit@plt>
    4b96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004ba0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4ba0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4ba4:	8b 46 44             	mov    0x44(%rsi),%eax
    4ba7:	48 89 fa             	mov    %rdi,%rdx
    4baa:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    4bad:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4bb3:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4bb6:	48 8b 07             	mov    (%rdi),%rax
    4bb9:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4bbc:	f6 c1 02             	test   $0x2,%cl
    4bbf:	74 00                	je     4bc1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4bc1:	89 f0                	mov    %esi,%eax
    4bc3:	44 29 c0             	sub    %r8d,%eax
    4bc6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4bc9:	0f 82 93 d9 ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4bcf:	c1 e9 0a             	shr    $0xa,%ecx
    4bd2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4bd6:	8b 47 44             	mov    0x44(%rdi),%eax
    4bd9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4bdc:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4bdf:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4be2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4be5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4be9:	d3 e0                	shl    %cl,%eax
    4beb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    4bee:	48 c1 e0 06          	shl    $0x6,%rax
    4bf2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4bf6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    4bfc:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4bff:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4c03:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4c09:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4c11:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4c15:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4c18:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4c1f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4c27:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    4c2b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    4c2f:	e8 0c d7 ff ff       	call   2340 <io_uring_submit@plt>
}
    4c34:	31 c0                	xor    %eax,%eax
    4c36:	48 83 c4 08          	add    $0x8,%rsp
    4c3a:	c3                   	ret
    4c3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004c40 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4c40:	f3 0f 1e fa          	endbr64
    4c44:	41 55                	push   %r13
    4c46:	41 89 fd             	mov    %edi,%r13d
    4c49:	41 54                	push   %r12
    4c4b:	55                   	push   %rbp
    4c4c:	53                   	push   %rbx
    4c4d:	48 89 f3             	mov    %rsi,%rbx
    4c50:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4c54:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4c57:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    4c5d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4c60:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4c63:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4c65:	f6 c1 02             	test   $0x2,%cl
    4c68:	74 00                	je     4c6a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    4c6a:	89 c2                	mov    %eax,%edx
    4c6c:	29 f2                	sub    %esi,%edx
    4c6e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4c71:	0f 82 fb d8 ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c77:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    4c7a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    4c7d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4c80:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4c85:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c88:	23 6b 58             	and    0x58(%rbx),%ebp
    4c8b:	d3 e5                	shl    %cl,%ebp
    4c8d:	48 c1 e5 06          	shl    $0x6,%rbp
    4c91:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4c95:	e8 76 d7 ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    4c9a:	be 01 00 00 00       	mov    $0x1,%esi
    4c9f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4ca4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4ca7:	e8 f4 d6 ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    4cac:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4cb1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4cb5:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4cb8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4cbd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4cc2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    4ccb:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4cd3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4cd7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    4cdb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4ce2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4cea:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    4cee:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4cf6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    4cfe:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4d02:	e8 39 d6 ff ff       	call   2340 <io_uring_submit@plt>
}
    4d07:	48 83 c4 08          	add    $0x8,%rsp
    4d0b:	31 c0                	xor    %eax,%eax
    4d0d:	5b                   	pop    %rbx
    4d0e:	5d                   	pop    %rbp
    4d0f:	41 5c                	pop    %r12
    4d11:	41 5d                	pop    %r13
    4d13:	c3                   	ret
    4d14:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4d1f:	90                   	nop

0000000000004d20 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4d20:	f3 0f 1e fa          	endbr64
    4d24:	41 56                	push   %r14
    4d26:	41 89 f6             	mov    %esi,%r14d
    4d29:	41 55                	push   %r13
    4d2b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    4d2e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4d33:	41 54                	push   %r12
    4d35:	55                   	push   %rbp
    4d36:	48 89 d5             	mov    %rdx,%rbp
    4d39:	53                   	push   %rbx
    void *buf = malloc(size);
    4d3a:	e8 d1 d6 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4d3f:	48 85 c0             	test   %rax,%rax
    4d42:	0f 84 dd 00 00 00    	je     4e25 <_send_static_string_content+0x105>
    4d48:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    4d4b:	4c 89 ef             	mov    %r13,%rdi
    4d4e:	e8 cd d5 ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4d53:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    4d5a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    4d5e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4d61:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4d64:	e8 a7 d6 ff ff       	call   2410 <malloc@plt>
    4d69:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    4d6c:	48 85 c0             	test   %rax,%rax
    4d6f:	0f 84 b0 00 00 00    	je     4e25 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4d75:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4d79:	4c 89 e2             	mov    %r12,%rdx
    4d7c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    4d7f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4d83:	e8 58 d6 ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4d88:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4d8b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4d91:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4d94:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4d98:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4d9a:	f6 c1 02             	test   $0x2,%cl
    4d9d:	0f 85 7d 00 00 00    	jne    4e20 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4da3:	89 d0                	mov    %edx,%eax
    4da5:	29 f0                	sub    %esi,%eax
    4da7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    4daa:	0f 82 cc d7 ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4db0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4db3:	8b 45 44             	mov    0x44(%rbp),%eax
    4db6:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4db9:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    4dbc:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4dbf:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4dc2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4dc8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4dcc:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4dce:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4dd1:	48 89 ef             	mov    %rbp,%rdi
    4dd4:	48 c1 e0 06          	shl    $0x6,%rax
    4dd8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    4ddc:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4ddf:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4de3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4de9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4df1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4df5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4df8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4dff:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4e07:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    4e0b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    4e0f:	5b                   	pop    %rbx
    4e10:	5d                   	pop    %rbp
    4e11:	41 5c                	pop    %r12
    4e13:	41 5d                	pop    %r13
    4e15:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4e17:	e9 24 d5 ff ff       	jmp    2340 <io_uring_submit@plt>
    4e1c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4e20:	e9 7e ff ff ff       	jmp    4da3 <_send_static_string_content+0x83>
    4e25:	48 8b 0d f4 51 00 00 	mov    0x51f4(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4e2c:	ba 28 00 00 00       	mov    $0x28,%edx
    4e31:	be 01 00 00 00       	mov    $0x1,%esi
    4e36:	48 8d 3d 7b 26 00 00 	lea    0x267b(%rip),%rdi        # 74b8 <_IO_stdin_used+0x4b8>
    4e3d:	e8 7e d6 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4e42:	bf 01 00 00 00       	mov    $0x1,%edi
    4e47:	e8 54 d6 ff ff       	call   24a0 <exit@plt>
    4e4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004e50 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4e50:	f3 0f 1e fa          	endbr64
    4e54:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4e57:	89 fe                	mov    %edi,%esi
    4e59:	48 8b 3d b8 51 00 00 	mov    0x51b8(%rip),%rdi        # a018 <unimplemented_content>
    4e60:	e9 bb fe ff ff       	jmp    4d20 <_send_static_string_content>
    4e65:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004e70 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4e70:	f3 0f 1e fa          	endbr64
    4e74:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4e77:	89 fe                	mov    %edi,%esi
    4e79:	48 8b 3d 90 51 00 00 	mov    0x5190(%rip),%rdi        # a010 <http_404_content>
    4e80:	e9 9b fe ff ff       	jmp    4d20 <_send_static_string_content>
    4e85:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004e90 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4e90:	f3 0f 1e fa          	endbr64
    4e94:	41 56                	push   %r14
    4e96:	41 55                	push   %r13
    4e98:	49 89 d5             	mov    %rdx,%r13
    4e9b:	41 54                	push   %r12
    4e9d:	41 89 f4             	mov    %esi,%r12d
    4ea0:	55                   	push   %rbp
    4ea1:	48 89 fd             	mov    %rdi,%rbp
    4ea4:	53                   	push   %rbx
    4ea5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    4eac:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4eb5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    4ebd:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    4ebf:	e8 5c d4 ff ff       	call   2320 <strlen@plt>
    4ec4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4ec9:	48 89 c3             	mov    %rax,%rbx
    4ecc:	0f 84 b6 00 00 00    	je     4f88 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ed2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4ed7:	48 89 ee             	mov    %rbp,%rsi
    4eda:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4ede:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4ee3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4eeb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ef3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4efe:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4f06:	e8 b5 d4 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4f0b:	48 89 e6             	mov    %rsp,%rsi
    4f0e:	4c 89 f7             	mov    %r14,%rdi
    4f11:	e8 ba d4 ff ff       	call   23d0 <stat@plt>
    4f16:	83 f8 ff             	cmp    $0xffffffff,%eax
    4f19:	0f 84 d3 00 00 00    	je     4ff2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    4f1f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4f23:	25 00 f0 00 00       	and    $0xf000,%eax
    4f28:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4f2d:	0f 84 f5 00 00 00    	je     5028 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4f33:	48 8b 3d d6 50 00 00 	mov    0x50d6(%rip),%rdi        # a010 <http_404_content>
    4f3a:	4c 89 ea             	mov    %r13,%rdx
    4f3d:	44 89 e6             	mov    %r12d,%esi
    4f40:	e8 db fd ff ff       	call   4d20 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4f45:	4c 89 f2             	mov    %r14,%rdx
    4f48:	bf 01 00 00 00       	mov    $0x1,%edi
    4f4d:	31 c0                	xor    %eax,%eax
    4f4f:	48 8d 35 eb 21 00 00 	lea    0x21eb(%rip),%rsi        # 7141 <_IO_stdin_used+0x141>
    4f56:	e8 f5 d4 ff ff       	call   2450 <__printf_chk@plt>
}
    4f5b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4f63:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4f6c:	0f 85 20 01 00 00    	jne    5092 <handle_get_method+0x202>
    4f72:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4f79:	5b                   	pop    %rbx
    4f7a:	5d                   	pop    %rbp
    4f7b:	41 5c                	pop    %r12
    4f7d:	41 5d                	pop    %r13
    4f7f:	41 5e                	pop    %r14
    4f81:	c3                   	ret
    4f82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f88:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4f8d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4f95:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4f9a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f9d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4fa5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4fa8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4fb0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4fbb:	e8 00 d4 ff ff       	call   23c0 <__memcpy_chk@plt>
    4fc0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4fc5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4fca:	48 8d 35 3b 21 00 00 	lea    0x213b(%rip),%rsi        # 710c <_IO_stdin_used+0x10c>
    4fd1:	48 29 d9             	sub    %rbx,%rcx
    4fd4:	ba 0b 00 00 00       	mov    $0xb,%edx
    4fd9:	e8 e2 d3 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4fde:	48 89 e6             	mov    %rsp,%rsi
    4fe1:	4c 89 f7             	mov    %r14,%rdi
    4fe4:	e8 e7 d3 ff ff       	call   23d0 <stat@plt>
    4fe9:	83 f8 ff             	cmp    $0xffffffff,%eax
    4fec:	0f 85 2d ff ff ff    	jne    4f1f <handle_get_method+0x8f>
    4ff2:	4c 89 f2             	mov    %r14,%rdx
    4ff5:	48 89 e9             	mov    %rbp,%rcx
    4ff8:	48 8d 35 18 21 00 00 	lea    0x2118(%rip),%rsi        # 7117 <_IO_stdin_used+0x117>
    4fff:	31 c0                	xor    %eax,%eax
    5001:	bf 01 00 00 00       	mov    $0x1,%edi
    5006:	e8 45 d4 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    500b:	48 8b 3d fe 4f 00 00 	mov    0x4ffe(%rip),%rdi        # a010 <http_404_content>
    5012:	4c 89 ea             	mov    %r13,%rdx
    5015:	44 89 e6             	mov    %r12d,%esi
    5018:	e8 03 fd ff ff       	call   4d20 <_send_static_string_content>
}
    501d:	e9 39 ff ff ff       	jmp    4f5b <handle_get_method+0xcb>
    5022:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5028:	bf 70 00 00 00       	mov    $0x70,%edi
    502d:	e8 de d3 ff ff       	call   2410 <malloc@plt>
    5032:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5035:	48 85 c0             	test   %rax,%rax
    5038:	74 5d                	je     5097 <handle_get_method+0x207>
            req->client_socket = client_socket;
    503a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    503e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5043:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5047:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    504a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    5051:	e8 5a f5 ff ff       	call   45b0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5056:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    505b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    505f:	4c 89 f7             	mov    %r14,%rdi
    5062:	e8 79 fa ff ff       	call   4ae0 <copy_file_contents>
    5067:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    506c:	4c 89 f2             	mov    %r14,%rdx
    506f:	31 c0                	xor    %eax,%eax
    5071:	48 8d 35 b7 20 00 00 	lea    0x20b7(%rip),%rsi        # 712f <_IO_stdin_used+0x12f>
    5078:	bf 01 00 00 00       	mov    $0x1,%edi
    507d:	e8 ce d3 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    5082:	4c 89 ee             	mov    %r13,%rsi
    5085:	48 89 df             	mov    %rbx,%rdi
    5088:	e8 13 fb ff ff       	call   4ba0 <add_write_request>
    508d:	e9 c9 fe ff ff       	jmp    4f5b <handle_get_method+0xcb>
}
    5092:	e8 99 d2 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5097:	48 8b 0d 82 4f 00 00 	mov    0x4f82(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    509e:	ba 28 00 00 00       	mov    $0x28,%edx
    50a3:	be 01 00 00 00       	mov    $0x1,%esi
    50a8:	48 8d 3d 09 24 00 00 	lea    0x2409(%rip),%rdi        # 74b8 <_IO_stdin_used+0x4b8>
    50af:	e8 0c d4 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    50b4:	bf 01 00 00 00       	mov    $0x1,%edi
    50b9:	e8 e2 d3 ff ff       	call   24a0 <exit@plt>
    50be:	66 90                	xchg   %ax,%ax

00000000000050c0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    50c0:	f3 0f 1e fa          	endbr64
    50c4:	41 57                	push   %r15
    50c6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    50c8:	4c 8d 35 d7 1f 00 00 	lea    0x1fd7(%rip),%r14        # 70a6 <_IO_stdin_used+0xa6>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    50cf:	41 55                	push   %r13
    50d1:	49 89 d5             	mov    %rdx,%r13
    50d4:	41 54                	push   %r12
    50d6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    50d9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    50dc:	55                   	push   %rbp
    50dd:	53                   	push   %rbx
    50de:	48 83 ec 18          	sub    $0x18,%rsp
    50e2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    50eb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    50f0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    50f2:	49 89 e7             	mov    %rsp,%r15
    50f5:	4c 89 fa             	mov    %r15,%rdx
    50f8:	e8 83 d2 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    50fd:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    5101:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    5104:	84 db                	test   %bl,%bl
    5106:	74 1d                	je     5125 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    5108:	e8 03 d4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    510d:	48 89 ea             	mov    %rbp,%rdx
    5110:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    5113:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    5117:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    511a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    511d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5121:	84 db                	test   %bl,%bl
    5123:	75 eb                	jne    5110 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    5125:	4c 89 fa             	mov    %r15,%rdx
    5128:	4c 89 f6             	mov    %r14,%rsi
    512b:	31 ff                	xor    %edi,%edi
    512d:	e8 4e d2 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5132:	48 8d 35 1b 20 00 00 	lea    0x201b(%rip),%rsi        # 7154 <_IO_stdin_used+0x154>
    5139:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    513c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    513f:	e8 6c d2 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    5144:	4c 89 ea             	mov    %r13,%rdx
    5147:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    514a:	85 c0                	test   %eax,%eax
    514c:	75 2a                	jne    5178 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    514e:	48 89 df             	mov    %rbx,%rdi
    5151:	e8 3a fd ff ff       	call   4e90 <handle_get_method>
}
    5156:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    515b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5164:	75 20                	jne    5186 <handle_http_method+0xc6>
    5166:	48 83 c4 18          	add    $0x18,%rsp
    516a:	5b                   	pop    %rbx
    516b:	5d                   	pop    %rbp
    516c:	41 5c                	pop    %r12
    516e:	41 5d                	pop    %r13
    5170:	41 5e                	pop    %r14
    5172:	41 5f                	pop    %r15
    5174:	c3                   	ret
    5175:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5178:	48 8b 3d 99 4e 00 00 	mov    0x4e99(%rip),%rdi        # a018 <unimplemented_content>
    517f:	e8 9c fb ff ff       	call   4d20 <_send_static_string_content>
}
    5184:	eb d0                	jmp    5156 <handle_http_method+0x96>
    5186:	e8 a5 d1 ff ff       	call   2330 <__stack_chk_fail@plt>
    518b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005190 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5190:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5194:	85 d2                	test   %edx,%edx
    5196:	7e 38                	jle    51d0 <get_line+0x40>
    5198:	48 63 d2             	movslq %edx,%rdx
    519b:	48 83 c7 01          	add    $0x1,%rdi
    519f:	48 01 f2             	add    %rsi,%rdx
    51a2:	eb 11                	jmp    51b5 <get_line+0x25>
    51a4:	0f 1f 40 00          	nopl   0x0(%rax)
    51a8:	48 83 c6 01          	add    $0x1,%rsi
    51ac:	48 83 c7 01          	add    $0x1,%rdi
    51b0:	48 39 d6             	cmp    %rdx,%rsi
    51b3:	74 1b                	je     51d0 <get_line+0x40>
        dest[i] = src[i];
    51b5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    51b9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    51bb:	3c 0d                	cmp    $0xd,%al
    51bd:	75 e9                	jne    51a8 <get_line+0x18>
    51bf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    51c2:	75 e4                	jne    51a8 <get_line+0x18>
            dest[i] = '\0';
    51c4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    51c7:	31 c0                	xor    %eax,%eax
    51c9:	c3                   	ret
    51ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    51d0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    51d5:	c3                   	ret
    51d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000051e0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    51e0:	f3 0f 1e fa          	endbr64
    51e4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    51eb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    51ef:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    51f8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5200:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5202:	49 89 e2             	mov    %rsp,%r10
    5205:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    520d:	4c 89 d0             	mov    %r10,%rax
    5210:	eb 13                	jmp    5225 <handle_client_request+0x45>
    5212:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5218:	48 83 c0 01          	add    $0x1,%rax
    521c:	48 83 c1 01          	add    $0x1,%rcx
    5220:	4c 39 c8             	cmp    %r9,%rax
    5223:	74 4b                	je     5270 <handle_client_request+0x90>
        dest[i] = src[i];
    5225:	44 0f b6 01          	movzbl (%rcx),%r8d
    5229:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    522c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5230:	75 e6                	jne    5218 <handle_client_request+0x38>
    5232:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5236:	75 e0                	jne    5218 <handle_client_request+0x38>
            dest[i] = '\0';
    5238:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    523b:	8b 47 08             	mov    0x8(%rdi),%eax
    523e:	48 89 f2             	mov    %rsi,%rdx
    5241:	4c 89 d7             	mov    %r10,%rdi
    5244:	89 c6                	mov    %eax,%esi
    5246:	e8 75 fe ff ff       	call   50c0 <handle_http_method>
}
    524b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5253:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    525c:	75 39                	jne    5297 <handle_client_request+0xb7>
    525e:	31 c0                	xor    %eax,%eax
    5260:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5267:	c3                   	ret
    5268:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5270:	48 8b 0d a9 4d 00 00 	mov    0x4da9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5277:	ba 12 00 00 00       	mov    $0x12,%edx
    527c:	be 01 00 00 00       	mov    $0x1,%esi
    5281:	48 8d 3d d0 1e 00 00 	lea    0x1ed0(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    5288:	e8 33 d2 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    528d:	bf 01 00 00 00       	mov    $0x1,%edi
    5292:	e8 09 d2 ff ff       	call   24a0 <exit@plt>
}
    5297:	e8 94 d0 ff ff       	call   2330 <__stack_chk_fail@plt>
    529c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000052a0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    52a0:	f3 0f 1e fa          	endbr64
    52a4:	55                   	push   %rbp
    52a5:	53                   	push   %rbx
    52a6:	48 89 cb             	mov    %rcx,%rbx
    52a9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    52ad:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    52b0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    52b3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    52b9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    52bc:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    52bf:	f6 c1 02             	test   $0x2,%cl
    52c2:	74 00                	je     52c4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    52c4:	41 89 c0             	mov    %eax,%r8d
    52c7:	45 29 c8             	sub    %r9d,%r8d
    52ca:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    52ce:	0f 82 b8 d2 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    52d4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52d7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    52da:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    52dd:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    52e0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    52e3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52e7:	d3 e5                	shl    %cl,%ebp
    52e9:	48 c1 e5 06          	shl    $0x6,%rbp
    52ed:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    52f1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    52f4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    52f9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5300:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5304:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5308:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    5310:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    5318:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    531c:	e8 ef d0 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    5321:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5324:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    532a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    532e:	48 83 c4 08          	add    $0x8,%rsp
    5332:	5b                   	pop    %rbx
    5333:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5334:	e9 07 d0 ff ff       	jmp    2340 <io_uring_submit@plt>
    5339:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005340 <io_thread>:
void* io_thread(void *arg) {
    5340:	f3 0f 1e fa          	endbr64
    5344:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5346:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5348:	41 56                	push   %r14
    534a:	41 55                	push   %r13
    534c:	41 54                	push   %r12
    534e:	55                   	push   %rbp
    534f:	48 89 fd             	mov    %rdi,%rbp
    5352:	53                   	push   %rbx
    5353:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    535a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5363:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    536b:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    536f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5374:	bf 00 01 00 00       	mov    $0x100,%edi
    5379:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    537c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5380:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5385:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    538a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    538f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5394:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    539c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    53a1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    53a9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    53ae:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    53b6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    53bb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    53c3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    53c8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    53d0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    53d5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    53dd:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    53e5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    53ed:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    53f5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    53fd:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5405:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    540d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5415:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    541d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5425:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    542d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5434:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    543c:	e8 af cf ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5441:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5445:	31 f6                	xor    %esi,%esi
    5447:	e8 94 d0 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    544c:	31 d2                	xor    %edx,%edx
    544e:	be 01 00 00 00       	mov    $0x1,%esi
    5453:	bf 02 00 00 00       	mov    $0x2,%edi
    5458:	e8 d3 d0 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    545d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5460:	0f 84 68 d1 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    5466:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    546b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5471:	89 c7                	mov    %eax,%edi
    5473:	41 89 c4             	mov    %eax,%r12d
    5476:	ba 02 00 00 00       	mov    $0x2,%edx
    547b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5480:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5488:	e8 73 ce ff ff       	call   2300 <setsockopt@plt>
    548d:	85 c0                	test   %eax,%eax
    548f:	0f 88 0d d1 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5495:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    549a:	ba 10 00 00 00       	mov    $0x10,%edx
    549f:	44 89 e7             	mov    %r12d,%edi
    54a2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    54ab:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    54b3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    54bb:	e8 a0 cf ff ff       	call   2460 <bind@plt>
    54c0:	85 c0                	test   %eax,%eax
    54c2:	0f 88 12 d1 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    54c8:	be 0a 00 00 00       	mov    $0xa,%esi
    54cd:	44 89 e7             	mov    %r12d,%edi
    54d0:	e8 4b cf ff ff       	call   2420 <listen@plt>
    54d5:	85 c0                	test   %eax,%eax
    54d7:	0f 88 d1 d0 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    54dd:	ba db 18 00 00       	mov    $0x18db,%edx
    54e2:	48 8d 35 b4 1c 00 00 	lea    0x1cb4(%rip),%rsi        # 719d <_IO_stdin_used+0x19d>
    54e9:	bf 01 00 00 00       	mov    $0x1,%edi
    54ee:	31 c0                	xor    %eax,%eax
    54f0:	e8 5b cf ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    54f5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    54fa:	48 89 d9             	mov    %rbx,%rcx
    54fd:	44 89 e7             	mov    %r12d,%edi
    5500:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5505:	48 89 c6             	mov    %rax,%rsi
    5508:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    550d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5512:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    551a:	e8 81 fd ff ff       	call   52a0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    551f:	bf 01 00 00 00       	mov    $0x1,%edi
    5524:	be 10 00 00 00       	mov    $0x10,%esi
    5529:	e8 72 ce ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    552e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5533:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5536:	e8 d5 ce ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    553b:	48 85 c0             	test   %rax,%rax
    553e:	0f 84 ae 04 00 00    	je     59f2 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5544:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5548:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    554f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5556:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    555e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5561:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5566:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5568:	f6 c1 02             	test   $0x2,%cl
    556b:	0f 85 0f 04 00 00    	jne    5980 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5571:	89 d0                	mov    %edx,%eax
    5573:	29 f0                	sub    %esi,%eax
    5575:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    557c:	0f 82 42 d0 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5582:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5585:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5589:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    558d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5590:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5597:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    559a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    55a1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    55a8:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    55aa:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    55ad:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    55b2:	48 c1 e0 06          	shl    $0x6,%rax
    55b6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    55be:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    55c4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    55c7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    55cf:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    55d3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    55db:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    55e3:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    55e7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    55eb:	e8 50 cd ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    55f0:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    55f4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    55f9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5601:	0f 85 d7 01 00 00    	jne    57de <io_thread+0x49e>
    5607:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    560c:	4d 89 ce             	mov    %r9,%r14
    560f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5614:	0f 1f 40 00          	nopl   0x0(%rax)
    5618:	48 8d 3d 94 1b 00 00 	lea    0x1b94(%rip),%rdi        # 71b3 <_IO_stdin_used+0x1b3>
    561f:	e8 cc cc ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5624:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    562b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5632:	c1 e9 0b             	shr    $0xb,%ecx
    5635:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5638:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5640:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5642:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    564a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    564c:	39 d0                	cmp    %edx,%eax
    564e:	74 36                	je     5686 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5650:	89 f8                	mov    %edi,%eax
    5652:	21 d0                	and    %edx,%eax
    5654:	d3 e0                	shl    %cl,%eax
    5656:	48 c1 e0 04          	shl    $0x4,%rax
    565a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5662:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    566a:	0f 85 a8 01 00 00    	jne    5818 <io_thread+0x4d8>
    5670:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5674:	0f 85 0e 03 00 00    	jne    5988 <io_thread+0x648>
			if (cqe->res < 0)
    567a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    567d:	83 c2 01             	add    $0x1,%edx
    5680:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5682:	85 c0                	test   %eax,%eax
    5684:	79 b2                	jns    5638 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5686:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    568f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5690:	45 31 c0             	xor    %r8d,%r8d
    5693:	31 d2                	xor    %edx,%edx
    5695:	b9 01 00 00 00       	mov    $0x1,%ecx
    569a:	4c 89 f6             	mov    %r14,%rsi
    569d:	48 89 df             	mov    %rbx,%rdi
    56a0:	e8 9b cd ff ff       	call   2440 <__io_uring_get_cqe@plt>
    56a5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    56a8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    56ad:	48 83 38 01          	cmpq   $0x1,(%rax)
    56b1:	0f 84 e1 02 00 00    	je     5998 <io_thread+0x658>
    56b7:	48 8d 3d 1b 1b 00 00 	lea    0x1b1b(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    56be:	e8 2d cc ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    56c3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    56c8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    56cb:	45 85 ff             	test   %r15d,%r15d
    56ce:	0f 88 c2 ce ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    56d4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    56d7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    56db:	85 c0                	test   %eax,%eax
    56dd:	0f 88 d5 02 00 00    	js     59b8 <io_thread+0x678>
      switch (req->event_type) {
    56e3:	41 83 f8 01          	cmp    $0x1,%r8d
    56e7:	0f 84 7b 01 00 00    	je     5868 <io_thread+0x528>
    56ed:	41 83 f8 02          	cmp    $0x2,%r8d
    56f1:	0f 84 a1 01 00 00    	je     5898 <io_thread+0x558>
    56f7:	45 85 c0             	test   %r8d,%r8d
    56fa:	0f 85 50 01 00 00    	jne    5850 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5700:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5705:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    570a:	48 89 d9             	mov    %rbx,%rcx
    570d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5711:	e8 8a fb ff ff       	call   52a0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5716:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    571b:	48 89 de             	mov    %rbx,%rsi
    571e:	8b 78 08             	mov    0x8(%rax),%edi
    5721:	e8 1a f5 ff ff       	call   4c40 <add_read_request>
              free(req);
    5726:	4c 89 e7             	mov    %r12,%rdi
    5729:	e8 92 cb ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    572e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5733:	48 85 c0             	test   %rax,%rax
    5736:	0f 85 14 01 00 00    	jne    5850 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    573c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5743:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    574a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    574d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5752:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5754:	f6 c1 02             	test   $0x2,%cl
    5757:	74 00                	je     5759 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5759:	89 d0                	mov    %edx,%eax
    575b:	29 f0                	sub    %esi,%eax
    575d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5764:	0f 82 50 ce ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    576a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    576d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5772:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5776:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5779:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5780:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5783:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    578a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5791:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5793:	8b 55 60             	mov    0x60(%rbp),%edx
    5796:	48 c1 e0 06          	shl    $0x6,%rax
    579a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    57a2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    57a8:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    57ab:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    57b3:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    57b7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    57bf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    57c7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    57cb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    57cf:	e8 6c cb ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    57d4:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    57d8:	0f 84 3a fe ff ff    	je     5618 <io_thread+0x2d8>
    57de:	48 8d 3d 2d 1a 00 00 	lea    0x1a2d(%rip),%rdi        # 7212 <_IO_stdin_used+0x212>
    57e5:	e8 06 cb ff ff       	call   22f0 <puts@plt>
}
    57ea:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    57f2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    57fb:	0f 85 18 02 00 00    	jne    5a19 <io_thread+0x6d9>
    5801:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5808:	31 c0                	xor    %eax,%eax
    580a:	5b                   	pop    %rbx
    580b:	5d                   	pop    %rbp
    580c:	41 5c                	pop    %r12
    580e:	41 5d                	pop    %r13
    5810:	41 5e                	pop    %r14
    5812:	41 5f                	pop    %r15
    5814:	c3                   	ret
    5815:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5818:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    581d:	48 85 c0             	test   %rax,%rax
    5820:	0f 84 6a fe ff ff    	je     5690 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5826:	48 83 38 01          	cmpq   $0x1,(%rax)
    582a:	0f 84 68 01 00 00    	je     5998 <io_thread+0x658>
    5830:	48 8d 3d a2 19 00 00 	lea    0x19a2(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    5837:	e8 b4 ca ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    583c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5841:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5844:	e9 8b fe ff ff       	jmp    56d4 <io_thread+0x394>
    5849:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5850:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5858:	8b 02                	mov    (%rdx),%eax
    585a:	83 c0 01             	add    $0x1,%eax
    585d:	89 02                	mov    %eax,(%rdx)
}
    585f:	e9 d8 fe ff ff       	jmp    573c <io_thread+0x3fc>
    5864:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5868:	85 c0                	test   %eax,%eax
    586a:	75 74                	jne    58e0 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    586c:	48 8b 0d ad 47 00 00 	mov    0x47ad(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5873:	ba 0f 00 00 00       	mov    $0xf,%edx
    5878:	be 01 00 00 00       	mov    $0x1,%esi
    587d:	48 8d 3d 7e 19 00 00 	lea    0x197e(%rip),%rdi        # 7202 <_IO_stdin_used+0x202>
    5884:	e8 37 cc ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5889:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    588e:	e9 a0 fe ff ff       	jmp    5733 <io_thread+0x3f3>
    5893:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5898:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    589d:	45 31 ff             	xor    %r15d,%r15d
    58a0:	85 c0                	test   %eax,%eax
    58a2:	7e 20                	jle    58c4 <io_thread+0x584>
    58a4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    58a8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    58ab:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    58af:	48 c1 e0 04          	shl    $0x4,%rax
    58b3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    58b8:	e8 03 ca ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    58bd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    58c2:	7f e4                	jg     58a8 <io_thread+0x568>
              close(req->client_socket);
    58c4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    58c9:	e8 a2 ca ff ff       	call   2370 <close@plt>
              free(req);
    58ce:	4c 89 e7             	mov    %r12,%rdi
    58d1:	e8 ea c9 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    58d6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    58db:	e9 53 fe ff ff       	jmp    5733 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    58e0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    58e5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    58ea:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    58f2:	eb 11                	jmp    5905 <io_thread+0x5c5>
    58f4:	0f 1f 40 00          	nopl   0x0(%rax)
    58f8:	48 83 c0 01          	add    $0x1,%rax
    58fc:	48 83 c2 01          	add    $0x1,%rdx
    5900:	48 39 c6             	cmp    %rax,%rsi
    5903:	74 4b                	je     5950 <io_thread+0x610>
        dest[i] = src[i];
    5905:	0f b6 0a             	movzbl (%rdx),%ecx
    5908:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    590a:	80 f9 0d             	cmp    $0xd,%cl
    590d:	75 e9                	jne    58f8 <io_thread+0x5b8>
    590f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5913:	75 e3                	jne    58f8 <io_thread+0x5b8>
            dest[i] = '\0';
    5915:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5918:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    591d:	48 89 da             	mov    %rbx,%rdx
    5920:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5925:	e8 96 f7 ff ff       	call   50c0 <handle_http_method>
              free(req->iov[0].iov_base);
    592a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    592f:	e8 8c c9 ff ff       	call   22c0 <free@plt>
              free(req);
    5934:	4c 89 e7             	mov    %r12,%rdi
    5937:	e8 84 c9 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    593c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5941:	e9 ed fd ff ff       	jmp    5733 <io_thread+0x3f3>
    5946:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5950:	48 8b 0d c9 46 00 00 	mov    0x46c9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5957:	ba 12 00 00 00       	mov    $0x12,%edx
    595c:	be 01 00 00 00       	mov    $0x1,%esi
    5961:	48 8d 3d f0 17 00 00 	lea    0x17f0(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    5968:	e8 53 cb ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    596d:	bf 01 00 00 00       	mov    $0x1,%edi
    5972:	e8 29 cb ff ff       	call   24a0 <exit@plt>
    5977:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5980:	e9 ec fb ff ff       	jmp    5571 <io_thread+0x231>
    5985:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5988:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    598d:	e9 94 fe ff ff       	jmp    5826 <io_thread+0x4e6>
    5992:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5998:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    59a0:	48 8d 3d 1e 18 00 00 	lea    0x181e(%rip),%rdi        # 71c5 <_IO_stdin_used+0x1c5>
    59a7:	8b 02                	mov    (%rdx),%eax
    59a9:	83 c0 01             	add    $0x1,%eax
    59ac:	89 02                	mov    %eax,(%rdx)
    59ae:	e8 3d c9 ff ff       	call   22f0 <puts@plt>
    59b3:	e9 26 fe ff ff       	jmp    57de <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    59b8:	f7 d8                	neg    %eax
    59ba:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    59bf:	89 c7                	mov    %eax,%edi
    59c1:	e8 3a cb ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    59c6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    59cb:	be 01 00 00 00       	mov    $0x1,%esi
    59d0:	48 8b 3d 49 46 00 00 	mov    0x4649(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    59d7:	48 89 c1             	mov    %rax,%rcx
    59da:	48 8d 15 07 1b 00 00 	lea    0x1b07(%rip),%rdx        # 74e8 <_IO_stdin_used+0x4e8>
    59e1:	31 c0                	xor    %eax,%eax
    59e3:	e8 e8 ca ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    59e8:	bf 01 00 00 00       	mov    $0x1,%edi
    59ed:	e8 ae ca ff ff       	call   24a0 <exit@plt>
    59f2:	48 8b 0d 27 46 00 00 	mov    0x4627(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    59f9:	ba 28 00 00 00       	mov    $0x28,%edx
    59fe:	be 01 00 00 00       	mov    $0x1,%esi
    5a03:	48 8d 3d ae 1a 00 00 	lea    0x1aae(%rip),%rdi        # 74b8 <_IO_stdin_used+0x4b8>
    5a0a:	e8 b1 ca ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5a0f:	bf 01 00 00 00       	mov    $0x1,%edi
    5a14:	e8 87 ca ff ff       	call   24a0 <exit@plt>
}
    5a19:	e8 12 c9 ff ff       	call   2330 <__stack_chk_fail@plt>
    5a1e:	66 90                	xchg   %ax,%ax

0000000000005a20 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5a20:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5a24:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5a2b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5a31:	85 c9                	test   %ecx,%ecx
    5a33:	0f 8e ea 00 00 00    	jle    5b23 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    5a39:	41 56                	push   %r14
    5a3b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5a3d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    5a40:	41 54                	push   %r12
    5a42:	49 89 fc             	mov    %rdi,%r12
    5a45:	55                   	push   %rbp
    5a46:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5a47:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5a4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5a50:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    5a54:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    5a5c:	31 db                	xor    %ebx,%ebx
    5a5e:	8b 10                	mov    (%rax),%edx
    5a60:	85 d2                	test   %edx,%edx
    5a62:	7e 26                	jle    5a8a <barriered_work_ingest+0x6a>
    5a64:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    5a68:	48 89 dd             	mov    %rbx,%rbp
    5a6b:	48 c1 e5 08          	shl    $0x8,%rbp
    5a6f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    5a73:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    5a7a:	74 24                	je     5aa0 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5a7c:	48 83 c3 01          	add    $0x1,%rbx
    5a80:	39 da                	cmp    %ebx,%edx
    5a82:	7f e4                	jg     5a68 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5a84:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5a8a:	49 83 c5 01          	add    $0x1,%r13
    5a8e:	44 39 e9             	cmp    %r13d,%ecx
    5a91:	7f bd                	jg     5a50 <barriered_work_ingest+0x30>
}
    5a93:	5b                   	pop    %rbx
    5a94:	31 c0                	xor    %eax,%eax
    5a96:	5d                   	pop    %rbp
    5a97:	41 5c                	pop    %r12
    5a99:	41 5d                	pop    %r13
    5a9b:	41 5e                	pop    %r14
    5a9d:	c3                   	ret
    5a9e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    5aa0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5aa9:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5ab0:	bf 04 00 00 00       	mov    $0x4,%edi
    5ab5:	48 c1 e6 05          	shl    $0x5,%rsi
    5ab9:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5ac0:	48 83 c6 10          	add    $0x10,%rsi
    5ac4:	e8 47 c8 ff ff       	call   2310 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5ac9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5ad1:	48 8b 40 50          	mov    0x50(%rax),%rax
    5ad5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5ad9:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    5add:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5ae7:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    5aed:	83 c0 01             	add    $0x1,%eax
    5af0:	99                   	cltd
    5af1:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5af7:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    5afd:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5b00:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5b08:	48 83 c3 01          	add    $0x1,%rbx
    5b0c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5b10:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5b14:	8b 10                	mov    (%rax),%edx
    5b16:	39 da                	cmp    %ebx,%edx
    5b18:	0f 8f 46 ff ff ff    	jg     5a64 <barriered_work_ingest+0x44>
    5b1e:	e9 61 ff ff ff       	jmp    5a84 <barriered_work_ingest+0x64>
}
    5b23:	31 c0                	xor    %eax,%eax
    5b25:	c3                   	ret
    5b26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005b30 <barriered_thread>:
void* barriered_thread(void *arg) {
    5b30:	f3 0f 1e fa          	endbr64
    5b34:	41 56                	push   %r14
    5b36:	41 55                	push   %r13
    5b38:	41 54                	push   %r12
  int t = 0;
    5b3a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    5b3d:	55                   	push   %rbp
  int waiting = 0;
    5b3e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    5b40:	53                   	push   %rbx
    5b41:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    5b44:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5b48:	0f 85 74 02 00 00    	jne    5dc2 <barriered_thread+0x292>
    if (t >= data->task_count) {
    5b4e:	8b 43 40             	mov    0x40(%rbx),%eax
    5b51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5b58:	41 39 c4             	cmp    %eax,%r12d
    5b5b:	0f 8d 6f 01 00 00    	jge    5cd0 <barriered_thread+0x1a0>
    5b61:	49 63 fc             	movslq %r12d,%rdi
    5b64:	48 c1 e7 09          	shl    $0x9,%rdi
    5b68:	49 89 fd             	mov    %rdi,%r13
    5b6b:	eb 32                	jmp    5b9f <barriered_thread+0x6f>
    5b6d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5b70:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5b74:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5b78:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5b7c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5b80:	4c 01 ef             	add    %r13,%rdi
    5b83:	e8 98 fe ff ff       	call   5a20 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    5b88:	8b 43 40             	mov    0x40(%rbx),%eax
    5b8b:	41 83 c4 01          	add    $0x1,%r12d
    5b8f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    5b96:	44 39 e0             	cmp    %r12d,%eax
    5b99:	0f 8e 19 02 00 00    	jle    5db8 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    5b9f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5ba3:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    5ba7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    5bae:	75 c0                	jne    5b70 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5bb0:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    5bb4:	83 e8 01             	sub    $0x1,%eax
    5bb7:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    5bbc:	45 85 e4             	test   %r12d,%r12d
    5bbf:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5bc2:	45 85 c0             	test   %r8d,%r8d
    5bc5:	0f 8e 2d 01 00 00    	jle    5cf8 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5bcb:	48 63 c8             	movslq %eax,%rcx
    5bce:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5bd2:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5bd5:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5bdb:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    5be2:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    5be6:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    5be9:	45 31 f6             	xor    %r14d,%r14d
    5bec:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5bf0:	48 8b 10             	mov    (%rax),%rdx
    5bf3:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    5bf7:	49 01 cb             	add    %rcx,%r11
    5bfa:	4c 89 da             	mov    %r11,%rdx
    5bfd:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    5c04:	75 04                	jne    5c0a <barriered_thread+0xda>
            arrived++;
    5c06:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5c0a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    5c10:	75 04                	jne    5c16 <barriered_thread+0xe6>
            prearrive++;
    5c12:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5c16:	48 83 c0 08          	add    $0x8,%rax
    5c1a:	48 39 c6             	cmp    %rax,%rsi
    5c1d:	75 d1                	jne    5bf0 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    5c1f:	45 85 d2             	test   %r10d,%r10d
    5c22:	0f 84 c0 00 00 00    	je     5ce8 <barriered_thread+0x1b8>
    5c28:	45 39 d0             	cmp    %r10d,%r8d
    5c2b:	0f 84 b7 00 00 00    	je     5ce8 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    5c31:	45 85 f6             	test   %r14d,%r14d
    5c34:	74 0a                	je     5c40 <barriered_thread+0x110>
    5c36:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    5c3a:	0f 85 ae 01 00 00    	jne    5dee <barriered_thread+0x2be>
    5c40:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    5c44:	4c 01 ea             	add    %r13,%rdx
    5c47:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    5c4e:	45 85 e4             	test   %r12d,%r12d
    5c51:	75 14                	jne    5c67 <barriered_thread+0x137>
    5c53:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5c5a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5c61:	0f 8c 69 01 00 00    	jl     5dd0 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5c67:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    5c6b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    5c6f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5c79:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    5c7d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5c81:	4c 01 ef             	add    %r13,%rdi
    5c84:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    5c8a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    5c8e:	4c 01 e8             	add    %r13,%rax
    5c91:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5c98:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    5c9b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5ca0:	83 e8 01             	sub    $0x1,%eax
    5ca3:	44 39 e0             	cmp    %r12d,%eax
    5ca6:	0f 84 a4 00 00 00    	je     5d50 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    5cac:	0f ae f8             	sfence
          if (waiting == 0) {
    5caf:	85 ed                	test   %ebp,%ebp
    5cb1:	0f 84 d1 00 00 00    	je     5d88 <barriered_thread+0x258>
        int arrived = 0; 
    5cb7:	bd 01 00 00 00       	mov    $0x1,%ebp
    5cbc:	e9 c7 fe ff ff       	jmp    5b88 <barriered_thread+0x58>
  while (data->running == 1) {
    5cc1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5cc5:	0f 85 f7 00 00 00    	jne    5dc2 <barriered_thread+0x292>
    5ccb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    5cd0:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    5cd8:	85 c0                	test   %eax,%eax
    5cda:	7e e5                	jle    5cc1 <barriered_thread+0x191>
    5cdc:	45 31 e4             	xor    %r12d,%r12d
    5cdf:	e9 7d fe ff ff       	jmp    5b61 <barriered_thread+0x31>
    5ce4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5ce8:	83 fd 01             	cmp    $0x1,%ebp
    5ceb:	74 1b                	je     5d08 <barriered_thread+0x1d8>
        int arrived = 0; 
    5ced:	31 ed                	xor    %ebp,%ebp
    5cef:	e9 3d ff ff ff       	jmp    5c31 <barriered_thread+0x101>
    5cf4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5cf8:	83 fd 01             	cmp    $0x1,%ebp
    5cfb:	0f 85 43 ff ff ff    	jne    5c44 <barriered_thread+0x114>
        int arrived = 0; 
    5d01:	45 31 f6             	xor    %r14d,%r14d
    5d04:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5d08:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5d0f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    5d14:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5d16:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5d1a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5d21:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    5d26:	e8 e5 c5 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    5d2b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5d32:	48 83 c0 01          	add    $0x1,%rax
    5d36:	48 99                	cqto
    5d38:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    5d3f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    5d46:	e9 e6 fe ff ff       	jmp    5c31 <barriered_thread+0x101>
    5d4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5d50:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5d57:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5d5e:	0f 8d 48 ff ff ff    	jge    5cac <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    5d64:	48 c1 e6 04          	shl    $0x4,%rsi
    5d68:	bf 04 00 00 00       	mov    $0x4,%edi
    5d6d:	48 03 73 70          	add    0x70(%rbx),%rsi
    5d71:	e8 9a c5 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    5d76:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    5d7e:	e9 29 ff ff ff       	jmp    5cac <barriered_thread+0x17c>
    5d83:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    5d88:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5d8f:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    5d94:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5d98:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5d9f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5da3:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5da7:	e8 64 c5 ff ff       	call   2310 <clock_gettime@plt>
            waiting = 1;
    5dac:	e9 06 ff ff ff       	jmp    5cb7 <barriered_thread+0x187>
    5db1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    5db8:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5dbc:	0f 84 96 fd ff ff    	je     5b58 <barriered_thread+0x28>
}
    5dc2:	5b                   	pop    %rbx
    5dc3:	31 c0                	xor    %eax,%eax
    5dc5:	5d                   	pop    %rbp
    5dc6:	41 5c                	pop    %r12
    5dc8:	41 5d                	pop    %r13
    5dca:	41 5e                	pop    %r14
    5dcc:	c3                   	ret
    5dcd:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    5dd0:	48 c1 e6 04          	shl    $0x4,%rsi
    5dd4:	bf 04 00 00 00       	mov    $0x4,%edi
    5dd9:	48 03 73 68          	add    0x68(%rbx),%rsi
    5ddd:	e8 2e c5 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    5de2:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5de6:	4c 01 ea             	add    %r13,%rdx
    5de9:	e9 79 fe ff ff       	jmp    5c67 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5dee:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5df2:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5df6:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5dfa:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5dfe:	4c 01 ef             	add    %r13,%rdi
    5e01:	e8 1a fc ff ff       	call   5a20 <barriered_work_ingest>
          break;
    5e06:	e9 39 fd ff ff       	jmp    5b44 <barriered_thread+0x14>
    5e0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005e10 <receive>:
int receive(struct BarrierTask *data) {
    5e10:	f3 0f 1e fa          	endbr64
    5e14:	41 57                	push   %r15
    5e16:	41 56                	push   %r14
    5e18:	41 55                	push   %r13
    5e1a:	41 54                	push   %r12
    5e1c:	55                   	push   %rbp
    5e1d:	53                   	push   %rbx
    5e1e:	48 83 ec 08          	sub    $0x8,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5e22:	48 63 87 40 01 00 00 	movslq 0x140(%rdi),%rax
    5e29:	85 c0                	test   %eax,%eax
    5e2b:	0f 8e fd 00 00 00    	jle    5f2e <receive+0x11e>
    5e31:	48 8b b7 70 01 00 00 	mov    0x170(%rdi),%rsi
    5e38:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    5e3c:	48 89 fa             	mov    %rdi,%rdx
    5e3f:	4c 8d 2c c6          	lea    (%rsi,%rax,8),%r13
    5e43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5e48:	44 8b 66 20          	mov    0x20(%rsi),%r12d
    struct Data *me = data->mailboxes[n].lower;
    5e4c:	48 8b 2e             	mov    (%rsi),%rbp
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5e4f:	41 83 fc 02          	cmp    $0x2,%r12d
    5e53:	0f 84 07 01 00 00    	je     5f60 <receive+0x150>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5e59:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    5e60:	48 85 ff             	test   %rdi,%rdi
    5e63:	0f 8e ad 00 00 00    	jle    5f16 <receive+0x106>
      data->sends++;
    5e69:	4c 8b 8a 78 01 00 00 	mov    0x178(%rdx),%r9
      data->n++;
    5e70:	4c 8b 82 08 01 00 00 	mov    0x108(%rdx),%r8
      data->mailboxes[n].received++;
    5e77:	31 c0                	xor    %eax,%eax
    5e79:	48 8b 4e 18          	mov    0x18(%rsi),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5e7d:	48 8b 5d 00          	mov    0x0(%rbp),%rbx
    5e81:	4d 8d 51 01          	lea    0x1(%r9),%r10
    5e85:	4c 63 5a 04          	movslq 0x4(%rdx),%r11
    5e89:	4d 8d 48 01          	lea    0x1(%r8),%r9
    5e8d:	4c 8d 41 01          	lea    0x1(%rcx),%r8
    5e91:	eb 0e                	jmp    5ea1 <receive+0x91>
    5e93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5e98:	48 83 c0 01          	add    $0x1,%rax
    5e9c:	48 39 f8             	cmp    %rdi,%rax
    5e9f:	7d 6f                	jge    5f10 <receive+0x100>
      data->sends++;
    5ea1:	49 8d 0c 02          	lea    (%r10,%rax,1),%rcx
    5ea5:	48 89 8a 78 01 00 00 	mov    %rcx,0x178(%rdx)
      data->n++;
    5eac:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    5eb0:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5eb7:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5ebb:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    5ebf:	48 8b 0c c3          	mov    (%rbx,%rax,8),%rcx
    5ec3:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5ec7:	75 cf                	jne    5e98 <receive+0x88>
    5ec9:	4c 8b b2 28 01 00 00 	mov    0x128(%rdx),%r14
    5ed0:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    5ed4:	4d 63 7e 08          	movslq 0x8(%r14),%r15
    5ed8:	4c 39 f9             	cmp    %r15,%rcx
    5edb:	75 bb                	jne    5e98 <receive+0x88>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    5edd:	49 63 46 04          	movslq 0x4(%r14),%rax
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5ee1:	bf 01 00 00 00       	mov    $0x1,%edi
    5ee6:	ba 01 00 00 00       	mov    $0x1,%edx
    5eeb:	48 8d 35 1e 16 00 00 	lea    0x161e(%rip),%rsi        # 7510 <_IO_stdin_used+0x510>
    5ef2:	48 39 c8             	cmp    %rcx,%rax
    5ef5:	0f 94 c1             	sete   %cl
    5ef8:	31 c0                	xor    %eax,%eax
    5efa:	0f b6 c9             	movzbl %cl,%ecx
    5efd:	e8 4e c5 ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5f02:	bf 01 00 00 00       	mov    $0x1,%edi
    5f07:	e8 94 c5 ff ff       	call   24a0 <exit@plt>
    5f0c:	0f 1f 40 00          	nopl   0x0(%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5f10:	41 83 fc 02          	cmp    $0x2,%r12d
    5f14:	74 32                	je     5f48 <receive+0x138>
    me->messages_count = 0;
    5f16:	48 c7 85 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rbp)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5f21:	48 83 c6 28          	add    $0x28,%rsi
    5f25:	49 39 f5             	cmp    %rsi,%r13
    5f28:	0f 85 1a ff ff ff    	jne    5e48 <receive+0x38>
  asm volatile ("sfence" ::: "memory");
    5f2e:	0f ae f8             	sfence
}
    5f31:	48 83 c4 08          	add    $0x8,%rsp
    5f35:	31 c0                	xor    %eax,%eax
    5f37:	5b                   	pop    %rbx
    5f38:	5d                   	pop    %rbp
    5f39:	41 5c                	pop    %r12
    5f3b:	41 5d                	pop    %r13
    5f3d:	41 5e                	pop    %r14
    5f3f:	41 5f                	pop    %r15
    5f41:	c3                   	ret
    5f42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5f48:	83 bd 00 01 00 00 01 	cmpl   $0x1,0x100(%rbp)
    5f4f:	75 c5                	jne    5f16 <receive+0x106>
      me->available = 0;
    5f51:	c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbp)
    5f5b:	eb b9                	jmp    5f16 <receive+0x106>
    5f5d:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5f60:	8b 85 00 01 00 00    	mov    0x100(%rbp),%eax
    5f66:	83 f8 01             	cmp    $0x1,%eax
    5f69:	74 09                	je     5f74 <receive+0x164>
    else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 0) {
    5f6b:	85 c0                	test   %eax,%eax
    5f6d:	74 b2                	je     5f21 <receive+0x111>
    5f6f:	e9 e5 fe ff ff       	jmp    5e59 <receive+0x49>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5f74:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    5f7b:	48 85 ff             	test   %rdi,%rdi
    5f7e:	0f 8f e5 fe ff ff    	jg     5e69 <receive+0x59>
    5f84:	eb cb                	jmp    5f51 <receive+0x141>
    5f86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005f90 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5f90:	f3 0f 1e fa          	endbr64
    5f94:	41 57                	push   %r15
    5f96:	41 56                	push   %r14
    5f98:	41 55                	push   %r13
    5f9a:	41 54                	push   %r12
    5f9c:	55                   	push   %rbp
    5f9d:	48 89 fd             	mov    %rdi,%rbp
    5fa0:	53                   	push   %rbx
    5fa1:	48 83 ec 38          	sub    $0x38,%rsp
  if (data->thread_index == data->task_index) {
    5fa5:	8b 47 04             	mov    0x4(%rdi),%eax
    5fa8:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    5fae:	74 50                	je     6000 <barriered_work+0x70>
    receive(data);
    5fb0:	e8 5b fe ff ff       	call   5e10 <receive>
    while (data->scheduled == 1) {
    5fb5:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    5fbc:	75 16                	jne    5fd4 <barriered_work+0x44>
    5fbe:	66 90                	xchg   %ax,%ax
      data->n++;
    5fc0:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      asm volatile ("sfence" ::: "memory");
    5fc8:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5fcb:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    5fd2:	74 ec                	je     5fc0 <barriered_work+0x30>
  if (data->sending == 1) {
    5fd4:	83 bd 80 01 00 00 01 	cmpl   $0x1,0x180(%rbp)
    5fdb:	75 08                	jne    5fe5 <barriered_work+0x55>
    5fdd:	48 89 ef             	mov    %rbp,%rdi
    5fe0:	e8 7b e2 ff ff       	call   4260 <sendm.part.0>
  asm volatile ("sfence" ::: "memory");
    5fe5:	0f ae f8             	sfence
}
    5fe8:	48 83 c4 38          	add    $0x38,%rsp
    5fec:	31 c0                	xor    %eax,%eax
    5fee:	5b                   	pop    %rbx
    5fef:	5d                   	pop    %rbp
    5ff0:	41 5c                	pop    %r12
    5ff2:	41 5d                	pop    %r13
    5ff4:	41 5e                	pop    %r14
    5ff6:	41 5f                	pop    %r15
    5ff8:	c3                   	ret
    5ff9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      receive(data);
    6000:	e8 0b fe ff ff       	call   5e10 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6005:	8b bd 40 01 00 00    	mov    0x140(%rbp),%edi
        int t = data->task_index;
    600b:	8b 45 04             	mov    0x4(%rbp),%eax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    600e:	85 ff                	test   %edi,%edi
    6010:	0f 8e e7 01 00 00    	jle    61fd <barriered_work+0x26d>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6016:	48 63 d0             	movslq %eax,%rdx
    6019:	45 31 ff             	xor    %r15d,%r15d
    601c:	44 8d 60 01          	lea    0x1(%rax),%r12d
    6020:	48 c1 e2 09          	shl    $0x9,%rdx
    6024:	48 89 54 24 20       	mov    %rdx,0x20(%rsp)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6029:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6030:	4f 8d 34 7f          	lea    (%r15,%r15,2),%r14
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6034:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    6039:	4f 8d 2c bf          	lea    (%r15,%r15,4),%r13
    603d:	31 db                	xor    %ebx,%ebx
    603f:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    6046:	49 c1 e6 06          	shl    $0x6,%r14
    604a:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    604f:	49 c1 e5 03          	shl    $0x3,%r13
    6053:	4c 8b 40 20          	mov    0x20(%rax),%r8
    6057:	4b 8b 44 30 38       	mov    0x38(%r8,%r14,1),%rax
    605c:	48 8b b4 30 70 01 00 00 	mov    0x170(%rax,%rsi,1),%rsi
    6064:	e9 ab 00 00 00       	jmp    6114 <barriered_work+0x184>
    6069:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                 if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 0 && ((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].lower)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available == 0 && ((struct Data*) data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available == 0) {
    6070:	44 8b 89 00 01 00 00 	mov    0x100(%rcx),%r9d
    6077:	45 85 c9             	test   %r9d,%r9d
    607a:	0f 85 88 00 00 00    	jne    6108 <barriered_work+0x178>
    6080:	4c 8b 0a             	mov    (%rdx),%r9
    6083:	45 8b b9 00 01 00 00 	mov    0x100(%r9),%r15d
    608a:	45 85 ff             	test   %r15d,%r15d
    608d:	75 79                	jne    6108 <barriered_work+0x178>
    608f:	4c 8d 14 5b          	lea    (%rbx,%rbx,2),%r10
    6093:	48 98                	cltq
    6095:	49 c1 e2 06          	shl    $0x6,%r10
    6099:	48 c1 e0 09          	shl    $0x9,%rax
    609d:	4b 03 44 10 38       	add    0x38(%r8,%r10,1),%rax
    60a2:	4c 8b 98 70 01 00 00 	mov    0x170(%rax),%r11
    60a9:	4d 01 eb             	add    %r13,%r11
    60ac:	4d 8b 53 08          	mov    0x8(%r11),%r10
    60b0:	4c 89 d8             	mov    %r11,%rax
    60b3:	45 8b 9a 00 01 00 00 	mov    0x100(%r10),%r11d
    60ba:	45 85 db             	test   %r11d,%r11d
    60bd:	75 49                	jne    6108 <barriered_work+0x178>
    60bf:	4c 8b 18             	mov    (%rax),%r11
    60c2:	45 8b bb 00 01 00 00 	mov    0x100(%r11),%r15d
    60c9:	45 85 ff             	test   %r15d,%r15d
    60cc:	75 3a                	jne    6108 <barriered_work+0x178>
                  data->thread->all_threads[y].tasks[t].mailboxes[b].lower = _c;
    60ce:	66 49 0f 6e c2       	movq   %r10,%xmm0
    60d3:	66 49 0f 6e db       	movq   %r11,%xmm3
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = _a;
    60d8:	66 49 0f 6e e1       	movq   %r9,%xmm4
                  data->thread->all_threads[y].tasks[t].mailboxes[b].lower = _c;
    60dd:	66 0f 6c c3          	punpcklqdq %xmm3,%xmm0
    60e1:	0f 11 02             	movups %xmm0,(%rdx)
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = _a;
    60e4:	66 48 0f 6e c1       	movq   %rcx,%xmm0
    60e9:	66 0f 6c c4          	punpcklqdq %xmm4,%xmm0
    60ed:	0f 11 00             	movups %xmm0,(%rax)
                  ((struct Data*)_a)->available = 1;
    60f0:	c7 81 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rcx)
                  ((struct Data*)_c)->available = 1;
    60fa:	41 c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r10)
    6105:	0f 1f 00             	nopl   (%rax)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6108:	48 83 c3 01          	add    $0x1,%rbx
    610c:	39 df                	cmp    %ebx,%edi
    610e:	0f 8e d7 00 00 00    	jle    61eb <barriered_work+0x25b>
              int next_task = abs((t + 1) % (data->thread_count));
    6114:	44 89 e0             	mov    %r12d,%eax
    6117:	99                   	cltd
    6118:	f7 bd 34 01 00 00    	idivl  0x134(%rbp)
    611e:	89 d0                	mov    %edx,%eax
    6120:	f7 d8                	neg    %eax
    6122:	0f 48 c2             	cmovs  %edx,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6125:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    6129:	48 8d 14 d6          	lea    (%rsi,%rdx,8),%rdx
              if (kind == MAILBOX_FRIEND) {
    612d:	83 7a 20 01          	cmpl   $0x1,0x20(%rdx)
                  void * _a = data->thread->all_threads[y].tasks[t].mailboxes[b].higher;
    6131:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
              if (kind == MAILBOX_FRIEND) {
    6135:	0f 85 35 ff ff ff    	jne    6070 <barriered_work+0xe0>
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    613b:	4c 63 7a 24          	movslq 0x24(%rdx),%r15
    613f:	4c 63 c8             	movslq %eax,%r9
    6142:	66 48 0f 6e c9       	movq   %rcx,%xmm1
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6147:	48 83 c3 01          	add    $0x1,%rbx
                  int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
    614b:	49 c1 e1 09          	shl    $0x9,%r9
    614f:	0f 16 0a             	movhps (%rdx),%xmm1
    6152:	bf 01 00 00 00       	mov    $0x1,%edi
    6157:	4f 8d 14 7f          	lea    (%r15,%r15,2),%r10
    615b:	48 8d 35 c3 10 00 00 	lea    0x10c3(%rip),%rsi        # 7225 <_IO_stdin_used+0x225>
    6162:	4c 89 0c 24          	mov    %r9,(%rsp)
    6166:	49 c1 e2 06          	shl    $0x6,%r10
    616a:	0f 29 4c 24 10       	movaps %xmm1,0x10(%rsp)
    616f:	4b 8b 44 10 38       	mov    0x38(%r8,%r10,1),%rax
    6174:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    6179:	4a 8b 84 08 70 01 00 00 	mov    0x170(%rax,%r9,1),%rax
    6181:	42 8b 54 28 20       	mov    0x20(%rax,%r13,1),%edx
    6186:	31 c0                	xor    %eax,%eax
    6188:	e8 c3 c2 ff ff       	call   2450 <__printf_chk@plt>
                  void * _c = data->thread->all_threads[other].tasks[next_task].mailboxes[y].higher;
    618d:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    6194:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    6199:	4c 89 e9             	mov    %r13,%rcx
    619c:	4c 8b 0c 24          	mov    (%rsp),%r9
                  data->thread->all_threads[y].tasks[t].mailboxes[other].higher = _d;
    61a0:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
                  void * _c = data->thread->all_threads[other].tasks[next_task].mailboxes[y].higher;
    61a5:	4c 8b 40 20          	mov    0x20(%rax),%r8
                  data->thread->all_threads[other].tasks[next_task].mailboxes[y].lower = _a;
    61a9:	66 0f 6f 4c 24 10    	movdqa 0x10(%rsp),%xmm1
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    61af:	8b bd 40 01 00 00    	mov    0x140(%rbp),%edi
                  void * _c = data->thread->all_threads[other].tasks[next_task].mailboxes[y].higher;
    61b5:	4b 8b 44 10 38       	mov    0x38(%r8,%r10,1),%rax
                  data->thread->all_threads[y].tasks[t].mailboxes[other].higher = _d;
    61ba:	4b 8b 54 30 38       	mov    0x38(%r8,%r14,1),%rdx
                  void * _c = data->thread->all_threads[other].tasks[next_task].mailboxes[y].higher;
    61bf:	4a 03 8c 08 70 01 00 00 	add    0x170(%rax,%r9,1),%rcx
                  data->thread->all_threads[y].tasks[t].mailboxes[other].higher = _d;
    61c7:	48 8b b4 32 70 01 00 00 	mov    0x170(%rdx,%rsi,1),%rsi
                  data->thread->all_threads[y].tasks[t].mailboxes[other].lower = _c;
    61cf:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
                  void * _d = data->thread->all_threads[other].tasks[next_task].mailboxes[y].lower;
    61d3:	f3 0f 6f 01          	movdqu (%rcx),%xmm0
    61d7:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
                  data->thread->all_threads[y].tasks[t].mailboxes[other].lower = _c;
    61dc:	0f 11 04 d6          	movups %xmm0,(%rsi,%rdx,8)
                  data->thread->all_threads[other].tasks[next_task].mailboxes[y].lower = _a;
    61e0:	0f 11 09             	movups %xmm1,(%rcx)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    61e3:	39 df                	cmp    %ebx,%edi
    61e5:	0f 8f 29 ff ff ff    	jg     6114 <barriered_work+0x184>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    61eb:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    61f0:	49 83 c7 01          	add    $0x1,%r15
    61f4:	44 39 ff             	cmp    %r15d,%edi
    61f7:	0f 8f 33 fe ff ff    	jg     6030 <barriered_work+0xa0>
      asm volatile ("sfence" ::: "memory");
    61fd:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6200:	48 8b b5 60 01 00 00 	mov    0x160(%rbp),%rsi
    6207:	31 ff                	xor    %edi,%edi
    6209:	48 c1 e6 05          	shl    $0x5,%rsi
    620d:	48 03 b5 50 01 00 00 	add    0x150(%rbp),%rsi
    6214:	e8 f7 c0 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6219:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    while (data->scheduled == 1) {
    6220:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    int modcount = ++data->thread->protected_state->modcount;
    6227:	48 8b 50 48          	mov    0x48(%rax),%rdx
    622b:	8b 4a 10             	mov    0x10(%rdx),%ecx
    622e:	8d 59 01             	lea    0x1(%rcx),%ebx
    6231:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    6234:	75 5b                	jne    6291 <barriered_work+0x301>
    6236:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6240:	48 63 95 30 01 00 00 	movslq 0x130(%rbp),%rdx
    6247:	48 8b 40 18          	mov    0x18(%rax),%rax
    624b:	48 63 7d 04          	movslq 0x4(%rbp),%rdi
      data->n++;
    624f:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6257:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    625b:	48 c1 e7 09          	shl    $0x9,%rdi
    625f:	48 03 78 38          	add    0x38(%rax),%rdi
    6263:	ff 95 20 01 00 00    	call   *0x120(%rbp)
      asm volatile ("sfence" ::: "memory");
    6269:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    626c:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    if (modcount != data->thread->protected_state->modcount) {
    6273:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    while (data->scheduled == 1) {
    627a:	74 c4                	je     6240 <barriered_work+0x2b0>
    if (modcount != data->thread->protected_state->modcount) {
    627c:	48 8b 40 48          	mov    0x48(%rax),%rax
    6280:	3b 58 10             	cmp    0x10(%rax),%ebx
    6283:	74 0c                	je     6291 <barriered_work+0x301>
    6285:	48 8d 3d aa 0f 00 00 	lea    0xfaa(%rip),%rdi        # 7236 <_IO_stdin_used+0x236>
    628c:	e8 5f c0 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6291:	48 8b b5 60 01 00 00 	mov    0x160(%rbp),%rsi
    6298:	31 ff                	xor    %edi,%edi
    629a:	48 c1 e6 05          	shl    $0x5,%rsi
    629e:	48 03 b5 50 01 00 00 	add    0x150(%rbp),%rsi
    62a5:	48 83 c6 10          	add    $0x10,%rsi
    62a9:	e8 62 c0 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    62ae:	48 8b 85 60 01 00 00 	mov    0x160(%rbp),%rax
    62b5:	48 83 c0 01          	add    $0x1,%rax
    62b9:	48 99                	cqto
    62bb:	48 f7 bd 58 01 00 00 	idivq  0x158(%rbp)
    62c2:	48 89 95 60 01 00 00 	mov    %rdx,0x160(%rbp)
    62c9:	e9 06 fd ff ff       	jmp    5fd4 <barriered_work+0x44>
    62ce:	66 90                	xchg   %ax,%ax

00000000000062d0 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    62d0:	f3 0f 1e fa          	endbr64
    62d4:	53                   	push   %rbx
    62d5:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    62d8:	e8 43 f7 ff ff       	call   5a20 <barriered_work_ingest>
  barriered_work(data);
    62dd:	48 89 df             	mov    %rbx,%rdi
}
    62e0:	5b                   	pop    %rbx
  barriered_work(data);
    62e1:	e9 aa fc ff ff       	jmp    5f90 <barriered_work>
    62e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000062f0 <sendm>:
int sendm(struct BarrierTask *data) {
    62f0:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    62f4:	83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%rdi)
    62fb:	74 03                	je     6300 <sendm+0x10>
}
    62fd:	31 c0                	xor    %eax,%eax
    62ff:	c3                   	ret
int sendm(struct BarrierTask *data) {
    6300:	48 83 ec 08          	sub    $0x8,%rsp
    6304:	e8 57 df ff ff       	call   4260 <sendm.part.0>
}
    6309:	31 c0                	xor    %eax,%eax
    630b:	48 83 c4 08          	add    $0x8,%rsp
    630f:	c3                   	ret

0000000000006310 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6310:	f3 0f 1e fa          	endbr64
}
    6314:	31 c0                	xor    %eax,%eax
    6316:	c3                   	ret
    6317:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006320 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6320:	f3 0f 1e fa          	endbr64
    6324:	31 c0                	xor    %eax,%eax
    6326:	c3                   	ret
    6327:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006330 <after>:
int after(struct timespec left, struct timespec right) {
    6330:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6334:	31 c0                	xor    %eax,%eax
    6336:	48 39 d7             	cmp    %rdx,%rdi
    6339:	7e 08                	jle    6343 <after+0x13>
    633b:	31 c0                	xor    %eax,%eax
    633d:	48 39 ce             	cmp    %rcx,%rsi
    6340:	0f 9f c0             	setg   %al
}
    6343:	c3                   	ret
    6344:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    634f:	90                   	nop

0000000000006350 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6350:	f3 0f 1e fa          	endbr64
    6354:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6359:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    635e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6360:	48 39 d7             	cmp    %rdx,%rdi
    6363:	7f 18                	jg     637d <within+0x2d>
    6365:	4d 39 d8             	cmp    %r11,%r8
    6368:	0f 9e c2             	setle  %dl
    636b:	48 39 ce             	cmp    %rcx,%rsi
    636e:	0f 9e c0             	setle  %al
    6371:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6373:	31 c0                	xor    %eax,%eax
    6375:	4d 39 d1             	cmp    %r10,%r9
    6378:	0f 9e c0             	setle  %al
    637b:	21 d0                	and    %edx,%eax
}
    637d:	c3                   	ret
    637e:	66 90                	xchg   %ax,%ax

0000000000006380 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6380:	f3 0f 1e fa          	endbr64
    6384:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6389:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    638e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6393:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6398:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    639d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    63a2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    63a7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    63ac:	48 39 fe             	cmp    %rdi,%rsi
    63af:	7d 2f                	jge    63e0 <overlap+0x60>
    63b1:	48 39 ca             	cmp    %rcx,%rdx
    63b4:	7d 62                	jge    6418 <overlap+0x98>
    63b6:	4d 39 da             	cmp    %r11,%r10
    63b9:	7d 0e                	jge    63c9 <overlap+0x49>
    return 1;
    63bb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    63c0:	4d 39 c1             	cmp    %r8,%r9
    63c3:	0f 8c 7f 00 00 00    	jl     6448 <overlap+0xc8>
  return 0;
    63c9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    63cb:	4d 39 c1             	cmp    %r8,%r9
    63ce:	7f 4c                	jg     641c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    63d0:	31 c0                	xor    %eax,%eax
    63d2:	4d 39 da             	cmp    %r11,%r10
    63d5:	0f 9e c0             	setle  %al
    63d8:	c3                   	ret
    63d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    63e0:	7e 4e                	jle    6430 <overlap+0xb0>
    63e2:	48 39 ca             	cmp    %rcx,%rdx
    63e5:	7f 39                	jg     6420 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    63e7:	75 31                	jne    641a <overlap+0x9a>
    63e9:	4d 39 c1             	cmp    %r8,%r9
    63ec:	7c 2c                	jl     641a <overlap+0x9a>
    return 1;
    63ee:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    63f3:	4d 39 da             	cmp    %r11,%r10
    63f6:	7d 24                	jge    641c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    63f8:	48 39 ca             	cmp    %rcx,%rdx
    63fb:	0f 94 c2             	sete   %dl
    63fe:	48 39 fe             	cmp    %rdi,%rsi
    6401:	0f 94 c0             	sete   %al
    6404:	21 c2                	and    %eax,%edx
    6406:	31 c0                	xor    %eax,%eax
    6408:	4d 39 c1             	cmp    %r8,%r9
    640b:	0f 94 c0             	sete   %al
    640e:	21 d0                	and    %edx,%eax
    6410:	c3                   	ret
    6411:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6418:	74 af                	je     63c9 <overlap+0x49>
  return 0;
    641a:	31 c0                	xor    %eax,%eax
}
    641c:	c3                   	ret
    641d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6420:	4d 39 da             	cmp    %r11,%r10
    6423:	7e c4                	jle    63e9 <overlap+0x69>
    return 1;
    6425:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    642a:	4d 39 c1             	cmp    %r8,%r9
    642d:	7e ba                	jle    63e9 <overlap+0x69>
    642f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6430:	48 39 ca             	cmp    %rcx,%rdx
    6433:	7c 94                	jl     63c9 <overlap+0x49>
    6435:	4d 39 c1             	cmp    %r8,%r9
    6438:	7d b4                	jge    63ee <overlap+0x6e>
    643a:	48 39 ca             	cmp    %rcx,%rdx
    643d:	74 91                	je     63d0 <overlap+0x50>
    643f:	eb d9                	jmp    641a <overlap+0x9a>
    6441:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6448:	c3                   	ret
    6449:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006450 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6450:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6454:	85 f6                	test   %esi,%esi
    6456:	0f 8e 44 03 00 00    	jle    67a0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    645c:	41 57                	push   %r15
    645e:	41 89 f7             	mov    %esi,%r15d
    6461:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6463:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6466:	41 55                	push   %r13
    6468:	41 54                	push   %r12
    646a:	55                   	push   %rbp
    646b:	53                   	push   %rbx
    646c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6470:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6474:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6479:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    647e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6481:	45 39 e6             	cmp    %r12d,%r14d
    6484:	0f 84 4e 02 00 00    	je     66d8 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    648a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    648f:	8b 50 08             	mov    0x8(%rax),%edx
    6492:	85 d2                	test   %edx,%edx
    6494:	0f 8e 3e 02 00 00    	jle    66d8 <verify+0x288>
    649a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    649f:	31 c9                	xor    %ecx,%ecx
    64a1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    64a6:	31 c0                	xor    %eax,%eax
    64a8:	44 89 f2             	mov    %r14d,%edx
    64ab:	bf 01 00 00 00       	mov    $0x1,%edi
    64b0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    64b5:	48 8d 35 8a 0d 00 00 	lea    0xd8a(%rip),%rsi        # 7246 <_IO_stdin_used+0x246>
    64bc:	e8 8f bf ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    64c1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    64c6:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    64cb:	8b 40 08             	mov    0x8(%rax),%eax
    64ce:	85 c0                	test   %eax,%eax
    64d0:	0f 8e e6 01 00 00    	jle    66bc <verify+0x26c>
    64d6:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    64d9:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    64de:	31 db                	xor    %ebx,%ebx
    64e0:	48 c1 e0 09          	shl    $0x9,%rax
    64e4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    64e9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    64ee:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    64f3:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    64f8:	4c 8b 20             	mov    (%rax),%r12
    64fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6500:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6505:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    650a:	49 89 de             	mov    %rbx,%r14
    650d:	48 8d 35 47 0d 00 00 	lea    0xd47(%rip),%rsi        # 725b <_IO_stdin_used+0x25b>
    6514:	49 c1 e6 09          	shl    $0x9,%r14
    6518:	bf 01 00 00 00       	mov    $0x1,%edi
    651d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6521:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    6529:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    652e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    6536:	31 c0                	xor    %eax,%eax
    6538:	e8 13 bf ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    653d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6542:	4c 8b 20             	mov    (%rax),%r12
    6545:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    654e:	0f 8e 47 01 00 00    	jle    669b <verify+0x24b>
    6554:	4c 03 75 00          	add    0x0(%rbp),%r14
    6558:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    655d:	ba 01 00 00 00       	mov    $0x1,%edx
    6562:	4d 89 f5             	mov    %r14,%r13
    6565:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    656c:	4d 85 f6             	test   %r14,%r14
    656f:	0f 8e 21 01 00 00    	jle    6696 <verify+0x246>
    6575:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6578:	48 89 d5             	mov    %rdx,%rbp
    657b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6580:	31 db                	xor    %ebx,%ebx
    6582:	4d 89 f2             	mov    %r14,%r10
    6585:	48 c1 e5 05          	shl    $0x5,%rbp
    6589:	48 83 ed 20          	sub    $0x20,%rbp
    658d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6591:	49 89 ee             	mov    %rbp,%r14
    6594:	48 89 dd             	mov    %rbx,%rbp
    6597:	48 89 d3             	mov    %rdx,%rbx
    659a:	eb 31                	jmp    65cd <verify+0x17d>
    659c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    65a0:	4c 39 c2             	cmp    %r8,%rdx
    65a3:	0f 8d 57 01 00 00    	jge    6700 <verify+0x2b0>
    65a9:	4c 39 df             	cmp    %r11,%rdi
    65ac:	7e 05                	jle    65b3 <verify+0x163>
    65ae:	49 39 c1             	cmp    %rax,%r9
    65b1:	7c 75                	jl     6628 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    65b3:	4c 39 df             	cmp    %r11,%rdi
    65b6:	0f 8d ab 01 00 00    	jge    6767 <verify+0x317>
    65bc:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    65c0:	48 83 c5 01          	add    $0x1,%rbp
    65c4:	49 39 ea             	cmp    %rbp,%r10
    65c7:	0f 8e a9 00 00 00    	jle    6676 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    65cd:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    65d4:	48 89 e8             	mov    %rbp,%rax
    65d7:	48 c1 e0 05          	shl    $0x5,%rax
    65db:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    65e2:	4c 01 f2             	add    %r14,%rdx
    65e5:	48 8b 08             	mov    (%rax),%rcx
    65e8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    65ec:	48 8b 32             	mov    (%rdx),%rsi
    65ef:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    65f3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    65f7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    65fb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    65ff:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6603:	48 39 f1             	cmp    %rsi,%rcx
    6606:	7c 98                	jl     65a0 <verify+0x150>
    6608:	0f 8e 42 01 00 00    	jle    6750 <verify+0x300>
    660e:	4c 39 c2             	cmp    %r8,%rdx
    6611:	0f 8f f9 00 00 00    	jg     6710 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6617:	75 a7                	jne    65c0 <verify+0x170>
    6619:	4c 39 df             	cmp    %r11,%rdi
    661c:	7f a2                	jg     65c0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    661e:	49 39 c1             	cmp    %rax,%r9
    6621:	7c 9d                	jl     65c0 <verify+0x170>
    6623:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6628:	49 89 c1             	mov    %rax,%r9
    662b:	48 89 f9             	mov    %rdi,%rcx
    662e:	48 89 f2             	mov    %rsi,%rdx
    6631:	bf 01 00 00 00       	mov    $0x1,%edi
    6636:	48 8d 35 fb 0e 00 00 	lea    0xefb(%rip),%rsi        # 7538 <_IO_stdin_used+0x538>
    663d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    663f:	48 83 c5 01          	add    $0x1,%rbp
    6643:	e8 08 be ff ff       	call   2450 <__printf_chk@plt>
    6648:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    664d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    6652:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6655:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    665a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6661:	4c 8b 20             	mov    (%rax),%r12
    6664:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6669:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    666d:	49 39 ea             	cmp    %rbp,%r10
    6670:	0f 8f 57 ff ff ff    	jg     65cd <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6676:	48 89 da             	mov    %rbx,%rdx
    6679:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    6680:	7d 14                	jge    6696 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6682:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6689:	48 83 c2 01          	add    $0x1,%rdx
    668d:	4d 85 f6             	test   %r14,%r14
    6690:	0f 8f e2 fe ff ff    	jg     6578 <verify+0x128>
    6696:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    669b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    66a0:	48 83 c3 01          	add    $0x1,%rbx
    66a4:	39 58 08             	cmp    %ebx,0x8(%rax)
    66a7:	0f 8f 53 fe ff ff    	jg     6500 <verify+0xb0>
    66ad:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    66b2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    66b7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    66bc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    66c1:	48 83 c1 01          	add    $0x1,%rcx
    66c5:	39 48 08             	cmp    %ecx,0x8(%rax)
    66c8:	0f 8f d8 fd ff ff    	jg     64a6 <verify+0x56>
    66ce:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    66d3:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    66d8:	48 81 44 24 10 c0 00 00 00 	addq   $0xc0,0x10(%rsp)
    66e1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    66e6:	41 39 c7             	cmp    %eax,%r15d
    66e9:	0f 84 86 00 00 00    	je     6775 <verify+0x325>
    66ef:	41 89 c4             	mov    %eax,%r12d
    66f2:	e9 8a fd ff ff       	jmp    6481 <verify+0x31>
    66f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6700:	0f 85 ba fe ff ff    	jne    65c0 <verify+0x170>
    6706:	e9 a8 fe ff ff       	jmp    65b3 <verify+0x163>
    670b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6710:	49 39 c1             	cmp    %rax,%r9
    6713:	7e 09                	jle    671e <verify+0x2ce>
    6715:	4c 39 df             	cmp    %r11,%rdi
    6718:	0f 8c 0a ff ff ff    	jl     6628 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    671e:	4c 39 df             	cmp    %r11,%rdi
    6721:	0f 8f 99 fe ff ff    	jg     65c0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6727:	49 39 c1             	cmp    %rax,%r9
    672a:	0f 8d f8 fe ff ff    	jge    6628 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6730:	48 39 f1             	cmp    %rsi,%rcx
    6733:	0f 85 87 fe ff ff    	jne    65c0 <verify+0x170>
    6739:	4c 39 c2             	cmp    %r8,%rdx
    673c:	0f 85 7e fe ff ff    	jne    65c0 <verify+0x170>
    6742:	4c 39 df             	cmp    %r11,%rdi
    6745:	0f 84 dd fe ff ff    	je     6628 <verify+0x1d8>
    674b:	e9 70 fe ff ff       	jmp    65c0 <verify+0x170>
    6750:	4c 39 c2             	cmp    %r8,%rdx
    6753:	0f 8c 5a fe ff ff    	jl     65b3 <verify+0x163>
    6759:	4c 39 df             	cmp    %r11,%rdi
    675c:	7e c9                	jle    6727 <verify+0x2d7>
    675e:	4c 39 c2             	cmp    %r8,%rdx
    6761:	0f 85 59 fe ff ff    	jne    65c0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6767:	49 39 c1             	cmp    %rax,%r9
    676a:	0f 8f 50 fe ff ff    	jg     65c0 <verify+0x170>
    6770:	e9 b3 fe ff ff       	jmp    6628 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    6775:	48 81 44 24 18 c0 00 00 00 	addq   $0xc0,0x18(%rsp)
    677e:	41 8d 46 01          	lea    0x1(%r14),%eax
    6782:	45 39 e6             	cmp    %r12d,%r14d
    6785:	74 08                	je     678f <verify+0x33f>
    6787:	41 89 c6             	mov    %eax,%r14d
    678a:	e9 ea fc ff ff       	jmp    6479 <verify+0x29>
}
    678f:	48 83 c4 58          	add    $0x58,%rsp
    6793:	31 c0                	xor    %eax,%eax
    6795:	5b                   	pop    %rbx
    6796:	5d                   	pop    %rbp
    6797:	41 5c                	pop    %r12
    6799:	41 5d                	pop    %r13
    679b:	41 5e                	pop    %r14
    679d:	41 5f                	pop    %r15
    679f:	c3                   	ret
    67a0:	31 c0                	xor    %eax,%eax
    67a2:	c3                   	ret

Disassembly of section .fini:

00000000000067a4 <_fini>:
    67a4:	f3 0f 1e fa          	endbr64
    67a8:	48 83 ec 08          	sub    $0x8,%rsp
    67ac:	48 83 c4 08          	add    $0x8,%rsp
    67b0:	c3                   	ret
