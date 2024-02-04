
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
    261d:	48 8d 05 ec 16 00 00 	lea    0x16ec(%rip),%rax        # 3d10 <barriered_reset>
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
    27ad:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    27b2:	e8 e9 fb ff ff       	call   23a0 <calloc@plt>
    27b7:	ba 04 00 00 00       	mov    $0x4,%edx
    27bc:	bf 01 00 00 00       	mov    $0x1,%edi
    27c1:	48 8d 35 93 4b 00 00 	lea    0x4b93(%rip),%rsi        # 735b <_IO_stdin_used+0x35b>
    27c8:	48 89 04 24          	mov    %rax,(%rsp)
    27cc:	31 c0                	xor    %eax,%eax
    27ce:	e8 7d fc ff ff       	call   2450 <__printf_chk@plt>
    27d3:	ba 08 00 00 00       	mov    $0x8,%edx
    27d8:	48 8d 35 92 4b 00 00 	lea    0x4b92(%rip),%rsi        # 7371 <_IO_stdin_used+0x371>
    27df:	31 c0                	xor    %eax,%eax
    27e1:	bf 01 00 00 00       	mov    $0x1,%edi
    27e6:	e8 65 fc ff ff       	call   2450 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    27eb:	be 10 00 00 00       	mov    $0x10,%esi
    27f0:	bf 08 00 00 00       	mov    $0x8,%edi
    27f5:	e8 a6 fb ff ff       	call   23a0 <calloc@plt>
    27fa:	4c 8b 34 24          	mov    (%rsp),%r14
    27fe:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2803:	48 89 c3             	mov    %rax,%rbx
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    2806:	48 8d a8 80 00 00 00 	lea    0x80(%rax),%rbp
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
    2839:	49 89 c4             	mov    %rax,%r12
      buffers[x].buffer[y].available = 0;
    283c:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2846:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2850:	e8 4b fb ff ff       	call   23a0 <calloc@plt>
    2855:	49 89 84 24 88 00 00 00 	mov    %rax,0x88(%r12)
  for (int x = 0 ; x < buffers_required; x++) {
    285d:	49 39 ed             	cmp    %rbp,%r13
    2860:	75 ae                	jne    2810 <main+0x220>
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
    2862:	c7 44 24 48 00 00 00 00 	movl   $0x0,0x48(%rsp)
  for (int x = 0 ; x < buffers_required; x++) {
    286a:	31 f6                	xor    %esi,%esi
    286c:	49 89 dc             	mov    %rbx,%r12
    286f:	4d 89 f3             	mov    %r14,%r11
  int curcpu = 0;
    2872:	c7 44 24 38 00 00 00 00 	movl   $0x0,0x38(%rsp)
  for (int x = 0 ; x < buffers_required; x++) {
    287a:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    287f:	b8 03 00 00 00       	mov    $0x3,%eax
    2884:	48 89 f3             	mov    %rsi,%rbx
    2887:	48 63 54 24 48       	movslq 0x48(%rsp),%rdx
    288c:	49 89 d9             	mov    %rbx,%r9
    288f:	48 89 7c 24 68       	mov    %rdi,0x68(%rsp)
    2894:	8d 2c 1b             	lea    (%rbx,%rbx,1),%ebp
    2897:	49 f7 d9             	neg    %r9
    289a:	4c 89 5c 24 30       	mov    %r11,0x30(%rsp)
    289f:	44 8d 78 fe          	lea    -0x2(%rax),%r15d
    28a3:	48 c1 e2 04          	shl    $0x4,%rdx
    28a7:	41 81 e1 80 01 00 00 	and    $0x180,%r9d
    28ae:	89 5c 24 78          	mov    %ebx,0x78(%rsp)
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    28b2:	49 8d 34 14          	lea    (%r12,%rdx,1),%rsi
    28b6:	4c 89 a4 24 80 00 00 00 	mov    %r12,0x80(%rsp)
    28be:	4f 8d 34 19          	lea    (%r9,%r11,1),%r14
    28c2:	48 89 74 24 28       	mov    %rsi,0x28(%rsp)
    28c7:	4d 89 f1             	mov    %r14,%r9
    28ca:	48 89 9c 24 88 00 00 00 	mov    %rbx,0x88(%rsp)
    28d2:	89 c3                	mov    %eax,%ebx
    28d4:	8b 54 24 78          	mov    0x78(%rsp),%edx
    28d8:	89 e9                	mov    %ebp,%ecx
    28da:	48 8d 35 67 4d 00 00 	lea    0x4d67(%rip),%rsi        # 7648 <_IO_stdin_used+0x648>
    28e1:	31 c0                	xor    %eax,%eax
    28e3:	bf 01 00 00 00       	mov    $0x1,%edi
    28e8:	4c 89 0c 24          	mov    %r9,(%rsp)
    28ec:	e8 5f fb ff ff       	call   2450 <__printf_chk@plt>
      int x = (k * threads_per_group) + d;
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    28f1:	be 08 00 00 00       	mov    $0x8,%esi
    28f6:	bf 02 00 00 00       	mov    $0x2,%edi
    28fb:	e8 a0 fa ff ff       	call   23a0 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2900:	be 80 00 00 00       	mov    $0x80,%esi
    2905:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    290a:	49 89 c4             	mov    %rax,%r12
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    290d:	e8 8e fa ff ff       	call   23a0 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2912:	40 f6 c5 01          	test   $0x1,%bpl
    2916:	4c 8b 0c 24          	mov    (%rsp),%r9
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    291a:	49 89 c5             	mov    %rax,%r13
      if (x % 2 == 1) {
    291d:	0f 84 98 06 00 00    	je     2fbb <main+0x9cb>
        other = abs(x - 1) % total_threads;
    2923:	8d 45 ff             	lea    -0x1(%rbp),%eax
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    2926:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
        my_thread_data[1] = &thread_data[x]; 
    292b:	4c 89 ca             	mov    %r9,%rdx
    292e:	41 b8 01 00 00 00    	mov    $0x1,%r8d
        other = abs(x - 1) % total_threads;
    2934:	49 89 c6             	mov    %rax,%r14
        my_thread_data[0] = &thread_data[other]; 
    2937:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    293b:	48 c1 e0 06          	shl    $0x6,%rax
    293f:	48 01 f8             	add    %rdi,%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2942:	49 8d 7c 24 08       	lea    0x8(%r12),%rdi
    2947:	48 89 7c 24 18       	mov    %rdi,0x18(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    294c:	48 8b 7c 24 68       	mov    0x68(%rsp),%rdi
        thread_data[x].thread_index = 1;
    2951:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2955:	44 89 f1             	mov    %r14d,%ecx
    2958:	48 8d 35 19 4d 00 00 	lea    0x4d19(%rip),%rsi        # 7678 <_IO_stdin_used+0x678>
    295f:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
    2964:	89 ea                	mov    %ebp,%edx
        thread_data[x].protected_state = &protected_state[k];
    2966:	49 89 79 48          	mov    %rdi,0x48(%r9)
    296a:	bf 01 00 00 00       	mov    $0x1,%edi
    296f:	49 89 04 24          	mov    %rax,(%r12)
    2973:	31 c0                	xor    %eax,%eax
    2975:	4c 89 0c 24          	mov    %r9,(%rsp)
    2979:	e8 d2 fa ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].other = other;
    297e:	4c 8b 0c 24          	mov    (%rsp),%r9
    2982:	8b 4c 24 38          	mov    0x38(%rsp),%ecx
    2986:	31 c0                	xor    %eax,%eax
    2988:	89 ea                	mov    %ebp,%edx
    298a:	48 8d 35 17 4d 00 00 	lea    0x4d17(%rip),%rsi        # 76a8 <_IO_stdin_used+0x6a8>
    2991:	bf 01 00 00 00       	mov    $0x1,%edi
    2996:	45 89 b1 b8 00 00 00 	mov    %r14d,0xb8(%r9)
    299d:	e8 ae fa ff ff       	call   2450 <__printf_chk@plt>
        if (x < thread_count) {
    29a2:	83 fd 01             	cmp    $0x1,%ebp
    29a5:	4c 8b 0c 24          	mov    (%rsp),%r9
    29a9:	0f 8f 55 07 00 00    	jg     3104 <main+0xb14>
          CPU_SET(curcpu, sendercpu);
    29af:	48 63 44 24 38       	movslq 0x38(%rsp),%rax
    29b4:	48 89 c7             	mov    %rax,%rdi
    29b7:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    29bd:	77 13                	ja     29d2 <main+0x3e2>
    29bf:	48 c1 e8 06          	shr    $0x6,%rax
    29c3:	ba 01 00 00 00       	mov    $0x1,%edx
    29c8:	89 f9                	mov    %edi,%ecx
    29ca:	48 d3 e2             	shl    %cl,%rdx
    29cd:	49 09 54 c5 00       	or     %rdx,0x0(%r13,%rax,8)
          curcpu += 2;
    29d2:	83 44 24 38 02       	addl   $0x2,0x38(%rsp)
      thread_data[x].all_threads = thread_data;
    29d7:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    29dc:	4d 89 61 18          	mov    %r12,0x18(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    29e0:	be 10 00 00 00       	mov    $0x10,%esi
    29e5:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].cpu_set = sendercpu;
    29ea:	4d 89 a9 b0 00 00 00 	mov    %r13,0xb0(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    29f1:	45 31 e4             	xor    %r12d,%r12d
      thread_data[x].all_threads = thread_data;
    29f4:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].thread_count = 2;
    29f8:	48 8b 05 a1 51 00 00 	mov    0x51a1(%rip),%rax        # 7ba0 <_IO_stdin_used+0xba0>
      thread_data[x].kind = KERNEL_THREAD;
    29ff:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].real_thread_index = x;
    2a06:	41 89 69 08          	mov    %ebp,0x8(%r9)
      thread_data[x].thread_count = 2;
    2a0a:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].task_count = total_barrier_count;
    2a0e:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
    2a16:	4c 89 0c 24          	mov    %r9,(%rsp)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a1a:	e8 81 f9 ff ff       	call   23a0 <calloc@plt>
    2a1f:	4c 8b 0c 24          	mov    (%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a23:	be 10 00 00 00       	mov    $0x10,%esi
    2a28:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a2d:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a31:	e8 6a f9 ff ff       	call   23a0 <calloc@plt>
    2a36:	4c 8b 0c 24          	mov    (%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a3a:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2a3f:	66 0f 6f 3d 29 51 00 00 	movdqa 0x5129(%rip),%xmm7        # 7b70 <_IO_stdin_used+0xb70>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a47:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a4c:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2a50:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a58:	e8 43 f9 ff ff       	call   23a0 <calloc@plt>
    2a5d:	4c 8b 0c 24          	mov    (%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a61:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_timestamp_count = 0;
    2a66:	66 0f 6f 1d 02 51 00 00 	movdqa 0x5102(%rip),%xmm3        # 7b70 <_IO_stdin_used+0xb70>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a6e:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a73:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2a7a:	41 0f 11 99 98 00 00 00 	movups %xmm3,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a82:	e8 19 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks = barriers;
    2a87:	4c 8b 0c 24          	mov    (%rsp),%r9
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a8b:	89 5c 24 70          	mov    %ebx,0x70(%rsp)
    2a8f:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks = barriers;
    2a92:	49 89 41 38          	mov    %rax,0x38(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2a96:	4d 89 cd             	mov    %r9,%r13
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a99:	49 63 c4             	movslq %r12d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2a9c:	be 28 00 00 00       	mov    $0x28,%esi
    2aa1:	bf 04 00 00 00       	mov    $0x4,%edi
          thread_data[x].tasks[y].protected = do_protected_write; 
    2aa6:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2aab:	48 c1 e0 09          	shl    $0x9,%rax
    2aaf:	4c 8d 34 02          	lea    (%rdx,%rax,1),%r14
    2ab3:	48 89 04 24          	mov    %rax,(%rsp)
    2ab7:	48 8d 05 12 12 00 00 	lea    0x1212(%rip),%rax        # 3cd0 <do_protected_write>
    2abe:	49 89 86 20 01 00 00 	mov    %rax,0x120(%r14)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2ac5:	e8 d6 f8 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2aca:	49 89 86 70 01 00 00 	mov    %rax,0x170(%r14)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2ad1:	48 89 c3             	mov    %rax,%rbx
            if ( b == x || b == x + 1) {
    2ad4:	85 ed                	test   %ebp,%ebp
    2ad6:	0f 84 a6 03 00 00    	je     2e82 <main+0x892>
    2adc:	83 fd 01             	cmp    $0x1,%ebp
    2adf:	0f 84 fc 04 00 00    	je     2fe1 <main+0x9f1>
    2ae5:	83 fd 02             	cmp    $0x2,%ebp
    2ae8:	0f 84 23 06 00 00    	je     3111 <main+0xb21>
    2aee:	ba 03 00 00 00       	mov    $0x3,%edx
    2af3:	48 8d 35 91 48 00 00 	lea    0x4891(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
    2afa:	bf 01 00 00 00       	mov    $0x1,%edi
    2aff:	31 c0                	xor    %eax,%eax
    2b01:	e8 4a f9 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b06:	be 08 00 00 00       	mov    $0x8,%esi
    2b0b:	bf 01 00 00 00       	mov    $0x1,%edi
    2b10:	e8 8b f8 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b15:	be 08 00 00 00       	mov    $0x8,%esi
    2b1a:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b1f:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b24:	e8 77 f8 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2b29:	be 80 01 00 00       	mov    $0x180,%esi
    2b2e:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b33:	49 89 c6             	mov    %rax,%r14
              struct Data *data = calloc(2, sizeof(struct Data));
    2b36:	e8 65 f8 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    2b3b:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
              data[0].messages_count = 0;
    2b40:	66 0f 6f 25 38 50 00 00 	movdqa 0x5038(%rip),%xmm4        # 7b80 <_IO_stdin_used+0xb80>
              mailboxes[b].kind = MAILBOX_FRIEND;
    2b48:	c7 83 98 00 00 00 01 00 00 00 	movl   $0x1,0x98(%rbx)
              mailboxes[b].higher = &data[1];
    2b52:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    2b59:	48 89 43 78          	mov    %rax,0x78(%rbx)
              mailboxes[b].higher = &data[1];
    2b5d:	48 89 b3 80 00 00 00 	mov    %rsi,0x80(%rbx)
              data[0].messages = messages;
    2b64:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    2b67:	4c 89 b0 80 01 00 00 	mov    %r14,0x180(%rax)
              data[0].messages_count = 0;
    2b6e:	0f 29 a0 80 00 00 00 	movaps %xmm4,0x80(%rax)
              data[1].messages_count = 0;
    2b75:	0f 29 a0 00 02 00 00 	movaps %xmm4,0x200(%rax)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2b7c:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    2b81:	45 31 f6             	xor    %r14d,%r14d
    2b84:	45 89 fd             	mov    %r15d,%r13d
    2b87:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
    2b8c:	41 89 ec             	mov    %ebp,%r12d
            if (b == x || b == x + 1) { continue; }
    2b8f:	45 39 e6             	cmp    %r12d,%r14d
    2b92:	0f 84 9b 00 00 00    	je     2c33 <main+0x643>
    2b98:	45 39 ee             	cmp    %r13d,%r14d
    2b9b:	0f 84 92 00 00 00    	je     2c33 <main+0x643>
    2ba1:	44 89 f2             	mov    %r14d,%edx
    2ba4:	48 8d 35 fc 47 00 00 	lea    0x47fc(%rip),%rsi        # 73a7 <_IO_stdin_used+0x3a7>
    2bab:	bf 01 00 00 00       	mov    $0x1,%edi
    2bb0:	31 c0                	xor    %eax,%eax
    2bb2:	e8 99 f8 ff ff       	call   2450 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2bb7:	be 08 00 00 00       	mov    $0x8,%esi
    2bbc:	bf 01 00 00 00       	mov    $0x1,%edi
    2bc1:	e8 da f7 ff ff       	call   23a0 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2bc6:	be 08 00 00 00       	mov    $0x8,%esi
    2bcb:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2bd0:	49 89 c7             	mov    %rax,%r15
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2bd3:	e8 c8 f7 ff ff       	call   23a0 <calloc@plt>
            struct Data *data = calloc(2, sizeof(struct Data));
    2bd8:	be 80 01 00 00       	mov    $0x180,%esi
    2bdd:	bf 02 00 00 00       	mov    $0x2,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2be2:	48 89 c5             	mov    %rax,%rbp
            struct Data *data = calloc(2, sizeof(struct Data));
    2be5:	e8 b6 f7 ff ff       	call   23a0 <calloc@plt>
            data[0].messages_count = 0;
    2bea:	66 0f 6f 05 8e 4f 00 00 	movdqa 0x4f8e(%rip),%xmm0        # 7b80 <_IO_stdin_used+0xb80>
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2bf2:	c7 43 20 02 00 00 00 	movl   $0x2,0x20(%rbx)
            mailboxes[b].higher = &data[1];
    2bf9:	48 8d 90 80 01 00 00 	lea    0x180(%rax),%rdx
            mailboxes[b].lower = &data[0];
    2c00:	48 89 03             	mov    %rax,(%rbx)
            mailboxes[b].higher = &data[1];
    2c03:	48 89 53 08          	mov    %rdx,0x8(%rbx)
            data[0].available = 0;
    2c07:	c7 80 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rax)
            data[0].messages = messages;
    2c11:	4c 89 38             	mov    %r15,(%rax)
            data[1].messages = messages2;
    2c14:	48 89 a8 80 01 00 00 	mov    %rbp,0x180(%rax)
            data[1].available = 0;
    2c1b:	c7 80 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rax)
            data[0].messages_count = 0;
    2c25:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
            data[1].messages_count = 0;
    2c2c:	0f 29 80 00 02 00 00 	movaps %xmm0,0x200(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c33:	41 83 c6 01          	add    $0x1,%r14d
    2c37:	48 83 c3 28          	add    $0x28,%rbx
    2c3b:	41 83 fe 04          	cmp    $0x4,%r14d
    2c3f:	0f 85 4a ff ff ff    	jne    2b8f <main+0x59f>
          char *message = malloc(sizeof(char) * 256);
    2c45:	be 01 00 00 00       	mov    $0x1,%esi
    2c4a:	bf 00 01 00 00       	mov    $0x100,%edi
    2c4f:	44 89 e5             	mov    %r12d,%ebp
    2c52:	45 89 ef             	mov    %r13d,%r15d
    2c55:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    2c5a:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    2c5f:	e8 3c f7 ff ff       	call   23a0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2c64:	bf 18 00 00 00       	mov    $0x18,%edi
          char *message = malloc(sizeof(char) * 256);
    2c69:	48 89 c3             	mov    %rax,%rbx
          struct Message *messaged = malloc(sizeof(struct Message));
    2c6c:	e8 9f f7 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2c71:	48 89 df             	mov    %rbx,%rdi
    2c74:	45 89 e1             	mov    %r12d,%r9d
    2c77:	41 89 e8             	mov    %ebp,%r8d
    2c7a:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2c7f:	48 8d 0d 42 4a 00 00 	lea    0x4a42(%rip),%rcx        # 76c8 <_IO_stdin_used+0x6c8>
    2c86:	ba 00 01 00 00       	mov    $0x100,%edx
    2c8b:	31 c0                	xor    %eax,%eax
    2c8d:	be 01 00 00 00       	mov    $0x1,%esi
    2c92:	e8 89 f8 ff ff       	call   2520 <__sprintf_chk@plt>
          messaged->message = message;
    2c97:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
          messaged->task_index = y;
    2c9c:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2ca1:	be 20 00 00 00       	mov    $0x20,%esi
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2ca6:	49 8b 55 38          	mov    0x38(%r13),%rdx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2caa:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->task_index = y;
    2caf:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].thread_index;
    2cb3:	49 63 45 04          	movslq 0x4(%r13),%rax
          messaged->message = message;
    2cb7:	49 89 1a             	mov    %rbx,(%r10)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2cba:	48 8b 1c 24          	mov    (%rsp),%rbx
          messaged->thread_index = thread_data[x].thread_index;
    2cbe:	49 89 42 08          	mov    %rax,0x8(%r10)
    2cc2:	49 89 c6             	mov    %rax,%r14
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2cc5:	41 8d 44 24 01       	lea    0x1(%r12),%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2cca:	48 01 d3             	add    %rdx,%rbx
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2ccd:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2cd0:	48 89 14 24          	mov    %rdx,(%rsp)
    2cd4:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2cda:	89 83 90 01 00 00    	mov    %eax,0x190(%rbx)
          thread_data[x].tasks[y].message = messaged;
    2ce0:	4c 89 93 88 01 00 00 	mov    %r10,0x188(%rbx)
          thread_data[x].tasks[y].sending = 1;
    2ce7:	c7 83 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rbx)
          thread_data[x].tasks[y].snapshot_count = 99;
    2cf1:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2cfc:	e8 9f f6 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2d01:	48 8b 14 24          	mov    (%rsp),%rdx
          thread_data[x].tasks[y].current_snapshot = 0;
    2d05:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2d10:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2d17:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    2d1c:	48 8b 00             	mov    (%rax),%rax
    2d1f:	8b 48 04             	mov    0x4(%rax),%ecx
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2d22:	4c 39 e8             	cmp    %r13,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2d25:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2d2c:	89 8b 30 01 00 00    	mov    %ecx,0x130(%rbx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2d32:	0f 85 98 0e 00 00    	jne    3bd0 <main+0x15e0>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2d38:	66 0f 6f 15 50 4e 00 00 	movdqa 0x4e50(%rip),%xmm2        # 7b90 <_IO_stdin_used+0xb90>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2d40:	44 89 63 04          	mov    %r12d,0x4(%rbx)
          thread_data[x].tasks[y].available = 1;
    2d44:	48 8b 05 5d 4e 00 00 	mov    0x4e5d(%rip),%rax        # 7ba8 <_IO_stdin_used+0xba8>
          thread_data[x].tasks[y].arrived = 0;
    2d4b:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
          thread_data[x].tasks[y].worker_count = thread_count;
    2d55:	c7 83 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rbx)
          thread_data[x].tasks[y].available = 1;
    2d5f:	48 89 83 44 01 00 00 	mov    %rax,0x144(%rbx)
          thread_data[x].tasks[y].thread_count = 2;
    2d66:	0f 11 93 34 01 00 00 	movups %xmm2,0x134(%rbx)
          if (y == barrier_count - 1) {
    2d6d:	41 83 fc 01          	cmp    $0x1,%r12d
    2d71:	0f 84 35 02 00 00    	je     2fac <main+0x9bc>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2d77:	45 85 e4             	test   %r12d,%r12d
    2d7a:	0f 84 13 02 00 00    	je     2f93 <main+0x9a3>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    2d80:	4d 89 e9             	mov    %r13,%r9
    2d83:	48 8d 05 b6 32 00 00 	lea    0x32b6(%rip),%rax        # 6040 <barriered_work>
    2d8a:	49 89 d5             	mov    %rdx,%r13
    2d8d:	48 89 da             	mov    %rbx,%rdx
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2d90:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].buffers_count = buffers_per_thread;
    2d95:	4c 89 0c 24          	mov    %r9,(%rsp)
               thread_data[x].tasks[y].run = barriered_work; 
    2d99:	8b 5c 24 70          	mov    0x70(%rsp),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    2d9d:	83 c5 01             	add    $0x1,%ebp
               thread_data[x].tasks[y].run = barriered_work; 
    2da0:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2da7:	be 08 00 00 00       	mov    $0x8,%esi
    for (int d = 0 ; d < threads_per_group ; d++) {
    2dac:	41 83 c7 01          	add    $0x1,%r15d
        thread_data[x].buffers_count = buffers_per_thread;
    2db0:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2dbb:	e8 e0 f5 ff ff       	call   23a0 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2dc0:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2dc5:	4c 8b 0c 24          	mov    (%rsp),%r9
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2dc9:	66 0f 6f 74 24 50    	movdqa 0x50(%rsp),%xmm6
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2dcf:	83 44 24 48 01       	addl   $0x1,0x48(%rsp)
    2dd4:	48 89 38             	mov    %rdi,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2dd7:	48 83 c7 10          	add    $0x10,%rdi
    2ddb:	49 81 c1 c0 00 00 00 	add    $0xc0,%r9
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2de2:	49 89 41 90          	mov    %rax,-0x70(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2de6:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    2deb:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2df0:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2df3:	41 0f 11 b5 18 05 00 00 	movups %xmm6,0x518(%r13)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    2dfb:	41 c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r13)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2e06:	49 89 85 28 05 00 00 	mov    %rax,0x528(%r13)
        thread_data[x].tasks[barrier_count].available = 1; 
    2e0d:	48 8b 05 94 4d 00 00 	mov    0x4d94(%rip),%rax        # 7ba8 <_IO_stdin_used+0xba8>
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2e14:	41 c7 85 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r13)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    2e1f:	41 c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r13)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2e2a:	45 89 b5 30 05 00 00 	mov    %r14d,0x530(%r13)
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2e31:	41 c7 85 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r13)
        thread_data[x].tasks[barrier_count].available = 1; 
    2e3c:	49 89 85 44 05 00 00 	mov    %rax,0x544(%r13)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2e43:	44 39 fb             	cmp    %r15d,%ebx
    2e46:	0f 85 88 fa ff ff    	jne    28d4 <main+0x2e4>
    2e4c:	89 d8                	mov    %ebx,%eax
    2e4e:	48 8b 7c 24 68       	mov    0x68(%rsp),%rdi
    2e53:	48 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%rbx
  for (int k = 0 ; k < group_count ; k++) {
    2e5b:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    2e60:	4c 8b a4 24 80 00 00 00 	mov    0x80(%rsp),%r12
    2e68:	83 c0 02             	add    $0x2,%eax
    2e6b:	48 83 c7 18          	add    $0x18,%rdi
    2e6f:	48 85 db             	test   %rbx,%rbx
    2e72:	0f 85 2d 03 00 00    	jne    31a5 <main+0xbb5>
    2e78:	bb 01 00 00 00       	mov    $0x1,%ebx
    2e7d:	e9 05 fa ff ff       	jmp    2887 <main+0x297>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2e82:	31 d2                	xor    %edx,%edx
    2e84:	48 8d 35 00 45 00 00 	lea    0x4500(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
    2e8b:	bf 01 00 00 00       	mov    $0x1,%edi
    2e90:	31 c0                	xor    %eax,%eax
    2e92:	e8 b9 f5 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e97:	be 08 00 00 00       	mov    $0x8,%esi
    2e9c:	bf 01 00 00 00       	mov    $0x1,%edi
    2ea1:	e8 fa f4 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ea6:	be 08 00 00 00       	mov    $0x8,%esi
    2eab:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2eb0:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2eb5:	e8 e6 f4 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2eba:	be 80 01 00 00       	mov    $0x180,%esi
    2ebf:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ec4:	49 89 c6             	mov    %rax,%r14
              struct Data *data = calloc(2, sizeof(struct Data));
    2ec7:	e8 d4 f4 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    2ecc:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2ed1:	ba 01 00 00 00       	mov    $0x1,%edx
              data[0].messages_count = 0;
    2ed6:	66 0f 6f 25 a2 4c 00 00 	movdqa 0x4ca2(%rip),%xmm4        # 7b80 <_IO_stdin_used+0xb80>
              mailboxes[b].higher = &data[1];
    2ede:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    2ee5:	48 89 03             	mov    %rax,(%rbx)
    2ee8:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages = messages;
    2eed:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    2ef0:	4c 89 b0 80 01 00 00 	mov    %r14,0x180(%rax)
              mailboxes[b].higher = &data[1];
    2ef7:	48 89 73 08          	mov    %rsi,0x8(%rbx)
    2efb:	48 8d 35 89 44 00 00 	lea    0x4489(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
              mailboxes[b].kind = MAILBOX_FRIEND;
    2f02:	c7 43 20 01 00 00 00 	movl   $0x1,0x20(%rbx)
              data[0].messages_count = 0;
    2f09:	0f 29 a0 80 00 00 00 	movaps %xmm4,0x80(%rax)
              data[1].messages_count = 0;
    2f10:	0f 29 a0 00 02 00 00 	movaps %xmm4,0x200(%rax)
    2f17:	31 c0                	xor    %eax,%eax
    2f19:	e8 32 f5 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f1e:	be 08 00 00 00       	mov    $0x8,%esi
    2f23:	bf 01 00 00 00       	mov    $0x1,%edi
    2f28:	e8 73 f4 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f2d:	be 08 00 00 00       	mov    $0x8,%esi
    2f32:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f37:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f3c:	e8 5f f4 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2f41:	be 80 01 00 00       	mov    $0x180,%esi
    2f46:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f4b:	49 89 c6             	mov    %rax,%r14
              struct Data *data = calloc(2, sizeof(struct Data));
    2f4e:	e8 4d f4 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    2f53:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
              data[0].messages_count = 0;
    2f58:	66 0f 6f 35 20 4c 00 00 	movdqa 0x4c20(%rip),%xmm6        # 7b80 <_IO_stdin_used+0xb80>
              mailboxes[b].kind = MAILBOX_FRIEND;
    2f60:	c7 43 48 01 00 00 00 	movl   $0x1,0x48(%rbx)
              mailboxes[b].higher = &data[1];
    2f67:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    2f6e:	48 89 43 28          	mov    %rax,0x28(%rbx)
              mailboxes[b].higher = &data[1];
    2f72:	48 89 73 30          	mov    %rsi,0x30(%rbx)
              data[0].messages = messages;
    2f76:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    2f79:	4c 89 b0 80 01 00 00 	mov    %r14,0x180(%rax)
              data[0].messages_count = 0;
    2f80:	0f 29 b0 80 00 00 00 	movaps %xmm6,0x80(%rax)
              data[1].messages_count = 0;
    2f87:	0f 29 b0 00 02 00 00 	movaps %xmm6,0x200(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2f8e:	e9 e9 fb ff ff       	jmp    2b7c <main+0x58c>
    2f93:	48 8d 05 c6 32 00 00 	lea    0x32c6(%rip),%rax        # 6260 <barriered_work_ingest_andwork>
    2f9a:	41 bc 01 00 00 00    	mov    $0x1,%r12d
            thread_data[x].tasks[y].run = barriered_work; 
    2fa0:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2fa7:	e9 ed fa ff ff       	jmp    2a99 <main+0x4a9>
    2fac:	48 8d 05 8d 30 00 00 	lea    0x308d(%rip),%rax        # 6040 <barriered_work>
    2fb3:	41 bc 02 00 00 00    	mov    $0x2,%r12d
    2fb9:	eb e5                	jmp    2fa0 <main+0x9b0>
        my_thread_data[1] = &thread_data[other]; 
    2fbb:	49 63 c7             	movslq %r15d,%rax
    2fbe:	4c 89 64 24 18       	mov    %r12,0x18(%rsp)
        other = (x + 1) % total_threads;
    2fc3:	45 89 fe             	mov    %r15d,%r14d
        my_thread_data[1] = &thread_data[other]; 
    2fc6:	45 31 c0             	xor    %r8d,%r8d
    2fc9:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
    2fcd:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    2fd2:	48 c1 e2 06          	shl    $0x6,%rdx
    2fd6:	48 01 c2             	add    %rax,%rdx
        my_thread_data[0] = &thread_data[x]; 
    2fd9:	4c 89 c8             	mov    %r9,%rax
    2fdc:	e9 6b f9 ff ff       	jmp    294c <main+0x35c>
    2fe1:	ba 01 00 00 00       	mov    $0x1,%edx
    2fe6:	48 8d 35 9e 43 00 00 	lea    0x439e(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
    2fed:	bf 01 00 00 00       	mov    $0x1,%edi
    2ff2:	31 c0                	xor    %eax,%eax
    2ff4:	e8 57 f4 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ff9:	be 08 00 00 00       	mov    $0x8,%esi
    2ffe:	bf 01 00 00 00       	mov    $0x1,%edi
    3003:	e8 98 f3 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3008:	be 08 00 00 00       	mov    $0x8,%esi
    300d:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3012:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3017:	e8 84 f3 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    301c:	be 80 01 00 00       	mov    $0x180,%esi
    3021:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3026:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    302b:	e8 70 f3 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    3030:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
              data[1].messages = messages2;
    3035:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    303a:	c7 43 48 01 00 00 00 	movl   $0x1,0x48(%rbx)
              mailboxes[b].higher = &data[1];
    3041:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    3048:	48 89 43 28          	mov    %rax,0x28(%rbx)
    304c:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages_count = 0;
    3051:	66 0f 6f 25 27 4b 00 00 	movdqa 0x4b27(%rip),%xmm4        # 7b80 <_IO_stdin_used+0xb80>
              data[0].messages = messages;
    3059:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    305c:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
    3063:	ba 02 00 00 00       	mov    $0x2,%edx
              mailboxes[b].higher = &data[1];
    3068:	48 89 73 30          	mov    %rsi,0x30(%rbx)
    306c:	48 8d 35 18 43 00 00 	lea    0x4318(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
              data[0].messages_count = 0;
    3073:	0f 29 a0 80 00 00 00 	movaps %xmm4,0x80(%rax)
              data[1].messages_count = 0;
    307a:	0f 29 a0 00 02 00 00 	movaps %xmm4,0x200(%rax)
    3081:	31 c0                	xor    %eax,%eax
    3083:	e8 c8 f3 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3088:	be 08 00 00 00       	mov    $0x8,%esi
    308d:	bf 01 00 00 00       	mov    $0x1,%edi
    3092:	e8 09 f3 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3097:	be 08 00 00 00       	mov    $0x8,%esi
    309c:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    30a1:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    30a6:	e8 f5 f2 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    30ab:	be 80 01 00 00       	mov    $0x180,%esi
    30b0:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    30b5:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    30ba:	e8 e1 f2 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    30bf:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
              data[1].messages = messages2;
    30c4:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    30c9:	c7 43 70 01 00 00 00 	movl   $0x1,0x70(%rbx)
              data[0].messages_count = 0;
    30d0:	66 0f 6f 35 a8 4a 00 00 	movdqa 0x4aa8(%rip),%xmm6        # 7b80 <_IO_stdin_used+0xb80>
              mailboxes[b].higher = &data[1];
    30d8:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    30df:	48 89 43 50          	mov    %rax,0x50(%rbx)
              mailboxes[b].higher = &data[1];
    30e3:	48 89 73 58          	mov    %rsi,0x58(%rbx)
              data[0].messages = messages;
    30e7:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    30ea:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
              data[0].messages_count = 0;
    30f1:	0f 29 b0 80 00 00 00 	movaps %xmm6,0x80(%rax)
              data[1].messages_count = 0;
    30f8:	0f 29 b0 00 02 00 00 	movaps %xmm6,0x200(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    30ff:	e9 78 fa ff ff       	jmp    2b7c <main+0x58c>
            CPU_SET(j, sendercpu);
    3104:	49 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%r13)
          for (int j = 0 ; j < cores ; j++) {
    310c:	e9 c6 f8 ff ff       	jmp    29d7 <main+0x3e7>
    3111:	ba 02 00 00 00       	mov    $0x2,%edx
    3116:	48 8d 35 6e 42 00 00 	lea    0x426e(%rip),%rsi        # 738b <_IO_stdin_used+0x38b>
    311d:	bf 01 00 00 00       	mov    $0x1,%edi
    3122:	31 c0                	xor    %eax,%eax
    3124:	e8 27 f3 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3129:	be 08 00 00 00       	mov    $0x8,%esi
    312e:	bf 01 00 00 00       	mov    $0x1,%edi
    3133:	e8 68 f2 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3138:	be 08 00 00 00       	mov    $0x8,%esi
    313d:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3142:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3147:	e8 54 f2 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    314c:	be 80 01 00 00       	mov    $0x180,%esi
    3151:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3156:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    315b:	e8 40 f2 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    3160:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
              data[0].messages_count = 0;
    3165:	66 0f 6f 3d 13 4a 00 00 	movdqa 0x4a13(%rip),%xmm7        # 7b80 <_IO_stdin_used+0xb80>
              mailboxes[b].kind = MAILBOX_FRIEND;
    316d:	c7 43 70 01 00 00 00 	movl   $0x1,0x70(%rbx)
              data[1].messages = messages2;
    3174:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
              mailboxes[b].higher = &data[1];
    3179:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    3180:	48 89 43 50          	mov    %rax,0x50(%rbx)
              mailboxes[b].higher = &data[1];
    3184:	48 89 73 58          	mov    %rsi,0x58(%rbx)
              data[0].messages = messages;
    3188:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    318b:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
              data[0].messages_count = 0;
    3192:	0f 29 b8 80 00 00 00 	movaps %xmm7,0x80(%rax)
              data[1].messages_count = 0;
    3199:	0f 29 b8 00 02 00 00 	movaps %xmm7,0x200(%rax)
            if ( b == x || b == x + 1) {
    31a0:	e9 49 f9 ff ff       	jmp    2aee <main+0x4fe>
    31a5:	ba 05 00 00 00       	mov    $0x5,%edx
    31aa:	bf 01 00 00 00       	mov    $0x1,%edi
    31af:	31 c0                	xor    %eax,%eax
    31b1:	4c 89 1c 24          	mov    %r11,(%rsp)
    31b5:	48 8d 35 09 42 00 00 	lea    0x4209(%rip),%rsi        # 73c5 <_IO_stdin_used+0x3c5>
    31bc:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
    31c1:	e8 8a f2 ff ff       	call   2450 <__printf_chk@plt>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    31c6:	be 08 00 00 00       	mov    $0x8,%esi
    31cb:	bf 02 00 00 00       	mov    $0x2,%edi
    31d0:	e8 cb f1 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    31d5:	4c 8b 1c 24          	mov    (%rsp),%r11
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    31d9:	be 38 00 00 00       	mov    $0x38,%esi
    31de:	bf 08 00 00 00       	mov    $0x8,%edi
    my_thread_data[0] = &thread_data[x]; 
    31e3:	4d 8d ab c0 03 00 00 	lea    0x3c0(%r11),%r13
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    31ea:	4c 89 58 08          	mov    %r11,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    31ee:	4d 8d a3 c0 00 00 00 	lea    0xc0(%r11),%r12
    thread_data[x].threads = my_thread_data;
    31f5:	49 89 83 d8 03 00 00 	mov    %rax,0x3d8(%r11)
    my_thread_data[0] = &thread_data[x]; 
    31fc:	4c 89 28             	mov    %r13,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    31ff:	49 8b 43 38          	mov    0x38(%r11),%rax
    thread_data[x].thread_count = 2;
    3203:	41 c7 83 e8 03 00 00 02 00 00 00 	movl   $0x2,0x3e8(%r11)
    thread_data[x].thread_index = 0;
    320e:	41 c7 83 c4 03 00 00 00 00 00 00 	movl   $0x0,0x3c4(%r11)
    thread_data[x].task_count = total_barrier_count;
    3219:	41 c7 83 00 04 00 00 03 00 00 00 	movl   $0x3,0x400(%r11)
    thread_data[n].tasks[0].scheduled = 1;
    3224:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    322e:	49 8b 83 f8 00 00 00 	mov    0xf8(%r11),%rax
    3235:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    323a:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3244:	e8 57 f1 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3249:	be 38 00 00 00       	mov    $0x38,%esi
    324e:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3253:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3256:	e8 45 f1 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    325b:	be 38 00 00 00       	mov    $0x38,%esi
    3260:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3265:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3268:	e8 33 f1 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    326d:	be 38 00 00 00       	mov    $0x38,%esi
    3272:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3277:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    327b:	e8 20 f1 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3280:	be 08 00 00 00       	mov    $0x8,%esi
    3285:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    328a:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    328f:	e8 0c f1 ff ff       	call   23a0 <calloc@plt>


  int timer_threadi = group_count * thread_count;
  thread_data[timer_threadi].type = TIMER;
    3294:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3299:	be 08 00 00 00       	mov    $0x8,%esi
    329e:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    32a3:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    32a6:	48 8b 05 03 49 00 00 	mov    0x4903(%rip),%rax        # 7bb0 <_IO_stdin_used+0xbb0>
  thread_data[timer_threadi].type = TIMER;
    32ad:	41 c7 83 0c 03 00 00 00 00 00 00 	movl   $0x0,0x30c(%r11)
  thread_data[timer_threadi].task_count = total_barrier_count;
    32b8:	49 89 83 40 03 00 00 	mov    %rax,0x340(%r11)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    32bf:	e8 dc f0 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    32c4:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    32c9:	bf 01 00 00 00       	mov    $0x1,%edi
    32ce:	48 8d 35 ff 40 00 00 	lea    0x40ff(%rip),%rsi        # 73d4 <_IO_stdin_used+0x3d4>
    32d5:	4c 89 60 08          	mov    %r12,0x8(%rax)
    32d9:	49 8d 93 80 01 00 00 	lea    0x180(%r11),%rdx
    32e0:	49 8d 8b 00 03 00 00 	lea    0x300(%r11),%rcx
    32e7:	4c 89 18             	mov    %r11,(%rax)
    32ea:	48 89 50 10          	mov    %rdx,0x10(%rax)
    32ee:	49 8d 93 40 02 00 00 	lea    0x240(%r11),%rdx
    32f5:	4d 8d b3 80 04 00 00 	lea    0x480(%r11),%r14
    32fc:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3300:	49 8d 93 40 05 00 00 	lea    0x540(%r11),%rdx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3307:	49 89 83 18 03 00 00 	mov    %rax,0x318(%r11)
    my_thread_data[n] = &thread_data[n]; 
    330e:	48 89 48 20          	mov    %rcx,0x20(%rax)
    3312:	4c 89 70 30          	mov    %r14,0x30(%rax)
    3316:	48 89 50 38          	mov    %rdx,0x38(%rax)
    331a:	ba 04 00 00 00       	mov    $0x4,%edx
    331f:	4c 89 68 28          	mov    %r13,0x28(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3323:	48 8b 05 8e 48 00 00 	mov    0x488e(%rip),%rax        # 7bb8 <_IO_stdin_used+0xbb8>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    332a:	41 c7 83 30 03 00 00 04 00 00 00 	movl   $0x4,0x330(%r11)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3335:	49 89 83 28 03 00 00 	mov    %rax,0x328(%r11)
    333c:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    333e:	41 c7 83 04 03 00 00 00 00 00 00 	movl   $0x0,0x304(%r11)
    my_thread_data[n] = &thread_data[n]; 
    3349:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    334e:	e8 fd f0 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3353:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3358:	48 8d 15 31 0b 00 00 	lea    0xb31(%rip),%rdx        # 3e90 <timer_thread>
    335f:	48 8d b5 e0 00 00 00 	lea    0xe0(%rbp),%rsi
    3366:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
    336a:	e8 01 f1 ff ff       	call   2470 <pthread_create@plt>
    336f:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
  for (int k = 0 ; k < group_count ; k++) {
    3374:	45 31 c9             	xor    %r9d,%r9d
    3377:	48 89 d9             	mov    %rbx,%rcx
    337a:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    337f:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    3385:	4c 89 f8             	mov    %r15,%rax
    3388:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    338d:	4c 89 da             	mov    %r11,%rdx
    3390:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    3395:	45 89 cc             	mov    %r9d,%r12d
    3398:	4c 89 74 24 28       	mov    %r14,0x28(%rsp)
    339d:	45 89 d6             	mov    %r10d,%r14d
    for (int d = 0 ; d < threads_per_group ; d++) {
    33a0:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    33a5:	43 8d 1c 24          	lea    (%r12,%r12,1),%ebx
  int curcpu = 0;
    33a9:	49 89 c5             	mov    %rax,%r13
    33ac:	49 89 cf             	mov    %rcx,%r15
    33af:	48 89 4c 24 38       	mov    %rcx,0x38(%rsp)
    33b4:	48 89 d5             	mov    %rdx,%rbp
    33b7:	48 89 54 24 48       	mov    %rdx,0x48(%rsp)
    33bc:	4c 89 5c 24 68       	mov    %r11,0x68(%rsp)
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    33c1:	c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%rbp)
    33c8:	89 da                	mov    %ebx,%edx
    33ca:	44 89 e1             	mov    %r12d,%ecx
    33cd:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    33cf:	c7 45 44 01 00 00 00 	movl   $0x1,0x44(%rbp)
    33d6:	48 8d 35 13 43 00 00 	lea    0x4313(%rip),%rsi        # 76f0 <_IO_stdin_used+0x6f0>
    33dd:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    33e2:	83 c3 01             	add    $0x1,%ebx
    33e5:	e8 66 f0 ff ff       	call   2450 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    33ea:	48 89 e9             	mov    %rbp,%rcx
    33ed:	4c 89 ee             	mov    %r13,%rsi
    33f0:	4c 89 ff             	mov    %r15,%rdi
    33f3:	48 8d 15 e6 27 00 00 	lea    0x27e6(%rip),%rdx        # 5be0 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    33fa:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
    3401:	49 83 c7 08          	add    $0x8,%r15
    3405:	49 83 c5 38          	add    $0x38,%r13
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3409:	e8 62 f0 ff ff       	call   2470 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    340e:	48 8b 55 f0          	mov    -0x10(%rbp),%rdx
    3412:	49 8b 7f f8          	mov    -0x8(%r15),%rdi
    3416:	be 08 00 00 00       	mov    $0x8,%esi
    341b:	e8 c0 ee ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3420:	41 39 de             	cmp    %ebx,%r14d
    3423:	75 9c                	jne    33c1 <main+0xdd1>
  for (int k = 0 ; k < group_count ; k++) {
    3425:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    342a:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
    342f:	41 83 c6 02          	add    $0x2,%r14d
    3433:	48 8b 54 24 48       	mov    0x48(%rsp),%rdx
    3438:	4c 8b 5c 24 68       	mov    0x68(%rsp),%r11
    343d:	48 83 c1 10          	add    $0x10,%rcx
    3441:	48 83 c0 70          	add    $0x70,%rax
    3445:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
    344c:	45 85 e4             	test   %r12d,%r12d
    344f:	75 0b                	jne    345c <main+0xe6c>
    3451:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    3457:	e9 44 ff ff ff       	jmp    33a0 <main+0xdb0>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    345c:	be d8 00 00 00       	mov    $0xd8,%esi
    3461:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    3466:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    thread_data[x].task_count = 0;
    346b:	48 8b 05 4e 47 00 00 	mov    0x474e(%rip),%rax        # 7bc0 <_IO_stdin_used+0xbc0>
    thread_data[x].type = IO;
    3472:	41 c7 83 cc 03 00 00 02 00 00 00 	movl   $0x2,0x3cc(%r11)
    347d:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    3482:	4c 8d 3d f7 08 00 00 	lea    0x8f7(%rip),%r15        # 3d80 <external_thread>
    3489:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
    348e:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    thread_data[x].task_count = 0;
    3493:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    3498:	49 89 83 00 04 00 00 	mov    %rax,0x400(%r11)
    349f:	4c 89 f5             	mov    %r14,%rbp
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    34a2:	41 be 06 00 00 00    	mov    $0x6,%r14d
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    34a8:	e8 f3 ee ff ff       	call   23a0 <calloc@plt>
    34ad:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    34b2:	be 00 08 00 00       	mov    $0x800,%esi
    34b7:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    34b9:	49 89 83 18 04 00 00 	mov    %rax,0x418(%r11)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    34c0:	e8 eb ef ff ff       	call   24b0 <eventfd@plt>
    34c5:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    34ca:	be 08 00 00 00       	mov    $0x8,%esi
    34cf:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    34d4:	41 89 83 20 04 00 00 	mov    %eax,0x420(%r11)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    34db:	e8 c0 ee ff ff       	call   23a0 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
    34e0:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    34e5:	ba 05 00 00 00       	mov    $0x5,%edx
    34ea:	48 8d 35 01 3f 00 00 	lea    0x3f01(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    34f1:	4c 89 60 08          	mov    %r12,0x8(%rax)
    34f5:	bf 01 00 00 00       	mov    $0x1,%edi
    34fa:	4c 89 18             	mov    %r11,(%rax)
    thread_data[x].threads = my_thread_data;
    34fd:	49 89 83 d8 03 00 00 	mov    %rax,0x3d8(%r11)
    3504:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_count = thread_count;
    3506:	41 c7 83 e8 03 00 00 02 00 00 00 	movl   $0x2,0x3e8(%r11)
    thread_data[x].thread_index = x;
    3511:	41 c7 83 c4 03 00 00 05 00 00 00 	movl   $0x5,0x3c4(%r11)
    351c:	e8 2f ef ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3521:	48 8b 34 24          	mov    (%rsp),%rsi
    3525:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
    3529:	4c 89 e9             	mov    %r13,%rcx
    352c:	48 8d 15 bd 1e 00 00 	lea    0x1ebd(%rip),%rdx        # 53f0 <io_thread>
    3533:	4c 8d 6b 30          	lea    0x30(%rbx),%r13
    3537:	48 81 c6 18 01 00 00 	add    $0x118,%rsi
    353e:	e8 2d ef ff ff       	call   2470 <pthread_create@plt>
    3543:	ba 06 00 00 00       	mov    $0x6,%edx
    3548:	48 8d 35 ba 3e 00 00 	lea    0x3eba(%rip),%rsi        # 7409 <_IO_stdin_used+0x409>
    354f:	31 c0                	xor    %eax,%eax
    3551:	bf 01 00 00 00       	mov    $0x1,%edi
    3556:	e8 f5 ee ff ff       	call   2450 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    355b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3560:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    3565:	4c 89 eb             	mov    %r13,%rbx
    3568:	4d 89 e5             	mov    %r12,%r13
    356b:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
    3570:	48 05 50 01 00 00    	add    $0x150,%rax
    3576:	48 89 04 24          	mov    %rax,(%rsp)
    357a:	44 89 f2             	mov    %r14d,%edx
    357d:	48 8d 35 9b 3e 00 00 	lea    0x3e9b(%rip),%rsi        # 741f <_IO_stdin_used+0x41f>
    3584:	bf 01 00 00 00       	mov    $0x1,%edi
    3589:	31 c0                	xor    %eax,%eax
    358b:	e8 c0 ee ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3590:	be 08 00 00 00       	mov    $0x8,%esi
    3595:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    359a:	48 8b 05 1f 46 00 00 	mov    0x461f(%rip),%rax        # 7bc0 <_IO_stdin_used+0xbc0>
    thread_data[x].type = EXTERNAL;
    35a1:	c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%rbp)
    thread_data[x].task_count = 0;
    35a8:	48 89 45 40          	mov    %rax,0x40(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    35ac:	e8 ef ed ff ff       	call   23a0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    35b1:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    35b6:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    35bb:	c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    35c5:	48 89 45 50          	mov    %rax,0x50(%rbp)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    35c9:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    35cc:	bf 02 00 00 00       	mov    $0x2,%edi
    35d1:	e8 ca ed ff ff       	call   23a0 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    35d6:	44 89 75 04          	mov    %r14d,0x4(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    35da:	48 8b 34 24          	mov    (%rsp),%rsi
    35de:	48 89 e9             	mov    %rbp,%rcx
      my_thread_data[n] = &thread_data[n]; 
    35e1:	4c 89 20             	mov    %r12,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    35e4:	48 89 df             	mov    %rbx,%rdi
    35e7:	4c 89 fa             	mov    %r15,%rdx
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    35ea:	48 83 c3 08          	add    $0x8,%rbx
    thread_data[x].threads = my_thread_data;
    35ee:	48 89 45 18          	mov    %rax,0x18(%rbp)
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    35f2:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
      my_thread_data[n] = &thread_data[n]; 
    35f9:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    35fd:	48 8b 05 9c 45 00 00 	mov    0x459c(%rip),%rax        # 7ba0 <_IO_stdin_used+0xba0>
    3604:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    360b:	e8 60 ee ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3610:	48 83 44 24 60 10    	addq   $0x10,0x60(%rsp)
    3616:	48 83 04 24 38       	addq   $0x38,(%rsp)
    361b:	41 83 fe 06          	cmp    $0x6,%r14d
    361f:	75 0b                	jne    362c <main+0x103c>
    3621:	41 be 07 00 00 00    	mov    $0x7,%r14d
    3627:	e9 4e ff ff ff       	jmp    357a <main+0xf8a>
    362c:	4d 89 e3             	mov    %r12,%r11
    362f:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    3634:	4d 8d 6c 24 04       	lea    0x4(%r12),%r13
    3639:	48 8d 2d fc 3d 00 00 	lea    0x3dfc(%rip),%rbp        # 743c <_IO_stdin_used+0x43c>
    3640:	4d 8d a4 24 04 06 00 00 	lea    0x604(%r12),%r12
    3648:	4d 89 de             	mov    %r11,%r14
    364b:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    364f:	41 8b 55 00          	mov    0x0(%r13),%edx
    3653:	48 89 ee             	mov    %rbp,%rsi
    3656:	bf 01 00 00 00       	mov    $0x1,%edi
    365b:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    365d:	49 81 c5 c0 00 00 00 	add    $0xc0,%r13
    3664:	e8 e7 ed ff ff       	call   2450 <__printf_chk@plt>
    3669:	4d 39 ec             	cmp    %r13,%r12
    366c:	75 dd                	jne    364b <main+0x105b>
    366e:	48 8d 3d da 3d 00 00 	lea    0x3dda(%rip),%rdi        # 744f <_IO_stdin_used+0x44f>
    3675:	4c 89 34 24          	mov    %r14,(%rsp)
    3679:	45 31 ed             	xor    %r13d,%r13d
    367c:	4c 8d a4 24 90 00 00 00 	lea    0x90(%rsp),%r12
    3684:	e8 67 ec ff ff       	call   22f0 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3689:	4c 8b 34 24          	mov    (%rsp),%r14
    368d:	48 8d 2d d9 3d 00 00 	lea    0x3dd9(%rip),%rbp        # 746d <_IO_stdin_used+0x46d>
    void * result; 
    pthread_join(thread[x], &result);
    3694:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    3698:	4c 89 e6             	mov    %r12,%rsi
    369b:	e8 50 ee ff ff       	call   24f0 <pthread_join@plt>
    36a0:	44 89 ea             	mov    %r13d,%edx
    36a3:	48 89 ee             	mov    %rbp,%rsi
    36a6:	bf 01 00 00 00       	mov    $0x1,%edi
    36ab:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    36ad:	49 83 c5 01          	add    $0x1,%r13
    36b1:	e8 9a ed ff ff       	call   2450 <__printf_chk@plt>
    36b6:	49 83 fd 08          	cmp    $0x8,%r13
    36ba:	75 d8                	jne    3694 <main+0x10a4>
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
    36bc:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
  long received = 0;
    36c4:	45 31 d2             	xor    %r10d,%r10d
    36c7:	31 ed                	xor    %ebp,%ebp
    36c9:	4c 89 f7             	mov    %r14,%rdi
  long ingests = 0;
    36cc:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
    36d5:	4c 89 d3             	mov    %r10,%rbx
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    36d8:	49 bc db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r12
  long total = 0;
    36e2:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    36eb:	48 89 e8             	mov    %rbp,%rax
    36ee:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    36f3:	48 89 7c 24 30       	mov    %rdi,0x30(%rsp)
    36f8:	4d 89 d7             	mov    %r10,%r15
    36fb:	48 f7 d8             	neg    %rax
    36fe:	48 89 6c 24 60       	mov    %rbp,0x60(%rsp)
    3703:	49 89 c6             	mov    %rax,%r14
    3706:	83 e0 30             	and    $0x30,%eax
    3709:	48 01 f0             	add    %rsi,%rax
    370c:	41 81 e6 80 01 00 00 	and    $0x180,%r14d
    3713:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    3718:	8d 44 2d 00          	lea    0x0(%rbp,%rbp,1),%eax
    371c:	48 89 dd             	mov    %rbx,%rbp
    371f:	48 8b 1c 24          	mov    (%rsp),%rbx
    3723:	89 44 24 48          	mov    %eax,0x48(%rsp)
    3727:	83 e8 01             	sub    $0x1,%eax
    372a:	49 01 fe             	add    %rdi,%r14
    372d:	89 44 24 28          	mov    %eax,0x28(%rsp)
      int x = (k * threads_per_group) + d;
    3731:	8b 7c 24 28          	mov    0x28(%rsp),%edi
    3735:	89 f8                	mov    %edi,%eax
    3737:	89 7c 24 38          	mov    %edi,0x38(%rsp)
    373b:	83 c7 01             	add    $0x1,%edi
    373e:	89 fe                	mov    %edi,%esi
    3740:	89 7c 24 28          	mov    %edi,0x28(%rsp)
        other = abs(x - 1) % total_threads;
    3744:	89 c7                	mov    %eax,%edi
    3746:	8d 40 02             	lea    0x2(%rax),%eax
    3749:	83 e6 01             	and    $0x1,%esi
    374c:	0f 45 c7             	cmovne %edi,%eax
    374f:	bf 0a 00 00 00       	mov    $0xa,%edi
    3754:	4c 63 e8             	movslq %eax,%r13
    3757:	e8 74 eb ff ff       	call   22d0 <putchar@plt>
    375c:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    3761:	bf 01 00 00 00       	mov    $0x1,%edi
    3766:	48 8d 35 14 3d 00 00 	lea    0x3d14(%rip),%rsi        # 7481 <_IO_stdin_used+0x481>
    376d:	48 8b 10             	mov    (%rax),%rdx
    3770:	31 c0                	xor    %eax,%eax
    3772:	e8 d9 ec ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3777:	41 8b 56 40          	mov    0x40(%r14),%edx
    377b:	85 d2                	test   %edx,%edx
    377d:	0f 8e 46 04 00 00    	jle    3bc9 <main+0x15d9>
    3783:	48 63 f2             	movslq %edx,%rsi
    3786:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    378a:	31 d2                	xor    %edx,%edx
    378c:	48 c1 e6 09          	shl    $0x9,%rsi
    3790:	48 01 c6             	add    %rax,%rsi
    3793:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    3798:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    379f:	48 05 00 02 00 00    	add    $0x200,%rax
    37a5:	48 39 f0             	cmp    %rsi,%rax
    37a8:	75 ee                	jne    3798 <main+0x11a8>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    37aa:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    37af:	4b 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%rax
    37b4:	48 c1 e0 06          	shl    $0x6,%rax
    37b8:	48 01 f8             	add    %rdi,%rax
    37bb:	48 63 70 40          	movslq 0x40(%rax),%rsi
    37bf:	85 f6                	test   %esi,%esi
    37c1:	7e 1f                	jle    37e2 <main+0x11f2>
    37c3:	48 8b 40 38          	mov    0x38(%rax),%rax
    37c7:	48 c1 e6 09          	shl    $0x9,%rsi
    37cb:	48 01 c6             	add    %rax,%rsi
    37ce:	66 90                	xchg   %ax,%ax
        v += thread_data[other].tasks[n].v;
    37d0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    37d7:	48 05 00 02 00 00    	add    $0x200,%rax
    37dd:	48 39 f0             	cmp    %rsi,%rax
    37e0:	75 ee                	jne    37d0 <main+0x11e0>
    37e2:	48 8d 35 ad 3c 00 00 	lea    0x3cad(%rip),%rsi        # 7496 <_IO_stdin_used+0x496>
    37e9:	bf 01 00 00 00       	mov    $0x1,%edi
    37ee:	31 c0                	xor    %eax,%eax
    37f0:	e8 5b ec ff ff       	call   2450 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    37f5:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    37fa:	bf 01 00 00 00       	mov    $0x1,%edi
    37ff:	48 8b 30             	mov    (%rax),%rsi
    3802:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    380c:	48 f7 ee             	imul   %rsi
    380f:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3813:	31 c0                	xor    %eax,%eax
    3815:	48 d1 fa             	sar    %rdx
    3818:	48 29 f2             	sub    %rsi,%rdx
    381b:	48 8d 35 fe 3e 00 00 	lea    0x3efe(%rip),%rsi        # 7720 <_IO_stdin_used+0x720>
    3822:	e8 29 ec ff ff       	call   2450 <__printf_chk@plt>
    3827:	bf 0a 00 00 00       	mov    $0xa,%edi
    382c:	e8 9f ea ff ff       	call   22d0 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3831:	41 8b 56 40          	mov    0x40(%r14),%edx
    3835:	85 d2                	test   %edx,%edx
    3837:	7e 60                	jle    3899 <main+0x12a9>
    3839:	49 8b 46 38          	mov    0x38(%r14),%rax
    383d:	48 63 f2             	movslq %edx,%rsi
    3840:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    3845:	48 c1 e6 09          	shl    $0x9,%rsi
    3849:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    384e:	48 01 c6             	add    %rax,%rsi
    3851:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3858:	48 8b 90 70 01 00 00 	mov    0x170(%rax),%rdx
        total += thread_data[x].tasks[n].n;
    385f:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3866:	48 05 00 02 00 00    	add    $0x200,%rax
        ingests += thread_data[x].tasks[n].ingest_count;
    386c:	48 03 88 68 ff ff ff 	add    -0x98(%rax),%rcx
        sends += thread_data[x].tasks[n].sends;
    3873:	4c 03 b8 78 ff ff ff 	add    -0x88(%rax),%r15
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    387a:	48 03 5a 10          	add    0x10(%rdx),%rbx
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    387e:	48 03 6a 18          	add    0x18(%rdx),%rbp
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3882:	48 03 5a 38          	add    0x38(%rdx),%rbx
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3886:	48 03 6a 40          	add    0x40(%rdx),%rbp
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    388a:	48 39 f0             	cmp    %rsi,%rax
    388d:	75 c9                	jne    3858 <main+0x1268>
    388f:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    3894:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3899:	45 31 ed             	xor    %r13d,%r13d
    389c:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    38a4:	0f 8e 7e 00 00 00    	jle    3928 <main+0x1338>
    38aa:	48 89 df             	mov    %rbx,%rdi
    38ad:	4c 89 f0             	mov    %r14,%rax
    38b0:	4c 89 eb             	mov    %r13,%rbx
    38b3:	49 89 ee             	mov    %rbp,%r14
    38b6:	49 89 fd             	mov    %rdi,%r13
    38b9:	48 89 c5             	mov    %rax,%rbp
    38bc:	0f 1f 40 00          	nopl   0x0(%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    38c0:	48 8b 85 90 00 00 00 	mov    0x90(%rbp),%rax
    38c7:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    38cb:	48 83 ec 08          	sub    $0x8,%rsp
    38cf:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    38d4:	48 83 c3 01          	add    $0x1,%rbx
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    38d8:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    38dc:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    38e0:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    38e4:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    38e7:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    38eb:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    38ee:	49 f7 e4             	mul    %r12
    38f1:	8b 49 20             	mov    0x20(%rcx),%ecx
    38f4:	56                   	push   %rsi
    38f5:	31 c0                	xor    %eax,%eax
    38f7:	48 8d 35 42 3e 00 00 	lea    0x3e42(%rip),%rsi        # 7740 <_IO_stdin_used+0x740>
    38fe:	48 c1 ea 12          	shr    $0x12,%rdx
    3902:	49 89 d1             	mov    %rdx,%r9
    3905:	ba 02 00 00 00       	mov    $0x2,%edx
    390a:	e8 41 eb ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    390f:	41 58                	pop    %r8
    3911:	41 59                	pop    %r9
    3913:	48 39 9d a0 00 00 00 	cmp    %rbx,0xa0(%rbp)
    391a:	7f a4                	jg     38c0 <main+0x12d0>
    391c:	48 89 e8             	mov    %rbp,%rax
    391f:	4c 89 eb             	mov    %r13,%rbx
    3922:	4c 89 f5             	mov    %r14,%rbp
    3925:	49 89 c6             	mov    %rax,%r14
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3928:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    392f:	85 f6                	test   %esi,%esi
    3931:	0f 8e 0d 01 00 00    	jle    3a44 <main+0x1454>
    3937:	48 89 5c 24 68       	mov    %rbx,0x68(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    393c:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    3940:	31 d2                	xor    %edx,%edx
    3942:	4c 89 7c 24 70       	mov    %r15,0x70(%rsp)
    3947:	48 89 6c 24 78       	mov    %rbp,0x78(%rsp)
    394c:	0f 1f 40 00          	nopl   0x0(%rax)
    3950:	49 8b 04 d1          	mov    (%r9,%rdx,8),%rax
    3954:	41 89 d7             	mov    %edx,%r15d
    3957:	48 8d 1c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rbx
    395f:	44 8b 00             	mov    (%rax),%r8d
    3962:	45 85 c0             	test   %r8d,%r8d
    3965:	0f 8e be 00 00 00    	jle    3a29 <main+0x1439>
    396b:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3970:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3974:	31 c0                	xor    %eax,%eax
    3976:	48 89 c6             	mov    %rax,%rsi
    3979:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3980:	48 89 f5             	mov    %rsi,%rbp
    3983:	45 31 ed             	xor    %r13d,%r13d
    3986:	48 c1 e5 08          	shl    $0x8,%rbp
    398a:	48 8d 14 29          	lea    (%rcx,%rbp,1),%rdx
    398e:	8b 82 94 00 00 00    	mov    0x94(%rdx),%eax
    3994:	85 c0                	test   %eax,%eax
    3996:	7e 78                	jle    3a10 <main+0x1420>
    3998:	48 89 34 24          	mov    %rsi,(%rsp)
    399c:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    39a0:	4c 89 e9             	mov    %r13,%rcx
    39a3:	48 83 ec 08          	sub    $0x8,%rsp
    39a7:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    39ac:	49 83 c5 01          	add    $0x1,%r13
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    39b0:	48 c1 e1 05          	shl    $0x5,%rcx
    39b4:	48 03 8a 88 00 00 00 	add    0x88(%rdx),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    39bb:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    39bf:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    39c3:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    39c6:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    39ca:	4c 2b 01             	sub    (%rcx),%r8
    39cd:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    39ce:	49 f7 e4             	mul    %r12
    39d1:	44 89 f9             	mov    %r15d,%ecx
    39d4:	48 8d 35 b5 3d 00 00 	lea    0x3db5(%rip),%rsi        # 7790 <_IO_stdin_used+0x790>
    39db:	31 c0                	xor    %eax,%eax
    39dd:	48 c1 ea 12          	shr    $0x12,%rdx
    39e1:	49 89 d1             	mov    %rdx,%r9
    39e4:	ba 02 00 00 00       	mov    $0x2,%edx
    39e9:	e8 62 ea ff ff       	call   2450 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    39ee:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    39f2:	5e                   	pop    %rsi
    39f3:	5f                   	pop    %rdi
    39f4:	49 8b 04 19          	mov    (%r9,%rbx,1),%rax
    39f8:	48 8b 48 08          	mov    0x8(%rax),%rcx
    39fc:	48 8d 14 29          	lea    (%rcx,%rbp,1),%rdx
    3a00:	44 39 aa 94 00 00 00 	cmp    %r13d,0x94(%rdx)
    3a07:	7f 97                	jg     39a0 <main+0x13b0>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3a09:	48 8b 34 24          	mov    (%rsp),%rsi
    3a0d:	44 8b 00             	mov    (%rax),%r8d
    3a10:	48 83 c6 01          	add    $0x1,%rsi
    3a14:	41 39 f0             	cmp    %esi,%r8d
    3a17:	0f 8f 63 ff ff ff    	jg     3980 <main+0x1390>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3a1d:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    3a22:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    3a29:	48 83 c2 01          	add    $0x1,%rdx
    3a2d:	39 d6                	cmp    %edx,%esi
    3a2f:	0f 8f 1b ff ff ff    	jg     3950 <main+0x1360>
    3a35:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
    3a3a:	4c 8b 7c 24 70       	mov    0x70(%rsp),%r15
    3a3f:	48 8b 6c 24 78       	mov    0x78(%rsp),%rbp
    for (int d = 0 ; d < threads_per_group ; d++) {
    3a44:	48 83 44 24 20 18    	addq   $0x18,0x20(%rsp)
    3a4a:	8b 7c 24 38          	mov    0x38(%rsp),%edi
    3a4e:	49 81 c6 c0 00 00 00 	add    $0xc0,%r14
    3a55:	39 7c 24 48          	cmp    %edi,0x48(%rsp)
    3a59:	0f 85 d2 fc ff ff    	jne    3731 <main+0x1141>
  for (int k = 0 ; k < group_count ; k++) {
    3a5f:	48 89 1c 24          	mov    %rbx,(%rsp)
    3a63:	48 89 eb             	mov    %rbp,%rbx
    3a66:	48 8b 6c 24 60       	mov    0x60(%rsp),%rbp
    3a6b:	4d 89 fa             	mov    %r15,%r10
    3a6e:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    3a73:	48 85 ed             	test   %rbp,%rbp
    3a76:	75 0a                	jne    3a82 <main+0x1492>
    3a78:	48 8b 6c 24 50       	mov    0x50(%rsp),%rbp
    3a7d:	e9 69 fc ff ff       	jmp    36eb <main+0x10fb>
    3a82:	4c 89 7c 24 20       	mov    %r15,0x20(%rsp)
    3a87:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
    3a8c:	48 8d 35 10 3a 00 00 	lea    0x3a10(%rip),%rsi        # 74a3 <_IO_stdin_used+0x4a3>
    3a93:	31 c0                	xor    %eax,%eax
    3a95:	bf 01 00 00 00       	mov    $0x1,%edi
    3a9a:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3a9f:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    3aa9:	4c 89 fa             	mov    %r15,%rdx
    3aac:	e8 9f e9 ff ff       	call   2450 <__printf_chk@plt>
    3ab1:	bf 0a 00 00 00       	mov    $0xa,%edi
    3ab6:	e8 15 e8 ff ff       	call   22d0 <putchar@plt>
    3abb:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3ac0:	bf 01 00 00 00       	mov    $0x1,%edi
    3ac5:	48 8d 35 1c 3d 00 00 	lea    0x3d1c(%rip),%rsi        # 77e8 <_IO_stdin_used+0x7e8>
    3acc:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3ad0:	31 c0                	xor    %eax,%eax
    3ad2:	e8 79 e9 ff ff       	call   2450 <__printf_chk@plt>
    3ad7:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3adc:	bf 01 00 00 00       	mov    $0x1,%edi
    3ae1:	48 8d 35 28 3d 00 00 	lea    0x3d28(%rip),%rsi        # 7810 <_IO_stdin_used+0x810>
    3ae8:	48 f7 eb             	imul   %rbx
    3aeb:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3af0:	48 c1 f8 3f          	sar    $0x3f,%rax
    3af4:	48 d1 fa             	sar    %rdx
    3af7:	48 29 c2             	sub    %rax,%rdx
    3afa:	31 c0                	xor    %eax,%eax
    3afc:	e8 4f e9 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3b01:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    3b06:	bf 01 00 00 00       	mov    $0x1,%edi
    3b0b:	48 8d 35 2e 3d 00 00 	lea    0x3d2e(%rip),%rsi        # 7840 <_IO_stdin_used+0x840>
    3b12:	4c 89 c8             	mov    %r9,%rax
    3b15:	49 c1 f9 3f          	sar    $0x3f,%r9
    3b19:	48 f7 eb             	imul   %rbx
    3b1c:	31 c0                	xor    %eax,%eax
    3b1e:	48 d1 fa             	sar    %rdx
    3b21:	4c 29 ca             	sub    %r9,%rdx
    3b24:	e8 27 e9 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3b29:	4c 89 f8             	mov    %r15,%rax
    3b2c:	bf 01 00 00 00       	mov    $0x1,%edi
    3b31:	48 8d 35 38 3d 00 00 	lea    0x3d38(%rip),%rsi        # 7870 <_IO_stdin_used+0x870>
    3b38:	48 f7 eb             	imul   %rbx
    3b3b:	4c 89 f8             	mov    %r15,%rax
    3b3e:	48 c1 f8 3f          	sar    $0x3f,%rax
    3b42:	48 d1 fa             	sar    %rdx
    3b45:	48 29 c2             	sub    %rax,%rdx
    3b48:	31 c0                	xor    %eax,%eax
    3b4a:	e8 01 e9 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3b4f:	48 8b 04 24          	mov    (%rsp),%rax
    3b53:	bf 01 00 00 00       	mov    $0x1,%edi
    3b58:	48 8d 35 58 39 00 00 	lea    0x3958(%rip),%rsi        # 74b7 <_IO_stdin_used+0x4b7>
    3b5f:	48 f7 eb             	imul   %rbx
    3b62:	48 8b 04 24          	mov    (%rsp),%rax
    3b66:	48 c1 f8 3f          	sar    $0x3f,%rax
    3b6a:	48 d1 fa             	sar    %rdx
    3b6d:	48 29 c2             	sub    %rax,%rdx
    3b70:	31 c0                	xor    %eax,%eax
    3b72:	e8 d9 e8 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3b77:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    3b7c:	bf 01 00 00 00       	mov    $0x1,%edi
    3b81:	48 8d 35 40 39 00 00 	lea    0x3940(%rip),%rsi        # 74c8 <_IO_stdin_used+0x4c8>
    3b88:	4c 89 d0             	mov    %r10,%rax
    3b8b:	48 f7 eb             	imul   %rbx
    3b8e:	4c 89 d0             	mov    %r10,%rax
    3b91:	48 c1 f8 3f          	sar    $0x3f,%rax
    3b95:	48 d1 fa             	sar    %rdx
    3b98:	48 29 c2             	sub    %rax,%rdx
    3b9b:	31 c0                	xor    %eax,%eax
    3b9d:	e8 ae e8 ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3ba2:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    3baa:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3bb3:	75 25                	jne    3bda <main+0x15ea>
    3bb5:	48 81 c4 a8 00 00 00 	add    $0xa8,%rsp
    3bbc:	31 c0                	xor    %eax,%eax
    3bbe:	5b                   	pop    %rbx
    3bbf:	5d                   	pop    %rbp
    3bc0:	41 5c                	pop    %r12
    3bc2:	41 5d                	pop    %r13
    3bc4:	41 5e                	pop    %r14
    3bc6:	41 5f                	pop    %r15
    3bc8:	c3                   	ret
      long v = 0;
    3bc9:	31 d2                	xor    %edx,%edx
    3bcb:	e9 da fb ff ff       	jmp    37aa <main+0x11ba>
            exit(1);
    3bd0:	bf 01 00 00 00       	mov    $0x1,%edi
    3bd5:	e8 c6 e8 ff ff       	call   24a0 <exit@plt>
}
    3bda:	e8 51 e7 ff ff       	call   2330 <__stack_chk_fail@plt>
    3bdf:	90                   	nop

0000000000003be0 <_start>:
    3be0:	f3 0f 1e fa          	endbr64
    3be4:	31 ed                	xor    %ebp,%ebp
    3be6:	49 89 d1             	mov    %rdx,%r9
    3be9:	5e                   	pop    %rsi
    3bea:	48 89 e2             	mov    %rsp,%rdx
    3bed:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3bf1:	50                   	push   %rax
    3bf2:	54                   	push   %rsp
    3bf3:	45 31 c0             	xor    %r8d,%r8d
    3bf6:	31 c9                	xor    %ecx,%ecx
    3bf8:	48 8d 3d f1 e9 ff ff 	lea    -0x160f(%rip),%rdi        # 25f0 <main>
    3bff:	ff 15 d3 63 00 00    	call   *0x63d3(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3c05:	f4                   	hlt
    3c06:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003c10 <deregister_tm_clones>:
    3c10:	48 8d 3d 09 64 00 00 	lea    0x6409(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3c17:	48 8d 05 02 64 00 00 	lea    0x6402(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    3c1e:	48 39 f8             	cmp    %rdi,%rax
    3c21:	74 15                	je     3c38 <deregister_tm_clones+0x28>
    3c23:	48 8b 05 b6 63 00 00 	mov    0x63b6(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    3c2a:	48 85 c0             	test   %rax,%rax
    3c2d:	74 09                	je     3c38 <deregister_tm_clones+0x28>
    3c2f:	ff e0                	jmp    *%rax
    3c31:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3c38:	c3                   	ret
    3c39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c40 <register_tm_clones>:
    3c40:	48 8d 3d d9 63 00 00 	lea    0x63d9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3c47:	48 8d 35 d2 63 00 00 	lea    0x63d2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    3c4e:	48 29 fe             	sub    %rdi,%rsi
    3c51:	48 89 f0             	mov    %rsi,%rax
    3c54:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3c58:	48 c1 f8 03          	sar    $0x3,%rax
    3c5c:	48 01 c6             	add    %rax,%rsi
    3c5f:	48 d1 fe             	sar    %rsi
    3c62:	74 14                	je     3c78 <register_tm_clones+0x38>
    3c64:	48 8b 05 85 63 00 00 	mov    0x6385(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    3c6b:	48 85 c0             	test   %rax,%rax
    3c6e:	74 08                	je     3c78 <register_tm_clones+0x38>
    3c70:	ff e0                	jmp    *%rax
    3c72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c78:	c3                   	ret
    3c79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c80 <__do_global_dtors_aux>:
    3c80:	f3 0f 1e fa          	endbr64
    3c84:	80 3d 9d 63 00 00 00 	cmpb   $0x0,0x639d(%rip)        # a028 <completed.0>
    3c8b:	75 2b                	jne    3cb8 <__do_global_dtors_aux+0x38>
    3c8d:	55                   	push   %rbp
    3c8e:	48 83 3d 62 63 00 00 00 	cmpq   $0x0,0x6362(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3c96:	48 89 e5             	mov    %rsp,%rbp
    3c99:	74 0c                	je     3ca7 <__do_global_dtors_aux+0x27>
    3c9b:	48 8b 3d 66 63 00 00 	mov    0x6366(%rip),%rdi        # a008 <__dso_handle>
    3ca2:	e8 09 e6 ff ff       	call   22b0 <__cxa_finalize@plt>
    3ca7:	e8 64 ff ff ff       	call   3c10 <deregister_tm_clones>
    3cac:	c6 05 75 63 00 00 01 	movb   $0x1,0x6375(%rip)        # a028 <completed.0>
    3cb3:	5d                   	pop    %rbp
    3cb4:	c3                   	ret
    3cb5:	0f 1f 00             	nopl   (%rax)
    3cb8:	c3                   	ret
    3cb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003cc0 <frame_dummy>:
    3cc0:	f3 0f 1e fa          	endbr64
    3cc4:	e9 77 ff ff ff       	jmp    3c40 <register_tm_clones>
    3cc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003cd0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3cd0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3cd4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3cdb:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    3cdf:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3ce7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    3ceb:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3cef:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3cf6:	48 85 c9             	test   %rcx,%rcx
    3cf9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3d00:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3d04:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3d08:	31 c0                	xor    %eax,%eax
    3d0a:	c3                   	ret
    3d0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003d10 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3d10:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3d14:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    3d1b:	85 c9                	test   %ecx,%ecx
    3d1d:	7e 4f                	jle    3d6e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3d1f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3d26:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    3d2d:	48 c1 e1 09          	shl    $0x9,%rcx
    3d31:	48 8b 50 18          	mov    0x18(%rax),%rdx
    3d35:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3d39:	48 8b 70 38          	mov    0x38(%rax),%rsi
    3d3d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3d3f:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    3d43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3d48:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3d50:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3d58:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3d63:	48 05 00 02 00 00    	add    $0x200,%rax
    3d69:	48 39 c1             	cmp    %rax,%rcx
    3d6c:	75 da                	jne    3d48 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    3d6e:	0f ae f8             	sfence
}
    3d71:	31 c0                	xor    %eax,%eax
    3d73:	c3                   	ret
    3d74:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3d7f:	90                   	nop

0000000000003d80 <external_thread>:
void * external_thread(void *arg) {
    3d80:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3d84:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    3d88:	0f 85 fb 00 00 00    	jne    3e89 <external_thread+0x109>
void * external_thread(void *arg) {
    3d8e:	41 57                	push   %r15
    3d90:	49 89 ff             	mov    %rdi,%r15
    3d93:	41 56                	push   %r14
    3d95:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    3d97:	4c 8d 2d 66 32 00 00 	lea    0x3266(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    3d9e:	41 54                	push   %r12
    3da0:	55                   	push   %rbp
    3da1:	53                   	push   %rbx
    3da2:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    3da6:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    3dac:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    3db0:	85 c9                	test   %ecx,%ecx
    3db2:	7e 6e                	jle    3e22 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3db4:	45 31 e4             	xor    %r12d,%r12d
    3db7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3dc0:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    3dc8:	31 db                	xor    %ebx,%ebx
    3dca:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3dce:	48 8b 06             	mov    (%rsi),%rax
    3dd1:	8b 10                	mov    (%rax),%edx
    3dd3:	85 d2                	test   %edx,%edx
    3dd5:	7e 2a                	jle    3e01 <external_thread+0x81>
    3dd7:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    3ddb:	48 89 dd             	mov    %rbx,%rbp
    3dde:	48 c1 e5 08          	shl    $0x8,%rbp
    3de2:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    3de6:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    3ded:	45 85 c0             	test   %r8d,%r8d
    3df0:	74 36                	je     3e28 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3df2:	48 83 c3 01          	add    $0x1,%rbx
    3df6:	39 da                	cmp    %ebx,%edx
    3df8:	7f e1                	jg     3ddb <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    3dfa:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    3e01:	49 83 c4 01          	add    $0x1,%r12
    3e05:	44 39 e1             	cmp    %r12d,%ecx
    3e08:	7f b6                	jg     3dc0 <external_thread+0x40>
  while (data->running == 1) {
    3e0a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    3e0f:	74 9f                	je     3db0 <external_thread+0x30>
}
    3e11:	48 83 c4 08          	add    $0x8,%rsp
    3e15:	31 c0                	xor    %eax,%eax
    3e17:	5b                   	pop    %rbx
    3e18:	5d                   	pop    %rbp
    3e19:	41 5c                	pop    %r12
    3e1b:	41 5d                	pop    %r13
    3e1d:	41 5e                	pop    %r14
    3e1f:	41 5f                	pop    %r15
    3e21:	c3                   	ret
  while (data->running == 1) {
    3e22:	eb fe                	jmp    3e22 <external_thread+0xa2>
    3e24:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    3e28:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    3e2b:	48 8b 06             	mov    (%rsi),%rax
    3e2e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    3e32:	48 01 ef             	add    %rbp,%rdi
    3e35:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    3e3c:	48 c1 e6 05          	shl    $0x5,%rsi
    3e40:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    3e47:	bf 04 00 00 00       	mov    $0x4,%edi
    3e4c:	e8 bf e4 ff ff       	call   2310 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    3e51:	49 8b 47 50          	mov    0x50(%r15),%rax
    3e55:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    3e59:	48 8b 40 08          	mov    0x8(%rax),%rax
    3e5d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    3e68:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3e6b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    3e6f:	48 83 c3 01          	add    $0x1,%rbx
    3e73:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3e77:	48 8b 06             	mov    (%rsi),%rax
    3e7a:	8b 10                	mov    (%rax),%edx
    3e7c:	39 da                	cmp    %ebx,%edx
    3e7e:	0f 8f 53 ff ff ff    	jg     3dd7 <external_thread+0x57>
    3e84:	e9 71 ff ff ff       	jmp    3dfa <external_thread+0x7a>
}
    3e89:	31 c0                	xor    %eax,%eax
    3e8b:	c3                   	ret
    3e8c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003e90 <timer_thread>:
void* timer_thread(void *arg) {
    3e90:	f3 0f 1e fa          	endbr64
    3e94:	41 57                	push   %r15
    3e96:	48 8d 35 73 31 00 00 	lea    0x3173(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3e9d:	41 56                	push   %r14
    3e9f:	41 55                	push   %r13
    3ea1:	41 54                	push   %r12
    3ea3:	55                   	push   %rbp
    3ea4:	48 89 fd             	mov    %rdi,%rbp
    3ea7:	53                   	push   %rbx
    3ea8:	48 83 ec 58          	sub    $0x58,%rsp
    3eac:	8b 57 04             	mov    0x4(%rdi),%edx
    3eaf:	bf 01 00 00 00       	mov    $0x1,%edi
    3eb4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3ebd:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3ec2:	31 c0                	xor    %eax,%eax
    3ec4:	e8 87 e5 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3ec9:	66 0f 6f 05 bf 3b 00 00 	movdqa 0x3bbf(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
    3ed1:	ba 88 13 00 00       	mov    $0x1388,%edx
    3ed6:	31 c0                	xor    %eax,%eax
    3ed8:	48 8d 35 43 31 00 00 	lea    0x3143(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3edf:	bf 01 00 00 00       	mov    $0x1,%edi
    3ee4:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3ee9:	e8 62 e5 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3eee:	44 8b 65 44          	mov    0x44(%rbp),%r12d
    3ef2:	45 85 e4             	test   %r12d,%r12d
    3ef5:	0f 84 a3 00 00 00    	je     3f9e <timer_thread+0x10e>
  int n = 0;
    3efb:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    3efe:	45 31 e4             	xor    %r12d,%r12d
    3f01:	49 89 e6             	mov    %rsp,%r14
    y++;
    3f04:	31 db                	xor    %ebx,%ebx
    3f06:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    3f0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    nanosleep(&preempt , &rem2);
    3f10:	4c 89 ef             	mov    %r13,%rdi
    3f13:	4c 89 f6             	mov    %r14,%rsi
    n++;
    3f16:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3f1a:	e8 31 e4 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f1f:	48 63 45 30          	movslq 0x30(%rbp),%rax
    y++;
    3f23:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f28:	85 c0                	test   %eax,%eax
    3f2a:	7e 49                	jle    3f75 <timer_thread+0xe5>
    3f2c:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3f30:	49 c1 e4 09          	shl    $0x9,%r12
    3f34:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3f38:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3f40:	4c 8b 11             	mov    (%rcx),%r10
    3f43:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f45:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3f49:	99                   	cltd
    3f4a:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3f4e:	49 8b 72 38          	mov    0x38(%r10),%rsi
    3f52:	48 63 d2             	movslq %edx,%rdx
    3f55:	48 c1 e2 09          	shl    $0x9,%rdx
    3f59:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3f64:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f70:	49 39 c8             	cmp    %rcx,%r8
    3f73:	75 cb                	jne    3f40 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    3f75:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3f78:	48 8b 45 18          	mov    0x18(%rbp),%rax
  while (data->running && n < times) {
    3f7c:	44 8b 45 44          	mov    0x44(%rbp),%r8d
    if (y >= data->threads[0]->task_count) {
    3f80:	48 8b 00             	mov    (%rax),%rax
    y++;
    3f83:	39 78 40             	cmp    %edi,0x40(%rax)
    3f86:	0f 4e fb             	cmovle %ebx,%edi
    3f89:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3f8c:	45 85 c0             	test   %r8d,%r8d
    3f8f:	74 0d                	je     3f9e <timer_thread+0x10e>
    3f91:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    3f98:	0f 85 72 ff ff ff    	jne    3f10 <timer_thread+0x80>
    3f9e:	48 8d 3d 93 30 00 00 	lea    0x3093(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3fa5:	e8 46 e3 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3faa:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    3fae:	85 d2                	test   %edx,%edx
    3fb0:	7e 73                	jle    4025 <timer_thread+0x195>
    for (int y = 0 ; y < data->task_count ; y++) {
    3fb2:	48 63 45 40          	movslq 0x40(%rbp),%rax
    3fb6:	85 c0                	test   %eax,%eax
    3fb8:	7e 6b                	jle    4025 <timer_thread+0x195>
    3fba:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3fbe:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    3fc2:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3fca:	31 c9                	xor    %ecx,%ecx
    3fcc:	48 89 c6             	mov    %rax,%rsi
    3fcf:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3fd3:	48 8b 40 38          	mov    0x38(%rax),%rax
    3fd7:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    3fdb:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3fe1:	74 1d                	je     4000 <timer_thread+0x170>
    3fe3:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3fed:	48 05 00 02 00 00    	add    $0x200,%rax
    3ff3:	48 39 c2             	cmp    %rax,%rdx
    3ff6:	74 24                	je     401c <timer_thread+0x18c>
    3ff8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->threads[x]->tasks[y].sending = 0;
    4000:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    400a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4010:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4017:	48 39 c2             	cmp    %rax,%rdx
    401a:	75 e4                	jne    4000 <timer_thread+0x170>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    401c:	48 83 c1 08          	add    $0x8,%rcx
    4020:	48 39 cf             	cmp    %rcx,%rdi
    4023:	75 aa                	jne    3fcf <timer_thread+0x13f>
  asm volatile ("mfence" ::: "memory");
    4025:	0f ae f0             	mfence
  struct timespec drain = {
    4028:	66 0f 6f 05 70 3a 00 00 	movdqa 0x3a70(%rip),%xmm0        # 7aa0 <_IO_stdin_used+0xaa0>
    4030:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4035:	48 63 45 28          	movslq 0x28(%rbp),%rax
    y++;
    4039:	45 8d 44 24 01       	lea    0x1(%r12),%r8d
    for (int x = 0 ; x < data->thread_count ; x++) {
    403e:	85 c0                	test   %eax,%eax
    4040:	7e 4b                	jle    408d <timer_thread+0x1fd>
    4042:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4046:	4d 63 e4             	movslq %r12d,%r12
    4049:	49 c1 e4 09          	shl    $0x9,%r12
    404d:	48 8d 3c c1          	lea    (%rcx,%rax,8),%rdi
    4051:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4058:	48 8b 19             	mov    (%rcx),%rbx
    405b:	44 89 c0             	mov    %r8d,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    405e:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4062:	99                   	cltd
    4063:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4066:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    406a:	48 63 d2             	movslq %edx,%rdx
    406d:	48 c1 e2 09          	shl    $0x9,%rdx
    4071:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    407c:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4088:	48 39 cf             	cmp    %rcx,%rdi
    408b:	75 cb                	jne    4058 <timer_thread+0x1c8>
    asm volatile ("mfence" ::: "memory");
    408d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4090:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4094:	8b 4d 30             	mov    0x30(%rbp),%ecx
    y++;
    4097:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    409a:	48 8b 07             	mov    (%rdi),%rax
    y++;
    409d:	44 39 40 40          	cmp    %r8d,0x40(%rax)
    40a1:	45 0f 4f e0          	cmovg  %r8d,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    40a5:	85 c9                	test   %ecx,%ecx
    40a7:	0f 8e 0d 01 00 00    	jle    41ba <timer_thread+0x32a>
    40ad:	45 31 ff             	xor    %r15d,%r15d
    int all_empty = 1;
    40b0:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    40b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int y = 0 ; y < 2 ; y++) {
    40c0:	31 db                	xor    %ebx,%ebx
    40c2:	45 89 fd             	mov    %r15d,%r13d
    40c5:	4e 8d 34 fd 00 00 00 00 	lea    0x0(,%r15,8),%r14
    40cd:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    40cf:	85 c9                	test   %ecx,%ecx
    40d1:	0f 8e 91 00 00 00    	jle    4168 <timer_thread+0x2d8>
    40d7:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    40db:	4a 8b 14 37          	mov    (%rdi,%r14,1),%rdx
    40df:	48 89 d8             	mov    %rbx,%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    40e2:	45 31 c0             	xor    %r8d,%r8d
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    40e5:	48 c1 e0 09          	shl    $0x9,%rax
    40e9:	48 03 42 38          	add    0x38(%rdx),%rax
    40ed:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    40f4:	eb 1c                	jmp    4112 <timer_thread+0x282>
    40f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4100:	48 85 d2             	test   %rdx,%rdx
    4103:	7f 27                	jg     412c <timer_thread+0x29c>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4105:	41 83 c0 01          	add    $0x1,%r8d
    4109:	48 83 c0 28          	add    $0x28,%rax
    410d:	41 39 c8             	cmp    %ecx,%r8d
    4110:	74 7e                	je     4190 <timer_thread+0x300>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4112:	48 8b 10             	mov    (%rax),%rdx
    4115:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    411c:	48 8b 50 08          	mov    0x8(%rax),%rdx
    4120:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    4127:	4d 85 c9             	test   %r9,%r9
    412a:	7e d4                	jle    4100 <timer_thread+0x270>
    412c:	48 83 ec 08          	sub    $0x8,%rsp
    4130:	89 f1                	mov    %esi,%ecx
    4132:	bf 01 00 00 00       	mov    $0x1,%edi
    4137:	31 c0                	xor    %eax,%eax
    4139:	52                   	push   %rdx
    413a:	48 8d 35 1c 2f 00 00 	lea    0x2f1c(%rip),%rsi        # 705d <_IO_stdin_used+0x5d>
    4141:	44 89 ea             	mov    %r13d,%edx
    4144:	e8 07 e3 ff ff       	call   2450 <__printf_chk@plt>
      for (int y = 0 ; y < 2 ; y++) {
    4149:	5a                   	pop    %rdx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    414a:	8b 4d 30             	mov    0x30(%rbp),%ecx
      for (int y = 0 ; y < 2 ; y++) {
    414d:	5e                   	pop    %rsi
    414e:	48 83 fb 01          	cmp    $0x1,%rbx
    4152:	74 54                	je     41a8 <timer_thread+0x318>
    4154:	48 83 c3 01          	add    $0x1,%rbx
    4158:	45 31 db             	xor    %r11d,%r11d
    415b:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    415d:	85 c9                	test   %ecx,%ecx
    415f:	0f 8f 72 ff ff ff    	jg     40d7 <timer_thread+0x247>
    4165:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4168:	49 83 c7 01          	add    $0x1,%r15
    416c:	44 39 f9             	cmp    %r15d,%ecx
    416f:	0f 8f 4b ff ff ff    	jg     40c0 <timer_thread+0x230>
    if (all_empty == 1) {
    4175:	41 83 fb 01          	cmp    $0x1,%r11d
    4179:	74 3f                	je     41ba <timer_thread+0x32a>
      nanosleep(&drain , &drainrem);
    417b:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4180:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4185:	e8 c6 e1 ff ff       	call   2350 <nanosleep@plt>
    418a:	e9 a6 fe ff ff       	jmp    4035 <timer_thread+0x1a5>
    418f:	90                   	nop
      for (int y = 0 ; y < 2 ; y++) {
    4190:	48 83 fb 01          	cmp    $0x1,%rbx
    4194:	74 d2                	je     4168 <timer_thread+0x2d8>
    4196:	48 83 c3 01          	add    $0x1,%rbx
    419a:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    419c:	e9 3a ff ff ff       	jmp    40db <timer_thread+0x24b>
    41a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    41a8:	49 83 c7 01          	add    $0x1,%r15
    41ac:	45 31 db             	xor    %r11d,%r11d
    41af:	44 39 f9             	cmp    %r15d,%ecx
    41b2:	0f 8f 08 ff ff ff    	jg     40c0 <timer_thread+0x230>
    41b8:	eb bb                	jmp    4175 <timer_thread+0x2e5>
    41ba:	48 8d 3d 93 2e 00 00 	lea    0x2e93(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    41c1:	e8 2a e1 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    41c6:	8b 7d 44             	mov    0x44(%rbp),%edi
    41c9:	85 ff                	test   %edi,%edi
    41cb:	0f 84 ed 00 00 00    	je     42be <timer_thread+0x42e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    41d1:	8b 45 2c             	mov    0x2c(%rbp),%eax
    41d4:	31 db                	xor    %ebx,%ebx
    41d6:	4c 8d 25 97 2e 00 00 	lea    0x2e97(%rip),%r12        # 7074 <_IO_stdin_used+0x74>
    41dd:	4c 8d 2d ab 2e 00 00 	lea    0x2eab(%rip),%r13        # 708f <_IO_stdin_used+0x8f>
    41e4:	85 c0                	test   %eax,%eax
    41e6:	7e 3b                	jle    4223 <timer_thread+0x393>
    41e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    41f0:	31 c0                	xor    %eax,%eax
    41f2:	89 da                	mov    %ebx,%edx
    41f4:	4c 89 e6             	mov    %r12,%rsi
    41f7:	bf 01 00 00 00       	mov    $0x1,%edi
    41fc:	e8 4f e2 ff ff       	call   2450 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4201:	48 8b 45 18          	mov    0x18(%rbp),%rax
    4205:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4209:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    420d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4214:	0f 84 d1 00 00 00    	je     42eb <timer_thread+0x45b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    421a:	48 83 c3 01          	add    $0x1,%rbx
    421e:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    4221:	7f cd                	jg     41f0 <timer_thread+0x360>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4223:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    4227:	85 d2                	test   %edx,%edx
    4229:	7e 7d                	jle    42a8 <timer_thread+0x418>
      for (int y = 0 ; y < data->task_count ; y++) {
    422b:	8b 45 40             	mov    0x40(%rbp),%eax
    422e:	85 c0                	test   %eax,%eax
    4230:	7e 76                	jle    42a8 <timer_thread+0x418>
    4232:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4235:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    4239:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4241:	31 c9                	xor    %ecx,%ecx
    4243:	48 c1 e6 09          	shl    $0x9,%rsi
    4247:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4250:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4254:	48 8b 40 38          	mov    0x38(%rax),%rax
    4258:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    425c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4262:	74 1c                	je     4280 <timer_thread+0x3f0>
    4264:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    426e:	48 05 00 02 00 00    	add    $0x200,%rax
    4274:	48 39 d0             	cmp    %rdx,%rax
    4277:	74 26                	je     429f <timer_thread+0x40f>
    4279:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4280:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    428a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4290:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    429a:	48 39 d0             	cmp    %rdx,%rax
    429d:	75 e1                	jne    4280 <timer_thread+0x3f0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    429f:	48 83 c1 08          	add    $0x8,%rcx
    42a3:	48 39 f9             	cmp    %rdi,%rcx
    42a6:	75 a8                	jne    4250 <timer_thread+0x3c0>
    asm volatile ("mfence" ::: "memory");
    42a8:	0f ae f0             	mfence
    42ab:	48 8d 3d ef 2d 00 00 	lea    0x2def(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    42b2:	e8 39 e0 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    42b7:	c7 45 44 00 00 00 00 	movl   $0x0,0x44(%rbp)
    42be:	48 8d 3d e3 2d 00 00 	lea    0x2de3(%rip),%rdi        # 70a8 <_IO_stdin_used+0xa8>
    42c5:	e8 26 e0 ff ff       	call   22f0 <puts@plt>
}
    42ca:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    42cf:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    42d8:	75 40                	jne    431a <timer_thread+0x48a>
    42da:	48 83 c4 58          	add    $0x58,%rsp
    42de:	31 c0                	xor    %eax,%eax
    42e0:	5b                   	pop    %rbx
    42e1:	5d                   	pop    %rbp
    42e2:	41 5c                	pop    %r12
    42e4:	41 5d                	pop    %r13
    42e6:	41 5e                	pop    %r14
    42e8:	41 5f                	pop    %r15
    42ea:	c3                   	ret
    42eb:	4c 89 ef             	mov    %r13,%rdi
    42ee:	e8 fd df ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    42f3:	48 8b 45 18          	mov    0x18(%rbp),%rax
    42f7:	be 01 00 00 00       	mov    $0x1,%esi
    42fc:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4300:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4304:	8b 78 60             	mov    0x60(%rax),%edi
    4307:	e8 f4 e0 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    430c:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    430f:	0f 8f db fe ff ff    	jg     41f0 <timer_thread+0x360>
    4315:	e9 09 ff ff ff       	jmp    4223 <timer_thread+0x393>
}
    431a:	e8 11 e0 ff ff       	call   2330 <__stack_chk_fail@plt>
    431f:	90                   	nop

0000000000004320 <sendm.part.0>:
int sendm(struct BarrierTask *data) {
    4320:	41 57                	push   %r15
    4322:	41 56                	push   %r14
    4324:	41 55                	push   %r13
    4326:	41 54                	push   %r12
    4328:	55                   	push   %rbp
    4329:	53                   	push   %rbx
    432a:	48 8d 9f 88 01 00 00 	lea    0x188(%rdi),%rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    4331:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    4337:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    433c:	48 8d 9f 90 01 00 00 	lea    0x190(%rdi),%rbx
    4343:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    4348:	85 c0                	test   %eax,%eax
    434a:	0f 8e 59 01 00 00    	jle    44a9 <sendm.part.0+0x189>
    4350:	49 89 fe             	mov    %rdi,%r14
    4353:	45 31 e4             	xor    %r12d,%r12d
    4356:	45 31 ff             	xor    %r15d,%r15d
    4359:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    4360:	45 39 be 30 01 00 00 	cmp    %r15d,0x130(%r14)
    4367:	0f 84 2b 01 00 00    	je     4498 <sendm.part.0+0x178>
        struct Data *them = data->mailboxes[n].higher;
    436d:	4d 8b 86 70 01 00 00 	mov    0x170(%r14),%r8
    4374:	4d 01 e0             	add    %r12,%r8
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4377:	45 8b 48 20          	mov    0x20(%r8),%r9d
        struct Data *them = data->mailboxes[n].higher;
    437b:	49 8b 78 08          	mov    0x8(%r8),%rdi
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    437f:	41 83 f9 02          	cmp    $0x2,%r9d
    4383:	0f 84 2f 01 00 00    	je     44b8 <sendm.part.0+0x198>
        for (; them->messages_count < min;) {
    4389:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    4390:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    4397:	48 39 e9             	cmp    %rbp,%rcx
    439a:	0f 8d ee 00 00 00    	jge    448e <sendm.part.0+0x16e>
    43a0:	49 8b 86 08 01 00 00 	mov    0x108(%r14),%rax
    43a7:	48 39 e9             	cmp    %rbp,%rcx
    43aa:	49 89 eb             	mov    %rbp,%r11
          them->messages[them->messages_count++] = data->message; 
    43ad:	48 8b 17             	mov    (%rdi),%rdx
    43b0:	41 0f 9c c5          	setl   %r13b
    43b4:	49 29 cb             	sub    %rcx,%r11
    43b7:	48 89 44 24 d0       	mov    %rax,-0x30(%rsp)
    43bc:	49 8b 40 10          	mov    0x10(%r8),%rax
    43c0:	49 8d 5b ff          	lea    -0x1(%r11),%rbx
    43c4:	4c 89 5c 24 c8       	mov    %r11,-0x38(%rsp)
    43c9:	48 89 44 24 d8       	mov    %rax,-0x28(%rsp)
    43ce:	48 83 fb 02          	cmp    $0x2,%rbx
    43d2:	0f 86 98 01 00 00    	jbe    4570 <sendm.part.0+0x250>
    43d8:	45 84 ed             	test   %r13b,%r13b
    43db:	0f 84 8f 01 00 00    	je     4570 <sendm.part.0+0x250>
    43e1:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    43e9:	4a 8d 04 12          	lea    (%rdx,%r10,1),%rax
    43ed:	48 89 44 24 e0       	mov    %rax,-0x20(%rsp)
    43f2:	49 89 c3             	mov    %rax,%r11
    43f5:	48 8d 04 ea          	lea    (%rdx,%rbp,8),%rax
    43f9:	48 39 44 24 e8       	cmp    %rax,-0x18(%rsp)
    43fe:	0f 83 cc 00 00 00    	jae    44d0 <sendm.part.0+0x1b0>
    4404:	4c 89 d8             	mov    %r11,%rax
    4407:	4c 8b 5c 24 f0       	mov    -0x10(%rsp),%r11
    440c:	48 89 ce             	mov    %rcx,%rsi
    440f:	4c 39 d8             	cmp    %r11,%rax
    4412:	0f 83 b8 00 00 00    	jae    44d0 <sendm.part.0+0x1b0>
    4418:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4420:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    4427:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    442b:	48 83 c6 01          	add    $0x1,%rsi
    442f:	48 39 f5             	cmp    %rsi,%rbp
    4432:	7f ec                	jg     4420 <sendm.part.0+0x100>
    4434:	0f 1f 40 00          	nopl   0x0(%rax)
    4438:	31 f6                	xor    %esi,%esi
    443a:	45 84 ed             	test   %r13b,%r13b
    443d:	4c 8b 5c 24 d0       	mov    -0x30(%rsp),%r11
    4442:	48 0f 45 f3          	cmovne %rbx,%rsi
    4446:	4d 8d 5c 33 01       	lea    0x1(%r11,%rsi,1),%r11
    444b:	48 8d 4c 31 01       	lea    0x1(%rcx,%rsi,1),%rcx
    4450:	4d 89 9e 08 01 00 00 	mov    %r11,0x108(%r14)
    4457:	4c 8b 5c 24 d8       	mov    -0x28(%rsp),%r11
    445c:	4d 8d 5c 33 01       	lea    0x1(%r11,%rsi,1),%r11
    4461:	4d 89 58 10          	mov    %r11,0x10(%r8)
    4465:	48 89 8f 80 00 00 00 	mov    %rcx,0x80(%rdi)
    446c:	48 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%rcx
    4474:	bb 00 00 00 00       	mov    $0x0,%ebx
    4479:	48 0f 44 cb          	cmove  %rbx,%rcx
    447d:	4c 01 d2             	add    %r10,%rdx
    4480:	48 89 04 0a          	mov    %rax,(%rdx,%rcx,1)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4484:	41 83 f9 02          	cmp    $0x2,%r9d
    4488:	0f 84 c2 00 00 00    	je     4550 <sendm.part.0+0x230>
        asm volatile ("sfence" ::: "memory");
    448e:	0f ae f8             	sfence
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    4491:	41 8b 86 40 01 00 00 	mov    0x140(%r14),%eax
    4498:	41 83 c7 01          	add    $0x1,%r15d
    449c:	49 83 c4 28          	add    $0x28,%r12
    44a0:	41 39 c7             	cmp    %eax,%r15d
    44a3:	0f 8c b7 fe ff ff    	jl     4360 <sendm.part.0+0x40>
}
    44a9:	5b                   	pop    %rbx
    44aa:	5d                   	pop    %rbp
    44ab:	41 5c                	pop    %r12
    44ad:	41 5d                	pop    %r13
    44af:	41 5e                	pop    %r14
    44b1:	41 5f                	pop    %r15
    44b3:	c3                   	ret
    44b4:	0f 1f 40 00          	nopl   0x0(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    44b8:	8b 97 00 01 00 00    	mov    0x100(%rdi),%edx
    44be:	83 fa 01             	cmp    $0x1,%edx
    44c1:	0f 84 b9 00 00 00    	je     4580 <sendm.part.0+0x260>
        else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    44c7:	85 d2                	test   %edx,%edx
    44c9:	74 cd                	je     4498 <sendm.part.0+0x178>
    44cb:	e9 b9 fe ff ff       	jmp    4389 <sendm.part.0+0x69>
    44d0:	4c 8b 5c 24 c8       	mov    -0x38(%rsp),%r11
    44d5:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    44dc:	48 8b 74 24 e0       	mov    -0x20(%rsp),%rsi
    44e1:	49 d1 eb             	shr    %r11
    44e4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    44e9:	4c 89 dd             	mov    %r11,%rbp
    44ec:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    44f0:	48 c1 e5 04          	shl    $0x4,%rbp
    44f4:	49 89 eb             	mov    %rbp,%r11
    44f7:	48 01 f5             	add    %rsi,%rbp
    44fa:	41 83 e3 10          	and    $0x10,%r11d
    44fe:	74 11                	je     4511 <sendm.part.0+0x1f1>
          them->messages[them->messages_count++] = data->message; 
    4500:	0f 11 06             	movups %xmm0,(%rsi)
        for (; them->messages_count < min;) {
    4503:	48 83 c6 10          	add    $0x10,%rsi
    4507:	4c 8b 5c 24 c8       	mov    -0x38(%rsp),%r11
    450c:	48 39 f5             	cmp    %rsi,%rbp
    450f:	74 1a                	je     452b <sendm.part.0+0x20b>
    4511:	4c 8b 5c 24 c8       	mov    -0x38(%rsp),%r11
          them->messages[them->messages_count++] = data->message; 
    4516:	0f 11 06             	movups %xmm0,(%rsi)
    4519:	48 83 c6 20          	add    $0x20,%rsi
    451d:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
        for (; them->messages_count < min;) {
    4521:	48 39 f5             	cmp    %rsi,%rbp
    4524:	75 f0                	jne    4516 <sendm.part.0+0x1f6>
    4526:	4c 89 5c 24 c8       	mov    %r11,-0x38(%rsp)
    452b:	4c 89 de             	mov    %r11,%rsi
    452e:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    4532:	48 01 ce             	add    %rcx,%rsi
    4535:	41 83 e3 01          	and    $0x1,%r11d
    4539:	0f 84 f9 fe ff ff    	je     4438 <sendm.part.0+0x118>
          them->messages[them->messages_count++] = data->message; 
    453f:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    4546:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    454a:	e9 e9 fe ff ff       	jmp    4438 <sendm.part.0+0x118>
    454f:	90                   	nop
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4550:	83 bf 00 01 00 00 01 	cmpl   $0x1,0x100(%rdi)
    4557:	0f 85 31 ff ff ff    	jne    448e <sendm.part.0+0x16e>
          them->available = 0;
    455d:	c7 87 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdi)
    4567:	e9 22 ff ff ff       	jmp    448e <sendm.part.0+0x16e>
    456c:	0f 1f 40 00          	nopl   0x0(%rax)
          them->messages[them->messages_count++] = data->message; 
    4570:	48 89 ce             	mov    %rcx,%rsi
    4573:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    457b:	e9 a0 fe ff ff       	jmp    4420 <sendm.part.0+0x100>
        for (; them->messages_count < min;) {
    4580:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    4587:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    458e:	48 39 cd             	cmp    %rcx,%rbp
    4591:	0f 8f 09 fe ff ff    	jg     43a0 <sendm.part.0+0x80>
    4597:	eb c4                	jmp    455d <sendm.part.0+0x23d>
    4599:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000045a0 <strtolower>:
void strtolower(char *str) {
    45a0:	f3 0f 1e fa          	endbr64
    45a4:	55                   	push   %rbp
    45a5:	53                   	push   %rbx
    45a6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    45aa:	48 0f be 1f          	movsbq (%rdi),%rbx
    45ae:	84 db                	test   %bl,%bl
    45b0:	74 24                	je     45d6 <strtolower+0x36>
    45b2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    45b5:	e8 56 df ff ff       	call   2510 <__ctype_tolower_loc@plt>
    45ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    45c0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    45c3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    45c7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    45ca:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    45cd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    45d2:	84 db                	test   %bl,%bl
    45d4:	75 ea                	jne    45c0 <strtolower+0x20>
}
    45d6:	48 83 c4 08          	add    $0x8,%rsp
    45da:	5b                   	pop    %rbx
    45db:	5d                   	pop    %rbp
    45dc:	c3                   	ret
    45dd:	0f 1f 00             	nopl   (%rax)

00000000000045e0 <zh_malloc>:
void *zh_malloc(size_t size) {
    45e0:	f3 0f 1e fa          	endbr64
    45e4:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    45e8:	e8 23 de ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    45ed:	48 85 c0             	test   %rax,%rax
    45f0:	74 05                	je     45f7 <zh_malloc+0x17>
}
    45f2:	48 83 c4 08          	add    $0x8,%rsp
    45f6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    45f7:	48 8b 0d 22 5a 00 00 	mov    0x5a22(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    45fe:	ba 28 00 00 00       	mov    $0x28,%edx
    4603:	be 01 00 00 00       	mov    $0x1,%esi
    4608:	48 8d 3d d1 2e 00 00 	lea    0x2ed1(%rip),%rdi        # 74e0 <_IO_stdin_used+0x4e0>
    460f:	e8 ac de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4614:	bf 01 00 00 00       	mov    $0x1,%edi
    4619:	e8 82 de ff ff       	call   24a0 <exit@plt>
    461e:	66 90                	xchg   %ax,%ax

0000000000004620 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4620:	f3 0f 1e fa          	endbr64
    4624:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4625:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    462a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    462d:	e8 2e dd ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4632:	48 85 c0             	test   %rax,%rax
    4635:	74 11                	je     4648 <get_filename_ext+0x28>
    4637:	48 39 c3             	cmp    %rax,%rbx
    463a:	74 0c                	je     4648 <get_filename_ext+0x28>
    return dot + 1;
    463c:	48 83 c0 01          	add    $0x1,%rax
}
    4640:	5b                   	pop    %rbx
    4641:	c3                   	ret
    4642:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4648:	48 8d 05 a1 2a 00 00 	lea    0x2aa1(%rip),%rax        # 70f0 <_IO_stdin_used+0xf0>
}
    464f:	5b                   	pop    %rbx
    4650:	c3                   	ret
    4651:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    465c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004660 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4660:	f3 0f 1e fa          	endbr64
    4664:	41 55                	push   %r13
    4666:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4669:	48 89 fe             	mov    %rdi,%rsi
    466c:	41 54                	push   %r12
    466e:	55                   	push   %rbp
    466f:	48 89 d5             	mov    %rdx,%rbp
    4672:	ba 00 04 00 00       	mov    $0x400,%edx
    4677:	53                   	push   %rbx
    4678:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    467f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4688:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4690:	31 c0                	xor    %eax,%eax
    4692:	49 89 e4             	mov    %rsp,%r12
    4695:	4c 89 e7             	mov    %r12,%rdi
    4698:	e8 93 dd ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    469d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    46a2:	84 db                	test   %bl,%bl
    46a4:	74 24                	je     46ca <send_headers+0x6a>
        *str = (char)tolower(*str);
    46a6:	e8 65 de ff ff       	call   2510 <__ctype_tolower_loc@plt>
    46ab:	48 8b 08             	mov    (%rax),%rcx
    46ae:	4c 89 e0             	mov    %r12,%rax
    46b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    46b8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    46bb:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    46bf:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    46c2:	48 0f be 18          	movsbq (%rax),%rbx
    46c6:	84 db                	test   %bl,%bl
    46c8:	75 ee                	jne    46b8 <send_headers+0x58>
    void *buf = malloc(size);
    46ca:	bf 11 00 00 00       	mov    $0x11,%edi
    46cf:	e8 3c dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    46d4:	48 85 c0             	test   %rax,%rax
    46d7:	0f 84 7e 04 00 00    	je     4b5b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    46dd:	66 0f 6f 05 cb 33 00 00 	movdqa 0x33cb(%rip),%xmm0        # 7ab0 <_IO_stdin_used+0xab0>
    iov[0].iov_base = zh_malloc(slen);
    46e5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    46e9:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    46ee:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    46f6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    46fa:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    46fd:	e8 0e dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4702:	48 85 c0             	test   %rax,%rax
    4705:	0f 84 50 04 00 00    	je     4b5b <send_headers+0x4fb>
    470b:	66 0f 6f 05 ad 33 00 00 	movdqa 0x33ad(%rip),%xmm0        # 7ac0 <_IO_stdin_used+0xac0>
    iov[1].iov_base = zh_malloc(slen);
    4713:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4717:	4c 89 e7             	mov    %r12,%rdi
    471a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4724:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    472c:	0f 11 00             	movups %xmm0,(%rax)
    472f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4733:	be 2e 00 00 00       	mov    $0x2e,%esi
    4738:	e8 23 dc ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    473d:	48 85 c0             	test   %rax,%rax
    4740:	0f 84 ea 02 00 00    	je     4a30 <send_headers+0x3d0>
    4746:	4c 39 e0             	cmp    %r12,%rax
    4749:	0f 84 e1 02 00 00    	je     4a30 <send_headers+0x3d0>
    return dot + 1;
    474f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4753:	48 8d 3d 64 29 00 00 	lea    0x2964(%rip),%rdi        # 70be <_IO_stdin_used+0xbe>
    475a:	48 89 de             	mov    %rbx,%rsi
    475d:	e8 4e dc ff ff       	call   23b0 <strcmp@plt>
    4762:	85 c0                	test   %eax,%eax
    4764:	75 20                	jne    4786 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4766:	66 0f 6f 05 62 33 00 00 	movdqa 0x3362(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    476e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4776:	66 0f 6f 05 62 33 00 00 	movdqa 0x3362(%rip),%xmm0        # 7ae0 <_IO_stdin_used+0xae0>
    477e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4786:	48 89 de             	mov    %rbx,%rsi
    4789:	48 8d 3d 32 29 00 00 	lea    0x2932(%rip),%rdi        # 70c2 <_IO_stdin_used+0xc2>
    4790:	e8 1b dc ff ff       	call   23b0 <strcmp@plt>
    4795:	85 c0                	test   %eax,%eax
    4797:	75 20                	jne    47b9 <send_headers+0x159>
    4799:	66 0f 6f 05 2f 33 00 00 	movdqa 0x332f(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    47a1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    47a9:	66 0f 6f 05 2f 33 00 00 	movdqa 0x332f(%rip),%xmm0        # 7ae0 <_IO_stdin_used+0xae0>
    47b1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    47b9:	48 89 de             	mov    %rbx,%rsi
    47bc:	48 8d 3d 04 29 00 00 	lea    0x2904(%rip),%rdi        # 70c7 <_IO_stdin_used+0xc7>
    47c3:	e8 e8 db ff ff       	call   23b0 <strcmp@plt>
    47c8:	85 c0                	test   %eax,%eax
    47ca:	0f 84 10 02 00 00    	je     49e0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    47d0:	48 89 de             	mov    %rbx,%rsi
    47d3:	48 8d 3d f1 28 00 00 	lea    0x28f1(%rip),%rdi        # 70cb <_IO_stdin_used+0xcb>
    47da:	e8 d1 db ff ff       	call   23b0 <strcmp@plt>
    47df:	85 c0                	test   %eax,%eax
    47e1:	0f 84 a9 02 00 00    	je     4a90 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    47e7:	48 89 de             	mov    %rbx,%rsi
    47ea:	48 8d 3d de 28 00 00 	lea    0x28de(%rip),%rdi        # 70cf <_IO_stdin_used+0xcf>
    47f1:	e8 ba db ff ff       	call   23b0 <strcmp@plt>
    47f6:	85 c0                	test   %eax,%eax
    47f8:	0f 84 6a 02 00 00    	je     4a68 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    47fe:	48 89 de             	mov    %rbx,%rsi
    4801:	48 8d 3d 0a 29 00 00 	lea    0x290a(%rip),%rdi        # 7112 <_IO_stdin_used+0x112>
    4808:	e8 a3 db ff ff       	call   23b0 <strcmp@plt>
    480d:	85 c0                	test   %eax,%eax
    480f:	0f 84 2b 02 00 00    	je     4a40 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4815:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4818:	0f 84 52 01 00 00    	je     4970 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    481e:	48 89 de             	mov    %rbx,%rsi
    4821:	48 8d 3d ab 28 00 00 	lea    0x28ab(%rip),%rdi        # 70d3 <_IO_stdin_used+0xd3>
    4828:	e8 83 db ff ff       	call   23b0 <strcmp@plt>
    482d:	85 c0                	test   %eax,%eax
    482f:	0f 84 ab 02 00 00    	je     4ae0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4835:	48 89 de             	mov    %rbx,%rsi
    4838:	48 8d 3d 98 28 00 00 	lea    0x2898(%rip),%rdi        # 70d7 <_IO_stdin_used+0xd7>
    483f:	e8 6c db ff ff       	call   23b0 <strcmp@plt>
    4844:	85 c0                	test   %eax,%eax
    4846:	0f 84 6c 02 00 00    	je     4ab8 <send_headers+0x458>
    slen = strlen(send_buffer);
    484c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4854:	4c 89 e7             	mov    %r12,%rdi
    4857:	e8 c4 da ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    485c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    485f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4862:	e8 a9 db ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4867:	48 85 c0             	test   %rax,%rax
    486a:	0f 84 eb 02 00 00    	je     4b5b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4870:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4874:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4878:	83 fb 08             	cmp    $0x8,%ebx
    487b:	0f 83 3f 01 00 00    	jae    49c0 <send_headers+0x360>
    4881:	f6 c3 04             	test   $0x4,%bl
    4884:	0f 85 7b 02 00 00    	jne    4b05 <send_headers+0x4a5>
    488a:	85 db                	test   %ebx,%ebx
    488c:	74 13                	je     48a1 <send_headers+0x241>
    488e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4896:	88 10                	mov    %dl,(%rax)
    4898:	f6 c3 02             	test   $0x2,%bl
    489b:	0f 85 96 02 00 00    	jne    4b37 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    48a1:	4d 89 e8             	mov    %r13,%r8
    48a4:	48 8d 0d 30 28 00 00 	lea    0x2830(%rip),%rcx        # 70db <_IO_stdin_used+0xdb>
    48ab:	4c 89 e7             	mov    %r12,%rdi
    48ae:	31 c0                	xor    %eax,%eax
    48b0:	ba 00 04 00 00       	mov    $0x400,%edx
    48b5:	be 01 00 00 00       	mov    $0x1,%esi
    48ba:	e8 61 dc ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    48bf:	4c 89 e7             	mov    %r12,%rdi
    48c2:	e8 59 da ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    48c7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    48ca:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    48cd:	e8 3e db ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    48d2:	48 85 c0             	test   %rax,%rax
    48d5:	0f 84 80 02 00 00    	je     4b5b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    48db:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    48df:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    48e3:	83 fb 08             	cmp    $0x8,%ebx
    48e6:	0f 83 1c 01 00 00    	jae    4a08 <send_headers+0x3a8>
    48ec:	f6 c3 04             	test   $0x4,%bl
    48ef:	0f 85 29 02 00 00    	jne    4b1e <send_headers+0x4be>
    48f5:	85 db                	test   %ebx,%ebx
    48f7:	74 13                	je     490c <send_headers+0x2ac>
    48f9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4901:	88 10                	mov    %dl,(%rax)
    4903:	f6 c3 02             	test   $0x2,%bl
    4906:	0f 85 3d 02 00 00    	jne    4b49 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    490c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4911:	bf 02 00 00 00       	mov    $0x2,%edi
    4916:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    491e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4926:	e8 e5 da ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    492b:	48 85 c0             	test   %rax,%rax
    492e:	0f 84 27 02 00 00    	je     4b5b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4934:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    493c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4940:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4948:	66 89 10             	mov    %dx,(%rax)
}
    494b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4953:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    495c:	0f 85 20 02 00 00    	jne    4b82 <send_headers+0x522>
    4962:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4969:	5b                   	pop    %rbx
    496a:	5d                   	pop    %rbp
    496b:	41 5c                	pop    %r12
    496d:	41 5d                	pop    %r13
    496f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4970:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4974:	0f 85 a4 fe ff ff    	jne    481e <send_headers+0x1be>
    497a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    497e:	0f 85 9a fe ff ff    	jne    481e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4984:	66 0f 6f 05 a4 31 00 00 	movdqa 0x31a4(%rip),%xmm0        # 7b30 <_IO_stdin_used+0xb30>
    498c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4996:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    499e:	66 0f 6f 05 9a 31 00 00 	movdqa 0x319a(%rip),%xmm0        # 7b40 <_IO_stdin_used+0xb40>
    49a6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    49ae:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    49b6:	e9 63 fe ff ff       	jmp    481e <send_headers+0x1be>
    49bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    49c0:	89 da                	mov    %ebx,%edx
    49c2:	48 89 c7             	mov    %rax,%rdi
    49c5:	4c 89 e6             	mov    %r12,%rsi
    49c8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    49cd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    49d2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    49d5:	c1 e9 03             	shr    $0x3,%ecx
    49d8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    49db:	e9 c1 fe ff ff       	jmp    48a1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    49e0:	66 0f 6f 05 e8 30 00 00 	movdqa 0x30e8(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    49e8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    49f0:	66 0f 6f 05 f8 30 00 00 	movdqa 0x30f8(%rip),%xmm0        # 7af0 <_IO_stdin_used+0xaf0>
    49f8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a00:	e9 cb fd ff ff       	jmp    47d0 <send_headers+0x170>
    4a05:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4a08:	89 da                	mov    %ebx,%edx
    4a0a:	48 89 c7             	mov    %rax,%rdi
    4a0d:	4c 89 e6             	mov    %r12,%rsi
    4a10:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4a15:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4a1a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4a1d:	c1 e9 03             	shr    $0x3,%ecx
    4a20:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4a23:	e9 e4 fe ff ff       	jmp    490c <send_headers+0x2ac>
    4a28:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4a30:	48 8d 1d b9 26 00 00 	lea    0x26b9(%rip),%rbx        # 70f0 <_IO_stdin_used+0xf0>
    4a37:	e9 94 fd ff ff       	jmp    47d0 <send_headers+0x170>
    4a3c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a40:	66 0f 6f 05 c8 30 00 00 	movdqa 0x30c8(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4a48:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a50:	66 0f 6f 05 c8 30 00 00 	movdqa 0x30c8(%rip),%xmm0        # 7b20 <_IO_stdin_used+0xb20>
    4a58:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a60:	e9 b0 fd ff ff       	jmp    4815 <send_headers+0x1b5>
    4a65:	0f 1f 00             	nopl   (%rax)
    4a68:	66 0f 6f 05 a0 30 00 00 	movdqa 0x30a0(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4a70:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4a78:	66 0f 6f 05 a0 30 00 00 	movdqa 0x30a0(%rip),%xmm0        # 7b20 <_IO_stdin_used+0xb20>
    4a80:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4a88:	e9 71 fd ff ff       	jmp    47fe <send_headers+0x19e>
    4a8d:	0f 1f 00             	nopl   (%rax)
    4a90:	66 0f 6f 05 38 30 00 00 	movdqa 0x3038(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    4a98:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4aa0:	66 0f 6f 05 58 30 00 00 	movdqa 0x3058(%rip),%xmm0        # 7b00 <_IO_stdin_used+0xb00>
    4aa8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4ab0:	e9 32 fd ff ff       	jmp    47e7 <send_headers+0x187>
    4ab5:	0f 1f 00             	nopl   (%rax)
    4ab8:	66 0f 6f 05 50 30 00 00 	movdqa 0x3050(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4ac0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ac8:	66 0f 6f 05 90 30 00 00 	movdqa 0x3090(%rip),%xmm0        # 7b60 <_IO_stdin_used+0xb60>
    4ad0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4ad8:	e9 6f fd ff ff       	jmp    484c <send_headers+0x1ec>
    4add:	0f 1f 00             	nopl   (%rax)
    4ae0:	66 0f 6f 05 28 30 00 00 	movdqa 0x3028(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
    4ae8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4af0:	66 0f 6f 05 58 30 00 00 	movdqa 0x3058(%rip),%xmm0        # 7b50 <_IO_stdin_used+0xb50>
    4af8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4b00:	e9 30 fd ff ff       	jmp    4835 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4b05:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4b0c:	89 db                	mov    %ebx,%ebx
    4b0e:	89 10                	mov    %edx,(%rax)
    4b10:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4b15:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4b19:	e9 83 fd ff ff       	jmp    48a1 <send_headers+0x241>
    4b1e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4b25:	89 db                	mov    %ebx,%ebx
    4b27:	89 10                	mov    %edx,(%rax)
    4b29:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4b2e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4b32:	e9 d5 fd ff ff       	jmp    490c <send_headers+0x2ac>
    4b37:	89 db                	mov    %ebx,%ebx
    4b39:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4b3f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4b44:	e9 58 fd ff ff       	jmp    48a1 <send_headers+0x241>
    4b49:	89 db                	mov    %ebx,%ebx
    4b4b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4b51:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4b56:	e9 b1 fd ff ff       	jmp    490c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4b5b:	48 8b 0d be 54 00 00 	mov    0x54be(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4b62:	ba 28 00 00 00       	mov    $0x28,%edx
    4b67:	be 01 00 00 00       	mov    $0x1,%esi
    4b6c:	48 8d 3d 6d 29 00 00 	lea    0x296d(%rip),%rdi        # 74e0 <_IO_stdin_used+0x4e0>
    4b73:	e8 48 d9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4b78:	bf 01 00 00 00       	mov    $0x1,%edi
    4b7d:	e8 1e d9 ff ff       	call   24a0 <exit@plt>
}
    4b82:	e8 a9 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
    4b87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004b90 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4b90:	f3 0f 1e fa          	endbr64
    4b94:	41 55                	push   %r13
    4b96:	49 89 d5             	mov    %rdx,%r13
    4b99:	41 54                	push   %r12
    4b9b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    4b9e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4ba1:	55                   	push   %rbp
    4ba2:	53                   	push   %rbx
    4ba3:	48 89 f3             	mov    %rsi,%rbx
    4ba6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4baa:	e8 61 d8 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4baf:	48 85 c0             	test   %rax,%rax
    4bb2:	74 6b                	je     4c1f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4bb4:	4c 89 e7             	mov    %r12,%rdi
    4bb7:	48 89 c5             	mov    %rax,%rbp
    4bba:	31 f6                	xor    %esi,%esi
    4bbc:	31 c0                	xor    %eax,%eax
    4bbe:	e8 bd d8 ff ff       	call   2480 <open@plt>
    4bc3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4bc6:	85 c0                	test   %eax,%eax
    4bc8:	0f 88 88 d9 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4bce:	48 89 da             	mov    %rbx,%rdx
    4bd1:	48 89 ee             	mov    %rbp,%rsi
    4bd4:	89 c7                	mov    %eax,%edi
    4bd6:	e8 b5 d7 ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    4bdb:	48 98                	cltq
    4bdd:	48 39 d8             	cmp    %rbx,%rax
    4be0:	7c 1e                	jl     4c00 <copy_file_contents+0x70>
    close(fd);
    4be2:	44 89 e7             	mov    %r12d,%edi
    4be5:	e8 86 d7 ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    4bea:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    4bee:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4bf2:	48 83 c4 08          	add    $0x8,%rsp
    4bf6:	5b                   	pop    %rbx
    4bf7:	5d                   	pop    %rbp
    4bf8:	41 5c                	pop    %r12
    4bfa:	41 5d                	pop    %r13
    4bfc:	c3                   	ret
    4bfd:	0f 1f 00             	nopl   (%rax)
    4c00:	48 8b 0d 19 54 00 00 	mov    0x5419(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c07:	ba 1a 00 00 00       	mov    $0x1a,%edx
    4c0c:	be 01 00 00 00       	mov    $0x1,%esi
    4c11:	48 8d 3d d9 24 00 00 	lea    0x24d9(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4c18:	e8 a3 d8 ff ff       	call   24c0 <fwrite@plt>
    4c1d:	eb c3                	jmp    4be2 <copy_file_contents+0x52>
    4c1f:	48 8b 0d fa 53 00 00 	mov    0x53fa(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c26:	ba 28 00 00 00       	mov    $0x28,%edx
    4c2b:	be 01 00 00 00       	mov    $0x1,%esi
    4c30:	48 8d 3d a9 28 00 00 	lea    0x28a9(%rip),%rdi        # 74e0 <_IO_stdin_used+0x4e0>
    4c37:	e8 84 d8 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4c3c:	bf 01 00 00 00       	mov    $0x1,%edi
    4c41:	e8 5a d8 ff ff       	call   24a0 <exit@plt>
    4c46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004c50 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4c50:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4c54:	8b 46 44             	mov    0x44(%rsi),%eax
    4c57:	48 89 fa             	mov    %rdi,%rdx
    4c5a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    4c5d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4c63:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4c66:	48 8b 07             	mov    (%rdi),%rax
    4c69:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4c6c:	f6 c1 02             	test   $0x2,%cl
    4c6f:	74 00                	je     4c71 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4c71:	89 f0                	mov    %esi,%eax
    4c73:	44 29 c0             	sub    %r8d,%eax
    4c76:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4c79:	0f 82 e3 d8 ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4c7f:	c1 e9 0a             	shr    $0xa,%ecx
    4c82:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c86:	8b 47 44             	mov    0x44(%rdi),%eax
    4c89:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4c8c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    4c8f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4c92:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4c95:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c99:	d3 e0                	shl    %cl,%eax
    4c9b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    4c9e:	48 c1 e0 06          	shl    $0x6,%rax
    4ca2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4ca6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    4cac:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4caf:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4cb3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4cb9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4cc1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4cc5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4cc8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4ccf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4cd7:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    4cdb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    4cdf:	e8 5c d6 ff ff       	call   2340 <io_uring_submit@plt>
}
    4ce4:	31 c0                	xor    %eax,%eax
    4ce6:	48 83 c4 08          	add    $0x8,%rsp
    4cea:	c3                   	ret
    4ceb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004cf0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4cf0:	f3 0f 1e fa          	endbr64
    4cf4:	41 55                	push   %r13
    4cf6:	41 89 fd             	mov    %edi,%r13d
    4cf9:	41 54                	push   %r12
    4cfb:	55                   	push   %rbp
    4cfc:	53                   	push   %rbx
    4cfd:	48 89 f3             	mov    %rsi,%rbx
    4d00:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4d04:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4d07:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    4d0d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4d10:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4d13:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4d15:	f6 c1 02             	test   $0x2,%cl
    4d18:	74 00                	je     4d1a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    4d1a:	89 c2                	mov    %eax,%edx
    4d1c:	29 f2                	sub    %esi,%edx
    4d1e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4d21:	0f 82 4b d8 ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d27:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    4d2a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    4d2d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4d30:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4d35:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d38:	23 6b 58             	and    0x58(%rbx),%ebp
    4d3b:	d3 e5                	shl    %cl,%ebp
    4d3d:	48 c1 e5 06          	shl    $0x6,%rbp
    4d41:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4d45:	e8 c6 d6 ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    4d4a:	be 01 00 00 00       	mov    $0x1,%esi
    4d4f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4d54:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4d57:	e8 44 d6 ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    4d5c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4d61:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4d65:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4d68:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4d6d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4d72:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    4d7b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4d83:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4d87:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    4d8b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4d92:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    4d9a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    4d9e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4da6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    4dae:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4db2:	e8 89 d5 ff ff       	call   2340 <io_uring_submit@plt>
}
    4db7:	48 83 c4 08          	add    $0x8,%rsp
    4dbb:	31 c0                	xor    %eax,%eax
    4dbd:	5b                   	pop    %rbx
    4dbe:	5d                   	pop    %rbp
    4dbf:	41 5c                	pop    %r12
    4dc1:	41 5d                	pop    %r13
    4dc3:	c3                   	ret
    4dc4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4dcf:	90                   	nop

0000000000004dd0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4dd0:	f3 0f 1e fa          	endbr64
    4dd4:	41 56                	push   %r14
    4dd6:	41 89 f6             	mov    %esi,%r14d
    4dd9:	41 55                	push   %r13
    4ddb:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    4dde:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4de3:	41 54                	push   %r12
    4de5:	55                   	push   %rbp
    4de6:	48 89 d5             	mov    %rdx,%rbp
    4de9:	53                   	push   %rbx
    void *buf = malloc(size);
    4dea:	e8 21 d6 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4def:	48 85 c0             	test   %rax,%rax
    4df2:	0f 84 dd 00 00 00    	je     4ed5 <_send_static_string_content+0x105>
    4df8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    4dfb:	4c 89 ef             	mov    %r13,%rdi
    4dfe:	e8 1d d5 ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4e03:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    4e0a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    4e0e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4e11:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4e14:	e8 f7 d5 ff ff       	call   2410 <malloc@plt>
    4e19:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    4e1c:	48 85 c0             	test   %rax,%rax
    4e1f:	0f 84 b0 00 00 00    	je     4ed5 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4e25:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4e29:	4c 89 e2             	mov    %r12,%rdx
    4e2c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    4e2f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4e33:	e8 a8 d5 ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4e38:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e3b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4e41:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4e44:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4e48:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4e4a:	f6 c1 02             	test   $0x2,%cl
    4e4d:	0f 85 7d 00 00 00    	jne    4ed0 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4e53:	89 d0                	mov    %edx,%eax
    4e55:	29 f0                	sub    %esi,%eax
    4e57:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    4e5a:	0f 82 1c d7 ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4e60:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e63:	8b 45 44             	mov    0x44(%rbp),%eax
    4e66:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4e69:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    4e6c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4e6f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4e72:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4e78:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e7c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4e7e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4e81:	48 89 ef             	mov    %rbp,%rdi
    4e84:	48 c1 e0 06          	shl    $0x6,%rax
    4e88:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    4e8c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4e8f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4e93:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4e99:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4ea1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4ea5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4ea8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4eaf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4eb7:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    4ebb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    4ebf:	5b                   	pop    %rbx
    4ec0:	5d                   	pop    %rbp
    4ec1:	41 5c                	pop    %r12
    4ec3:	41 5d                	pop    %r13
    4ec5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4ec7:	e9 74 d4 ff ff       	jmp    2340 <io_uring_submit@plt>
    4ecc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4ed0:	e9 7e ff ff ff       	jmp    4e53 <_send_static_string_content+0x83>
    4ed5:	48 8b 0d 44 51 00 00 	mov    0x5144(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4edc:	ba 28 00 00 00       	mov    $0x28,%edx
    4ee1:	be 01 00 00 00       	mov    $0x1,%esi
    4ee6:	48 8d 3d f3 25 00 00 	lea    0x25f3(%rip),%rdi        # 74e0 <_IO_stdin_used+0x4e0>
    4eed:	e8 ce d5 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4ef2:	bf 01 00 00 00       	mov    $0x1,%edi
    4ef7:	e8 a4 d5 ff ff       	call   24a0 <exit@plt>
    4efc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004f00 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4f00:	f3 0f 1e fa          	endbr64
    4f04:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4f07:	89 fe                	mov    %edi,%esi
    4f09:	48 8b 3d 08 51 00 00 	mov    0x5108(%rip),%rdi        # a018 <unimplemented_content>
    4f10:	e9 bb fe ff ff       	jmp    4dd0 <_send_static_string_content>
    4f15:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004f20 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4f20:	f3 0f 1e fa          	endbr64
    4f24:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4f27:	89 fe                	mov    %edi,%esi
    4f29:	48 8b 3d e0 50 00 00 	mov    0x50e0(%rip),%rdi        # a010 <http_404_content>
    4f30:	e9 9b fe ff ff       	jmp    4dd0 <_send_static_string_content>
    4f35:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004f40 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4f40:	f3 0f 1e fa          	endbr64
    4f44:	41 56                	push   %r14
    4f46:	41 55                	push   %r13
    4f48:	49 89 d5             	mov    %rdx,%r13
    4f4b:	41 54                	push   %r12
    4f4d:	41 89 f4             	mov    %esi,%r12d
    4f50:	55                   	push   %rbp
    4f51:	48 89 fd             	mov    %rdi,%rbp
    4f54:	53                   	push   %rbx
    4f55:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    4f5c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4f65:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    4f6d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    4f6f:	e8 ac d3 ff ff       	call   2320 <strlen@plt>
    4f74:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4f79:	48 89 c3             	mov    %rax,%rbx
    4f7c:	0f 84 b6 00 00 00    	je     5038 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f82:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4f87:	48 89 ee             	mov    %rbp,%rsi
    4f8a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4f8e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4f93:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4f9b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4fa3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4fae:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4fb6:	e8 05 d4 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4fbb:	48 89 e6             	mov    %rsp,%rsi
    4fbe:	4c 89 f7             	mov    %r14,%rdi
    4fc1:	e8 0a d4 ff ff       	call   23d0 <stat@plt>
    4fc6:	83 f8 ff             	cmp    $0xffffffff,%eax
    4fc9:	0f 84 d3 00 00 00    	je     50a2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    4fcf:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4fd3:	25 00 f0 00 00       	and    $0xf000,%eax
    4fd8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4fdd:	0f 84 f5 00 00 00    	je     50d8 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4fe3:	48 8b 3d 26 50 00 00 	mov    0x5026(%rip),%rdi        # a010 <http_404_content>
    4fea:	4c 89 ea             	mov    %r13,%rdx
    4fed:	44 89 e6             	mov    %r12d,%esi
    4ff0:	e8 db fd ff ff       	call   4dd0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4ff5:	4c 89 f2             	mov    %r14,%rdx
    4ff8:	bf 01 00 00 00       	mov    $0x1,%edi
    4ffd:	31 c0                	xor    %eax,%eax
    4fff:	48 8d 35 3b 21 00 00 	lea    0x213b(%rip),%rsi        # 7141 <_IO_stdin_used+0x141>
    5006:	e8 45 d4 ff ff       	call   2450 <__printf_chk@plt>
}
    500b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5013:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    501c:	0f 85 20 01 00 00    	jne    5142 <handle_get_method+0x202>
    5022:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5029:	5b                   	pop    %rbx
    502a:	5d                   	pop    %rbp
    502b:	41 5c                	pop    %r12
    502d:	41 5d                	pop    %r13
    502f:	41 5e                	pop    %r14
    5031:	c3                   	ret
    5032:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5038:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    503d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5045:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    504a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    504d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5055:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5058:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5060:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    506b:	e8 50 d3 ff ff       	call   23c0 <__memcpy_chk@plt>
    5070:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5075:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    507a:	48 8d 35 8b 20 00 00 	lea    0x208b(%rip),%rsi        # 710c <_IO_stdin_used+0x10c>
    5081:	48 29 d9             	sub    %rbx,%rcx
    5084:	ba 0b 00 00 00       	mov    $0xb,%edx
    5089:	e8 32 d3 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    508e:	48 89 e6             	mov    %rsp,%rsi
    5091:	4c 89 f7             	mov    %r14,%rdi
    5094:	e8 37 d3 ff ff       	call   23d0 <stat@plt>
    5099:	83 f8 ff             	cmp    $0xffffffff,%eax
    509c:	0f 85 2d ff ff ff    	jne    4fcf <handle_get_method+0x8f>
    50a2:	4c 89 f2             	mov    %r14,%rdx
    50a5:	48 89 e9             	mov    %rbp,%rcx
    50a8:	48 8d 35 68 20 00 00 	lea    0x2068(%rip),%rsi        # 7117 <_IO_stdin_used+0x117>
    50af:	31 c0                	xor    %eax,%eax
    50b1:	bf 01 00 00 00       	mov    $0x1,%edi
    50b6:	e8 95 d3 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    50bb:	48 8b 3d 4e 4f 00 00 	mov    0x4f4e(%rip),%rdi        # a010 <http_404_content>
    50c2:	4c 89 ea             	mov    %r13,%rdx
    50c5:	44 89 e6             	mov    %r12d,%esi
    50c8:	e8 03 fd ff ff       	call   4dd0 <_send_static_string_content>
}
    50cd:	e9 39 ff ff ff       	jmp    500b <handle_get_method+0xcb>
    50d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    50d8:	bf 70 00 00 00       	mov    $0x70,%edi
    50dd:	e8 2e d3 ff ff       	call   2410 <malloc@plt>
    50e2:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    50e5:	48 85 c0             	test   %rax,%rax
    50e8:	74 5d                	je     5147 <handle_get_method+0x207>
            req->client_socket = client_socket;
    50ea:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    50ee:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    50f3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    50f7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    50fa:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    5101:	e8 5a f5 ff ff       	call   4660 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5106:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    510b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    510f:	4c 89 f7             	mov    %r14,%rdi
    5112:	e8 79 fa ff ff       	call   4b90 <copy_file_contents>
    5117:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    511c:	4c 89 f2             	mov    %r14,%rdx
    511f:	31 c0                	xor    %eax,%eax
    5121:	48 8d 35 07 20 00 00 	lea    0x2007(%rip),%rsi        # 712f <_IO_stdin_used+0x12f>
    5128:	bf 01 00 00 00       	mov    $0x1,%edi
    512d:	e8 1e d3 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    5132:	4c 89 ee             	mov    %r13,%rsi
    5135:	48 89 df             	mov    %rbx,%rdi
    5138:	e8 13 fb ff ff       	call   4c50 <add_write_request>
    513d:	e9 c9 fe ff ff       	jmp    500b <handle_get_method+0xcb>
}
    5142:	e8 e9 d1 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5147:	48 8b 0d d2 4e 00 00 	mov    0x4ed2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    514e:	ba 28 00 00 00       	mov    $0x28,%edx
    5153:	be 01 00 00 00       	mov    $0x1,%esi
    5158:	48 8d 3d 81 23 00 00 	lea    0x2381(%rip),%rdi        # 74e0 <_IO_stdin_used+0x4e0>
    515f:	e8 5c d3 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5164:	bf 01 00 00 00       	mov    $0x1,%edi
    5169:	e8 32 d3 ff ff       	call   24a0 <exit@plt>
    516e:	66 90                	xchg   %ax,%ax

0000000000005170 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5170:	f3 0f 1e fa          	endbr64
    5174:	41 57                	push   %r15
    5176:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5178:	4c 8d 35 27 1f 00 00 	lea    0x1f27(%rip),%r14        # 70a6 <_IO_stdin_used+0xa6>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    517f:	41 55                	push   %r13
    5181:	49 89 d5             	mov    %rdx,%r13
    5184:	41 54                	push   %r12
    5186:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    5189:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    518c:	55                   	push   %rbp
    518d:	53                   	push   %rbx
    518e:	48 83 ec 18          	sub    $0x18,%rsp
    5192:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    519b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    51a0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    51a2:	49 89 e7             	mov    %rsp,%r15
    51a5:	4c 89 fa             	mov    %r15,%rdx
    51a8:	e8 d3 d1 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    51ad:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    51b1:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    51b4:	84 db                	test   %bl,%bl
    51b6:	74 1d                	je     51d5 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    51b8:	e8 53 d3 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    51bd:	48 89 ea             	mov    %rbp,%rdx
    51c0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    51c3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    51c7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    51ca:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    51cd:	48 0f be 1a          	movsbq (%rdx),%rbx
    51d1:	84 db                	test   %bl,%bl
    51d3:	75 eb                	jne    51c0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    51d5:	4c 89 fa             	mov    %r15,%rdx
    51d8:	4c 89 f6             	mov    %r14,%rsi
    51db:	31 ff                	xor    %edi,%edi
    51dd:	e8 9e d1 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    51e2:	48 8d 35 6b 1f 00 00 	lea    0x1f6b(%rip),%rsi        # 7154 <_IO_stdin_used+0x154>
    51e9:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    51ec:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    51ef:	e8 bc d1 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    51f4:	4c 89 ea             	mov    %r13,%rdx
    51f7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    51fa:	85 c0                	test   %eax,%eax
    51fc:	75 2a                	jne    5228 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    51fe:	48 89 df             	mov    %rbx,%rdi
    5201:	e8 3a fd ff ff       	call   4f40 <handle_get_method>
}
    5206:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    520b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5214:	75 20                	jne    5236 <handle_http_method+0xc6>
    5216:	48 83 c4 18          	add    $0x18,%rsp
    521a:	5b                   	pop    %rbx
    521b:	5d                   	pop    %rbp
    521c:	41 5c                	pop    %r12
    521e:	41 5d                	pop    %r13
    5220:	41 5e                	pop    %r14
    5222:	41 5f                	pop    %r15
    5224:	c3                   	ret
    5225:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5228:	48 8b 3d e9 4d 00 00 	mov    0x4de9(%rip),%rdi        # a018 <unimplemented_content>
    522f:	e8 9c fb ff ff       	call   4dd0 <_send_static_string_content>
}
    5234:	eb d0                	jmp    5206 <handle_http_method+0x96>
    5236:	e8 f5 d0 ff ff       	call   2330 <__stack_chk_fail@plt>
    523b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005240 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5240:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5244:	85 d2                	test   %edx,%edx
    5246:	7e 38                	jle    5280 <get_line+0x40>
    5248:	48 63 d2             	movslq %edx,%rdx
    524b:	48 83 c7 01          	add    $0x1,%rdi
    524f:	48 01 f2             	add    %rsi,%rdx
    5252:	eb 11                	jmp    5265 <get_line+0x25>
    5254:	0f 1f 40 00          	nopl   0x0(%rax)
    5258:	48 83 c6 01          	add    $0x1,%rsi
    525c:	48 83 c7 01          	add    $0x1,%rdi
    5260:	48 39 d6             	cmp    %rdx,%rsi
    5263:	74 1b                	je     5280 <get_line+0x40>
        dest[i] = src[i];
    5265:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5269:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    526b:	3c 0d                	cmp    $0xd,%al
    526d:	75 e9                	jne    5258 <get_line+0x18>
    526f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5272:	75 e4                	jne    5258 <get_line+0x18>
            dest[i] = '\0';
    5274:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5277:	31 c0                	xor    %eax,%eax
    5279:	c3                   	ret
    527a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5280:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5285:	c3                   	ret
    5286:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005290 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    5290:	f3 0f 1e fa          	endbr64
    5294:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    529b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    529f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    52a8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    52b0:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    52b2:	49 89 e2             	mov    %rsp,%r10
    52b5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    52bd:	4c 89 d0             	mov    %r10,%rax
    52c0:	eb 13                	jmp    52d5 <handle_client_request+0x45>
    52c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    52c8:	48 83 c0 01          	add    $0x1,%rax
    52cc:	48 83 c1 01          	add    $0x1,%rcx
    52d0:	4c 39 c8             	cmp    %r9,%rax
    52d3:	74 4b                	je     5320 <handle_client_request+0x90>
        dest[i] = src[i];
    52d5:	44 0f b6 01          	movzbl (%rcx),%r8d
    52d9:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    52dc:	41 80 f8 0d          	cmp    $0xd,%r8b
    52e0:	75 e6                	jne    52c8 <handle_client_request+0x38>
    52e2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    52e6:	75 e0                	jne    52c8 <handle_client_request+0x38>
            dest[i] = '\0';
    52e8:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    52eb:	8b 47 08             	mov    0x8(%rdi),%eax
    52ee:	48 89 f2             	mov    %rsi,%rdx
    52f1:	4c 89 d7             	mov    %r10,%rdi
    52f4:	89 c6                	mov    %eax,%esi
    52f6:	e8 75 fe ff ff       	call   5170 <handle_http_method>
}
    52fb:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5303:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    530c:	75 39                	jne    5347 <handle_client_request+0xb7>
    530e:	31 c0                	xor    %eax,%eax
    5310:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5317:	c3                   	ret
    5318:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5320:	48 8b 0d f9 4c 00 00 	mov    0x4cf9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5327:	ba 12 00 00 00       	mov    $0x12,%edx
    532c:	be 01 00 00 00       	mov    $0x1,%esi
    5331:	48 8d 3d 20 1e 00 00 	lea    0x1e20(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    5338:	e8 83 d1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    533d:	bf 01 00 00 00       	mov    $0x1,%edi
    5342:	e8 59 d1 ff ff       	call   24a0 <exit@plt>
}
    5347:	e8 e4 cf ff ff       	call   2330 <__stack_chk_fail@plt>
    534c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005350 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5350:	f3 0f 1e fa          	endbr64
    5354:	55                   	push   %rbp
    5355:	53                   	push   %rbx
    5356:	48 89 cb             	mov    %rcx,%rbx
    5359:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    535d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5360:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5363:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5369:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    536c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    536f:	f6 c1 02             	test   $0x2,%cl
    5372:	74 00                	je     5374 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    5374:	41 89 c0             	mov    %eax,%r8d
    5377:	45 29 c8             	sub    %r9d,%r8d
    537a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    537e:	0f 82 08 d2 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5384:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5387:	8b 6b 44             	mov    0x44(%rbx),%ebp
    538a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    538d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5390:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5393:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5397:	d3 e5                	shl    %cl,%ebp
    5399:	48 c1 e5 06          	shl    $0x6,%rbp
    539d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    53a1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    53a4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    53a9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    53b0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    53b4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    53b8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    53c0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    53c8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    53cc:	e8 3f d0 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    53d1:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    53d4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    53da:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    53de:	48 83 c4 08          	add    $0x8,%rsp
    53e2:	5b                   	pop    %rbx
    53e3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    53e4:	e9 57 cf ff ff       	jmp    2340 <io_uring_submit@plt>
    53e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000053f0 <io_thread>:
void* io_thread(void *arg) {
    53f0:	f3 0f 1e fa          	endbr64
    53f4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    53f6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    53f8:	41 56                	push   %r14
    53fa:	41 55                	push   %r13
    53fc:	41 54                	push   %r12
    53fe:	55                   	push   %rbp
    53ff:	48 89 fd             	mov    %rdi,%rbp
    5402:	53                   	push   %rbx
    5403:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    540a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5413:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    541b:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    541f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5424:	bf 00 01 00 00       	mov    $0x100,%edi
    5429:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    542c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5430:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5435:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    543a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    543f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5444:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    544c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5451:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5459:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    545e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5466:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    546b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5473:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5478:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5480:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5485:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    548d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5495:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    549d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    54a5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    54ad:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    54b5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    54bd:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    54c5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    54cd:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    54d5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    54dd:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    54e4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    54ec:	e8 ff ce ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    54f1:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    54f5:	31 f6                	xor    %esi,%esi
    54f7:	e8 e4 cf ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    54fc:	31 d2                	xor    %edx,%edx
    54fe:	be 01 00 00 00       	mov    $0x1,%esi
    5503:	bf 02 00 00 00       	mov    $0x2,%edi
    5508:	e8 23 d0 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    550d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5510:	0f 84 b8 d0 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    5516:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    551b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5521:	89 c7                	mov    %eax,%edi
    5523:	41 89 c4             	mov    %eax,%r12d
    5526:	ba 02 00 00 00       	mov    $0x2,%edx
    552b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5530:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5538:	e8 c3 cd ff ff       	call   2300 <setsockopt@plt>
    553d:	85 c0                	test   %eax,%eax
    553f:	0f 88 5d d0 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5545:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    554a:	ba 10 00 00 00       	mov    $0x10,%edx
    554f:	44 89 e7             	mov    %r12d,%edi
    5552:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    555b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5563:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    556b:	e8 f0 ce ff ff       	call   2460 <bind@plt>
    5570:	85 c0                	test   %eax,%eax
    5572:	0f 88 62 d0 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5578:	be 0a 00 00 00       	mov    $0xa,%esi
    557d:	44 89 e7             	mov    %r12d,%edi
    5580:	e8 9b ce ff ff       	call   2420 <listen@plt>
    5585:	85 c0                	test   %eax,%eax
    5587:	0f 88 21 d0 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    558d:	ba db 18 00 00       	mov    $0x18db,%edx
    5592:	48 8d 35 04 1c 00 00 	lea    0x1c04(%rip),%rsi        # 719d <_IO_stdin_used+0x19d>
    5599:	bf 01 00 00 00       	mov    $0x1,%edi
    559e:	31 c0                	xor    %eax,%eax
    55a0:	e8 ab ce ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    55a5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    55aa:	48 89 d9             	mov    %rbx,%rcx
    55ad:	44 89 e7             	mov    %r12d,%edi
    55b0:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    55b5:	48 89 c6             	mov    %rax,%rsi
    55b8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    55bd:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    55c2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    55ca:	e8 81 fd ff ff       	call   5350 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    55cf:	bf 01 00 00 00       	mov    $0x1,%edi
    55d4:	be 10 00 00 00       	mov    $0x10,%esi
    55d9:	e8 c2 cd ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    55de:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    55e3:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    55e6:	e8 25 ce ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    55eb:	48 85 c0             	test   %rax,%rax
    55ee:	0f 84 ae 04 00 00    	je     5aa2 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    55f4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    55f8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    55ff:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5606:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    560e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5611:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5616:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5618:	f6 c1 02             	test   $0x2,%cl
    561b:	0f 85 0f 04 00 00    	jne    5a30 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5621:	89 d0                	mov    %edx,%eax
    5623:	29 f0                	sub    %esi,%eax
    5625:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    562c:	0f 82 92 cf ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5632:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5635:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5639:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    563d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5640:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5647:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    564a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5651:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5658:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    565a:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    565d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5662:	48 c1 e0 06          	shl    $0x6,%rax
    5666:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    566e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5674:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5677:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    567f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5683:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    568b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5693:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5697:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    569b:	e8 a0 cc ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    56a0:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    56a4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    56a9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    56b1:	0f 85 d7 01 00 00    	jne    588e <io_thread+0x49e>
    56b7:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    56bc:	4d 89 ce             	mov    %r9,%r14
    56bf:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    56c4:	0f 1f 40 00          	nopl   0x0(%rax)
    56c8:	48 8d 3d e4 1a 00 00 	lea    0x1ae4(%rip),%rdi        # 71b3 <_IO_stdin_used+0x1b3>
    56cf:	e8 1c cc ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    56d4:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    56db:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    56e2:	c1 e9 0b             	shr    $0xb,%ecx
    56e5:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    56e8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    56f0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    56f2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    56fa:	8b 16                	mov    (%rsi),%edx
		if (!available)
    56fc:	39 d0                	cmp    %edx,%eax
    56fe:	74 36                	je     5736 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5700:	89 f8                	mov    %edi,%eax
    5702:	21 d0                	and    %edx,%eax
    5704:	d3 e0                	shl    %cl,%eax
    5706:	48 c1 e0 04          	shl    $0x4,%rax
    570a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5712:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    571a:	0f 85 a8 01 00 00    	jne    58c8 <io_thread+0x4d8>
    5720:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5724:	0f 85 0e 03 00 00    	jne    5a38 <io_thread+0x648>
			if (cqe->res < 0)
    572a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    572d:	83 c2 01             	add    $0x1,%edx
    5730:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5732:	85 c0                	test   %eax,%eax
    5734:	79 b2                	jns    56e8 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5736:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    573f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5740:	45 31 c0             	xor    %r8d,%r8d
    5743:	31 d2                	xor    %edx,%edx
    5745:	b9 01 00 00 00       	mov    $0x1,%ecx
    574a:	4c 89 f6             	mov    %r14,%rsi
    574d:	48 89 df             	mov    %rbx,%rdi
    5750:	e8 eb cc ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5755:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5758:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    575d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5761:	0f 84 e1 02 00 00    	je     5a48 <io_thread+0x658>
    5767:	48 8d 3d 6b 1a 00 00 	lea    0x1a6b(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    576e:	e8 7d cb ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5773:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5778:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    577b:	45 85 ff             	test   %r15d,%r15d
    577e:	0f 88 12 ce ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    5784:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5787:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    578b:	85 c0                	test   %eax,%eax
    578d:	0f 88 d5 02 00 00    	js     5a68 <io_thread+0x678>
      switch (req->event_type) {
    5793:	41 83 f8 01          	cmp    $0x1,%r8d
    5797:	0f 84 7b 01 00 00    	je     5918 <io_thread+0x528>
    579d:	41 83 f8 02          	cmp    $0x2,%r8d
    57a1:	0f 84 a1 01 00 00    	je     5948 <io_thread+0x558>
    57a7:	45 85 c0             	test   %r8d,%r8d
    57aa:	0f 85 50 01 00 00    	jne    5900 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    57b0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    57b5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    57ba:	48 89 d9             	mov    %rbx,%rcx
    57bd:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    57c1:	e8 8a fb ff ff       	call   5350 <add_accept_request>
              add_read_request(cqe->res, &ring);
    57c6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    57cb:	48 89 de             	mov    %rbx,%rsi
    57ce:	8b 78 08             	mov    0x8(%rax),%edi
    57d1:	e8 1a f5 ff ff       	call   4cf0 <add_read_request>
              free(req);
    57d6:	4c 89 e7             	mov    %r12,%rdi
    57d9:	e8 e2 ca ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    57de:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    57e3:	48 85 c0             	test   %rax,%rax
    57e6:	0f 85 14 01 00 00    	jne    5900 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    57ec:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    57f3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    57fa:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    57fd:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5802:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5804:	f6 c1 02             	test   $0x2,%cl
    5807:	74 00                	je     5809 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5809:	89 d0                	mov    %edx,%eax
    580b:	29 f0                	sub    %esi,%eax
    580d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5814:	0f 82 a0 cd ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    581a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    581d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5822:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5826:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5829:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5830:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5833:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    583a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5841:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5843:	8b 55 60             	mov    0x60(%rbp),%edx
    5846:	48 c1 e0 06          	shl    $0x6,%rax
    584a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5852:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5858:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    585b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5863:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5867:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    586f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5877:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    587b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    587f:	e8 bc ca ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5884:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5888:	0f 84 3a fe ff ff    	je     56c8 <io_thread+0x2d8>
    588e:	48 8d 3d 7d 19 00 00 	lea    0x197d(%rip),%rdi        # 7212 <_IO_stdin_used+0x212>
    5895:	e8 56 ca ff ff       	call   22f0 <puts@plt>
}
    589a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    58a2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    58ab:	0f 85 18 02 00 00    	jne    5ac9 <io_thread+0x6d9>
    58b1:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    58b8:	31 c0                	xor    %eax,%eax
    58ba:	5b                   	pop    %rbx
    58bb:	5d                   	pop    %rbp
    58bc:	41 5c                	pop    %r12
    58be:	41 5d                	pop    %r13
    58c0:	41 5e                	pop    %r14
    58c2:	41 5f                	pop    %r15
    58c4:	c3                   	ret
    58c5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    58c8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    58cd:	48 85 c0             	test   %rax,%rax
    58d0:	0f 84 6a fe ff ff    	je     5740 <io_thread+0x350>
      if (cqe->user_data == 1) {
    58d6:	48 83 38 01          	cmpq   $0x1,(%rax)
    58da:	0f 84 68 01 00 00    	je     5a48 <io_thread+0x658>
    58e0:	48 8d 3d f2 18 00 00 	lea    0x18f2(%rip),%rdi        # 71d9 <_IO_stdin_used+0x1d9>
    58e7:	e8 04 ca ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    58ec:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    58f1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    58f4:	e9 8b fe ff ff       	jmp    5784 <io_thread+0x394>
    58f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5900:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5908:	8b 02                	mov    (%rdx),%eax
    590a:	83 c0 01             	add    $0x1,%eax
    590d:	89 02                	mov    %eax,(%rdx)
}
    590f:	e9 d8 fe ff ff       	jmp    57ec <io_thread+0x3fc>
    5914:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5918:	85 c0                	test   %eax,%eax
    591a:	75 74                	jne    5990 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    591c:	48 8b 0d fd 46 00 00 	mov    0x46fd(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5923:	ba 0f 00 00 00       	mov    $0xf,%edx
    5928:	be 01 00 00 00       	mov    $0x1,%esi
    592d:	48 8d 3d ce 18 00 00 	lea    0x18ce(%rip),%rdi        # 7202 <_IO_stdin_used+0x202>
    5934:	e8 87 cb ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5939:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    593e:	e9 a0 fe ff ff       	jmp    57e3 <io_thread+0x3f3>
    5943:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5948:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    594d:	45 31 ff             	xor    %r15d,%r15d
    5950:	85 c0                	test   %eax,%eax
    5952:	7e 20                	jle    5974 <io_thread+0x584>
    5954:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5958:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    595b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    595f:	48 c1 e0 04          	shl    $0x4,%rax
    5963:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5968:	e8 53 c9 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    596d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5972:	7f e4                	jg     5958 <io_thread+0x568>
              close(req->client_socket);
    5974:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5979:	e8 f2 c9 ff ff       	call   2370 <close@plt>
              free(req);
    597e:	4c 89 e7             	mov    %r12,%rdi
    5981:	e8 3a c9 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5986:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    598b:	e9 53 fe ff ff       	jmp    57e3 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5990:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5995:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    599a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    59a2:	eb 11                	jmp    59b5 <io_thread+0x5c5>
    59a4:	0f 1f 40 00          	nopl   0x0(%rax)
    59a8:	48 83 c0 01          	add    $0x1,%rax
    59ac:	48 83 c2 01          	add    $0x1,%rdx
    59b0:	48 39 c6             	cmp    %rax,%rsi
    59b3:	74 4b                	je     5a00 <io_thread+0x610>
        dest[i] = src[i];
    59b5:	0f b6 0a             	movzbl (%rdx),%ecx
    59b8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    59ba:	80 f9 0d             	cmp    $0xd,%cl
    59bd:	75 e9                	jne    59a8 <io_thread+0x5b8>
    59bf:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    59c3:	75 e3                	jne    59a8 <io_thread+0x5b8>
            dest[i] = '\0';
    59c5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    59c8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    59cd:	48 89 da             	mov    %rbx,%rdx
    59d0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    59d5:	e8 96 f7 ff ff       	call   5170 <handle_http_method>
              free(req->iov[0].iov_base);
    59da:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    59df:	e8 dc c8 ff ff       	call   22c0 <free@plt>
              free(req);
    59e4:	4c 89 e7             	mov    %r12,%rdi
    59e7:	e8 d4 c8 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    59ec:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    59f1:	e9 ed fd ff ff       	jmp    57e3 <io_thread+0x3f3>
    59f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5a00:	48 8b 0d 19 46 00 00 	mov    0x4619(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5a07:	ba 12 00 00 00       	mov    $0x12,%edx
    5a0c:	be 01 00 00 00       	mov    $0x1,%esi
    5a11:	48 8d 3d 40 17 00 00 	lea    0x1740(%rip),%rdi        # 7158 <_IO_stdin_used+0x158>
    5a18:	e8 a3 ca ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5a1d:	bf 01 00 00 00       	mov    $0x1,%edi
    5a22:	e8 79 ca ff ff       	call   24a0 <exit@plt>
    5a27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5a30:	e9 ec fb ff ff       	jmp    5621 <io_thread+0x231>
    5a35:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5a38:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    5a3d:	e9 94 fe ff ff       	jmp    58d6 <io_thread+0x4e6>
    5a42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5a48:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5a50:	48 8d 3d 6e 17 00 00 	lea    0x176e(%rip),%rdi        # 71c5 <_IO_stdin_used+0x1c5>
    5a57:	8b 02                	mov    (%rdx),%eax
    5a59:	83 c0 01             	add    $0x1,%eax
    5a5c:	89 02                	mov    %eax,(%rdx)
    5a5e:	e8 8d c8 ff ff       	call   22f0 <puts@plt>
    5a63:	e9 26 fe ff ff       	jmp    588e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5a68:	f7 d8                	neg    %eax
    5a6a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5a6f:	89 c7                	mov    %eax,%edi
    5a71:	e8 8a ca ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5a76:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5a7b:	be 01 00 00 00       	mov    $0x1,%esi
    5a80:	48 8b 3d 99 45 00 00 	mov    0x4599(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5a87:	48 89 c1             	mov    %rax,%rcx
    5a8a:	48 8d 15 7f 1a 00 00 	lea    0x1a7f(%rip),%rdx        # 7510 <_IO_stdin_used+0x510>
    5a91:	31 c0                	xor    %eax,%eax
    5a93:	e8 38 ca ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5a98:	bf 01 00 00 00       	mov    $0x1,%edi
    5a9d:	e8 fe c9 ff ff       	call   24a0 <exit@plt>
    5aa2:	48 8b 0d 77 45 00 00 	mov    0x4577(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5aa9:	ba 28 00 00 00       	mov    $0x28,%edx
    5aae:	be 01 00 00 00       	mov    $0x1,%esi
    5ab3:	48 8d 3d 26 1a 00 00 	lea    0x1a26(%rip),%rdi        # 74e0 <_IO_stdin_used+0x4e0>
    5aba:	e8 01 ca ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5abf:	bf 01 00 00 00       	mov    $0x1,%edi
    5ac4:	e8 d7 c9 ff ff       	call   24a0 <exit@plt>
}
    5ac9:	e8 62 c8 ff ff       	call   2330 <__stack_chk_fail@plt>
    5ace:	66 90                	xchg   %ax,%ax

0000000000005ad0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5ad0:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5ad4:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5adb:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5ae1:	85 c9                	test   %ecx,%ecx
    5ae3:	0f 8e ea 00 00 00    	jle    5bd3 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    5ae9:	41 56                	push   %r14
    5aeb:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5aed:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    5af0:	41 54                	push   %r12
    5af2:	49 89 fc             	mov    %rdi,%r12
    5af5:	55                   	push   %rbp
    5af6:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5af7:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5afb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5b00:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    5b04:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    5b0c:	31 db                	xor    %ebx,%ebx
    5b0e:	8b 10                	mov    (%rax),%edx
    5b10:	85 d2                	test   %edx,%edx
    5b12:	7e 26                	jle    5b3a <barriered_work_ingest+0x6a>
    5b14:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    5b18:	48 89 dd             	mov    %rbx,%rbp
    5b1b:	48 c1 e5 08          	shl    $0x8,%rbp
    5b1f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    5b23:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    5b2a:	74 24                	je     5b50 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5b2c:	48 83 c3 01          	add    $0x1,%rbx
    5b30:	39 da                	cmp    %ebx,%edx
    5b32:	7f e4                	jg     5b18 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5b34:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5b3a:	49 83 c5 01          	add    $0x1,%r13
    5b3e:	44 39 e9             	cmp    %r13d,%ecx
    5b41:	7f bd                	jg     5b00 <barriered_work_ingest+0x30>
}
    5b43:	5b                   	pop    %rbx
    5b44:	31 c0                	xor    %eax,%eax
    5b46:	5d                   	pop    %rbp
    5b47:	41 5c                	pop    %r12
    5b49:	41 5d                	pop    %r13
    5b4b:	41 5e                	pop    %r14
    5b4d:	c3                   	ret
    5b4e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    5b50:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5b59:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5b60:	bf 04 00 00 00       	mov    $0x4,%edi
    5b65:	48 c1 e6 05          	shl    $0x5,%rsi
    5b69:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5b70:	48 83 c6 10          	add    $0x10,%rsi
    5b74:	e8 97 c7 ff ff       	call   2310 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5b79:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5b81:	48 8b 40 50          	mov    0x50(%rax),%rax
    5b85:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5b89:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    5b8d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5b97:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    5b9d:	83 c0 01             	add    $0x1,%eax
    5ba0:	99                   	cltd
    5ba1:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5ba7:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    5bad:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5bb0:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5bb8:	48 83 c3 01          	add    $0x1,%rbx
    5bbc:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5bc0:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5bc4:	8b 10                	mov    (%rax),%edx
    5bc6:	39 da                	cmp    %ebx,%edx
    5bc8:	0f 8f 46 ff ff ff    	jg     5b14 <barriered_work_ingest+0x44>
    5bce:	e9 61 ff ff ff       	jmp    5b34 <barriered_work_ingest+0x64>
}
    5bd3:	31 c0                	xor    %eax,%eax
    5bd5:	c3                   	ret
    5bd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005be0 <barriered_thread>:
void* barriered_thread(void *arg) {
    5be0:	f3 0f 1e fa          	endbr64
    5be4:	41 56                	push   %r14
    5be6:	41 55                	push   %r13
    5be8:	41 54                	push   %r12
  int t = 0;
    5bea:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    5bed:	55                   	push   %rbp
  int waiting = 0;
    5bee:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    5bf0:	53                   	push   %rbx
    5bf1:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    5bf4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5bf8:	0f 85 74 02 00 00    	jne    5e72 <barriered_thread+0x292>
    if (t >= data->task_count) {
    5bfe:	8b 43 40             	mov    0x40(%rbx),%eax
    5c01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5c08:	41 39 c4             	cmp    %eax,%r12d
    5c0b:	0f 8d 6f 01 00 00    	jge    5d80 <barriered_thread+0x1a0>
    5c11:	49 63 fc             	movslq %r12d,%rdi
    5c14:	48 c1 e7 09          	shl    $0x9,%rdi
    5c18:	49 89 fd             	mov    %rdi,%r13
    5c1b:	eb 32                	jmp    5c4f <barriered_thread+0x6f>
    5c1d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5c20:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5c24:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5c28:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5c2c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5c30:	4c 01 ef             	add    %r13,%rdi
    5c33:	e8 98 fe ff ff       	call   5ad0 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    5c38:	8b 43 40             	mov    0x40(%rbx),%eax
    5c3b:	41 83 c4 01          	add    $0x1,%r12d
    5c3f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    5c46:	44 39 e0             	cmp    %r12d,%eax
    5c49:	0f 8e 19 02 00 00    	jle    5e68 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    5c4f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5c53:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    5c57:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    5c5e:	75 c0                	jne    5c20 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5c60:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    5c64:	83 e8 01             	sub    $0x1,%eax
    5c67:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    5c6c:	45 85 e4             	test   %r12d,%r12d
    5c6f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5c72:	45 85 c0             	test   %r8d,%r8d
    5c75:	0f 8e 2d 01 00 00    	jle    5da8 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5c7b:	48 63 c8             	movslq %eax,%rcx
    5c7e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5c82:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5c85:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5c8b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    5c92:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    5c96:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    5c99:	45 31 f6             	xor    %r14d,%r14d
    5c9c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5ca0:	48 8b 10             	mov    (%rax),%rdx
    5ca3:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    5ca7:	49 01 cb             	add    %rcx,%r11
    5caa:	4c 89 da             	mov    %r11,%rdx
    5cad:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    5cb4:	75 04                	jne    5cba <barriered_thread+0xda>
            arrived++;
    5cb6:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5cba:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    5cc0:	75 04                	jne    5cc6 <barriered_thread+0xe6>
            prearrive++;
    5cc2:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5cc6:	48 83 c0 08          	add    $0x8,%rax
    5cca:	48 39 c6             	cmp    %rax,%rsi
    5ccd:	75 d1                	jne    5ca0 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    5ccf:	45 85 d2             	test   %r10d,%r10d
    5cd2:	0f 84 c0 00 00 00    	je     5d98 <barriered_thread+0x1b8>
    5cd8:	45 39 d0             	cmp    %r10d,%r8d
    5cdb:	0f 84 b7 00 00 00    	je     5d98 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    5ce1:	45 85 f6             	test   %r14d,%r14d
    5ce4:	74 0a                	je     5cf0 <barriered_thread+0x110>
    5ce6:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    5cea:	0f 85 ae 01 00 00    	jne    5e9e <barriered_thread+0x2be>
    5cf0:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    5cf4:	4c 01 ea             	add    %r13,%rdx
    5cf7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    5cfe:	45 85 e4             	test   %r12d,%r12d
    5d01:	75 14                	jne    5d17 <barriered_thread+0x137>
    5d03:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5d0a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5d11:	0f 8c 69 01 00 00    	jl     5e80 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5d17:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    5d1b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    5d1f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    5d29:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    5d2d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5d31:	4c 01 ef             	add    %r13,%rdi
    5d34:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    5d3a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    5d3e:	4c 01 e8             	add    %r13,%rax
    5d41:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5d48:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    5d4b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5d50:	83 e8 01             	sub    $0x1,%eax
    5d53:	44 39 e0             	cmp    %r12d,%eax
    5d56:	0f 84 a4 00 00 00    	je     5e00 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    5d5c:	0f ae f8             	sfence
          if (waiting == 0) {
    5d5f:	85 ed                	test   %ebp,%ebp
    5d61:	0f 84 d1 00 00 00    	je     5e38 <barriered_thread+0x258>
        int arrived = 0; 
    5d67:	bd 01 00 00 00       	mov    $0x1,%ebp
    5d6c:	e9 c7 fe ff ff       	jmp    5c38 <barriered_thread+0x58>
  while (data->running == 1) {
    5d71:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5d75:	0f 85 f7 00 00 00    	jne    5e72 <barriered_thread+0x292>
    5d7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    5d80:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    5d88:	85 c0                	test   %eax,%eax
    5d8a:	7e e5                	jle    5d71 <barriered_thread+0x191>
    5d8c:	45 31 e4             	xor    %r12d,%r12d
    5d8f:	e9 7d fe ff ff       	jmp    5c11 <barriered_thread+0x31>
    5d94:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5d98:	83 fd 01             	cmp    $0x1,%ebp
    5d9b:	74 1b                	je     5db8 <barriered_thread+0x1d8>
        int arrived = 0; 
    5d9d:	31 ed                	xor    %ebp,%ebp
    5d9f:	e9 3d ff ff ff       	jmp    5ce1 <barriered_thread+0x101>
    5da4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5da8:	83 fd 01             	cmp    $0x1,%ebp
    5dab:	0f 85 43 ff ff ff    	jne    5cf4 <barriered_thread+0x114>
        int arrived = 0; 
    5db1:	45 31 f6             	xor    %r14d,%r14d
    5db4:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5db8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5dbf:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    5dc4:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5dc6:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5dca:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5dd1:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    5dd6:	e8 35 c5 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    5ddb:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5de2:	48 83 c0 01          	add    $0x1,%rax
    5de6:	48 99                	cqto
    5de8:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    5def:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    5df6:	e9 e6 fe ff ff       	jmp    5ce1 <barriered_thread+0x101>
    5dfb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5e00:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    5e07:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    5e0e:	0f 8d 48 ff ff ff    	jge    5d5c <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    5e14:	48 c1 e6 04          	shl    $0x4,%rsi
    5e18:	bf 04 00 00 00       	mov    $0x4,%edi
    5e1d:	48 03 73 70          	add    0x70(%rbx),%rsi
    5e21:	e8 ea c4 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    5e26:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    5e2e:	e9 29 ff ff ff       	jmp    5d5c <barriered_thread+0x17c>
    5e33:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    5e38:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5e3f:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    5e44:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5e48:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    5e4f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5e53:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5e57:	e8 b4 c4 ff ff       	call   2310 <clock_gettime@plt>
            waiting = 1;
    5e5c:	e9 06 ff ff ff       	jmp    5d67 <barriered_thread+0x187>
    5e61:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    5e68:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    5e6c:	0f 84 96 fd ff ff    	je     5c08 <barriered_thread+0x28>
}
    5e72:	5b                   	pop    %rbx
    5e73:	31 c0                	xor    %eax,%eax
    5e75:	5d                   	pop    %rbp
    5e76:	41 5c                	pop    %r12
    5e78:	41 5d                	pop    %r13
    5e7a:	41 5e                	pop    %r14
    5e7c:	c3                   	ret
    5e7d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    5e80:	48 c1 e6 04          	shl    $0x4,%rsi
    5e84:	bf 04 00 00 00       	mov    $0x4,%edi
    5e89:	48 03 73 68          	add    0x68(%rbx),%rsi
    5e8d:	e8 7e c4 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    5e92:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    5e96:	4c 01 ea             	add    %r13,%rdx
    5e99:	e9 79 fe ff ff       	jmp    5d17 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5e9e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    5ea2:	48 8b 43 18          	mov    0x18(%rbx),%rax
    5ea6:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5eaa:	48 8b 78 38          	mov    0x38(%rax),%rdi
    5eae:	4c 01 ef             	add    %r13,%rdi
    5eb1:	e8 1a fc ff ff       	call   5ad0 <barriered_work_ingest>
          break;
    5eb6:	e9 39 fd ff ff       	jmp    5bf4 <barriered_thread+0x14>
    5ebb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005ec0 <receive>:
int receive(struct BarrierTask *data) {
    5ec0:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5ec4:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    5eca:	85 c0                	test   %eax,%eax
    5ecc:	0f 8e 5c 01 00 00    	jle    602e <receive+0x16e>
int receive(struct BarrierTask *data) {
    5ed2:	41 57                	push   %r15
    5ed4:	48 89 fa             	mov    %rdi,%rdx
    5ed7:	41 56                	push   %r14
    5ed9:	41 55                	push   %r13
    5edb:	45 31 ed             	xor    %r13d,%r13d
    5ede:	41 54                	push   %r12
    5ee0:	45 31 e4             	xor    %r12d,%r12d
    5ee3:	55                   	push   %rbp
    5ee4:	53                   	push   %rbx
    5ee5:	48 83 ec 08          	sub    $0x8,%rsp
    5ee9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    struct Data *me = data->mailboxes[n].lower;
    5ef0:	48 8b b2 70 01 00 00 	mov    0x170(%rdx),%rsi
    5ef7:	4c 01 ee             	add    %r13,%rsi
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5efa:	44 8b 76 20          	mov    0x20(%rsi),%r14d
    struct Data *me = data->mailboxes[n].lower;
    5efe:	48 8b 2e             	mov    (%rsi),%rbp
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5f01:	41 83 fe 02          	cmp    $0x2,%r14d
    5f05:	0f 84 fd 00 00 00    	je     6008 <receive+0x148>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5f0b:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    5f12:	48 85 ff             	test   %rdi,%rdi
    5f15:	0f 8e 9b 00 00 00    	jle    5fb6 <receive+0xf6>
      data->sends++;
    5f1b:	4c 8b 8a 78 01 00 00 	mov    0x178(%rdx),%r9
      data->n++;
    5f22:	4c 8b 82 08 01 00 00 	mov    0x108(%rdx),%r8
      data->mailboxes[n].received++;
    5f29:	31 c0                	xor    %eax,%eax
    5f2b:	48 8b 4e 18          	mov    0x18(%rsi),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5f2f:	48 8b 5d 00          	mov    0x0(%rbp),%rbx
    5f33:	4d 8d 51 01          	lea    0x1(%r9),%r10
    5f37:	4c 63 5a 04          	movslq 0x4(%rdx),%r11
    5f3b:	4d 8d 48 01          	lea    0x1(%r8),%r9
    5f3f:	4c 8d 41 01          	lea    0x1(%rcx),%r8
    5f43:	eb 0c                	jmp    5f51 <receive+0x91>
    5f45:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5f48:	48 83 c0 01          	add    $0x1,%rax
    5f4c:	48 39 f8             	cmp    %rdi,%rax
    5f4f:	7d 5f                	jge    5fb0 <receive+0xf0>
      data->sends++;
    5f51:	49 8d 0c 02          	lea    (%r10,%rax,1),%rcx
    5f55:	48 89 8a 78 01 00 00 	mov    %rcx,0x178(%rdx)
      data->n++;
    5f5c:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    5f60:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5f67:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5f6b:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5f6f:	48 8b 0c c3          	mov    (%rbx,%rax,8),%rcx
    5f73:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5f77:	75 cf                	jne    5f48 <receive+0x88>
    5f79:	4c 63 ba 30 01 00 00 	movslq 0x130(%rdx),%r15
    5f80:	4c 39 79 08          	cmp    %r15,0x8(%rcx)
    5f84:	75 c2                	jne    5f48 <receive+0x88>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5f86:	bf 01 00 00 00       	mov    $0x1,%edi
    5f8b:	b9 01 00 00 00       	mov    $0x1,%ecx
    5f90:	ba 01 00 00 00       	mov    $0x1,%edx
    5f95:	31 c0                	xor    %eax,%eax
    5f97:	48 8d 35 9a 15 00 00 	lea    0x159a(%rip),%rsi        # 7538 <_IO_stdin_used+0x538>
    5f9e:	e8 ad c4 ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5fa3:	bf 01 00 00 00       	mov    $0x1,%edi
    5fa8:	e8 f3 c4 ff ff       	call   24a0 <exit@plt>
    5fad:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5fb0:	41 83 fe 02          	cmp    $0x2,%r14d
    5fb4:	74 3a                	je     5ff0 <receive+0x130>
    me->messages_count = 0;
    5fb6:	48 c7 85 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rbp)
    asm volatile ("sfence" ::: "memory");
    5fc1:	0f ae f8             	sfence
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5fc4:	8b 82 40 01 00 00    	mov    0x140(%rdx),%eax
    5fca:	41 83 c4 01          	add    $0x1,%r12d
    5fce:	49 83 c5 28          	add    $0x28,%r13
    5fd2:	41 39 c4             	cmp    %eax,%r12d
    5fd5:	0f 8c 15 ff ff ff    	jl     5ef0 <receive+0x30>
}
    5fdb:	48 83 c4 08          	add    $0x8,%rsp
    5fdf:	31 c0                	xor    %eax,%eax
    5fe1:	5b                   	pop    %rbx
    5fe2:	5d                   	pop    %rbp
    5fe3:	41 5c                	pop    %r12
    5fe5:	41 5d                	pop    %r13
    5fe7:	41 5e                	pop    %r14
    5fe9:	41 5f                	pop    %r15
    5feb:	c3                   	ret
    5fec:	0f 1f 40 00          	nopl   0x0(%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5ff0:	83 bd 00 01 00 00 01 	cmpl   $0x1,0x100(%rbp)
    5ff7:	75 bd                	jne    5fb6 <receive+0xf6>
      me->available = 0;
    5ff9:	c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbp)
    6003:	eb b1                	jmp    5fb6 <receive+0xf6>
    6005:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    6008:	8b 8d 00 01 00 00    	mov    0x100(%rbp),%ecx
    600e:	83 f9 01             	cmp    $0x1,%ecx
    6011:	74 09                	je     601c <receive+0x15c>
    else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 0) {
    6013:	85 c9                	test   %ecx,%ecx
    6015:	74 b3                	je     5fca <receive+0x10a>
    6017:	e9 ef fe ff ff       	jmp    5f0b <receive+0x4b>
    for (int x = 0 ; x < me->messages_count ; x++) {
    601c:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    6023:	48 85 ff             	test   %rdi,%rdi
    6026:	0f 8f ef fe ff ff    	jg     5f1b <receive+0x5b>
    602c:	eb cb                	jmp    5ff9 <receive+0x139>
}
    602e:	31 c0                	xor    %eax,%eax
    6030:	c3                   	ret
    6031:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    603c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006040 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    6040:	f3 0f 1e fa          	endbr64
    6044:	41 56                	push   %r14
    6046:	55                   	push   %rbp
    6047:	53                   	push   %rbx
    6048:	48 89 fb             	mov    %rdi,%rbx
  if (data->thread_index == data->task_index) {
    604b:	8b 47 04             	mov    0x4(%rdi),%eax
    604e:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    6054:	74 4a                	je     60a0 <barriered_work+0x60>
    receive(data);
    6056:	e8 65 fe ff ff       	call   5ec0 <receive>
    while (data->scheduled == 1) {
    605b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6062:	75 18                	jne    607c <barriered_work+0x3c>
    6064:	0f 1f 40 00          	nopl   0x0(%rax)
      data->n++;
    6068:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    6070:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6073:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    607a:	74 ec                	je     6068 <barriered_work+0x28>
  if (data->sending == 1) {
    607c:	83 bb 80 01 00 00 01 	cmpl   $0x1,0x180(%rbx)
    6083:	75 08                	jne    608d <barriered_work+0x4d>
    6085:	48 89 df             	mov    %rbx,%rdi
    6088:	e8 93 e2 ff ff       	call   4320 <sendm.part.0>
  asm volatile ("sfence" ::: "memory");
    608d:	0f ae f8             	sfence
}
    6090:	31 c0                	xor    %eax,%eax
    6092:	5b                   	pop    %rbx
    6093:	5d                   	pop    %rbp
    6094:	41 5e                	pop    %r14
    6096:	c3                   	ret
    6097:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      receive(data);
    60a0:	e8 1b fe ff ff       	call   5ec0 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    60a5:	48 63 8b 40 01 00 00 	movslq 0x140(%rbx),%rcx
        int t = data->task_index;
    60ac:	8b 43 04             	mov    0x4(%rbx),%eax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    60af:	85 c9                	test   %ecx,%ecx
    60b1:	0f 8e d6 00 00 00    	jle    618d <barriered_work+0x14d>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    60b7:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    60be:	4c 63 d0             	movslq %eax,%r10
              int next_task = abs((t + 1) % (data->thread_count));
    60c1:	83 c0 01             	add    $0x1,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    60c4:	49 c1 e2 09          	shl    $0x9,%r10
    60c8:	48 8b 72 20          	mov    0x20(%rdx),%rsi
              int next_task = abs((t + 1) % (data->thread_count));
    60cc:	99                   	cltd
    60cd:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    60d3:	48 8d 6e 38          	lea    0x38(%rsi),%rbp
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    60d7:	49 89 eb             	mov    %rbp,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    60da:	89 d0                	mov    %edx,%eax
    60dc:	f7 d8                	neg    %eax
    60de:	0f 49 d0             	cmovns %eax,%edx
    60e1:	48 8d 04 49          	lea    (%rcx,%rcx,2),%rax
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    60e5:	45 31 c0             	xor    %r8d,%r8d
    60e8:	48 c1 e0 06          	shl    $0x6,%rax
              int next_task = abs((t + 1) % (data->thread_count));
    60ec:	4c 63 ca             	movslq %edx,%r9
    60ef:	48 8d 74 06 38       	lea    0x38(%rsi,%rax,1),%rsi
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    60f4:	49 c1 e1 09          	shl    $0x9,%r9
    60f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6100:	49 8b 03             	mov    (%r11),%rax
    6103:	48 89 ea             	mov    %rbp,%rdx
    6106:	4a 8b 84 10 70 01 00 00 	mov    0x170(%rax,%r10,1),%rax
    610e:	48 83 c0 08          	add    $0x8,%rax
    6112:	eb 3d                	jmp    6151 <barriered_work+0x111>
    6114:	0f 1f 40 00          	nopl   0x0(%rax)
                 if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 0) {
    6118:	8b b9 00 01 00 00    	mov    0x100(%rcx),%edi
    611e:	85 ff                	test   %edi,%edi
    6120:	75 1f                	jne    6141 <barriered_work+0x101>
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    6122:	48 8b 3a             	mov    (%rdx),%rdi
    6125:	4e 8b b4 0f 70 01 00 00 	mov    0x170(%rdi,%r9,1),%r14
    612d:	4d 01 c6             	add    %r8,%r14
    6130:	49 89 0e             	mov    %rcx,(%r14)
                  ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available = 1;
    6133:	49 8b 4e 08          	mov    0x8(%r14),%rcx
    6137:	c7 81 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rcx)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6141:	48 81 c2 c0 00 00 00 	add    $0xc0,%rdx
    6148:	48 83 c0 28          	add    $0x28,%rax
    614c:	48 39 d6             	cmp    %rdx,%rsi
    614f:	74 28                	je     6179 <barriered_work+0x139>
              if (kind == MAILBOX_FRIEND) {
    6151:	83 78 18 01          	cmpl   $0x1,0x18(%rax)
                tmp = data->thread->all_threads[y].tasks[t].mailboxes[b].higher; 
    6155:	48 8b 08             	mov    (%rax),%rcx
              if (kind == MAILBOX_FRIEND) {
    6158:	75 be                	jne    6118 <barriered_work+0xd8>
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    615a:	48 8b 3a             	mov    (%rdx),%rdi
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    615d:	48 81 c2 c0 00 00 00 	add    $0xc0,%rdx
    6164:	48 83 c0 28          	add    $0x28,%rax
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    6168:	4a 8b bc 0f 70 01 00 00 	mov    0x170(%rdi,%r9,1),%rdi
    6170:	4a 89 0c 07          	mov    %rcx,(%rdi,%r8,1)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6174:	48 39 d6             	cmp    %rdx,%rsi
    6177:	75 d8                	jne    6151 <barriered_work+0x111>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6179:	49 81 c3 c0 00 00 00 	add    $0xc0,%r11
    6180:	49 83 c0 28          	add    $0x28,%r8
    6184:	4c 39 de             	cmp    %r11,%rsi
    6187:	0f 85 73 ff ff ff    	jne    6100 <barriered_work+0xc0>
      asm volatile ("sfence" ::: "memory");
    618d:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6190:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6197:	31 ff                	xor    %edi,%edi
    6199:	48 c1 e6 05          	shl    $0x5,%rsi
    619d:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    61a4:	e8 67 c1 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    61a9:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    61b0:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    61b7:	48 8b 50 48          	mov    0x48(%rax),%rdx
    61bb:	8b 72 10             	mov    0x10(%rdx),%esi
    61be:	8d 6e 01             	lea    0x1(%rsi),%ebp
    61c1:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    61c4:	75 5b                	jne    6221 <barriered_work+0x1e1>
    61c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    61d0:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    61d7:	48 8b 40 18          	mov    0x18(%rax),%rax
    61db:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
      data->n++;
    61df:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    61e7:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    61eb:	48 c1 e7 09          	shl    $0x9,%rdi
    61ef:	48 03 78 38          	add    0x38(%rax),%rdi
    61f3:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    61f9:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    61fc:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    6203:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    620a:	74 c4                	je     61d0 <barriered_work+0x190>
    if (modcount != data->thread->protected_state->modcount) {
    620c:	48 8b 40 48          	mov    0x48(%rax),%rax
    6210:	3b 68 10             	cmp    0x10(%rax),%ebp
    6213:	74 0c                	je     6221 <barriered_work+0x1e1>
    6215:	48 8d 3d 09 10 00 00 	lea    0x1009(%rip),%rdi        # 7225 <_IO_stdin_used+0x225>
    621c:	e8 cf c0 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6221:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6228:	31 ff                	xor    %edi,%edi
    622a:	48 c1 e6 05          	shl    $0x5,%rsi
    622e:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6235:	48 83 c6 10          	add    $0x10,%rsi
    6239:	e8 d2 c0 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    623e:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6245:	48 83 c0 01          	add    $0x1,%rax
    6249:	48 99                	cqto
    624b:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6252:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    6259:	e9 1e fe ff ff       	jmp    607c <barriered_work+0x3c>
    625e:	66 90                	xchg   %ax,%ax

0000000000006260 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6260:	f3 0f 1e fa          	endbr64
    6264:	53                   	push   %rbx
    6265:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6268:	e8 63 f8 ff ff       	call   5ad0 <barriered_work_ingest>
  barriered_work(data);
    626d:	48 89 df             	mov    %rbx,%rdi
}
    6270:	5b                   	pop    %rbx
  barriered_work(data);
    6271:	e9 ca fd ff ff       	jmp    6040 <barriered_work>
    6276:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006280 <sendm>:
int sendm(struct BarrierTask *data) {
    6280:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    6284:	83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%rdi)
    628b:	74 03                	je     6290 <sendm+0x10>
}
    628d:	31 c0                	xor    %eax,%eax
    628f:	c3                   	ret
int sendm(struct BarrierTask *data) {
    6290:	48 83 ec 08          	sub    $0x8,%rsp
    6294:	e8 87 e0 ff ff       	call   4320 <sendm.part.0>
}
    6299:	31 c0                	xor    %eax,%eax
    629b:	48 83 c4 08          	add    $0x8,%rsp
    629f:	c3                   	ret

00000000000062a0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    62a0:	f3 0f 1e fa          	endbr64
}
    62a4:	31 c0                	xor    %eax,%eax
    62a6:	c3                   	ret
    62a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000062b0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    62b0:	f3 0f 1e fa          	endbr64
    62b4:	31 c0                	xor    %eax,%eax
    62b6:	c3                   	ret
    62b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000062c0 <after>:
int after(struct timespec left, struct timespec right) {
    62c0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    62c4:	31 c0                	xor    %eax,%eax
    62c6:	48 39 d7             	cmp    %rdx,%rdi
    62c9:	7e 08                	jle    62d3 <after+0x13>
    62cb:	31 c0                	xor    %eax,%eax
    62cd:	48 39 ce             	cmp    %rcx,%rsi
    62d0:	0f 9f c0             	setg   %al
}
    62d3:	c3                   	ret
    62d4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    62df:	90                   	nop

00000000000062e0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    62e0:	f3 0f 1e fa          	endbr64
    62e4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    62e9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    62ee:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    62f0:	48 39 d7             	cmp    %rdx,%rdi
    62f3:	7f 18                	jg     630d <within+0x2d>
    62f5:	4d 39 d8             	cmp    %r11,%r8
    62f8:	0f 9e c2             	setle  %dl
    62fb:	48 39 ce             	cmp    %rcx,%rsi
    62fe:	0f 9e c0             	setle  %al
    6301:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6303:	31 c0                	xor    %eax,%eax
    6305:	4d 39 d1             	cmp    %r10,%r9
    6308:	0f 9e c0             	setle  %al
    630b:	21 d0                	and    %edx,%eax
}
    630d:	c3                   	ret
    630e:	66 90                	xchg   %ax,%ax

0000000000006310 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6310:	f3 0f 1e fa          	endbr64
    6314:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6319:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    631e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6323:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6328:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    632d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6332:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6337:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    633c:	48 39 fe             	cmp    %rdi,%rsi
    633f:	7d 2f                	jge    6370 <overlap+0x60>
    6341:	48 39 ca             	cmp    %rcx,%rdx
    6344:	7d 62                	jge    63a8 <overlap+0x98>
    6346:	4d 39 da             	cmp    %r11,%r10
    6349:	7d 0e                	jge    6359 <overlap+0x49>
    return 1;
    634b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6350:	4d 39 c1             	cmp    %r8,%r9
    6353:	0f 8c 7f 00 00 00    	jl     63d8 <overlap+0xc8>
  return 0;
    6359:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    635b:	4d 39 c1             	cmp    %r8,%r9
    635e:	7f 4c                	jg     63ac <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6360:	31 c0                	xor    %eax,%eax
    6362:	4d 39 da             	cmp    %r11,%r10
    6365:	0f 9e c0             	setle  %al
    6368:	c3                   	ret
    6369:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6370:	7e 4e                	jle    63c0 <overlap+0xb0>
    6372:	48 39 ca             	cmp    %rcx,%rdx
    6375:	7f 39                	jg     63b0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6377:	75 31                	jne    63aa <overlap+0x9a>
    6379:	4d 39 c1             	cmp    %r8,%r9
    637c:	7c 2c                	jl     63aa <overlap+0x9a>
    return 1;
    637e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6383:	4d 39 da             	cmp    %r11,%r10
    6386:	7d 24                	jge    63ac <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6388:	48 39 ca             	cmp    %rcx,%rdx
    638b:	0f 94 c2             	sete   %dl
    638e:	48 39 fe             	cmp    %rdi,%rsi
    6391:	0f 94 c0             	sete   %al
    6394:	21 c2                	and    %eax,%edx
    6396:	31 c0                	xor    %eax,%eax
    6398:	4d 39 c1             	cmp    %r8,%r9
    639b:	0f 94 c0             	sete   %al
    639e:	21 d0                	and    %edx,%eax
    63a0:	c3                   	ret
    63a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    63a8:	74 af                	je     6359 <overlap+0x49>
  return 0;
    63aa:	31 c0                	xor    %eax,%eax
}
    63ac:	c3                   	ret
    63ad:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    63b0:	4d 39 da             	cmp    %r11,%r10
    63b3:	7e c4                	jle    6379 <overlap+0x69>
    return 1;
    63b5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    63ba:	4d 39 c1             	cmp    %r8,%r9
    63bd:	7e ba                	jle    6379 <overlap+0x69>
    63bf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    63c0:	48 39 ca             	cmp    %rcx,%rdx
    63c3:	7c 94                	jl     6359 <overlap+0x49>
    63c5:	4d 39 c1             	cmp    %r8,%r9
    63c8:	7d b4                	jge    637e <overlap+0x6e>
    63ca:	48 39 ca             	cmp    %rcx,%rdx
    63cd:	74 91                	je     6360 <overlap+0x50>
    63cf:	eb d9                	jmp    63aa <overlap+0x9a>
    63d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    63d8:	c3                   	ret
    63d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000063e0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    63e0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    63e4:	85 f6                	test   %esi,%esi
    63e6:	0f 8e 44 03 00 00    	jle    6730 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    63ec:	41 57                	push   %r15
    63ee:	41 89 f7             	mov    %esi,%r15d
    63f1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    63f3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    63f6:	41 55                	push   %r13
    63f8:	41 54                	push   %r12
    63fa:	55                   	push   %rbp
    63fb:	53                   	push   %rbx
    63fc:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6400:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6404:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6409:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    640e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6411:	45 39 e6             	cmp    %r12d,%r14d
    6414:	0f 84 4e 02 00 00    	je     6668 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    641a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    641f:	8b 50 08             	mov    0x8(%rax),%edx
    6422:	85 d2                	test   %edx,%edx
    6424:	0f 8e 3e 02 00 00    	jle    6668 <verify+0x288>
    642a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    642f:	31 c9                	xor    %ecx,%ecx
    6431:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    6436:	31 c0                	xor    %eax,%eax
    6438:	44 89 f2             	mov    %r14d,%edx
    643b:	bf 01 00 00 00       	mov    $0x1,%edi
    6440:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6445:	48 8d 35 e9 0d 00 00 	lea    0xde9(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    644c:	e8 ff bf ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6451:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6456:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    645b:	8b 40 08             	mov    0x8(%rax),%eax
    645e:	85 c0                	test   %eax,%eax
    6460:	0f 8e e6 01 00 00    	jle    664c <verify+0x26c>
    6466:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6469:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    646e:	31 db                	xor    %ebx,%ebx
    6470:	48 c1 e0 09          	shl    $0x9,%rax
    6474:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6479:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    647e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6483:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6488:	4c 8b 20             	mov    (%rax),%r12
    648b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6490:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6495:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    649a:	49 89 de             	mov    %rbx,%r14
    649d:	48 8d 35 a6 0d 00 00 	lea    0xda6(%rip),%rsi        # 724a <_IO_stdin_used+0x24a>
    64a4:	49 c1 e6 09          	shl    $0x9,%r14
    64a8:	bf 01 00 00 00       	mov    $0x1,%edi
    64ad:	48 8b 45 00          	mov    0x0(%rbp),%rax
    64b1:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    64b9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    64be:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    64c6:	31 c0                	xor    %eax,%eax
    64c8:	e8 83 bf ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    64cd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    64d2:	4c 8b 20             	mov    (%rax),%r12
    64d5:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    64de:	0f 8e 47 01 00 00    	jle    662b <verify+0x24b>
    64e4:	4c 03 75 00          	add    0x0(%rbp),%r14
    64e8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    64ed:	ba 01 00 00 00       	mov    $0x1,%edx
    64f2:	4d 89 f5             	mov    %r14,%r13
    64f5:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    64fc:	4d 85 f6             	test   %r14,%r14
    64ff:	0f 8e 21 01 00 00    	jle    6626 <verify+0x246>
    6505:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6508:	48 89 d5             	mov    %rdx,%rbp
    650b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6510:	31 db                	xor    %ebx,%ebx
    6512:	4d 89 f2             	mov    %r14,%r10
    6515:	48 c1 e5 05          	shl    $0x5,%rbp
    6519:	48 83 ed 20          	sub    $0x20,%rbp
    651d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6521:	49 89 ee             	mov    %rbp,%r14
    6524:	48 89 dd             	mov    %rbx,%rbp
    6527:	48 89 d3             	mov    %rdx,%rbx
    652a:	eb 31                	jmp    655d <verify+0x17d>
    652c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6530:	4c 39 c2             	cmp    %r8,%rdx
    6533:	0f 8d 57 01 00 00    	jge    6690 <verify+0x2b0>
    6539:	4c 39 df             	cmp    %r11,%rdi
    653c:	7e 05                	jle    6543 <verify+0x163>
    653e:	49 39 c1             	cmp    %rax,%r9
    6541:	7c 75                	jl     65b8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6543:	4c 39 df             	cmp    %r11,%rdi
    6546:	0f 8d ab 01 00 00    	jge    66f7 <verify+0x317>
    654c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6550:	48 83 c5 01          	add    $0x1,%rbp
    6554:	49 39 ea             	cmp    %rbp,%r10
    6557:	0f 8e a9 00 00 00    	jle    6606 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    655d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    6564:	48 89 e8             	mov    %rbp,%rax
    6567:	48 c1 e0 05          	shl    $0x5,%rax
    656b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    6572:	4c 01 f2             	add    %r14,%rdx
    6575:	48 8b 08             	mov    (%rax),%rcx
    6578:	48 8b 78 10          	mov    0x10(%rax),%rdi
    657c:	48 8b 32             	mov    (%rdx),%rsi
    657f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6583:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6587:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    658b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    658f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6593:	48 39 f1             	cmp    %rsi,%rcx
    6596:	7c 98                	jl     6530 <verify+0x150>
    6598:	0f 8e 42 01 00 00    	jle    66e0 <verify+0x300>
    659e:	4c 39 c2             	cmp    %r8,%rdx
    65a1:	0f 8f f9 00 00 00    	jg     66a0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    65a7:	75 a7                	jne    6550 <verify+0x170>
    65a9:	4c 39 df             	cmp    %r11,%rdi
    65ac:	7f a2                	jg     6550 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    65ae:	49 39 c1             	cmp    %rax,%r9
    65b1:	7c 9d                	jl     6550 <verify+0x170>
    65b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    65b8:	49 89 c1             	mov    %rax,%r9
    65bb:	48 89 f9             	mov    %rdi,%rcx
    65be:	48 89 f2             	mov    %rsi,%rdx
    65c1:	bf 01 00 00 00       	mov    $0x1,%edi
    65c6:	48 8d 35 93 0f 00 00 	lea    0xf93(%rip),%rsi        # 7560 <_IO_stdin_used+0x560>
    65cd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    65cf:	48 83 c5 01          	add    $0x1,%rbp
    65d3:	e8 78 be ff ff       	call   2450 <__printf_chk@plt>
    65d8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    65dd:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    65e2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    65e5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    65ea:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    65f1:	4c 8b 20             	mov    (%rax),%r12
    65f4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    65f9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    65fd:	49 39 ea             	cmp    %rbp,%r10
    6600:	0f 8f 57 ff ff ff    	jg     655d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6606:	48 89 da             	mov    %rbx,%rdx
    6609:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    6610:	7d 14                	jge    6626 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6612:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    6619:	48 83 c2 01          	add    $0x1,%rdx
    661d:	4d 85 f6             	test   %r14,%r14
    6620:	0f 8f e2 fe ff ff    	jg     6508 <verify+0x128>
    6626:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    662b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6630:	48 83 c3 01          	add    $0x1,%rbx
    6634:	39 58 08             	cmp    %ebx,0x8(%rax)
    6637:	0f 8f 53 fe ff ff    	jg     6490 <verify+0xb0>
    663d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6642:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6647:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    664c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6651:	48 83 c1 01          	add    $0x1,%rcx
    6655:	39 48 08             	cmp    %ecx,0x8(%rax)
    6658:	0f 8f d8 fd ff ff    	jg     6436 <verify+0x56>
    665e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6663:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6668:	48 81 44 24 10 c0 00 00 00 	addq   $0xc0,0x10(%rsp)
    6671:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6676:	41 39 c7             	cmp    %eax,%r15d
    6679:	0f 84 86 00 00 00    	je     6705 <verify+0x325>
    667f:	41 89 c4             	mov    %eax,%r12d
    6682:	e9 8a fd ff ff       	jmp    6411 <verify+0x31>
    6687:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6690:	0f 85 ba fe ff ff    	jne    6550 <verify+0x170>
    6696:	e9 a8 fe ff ff       	jmp    6543 <verify+0x163>
    669b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    66a0:	49 39 c1             	cmp    %rax,%r9
    66a3:	7e 09                	jle    66ae <verify+0x2ce>
    66a5:	4c 39 df             	cmp    %r11,%rdi
    66a8:	0f 8c 0a ff ff ff    	jl     65b8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    66ae:	4c 39 df             	cmp    %r11,%rdi
    66b1:	0f 8f 99 fe ff ff    	jg     6550 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    66b7:	49 39 c1             	cmp    %rax,%r9
    66ba:	0f 8d f8 fe ff ff    	jge    65b8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    66c0:	48 39 f1             	cmp    %rsi,%rcx
    66c3:	0f 85 87 fe ff ff    	jne    6550 <verify+0x170>
    66c9:	4c 39 c2             	cmp    %r8,%rdx
    66cc:	0f 85 7e fe ff ff    	jne    6550 <verify+0x170>
    66d2:	4c 39 df             	cmp    %r11,%rdi
    66d5:	0f 84 dd fe ff ff    	je     65b8 <verify+0x1d8>
    66db:	e9 70 fe ff ff       	jmp    6550 <verify+0x170>
    66e0:	4c 39 c2             	cmp    %r8,%rdx
    66e3:	0f 8c 5a fe ff ff    	jl     6543 <verify+0x163>
    66e9:	4c 39 df             	cmp    %r11,%rdi
    66ec:	7e c9                	jle    66b7 <verify+0x2d7>
    66ee:	4c 39 c2             	cmp    %r8,%rdx
    66f1:	0f 85 59 fe ff ff    	jne    6550 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    66f7:	49 39 c1             	cmp    %rax,%r9
    66fa:	0f 8f 50 fe ff ff    	jg     6550 <verify+0x170>
    6700:	e9 b3 fe ff ff       	jmp    65b8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    6705:	48 81 44 24 18 c0 00 00 00 	addq   $0xc0,0x18(%rsp)
    670e:	41 8d 46 01          	lea    0x1(%r14),%eax
    6712:	45 39 e6             	cmp    %r12d,%r14d
    6715:	74 08                	je     671f <verify+0x33f>
    6717:	41 89 c6             	mov    %eax,%r14d
    671a:	e9 ea fc ff ff       	jmp    6409 <verify+0x29>
}
    671f:	48 83 c4 58          	add    $0x58,%rsp
    6723:	31 c0                	xor    %eax,%eax
    6725:	5b                   	pop    %rbx
    6726:	5d                   	pop    %rbp
    6727:	41 5c                	pop    %r12
    6729:	41 5d                	pop    %r13
    672b:	41 5e                	pop    %r14
    672d:	41 5f                	pop    %r15
    672f:	c3                   	ret
    6730:	31 c0                	xor    %eax,%eax
    6732:	c3                   	ret

Disassembly of section .fini:

0000000000006734 <_fini>:
    6734:	f3 0f 1e fa          	endbr64
    6738:	48 83 ec 08          	sub    $0x8,%rsp
    673c:	48 83 c4 08          	add    $0x8,%rsp
    6740:	c3                   	ret
