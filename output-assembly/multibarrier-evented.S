
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
    2605:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
    260c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2615:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    261a:	48 8d 05 9f 12 00 00 	lea    0x129f(%rip),%rax        # 38c0 <barriered_reset>
    2621:	66 48 0f 6e f0       	movq   %rax,%xmm6
    2626:	0f 16 35 4b 76 00 00 	movhps 0x764b(%rip),%xmm6        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    262d:	0f 29 74 24 40       	movaps %xmm6,0x40(%rsp)
    2632:	e8 b9 fc ff ff       	call   22f0 <puts@plt>
    2637:	bf 0a 00 00 00       	mov    $0xa,%edi
    263c:	e8 8f fc ff ff       	call   22d0 <putchar@plt>
    2641:	ba 02 00 00 00       	mov    $0x2,%edx
    2646:	48 8d 35 06 4c 00 00 	lea    0x4c06(%rip),%rsi        # 7253 <_IO_stdin_used+0x253>
    264d:	31 c0                	xor    %eax,%eax
    264f:	bf 01 00 00 00       	mov    $0x1,%edi
    2654:	e8 f7 fd ff ff       	call   2450 <__printf_chk@plt>
    2659:	48 8d 3d 08 4c 00 00 	lea    0x4c08(%rip),%rdi        # 7268 <_IO_stdin_used+0x268>
    2660:	e8 8b fc ff ff       	call   22f0 <puts@plt>
    2665:	ba 02 00 00 00       	mov    $0x2,%edx
    266a:	48 8d 35 13 4c 00 00 	lea    0x4c13(%rip),%rsi        # 7284 <_IO_stdin_used+0x284>
    2671:	31 c0                	xor    %eax,%eax
    2673:	bf 01 00 00 00       	mov    $0x1,%edi
    2678:	e8 d3 fd ff ff       	call   2450 <__printf_chk@plt>
    267d:	ba 06 00 00 00       	mov    $0x6,%edx
    2682:	48 8d 35 15 4c 00 00 	lea    0x4c15(%rip),%rsi        # 729e <_IO_stdin_used+0x29e>
    2689:	31 c0                	xor    %eax,%eax
    268b:	bf 01 00 00 00       	mov    $0x1,%edi
    2690:	e8 bb fd ff ff       	call   2450 <__printf_chk@plt>
    2695:	ba 01 00 00 00       	mov    $0x1,%edx
    269a:	48 8d 35 11 4c 00 00 	lea    0x4c11(%rip),%rsi        # 72b2 <_IO_stdin_used+0x2b2>
    26a1:	31 c0                	xor    %eax,%eax
    26a3:	bf 01 00 00 00       	mov    $0x1,%edi
    26a8:	e8 a3 fd ff ff       	call   2450 <__printf_chk@plt>
    26ad:	ba 01 00 00 00       	mov    $0x1,%edx
    26b2:	48 8d 35 0a 4c 00 00 	lea    0x4c0a(%rip),%rsi        # 72c3 <_IO_stdin_used+0x2c3>
    26b9:	31 c0                	xor    %eax,%eax
    26bb:	bf 01 00 00 00       	mov    $0x1,%edi
    26c0:	e8 8b fd ff ff       	call   2450 <__printf_chk@plt>
    26c5:	ba 02 00 00 00       	mov    $0x2,%edx
    26ca:	48 8d 35 0a 4c 00 00 	lea    0x4c0a(%rip),%rsi        # 72db <_IO_stdin_used+0x2db>
    26d1:	31 c0                	xor    %eax,%eax
    26d3:	bf 01 00 00 00       	mov    $0x1,%edi
    26d8:	e8 73 fd ff ff       	call   2450 <__printf_chk@plt>
    26dd:	ba 01 00 00 00       	mov    $0x1,%edx
    26e2:	48 8d 35 cf 4e 00 00 	lea    0x4ecf(%rip),%rsi        # 75b8 <_IO_stdin_used+0x5b8>
    26e9:	31 c0                	xor    %eax,%eax
    26eb:	bf 01 00 00 00       	mov    $0x1,%edi
    26f0:	e8 5b fd ff ff       	call   2450 <__printf_chk@plt>
    26f5:	ba 01 00 00 00       	mov    $0x1,%edx
    26fa:	48 8d 35 e7 4e 00 00 	lea    0x4ee7(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2701:	31 c0                	xor    %eax,%eax
    2703:	bf 01 00 00 00       	mov    $0x1,%edi
    2708:	e8 43 fd ff ff       	call   2450 <__printf_chk@plt>
    270d:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2712:	48 8d 35 de 4b 00 00 	lea    0x4bde(%rip),%rsi        # 72f7 <_IO_stdin_used+0x2f7>
    2719:	31 c0                	xor    %eax,%eax
    271b:	bf 01 00 00 00       	mov    $0x1,%edi
    2720:	e8 2b fd ff ff       	call   2450 <__printf_chk@plt>
    2725:	ba 05 00 00 00       	mov    $0x5,%edx
    272a:	48 8d 35 e0 4b 00 00 	lea    0x4be0(%rip),%rsi        # 7311 <_IO_stdin_used+0x311>
    2731:	31 c0                	xor    %eax,%eax
    2733:	bf 01 00 00 00       	mov    $0x1,%edi
    2738:	e8 13 fd ff ff       	call   2450 <__printf_chk@plt>
    273d:	48 8d 3d ab 49 00 00 	lea    0x49ab(%rip),%rdi        # 70ef <_IO_stdin_used+0xef>
    2744:	e8 a7 fb ff ff       	call   22f0 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2749:	be 18 00 00 00       	mov    $0x18,%esi
    274e:	bf 01 00 00 00       	mov    $0x1,%edi
    2753:	e8 48 fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2758:	be c0 00 00 00       	mov    $0xc0,%esi
    275d:	bf 06 00 00 00       	mov    $0x6,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2762:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2767:	e8 34 fc ff ff       	call   23a0 <calloc@plt>
    276c:	ba 02 00 00 00       	mov    $0x2,%edx
    2771:	bf 01 00 00 00       	mov    $0x1,%edi
    2776:	48 8d 35 a8 4b 00 00 	lea    0x4ba8(%rip),%rsi        # 7325 <_IO_stdin_used+0x325>
    277d:	48 89 c3             	mov    %rax,%rbx
    2780:	31 c0                	xor    %eax,%eax
    2782:	e8 c9 fc ff ff       	call   2450 <__printf_chk@plt>
    2787:	ba 04 00 00 00       	mov    $0x4,%edx
    278c:	48 8d 35 a8 4b 00 00 	lea    0x4ba8(%rip),%rsi        # 733b <_IO_stdin_used+0x33b>
    2793:	31 c0                	xor    %eax,%eax
    2795:	bf 01 00 00 00       	mov    $0x1,%edi
    279a:	e8 b1 fc ff ff       	call   2450 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    279f:	be 10 00 00 00       	mov    $0x10,%esi
    27a4:	bf 04 00 00 00       	mov    $0x4,%edi
    27a9:	e8 f2 fb ff ff       	call   23a0 <calloc@plt>
    27ae:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    27b3:	49 89 c5             	mov    %rax,%r13
    27b6:	48 8d 68 40          	lea    0x40(%rax),%rbp
    27ba:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27bf:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    27c4:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27cc:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    27d1:	49 83 c5 10          	add    $0x10,%r13
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27d5:	e8 c6 fb ff ff       	call   23a0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    27da:	be 20 00 00 00       	mov    $0x20,%esi
    27df:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27e4:	49 89 45 f8          	mov    %rax,-0x8(%r13)
    27e8:	49 89 c4             	mov    %rax,%r12
      buffers[x].buffer[y].available = 0;
    27eb:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    27f5:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    27ff:	e8 9c fb ff ff       	call   23a0 <calloc@plt>
    2804:	49 89 84 24 88 00 00 00 	mov    %rax,0x88(%r12)
  for (int x = 0 ; x < buffers_required; x++) {
    280c:	4c 39 ed             	cmp    %r13,%rbp
    280f:	75 ae                	jne    27bf <main+0x1cf>
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
        other = abs(x - 1) % total_threads;
        thread_data[x].thread_index = 1;
    2811:	48 8d 83 c0 00 00 00 	lea    0xc0(%rbx),%rax
    2818:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    281d:	49 89 de             	mov    %rbx,%r14
    2820:	45 31 ed             	xor    %r13d,%r13d
    2823:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2828:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    2831:	e9 bf 00 00 00       	jmp    28f5 <main+0x305>
            if (y == 0) {
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    2836:	48 8d 05 b3 33 00 00 	lea    0x33b3(%rip),%rax        # 5bf0 <barriered_work>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    283d:	bf 01 00 00 00       	mov    $0x1,%edi
    2842:	be 08 00 00 00       	mov    $0x8,%esi
    for (int d = 0 ; d < threads_per_group ; d++) {
    2847:	49 81 c6 c0 00 00 00 	add    $0xc0,%r14
               thread_data[x].tasks[y].run = barriered_work; 
    284e:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        thread_data[x].buffers_count = buffers_per_thread;
    2855:	41 c7 46 fc 01 00 00 00 	movl   $0x1,-0x4(%r14)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    285d:	e8 3e fb ff ff       	call   23a0 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2862:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    2867:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    286c:	49 89 46 90          	mov    %rax,-0x70(%r14)
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2870:	66 0f 6f 7c 24 40    	movdqa 0x40(%rsp),%xmm7
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2876:	48 8d 14 fb          	lea    (%rbx,%rdi,8),%rdx
    for (int d = 0 ; d < threads_per_group ; d++) {
    287a:	48 83 c7 02          	add    $0x2,%rdi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    287e:	48 89 10             	mov    %rdx,(%rax)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2881:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    2886:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    288b:	41 0f 11 bc 24 18 05 00 00 	movups %xmm7,0x518(%r12)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    2894:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    2897:	41 c7 84 24 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r12)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    28a3:	49 89 84 24 28 05 00 00 	mov    %rax,0x528(%r12)
        thread_data[x].tasks[barrier_count].available = 1; 
    28ab:	48 8b 05 b6 52 00 00 	mov    0x52b6(%rip),%rax        # 7b68 <_IO_stdin_used+0xb68>
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    28b2:	41 c7 84 24 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r12)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    28be:	41 c7 84 24 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r12)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    28ca:	45 89 bc 24 30 05 00 00 	mov    %r15d,0x530(%r12)
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    28d2:	41 c7 84 24 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r12)
        thread_data[x].tasks[barrier_count].available = 1; 
    28de:	49 89 84 24 44 05 00 00 	mov    %rax,0x544(%r12)
    for (int d = 0 ; d < threads_per_group ; d++) {
    28e6:	45 85 ed             	test   %r13d,%r13d
    28e9:	0f 85 63 05 00 00    	jne    2e52 <main+0x862>
    28ef:	41 bd 01 00 00 00    	mov    $0x1,%r13d
    28f5:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    28fa:	44 89 e9             	mov    %r13d,%ecx
    28fd:	31 d2                	xor    %edx,%edx
    28ff:	bf 01 00 00 00       	mov    $0x1,%edi
    2904:	48 8d 35 05 4d 00 00 	lea    0x4d05(%rip),%rsi        # 7610 <_IO_stdin_used+0x610>
    290b:	89 44 24 08          	mov    %eax,0x8(%rsp)
    290f:	41 89 c4             	mov    %eax,%r12d
    2912:	31 c0                	xor    %eax,%eax
    2914:	e8 37 fb ff ff       	call   2450 <__printf_chk@plt>
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2919:	be 08 00 00 00       	mov    $0x8,%esi
    291e:	bf 02 00 00 00       	mov    $0x2,%edi
    2923:	e8 78 fa ff ff       	call   23a0 <calloc@plt>
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2928:	be 80 00 00 00       	mov    $0x80,%esi
    292d:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2932:	48 89 c3             	mov    %rax,%rbx
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2935:	e8 66 fa ff ff       	call   23a0 <calloc@plt>
    293a:	49 89 c7             	mov    %rax,%r15
        thread_data[x].thread_index = 1;
    293d:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
      if (x % 2 == 1) {
    2942:	45 85 ed             	test   %r13d,%r13d
    2945:	0f 84 00 09 00 00    	je     324b <main+0xc5b>
        thread_data[x].protected_state = &protected_state[k];
    294b:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
        other = abs(x - 1) % total_threads;
    2950:	31 ed                	xor    %ebp,%ebp
        thread_data[x].thread_index = 1;
    2952:	c7 80 c4 00 00 00 01 00 00 00 	movl   $0x1,0xc4(%rax)
        thread_data[x].protected_state = &protected_state[k];
    295c:	48 89 b8 08 01 00 00 	mov    %rdi,0x108(%rax)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2963:	48 8d 43 08          	lea    0x8(%rbx),%rax
    2967:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    296c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2971:	45 8b 46 04          	mov    0x4(%r14),%r8d
    2975:	89 e9                	mov    %ebp,%ecx
    2977:	44 89 ea             	mov    %r13d,%edx
    297a:	48 8d 35 bf 4c 00 00 	lea    0x4cbf(%rip),%rsi        # 7640 <_IO_stdin_used+0x640>
    2981:	bf 01 00 00 00       	mov    $0x1,%edi
    2986:	48 89 43 08          	mov    %rax,0x8(%rbx)
    298a:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    298f:	48 89 03             	mov    %rax,(%rbx)
    2992:	31 c0                	xor    %eax,%eax
    2994:	e8 b7 fa ff ff       	call   2450 <__printf_chk@plt>
    2999:	44 89 ea             	mov    %r13d,%edx
    299c:	44 89 e1             	mov    %r12d,%ecx
    299f:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].other = other;
    29a4:	41 89 ae b8 00 00 00 	mov    %ebp,0xb8(%r14)
    29ab:	48 8d 35 be 4c 00 00 	lea    0x4cbe(%rip),%rsi        # 7670 <_IO_stdin_used+0x670>
    29b2:	31 c0                	xor    %eax,%eax
        for (int y = 0 ; y < total_barrier_count ; y++) {
    29b4:	31 ed                	xor    %ebp,%ebp
    29b6:	e8 95 fa ff ff       	call   2450 <__printf_chk@plt>
          CPU_SET(curcpu, sendercpu);
    29bb:	0f b6 4c 24 08       	movzbl 0x8(%rsp),%ecx
      thread_data[x].real_thread_index = x;
    29c0:	45 89 6e 08          	mov    %r13d,0x8(%r14)
          CPU_SET(curcpu, sendercpu);
    29c4:	b8 01 00 00 00       	mov    $0x1,%eax
      thread_data[x].threads = my_thread_data;
    29c9:	49 89 5e 18          	mov    %rbx,0x18(%r14)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    29cd:	be 10 00 00 00       	mov    $0x10,%esi
    29d2:	bf 64 00 00 00       	mov    $0x64,%edi
          CPU_SET(curcpu, sendercpu);
    29d7:	48 d3 e0             	shl    %cl,%rax
    29da:	49 09 07             	or     %rax,(%r15)
      thread_data[x].all_threads = thread_data;
    29dd:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
      thread_data[x].kind = KERNEL_THREAD;
    29e2:	41 c7 06 5f 00 00 00 	movl   $0x5f,(%r14)
      thread_data[x].all_threads = thread_data;
    29e9:	49 89 46 20          	mov    %rax,0x20(%r14)
      thread_data[x].thread_count = 2;
    29ed:	48 8b 05 6c 51 00 00 	mov    0x516c(%rip),%rax        # 7b60 <_IO_stdin_used+0xb60>
      thread_data[x].cpu_set = sendercpu;
    29f4:	4d 89 be b0 00 00 00 	mov    %r15,0xb0(%r14)
      thread_data[x].thread_count = 2;
    29fb:	49 89 46 28          	mov    %rax,0x28(%r14)
      thread_data[x].task_count = total_barrier_count;
    29ff:	41 c7 46 40 03 00 00 00 	movl   $0x3,0x40(%r14)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a07:	e8 94 f9 ff ff       	call   23a0 <calloc@plt>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a0c:	be 10 00 00 00       	mov    $0x10,%esi
    2a11:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2a16:	49 89 46 68          	mov    %rax,0x68(%r14)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a1a:	e8 81 f9 ff ff       	call   23a0 <calloc@plt>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a1f:	be 28 00 00 00       	mov    $0x28,%esi
    2a24:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].timestamp_count = 0;
    2a29:	66 0f 6f 05 ff 50 00 00 	movdqa 0x50ff(%rip),%xmm0        # 7b30 <_IO_stdin_used+0xb30>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2a31:	49 89 46 70          	mov    %rax,0x70(%r14)
      thread_data[x].timestamp_count = 0;
    2a35:	41 0f 11 86 80 00 00 00 	movups %xmm0,0x80(%r14)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a3d:	e8 5e f9 ff ff       	call   23a0 <calloc@plt>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a42:	be 00 02 00 00       	mov    $0x200,%esi
    2a47:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2a4c:	66 0f 6f 0d dc 50 00 00 	movdqa 0x50dc(%rip),%xmm1        # 7b30 <_IO_stdin_used+0xb30>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2a54:	49 89 86 90 00 00 00 	mov    %rax,0x90(%r14)
      thread_data[x].task_timestamp_count = 0;
    2a5b:	41 0f 11 8e 98 00 00 00 	movups %xmm1,0x98(%r14)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a63:	e8 38 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks = barriers;
    2a68:	49 89 46 38          	mov    %rax,0x38(%r14)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2a6c:	49 89 c4             	mov    %rax,%r12
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a6f:	4c 63 fd             	movslq %ebp,%r15
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2a72:	be 28 00 00 00       	mov    $0x28,%esi
    2a77:	bf 02 00 00 00       	mov    $0x2,%edi
          thread_data[x].tasks[y].protected = do_protected_write; 
    2a7c:	4c 89 fb             	mov    %r15,%rbx
    2a7f:	48 8d 05 fa 0d 00 00 	lea    0xdfa(%rip),%rax        # 3880 <do_protected_write>
    2a86:	48 c1 e3 09          	shl    $0x9,%rbx
    2a8a:	49 8d 14 1c          	lea    (%r12,%rbx,1),%rdx
    2a8e:	48 89 82 20 01 00 00 	mov    %rax,0x120(%rdx)
    2a95:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2a9a:	e8 01 f9 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2a9f:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2aa4:	49 89 c4             	mov    %rax,%r12
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2aa7:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
            if ( b == x || b == x + 1) {
    2aae:	45 85 ed             	test   %r13d,%r13d
    2ab1:	0f 84 63 02 00 00    	je     2d1a <main+0x72a>
    2ab7:	ba 01 00 00 00       	mov    $0x1,%edx
    2abc:	48 8d 35 92 48 00 00 	lea    0x4892(%rip),%rsi        # 7355 <_IO_stdin_used+0x355>
    2ac3:	bf 01 00 00 00       	mov    $0x1,%edi
    2ac8:	31 c0                	xor    %eax,%eax
    2aca:	e8 81 f9 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2acf:	be 08 00 00 00       	mov    $0x8,%esi
    2ad4:	bf 01 00 00 00       	mov    $0x1,%edi
    2ad9:	e8 c2 f8 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ade:	be 08 00 00 00       	mov    $0x8,%esi
    2ae3:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ae8:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2aed:	e8 ae f8 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2af2:	be 80 01 00 00       	mov    $0x180,%esi
    2af7:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2afc:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    2b01:	e8 9a f8 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    2b06:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
              data[1].messages = messages2;
    2b0b:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    2b10:	41 c7 44 24 48 01 00 00 00 	movl   $0x1,0x48(%r12)
              mailboxes[b].higher = &data[1];
    2b19:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    2b20:	49 89 44 24 28       	mov    %rax,0x28(%r12)
    2b25:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages_count = 0;
    2b2a:	66 0f 6f 0d 0e 50 00 00 	movdqa 0x500e(%rip),%xmm1        # 7b40 <_IO_stdin_used+0xb40>
              data[0].messages = messages;
    2b32:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    2b35:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
    2b3c:	31 d2                	xor    %edx,%edx
              mailboxes[b].higher = &data[1];
    2b3e:	49 89 74 24 30       	mov    %rsi,0x30(%r12)
    2b43:	48 8d 35 3e 49 00 00 	lea    0x493e(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
              data[0].messages_count = 0;
    2b4a:	0f 29 88 80 00 00 00 	movaps %xmm1,0x80(%rax)
              data[1].messages_count = 0;
    2b51:	0f 29 88 00 02 00 00 	movaps %xmm1,0x200(%rax)
    2b58:	31 c0                	xor    %eax,%eax
    2b5a:	e8 f1 f8 ff ff       	call   2450 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b5f:	be 08 00 00 00       	mov    $0x8,%esi
    2b64:	bf 01 00 00 00       	mov    $0x1,%edi
    2b69:	e8 32 f8 ff ff       	call   23a0 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b6e:	be 08 00 00 00       	mov    $0x8,%esi
    2b73:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2b78:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b7d:	e8 1e f8 ff ff       	call   23a0 <calloc@plt>
            struct Data *data = calloc(2, sizeof(struct Data));
    2b82:	be 80 01 00 00       	mov    $0x180,%esi
    2b87:	bf 02 00 00 00       	mov    $0x2,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2b8c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
            struct Data *data = calloc(2, sizeof(struct Data));
    2b91:	e8 0a f8 ff ff       	call   23a0 <calloc@plt>
            data[0].messages = messages;
    2b96:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
            data[1].messages = messages2;
    2b9b:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2ba0:	41 c7 44 24 20 02 00 00 00 	movl   $0x2,0x20(%r12)
            mailboxes[b].higher = &data[1];
    2ba9:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
            mailboxes[b].lower = &data[0];
    2bb0:	49 89 04 24          	mov    %rax,(%r12)
            data[0].messages_count = 0;
    2bb4:	66 0f 6f 1d 84 4f 00 00 	movdqa 0x4f84(%rip),%xmm3        # 7b40 <_IO_stdin_used+0xb40>
            mailboxes[b].higher = &data[1];
    2bbc:	49 89 74 24 08       	mov    %rsi,0x8(%r12)
            data[0].available = 0;
    2bc1:	c7 80 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rax)
            data[0].messages = messages;
    2bcb:	48 89 08             	mov    %rcx,(%rax)
            data[1].messages = messages2;
    2bce:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
            data[1].available = 0;
    2bd5:	c7 80 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rax)
            data[0].messages_count = 0;
    2bdf:	0f 29 98 80 00 00 00 	movaps %xmm3,0x80(%rax)
            data[1].messages_count = 0;
    2be6:	0f 29 98 00 02 00 00 	movaps %xmm3,0x200(%rax)
          char *message = malloc(sizeof(char) * 256);
    2bed:	be 01 00 00 00       	mov    $0x1,%esi
    2bf2:	bf 00 01 00 00       	mov    $0x100,%edi
    2bf7:	e8 a4 f7 ff ff       	call   23a0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2bfc:	bf 18 00 00 00       	mov    $0x18,%edi
          char *message = malloc(sizeof(char) * 256);
    2c01:	49 89 c4             	mov    %rax,%r12
          struct Message *messaged = malloc(sizeof(struct Message));
    2c04:	e8 07 f8 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2c09:	ba 00 01 00 00       	mov    $0x100,%edx
    2c0e:	4c 89 e7             	mov    %r12,%rdi
    2c11:	41 89 e9             	mov    %ebp,%r9d
    2c14:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2c19:	45 89 e8             	mov    %r13d,%r8d
    2c1c:	be 01 00 00 00       	mov    $0x1,%esi
    2c21:	31 c0                	xor    %eax,%eax
    2c23:	48 8d 0d 66 4a 00 00 	lea    0x4a66(%rip),%rcx        # 7690 <_IO_stdin_used+0x690>
    2c2a:	e8 f1 f8 ff ff       	call   2520 <__sprintf_chk@plt>
          messaged->message = message;
    2c2f:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
          messaged->thread_index = thread_data[x].thread_index;
    2c34:	49 63 46 04          	movslq 0x4(%r14),%rax
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2c38:	be 20 00 00 00       	mov    $0x20,%esi
    2c3d:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->message = message;
    2c42:	4d 89 22             	mov    %r12,(%r10)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2c45:	4d 8b 66 38          	mov    0x38(%r14),%r12
          messaged->task_index = y;
    2c49:	4d 89 7a 10          	mov    %r15,0x10(%r10)
          messaged->thread_index = thread_data[x].thread_index;
    2c4d:	49 89 c7             	mov    %rax,%r15
    2c50:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2c54:	8d 45 01             	lea    0x1(%rbp),%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2c57:	4c 01 e3             	add    %r12,%rbx
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2c5a:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2c5d:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2c63:	89 83 90 01 00 00    	mov    %eax,0x190(%rbx)
          thread_data[x].tasks[y].message = messaged;
    2c69:	4c 89 93 88 01 00 00 	mov    %r10,0x188(%rbx)
          thread_data[x].tasks[y].sending = 1;
    2c70:	c7 83 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rbx)
          thread_data[x].tasks[y].snapshot_count = 99;
    2c7a:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2c85:	e8 16 f7 ff ff       	call   23a0 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    2c8a:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2c95:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2c9c:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    2ca1:	48 8b 00             	mov    (%rax),%rax
    2ca4:	8b 50 04             	mov    0x4(%rax),%edx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2ca7:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2cae:	89 93 30 01 00 00    	mov    %edx,0x130(%rbx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2cb4:	4c 39 f0             	cmp    %r14,%rax
    2cb7:	0f 85 be 0a 00 00    	jne    377b <main+0x118b>
          thread_data[x].tasks[y].thread_count = 2;
    2cbd:	66 0f 6f 05 8b 4e 00 00 	movdqa 0x4e8b(%rip),%xmm0        # 7b50 <_IO_stdin_used+0xb50>
          thread_data[x].tasks[y].task_index = y;
    2cc5:	89 6b 04             	mov    %ebp,0x4(%rbx)
          thread_data[x].tasks[y].available = 1;
    2cc8:	48 8b 05 99 4e 00 00 	mov    0x4e99(%rip),%rax        # 7b68 <_IO_stdin_used+0xb68>
          thread_data[x].tasks[y].arrived = 0;
    2ccf:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
          thread_data[x].tasks[y].worker_count = thread_count;
    2cd9:	c7 83 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rbx)
          thread_data[x].tasks[y].available = 1;
    2ce3:	48 89 83 44 01 00 00 	mov    %rax,0x144(%rbx)
          thread_data[x].tasks[y].thread_count = 2;
    2cea:	0f 11 83 34 01 00 00 	movups %xmm0,0x134(%rbx)
          if (y == barrier_count - 1) {
    2cf1:	83 fd 01             	cmp    $0x1,%ebp
    2cf4:	0f 84 47 01 00 00    	je     2e41 <main+0x851>
            if (y == 0) {
    2cfa:	85 ed                	test   %ebp,%ebp
    2cfc:	0f 85 34 fb ff ff    	jne    2836 <main+0x246>
    2d02:	48 8d 05 07 31 00 00 	lea    0x3107(%rip),%rax        # 5e10 <barriered_work_ingest_andwork>
    2d09:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    2d0e:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2d15:	e9 55 fd ff ff       	jmp    2a6f <main+0x47f>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2d1a:	31 d2                	xor    %edx,%edx
    2d1c:	48 8d 35 32 46 00 00 	lea    0x4632(%rip),%rsi        # 7355 <_IO_stdin_used+0x355>
    2d23:	bf 01 00 00 00       	mov    $0x1,%edi
    2d28:	31 c0                	xor    %eax,%eax
    2d2a:	e8 21 f7 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d2f:	be 08 00 00 00       	mov    $0x8,%esi
    2d34:	bf 01 00 00 00       	mov    $0x1,%edi
    2d39:	e8 62 f6 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d3e:	be 08 00 00 00       	mov    $0x8,%esi
    2d43:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d48:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d4d:	e8 4e f6 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2d52:	be 80 01 00 00       	mov    $0x180,%esi
    2d57:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d5c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    2d61:	e8 3a f6 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    2d66:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
              data[1].messages = messages2;
    2d6b:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    2d70:	41 c7 44 24 20 01 00 00 00 	movl   $0x1,0x20(%r12)
              mailboxes[b].higher = &data[1];
    2d79:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    2d80:	49 89 04 24          	mov    %rax,(%r12)
    2d84:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].messages_count = 0;
    2d89:	66 0f 6f 2d af 4d 00 00 	movdqa 0x4daf(%rip),%xmm5        # 7b40 <_IO_stdin_used+0xb40>
              data[0].messages = messages;
    2d91:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    2d94:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
    2d9b:	ba 01 00 00 00       	mov    $0x1,%edx
              mailboxes[b].higher = &data[1];
    2da0:	49 89 74 24 08       	mov    %rsi,0x8(%r12)
    2da5:	48 8d 35 a9 45 00 00 	lea    0x45a9(%rip),%rsi        # 7355 <_IO_stdin_used+0x355>
              data[0].messages_count = 0;
    2dac:	0f 29 a8 80 00 00 00 	movaps %xmm5,0x80(%rax)
              data[1].messages_count = 0;
    2db3:	0f 29 a8 00 02 00 00 	movaps %xmm5,0x200(%rax)
    2dba:	31 c0                	xor    %eax,%eax
    2dbc:	e8 8f f6 ff ff       	call   2450 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2dc1:	be 08 00 00 00       	mov    $0x8,%esi
    2dc6:	bf 01 00 00 00       	mov    $0x1,%edi
    2dcb:	e8 d0 f5 ff ff       	call   23a0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2dd0:	be 08 00 00 00       	mov    $0x8,%esi
    2dd5:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2dda:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ddf:	e8 bc f5 ff ff       	call   23a0 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    2de4:	be 80 01 00 00       	mov    $0x180,%esi
    2de9:	bf 02 00 00 00       	mov    $0x2,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2dee:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
              struct Data *data = calloc(2, sizeof(struct Data));
    2df3:	e8 a8 f5 ff ff       	call   23a0 <calloc@plt>
              data[0].messages = messages;
    2df8:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
              data[1].messages = messages2;
    2dfd:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    2e02:	41 c7 44 24 48 01 00 00 00 	movl   $0x1,0x48(%r12)
              data[0].messages_count = 0;
    2e0b:	66 0f 6f 3d 2d 4d 00 00 	movdqa 0x4d2d(%rip),%xmm7        # 7b40 <_IO_stdin_used+0xb40>
              mailboxes[b].higher = &data[1];
    2e13:	48 8d b0 80 01 00 00 	lea    0x180(%rax),%rsi
              mailboxes[b].lower = &data[0];
    2e1a:	49 89 44 24 28       	mov    %rax,0x28(%r12)
              mailboxes[b].higher = &data[1];
    2e1f:	49 89 74 24 30       	mov    %rsi,0x30(%r12)
              data[0].messages = messages;
    2e24:	48 89 08             	mov    %rcx,(%rax)
              data[1].messages = messages2;
    2e27:	48 89 90 80 01 00 00 	mov    %rdx,0x180(%rax)
              data[0].messages_count = 0;
    2e2e:	0f 29 b8 80 00 00 00 	movaps %xmm7,0x80(%rax)
              data[1].messages_count = 0;
    2e35:	0f 29 b8 00 02 00 00 	movaps %xmm7,0x200(%rax)
            if (b == x || b == x + 1) { continue; }
    2e3c:	e9 ac fd ff ff       	jmp    2bed <main+0x5fd>
    2e41:	48 8d 05 a8 2d 00 00 	lea    0x2da8(%rip),%rax        # 5bf0 <barriered_work>
    2e48:	bd 02 00 00 00       	mov    $0x2,%ebp
    2e4d:	e9 bc fe ff ff       	jmp    2d0e <main+0x71e>
    2e52:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    2e57:	ba 03 00 00 00       	mov    $0x3,%edx
    2e5c:	48 8d 35 0e 45 00 00 	lea    0x450e(%rip),%rsi        # 7371 <_IO_stdin_used+0x371>
    2e63:	31 c0                	xor    %eax,%eax
    2e65:	bf 01 00 00 00       	mov    $0x1,%edi
    2e6a:	44 89 6c 24 40       	mov    %r13d,0x40(%rsp)
    2e6f:	e8 dc f5 ff ff       	call   2450 <__printf_chk@plt>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2e74:	be 08 00 00 00       	mov    $0x8,%esi
    2e79:	bf 02 00 00 00       	mov    $0x2,%edi
    my_thread_data[0] = &thread_data[x]; 
    2e7e:	4c 8d ab 40 02 00 00 	lea    0x240(%rbx),%r13
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2e85:	e8 16 f5 ff ff       	call   23a0 <calloc@plt>
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e8a:	be 38 00 00 00       	mov    $0x38,%esi
    2e8f:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[x].thread_count = 2;
    2e94:	c7 83 68 02 00 00 02 00 00 00 	movl   $0x2,0x268(%rbx)
    thread_data[x].threads = my_thread_data;
    2e9e:	48 89 83 58 02 00 00 	mov    %rax,0x258(%rbx)
    my_thread_data[0] = &thread_data[x]; 
    2ea5:	4c 89 28             	mov    %r13,(%rax)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2ea8:	48 89 58 08          	mov    %rbx,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2eac:	48 8b 43 38          	mov    0x38(%rbx),%rax
    thread_data[x].thread_index = 0;
    2eb0:	c7 83 44 02 00 00 00 00 00 00 	movl   $0x0,0x244(%rbx)
    thread_data[x].task_count = total_barrier_count;
    2eba:	c7 83 80 02 00 00 03 00 00 00 	movl   $0x3,0x280(%rbx)
    thread_data[n].tasks[0].scheduled = 1;
    2ec4:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    2ece:	48 8b 83 f8 00 00 00 	mov    0xf8(%rbx),%rax
    2ed5:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2edf:	e8 bc f4 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ee4:	be 38 00 00 00       	mov    $0x38,%esi
    2ee9:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2eee:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ef1:	e8 aa f4 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ef6:	be 38 00 00 00       	mov    $0x38,%esi
    2efb:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2f00:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2f03:	e8 98 f4 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2f08:	be 38 00 00 00       	mov    $0x38,%esi
    2f0d:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2f12:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2f17:	e8 84 f4 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2f1c:	be 08 00 00 00       	mov    $0x8,%esi
    2f21:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2f26:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2f2b:	e8 70 f4 ff ff       	call   23a0 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2f30:	be 08 00 00 00       	mov    $0x8,%esi
    2f35:	bf 06 00 00 00       	mov    $0x6,%edi
  thread_data[timer_threadi].type = TIMER;
    2f3a:	c7 83 8c 01 00 00 00 00 00 00 	movl   $0x0,0x18c(%rbx)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2f44:	48 89 c5             	mov    %rax,%rbp
  thread_data[timer_threadi].task_count = total_barrier_count;
    2f47:	48 8b 05 22 4c 00 00 	mov    0x4c22(%rip),%rax        # 7b70 <_IO_stdin_used+0xb70>
    2f4e:	48 89 83 c0 01 00 00 	mov    %rax,0x1c0(%rbx)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2f55:	e8 46 f4 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2f5a:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
  }
  thread_data[timer_threadi].threads = my_thread_data;
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    2f5f:	48 8b 3d fa 4b 00 00 	mov    0x4bfa(%rip),%rdi        # 7b60 <_IO_stdin_used+0xb60>
    my_thread_data[n] = &thread_data[n]; 
    2f66:	4c 8d 83 00 03 00 00 	lea    0x300(%rbx),%r8
    2f6d:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    2f74:	48 8d 93 c0 03 00 00 	lea    0x3c0(%rbx),%rdx
    2f7b:	4c 89 40 20          	mov    %r8,0x20(%rax)
    2f7f:	48 89 18             	mov    %rbx,(%rax)
    2f82:	48 8d 35 f7 43 00 00 	lea    0x43f7(%rip),%rsi        # 7380 <_IO_stdin_used+0x380>
    2f89:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2f8d:	48 89 48 10          	mov    %rcx,0x10(%rax)
    2f91:	4c 89 68 18          	mov    %r13,0x18(%rax)
    2f95:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2f99:	ba 02 00 00 00       	mov    $0x2,%edx
  thread_data[timer_threadi].threads = my_thread_data;
    2f9e:	48 89 83 98 01 00 00 	mov    %rax,0x198(%rbx)
    2fa5:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    2fa7:	48 89 bb a8 01 00 00 	mov    %rdi,0x1a8(%rbx)
    2fae:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    2fb3:	c7 83 b0 01 00 00 02 00 00 00 	movl   $0x2,0x1b0(%rbx)
  thread_data[timer_threadi].thread_index = 0;
    2fbd:	c7 83 84 01 00 00 00 00 00 00 	movl   $0x0,0x184(%rbx)
    my_thread_data[n] = &thread_data[n]; 
    2fc7:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    2fcc:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    2fd1:	e8 7a f4 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    2fd6:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    2fdb:	48 8d 7d 10          	lea    0x10(%rbp),%rdi
    2fdf:	49 8d 74 24 70       	lea    0x70(%r12),%rsi
    2fe4:	48 8d 15 55 0a 00 00 	lea    0xa55(%rip),%rdx        # 3a40 <timer_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
      thread_data[x].running = 1;
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2feb:	4c 8d 25 9e 27 00 00 	lea    0x279e(%rip),%r12        # 5790 <barriered_thread>
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    2ff2:	e8 79 f4 ff ff       	call   2470 <pthread_create@plt>
      thread_data[x].type = WORKER;
    2ff7:	c7 43 0c 01 00 00 00 	movl   $0x1,0xc(%rbx)
    2ffe:	31 c9                	xor    %ecx,%ecx
    3000:	31 d2                	xor    %edx,%edx
      thread_data[x].running = 1;
    3002:	c7 43 44 01 00 00 00 	movl   $0x1,0x44(%rbx)
    3009:	4c 8d 0d a8 46 00 00 	lea    0x46a8(%rip),%r9        # 76b8 <_IO_stdin_used+0x6b8>
    3010:	bf 01 00 00 00       	mov    $0x1,%edi
    3015:	31 c0                	xor    %eax,%eax
    3017:	4c 89 ce             	mov    %r9,%rsi
    301a:	e8 31 f4 ff ff       	call   2450 <__printf_chk@plt>
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    301f:	48 89 d9             	mov    %rbx,%rcx
    3022:	4c 89 e2             	mov    %r12,%rdx
    3025:	4c 89 fe             	mov    %r15,%rsi
    3028:	48 89 ef             	mov    %rbp,%rdi
    302b:	e8 40 f4 ff ff       	call   2470 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3030:	48 8b 93 b0 00 00 00 	mov    0xb0(%rbx),%rdx
    3037:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
    303b:	be 08 00 00 00       	mov    $0x8,%esi
    3040:	e8 9b f2 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    3045:	4c 8d 0d 6c 46 00 00 	lea    0x466c(%rip),%r9        # 76b8 <_IO_stdin_used+0x6b8>
    304c:	31 c9                	xor    %ecx,%ecx
    304e:	31 c0                	xor    %eax,%eax
    3050:	4c 89 ce             	mov    %r9,%rsi
    3053:	ba 01 00 00 00       	mov    $0x1,%edx
    3058:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].type = WORKER;
    305d:	c7 83 cc 00 00 00 01 00 00 00 	movl   $0x1,0xcc(%rbx)
      thread_data[x].running = 1;
    3067:	c7 83 04 01 00 00 01 00 00 00 	movl   $0x1,0x104(%rbx)
    3071:	e8 da f3 ff ff       	call   2450 <__printf_chk@plt>
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3076:	4c 89 f1             	mov    %r14,%rcx
    3079:	49 8d 77 38          	lea    0x38(%r15),%rsi
    307d:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
    3081:	4c 89 e2             	mov    %r12,%rdx
    3084:	4d 89 f7             	mov    %r14,%r15
    3087:	e8 e4 f3 ff ff       	call   2470 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    308c:	48 8b 93 70 01 00 00 	mov    0x170(%rbx),%rdx
    3093:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
    3097:	be 08 00 00 00       	mov    $0x8,%esi
    309c:	e8 3f f2 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    30a1:	be d8 00 00 00       	mov    $0xd8,%esi
    30a6:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    30ab:	4c 8b 35 c6 4a 00 00 	mov    0x4ac6(%rip),%r14        # 7b78 <_IO_stdin_used+0xb78>
    thread_data[x].type = IO;
    30b2:	c7 83 4c 02 00 00 02 00 00 00 	movl   $0x2,0x24c(%rbx)
    thread_data[x].task_count = 0;
    30bc:	4c 89 b3 80 02 00 00 	mov    %r14,0x280(%rbx)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    30c3:	e8 d8 f2 ff ff       	call   23a0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    30c8:	31 ff                	xor    %edi,%edi
    30ca:	be 00 08 00 00       	mov    $0x800,%esi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    30cf:	48 89 83 98 02 00 00 	mov    %rax,0x298(%rbx)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    30d6:	e8 d5 f3 ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    30db:	be 08 00 00 00       	mov    $0x8,%esi
    30e0:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    30e5:	89 83 a0 02 00 00    	mov    %eax,0x2a0(%rbx)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    30eb:	e8 b0 f2 ff ff       	call   23a0 <calloc@plt>
    30f0:	ba 03 00 00 00       	mov    $0x3,%edx
    30f5:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    30fa:	c7 83 68 02 00 00 02 00 00 00 	movl   $0x2,0x268(%rbx)
      my_thread_data[n] = &thread_data[n]; 
    3104:	48 89 18             	mov    %rbx,(%rax)
    3107:	48 8d 35 90 42 00 00 	lea    0x4290(%rip),%rsi        # 739e <_IO_stdin_used+0x39e>
    310e:	4c 89 78 08          	mov    %r15,0x8(%rax)
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3112:	41 bf 04 00 00 00    	mov    $0x4,%r15d
    thread_data[x].threads = my_thread_data;
    3118:	48 89 83 58 02 00 00 	mov    %rax,0x258(%rbx)
    311f:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3121:	c7 83 44 02 00 00 03 00 00 00 	movl   $0x3,0x244(%rbx)
    312b:	e8 20 f3 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3130:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3135:	48 8d 7d 18          	lea    0x18(%rbp),%rdi
    3139:	4c 89 e9             	mov    %r13,%rcx
    313c:	48 8d 15 5d 1e 00 00 	lea    0x1e5d(%rip),%rdx        # 4fa0 <io_thread>
    3143:	4c 8d 6d 20          	lea    0x20(%rbp),%r13
    3147:	48 81 c6 a8 00 00 00 	add    $0xa8,%rsi
    314e:	e8 1d f3 ff ff       	call   2470 <pthread_create@plt>
    3153:	ba 04 00 00 00       	mov    $0x4,%edx
    3158:	48 8d 35 56 42 00 00 	lea    0x4256(%rip),%rsi        # 73b5 <_IO_stdin_used+0x3b5>
    315f:	31 c0                	xor    %eax,%eax
    3161:	bf 01 00 00 00       	mov    $0x1,%edi
    3166:	e8 e5 f2 ff ff       	call   2450 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    316b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3170:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    3175:	48 05 e0 00 00 00    	add    $0xe0,%rax
    317b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3180:	48 89 e8             	mov    %rbp,%rax
    3183:	48 89 dd             	mov    %rbx,%rbp
    3186:	48 89 c3             	mov    %rax,%rbx
    3189:	44 89 fa             	mov    %r15d,%edx
    318c:	48 8d 35 38 42 00 00 	lea    0x4238(%rip),%rsi        # 73cb <_IO_stdin_used+0x3cb>
    3193:	bf 01 00 00 00       	mov    $0x1,%edi
    3198:	31 c0                	xor    %eax,%eax
    319a:	e8 b1 f2 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    319f:	4d 89 74 24 40       	mov    %r14,0x40(%r12)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    31a4:	be 08 00 00 00       	mov    $0x8,%esi
    31a9:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = EXTERNAL;
    31ae:	41 c7 44 24 0c 03 00 00 00 	movl   $0x3,0xc(%r12)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    31b7:	e8 e4 f1 ff ff       	call   23a0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    31bc:	48 8b 7c 24 50       	mov    0x50(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    31c1:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    31c6:	41 c7 84 24 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r12)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    31d2:	49 89 44 24 50       	mov    %rax,0x50(%r12)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    31d7:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    31da:	bf 02 00 00 00       	mov    $0x2,%edi
    31df:	e8 bc f1 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    31e4:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31e9:	4c 89 e1             	mov    %r12,%rcx
    31ec:	4c 89 ef             	mov    %r13,%rdi
    thread_data[x].threads = my_thread_data;
    31ef:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31f4:	48 8d 15 35 07 00 00 	lea    0x735(%rip),%rdx        # 3930 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    31fb:	49 83 c5 08          	add    $0x8,%r13
    31ff:	49 81 c4 c0 00 00 00 	add    $0xc0,%r12
      my_thread_data[n] = &thread_data[n]; 
    3206:	48 89 70 08          	mov    %rsi,0x8(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    320a:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    320f:	48 89 28             	mov    %rbp,(%rax)
    thread_data[x].thread_count = thread_count;
    3212:	48 8b 05 47 49 00 00 	mov    0x4947(%rip),%rax        # 7b60 <_IO_stdin_used+0xb60>
    thread_data[x].thread_index = x;
    3219:	45 89 bc 24 44 ff ff ff 	mov    %r15d,-0xbc(%r12)
    thread_data[x].thread_count = thread_count;
    3221:	49 89 84 24 68 ff ff ff 	mov    %rax,-0x98(%r12)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3229:	e8 42 f2 ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    322e:	48 83 44 24 50 10    	addq   $0x10,0x50(%rsp)
    3234:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    323a:	41 83 ff 04          	cmp    $0x4,%r15d
    323e:	75 2a                	jne    326a <main+0xc7a>
    3240:	41 bf 05 00 00 00    	mov    $0x5,%r15d
    3246:	e9 3e ff ff ff       	jmp    3189 <main+0xb99>
        thread_data[x].protected_state = &protected_state[k];
    324b:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    3250:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
        other = (x + 1) % total_threads;
    3255:	bd 01 00 00 00       	mov    $0x1,%ebp
        thread_data[x].thread_index = 0;
    325a:	c7 40 04 00 00 00 00 	movl   $0x0,0x4(%rax)
        thread_data[x].protected_state = &protected_state[k];
    3261:	48 89 78 48          	mov    %rdi,0x48(%rax)
    3265:	e9 02 f7 ff ff       	jmp    296c <main+0x37c>
    326a:	48 87 eb             	xchg   %rbp,%rbx
    326d:	4c 8d 25 74 41 00 00 	lea    0x4174(%rip),%r12        # 73e8 <_IO_stdin_used+0x3e8>
    3274:	4c 8d 73 04          	lea    0x4(%rbx),%r14
    3278:	4c 8d ab 84 04 00 00 	lea    0x484(%rbx),%r13
    327f:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    3283:	41 8b 16             	mov    (%r14),%edx
    3286:	4c 89 e6             	mov    %r12,%rsi
    3289:	bf 01 00 00 00       	mov    $0x1,%edi
    328e:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3290:	49 81 c6 c0 00 00 00 	add    $0xc0,%r14
    3297:	e8 b4 f1 ff ff       	call   2450 <__printf_chk@plt>
    329c:	4d 39 ee             	cmp    %r13,%r14
    329f:	75 de                	jne    327f <main+0xc8f>
    32a1:	48 8d 3d 53 41 00 00 	lea    0x4153(%rip),%rdi        # 73fb <_IO_stdin_used+0x3fb>
    32a8:	45 31 f6             	xor    %r14d,%r14d
    32ab:	4c 8d 6c 24 70       	lea    0x70(%rsp),%r13
    32b0:	e8 3b f0 ff ff       	call   22f0 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    32b5:	4c 8d 25 5d 41 00 00 	lea    0x415d(%rip),%r12        # 7419 <_IO_stdin_used+0x419>
    void * result; 
    pthread_join(thread[x], &result);
    32bc:	4a 8b 7c f5 00       	mov    0x0(%rbp,%r14,8),%rdi
    32c1:	4c 89 ee             	mov    %r13,%rsi
    32c4:	e8 27 f2 ff ff       	call   24f0 <pthread_join@plt>
    32c9:	44 89 f2             	mov    %r14d,%edx
    32cc:	4c 89 e6             	mov    %r12,%rsi
    32cf:	bf 01 00 00 00       	mov    $0x1,%edi
    32d4:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    32d6:	49 83 c6 01          	add    $0x1,%r14
    32da:	e8 71 f1 ff ff       	call   2450 <__printf_chk@plt>
    32df:	49 83 fe 06          	cmp    $0x6,%r14
    32e3:	75 d7                	jne    32bc <main+0xccc>
    32e5:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    32ea:	45 31 d2             	xor    %r10d,%r10d
    32ed:	45 31 ff             	xor    %r15d,%r15d
    32f0:	48 89 5c 24 38       	mov    %rbx,0x38(%rsp)
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    32f5:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    32fd:	4c 8d 73 38          	lea    0x38(%rbx),%r14
  for (int x = 0 ; x < total_threads ; x++) {
    3301:	45 31 ed             	xor    %r13d,%r13d
    3304:	4c 89 fb             	mov    %r15,%rbx
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3307:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
    3311:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    3316:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    331b:	bf 0a 00 00 00       	mov    $0xa,%edi
    3320:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
      if (x % 2 == 1) {
    3325:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    332a:	e8 a1 ef ff ff       	call   22d0 <putchar@plt>
    332f:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3334:	bf 01 00 00 00       	mov    $0x1,%edi
    3339:	48 8d 35 ed 40 00 00 	lea    0x40ed(%rip),%rsi        # 742d <_IO_stdin_used+0x42d>
    3340:	41 83 f4 01          	xor    $0x1,%r12d
    3344:	48 8b 10             	mov    (%rax),%rdx
    3347:	31 c0                	xor    %eax,%eax
    3349:	e8 02 f1 ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    334e:	41 8b 56 08          	mov    0x8(%r14),%edx
    3352:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    3357:	85 d2                	test   %edx,%edx
    3359:	0f 8e 15 04 00 00    	jle    3774 <main+0x1184>
    335f:	48 63 f2             	movslq %edx,%rsi
    3362:	49 8b 06             	mov    (%r14),%rax
      long v = 0;
    3365:	31 d2                	xor    %edx,%edx
    3367:	48 c1 e6 09          	shl    $0x9,%rsi
    336b:	48 01 c6             	add    %rax,%rsi
    336e:	66 90                	xchg   %ax,%ax
        v += thread_data[me].tasks[n].v;
    3370:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3377:	48 05 00 02 00 00    	add    $0x200,%rax
    337d:	48 39 f0             	cmp    %rsi,%rax
    3380:	75 ee                	jne    3370 <main+0xd80>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3382:	4c 89 e0             	mov    %r12,%rax
    3385:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    338a:	48 f7 d8             	neg    %rax
    338d:	25 c0 00 00 00       	and    $0xc0,%eax
    3392:	48 01 f8             	add    %rdi,%rax
    3395:	48 63 70 40          	movslq 0x40(%rax),%rsi
    3399:	85 f6                	test   %esi,%esi
    339b:	7e 25                	jle    33c2 <main+0xdd2>
    339d:	48 8b 40 38          	mov    0x38(%rax),%rax
    33a1:	48 c1 e6 09          	shl    $0x9,%rsi
    33a5:	48 01 c6             	add    %rax,%rsi
    33a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    33b0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    33b7:	48 05 00 02 00 00    	add    $0x200,%rax
    33bd:	48 39 f0             	cmp    %rsi,%rax
    33c0:	75 ee                	jne    33b0 <main+0xdc0>
    33c2:	48 8d 35 79 40 00 00 	lea    0x4079(%rip),%rsi        # 7442 <_IO_stdin_used+0x442>
    33c9:	bf 01 00 00 00       	mov    $0x1,%edi
    33ce:	31 c0                	xor    %eax,%eax
    33d0:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    33d5:	e8 76 f0 ff ff       	call   2450 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    33da:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    33df:	bf 01 00 00 00       	mov    $0x1,%edi
    33e4:	48 8b 30             	mov    (%rax),%rsi
    33e7:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    33f1:	48 f7 ee             	imul   %rsi
    33f4:	48 c1 fe 3f          	sar    $0x3f,%rsi
    33f8:	31 c0                	xor    %eax,%eax
    33fa:	48 d1 fa             	sar    %rdx
    33fd:	48 29 f2             	sub    %rsi,%rdx
    3400:	48 8d 35 e1 42 00 00 	lea    0x42e1(%rip),%rsi        # 76e8 <_IO_stdin_used+0x6e8>
    3407:	e8 44 f0 ff ff       	call   2450 <__printf_chk@plt>
    340c:	bf 0a 00 00 00       	mov    $0xa,%edi
    3411:	e8 ba ee ff ff       	call   22d0 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3416:	41 8b 56 08          	mov    0x8(%r14),%edx
    341a:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    341f:	85 d2                	test   %edx,%edx
    3421:	7e 51                	jle    3474 <main+0xe84>
    3423:	49 8b 06             	mov    (%r14),%rax
    3426:	4c 63 c2             	movslq %edx,%r8
    3429:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    342e:	49 c1 e0 09          	shl    $0x9,%r8
    3432:	49 01 c0             	add    %rax,%r8
    3435:	0f 1f 00             	nopl   (%rax)
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3438:	48 8b 90 70 01 00 00 	mov    0x170(%rax),%rdx
        total += thread_data[x].tasks[n].n;
    343f:	4c 03 a8 08 01 00 00 	add    0x108(%rax),%r13
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3446:	48 05 00 02 00 00    	add    $0x200,%rax
        ingests += thread_data[x].tasks[n].ingest_count;
    344c:	48 03 98 68 ff ff ff 	add    -0x98(%rax),%rbx
        sends += thread_data[x].tasks[n].sends;
    3453:	48 03 88 78 ff ff ff 	add    -0x88(%rax),%rcx
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    345a:	4c 03 52 10          	add    0x10(%rdx),%r10
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    345e:	4c 03 7a 18          	add    0x18(%rdx),%r15
          sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3462:	4c 03 52 38          	add    0x38(%rdx),%r10
          received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3466:	4c 03 7a 40          	add    0x40(%rdx),%r15
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    346a:	4c 39 c0             	cmp    %r8,%rax
    346d:	75 c9                	jne    3438 <main+0xe48>
    346f:	48 89 4c 24 28       	mov    %rcx,0x28(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3474:	45 31 e4             	xor    %r12d,%r12d
    3477:	49 83 7e 68 00       	cmpq   $0x0,0x68(%r14)
    347c:	7e 74                	jle    34f2 <main+0xf02>
    347e:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    3483:	4c 89 e3             	mov    %r12,%rbx
    3486:	4d 89 f4             	mov    %r14,%r12
    3489:	4d 89 d6             	mov    %r10,%r14
    348c:	0f 1f 40 00          	nopl   0x0(%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3490:	49 8b 44 24 58       	mov    0x58(%r12),%rax
    3495:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    3499:	48 83 ec 08          	sub    $0x8,%rsp
    349d:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    34a2:	48 83 c3 01          	add    $0x1,%rbx
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    34a6:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    34aa:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    34ae:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    34b2:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    34b5:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    34b9:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    34bc:	48 f7 e5             	mul    %rbp
    34bf:	8b 49 20             	mov    0x20(%rcx),%ecx
    34c2:	56                   	push   %rsi
    34c3:	31 c0                	xor    %eax,%eax
    34c5:	48 8d 35 3c 42 00 00 	lea    0x423c(%rip),%rsi        # 7708 <_IO_stdin_used+0x708>
    34cc:	48 c1 ea 12          	shr    $0x12,%rdx
    34d0:	49 89 d1             	mov    %rdx,%r9
    34d3:	ba 02 00 00 00       	mov    $0x2,%edx
    34d8:	e8 73 ef ff ff       	call   2450 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    34dd:	41 5b                	pop    %r11
    34df:	58                   	pop    %rax
    34e0:	49 39 5c 24 68       	cmp    %rbx,0x68(%r12)
    34e5:	7f a9                	jg     3490 <main+0xea0>
    34e7:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    34ec:	4d 89 f2             	mov    %r14,%r10
    34ef:	4d 89 e6             	mov    %r12,%r14
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    34f2:	41 8b b6 84 00 00 00 	mov    0x84(%r14),%esi
    34f9:	85 f6                	test   %esi,%esi
    34fb:	0f 8e 12 01 00 00    	jle    3613 <main+0x1023>
    3501:	4c 89 6c 24 50       	mov    %r13,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3506:	4d 8b 4e 18          	mov    0x18(%r14),%r9
    350a:	31 d2                	xor    %edx,%edx
    350c:	48 89 5c 24 58       	mov    %rbx,0x58(%rsp)
    3511:	4c 89 54 24 60       	mov    %r10,0x60(%rsp)
    3516:	4c 89 7c 24 68       	mov    %r15,0x68(%rsp)
    351b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3520:	49 8b 04 d1          	mov    (%r9,%rdx,8),%rax
    3524:	89 d3                	mov    %edx,%ebx
    3526:	4c 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%r15
    352e:	44 8b 00             	mov    (%rax),%r8d
    3531:	45 85 c0             	test   %r8d,%r8d
    3534:	0f 8e b9 00 00 00    	jle    35f3 <main+0x1003>
    353a:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    353f:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3543:	31 f6                	xor    %esi,%esi
    3545:	0f 1f 00             	nopl   (%rax)
    3548:	49 89 f4             	mov    %rsi,%r12
    354b:	45 31 ed             	xor    %r13d,%r13d
    354e:	49 c1 e4 08          	shl    $0x8,%r12
    3552:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    3556:	8b ba 94 00 00 00    	mov    0x94(%rdx),%edi
    355c:	85 ff                	test   %edi,%edi
    355e:	7e 7a                	jle    35da <main+0xfea>
    3560:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    3565:	0f 1f 00             	nopl   (%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3568:	4c 89 e9             	mov    %r13,%rcx
    356b:	48 83 ec 08          	sub    $0x8,%rsp
    356f:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3574:	49 83 c5 01          	add    $0x1,%r13
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3578:	48 c1 e1 05          	shl    $0x5,%rcx
    357c:	48 03 8a 88 00 00 00 	add    0x88(%rdx),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3583:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3587:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    358b:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    358e:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3592:	4c 2b 01             	sub    (%rcx),%r8
    3595:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3596:	48 f7 e5             	mul    %rbp
    3599:	89 d9                	mov    %ebx,%ecx
    359b:	48 8d 35 b6 41 00 00 	lea    0x41b6(%rip),%rsi        # 7758 <_IO_stdin_used+0x758>
    35a2:	31 c0                	xor    %eax,%eax
    35a4:	48 c1 ea 12          	shr    $0x12,%rdx
    35a8:	49 89 d1             	mov    %rdx,%r9
    35ab:	ba 02 00 00 00       	mov    $0x2,%edx
    35b0:	e8 9b ee ff ff       	call   2450 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    35b5:	4d 8b 4e 18          	mov    0x18(%r14),%r9
    35b9:	41 58                	pop    %r8
    35bb:	41 5a                	pop    %r10
    35bd:	4b 8b 04 39          	mov    (%r9,%r15,1),%rax
    35c1:	48 8b 48 08          	mov    0x8(%rax),%rcx
    35c5:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    35c9:	44 39 aa 94 00 00 00 	cmp    %r13d,0x94(%rdx)
    35d0:	7f 96                	jg     3568 <main+0xf78>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    35d2:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    35d7:	44 8b 00             	mov    (%rax),%r8d
    35da:	48 83 c6 01          	add    $0x1,%rsi
    35de:	41 39 f0             	cmp    %esi,%r8d
    35e1:	0f 8f 61 ff ff ff    	jg     3548 <main+0xf58>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    35e7:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    35ec:	41 8b b6 84 00 00 00 	mov    0x84(%r14),%esi
    35f3:	48 83 c2 01          	add    $0x1,%rdx
    35f7:	39 d6                	cmp    %edx,%esi
    35f9:	0f 8f 21 ff ff ff    	jg     3520 <main+0xf30>
    35ff:	4c 8b 6c 24 50       	mov    0x50(%rsp),%r13
    3604:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
    3609:	4c 8b 54 24 60       	mov    0x60(%rsp),%r10
    360e:	4c 8b 7c 24 68       	mov    0x68(%rsp),%r15
    for (int d = 0 ; d < threads_per_group ; d++) {
    3613:	8b 44 24 20          	mov    0x20(%rsp),%eax
    3617:	48 83 44 24 18 18    	addq   $0x18,0x18(%rsp)
    361d:	49 81 c6 c0 00 00 00 	add    $0xc0,%r14
    3624:	85 c0                	test   %eax,%eax
    3626:	75 0d                	jne    3635 <main+0x1045>
    3628:	8b 44 24 40          	mov    0x40(%rsp),%eax
    362c:	89 44 24 20          	mov    %eax,0x20(%rsp)
    3630:	e9 e6 fc ff ff       	jmp    331b <main+0xd2b>
    3635:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    363a:	4c 8b 54 24 28       	mov    0x28(%rsp),%r10
    363f:	4c 89 ea             	mov    %r13,%rdx
    3642:	31 c0                	xor    %eax,%eax
    3644:	48 8d 35 04 3e 00 00 	lea    0x3e04(%rip),%rsi        # 744f <_IO_stdin_used+0x44f>
    364b:	bf 01 00 00 00       	mov    $0x1,%edi
    3650:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    3655:	49 89 df             	mov    %rbx,%r15
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3658:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    3662:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    3667:	e8 e4 ed ff ff       	call   2450 <__printf_chk@plt>
    366c:	bf 0a 00 00 00       	mov    $0xa,%edi
    3671:	e8 5a ec ff ff       	call   22d0 <putchar@plt>
    3676:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    367b:	bf 01 00 00 00       	mov    $0x1,%edi
    3680:	48 8d 35 29 41 00 00 	lea    0x4129(%rip),%rsi        # 77b0 <_IO_stdin_used+0x7b0>
    3687:	48 8b 50 08          	mov    0x8(%rax),%rdx
    368b:	31 c0                	xor    %eax,%eax
    368d:	e8 be ed ff ff       	call   2450 <__printf_chk@plt>
    3692:	4c 89 f8             	mov    %r15,%rax
    3695:	49 c1 ff 3f          	sar    $0x3f,%r15
    3699:	48 8d 35 38 41 00 00 	lea    0x4138(%rip),%rsi        # 77d8 <_IO_stdin_used+0x7d8>
    36a0:	48 f7 eb             	imul   %rbx
    36a3:	bf 01 00 00 00       	mov    $0x1,%edi
    36a8:	31 c0                	xor    %eax,%eax
    36aa:	48 d1 fa             	sar    %rdx
    36ad:	4c 29 fa             	sub    %r15,%rdx
    36b0:	e8 9b ed ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    36b5:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    36ba:	bf 01 00 00 00       	mov    $0x1,%edi
    36bf:	48 8d 35 42 41 00 00 	lea    0x4142(%rip),%rsi        # 7808 <_IO_stdin_used+0x808>
    36c6:	4c 89 d0             	mov    %r10,%rax
    36c9:	49 c1 fa 3f          	sar    $0x3f,%r10
    36cd:	48 f7 eb             	imul   %rbx
    36d0:	31 c0                	xor    %eax,%eax
    36d2:	48 d1 fa             	sar    %rdx
    36d5:	4c 29 d2             	sub    %r10,%rdx
    36d8:	e8 73 ed ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    36dd:	4c 89 e8             	mov    %r13,%rax
    36e0:	49 c1 fd 3f          	sar    $0x3f,%r13
    36e4:	48 8d 35 4d 41 00 00 	lea    0x414d(%rip),%rsi        # 7838 <_IO_stdin_used+0x838>
    36eb:	48 f7 eb             	imul   %rbx
    36ee:	bf 01 00 00 00       	mov    $0x1,%edi
    36f3:	31 c0                	xor    %eax,%eax
    36f5:	48 d1 fa             	sar    %rdx
    36f8:	4c 29 ea             	sub    %r13,%rdx
    36fb:	e8 50 ed ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3700:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3705:	bf 01 00 00 00       	mov    $0x1,%edi
    370a:	48 8d 35 52 3d 00 00 	lea    0x3d52(%rip),%rsi        # 7463 <_IO_stdin_used+0x463>
    3711:	48 89 c8             	mov    %rcx,%rax
    3714:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3718:	48 f7 eb             	imul   %rbx
    371b:	31 c0                	xor    %eax,%eax
    371d:	48 d1 fa             	sar    %rdx
    3720:	48 29 ca             	sub    %rcx,%rdx
    3723:	e8 28 ed ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3728:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    372d:	bf 01 00 00 00       	mov    $0x1,%edi
    3732:	48 8d 35 3b 3d 00 00 	lea    0x3d3b(%rip),%rsi        # 7474 <_IO_stdin_used+0x474>
    3739:	4c 89 c0             	mov    %r8,%rax
    373c:	49 c1 f8 3f          	sar    $0x3f,%r8
    3740:	48 f7 eb             	imul   %rbx
    3743:	48 d1 fa             	sar    %rdx
    3746:	4c 29 c2             	sub    %r8,%rdx
    3749:	31 c0                	xor    %eax,%eax
    374b:	e8 00 ed ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3750:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    3755:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    375e:	75 25                	jne    3785 <main+0x1195>
    3760:	48 81 c4 88 00 00 00 	add    $0x88,%rsp
    3767:	31 c0                	xor    %eax,%eax
    3769:	5b                   	pop    %rbx
    376a:	5d                   	pop    %rbp
    376b:	41 5c                	pop    %r12
    376d:	41 5d                	pop    %r13
    376f:	41 5e                	pop    %r14
    3771:	41 5f                	pop    %r15
    3773:	c3                   	ret
      long v = 0;
    3774:	31 d2                	xor    %edx,%edx
    3776:	e9 07 fc ff ff       	jmp    3382 <main+0xd92>
            exit(1);
    377b:	bf 01 00 00 00       	mov    $0x1,%edi
    3780:	e8 1b ed ff ff       	call   24a0 <exit@plt>
}
    3785:	e8 a6 eb ff ff       	call   2330 <__stack_chk_fail@plt>
    378a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000003790 <_start>:
    3790:	f3 0f 1e fa          	endbr64
    3794:	31 ed                	xor    %ebp,%ebp
    3796:	49 89 d1             	mov    %rdx,%r9
    3799:	5e                   	pop    %rsi
    379a:	48 89 e2             	mov    %rsp,%rdx
    379d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    37a1:	50                   	push   %rax
    37a2:	54                   	push   %rsp
    37a3:	45 31 c0             	xor    %r8d,%r8d
    37a6:	31 c9                	xor    %ecx,%ecx
    37a8:	48 8d 3d 41 ee ff ff 	lea    -0x11bf(%rip),%rdi        # 25f0 <main>
    37af:	ff 15 23 68 00 00    	call   *0x6823(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    37b5:	f4                   	hlt
    37b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000037c0 <deregister_tm_clones>:
    37c0:	48 8d 3d 59 68 00 00 	lea    0x6859(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    37c7:	48 8d 05 52 68 00 00 	lea    0x6852(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    37ce:	48 39 f8             	cmp    %rdi,%rax
    37d1:	74 15                	je     37e8 <deregister_tm_clones+0x28>
    37d3:	48 8b 05 06 68 00 00 	mov    0x6806(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    37da:	48 85 c0             	test   %rax,%rax
    37dd:	74 09                	je     37e8 <deregister_tm_clones+0x28>
    37df:	ff e0                	jmp    *%rax
    37e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    37e8:	c3                   	ret
    37e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037f0 <register_tm_clones>:
    37f0:	48 8d 3d 29 68 00 00 	lea    0x6829(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    37f7:	48 8d 35 22 68 00 00 	lea    0x6822(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    37fe:	48 29 fe             	sub    %rdi,%rsi
    3801:	48 89 f0             	mov    %rsi,%rax
    3804:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3808:	48 c1 f8 03          	sar    $0x3,%rax
    380c:	48 01 c6             	add    %rax,%rsi
    380f:	48 d1 fe             	sar    %rsi
    3812:	74 14                	je     3828 <register_tm_clones+0x38>
    3814:	48 8b 05 d5 67 00 00 	mov    0x67d5(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    381b:	48 85 c0             	test   %rax,%rax
    381e:	74 08                	je     3828 <register_tm_clones+0x38>
    3820:	ff e0                	jmp    *%rax
    3822:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3828:	c3                   	ret
    3829:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003830 <__do_global_dtors_aux>:
    3830:	f3 0f 1e fa          	endbr64
    3834:	80 3d ed 67 00 00 00 	cmpb   $0x0,0x67ed(%rip)        # a028 <completed.0>
    383b:	75 2b                	jne    3868 <__do_global_dtors_aux+0x38>
    383d:	55                   	push   %rbp
    383e:	48 83 3d b2 67 00 00 00 	cmpq   $0x0,0x67b2(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3846:	48 89 e5             	mov    %rsp,%rbp
    3849:	74 0c                	je     3857 <__do_global_dtors_aux+0x27>
    384b:	48 8b 3d b6 67 00 00 	mov    0x67b6(%rip),%rdi        # a008 <__dso_handle>
    3852:	e8 59 ea ff ff       	call   22b0 <__cxa_finalize@plt>
    3857:	e8 64 ff ff ff       	call   37c0 <deregister_tm_clones>
    385c:	c6 05 c5 67 00 00 01 	movb   $0x1,0x67c5(%rip)        # a028 <completed.0>
    3863:	5d                   	pop    %rbp
    3864:	c3                   	ret
    3865:	0f 1f 00             	nopl   (%rax)
    3868:	c3                   	ret
    3869:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003870 <frame_dummy>:
    3870:	f3 0f 1e fa          	endbr64
    3874:	e9 77 ff ff ff       	jmp    37f0 <register_tm_clones>
    3879:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003880 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3880:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3884:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    388b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    388f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3897:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    389b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    389f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    38a6:	48 85 c9             	test   %rcx,%rcx
    38a9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    38b0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    38b4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    38b8:	31 c0                	xor    %eax,%eax
    38ba:	c3                   	ret
    38bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000038c0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    38c0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    38c4:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    38cb:	85 c9                	test   %ecx,%ecx
    38cd:	7e 4f                	jle    391e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    38cf:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    38d6:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    38dd:	48 c1 e1 09          	shl    $0x9,%rcx
    38e1:	48 8b 50 18          	mov    0x18(%rax),%rdx
    38e5:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    38e9:	48 8b 70 38          	mov    0x38(%rax),%rsi
    38ed:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    38ef:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    38f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    38f8:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3900:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3908:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3913:	48 05 00 02 00 00    	add    $0x200,%rax
    3919:	48 39 c1             	cmp    %rax,%rcx
    391c:	75 da                	jne    38f8 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    391e:	0f ae f8             	sfence
}
    3921:	31 c0                	xor    %eax,%eax
    3923:	c3                   	ret
    3924:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    392f:	90                   	nop

0000000000003930 <external_thread>:
void * external_thread(void *arg) {
    3930:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3934:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    3938:	0f 85 fb 00 00 00    	jne    3a39 <external_thread+0x109>
void * external_thread(void *arg) {
    393e:	41 57                	push   %r15
    3940:	49 89 ff             	mov    %rdi,%r15
    3943:	41 56                	push   %r14
    3945:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    3947:	4c 8d 2d b6 36 00 00 	lea    0x36b6(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    394e:	41 54                	push   %r12
    3950:	55                   	push   %rbp
    3951:	53                   	push   %rbx
    3952:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    3956:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    395c:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    3960:	85 c9                	test   %ecx,%ecx
    3962:	7e 6e                	jle    39d2 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3964:	45 31 e4             	xor    %r12d,%r12d
    3967:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3970:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    3978:	31 db                	xor    %ebx,%ebx
    397a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    397e:	48 8b 06             	mov    (%rsi),%rax
    3981:	8b 10                	mov    (%rax),%edx
    3983:	85 d2                	test   %edx,%edx
    3985:	7e 2a                	jle    39b1 <external_thread+0x81>
    3987:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    398b:	48 89 dd             	mov    %rbx,%rbp
    398e:	48 c1 e5 08          	shl    $0x8,%rbp
    3992:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    3996:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    399d:	45 85 c0             	test   %r8d,%r8d
    39a0:	74 36                	je     39d8 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    39a2:	48 83 c3 01          	add    $0x1,%rbx
    39a6:	39 da                	cmp    %ebx,%edx
    39a8:	7f e1                	jg     398b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    39aa:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    39b1:	49 83 c4 01          	add    $0x1,%r12
    39b5:	44 39 e1             	cmp    %r12d,%ecx
    39b8:	7f b6                	jg     3970 <external_thread+0x40>
  while (data->running == 1) {
    39ba:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    39bf:	74 9f                	je     3960 <external_thread+0x30>
}
    39c1:	48 83 c4 08          	add    $0x8,%rsp
    39c5:	31 c0                	xor    %eax,%eax
    39c7:	5b                   	pop    %rbx
    39c8:	5d                   	pop    %rbp
    39c9:	41 5c                	pop    %r12
    39cb:	41 5d                	pop    %r13
    39cd:	41 5e                	pop    %r14
    39cf:	41 5f                	pop    %r15
    39d1:	c3                   	ret
  while (data->running == 1) {
    39d2:	eb fe                	jmp    39d2 <external_thread+0xa2>
    39d4:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    39d8:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    39db:	48 8b 06             	mov    (%rsi),%rax
    39de:	48 8b 78 08          	mov    0x8(%rax),%rdi
    39e2:	48 01 ef             	add    %rbp,%rdi
    39e5:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    39ec:	48 c1 e6 05          	shl    $0x5,%rsi
    39f0:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    39f7:	bf 04 00 00 00       	mov    $0x4,%edi
    39fc:	e8 0f e9 ff ff       	call   2310 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    3a01:	49 8b 47 50          	mov    0x50(%r15),%rax
    3a05:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    3a09:	48 8b 40 08          	mov    0x8(%rax),%rax
    3a0d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    3a18:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3a1b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    3a1f:	48 83 c3 01          	add    $0x1,%rbx
    3a23:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3a27:	48 8b 06             	mov    (%rsi),%rax
    3a2a:	8b 10                	mov    (%rax),%edx
    3a2c:	39 da                	cmp    %ebx,%edx
    3a2e:	0f 8f 53 ff ff ff    	jg     3987 <external_thread+0x57>
    3a34:	e9 71 ff ff ff       	jmp    39aa <external_thread+0x7a>
}
    3a39:	31 c0                	xor    %eax,%eax
    3a3b:	c3                   	ret
    3a3c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003a40 <timer_thread>:
void* timer_thread(void *arg) {
    3a40:	f3 0f 1e fa          	endbr64
    3a44:	41 57                	push   %r15
    3a46:	48 8d 35 c3 35 00 00 	lea    0x35c3(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3a4d:	41 56                	push   %r14
    3a4f:	41 55                	push   %r13
    3a51:	41 54                	push   %r12
    3a53:	55                   	push   %rbp
    3a54:	48 89 fd             	mov    %rdi,%rbp
    3a57:	53                   	push   %rbx
    3a58:	48 83 ec 58          	sub    $0x58,%rsp
    3a5c:	8b 57 04             	mov    0x4(%rdi),%edx
    3a5f:	bf 01 00 00 00       	mov    $0x1,%edi
    3a64:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3a6d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3a72:	31 c0                	xor    %eax,%eax
    3a74:	e8 d7 e9 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3a79:	66 0f 6f 05 cf 3f 00 00 	movdqa 0x3fcf(%rip),%xmm0        # 7a50 <_IO_stdin_used+0xa50>
    3a81:	ba 88 13 00 00       	mov    $0x1388,%edx
    3a86:	31 c0                	xor    %eax,%eax
    3a88:	48 8d 35 93 35 00 00 	lea    0x3593(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3a8f:	bf 01 00 00 00       	mov    $0x1,%edi
    3a94:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3a99:	e8 b2 e9 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3a9e:	44 8b 65 44          	mov    0x44(%rbp),%r12d
    3aa2:	45 85 e4             	test   %r12d,%r12d
    3aa5:	0f 84 a3 00 00 00    	je     3b4e <timer_thread+0x10e>
  int n = 0;
    3aab:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    3aae:	45 31 e4             	xor    %r12d,%r12d
    3ab1:	49 89 e6             	mov    %rsp,%r14
    y++;
    3ab4:	31 db                	xor    %ebx,%ebx
    3ab6:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    3abb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    nanosleep(&preempt , &rem2);
    3ac0:	4c 89 ef             	mov    %r13,%rdi
    3ac3:	4c 89 f6             	mov    %r14,%rsi
    n++;
    3ac6:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    3aca:	e8 81 e8 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3acf:	48 63 45 30          	movslq 0x30(%rbp),%rax
    y++;
    3ad3:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3ad8:	85 c0                	test   %eax,%eax
    3ada:	7e 49                	jle    3b25 <timer_thread+0xe5>
    3adc:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3ae0:	49 c1 e4 09          	shl    $0x9,%r12
    3ae4:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3ae8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3af0:	4c 8b 11             	mov    (%rcx),%r10
    3af3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3af5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3af9:	99                   	cltd
    3afa:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3afe:	49 8b 72 38          	mov    0x38(%r10),%rsi
    3b02:	48 63 d2             	movslq %edx,%rdx
    3b05:	48 c1 e2 09          	shl    $0x9,%rdx
    3b09:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3b14:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3b20:	49 39 c8             	cmp    %rcx,%r8
    3b23:	75 cb                	jne    3af0 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    3b25:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3b28:	48 8b 45 18          	mov    0x18(%rbp),%rax
  while (data->running && n < times) {
    3b2c:	44 8b 45 44          	mov    0x44(%rbp),%r8d
    if (y >= data->threads[0]->task_count) {
    3b30:	48 8b 00             	mov    (%rax),%rax
    y++;
    3b33:	39 78 40             	cmp    %edi,0x40(%rax)
    3b36:	0f 4e fb             	cmovle %ebx,%edi
    3b39:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3b3c:	45 85 c0             	test   %r8d,%r8d
    3b3f:	74 0d                	je     3b4e <timer_thread+0x10e>
    3b41:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    3b48:	0f 85 72 ff ff ff    	jne    3ac0 <timer_thread+0x80>
    3b4e:	48 8d 3d e3 34 00 00 	lea    0x34e3(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3b55:	e8 96 e7 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3b5a:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    3b5e:	85 d2                	test   %edx,%edx
    3b60:	7e 73                	jle    3bd5 <timer_thread+0x195>
    for (int y = 0 ; y < data->task_count ; y++) {
    3b62:	48 63 45 40          	movslq 0x40(%rbp),%rax
    3b66:	85 c0                	test   %eax,%eax
    3b68:	7e 6b                	jle    3bd5 <timer_thread+0x195>
    3b6a:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3b6e:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    3b72:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3b7a:	31 c9                	xor    %ecx,%ecx
    3b7c:	48 89 c6             	mov    %rax,%rsi
    3b7f:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3b83:	48 8b 40 38          	mov    0x38(%rax),%rax
    3b87:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    3b8b:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3b91:	74 1d                	je     3bb0 <timer_thread+0x170>
    3b93:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3b9d:	48 05 00 02 00 00    	add    $0x200,%rax
    3ba3:	48 39 c2             	cmp    %rax,%rdx
    3ba6:	74 24                	je     3bcc <timer_thread+0x18c>
    3ba8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->threads[x]->tasks[y].sending = 0;
    3bb0:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3bba:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3bc0:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3bc7:	48 39 c2             	cmp    %rax,%rdx
    3bca:	75 e4                	jne    3bb0 <timer_thread+0x170>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    3bcc:	48 83 c1 08          	add    $0x8,%rcx
    3bd0:	48 39 cf             	cmp    %rcx,%rdi
    3bd3:	75 aa                	jne    3b7f <timer_thread+0x13f>
  asm volatile ("mfence" ::: "memory");
    3bd5:	0f ae f0             	mfence
  struct timespec drain = {
    3bd8:	66 0f 6f 05 80 3e 00 00 	movdqa 0x3e80(%rip),%xmm0        # 7a60 <_IO_stdin_used+0xa60>
    3be0:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3be5:	48 63 45 28          	movslq 0x28(%rbp),%rax
    y++;
    3be9:	45 8d 44 24 01       	lea    0x1(%r12),%r8d
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bee:	85 c0                	test   %eax,%eax
    3bf0:	7e 4b                	jle    3c3d <timer_thread+0x1fd>
    3bf2:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3bf6:	4d 63 e4             	movslq %r12d,%r12
    3bf9:	49 c1 e4 09          	shl    $0x9,%r12
    3bfd:	48 8d 3c c1          	lea    (%rcx,%rax,8),%rdi
    3c01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3c08:	48 8b 19             	mov    (%rcx),%rbx
    3c0b:	44 89 c0             	mov    %r8d,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c0e:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3c12:	99                   	cltd
    3c13:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3c16:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    3c1a:	48 63 d2             	movslq %edx,%rdx
    3c1d:	48 c1 e2 09          	shl    $0x9,%rdx
    3c21:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3c2c:	42 c7 84 26 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c38:	48 39 cf             	cmp    %rcx,%rdi
    3c3b:	75 cb                	jne    3c08 <timer_thread+0x1c8>
    asm volatile ("mfence" ::: "memory");
    3c3d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3c40:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3c44:	8b 4d 30             	mov    0x30(%rbp),%ecx
    y++;
    3c47:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3c4a:	48 8b 07             	mov    (%rdi),%rax
    y++;
    3c4d:	44 39 40 40          	cmp    %r8d,0x40(%rax)
    3c51:	45 0f 4f e0          	cmovg  %r8d,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3c55:	85 c9                	test   %ecx,%ecx
    3c57:	0f 8e 0d 01 00 00    	jle    3d6a <timer_thread+0x32a>
    3c5d:	45 31 ff             	xor    %r15d,%r15d
    int all_empty = 1;
    3c60:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    3c66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int y = 0 ; y < 2 ; y++) {
    3c70:	31 db                	xor    %ebx,%ebx
    3c72:	45 89 fd             	mov    %r15d,%r13d
    3c75:	4e 8d 34 fd 00 00 00 00 	lea    0x0(,%r15,8),%r14
    3c7d:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3c7f:	85 c9                	test   %ecx,%ecx
    3c81:	0f 8e 91 00 00 00    	jle    3d18 <timer_thread+0x2d8>
    3c87:	48 8b 7d 18          	mov    0x18(%rbp),%rdi
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3c8b:	4a 8b 14 37          	mov    (%rdi,%r14,1),%rdx
    3c8f:	48 89 d8             	mov    %rbx,%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3c92:	45 31 c0             	xor    %r8d,%r8d
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3c95:	48 c1 e0 09          	shl    $0x9,%rax
    3c99:	48 03 42 38          	add    0x38(%rdx),%rax
    3c9d:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    3ca4:	eb 1c                	jmp    3cc2 <timer_thread+0x282>
    3ca6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3cb0:	48 85 d2             	test   %rdx,%rdx
    3cb3:	7f 27                	jg     3cdc <timer_thread+0x29c>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3cb5:	41 83 c0 01          	add    $0x1,%r8d
    3cb9:	48 83 c0 28          	add    $0x28,%rax
    3cbd:	41 39 c8             	cmp    %ecx,%r8d
    3cc0:	74 7e                	je     3d40 <timer_thread+0x300>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3cc2:	48 8b 10             	mov    (%rax),%rdx
    3cc5:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    3ccc:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3cd0:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    3cd7:	4d 85 c9             	test   %r9,%r9
    3cda:	7e d4                	jle    3cb0 <timer_thread+0x270>
    3cdc:	48 83 ec 08          	sub    $0x8,%rsp
    3ce0:	89 f1                	mov    %esi,%ecx
    3ce2:	bf 01 00 00 00       	mov    $0x1,%edi
    3ce7:	31 c0                	xor    %eax,%eax
    3ce9:	52                   	push   %rdx
    3cea:	48 8d 35 6c 33 00 00 	lea    0x336c(%rip),%rsi        # 705d <_IO_stdin_used+0x5d>
    3cf1:	44 89 ea             	mov    %r13d,%edx
    3cf4:	e8 57 e7 ff ff       	call   2450 <__printf_chk@plt>
      for (int y = 0 ; y < 2 ; y++) {
    3cf9:	5a                   	pop    %rdx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3cfa:	8b 4d 30             	mov    0x30(%rbp),%ecx
      for (int y = 0 ; y < 2 ; y++) {
    3cfd:	5e                   	pop    %rsi
    3cfe:	48 83 fb 01          	cmp    $0x1,%rbx
    3d02:	74 54                	je     3d58 <timer_thread+0x318>
    3d04:	48 83 c3 01          	add    $0x1,%rbx
    3d08:	45 31 db             	xor    %r11d,%r11d
    3d0b:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3d0d:	85 c9                	test   %ecx,%ecx
    3d0f:	0f 8f 72 ff ff ff    	jg     3c87 <timer_thread+0x247>
    3d15:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3d18:	49 83 c7 01          	add    $0x1,%r15
    3d1c:	44 39 f9             	cmp    %r15d,%ecx
    3d1f:	0f 8f 4b ff ff ff    	jg     3c70 <timer_thread+0x230>
    if (all_empty == 1) {
    3d25:	41 83 fb 01          	cmp    $0x1,%r11d
    3d29:	74 3f                	je     3d6a <timer_thread+0x32a>
      nanosleep(&drain , &drainrem);
    3d2b:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3d30:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3d35:	e8 16 e6 ff ff       	call   2350 <nanosleep@plt>
    3d3a:	e9 a6 fe ff ff       	jmp    3be5 <timer_thread+0x1a5>
    3d3f:	90                   	nop
      for (int y = 0 ; y < 2 ; y++) {
    3d40:	48 83 fb 01          	cmp    $0x1,%rbx
    3d44:	74 d2                	je     3d18 <timer_thread+0x2d8>
    3d46:	48 83 c3 01          	add    $0x1,%rbx
    3d4a:	89 de                	mov    %ebx,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3d4c:	e9 3a ff ff ff       	jmp    3c8b <timer_thread+0x24b>
    3d51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3d58:	49 83 c7 01          	add    $0x1,%r15
    3d5c:	45 31 db             	xor    %r11d,%r11d
    3d5f:	44 39 f9             	cmp    %r15d,%ecx
    3d62:	0f 8f 08 ff ff ff    	jg     3c70 <timer_thread+0x230>
    3d68:	eb bb                	jmp    3d25 <timer_thread+0x2e5>
    3d6a:	48 8d 3d e3 32 00 00 	lea    0x32e3(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3d71:	e8 7a e5 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3d76:	8b 7d 44             	mov    0x44(%rbp),%edi
    3d79:	85 ff                	test   %edi,%edi
    3d7b:	0f 84 ed 00 00 00    	je     3e6e <timer_thread+0x42e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d81:	8b 45 2c             	mov    0x2c(%rbp),%eax
    3d84:	31 db                	xor    %ebx,%ebx
    3d86:	4c 8d 25 e7 32 00 00 	lea    0x32e7(%rip),%r12        # 7074 <_IO_stdin_used+0x74>
    3d8d:	4c 8d 2d fb 32 00 00 	lea    0x32fb(%rip),%r13        # 708f <_IO_stdin_used+0x8f>
    3d94:	85 c0                	test   %eax,%eax
    3d96:	7e 3b                	jle    3dd3 <timer_thread+0x393>
    3d98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3da0:	31 c0                	xor    %eax,%eax
    3da2:	89 da                	mov    %ebx,%edx
    3da4:	4c 89 e6             	mov    %r12,%rsi
    3da7:	bf 01 00 00 00       	mov    $0x1,%edi
    3dac:	e8 9f e6 ff ff       	call   2450 <__printf_chk@plt>
      data->threads[x]->running = 0;
    3db1:	48 8b 45 18          	mov    0x18(%rbp),%rax
    3db5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    3db9:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    3dbd:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    3dc4:	0f 84 d1 00 00 00    	je     3e9b <timer_thread+0x45b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3dca:	48 83 c3 01          	add    $0x1,%rbx
    3dce:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    3dd1:	7f cd                	jg     3da0 <timer_thread+0x360>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3dd3:	48 63 55 30          	movslq 0x30(%rbp),%rdx
    3dd7:	85 d2                	test   %edx,%edx
    3dd9:	7e 7d                	jle    3e58 <timer_thread+0x418>
      for (int y = 0 ; y < data->task_count ; y++) {
    3ddb:	8b 45 40             	mov    0x40(%rbp),%eax
    3dde:	85 c0                	test   %eax,%eax
    3de0:	7e 76                	jle    3e58 <timer_thread+0x418>
    3de2:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    3de5:	4c 8b 45 18          	mov    0x18(%rbp),%r8
    3de9:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3df1:	31 c9                	xor    %ecx,%ecx
    3df3:	48 c1 e6 09          	shl    $0x9,%rsi
    3df7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3e00:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3e04:	48 8b 40 38          	mov    0x38(%rax),%rax
    3e08:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3e0c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3e12:	74 1c                	je     3e30 <timer_thread+0x3f0>
    3e14:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3e1e:	48 05 00 02 00 00    	add    $0x200,%rax
    3e24:	48 39 d0             	cmp    %rdx,%rax
    3e27:	74 26                	je     3e4f <timer_thread+0x40f>
    3e29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3e30:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3e3a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3e40:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3e4a:	48 39 d0             	cmp    %rdx,%rax
    3e4d:	75 e1                	jne    3e30 <timer_thread+0x3f0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3e4f:	48 83 c1 08          	add    $0x8,%rcx
    3e53:	48 39 f9             	cmp    %rdi,%rcx
    3e56:	75 a8                	jne    3e00 <timer_thread+0x3c0>
    asm volatile ("mfence" ::: "memory");
    3e58:	0f ae f0             	mfence
    3e5b:	48 8d 3d 3f 32 00 00 	lea    0x323f(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    3e62:	e8 89 e4 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3e67:	c7 45 44 00 00 00 00 	movl   $0x0,0x44(%rbp)
    3e6e:	48 8d 3d 33 32 00 00 	lea    0x3233(%rip),%rdi        # 70a8 <_IO_stdin_used+0xa8>
    3e75:	e8 76 e4 ff ff       	call   22f0 <puts@plt>
}
    3e7a:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3e7f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3e88:	75 40                	jne    3eca <timer_thread+0x48a>
    3e8a:	48 83 c4 58          	add    $0x58,%rsp
    3e8e:	31 c0                	xor    %eax,%eax
    3e90:	5b                   	pop    %rbx
    3e91:	5d                   	pop    %rbp
    3e92:	41 5c                	pop    %r12
    3e94:	41 5d                	pop    %r13
    3e96:	41 5e                	pop    %r14
    3e98:	41 5f                	pop    %r15
    3e9a:	c3                   	ret
    3e9b:	4c 89 ef             	mov    %r13,%rdi
    3e9e:	e8 4d e4 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3ea3:	48 8b 45 18          	mov    0x18(%rbp),%rax
    3ea7:	be 01 00 00 00       	mov    $0x1,%esi
    3eac:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3eb0:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3eb4:	8b 78 60             	mov    0x60(%rax),%edi
    3eb7:	e8 44 e5 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ebc:	39 5d 2c             	cmp    %ebx,0x2c(%rbp)
    3ebf:	0f 8f db fe ff ff    	jg     3da0 <timer_thread+0x360>
    3ec5:	e9 09 ff ff ff       	jmp    3dd3 <timer_thread+0x393>
}
    3eca:	e8 61 e4 ff ff       	call   2330 <__stack_chk_fail@plt>
    3ecf:	90                   	nop

0000000000003ed0 <sendm.part.0>:
int sendm(struct BarrierTask *data) {
    3ed0:	41 57                	push   %r15
    3ed2:	41 56                	push   %r14
    3ed4:	41 55                	push   %r13
    3ed6:	41 54                	push   %r12
    3ed8:	55                   	push   %rbp
    3ed9:	53                   	push   %rbx
    3eda:	48 8d 9f 88 01 00 00 	lea    0x188(%rdi),%rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    3ee1:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    3ee7:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    3eec:	48 8d 9f 90 01 00 00 	lea    0x190(%rdi),%rbx
    3ef3:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    3ef8:	85 c0                	test   %eax,%eax
    3efa:	0f 8e 59 01 00 00    	jle    4059 <sendm.part.0+0x189>
    3f00:	49 89 fe             	mov    %rdi,%r14
    3f03:	45 31 e4             	xor    %r12d,%r12d
    3f06:	45 31 ff             	xor    %r15d,%r15d
    3f09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    3f10:	45 39 be 30 01 00 00 	cmp    %r15d,0x130(%r14)
    3f17:	0f 84 2b 01 00 00    	je     4048 <sendm.part.0+0x178>
        struct Data *them = data->mailboxes[n].higher;
    3f1d:	4d 8b 86 70 01 00 00 	mov    0x170(%r14),%r8
    3f24:	4d 01 e0             	add    %r12,%r8
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    3f27:	45 8b 48 20          	mov    0x20(%r8),%r9d
        struct Data *them = data->mailboxes[n].higher;
    3f2b:	49 8b 78 08          	mov    0x8(%r8),%rdi
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    3f2f:	41 83 f9 02          	cmp    $0x2,%r9d
    3f33:	0f 84 2f 01 00 00    	je     4068 <sendm.part.0+0x198>
        for (; them->messages_count < min;) {
    3f39:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    3f40:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    3f47:	48 39 e9             	cmp    %rbp,%rcx
    3f4a:	0f 8d ee 00 00 00    	jge    403e <sendm.part.0+0x16e>
    3f50:	49 8b 86 08 01 00 00 	mov    0x108(%r14),%rax
    3f57:	48 39 e9             	cmp    %rbp,%rcx
    3f5a:	49 89 eb             	mov    %rbp,%r11
          them->messages[them->messages_count++] = data->message; 
    3f5d:	48 8b 17             	mov    (%rdi),%rdx
    3f60:	41 0f 9c c5          	setl   %r13b
    3f64:	49 29 cb             	sub    %rcx,%r11
    3f67:	48 89 44 24 d0       	mov    %rax,-0x30(%rsp)
    3f6c:	49 8b 40 10          	mov    0x10(%r8),%rax
    3f70:	49 8d 5b ff          	lea    -0x1(%r11),%rbx
    3f74:	4c 89 5c 24 c8       	mov    %r11,-0x38(%rsp)
    3f79:	48 89 44 24 d8       	mov    %rax,-0x28(%rsp)
    3f7e:	48 83 fb 02          	cmp    $0x2,%rbx
    3f82:	0f 86 98 01 00 00    	jbe    4120 <sendm.part.0+0x250>
    3f88:	45 84 ed             	test   %r13b,%r13b
    3f8b:	0f 84 8f 01 00 00    	je     4120 <sendm.part.0+0x250>
    3f91:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    3f99:	4a 8d 04 12          	lea    (%rdx,%r10,1),%rax
    3f9d:	48 89 44 24 e0       	mov    %rax,-0x20(%rsp)
    3fa2:	49 89 c3             	mov    %rax,%r11
    3fa5:	48 8d 04 ea          	lea    (%rdx,%rbp,8),%rax
    3fa9:	48 39 44 24 e8       	cmp    %rax,-0x18(%rsp)
    3fae:	0f 83 cc 00 00 00    	jae    4080 <sendm.part.0+0x1b0>
    3fb4:	4c 89 d8             	mov    %r11,%rax
    3fb7:	4c 8b 5c 24 f0       	mov    -0x10(%rsp),%r11
    3fbc:	48 89 ce             	mov    %rcx,%rsi
    3fbf:	4c 39 d8             	cmp    %r11,%rax
    3fc2:	0f 83 b8 00 00 00    	jae    4080 <sendm.part.0+0x1b0>
    3fc8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3fd0:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    3fd7:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    3fdb:	48 83 c6 01          	add    $0x1,%rsi
    3fdf:	48 39 f5             	cmp    %rsi,%rbp
    3fe2:	7f ec                	jg     3fd0 <sendm.part.0+0x100>
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
    4011:	4d 89 58 10          	mov    %r11,0x10(%r8)
    4015:	48 89 8f 80 00 00 00 	mov    %rcx,0x80(%rdi)
    401c:	48 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%rcx
    4024:	bb 00 00 00 00       	mov    $0x0,%ebx
    4029:	48 0f 44 cb          	cmove  %rbx,%rcx
    402d:	4c 01 d2             	add    %r10,%rdx
    4030:	48 89 04 0a          	mov    %rax,(%rdx,%rcx,1)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4034:	41 83 f9 02          	cmp    $0x2,%r9d
    4038:	0f 84 c2 00 00 00    	je     4100 <sendm.part.0+0x230>
        asm volatile ("sfence" ::: "memory");
    403e:	0f ae f8             	sfence
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    4041:	41 8b 86 40 01 00 00 	mov    0x140(%r14),%eax
    4048:	41 83 c7 01          	add    $0x1,%r15d
    404c:	49 83 c4 28          	add    $0x28,%r12
    4050:	41 39 c7             	cmp    %eax,%r15d
    4053:	0f 8c b7 fe ff ff    	jl     3f10 <sendm.part.0+0x40>
}
    4059:	5b                   	pop    %rbx
    405a:	5d                   	pop    %rbp
    405b:	41 5c                	pop    %r12
    405d:	41 5d                	pop    %r13
    405f:	41 5e                	pop    %r14
    4061:	41 5f                	pop    %r15
    4063:	c3                   	ret
    4064:	0f 1f 40 00          	nopl   0x0(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4068:	8b 97 00 01 00 00    	mov    0x100(%rdi),%edx
    406e:	83 fa 01             	cmp    $0x1,%edx
    4071:	0f 84 b9 00 00 00    	je     4130 <sendm.part.0+0x260>
        else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    4077:	85 d2                	test   %edx,%edx
    4079:	74 cd                	je     4048 <sendm.part.0+0x178>
    407b:	e9 b9 fe ff ff       	jmp    3f39 <sendm.part.0+0x69>
    4080:	4c 8b 5c 24 c8       	mov    -0x38(%rsp),%r11
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
    40ae:	74 11                	je     40c1 <sendm.part.0+0x1f1>
          them->messages[them->messages_count++] = data->message; 
    40b0:	0f 11 06             	movups %xmm0,(%rsi)
        for (; them->messages_count < min;) {
    40b3:	48 83 c6 10          	add    $0x10,%rsi
    40b7:	4c 8b 5c 24 c8       	mov    -0x38(%rsp),%r11
    40bc:	48 39 f5             	cmp    %rsi,%rbp
    40bf:	74 1a                	je     40db <sendm.part.0+0x20b>
    40c1:	4c 8b 5c 24 c8       	mov    -0x38(%rsp),%r11
          them->messages[them->messages_count++] = data->message; 
    40c6:	0f 11 06             	movups %xmm0,(%rsi)
    40c9:	48 83 c6 20          	add    $0x20,%rsi
    40cd:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
        for (; them->messages_count < min;) {
    40d1:	48 39 f5             	cmp    %rsi,%rbp
    40d4:	75 f0                	jne    40c6 <sendm.part.0+0x1f6>
    40d6:	4c 89 5c 24 c8       	mov    %r11,-0x38(%rsp)
    40db:	4c 89 de             	mov    %r11,%rsi
    40de:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    40e2:	48 01 ce             	add    %rcx,%rsi
    40e5:	41 83 e3 01          	and    $0x1,%r11d
    40e9:	0f 84 f9 fe ff ff    	je     3fe8 <sendm.part.0+0x118>
          them->messages[them->messages_count++] = data->message; 
    40ef:	49 8b 86 88 01 00 00 	mov    0x188(%r14),%rax
    40f6:	48 89 04 f2          	mov    %rax,(%rdx,%rsi,8)
        for (; them->messages_count < min;) {
    40fa:	e9 e9 fe ff ff       	jmp    3fe8 <sendm.part.0+0x118>
    40ff:	90                   	nop
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    4100:	83 bf 00 01 00 00 01 	cmpl   $0x1,0x100(%rdi)
    4107:	0f 85 31 ff ff ff    	jne    403e <sendm.part.0+0x16e>
          them->available = 0;
    410d:	c7 87 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdi)
    4117:	e9 22 ff ff ff       	jmp    403e <sendm.part.0+0x16e>
    411c:	0f 1f 40 00          	nopl   0x0(%rax)
          them->messages[them->messages_count++] = data->message; 
    4120:	48 89 ce             	mov    %rcx,%rsi
    4123:	4c 8d 14 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r10
    412b:	e9 a0 fe ff ff       	jmp    3fd0 <sendm.part.0+0x100>
        for (; them->messages_count < min;) {
    4130:	48 8b 8f 80 00 00 00 	mov    0x80(%rdi),%rcx
    4137:	48 63 af 88 00 00 00 	movslq 0x88(%rdi),%rbp
    413e:	48 39 cd             	cmp    %rcx,%rbp
    4141:	0f 8f 09 fe ff ff    	jg     3f50 <sendm.part.0+0x80>
    4147:	eb c4                	jmp    410d <sendm.part.0+0x23d>
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
    41b8:	48 8d 3d e9 32 00 00 	lea    0x32e9(%rip),%rdi        # 74a8 <_IO_stdin_used+0x4a8>
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
    428d:	66 0f 6f 05 db 37 00 00 	movdqa 0x37db(%rip),%xmm0        # 7a70 <_IO_stdin_used+0xa70>
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
    42bb:	66 0f 6f 05 bd 37 00 00 	movdqa 0x37bd(%rip),%xmm0        # 7a80 <_IO_stdin_used+0xa80>
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
    4316:	66 0f 6f 05 72 37 00 00 	movdqa 0x3772(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
    431e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4326:	66 0f 6f 05 72 37 00 00 	movdqa 0x3772(%rip),%xmm0        # 7aa0 <_IO_stdin_used+0xaa0>
    432e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4336:	48 89 de             	mov    %rbx,%rsi
    4339:	48 8d 3d 82 2d 00 00 	lea    0x2d82(%rip),%rdi        # 70c2 <_IO_stdin_used+0xc2>
    4340:	e8 6b e0 ff ff       	call   23b0 <strcmp@plt>
    4345:	85 c0                	test   %eax,%eax
    4347:	75 20                	jne    4369 <send_headers+0x159>
    4349:	66 0f 6f 05 3f 37 00 00 	movdqa 0x373f(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
    4351:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4359:	66 0f 6f 05 3f 37 00 00 	movdqa 0x373f(%rip),%xmm0        # 7aa0 <_IO_stdin_used+0xaa0>
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
    4534:	66 0f 6f 05 b4 35 00 00 	movdqa 0x35b4(%rip),%xmm0        # 7af0 <_IO_stdin_used+0xaf0>
    453c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4546:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    454e:	66 0f 6f 05 aa 35 00 00 	movdqa 0x35aa(%rip),%xmm0        # 7b00 <_IO_stdin_used+0xb00>
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
    4590:	66 0f 6f 05 f8 34 00 00 	movdqa 0x34f8(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
    4598:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    45a0:	66 0f 6f 05 08 35 00 00 	movdqa 0x3508(%rip),%xmm0        # 7ab0 <_IO_stdin_used+0xab0>
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
    45f0:	66 0f 6f 05 d8 34 00 00 	movdqa 0x34d8(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    45f8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4600:	66 0f 6f 05 d8 34 00 00 	movdqa 0x34d8(%rip),%xmm0        # 7ae0 <_IO_stdin_used+0xae0>
    4608:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4610:	e9 b0 fd ff ff       	jmp    43c5 <send_headers+0x1b5>
    4615:	0f 1f 00             	nopl   (%rax)
    4618:	66 0f 6f 05 b0 34 00 00 	movdqa 0x34b0(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    4620:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4628:	66 0f 6f 05 b0 34 00 00 	movdqa 0x34b0(%rip),%xmm0        # 7ae0 <_IO_stdin_used+0xae0>
    4630:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4638:	e9 71 fd ff ff       	jmp    43ae <send_headers+0x19e>
    463d:	0f 1f 00             	nopl   (%rax)
    4640:	66 0f 6f 05 48 34 00 00 	movdqa 0x3448(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
    4648:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4650:	66 0f 6f 05 68 34 00 00 	movdqa 0x3468(%rip),%xmm0        # 7ac0 <_IO_stdin_used+0xac0>
    4658:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4660:	e9 32 fd ff ff       	jmp    4397 <send_headers+0x187>
    4665:	0f 1f 00             	nopl   (%rax)
    4668:	66 0f 6f 05 60 34 00 00 	movdqa 0x3460(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    4670:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4678:	66 0f 6f 05 a0 34 00 00 	movdqa 0x34a0(%rip),%xmm0        # 7b20 <_IO_stdin_used+0xb20>
    4680:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4688:	e9 6f fd ff ff       	jmp    43fc <send_headers+0x1ec>
    468d:	0f 1f 00             	nopl   (%rax)
    4690:	66 0f 6f 05 38 34 00 00 	movdqa 0x3438(%rip),%xmm0        # 7ad0 <_IO_stdin_used+0xad0>
    4698:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    46a0:	66 0f 6f 05 68 34 00 00 	movdqa 0x3468(%rip),%xmm0        # 7b10 <_IO_stdin_used+0xb10>
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
    471c:	48 8d 3d 85 2d 00 00 	lea    0x2d85(%rip),%rdi        # 74a8 <_IO_stdin_used+0x4a8>
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
    47e0:	48 8d 3d c1 2c 00 00 	lea    0x2cc1(%rip),%rdi        # 74a8 <_IO_stdin_used+0x4a8>
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
    4a96:	48 8d 3d 0b 2a 00 00 	lea    0x2a0b(%rip),%rdi        # 74a8 <_IO_stdin_used+0x4a8>
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
    4d08:	48 8d 3d 99 27 00 00 	lea    0x2799(%rip),%rdi        # 74a8 <_IO_stdin_used+0x4a8>
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
    563a:	48 8d 15 97 1e 00 00 	lea    0x1e97(%rip),%rdx        # 74d8 <_IO_stdin_used+0x4d8>
    5641:	31 c0                	xor    %eax,%eax
    5643:	e8 88 ce ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5648:	bf 01 00 00 00       	mov    $0x1,%edi
    564d:	e8 4e ce ff ff       	call   24a0 <exit@plt>
    5652:	48 8b 0d c7 49 00 00 	mov    0x49c7(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5659:	ba 28 00 00 00       	mov    $0x28,%edx
    565e:	be 01 00 00 00       	mov    $0x1,%esi
    5663:	48 8d 3d 3e 1e 00 00 	lea    0x1e3e(%rip),%rdi        # 74a8 <_IO_stdin_used+0x4a8>
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
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5a74:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    5a7a:	85 c0                	test   %eax,%eax
    5a7c:	0f 8e 5c 01 00 00    	jle    5bde <receive+0x16e>
int receive(struct BarrierTask *data) {
    5a82:	41 57                	push   %r15
    5a84:	48 89 fa             	mov    %rdi,%rdx
    5a87:	41 56                	push   %r14
    5a89:	41 55                	push   %r13
    5a8b:	45 31 ed             	xor    %r13d,%r13d
    5a8e:	41 54                	push   %r12
    5a90:	45 31 e4             	xor    %r12d,%r12d
    5a93:	55                   	push   %rbp
    5a94:	53                   	push   %rbx
    5a95:	48 83 ec 08          	sub    $0x8,%rsp
    5a99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    struct Data *me = data->mailboxes[n].lower;
    5aa0:	48 8b b2 70 01 00 00 	mov    0x170(%rdx),%rsi
    5aa7:	4c 01 ee             	add    %r13,%rsi
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5aaa:	44 8b 76 20          	mov    0x20(%rsi),%r14d
    struct Data *me = data->mailboxes[n].lower;
    5aae:	48 8b 2e             	mov    (%rsi),%rbp
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5ab1:	41 83 fe 02          	cmp    $0x2,%r14d
    5ab5:	0f 84 fd 00 00 00    	je     5bb8 <receive+0x148>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5abb:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    5ac2:	48 85 ff             	test   %rdi,%rdi
    5ac5:	0f 8e 9b 00 00 00    	jle    5b66 <receive+0xf6>
      data->sends++;
    5acb:	4c 8b 8a 78 01 00 00 	mov    0x178(%rdx),%r9
      data->n++;
    5ad2:	4c 8b 82 08 01 00 00 	mov    0x108(%rdx),%r8
      data->mailboxes[n].received++;
    5ad9:	31 c0                	xor    %eax,%eax
    5adb:	48 8b 4e 18          	mov    0x18(%rsi),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5adf:	48 8b 5d 00          	mov    0x0(%rbp),%rbx
    5ae3:	4d 8d 51 01          	lea    0x1(%r9),%r10
    5ae7:	4c 63 5a 04          	movslq 0x4(%rdx),%r11
    5aeb:	4d 8d 48 01          	lea    0x1(%r8),%r9
    5aef:	4c 8d 41 01          	lea    0x1(%rcx),%r8
    5af3:	eb 0c                	jmp    5b01 <receive+0x91>
    5af5:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5af8:	48 83 c0 01          	add    $0x1,%rax
    5afc:	48 39 f8             	cmp    %rdi,%rax
    5aff:	7d 5f                	jge    5b60 <receive+0xf0>
      data->sends++;
    5b01:	49 8d 0c 02          	lea    (%r10,%rax,1),%rcx
    5b05:	48 89 8a 78 01 00 00 	mov    %rcx,0x178(%rdx)
      data->n++;
    5b0c:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    5b10:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5b17:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5b1b:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5b1f:	48 8b 0c c3          	mov    (%rbx,%rax,8),%rcx
    5b23:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5b27:	75 cf                	jne    5af8 <receive+0x88>
    5b29:	4c 63 ba 30 01 00 00 	movslq 0x130(%rdx),%r15
    5b30:	4c 39 79 08          	cmp    %r15,0x8(%rcx)
    5b34:	75 c2                	jne    5af8 <receive+0x88>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5b36:	bf 01 00 00 00       	mov    $0x1,%edi
    5b3b:	b9 01 00 00 00       	mov    $0x1,%ecx
    5b40:	ba 01 00 00 00       	mov    $0x1,%edx
    5b45:	31 c0                	xor    %eax,%eax
    5b47:	48 8d 35 b2 19 00 00 	lea    0x19b2(%rip),%rsi        # 7500 <_IO_stdin_used+0x500>
    5b4e:	e8 fd c8 ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5b53:	bf 01 00 00 00       	mov    $0x1,%edi
    5b58:	e8 43 c9 ff ff       	call   24a0 <exit@plt>
    5b5d:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5b60:	41 83 fe 02          	cmp    $0x2,%r14d
    5b64:	74 3a                	je     5ba0 <receive+0x130>
    me->messages_count = 0;
    5b66:	48 c7 85 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rbp)
    asm volatile ("sfence" ::: "memory");
    5b71:	0f ae f8             	sfence
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    5b74:	8b 82 40 01 00 00    	mov    0x140(%rdx),%eax
    5b7a:	41 83 c4 01          	add    $0x1,%r12d
    5b7e:	49 83 c5 28          	add    $0x28,%r13
    5b82:	41 39 c4             	cmp    %eax,%r12d
    5b85:	0f 8c 15 ff ff ff    	jl     5aa0 <receive+0x30>
}
    5b8b:	48 83 c4 08          	add    $0x8,%rsp
    5b8f:	31 c0                	xor    %eax,%eax
    5b91:	5b                   	pop    %rbx
    5b92:	5d                   	pop    %rbp
    5b93:	41 5c                	pop    %r12
    5b95:	41 5d                	pop    %r13
    5b97:	41 5e                	pop    %r14
    5b99:	41 5f                	pop    %r15
    5b9b:	c3                   	ret
    5b9c:	0f 1f 40 00          	nopl   0x0(%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5ba0:	83 bd 00 01 00 00 01 	cmpl   $0x1,0x100(%rbp)
    5ba7:	75 bd                	jne    5b66 <receive+0xf6>
      me->available = 0;
    5ba9:	c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rbp)
    5bb3:	eb b1                	jmp    5b66 <receive+0xf6>
    5bb5:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    5bb8:	8b 8d 00 01 00 00    	mov    0x100(%rbp),%ecx
    5bbe:	83 f9 01             	cmp    $0x1,%ecx
    5bc1:	74 09                	je     5bcc <receive+0x15c>
    else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 0) {
    5bc3:	85 c9                	test   %ecx,%ecx
    5bc5:	74 b3                	je     5b7a <receive+0x10a>
    5bc7:	e9 ef fe ff ff       	jmp    5abb <receive+0x4b>
    for (int x = 0 ; x < me->messages_count ; x++) {
    5bcc:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    5bd3:	48 85 ff             	test   %rdi,%rdi
    5bd6:	0f 8f ef fe ff ff    	jg     5acb <receive+0x5b>
    5bdc:	eb cb                	jmp    5ba9 <receive+0x139>
}
    5bde:	31 c0                	xor    %eax,%eax
    5be0:	c3                   	ret
    5be1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5bec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005bf0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5bf0:	f3 0f 1e fa          	endbr64
    5bf4:	41 56                	push   %r14
    5bf6:	55                   	push   %rbp
    5bf7:	53                   	push   %rbx
    5bf8:	48 89 fb             	mov    %rdi,%rbx
  if (data->thread_index == data->task_index) {
    5bfb:	8b 47 04             	mov    0x4(%rdi),%eax
    5bfe:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    5c04:	74 4a                	je     5c50 <barriered_work+0x60>
    receive(data);
    5c06:	e8 65 fe ff ff       	call   5a70 <receive>
    while (data->scheduled == 1) {
    5c0b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    5c12:	75 18                	jne    5c2c <barriered_work+0x3c>
    5c14:	0f 1f 40 00          	nopl   0x0(%rax)
      data->n++;
    5c18:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    5c20:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5c23:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    5c2a:	74 ec                	je     5c18 <barriered_work+0x28>
  if (data->sending == 1) {
    5c2c:	83 bb 80 01 00 00 01 	cmpl   $0x1,0x180(%rbx)
    5c33:	75 08                	jne    5c3d <barriered_work+0x4d>
    5c35:	48 89 df             	mov    %rbx,%rdi
    5c38:	e8 93 e2 ff ff       	call   3ed0 <sendm.part.0>
  asm volatile ("sfence" ::: "memory");
    5c3d:	0f ae f8             	sfence
}
    5c40:	31 c0                	xor    %eax,%eax
    5c42:	5b                   	pop    %rbx
    5c43:	5d                   	pop    %rbp
    5c44:	41 5e                	pop    %r14
    5c46:	c3                   	ret
    5c47:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      receive(data);
    5c50:	e8 1b fe ff ff       	call   5a70 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    5c55:	48 63 8b 40 01 00 00 	movslq 0x140(%rbx),%rcx
        int t = data->task_index;
    5c5c:	8b 43 04             	mov    0x4(%rbx),%eax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    5c5f:	85 c9                	test   %ecx,%ecx
    5c61:	0f 8e d6 00 00 00    	jle    5d3d <barriered_work+0x14d>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    5c67:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    5c6e:	4c 63 d0             	movslq %eax,%r10
              int next_task = abs((t + 1) % (data->thread_count));
    5c71:	83 c0 01             	add    $0x1,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    5c74:	49 c1 e2 09          	shl    $0x9,%r10
    5c78:	48 8b 72 20          	mov    0x20(%rdx),%rsi
              int next_task = abs((t + 1) % (data->thread_count));
    5c7c:	99                   	cltd
    5c7d:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    5c83:	48 8d 6e 38          	lea    0x38(%rsi),%rbp
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5c87:	49 89 eb             	mov    %rbp,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    5c8a:	89 d0                	mov    %edx,%eax
    5c8c:	f7 d8                	neg    %eax
    5c8e:	0f 49 d0             	cmovns %eax,%edx
    5c91:	48 8d 04 49          	lea    (%rcx,%rcx,2),%rax
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5c95:	45 31 c0             	xor    %r8d,%r8d
    5c98:	48 c1 e0 06          	shl    $0x6,%rax
              int next_task = abs((t + 1) % (data->thread_count));
    5c9c:	4c 63 ca             	movslq %edx,%r9
    5c9f:	48 8d 74 06 38       	lea    0x38(%rsi,%rax,1),%rsi
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5ca4:	49 c1 e1 09          	shl    $0x9,%r9
    5ca8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    5cb0:	49 8b 03             	mov    (%r11),%rax
    5cb3:	48 89 ea             	mov    %rbp,%rdx
    5cb6:	4a 8b 84 10 70 01 00 00 	mov    0x170(%rax,%r10,1),%rax
    5cbe:	48 83 c0 08          	add    $0x8,%rax
    5cc2:	eb 3d                	jmp    5d01 <barriered_work+0x111>
    5cc4:	0f 1f 40 00          	nopl   0x0(%rax)
                 if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 0) {
    5cc8:	8b b9 00 01 00 00    	mov    0x100(%rcx),%edi
    5cce:	85 ff                	test   %edi,%edi
    5cd0:	75 1f                	jne    5cf1 <barriered_work+0x101>
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5cd2:	48 8b 3a             	mov    (%rdx),%rdi
    5cd5:	4e 8b b4 0f 70 01 00 00 	mov    0x170(%rdi,%r9,1),%r14
    5cdd:	4d 01 c6             	add    %r8,%r14
    5ce0:	49 89 0e             	mov    %rcx,(%r14)
                  ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available = 1;
    5ce3:	49 8b 4e 08          	mov    0x8(%r14),%rcx
    5ce7:	c7 81 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rcx)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    5cf1:	48 81 c2 c0 00 00 00 	add    $0xc0,%rdx
    5cf8:	48 83 c0 28          	add    $0x28,%rax
    5cfc:	48 39 d6             	cmp    %rdx,%rsi
    5cff:	74 28                	je     5d29 <barriered_work+0x139>
              if (kind == MAILBOX_FRIEND) {
    5d01:	83 78 18 01          	cmpl   $0x1,0x18(%rax)
                tmp = data->thread->all_threads[y].tasks[t].mailboxes[b].higher; 
    5d05:	48 8b 08             	mov    (%rax),%rcx
              if (kind == MAILBOX_FRIEND) {
    5d08:	75 be                	jne    5cc8 <barriered_work+0xd8>
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5d0a:	48 8b 3a             	mov    (%rdx),%rdi
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    5d0d:	48 81 c2 c0 00 00 00 	add    $0xc0,%rdx
    5d14:	48 83 c0 28          	add    $0x28,%rax
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5d18:	4a 8b bc 0f 70 01 00 00 	mov    0x170(%rdi,%r9,1),%rdi
    5d20:	4a 89 0c 07          	mov    %rcx,(%rdi,%r8,1)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    5d24:	48 39 d6             	cmp    %rdx,%rsi
    5d27:	75 d8                	jne    5d01 <barriered_work+0x111>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    5d29:	49 81 c3 c0 00 00 00 	add    $0xc0,%r11
    5d30:	49 83 c0 28          	add    $0x28,%r8
    5d34:	4c 39 de             	cmp    %r11,%rsi
    5d37:	0f 85 73 ff ff ff    	jne    5cb0 <barriered_work+0xc0>
      asm volatile ("sfence" ::: "memory");
    5d3d:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5d40:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    5d47:	31 ff                	xor    %edi,%edi
    5d49:	48 c1 e6 05          	shl    $0x5,%rsi
    5d4d:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    5d54:	e8 b7 c5 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5d59:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5d60:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5d67:	48 8b 50 48          	mov    0x48(%rax),%rdx
    5d6b:	8b 72 10             	mov    0x10(%rdx),%esi
    5d6e:	8d 6e 01             	lea    0x1(%rsi),%ebp
    5d71:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5d74:	75 5b                	jne    5dd1 <barriered_work+0x1e1>
    5d76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5d80:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    5d87:	48 8b 40 18          	mov    0x18(%rax),%rax
    5d8b:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
      data->n++;
    5d8f:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5d97:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5d9b:	48 c1 e7 09          	shl    $0x9,%rdi
    5d9f:	48 03 78 38          	add    0x38(%rax),%rdi
    5da3:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    5da9:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5dac:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    5db3:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5dba:	74 c4                	je     5d80 <barriered_work+0x190>
    if (modcount != data->thread->protected_state->modcount) {
    5dbc:	48 8b 40 48          	mov    0x48(%rax),%rax
    5dc0:	3b 68 10             	cmp    0x10(%rax),%ebp
    5dc3:	74 0c                	je     5dd1 <barriered_work+0x1e1>
    5dc5:	48 8d 3d 59 14 00 00 	lea    0x1459(%rip),%rdi        # 7225 <_IO_stdin_used+0x225>
    5dcc:	e8 1f c5 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5dd1:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    5dd8:	31 ff                	xor    %edi,%edi
    5dda:	48 c1 e6 05          	shl    $0x5,%rsi
    5dde:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    5de5:	48 83 c6 10          	add    $0x10,%rsi
    5de9:	e8 22 c5 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5dee:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    5df5:	48 83 c0 01          	add    $0x1,%rax
    5df9:	48 99                	cqto
    5dfb:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    5e02:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    5e09:	e9 1e fe ff ff       	jmp    5c2c <barriered_work+0x3c>
    5e0e:	66 90                	xchg   %ax,%ax

0000000000005e10 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    5e10:	f3 0f 1e fa          	endbr64
    5e14:	53                   	push   %rbx
    5e15:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    5e18:	e8 63 f8 ff ff       	call   5680 <barriered_work_ingest>
  barriered_work(data);
    5e1d:	48 89 df             	mov    %rbx,%rdi
}
    5e20:	5b                   	pop    %rbx
  barriered_work(data);
    5e21:	e9 ca fd ff ff       	jmp    5bf0 <barriered_work>
    5e26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005e30 <sendm>:
int sendm(struct BarrierTask *data) {
    5e30:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    5e34:	83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%rdi)
    5e3b:	74 03                	je     5e40 <sendm+0x10>
}
    5e3d:	31 c0                	xor    %eax,%eax
    5e3f:	c3                   	ret
int sendm(struct BarrierTask *data) {
    5e40:	48 83 ec 08          	sub    $0x8,%rsp
    5e44:	e8 87 e0 ff ff       	call   3ed0 <sendm.part.0>
}
    5e49:	31 c0                	xor    %eax,%eax
    5e4b:	48 83 c4 08          	add    $0x8,%rsp
    5e4f:	c3                   	ret

0000000000005e50 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5e50:	f3 0f 1e fa          	endbr64
}
    5e54:	31 c0                	xor    %eax,%eax
    5e56:	c3                   	ret
    5e57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005e60 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5e60:	f3 0f 1e fa          	endbr64
    5e64:	31 c0                	xor    %eax,%eax
    5e66:	c3                   	ret
    5e67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005e70 <after>:
int after(struct timespec left, struct timespec right) {
    5e70:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5e74:	31 c0                	xor    %eax,%eax
    5e76:	48 39 d7             	cmp    %rdx,%rdi
    5e79:	7e 08                	jle    5e83 <after+0x13>
    5e7b:	31 c0                	xor    %eax,%eax
    5e7d:	48 39 ce             	cmp    %rcx,%rsi
    5e80:	0f 9f c0             	setg   %al
}
    5e83:	c3                   	ret
    5e84:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5e8f:	90                   	nop

0000000000005e90 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5e90:	f3 0f 1e fa          	endbr64
    5e94:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5e99:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5e9e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ea0:	48 39 d7             	cmp    %rdx,%rdi
    5ea3:	7f 18                	jg     5ebd <within+0x2d>
    5ea5:	4d 39 d8             	cmp    %r11,%r8
    5ea8:	0f 9e c2             	setle  %dl
    5eab:	48 39 ce             	cmp    %rcx,%rsi
    5eae:	0f 9e c0             	setle  %al
    5eb1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5eb3:	31 c0                	xor    %eax,%eax
    5eb5:	4d 39 d1             	cmp    %r10,%r9
    5eb8:	0f 9e c0             	setle  %al
    5ebb:	21 d0                	and    %edx,%eax
}
    5ebd:	c3                   	ret
    5ebe:	66 90                	xchg   %ax,%ax

0000000000005ec0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5ec0:	f3 0f 1e fa          	endbr64
    5ec4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5ec9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5ece:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5ed3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5ed8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5edd:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5ee2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5ee7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5eec:	48 39 fe             	cmp    %rdi,%rsi
    5eef:	7d 2f                	jge    5f20 <overlap+0x60>
    5ef1:	48 39 ca             	cmp    %rcx,%rdx
    5ef4:	7d 62                	jge    5f58 <overlap+0x98>
    5ef6:	4d 39 da             	cmp    %r11,%r10
    5ef9:	7d 0e                	jge    5f09 <overlap+0x49>
    return 1;
    5efb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5f00:	4d 39 c1             	cmp    %r8,%r9
    5f03:	0f 8c 7f 00 00 00    	jl     5f88 <overlap+0xc8>
  return 0;
    5f09:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f0b:	4d 39 c1             	cmp    %r8,%r9
    5f0e:	7f 4c                	jg     5f5c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5f10:	31 c0                	xor    %eax,%eax
    5f12:	4d 39 da             	cmp    %r11,%r10
    5f15:	0f 9e c0             	setle  %al
    5f18:	c3                   	ret
    5f19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5f20:	7e 4e                	jle    5f70 <overlap+0xb0>
    5f22:	48 39 ca             	cmp    %rcx,%rdx
    5f25:	7f 39                	jg     5f60 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f27:	75 31                	jne    5f5a <overlap+0x9a>
    5f29:	4d 39 c1             	cmp    %r8,%r9
    5f2c:	7c 2c                	jl     5f5a <overlap+0x9a>
    return 1;
    5f2e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5f33:	4d 39 da             	cmp    %r11,%r10
    5f36:	7d 24                	jge    5f5c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f38:	48 39 ca             	cmp    %rcx,%rdx
    5f3b:	0f 94 c2             	sete   %dl
    5f3e:	48 39 fe             	cmp    %rdi,%rsi
    5f41:	0f 94 c0             	sete   %al
    5f44:	21 c2                	and    %eax,%edx
    5f46:	31 c0                	xor    %eax,%eax
    5f48:	4d 39 c1             	cmp    %r8,%r9
    5f4b:	0f 94 c0             	sete   %al
    5f4e:	21 d0                	and    %edx,%eax
    5f50:	c3                   	ret
    5f51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5f58:	74 af                	je     5f09 <overlap+0x49>
  return 0;
    5f5a:	31 c0                	xor    %eax,%eax
}
    5f5c:	c3                   	ret
    5f5d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5f60:	4d 39 da             	cmp    %r11,%r10
    5f63:	7e c4                	jle    5f29 <overlap+0x69>
    return 1;
    5f65:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5f6a:	4d 39 c1             	cmp    %r8,%r9
    5f6d:	7e ba                	jle    5f29 <overlap+0x69>
    5f6f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f70:	48 39 ca             	cmp    %rcx,%rdx
    5f73:	7c 94                	jl     5f09 <overlap+0x49>
    5f75:	4d 39 c1             	cmp    %r8,%r9
    5f78:	7d b4                	jge    5f2e <overlap+0x6e>
    5f7a:	48 39 ca             	cmp    %rcx,%rdx
    5f7d:	74 91                	je     5f10 <overlap+0x50>
    5f7f:	eb d9                	jmp    5f5a <overlap+0x9a>
    5f81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5f88:	c3                   	ret
    5f89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005f90 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5f90:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5f94:	85 f6                	test   %esi,%esi
    5f96:	0f 8e 44 03 00 00    	jle    62e0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    5f9c:	41 57                	push   %r15
    5f9e:	41 89 f7             	mov    %esi,%r15d
    5fa1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5fa3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5fa6:	41 55                	push   %r13
    5fa8:	41 54                	push   %r12
    5faa:	55                   	push   %rbp
    5fab:	53                   	push   %rbx
    5fac:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    5fb0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5fb4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5fb9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5fbe:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    5fc1:	45 39 e6             	cmp    %r12d,%r14d
    5fc4:	0f 84 4e 02 00 00    	je     6218 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5fca:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5fcf:	8b 50 08             	mov    0x8(%rax),%edx
    5fd2:	85 d2                	test   %edx,%edx
    5fd4:	0f 8e 3e 02 00 00    	jle    6218 <verify+0x288>
    5fda:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    5fdf:	31 c9                	xor    %ecx,%ecx
    5fe1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    5fe6:	31 c0                	xor    %eax,%eax
    5fe8:	44 89 f2             	mov    %r14d,%edx
    5feb:	bf 01 00 00 00       	mov    $0x1,%edi
    5ff0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5ff5:	48 8d 35 39 12 00 00 	lea    0x1239(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5ffc:	e8 4f c4 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6001:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6006:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    600b:	8b 40 08             	mov    0x8(%rax),%eax
    600e:	85 c0                	test   %eax,%eax
    6010:	0f 8e e6 01 00 00    	jle    61fc <verify+0x26c>
    6016:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6019:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    601e:	31 db                	xor    %ebx,%ebx
    6020:	48 c1 e0 09          	shl    $0x9,%rax
    6024:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6029:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    602e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6033:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6038:	4c 8b 20             	mov    (%rax),%r12
    603b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6040:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6045:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    604a:	49 89 de             	mov    %rbx,%r14
    604d:	48 8d 35 f6 11 00 00 	lea    0x11f6(%rip),%rsi        # 724a <_IO_stdin_used+0x24a>
    6054:	49 c1 e6 09          	shl    $0x9,%r14
    6058:	bf 01 00 00 00       	mov    $0x1,%edi
    605d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6061:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    6069:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    606e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    6076:	31 c0                	xor    %eax,%eax
    6078:	e8 d3 c3 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    607d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6082:	4c 8b 20             	mov    (%rax),%r12
    6085:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    608e:	0f 8e 47 01 00 00    	jle    61db <verify+0x24b>
    6094:	4c 03 75 00          	add    0x0(%rbp),%r14
    6098:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    609d:	ba 01 00 00 00       	mov    $0x1,%edx
    60a2:	4d 89 f5             	mov    %r14,%r13
    60a5:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    60ac:	4d 85 f6             	test   %r14,%r14
    60af:	0f 8e 21 01 00 00    	jle    61d6 <verify+0x246>
    60b5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    60b8:	48 89 d5             	mov    %rdx,%rbp
    60bb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    60c0:	31 db                	xor    %ebx,%ebx
    60c2:	4d 89 f2             	mov    %r14,%r10
    60c5:	48 c1 e5 05          	shl    $0x5,%rbp
    60c9:	48 83 ed 20          	sub    $0x20,%rbp
    60cd:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    60d1:	49 89 ee             	mov    %rbp,%r14
    60d4:	48 89 dd             	mov    %rbx,%rbp
    60d7:	48 89 d3             	mov    %rdx,%rbx
    60da:	eb 31                	jmp    610d <verify+0x17d>
    60dc:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    60e0:	4c 39 c2             	cmp    %r8,%rdx
    60e3:	0f 8d 57 01 00 00    	jge    6240 <verify+0x2b0>
    60e9:	4c 39 df             	cmp    %r11,%rdi
    60ec:	7e 05                	jle    60f3 <verify+0x163>
    60ee:	49 39 c1             	cmp    %rax,%r9
    60f1:	7c 75                	jl     6168 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    60f3:	4c 39 df             	cmp    %r11,%rdi
    60f6:	0f 8d ab 01 00 00    	jge    62a7 <verify+0x317>
    60fc:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6100:	48 83 c5 01          	add    $0x1,%rbp
    6104:	49 39 ea             	cmp    %rbp,%r10
    6107:	0f 8e a9 00 00 00    	jle    61b6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    610d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    6114:	48 89 e8             	mov    %rbp,%rax
    6117:	48 c1 e0 05          	shl    $0x5,%rax
    611b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    6122:	4c 01 f2             	add    %r14,%rdx
    6125:	48 8b 08             	mov    (%rax),%rcx
    6128:	48 8b 78 10          	mov    0x10(%rax),%rdi
    612c:	48 8b 32             	mov    (%rdx),%rsi
    612f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6133:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6137:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    613b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    613f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6143:	48 39 f1             	cmp    %rsi,%rcx
    6146:	7c 98                	jl     60e0 <verify+0x150>
    6148:	0f 8e 42 01 00 00    	jle    6290 <verify+0x300>
    614e:	4c 39 c2             	cmp    %r8,%rdx
    6151:	0f 8f f9 00 00 00    	jg     6250 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6157:	75 a7                	jne    6100 <verify+0x170>
    6159:	4c 39 df             	cmp    %r11,%rdi
    615c:	7f a2                	jg     6100 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    615e:	49 39 c1             	cmp    %rax,%r9
    6161:	7c 9d                	jl     6100 <verify+0x170>
    6163:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6168:	49 89 c1             	mov    %rax,%r9
    616b:	48 89 f9             	mov    %rdi,%rcx
    616e:	48 89 f2             	mov    %rsi,%rdx
    6171:	bf 01 00 00 00       	mov    $0x1,%edi
    6176:	48 8d 35 ab 13 00 00 	lea    0x13ab(%rip),%rsi        # 7528 <_IO_stdin_used+0x528>
    617d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    617f:	48 83 c5 01          	add    $0x1,%rbp
    6183:	e8 c8 c2 ff ff       	call   2450 <__printf_chk@plt>
    6188:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    618d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    6192:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6195:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    619a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    61a1:	4c 8b 20             	mov    (%rax),%r12
    61a4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    61a9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    61ad:	49 39 ea             	cmp    %rbp,%r10
    61b0:	0f 8f 57 ff ff ff    	jg     610d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    61b6:	48 89 da             	mov    %rbx,%rdx
    61b9:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    61c0:	7d 14                	jge    61d6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    61c2:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    61c9:	48 83 c2 01          	add    $0x1,%rdx
    61cd:	4d 85 f6             	test   %r14,%r14
    61d0:	0f 8f e2 fe ff ff    	jg     60b8 <verify+0x128>
    61d6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    61db:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    61e0:	48 83 c3 01          	add    $0x1,%rbx
    61e4:	39 58 08             	cmp    %ebx,0x8(%rax)
    61e7:	0f 8f 53 fe ff ff    	jg     6040 <verify+0xb0>
    61ed:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    61f2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    61f7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    61fc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6201:	48 83 c1 01          	add    $0x1,%rcx
    6205:	39 48 08             	cmp    %ecx,0x8(%rax)
    6208:	0f 8f d8 fd ff ff    	jg     5fe6 <verify+0x56>
    620e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6213:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6218:	48 81 44 24 10 c0 00 00 00 	addq   $0xc0,0x10(%rsp)
    6221:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6226:	41 39 c7             	cmp    %eax,%r15d
    6229:	0f 84 86 00 00 00    	je     62b5 <verify+0x325>
    622f:	41 89 c4             	mov    %eax,%r12d
    6232:	e9 8a fd ff ff       	jmp    5fc1 <verify+0x31>
    6237:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6240:	0f 85 ba fe ff ff    	jne    6100 <verify+0x170>
    6246:	e9 a8 fe ff ff       	jmp    60f3 <verify+0x163>
    624b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6250:	49 39 c1             	cmp    %rax,%r9
    6253:	7e 09                	jle    625e <verify+0x2ce>
    6255:	4c 39 df             	cmp    %r11,%rdi
    6258:	0f 8c 0a ff ff ff    	jl     6168 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    625e:	4c 39 df             	cmp    %r11,%rdi
    6261:	0f 8f 99 fe ff ff    	jg     6100 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6267:	49 39 c1             	cmp    %rax,%r9
    626a:	0f 8d f8 fe ff ff    	jge    6168 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6270:	48 39 f1             	cmp    %rsi,%rcx
    6273:	0f 85 87 fe ff ff    	jne    6100 <verify+0x170>
    6279:	4c 39 c2             	cmp    %r8,%rdx
    627c:	0f 85 7e fe ff ff    	jne    6100 <verify+0x170>
    6282:	4c 39 df             	cmp    %r11,%rdi
    6285:	0f 84 dd fe ff ff    	je     6168 <verify+0x1d8>
    628b:	e9 70 fe ff ff       	jmp    6100 <verify+0x170>
    6290:	4c 39 c2             	cmp    %r8,%rdx
    6293:	0f 8c 5a fe ff ff    	jl     60f3 <verify+0x163>
    6299:	4c 39 df             	cmp    %r11,%rdi
    629c:	7e c9                	jle    6267 <verify+0x2d7>
    629e:	4c 39 c2             	cmp    %r8,%rdx
    62a1:	0f 85 59 fe ff ff    	jne    6100 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    62a7:	49 39 c1             	cmp    %rax,%r9
    62aa:	0f 8f 50 fe ff ff    	jg     6100 <verify+0x170>
    62b0:	e9 b3 fe ff ff       	jmp    6168 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    62b5:	48 81 44 24 18 c0 00 00 00 	addq   $0xc0,0x18(%rsp)
    62be:	41 8d 46 01          	lea    0x1(%r14),%eax
    62c2:	45 39 e6             	cmp    %r12d,%r14d
    62c5:	74 08                	je     62cf <verify+0x33f>
    62c7:	41 89 c6             	mov    %eax,%r14d
    62ca:	e9 ea fc ff ff       	jmp    5fb9 <verify+0x29>
}
    62cf:	48 83 c4 58          	add    $0x58,%rsp
    62d3:	31 c0                	xor    %eax,%eax
    62d5:	5b                   	pop    %rbx
    62d6:	5d                   	pop    %rbp
    62d7:	41 5c                	pop    %r12
    62d9:	41 5d                	pop    %r13
    62db:	41 5e                	pop    %r14
    62dd:	41 5f                	pop    %r15
    62df:	c3                   	ret
    62e0:	31 c0                	xor    %eax,%eax
    62e2:	c3                   	ret

Disassembly of section .fini:

00000000000062e4 <_fini>:
    62e4:	f3 0f 1e fa          	endbr64
    62e8:	48 83 ec 08          	sub    $0x8,%rsp
    62ec:	48 83 c4 08          	add    $0x8,%rsp
    62f0:	c3                   	ret
