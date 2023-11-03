
multibarrier-prearrive:     file format elf64-x86-64


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

0000000000002540 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    2540:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

static inline void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
    2546:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    254e:	0f 0b                	ud2

0000000000002550 <add_read_request.cold>:
    2550:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2558:	0f 0b                	ud2

000000000000255a <_send_static_string_content.cold>:
    255a:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    2560:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2568:	0f 0b                	ud2

000000000000256a <add_accept_request.cold>:
    256a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2572:	0f 0b                	ud2

0000000000002574 <io_thread.cold>:
    2574:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    257c:	0f 0b                	ud2
    257e:	66 90                	xchg   %ax,%ax

0000000000002580 <main>:
    }


  return 0;
}
int main() {
    2580:	f3 0f 1e fa          	endbr64
    2584:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2586:	48 8d 3d 1b 4f 00 00 	lea    0x4f1b(%rip),%rdi        # 74a8 <_IO_stdin_used+0x4a8>
    258d:	41 56                	push   %r14
    258f:	41 55                	push   %r13
    2591:	41 54                	push   %r12
    2593:	55                   	push   %rbp
    2594:	53                   	push   %rbx
    2595:	48 81 ec a8 00 00 00 	sub    $0xa8,%rsp
    259c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    25a5:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
    25ad:	31 c0                	xor    %eax,%eax
    25af:	e8 3c fd ff ff       	call   22f0 <puts@plt>
    25b4:	bf 0a 00 00 00       	mov    $0xa,%edi
    25b9:	e8 12 fd ff ff       	call   22d0 <putchar@plt>
    25be:	48 8d 3d 6d 4c 00 00 	lea    0x4c6d(%rip),%rdi        # 7232 <_IO_stdin_used+0x232>
    25c5:	e8 26 fd ff ff       	call   22f0 <puts@plt>
    25ca:	ba 0c 00 00 00       	mov    $0xc,%edx
    25cf:	48 8d 35 78 4c 00 00 	lea    0x4c78(%rip),%rsi        # 724e <_IO_stdin_used+0x24e>
    25d6:	31 c0                	xor    %eax,%eax
    25d8:	bf 01 00 00 00       	mov    $0x1,%edi
    25dd:	e8 6e fe ff ff       	call   2450 <__printf_chk@plt>
    25e2:	ba 0f 00 00 00       	mov    $0xf,%edx
    25e7:	48 8d 35 7a 4c 00 00 	lea    0x4c7a(%rip),%rsi        # 7268 <_IO_stdin_used+0x268>
    25ee:	31 c0                	xor    %eax,%eax
    25f0:	bf 01 00 00 00       	mov    $0x1,%edi
    25f5:	e8 56 fe ff ff       	call   2450 <__printf_chk@plt>
    25fa:	ba 01 00 00 00       	mov    $0x1,%edx
    25ff:	48 8d 35 76 4c 00 00 	lea    0x4c76(%rip),%rsi        # 727c <_IO_stdin_used+0x27c>
    2606:	31 c0                	xor    %eax,%eax
    2608:	bf 01 00 00 00       	mov    $0x1,%edi
    260d:	e8 3e fe ff ff       	call   2450 <__printf_chk@plt>
    2612:	ba 01 00 00 00       	mov    $0x1,%edx
    2617:	48 8d 35 6f 4c 00 00 	lea    0x4c6f(%rip),%rsi        # 728d <_IO_stdin_used+0x28d>
    261e:	31 c0                	xor    %eax,%eax
    2620:	bf 01 00 00 00       	mov    $0x1,%edi
    2625:	e8 26 fe ff ff       	call   2450 <__printf_chk@plt>
    262a:	ba 01 00 00 00       	mov    $0x1,%edx
    262f:	48 8d 35 6f 4c 00 00 	lea    0x4c6f(%rip),%rsi        # 72a5 <_IO_stdin_used+0x2a5>
    2636:	31 c0                	xor    %eax,%eax
    2638:	bf 01 00 00 00       	mov    $0x1,%edi
    263d:	e8 0e fe ff ff       	call   2450 <__printf_chk@plt>
    2642:	ba 01 00 00 00       	mov    $0x1,%edx
    2647:	48 8d 35 c2 4e 00 00 	lea    0x4ec2(%rip),%rsi        # 7510 <_IO_stdin_used+0x510>
    264e:	31 c0                	xor    %eax,%eax
    2650:	bf 01 00 00 00       	mov    $0x1,%edi
    2655:	e8 f6 fd ff ff       	call   2450 <__printf_chk@plt>
    265a:	ba 01 00 00 00       	mov    $0x1,%edx
    265f:	48 8d 35 da 4e 00 00 	lea    0x4eda(%rip),%rsi        # 7540 <_IO_stdin_used+0x540>
    2666:	31 c0                	xor    %eax,%eax
    2668:	bf 01 00 00 00       	mov    $0x1,%edi
    266d:	e8 de fd ff ff       	call   2450 <__printf_chk@plt>
    2672:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2677:	48 8d 35 43 4c 00 00 	lea    0x4c43(%rip),%rsi        # 72c1 <_IO_stdin_used+0x2c1>
    267e:	31 c0                	xor    %eax,%eax
    2680:	bf 01 00 00 00       	mov    $0x1,%edi
    2685:	e8 c6 fd ff ff       	call   2450 <__printf_chk@plt>
    268a:	ba 05 00 00 00       	mov    $0x5,%edx
    268f:	48 8d 35 45 4c 00 00 	lea    0x4c45(%rip),%rsi        # 72db <_IO_stdin_used+0x2db>
    2696:	31 c0                	xor    %eax,%eax
    2698:	bf 01 00 00 00       	mov    $0x1,%edi
    269d:	e8 ae fd ff ff       	call   2450 <__printf_chk@plt>
    26a2:	48 8d 3d 25 4a 00 00 	lea    0x4a25(%rip),%rdi        # 70ce <_IO_stdin_used+0xce>
    26a9:	e8 42 fc ff ff       	call   22f0 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    26ae:	be 18 00 00 00       	mov    $0x18,%esi
    26b3:	bf 0c 00 00 00       	mov    $0xc,%edi
    26b8:	e8 e3 fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    26bd:	be 40 01 00 00       	mov    $0x140,%esi
    26c2:	bf 0f 00 00 00       	mov    $0xf,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    26c7:	49 89 c6             	mov    %rax,%r14
    26ca:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    26cf:	e8 cc fc ff ff       	call   23a0 <calloc@plt>
  int barrier_count = 2;
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    26d4:	be 10 00 00 00       	mov    $0x10,%esi
    26d9:	bf 01 00 00 00       	mov    $0x1,%edi
    26de:	49 8d 6e e8          	lea    -0x18(%r14),%rbp
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    26e2:	48 89 04 24          	mov    %rax,(%rsp)
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    26e6:	45 31 f6             	xor    %r14d,%r14d
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    26e9:	e8 b2 fc ff ff       	call   23a0 <calloc@plt>
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    26ee:	be 10 00 00 00       	mov    $0x10,%esi
    26f3:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    26f8:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    26fe:	48 89 c3             	mov    %rax,%rbx
    2701:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2706:	e8 95 fc ff ff       	call   23a0 <calloc@plt>
    270b:	4c 8b 1c 24          	mov    (%rsp),%r11
    }
  }
  int external_thread_index = 0;
    270f:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2717:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
    271b:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    2722:	4d 89 df             	mov    %r11,%r15
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    2725:	4c 89 5c 24 38       	mov    %r11,0x38(%rsp)
    272a:	4c 89 5c 24 48       	mov    %r11,0x48(%rsp)
    272f:	90                   	nop
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2730:	be 08 00 00 00       	mov    $0x8,%esi
    2735:	bf 02 00 00 00       	mov    $0x2,%edi
    273a:	45 89 f4             	mov    %r14d,%r12d
    273d:	e8 5e fc ff ff       	call   23a0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2742:	be 80 00 00 00       	mov    $0x80,%esi
    2747:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    274c:	48 89 04 24          	mov    %rax,(%rsp)
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2750:	e8 4b fc ff ff       	call   23a0 <calloc@plt>
    2755:	48 89 c3             	mov    %rax,%rbx
    if (x % 2 == 1) {
    2758:	44 89 f0             	mov    %r14d,%eax
    275b:	41 83 c6 01          	add    $0x1,%r14d
    275f:	83 e0 01             	and    $0x1,%eax
    2762:	85 c0                	test   %eax,%eax
    2764:	0f 84 f3 0e 00 00    	je     365d <main+0x10dd>
      my_thread_data[0] = &thread_data[other]; 
    276a:	48 8b 04 24          	mov    (%rsp),%rax
    276e:	4d 89 f8             	mov    %r15,%r8
    2771:	44 89 e2             	mov    %r12d,%edx
    2774:	bf 01 00 00 00       	mov    $0x1,%edi
    2779:	49 8d 8f c0 fe ff ff 	lea    -0x140(%r15),%rcx
      thread_data[x].thread_index = 1;
    2780:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
      other = abs(x - 1) % total_threads;
    2787:	45 8d 6c 24 ff       	lea    -0x1(%r12),%r13d
      my_thread_data[0] = &thread_data[other]; 
    278c:	48 89 08             	mov    %rcx,(%rax)
    278f:	48 8d 35 59 4b 00 00 	lea    0x4b59(%rip),%rsi        # 72ef <_IO_stdin_used+0x2ef>
      my_thread_data[1] = &thread_data[x]; 
    2796:	4c 89 78 08          	mov    %r15,0x8(%rax)
    279a:	31 c0                	xor    %eax,%eax
    279c:	e8 af fc ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    27a1:	48 8d 45 18          	lea    0x18(%rbp),%rax
    27a5:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    27aa:	49 89 af 80 00 00 00 	mov    %rbp,0x80(%r15)
    27b1:	45 8b 07             	mov    (%r15),%r8d
    27b4:	44 89 e9             	mov    %r13d,%ecx
    27b7:	44 89 e2             	mov    %r12d,%edx
    27ba:	48 8d 35 a7 4d 00 00 	lea    0x4da7(%rip),%rsi        # 7568 <_IO_stdin_used+0x568>
    27c1:	bf 01 00 00 00       	mov    $0x1,%edi
    27c6:	31 c0                	xor    %eax,%eax
      CPU_SET(j, sendercpu);
    27c8:	bd 01 00 00 00       	mov    $0x1,%ebp
    27cd:	e8 7e fc ff ff       	call   2450 <__printf_chk@plt>
    thread_data[x].other = other;
    27d2:	45 89 af 28 01 00 00 	mov    %r13d,0x128(%r15)
    for (int j = 0 ; j < cores / 2 ; j++) {
    27d9:	45 31 ed             	xor    %r13d,%r13d
    27dc:	0f 1f 40 00          	nopl   0x0(%rax)
    27e0:	44 89 e9             	mov    %r13d,%ecx
    27e3:	44 89 e2             	mov    %r12d,%edx
    27e6:	48 8d 35 ab 4d 00 00 	lea    0x4dab(%rip),%rsi        # 7598 <_IO_stdin_used+0x598>
    27ed:	31 c0                	xor    %eax,%eax
    27ef:	bf 01 00 00 00       	mov    $0x1,%edi
    27f4:	e8 57 fc ff ff       	call   2450 <__printf_chk@plt>
      CPU_SET(j, sendercpu);
    27f9:	44 89 e9             	mov    %r13d,%ecx
    27fc:	48 89 e8             	mov    %rbp,%rax
    for (int j = 0 ; j < cores / 2 ; j++) {
    27ff:	41 83 c5 01          	add    $0x1,%r13d
      CPU_SET(j, sendercpu);
    2803:	48 d3 e0             	shl    %cl,%rax
    2806:	48 09 03             	or     %rax,(%rbx)
    for (int j = 0 ; j < cores / 2 ; j++) {
    2809:	41 83 fd 06          	cmp    $0x6,%r13d
    280d:	75 d1                	jne    27e0 <main+0x260>
    thread_data[x].threads = my_thread_data;
    280f:	48 8b 04 24          	mov    (%rsp),%rax
    thread_data[x].cpu_set = sendercpu;
    2813:	49 89 9f 20 01 00 00 	mov    %rbx,0x120(%r15)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    281a:	31 db                	xor    %ebx,%ebx
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    281c:	be 10 00 00 00       	mov    $0x10,%esi
    thread_data[x].real_thread_index = x;
    2821:	45 89 67 04          	mov    %r12d,0x4(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2825:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].threads = my_thread_data;
    282a:	49 89 47 40          	mov    %rax,0x40(%r15)
    thread_data[x].thread_count = 2;
    282e:	48 8b 05 03 52 00 00 	mov    0x5203(%rip),%rax        # 7a38 <_IO_stdin_used+0xa38>
    thread_data[x].task_count = total_barrier_count;
    2835:	41 c7 47 60 03 00 00 00 	movl   $0x3,0x60(%r15)
    thread_data[x].thread_count = 2;
    283d:	49 89 47 48          	mov    %rax,0x48(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2841:	e8 5a fb ff ff       	call   23a0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2846:	be 10 00 00 00       	mov    $0x10,%esi
    284b:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2850:	49 89 87 d8 00 00 00 	mov    %rax,0xd8(%r15)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2857:	e8 44 fb ff ff       	call   23a0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    285c:	be 28 00 00 00       	mov    $0x28,%esi
    2861:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    2866:	66 0f 6f 05 b2 51 00 00 	movdqa 0x51b2(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    286e:	49 89 87 e0 00 00 00 	mov    %rax,0xe0(%r15)
    thread_data[x].timestamp_count = 0;
    2875:	41 0f 29 87 f0 00 00 00 	movaps %xmm0,0xf0(%r15)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    287d:	e8 1e fb ff ff       	call   23a0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2882:	be 80 01 00 00       	mov    $0x180,%esi
    2887:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
    288c:	66 0f 6f 0d 8c 51 00 00 	movdqa 0x518c(%rip),%xmm1        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2894:	49 89 87 00 01 00 00 	mov    %rax,0x100(%r15)
    thread_data[x].task_timestamp_count = 0;
    289b:	41 0f 11 8f 08 01 00 00 	movups %xmm1,0x108(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    28a3:	e8 f8 fa ff ff       	call   23a0 <calloc@plt>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28a8:	44 89 74 24 20       	mov    %r14d,0x20(%rsp)
      thread_data[x].tasks = barriers;
    28ad:	49 89 47 58          	mov    %rax,0x58(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    28b1:	48 89 c2             	mov    %rax,%rdx
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28b4:	44 89 24 24          	mov    %r12d,(%rsp)
        thread_data[x].tasks[y].protected = do_protected_write; 
    28b8:	4c 63 f3             	movslq %ebx,%r14
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    28bb:	be 20 00 00 00       	mov    $0x20,%esi
    28c0:	bf 0c 00 00 00       	mov    $0xc,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    28c5:	4b 8d 2c 76          	lea    (%r14,%r14,2),%rbp
    28c9:	48 8d 05 00 0f 00 00 	lea    0xf00(%rip),%rax        # 37d0 <do_protected_write>
    28d0:	48 c1 e5 07          	shl    $0x7,%rbp
    28d4:	4c 8d 2c 2a          	lea    (%rdx,%rbp,1),%r13
    28d8:	49 89 85 e0 00 00 00 	mov    %rax,0xe0(%r13)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    28df:	e8 bc fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    28e4:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    28e8:	48 89 6c 24 10       	mov    %rbp,0x10(%rsp)
    28ed:	49 89 c4             	mov    %rax,%r12
    28f0:	49 89 85 28 01 00 00 	mov    %rax,0x128(%r13)
        for (int b = 0 ; b < 2 ; b++) {
    28f7:	4c 8d 68 40          	lea    0x40(%rax),%r13
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    28fb:	be 08 00 00 00       	mov    $0x8,%esi
    2900:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    2905:	49 83 c4 20          	add    $0x20,%r12
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2909:	e8 92 fa ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    290e:	be 08 00 00 00       	mov    $0x8,%esi
    2913:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2918:	48 89 c5             	mov    %rax,%rbp
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    291b:	e8 80 fa ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    2920:	be 18 00 00 00       	mov    $0x18,%esi
    2925:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    292a:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    292d:	e8 6e fa ff ff       	call   23a0 <calloc@plt>
          mailboxes[b].higher = &data[1];
    2932:	48 8d 70 18          	lea    0x18(%rax),%rsi
          data[0].messages_count = 0;
    2936:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
          mailboxes[b].lower = &data[0];
    293e:	49 89 44 24 e0       	mov    %rax,-0x20(%r12)
          mailboxes[b].higher = &data[1];
    2943:	49 89 74 24 e8       	mov    %rsi,-0x18(%r12)
          data[0].messages = messages;
    2948:	48 89 28             	mov    %rbp,(%rax)
          data[1].messages = messages2;
    294b:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_limit = messages_limit;
    294f:	48 c7 40 10 01 00 00 00 	movq   $0x1,0x10(%rax)
          data[1].messages_count = 0;
    2957:	48 c7 40 20 00 00 00 00 	movq   $0x0,0x20(%rax)
          data[1].messages_limit = messages_limit;
    295f:	48 c7 40 28 01 00 00 00 	movq   $0x1,0x28(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    2967:	4d 39 e5             	cmp    %r12,%r13
    296a:	75 8f                	jne    28fb <main+0x37b>
        char *message = malloc(sizeof(char) * 256);
    296c:	be 01 00 00 00       	mov    $0x1,%esi
    2971:	bf 00 01 00 00       	mov    $0x100,%edi
    2976:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    297a:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    297f:	e8 1c fa ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2984:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2989:	49 89 c5             	mov    %rax,%r13
        struct Message *messaged = malloc(sizeof(struct Message));
    298c:	e8 7f fa ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2991:	44 8b 04 24          	mov    (%rsp),%r8d
    2995:	4c 89 ef             	mov    %r13,%rdi
    2998:	41 89 d9             	mov    %ebx,%r9d
    299b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    29a0:	48 8d 0d 11 4c 00 00 	lea    0x4c11(%rip),%rcx        # 75b8 <_IO_stdin_used+0x5b8>
    29a7:	ba 00 01 00 00       	mov    $0x100,%edx
    29ac:	31 c0                	xor    %eax,%eax
    29ae:	be 01 00 00 00       	mov    $0x1,%esi
    29b3:	e8 68 fb ff ff       	call   2520 <__sprintf_chk@plt>
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    29b8:	49 8b 57 58          	mov    0x58(%r15),%rdx
        messaged->message = message;
    29bc:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    29c1:	be 20 00 00 00       	mov    $0x20,%esi
        messaged->thread_index = thread_data[x].thread_index;
    29c6:	49 63 07             	movslq (%r15),%rax
        messaged->message = message;
    29c9:	4d 89 2a             	mov    %r13,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    29cc:	4c 8d 2c 2a          	lea    (%rdx,%rbp,1),%r13
        messaged->task_index = y;
    29d0:	4d 89 72 10          	mov    %r14,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    29d4:	44 8d 73 01          	lea    0x1(%rbx),%r14d
        messaged->thread_index = thread_data[x].thread_index;
    29d8:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    29dc:	45 89 b5 48 01 00 00 	mov    %r14d,0x148(%r13)
        thread_data[x].tasks[y].message = messaged;
    29e3:	4d 89 95 40 01 00 00 	mov    %r10,0x140(%r13)
        thread_data[x].tasks[y].sending = 1;
    29ea:	41 c7 85 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%r13)
        thread_data[x].tasks[y].snapshot_count = 99;
    29f5:	49 c7 85 10 01 00 00 63 00 00 00 	movq   $0x63,0x110(%r13)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a00:	49 8b bd 10 01 00 00 	mov    0x110(%r13),%rdi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a07:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
        messaged->thread_index = thread_data[x].thread_index;
    2a0c:	89 44 24 10          	mov    %eax,0x10(%rsp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a10:	e8 8b f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a15:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
        if (y == barrier_count - 1) {
    2a19:	83 fb 01             	cmp    $0x1,%ebx
    2a1c:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a21:	49 89 85 08 01 00 00 	mov    %rax,0x108(%r13)
        thread_data[x].tasks[y].current_snapshot = 0;
    2a28:	49 c7 85 18 01 00 00 00 00 00 00 	movq   $0x0,0x118(%r13)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a33:	41 89 8d f0 00 00 00 	mov    %ecx,0xf0(%r13)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2a3a:	4d 89 bd e8 00 00 00 	mov    %r15,0xe8(%r13)
        thread_data[x].tasks[y].available = 1;
    2a41:	41 c7 85 f8 00 00 00 01 00 00 00 	movl   $0x1,0xf8(%r13)
        thread_data[x].tasks[y].arrived = 0;
    2a4c:	41 c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r13)
        thread_data[x].tasks[y].thread_count = 2;
    2a57:	41 c7 85 f4 00 00 00 02 00 00 00 	movl   $0x2,0xf4(%r13)
        thread_data[x].tasks[y].task_count = total_barrier_count;
    2a62:	41 c7 85 fc 00 00 00 03 00 00 00 	movl   $0x3,0xfc(%r13)
        thread_data[x].tasks[y].worker_count = thread_count;
    2a6d:	41 c7 85 3c 01 00 00 0c 00 00 00 	movl   $0xc,0x13c(%r13)
        thread_data[x].tasks[y].task_index = y;
    2a78:	41 89 5d 00          	mov    %ebx,0x0(%r13)
        if (y == barrier_count - 1) {
    2a7c:	0f 84 c3 0b 00 00    	je     3645 <main+0x10c5>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2a82:	8b 04 24             	mov    (%rsp),%eax
    2a85:	39 d8                	cmp    %ebx,%eax
    2a87:	75 57                	jne    2ae0 <main+0x560>
    2a89:	8b 4c 24 18          	mov    0x18(%rsp),%ecx
    2a8d:	85 c9                	test   %ecx,%ecx
    2a8f:	75 4f                	jne    2ae0 <main+0x560>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2a91:	89 c2                	mov    %eax,%edx
    2a93:	48 8d 35 46 4b 00 00 	lea    0x4b46(%rip),%rsi        # 75e0 <_IO_stdin_used+0x5e0>
    2a9a:	bf 01 00 00 00       	mov    $0x1,%edi
    2a9f:	31 c0                	xor    %eax,%eax
    2aa1:	e8 aa f9 ff ff       	call   2450 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2aa6:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2aab:	49 8b 57 58          	mov    0x58(%r15),%rdx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2aaf:	c7 44 24 18 01 00 00 00 	movl   $0x1,0x18(%rsp)
    2ab7:	49 89 87 c0 00 00 00 	mov    %rax,0xc0(%r15)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2abe:	48 01 d5             	add    %rdx,%rbp
    2ac1:	48 8d 05 d8 30 00 00 	lea    0x30d8(%rip),%rax        # 5ba0 <barriered_work_ingest>
    2ac8:	48 89 85 d8 00 00 00 	mov    %rax,0xd8(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2acf:	41 83 fe 03          	cmp    $0x3,%r14d
    2ad3:	74 1f                	je     2af4 <main+0x574>
    2ad5:	bb 01 00 00 00       	mov    $0x1,%ebx
    2ada:	e9 d9 fd ff ff       	jmp    28b8 <main+0x338>
    2adf:	90                   	nop
            thread_data[x].tasks[y].run = barriered_work; 
    2ae0:	48 8d 05 49 2d 00 00 	lea    0x2d49(%rip),%rax        # 5830 <barriered_work>
    2ae7:	49 89 85 d8 00 00 00 	mov    %rax,0xd8(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2aee:	41 83 fe 03          	cmp    $0x3,%r14d
    2af2:	75 e1                	jne    2ad5 <main+0x555>

          }
        }
      }
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
    2af4:	48 8d 05 d5 0c 00 00 	lea    0xcd5(%rip),%rax        # 37d0 <do_protected_write>
    2afb:	44 8b 74 24 20       	mov    0x20(%rsp),%r14d
  for (int x = 0 ; x < total_threads ; x++) {
    2b00:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
    2b05:	48 89 82 e0 03 00 00 	mov    %rax,0x3e0(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b0c:	48 8d 05 0d 0d 00 00 	lea    0xd0d(%rip),%rax        # 3820 <barriered_reset>
    2b13:	48 89 82 d8 03 00 00 	mov    %rax,0x3d8(%rdx)
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2b1a:	4c 89 ba e8 03 00 00 	mov    %r15,0x3e8(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2b21:	49 81 c7 40 01 00 00 	add    $0x140,%r15
      thread_data[x].tasks[barrier_count].available = 1; 
    2b28:	c7 82 f8 03 00 00 01 00 00 00 	movl   $0x1,0x3f8(%rdx)
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2b32:	c7 82 80 03 00 00 00 00 00 00 	movl   $0x0,0x380(%rdx)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2b3c:	c7 82 00 03 00 00 02 00 00 00 	movl   $0x2,0x300(%rdx)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b46:	c7 82 f4 03 00 00 02 00 00 00 	movl   $0x2,0x3f4(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2b50:	41 8b 87 c0 fe ff ff 	mov    -0x140(%r15),%eax
    2b57:	89 82 f0 03 00 00    	mov    %eax,0x3f0(%rdx)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2b5d:	c7 82 3c 04 00 00 0c 00 00 00 	movl   $0xc,0x43c(%rdx)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2b67:	c7 82 fc 03 00 00 03 00 00 00 	movl   $0x3,0x3fc(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2b71:	41 83 fe 0f          	cmp    $0xf,%r14d
    2b75:	0f 85 b5 fb ff ff    	jne    2730 <main+0x1b0>
    2b7b:	4c 8b 5c 24 38       	mov    0x38(%rsp),%r11
    2b80:	ba 0d 00 00 00       	mov    $0xd,%edx
    2b85:	48 8d 35 80 47 00 00 	lea    0x4780(%rip),%rsi        # 730c <_IO_stdin_used+0x30c>
    2b8c:	31 c0                	xor    %eax,%eax
    2b8e:	bf 01 00 00 00       	mov    $0x1,%edi
    2b93:	4c 8b 64 24 48       	mov    0x48(%rsp),%r12
    2b98:	4c 89 1c 24          	mov    %r11,(%rsp)
    2b9c:	e8 af f8 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2ba1:	be 08 00 00 00       	mov    $0x8,%esi
    2ba6:	bf 02 00 00 00       	mov    $0x2,%edi
    2bab:	e8 f0 f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2bb0:	4c 8b 1c 24          	mov    (%rsp),%r11
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bb4:	bf 0f 00 00 00       	mov    $0xf,%edi
    my_thread_data[0] = &thread_data[x]; 
    2bb9:	4d 8d bb 40 10 00 00 	lea    0x1040(%r11),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2bc0:	4d 8d b3 80 02 00 00 	lea    0x280(%r11),%r14
    thread_data[x].threads = my_thread_data;
    2bc7:	49 89 83 80 10 00 00 	mov    %rax,0x1080(%r11)
    my_thread_data[0] = &thread_data[x]; 
    2bce:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2bd1:	49 8d 93 00 05 00 00 	lea    0x500(%r11),%rdx
    2bd8:	49 8d 8b 80 07 00 00 	lea    0x780(%r11),%rcx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2bdf:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2be3:	49 8b 43 58          	mov    0x58(%r11),%rax
    2be7:	4d 8d 8b c0 08 00 00 	lea    0x8c0(%r11),%r9
    2bee:	4d 8d 93 00 0a 00 00 	lea    0xa00(%r11),%r10
    2bf5:	49 8d b3 c0 03 00 00 	lea    0x3c0(%r11),%rsi
    2bfc:	49 8d 9b 40 06 00 00 	lea    0x640(%r11),%rbx
    thread_data[x].thread_count = 2;
    2c03:	41 c7 83 88 10 00 00 02 00 00 00 	movl   $0x2,0x1088(%r11)
    thread_data[n].tasks[0].scheduled = 1;
    2c0e:	48 89 54 24 50       	mov    %rdx,0x50(%rsp)
    2c13:	4d 8d 83 40 0b 00 00 	lea    0xb40(%r11),%r8
    2c1a:	49 8d ab 80 0c 00 00 	lea    0xc80(%r11),%rbp
    2c21:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    2c26:	4d 8d ab c0 0d 00 00 	lea    0xdc0(%r11),%r13
    thread_data[x].thread_index = 0;
    2c2d:	41 c7 83 40 10 00 00 00 00 00 00 	movl   $0x0,0x1040(%r11)
    thread_data[x].task_count = total_barrier_count;
    2c38:	41 c7 83 a0 10 00 00 03 00 00 00 	movl   $0x3,0x10a0(%r11)
    thread_data[n].tasks[0].scheduled = 1;
    2c43:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2c4d:	49 8d 83 40 01 00 00 	lea    0x140(%r11),%rax
    2c54:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2c59:	49 8b 83 98 01 00 00 	mov    0x198(%r11),%rax
    2c60:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2c65:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2c6f:	49 8b 83 d8 02 00 00 	mov    0x2d8(%r11),%rax
    2c76:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    2c7b:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2c85:	49 8b 83 18 04 00 00 	mov    0x418(%r11),%rax
    my_thread_data[0] = &thread_data[x]; 
    2c8c:	4c 89 7c 24 60       	mov    %r15,0x60(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2c91:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2c9b:	49 8b 83 58 05 00 00 	mov    0x558(%r11),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2ca2:	4c 89 74 24 68       	mov    %r14,0x68(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2ca7:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2cb1:	49 8b 83 98 06 00 00 	mov    0x698(%r11),%rax
    2cb8:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cbd:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2cc2:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2ccc:	49 8b 83 d8 07 00 00 	mov    0x7d8(%r11),%rax
    2cd3:	48 89 5c 24 58       	mov    %rbx,0x58(%rsp)
    2cd8:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2ce2:	49 8b 83 18 09 00 00 	mov    0x918(%r11),%rax
    2ce9:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2cf3:	49 8b 83 58 0a 00 00 	mov    0xa58(%r11),%rax
    2cfa:	4c 89 44 24 20       	mov    %r8,0x20(%rsp)
    2cff:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2d09:	49 8b 83 98 0b 00 00 	mov    0xb98(%r11),%rax
    2d10:	4c 89 5c 24 70       	mov    %r11,0x70(%rsp)
    2d15:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2d1f:	49 8b 83 d8 0c 00 00 	mov    0xcd8(%r11),%rax
    2d26:	48 89 6c 24 28       	mov    %rbp,0x28(%rsp)
    2d2b:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2d35:	49 8b 83 18 0e 00 00 	mov    0xe18(%r11),%rax
    2d3c:	4c 89 2c 24          	mov    %r13,(%rsp)
    2d40:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d4a:	e8 51 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d4f:	be 38 00 00 00       	mov    $0x38,%esi
    2d54:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d59:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d5c:	e8 3f f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d61:	be 38 00 00 00       	mov    $0x38,%esi
    2d66:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d6b:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d6e:	e8 2d f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d73:	be 38 00 00 00       	mov    $0x38,%esi
    2d78:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d7d:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d82:	e8 19 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d87:	be 08 00 00 00       	mov    $0x8,%esi
    2d8c:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d91:	48 89 84 24 80 00 00 00 	mov    %rax,0x80(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d99:	e8 02 f6 ff ff       	call   23a0 <calloc@plt>

  thread_data[thread_count].type = TIMER;
    2d9e:	4c 8b 5c 24 70       	mov    0x70(%rsp),%r11
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2da3:	be 08 00 00 00       	mov    $0x8,%esi
    2da8:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2dad:	49 89 c5             	mov    %rax,%r13
  thread_data[thread_count].type = TIMER;
    2db0:	41 c7 83 08 0f 00 00 00 00 00 00 	movl   $0x0,0xf08(%r11)
  thread_data[thread_count].running = 1;
    2dbb:	41 c7 83 64 0f 00 00 01 00 00 00 	movl   $0x1,0xf64(%r11)
  thread_data[thread_count].task_count = total_barrier_count;
    2dc6:	41 c7 83 60 0f 00 00 03 00 00 00 	movl   $0x3,0xf60(%r11)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2dd1:	e8 ca f5 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2dd6:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    2ddb:	4c 8b 5c 24 70       	mov    0x70(%rsp),%r11
    2de0:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    2de5:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
    2dea:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2dee:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2df2:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
    2df7:	4d 8d b3 00 0f 00 00 	lea    0xf00(%r11),%r14
    2dfe:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    2e03:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2e08:	4c 89 18             	mov    %r11,(%rax)
    2e0b:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    2e10:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    2e15:	48 89 78 28          	mov    %rdi,0x28(%rax)
    2e19:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    2e1e:	48 89 70 18          	mov    %rsi,0x18(%rax)
    2e22:	48 8d 35 f2 44 00 00 	lea    0x44f2(%rip),%rsi        # 731b <_IO_stdin_used+0x31b>
    2e29:	48 89 50 20          	mov    %rdx,0x20(%rax)
    2e2d:	ba 0c 00 00 00       	mov    $0xc,%edx
    2e32:	48 89 78 50          	mov    %rdi,0x50(%rax)
    2e36:	48 8b 3c 24          	mov    (%rsp),%rdi
    2e3a:	48 89 48 30          	mov    %rcx,0x30(%rax)
    2e3e:	48 89 78 58          	mov    %rdi,0x58(%rax)
    2e42:	49 8d bb 80 11 00 00 	lea    0x1180(%r11),%rdi
    2e49:	4c 89 48 38          	mov    %r9,0x38(%rax)
    2e4d:	4c 89 50 40          	mov    %r10,0x40(%rax)
    2e51:	4c 89 40 48          	mov    %r8,0x48(%rax)
    2e55:	4c 89 70 60          	mov    %r14,0x60(%rax)
    2e59:	4c 89 78 68          	mov    %r15,0x68(%rax)
    2e5d:	4c 8d 3d 6c 0a 00 00 	lea    0xa6c(%rip),%r15        # 38d0 <barriered_thread>
    2e64:	48 89 78 70          	mov    %rdi,0x70(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2e68:	49 89 83 40 0f 00 00 	mov    %rax,0xf40(%r11)
    2e6f:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2e71:	41 c7 83 48 0f 00 00 0c 00 00 00 	movl   $0xc,0xf48(%r11)
  thread_data[thread_count].my_thread_count = 2;
    2e7c:	41 c7 83 50 0f 00 00 02 00 00 00 	movl   $0x2,0xf50(%r11)
  thread_data[thread_count].thread_index = 0;
    2e87:	41 c7 83 00 0f 00 00 00 00 00 00 	movl   $0x0,0xf00(%r11)
    my_thread_data[n] = &thread_data[n]; 
    2e92:	48 89 7c 24 70       	mov    %rdi,0x70(%rsp)
    2e97:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].thread_index = 0;
    2e9c:	4c 89 9c 24 88 00 00 00 	mov    %r11,0x88(%rsp)
    2ea4:	e8 a7 f5 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2ea9:	48 8d b3 a0 02 00 00 	lea    0x2a0(%rbx),%rsi
    2eb0:	49 8d 7d 60          	lea    0x60(%r13),%rdi
    2eb4:	4c 89 f1             	mov    %r14,%rcx
    2eb7:	4c 89 eb             	mov    %r13,%rbx
  for (int x = 0 ; x < thread_count ; x++) {
    2eba:	45 31 f6             	xor    %r14d,%r14d
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2ebd:	48 8d 15 bc 0d 00 00 	lea    0xdbc(%rip),%rdx        # 3c80 <timer_thread>
    2ec4:	e8 a7 f5 ff ff       	call   2470 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2ec9:	45 89 f5             	mov    %r14d,%r13d
    2ecc:	49 89 de             	mov    %rbx,%r14
    thread_data[x].type = WORKER;
    2ecf:	41 c7 44 24 08 01 00 00 00 	movl   $0x1,0x8(%r12)
    2ed8:	44 89 ea             	mov    %r13d,%edx
    2edb:	bf 01 00 00 00       	mov    $0x1,%edi
    2ee0:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2ee2:	41 c7 44 24 64 01 00 00 00 	movl   $0x1,0x64(%r12)
    2eeb:	48 8d 35 0e 47 00 00 	lea    0x470e(%rip),%rsi        # 7600 <_IO_stdin_used+0x600>
  for (int x = 0 ; x < thread_count ; x++) {
    2ef2:	41 83 c5 01          	add    $0x1,%r13d
    2ef6:	e8 55 f5 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2efb:	4c 89 e1             	mov    %r12,%rcx
    2efe:	48 89 ee             	mov    %rbp,%rsi
    2f01:	48 89 df             	mov    %rbx,%rdi
    2f04:	4c 89 fa             	mov    %r15,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2f07:	49 81 c4 40 01 00 00 	add    $0x140,%r12
    2f0e:	48 83 c3 08          	add    $0x8,%rbx
    2f12:	48 83 c5 38          	add    $0x38,%rbp
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2f16:	e8 55 f5 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2f1b:	49 8b 54 24 e0       	mov    -0x20(%r12),%rdx
    2f20:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    2f24:	be 08 00 00 00       	mov    $0x8,%esi
    2f29:	e8 b2 f3 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2f2e:	41 83 fd 0c          	cmp    $0xc,%r13d
    2f32:	75 9b                	jne    2ecf <main+0x94f>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2f34:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f3c:	be d8 00 00 00       	mov    $0xd8,%esi
    2f41:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    2f46:	4d 89 f5             	mov    %r14,%r13
    2f49:	41 c7 83 48 10 00 00 02 00 00 00 	movl   $0x2,0x1048(%r11)
    thread_data[x].running = 1;
    2f54:	41 c7 83 a4 10 00 00 01 00 00 00 	movl   $0x1,0x10a4(%r11)
    thread_data[x].task_count = 0;
    2f5f:	41 c7 83 a0 10 00 00 00 00 00 00 	movl   $0x0,0x10a0(%r11)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f6a:	e8 31 f4 ff ff       	call   23a0 <calloc@plt>
    2f6f:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f77:	be 00 08 00 00       	mov    $0x800,%esi
    2f7c:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f7e:	49 89 83 08 11 00 00 	mov    %rax,0x1108(%r11)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f85:	e8 26 f5 ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f8a:	be 08 00 00 00       	mov    $0x8,%esi
    2f8f:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f94:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    2f9c:	41 89 83 10 11 00 00 	mov    %eax,0x1110(%r11)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2fa3:	e8 f8 f3 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    2fa8:	4c 8b 4c 24 28       	mov    0x28(%rsp),%r9
    2fad:	4c 8b 14 24          	mov    (%rsp),%r10
    2fb1:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    2fb9:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    2fbe:	4c 8b 74 24 68       	mov    0x68(%rsp),%r14
    2fc3:	48 8b 6c 24 50       	mov    0x50(%rsp),%rbp
    2fc8:	4c 89 48 50          	mov    %r9,0x50(%rax)
    2fcc:	4c 8b 64 24 58       	mov    0x58(%rsp),%r12
    2fd1:	4c 8b 7c 24 48       	mov    0x48(%rsp),%r15
    2fd6:	4c 89 50 58          	mov    %r10,0x58(%rax)
    2fda:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    2fdf:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    2fe4:	4c 89 18             	mov    %r11,(%rax)
    2fe7:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    2fec:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    }
    thread_data[x].threads = my_thread_data;
    2ff1:	49 89 83 80 10 00 00 	mov    %rax,0x1080(%r11)
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    2ff8:	41 c7 83 88 10 00 00 0c 00 00 00 	movl   $0xc,0x1088(%r11)
    thread_data[x].thread_index = x;
    3003:	41 c7 83 40 10 00 00 0d 00 00 00 	movl   $0xd,0x1040(%r11)
      my_thread_data[n] = &thread_data[n]; 
    300e:	48 89 58 08          	mov    %rbx,0x8(%rax)
    3012:	4c 89 70 10          	mov    %r14,0x10(%rax)
    3016:	48 89 68 20          	mov    %rbp,0x20(%rax)
    301a:	4c 89 60 28          	mov    %r12,0x28(%rax)
    301e:	48 89 78 30          	mov    %rdi,0x30(%rax)
    3022:	bf 01 00 00 00       	mov    $0x1,%edi
    3027:	48 89 70 38          	mov    %rsi,0x38(%rax)
    302b:	48 8d 35 07 43 00 00 	lea    0x4307(%rip),%rsi        # 7339 <_IO_stdin_used+0x339>
    3032:	48 89 50 40          	mov    %rdx,0x40(%rax)
    3036:	ba 0d 00 00 00       	mov    $0xd,%edx
    303b:	48 89 48 48          	mov    %rcx,0x48(%rax)
    303f:	4c 89 78 18          	mov    %r15,0x18(%rax)
    3043:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3045:	4c 89 5c 24 38       	mov    %r11,0x38(%rsp)
    304a:	e8 01 f4 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    304f:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    3054:	49 8d 7d 68          	lea    0x68(%r13),%rdi
    3058:	48 8b 4c 24 60       	mov    0x60(%rsp),%rcx
    305d:	48 8d 15 bc 1e 00 00 	lea    0x1ebc(%rip),%rdx        # 4f20 <io_thread>
    3064:	48 05 d8 02 00 00    	add    $0x2d8,%rax
    306a:	48 89 c6             	mov    %rax,%rsi
    306d:	e8 fe f3 ff ff       	call   2470 <pthread_create@plt>
    3072:	ba 0e 00 00 00       	mov    $0xe,%edx
    3077:	48 8d 35 d2 42 00 00 	lea    0x42d2(%rip),%rsi        # 7350 <_IO_stdin_used+0x350>
    307e:	31 c0                	xor    %eax,%eax
    3080:	bf 01 00 00 00       	mov    $0x1,%edi
    3085:	e8 c6 f3 ff ff       	call   2450 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    308a:	4c 8b 5c 24 38       	mov    0x38(%rsp),%r11
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    308f:	48 8b 44 24 30       	mov    0x30(%rsp),%rax

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3094:	be 08 00 00 00       	mov    $0x8,%esi
    3099:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x].type = EXTERNAL;
    309e:	41 c7 83 88 11 00 00 03 00 00 00 	movl   $0x3,0x1188(%r11)
    thread_data[x].running = 1;
    30a9:	41 c7 83 e4 11 00 00 01 00 00 00 	movl   $0x1,0x11e4(%r11)
    thread_data[x].task_count = 0;
    30b4:	41 c7 83 e0 11 00 00 00 00 00 00 	movl   $0x0,0x11e0(%r11)
    thread_data[x].buffers = &buffers[buffer_index];
    30bf:	49 89 83 40 12 00 00 	mov    %rax,0x1240(%r11)
    30c6:	4c 89 5c 24 30       	mov    %r11,0x30(%rsp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    30cb:	e8 d0 f2 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    30d0:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    30d5:	4c 8b 14 24          	mov    (%rsp),%r10
    30d9:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    30de:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    30e3:	48 89 58 08          	mov    %rbx,0x8(%rax)
    30e7:	31 db                	xor    %ebx,%ebx
    30e9:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    30ee:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    30f3:	4c 89 18             	mov    %r11,(%rax)
    30f6:	4c 8b 4c 24 28       	mov    0x28(%rsp),%r9
    30fb:	4c 89 70 10          	mov    %r14,0x10(%rax)
    30ff:	48 89 68 20          	mov    %rbp,0x20(%rax)
    3103:	48 8d 2d 81 42 00 00 	lea    0x4281(%rip),%rbp        # 738b <_IO_stdin_used+0x38b>
    310a:	4c 89 60 28          	mov    %r12,0x28(%rax)
    310e:	4c 8d a4 24 90 00 00 00 	lea    0x90(%rsp),%r12
    3116:	48 89 78 30          	mov    %rdi,0x30(%rax)
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    311a:	49 8d 7d 70          	lea    0x70(%r13),%rdi
      my_thread_data[n] = &thread_data[n]; 
    311e:	48 89 70 38          	mov    %rsi,0x38(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3122:	48 8b b4 24 80 00 00 00 	mov    0x80(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    312a:	48 89 50 40          	mov    %rdx,0x40(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    312e:	48 8d 15 8b 0a 00 00 	lea    0xa8b(%rip),%rdx        # 3bc0 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    3135:	48 89 48 48          	mov    %rcx,0x48(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3139:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    313e:	48 81 c6 10 03 00 00 	add    $0x310,%rsi
      my_thread_data[n] = &thread_data[n]; 
    3145:	4c 89 48 50          	mov    %r9,0x50(%rax)
    3149:	4c 89 50 58          	mov    %r10,0x58(%rax)
    thread_data[x].threads = my_thread_data;
    314d:	49 89 83 c0 11 00 00 	mov    %rax,0x11c0(%r11)
      my_thread_data[n] = &thread_data[n]; 
    3154:	4c 89 78 18          	mov    %r15,0x18(%rax)
    thread_data[x].thread_count = thread_count;
    3158:	48 8b 05 e1 48 00 00 	mov    0x48e1(%rip),%rax        # 7a40 <_IO_stdin_used+0xa40>
    thread_data[x].thread_index = x;
    315f:	41 c7 83 80 11 00 00 0e 00 00 00 	movl   $0xe,0x1180(%r11)
    thread_data[x].thread_count = thread_count;
    316a:	49 89 83 c8 11 00 00 	mov    %rax,0x11c8(%r11)
    thread_data[x].thread_index = x;
    3171:	4c 89 1c 24          	mov    %r11,(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3175:	e8 f6 f2 ff ff       	call   2470 <pthread_create@plt>
    317a:	48 8d 3d ec 41 00 00 	lea    0x41ec(%rip),%rdi        # 736d <_IO_stdin_used+0x36d>
    3181:	e8 6a f1 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3186:	4c 8b 34 24          	mov    (%rsp),%r14
    318a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void * result; 
    pthread_join(thread[x], &result);
    3190:	49 8b 7c dd 00       	mov    0x0(%r13,%rbx,8),%rdi
    3195:	4c 89 e6             	mov    %r12,%rsi
    3198:	e8 53 f3 ff ff       	call   24f0 <pthread_join@plt>
    319d:	89 da                	mov    %ebx,%edx
    319f:	48 89 ee             	mov    %rbp,%rsi
    31a2:	bf 01 00 00 00       	mov    $0x1,%edi
    31a7:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    31a9:	48 83 c3 01          	add    $0x1,%rbx
    31ad:	e8 9e f2 ff ff       	call   2450 <__printf_chk@plt>
    31b2:	48 83 fb 0f          	cmp    $0xf,%rbx
    31b6:	75 d8                	jne    3190 <main+0xc10>
    31b8:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    31bd:	4d 89 f3             	mov    %r14,%r11
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
    31c0:	45 31 d2             	xor    %r10d,%r10d
    31c3:	4d 8d 7e 58          	lea    0x58(%r14),%r15
  long sents = 0;
  long received = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    31c7:	c7 04 24 00 00 00 00 	movl   $0x0,(%rsp)
  long total = 0;
    31ce:	45 31 f6             	xor    %r14d,%r14d
  long ingests = 0;
    31d1:	45 31 c9             	xor    %r9d,%r9d
  long received = 0;
    31d4:	31 db                	xor    %ebx,%ebx
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    31d6:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
  long sents = 0;
    31db:	31 ed                	xor    %ebp,%ebp
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    31dd:	4d 89 c8             	mov    %r9,%r8
    31e0:	49 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r13
    31ea:	4c 89 5c 24 20       	mov    %r11,0x20(%rsp)
    31ef:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    31f4:	4c 89 f8             	mov    %r15,%rax
    31f7:	4d 89 f7             	mov    %r14,%r15
    31fa:	49 89 c6             	mov    %rax,%r14
    if (x % 2 == 1) {
    31fd:	8b 3c 24             	mov    (%rsp),%edi
    3200:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    3205:	89 f8                	mov    %edi,%eax
    3207:	41 89 fc             	mov    %edi,%r12d
      other = (x + 1) % total_threads;
    320a:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
    320d:	83 e0 01             	and    $0x1,%eax
      other = abs(x - 1) % total_threads;
    3210:	41 83 ec 01          	sub    $0x1,%r12d
      other = (x + 1) % total_threads;
    3214:	89 3c 24             	mov    %edi,(%rsp)
      other = abs(x - 1) % total_threads;
    3217:	85 c0                	test   %eax,%eax
    3219:	44 0f 44 e7          	cmove  %edi,%r12d
    321d:	bf 0a 00 00 00       	mov    $0xa,%edi
    3222:	e8 a9 f0 ff ff       	call   22d0 <putchar@plt>
    3227:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    322c:	bf 01 00 00 00       	mov    $0x1,%edi
    3231:	48 8d 35 67 41 00 00 	lea    0x4167(%rip),%rsi        # 739f <_IO_stdin_used+0x39f>
    3238:	48 8b 10             	mov    (%rax),%rdx
    323b:	31 c0                	xor    %eax,%eax
    323d:	e8 0e f2 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3242:	49 63 56 08          	movslq 0x8(%r14),%rdx
    3246:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    324b:	85 d2                	test   %edx,%edx
    324d:	0f 8e 78 04 00 00    	jle    36cb <main+0x114b>
    3253:	48 8d 3c 52          	lea    (%rdx,%rdx,2),%rdi
    3257:	49 8b 06             	mov    (%r14),%rax
    long v = 0;
    325a:	31 d2                	xor    %edx,%edx
    325c:	48 c1 e7 07          	shl    $0x7,%rdi
    3260:	48 01 c7             	add    %rax,%rdi
    3263:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      v += thread_data[me].tasks[n].v;
    3268:	48 8b 88 d0 00 00 00 	mov    0xd0(%rax),%rcx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    326f:	48 05 80 01 00 00    	add    $0x180,%rax
      v += thread_data[me].tasks[n].v;
    3275:	48 01 ca             	add    %rcx,%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3278:	48 39 c7             	cmp    %rax,%rdi
    327b:	75 eb                	jne    3268 <main+0xce8>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    327d:	4d 63 e4             	movslq %r12d,%r12
    3280:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3285:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    3289:	48 c1 e0 06          	shl    $0x6,%rax
    328d:	48 01 f8             	add    %rdi,%rax
    3290:	48 63 70 60          	movslq 0x60(%rax),%rsi
    3294:	85 f6                	test   %esi,%esi
    3296:	7e 2d                	jle    32c5 <main+0xd45>
    3298:	48 8b 40 58          	mov    0x58(%rax),%rax
    329c:	48 8d 3c 76          	lea    (%rsi,%rsi,2),%rdi
    32a0:	48 c1 e7 07          	shl    $0x7,%rdi
    32a4:	48 01 c7             	add    %rax,%rdi
    32a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      v += thread_data[other].tasks[n].v;
    32b0:	48 8b 88 d0 00 00 00 	mov    0xd0(%rax),%rcx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    32b7:	48 05 80 01 00 00    	add    $0x180,%rax
      v += thread_data[other].tasks[n].v;
    32bd:	48 01 ca             	add    %rcx,%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    32c0:	48 39 c7             	cmp    %rax,%rdi
    32c3:	75 eb                	jne    32b0 <main+0xd30>
    32c5:	48 8d 35 e8 40 00 00 	lea    0x40e8(%rip),%rsi        # 73b4 <_IO_stdin_used+0x3b4>
    32cc:	bf 01 00 00 00       	mov    $0x1,%edi
    32d1:	31 c0                	xor    %eax,%eax
    32d3:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    32d8:	e8 73 f1 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    32dd:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    32e2:	bf 01 00 00 00       	mov    $0x1,%edi
    32e7:	48 8b 30             	mov    (%rax),%rsi
    32ea:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    32f4:	48 f7 ee             	imul   %rsi
    32f7:	48 c1 fe 3f          	sar    $0x3f,%rsi
    32fb:	31 c0                	xor    %eax,%eax
    32fd:	48 d1 fa             	sar    %rdx
    3300:	48 29 f2             	sub    %rsi,%rdx
    3303:	48 8d 35 1e 43 00 00 	lea    0x431e(%rip),%rsi        # 7628 <_IO_stdin_used+0x628>
    330a:	e8 41 f1 ff ff       	call   2450 <__printf_chk@plt>
    330f:	bf 0a 00 00 00       	mov    $0xa,%edi
    3314:	e8 b7 ef ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3319:	49 63 56 08          	movslq 0x8(%r14),%rdx
    331d:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    3322:	85 d2                	test   %edx,%edx
    3324:	0f 8e 32 01 00 00    	jle    345c <main+0xedc>
    332a:	49 8b 06             	mov    (%r14),%rax
    332d:	48 8d 14 52          	lea    (%rdx,%rdx,2),%rdx
    3331:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3336:	48 c1 e2 07          	shl    $0x7,%rdx
    333a:	48 01 c2             	add    %rax,%rdx
    333d:	0f 1f 00             	nopl   (%rax)
      total += thread_data[x].tasks[n].n;
    3340:	48 8b 88 c8 00 00 00 	mov    0xc8(%rax),%rcx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3347:	48 05 80 01 00 00    	add    $0x180,%rax
      total += thread_data[x].tasks[n].n;
    334d:	49 01 cf             	add    %rcx,%r15
      ingests += thread_data[x].tasks[n].ingest_count;
    3350:	48 8b 48 a0          	mov    -0x60(%rax),%rcx
    3354:	49 01 c8             	add    %rcx,%r8
      sends += thread_data[x].tasks[n].sends;
    3357:	48 8b 48 b0          	mov    -0x50(%rax),%rcx
    335b:	49 01 c9             	add    %rcx,%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    335e:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3362:	48 03 69 10          	add    0x10(%rcx),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3366:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    336a:	48 03 59 18          	add    0x18(%rcx),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    336e:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3372:	48 03 69 30          	add    0x30(%rcx),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3376:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    337a:	48 03 59 38          	add    0x38(%rcx),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    337e:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3382:	48 03 69 50          	add    0x50(%rcx),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3386:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    338a:	48 03 59 58          	add    0x58(%rcx),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    338e:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3392:	48 03 69 70          	add    0x70(%rcx),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3396:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    339a:	48 03 59 78          	add    0x78(%rcx),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    339e:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33a2:	48 03 a9 90 00 00 00 	add    0x90(%rcx),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33a9:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33ad:	48 03 99 98 00 00 00 	add    0x98(%rcx),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33b4:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33b8:	48 03 a9 b0 00 00 00 	add    0xb0(%rcx),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33bf:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33c3:	48 03 99 b8 00 00 00 	add    0xb8(%rcx),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33ca:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33ce:	48 03 a9 d0 00 00 00 	add    0xd0(%rcx),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33d5:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33d9:	48 03 99 d8 00 00 00 	add    0xd8(%rcx),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33e0:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33e4:	48 03 a9 f0 00 00 00 	add    0xf0(%rcx),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33eb:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33ef:	48 03 99 f8 00 00 00 	add    0xf8(%rcx),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33f6:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33fa:	48 03 a9 10 01 00 00 	add    0x110(%rcx),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3401:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3405:	48 03 99 18 01 00 00 	add    0x118(%rcx),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    340c:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3410:	48 03 a9 30 01 00 00 	add    0x130(%rcx),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3417:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    341b:	48 03 99 38 01 00 00 	add    0x138(%rcx),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3422:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3426:	48 03 a9 50 01 00 00 	add    0x150(%rcx),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    342d:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3431:	48 03 99 58 01 00 00 	add    0x158(%rcx),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3438:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    343c:	48 03 a9 70 01 00 00 	add    0x170(%rcx),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3443:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3447:	48 03 99 78 01 00 00 	add    0x178(%rcx),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    344e:	48 39 c2             	cmp    %rax,%rdx
    3451:	0f 85 e9 fe ff ff    	jne    3340 <main+0xdc0>
    3457:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    345c:	45 31 e4             	xor    %r12d,%r12d
    345f:	49 83 be b8 00 00 00 00 	cmpq   $0x0,0xb8(%r14)
    3467:	0f 8e 87 00 00 00    	jle    34f4 <main+0xf74>
    346d:	4c 89 f0             	mov    %r14,%rax
    3470:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    3475:	49 89 de             	mov    %rbx,%r14
    3478:	4c 89 e5             	mov    %r12,%rbp
    347b:	48 89 c3             	mov    %rax,%rbx
    347e:	4d 89 c4             	mov    %r8,%r12
    3481:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3488:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    348f:	48 8d 54 ad 00       	lea    0x0(%rbp,%rbp,4),%rdx
    3494:	48 83 ec 08          	sub    $0x8,%rsp
    3498:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    349d:	48 83 c5 01          	add    $0x1,%rbp
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    34a1:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    34a5:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    34a9:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    34ad:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    34b0:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    34b4:	4c 2b 01             	sub    (%rcx),%r8
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    34b7:	49 f7 e5             	mul    %r13
    34ba:	8b 49 20             	mov    0x20(%rcx),%ecx
    34bd:	56                   	push   %rsi
    34be:	31 c0                	xor    %eax,%eax
    34c0:	48 8d 35 81 41 00 00 	lea    0x4181(%rip),%rsi        # 7648 <_IO_stdin_used+0x648>
    34c7:	48 c1 ea 12          	shr    $0x12,%rdx
    34cb:	49 89 d1             	mov    %rdx,%r9
    34ce:	ba 02 00 00 00       	mov    $0x2,%edx
    34d3:	e8 78 ef ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    34d8:	58                   	pop    %rax
    34d9:	5a                   	pop    %rdx
    34da:	48 39 ab b8 00 00 00 	cmp    %rbp,0xb8(%rbx)
    34e1:	7f a5                	jg     3488 <main+0xf08>
    34e3:	48 89 d8             	mov    %rbx,%rax
    34e6:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    34eb:	4c 89 f3             	mov    %r14,%rbx
    34ee:	4d 89 e0             	mov    %r12,%r8
    34f1:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < thread_count ; x++) {
    34f4:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    34fa:	49 81 c6 40 01 00 00 	add    $0x140,%r14
    3501:	83 3c 24 0c          	cmpl   $0xc,(%rsp)
    3505:	0f 85 f2 fc ff ff    	jne    31fd <main+0xc7d>
    350b:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    3510:	4c 89 fa             	mov    %r15,%rdx
    3513:	bf 01 00 00 00       	mov    $0x1,%edi
    3518:	31 c0                	xor    %eax,%eax
    351a:	48 8d 35 a0 3e 00 00 	lea    0x3ea0(%rip),%rsi        # 73c1 <_IO_stdin_used+0x3c1>
    3521:	4c 89 04 24          	mov    %r8,(%rsp)
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3525:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    352f:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    3534:	e8 17 ef ff ff       	call   2450 <__printf_chk@plt>
    3539:	bf 0a 00 00 00       	mov    $0xa,%edi
    353e:	e8 8d ed ff ff       	call   22d0 <putchar@plt>
    3543:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3548:	bf 01 00 00 00       	mov    $0x1,%edi
    354d:	48 8d 35 44 41 00 00 	lea    0x4144(%rip),%rsi        # 7698 <_IO_stdin_used+0x698>
    3554:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3558:	31 c0                	xor    %eax,%eax
    355a:	e8 f1 ee ff ff       	call   2450 <__printf_chk@plt>
    355f:	4c 8b 0c 24          	mov    (%rsp),%r9
    3563:	bf 01 00 00 00       	mov    $0x1,%edi
    3568:	48 8d 35 51 41 00 00 	lea    0x4151(%rip),%rsi        # 76c0 <_IO_stdin_used+0x6c0>
    356f:	4c 89 c8             	mov    %r9,%rax
    3572:	49 c1 f9 3f          	sar    $0x3f,%r9
    3576:	49 f7 ec             	imul   %r12
    3579:	31 c0                	xor    %eax,%eax
    357b:	48 d1 fa             	sar    %rdx
    357e:	4c 29 ca             	sub    %r9,%rdx
    3581:	e8 ca ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3586:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    358b:	bf 01 00 00 00       	mov    $0x1,%edi
    3590:	48 8d 35 59 41 00 00 	lea    0x4159(%rip),%rsi        # 76f0 <_IO_stdin_used+0x6f0>
    3597:	4c 89 d0             	mov    %r10,%rax
    359a:	49 c1 fa 3f          	sar    $0x3f,%r10
    359e:	49 f7 ec             	imul   %r12
    35a1:	31 c0                	xor    %eax,%eax
    35a3:	48 d1 fa             	sar    %rdx
    35a6:	4c 29 d2             	sub    %r10,%rdx
    35a9:	e8 a2 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    35ae:	4c 89 f8             	mov    %r15,%rax
    35b1:	4c 89 f9             	mov    %r15,%rcx
    35b4:	bf 01 00 00 00       	mov    $0x1,%edi
    35b9:	49 f7 ec             	imul   %r12
    35bc:	48 c1 f9 3f          	sar    $0x3f,%rcx
    35c0:	48 8d 35 59 41 00 00 	lea    0x4159(%rip),%rsi        # 7720 <_IO_stdin_used+0x720>
    35c7:	31 c0                	xor    %eax,%eax
    35c9:	48 d1 fa             	sar    %rdx
    35cc:	48 29 ca             	sub    %rcx,%rdx
    35cf:	e8 7c ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    35d4:	48 89 e8             	mov    %rbp,%rax
    35d7:	48 c1 fd 3f          	sar    $0x3f,%rbp
    35db:	48 8d 35 f3 3d 00 00 	lea    0x3df3(%rip),%rsi        # 73d5 <_IO_stdin_used+0x3d5>
    35e2:	49 f7 ec             	imul   %r12
    35e5:	bf 01 00 00 00       	mov    $0x1,%edi
    35ea:	31 c0                	xor    %eax,%eax
    35ec:	48 d1 fa             	sar    %rdx
    35ef:	48 29 ea             	sub    %rbp,%rdx
    35f2:	e8 59 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    35f7:	48 89 d8             	mov    %rbx,%rax
    35fa:	48 c1 fb 3f          	sar    $0x3f,%rbx
    35fe:	48 8d 35 e1 3d 00 00 	lea    0x3de1(%rip),%rsi        # 73e6 <_IO_stdin_used+0x3e6>
    3605:	49 f7 ec             	imul   %r12
    3608:	bf 01 00 00 00       	mov    $0x1,%edi
    360d:	48 d1 fa             	sar    %rdx
    3610:	48 29 da             	sub    %rbx,%rdx
    3613:	31 c0                	xor    %eax,%eax
    3615:	e8 36 ee ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    361a:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    3622:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    362b:	0f 85 a1 00 00 00    	jne    36d2 <main+0x1152>
    3631:	48 81 c4 a8 00 00 00 	add    $0xa8,%rsp
    3638:	31 c0                	xor    %eax,%eax
    363a:	5b                   	pop    %rbx
    363b:	5d                   	pop    %rbp
    363c:	41 5c                	pop    %r12
    363e:	41 5d                	pop    %r13
    3640:	41 5e                	pop    %r14
    3642:	41 5f                	pop    %r15
    3644:	c3                   	ret
          thread_data[x].tasks[y].run = barriered_work; 
    3645:	48 8d 05 e4 21 00 00 	lea    0x21e4(%rip),%rax        # 5830 <barriered_work>
    364c:	bb 02 00 00 00       	mov    $0x2,%ebx
    3651:	49 89 85 d8 00 00 00 	mov    %rax,0xd8(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3658:	e9 5b f2 ff ff       	jmp    28b8 <main+0x338>
      other = (x + 1) % total_threads;
    365d:	b8 89 88 88 88       	mov    $0x88888889,%eax
    3662:	45 89 f2             	mov    %r14d,%r10d
    3665:	45 89 f5             	mov    %r14d,%r13d
      my_thread_data[0] = &thread_data[x]; 
    3668:	48 8b 3c 24          	mov    (%rsp),%rdi
      other = (x + 1) % total_threads;
    366c:	4c 0f af d0          	imul   %rax,%r10
      thread_data[x].thread_index = 0;
    3670:	41 c7 07 00 00 00 00 	movl   $0x0,(%r15)
    3677:	4c 89 f9             	mov    %r15,%rcx
    367a:	44 89 e2             	mov    %r12d,%edx
      my_thread_data[0] = &thread_data[x]; 
    367d:	4c 89 3f             	mov    %r15,(%rdi)
    3680:	48 8d 35 76 3c 00 00 	lea    0x3c76(%rip),%rsi        # 72fd <_IO_stdin_used+0x2fd>
      other = (x + 1) % total_threads;
    3687:	49 c1 ea 23          	shr    $0x23,%r10
    368b:	44 89 d0             	mov    %r10d,%eax
    368e:	c1 e0 04             	shl    $0x4,%eax
    3691:	44 29 d0             	sub    %r10d,%eax
    3694:	41 29 c5             	sub    %eax,%r13d
      my_thread_data[1] = &thread_data[other]; 
    3697:	49 63 c5             	movslq %r13d,%rax
    369a:	4c 8d 04 80          	lea    (%rax,%rax,4),%r8
    369e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    36a3:	49 c1 e0 06          	shl    $0x6,%r8
    36a7:	49 01 c0             	add    %rax,%r8
    36aa:	31 c0                	xor    %eax,%eax
    36ac:	4c 89 47 08          	mov    %r8,0x8(%rdi)
    36b0:	bf 01 00 00 00       	mov    $0x1,%edi
    36b5:	e8 96 ed ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    36ba:	48 8d 45 18          	lea    0x18(%rbp),%rax
    36be:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    36c3:	48 89 c5             	mov    %rax,%rbp
    36c6:	e9 df f0 ff ff       	jmp    27aa <main+0x22a>
    long v = 0;
    36cb:	31 d2                	xor    %edx,%edx
    36cd:	e9 ab fb ff ff       	jmp    327d <main+0xcfd>
}
    36d2:	e8 59 ec ff ff       	call   2330 <__stack_chk_fail@plt>
    36d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000036e0 <_start>:
    36e0:	f3 0f 1e fa          	endbr64
    36e4:	31 ed                	xor    %ebp,%ebp
    36e6:	49 89 d1             	mov    %rdx,%r9
    36e9:	5e                   	pop    %rsi
    36ea:	48 89 e2             	mov    %rsp,%rdx
    36ed:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    36f1:	50                   	push   %rax
    36f2:	54                   	push   %rsp
    36f3:	45 31 c0             	xor    %r8d,%r8d
    36f6:	31 c9                	xor    %ecx,%ecx
    36f8:	48 8d 3d 81 ee ff ff 	lea    -0x117f(%rip),%rdi        # 2580 <main>
    36ff:	ff 15 d3 68 00 00    	call   *0x68d3(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3705:	f4                   	hlt
    3706:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003710 <deregister_tm_clones>:
    3710:	48 8d 3d 09 69 00 00 	lea    0x6909(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3717:	48 8d 05 02 69 00 00 	lea    0x6902(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    371e:	48 39 f8             	cmp    %rdi,%rax
    3721:	74 15                	je     3738 <deregister_tm_clones+0x28>
    3723:	48 8b 05 b6 68 00 00 	mov    0x68b6(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    372a:	48 85 c0             	test   %rax,%rax
    372d:	74 09                	je     3738 <deregister_tm_clones+0x28>
    372f:	ff e0                	jmp    *%rax
    3731:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3738:	c3                   	ret
    3739:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003740 <register_tm_clones>:
    3740:	48 8d 3d d9 68 00 00 	lea    0x68d9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3747:	48 8d 35 d2 68 00 00 	lea    0x68d2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    374e:	48 29 fe             	sub    %rdi,%rsi
    3751:	48 89 f0             	mov    %rsi,%rax
    3754:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3758:	48 c1 f8 03          	sar    $0x3,%rax
    375c:	48 01 c6             	add    %rax,%rsi
    375f:	48 d1 fe             	sar    %rsi
    3762:	74 14                	je     3778 <register_tm_clones+0x38>
    3764:	48 8b 05 85 68 00 00 	mov    0x6885(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    376b:	48 85 c0             	test   %rax,%rax
    376e:	74 08                	je     3778 <register_tm_clones+0x38>
    3770:	ff e0                	jmp    *%rax
    3772:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3778:	c3                   	ret
    3779:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003780 <__do_global_dtors_aux>:
    3780:	f3 0f 1e fa          	endbr64
    3784:	80 3d 9d 68 00 00 00 	cmpb   $0x0,0x689d(%rip)        # a028 <completed.0>
    378b:	75 2b                	jne    37b8 <__do_global_dtors_aux+0x38>
    378d:	55                   	push   %rbp
    378e:	48 83 3d 62 68 00 00 00 	cmpq   $0x0,0x6862(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3796:	48 89 e5             	mov    %rsp,%rbp
    3799:	74 0c                	je     37a7 <__do_global_dtors_aux+0x27>
    379b:	48 8b 3d 66 68 00 00 	mov    0x6866(%rip),%rdi        # a008 <__dso_handle>
    37a2:	e8 09 eb ff ff       	call   22b0 <__cxa_finalize@plt>
    37a7:	e8 64 ff ff ff       	call   3710 <deregister_tm_clones>
    37ac:	c6 05 75 68 00 00 01 	movb   $0x1,0x6875(%rip)        # a028 <completed.0>
    37b3:	5d                   	pop    %rbp
    37b4:	c3                   	ret
    37b5:	0f 1f 00             	nopl   (%rax)
    37b8:	c3                   	ret
    37b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037c0 <frame_dummy>:
    37c0:	f3 0f 1e fa          	endbr64
    37c4:	e9 77 ff ff ff       	jmp    3740 <register_tm_clones>
    37c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037d0 <do_protected_write>:
int do_protected_write(volatile struct BarrierTask *data) {
    37d0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    37d4:	48 8b 87 e8 00 00 00 	mov    0xe8(%rdi),%rax
  data->v++; // thread local
    37db:	48 8b 97 d0 00 00 00 	mov    0xd0(%rdi),%rdx
  struct ProtectedState *protected = data->thread->protected_state;
    37e2:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
  data->v++; // thread local
    37e9:	48 83 c2 01          	add    $0x1,%rdx
    37ed:	48 89 97 d0 00 00 00 	mov    %rdx,0xd0(%rdi)
  if (protected->balance > 0) {
    37f4:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    37f8:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    37fc:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3803:	48 85 c9             	test   %rcx,%rcx
    3806:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    380d:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3811:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3815:	31 c0                	xor    %eax,%eax
    3817:	c3                   	ret
    3818:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000003820 <barriered_reset>:
int barriered_reset(volatile struct BarrierTask *data) {
    3820:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3824:	8b 97 fc 00 00 00    	mov    0xfc(%rdi),%edx
int barriered_reset(volatile struct BarrierTask *data) {
    382a:	48 89 f8             	mov    %rdi,%rax
    for (int x = 0 ; x < data->task_count ; x++) {
    382d:	85 d2                	test   %edx,%edx
    382f:	0f 8e 93 00 00 00    	jle    38c8 <barriered_reset+0xa8>
    3835:	31 d2                	xor    %edx,%edx
    3837:	31 f6                	xor    %esi,%esi
    3839:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3840:	48 8b b8 e8 00 00 00 	mov    0xe8(%rax),%rdi
    3847:	48 63 88 f0 00 00 00 	movslq 0xf0(%rax),%rcx
    for (int x = 0 ; x < data->task_count ; x++) {
    384e:	83 c6 01             	add    $0x1,%esi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3851:	48 8b 7f 40          	mov    0x40(%rdi),%rdi
    3855:	48 8b 0c cf          	mov    (%rdi,%rcx,8),%rcx
    3859:	48 8b 79 58          	mov    0x58(%rcx),%rdi
    385d:	48 01 d7             	add    %rdx,%rdi
    3860:	8b 8f 80 00 00 00    	mov    0x80(%rdi),%ecx
    3866:	83 c1 01             	add    $0x1,%ecx
    3869:	89 8f 80 00 00 00    	mov    %ecx,0x80(%rdi)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    386f:	48 8b b8 e8 00 00 00 	mov    0xe8(%rax),%rdi
    3876:	48 63 88 f0 00 00 00 	movslq 0xf0(%rax),%rcx
    387d:	48 8b 7f 40          	mov    0x40(%rdi),%rdi
    3881:	48 8b 0c cf          	mov    (%rdi,%rcx,8),%rcx
    3885:	48 8b 79 58          	mov    0x58(%rcx),%rdi
    3889:	48 01 d7             	add    %rdx,%rdi
    388c:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    3892:	83 c1 01             	add    $0x1,%ecx
    3895:	89 8f c0 00 00 00    	mov    %ecx,0xc0(%rdi)
      data->thread->tasks[x].available = 1; 
    389b:	48 8b 88 e8 00 00 00 	mov    0xe8(%rax),%rcx
    38a2:	48 8b 79 58          	mov    0x58(%rcx),%rdi
    38a6:	48 01 d7             	add    %rdx,%rdi
    for (int x = 0 ; x < data->task_count ; x++) {
    38a9:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
      data->thread->tasks[x].available = 1; 
    38b0:	c7 87 f8 00 00 00 01 00 00 00 	movl   $0x1,0xf8(%rdi)
    for (int x = 0 ; x < data->task_count ; x++) {
    38ba:	8b 88 fc 00 00 00    	mov    0xfc(%rax),%ecx
    38c0:	39 f1                	cmp    %esi,%ecx
    38c2:	0f 8f 78 ff ff ff    	jg     3840 <barriered_reset+0x20>
  asm volatile ("sfence" ::: "memory");
    38c8:	0f ae f8             	sfence
}
    38cb:	31 c0                	xor    %eax,%eax
    38cd:	c3                   	ret
    38ce:	66 90                	xchg   %ax,%ax

00000000000038d0 <barriered_thread>:
void* barriered_thread(void *arg) {
    38d0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    38d4:	8b 47 64             	mov    0x64(%rdi),%eax
    38d7:	83 f8 01             	cmp    $0x1,%eax
    38da:	0f 85 d1 02 00 00    	jne    3bb1 <barriered_thread+0x2e1>
void* barriered_thread(void *arg) {
    38e0:	41 56                	push   %r14
    38e2:	41 55                	push   %r13
    38e4:	49 89 fd             	mov    %rdi,%r13
    38e7:	41 54                	push   %r12
    38e9:	45 31 e4             	xor    %r12d,%r12d
    38ec:	55                   	push   %rbp
    38ed:	53                   	push   %rbx
    38ee:	31 db                	xor    %ebx,%ebx
    if (t >= data->task_count) {
    38f0:	41 8b 4d 60          	mov    0x60(%r13),%ecx
    38f4:	39 d9                	cmp    %ebx,%ecx
    38f6:	7f 12                	jg     390a <barriered_thread+0x3a>
      data->cycles++;
    38f8:	49 83 85 18 01 00 00 01 	addq   $0x1,0x118(%r13)
      t = 0;
    3900:	31 db                	xor    %ebx,%ebx
    for (; t < data->task_count; t++) {
    3902:	85 c9                	test   %ecx,%ecx
    3904:	0f 8e 86 01 00 00    	jle    3a90 <barriered_thread+0x1c0>
    390a:	48 63 c3             	movslq %ebx,%rax
    390d:	48 8d 2c 40          	lea    (%rax,%rax,2),%rbp
    3911:	48 c1 e5 07          	shl    $0x7,%rbp
    3915:	eb 1b                	jmp    3932 <barriered_thread+0x62>
    3917:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3920:	83 c3 01             	add    $0x1,%ebx
    3923:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    392a:	39 cb                	cmp    %ecx,%ebx
    392c:	0f 8d 5e 01 00 00    	jge    3a90 <barriered_thread+0x1c0>
      if (data->tasks[t].available == 1) {
    3932:	49 8b 45 58          	mov    0x58(%r13),%rax
    3936:	48 8d 14 28          	lea    (%rax,%rbp,1),%rdx
    393a:	8b b2 f8 00 00 00    	mov    0xf8(%rdx),%esi
    3940:	83 fe 01             	cmp    $0x1,%esi
    3943:	75 db                	jne    3920 <barriered_thread+0x50>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3945:	45 8b 4d 48          	mov    0x48(%r13),%r9d
          previous = t - 1;
    3949:	83 e9 01             	sub    $0x1,%ecx
    394c:	8d 73 ff             	lea    -0x1(%rbx),%esi
    394f:	85 db                	test   %ebx,%ebx
    3951:	0f 4f ce             	cmovg  %esi,%ecx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3954:	45 85 c9             	test   %r9d,%r9d
    3957:	0f 8e 03 02 00 00    	jle    3b60 <barriered_thread+0x290>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    395d:	48 63 c9             	movslq %ecx,%rcx
    3960:	49 8b 45 40          	mov    0x40(%r13),%rax
        int prearrive = 0; 
    3964:	31 f6                	xor    %esi,%esi
        int arrived = 0; 
    3966:	45 31 f6             	xor    %r14d,%r14d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3969:	4c 8d 04 49          	lea    (%rcx,%rcx,2),%r8
    396d:	49 63 c9             	movslq %r9d,%rcx
    3970:	49 c1 e0 07          	shl    $0x7,%r8
    3974:	4c 8d 14 c8          	lea    (%rax,%rcx,8),%r10
    3978:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3980:	48 8b 08             	mov    (%rax),%rcx
    3983:	48 8b 79 58          	mov    0x58(%rcx),%rdi
    3987:	4c 01 c7             	add    %r8,%rdi
    398a:	48 89 f9             	mov    %rdi,%rcx
    398d:	8b bf 80 00 00 00    	mov    0x80(%rdi),%edi
    3993:	44 8b 9a 80 00 00 00 	mov    0x80(%rdx),%r11d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    399a:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
            arrived++;
    39a0:	41 39 fb             	cmp    %edi,%r11d
    39a3:	40 0f 94 c7          	sete   %dil
    39a7:	40 0f b6 ff          	movzbl %dil,%edi
    39ab:	41 01 fe             	add    %edi,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    39ae:	8b ba c0 00 00 00    	mov    0xc0(%rdx),%edi
            prearrive++;
    39b4:	39 cf                	cmp    %ecx,%edi
    39b6:	0f 94 c1             	sete   %cl
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    39b9:	48 83 c0 08          	add    $0x8,%rax
            prearrive++;
    39bd:	0f b6 c9             	movzbl %cl,%ecx
    39c0:	01 ce                	add    %ecx,%esi
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    39c2:	4c 39 d0             	cmp    %r10,%rax
    39c5:	75 b9                	jne    3980 <barriered_thread+0xb0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    39c7:	41 39 f1             	cmp    %esi,%r9d
    39ca:	0f 84 e0 00 00 00    	je     3ab0 <barriered_thread+0x1e0>
    39d0:	85 f6                	test   %esi,%esi
    39d2:	0f 84 d8 00 00 00    	je     3ab0 <barriered_thread+0x1e0>
        if (arrived == 0 || arrived == data->thread_count) {
    39d8:	45 85 f6             	test   %r14d,%r14d
    39db:	74 0a                	je     39e7 <barriered_thread+0x117>
    39dd:	45 39 75 48          	cmp    %r14d,0x48(%r13)
    39e1:	0f 85 a9 00 00 00    	jne    3a90 <barriered_thread+0x1c0>
    39e7:	49 8b 45 58          	mov    0x58(%r13),%rax
          data->tasks[t].prearrive++;
    39eb:	48 01 e8             	add    %rbp,%rax
    39ee:	8b 90 c0 00 00 00    	mov    0xc0(%rax),%edx
    39f4:	83 c2 01             	add    $0x1,%edx
    39f7:	89 90 c0 00 00 00    	mov    %edx,0xc0(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    39fd:	85 db                	test   %ebx,%ebx
    39ff:	75 14                	jne    3a15 <barriered_thread+0x145>
    3a01:	49 8b b5 f0 00 00 00 	mov    0xf0(%r13),%rsi
    3a08:	49 3b b5 f8 00 00 00 	cmp    0xf8(%r13),%rsi
    3a0f:	0f 8c 23 01 00 00    	jl     3b38 <barriered_thread+0x268>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3a15:	49 63 4d 00          	movslq 0x0(%r13),%rcx
    3a19:	49 8b 55 40          	mov    0x40(%r13),%rdx
          data->tasks[t].available = 0;
    3a1d:	c7 80 f8 00 00 00 00 00 00 00 	movl   $0x0,0xf8(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3a27:	48 8b 80 d8 00 00 00 	mov    0xd8(%rax),%rax
    3a2e:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    3a32:	48 8b 7a 58          	mov    0x58(%rdx),%rdi
    3a36:	48 01 ef             	add    %rbp,%rdi
    3a39:	ff d0                	call   *%rax
          data->tasks[t].arrived++;
    3a3b:	49 8b 55 58          	mov    0x58(%r13),%rdx
    3a3f:	48 01 ea             	add    %rbp,%rdx
    3a42:	8b 82 80 00 00 00    	mov    0x80(%rdx),%eax
    3a48:	83 c0 01             	add    $0x1,%eax
    3a4b:	89 82 80 00 00 00    	mov    %eax,0x80(%rdx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3a51:	41 8b 45 60          	mov    0x60(%r13),%eax
          data->iteration_count++;
    3a55:	49 83 85 e8 00 00 00 01 	addq   $0x1,0xe8(%r13)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3a5d:	83 e8 01             	sub    $0x1,%eax
    3a60:	39 d8                	cmp    %ebx,%eax
    3a62:	74 64                	je     3ac8 <barriered_thread+0x1f8>
          asm volatile ("sfence" ::: "memory");
    3a64:	0f ae f8             	sfence
          if (waiting == 0) {
    3a67:	45 85 e4             	test   %r12d,%r12d
    3a6a:	0f 84 90 00 00 00    	je     3b00 <barriered_thread+0x230>
    for (; t < data->task_count; t++) {
    3a70:	41 8b 4d 60          	mov    0x60(%r13),%ecx
    3a74:	83 c3 01             	add    $0x1,%ebx
    3a77:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    3a7e:	39 cb                	cmp    %ecx,%ebx
    3a80:	0f 8c ac fe ff ff    	jl     3932 <barriered_thread+0x62>
    3a86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  while (data->running == 1) {
    3a90:	41 8b 45 64          	mov    0x64(%r13),%eax
    3a94:	83 f8 01             	cmp    $0x1,%eax
    3a97:	0f 84 53 fe ff ff    	je     38f0 <barriered_thread+0x20>
}
    3a9d:	5b                   	pop    %rbx
    3a9e:	31 c0                	xor    %eax,%eax
    3aa0:	5d                   	pop    %rbp
    3aa1:	41 5c                	pop    %r12
    3aa3:	41 5d                	pop    %r13
    3aa5:	41 5e                	pop    %r14
    3aa7:	c3                   	ret
    3aa8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (waiting == 1) {
    3ab0:	41 83 fc 01          	cmp    $0x1,%r12d
    3ab4:	0f 84 b6 00 00 00    	je     3b70 <barriered_thread+0x2a0>
        int arrived = 0; 
    3aba:	45 31 e4             	xor    %r12d,%r12d
    3abd:	e9 16 ff ff ff       	jmp    39d8 <barriered_thread+0x108>
    3ac2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3ac8:	49 8b b5 f0 00 00 00 	mov    0xf0(%r13),%rsi
    3acf:	49 3b b5 f8 00 00 00 	cmp    0xf8(%r13),%rsi
    3ad6:	7d 8c                	jge    3a64 <barriered_thread+0x194>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    3ad8:	48 c1 e6 04          	shl    $0x4,%rsi
    3adc:	bf 04 00 00 00       	mov    $0x4,%edi
    3ae1:	49 03 b5 e0 00 00 00 	add    0xe0(%r13),%rsi
    3ae8:	e8 23 e8 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3aed:	49 83 85 f0 00 00 00 01 	addq   $0x1,0xf0(%r13)
    3af5:	e9 6a ff ff ff       	jmp    3a64 <barriered_thread+0x194>
    3afa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    3b00:	49 8b 85 08 01 00 00 	mov    0x108(%r13),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3b07:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3b0c:	41 bc 01 00 00 00    	mov    $0x1,%r12d
            data->task_snapshot[data->task_timestamp_count].task = t;
    3b12:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3b16:	49 8b 85 00 01 00 00 	mov    0x100(%r13),%rax
    3b1d:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3b21:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3b24:	e8 e7 e7 ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3b29:	41 8b 4d 60          	mov    0x60(%r13),%ecx
    3b2d:	e9 ee fd ff ff       	jmp    3920 <barriered_thread+0x50>
    3b32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3b38:	48 c1 e6 04          	shl    $0x4,%rsi
    3b3c:	bf 04 00 00 00       	mov    $0x4,%edi
    3b41:	49 03 b5 d8 00 00 00 	add    0xd8(%r13),%rsi
    3b48:	e8 c3 e7 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3b4d:	49 8b 45 58          	mov    0x58(%r13),%rax
    3b51:	48 01 e8             	add    %rbp,%rax
    3b54:	e9 bc fe ff ff       	jmp    3a15 <barriered_thread+0x145>
    3b59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          if (waiting == 1) {
    3b60:	41 83 fc 01          	cmp    $0x1,%r12d
    3b64:	0f 85 81 fe ff ff    	jne    39eb <barriered_thread+0x11b>
        int arrived = 0; 
    3b6a:	45 31 f6             	xor    %r14d,%r14d
    3b6d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3b70:	49 8b 85 08 01 00 00 	mov    0x108(%r13),%rax
    3b77:	bf 04 00 00 00       	mov    $0x4,%edi
    3b7c:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3b80:	49 8b 85 00 01 00 00 	mov    0x100(%r13),%rax
    3b87:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3b8c:	e8 7f e7 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3b91:	49 8b 85 08 01 00 00 	mov    0x108(%r13),%rax
    3b98:	48 83 c0 01          	add    $0x1,%rax
    3b9c:	48 99                	cqto
    3b9e:	49 f7 bd 10 01 00 00 	idivq  0x110(%r13)
    3ba5:	49 89 95 08 01 00 00 	mov    %rdx,0x108(%r13)
            waiting = 0; 
    3bac:	e9 09 ff ff ff       	jmp    3aba <barriered_thread+0x1ea>
}
    3bb1:	31 c0                	xor    %eax,%eax
    3bb3:	c3                   	ret
    3bb4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3bbf:	90                   	nop

0000000000003bc0 <external_thread>:
void * external_thread(void *arg) {
    3bc0:	f3 0f 1e fa          	endbr64
    3bc4:	41 55                	push   %r13
    3bc6:	41 54                	push   %r12
    3bc8:	55                   	push   %rbp
    3bc9:	53                   	push   %rbx
    3bca:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    3bce:	66 0f 6f 05 6a 3d 00 00 	movdqa 0x3d6a(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
void * external_thread(void *arg) {
    3bd6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3bdf:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3be4:	31 c0                	xor    %eax,%eax
  struct timespec req = {
    3be6:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    3bea:	8b 47 64             	mov    0x64(%rdi),%eax
    3bed:	83 f8 01             	cmp    $0x1,%eax
    3bf0:	75 64                	jne    3c56 <external_thread+0x96>
    3bf2:	49 89 fd             	mov    %rdi,%r13
    3bf5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3bfa:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    3bfd:	4c 8d 25 00 34 00 00 	lea    0x3400(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    3c04:	0f 1f 40 00          	nopl   0x0(%rax)
    nanosleep(&req , &rem);
    3c08:	48 89 ee             	mov    %rbp,%rsi
    3c0b:	48 89 df             	mov    %rbx,%rdi
    3c0e:	e8 3d e7 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3c13:	49 8b 85 c0 00 00 00 	mov    0xc0(%r13),%rax
    3c1a:	48 63 08             	movslq (%rax),%rcx
    3c1d:	85 c9                	test   %ecx,%ecx
    3c1f:	7e 29                	jle    3c4a <external_thread+0x8a>
    3c21:	48 8b 40 08          	mov    0x8(%rax),%rax
    3c25:	48 c1 e1 04          	shl    $0x4,%rcx
    3c29:	48 01 c1             	add    %rax,%rcx
    3c2c:	0f 1f 40 00          	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    3c30:	8b 50 08             	mov    0x8(%rax),%edx
    3c33:	85 d2                	test   %edx,%edx
    3c35:	75 0a                	jne    3c41 <external_thread+0x81>
        data->buffers->buffer[x].data = "Hello world";
    3c37:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    3c3a:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3c41:	48 83 c0 10          	add    $0x10,%rax
    3c45:	48 39 c1             	cmp    %rax,%rcx
    3c48:	75 e6                	jne    3c30 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    3c4a:	0f ae f0             	mfence
  while (data->running == 1) {
    3c4d:	41 8b 45 64          	mov    0x64(%r13),%eax
    3c51:	83 f8 01             	cmp    $0x1,%eax
    3c54:	74 b2                	je     3c08 <external_thread+0x48>
}
    3c56:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3c5b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3c64:	75 0d                	jne    3c73 <external_thread+0xb3>
    3c66:	48 83 c4 38          	add    $0x38,%rsp
    3c6a:	31 c0                	xor    %eax,%eax
    3c6c:	5b                   	pop    %rbx
    3c6d:	5d                   	pop    %rbp
    3c6e:	41 5c                	pop    %r12
    3c70:	41 5d                	pop    %r13
    3c72:	c3                   	ret
    3c73:	e8 b8 e6 ff ff       	call   2330 <__stack_chk_fail@plt>
    3c78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000003c80 <timer_thread>:
void* timer_thread(void *arg) {
    3c80:	f3 0f 1e fa          	endbr64
    3c84:	41 57                	push   %r15
    3c86:	48 8d 35 83 33 00 00 	lea    0x3383(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3c8d:	49 89 ff             	mov    %rdi,%r15
    3c90:	41 56                	push   %r14
    3c92:	41 55                	push   %r13
    3c94:	41 54                	push   %r12
    3c96:	55                   	push   %rbp
    3c97:	53                   	push   %rbx
    3c98:	48 83 ec 58          	sub    $0x58,%rsp
    3c9c:	8b 17                	mov    (%rdi),%edx
    3c9e:	bf 01 00 00 00       	mov    $0x1,%edi
    3ca3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3cac:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3cb1:	31 c0                	xor    %eax,%eax
    3cb3:	e8 98 e7 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3cb8:	66 0f 6f 05 80 3c 00 00 	movdqa 0x3c80(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3cc0:	ba 88 13 00 00       	mov    $0x1388,%edx
    3cc5:	31 c0                	xor    %eax,%eax
    3cc7:	48 8d 35 54 33 00 00 	lea    0x3354(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3cce:	bf 01 00 00 00       	mov    $0x1,%edi
    3cd3:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3cd8:	e8 73 e7 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3cdd:	4d 63 77 64          	movslq 0x64(%r15),%r14
    3ce1:	45 85 f6             	test   %r14d,%r14d
    3ce4:	0f 84 a2 00 00 00    	je     3d8c <timer_thread+0x10c>
  int n = 0;
    3cea:	45 31 ed             	xor    %r13d,%r13d
  int y = 0;
    3ced:	45 31 f6             	xor    %r14d,%r14d
    3cf0:	49 89 e4             	mov    %rsp,%r12
    if (y >= data->threads[0]->task_count) {
    3cf3:	31 db                	xor    %ebx,%ebx
    3cf5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    3cfa:	48 89 ef             	mov    %rbp,%rdi
    3cfd:	4c 89 e6             	mov    %r12,%rsi
    n++;
    3d00:	41 83 c5 01          	add    $0x1,%r13d
    nanosleep(&preempt , &rem2);
    3d04:	e8 47 e6 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d09:	49 63 47 48          	movslq 0x48(%r15),%rax
    y++;
    3d0d:	41 8d 7e 01          	lea    0x1(%r14),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d11:	85 c0                	test   %eax,%eax
    3d13:	7e 4f                	jle    3d64 <timer_thread+0xe4>
    3d15:	49 8b 77 40          	mov    0x40(%r15),%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    3d19:	4f 8d 04 76          	lea    (%r14,%r14,2),%r8
    3d1d:	49 c1 e0 07          	shl    $0x7,%r8
    3d21:	4c 8d 0c c6          	lea    (%rsi,%rax,8),%r9
    3d25:	0f 1f 00             	nopl   (%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3d28:	4c 8b 16             	mov    (%rsi),%r10
    3d2b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d2d:	48 83 c6 08          	add    $0x8,%rsi
        int next = (y + 1) % data->threads[x]->task_count;
    3d31:	99                   	cltd
    3d32:	41 f7 7a 60          	idivl  0x60(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3d36:	49 8b 4a 58          	mov    0x58(%r10),%rcx
    3d3a:	48 63 d2             	movslq %edx,%rdx
    3d3d:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
    3d41:	48 c1 e0 07          	shl    $0x7,%rax
    3d45:	48 01 c8             	add    %rcx,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3d48:	4c 01 c1             	add    %r8,%rcx
        data->threads[x]->tasks[next].scheduled = 1;
    3d4b:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3d55:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d5f:	4c 39 ce             	cmp    %r9,%rsi
    3d62:	75 c4                	jne    3d28 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    3d64:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3d67:	49 8b 47 40          	mov    0x40(%r15),%rax
    3d6b:	48 8b 00             	mov    (%rax),%rax
    3d6e:	39 78 60             	cmp    %edi,0x60(%rax)
  while (data->running && n < times) {
    3d71:	41 8b 47 64          	mov    0x64(%r15),%eax
    if (y >= data->threads[0]->task_count) {
    3d75:	0f 4e fb             	cmovle %ebx,%edi
    3d78:	4c 63 f7             	movslq %edi,%r14
  while (data->running && n < times) {
    3d7b:	85 c0                	test   %eax,%eax
    3d7d:	74 0d                	je     3d8c <timer_thread+0x10c>
    3d7f:	41 81 fd 88 13 00 00 	cmp    $0x1388,%r13d
    3d86:	0f 85 6e ff ff ff    	jne    3cfa <timer_thread+0x7a>
    3d8c:	48 8d 3d a5 32 00 00 	lea    0x32a5(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3d93:	e8 58 e5 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d98:	49 63 47 4c          	movslq 0x4c(%r15),%rax
    3d9c:	85 c0                	test   %eax,%eax
    3d9e:	7e 4e                	jle    3dee <timer_thread+0x16e>
    for (int y = 0 ; y < data->task_count ; y++) {
    3da0:	41 8b 57 60          	mov    0x60(%r15),%edx
    3da4:	85 d2                	test   %edx,%edx
    3da6:	7e 46                	jle    3dee <timer_thread+0x16e>
    3da8:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    3db0:	48 63 c2             	movslq %edx,%rax
      data->threads[x]->tasks[y].sending = 0;
    3db3:	4d 8b 47 40          	mov    0x40(%r15),%r8
    3db7:	31 f6                	xor    %esi,%esi
    3db9:	48 8d 3c 40          	lea    (%rax,%rax,2),%rdi
    3dbd:	48 c1 e7 07          	shl    $0x7,%rdi
    3dc1:	49 8b 04 30          	mov    (%r8,%rsi,1),%rax
    3dc5:	48 8b 40 58          	mov    0x58(%rax),%rax
    3dc9:	48 8d 14 07          	lea    (%rdi,%rax,1),%rdx
    3dcd:	0f 1f 00             	nopl   (%rax)
    3dd0:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3dda:	48 05 80 01 00 00    	add    $0x180,%rax
    3de0:	48 39 c2             	cmp    %rax,%rdx
    3de3:	75 eb                	jne    3dd0 <timer_thread+0x150>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3de5:	48 83 c6 08          	add    $0x8,%rsi
    3de9:	48 39 f1             	cmp    %rsi,%rcx
    3dec:	75 d3                	jne    3dc1 <timer_thread+0x141>
  asm volatile ("mfence" ::: "memory");
    3dee:	0f ae f0             	mfence
  struct timespec drain = {
    3df1:	66 0f 6f 05 57 3b 00 00 	movdqa 0x3b57(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3df9:	48 8d 2d 5d 32 00 00 	lea    0x325d(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3e00:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3e05:	49 63 47 48          	movslq 0x48(%r15),%rax
    y++;
    3e09:	45 8d 6e 01          	lea    0x1(%r14),%r13d
    for (int x = 0 ; x < data->thread_count ; x++) {
    3e0d:	85 c0                	test   %eax,%eax
    3e0f:	7e 53                	jle    3e64 <timer_thread+0x1e4>
    3e11:	49 8b 77 40          	mov    0x40(%r15),%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    3e15:	4b 8d 3c 76          	lea    (%r14,%r14,2),%rdi
    3e19:	48 c1 e7 07          	shl    $0x7,%rdi
    3e1d:	4c 8d 04 c6          	lea    (%rsi,%rax,8),%r8
    3e21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3e28:	48 8b 1e             	mov    (%rsi),%rbx
    3e2b:	44 89 e8             	mov    %r13d,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3e2e:	48 83 c6 08          	add    $0x8,%rsi
        int next = (y + 1) % data->threads[x]->task_count;
    3e32:	99                   	cltd
    3e33:	f7 7b 60             	idivl  0x60(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3e36:	48 8b 4b 58          	mov    0x58(%rbx),%rcx
    3e3a:	48 63 c2             	movslq %edx,%rax
    3e3d:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    3e41:	48 c1 e0 07          	shl    $0x7,%rax
    3e45:	48 01 c8             	add    %rcx,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3e48:	48 01 f9             	add    %rdi,%rcx
        data->threads[x]->tasks[next].scheduled = 1;
    3e4b:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3e55:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3e5f:	49 39 f0             	cmp    %rsi,%r8
    3e62:	75 c4                	jne    3e28 <timer_thread+0x1a8>
    asm volatile ("mfence" ::: "memory");
    3e64:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3e67:	49 8b 47 40          	mov    0x40(%r15),%rax
    3e6b:	48 8b 00             	mov    (%rax),%rax
    3e6e:	44 39 68 60          	cmp    %r13d,0x60(%rax)
    3e72:	7f 03                	jg     3e77 <timer_thread+0x1f7>
      y = 0;
    3e74:	45 31 ed             	xor    %r13d,%r13d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3e77:	45 8b 47 50          	mov    0x50(%r15),%r8d
    3e7b:	45 85 c0             	test   %r8d,%r8d
    3e7e:	0f 8e e6 00 00 00    	jle    3f6a <timer_thread+0x2ea>
    3e84:	31 db                	xor    %ebx,%ebx
    3e86:	45 31 e4             	xor    %r12d,%r12d
    int all_empty = 1;
    3e89:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3e8f:	90                   	nop
            all_empty = 0;
    3e90:	45 31 f6             	xor    %r14d,%r14d
    3e93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3e98:	45 85 c0             	test   %r8d,%r8d
    3e9b:	0f 8e 8d 00 00 00    	jle    3f2e <timer_thread+0x2ae>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3ea1:	49 8b 47 40          	mov    0x40(%r15),%rax
    3ea5:	4b 8d 0c 76          	lea    (%r14,%r14,2),%rcx
    3ea9:	49 63 f8             	movslq %r8d,%rdi
    3eac:	31 d2                	xor    %edx,%edx
    3eae:	48 c1 e1 07          	shl    $0x7,%rcx
    3eb2:	48 8b 04 18          	mov    (%rax,%rbx,1),%rax
    3eb6:	48 03 48 58          	add    0x58(%rax),%rcx
    3eba:	eb 22                	jmp    3ede <timer_thread+0x25e>
    3ebc:	0f 1f 40 00          	nopl   0x0(%rax)
    3ec0:	48 8b b1 28 01 00 00 	mov    0x128(%rcx),%rsi
    3ec7:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    3ecc:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    3ed0:	48 85 f6             	test   %rsi,%rsi
    3ed3:	7f 24                	jg     3ef9 <timer_thread+0x279>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3ed5:	48 83 c2 01          	add    $0x1,%rdx
    3ed9:	48 39 fa             	cmp    %rdi,%rdx
    3edc:	74 50                	je     3f2e <timer_thread+0x2ae>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3ede:	48 8b b1 28 01 00 00 	mov    0x128(%rcx),%rsi
    3ee5:	48 89 d0             	mov    %rdx,%rax
    3ee8:	48 c1 e0 05          	shl    $0x5,%rax
    3eec:	48 8b 34 06          	mov    (%rsi,%rax,1),%rsi
    3ef0:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    3ef4:	48 85 f6             	test   %rsi,%rsi
    3ef7:	7e c7                	jle    3ec0 <timer_thread+0x240>
            printf("%d %ld %ld left\n", k, ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count, ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count);
    3ef9:	48 8b b1 28 01 00 00 	mov    0x128(%rcx),%rsi
    3f00:	bf 01 00 00 00       	mov    $0x1,%edi
    3f05:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    3f0a:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3f0e:	48 8b 89 28 01 00 00 	mov    0x128(%rcx),%rcx
    3f15:	48 89 ee             	mov    %rbp,%rsi
    3f18:	48 8b 04 01          	mov    (%rcx,%rax,1),%rax
    3f1c:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3f20:	31 c0                	xor    %eax,%eax
    3f22:	e8 29 e5 ff ff       	call   2450 <__printf_chk@plt>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3f27:	45 8b 47 50          	mov    0x50(%r15),%r8d
            all_empty = 0;
    3f2b:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3f2e:	49 83 c6 01          	add    $0x1,%r14
    3f32:	45 39 f0             	cmp    %r14d,%r8d
    3f35:	0f 8f 5d ff ff ff    	jg     3e98 <timer_thread+0x218>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f3b:	41 83 c4 01          	add    $0x1,%r12d
    3f3f:	45 39 c4             	cmp    %r8d,%r12d
    3f42:	7d 09                	jge    3f4d <timer_thread+0x2cd>
    3f44:	48 83 c3 08          	add    $0x8,%rbx
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3f48:	e9 43 ff ff ff       	jmp    3e90 <timer_thread+0x210>
    if (all_empty == 1) {
    3f4d:	41 83 f9 01          	cmp    $0x1,%r9d
    3f51:	74 17                	je     3f6a <timer_thread+0x2ea>
      nanosleep(&drain , &drainrem);
    3f53:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3f58:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3f5d:	4d 63 f5             	movslq %r13d,%r14
    3f60:	e8 eb e3 ff ff       	call   2350 <nanosleep@plt>
    3f65:	e9 9b fe ff ff       	jmp    3e05 <timer_thread+0x185>
    3f6a:	48 8d 3d e3 30 00 00 	lea    0x30e3(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3f71:	4c 8d 25 08 31 00 00 	lea    0x3108(%rip),%r12        # 7080 <_IO_stdin_used+0x80>
    3f78:	e8 73 e3 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3f7d:	41 8b 47 64          	mov    0x64(%r15),%eax
    3f81:	48 8d 2d e6 30 00 00 	lea    0x30e6(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3f88:	85 c0                	test   %eax,%eax
    3f8a:	0f 84 a5 00 00 00    	je     4035 <timer_thread+0x3b5>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3f90:	41 8b 57 4c          	mov    0x4c(%r15),%edx
    3f94:	31 db                	xor    %ebx,%ebx
    3f96:	85 d2                	test   %edx,%edx
    3f98:	7e 21                	jle    3fbb <timer_thread+0x33b>
    3f9a:	49 8b 4f 40          	mov    0x40(%r15),%rcx
      data->threads[x]->running = 0;
    3f9e:	48 8b 04 d9          	mov    (%rcx,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    3fa2:	83 78 08 02          	cmpl   $0x2,0x8(%rax)
      data->threads[x]->running = 0;
    3fa6:	c7 40 64 00 00 00 00 	movl   $0x0,0x64(%rax)
      if (data->threads[x]->type == IO) {
    3fad:	0f 84 af 00 00 00    	je     4062 <timer_thread+0x3e2>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3fb3:	48 83 c3 01          	add    $0x1,%rbx
    3fb7:	39 da                	cmp    %ebx,%edx
    3fb9:	7f e3                	jg     3f9e <timer_thread+0x31e>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3fbb:	49 63 47 48          	movslq 0x48(%r15),%rax
    3fbf:	85 c0                	test   %eax,%eax
    3fc1:	7e 53                	jle    4016 <timer_thread+0x396>
      for (int y = 0 ; y < data->task_count ; y++) {
    3fc3:	41 8b 57 60          	mov    0x60(%r15),%edx
    3fc7:	85 d2                	test   %edx,%edx
    3fc9:	7e 4b                	jle    4016 <timer_thread+0x396>
    3fcb:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
    3fd3:	48 63 c2             	movslq %edx,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3fd6:	4d 8b 47 40          	mov    0x40(%r15),%r8
    3fda:	31 c9                	xor    %ecx,%ecx
    3fdc:	48 8d 3c 40          	lea    (%rax,%rax,2),%rdi
    3fe0:	48 c1 e7 07          	shl    $0x7,%rdi
    3fe4:	0f 1f 40 00          	nopl   0x0(%rax)
    3fe8:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3fec:	48 8b 40 58          	mov    0x58(%rax),%rax
    3ff0:	48 8d 14 38          	lea    (%rax,%rdi,1),%rdx
    3ff4:	0f 1f 40 00          	nopl   0x0(%rax)
    3ff8:	c7 80 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4002:	48 05 80 01 00 00    	add    $0x180,%rax
    4008:	48 39 d0             	cmp    %rdx,%rax
    400b:	75 eb                	jne    3ff8 <timer_thread+0x378>
    for (int x = 0 ; x < data->thread_count ; x++) {
    400d:	48 83 c1 08          	add    $0x8,%rcx
    4011:	48 39 f1             	cmp    %rsi,%rcx
    4014:	75 d2                	jne    3fe8 <timer_thread+0x368>
    asm volatile ("mfence" ::: "memory");
    4016:	0f ae f0             	mfence
    4019:	4c 89 e7             	mov    %r12,%rdi
    401c:	e8 cf e2 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    4021:	41 c7 47 64 00 00 00 00 	movl   $0x0,0x64(%r15)
  while (data->running) {
    4029:	41 8b 47 64          	mov    0x64(%r15),%eax
    402d:	85 c0                	test   %eax,%eax
    402f:	0f 85 5b ff ff ff    	jne    3f90 <timer_thread+0x310>
    4035:	48 8d 3d 4b 30 00 00 	lea    0x304b(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    403c:	e8 af e2 ff ff       	call   22f0 <puts@plt>
}
    4041:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    4046:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    404f:	75 46                	jne    4097 <timer_thread+0x417>
    4051:	48 83 c4 58          	add    $0x58,%rsp
    4055:	31 c0                	xor    %eax,%eax
    4057:	5b                   	pop    %rbx
    4058:	5d                   	pop    %rbp
    4059:	41 5c                	pop    %r12
    405b:	41 5d                	pop    %r13
    405d:	41 5e                	pop    %r14
    405f:	41 5f                	pop    %r15
    4061:	c3                   	ret
    4062:	48 89 ef             	mov    %rbp,%rdi
    4065:	e8 86 e2 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    406a:	49 8b 47 40          	mov    0x40(%r15),%rax
    406e:	be 01 00 00 00       	mov    $0x1,%esi
    4073:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4077:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    407b:	8b b8 d0 00 00 00    	mov    0xd0(%rax),%edi
    4081:	e8 7a e3 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4086:	41 8b 57 4c          	mov    0x4c(%r15),%edx
    408a:	39 da                	cmp    %ebx,%edx
    408c:	0f 8f 08 ff ff ff    	jg     3f9a <timer_thread+0x31a>
    4092:	e9 24 ff ff ff       	jmp    3fbb <timer_thread+0x33b>
}
    4097:	e8 94 e2 ff ff       	call   2330 <__stack_chk_fail@plt>
    409c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000040a0 <fatal_error>:
void fatal_error(const char *syscall) {
    40a0:	f3 0f 1e fa          	endbr64
    40a4:	50                   	push   %rax
    40a5:	58                   	pop    %rax
    40a6:	48 83 ec 08          	sub    $0x8,%rsp
    perror(syscall);
    40aa:	e8 e1 e3 ff ff       	call   2490 <perror@plt>
    exit(1);
    40af:	bf 01 00 00 00       	mov    $0x1,%edi
    40b4:	e8 e7 e3 ff ff       	call   24a0 <exit@plt>
    40b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000040c0 <strtolower>:
void strtolower(char *str) {
    40c0:	f3 0f 1e fa          	endbr64
    40c4:	55                   	push   %rbp
    40c5:	53                   	push   %rbx
    40c6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    40ca:	48 0f be 1f          	movsbq (%rdi),%rbx
    40ce:	84 db                	test   %bl,%bl
    40d0:	74 24                	je     40f6 <strtolower+0x36>
    40d2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    40d5:	e8 36 e4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    40da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    40e0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    40e3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    40e7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    40ea:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    40ed:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    40f2:	84 db                	test   %bl,%bl
    40f4:	75 ea                	jne    40e0 <strtolower+0x20>
}
    40f6:	48 83 c4 08          	add    $0x8,%rsp
    40fa:	5b                   	pop    %rbx
    40fb:	5d                   	pop    %rbp
    40fc:	c3                   	ret
    40fd:	0f 1f 00             	nopl   (%rax)

0000000000004100 <zh_malloc>:
void *zh_malloc(size_t size) {
    4100:	f3 0f 1e fa          	endbr64
    4104:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4108:	e8 03 e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    410d:	48 85 c0             	test   %rax,%rax
    4110:	74 05                	je     4117 <zh_malloc+0x17>
}
    4112:	48 83 c4 08          	add    $0x8,%rsp
    4116:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4117:	48 8b 0d 02 5f 00 00 	mov    0x5f02(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    411e:	ba 28 00 00 00       	mov    $0x28,%edx
    4123:	be 01 00 00 00       	mov    $0x1,%esi
    4128:	48 8d 3d d1 32 00 00 	lea    0x32d1(%rip),%rdi        # 7400 <_IO_stdin_used+0x400>
    412f:	e8 8c e3 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4134:	bf 01 00 00 00       	mov    $0x1,%edi
    4139:	e8 62 e3 ff ff       	call   24a0 <exit@plt>
    413e:	66 90                	xchg   %ax,%ax

0000000000004140 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4140:	f3 0f 1e fa          	endbr64
    4144:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4145:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    414a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    414d:	e8 0e e2 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4152:	48 85 c0             	test   %rax,%rax
    4155:	74 11                	je     4168 <get_filename_ext+0x28>
    4157:	48 39 c3             	cmp    %rax,%rbx
    415a:	74 0c                	je     4168 <get_filename_ext+0x28>
    return dot + 1;
    415c:	48 83 c0 01          	add    $0x1,%rax
}
    4160:	5b                   	pop    %rbx
    4161:	c3                   	ret
    4162:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4168:	48 8d 05 60 2f 00 00 	lea    0x2f60(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    416f:	5b                   	pop    %rbx
    4170:	c3                   	ret
    4171:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    417c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004180 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4180:	f3 0f 1e fa          	endbr64
    4184:	41 55                	push   %r13
    4186:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4189:	48 89 fe             	mov    %rdi,%rsi
    418c:	41 54                	push   %r12
    418e:	55                   	push   %rbp
    418f:	48 89 d5             	mov    %rdx,%rbp
    4192:	ba 00 04 00 00       	mov    $0x400,%edx
    4197:	53                   	push   %rbx
    4198:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    419f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    41a8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    41b0:	31 c0                	xor    %eax,%eax
    41b2:	49 89 e4             	mov    %rsp,%r12
    41b5:	4c 89 e7             	mov    %r12,%rdi
    41b8:	e8 73 e2 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    41bd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    41c2:	84 db                	test   %bl,%bl
    41c4:	74 24                	je     41ea <send_headers+0x6a>
        *str = (char)tolower(*str);
    41c6:	e8 45 e3 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    41cb:	48 8b 08             	mov    (%rax),%rcx
    41ce:	4c 89 e0             	mov    %r12,%rax
    41d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    41d8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    41db:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    41df:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    41e2:	48 0f be 18          	movsbq (%rax),%rbx
    41e6:	84 db                	test   %bl,%bl
    41e8:	75 ee                	jne    41d8 <send_headers+0x58>
    void *buf = malloc(size);
    41ea:	bf 11 00 00 00       	mov    $0x11,%edi
    41ef:	e8 1c e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    41f4:	48 85 c0             	test   %rax,%rax
    41f7:	0f 84 7e 04 00 00    	je     467b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    41fd:	66 0f 6f 05 5b 37 00 00 	movdqa 0x375b(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    4205:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4209:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    420e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4216:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    421a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    421d:	e8 ee e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4222:	48 85 c0             	test   %rax,%rax
    4225:	0f 84 50 04 00 00    	je     467b <send_headers+0x4fb>
    422b:	66 0f 6f 05 3d 37 00 00 	movdqa 0x373d(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    4233:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4237:	4c 89 e7             	mov    %r12,%rdi
    423a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4244:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    424c:	0f 11 00             	movups %xmm0,(%rax)
    424f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4253:	be 2e 00 00 00       	mov    $0x2e,%esi
    4258:	e8 03 e1 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    425d:	48 85 c0             	test   %rax,%rax
    4260:	0f 84 ea 02 00 00    	je     4550 <send_headers+0x3d0>
    4266:	4c 39 e0             	cmp    %r12,%rax
    4269:	0f 84 e1 02 00 00    	je     4550 <send_headers+0x3d0>
    return dot + 1;
    426f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4273:	48 8d 3d 23 2e 00 00 	lea    0x2e23(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    427a:	48 89 de             	mov    %rbx,%rsi
    427d:	e8 2e e1 ff ff       	call   23b0 <strcmp@plt>
    4282:	85 c0                	test   %eax,%eax
    4284:	75 20                	jne    42a6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4286:	66 0f 6f 05 f2 36 00 00 	movdqa 0x36f2(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    428e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4296:	66 0f 6f 05 f2 36 00 00 	movdqa 0x36f2(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    429e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    42a6:	48 89 de             	mov    %rbx,%rsi
    42a9:	48 8d 3d f1 2d 00 00 	lea    0x2df1(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    42b0:	e8 fb e0 ff ff       	call   23b0 <strcmp@plt>
    42b5:	85 c0                	test   %eax,%eax
    42b7:	75 20                	jne    42d9 <send_headers+0x159>
    42b9:	66 0f 6f 05 bf 36 00 00 	movdqa 0x36bf(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    42c1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    42c9:	66 0f 6f 05 bf 36 00 00 	movdqa 0x36bf(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    42d1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    42d9:	48 89 de             	mov    %rbx,%rsi
    42dc:	48 8d 3d c3 2d 00 00 	lea    0x2dc3(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    42e3:	e8 c8 e0 ff ff       	call   23b0 <strcmp@plt>
    42e8:	85 c0                	test   %eax,%eax
    42ea:	0f 84 10 02 00 00    	je     4500 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    42f0:	48 89 de             	mov    %rbx,%rsi
    42f3:	48 8d 3d b0 2d 00 00 	lea    0x2db0(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    42fa:	e8 b1 e0 ff ff       	call   23b0 <strcmp@plt>
    42ff:	85 c0                	test   %eax,%eax
    4301:	0f 84 a9 02 00 00    	je     45b0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4307:	48 89 de             	mov    %rbx,%rsi
    430a:	48 8d 3d 9d 2d 00 00 	lea    0x2d9d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4311:	e8 9a e0 ff ff       	call   23b0 <strcmp@plt>
    4316:	85 c0                	test   %eax,%eax
    4318:	0f 84 6a 02 00 00    	je     4588 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    431e:	48 89 de             	mov    %rbx,%rsi
    4321:	48 8d 3d c9 2d 00 00 	lea    0x2dc9(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4328:	e8 83 e0 ff ff       	call   23b0 <strcmp@plt>
    432d:	85 c0                	test   %eax,%eax
    432f:	0f 84 2b 02 00 00    	je     4560 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4335:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4338:	0f 84 52 01 00 00    	je     4490 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    433e:	48 89 de             	mov    %rbx,%rsi
    4341:	48 8d 3d 6a 2d 00 00 	lea    0x2d6a(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    4348:	e8 63 e0 ff ff       	call   23b0 <strcmp@plt>
    434d:	85 c0                	test   %eax,%eax
    434f:	0f 84 ab 02 00 00    	je     4600 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4355:	48 89 de             	mov    %rbx,%rsi
    4358:	48 8d 3d 57 2d 00 00 	lea    0x2d57(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    435f:	e8 4c e0 ff ff       	call   23b0 <strcmp@plt>
    4364:	85 c0                	test   %eax,%eax
    4366:	0f 84 6c 02 00 00    	je     45d8 <send_headers+0x458>
    slen = strlen(send_buffer);
    436c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4374:	4c 89 e7             	mov    %r12,%rdi
    4377:	e8 a4 df ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    437c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    437f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4382:	e8 89 e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4387:	48 85 c0             	test   %rax,%rax
    438a:	0f 84 eb 02 00 00    	je     467b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4390:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4394:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4398:	83 fb 08             	cmp    $0x8,%ebx
    439b:	0f 83 3f 01 00 00    	jae    44e0 <send_headers+0x360>
    43a1:	f6 c3 04             	test   $0x4,%bl
    43a4:	0f 85 7b 02 00 00    	jne    4625 <send_headers+0x4a5>
    43aa:	85 db                	test   %ebx,%ebx
    43ac:	74 13                	je     43c1 <send_headers+0x241>
    43ae:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    43b6:	88 10                	mov    %dl,(%rax)
    43b8:	f6 c3 02             	test   $0x2,%bl
    43bb:	0f 85 96 02 00 00    	jne    4657 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    43c1:	4d 89 e8             	mov    %r13,%r8
    43c4:	48 8d 0d ef 2c 00 00 	lea    0x2cef(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    43cb:	4c 89 e7             	mov    %r12,%rdi
    43ce:	31 c0                	xor    %eax,%eax
    43d0:	ba 00 04 00 00       	mov    $0x400,%edx
    43d5:	be 01 00 00 00       	mov    $0x1,%esi
    43da:	e8 41 e1 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    43df:	4c 89 e7             	mov    %r12,%rdi
    43e2:	e8 39 df ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    43e7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    43ea:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    43ed:	e8 1e e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    43f2:	48 85 c0             	test   %rax,%rax
    43f5:	0f 84 80 02 00 00    	je     467b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    43fb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    43ff:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4403:	83 fb 08             	cmp    $0x8,%ebx
    4406:	0f 83 1c 01 00 00    	jae    4528 <send_headers+0x3a8>
    440c:	f6 c3 04             	test   $0x4,%bl
    440f:	0f 85 29 02 00 00    	jne    463e <send_headers+0x4be>
    4415:	85 db                	test   %ebx,%ebx
    4417:	74 13                	je     442c <send_headers+0x2ac>
    4419:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4421:	88 10                	mov    %dl,(%rax)
    4423:	f6 c3 02             	test   $0x2,%bl
    4426:	0f 85 3d 02 00 00    	jne    4669 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    442c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4431:	bf 02 00 00 00       	mov    $0x2,%edi
    4436:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    443e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4446:	e8 c5 df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    444b:	48 85 c0             	test   %rax,%rax
    444e:	0f 84 27 02 00 00    	je     467b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4454:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    445c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4460:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4468:	66 89 10             	mov    %dx,(%rax)
}
    446b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4473:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    447c:	0f 85 20 02 00 00    	jne    46a2 <send_headers+0x522>
    4482:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4489:	5b                   	pop    %rbx
    448a:	5d                   	pop    %rbp
    448b:	41 5c                	pop    %r12
    448d:	41 5d                	pop    %r13
    448f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4490:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4494:	0f 85 a4 fe ff ff    	jne    433e <send_headers+0x1be>
    449a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    449e:	0f 85 9a fe ff ff    	jne    433e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    44a4:	66 0f 6f 05 34 35 00 00 	movdqa 0x3534(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    44ac:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    44b6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44be:	66 0f 6f 05 2a 35 00 00 	movdqa 0x352a(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    44c6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    44ce:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    44d6:	e9 63 fe ff ff       	jmp    433e <send_headers+0x1be>
    44db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    44e0:	89 da                	mov    %ebx,%edx
    44e2:	48 89 c7             	mov    %rax,%rdi
    44e5:	4c 89 e6             	mov    %r12,%rsi
    44e8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    44ed:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    44f2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    44f5:	c1 e9 03             	shr    $0x3,%ecx
    44f8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    44fb:	e9 c1 fe ff ff       	jmp    43c1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4500:	66 0f 6f 05 78 34 00 00 	movdqa 0x3478(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4508:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4510:	66 0f 6f 05 88 34 00 00 	movdqa 0x3488(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4518:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4520:	e9 cb fd ff ff       	jmp    42f0 <send_headers+0x170>
    4525:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4528:	89 da                	mov    %ebx,%edx
    452a:	48 89 c7             	mov    %rax,%rdi
    452d:	4c 89 e6             	mov    %r12,%rsi
    4530:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4535:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    453a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    453d:	c1 e9 03             	shr    $0x3,%ecx
    4540:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4543:	e9 e4 fe ff ff       	jmp    442c <send_headers+0x2ac>
    4548:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4550:	48 8d 1d 78 2b 00 00 	lea    0x2b78(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4557:	e9 94 fd ff ff       	jmp    42f0 <send_headers+0x170>
    455c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4560:	66 0f 6f 05 58 34 00 00 	movdqa 0x3458(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4568:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4570:	66 0f 6f 05 58 34 00 00 	movdqa 0x3458(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4578:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4580:	e9 b0 fd ff ff       	jmp    4335 <send_headers+0x1b5>
    4585:	0f 1f 00             	nopl   (%rax)
    4588:	66 0f 6f 05 30 34 00 00 	movdqa 0x3430(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4590:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4598:	66 0f 6f 05 30 34 00 00 	movdqa 0x3430(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    45a0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    45a8:	e9 71 fd ff ff       	jmp    431e <send_headers+0x19e>
    45ad:	0f 1f 00             	nopl   (%rax)
    45b0:	66 0f 6f 05 c8 33 00 00 	movdqa 0x33c8(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    45b8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    45c0:	66 0f 6f 05 e8 33 00 00 	movdqa 0x33e8(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    45c8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    45d0:	e9 32 fd ff ff       	jmp    4307 <send_headers+0x187>
    45d5:	0f 1f 00             	nopl   (%rax)
    45d8:	66 0f 6f 05 e0 33 00 00 	movdqa 0x33e0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    45e0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    45e8:	66 0f 6f 05 20 34 00 00 	movdqa 0x3420(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    45f0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    45f8:	e9 6f fd ff ff       	jmp    436c <send_headers+0x1ec>
    45fd:	0f 1f 00             	nopl   (%rax)
    4600:	66 0f 6f 05 b8 33 00 00 	movdqa 0x33b8(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4608:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4610:	66 0f 6f 05 e8 33 00 00 	movdqa 0x33e8(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4618:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4620:	e9 30 fd ff ff       	jmp    4355 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4625:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    462c:	89 db                	mov    %ebx,%ebx
    462e:	89 10                	mov    %edx,(%rax)
    4630:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4635:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4639:	e9 83 fd ff ff       	jmp    43c1 <send_headers+0x241>
    463e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4645:	89 db                	mov    %ebx,%ebx
    4647:	89 10                	mov    %edx,(%rax)
    4649:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    464e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4652:	e9 d5 fd ff ff       	jmp    442c <send_headers+0x2ac>
    4657:	89 db                	mov    %ebx,%ebx
    4659:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    465f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4664:	e9 58 fd ff ff       	jmp    43c1 <send_headers+0x241>
    4669:	89 db                	mov    %ebx,%ebx
    466b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4671:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4676:	e9 b1 fd ff ff       	jmp    442c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    467b:	48 8b 0d 9e 59 00 00 	mov    0x599e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4682:	ba 28 00 00 00       	mov    $0x28,%edx
    4687:	be 01 00 00 00       	mov    $0x1,%esi
    468c:	48 8d 3d 6d 2d 00 00 	lea    0x2d6d(%rip),%rdi        # 7400 <_IO_stdin_used+0x400>
    4693:	e8 28 de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4698:	bf 01 00 00 00       	mov    $0x1,%edi
    469d:	e8 fe dd ff ff       	call   24a0 <exit@plt>
}
    46a2:	e8 89 dc ff ff       	call   2330 <__stack_chk_fail@plt>
    46a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000046b0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    46b0:	f3 0f 1e fa          	endbr64
    46b4:	41 55                	push   %r13
    46b6:	49 89 d5             	mov    %rdx,%r13
    46b9:	41 54                	push   %r12
    46bb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    46be:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    46c1:	55                   	push   %rbp
    46c2:	53                   	push   %rbx
    46c3:	48 89 f3             	mov    %rsi,%rbx
    46c6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    46ca:	e8 41 dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    46cf:	48 85 c0             	test   %rax,%rax
    46d2:	74 77                	je     474b <copy_file_contents+0x9b>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    46d4:	4c 89 e7             	mov    %r12,%rdi
    46d7:	48 89 c5             	mov    %rax,%rbp
    46da:	31 f6                	xor    %esi,%esi
    46dc:	31 c0                	xor    %eax,%eax
    46de:	e8 9d dd ff ff       	call   2480 <open@plt>
    46e3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    46e6:	85 c0                	test   %eax,%eax
    46e8:	78 55                	js     473f <copy_file_contents+0x8f>
		       "the destination buffer");

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    46ea:	48 89 da             	mov    %rbx,%rdx
    46ed:	48 89 ee             	mov    %rbp,%rsi
    46f0:	89 c7                	mov    %eax,%edi
    46f2:	e8 99 dc ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    46f7:	48 98                	cltq
    46f9:	48 39 d8             	cmp    %rbx,%rax
    46fc:	7c 22                	jl     4720 <copy_file_contents+0x70>
    close(fd);
    46fe:	44 89 e7             	mov    %r12d,%edi
    4701:	e8 6a dc ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    4706:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    470a:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    470e:	48 83 c4 08          	add    $0x8,%rsp
    4712:	5b                   	pop    %rbx
    4713:	5d                   	pop    %rbp
    4714:	41 5c                	pop    %r12
    4716:	41 5d                	pop    %r13
    4718:	c3                   	ret
    4719:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4720:	48 8b 0d f9 58 00 00 	mov    0x58f9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4727:	ba 1a 00 00 00       	mov    $0x1a,%edx
    472c:	be 01 00 00 00       	mov    $0x1,%esi
    4731:	48 8d 3d 98 29 00 00 	lea    0x2998(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    4738:	e8 83 dd ff ff       	call   24c0 <fwrite@plt>
    473d:	eb bf                	jmp    46fe <copy_file_contents+0x4e>
        fatal_error("read");
    473f:	48 8d 3d b9 2a 00 00 	lea    0x2ab9(%rip),%rdi        # 71ff <_IO_stdin_used+0x1ff>
    4746:	e8 55 f9 ff ff       	call   40a0 <fatal_error>
    474b:	48 8b 0d ce 58 00 00 	mov    0x58ce(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4752:	ba 28 00 00 00       	mov    $0x28,%edx
    4757:	be 01 00 00 00       	mov    $0x1,%esi
    475c:	48 8d 3d 9d 2c 00 00 	lea    0x2c9d(%rip),%rdi        # 7400 <_IO_stdin_used+0x400>
    4763:	e8 58 dd ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4768:	bf 01 00 00 00       	mov    $0x1,%edi
    476d:	e8 2e dd ff ff       	call   24a0 <exit@plt>
    4772:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    477d:	0f 1f 00             	nopl   (%rax)

0000000000004780 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4780:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
static inline struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4784:	8b 46 44             	mov    0x44(%rsi),%eax
    4787:	48 89 fa             	mov    %rdi,%rdx
    478a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    478d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4793:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4796:	48 8b 07             	mov    (%rdi),%rax
    4799:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    479c:	f6 c1 02             	test   $0x2,%cl
    479f:	74 00                	je     47a1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    47a1:	89 f0                	mov    %esi,%eax
    47a3:	44 29 c0             	sub    %r8d,%eax
    47a6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    47a9:	0f 82 91 dd ff ff    	jb     2540 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    47af:	c1 e9 0a             	shr    $0xa,%ecx
    47b2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    47b6:	8b 47 44             	mov    0x44(%rdi),%eax
    47b9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    47bc:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    47bf:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    47c2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    47c5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    47c9:	d3 e0                	shl    %cl,%eax
    47cb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    47ce:	48 c1 e0 06          	shl    $0x6,%rax
    47d2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    47d6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    47dc:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    47df:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    47e3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    47e9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    47f1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    47f5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    47f8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    47ff:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4807:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    480b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    480f:	e8 2c db ff ff       	call   2340 <io_uring_submit@plt>
}
    4814:	31 c0                	xor    %eax,%eax
    4816:	48 83 c4 08          	add    $0x8,%rsp
    481a:	c3                   	ret
    481b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004820 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4820:	f3 0f 1e fa          	endbr64
    4824:	41 55                	push   %r13
    4826:	41 89 fd             	mov    %edi,%r13d
    4829:	41 54                	push   %r12
    482b:	55                   	push   %rbp
    482c:	53                   	push   %rbx
    482d:	48 89 f3             	mov    %rsi,%rbx
    4830:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4834:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4837:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    483d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4840:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4843:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4845:	f6 c1 02             	test   $0x2,%cl
    4848:	74 00                	je     484a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    484a:	89 c2                	mov    %eax,%edx
    484c:	29 f2                	sub    %esi,%edx
    484e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4851:	0f 82 f9 dc ff ff    	jb     2550 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4857:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    485a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    485d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4860:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4865:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4868:	23 6b 58             	and    0x58(%rbx),%ebp
    486b:	d3 e5                	shl    %cl,%ebp
    486d:	48 c1 e5 06          	shl    $0x6,%rbp
    4871:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4875:	e8 96 db ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    487a:	be 01 00 00 00       	mov    $0x1,%esi
    487f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4884:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4887:	e8 14 db ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    488c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4891:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4895:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4898:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    489d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    48a2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    48ab:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    48b3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    48b7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    48bb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    48c2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    48ca:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    48ce:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    48d6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    48de:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    48e2:	e8 59 da ff ff       	call   2340 <io_uring_submit@plt>
}
    48e7:	48 83 c4 08          	add    $0x8,%rsp
    48eb:	31 c0                	xor    %eax,%eax
    48ed:	5b                   	pop    %rbx
    48ee:	5d                   	pop    %rbp
    48ef:	41 5c                	pop    %r12
    48f1:	41 5d                	pop    %r13
    48f3:	c3                   	ret
    48f4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    48ff:	90                   	nop

0000000000004900 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4900:	f3 0f 1e fa          	endbr64
    4904:	41 56                	push   %r14
    4906:	41 89 f6             	mov    %esi,%r14d
    4909:	41 55                	push   %r13
    490b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    490e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4913:	41 54                	push   %r12
    4915:	55                   	push   %rbp
    4916:	48 89 d5             	mov    %rdx,%rbp
    4919:	53                   	push   %rbx
    void *buf = malloc(size);
    491a:	e8 f1 da ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    491f:	48 85 c0             	test   %rax,%rax
    4922:	0f 84 dd 00 00 00    	je     4a05 <_send_static_string_content+0x105>
    4928:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    492b:	4c 89 ef             	mov    %r13,%rdi
    492e:	e8 ed d9 ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4933:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    493a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    493e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4941:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4944:	e8 c7 da ff ff       	call   2410 <malloc@plt>
    4949:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    494c:	48 85 c0             	test   %rax,%rax
    494f:	0f 84 b0 00 00 00    	je     4a05 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4955:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4959:	4c 89 e2             	mov    %r12,%rdx
    495c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    495f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4963:	e8 78 da ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4968:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    496b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4971:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4974:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4978:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    497a:	f6 c1 02             	test   $0x2,%cl
    497d:	0f 85 7d 00 00 00    	jne    4a00 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4983:	89 d0                	mov    %edx,%eax
    4985:	29 f0                	sub    %esi,%eax
    4987:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    498a:	0f 82 ca db ff ff    	jb     255a <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4990:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4993:	8b 45 44             	mov    0x44(%rbp),%eax
    4996:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4999:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    499c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    499f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    49a2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    49a8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    49ac:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    49ae:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    49b1:	48 89 ef             	mov    %rbp,%rdi
    49b4:	48 c1 e0 06          	shl    $0x6,%rax
    49b8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    49bc:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    49bf:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    49c3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    49c9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    49d1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    49d5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    49d8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    49df:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    49e7:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    49eb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    49ef:	5b                   	pop    %rbx
    49f0:	5d                   	pop    %rbp
    49f1:	41 5c                	pop    %r12
    49f3:	41 5d                	pop    %r13
    49f5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    49f7:	e9 44 d9 ff ff       	jmp    2340 <io_uring_submit@plt>
    49fc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4a00:	e9 7e ff ff ff       	jmp    4983 <_send_static_string_content+0x83>
    4a05:	48 8b 0d 14 56 00 00 	mov    0x5614(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4a0c:	ba 28 00 00 00       	mov    $0x28,%edx
    4a11:	be 01 00 00 00       	mov    $0x1,%esi
    4a16:	48 8d 3d e3 29 00 00 	lea    0x29e3(%rip),%rdi        # 7400 <_IO_stdin_used+0x400>
    4a1d:	e8 9e da ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4a22:	bf 01 00 00 00       	mov    $0x1,%edi
    4a27:	e8 74 da ff ff       	call   24a0 <exit@plt>
    4a2c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a30 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4a30:	f3 0f 1e fa          	endbr64
    4a34:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4a37:	89 fe                	mov    %edi,%esi
    4a39:	48 8b 3d d8 55 00 00 	mov    0x55d8(%rip),%rdi        # a018 <unimplemented_content>
    4a40:	e9 bb fe ff ff       	jmp    4900 <_send_static_string_content>
    4a45:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004a50 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4a50:	f3 0f 1e fa          	endbr64
    4a54:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4a57:	89 fe                	mov    %edi,%esi
    4a59:	48 8b 3d b0 55 00 00 	mov    0x55b0(%rip),%rdi        # a010 <http_404_content>
    4a60:	e9 9b fe ff ff       	jmp    4900 <_send_static_string_content>
    4a65:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004a70 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4a70:	f3 0f 1e fa          	endbr64
    4a74:	41 56                	push   %r14
    4a76:	41 55                	push   %r13
    4a78:	49 89 d5             	mov    %rdx,%r13
    4a7b:	41 54                	push   %r12
    4a7d:	41 89 f4             	mov    %esi,%r12d
    4a80:	55                   	push   %rbp
    4a81:	48 89 fd             	mov    %rdi,%rbp
    4a84:	53                   	push   %rbx
    4a85:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    4a8c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a95:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    4a9d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    4a9f:	e8 7c d8 ff ff       	call   2320 <strlen@plt>
    4aa4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4aa9:	48 89 c3             	mov    %rax,%rbx
    4aac:	0f 84 b6 00 00 00    	je     4b68 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ab2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4ab7:	48 89 ee             	mov    %rbp,%rsi
    4aba:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4abe:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4ac3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4acb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ad3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4ade:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4ae6:	e8 d5 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4aeb:	48 89 e6             	mov    %rsp,%rsi
    4aee:	4c 89 f7             	mov    %r14,%rdi
    4af1:	e8 da d8 ff ff       	call   23d0 <stat@plt>
    4af6:	83 f8 ff             	cmp    $0xffffffff,%eax
    4af9:	0f 84 d3 00 00 00    	je     4bd2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    4aff:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4b03:	25 00 f0 00 00       	and    $0xf000,%eax
    4b08:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4b0d:	0f 84 f5 00 00 00    	je     4c08 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4b13:	48 8b 3d f6 54 00 00 	mov    0x54f6(%rip),%rdi        # a010 <http_404_content>
    4b1a:	4c 89 ea             	mov    %r13,%rdx
    4b1d:	44 89 e6             	mov    %r12d,%esi
    4b20:	e8 db fd ff ff       	call   4900 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4b25:	4c 89 f2             	mov    %r14,%rdx
    4b28:	bf 01 00 00 00       	mov    $0x1,%edi
    4b2d:	31 c0                	xor    %eax,%eax
    4b2f:	48 8d 35 ea 25 00 00 	lea    0x25ea(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    4b36:	e8 15 d9 ff ff       	call   2450 <__printf_chk@plt>
}
    4b3b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4b43:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b4c:	0f 85 20 01 00 00    	jne    4c72 <handle_get_method+0x202>
    4b52:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4b59:	5b                   	pop    %rbx
    4b5a:	5d                   	pop    %rbp
    4b5b:	41 5c                	pop    %r12
    4b5d:	41 5d                	pop    %r13
    4b5f:	41 5e                	pop    %r14
    4b61:	c3                   	ret
    4b62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4b68:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4b6d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4b75:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4b7a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4b7d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4b85:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4b88:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4b90:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4b9b:	e8 20 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    4ba0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4ba5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4baa:	48 8d 35 3a 25 00 00 	lea    0x253a(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4bb1:	48 29 d9             	sub    %rbx,%rcx
    4bb4:	ba 0b 00 00 00       	mov    $0xb,%edx
    4bb9:	e8 02 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4bbe:	48 89 e6             	mov    %rsp,%rsi
    4bc1:	4c 89 f7             	mov    %r14,%rdi
    4bc4:	e8 07 d8 ff ff       	call   23d0 <stat@plt>
    4bc9:	83 f8 ff             	cmp    $0xffffffff,%eax
    4bcc:	0f 85 2d ff ff ff    	jne    4aff <handle_get_method+0x8f>
    4bd2:	4c 89 f2             	mov    %r14,%rdx
    4bd5:	48 89 e9             	mov    %rbp,%rcx
    4bd8:	48 8d 35 17 25 00 00 	lea    0x2517(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    4bdf:	31 c0                	xor    %eax,%eax
    4be1:	bf 01 00 00 00       	mov    $0x1,%edi
    4be6:	e8 65 d8 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    4beb:	48 8b 3d 1e 54 00 00 	mov    0x541e(%rip),%rdi        # a010 <http_404_content>
    4bf2:	4c 89 ea             	mov    %r13,%rdx
    4bf5:	44 89 e6             	mov    %r12d,%esi
    4bf8:	e8 03 fd ff ff       	call   4900 <_send_static_string_content>
}
    4bfd:	e9 39 ff ff ff       	jmp    4b3b <handle_get_method+0xcb>
    4c02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4c08:	bf 70 00 00 00       	mov    $0x70,%edi
    4c0d:	e8 fe d7 ff ff       	call   2410 <malloc@plt>
    4c12:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4c15:	48 85 c0             	test   %rax,%rax
    4c18:	74 5d                	je     4c77 <handle_get_method+0x207>
            req->client_socket = client_socket;
    4c1a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4c1e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4c23:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4c27:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    4c2a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4c31:	e8 4a f5 ff ff       	call   4180 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4c36:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4c3b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4c3f:	4c 89 f7             	mov    %r14,%rdi
    4c42:	e8 69 fa ff ff       	call   46b0 <copy_file_contents>
    4c47:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4c4c:	4c 89 f2             	mov    %r14,%rdx
    4c4f:	31 c0                	xor    %eax,%eax
    4c51:	48 8d 35 b6 24 00 00 	lea    0x24b6(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4c58:	bf 01 00 00 00       	mov    $0x1,%edi
    4c5d:	e8 ee d7 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    4c62:	4c 89 ee             	mov    %r13,%rsi
    4c65:	48 89 df             	mov    %rbx,%rdi
    4c68:	e8 13 fb ff ff       	call   4780 <add_write_request>
    4c6d:	e9 c9 fe ff ff       	jmp    4b3b <handle_get_method+0xcb>
}
    4c72:	e8 b9 d6 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4c77:	48 8b 0d a2 53 00 00 	mov    0x53a2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c7e:	ba 28 00 00 00       	mov    $0x28,%edx
    4c83:	be 01 00 00 00       	mov    $0x1,%esi
    4c88:	48 8d 3d 71 27 00 00 	lea    0x2771(%rip),%rdi        # 7400 <_IO_stdin_used+0x400>
    4c8f:	e8 2c d8 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4c94:	bf 01 00 00 00       	mov    $0x1,%edi
    4c99:	e8 02 d8 ff ff       	call   24a0 <exit@plt>
    4c9e:	66 90                	xchg   %ax,%ax

0000000000004ca0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4ca0:	f3 0f 1e fa          	endbr64
    4ca4:	41 57                	push   %r15
    4ca6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4ca8:	4c 8d 35 d6 23 00 00 	lea    0x23d6(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4caf:	41 55                	push   %r13
    4cb1:	49 89 d5             	mov    %rdx,%r13
    4cb4:	41 54                	push   %r12
    4cb6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4cb9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4cbc:	55                   	push   %rbp
    4cbd:	53                   	push   %rbx
    4cbe:	48 83 ec 18          	sub    $0x18,%rsp
    4cc2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4ccb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4cd0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4cd2:	49 89 e7             	mov    %rsp,%r15
    4cd5:	4c 89 fa             	mov    %r15,%rdx
    4cd8:	e8 a3 d6 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4cdd:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4ce1:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4ce4:	84 db                	test   %bl,%bl
    4ce6:	74 1d                	je     4d05 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4ce8:	e8 23 d8 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4ced:	48 89 ea             	mov    %rbp,%rdx
    4cf0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4cf3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4cf7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4cfa:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    4cfd:	48 0f be 1a          	movsbq (%rdx),%rbx
    4d01:	84 db                	test   %bl,%bl
    4d03:	75 eb                	jne    4cf0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4d05:	4c 89 fa             	mov    %r15,%rdx
    4d08:	4c 89 f6             	mov    %r14,%rsi
    4d0b:	31 ff                	xor    %edi,%edi
    4d0d:	e8 6e d6 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4d12:	48 8d 35 1a 24 00 00 	lea    0x241a(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4d19:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4d1c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    4d1f:	e8 8c d6 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4d24:	4c 89 ea             	mov    %r13,%rdx
    4d27:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4d2a:	85 c0                	test   %eax,%eax
    4d2c:	75 2a                	jne    4d58 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    4d2e:	48 89 df             	mov    %rbx,%rdi
    4d31:	e8 3a fd ff ff       	call   4a70 <handle_get_method>
}
    4d36:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4d3b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d44:	75 20                	jne    4d66 <handle_http_method+0xc6>
    4d46:	48 83 c4 18          	add    $0x18,%rsp
    4d4a:	5b                   	pop    %rbx
    4d4b:	5d                   	pop    %rbp
    4d4c:	41 5c                	pop    %r12
    4d4e:	41 5d                	pop    %r13
    4d50:	41 5e                	pop    %r14
    4d52:	41 5f                	pop    %r15
    4d54:	c3                   	ret
    4d55:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4d58:	48 8b 3d b9 52 00 00 	mov    0x52b9(%rip),%rdi        # a018 <unimplemented_content>
    4d5f:	e8 9c fb ff ff       	call   4900 <_send_static_string_content>
}
    4d64:	eb d0                	jmp    4d36 <handle_http_method+0x96>
    4d66:	e8 c5 d5 ff ff       	call   2330 <__stack_chk_fail@plt>
    4d6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004d70 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4d70:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4d74:	85 d2                	test   %edx,%edx
    4d76:	7e 38                	jle    4db0 <get_line+0x40>
    4d78:	48 63 d2             	movslq %edx,%rdx
    4d7b:	48 83 c7 01          	add    $0x1,%rdi
    4d7f:	48 01 f2             	add    %rsi,%rdx
    4d82:	eb 11                	jmp    4d95 <get_line+0x25>
    4d84:	0f 1f 40 00          	nopl   0x0(%rax)
    4d88:	48 83 c6 01          	add    $0x1,%rsi
    4d8c:	48 83 c7 01          	add    $0x1,%rdi
    4d90:	48 39 d6             	cmp    %rdx,%rsi
    4d93:	74 1b                	je     4db0 <get_line+0x40>
        dest[i] = src[i];
    4d95:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4d99:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4d9b:	3c 0d                	cmp    $0xd,%al
    4d9d:	75 e9                	jne    4d88 <get_line+0x18>
    4d9f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4da2:	75 e4                	jne    4d88 <get_line+0x18>
            dest[i] = '\0';
    4da4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4da7:	31 c0                	xor    %eax,%eax
    4da9:	c3                   	ret
    4daa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4db0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4db5:	c3                   	ret
    4db6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004dc0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4dc0:	f3 0f 1e fa          	endbr64
    4dc4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4dcb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4dcf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4dd8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4de0:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4de2:	49 89 e2             	mov    %rsp,%r10
    4de5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4ded:	4c 89 d0             	mov    %r10,%rax
    4df0:	eb 13                	jmp    4e05 <handle_client_request+0x45>
    4df2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4df8:	48 83 c0 01          	add    $0x1,%rax
    4dfc:	48 83 c1 01          	add    $0x1,%rcx
    4e00:	4c 39 c8             	cmp    %r9,%rax
    4e03:	74 4b                	je     4e50 <handle_client_request+0x90>
        dest[i] = src[i];
    4e05:	44 0f b6 01          	movzbl (%rcx),%r8d
    4e09:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4e0c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4e10:	75 e6                	jne    4df8 <handle_client_request+0x38>
    4e12:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4e16:	75 e0                	jne    4df8 <handle_client_request+0x38>
            dest[i] = '\0';
    4e18:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4e1b:	8b 47 08             	mov    0x8(%rdi),%eax
    4e1e:	48 89 f2             	mov    %rsi,%rdx
    4e21:	4c 89 d7             	mov    %r10,%rdi
    4e24:	89 c6                	mov    %eax,%esi
    4e26:	e8 75 fe ff ff       	call   4ca0 <handle_http_method>
}
    4e2b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4e33:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4e3c:	75 39                	jne    4e77 <handle_client_request+0xb7>
    4e3e:	31 c0                	xor    %eax,%eax
    4e40:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4e47:	c3                   	ret
    4e48:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4e50:	48 8b 0d c9 51 00 00 	mov    0x51c9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4e57:	ba 12 00 00 00       	mov    $0x12,%edx
    4e5c:	be 01 00 00 00       	mov    $0x1,%esi
    4e61:	48 8d 3d cf 22 00 00 	lea    0x22cf(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4e68:	e8 53 d6 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4e6d:	bf 01 00 00 00       	mov    $0x1,%edi
    4e72:	e8 29 d6 ff ff       	call   24a0 <exit@plt>
}
    4e77:	e8 b4 d4 ff ff       	call   2330 <__stack_chk_fail@plt>
    4e7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004e80 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4e80:	f3 0f 1e fa          	endbr64
    4e84:	55                   	push   %rbp
    4e85:	53                   	push   %rbx
    4e86:	48 89 cb             	mov    %rcx,%rbx
    4e89:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4e8d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4e90:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4e93:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4e99:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4e9c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4e9f:	f6 c1 02             	test   $0x2,%cl
    4ea2:	74 00                	je     4ea4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4ea4:	41 89 c0             	mov    %eax,%r8d
    4ea7:	45 29 c8             	sub    %r9d,%r8d
    4eaa:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4eae:	0f 82 b6 d6 ff ff    	jb     256a <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4eb4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4eb7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4eba:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4ebd:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4ec0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4ec3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ec7:	d3 e5                	shl    %cl,%ebp
    4ec9:	48 c1 e5 06          	shl    $0x6,%rbp
    4ecd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4ed1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4ed4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4ed9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4ee0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4ee4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4ee8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4ef0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4ef8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4efc:	e8 0f d5 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4f01:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4f04:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4f0a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4f0e:	48 83 c4 08          	add    $0x8,%rsp
    4f12:	5b                   	pop    %rbx
    4f13:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4f14:	e9 27 d4 ff ff       	jmp    2340 <io_uring_submit@plt>
    4f19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004f20 <io_thread>:
void* io_thread(void *arg) {
    4f20:	f3 0f 1e fa          	endbr64
    4f24:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4f26:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4f28:	41 56                	push   %r14
    4f2a:	41 55                	push   %r13
    4f2c:	41 54                	push   %r12
    4f2e:	55                   	push   %rbp
    4f2f:	48 89 fd             	mov    %rdi,%rbp
    4f32:	53                   	push   %rbx
    4f33:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4f3a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4f43:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4f4b:	48 8b 87 c8 00 00 00 	mov    0xc8(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4f52:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4f57:	bf 00 01 00 00       	mov    $0x100,%edi
    4f5c:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4f5f:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4f63:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4f68:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4f6d:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4f72:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4f77:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4f7f:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4f84:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4f8c:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4f91:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4f99:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4f9e:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4fa6:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4fab:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4fb3:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4fb8:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4fc0:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4fc8:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4fd0:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4fd8:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4fe0:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4fe8:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4ff0:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4ff8:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5000:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5008:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5010:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5017:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    501f:	e8 cc d3 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5024:	48 8b bd c8 00 00 00 	mov    0xc8(%rbp),%rdi
    502b:	31 f6                	xor    %esi,%esi
    502d:	e8 ae d4 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    5032:	31 d2                	xor    %edx,%edx
    5034:	be 01 00 00 00       	mov    $0x1,%esi
    5039:	bf 02 00 00 00       	mov    $0x2,%edi
    503e:	e8 ed d4 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    5043:	83 f8 ff             	cmp    $0xffffffff,%eax
    5046:	0f 84 02 06 00 00    	je     564e <io_thread+0x72e>
  if (setsockopt(sock,
    504c:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5051:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5057:	89 c7                	mov    %eax,%edi
    5059:	41 89 c4             	mov    %eax,%r12d
    505c:	ba 02 00 00 00       	mov    $0x2,%edx
    5061:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5066:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    506e:	e8 8d d2 ff ff       	call   2300 <setsockopt@plt>
    5073:	85 c0                	test   %eax,%eax
    5075:	0f 88 c7 05 00 00    	js     5642 <io_thread+0x722>
  srv_addr.sin_family = AF_INET;
    507b:	8b 05 af 29 00 00    	mov    0x29af(%rip),%eax        # 7a30 <_IO_stdin_used+0xa30>
  return __builtin___memset_chk (__dest, __ch, __len,
    5081:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    5086:	ba 10 00 00 00       	mov    $0x10,%edx
    508b:	44 89 e7             	mov    %r12d,%edi
    508e:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5097:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    509f:	89 44 24 40          	mov    %eax,0x40(%rsp)
  if (bind(sock,
    50a3:	e8 b8 d3 ff ff       	call   2460 <bind@plt>
    50a8:	85 c0                	test   %eax,%eax
    50aa:	0f 88 86 05 00 00    	js     5636 <io_thread+0x716>
  if (listen(sock, 10) < 0) {
    50b0:	be 0a 00 00 00       	mov    $0xa,%esi
    50b5:	44 89 e7             	mov    %r12d,%edi
    50b8:	e8 63 d3 ff ff       	call   2420 <listen@plt>
    50bd:	85 c0                	test   %eax,%eax
    50bf:	0f 88 65 05 00 00    	js     562a <io_thread+0x70a>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    50c5:	ba db 18 00 00       	mov    $0x18db,%edx
    50ca:	48 8d 35 ab 20 00 00 	lea    0x20ab(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    50d1:	bf 01 00 00 00       	mov    $0x1,%edi
    50d6:	31 c0                	xor    %eax,%eax
    50d8:	e8 73 d3 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    50dd:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    50e2:	48 89 d9             	mov    %rbx,%rcx
    50e5:	44 89 e7             	mov    %r12d,%edi
    50e8:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    50ed:	48 89 c6             	mov    %rax,%rsi
    50f0:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    50f5:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    50fa:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5102:	e8 79 fd ff ff       	call   4e80 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5107:	bf 01 00 00 00       	mov    $0x1,%edi
    510c:	be 10 00 00 00       	mov    $0x10,%esi
    5111:	e8 8a d2 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    5116:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    511b:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    511e:	e8 ed d2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    5123:	48 85 c0             	test   %rax,%rax
    5126:	0f 84 d7 04 00 00    	je     5603 <io_thread+0x6e3>
  iov->iov_base = zh_malloc(10);
    512c:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5130:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5137:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    513e:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5146:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5149:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    514e:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5150:	f6 c1 02             	test   $0x2,%cl
    5153:	0f 85 27 04 00 00    	jne    5580 <io_thread+0x660>
	if (next - head <= sq->ring_entries) {
    5159:	89 d0                	mov    %edx,%eax
    515b:	29 f0                	sub    %esi,%eax
    515d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5164:	0f 82 0a d4 ff ff    	jb     2574 <io_thread.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    516a:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    516d:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	sqe->addr3 = 0;
    5174:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5178:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    517b:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5182:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    5185:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    518c:	48 8d b5 d0 00 00 00 	lea    0xd0(%rbp),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5193:	8b 95 d0 00 00 00    	mov    0xd0(%rbp),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5199:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    519b:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    51a0:	48 c1 e0 06          	shl    $0x6,%rax
    51a4:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    51ac:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    51b2:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    51b5:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    51bd:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    51c1:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    51c9:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    51d1:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    51d5:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    51d9:	e8 62 d1 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    51de:	8b 45 64             	mov    0x64(%rbp),%eax
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    51e1:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    51e6:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    51ee:	83 f8 01             	cmp    $0x1,%eax
    51f1:	0f 85 af 01 00 00    	jne    53a6 <io_thread+0x486>
    51f7:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    51fc:	4d 89 ce             	mov    %r9,%r14
    51ff:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5204:	0f 1f 40 00          	nopl   0x0(%rax)
    5208:	48 8d 3d 83 1f 00 00 	lea    0x1f83(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    520f:	e8 dc d0 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5214:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    521b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5222:	c1 e9 0b             	shr    $0xb,%ecx
    5225:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5228:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5230:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5232:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    523a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    523c:	39 d0                	cmp    %edx,%eax
    523e:	74 36                	je     5276 <io_thread+0x356>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5240:	89 f8                	mov    %edi,%eax
    5242:	21 d0                	and    %edx,%eax
    5244:	d3 e0                	shl    %cl,%eax
    5246:	48 c1 e0 04          	shl    $0x4,%rax
    524a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5252:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    525a:	0f 85 80 01 00 00    	jne    53e0 <io_thread+0x4c0>
    5260:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5264:	0f 85 1e 03 00 00    	jne    5588 <io_thread+0x668>
			if (cqe->res < 0)
    526a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    526d:	83 c2 01             	add    $0x1,%edx
    5270:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5272:	85 c0                	test   %eax,%eax
    5274:	79 b2                	jns    5228 <io_thread+0x308>
	*cqe_ptr = cqe;
    5276:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    527f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5280:	45 31 c0             	xor    %r8d,%r8d
    5283:	31 d2                	xor    %edx,%edx
    5285:	b9 01 00 00 00       	mov    $0x1,%ecx
    528a:	4c 89 f6             	mov    %r14,%rsi
    528d:	48 89 df             	mov    %rbx,%rdi
    5290:	e8 ab d1 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5295:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5298:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    529d:	48 83 38 01          	cmpq   $0x1,(%rax)
    52a1:	0f 84 f1 02 00 00    	je     5598 <io_thread+0x678>
    52a7:	48 8d 3d 0a 1f 00 00 	lea    0x1f0a(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    52ae:	e8 3d d0 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    52b3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    52b8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    52bb:	45 85 ff             	test   %r15d,%r15d
    52be:	0f 88 2e 03 00 00    	js     55f2 <io_thread+0x6d2>
      if (cqe->res < 0) {
    52c4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    52c7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    52cb:	85 c0                	test   %eax,%eax
    52cd:	0f 88 e5 02 00 00    	js     55b8 <io_thread+0x698>
      switch (req->event_type) {
    52d3:	41 83 f8 01          	cmp    $0x1,%r8d
    52d7:	0f 84 3b 01 00 00    	je     5418 <io_thread+0x4f8>
    52dd:	41 83 f8 02          	cmp    $0x2,%r8d
    52e1:	0f 84 b1 01 00 00    	je     5498 <io_thread+0x578>
    52e7:	45 85 c0             	test   %r8d,%r8d
    52ea:	0f 84 70 01 00 00    	je     5460 <io_thread+0x540>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    52f0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    52f8:	8b 02                	mov    (%rdx),%eax
    52fa:	83 c0 01             	add    $0x1,%eax
    52fd:	89 02                	mov    %eax,(%rdx)
	unsigned int head, next = sq->sqe_tail + 1;
    52ff:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5306:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    530d:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5310:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5315:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5317:	f6 c1 02             	test   $0x2,%cl
    531a:	74 00                	je     531c <io_thread+0x3fc>
	if (next - head <= sq->ring_entries) {
    531c:	89 d0                	mov    %edx,%eax
    531e:	29 f0                	sub    %esi,%eax
    5320:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5327:	0f 82 47 d2 ff ff    	jb     2574 <io_thread.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    532d:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    5330:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5335:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5339:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    533c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5343:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5346:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    534d:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5354:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5356:	8b 95 d0 00 00 00    	mov    0xd0(%rbp),%edx
    535c:	48 c1 e0 06          	shl    $0x6,%rax
    5360:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5368:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    536e:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5371:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5379:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    537d:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5385:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    538d:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5391:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5395:	e8 a6 cf ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    539a:	8b 45 64             	mov    0x64(%rbp),%eax
    539d:	83 f8 01             	cmp    $0x1,%eax
    53a0:	0f 84 62 fe ff ff    	je     5208 <io_thread+0x2e8>
    53a6:	48 8d 3d 44 1e 00 00 	lea    0x1e44(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    53ad:	e8 3e cf ff ff       	call   22f0 <puts@plt>
}
    53b2:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    53ba:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    53c3:	0f 85 35 02 00 00    	jne    55fe <io_thread+0x6de>
    53c9:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    53d0:	31 c0                	xor    %eax,%eax
    53d2:	5b                   	pop    %rbx
    53d3:	5d                   	pop    %rbp
    53d4:	41 5c                	pop    %r12
    53d6:	41 5d                	pop    %r13
    53d8:	41 5e                	pop    %r14
    53da:	41 5f                	pop    %r15
    53dc:	c3                   	ret
    53dd:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    53e0:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    53e5:	48 85 c0             	test   %rax,%rax
    53e8:	0f 84 92 fe ff ff    	je     5280 <io_thread+0x360>
      if (cqe->user_data == 1) {
    53ee:	48 83 38 01          	cmpq   $0x1,(%rax)
    53f2:	0f 84 a0 01 00 00    	je     5598 <io_thread+0x678>
    53f8:	48 8d 3d b9 1d 00 00 	lea    0x1db9(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    53ff:	e8 ec ce ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5404:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5409:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    540c:	e9 b3 fe ff ff       	jmp    52c4 <io_thread+0x3a4>
    5411:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
              if (!cqe->res) {
    5418:	85 c0                	test   %eax,%eax
    541a:	0f 85 c0 00 00 00    	jne    54e0 <io_thread+0x5c0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5420:	48 8b 0d f9 4b 00 00 	mov    0x4bf9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5427:	ba 0f 00 00 00       	mov    $0xf,%edx
    542c:	be 01 00 00 00       	mov    $0x1,%esi
    5431:	48 8d 3d a9 1d 00 00 	lea    0x1da9(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    5438:	e8 83 d0 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    543d:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5442:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
	if (cqe)
    5448:	48 85 c0             	test   %rax,%rax
    544b:	0f 84 ae fe ff ff    	je     52ff <io_thread+0x3df>
    5451:	e9 9a fe ff ff       	jmp    52f0 <io_thread+0x3d0>
    5456:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5460:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    5465:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    546a:	48 89 d9             	mov    %rbx,%rcx
    546d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5471:	e8 0a fa ff ff       	call   4e80 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5476:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    547b:	48 89 de             	mov    %rbx,%rsi
    547e:	8b 78 08             	mov    0x8(%rax),%edi
    5481:	e8 9a f3 ff ff       	call   4820 <add_read_request>
              free(req);
    5486:	4c 89 e7             	mov    %r12,%rdi
    5489:	e8 32 ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    548e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5493:	eb b3                	jmp    5448 <io_thread+0x528>
    5495:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    5498:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    549d:	45 31 ff             	xor    %r15d,%r15d
    54a0:	85 c0                	test   %eax,%eax
    54a2:	7e 20                	jle    54c4 <io_thread+0x5a4>
    54a4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    54a8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    54ab:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    54af:	48 c1 e0 04          	shl    $0x4,%rax
    54b3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    54b8:	e8 03 ce ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    54bd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    54c2:	7f e4                	jg     54a8 <io_thread+0x588>
              close(req->client_socket);
    54c4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    54c9:	e8 a2 ce ff ff       	call   2370 <close@plt>
              free(req);
    54ce:	4c 89 e7             	mov    %r12,%rdi
    54d1:	e8 ea cd ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    54d6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    54db:	e9 68 ff ff ff       	jmp    5448 <io_thread+0x528>
    for (int i = 0; i < dest_sz; i++) {
    54e0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    54e5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    54ea:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    54f2:	eb 11                	jmp    5505 <io_thread+0x5e5>
    54f4:	0f 1f 40 00          	nopl   0x0(%rax)
    54f8:	48 83 c0 01          	add    $0x1,%rax
    54fc:	48 83 c2 01          	add    $0x1,%rdx
    5500:	48 39 c6             	cmp    %rax,%rsi
    5503:	74 4b                	je     5550 <io_thread+0x630>
        dest[i] = src[i];
    5505:	0f b6 0a             	movzbl (%rdx),%ecx
    5508:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    550a:	80 f9 0d             	cmp    $0xd,%cl
    550d:	75 e9                	jne    54f8 <io_thread+0x5d8>
    550f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5513:	75 e3                	jne    54f8 <io_thread+0x5d8>
            dest[i] = '\0';
    5515:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5518:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    551d:	48 89 da             	mov    %rbx,%rdx
    5520:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5525:	e8 76 f7 ff ff       	call   4ca0 <handle_http_method>
              free(req->iov[0].iov_base);
    552a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    552f:	e8 8c cd ff ff       	call   22c0 <free@plt>
              free(req);
    5534:	4c 89 e7             	mov    %r12,%rdi
    5537:	e8 84 cd ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    553c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5541:	e9 02 ff ff ff       	jmp    5448 <io_thread+0x528>
    5546:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5550:	48 8b 0d c9 4a 00 00 	mov    0x4ac9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5557:	ba 12 00 00 00       	mov    $0x12,%edx
    555c:	be 01 00 00 00       	mov    $0x1,%esi
    5561:	48 8d 3d cf 1b 00 00 	lea    0x1bcf(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5568:	e8 53 cf ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    556d:	bf 01 00 00 00       	mov    $0x1,%edi
    5572:	e8 29 cf ff ff       	call   24a0 <exit@plt>
    5577:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5580:	e9 d4 fb ff ff       	jmp    5159 <io_thread+0x239>
    5585:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5588:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    558d:	e9 5c fe ff ff       	jmp    53ee <io_thread+0x4ce>
    5592:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5598:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    55a0:	48 8d 3d fd 1b 00 00 	lea    0x1bfd(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    55a7:	8b 02                	mov    (%rdx),%eax
    55a9:	83 c0 01             	add    $0x1,%eax
    55ac:	89 02                	mov    %eax,(%rdx)
    55ae:	e8 3d cd ff ff       	call   22f0 <puts@plt>
    55b3:	e9 ee fd ff ff       	jmp    53a6 <io_thread+0x486>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    55b8:	f7 d8                	neg    %eax
    55ba:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    55bf:	89 c7                	mov    %eax,%edi
    55c1:	e8 3a cf ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    55c6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    55cb:	be 01 00 00 00       	mov    $0x1,%esi
    55d0:	48 8b 3d 49 4a 00 00 	mov    0x4a49(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    55d7:	48 89 c1             	mov    %rax,%rcx
    55da:	48 8d 15 4f 1e 00 00 	lea    0x1e4f(%rip),%rdx        # 7430 <_IO_stdin_used+0x430>
    55e1:	31 c0                	xor    %eax,%eax
    55e3:	e8 e8 ce ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    55e8:	bf 01 00 00 00       	mov    $0x1,%edi
    55ed:	e8 ae ce ff ff       	call   24a0 <exit@plt>
          fatal_error("io_uring_wait_cqe");
    55f2:	48 8d 3d d6 1b 00 00 	lea    0x1bd6(%rip),%rdi        # 71cf <_IO_stdin_used+0x1cf>
    55f9:	e8 a2 ea ff ff       	call   40a0 <fatal_error>
}
    55fe:	e8 2d cd ff ff       	call   2330 <__stack_chk_fail@plt>
    5603:	48 8b 0d 16 4a 00 00 	mov    0x4a16(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    560a:	ba 28 00 00 00       	mov    $0x28,%edx
    560f:	be 01 00 00 00       	mov    $0x1,%esi
    5614:	48 8d 3d e5 1d 00 00 	lea    0x1de5(%rip),%rdi        # 7400 <_IO_stdin_used+0x400>
    561b:	e8 a0 ce ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5620:	bf 01 00 00 00       	mov    $0x1,%edi
    5625:	e8 76 ce ff ff       	call   24a0 <exit@plt>
    fatal_error("listen()");
    562a:	48 8d 3d 42 1b 00 00 	lea    0x1b42(%rip),%rdi        # 7173 <_IO_stdin_used+0x173>
    5631:	e8 6a ea ff ff       	call   40a0 <fatal_error>
      fatal_error("bind()");
    5636:	48 8d 3d 2f 1b 00 00 	lea    0x1b2f(%rip),%rdi        # 716c <_IO_stdin_used+0x16c>
    563d:	e8 5e ea ff ff       	call   40a0 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    5642:	48 8d 3d 0a 1b 00 00 	lea    0x1b0a(%rip),%rdi        # 7153 <_IO_stdin_used+0x153>
    5649:	e8 52 ea ff ff       	call   40a0 <fatal_error>
      fatal_error("socket()");
    564e:	48 8d 3d f5 1a 00 00 	lea    0x1af5(%rip),%rdi        # 714a <_IO_stdin_used+0x14a>
    5655:	e8 46 ea ff ff       	call   40a0 <fatal_error>
    565a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005660 <sendm>:
int sendm(volatile struct BarrierTask *data) {
    5660:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    5664:	8b 97 38 01 00 00    	mov    0x138(%rdi),%edx
int sendm(volatile struct BarrierTask *data) {
    566a:	48 89 f8             	mov    %rdi,%rax
  if (data->sending == 1) {
    566d:	83 fa 01             	cmp    $0x1,%edx
    5670:	74 06                	je     5678 <sendm+0x18>
}
    5672:	31 c0                	xor    %eax,%eax
    5674:	c3                   	ret
    5675:	0f 1f 00             	nopl   (%rax)
      for (int n = 0 ; n < data->thread_count; n++) {
    5678:	8b 97 f4 00 00 00    	mov    0xf4(%rdi),%edx
    567e:	85 d2                	test   %edx,%edx
    5680:	7e f0                	jle    5672 <sendm+0x12>
    5682:	45 31 d2             	xor    %r10d,%r10d
    5685:	0f 1f 00             	nopl   (%rax)
        if (n == data->thread_index) { continue; }
    5688:	8b 90 f0 00 00 00    	mov    0xf0(%rax),%edx
    568e:	44 39 d2             	cmp    %r10d,%edx
    5691:	74 6c                	je     56ff <sendm+0x9f>
        struct Data *them = data->mailboxes[n].higher;
    5693:	48 8b 90 28 01 00 00 	mov    0x128(%rax),%rdx
    569a:	4c 89 d6             	mov    %r10,%rsi
    569d:	48 c1 e6 05          	shl    $0x5,%rsi
    56a1:	48 8b 4c 32 08       	mov    0x8(%rdx,%rsi,1),%rcx
        for (; them->messages_count < min;) {
    56a6:	48 8b 51 08          	mov    0x8(%rcx),%rdx
    56aa:	4c 63 41 10          	movslq 0x10(%rcx),%r8
    56ae:	4c 39 c2             	cmp    %r8,%rdx
    56b1:	7d 4c                	jge    56ff <sendm+0x9f>
          them->messages[them->messages_count++] = data->message; 
    56b3:	4c 8b 09             	mov    (%rcx),%r9
    56b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          data->n++;
    56c0:	48 8b 90 c8 00 00 00 	mov    0xc8(%rax),%rdx
    56c7:	48 83 c2 01          	add    $0x1,%rdx
    56cb:	48 89 90 c8 00 00 00 	mov    %rdx,0xc8(%rax)
          data->mailboxes[n].sent++;
    56d2:	48 8b 90 28 01 00 00 	mov    0x128(%rax),%rdx
    56d9:	48 83 44 32 10 01    	addq   $0x1,0x10(%rdx,%rsi,1)
          them->messages[them->messages_count++] = data->message; 
    56df:	48 8b 51 08          	mov    0x8(%rcx),%rdx
    56e3:	48 8d 7a 01          	lea    0x1(%rdx),%rdi
    56e7:	48 89 79 08          	mov    %rdi,0x8(%rcx)
    56eb:	48 8b b8 40 01 00 00 	mov    0x140(%rax),%rdi
    56f2:	49 89 3c d1          	mov    %rdi,(%r9,%rdx,8)
        for (; them->messages_count < min;) {
    56f6:	48 8b 51 08          	mov    0x8(%rcx),%rdx
    56fa:	49 39 d0             	cmp    %rdx,%r8
    56fd:	7f c1                	jg     56c0 <sendm+0x60>
      for (int n = 0 ; n < data->thread_count; n++) {
    56ff:	8b 90 f4 00 00 00    	mov    0xf4(%rax),%edx
    5705:	49 83 c2 01          	add    $0x1,%r10
    5709:	44 39 d2             	cmp    %r10d,%edx
    570c:	0f 8f 76 ff ff ff    	jg     5688 <sendm+0x28>
}
    5712:	31 c0                	xor    %eax,%eax
    5714:	c3                   	ret
    5715:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005720 <receive>:
int receive(volatile struct BarrierTask *data) {
    5720:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5724:	8b 97 f4 00 00 00    	mov    0xf4(%rdi),%edx
    572a:	85 d2                	test   %edx,%edx
    572c:	0f 8e f9 00 00 00    	jle    582b <receive+0x10b>
    5732:	48 89 f8             	mov    %rdi,%rax
    5735:	45 31 db             	xor    %r11d,%r11d
    5738:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5740:	48 8b 90 28 01 00 00 	mov    0x128(%rax),%rdx
    5747:	4c 89 df             	mov    %r11,%rdi
    574a:	48 c1 e7 05          	shl    $0x5,%rdi
    574e:	4c 8b 0c 3a          	mov    (%rdx,%rdi,1),%r9
    for (int x = 0 ; x < me->messages_count ; x++) {
    5752:	49 8b 51 08          	mov    0x8(%r9),%rdx
    5756:	48 85 d2             	test   %rdx,%rdx
    5759:	0f 8e b1 00 00 00    	jle    5810 <receive+0xf0>
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    575f:	4d 8b 11             	mov    (%r9),%r10
    5762:	31 d2                	xor    %edx,%edx
    5764:	eb 1b                	jmp    5781 <receive+0x61>
    5766:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5770:	49 8b 49 08          	mov    0x8(%r9),%rcx
    5774:	48 83 c2 01          	add    $0x1,%rdx
    5778:	48 39 d1             	cmp    %rdx,%rcx
    577b:	0f 8e 8f 00 00 00    	jle    5810 <receive+0xf0>
      data->sends++;
    5781:	48 8b 88 30 01 00 00 	mov    0x130(%rax),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5788:	49 8b 34 d2          	mov    (%r10,%rdx,8),%rsi
      data->sends++;
    578c:	48 83 c1 01          	add    $0x1,%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5790:	4c 8b 46 10          	mov    0x10(%rsi),%r8
      data->sends++;
    5794:	48 89 88 30 01 00 00 	mov    %rcx,0x130(%rax)
      data->n++;
    579b:	48 8b 88 c8 00 00 00 	mov    0xc8(%rax),%rcx
    57a2:	48 83 c1 01          	add    $0x1,%rcx
    57a6:	48 89 88 c8 00 00 00 	mov    %rcx,0xc8(%rax)
      data->mailboxes[n].received++;
    57ad:	48 8b 88 28 01 00 00 	mov    0x128(%rax),%rcx
    57b4:	48 83 44 39 18 01    	addq   $0x1,0x18(%rcx,%rdi,1)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    57ba:	48 63 08             	movslq (%rax),%rcx
    57bd:	49 39 c8             	cmp    %rcx,%r8
    57c0:	75 ae                	jne    5770 <receive+0x50>
    57c2:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    57c6:	48 63 88 f0 00 00 00 	movslq 0xf0(%rax),%rcx
    57cd:	48 39 ce             	cmp    %rcx,%rsi
    57d0:	75 9e                	jne    5770 <receive+0x50>
int receive(volatile struct BarrierTask *data) {
    57d2:	48 83 ec 08          	sub    $0x8,%rsp
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread_index);
    57d6:	48 63 90 f0 00 00 00 	movslq 0xf0(%rax),%rdx
    57dd:	48 63 00             	movslq (%rax),%rax
    57e0:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    57e2:	bf 01 00 00 00       	mov    $0x1,%edi
    57e7:	48 39 f2             	cmp    %rsi,%rdx
    57ea:	48 8d 35 67 1c 00 00 	lea    0x1c67(%rip),%rsi        # 7458 <_IO_stdin_used+0x458>
    57f1:	0f 94 c1             	sete   %cl
    57f4:	31 d2                	xor    %edx,%edx
    57f6:	4c 39 c0             	cmp    %r8,%rax
    57f9:	0f 94 c2             	sete   %dl
    57fc:	31 c0                	xor    %eax,%eax
    57fe:	e8 4d cc ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5803:	bf 01 00 00 00       	mov    $0x1,%edi
    5808:	e8 93 cc ff ff       	call   24a0 <exit@plt>
    580d:	0f 1f 00             	nopl   (%rax)
    me->messages_count = 0;
    5810:	49 c7 41 08 00 00 00 00 	movq   $0x0,0x8(%r9)
  for (int n = 0 ; n < data->thread_count; n++) {
    5818:	8b 90 f4 00 00 00    	mov    0xf4(%rax),%edx
    581e:	49 83 c3 01          	add    $0x1,%r11
    5822:	44 39 da             	cmp    %r11d,%edx
    5825:	0f 8f 15 ff ff ff    	jg     5740 <receive+0x20>
}
    582b:	c3                   	ret
    582c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005830 <barriered_work>:
int barriered_work(volatile struct BarrierTask *data) {
    5830:	f3 0f 1e fa          	endbr64
    5834:	41 54                	push   %r12
    5836:	55                   	push   %rbp
    5837:	53                   	push   %rbx
  if (data->thread_index == data->task_index) {
    5838:	8b 97 f0 00 00 00    	mov    0xf0(%rdi),%edx
int barriered_work(volatile struct BarrierTask *data) {
    583e:	48 89 fb             	mov    %rdi,%rbx
  if (data->thread_index == data->task_index) {
    5841:	8b 07                	mov    (%rdi),%eax
    5843:	39 c2                	cmp    %eax,%edx
    5845:	0f 84 dd 00 00 00    	je     5928 <barriered_work+0xf8>
    receive(data);
    584b:	e8 d0 fe ff ff       	call   5720 <receive>
    while (data->scheduled == 1) {
    5850:	8b 83 00 01 00 00    	mov    0x100(%rbx),%eax
    5856:	83 f8 01             	cmp    $0x1,%eax
    5859:	75 22                	jne    587d <barriered_work+0x4d>
    585b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->n++;
    5860:	48 8b 83 c8 00 00 00 	mov    0xc8(%rbx),%rax
    5867:	48 83 c0 01          	add    $0x1,%rax
    586b:	48 89 83 c8 00 00 00 	mov    %rax,0xc8(%rbx)
    while (data->scheduled == 1) {
    5872:	8b 83 00 01 00 00    	mov    0x100(%rbx),%eax
    5878:	83 f8 01             	cmp    $0x1,%eax
    587b:	74 e3                	je     5860 <barriered_work+0x30>
  if (data->sending == 1) {
    587d:	8b 83 38 01 00 00    	mov    0x138(%rbx),%eax
    5883:	83 f8 01             	cmp    $0x1,%eax
    5886:	74 0a                	je     5892 <barriered_work+0x62>
  asm volatile ("sfence" ::: "memory");
    5888:	0f ae f8             	sfence
}
    588b:	31 c0                	xor    %eax,%eax
    588d:	5b                   	pop    %rbx
    588e:	5d                   	pop    %rbp
    588f:	41 5c                	pop    %r12
    5891:	c3                   	ret
      for (int n = 0 ; n < data->thread_count; n++) {
    5892:	8b 83 f4 00 00 00    	mov    0xf4(%rbx),%eax
    5898:	85 c0                	test   %eax,%eax
    589a:	7e ec                	jle    5888 <barriered_work+0x58>
    589c:	45 31 c9             	xor    %r9d,%r9d
    589f:	90                   	nop
        if (n == data->thread_index) { continue; }
    58a0:	8b 83 f0 00 00 00    	mov    0xf0(%rbx),%eax
    58a6:	44 39 c8             	cmp    %r9d,%eax
    58a9:	74 64                	je     590f <barriered_work+0xdf>
        struct Data *them = data->mailboxes[n].higher;
    58ab:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    58b2:	4c 89 c9             	mov    %r9,%rcx
    58b5:	48 c1 e1 05          	shl    $0x5,%rcx
    58b9:	48 8b 54 08 08       	mov    0x8(%rax,%rcx,1),%rdx
        for (; them->messages_count < min;) {
    58be:	48 8b 42 08          	mov    0x8(%rdx),%rax
    58c2:	48 63 7a 10          	movslq 0x10(%rdx),%rdi
    58c6:	48 39 f8             	cmp    %rdi,%rax
    58c9:	7d 44                	jge    590f <barriered_work+0xdf>
          them->messages[them->messages_count++] = data->message; 
    58cb:	4c 8b 02             	mov    (%rdx),%r8
    58ce:	66 90                	xchg   %ax,%ax
          data->n++;
    58d0:	48 8b 83 c8 00 00 00 	mov    0xc8(%rbx),%rax
    58d7:	48 83 c0 01          	add    $0x1,%rax
    58db:	48 89 83 c8 00 00 00 	mov    %rax,0xc8(%rbx)
          data->mailboxes[n].sent++;
    58e2:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    58e9:	48 83 44 08 10 01    	addq   $0x1,0x10(%rax,%rcx,1)
          them->messages[them->messages_count++] = data->message; 
    58ef:	48 8b 42 08          	mov    0x8(%rdx),%rax
    58f3:	48 8d 70 01          	lea    0x1(%rax),%rsi
    58f7:	48 89 72 08          	mov    %rsi,0x8(%rdx)
    58fb:	48 8b b3 40 01 00 00 	mov    0x140(%rbx),%rsi
    5902:	49 89 34 c0          	mov    %rsi,(%r8,%rax,8)
        for (; them->messages_count < min;) {
    5906:	48 8b 42 08          	mov    0x8(%rdx),%rax
    590a:	48 39 f8             	cmp    %rdi,%rax
    590d:	7c c1                	jl     58d0 <barriered_work+0xa0>
      for (int n = 0 ; n < data->thread_count; n++) {
    590f:	8b 83 f4 00 00 00    	mov    0xf4(%rbx),%eax
    5915:	49 83 c1 01          	add    $0x1,%r9
    5919:	44 39 c8             	cmp    %r9d,%eax
    591c:	7f 82                	jg     58a0 <barriered_work+0x70>
    591e:	e9 65 ff ff ff       	jmp    5888 <barriered_work+0x58>
    5923:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      receive(data);
    5928:	e8 f3 fd ff ff       	call   5720 <receive>
        int t = data->task_index;
    592d:	8b 33                	mov    (%rbx),%esi
        for (int y = 0; y < data->thread_count ; y++) {
    592f:	8b 83 f4 00 00 00    	mov    0xf4(%rbx),%eax
    5935:	85 c0                	test   %eax,%eax
    5937:	0f 8e ba 00 00 00    	jle    59f7 <barriered_work+0x1c7>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    593d:	48 63 c6             	movslq %esi,%rax
    5940:	45 31 db             	xor    %r11d,%r11d
              int next_task = abs((t + 1) % (data->thread_count));
    5943:	83 c6 01             	add    $0x1,%esi
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5946:	4c 8d 14 40          	lea    (%rax,%rax,2),%r10
    594a:	49 c1 e2 07          	shl    $0x7,%r10
    594e:	66 90                	xchg   %ax,%ax
          for (int b = 0; b < data->thread_count ; b++) {
    5950:	8b 83 f4 00 00 00    	mov    0xf4(%rbx),%eax
    5956:	4d 89 d8             	mov    %r11,%r8
    5959:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
              int next_task = abs((t + 1) % (data->thread_count));
    5961:	31 c9                	xor    %ecx,%ecx
    5963:	49 c1 e0 05          	shl    $0x5,%r8
          for (int b = 0; b < data->thread_count ; b++) {
    5967:	85 c0                	test   %eax,%eax
    5969:	7e 79                	jle    59e4 <barriered_work+0x1b4>
    596b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              int next_task = abs((t + 1) % (data->thread_count));
    5970:	44 8b a3 f4 00 00 00 	mov    0xf4(%rbx),%r12d
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5977:	48 8b 83 e8 00 00 00 	mov    0xe8(%rbx),%rax
    597e:	48 8b 40 40          	mov    0x40(%rax),%rax
    5982:	4a 8b 04 08          	mov    (%rax,%r9,1),%rax
    5986:	48 8b 78 58          	mov    0x58(%rax),%rdi
    598a:	4c 01 d7             	add    %r10,%rdi
    598d:	48 8b bf 28 01 00 00 	mov    0x128(%rdi),%rdi
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5994:	48 8b 83 e8 00 00 00 	mov    0xe8(%rbx),%rax
    599b:	48 8b 40 40          	mov    0x40(%rax),%rax
    599f:	48 8b 2c c8          	mov    (%rax,%rcx,8),%rbp
              int next_task = abs((t + 1) % (data->thread_count));
    59a3:	89 f0                	mov    %esi,%eax
    59a5:	99                   	cltd
    59a6:	41 f7 fc             	idiv   %r12d
    59a9:	89 d0                	mov    %edx,%eax
    59ab:	f7 d8                	neg    %eax
    59ad:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59b0:	48 63 d2             	movslq %edx,%rdx
    59b3:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59b7:	48 89 ca             	mov    %rcx,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    59ba:	48 83 c1 01          	add    $0x1,%rcx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59be:	48 c1 e0 07          	shl    $0x7,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59c2:	48 c1 e2 05          	shl    $0x5,%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59c6:	48 03 45 58          	add    0x58(%rbp),%rax
    59ca:	48 8b 80 28 01 00 00 	mov    0x128(%rax),%rax
    59d1:	48 8b 54 17 08       	mov    0x8(%rdi,%rdx,1),%rdx
    59d6:	4a 89 14 00          	mov    %rdx,(%rax,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    59da:	8b 83 f4 00 00 00    	mov    0xf4(%rbx),%eax
    59e0:	39 c8                	cmp    %ecx,%eax
    59e2:	7f 8c                	jg     5970 <barriered_work+0x140>
        for (int y = 0; y < data->thread_count ; y++) {
    59e4:	8b 83 f4 00 00 00    	mov    0xf4(%rbx),%eax
    59ea:	49 83 c3 01          	add    $0x1,%r11
    59ee:	44 39 d8             	cmp    %r11d,%eax
    59f1:	0f 8f 59 ff ff ff    	jg     5950 <barriered_work+0x120>
      asm volatile ("sfence" ::: "memory");
    59f7:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    59fa:	48 8b b3 08 01 00 00 	mov    0x108(%rbx),%rsi
    5a01:	48 8b 83 18 01 00 00 	mov    0x118(%rbx),%rax
    5a08:	31 ff                	xor    %edi,%edi
    5a0a:	48 c1 e0 05          	shl    $0x5,%rax
    5a0e:	48 01 c6             	add    %rax,%rsi
    5a11:	e8 fa c8 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5a16:	48 8b 83 e8 00 00 00 	mov    0xe8(%rbx),%rax
    5a1d:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    5a24:	8b 70 10             	mov    0x10(%rax),%esi
    5a27:	8d 6e 01             	lea    0x1(%rsi),%ebp
    5a2a:	89 68 10             	mov    %ebp,0x10(%rax)
    while (data->scheduled == 1) {
    5a2d:	8b 83 00 01 00 00    	mov    0x100(%rbx),%eax
    5a33:	83 f8 01             	cmp    $0x1,%eax
    5a36:	75 53                	jne    5a8b <barriered_work+0x25b>
    5a38:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->n++;
    5a40:	48 8b 83 c8 00 00 00 	mov    0xc8(%rbx),%rax
    5a47:	48 83 c0 01          	add    $0x1,%rax
    5a4b:	48 89 83 c8 00 00 00 	mov    %rax,0xc8(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a52:	48 8b 8b e0 00 00 00 	mov    0xe0(%rbx),%rcx
    5a59:	48 8b b3 e8 00 00 00 	mov    0xe8(%rbx),%rsi
    5a60:	48 63 93 f0 00 00 00 	movslq 0xf0(%rbx),%rdx
    5a67:	48 63 03             	movslq (%rbx),%rax
    5a6a:	48 8b 76 40          	mov    0x40(%rsi),%rsi
    5a6e:	48 8d 3c 40          	lea    (%rax,%rax,2),%rdi
    5a72:	48 8b 14 d6          	mov    (%rsi,%rdx,8),%rdx
    5a76:	48 c1 e7 07          	shl    $0x7,%rdi
    5a7a:	48 03 7a 58          	add    0x58(%rdx),%rdi
    5a7e:	ff d1                	call   *%rcx
    while (data->scheduled == 1) {
    5a80:	8b 83 00 01 00 00    	mov    0x100(%rbx),%eax
    5a86:	83 f8 01             	cmp    $0x1,%eax
    5a89:	74 b5                	je     5a40 <barriered_work+0x210>
    if (modcount != data->thread->protected_state->modcount) {
    5a8b:	48 8b 83 e8 00 00 00 	mov    0xe8(%rbx),%rax
    5a92:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    5a99:	3b 68 10             	cmp    0x10(%rax),%ebp
    5a9c:	0f 85 e1 00 00 00    	jne    5b83 <barriered_work+0x353>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5aa2:	48 8b 93 08 01 00 00 	mov    0x108(%rbx),%rdx
    5aa9:	48 8b 83 18 01 00 00 	mov    0x118(%rbx),%rax
    5ab0:	31 ff                	xor    %edi,%edi
    5ab2:	48 c1 e0 05          	shl    $0x5,%rax
    5ab6:	48 8d 74 02 10       	lea    0x10(%rdx,%rax,1),%rsi
    5abb:	e8 50 c8 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5ac0:	48 8b 83 18 01 00 00 	mov    0x118(%rbx),%rax
    5ac7:	48 8b 8b 10 01 00 00 	mov    0x110(%rbx),%rcx
    5ace:	48 83 c0 01          	add    $0x1,%rax
    5ad2:	48 99                	cqto
    5ad4:	48 f7 f9             	idiv   %rcx
    5ad7:	48 89 93 18 01 00 00 	mov    %rdx,0x118(%rbx)
  if (data->sending == 1) {
    5ade:	8b 83 38 01 00 00    	mov    0x138(%rbx),%eax
    5ae4:	83 f8 01             	cmp    $0x1,%eax
    5ae7:	0f 85 9b fd ff ff    	jne    5888 <barriered_work+0x58>
      for (int n = 0 ; n < data->thread_count; n++) {
    5aed:	8b 83 f4 00 00 00    	mov    0xf4(%rbx),%eax
    5af3:	85 c0                	test   %eax,%eax
    5af5:	0f 8e 8d fd ff ff    	jle    5888 <barriered_work+0x58>
    5afb:	45 31 c9             	xor    %r9d,%r9d
    5afe:	66 90                	xchg   %ax,%ax
        if (n == data->thread_index) { continue; }
    5b00:	8b 83 f0 00 00 00    	mov    0xf0(%rbx),%eax
    5b06:	44 39 c8             	cmp    %r9d,%eax
    5b09:	74 64                	je     5b6f <barriered_work+0x33f>
        struct Data *them = data->mailboxes[n].higher;
    5b0b:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    5b12:	4c 89 c9             	mov    %r9,%rcx
    5b15:	48 c1 e1 05          	shl    $0x5,%rcx
    5b19:	48 8b 54 08 08       	mov    0x8(%rax,%rcx,1),%rdx
        for (; them->messages_count < min;) {
    5b1e:	48 8b 42 08          	mov    0x8(%rdx),%rax
    5b22:	48 63 7a 10          	movslq 0x10(%rdx),%rdi
    5b26:	48 39 c7             	cmp    %rax,%rdi
    5b29:	7e 44                	jle    5b6f <barriered_work+0x33f>
          them->messages[them->messages_count++] = data->message; 
    5b2b:	4c 8b 02             	mov    (%rdx),%r8
    5b2e:	66 90                	xchg   %ax,%ax
          data->n++;
    5b30:	48 8b 83 c8 00 00 00 	mov    0xc8(%rbx),%rax
    5b37:	48 83 c0 01          	add    $0x1,%rax
    5b3b:	48 89 83 c8 00 00 00 	mov    %rax,0xc8(%rbx)
          data->mailboxes[n].sent++;
    5b42:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    5b49:	48 83 44 08 10 01    	addq   $0x1,0x10(%rax,%rcx,1)
          them->messages[them->messages_count++] = data->message; 
    5b4f:	48 8b 42 08          	mov    0x8(%rdx),%rax
    5b53:	48 8d 70 01          	lea    0x1(%rax),%rsi
    5b57:	48 89 72 08          	mov    %rsi,0x8(%rdx)
    5b5b:	48 8b b3 40 01 00 00 	mov    0x140(%rbx),%rsi
    5b62:	49 89 34 c0          	mov    %rsi,(%r8,%rax,8)
        for (; them->messages_count < min;) {
    5b66:	48 8b 42 08          	mov    0x8(%rdx),%rax
    5b6a:	48 39 f8             	cmp    %rdi,%rax
    5b6d:	7c c1                	jl     5b30 <barriered_work+0x300>
      for (int n = 0 ; n < data->thread_count; n++) {
    5b6f:	8b 83 f4 00 00 00    	mov    0xf4(%rbx),%eax
    5b75:	49 83 c1 01          	add    $0x1,%r9
    5b79:	44 39 c8             	cmp    %r9d,%eax
    5b7c:	7f 82                	jg     5b00 <barriered_work+0x2d0>
    5b7e:	e9 05 fd ff ff       	jmp    5888 <barriered_work+0x58>
    5b83:	48 8d 3d 7a 16 00 00 	lea    0x167a(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5b8a:	e8 61 c7 ff ff       	call   22f0 <puts@plt>
    5b8f:	e9 0e ff ff ff       	jmp    5aa2 <barriered_work+0x272>
    5b94:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5b9f:	90                   	nop

0000000000005ba0 <barriered_work_ingest>:
int barriered_work_ingest(volatile struct BarrierTask *data) {
    5ba0:	f3 0f 1e fa          	endbr64
    5ba4:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5ba8:	48 8b 87 e8 00 00 00 	mov    0xe8(%rdi),%rax
    5baf:	48 8b 80 c0 00 00 00 	mov    0xc0(%rax),%rax
    5bb6:	8b 00                	mov    (%rax),%eax
    5bb8:	85 c0                	test   %eax,%eax
    5bba:	7e 69                	jle    5c25 <barriered_work_ingest+0x85>
    5bbc:	31 c0                	xor    %eax,%eax
    5bbe:	66 90                	xchg   %ax,%ax
    if (data->thread->buffers->buffer[x].available == 1) {
    5bc0:	48 8b 8f e8 00 00 00 	mov    0xe8(%rdi),%rcx
    5bc7:	48 89 c2             	mov    %rax,%rdx
    5bca:	48 c1 e2 04          	shl    $0x4,%rdx
    5bce:	48 8b 89 c0 00 00 00 	mov    0xc0(%rcx),%rcx
    5bd5:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    5bd9:	48 01 d6             	add    %rdx,%rsi
    5bdc:	8b 4e 08             	mov    0x8(%rsi),%ecx
    5bdf:	83 f9 01             	cmp    $0x1,%ecx
    5be2:	75 2b                	jne    5c0f <barriered_work_ingest+0x6f>
      data->ingest_count++;
    5be4:	48 8b 8f 20 01 00 00 	mov    0x120(%rdi),%rcx
    5beb:	48 83 c1 01          	add    $0x1,%rcx
    5bef:	48 89 8f 20 01 00 00 	mov    %rcx,0x120(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5bf6:	48 8b 8f e8 00 00 00 	mov    0xe8(%rdi),%rcx
    5bfd:	48 8b 89 c0 00 00 00 	mov    0xc0(%rcx),%rcx
    5c04:	48 03 51 08          	add    0x8(%rcx),%rdx
    5c08:	c7 42 08 00 00 00 00 	movl   $0x0,0x8(%rdx)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5c0f:	48 8b 97 e8 00 00 00 	mov    0xe8(%rdi),%rdx
    5c16:	48 83 c0 01          	add    $0x1,%rax
    5c1a:	48 8b 92 c0 00 00 00 	mov    0xc0(%rdx),%rdx
    5c21:	39 02                	cmp    %eax,(%rdx)
    5c23:	7f 9b                	jg     5bc0 <barriered_work_ingest+0x20>
  asm volatile ("sfence" ::: "memory");
    5c25:	0f ae f8             	sfence
  barriered_work(data);
    5c28:	e8 03 fc ff ff       	call   5830 <barriered_work>
}
    5c2d:	31 c0                	xor    %eax,%eax
    5c2f:	48 83 c4 08          	add    $0x8,%rsp
    5c33:	c3                   	ret
    5c34:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5c3f:	90                   	nop

0000000000005c40 <barriered_nulltask>:
int barriered_nulltask(volatile struct BarrierTask *data) {
    5c40:	f3 0f 1e fa          	endbr64
}
    5c44:	31 c0                	xor    %eax,%eax
    5c46:	c3                   	ret
    5c47:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005c50 <barriered_steal>:
int barriered_steal(volatile struct BarrierTask *data) {
    5c50:	f3 0f 1e fa          	endbr64
    5c54:	31 c0                	xor    %eax,%eax
    5c56:	c3                   	ret
    5c57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005c60 <after>:
int after(struct timespec left, struct timespec right) {
    5c60:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5c64:	31 c0                	xor    %eax,%eax
    5c66:	48 39 d7             	cmp    %rdx,%rdi
    5c69:	7e 08                	jle    5c73 <after+0x13>
    5c6b:	31 c0                	xor    %eax,%eax
    5c6d:	48 39 ce             	cmp    %rcx,%rsi
    5c70:	0f 9f c0             	setg   %al
}
    5c73:	c3                   	ret
    5c74:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5c7f:	90                   	nop

0000000000005c80 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5c80:	f3 0f 1e fa          	endbr64
    5c84:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5c89:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5c8e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5c90:	48 39 d7             	cmp    %rdx,%rdi
    5c93:	7f 18                	jg     5cad <within+0x2d>
    5c95:	4d 39 d8             	cmp    %r11,%r8
    5c98:	0f 9e c2             	setle  %dl
    5c9b:	48 39 ce             	cmp    %rcx,%rsi
    5c9e:	0f 9e c0             	setle  %al
    5ca1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5ca3:	31 c0                	xor    %eax,%eax
    5ca5:	4d 39 d1             	cmp    %r10,%r9
    5ca8:	0f 9e c0             	setle  %al
    5cab:	21 d0                	and    %edx,%eax
}
    5cad:	c3                   	ret
    5cae:	66 90                	xchg   %ax,%ax

0000000000005cb0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5cb0:	f3 0f 1e fa          	endbr64
    5cb4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5cb9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5cbe:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    5cc3:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    5cc8:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
    5ccd:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5cd2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5cd7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5cdc:	48 39 fe             	cmp    %rdi,%rsi
    5cdf:	7d 2f                	jge    5d10 <overlap+0x60>
    5ce1:	48 39 ca             	cmp    %rcx,%rdx
    5ce4:	7d 62                	jge    5d48 <overlap+0x98>
    5ce6:	4d 39 da             	cmp    %r11,%r10
    5ce9:	7e 0e                	jle    5cf9 <overlap+0x49>
    return 1;
    5ceb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5cf0:	4d 39 c1             	cmp    %r8,%r9
    5cf3:	0f 8f 7f 00 00 00    	jg     5d78 <overlap+0xc8>
  return 0;
    5cf9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5cfb:	4d 39 c1             	cmp    %r8,%r9
    5cfe:	7c 4c                	jl     5d4c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5d00:	31 c0                	xor    %eax,%eax
    5d02:	4d 39 da             	cmp    %r11,%r10
    5d05:	0f 9d c0             	setge  %al
    5d08:	c3                   	ret
    5d09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5d10:	7e 4e                	jle    5d60 <overlap+0xb0>
    5d12:	48 39 ca             	cmp    %rcx,%rdx
    5d15:	7f 39                	jg     5d50 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5d17:	75 31                	jne    5d4a <overlap+0x9a>
    5d19:	4d 39 c1             	cmp    %r8,%r9
    5d1c:	7f 2c                	jg     5d4a <overlap+0x9a>
    return 1;
    5d1e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5d23:	4d 39 da             	cmp    %r11,%r10
    5d26:	7e 24                	jle    5d4c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5d28:	48 39 ca             	cmp    %rcx,%rdx
    5d2b:	0f 94 c2             	sete   %dl
    5d2e:	48 39 fe             	cmp    %rdi,%rsi
    5d31:	0f 94 c0             	sete   %al
    5d34:	21 c2                	and    %eax,%edx
    5d36:	31 c0                	xor    %eax,%eax
    5d38:	4d 39 c1             	cmp    %r8,%r9
    5d3b:	0f 94 c0             	sete   %al
    5d3e:	21 d0                	and    %edx,%eax
    5d40:	c3                   	ret
    5d41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5d48:	74 af                	je     5cf9 <overlap+0x49>
  return 0;
    5d4a:	31 c0                	xor    %eax,%eax
}
    5d4c:	c3                   	ret
    5d4d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5d50:	4d 39 c1             	cmp    %r8,%r9
    5d53:	7d c4                	jge    5d19 <overlap+0x69>
    return 1;
    5d55:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5d5a:	4d 39 da             	cmp    %r11,%r10
    5d5d:	7d ba                	jge    5d19 <overlap+0x69>
    5d5f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5d60:	48 39 ca             	cmp    %rcx,%rdx
    5d63:	7c 94                	jl     5cf9 <overlap+0x49>
    5d65:	4d 39 c1             	cmp    %r8,%r9
    5d68:	7e b4                	jle    5d1e <overlap+0x6e>
    5d6a:	48 39 ca             	cmp    %rcx,%rdx
    5d6d:	74 91                	je     5d00 <overlap+0x50>
    5d6f:	eb d9                	jmp    5d4a <overlap+0x9a>
    5d71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5d78:	c3                   	ret
    5d79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005d80 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5d80:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5d84:	85 f6                	test   %esi,%esi
    5d86:	0f 8e 2d 03 00 00    	jle    60b9 <verify+0x339>
int verify(struct KernelThread *thread_data, int thread_count) {
    5d8c:	41 57                	push   %r15
  for (int x = 0 ; x < thread_count; x++) {
    5d8e:	45 31 ff             	xor    %r15d,%r15d
int verify(struct KernelThread *thread_data, int thread_count) {
    5d91:	41 56                	push   %r14
    5d93:	41 89 f6             	mov    %esi,%r14d
    5d96:	41 55                	push   %r13
    5d98:	4c 8d 6f 58          	lea    0x58(%rdi),%r13
    5d9c:	41 54                	push   %r12
    5d9e:	55                   	push   %rbp
    5d9f:	53                   	push   %rbx
    5da0:	48 83 ec 48          	sub    $0x48,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5da4:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5da9:	4c 89 6c 24 08       	mov    %r13,0x8(%rsp)
    5dae:	45 31 e4             	xor    %r12d,%r12d
    5db1:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
      if (z != x)  {
    5db6:	45 39 e7             	cmp    %r12d,%r15d
    5db9:	0f 84 5a 02 00 00    	je     6019 <verify+0x299>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5dbf:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5dc4:	8b 50 08             	mov    0x8(%rax),%edx
    5dc7:	85 d2                	test   %edx,%edx
    5dc9:	0f 8e 4a 02 00 00    	jle    6019 <verify+0x299>
    5dcf:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    5dd8:	31 db                	xor    %ebx,%ebx
    5dda:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    5ddf:	44 89 fa             	mov    %r15d,%edx
    5de2:	48 8d 35 2b 14 00 00 	lea    0x142b(%rip),%rsi        # 7214 <_IO_stdin_used+0x214>
    5de9:	bf 01 00 00 00       	mov    $0x1,%edi
    5dee:	31 c0                	xor    %eax,%eax
    5df0:	e8 5b c6 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5df5:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5dfa:	8b 40 08             	mov    0x8(%rax),%eax
    5dfd:	85 c0                	test   %eax,%eax
    5dff:	0f 8e f5 01 00 00    	jle    5ffa <verify+0x27a>
    5e05:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5e0a:	89 5c 24 34          	mov    %ebx,0x34(%rsp)
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5e0e:	45 31 e4             	xor    %r12d,%r12d
    5e11:	44 89 7c 24 38       	mov    %r15d,0x38(%rsp)
    5e16:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    5e1b:	44 89 74 24 3c       	mov    %r14d,0x3c(%rsp)
    5e20:	4c 03 28             	add    (%rax),%r13
    5e23:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5e28:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    5e2d:	4b 8d 2c 64          	lea    (%r12,%r12,2),%rbp
    5e31:	49 8b 8d 18 01 00 00 	mov    0x118(%r13),%rcx
    5e38:	48 8d 35 ea 13 00 00 	lea    0x13ea(%rip),%rsi        # 7229 <_IO_stdin_used+0x229>
    5e3f:	48 c1 e5 07          	shl    $0x7,%rbp
    5e43:	bf 01 00 00 00       	mov    $0x1,%edi
    5e48:	48 8b 03             	mov    (%rbx),%rax
    5e4b:	48 01 e8             	add    %rbp,%rax
    5e4e:	48 8b 90 18 01 00 00 	mov    0x118(%rax),%rdx
    5e55:	31 c0                	xor    %eax,%eax
    5e57:	e8 f4 c5 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5e5c:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5e61:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    5e66:	4c 03 28             	add    (%rax),%r13
    5e69:	49 8b 85 18 01 00 00 	mov    0x118(%r13),%rax
    5e70:	48 85 c0             	test   %rax,%rax
    5e73:	0f 8e 60 01 00 00    	jle    5fd9 <verify+0x259>
    5e79:	48 8b 13             	mov    (%rbx),%rdx
    5e7c:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5e81:	45 31 ff             	xor    %r15d,%r15d
    5e84:	48 01 ea             	add    %rbp,%rdx
    5e87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5e90:	48 8b 82 18 01 00 00 	mov    0x118(%rdx),%rax
    5e97:	4d 89 fc             	mov    %r15,%r12
    5e9a:	31 db                	xor    %ebx,%ebx
    5e9c:	49 c1 e4 05          	shl    $0x5,%r12
    5ea0:	48 85 c0             	test   %rax,%rax
    5ea3:	7f 3f                	jg     5ee4 <verify+0x164>
    5ea5:	e9 16 01 00 00       	jmp    5fc0 <verify+0x240>
    5eaa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5eb0:	48 39 f1             	cmp    %rsi,%rcx
    5eb3:	0f 8d 7f 01 00 00    	jge    6038 <verify+0x2b8>
    5eb9:	4d 39 da             	cmp    %r11,%r10
    5ebc:	7e 09                	jle    5ec7 <verify+0x147>
    5ebe:	49 39 c6             	cmp    %rax,%r14
    5ec1:	0f 8c 89 00 00 00    	jl     5f50 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ec7:	4d 39 da             	cmp    %r11,%r10
    5eca:	0f 8d ab 01 00 00    	jge    607b <verify+0x2fb>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5ed0:	48 8b 82 18 01 00 00 	mov    0x118(%rdx),%rax
    5ed7:	48 83 c3 01          	add    $0x1,%rbx
    5edb:	48 39 d8             	cmp    %rbx,%rax
    5ede:	0f 8e dc 00 00 00    	jle    5fc0 <verify+0x240>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5ee4:	48 8b 82 08 01 00 00 	mov    0x108(%rdx),%rax
    5eeb:	49 89 d9             	mov    %rbx,%r9
    5eee:	49 8b 8d 08 01 00 00 	mov    0x108(%r13),%rcx
    5ef5:	49 c1 e1 05          	shl    $0x5,%r9
    5ef9:	4c 01 e1             	add    %r12,%rcx
    5efc:	4c 01 c8             	add    %r9,%rax
    5eff:	4c 8b 01             	mov    (%rcx),%r8
    5f02:	48 8b 38             	mov    (%rax),%rdi
    5f05:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    5f09:	4c 8b 59 10          	mov    0x10(%rcx),%r11
    5f0d:	4c 8b 71 18          	mov    0x18(%rcx),%r14
    5f11:	4c 8b 50 10          	mov    0x10(%rax),%r10
    5f15:	48 8b 48 08          	mov    0x8(%rax),%rcx
    5f19:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    5f1d:	4c 39 c7             	cmp    %r8,%rdi
    5f20:	7c 8e                	jl     5eb0 <verify+0x130>
    5f22:	0f 8e 38 01 00 00    	jle    6060 <verify+0x2e0>
    5f28:	48 39 f1             	cmp    %rsi,%rcx
    5f2b:	0f 8f 17 01 00 00    	jg     6048 <verify+0x2c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f31:	75 9d                	jne    5ed0 <verify+0x150>
    5f33:	4d 39 da             	cmp    %r11,%r10
    5f36:	7f 98                	jg     5ed0 <verify+0x150>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5f38:	49 39 c6             	cmp    %rax,%r14
    5f3b:	7d 13                	jge    5f50 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f3d:	4c 39 c7             	cmp    %r8,%rdi
    5f40:	75 8e                	jne    5ed0 <verify+0x150>
    5f42:	48 39 f1             	cmp    %rsi,%rcx
    5f45:	75 89                	jne    5ed0 <verify+0x150>
    5f47:	4d 39 da             	cmp    %r11,%r10
    5f4a:	75 84                	jne    5ed0 <verify+0x150>
    5f4c:	0f 1f 40 00          	nopl   0x0(%rax)
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
    5f50:	48 8b b2 08 01 00 00 	mov    0x108(%rdx),%rsi
    5f57:	bf 01 00 00 00       	mov    $0x1,%edi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5f5c:	48 83 c3 01          	add    $0x1,%rbx
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
    5f60:	49 8b 85 08 01 00 00 	mov    0x108(%r13),%rax
    5f67:	48 8b 8a 08 01 00 00 	mov    0x108(%rdx),%rcx
    5f6e:	49 8b 95 08 01 00 00 	mov    0x108(%r13),%rdx
    5f75:	4e 8b 44 20 08       	mov    0x8(%rax,%r12,1),%r8
    5f7a:	31 c0                	xor    %eax,%eax
    5f7c:	4a 8b 4c 09 10       	mov    0x10(%rcx,%r9,1),%rcx
    5f81:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    5f85:	4e 8b 4c 0e 18       	mov    0x18(%rsi,%r9,1),%r9
    5f8a:	48 8d 35 ef 14 00 00 	lea    0x14ef(%rip),%rsi        # 7480 <_IO_stdin_used+0x480>
    5f91:	e8 ba c4 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5f96:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5f9b:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    5fa0:	4c 03 28             	add    (%rax),%r13
    5fa3:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5fa8:	48 8b 10             	mov    (%rax),%rdx
    5fab:	48 01 ea             	add    %rbp,%rdx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5fae:	48 8b 82 18 01 00 00 	mov    0x118(%rdx),%rax
    5fb5:	48 39 d8             	cmp    %rbx,%rax
    5fb8:	0f 8f 26 ff ff ff    	jg     5ee4 <verify+0x164>
    5fbe:	66 90                	xchg   %ax,%ax
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5fc0:	49 8b 85 18 01 00 00 	mov    0x118(%r13),%rax
    5fc7:	49 83 c7 01          	add    $0x1,%r15
    5fcb:	4c 39 f8             	cmp    %r15,%rax
    5fce:	0f 8f bc fe ff ff    	jg     5e90 <verify+0x110>
    5fd4:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5fd9:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5fde:	49 83 c4 01          	add    $0x1,%r12
    5fe2:	44 39 60 08          	cmp    %r12d,0x8(%rax)
    5fe6:	0f 8f 3c fe ff ff    	jg     5e28 <verify+0xa8>
    5fec:	8b 5c 24 34          	mov    0x34(%rsp),%ebx
    5ff0:	44 8b 7c 24 38       	mov    0x38(%rsp),%r15d
    5ff5:	44 8b 74 24 3c       	mov    0x3c(%rsp),%r14d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5ffa:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5fff:	83 c3 01             	add    $0x1,%ebx
    6002:	48 81 44 24 18 80 01 00 00 	addq   $0x180,0x18(%rsp)
    600b:	39 58 08             	cmp    %ebx,0x8(%rax)
    600e:	0f 8f cb fd ff ff    	jg     5ddf <verify+0x5f>
    6014:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6019:	48 81 44 24 08 40 01 00 00 	addq   $0x140,0x8(%rsp)
    6022:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6027:	41 39 c6             	cmp    %eax,%r14d
    602a:	74 5d                	je     6089 <verify+0x309>
    602c:	41 89 c4             	mov    %eax,%r12d
    602f:	e9 82 fd ff ff       	jmp    5db6 <verify+0x36>
    6034:	0f 1f 40 00          	nopl   0x0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6038:	0f 85 92 fe ff ff    	jne    5ed0 <verify+0x150>
    603e:	e9 84 fe ff ff       	jmp    5ec7 <verify+0x147>
    6043:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6048:	49 39 c6             	cmp    %rax,%r14
    604b:	0f 8e e2 fe ff ff    	jle    5f33 <verify+0x1b3>
    6051:	4d 39 da             	cmp    %r11,%r10
    6054:	0f 8d d9 fe ff ff    	jge    5f33 <verify+0x1b3>
    605a:	e9 f1 fe ff ff       	jmp    5f50 <verify+0x1d0>
    605f:	90                   	nop
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6060:	48 39 f1             	cmp    %rsi,%rcx
    6063:	0f 8c 5e fe ff ff    	jl     5ec7 <verify+0x147>
    6069:	4d 39 da             	cmp    %r11,%r10
    606c:	0f 8e c6 fe ff ff    	jle    5f38 <verify+0x1b8>
    6072:	48 39 f1             	cmp    %rsi,%rcx
    6075:	0f 85 55 fe ff ff    	jne    5ed0 <verify+0x150>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    607b:	49 39 c6             	cmp    %rax,%r14
    607e:	0f 8f 4c fe ff ff    	jg     5ed0 <verify+0x150>
    6084:	e9 c7 fe ff ff       	jmp    5f50 <verify+0x1d0>
  for (int x = 0 ; x < thread_count; x++) {
    6089:	48 81 44 24 10 40 01 00 00 	addq   $0x140,0x10(%rsp)
    6092:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    6097:	41 8d 47 01          	lea    0x1(%r15),%eax
    609b:	45 39 e7             	cmp    %r12d,%r15d
    609e:	74 08                	je     60a8 <verify+0x328>
    60a0:	41 89 c7             	mov    %eax,%r15d
    60a3:	e9 01 fd ff ff       	jmp    5da9 <verify+0x29>
}
    60a8:	48 83 c4 48          	add    $0x48,%rsp
    60ac:	31 c0                	xor    %eax,%eax
    60ae:	5b                   	pop    %rbx
    60af:	5d                   	pop    %rbp
    60b0:	41 5c                	pop    %r12
    60b2:	41 5d                	pop    %r13
    60b4:	41 5e                	pop    %r14
    60b6:	41 5f                	pop    %r15
    60b8:	c3                   	ret
    60b9:	31 c0                	xor    %eax,%eax
    60bb:	c3                   	ret

Disassembly of section .fini:

00000000000060bc <_fini>:
    60bc:	f3 0f 1e fa          	endbr64
    60c0:	48 83 ec 08          	sub    $0x8,%rsp
    60c4:	48 83 c4 08          	add    $0x8,%rsp
    60c8:	c3                   	ret
