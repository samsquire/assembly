
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
    2540:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
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
    2580:	f3 0f 1e fa          	endbr64
    2584:	41 57                	push   %r15
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
    26ae:	be 18 00 00 00       	mov    $0x18,%esi
    26b3:	bf 0c 00 00 00       	mov    $0xc,%edi
    26b8:	e8 e3 fc ff ff       	call   23a0 <calloc@plt>
    26bd:	be 40 01 00 00       	mov    $0x140,%esi
    26c2:	bf 0f 00 00 00       	mov    $0xf,%edi
    26c7:	49 89 c6             	mov    %rax,%r14
    26ca:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    26cf:	e8 cc fc ff ff       	call   23a0 <calloc@plt>
    26d4:	be 10 00 00 00       	mov    $0x10,%esi
    26d9:	bf 01 00 00 00       	mov    $0x1,%edi
    26de:	4d 8d 66 e8          	lea    -0x18(%r14),%r12
    26e2:	48 89 04 24          	mov    %rax,(%rsp)
    26e6:	45 31 f6             	xor    %r14d,%r14d
    26e9:	e8 b2 fc ff ff       	call   23a0 <calloc@plt>
    26ee:	be 10 00 00 00       	mov    $0x10,%esi
    26f3:	bf 01 00 00 00       	mov    $0x1,%edi
    26f8:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    26fe:	48 89 c3             	mov    %rax,%rbx
    2701:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2706:	e8 95 fc ff ff       	call   23a0 <calloc@plt>
    270b:	4c 8b 1c 24          	mov    (%rsp),%r11
    270f:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
    2717:	48 89 43 08          	mov    %rax,0x8(%rbx)
    271b:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    2722:	4d 89 df             	mov    %r11,%r15
    2725:	4c 89 5c 24 38       	mov    %r11,0x38(%rsp)
    272a:	4c 89 5c 24 48       	mov    %r11,0x48(%rsp)
    272f:	90                   	nop
    2730:	be 08 00 00 00       	mov    $0x8,%esi
    2735:	bf 02 00 00 00       	mov    $0x2,%edi
    273a:	44 89 f5             	mov    %r14d,%ebp
    273d:	e8 5e fc ff ff       	call   23a0 <calloc@plt>
    2742:	be 80 00 00 00       	mov    $0x80,%esi
    2747:	bf 01 00 00 00       	mov    $0x1,%edi
    274c:	48 89 04 24          	mov    %rax,(%rsp)
    2750:	e8 4b fc ff ff       	call   23a0 <calloc@plt>
    2755:	48 89 c3             	mov    %rax,%rbx
    2758:	44 89 f0             	mov    %r14d,%eax
    275b:	41 83 c6 01          	add    $0x1,%r14d
    275f:	83 e0 01             	and    $0x1,%eax
    2762:	85 c0                	test   %eax,%eax
    2764:	0f 84 2c 0f 00 00    	je     3696 <main+0x1116>
    276a:	48 8b 04 24          	mov    (%rsp),%rax
    276e:	49 8d 8f c0 fe ff ff 	lea    -0x140(%r15),%rcx
    2775:	4d 89 f8             	mov    %r15,%r8
    2778:	89 ea                	mov    %ebp,%edx
    277a:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
    2781:	48 8d 35 67 4b 00 00 	lea    0x4b67(%rip),%rsi        # 72ef <_IO_stdin_used+0x2ef>
    2788:	bf 01 00 00 00       	mov    $0x1,%edi
    278d:	44 8d 6d ff          	lea    -0x1(%rbp),%r13d
    2791:	48 89 08             	mov    %rcx,(%rax)
    2794:	4c 89 78 08          	mov    %r15,0x8(%rax)
    2798:	31 c0                	xor    %eax,%eax
    279a:	e8 b1 fc ff ff       	call   2450 <__printf_chk@plt>
    279f:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    27a4:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    27a9:	4d 89 a7 80 00 00 00 	mov    %r12,0x80(%r15)
    27b0:	45 8b 07             	mov    (%r15),%r8d
    27b3:	44 89 e9             	mov    %r13d,%ecx
    27b6:	89 ea                	mov    %ebp,%edx
    27b8:	48 8d 35 a9 4d 00 00 	lea    0x4da9(%rip),%rsi        # 7568 <_IO_stdin_used+0x568>
    27bf:	bf 01 00 00 00       	mov    $0x1,%edi
    27c4:	31 c0                	xor    %eax,%eax
    27c6:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    27cc:	e8 7f fc ff ff       	call   2450 <__printf_chk@plt>
    27d1:	45 89 af 28 01 00 00 	mov    %r13d,0x128(%r15)
    27d8:	45 31 ed             	xor    %r13d,%r13d
    27db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    27e0:	44 89 e9             	mov    %r13d,%ecx
    27e3:	89 ea                	mov    %ebp,%edx
    27e5:	48 8d 35 ac 4d 00 00 	lea    0x4dac(%rip),%rsi        # 7598 <_IO_stdin_used+0x598>
    27ec:	31 c0                	xor    %eax,%eax
    27ee:	bf 01 00 00 00       	mov    $0x1,%edi
    27f3:	e8 58 fc ff ff       	call   2450 <__printf_chk@plt>
    27f8:	44 89 e9             	mov    %r13d,%ecx
    27fb:	4c 89 e0             	mov    %r12,%rax
    27fe:	41 83 c5 01          	add    $0x1,%r13d
    2802:	48 d3 e0             	shl    %cl,%rax
    2805:	48 09 03             	or     %rax,(%rbx)
    2808:	41 83 fd 06          	cmp    $0x6,%r13d
    280c:	75 d2                	jne    27e0 <main+0x260>
    280e:	48 8b 04 24          	mov    (%rsp),%rax
    2812:	49 89 9f 20 01 00 00 	mov    %rbx,0x120(%r15)
    2819:	31 db                	xor    %ebx,%ebx
    281b:	be 10 00 00 00       	mov    $0x10,%esi
    2820:	41 89 6f 04          	mov    %ebp,0x4(%r15)
    2824:	bf 64 00 00 00       	mov    $0x64,%edi
    2829:	49 89 47 40          	mov    %rax,0x40(%r15)
    282d:	48 8b 05 04 52 00 00 	mov    0x5204(%rip),%rax        # 7a38 <_IO_stdin_used+0xa38>
    2834:	41 c7 47 60 03 00 00 00 	movl   $0x3,0x60(%r15)
    283c:	49 89 47 48          	mov    %rax,0x48(%r15)
    2840:	e8 5b fb ff ff       	call   23a0 <calloc@plt>
    2845:	be 10 00 00 00       	mov    $0x10,%esi
    284a:	bf 64 00 00 00       	mov    $0x64,%edi
    284f:	49 89 87 d8 00 00 00 	mov    %rax,0xd8(%r15)
    2856:	e8 45 fb ff ff       	call   23a0 <calloc@plt>
    285b:	be 28 00 00 00       	mov    $0x28,%esi
    2860:	bf 64 00 00 00       	mov    $0x64,%edi
    2865:	66 0f 6f 05 b3 51 00 00 	movdqa 0x51b3(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    286d:	49 89 87 e0 00 00 00 	mov    %rax,0xe0(%r15)
    2874:	41 0f 29 87 f0 00 00 00 	movaps %xmm0,0xf0(%r15)
    287c:	e8 1f fb ff ff       	call   23a0 <calloc@plt>
    2881:	be 00 02 00 00       	mov    $0x200,%esi
    2886:	bf 03 00 00 00       	mov    $0x3,%edi
    288b:	66 0f 6f 0d 8d 51 00 00 	movdqa 0x518d(%rip),%xmm1        # 7a20 <_IO_stdin_used+0xa20>
    2893:	49 89 87 00 01 00 00 	mov    %rax,0x100(%r15)
    289a:	41 0f 11 8f 08 01 00 00 	movups %xmm1,0x108(%r15)
    28a2:	e8 f9 fa ff ff       	call   23a0 <calloc@plt>
    28a7:	44 89 74 24 20       	mov    %r14d,0x20(%rsp)
    28ac:	49 89 47 58          	mov    %rax,0x58(%r15)
    28b0:	48 89 c2             	mov    %rax,%rdx
    28b3:	4c 63 f3             	movslq %ebx,%r14
    28b6:	be 20 00 00 00       	mov    $0x20,%esi
    28bb:	bf 0c 00 00 00       	mov    $0xc,%edi
    28c0:	4d 89 f5             	mov    %r14,%r13
    28c3:	48 8d 05 36 0f 00 00 	lea    0xf36(%rip),%rax        # 3800 <do_protected_write>
    28ca:	49 c1 e5 09          	shl    $0x9,%r13
    28ce:	4e 8d 24 2a          	lea    (%rdx,%r13,1),%r12
    28d2:	49 89 84 24 20 01 00 00 	mov    %rax,0x120(%r12)
    28da:	e8 c1 fa ff ff       	call   23a0 <calloc@plt>
    28df:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    28e3:	49 89 84 24 68 01 00 00 	mov    %rax,0x168(%r12)
    28eb:	49 89 c4             	mov    %rax,%r12
    28ee:	48 8d 40 40          	lea    0x40(%rax),%rax
    28f2:	48 89 04 24          	mov    %rax,(%rsp)
    28f6:	89 6c 24 10          	mov    %ebp,0x10(%rsp)
    28fa:	be 08 00 00 00       	mov    $0x8,%esi
    28ff:	bf 01 00 00 00       	mov    $0x1,%edi
    2904:	49 83 c4 20          	add    $0x20,%r12
    2908:	e8 93 fa ff ff       	call   23a0 <calloc@plt>
    290d:	be 08 00 00 00       	mov    $0x8,%esi
    2912:	bf 01 00 00 00       	mov    $0x1,%edi
    2917:	48 89 c5             	mov    %rax,%rbp
    291a:	e8 81 fa ff ff       	call   23a0 <calloc@plt>
    291f:	be 18 00 00 00       	mov    $0x18,%esi
    2924:	bf 02 00 00 00       	mov    $0x2,%edi
    2929:	48 89 c3             	mov    %rax,%rbx
    292c:	e8 6f fa ff ff       	call   23a0 <calloc@plt>
    2931:	48 8d 70 18          	lea    0x18(%rax),%rsi
    2935:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    293d:	49 89 44 24 e0       	mov    %rax,-0x20(%r12)
    2942:	49 89 74 24 e8       	mov    %rsi,-0x18(%r12)
    2947:	48 89 28             	mov    %rbp,(%rax)
    294a:	48 89 58 18          	mov    %rbx,0x18(%rax)
    294e:	48 c7 40 10 01 00 00 00 	movq   $0x1,0x10(%rax)
    2956:	48 c7 40 20 00 00 00 00 	movq   $0x0,0x20(%rax)
    295e:	48 c7 40 28 01 00 00 00 	movq   $0x1,0x28(%rax)
    2966:	4c 39 24 24          	cmp    %r12,(%rsp)
    296a:	75 8e                	jne    28fa <main+0x37a>
    296c:	be 01 00 00 00       	mov    $0x1,%esi
    2971:	bf 00 01 00 00       	mov    $0x100,%edi
    2976:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    297a:	8b 6c 24 10          	mov    0x10(%rsp),%ebp
    297e:	e8 1d fa ff ff       	call   23a0 <calloc@plt>
    2983:	bf 18 00 00 00       	mov    $0x18,%edi
    2988:	49 89 c4             	mov    %rax,%r12
    298b:	e8 80 fa ff ff       	call   2410 <malloc@plt>
    2990:	4c 89 e7             	mov    %r12,%rdi
    2993:	41 89 d9             	mov    %ebx,%r9d
    2996:	41 89 e8             	mov    %ebp,%r8d
    2999:	48 8d 0d 18 4c 00 00 	lea    0x4c18(%rip),%rcx        # 75b8 <_IO_stdin_used+0x5b8>
    29a0:	48 89 04 24          	mov    %rax,(%rsp)
    29a4:	ba 00 01 00 00       	mov    $0x100,%edx
    29a9:	31 c0                	xor    %eax,%eax
    29ab:	be 01 00 00 00       	mov    $0x1,%esi
    29b0:	e8 6b fb ff ff       	call   2520 <__sprintf_chk@plt>
    29b5:	49 8b 57 58          	mov    0x58(%r15),%rdx
    29b9:	4c 8b 14 24          	mov    (%rsp),%r10
    29bd:	be 20 00 00 00       	mov    $0x20,%esi
    29c2:	49 63 07             	movslq (%r15),%rax
    29c5:	4d 89 22             	mov    %r12,(%r10)
    29c8:	4e 8d 24 2a          	lea    (%rdx,%r13,1),%r12
    29cc:	4d 89 72 10          	mov    %r14,0x10(%r10)
    29d0:	44 8d 73 01          	lea    0x1(%rbx),%r14d
    29d4:	49 89 42 08          	mov    %rax,0x8(%r10)
    29d8:	45 89 b4 24 88 01 00 00 	mov    %r14d,0x188(%r12)
    29e0:	4d 89 94 24 80 01 00 00 	mov    %r10,0x180(%r12)
    29e8:	41 c7 84 24 78 01 00 00 01 00 00 00 	movl   $0x1,0x178(%r12)
    29f4:	49 c7 84 24 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%r12)
    2a00:	49 8b bc 24 50 01 00 00 	mov    0x150(%r12),%rdi
    2a08:	48 89 14 24          	mov    %rdx,(%rsp)
    2a0c:	89 44 24 08          	mov    %eax,0x8(%rsp)
    2a10:	e8 8b f9 ff ff       	call   23a0 <calloc@plt>
    2a15:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2a19:	83 fb 01             	cmp    $0x1,%ebx
    2a1c:	48 8b 14 24          	mov    (%rsp),%rdx
    2a20:	49 89 84 24 48 01 00 00 	mov    %rax,0x148(%r12)
    2a28:	49 c7 84 24 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%r12)
    2a34:	41 89 8c 24 30 01 00 00 	mov    %ecx,0x130(%r12)
    2a3c:	4d 89 bc 24 28 01 00 00 	mov    %r15,0x128(%r12)
    2a44:	41 c7 84 24 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%r12)
    2a50:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
    2a5c:	41 c7 84 24 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%r12)
    2a68:	41 c7 84 24 3c 01 00 00 03 00 00 00 	movl   $0x3,0x13c(%r12)
    2a74:	41 c7 84 24 7c 01 00 00 0c 00 00 00 	movl   $0xc,0x17c(%r12)
    2a80:	41 89 1c 24          	mov    %ebx,(%r12)
    2a84:	0f 84 f3 0b 00 00    	je     367d <main+0x10fd>
    2a8a:	39 dd                	cmp    %ebx,%ebp
    2a8c:	75 5a                	jne    2ae8 <main+0x568>
    2a8e:	8b 4c 24 18          	mov    0x18(%rsp),%ecx
    2a92:	85 c9                	test   %ecx,%ecx
    2a94:	75 52                	jne    2ae8 <main+0x568>
    2a96:	89 ea                	mov    %ebp,%edx
    2a98:	48 8d 35 41 4b 00 00 	lea    0x4b41(%rip),%rsi        # 75e0 <_IO_stdin_used+0x5e0>
    2a9f:	bf 01 00 00 00       	mov    $0x1,%edi
    2aa4:	31 c0                	xor    %eax,%eax
    2aa6:	e8 a5 f9 ff ff       	call   2450 <__printf_chk@plt>
    2aab:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    2ab0:	49 8b 57 58          	mov    0x58(%r15),%rdx
    2ab4:	c7 44 24 18 01 00 00 00 	movl   $0x1,0x18(%rsp)
    2abc:	49 89 87 c0 00 00 00 	mov    %rax,0xc0(%r15)
    2ac3:	49 01 d5             	add    %rdx,%r13
    2ac6:	48 8d 05 e3 30 00 00 	lea    0x30e3(%rip),%rax        # 5bb0 <barriered_work_ingest>
    2acd:	49 89 85 18 01 00 00 	mov    %rax,0x118(%r13)
    2ad4:	41 83 fe 03          	cmp    $0x3,%r14d
    2ad8:	74 23                	je     2afd <main+0x57d>
    2ada:	bb 01 00 00 00       	mov    $0x1,%ebx
    2adf:	e9 cf fd ff ff       	jmp    28b3 <main+0x333>
    2ae4:	0f 1f 40 00          	nopl   0x0(%rax)
    2ae8:	48 8d 05 51 2d 00 00 	lea    0x2d51(%rip),%rax        # 5840 <barriered_work>
    2aef:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
    2af7:	41 83 fe 03          	cmp    $0x3,%r14d
    2afb:	75 dd                	jne    2ada <main+0x55a>
    2afd:	48 8d 05 fc 0c 00 00 	lea    0xcfc(%rip),%rax        # 3800 <do_protected_write>
    2b04:	44 8b 74 24 20       	mov    0x20(%rsp),%r14d
    2b09:	4c 8b 64 24 28       	mov    0x28(%rsp),%r12
    2b0e:	48 89 82 20 05 00 00 	mov    %rax,0x520(%rdx)
    2b15:	48 8d 05 34 0d 00 00 	lea    0xd34(%rip),%rax        # 3850 <barriered_reset>
    2b1c:	48 89 82 18 05 00 00 	mov    %rax,0x518(%rdx)
    2b23:	4c 89 ba 28 05 00 00 	mov    %r15,0x528(%rdx)
    2b2a:	49 81 c7 40 01 00 00 	add    $0x140,%r15
    2b31:	c7 82 38 05 00 00 01 00 00 00 	movl   $0x1,0x538(%rdx)
    2b3b:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
    2b45:	c7 82 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%rdx)
    2b4f:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
    2b59:	41 8b 87 c0 fe ff ff 	mov    -0x140(%r15),%eax
    2b60:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
    2b66:	c7 82 7c 05 00 00 0c 00 00 00 	movl   $0xc,0x57c(%rdx)
    2b70:	c7 82 3c 05 00 00 03 00 00 00 	movl   $0x3,0x53c(%rdx)
    2b7a:	41 83 fe 0f          	cmp    $0xf,%r14d
    2b7e:	0f 85 ac fb ff ff    	jne    2730 <main+0x1b0>
    2b84:	4c 8b 5c 24 38       	mov    0x38(%rsp),%r11
    2b89:	ba 0d 00 00 00       	mov    $0xd,%edx
    2b8e:	48 8d 35 77 47 00 00 	lea    0x4777(%rip),%rsi        # 730c <_IO_stdin_used+0x30c>
    2b95:	31 c0                	xor    %eax,%eax
    2b97:	bf 01 00 00 00       	mov    $0x1,%edi
    2b9c:	48 8b 6c 24 48       	mov    0x48(%rsp),%rbp
    2ba1:	4c 89 1c 24          	mov    %r11,(%rsp)
    2ba5:	e8 a6 f8 ff ff       	call   2450 <__printf_chk@plt>
    2baa:	be 08 00 00 00       	mov    $0x8,%esi
    2baf:	bf 02 00 00 00       	mov    $0x2,%edi
    2bb4:	e8 e7 f7 ff ff       	call   23a0 <calloc@plt>
    2bb9:	4c 8b 1c 24          	mov    (%rsp),%r11
    2bbd:	bf 0f 00 00 00       	mov    $0xf,%edi
    2bc2:	4d 8d bb 40 10 00 00 	lea    0x1040(%r11),%r15
    2bc9:	4d 8d b3 80 02 00 00 	lea    0x280(%r11),%r14
    2bd0:	49 89 83 80 10 00 00 	mov    %rax,0x1080(%r11)
    2bd7:	4c 89 38             	mov    %r15,(%rax)
    2bda:	49 8d 93 00 05 00 00 	lea    0x500(%r11),%rdx
    2be1:	49 8d 8b 80 07 00 00 	lea    0x780(%r11),%rcx
    2be8:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2bec:	49 8b 43 58          	mov    0x58(%r11),%rax
    2bf0:	4d 8d 8b c0 08 00 00 	lea    0x8c0(%r11),%r9
    2bf7:	4d 8d 93 00 0a 00 00 	lea    0xa00(%r11),%r10
    2bfe:	49 8d b3 c0 03 00 00 	lea    0x3c0(%r11),%rsi
    2c05:	49 8d 9b 40 06 00 00 	lea    0x640(%r11),%rbx
    2c0c:	41 c7 83 88 10 00 00 02 00 00 00 	movl   $0x2,0x1088(%r11)
    2c17:	48 89 54 24 50       	mov    %rdx,0x50(%rsp)
    2c1c:	4d 8d 83 40 0b 00 00 	lea    0xb40(%r11),%r8
    2c23:	4d 8d ab 80 0c 00 00 	lea    0xc80(%r11),%r13
    2c2a:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    2c2f:	4d 8d a3 c0 0d 00 00 	lea    0xdc0(%r11),%r12
    2c36:	41 c7 83 40 10 00 00 00 00 00 00 	movl   $0x0,0x1040(%r11)
    2c41:	41 c7 83 a0 10 00 00 03 00 00 00 	movl   $0x3,0x10a0(%r11)
    2c4c:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2c56:	49 8d 83 40 01 00 00 	lea    0x140(%r11),%rax
    2c5d:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2c62:	49 8b 83 98 01 00 00 	mov    0x198(%r11),%rax
    2c69:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2c6e:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2c78:	49 8b 83 d8 02 00 00 	mov    0x2d8(%r11),%rax
    2c7f:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    2c84:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2c8e:	49 8b 83 18 04 00 00 	mov    0x418(%r11),%rax
    2c95:	4c 89 7c 24 60       	mov    %r15,0x60(%rsp)
    2c9a:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2ca4:	49 8b 83 58 05 00 00 	mov    0x558(%r11),%rax
    2cab:	4c 89 74 24 68       	mov    %r14,0x68(%rsp)
    2cb0:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cba:	49 8b 83 98 06 00 00 	mov    0x698(%r11),%rax
    2cc1:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
    2cc6:	be 38 00 00 00       	mov    $0x38,%esi
    2ccb:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cd5:	49 8b 83 d8 07 00 00 	mov    0x7d8(%r11),%rax
    2cdc:	48 89 5c 24 58       	mov    %rbx,0x58(%rsp)
    2ce1:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2ceb:	49 8b 83 18 09 00 00 	mov    0x918(%r11),%rax
    2cf2:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cfc:	49 8b 83 58 0a 00 00 	mov    0xa58(%r11),%rax
    2d03:	4c 89 44 24 20       	mov    %r8,0x20(%rsp)
    2d08:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d12:	49 8b 83 98 0b 00 00 	mov    0xb98(%r11),%rax
    2d19:	4c 89 5c 24 70       	mov    %r11,0x70(%rsp)
    2d1e:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d28:	49 8b 83 d8 0c 00 00 	mov    0xcd8(%r11),%rax
    2d2f:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    2d34:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d3e:	49 8b 83 18 0e 00 00 	mov    0xe18(%r11),%rax
    2d45:	4c 89 24 24          	mov    %r12,(%rsp)
    2d49:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d53:	e8 48 f6 ff ff       	call   23a0 <calloc@plt>
    2d58:	be 38 00 00 00       	mov    $0x38,%esi
    2d5d:	bf 0f 00 00 00       	mov    $0xf,%edi
    2d62:	49 89 c4             	mov    %rax,%r12
    2d65:	e8 36 f6 ff ff       	call   23a0 <calloc@plt>
    2d6a:	be 38 00 00 00       	mov    $0x38,%esi
    2d6f:	bf 0f 00 00 00       	mov    $0xf,%edi
    2d74:	48 89 c3             	mov    %rax,%rbx
    2d77:	e8 24 f6 ff ff       	call   23a0 <calloc@plt>
    2d7c:	be 38 00 00 00       	mov    $0x38,%esi
    2d81:	bf 0f 00 00 00       	mov    $0xf,%edi
    2d86:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    2d8b:	e8 10 f6 ff ff       	call   23a0 <calloc@plt>
    2d90:	be 08 00 00 00       	mov    $0x8,%esi
    2d95:	bf 0f 00 00 00       	mov    $0xf,%edi
    2d9a:	48 89 84 24 80 00 00 00 	mov    %rax,0x80(%rsp)
    2da2:	e8 f9 f5 ff ff       	call   23a0 <calloc@plt>
    2da7:	4c 8b 5c 24 70       	mov    0x70(%rsp),%r11
    2dac:	be 08 00 00 00       	mov    $0x8,%esi
    2db1:	bf 0f 00 00 00       	mov    $0xf,%edi
    2db6:	49 89 c5             	mov    %rax,%r13
    2db9:	41 c7 83 08 0f 00 00 00 00 00 00 	movl   $0x0,0xf08(%r11)
    2dc4:	41 c7 83 64 0f 00 00 01 00 00 00 	movl   $0x1,0xf64(%r11)
    2dcf:	41 c7 83 60 0f 00 00 03 00 00 00 	movl   $0x3,0xf60(%r11)
    2dda:	e8 c1 f5 ff ff       	call   23a0 <calloc@plt>
    2ddf:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    2de4:	4c 8b 5c 24 70       	mov    0x70(%rsp),%r11
    2de9:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    2dee:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
    2df3:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2df7:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2dfb:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
    2e00:	4d 8d b3 00 0f 00 00 	lea    0xf00(%r11),%r14
    2e07:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    2e0c:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2e11:	4c 89 18             	mov    %r11,(%rax)
    2e14:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    2e19:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    2e1e:	48 89 78 28          	mov    %rdi,0x28(%rax)
    2e22:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    2e27:	48 89 70 18          	mov    %rsi,0x18(%rax)
    2e2b:	48 8d 35 e9 44 00 00 	lea    0x44e9(%rip),%rsi        # 731b <_IO_stdin_used+0x31b>
    2e32:	48 89 50 20          	mov    %rdx,0x20(%rax)
    2e36:	ba 0c 00 00 00       	mov    $0xc,%edx
    2e3b:	48 89 78 50          	mov    %rdi,0x50(%rax)
    2e3f:	48 8b 3c 24          	mov    (%rsp),%rdi
    2e43:	48 89 48 30          	mov    %rcx,0x30(%rax)
    2e47:	48 89 78 58          	mov    %rdi,0x58(%rax)
    2e4b:	49 8d bb 80 11 00 00 	lea    0x1180(%r11),%rdi
    2e52:	4c 89 48 38          	mov    %r9,0x38(%rax)
    2e56:	4c 89 50 40          	mov    %r10,0x40(%rax)
    2e5a:	4c 89 40 48          	mov    %r8,0x48(%rax)
    2e5e:	4c 89 70 60          	mov    %r14,0x60(%rax)
    2e62:	4c 89 78 68          	mov    %r15,0x68(%rax)
    2e66:	4c 8d 3d 93 0a 00 00 	lea    0xa93(%rip),%r15        # 3900 <barriered_thread>
    2e6d:	48 89 78 70          	mov    %rdi,0x70(%rax)
    2e71:	49 89 83 40 0f 00 00 	mov    %rax,0xf40(%r11)
    2e78:	31 c0                	xor    %eax,%eax
    2e7a:	41 c7 83 48 0f 00 00 0c 00 00 00 	movl   $0xc,0xf48(%r11)
    2e85:	41 c7 83 50 0f 00 00 02 00 00 00 	movl   $0x2,0xf50(%r11)
    2e90:	41 c7 83 00 0f 00 00 00 00 00 00 	movl   $0x0,0xf00(%r11)
    2e9b:	48 89 7c 24 70       	mov    %rdi,0x70(%rsp)
    2ea0:	bf 01 00 00 00       	mov    $0x1,%edi
    2ea5:	4c 89 9c 24 88 00 00 00 	mov    %r11,0x88(%rsp)
    2ead:	e8 9e f5 ff ff       	call   2450 <__printf_chk@plt>
    2eb2:	48 8d b3 a0 02 00 00 	lea    0x2a0(%rbx),%rsi
    2eb9:	49 8d 7d 60          	lea    0x60(%r13),%rdi
    2ebd:	4c 89 f1             	mov    %r14,%rcx
    2ec0:	4c 89 eb             	mov    %r13,%rbx
    2ec3:	45 31 f6             	xor    %r14d,%r14d
    2ec6:	48 8d 15 c3 0d 00 00 	lea    0xdc3(%rip),%rdx        # 3c90 <timer_thread>
    2ecd:	e8 9e f5 ff ff       	call   2470 <pthread_create@plt>
    2ed2:	45 89 f5             	mov    %r14d,%r13d
    2ed5:	49 89 de             	mov    %rbx,%r14
    2ed8:	c7 45 08 01 00 00 00 	movl   $0x1,0x8(%rbp)
    2edf:	44 89 ea             	mov    %r13d,%edx
    2ee2:	bf 01 00 00 00       	mov    $0x1,%edi
    2ee7:	31 c0                	xor    %eax,%eax
    2ee9:	c7 45 64 01 00 00 00 	movl   $0x1,0x64(%rbp)
    2ef0:	48 8d 35 09 47 00 00 	lea    0x4709(%rip),%rsi        # 7600 <_IO_stdin_used+0x600>
    2ef7:	41 83 c5 01          	add    $0x1,%r13d
    2efb:	e8 50 f5 ff ff       	call   2450 <__printf_chk@plt>
    2f00:	48 89 e9             	mov    %rbp,%rcx
    2f03:	4c 89 e6             	mov    %r12,%rsi
    2f06:	48 89 df             	mov    %rbx,%rdi
    2f09:	4c 89 fa             	mov    %r15,%rdx
    2f0c:	48 81 c5 40 01 00 00 	add    $0x140,%rbp
    2f13:	48 83 c3 08          	add    $0x8,%rbx
    2f17:	49 83 c4 38          	add    $0x38,%r12
    2f1b:	e8 50 f5 ff ff       	call   2470 <pthread_create@plt>
    2f20:	48 8b 55 e0          	mov    -0x20(%rbp),%rdx
    2f24:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    2f28:	be 08 00 00 00       	mov    $0x8,%esi
    2f2d:	e8 ae f3 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    2f32:	41 83 fd 0c          	cmp    $0xc,%r13d
    2f36:	75 a0                	jne    2ed8 <main+0x958>
    2f38:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    2f40:	be d8 00 00 00       	mov    $0xd8,%esi
    2f45:	bf 01 00 00 00       	mov    $0x1,%edi
    2f4a:	4d 89 f5             	mov    %r14,%r13
    2f4d:	41 c7 83 48 10 00 00 02 00 00 00 	movl   $0x2,0x1048(%r11)
    2f58:	41 c7 83 a4 10 00 00 01 00 00 00 	movl   $0x1,0x10a4(%r11)
    2f63:	41 c7 83 a0 10 00 00 00 00 00 00 	movl   $0x0,0x10a0(%r11)
    2f6e:	e8 2d f4 ff ff       	call   23a0 <calloc@plt>
    2f73:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    2f7b:	be 00 08 00 00       	mov    $0x800,%esi
    2f80:	31 ff                	xor    %edi,%edi
    2f82:	49 89 83 08 11 00 00 	mov    %rax,0x1108(%r11)
    2f89:	e8 22 f5 ff ff       	call   24b0 <eventfd@plt>
    2f8e:	be 08 00 00 00       	mov    $0x8,%esi
    2f93:	bf 0c 00 00 00       	mov    $0xc,%edi
    2f98:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    2fa0:	41 89 83 10 11 00 00 	mov    %eax,0x1110(%r11)
    2fa7:	e8 f4 f3 ff ff       	call   23a0 <calloc@plt>
    2fac:	4c 8b 4c 24 28       	mov    0x28(%rsp),%r9
    2fb1:	4c 8b 14 24          	mov    (%rsp),%r10
    2fb5:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    2fbd:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    2fc2:	4c 8b 74 24 68       	mov    0x68(%rsp),%r14
    2fc7:	48 8b 6c 24 50       	mov    0x50(%rsp),%rbp
    2fcc:	4c 89 48 50          	mov    %r9,0x50(%rax)
    2fd0:	4c 8b 64 24 58       	mov    0x58(%rsp),%r12
    2fd5:	4c 8b 7c 24 48       	mov    0x48(%rsp),%r15
    2fda:	4c 89 50 58          	mov    %r10,0x58(%rax)
    2fde:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    2fe3:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    2fe8:	4c 89 18             	mov    %r11,(%rax)
    2feb:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    2ff0:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    2ff5:	49 89 83 80 10 00 00 	mov    %rax,0x1080(%r11)
    2ffc:	41 c7 83 88 10 00 00 0c 00 00 00 	movl   $0xc,0x1088(%r11)
    3007:	41 c7 83 40 10 00 00 0d 00 00 00 	movl   $0xd,0x1040(%r11)
    3012:	48 89 58 08          	mov    %rbx,0x8(%rax)
    3016:	4c 89 70 10          	mov    %r14,0x10(%rax)
    301a:	48 89 68 20          	mov    %rbp,0x20(%rax)
    301e:	4c 89 60 28          	mov    %r12,0x28(%rax)
    3022:	48 89 78 30          	mov    %rdi,0x30(%rax)
    3026:	bf 01 00 00 00       	mov    $0x1,%edi
    302b:	48 89 70 38          	mov    %rsi,0x38(%rax)
    302f:	48 8d 35 03 43 00 00 	lea    0x4303(%rip),%rsi        # 7339 <_IO_stdin_used+0x339>
    3036:	48 89 50 40          	mov    %rdx,0x40(%rax)
    303a:	ba 0d 00 00 00       	mov    $0xd,%edx
    303f:	48 89 48 48          	mov    %rcx,0x48(%rax)
    3043:	4c 89 78 18          	mov    %r15,0x18(%rax)
    3047:	31 c0                	xor    %eax,%eax
    3049:	4c 89 5c 24 38       	mov    %r11,0x38(%rsp)
    304e:	e8 fd f3 ff ff       	call   2450 <__printf_chk@plt>
    3053:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    3058:	49 8d 7d 68          	lea    0x68(%r13),%rdi
    305c:	48 8b 4c 24 60       	mov    0x60(%rsp),%rcx
    3061:	48 8d 15 c8 1e 00 00 	lea    0x1ec8(%rip),%rdx        # 4f30 <io_thread>
    3068:	48 05 d8 02 00 00    	add    $0x2d8,%rax
    306e:	48 89 c6             	mov    %rax,%rsi
    3071:	e8 fa f3 ff ff       	call   2470 <pthread_create@plt>
    3076:	ba 0e 00 00 00       	mov    $0xe,%edx
    307b:	48 8d 35 ce 42 00 00 	lea    0x42ce(%rip),%rsi        # 7350 <_IO_stdin_used+0x350>
    3082:	31 c0                	xor    %eax,%eax
    3084:	bf 01 00 00 00       	mov    $0x1,%edi
    3089:	e8 c2 f3 ff ff       	call   2450 <__printf_chk@plt>
    308e:	4c 8b 5c 24 38       	mov    0x38(%rsp),%r11
    3093:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3098:	be 08 00 00 00       	mov    $0x8,%esi
    309d:	bf 0c 00 00 00       	mov    $0xc,%edi
    30a2:	41 c7 83 88 11 00 00 03 00 00 00 	movl   $0x3,0x1188(%r11)
    30ad:	41 c7 83 e4 11 00 00 01 00 00 00 	movl   $0x1,0x11e4(%r11)
    30b8:	41 c7 83 e0 11 00 00 00 00 00 00 	movl   $0x0,0x11e0(%r11)
    30c3:	49 89 83 40 12 00 00 	mov    %rax,0x1240(%r11)
    30ca:	4c 89 5c 24 30       	mov    %r11,0x30(%rsp)
    30cf:	e8 cc f2 ff ff       	call   23a0 <calloc@plt>
    30d4:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    30d9:	4c 8b 14 24          	mov    (%rsp),%r10
    30dd:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    30e2:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    30e7:	48 89 58 08          	mov    %rbx,0x8(%rax)
    30eb:	31 db                	xor    %ebx,%ebx
    30ed:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    30f2:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    30f7:	4c 89 18             	mov    %r11,(%rax)
    30fa:	4c 8b 4c 24 28       	mov    0x28(%rsp),%r9
    30ff:	4c 89 70 10          	mov    %r14,0x10(%rax)
    3103:	48 89 68 20          	mov    %rbp,0x20(%rax)
    3107:	48 8d 2d 7d 42 00 00 	lea    0x427d(%rip),%rbp        # 738b <_IO_stdin_used+0x38b>
    310e:	4c 89 60 28          	mov    %r12,0x28(%rax)
    3112:	4c 8d a4 24 90 00 00 00 	lea    0x90(%rsp),%r12
    311a:	48 89 78 30          	mov    %rdi,0x30(%rax)
    311e:	49 8d 7d 70          	lea    0x70(%r13),%rdi
    3122:	48 89 70 38          	mov    %rsi,0x38(%rax)
    3126:	48 8b b4 24 80 00 00 00 	mov    0x80(%rsp),%rsi
    312e:	48 89 50 40          	mov    %rdx,0x40(%rax)
    3132:	48 8d 15 97 0a 00 00 	lea    0xa97(%rip),%rdx        # 3bd0 <external_thread>
    3139:	48 89 48 48          	mov    %rcx,0x48(%rax)
    313d:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    3142:	48 81 c6 10 03 00 00 	add    $0x310,%rsi
    3149:	4c 89 48 50          	mov    %r9,0x50(%rax)
    314d:	4c 89 50 58          	mov    %r10,0x58(%rax)
    3151:	49 89 83 c0 11 00 00 	mov    %rax,0x11c0(%r11)
    3158:	4c 89 78 18          	mov    %r15,0x18(%rax)
    315c:	48 8b 05 dd 48 00 00 	mov    0x48dd(%rip),%rax        # 7a40 <_IO_stdin_used+0xa40>
    3163:	41 c7 83 80 11 00 00 0e 00 00 00 	movl   $0xe,0x1180(%r11)
    316e:	49 89 83 c8 11 00 00 	mov    %rax,0x11c8(%r11)
    3175:	4c 89 1c 24          	mov    %r11,(%rsp)
    3179:	e8 f2 f2 ff ff       	call   2470 <pthread_create@plt>
    317e:	48 8d 3d e8 41 00 00 	lea    0x41e8(%rip),%rdi        # 736d <_IO_stdin_used+0x36d>
    3185:	e8 66 f1 ff ff       	call   22f0 <puts@plt>
    318a:	4c 8b 34 24          	mov    (%rsp),%r14
    318e:	66 90                	xchg   %ax,%ax
    3190:	49 8b 7c dd 00       	mov    0x0(%r13,%rbx,8),%rdi
    3195:	4c 89 e6             	mov    %r12,%rsi
    3198:	e8 53 f3 ff ff       	call   24f0 <pthread_join@plt>
    319d:	89 da                	mov    %ebx,%edx
    319f:	48 89 ee             	mov    %rbp,%rsi
    31a2:	bf 01 00 00 00       	mov    $0x1,%edi
    31a7:	31 c0                	xor    %eax,%eax
    31a9:	48 83 c3 01          	add    $0x1,%rbx
    31ad:	e8 9e f2 ff ff       	call   2450 <__printf_chk@plt>
    31b2:	48 83 fb 0f          	cmp    $0xf,%rbx
    31b6:	75 d8                	jne    3190 <main+0xc10>
    31b8:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    31bd:	4d 89 f3             	mov    %r14,%r11
    31c0:	45 31 d2             	xor    %r10d,%r10d
    31c3:	4d 8d 7e 58          	lea    0x58(%r14),%r15
    31c7:	c7 04 24 00 00 00 00 	movl   $0x0,(%rsp)
    31ce:	45 31 f6             	xor    %r14d,%r14d
    31d1:	45 31 c9             	xor    %r9d,%r9d
    31d4:	31 db                	xor    %ebx,%ebx
    31d6:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    31db:	31 ed                	xor    %ebp,%ebp
    31dd:	4d 89 c8             	mov    %r9,%r8
    31e0:	49 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r13
    31ea:	4c 89 5c 24 20       	mov    %r11,0x20(%rsp)
    31ef:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    31f4:	4c 89 f8             	mov    %r15,%rax
    31f7:	4d 89 f7             	mov    %r14,%r15
    31fa:	49 89 c6             	mov    %rax,%r14
    31fd:	8b 3c 24             	mov    (%rsp),%edi
    3200:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    3205:	89 f8                	mov    %edi,%eax
    3207:	41 89 fc             	mov    %edi,%r12d
    320a:	83 c7 01             	add    $0x1,%edi
    320d:	83 e0 01             	and    $0x1,%eax
    3210:	41 83 ec 01          	sub    $0x1,%r12d
    3214:	89 3c 24             	mov    %edi,(%rsp)
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
    3242:	49 63 56 08          	movslq 0x8(%r14),%rdx
    3246:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    324b:	85 d2                	test   %edx,%edx
    324d:	0f 8e b1 04 00 00    	jle    3704 <main+0x1184>
    3253:	49 8b 06             	mov    (%r14),%rax
    3256:	48 c1 e2 09          	shl    $0x9,%rdx
    325a:	48 8d 3c 02          	lea    (%rdx,%rax,1),%rdi
    325e:	31 d2                	xor    %edx,%edx
    3260:	48 8b 88 10 01 00 00 	mov    0x110(%rax),%rcx
    3267:	48 05 00 02 00 00    	add    $0x200,%rax
    326d:	48 01 ca             	add    %rcx,%rdx
    3270:	48 39 c7             	cmp    %rax,%rdi
    3273:	75 eb                	jne    3260 <main+0xce0>
    3275:	4d 63 e4             	movslq %r12d,%r12
    3278:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    327d:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    3281:	48 c1 e0 06          	shl    $0x6,%rax
    3285:	48 01 f8             	add    %rdi,%rax
    3288:	48 63 70 60          	movslq 0x60(%rax),%rsi
    328c:	85 f6                	test   %esi,%esi
    328e:	7e 25                	jle    32b5 <main+0xd35>
    3290:	48 8b 40 58          	mov    0x58(%rax),%rax
    3294:	48 c1 e6 09          	shl    $0x9,%rsi
    3298:	48 8d 3c 06          	lea    (%rsi,%rax,1),%rdi
    329c:	0f 1f 40 00          	nopl   0x0(%rax)
    32a0:	48 8b 88 10 01 00 00 	mov    0x110(%rax),%rcx
    32a7:	48 05 00 02 00 00    	add    $0x200,%rax
    32ad:	48 01 ca             	add    %rcx,%rdx
    32b0:	48 39 c7             	cmp    %rax,%rdi
    32b3:	75 eb                	jne    32a0 <main+0xd20>
    32b5:	48 8d 35 f8 40 00 00 	lea    0x40f8(%rip),%rsi        # 73b4 <_IO_stdin_used+0x3b4>
    32bc:	bf 01 00 00 00       	mov    $0x1,%edi
    32c1:	31 c0                	xor    %eax,%eax
    32c3:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    32c8:	e8 83 f1 ff ff       	call   2450 <__printf_chk@plt>
    32cd:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    32d2:	bf 01 00 00 00       	mov    $0x1,%edi
    32d7:	48 8b 30             	mov    (%rax),%rsi
    32da:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    32e4:	48 f7 ee             	imul   %rsi
    32e7:	48 c1 fe 3f          	sar    $0x3f,%rsi
    32eb:	31 c0                	xor    %eax,%eax
    32ed:	48 d1 fa             	sar    %rdx
    32f0:	48 29 f2             	sub    %rsi,%rdx
    32f3:	48 8d 35 2e 43 00 00 	lea    0x432e(%rip),%rsi        # 7628 <_IO_stdin_used+0x628>
    32fa:	e8 51 f1 ff ff       	call   2450 <__printf_chk@plt>
    32ff:	bf 0a 00 00 00       	mov    $0xa,%edi
    3304:	e8 c7 ef ff ff       	call   22d0 <putchar@plt>
    3309:	49 63 56 08          	movslq 0x8(%r14),%rdx
    330d:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    3312:	85 d2                	test   %edx,%edx
    3314:	0f 8e 80 01 00 00    	jle    349a <main+0xf1a>
    331a:	49 8b 06             	mov    (%r14),%rax
    331d:	48 c1 e2 09          	shl    $0x9,%rdx
    3321:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3326:	48 01 c2             	add    %rax,%rdx
    3329:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3330:	48 8b 88 08 01 00 00 	mov    0x108(%rax),%rcx
    3337:	48 05 00 02 00 00    	add    $0x200,%rax
    333d:	49 01 cf             	add    %rcx,%r15
    3340:	48 8b 88 60 ff ff ff 	mov    -0xa0(%rax),%rcx
    3347:	49 01 c8             	add    %rcx,%r8
    334a:	48 8b 88 70 ff ff ff 	mov    -0x90(%rax),%rcx
    3351:	49 01 c9             	add    %rcx,%r9
    3354:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    335b:	48 03 69 10          	add    0x10(%rcx),%rbp
    335f:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    3366:	48 03 59 18          	add    0x18(%rcx),%rbx
    336a:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    3371:	48 03 69 30          	add    0x30(%rcx),%rbp
    3375:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    337c:	48 03 59 38          	add    0x38(%rcx),%rbx
    3380:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    3387:	48 03 69 50          	add    0x50(%rcx),%rbp
    338b:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    3392:	48 03 59 58          	add    0x58(%rcx),%rbx
    3396:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    339d:	48 03 69 70          	add    0x70(%rcx),%rbp
    33a1:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    33a8:	48 03 59 78          	add    0x78(%rcx),%rbx
    33ac:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    33b3:	48 03 a9 90 00 00 00 	add    0x90(%rcx),%rbp
    33ba:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    33c1:	48 03 99 98 00 00 00 	add    0x98(%rcx),%rbx
    33c8:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    33cf:	48 03 a9 b0 00 00 00 	add    0xb0(%rcx),%rbp
    33d6:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    33dd:	48 03 99 b8 00 00 00 	add    0xb8(%rcx),%rbx
    33e4:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    33eb:	48 03 a9 d0 00 00 00 	add    0xd0(%rcx),%rbp
    33f2:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    33f9:	48 03 99 d8 00 00 00 	add    0xd8(%rcx),%rbx
    3400:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    3407:	48 03 a9 f0 00 00 00 	add    0xf0(%rcx),%rbp
    340e:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    3415:	48 03 99 f8 00 00 00 	add    0xf8(%rcx),%rbx
    341c:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    3423:	48 03 a9 10 01 00 00 	add    0x110(%rcx),%rbp
    342a:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    3431:	48 03 99 18 01 00 00 	add    0x118(%rcx),%rbx
    3438:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    343f:	48 03 a9 30 01 00 00 	add    0x130(%rcx),%rbp
    3446:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    344d:	48 03 99 38 01 00 00 	add    0x138(%rcx),%rbx
    3454:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    345b:	48 03 a9 50 01 00 00 	add    0x150(%rcx),%rbp
    3462:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    3469:	48 03 99 58 01 00 00 	add    0x158(%rcx),%rbx
    3470:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    3477:	48 03 a9 70 01 00 00 	add    0x170(%rcx),%rbp
    347e:	48 8b 88 68 ff ff ff 	mov    -0x98(%rax),%rcx
    3485:	48 03 99 78 01 00 00 	add    0x178(%rcx),%rbx
    348c:	48 39 c2             	cmp    %rax,%rdx
    348f:	0f 85 9b fe ff ff    	jne    3330 <main+0xdb0>
    3495:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    349a:	45 31 e4             	xor    %r12d,%r12d
    349d:	49 83 be b8 00 00 00 00 	cmpq   $0x0,0xb8(%r14)
    34a5:	0f 8e 81 00 00 00    	jle    352c <main+0xfac>
    34ab:	4c 89 f0             	mov    %r14,%rax
    34ae:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    34b3:	49 89 de             	mov    %rbx,%r14
    34b6:	4c 89 e5             	mov    %r12,%rbp
    34b9:	48 89 c3             	mov    %rax,%rbx
    34bc:	4d 89 c4             	mov    %r8,%r12
    34bf:	90                   	nop
    34c0:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    34c7:	48 8d 54 ad 00       	lea    0x0(%rbp,%rbp,4),%rdx
    34cc:	48 83 ec 08          	sub    $0x8,%rsp
    34d0:	bf 01 00 00 00       	mov    $0x1,%edi
    34d5:	48 83 c5 01          	add    $0x1,%rbp
    34d9:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    34dd:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    34e1:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    34e5:	48 89 f0             	mov    %rsi,%rax
    34e8:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    34ec:	4c 2b 01             	sub    (%rcx),%r8
    34ef:	49 f7 e5             	mul    %r13
    34f2:	8b 49 20             	mov    0x20(%rcx),%ecx
    34f5:	56                   	push   %rsi
    34f6:	31 c0                	xor    %eax,%eax
    34f8:	48 8d 35 49 41 00 00 	lea    0x4149(%rip),%rsi        # 7648 <_IO_stdin_used+0x648>
    34ff:	48 c1 ea 12          	shr    $0x12,%rdx
    3503:	49 89 d1             	mov    %rdx,%r9
    3506:	ba 02 00 00 00       	mov    $0x2,%edx
    350b:	e8 40 ef ff ff       	call   2450 <__printf_chk@plt>
    3510:	58                   	pop    %rax
    3511:	5a                   	pop    %rdx
    3512:	48 39 ab b8 00 00 00 	cmp    %rbp,0xb8(%rbx)
    3519:	7f a5                	jg     34c0 <main+0xf40>
    351b:	48 89 d8             	mov    %rbx,%rax
    351e:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    3523:	4c 89 f3             	mov    %r14,%rbx
    3526:	4d 89 e0             	mov    %r12,%r8
    3529:	49 89 c6             	mov    %rax,%r14
    352c:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    3532:	49 81 c6 40 01 00 00 	add    $0x140,%r14
    3539:	83 3c 24 0c          	cmpl   $0xc,(%rsp)
    353d:	0f 85 ba fc ff ff    	jne    31fd <main+0xc7d>
    3543:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    3548:	4c 89 fa             	mov    %r15,%rdx
    354b:	bf 01 00 00 00       	mov    $0x1,%edi
    3550:	31 c0                	xor    %eax,%eax
    3552:	48 8d 35 68 3e 00 00 	lea    0x3e68(%rip),%rsi        # 73c1 <_IO_stdin_used+0x3c1>
    3559:	4c 89 04 24          	mov    %r8,(%rsp)
    355d:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    3567:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    356c:	e8 df ee ff ff       	call   2450 <__printf_chk@plt>
    3571:	bf 0a 00 00 00       	mov    $0xa,%edi
    3576:	e8 55 ed ff ff       	call   22d0 <putchar@plt>
    357b:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3580:	bf 01 00 00 00       	mov    $0x1,%edi
    3585:	48 8d 35 0c 41 00 00 	lea    0x410c(%rip),%rsi        # 7698 <_IO_stdin_used+0x698>
    358c:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3590:	31 c0                	xor    %eax,%eax
    3592:	e8 b9 ee ff ff       	call   2450 <__printf_chk@plt>
    3597:	4c 8b 0c 24          	mov    (%rsp),%r9
    359b:	bf 01 00 00 00       	mov    $0x1,%edi
    35a0:	48 8d 35 19 41 00 00 	lea    0x4119(%rip),%rsi        # 76c0 <_IO_stdin_used+0x6c0>
    35a7:	4c 89 c8             	mov    %r9,%rax
    35aa:	49 c1 f9 3f          	sar    $0x3f,%r9
    35ae:	49 f7 ec             	imul   %r12
    35b1:	31 c0                	xor    %eax,%eax
    35b3:	48 d1 fa             	sar    %rdx
    35b6:	4c 29 ca             	sub    %r9,%rdx
    35b9:	e8 92 ee ff ff       	call   2450 <__printf_chk@plt>
    35be:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    35c3:	bf 01 00 00 00       	mov    $0x1,%edi
    35c8:	48 8d 35 21 41 00 00 	lea    0x4121(%rip),%rsi        # 76f0 <_IO_stdin_used+0x6f0>
    35cf:	4c 89 d0             	mov    %r10,%rax
    35d2:	49 c1 fa 3f          	sar    $0x3f,%r10
    35d6:	49 f7 ec             	imul   %r12
    35d9:	31 c0                	xor    %eax,%eax
    35db:	48 d1 fa             	sar    %rdx
    35de:	4c 29 d2             	sub    %r10,%rdx
    35e1:	e8 6a ee ff ff       	call   2450 <__printf_chk@plt>
    35e6:	4c 89 f8             	mov    %r15,%rax
    35e9:	4c 89 f9             	mov    %r15,%rcx
    35ec:	bf 01 00 00 00       	mov    $0x1,%edi
    35f1:	49 f7 ec             	imul   %r12
    35f4:	48 c1 f9 3f          	sar    $0x3f,%rcx
    35f8:	48 8d 35 21 41 00 00 	lea    0x4121(%rip),%rsi        # 7720 <_IO_stdin_used+0x720>
    35ff:	31 c0                	xor    %eax,%eax
    3601:	48 d1 fa             	sar    %rdx
    3604:	48 29 ca             	sub    %rcx,%rdx
    3607:	e8 44 ee ff ff       	call   2450 <__printf_chk@plt>
    360c:	48 89 e8             	mov    %rbp,%rax
    360f:	48 c1 fd 3f          	sar    $0x3f,%rbp
    3613:	48 8d 35 bb 3d 00 00 	lea    0x3dbb(%rip),%rsi        # 73d5 <_IO_stdin_used+0x3d5>
    361a:	49 f7 ec             	imul   %r12
    361d:	bf 01 00 00 00       	mov    $0x1,%edi
    3622:	31 c0                	xor    %eax,%eax
    3624:	48 d1 fa             	sar    %rdx
    3627:	48 29 ea             	sub    %rbp,%rdx
    362a:	e8 21 ee ff ff       	call   2450 <__printf_chk@plt>
    362f:	48 89 d8             	mov    %rbx,%rax
    3632:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3636:	48 8d 35 a9 3d 00 00 	lea    0x3da9(%rip),%rsi        # 73e6 <_IO_stdin_used+0x3e6>
    363d:	49 f7 ec             	imul   %r12
    3640:	bf 01 00 00 00       	mov    $0x1,%edi
    3645:	48 d1 fa             	sar    %rdx
    3648:	48 29 da             	sub    %rbx,%rdx
    364b:	31 c0                	xor    %eax,%eax
    364d:	e8 fe ed ff ff       	call   2450 <__printf_chk@plt>
    3652:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    365a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3663:	0f 85 a2 00 00 00    	jne    370b <main+0x118b>
    3669:	48 81 c4 a8 00 00 00 	add    $0xa8,%rsp
    3670:	31 c0                	xor    %eax,%eax
    3672:	5b                   	pop    %rbx
    3673:	5d                   	pop    %rbp
    3674:	41 5c                	pop    %r12
    3676:	41 5d                	pop    %r13
    3678:	41 5e                	pop    %r14
    367a:	41 5f                	pop    %r15
    367c:	c3                   	ret
    367d:	48 8d 05 bc 21 00 00 	lea    0x21bc(%rip),%rax        # 5840 <barriered_work>
    3684:	bb 02 00 00 00       	mov    $0x2,%ebx
    3689:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
    3691:	e9 1d f2 ff ff       	jmp    28b3 <main+0x333>
    3696:	b8 89 88 88 88       	mov    $0x88888889,%eax
    369b:	45 89 f2             	mov    %r14d,%r10d
    369e:	45 89 f5             	mov    %r14d,%r13d
    36a1:	48 8b 3c 24          	mov    (%rsp),%rdi
    36a5:	4c 0f af d0          	imul   %rax,%r10
    36a9:	41 c7 07 00 00 00 00 	movl   $0x0,(%r15)
    36b0:	4c 89 f9             	mov    %r15,%rcx
    36b3:	89 ea                	mov    %ebp,%edx
    36b5:	4c 89 3f             	mov    %r15,(%rdi)
    36b8:	48 8d 35 3e 3c 00 00 	lea    0x3c3e(%rip),%rsi        # 72fd <_IO_stdin_used+0x2fd>
    36bf:	49 c1 ea 23          	shr    $0x23,%r10
    36c3:	44 89 d0             	mov    %r10d,%eax
    36c6:	c1 e0 04             	shl    $0x4,%eax
    36c9:	44 29 d0             	sub    %r10d,%eax
    36cc:	41 29 c5             	sub    %eax,%r13d
    36cf:	49 63 c5             	movslq %r13d,%rax
    36d2:	4c 8d 04 80          	lea    (%rax,%rax,4),%r8
    36d6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    36db:	49 c1 e0 06          	shl    $0x6,%r8
    36df:	49 01 c0             	add    %rax,%r8
    36e2:	31 c0                	xor    %eax,%eax
    36e4:	4c 89 47 08          	mov    %r8,0x8(%rdi)
    36e8:	bf 01 00 00 00       	mov    $0x1,%edi
    36ed:	e8 5e ed ff ff       	call   2450 <__printf_chk@plt>
    36f2:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    36f7:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    36fc:	49 89 c4             	mov    %rax,%r12
    36ff:	e9 a5 f0 ff ff       	jmp    27a9 <main+0x229>
    3704:	31 d2                	xor    %edx,%edx
    3706:	e9 6a fb ff ff       	jmp    3275 <main+0xcf5>
    370b:	e8 20 ec ff ff       	call   2330 <__stack_chk_fail@plt>

0000000000003710 <_start>:
    3710:	f3 0f 1e fa          	endbr64
    3714:	31 ed                	xor    %ebp,%ebp
    3716:	49 89 d1             	mov    %rdx,%r9
    3719:	5e                   	pop    %rsi
    371a:	48 89 e2             	mov    %rsp,%rdx
    371d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3721:	50                   	push   %rax
    3722:	54                   	push   %rsp
    3723:	45 31 c0             	xor    %r8d,%r8d
    3726:	31 c9                	xor    %ecx,%ecx
    3728:	48 8d 3d 51 ee ff ff 	lea    -0x11af(%rip),%rdi        # 2580 <main>
    372f:	ff 15 a3 68 00 00    	call   *0x68a3(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3735:	f4                   	hlt
    3736:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003740 <deregister_tm_clones>:
    3740:	48 8d 3d d9 68 00 00 	lea    0x68d9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3747:	48 8d 05 d2 68 00 00 	lea    0x68d2(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    374e:	48 39 f8             	cmp    %rdi,%rax
    3751:	74 15                	je     3768 <deregister_tm_clones+0x28>
    3753:	48 8b 05 86 68 00 00 	mov    0x6886(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    375a:	48 85 c0             	test   %rax,%rax
    375d:	74 09                	je     3768 <deregister_tm_clones+0x28>
    375f:	ff e0                	jmp    *%rax
    3761:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3768:	c3                   	ret
    3769:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003770 <register_tm_clones>:
    3770:	48 8d 3d a9 68 00 00 	lea    0x68a9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3777:	48 8d 35 a2 68 00 00 	lea    0x68a2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    377e:	48 29 fe             	sub    %rdi,%rsi
    3781:	48 89 f0             	mov    %rsi,%rax
    3784:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3788:	48 c1 f8 03          	sar    $0x3,%rax
    378c:	48 01 c6             	add    %rax,%rsi
    378f:	48 d1 fe             	sar    %rsi
    3792:	74 14                	je     37a8 <register_tm_clones+0x38>
    3794:	48 8b 05 55 68 00 00 	mov    0x6855(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    379b:	48 85 c0             	test   %rax,%rax
    379e:	74 08                	je     37a8 <register_tm_clones+0x38>
    37a0:	ff e0                	jmp    *%rax
    37a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    37a8:	c3                   	ret
    37a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037b0 <__do_global_dtors_aux>:
    37b0:	f3 0f 1e fa          	endbr64
    37b4:	80 3d 6d 68 00 00 00 	cmpb   $0x0,0x686d(%rip)        # a028 <completed.0>
    37bb:	75 2b                	jne    37e8 <__do_global_dtors_aux+0x38>
    37bd:	55                   	push   %rbp
    37be:	48 83 3d 32 68 00 00 00 	cmpq   $0x0,0x6832(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    37c6:	48 89 e5             	mov    %rsp,%rbp
    37c9:	74 0c                	je     37d7 <__do_global_dtors_aux+0x27>
    37cb:	48 8b 3d 36 68 00 00 	mov    0x6836(%rip),%rdi        # a008 <__dso_handle>
    37d2:	e8 d9 ea ff ff       	call   22b0 <__cxa_finalize@plt>
    37d7:	e8 64 ff ff ff       	call   3740 <deregister_tm_clones>
    37dc:	c6 05 45 68 00 00 01 	movb   $0x1,0x6845(%rip)        # a028 <completed.0>
    37e3:	5d                   	pop    %rbp
    37e4:	c3                   	ret
    37e5:	0f 1f 00             	nopl   (%rax)
    37e8:	c3                   	ret
    37e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037f0 <frame_dummy>:
    37f0:	f3 0f 1e fa          	endbr64
    37f4:	e9 77 ff ff ff       	jmp    3770 <register_tm_clones>
    37f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003800 <do_protected_write>:
    3800:	f3 0f 1e fa          	endbr64
    3804:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    380b:	48 8b 97 10 01 00 00 	mov    0x110(%rdi),%rdx
    3812:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    3819:	48 83 c2 01          	add    $0x1,%rdx
    381d:	48 89 97 10 01 00 00 	mov    %rdx,0x110(%rdi)
    3824:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3828:	48 83 00 01          	addq   $0x1,(%rax)
    382c:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3833:	48 85 c9             	test   %rcx,%rcx
    3836:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    383d:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3841:	48 89 50 08          	mov    %rdx,0x8(%rax)
    3845:	31 c0                	xor    %eax,%eax
    3847:	c3                   	ret
    3848:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000003850 <barriered_reset>:
    3850:	f3 0f 1e fa          	endbr64
    3854:	8b 97 3c 01 00 00    	mov    0x13c(%rdi),%edx
    385a:	48 89 f8             	mov    %rdi,%rax
    385d:	85 d2                	test   %edx,%edx
    385f:	0f 8e 91 00 00 00    	jle    38f6 <barriered_reset+0xa6>
    3865:	31 c9                	xor    %ecx,%ecx
    3867:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3870:	48 8b b8 28 01 00 00 	mov    0x128(%rax),%rdi
    3877:	48 63 b0 30 01 00 00 	movslq 0x130(%rax),%rsi
    387e:	48 89 ca             	mov    %rcx,%rdx
    3881:	48 83 c1 01          	add    $0x1,%rcx
    3885:	48 c1 e2 09          	shl    $0x9,%rdx
    3889:	48 8b 7f 40          	mov    0x40(%rdi),%rdi
    388d:	48 8b 34 f7          	mov    (%rdi,%rsi,8),%rsi
    3891:	48 8b 7e 58          	mov    0x58(%rsi),%rdi
    3895:	48 01 d7             	add    %rdx,%rdi
    3898:	8b b7 80 00 00 00    	mov    0x80(%rdi),%esi
    389e:	83 c6 01             	add    $0x1,%esi
    38a1:	89 b7 80 00 00 00    	mov    %esi,0x80(%rdi)
    38a7:	48 8b b8 28 01 00 00 	mov    0x128(%rax),%rdi
    38ae:	48 63 b0 30 01 00 00 	movslq 0x130(%rax),%rsi
    38b5:	48 8b 7f 40          	mov    0x40(%rdi),%rdi
    38b9:	48 8b 34 f7          	mov    (%rdi,%rsi,8),%rsi
    38bd:	48 8b 7e 58          	mov    0x58(%rsi),%rdi
    38c1:	48 01 d7             	add    %rdx,%rdi
    38c4:	8b b7 00 01 00 00    	mov    0x100(%rdi),%esi
    38ca:	83 c6 01             	add    $0x1,%esi
    38cd:	89 b7 00 01 00 00    	mov    %esi,0x100(%rdi)
    38d3:	48 8b b0 28 01 00 00 	mov    0x128(%rax),%rsi
    38da:	48 03 56 58          	add    0x58(%rsi),%rdx
    38de:	c7 82 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rdx)
    38e8:	8b 90 3c 01 00 00    	mov    0x13c(%rax),%edx
    38ee:	39 ca                	cmp    %ecx,%edx
    38f0:	0f 8f 7a ff ff ff    	jg     3870 <barriered_reset+0x20>
    38f6:	0f ae f8             	sfence
    38f9:	31 c0                	xor    %eax,%eax
    38fb:	c3                   	ret
    38fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003900 <barriered_thread>:
    3900:	f3 0f 1e fa          	endbr64
    3904:	8b 47 64             	mov    0x64(%rdi),%eax
    3907:	83 f8 01             	cmp    $0x1,%eax
    390a:	0f 85 b9 02 00 00    	jne    3bc9 <barriered_thread+0x2c9>
    3910:	41 56                	push   %r14
    3912:	41 55                	push   %r13
    3914:	49 89 fd             	mov    %rdi,%r13
    3917:	41 54                	push   %r12
    3919:	55                   	push   %rbp
    391a:	31 ed                	xor    %ebp,%ebp
    391c:	53                   	push   %rbx
    391d:	31 db                	xor    %ebx,%ebx
    391f:	90                   	nop
    3920:	41 8b 4d 60          	mov    0x60(%r13),%ecx
    3924:	39 d9                	cmp    %ebx,%ecx
    3926:	7f 12                	jg     393a <barriered_thread+0x3a>
    3928:	49 83 85 18 01 00 00 01 	addq   $0x1,0x118(%r13)
    3930:	31 db                	xor    %ebx,%ebx
    3932:	85 c9                	test   %ecx,%ecx
    3934:	0f 8e 76 01 00 00    	jle    3ab0 <barriered_thread+0x1b0>
    393a:	4c 63 e3             	movslq %ebx,%r12
    393d:	49 c1 e4 09          	shl    $0x9,%r12
    3941:	eb 17                	jmp    395a <barriered_thread+0x5a>
    3943:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3948:	83 c3 01             	add    $0x1,%ebx
    394b:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    3952:	39 cb                	cmp    %ecx,%ebx
    3954:	0f 8d 56 01 00 00    	jge    3ab0 <barriered_thread+0x1b0>
    395a:	49 8b 45 58          	mov    0x58(%r13),%rax
    395e:	4a 8d 14 20          	lea    (%rax,%r12,1),%rdx
    3962:	8b b2 38 01 00 00    	mov    0x138(%rdx),%esi
    3968:	83 fe 01             	cmp    $0x1,%esi
    396b:	75 db                	jne    3948 <barriered_thread+0x48>
    396d:	45 8b 4d 48          	mov    0x48(%r13),%r9d
    3971:	83 e9 01             	sub    $0x1,%ecx
    3974:	8d 73 ff             	lea    -0x1(%rbx),%esi
    3977:	85 db                	test   %ebx,%ebx
    3979:	0f 4f ce             	cmovg  %esi,%ecx
    397c:	45 85 c9             	test   %r9d,%r9d
    397f:	0f 8e 5b 01 00 00    	jle    3ae0 <barriered_thread+0x1e0>
    3985:	49 8b 45 40          	mov    0x40(%r13),%rax
    3989:	48 63 f1             	movslq %ecx,%rsi
    398c:	49 63 c9             	movslq %r9d,%rcx
    398f:	31 ff                	xor    %edi,%edi
    3991:	48 c1 e6 09          	shl    $0x9,%rsi
    3995:	45 31 f6             	xor    %r14d,%r14d
    3998:	4c 8d 14 c8          	lea    (%rax,%rcx,8),%r10
    399c:	0f 1f 40 00          	nopl   0x0(%rax)
    39a0:	48 8b 08             	mov    (%rax),%rcx
    39a3:	4c 8b 59 58          	mov    0x58(%rcx),%r11
    39a7:	49 01 f3             	add    %rsi,%r11
    39aa:	45 8b 83 80 00 00 00 	mov    0x80(%r11),%r8d
    39b1:	4c 89 d9             	mov    %r11,%rcx
    39b4:	44 8b 9a 80 00 00 00 	mov    0x80(%rdx),%r11d
    39bb:	8b 89 00 01 00 00    	mov    0x100(%rcx),%ecx
    39c1:	45 39 c3             	cmp    %r8d,%r11d
    39c4:	41 0f 94 c0          	sete   %r8b
    39c8:	45 0f b6 c0          	movzbl %r8b,%r8d
    39cc:	45 01 c6             	add    %r8d,%r14d
    39cf:	44 8b 82 00 01 00 00 	mov    0x100(%rdx),%r8d
    39d6:	41 39 c8             	cmp    %ecx,%r8d
    39d9:	0f 94 c1             	sete   %cl
    39dc:	48 83 c0 08          	add    $0x8,%rax
    39e0:	0f b6 c9             	movzbl %cl,%ecx
    39e3:	01 cf                	add    %ecx,%edi
    39e5:	4c 39 d0             	cmp    %r10,%rax
    39e8:	75 b6                	jne    39a0 <barriered_thread+0xa0>
    39ea:	41 39 f9             	cmp    %edi,%r9d
    39ed:	0f 84 dd 00 00 00    	je     3ad0 <barriered_thread+0x1d0>
    39f3:	85 ff                	test   %edi,%edi
    39f5:	0f 84 d5 00 00 00    	je     3ad0 <barriered_thread+0x1d0>
    39fb:	45 85 f6             	test   %r14d,%r14d
    39fe:	74 0a                	je     3a0a <barriered_thread+0x10a>
    3a00:	45 39 75 48          	cmp    %r14d,0x48(%r13)
    3a04:	0f 85 a6 00 00 00    	jne    3ab0 <barriered_thread+0x1b0>
    3a0a:	49 8b 45 58          	mov    0x58(%r13),%rax
    3a0e:	4c 01 e0             	add    %r12,%rax
    3a11:	8b 90 00 01 00 00    	mov    0x100(%rax),%edx
    3a17:	83 c2 01             	add    $0x1,%edx
    3a1a:	89 90 00 01 00 00    	mov    %edx,0x100(%rax)
    3a20:	85 db                	test   %ebx,%ebx
    3a22:	75 14                	jne    3a38 <barriered_thread+0x138>
    3a24:	49 8b b5 f0 00 00 00 	mov    0xf0(%r13),%rsi
    3a2b:	49 3b b5 f8 00 00 00 	cmp    0xf8(%r13),%rsi
    3a32:	0f 8c 70 01 00 00    	jl     3ba8 <barriered_thread+0x2a8>
    3a38:	49 63 4d 00          	movslq 0x0(%r13),%rcx
    3a3c:	49 8b 55 40          	mov    0x40(%r13),%rdx
    3a40:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
    3a4a:	48 8b 80 18 01 00 00 	mov    0x118(%rax),%rax
    3a51:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    3a55:	48 8b 7a 58          	mov    0x58(%rdx),%rdi
    3a59:	4c 01 e7             	add    %r12,%rdi
    3a5c:	ff d0                	call   *%rax
    3a5e:	49 8b 55 58          	mov    0x58(%r13),%rdx
    3a62:	4c 01 e2             	add    %r12,%rdx
    3a65:	8b 82 80 00 00 00    	mov    0x80(%rdx),%eax
    3a6b:	83 c0 01             	add    $0x1,%eax
    3a6e:	89 82 80 00 00 00    	mov    %eax,0x80(%rdx)
    3a74:	41 8b 45 60          	mov    0x60(%r13),%eax
    3a78:	49 83 85 e8 00 00 00 01 	addq   $0x1,0xe8(%r13)
    3a80:	83 e8 01             	sub    $0x1,%eax
    3a83:	39 d8                	cmp    %ebx,%eax
    3a85:	0f 84 ad 00 00 00    	je     3b38 <barriered_thread+0x238>
    3a8b:	0f ae f8             	sfence
    3a8e:	85 ed                	test   %ebp,%ebp
    3a90:	0f 84 da 00 00 00    	je     3b70 <barriered_thread+0x270>
    3a96:	41 8b 4d 60          	mov    0x60(%r13),%ecx
    3a9a:	83 c3 01             	add    $0x1,%ebx
    3a9d:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    3aa4:	39 cb                	cmp    %ecx,%ebx
    3aa6:	0f 8c ae fe ff ff    	jl     395a <barriered_thread+0x5a>
    3aac:	0f 1f 40 00          	nopl   0x0(%rax)
    3ab0:	41 8b 45 64          	mov    0x64(%r13),%eax
    3ab4:	83 f8 01             	cmp    $0x1,%eax
    3ab7:	0f 84 63 fe ff ff    	je     3920 <barriered_thread+0x20>
    3abd:	5b                   	pop    %rbx
    3abe:	31 c0                	xor    %eax,%eax
    3ac0:	5d                   	pop    %rbp
    3ac1:	41 5c                	pop    %r12
    3ac3:	41 5d                	pop    %r13
    3ac5:	41 5e                	pop    %r14
    3ac7:	c3                   	ret
    3ac8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3ad0:	83 fd 01             	cmp    $0x1,%ebp
    3ad3:	74 1b                	je     3af0 <barriered_thread+0x1f0>
    3ad5:	31 ed                	xor    %ebp,%ebp
    3ad7:	e9 1f ff ff ff       	jmp    39fb <barriered_thread+0xfb>
    3adc:	0f 1f 40 00          	nopl   0x0(%rax)
    3ae0:	83 fd 01             	cmp    $0x1,%ebp
    3ae3:	0f 85 25 ff ff ff    	jne    3a0e <barriered_thread+0x10e>
    3ae9:	45 31 f6             	xor    %r14d,%r14d
    3aec:	0f 1f 40 00          	nopl   0x0(%rax)
    3af0:	49 8b 85 08 01 00 00 	mov    0x108(%r13),%rax
    3af7:	bf 04 00 00 00       	mov    $0x4,%edi
    3afc:	31 ed                	xor    %ebp,%ebp
    3afe:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3b02:	49 8b 85 00 01 00 00 	mov    0x100(%r13),%rax
    3b09:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3b0e:	e8 fd e7 ff ff       	call   2310 <clock_gettime@plt>
    3b13:	49 8b 85 08 01 00 00 	mov    0x108(%r13),%rax
    3b1a:	48 83 c0 01          	add    $0x1,%rax
    3b1e:	48 99                	cqto
    3b20:	49 f7 bd 10 01 00 00 	idivq  0x110(%r13)
    3b27:	49 89 95 08 01 00 00 	mov    %rdx,0x108(%r13)
    3b2e:	e9 c8 fe ff ff       	jmp    39fb <barriered_thread+0xfb>
    3b33:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3b38:	49 8b b5 f0 00 00 00 	mov    0xf0(%r13),%rsi
    3b3f:	49 3b b5 f8 00 00 00 	cmp    0xf8(%r13),%rsi
    3b46:	0f 8d 3f ff ff ff    	jge    3a8b <barriered_thread+0x18b>
    3b4c:	48 c1 e6 04          	shl    $0x4,%rsi
    3b50:	bf 04 00 00 00       	mov    $0x4,%edi
    3b55:	49 03 b5 e0 00 00 00 	add    0xe0(%r13),%rsi
    3b5c:	e8 af e7 ff ff       	call   2310 <clock_gettime@plt>
    3b61:	49 83 85 f0 00 00 00 01 	addq   $0x1,0xf0(%r13)
    3b69:	e9 1d ff ff ff       	jmp    3a8b <barriered_thread+0x18b>
    3b6e:	66 90                	xchg   %ax,%ax
    3b70:	49 8b 85 08 01 00 00 	mov    0x108(%r13),%rax
    3b77:	bf 04 00 00 00       	mov    $0x4,%edi
    3b7c:	bd 01 00 00 00       	mov    $0x1,%ebp
    3b81:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3b85:	49 8b 85 00 01 00 00 	mov    0x100(%r13),%rax
    3b8c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3b90:	89 5e 20             	mov    %ebx,0x20(%rsi)
    3b93:	e8 78 e7 ff ff       	call   2310 <clock_gettime@plt>
    3b98:	41 8b 4d 60          	mov    0x60(%r13),%ecx
    3b9c:	e9 a7 fd ff ff       	jmp    3948 <barriered_thread+0x48>
    3ba1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3ba8:	48 c1 e6 04          	shl    $0x4,%rsi
    3bac:	bf 04 00 00 00       	mov    $0x4,%edi
    3bb1:	49 03 b5 d8 00 00 00 	add    0xd8(%r13),%rsi
    3bb8:	e8 53 e7 ff ff       	call   2310 <clock_gettime@plt>
    3bbd:	49 8b 45 58          	mov    0x58(%r13),%rax
    3bc1:	4c 01 e0             	add    %r12,%rax
    3bc4:	e9 6f fe ff ff       	jmp    3a38 <barriered_thread+0x138>
    3bc9:	31 c0                	xor    %eax,%eax
    3bcb:	c3                   	ret
    3bcc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003bd0 <external_thread>:
    3bd0:	f3 0f 1e fa          	endbr64
    3bd4:	41 55                	push   %r13
    3bd6:	41 54                	push   %r12
    3bd8:	55                   	push   %rbp
    3bd9:	53                   	push   %rbx
    3bda:	48 83 ec 38          	sub    $0x38,%rsp
    3bde:	66 0f 6f 05 5a 3d 00 00 	movdqa 0x3d5a(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3be6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3bef:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3bf4:	31 c0                	xor    %eax,%eax
    3bf6:	0f 29 04 24          	movaps %xmm0,(%rsp)
    3bfa:	8b 47 64             	mov    0x64(%rdi),%eax
    3bfd:	83 f8 01             	cmp    $0x1,%eax
    3c00:	75 64                	jne    3c66 <external_thread+0x96>
    3c02:	49 89 fd             	mov    %rdi,%r13
    3c05:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3c0a:	48 89 e3             	mov    %rsp,%rbx
    3c0d:	4c 8d 25 f0 33 00 00 	lea    0x33f0(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    3c14:	0f 1f 40 00          	nopl   0x0(%rax)
    3c18:	48 89 ee             	mov    %rbp,%rsi
    3c1b:	48 89 df             	mov    %rbx,%rdi
    3c1e:	e8 2d e7 ff ff       	call   2350 <nanosleep@plt>
    3c23:	49 8b 85 c0 00 00 00 	mov    0xc0(%r13),%rax
    3c2a:	48 63 08             	movslq (%rax),%rcx
    3c2d:	85 c9                	test   %ecx,%ecx
    3c2f:	7e 29                	jle    3c5a <external_thread+0x8a>
    3c31:	48 8b 40 08          	mov    0x8(%rax),%rax
    3c35:	48 c1 e1 04          	shl    $0x4,%rcx
    3c39:	48 01 c1             	add    %rax,%rcx
    3c3c:	0f 1f 40 00          	nopl   0x0(%rax)
    3c40:	8b 50 08             	mov    0x8(%rax),%edx
    3c43:	85 d2                	test   %edx,%edx
    3c45:	75 0a                	jne    3c51 <external_thread+0x81>
    3c47:	4c 89 20             	mov    %r12,(%rax)
    3c4a:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    3c51:	48 83 c0 10          	add    $0x10,%rax
    3c55:	48 39 c1             	cmp    %rax,%rcx
    3c58:	75 e6                	jne    3c40 <external_thread+0x70>
    3c5a:	0f ae f0             	mfence
    3c5d:	41 8b 45 64          	mov    0x64(%r13),%eax
    3c61:	83 f8 01             	cmp    $0x1,%eax
    3c64:	74 b2                	je     3c18 <external_thread+0x48>
    3c66:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3c6b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3c74:	75 0d                	jne    3c83 <external_thread+0xb3>
    3c76:	48 83 c4 38          	add    $0x38,%rsp
    3c7a:	31 c0                	xor    %eax,%eax
    3c7c:	5b                   	pop    %rbx
    3c7d:	5d                   	pop    %rbp
    3c7e:	41 5c                	pop    %r12
    3c80:	41 5d                	pop    %r13
    3c82:	c3                   	ret
    3c83:	e8 a8 e6 ff ff       	call   2330 <__stack_chk_fail@plt>
    3c88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000003c90 <timer_thread>:
    3c90:	f3 0f 1e fa          	endbr64
    3c94:	41 57                	push   %r15
    3c96:	48 8d 35 73 33 00 00 	lea    0x3373(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3c9d:	49 89 ff             	mov    %rdi,%r15
    3ca0:	41 56                	push   %r14
    3ca2:	41 55                	push   %r13
    3ca4:	41 54                	push   %r12
    3ca6:	55                   	push   %rbp
    3ca7:	53                   	push   %rbx
    3ca8:	48 83 ec 58          	sub    $0x58,%rsp
    3cac:	8b 17                	mov    (%rdi),%edx
    3cae:	bf 01 00 00 00       	mov    $0x1,%edi
    3cb3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3cbc:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3cc1:	31 c0                	xor    %eax,%eax
    3cc3:	e8 88 e7 ff ff       	call   2450 <__printf_chk@plt>
    3cc8:	66 0f 6f 05 70 3c 00 00 	movdqa 0x3c70(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3cd0:	ba 88 13 00 00       	mov    $0x1388,%edx
    3cd5:	31 c0                	xor    %eax,%eax
    3cd7:	48 8d 35 44 33 00 00 	lea    0x3344(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3cde:	bf 01 00 00 00       	mov    $0x1,%edi
    3ce3:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3ce8:	e8 63 e7 ff ff       	call   2450 <__printf_chk@plt>
    3ced:	45 8b 77 64          	mov    0x64(%r15),%r14d
    3cf1:	45 85 f6             	test   %r14d,%r14d
    3cf4:	0f 84 a2 00 00 00    	je     3d9c <timer_thread+0x10c>
    3cfa:	45 31 ed             	xor    %r13d,%r13d
    3cfd:	45 31 f6             	xor    %r14d,%r14d
    3d00:	49 89 e4             	mov    %rsp,%r12
    3d03:	31 db                	xor    %ebx,%ebx
    3d05:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3d0a:	4c 89 e6             	mov    %r12,%rsi
    3d0d:	48 89 ef             	mov    %rbp,%rdi
    3d10:	41 83 c5 01          	add    $0x1,%r13d
    3d14:	e8 37 e6 ff ff       	call   2350 <nanosleep@plt>
    3d19:	49 63 47 48          	movslq 0x48(%r15),%rax
    3d1d:	45 8d 46 01          	lea    0x1(%r14),%r8d
    3d21:	85 c0                	test   %eax,%eax
    3d23:	7e 4d                	jle    3d72 <timer_thread+0xe2>
    3d25:	49 8b 77 40          	mov    0x40(%r15),%rsi
    3d29:	49 63 fe             	movslq %r14d,%rdi
    3d2c:	48 c1 e7 09          	shl    $0x9,%rdi
    3d30:	4c 8d 0c c6          	lea    (%rsi,%rax,8),%r9
    3d34:	0f 1f 40 00          	nopl   0x0(%rax)
    3d38:	4c 8b 16             	mov    (%rsi),%r10
    3d3b:	44 89 c0             	mov    %r8d,%eax
    3d3e:	48 83 c6 08          	add    $0x8,%rsi
    3d42:	99                   	cltd
    3d43:	41 f7 7a 60          	idivl  0x60(%r10)
    3d47:	49 8b 4a 58          	mov    0x58(%r10),%rcx
    3d4b:	48 63 d2             	movslq %edx,%rdx
    3d4e:	48 c1 e2 09          	shl    $0x9,%rdx
    3d52:	48 8d 04 11          	lea    (%rcx,%rdx,1),%rax
    3d56:	48 01 f9             	add    %rdi,%rcx
    3d59:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    3d63:	c7 81 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rcx)
    3d6d:	4c 39 ce             	cmp    %r9,%rsi
    3d70:	75 c6                	jne    3d38 <timer_thread+0xa8>
    3d72:	0f ae f0             	mfence
    3d75:	49 8b 47 40          	mov    0x40(%r15),%rax
    3d79:	45 89 c6             	mov    %r8d,%r14d
    3d7c:	48 8b 00             	mov    (%rax),%rax
    3d7f:	44 39 40 60          	cmp    %r8d,0x60(%rax)
    3d83:	41 8b 47 64          	mov    0x64(%r15),%eax
    3d87:	44 0f 4e f3          	cmovle %ebx,%r14d
    3d8b:	85 c0                	test   %eax,%eax
    3d8d:	74 0d                	je     3d9c <timer_thread+0x10c>
    3d8f:	41 81 fd 88 13 00 00 	cmp    $0x1388,%r13d
    3d96:	0f 85 6e ff ff ff    	jne    3d0a <timer_thread+0x7a>
    3d9c:	48 8d 3d 95 32 00 00 	lea    0x3295(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3da3:	e8 48 e5 ff ff       	call   22f0 <puts@plt>
    3da8:	49 63 57 4c          	movslq 0x4c(%r15),%rdx
    3dac:	85 d2                	test   %edx,%edx
    3dae:	7e 4e                	jle    3dfe <timer_thread+0x16e>
    3db0:	49 63 47 60          	movslq 0x60(%r15),%rax
    3db4:	85 c0                	test   %eax,%eax
    3db6:	7e 46                	jle    3dfe <timer_thread+0x16e>
    3db8:	48 c1 e0 09          	shl    $0x9,%rax
    3dbc:	4d 8b 47 40          	mov    0x40(%r15),%r8
    3dc0:	48 8d 34 d5 00 00 00 00 	lea    0x0(,%rdx,8),%rsi
    3dc8:	31 ff                	xor    %edi,%edi
    3dca:	48 89 c1             	mov    %rax,%rcx
    3dcd:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3dd1:	48 8b 40 58          	mov    0x58(%rax),%rax
    3dd5:	48 8d 14 01          	lea    (%rcx,%rax,1),%rdx
    3dd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3de0:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    3dea:	48 05 00 02 00 00    	add    $0x200,%rax
    3df0:	48 39 c2             	cmp    %rax,%rdx
    3df3:	75 eb                	jne    3de0 <timer_thread+0x150>
    3df5:	48 83 c7 08          	add    $0x8,%rdi
    3df9:	48 39 fe             	cmp    %rdi,%rsi
    3dfc:	75 cf                	jne    3dcd <timer_thread+0x13d>
    3dfe:	0f ae f0             	mfence
    3e01:	66 0f 6f 05 47 3b 00 00 	movdqa 0x3b47(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3e09:	48 8d 2d 4d 32 00 00 	lea    0x324d(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3e10:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    3e15:	49 63 47 48          	movslq 0x48(%r15),%rax
    3e19:	45 8d 6e 01          	lea    0x1(%r14),%r13d
    3e1d:	85 c0                	test   %eax,%eax
    3e1f:	7e 48                	jle    3e69 <timer_thread+0x1d9>
    3e21:	49 8b 77 40          	mov    0x40(%r15),%rsi
    3e25:	49 63 fe             	movslq %r14d,%rdi
    3e28:	48 c1 e7 09          	shl    $0x9,%rdi
    3e2c:	4c 8d 04 c6          	lea    (%rsi,%rax,8),%r8
    3e30:	48 8b 1e             	mov    (%rsi),%rbx
    3e33:	44 89 e8             	mov    %r13d,%eax
    3e36:	48 83 c6 08          	add    $0x8,%rsi
    3e3a:	99                   	cltd
    3e3b:	f7 7b 60             	idivl  0x60(%rbx)
    3e3e:	48 8b 4b 58          	mov    0x58(%rbx),%rcx
    3e42:	48 63 d2             	movslq %edx,%rdx
    3e45:	48 c1 e2 09          	shl    $0x9,%rdx
    3e49:	48 8d 04 11          	lea    (%rcx,%rdx,1),%rax
    3e4d:	48 01 f9             	add    %rdi,%rcx
    3e50:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    3e5a:	c7 81 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rcx)
    3e64:	49 39 f0             	cmp    %rsi,%r8
    3e67:	75 c7                	jne    3e30 <timer_thread+0x1a0>
    3e69:	0f ae f0             	mfence
    3e6c:	49 8b 47 40          	mov    0x40(%r15),%rax
    3e70:	48 8b 00             	mov    (%rax),%rax
    3e73:	44 39 68 60          	cmp    %r13d,0x60(%rax)
    3e77:	7f 03                	jg     3e7c <timer_thread+0x1ec>
    3e79:	45 31 ed             	xor    %r13d,%r13d
    3e7c:	45 8b 47 50          	mov    0x50(%r15),%r8d
    3e80:	45 85 c0             	test   %r8d,%r8d
    3e83:	0f 8e e9 00 00 00    	jle    3f72 <timer_thread+0x2e2>
    3e89:	31 db                	xor    %ebx,%ebx
    3e8b:	45 31 e4             	xor    %r12d,%r12d
    3e8e:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3e94:	0f 1f 40 00          	nopl   0x0(%rax)
    3e98:	45 31 f6             	xor    %r14d,%r14d
    3e9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3ea0:	45 85 c0             	test   %r8d,%r8d
    3ea3:	0f 8e 8d 00 00 00    	jle    3f36 <timer_thread+0x2a6>
    3ea9:	49 8b 47 40          	mov    0x40(%r15),%rax
    3ead:	4c 89 f1             	mov    %r14,%rcx
    3eb0:	49 63 f8             	movslq %r8d,%rdi
    3eb3:	31 d2                	xor    %edx,%edx
    3eb5:	48 c1 e1 09          	shl    $0x9,%rcx
    3eb9:	48 8b 04 18          	mov    (%rax,%rbx,1),%rax
    3ebd:	48 03 48 58          	add    0x58(%rax),%rcx
    3ec1:	eb 23                	jmp    3ee6 <timer_thread+0x256>
    3ec3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3ec8:	48 8b b1 68 01 00 00 	mov    0x168(%rcx),%rsi
    3ecf:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    3ed4:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    3ed8:	48 85 f6             	test   %rsi,%rsi
    3edb:	7f 24                	jg     3f01 <timer_thread+0x271>
    3edd:	48 83 c2 01          	add    $0x1,%rdx
    3ee1:	48 39 fa             	cmp    %rdi,%rdx
    3ee4:	74 50                	je     3f36 <timer_thread+0x2a6>
    3ee6:	48 8b b1 68 01 00 00 	mov    0x168(%rcx),%rsi
    3eed:	48 89 d0             	mov    %rdx,%rax
    3ef0:	48 c1 e0 05          	shl    $0x5,%rax
    3ef4:	48 8b 34 06          	mov    (%rsi,%rax,1),%rsi
    3ef8:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    3efc:	48 85 f6             	test   %rsi,%rsi
    3eff:	7e c7                	jle    3ec8 <timer_thread+0x238>
    3f01:	48 8b b1 68 01 00 00 	mov    0x168(%rcx),%rsi
    3f08:	bf 01 00 00 00       	mov    $0x1,%edi
    3f0d:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    3f12:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3f16:	48 8b 89 68 01 00 00 	mov    0x168(%rcx),%rcx
    3f1d:	48 89 ee             	mov    %rbp,%rsi
    3f20:	48 8b 04 01          	mov    (%rcx,%rax,1),%rax
    3f24:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3f28:	31 c0                	xor    %eax,%eax
    3f2a:	e8 21 e5 ff ff       	call   2450 <__printf_chk@plt>
    3f2f:	45 8b 47 50          	mov    0x50(%r15),%r8d
    3f33:	45 31 c9             	xor    %r9d,%r9d
    3f36:	49 83 c6 01          	add    $0x1,%r14
    3f3a:	45 39 f0             	cmp    %r14d,%r8d
    3f3d:	0f 8f 5d ff ff ff    	jg     3ea0 <timer_thread+0x210>
    3f43:	41 83 c4 01          	add    $0x1,%r12d
    3f47:	45 39 c4             	cmp    %r8d,%r12d
    3f4a:	7d 09                	jge    3f55 <timer_thread+0x2c5>
    3f4c:	48 83 c3 08          	add    $0x8,%rbx
    3f50:	e9 43 ff ff ff       	jmp    3e98 <timer_thread+0x208>
    3f55:	41 83 f9 01          	cmp    $0x1,%r9d
    3f59:	74 17                	je     3f72 <timer_thread+0x2e2>
    3f5b:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3f60:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3f65:	45 89 ee             	mov    %r13d,%r14d
    3f68:	e8 e3 e3 ff ff       	call   2350 <nanosleep@plt>
    3f6d:	e9 a3 fe ff ff       	jmp    3e15 <timer_thread+0x185>
    3f72:	48 8d 3d db 30 00 00 	lea    0x30db(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3f79:	4c 8d 25 00 31 00 00 	lea    0x3100(%rip),%r12        # 7080 <_IO_stdin_used+0x80>
    3f80:	e8 6b e3 ff ff       	call   22f0 <puts@plt>
    3f85:	41 8b 47 64          	mov    0x64(%r15),%eax
    3f89:	48 8d 2d de 30 00 00 	lea    0x30de(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3f90:	85 c0                	test   %eax,%eax
    3f92:	0f 84 a5 00 00 00    	je     403d <timer_thread+0x3ad>
    3f98:	41 8b 57 4c          	mov    0x4c(%r15),%edx
    3f9c:	31 db                	xor    %ebx,%ebx
    3f9e:	85 d2                	test   %edx,%edx
    3fa0:	7e 21                	jle    3fc3 <timer_thread+0x333>
    3fa2:	49 8b 4f 40          	mov    0x40(%r15),%rcx
    3fa6:	48 8b 04 d9          	mov    (%rcx,%rbx,8),%rax
    3faa:	83 78 08 02          	cmpl   $0x2,0x8(%rax)
    3fae:	c7 40 64 00 00 00 00 	movl   $0x0,0x64(%rax)
    3fb5:	0f 84 af 00 00 00    	je     406a <timer_thread+0x3da>
    3fbb:	48 83 c3 01          	add    $0x1,%rbx
    3fbf:	39 da                	cmp    %ebx,%edx
    3fc1:	7f e3                	jg     3fa6 <timer_thread+0x316>
    3fc3:	49 63 57 48          	movslq 0x48(%r15),%rdx
    3fc7:	85 d2                	test   %edx,%edx
    3fc9:	7e 53                	jle    401e <timer_thread+0x38e>
    3fcb:	49 63 47 60          	movslq 0x60(%r15),%rax
    3fcf:	85 c0                	test   %eax,%eax
    3fd1:	7e 4b                	jle    401e <timer_thread+0x38e>
    3fd3:	48 c1 e0 09          	shl    $0x9,%rax
    3fd7:	4d 8b 47 40          	mov    0x40(%r15),%r8
    3fdb:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3fe3:	31 c9                	xor    %ecx,%ecx
    3fe5:	48 89 c6             	mov    %rax,%rsi
    3fe8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3ff0:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3ff4:	48 8b 40 58          	mov    0x58(%rax),%rax
    3ff8:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3ffc:	0f 1f 40 00          	nopl   0x0(%rax)
    4000:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
    400a:	48 05 00 02 00 00    	add    $0x200,%rax
    4010:	48 39 d0             	cmp    %rdx,%rax
    4013:	75 eb                	jne    4000 <timer_thread+0x370>
    4015:	48 83 c1 08          	add    $0x8,%rcx
    4019:	48 39 f9             	cmp    %rdi,%rcx
    401c:	75 d2                	jne    3ff0 <timer_thread+0x360>
    401e:	0f ae f0             	mfence
    4021:	4c 89 e7             	mov    %r12,%rdi
    4024:	e8 c7 e2 ff ff       	call   22f0 <puts@plt>
    4029:	41 c7 47 64 00 00 00 00 	movl   $0x0,0x64(%r15)
    4031:	41 8b 47 64          	mov    0x64(%r15),%eax
    4035:	85 c0                	test   %eax,%eax
    4037:	0f 85 5b ff ff ff    	jne    3f98 <timer_thread+0x308>
    403d:	48 8d 3d 43 30 00 00 	lea    0x3043(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    4044:	e8 a7 e2 ff ff       	call   22f0 <puts@plt>
    4049:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    404e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4057:	75 46                	jne    409f <timer_thread+0x40f>
    4059:	48 83 c4 58          	add    $0x58,%rsp
    405d:	31 c0                	xor    %eax,%eax
    405f:	5b                   	pop    %rbx
    4060:	5d                   	pop    %rbp
    4061:	41 5c                	pop    %r12
    4063:	41 5d                	pop    %r13
    4065:	41 5e                	pop    %r14
    4067:	41 5f                	pop    %r15
    4069:	c3                   	ret
    406a:	48 89 ef             	mov    %rbp,%rdi
    406d:	e8 7e e2 ff ff       	call   22f0 <puts@plt>
    4072:	49 8b 47 40          	mov    0x40(%r15),%rax
    4076:	be 01 00 00 00       	mov    $0x1,%esi
    407b:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    407f:	48 83 c3 01          	add    $0x1,%rbx
    4083:	8b b8 d0 00 00 00    	mov    0xd0(%rax),%edi
    4089:	e8 72 e3 ff ff       	call   2400 <eventfd_write@plt>
    408e:	41 8b 57 4c          	mov    0x4c(%r15),%edx
    4092:	39 da                	cmp    %ebx,%edx
    4094:	0f 8f 08 ff ff ff    	jg     3fa2 <timer_thread+0x312>
    409a:	e9 24 ff ff ff       	jmp    3fc3 <timer_thread+0x333>
    409f:	e8 8c e2 ff ff       	call   2330 <__stack_chk_fail@plt>
    40a4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    40af:	90                   	nop

00000000000040b0 <fatal_error>:
    40b0:	f3 0f 1e fa          	endbr64
    40b4:	50                   	push   %rax
    40b5:	58                   	pop    %rax
    40b6:	48 83 ec 08          	sub    $0x8,%rsp
    40ba:	e8 d1 e3 ff ff       	call   2490 <perror@plt>
    40bf:	bf 01 00 00 00       	mov    $0x1,%edi
    40c4:	e8 d7 e3 ff ff       	call   24a0 <exit@plt>
    40c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000040d0 <strtolower>:
    40d0:	f3 0f 1e fa          	endbr64
    40d4:	55                   	push   %rbp
    40d5:	53                   	push   %rbx
    40d6:	48 83 ec 08          	sub    $0x8,%rsp
    40da:	48 0f be 1f          	movsbq (%rdi),%rbx
    40de:	84 db                	test   %bl,%bl
    40e0:	74 24                	je     4106 <strtolower+0x36>
    40e2:	48 89 fd             	mov    %rdi,%rbp
    40e5:	e8 26 e4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    40ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    40f0:	48 8b 10             	mov    (%rax),%rdx
    40f3:	48 83 c5 01          	add    $0x1,%rbp
    40f7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    40fa:	88 55 ff             	mov    %dl,-0x1(%rbp)
    40fd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4102:	84 db                	test   %bl,%bl
    4104:	75 ea                	jne    40f0 <strtolower+0x20>
    4106:	48 83 c4 08          	add    $0x8,%rsp
    410a:	5b                   	pop    %rbx
    410b:	5d                   	pop    %rbp
    410c:	c3                   	ret
    410d:	0f 1f 00             	nopl   (%rax)

0000000000004110 <zh_malloc>:
    4110:	f3 0f 1e fa          	endbr64
    4114:	48 83 ec 08          	sub    $0x8,%rsp
    4118:	e8 f3 e2 ff ff       	call   2410 <malloc@plt>
    411d:	48 85 c0             	test   %rax,%rax
    4120:	74 05                	je     4127 <zh_malloc+0x17>
    4122:	48 83 c4 08          	add    $0x8,%rsp
    4126:	c3                   	ret
    4127:	48 8b 0d f2 5e 00 00 	mov    0x5ef2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    412e:	ba 28 00 00 00       	mov    $0x28,%edx
    4133:	be 01 00 00 00       	mov    $0x1,%esi
    4138:	48 8d 3d c1 32 00 00 	lea    0x32c1(%rip),%rdi        # 7400 <_IO_stdin_used+0x400>
    413f:	e8 7c e3 ff ff       	call   24c0 <fwrite@plt>
    4144:	bf 01 00 00 00       	mov    $0x1,%edi
    4149:	e8 52 e3 ff ff       	call   24a0 <exit@plt>
    414e:	66 90                	xchg   %ax,%ax

0000000000004150 <get_filename_ext>:
    4150:	f3 0f 1e fa          	endbr64
    4154:	53                   	push   %rbx
    4155:	be 2e 00 00 00       	mov    $0x2e,%esi
    415a:	48 89 fb             	mov    %rdi,%rbx
    415d:	e8 fe e1 ff ff       	call   2360 <strrchr@plt>
    4162:	48 85 c0             	test   %rax,%rax
    4165:	74 11                	je     4178 <get_filename_ext+0x28>
    4167:	48 39 c3             	cmp    %rax,%rbx
    416a:	74 0c                	je     4178 <get_filename_ext+0x28>
    416c:	48 83 c0 01          	add    $0x1,%rax
    4170:	5b                   	pop    %rbx
    4171:	c3                   	ret
    4172:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4178:	48 8d 05 50 2f 00 00 	lea    0x2f50(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
    417f:	5b                   	pop    %rbx
    4180:	c3                   	ret
    4181:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    418c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004190 <send_headers>:
    4190:	f3 0f 1e fa          	endbr64
    4194:	41 55                	push   %r13
    4196:	49 89 f5             	mov    %rsi,%r13
    4199:	48 89 fe             	mov    %rdi,%rsi
    419c:	41 54                	push   %r12
    419e:	55                   	push   %rbp
    419f:	48 89 d5             	mov    %rdx,%rbp
    41a2:	ba 00 04 00 00       	mov    $0x400,%edx
    41a7:	53                   	push   %rbx
    41a8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    41af:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    41b8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    41c0:	31 c0                	xor    %eax,%eax
    41c2:	49 89 e4             	mov    %rsp,%r12
    41c5:	4c 89 e7             	mov    %r12,%rdi
    41c8:	e8 63 e2 ff ff       	call   2430 <__strcpy_chk@plt>
    41cd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    41d2:	84 db                	test   %bl,%bl
    41d4:	74 24                	je     41fa <send_headers+0x6a>
    41d6:	e8 35 e3 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    41db:	48 8b 08             	mov    (%rax),%rcx
    41de:	4c 89 e0             	mov    %r12,%rax
    41e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    41e8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    41eb:	48 83 c0 01          	add    $0x1,%rax
    41ef:	88 50 ff             	mov    %dl,-0x1(%rax)
    41f2:	48 0f be 18          	movsbq (%rax),%rbx
    41f6:	84 db                	test   %bl,%bl
    41f8:	75 ee                	jne    41e8 <send_headers+0x58>
    41fa:	bf 11 00 00 00       	mov    $0x11,%edi
    41ff:	e8 0c e2 ff ff       	call   2410 <malloc@plt>
    4204:	48 85 c0             	test   %rax,%rax
    4207:	0f 84 7e 04 00 00    	je     468b <send_headers+0x4fb>
    420d:	66 0f 6f 05 4b 37 00 00 	movdqa 0x374b(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    4215:	48 89 45 00          	mov    %rax,0x0(%rbp)
    4219:	bf 17 00 00 00       	mov    $0x17,%edi
    421e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4226:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    422a:	0f 11 00             	movups %xmm0,(%rax)
    422d:	e8 de e1 ff ff       	call   2410 <malloc@plt>
    4232:	48 85 c0             	test   %rax,%rax
    4235:	0f 84 50 04 00 00    	je     468b <send_headers+0x4fb>
    423b:	66 0f 6f 05 2d 37 00 00 	movdqa 0x372d(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    4243:	48 89 45 10          	mov    %rax,0x10(%rbp)
    4247:	4c 89 e7             	mov    %r12,%rdi
    424a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    4254:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    425c:	0f 11 00             	movups %xmm0,(%rax)
    425f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    4263:	be 2e 00 00 00       	mov    $0x2e,%esi
    4268:	e8 f3 e0 ff ff       	call   2360 <strrchr@plt>
    426d:	48 85 c0             	test   %rax,%rax
    4270:	0f 84 ea 02 00 00    	je     4560 <send_headers+0x3d0>
    4276:	4c 39 e0             	cmp    %r12,%rax
    4279:	0f 84 e1 02 00 00    	je     4560 <send_headers+0x3d0>
    427f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    4283:	48 8d 3d 13 2e 00 00 	lea    0x2e13(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    428a:	48 89 de             	mov    %rbx,%rsi
    428d:	e8 1e e1 ff ff       	call   23b0 <strcmp@plt>
    4292:	85 c0                	test   %eax,%eax
    4294:	75 20                	jne    42b6 <send_headers+0x126>
    4296:	66 0f 6f 05 e2 36 00 00 	movdqa 0x36e2(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    429e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    42a6:	66 0f 6f 05 e2 36 00 00 	movdqa 0x36e2(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    42ae:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    42b6:	48 89 de             	mov    %rbx,%rsi
    42b9:	48 8d 3d e1 2d 00 00 	lea    0x2de1(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    42c0:	e8 eb e0 ff ff       	call   23b0 <strcmp@plt>
    42c5:	85 c0                	test   %eax,%eax
    42c7:	75 20                	jne    42e9 <send_headers+0x159>
    42c9:	66 0f 6f 05 af 36 00 00 	movdqa 0x36af(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    42d1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    42d9:	66 0f 6f 05 af 36 00 00 	movdqa 0x36af(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    42e1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    42e9:	48 89 de             	mov    %rbx,%rsi
    42ec:	48 8d 3d b3 2d 00 00 	lea    0x2db3(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    42f3:	e8 b8 e0 ff ff       	call   23b0 <strcmp@plt>
    42f8:	85 c0                	test   %eax,%eax
    42fa:	0f 84 10 02 00 00    	je     4510 <send_headers+0x380>
    4300:	48 89 de             	mov    %rbx,%rsi
    4303:	48 8d 3d a0 2d 00 00 	lea    0x2da0(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    430a:	e8 a1 e0 ff ff       	call   23b0 <strcmp@plt>
    430f:	85 c0                	test   %eax,%eax
    4311:	0f 84 a9 02 00 00    	je     45c0 <send_headers+0x430>
    4317:	48 89 de             	mov    %rbx,%rsi
    431a:	48 8d 3d 8d 2d 00 00 	lea    0x2d8d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4321:	e8 8a e0 ff ff       	call   23b0 <strcmp@plt>
    4326:	85 c0                	test   %eax,%eax
    4328:	0f 84 6a 02 00 00    	je     4598 <send_headers+0x408>
    432e:	48 89 de             	mov    %rbx,%rsi
    4331:	48 8d 3d b9 2d 00 00 	lea    0x2db9(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4338:	e8 73 e0 ff ff       	call   23b0 <strcmp@plt>
    433d:	85 c0                	test   %eax,%eax
    433f:	0f 84 2b 02 00 00    	je     4570 <send_headers+0x3e0>
    4345:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4348:	0f 84 52 01 00 00    	je     44a0 <send_headers+0x310>
    434e:	48 89 de             	mov    %rbx,%rsi
    4351:	48 8d 3d 5a 2d 00 00 	lea    0x2d5a(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    4358:	e8 53 e0 ff ff       	call   23b0 <strcmp@plt>
    435d:	85 c0                	test   %eax,%eax
    435f:	0f 84 ab 02 00 00    	je     4610 <send_headers+0x480>
    4365:	48 89 de             	mov    %rbx,%rsi
    4368:	48 8d 3d 47 2d 00 00 	lea    0x2d47(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    436f:	e8 3c e0 ff ff       	call   23b0 <strcmp@plt>
    4374:	85 c0                	test   %eax,%eax
    4376:	0f 84 6c 02 00 00    	je     45e8 <send_headers+0x458>
    437c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4384:	4c 89 e7             	mov    %r12,%rdi
    4387:	e8 94 df ff ff       	call   2320 <strlen@plt>
    438c:	48 89 c7             	mov    %rax,%rdi
    438f:	48 89 c3             	mov    %rax,%rbx
    4392:	e8 79 e0 ff ff       	call   2410 <malloc@plt>
    4397:	48 85 c0             	test   %rax,%rax
    439a:	0f 84 eb 02 00 00    	je     468b <send_headers+0x4fb>
    43a0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    43a4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    43a8:	83 fb 08             	cmp    $0x8,%ebx
    43ab:	0f 83 3f 01 00 00    	jae    44f0 <send_headers+0x360>
    43b1:	f6 c3 04             	test   $0x4,%bl
    43b4:	0f 85 7b 02 00 00    	jne    4635 <send_headers+0x4a5>
    43ba:	85 db                	test   %ebx,%ebx
    43bc:	74 13                	je     43d1 <send_headers+0x241>
    43be:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    43c6:	88 10                	mov    %dl,(%rax)
    43c8:	f6 c3 02             	test   $0x2,%bl
    43cb:	0f 85 96 02 00 00    	jne    4667 <send_headers+0x4d7>
    43d1:	4d 89 e8             	mov    %r13,%r8
    43d4:	48 8d 0d df 2c 00 00 	lea    0x2cdf(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    43db:	4c 89 e7             	mov    %r12,%rdi
    43de:	31 c0                	xor    %eax,%eax
    43e0:	ba 00 04 00 00       	mov    $0x400,%edx
    43e5:	be 01 00 00 00       	mov    $0x1,%esi
    43ea:	e8 31 e1 ff ff       	call   2520 <__sprintf_chk@plt>
    43ef:	4c 89 e7             	mov    %r12,%rdi
    43f2:	e8 29 df ff ff       	call   2320 <strlen@plt>
    43f7:	48 89 c7             	mov    %rax,%rdi
    43fa:	48 89 c3             	mov    %rax,%rbx
    43fd:	e8 0e e0 ff ff       	call   2410 <malloc@plt>
    4402:	48 85 c0             	test   %rax,%rax
    4405:	0f 84 80 02 00 00    	je     468b <send_headers+0x4fb>
    440b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    440f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4413:	83 fb 08             	cmp    $0x8,%ebx
    4416:	0f 83 1c 01 00 00    	jae    4538 <send_headers+0x3a8>
    441c:	f6 c3 04             	test   $0x4,%bl
    441f:	0f 85 29 02 00 00    	jne    464e <send_headers+0x4be>
    4425:	85 db                	test   %ebx,%ebx
    4427:	74 13                	je     443c <send_headers+0x2ac>
    4429:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4431:	88 10                	mov    %dl,(%rax)
    4433:	f6 c3 02             	test   $0x2,%bl
    4436:	0f 85 3d 02 00 00    	jne    4679 <send_headers+0x4e9>
    443c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    4441:	bf 02 00 00 00       	mov    $0x2,%edi
    4446:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    444e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4456:	e8 b5 df ff ff       	call   2410 <malloc@plt>
    445b:	48 85 c0             	test   %rax,%rax
    445e:	0f 84 27 02 00 00    	je     468b <send_headers+0x4fb>
    4464:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    446c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    4470:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4478:	66 89 10             	mov    %dx,(%rax)
    447b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4483:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    448c:	0f 85 20 02 00 00    	jne    46b2 <send_headers+0x522>
    4492:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4499:	5b                   	pop    %rbx
    449a:	5d                   	pop    %rbp
    449b:	41 5c                	pop    %r12
    449d:	41 5d                	pop    %r13
    449f:	c3                   	ret
    44a0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    44a4:	0f 85 a4 fe ff ff    	jne    434e <send_headers+0x1be>
    44aa:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    44ae:	0f 85 9a fe ff ff    	jne    434e <send_headers+0x1be>
    44b4:	66 0f 6f 05 24 35 00 00 	movdqa 0x3524(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    44bc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    44c6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44ce:	66 0f 6f 05 1a 35 00 00 	movdqa 0x351a(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    44d6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    44de:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    44e6:	e9 63 fe ff ff       	jmp    434e <send_headers+0x1be>
    44eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    44f0:	89 da                	mov    %ebx,%edx
    44f2:	48 89 c7             	mov    %rax,%rdi
    44f5:	4c 89 e6             	mov    %r12,%rsi
    44f8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    44fd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4502:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4505:	c1 e9 03             	shr    $0x3,%ecx
    4508:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    450b:	e9 c1 fe ff ff       	jmp    43d1 <send_headers+0x241>
    4510:	66 0f 6f 05 68 34 00 00 	movdqa 0x3468(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4518:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4520:	66 0f 6f 05 78 34 00 00 	movdqa 0x3478(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4528:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4530:	e9 cb fd ff ff       	jmp    4300 <send_headers+0x170>
    4535:	0f 1f 00             	nopl   (%rax)
    4538:	89 da                	mov    %ebx,%edx
    453a:	48 89 c7             	mov    %rax,%rdi
    453d:	4c 89 e6             	mov    %r12,%rsi
    4540:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4545:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    454a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    454d:	c1 e9 03             	shr    $0x3,%ecx
    4550:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4553:	e9 e4 fe ff ff       	jmp    443c <send_headers+0x2ac>
    4558:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4560:	48 8d 1d 68 2b 00 00 	lea    0x2b68(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4567:	e9 94 fd ff ff       	jmp    4300 <send_headers+0x170>
    456c:	0f 1f 40 00          	nopl   0x0(%rax)
    4570:	66 0f 6f 05 48 34 00 00 	movdqa 0x3448(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4578:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4580:	66 0f 6f 05 48 34 00 00 	movdqa 0x3448(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4588:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4590:	e9 b0 fd ff ff       	jmp    4345 <send_headers+0x1b5>
    4595:	0f 1f 00             	nopl   (%rax)
    4598:	66 0f 6f 05 20 34 00 00 	movdqa 0x3420(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    45a0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    45a8:	66 0f 6f 05 20 34 00 00 	movdqa 0x3420(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    45b0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    45b8:	e9 71 fd ff ff       	jmp    432e <send_headers+0x19e>
    45bd:	0f 1f 00             	nopl   (%rax)
    45c0:	66 0f 6f 05 b8 33 00 00 	movdqa 0x33b8(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    45c8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    45d0:	66 0f 6f 05 d8 33 00 00 	movdqa 0x33d8(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    45d8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    45e0:	e9 32 fd ff ff       	jmp    4317 <send_headers+0x187>
    45e5:	0f 1f 00             	nopl   (%rax)
    45e8:	66 0f 6f 05 d0 33 00 00 	movdqa 0x33d0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    45f0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    45f8:	66 0f 6f 05 10 34 00 00 	movdqa 0x3410(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4600:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4608:	e9 6f fd ff ff       	jmp    437c <send_headers+0x1ec>
    460d:	0f 1f 00             	nopl   (%rax)
    4610:	66 0f 6f 05 a8 33 00 00 	movdqa 0x33a8(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4618:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4620:	66 0f 6f 05 d8 33 00 00 	movdqa 0x33d8(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4628:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4630:	e9 30 fd ff ff       	jmp    4365 <send_headers+0x1d5>
    4635:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    463c:	89 db                	mov    %ebx,%ebx
    463e:	89 10                	mov    %edx,(%rax)
    4640:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4645:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4649:	e9 83 fd ff ff       	jmp    43d1 <send_headers+0x241>
    464e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4655:	89 db                	mov    %ebx,%ebx
    4657:	89 10                	mov    %edx,(%rax)
    4659:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    465e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4662:	e9 d5 fd ff ff       	jmp    443c <send_headers+0x2ac>
    4667:	89 db                	mov    %ebx,%ebx
    4669:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    466f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4674:	e9 58 fd ff ff       	jmp    43d1 <send_headers+0x241>
    4679:	89 db                	mov    %ebx,%ebx
    467b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4681:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4686:	e9 b1 fd ff ff       	jmp    443c <send_headers+0x2ac>
    468b:	48 8b 0d 8e 59 00 00 	mov    0x598e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4692:	ba 28 00 00 00       	mov    $0x28,%edx
    4697:	be 01 00 00 00       	mov    $0x1,%esi
    469c:	48 8d 3d 5d 2d 00 00 	lea    0x2d5d(%rip),%rdi        # 7400 <_IO_stdin_used+0x400>
    46a3:	e8 18 de ff ff       	call   24c0 <fwrite@plt>
    46a8:	bf 01 00 00 00       	mov    $0x1,%edi
    46ad:	e8 ee dd ff ff       	call   24a0 <exit@plt>
    46b2:	e8 79 dc ff ff       	call   2330 <__stack_chk_fail@plt>
    46b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000046c0 <copy_file_contents>:
    46c0:	f3 0f 1e fa          	endbr64
    46c4:	41 55                	push   %r13
    46c6:	49 89 d5             	mov    %rdx,%r13
    46c9:	41 54                	push   %r12
    46cb:	49 89 fc             	mov    %rdi,%r12
    46ce:	48 89 f7             	mov    %rsi,%rdi
    46d1:	55                   	push   %rbp
    46d2:	53                   	push   %rbx
    46d3:	48 89 f3             	mov    %rsi,%rbx
    46d6:	48 83 ec 08          	sub    $0x8,%rsp
    46da:	e8 31 dd ff ff       	call   2410 <malloc@plt>
    46df:	48 85 c0             	test   %rax,%rax
    46e2:	74 77                	je     475b <copy_file_contents+0x9b>
    46e4:	4c 89 e7             	mov    %r12,%rdi
    46e7:	48 89 c5             	mov    %rax,%rbp
    46ea:	31 f6                	xor    %esi,%esi
    46ec:	31 c0                	xor    %eax,%eax
    46ee:	e8 8d dd ff ff       	call   2480 <open@plt>
    46f3:	41 89 c4             	mov    %eax,%r12d
    46f6:	85 c0                	test   %eax,%eax
    46f8:	78 55                	js     474f <copy_file_contents+0x8f>
    46fa:	48 89 da             	mov    %rbx,%rdx
    46fd:	48 89 ee             	mov    %rbp,%rsi
    4700:	89 c7                	mov    %eax,%edi
    4702:	e8 89 dc ff ff       	call   2390 <read@plt>
    4707:	48 98                	cltq
    4709:	48 39 d8             	cmp    %rbx,%rax
    470c:	7c 22                	jl     4730 <copy_file_contents+0x70>
    470e:	44 89 e7             	mov    %r12d,%edi
    4711:	e8 5a dc ff ff       	call   2370 <close@plt>
    4716:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    471a:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    471e:	48 83 c4 08          	add    $0x8,%rsp
    4722:	5b                   	pop    %rbx
    4723:	5d                   	pop    %rbp
    4724:	41 5c                	pop    %r12
    4726:	41 5d                	pop    %r13
    4728:	c3                   	ret
    4729:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4730:	48 8b 0d e9 58 00 00 	mov    0x58e9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4737:	ba 1a 00 00 00       	mov    $0x1a,%edx
    473c:	be 01 00 00 00       	mov    $0x1,%esi
    4741:	48 8d 3d 88 29 00 00 	lea    0x2988(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    4748:	e8 73 dd ff ff       	call   24c0 <fwrite@plt>
    474d:	eb bf                	jmp    470e <copy_file_contents+0x4e>
    474f:	48 8d 3d a9 2a 00 00 	lea    0x2aa9(%rip),%rdi        # 71ff <_IO_stdin_used+0x1ff>
    4756:	e8 55 f9 ff ff       	call   40b0 <fatal_error>
    475b:	48 8b 0d be 58 00 00 	mov    0x58be(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4762:	ba 28 00 00 00       	mov    $0x28,%edx
    4767:	be 01 00 00 00       	mov    $0x1,%esi
    476c:	48 8d 3d 8d 2c 00 00 	lea    0x2c8d(%rip),%rdi        # 7400 <_IO_stdin_used+0x400>
    4773:	e8 48 dd ff ff       	call   24c0 <fwrite@plt>
    4778:	bf 01 00 00 00       	mov    $0x1,%edi
    477d:	e8 1e dd ff ff       	call   24a0 <exit@plt>
    4782:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    478d:	0f 1f 00             	nopl   (%rax)

0000000000004790 <add_write_request>:
    4790:	f3 0f 1e fa          	endbr64
    4794:	8b 46 44             	mov    0x44(%rsi),%eax
    4797:	48 89 fa             	mov    %rdi,%rdx
    479a:	48 89 f7             	mov    %rsi,%rdi
    479d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    47a3:	8d 70 01             	lea    0x1(%rax),%esi
    47a6:	48 8b 07             	mov    (%rdi),%rax
    47a9:	44 8b 00             	mov    (%rax),%r8d
    47ac:	f6 c1 02             	test   $0x2,%cl
    47af:	74 00                	je     47b1 <add_write_request+0x21>
    47b1:	89 f0                	mov    %esi,%eax
    47b3:	44 29 c0             	sub    %r8d,%eax
    47b6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    47b9:	0f 82 81 dd ff ff    	jb     2540 <add_write_request.cold>
    47bf:	c1 e9 0a             	shr    $0xa,%ecx
    47c2:	48 83 ec 08          	sub    $0x8,%rsp
    47c6:	8b 47 44             	mov    0x44(%rdi),%eax
    47c9:	23 47 58             	and    0x58(%rdi),%eax
    47cc:	83 e1 01             	and    $0x1,%ecx
    47cf:	89 77 44             	mov    %esi,0x44(%rdi)
    47d2:	8b 72 08             	mov    0x8(%rdx),%esi
    47d5:	66 0f ef c0          	pxor   %xmm0,%xmm0
    47d9:	d3 e0                	shl    %cl,%eax
    47db:	8b 4a 04             	mov    0x4(%rdx),%ecx
    47de:	48 c1 e0 06          	shl    $0x6,%rax
    47e2:	48 03 47 38          	add    0x38(%rdi),%rax
    47e6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    47ec:	89 70 04             	mov    %esi,0x4(%rax)
    47ef:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    47f3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    47f9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4801:	48 89 70 10          	mov    %rsi,0x10(%rax)
    4805:	89 48 18             	mov    %ecx,0x18(%rax)
    4808:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    480f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4817:	48 89 50 20          	mov    %rdx,0x20(%rax)
    481b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    481f:	e8 1c db ff ff       	call   2340 <io_uring_submit@plt>
    4824:	31 c0                	xor    %eax,%eax
    4826:	48 83 c4 08          	add    $0x8,%rsp
    482a:	c3                   	ret
    482b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004830 <add_read_request>:
    4830:	f3 0f 1e fa          	endbr64
    4834:	41 55                	push   %r13
    4836:	41 89 fd             	mov    %edi,%r13d
    4839:	41 54                	push   %r12
    483b:	55                   	push   %rbp
    483c:	53                   	push   %rbx
    483d:	48 89 f3             	mov    %rsi,%rbx
    4840:	48 83 ec 08          	sub    $0x8,%rsp
    4844:	8b 46 44             	mov    0x44(%rsi),%eax
    4847:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    484d:	48 8b 16             	mov    (%rsi),%rdx
    4850:	83 c0 01             	add    $0x1,%eax
    4853:	8b 32                	mov    (%rdx),%esi
    4855:	f6 c1 02             	test   $0x2,%cl
    4858:	74 00                	je     485a <add_read_request+0x2a>
    485a:	89 c2                	mov    %eax,%edx
    485c:	29 f2                	sub    %esi,%edx
    485e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4861:	0f 82 e9 dc ff ff    	jb     2550 <add_read_request.cold>
    4867:	8b 6b 44             	mov    0x44(%rbx),%ebp
    486a:	c1 e9 0a             	shr    $0xa,%ecx
    486d:	89 43 44             	mov    %eax,0x44(%rbx)
    4870:	bf 20 00 00 00       	mov    $0x20,%edi
    4875:	83 e1 01             	and    $0x1,%ecx
    4878:	23 6b 58             	and    0x58(%rbx),%ebp
    487b:	d3 e5                	shl    %cl,%ebp
    487d:	48 c1 e5 06          	shl    $0x6,%rbp
    4881:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4885:	e8 86 db ff ff       	call   2410 <malloc@plt>
    488a:	be 01 00 00 00       	mov    $0x1,%esi
    488f:	bf 00 20 00 00       	mov    $0x2000,%edi
    4894:	49 89 c4             	mov    %rax,%r12
    4897:	e8 04 db ff ff       	call   23a0 <calloc@plt>
    489c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    48a1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    48a5:	48 89 df             	mov    %rbx,%rdi
    48a8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    48ad:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    48b2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    48bb:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    48c3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    48c7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    48cb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    48d2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    48da:	48 89 45 10          	mov    %rax,0x10(%rbp)
    48de:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    48e6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    48ee:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    48f2:	e8 49 da ff ff       	call   2340 <io_uring_submit@plt>
    48f7:	48 83 c4 08          	add    $0x8,%rsp
    48fb:	31 c0                	xor    %eax,%eax
    48fd:	5b                   	pop    %rbx
    48fe:	5d                   	pop    %rbp
    48ff:	41 5c                	pop    %r12
    4901:	41 5d                	pop    %r13
    4903:	c3                   	ret
    4904:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    490f:	90                   	nop

0000000000004910 <_send_static_string_content>:
    4910:	f3 0f 1e fa          	endbr64
    4914:	41 56                	push   %r14
    4916:	41 89 f6             	mov    %esi,%r14d
    4919:	41 55                	push   %r13
    491b:	49 89 fd             	mov    %rdi,%r13
    491e:	bf 20 00 00 00       	mov    $0x20,%edi
    4923:	41 54                	push   %r12
    4925:	55                   	push   %rbp
    4926:	48 89 d5             	mov    %rdx,%rbp
    4929:	53                   	push   %rbx
    492a:	e8 e1 da ff ff       	call   2410 <malloc@plt>
    492f:	48 85 c0             	test   %rax,%rax
    4932:	0f 84 dd 00 00 00    	je     4a15 <_send_static_string_content+0x105>
    4938:	48 89 c3             	mov    %rax,%rbx
    493b:	4c 89 ef             	mov    %r13,%rdi
    493e:	e8 dd d9 ff ff       	call   2320 <strlen@plt>
    4943:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    494a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    494e:	48 89 c7             	mov    %rax,%rdi
    4951:	49 89 c4             	mov    %rax,%r12
    4954:	e8 b7 da ff ff       	call   2410 <malloc@plt>
    4959:	48 89 c7             	mov    %rax,%rdi
    495c:	48 85 c0             	test   %rax,%rax
    495f:	0f 84 b0 00 00 00    	je     4a15 <_send_static_string_content+0x105>
    4965:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4969:	4c 89 e2             	mov    %r12,%rdx
    496c:	4c 89 ee             	mov    %r13,%rsi
    496f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4973:	e8 68 da ff ff       	call   23e0 <memcpy@plt>
    4978:	8b 45 44             	mov    0x44(%rbp),%eax
    497b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    4981:	8d 50 01             	lea    0x1(%rax),%edx
    4984:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4988:	8b 30                	mov    (%rax),%esi
    498a:	f6 c1 02             	test   $0x2,%cl
    498d:	0f 85 7d 00 00 00    	jne    4a10 <_send_static_string_content+0x100>
    4993:	89 d0                	mov    %edx,%eax
    4995:	29 f0                	sub    %esi,%eax
    4997:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    499a:	0f 82 ba db ff ff    	jb     255a <_send_static_string_content.cold>
    49a0:	c1 e9 0a             	shr    $0xa,%ecx
    49a3:	8b 45 44             	mov    0x44(%rbp),%eax
    49a6:	23 45 58             	and    0x58(%rbp),%eax
    49a9:	89 55 44             	mov    %edx,0x44(%rbp)
    49ac:	83 e1 01             	and    $0x1,%ecx
    49af:	8b 53 04             	mov    0x4(%rbx),%edx
    49b2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    49b8:	66 0f ef c0          	pxor   %xmm0,%xmm0
    49bc:	d3 e0                	shl    %cl,%eax
    49be:	8b 4b 08             	mov    0x8(%rbx),%ecx
    49c1:	48 89 ef             	mov    %rbp,%rdi
    49c4:	48 c1 e0 06          	shl    $0x6,%rax
    49c8:	48 03 45 38          	add    0x38(%rbp),%rax
    49cc:	89 48 04             	mov    %ecx,0x4(%rax)
    49cf:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    49d3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    49d9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    49e1:	48 89 48 10          	mov    %rcx,0x10(%rax)
    49e5:	89 50 18             	mov    %edx,0x18(%rax)
    49e8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    49ef:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    49f7:	48 89 58 20          	mov    %rbx,0x20(%rax)
    49fb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    49ff:	5b                   	pop    %rbx
    4a00:	5d                   	pop    %rbp
    4a01:	41 5c                	pop    %r12
    4a03:	41 5d                	pop    %r13
    4a05:	41 5e                	pop    %r14
    4a07:	e9 34 d9 ff ff       	jmp    2340 <io_uring_submit@plt>
    4a0c:	0f 1f 40 00          	nopl   0x0(%rax)
    4a10:	e9 7e ff ff ff       	jmp    4993 <_send_static_string_content+0x83>
    4a15:	48 8b 0d 04 56 00 00 	mov    0x5604(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4a1c:	ba 28 00 00 00       	mov    $0x28,%edx
    4a21:	be 01 00 00 00       	mov    $0x1,%esi
    4a26:	48 8d 3d d3 29 00 00 	lea    0x29d3(%rip),%rdi        # 7400 <_IO_stdin_used+0x400>
    4a2d:	e8 8e da ff ff       	call   24c0 <fwrite@plt>
    4a32:	bf 01 00 00 00       	mov    $0x1,%edi
    4a37:	e8 64 da ff ff       	call   24a0 <exit@plt>
    4a3c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a40 <handle_unimplemented_method>:
    4a40:	f3 0f 1e fa          	endbr64
    4a44:	48 89 f2             	mov    %rsi,%rdx
    4a47:	89 fe                	mov    %edi,%esi
    4a49:	48 8b 3d c8 55 00 00 	mov    0x55c8(%rip),%rdi        # a018 <unimplemented_content>
    4a50:	e9 bb fe ff ff       	jmp    4910 <_send_static_string_content>
    4a55:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004a60 <handle_http_404>:
    4a60:	f3 0f 1e fa          	endbr64
    4a64:	48 89 f2             	mov    %rsi,%rdx
    4a67:	89 fe                	mov    %edi,%esi
    4a69:	48 8b 3d a0 55 00 00 	mov    0x55a0(%rip),%rdi        # a010 <http_404_content>
    4a70:	e9 9b fe ff ff       	jmp    4910 <_send_static_string_content>
    4a75:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004a80 <handle_get_method>:
    4a80:	f3 0f 1e fa          	endbr64
    4a84:	41 56                	push   %r14
    4a86:	41 55                	push   %r13
    4a88:	49 89 d5             	mov    %rdx,%r13
    4a8b:	41 54                	push   %r12
    4a8d:	41 89 f4             	mov    %esi,%r12d
    4a90:	55                   	push   %rbp
    4a91:	48 89 fd             	mov    %rdi,%rbp
    4a94:	53                   	push   %rbx
    4a95:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    4a9c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4aa5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    4aad:	31 c0                	xor    %eax,%eax
    4aaf:	e8 6c d8 ff ff       	call   2320 <strlen@plt>
    4ab4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4ab9:	48 89 c3             	mov    %rax,%rbx
    4abc:	0f 84 b6 00 00 00    	je     4b78 <handle_get_method+0xf8>
    4ac2:	b8 69 63 00 00       	mov    $0x6369,%eax
    4ac7:	48 89 ee             	mov    %rbp,%rsi
    4aca:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4ace:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4ad3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4adb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4ae3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4aee:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    4af6:	e8 c5 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    4afb:	48 89 e6             	mov    %rsp,%rsi
    4afe:	4c 89 f7             	mov    %r14,%rdi
    4b01:	e8 ca d8 ff ff       	call   23d0 <stat@plt>
    4b06:	83 f8 ff             	cmp    $0xffffffff,%eax
    4b09:	0f 84 d3 00 00 00    	je     4be2 <handle_get_method+0x162>
    4b0f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4b13:	25 00 f0 00 00       	and    $0xf000,%eax
    4b18:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4b1d:	0f 84 f5 00 00 00    	je     4c18 <handle_get_method+0x198>
    4b23:	48 8b 3d e6 54 00 00 	mov    0x54e6(%rip),%rdi        # a010 <http_404_content>
    4b2a:	4c 89 ea             	mov    %r13,%rdx
    4b2d:	44 89 e6             	mov    %r12d,%esi
    4b30:	e8 db fd ff ff       	call   4910 <_send_static_string_content>
    4b35:	4c 89 f2             	mov    %r14,%rdx
    4b38:	bf 01 00 00 00       	mov    $0x1,%edi
    4b3d:	31 c0                	xor    %eax,%eax
    4b3f:	48 8d 35 da 25 00 00 	lea    0x25da(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    4b46:	e8 05 d9 ff ff       	call   2450 <__printf_chk@plt>
    4b4b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4b53:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b5c:	0f 85 20 01 00 00    	jne    4c82 <handle_get_method+0x202>
    4b62:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4b69:	5b                   	pop    %rbx
    4b6a:	5d                   	pop    %rbp
    4b6b:	41 5c                	pop    %r12
    4b6d:	41 5d                	pop    %r13
    4b6f:	41 5e                	pop    %r14
    4b71:	c3                   	ret
    4b72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b78:	ba 69 63 00 00       	mov    $0x6369,%edx
    4b7d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4b85:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4b8a:	48 89 ee             	mov    %rbp,%rsi
    4b8d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    4b95:	48 89 c2             	mov    %rax,%rdx
    4b98:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4ba0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4bab:	e8 10 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    4bb0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4bb5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4bba:	48 8d 35 2a 25 00 00 	lea    0x252a(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4bc1:	48 29 d9             	sub    %rbx,%rcx
    4bc4:	ba 0b 00 00 00       	mov    $0xb,%edx
    4bc9:	e8 f2 d7 ff ff       	call   23c0 <__memcpy_chk@plt>
    4bce:	48 89 e6             	mov    %rsp,%rsi
    4bd1:	4c 89 f7             	mov    %r14,%rdi
    4bd4:	e8 f7 d7 ff ff       	call   23d0 <stat@plt>
    4bd9:	83 f8 ff             	cmp    $0xffffffff,%eax
    4bdc:	0f 85 2d ff ff ff    	jne    4b0f <handle_get_method+0x8f>
    4be2:	4c 89 f2             	mov    %r14,%rdx
    4be5:	48 89 e9             	mov    %rbp,%rcx
    4be8:	48 8d 35 07 25 00 00 	lea    0x2507(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    4bef:	31 c0                	xor    %eax,%eax
    4bf1:	bf 01 00 00 00       	mov    $0x1,%edi
    4bf6:	e8 55 d8 ff ff       	call   2450 <__printf_chk@plt>
    4bfb:	48 8b 3d 0e 54 00 00 	mov    0x540e(%rip),%rdi        # a010 <http_404_content>
    4c02:	4c 89 ea             	mov    %r13,%rdx
    4c05:	44 89 e6             	mov    %r12d,%esi
    4c08:	e8 03 fd ff ff       	call   4910 <_send_static_string_content>
    4c0d:	e9 39 ff ff ff       	jmp    4b4b <handle_get_method+0xcb>
    4c12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4c18:	bf 70 00 00 00       	mov    $0x70,%edi
    4c1d:	e8 ee d7 ff ff       	call   2410 <malloc@plt>
    4c22:	48 89 c3             	mov    %rax,%rbx
    4c25:	48 85 c0             	test   %rax,%rax
    4c28:	74 5d                	je     4c87 <handle_get_method+0x207>
    4c2a:	44 89 60 08          	mov    %r12d,0x8(%rax)
    4c2e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4c33:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4c37:	4c 89 f7             	mov    %r14,%rdi
    4c3a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    4c41:	e8 4a f5 ff ff       	call   4190 <send_headers>
    4c46:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4c4b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4c4f:	4c 89 f7             	mov    %r14,%rdi
    4c52:	e8 69 fa ff ff       	call   46c0 <copy_file_contents>
    4c57:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4c5c:	4c 89 f2             	mov    %r14,%rdx
    4c5f:	31 c0                	xor    %eax,%eax
    4c61:	48 8d 35 a6 24 00 00 	lea    0x24a6(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4c68:	bf 01 00 00 00       	mov    $0x1,%edi
    4c6d:	e8 de d7 ff ff       	call   2450 <__printf_chk@plt>
    4c72:	4c 89 ee             	mov    %r13,%rsi
    4c75:	48 89 df             	mov    %rbx,%rdi
    4c78:	e8 13 fb ff ff       	call   4790 <add_write_request>
    4c7d:	e9 c9 fe ff ff       	jmp    4b4b <handle_get_method+0xcb>
    4c82:	e8 a9 d6 ff ff       	call   2330 <__stack_chk_fail@plt>
    4c87:	48 8b 0d 92 53 00 00 	mov    0x5392(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c8e:	ba 28 00 00 00       	mov    $0x28,%edx
    4c93:	be 01 00 00 00       	mov    $0x1,%esi
    4c98:	48 8d 3d 61 27 00 00 	lea    0x2761(%rip),%rdi        # 7400 <_IO_stdin_used+0x400>
    4c9f:	e8 1c d8 ff ff       	call   24c0 <fwrite@plt>
    4ca4:	bf 01 00 00 00       	mov    $0x1,%edi
    4ca9:	e8 f2 d7 ff ff       	call   24a0 <exit@plt>
    4cae:	66 90                	xchg   %ax,%ax

0000000000004cb0 <handle_http_method>:
    4cb0:	f3 0f 1e fa          	endbr64
    4cb4:	41 57                	push   %r15
    4cb6:	41 56                	push   %r14
    4cb8:	4c 8d 35 c6 23 00 00 	lea    0x23c6(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
    4cbf:	41 55                	push   %r13
    4cc1:	49 89 d5             	mov    %rdx,%r13
    4cc4:	41 54                	push   %r12
    4cc6:	41 89 f4             	mov    %esi,%r12d
    4cc9:	4c 89 f6             	mov    %r14,%rsi
    4ccc:	55                   	push   %rbp
    4ccd:	53                   	push   %rbx
    4cce:	48 83 ec 18          	sub    $0x18,%rsp
    4cd2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4cdb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4ce0:	31 c0                	xor    %eax,%eax
    4ce2:	49 89 e7             	mov    %rsp,%r15
    4ce5:	4c 89 fa             	mov    %r15,%rdx
    4ce8:	e8 93 d6 ff ff       	call   2380 <strtok_r@plt>
    4ced:	48 0f be 18          	movsbq (%rax),%rbx
    4cf1:	48 89 c5             	mov    %rax,%rbp
    4cf4:	84 db                	test   %bl,%bl
    4cf6:	74 1d                	je     4d15 <handle_http_method+0x65>
    4cf8:	e8 13 d8 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4cfd:	48 89 ea             	mov    %rbp,%rdx
    4d00:	48 8b 08             	mov    (%rax),%rcx
    4d03:	48 83 c2 01          	add    $0x1,%rdx
    4d07:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4d0a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    4d0d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4d11:	84 db                	test   %bl,%bl
    4d13:	75 eb                	jne    4d00 <handle_http_method+0x50>
    4d15:	4c 89 fa             	mov    %r15,%rdx
    4d18:	4c 89 f6             	mov    %r14,%rsi
    4d1b:	31 ff                	xor    %edi,%edi
    4d1d:	e8 5e d6 ff ff       	call   2380 <strtok_r@plt>
    4d22:	48 8d 35 0a 24 00 00 	lea    0x240a(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4d29:	48 89 ef             	mov    %rbp,%rdi
    4d2c:	48 89 c3             	mov    %rax,%rbx
    4d2f:	e8 7c d6 ff ff       	call   23b0 <strcmp@plt>
    4d34:	4c 89 ea             	mov    %r13,%rdx
    4d37:	44 89 e6             	mov    %r12d,%esi
    4d3a:	85 c0                	test   %eax,%eax
    4d3c:	75 2a                	jne    4d68 <handle_http_method+0xb8>
    4d3e:	48 89 df             	mov    %rbx,%rdi
    4d41:	e8 3a fd ff ff       	call   4a80 <handle_get_method>
    4d46:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4d4b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d54:	75 20                	jne    4d76 <handle_http_method+0xc6>
    4d56:	48 83 c4 18          	add    $0x18,%rsp
    4d5a:	5b                   	pop    %rbx
    4d5b:	5d                   	pop    %rbp
    4d5c:	41 5c                	pop    %r12
    4d5e:	41 5d                	pop    %r13
    4d60:	41 5e                	pop    %r14
    4d62:	41 5f                	pop    %r15
    4d64:	c3                   	ret
    4d65:	0f 1f 00             	nopl   (%rax)
    4d68:	48 8b 3d a9 52 00 00 	mov    0x52a9(%rip),%rdi        # a018 <unimplemented_content>
    4d6f:	e8 9c fb ff ff       	call   4910 <_send_static_string_content>
    4d74:	eb d0                	jmp    4d46 <handle_http_method+0x96>
    4d76:	e8 b5 d5 ff ff       	call   2330 <__stack_chk_fail@plt>
    4d7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004d80 <get_line>:
    4d80:	f3 0f 1e fa          	endbr64
    4d84:	85 d2                	test   %edx,%edx
    4d86:	7e 38                	jle    4dc0 <get_line+0x40>
    4d88:	48 63 d2             	movslq %edx,%rdx
    4d8b:	48 83 c7 01          	add    $0x1,%rdi
    4d8f:	48 01 f2             	add    %rsi,%rdx
    4d92:	eb 11                	jmp    4da5 <get_line+0x25>
    4d94:	0f 1f 40 00          	nopl   0x0(%rax)
    4d98:	48 83 c6 01          	add    $0x1,%rsi
    4d9c:	48 83 c7 01          	add    $0x1,%rdi
    4da0:	48 39 d6             	cmp    %rdx,%rsi
    4da3:	74 1b                	je     4dc0 <get_line+0x40>
    4da5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4da9:	88 06                	mov    %al,(%rsi)
    4dab:	3c 0d                	cmp    $0xd,%al
    4dad:	75 e9                	jne    4d98 <get_line+0x18>
    4daf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4db2:	75 e4                	jne    4d98 <get_line+0x18>
    4db4:	c6 06 00             	movb   $0x0,(%rsi)
    4db7:	31 c0                	xor    %eax,%eax
    4db9:	c3                   	ret
    4dba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4dc0:	b8 01 00 00 00       	mov    $0x1,%eax
    4dc5:	c3                   	ret
    4dc6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004dd0 <handle_client_request>:
    4dd0:	f3 0f 1e fa          	endbr64
    4dd4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4ddb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4ddf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4de8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4df0:	31 c0                	xor    %eax,%eax
    4df2:	49 89 e2             	mov    %rsp,%r10
    4df5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4dfd:	4c 89 d0             	mov    %r10,%rax
    4e00:	eb 13                	jmp    4e15 <handle_client_request+0x45>
    4e02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4e08:	48 83 c0 01          	add    $0x1,%rax
    4e0c:	48 83 c1 01          	add    $0x1,%rcx
    4e10:	4c 39 c8             	cmp    %r9,%rax
    4e13:	74 4b                	je     4e60 <handle_client_request+0x90>
    4e15:	44 0f b6 01          	movzbl (%rcx),%r8d
    4e19:	44 88 00             	mov    %r8b,(%rax)
    4e1c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4e20:	75 e6                	jne    4e08 <handle_client_request+0x38>
    4e22:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4e26:	75 e0                	jne    4e08 <handle_client_request+0x38>
    4e28:	c6 00 00             	movb   $0x0,(%rax)
    4e2b:	8b 47 08             	mov    0x8(%rdi),%eax
    4e2e:	48 89 f2             	mov    %rsi,%rdx
    4e31:	4c 89 d7             	mov    %r10,%rdi
    4e34:	89 c6                	mov    %eax,%esi
    4e36:	e8 75 fe ff ff       	call   4cb0 <handle_http_method>
    4e3b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4e43:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4e4c:	75 39                	jne    4e87 <handle_client_request+0xb7>
    4e4e:	31 c0                	xor    %eax,%eax
    4e50:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4e57:	c3                   	ret
    4e58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4e60:	48 8b 0d b9 51 00 00 	mov    0x51b9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4e67:	ba 12 00 00 00       	mov    $0x12,%edx
    4e6c:	be 01 00 00 00       	mov    $0x1,%esi
    4e71:	48 8d 3d bf 22 00 00 	lea    0x22bf(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4e78:	e8 43 d6 ff ff       	call   24c0 <fwrite@plt>
    4e7d:	bf 01 00 00 00       	mov    $0x1,%edi
    4e82:	e8 19 d6 ff ff       	call   24a0 <exit@plt>
    4e87:	e8 a4 d4 ff ff       	call   2330 <__stack_chk_fail@plt>
    4e8c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004e90 <add_accept_request>:
    4e90:	f3 0f 1e fa          	endbr64
    4e94:	55                   	push   %rbp
    4e95:	53                   	push   %rbx
    4e96:	48 89 cb             	mov    %rcx,%rbx
    4e99:	48 83 ec 08          	sub    $0x8,%rsp
    4e9d:	8b 41 44             	mov    0x44(%rcx),%eax
    4ea0:	4c 8b 03             	mov    (%rbx),%r8
    4ea3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    4ea9:	83 c0 01             	add    $0x1,%eax
    4eac:	45 8b 08             	mov    (%r8),%r9d
    4eaf:	f6 c1 02             	test   $0x2,%cl
    4eb2:	74 00                	je     4eb4 <add_accept_request+0x24>
    4eb4:	41 89 c0             	mov    %eax,%r8d
    4eb7:	45 29 c8             	sub    %r9d,%r8d
    4eba:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4ebe:	0f 82 a6 d6 ff ff    	jb     256a <add_accept_request.cold>
    4ec4:	c1 e9 0a             	shr    $0xa,%ecx
    4ec7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4eca:	23 6b 58             	and    0x58(%rbx),%ebp
    4ecd:	89 43 44             	mov    %eax,0x44(%rbx)
    4ed0:	83 e1 01             	and    $0x1,%ecx
    4ed3:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4ed7:	d3 e5                	shl    %cl,%ebp
    4ed9:	48 c1 e5 06          	shl    $0x6,%rbp
    4edd:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4ee1:	89 7d 04             	mov    %edi,0x4(%rbp)
    4ee4:	bf 10 00 00 00       	mov    $0x10,%edi
    4ee9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    4ef0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    4ef4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    4ef8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    4f00:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    4f08:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4f0c:	e8 ff d4 ff ff       	call   2410 <malloc@plt>
    4f11:	48 89 df             	mov    %rbx,%rdi
    4f14:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    4f1a:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4f1e:	48 83 c4 08          	add    $0x8,%rsp
    4f22:	5b                   	pop    %rbx
    4f23:	5d                   	pop    %rbp
    4f24:	e9 17 d4 ff ff       	jmp    2340 <io_uring_submit@plt>
    4f29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004f30 <io_thread>:
    4f30:	f3 0f 1e fa          	endbr64
    4f34:	41 57                	push   %r15
    4f36:	31 d2                	xor    %edx,%edx
    4f38:	41 56                	push   %r14
    4f3a:	41 55                	push   %r13
    4f3c:	41 54                	push   %r12
    4f3e:	55                   	push   %rbp
    4f3f:	48 89 fd             	mov    %rdi,%rbp
    4f42:	53                   	push   %rbx
    4f43:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4f4a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4f53:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4f5b:	48 8b 87 c8 00 00 00 	mov    0xc8(%rdi),%rax
    4f62:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4f67:	bf 00 01 00 00       	mov    $0x100,%edi
    4f6c:	48 89 de             	mov    %rbx,%rsi
    4f6f:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4f73:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4f78:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4f7d:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4f82:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4f87:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4f8f:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4f94:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4f9c:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4fa1:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4fa9:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4fae:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4fb6:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4fbb:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4fc3:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4fc8:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4fd0:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4fd8:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4fe0:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4fe8:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4ff0:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4ff8:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5000:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5008:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5010:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5018:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5020:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5027:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    502f:	e8 bc d3 ff ff       	call   23f0 <io_uring_queue_init@plt>
    5034:	48 8b bd c8 00 00 00 	mov    0xc8(%rbp),%rdi
    503b:	31 f6                	xor    %esi,%esi
    503d:	e8 9e d4 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
    5042:	31 d2                	xor    %edx,%edx
    5044:	be 01 00 00 00       	mov    $0x1,%esi
    5049:	bf 02 00 00 00       	mov    $0x2,%edi
    504e:	e8 dd d4 ff ff       	call   2530 <socket@plt>
    5053:	83 f8 ff             	cmp    $0xffffffff,%eax
    5056:	0f 84 02 06 00 00    	je     565e <io_thread+0x72e>
    505c:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5061:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5067:	89 c7                	mov    %eax,%edi
    5069:	41 89 c4             	mov    %eax,%r12d
    506c:	ba 02 00 00 00       	mov    $0x2,%edx
    5071:	be 01 00 00 00       	mov    $0x1,%esi
    5076:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    507e:	e8 7d d2 ff ff       	call   2300 <setsockopt@plt>
    5083:	85 c0                	test   %eax,%eax
    5085:	0f 88 c7 05 00 00    	js     5652 <io_thread+0x722>
    508b:	8b 05 9f 29 00 00    	mov    0x299f(%rip),%eax        # 7a30 <_IO_stdin_used+0xa30>
    5091:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    5096:	ba 10 00 00 00       	mov    $0x10,%edx
    509b:	44 89 e7             	mov    %r12d,%edi
    509e:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    50a7:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    50af:	89 44 24 40          	mov    %eax,0x40(%rsp)
    50b3:	e8 a8 d3 ff ff       	call   2460 <bind@plt>
    50b8:	85 c0                	test   %eax,%eax
    50ba:	0f 88 86 05 00 00    	js     5646 <io_thread+0x716>
    50c0:	be 0a 00 00 00       	mov    $0xa,%esi
    50c5:	44 89 e7             	mov    %r12d,%edi
    50c8:	e8 53 d3 ff ff       	call   2420 <listen@plt>
    50cd:	85 c0                	test   %eax,%eax
    50cf:	0f 88 65 05 00 00    	js     563a <io_thread+0x70a>
    50d5:	ba db 18 00 00       	mov    $0x18db,%edx
    50da:	48 8d 35 9b 20 00 00 	lea    0x209b(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    50e1:	bf 01 00 00 00       	mov    $0x1,%edi
    50e6:	31 c0                	xor    %eax,%eax
    50e8:	e8 63 d3 ff ff       	call   2450 <__printf_chk@plt>
    50ed:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    50f2:	48 89 d9             	mov    %rbx,%rcx
    50f5:	44 89 e7             	mov    %r12d,%edi
    50f8:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    50fd:	48 89 c6             	mov    %rax,%rsi
    5100:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    5105:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    510a:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    5112:	e8 79 fd ff ff       	call   4e90 <add_accept_request>
    5117:	bf 01 00 00 00       	mov    $0x1,%edi
    511c:	be 10 00 00 00       	mov    $0x10,%esi
    5121:	e8 7a d2 ff ff       	call   23a0 <calloc@plt>
    5126:	bf 0a 00 00 00       	mov    $0xa,%edi
    512b:	49 89 c5             	mov    %rax,%r13
    512e:	e8 dd d2 ff ff       	call   2410 <malloc@plt>
    5133:	48 85 c0             	test   %rax,%rax
    5136:	0f 84 d7 04 00 00    	je     5613 <io_thread+0x6e3>
    513c:	49 89 45 00          	mov    %rax,0x0(%r13)
    5140:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5147:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    514e:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    5156:	8d 50 01             	lea    0x1(%rax),%edx
    5159:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    515e:	8b 30                	mov    (%rax),%esi
    5160:	f6 c1 02             	test   $0x2,%cl
    5163:	0f 85 27 04 00 00    	jne    5590 <io_thread+0x660>
    5169:	89 d0                	mov    %edx,%eax
    516b:	29 f0                	sub    %esi,%eax
    516d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5174:	0f 82 fa d3 ff ff    	jb     2574 <io_thread.cold>
    517a:	c1 e9 0a             	shr    $0xa,%ecx
    517d:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5184:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5188:	48 89 df             	mov    %rbx,%rdi
    518b:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5192:	83 e1 01             	and    $0x1,%ecx
    5195:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    519c:	48 8d b5 d0 00 00 00 	lea    0xd0(%rbp),%rsi
    51a3:	8b 95 d0 00 00 00    	mov    0xd0(%rbp),%edx
    51a9:	d3 e0                	shl    %cl,%eax
    51ab:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    51b0:	48 c1 e0 06          	shl    $0x6,%rax
    51b4:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    51bc:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    51c2:	89 50 04             	mov    %edx,0x4(%rax)
    51c5:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    51cd:	4c 89 68 10          	mov    %r13,0x10(%rax)
    51d1:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    51d9:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    51e1:	48 89 70 20          	mov    %rsi,0x20(%rax)
    51e5:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    51e9:	e8 52 d1 ff ff       	call   2340 <io_uring_submit@plt>
    51ee:	8b 45 64             	mov    0x64(%rbp),%eax
    51f1:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    51f6:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    51fe:	83 f8 01             	cmp    $0x1,%eax
    5201:	0f 85 af 01 00 00    	jne    53b6 <io_thread+0x486>
    5207:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    520c:	4d 89 ce             	mov    %r9,%r14
    520f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5214:	0f 1f 40 00          	nopl   0x0(%rax)
    5218:	48 8d 3d 73 1f 00 00 	lea    0x1f73(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    521f:	e8 cc d0 ff ff       	call   22f0 <puts@plt>
    5224:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    522b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    5232:	c1 e9 0b             	shr    $0xb,%ecx
    5235:	83 e1 01             	and    $0x1,%ecx
    5238:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5240:	8b 00                	mov    (%rax),%eax
    5242:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    524a:	8b 16                	mov    (%rsi),%edx
    524c:	39 d0                	cmp    %edx,%eax
    524e:	74 36                	je     5286 <io_thread+0x356>
    5250:	89 f8                	mov    %edi,%eax
    5252:	21 d0                	and    %edx,%eax
    5254:	d3 e0                	shl    %cl,%eax
    5256:	48 c1 e0 04          	shl    $0x4,%rax
    525a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    5262:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    526a:	0f 85 80 01 00 00    	jne    53f0 <io_thread+0x4c0>
    5270:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5274:	0f 85 1e 03 00 00    	jne    5598 <io_thread+0x668>
    527a:	8b 40 08             	mov    0x8(%rax),%eax
    527d:	83 c2 01             	add    $0x1,%edx
    5280:	89 16                	mov    %edx,(%rsi)
    5282:	85 c0                	test   %eax,%eax
    5284:	79 b2                	jns    5238 <io_thread+0x308>
    5286:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    528f:	90                   	nop
    5290:	45 31 c0             	xor    %r8d,%r8d
    5293:	31 d2                	xor    %edx,%edx
    5295:	b9 01 00 00 00       	mov    $0x1,%ecx
    529a:	4c 89 f6             	mov    %r14,%rsi
    529d:	48 89 df             	mov    %rbx,%rdi
    52a0:	e8 9b d1 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    52a5:	41 89 c7             	mov    %eax,%r15d
    52a8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    52ad:	48 83 38 01          	cmpq   $0x1,(%rax)
    52b1:	0f 84 f1 02 00 00    	je     55a8 <io_thread+0x678>
    52b7:	48 8d 3d fa 1e 00 00 	lea    0x1efa(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    52be:	e8 2d d0 ff ff       	call   22f0 <puts@plt>
    52c3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    52c8:	4c 8b 22             	mov    (%rdx),%r12
    52cb:	45 85 ff             	test   %r15d,%r15d
    52ce:	0f 88 2e 03 00 00    	js     5602 <io_thread+0x6d2>
    52d4:	8b 42 08             	mov    0x8(%rdx),%eax
    52d7:	45 8b 04 24          	mov    (%r12),%r8d
    52db:	85 c0                	test   %eax,%eax
    52dd:	0f 88 e5 02 00 00    	js     55c8 <io_thread+0x698>
    52e3:	41 83 f8 01          	cmp    $0x1,%r8d
    52e7:	0f 84 3b 01 00 00    	je     5428 <io_thread+0x4f8>
    52ed:	41 83 f8 02          	cmp    $0x2,%r8d
    52f1:	0f 84 b1 01 00 00    	je     54a8 <io_thread+0x578>
    52f7:	45 85 c0             	test   %r8d,%r8d
    52fa:	0f 84 70 01 00 00    	je     5470 <io_thread+0x540>
    5300:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5308:	8b 02                	mov    (%rdx),%eax
    530a:	83 c0 01             	add    $0x1,%eax
    530d:	89 02                	mov    %eax,(%rdx)
    530f:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5316:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    531d:	8d 50 01             	lea    0x1(%rax),%edx
    5320:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5325:	8b 30                	mov    (%rax),%esi
    5327:	f6 c1 02             	test   $0x2,%cl
    532a:	74 00                	je     532c <io_thread+0x3fc>
    532c:	89 d0                	mov    %edx,%eax
    532e:	29 f0                	sub    %esi,%eax
    5330:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5337:	0f 82 37 d2 ff ff    	jb     2574 <io_thread.cold>
    533d:	c1 e9 0a             	shr    $0xa,%ecx
    5340:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    5345:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5349:	48 89 df             	mov    %rbx,%rdi
    534c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5353:	83 e1 01             	and    $0x1,%ecx
    5356:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    535d:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5364:	d3 e0                	shl    %cl,%eax
    5366:	8b 95 d0 00 00 00    	mov    0xd0(%rbp),%edx
    536c:	48 c1 e0 06          	shl    $0x6,%rax
    5370:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5378:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    537e:	89 50 04             	mov    %edx,0x4(%rax)
    5381:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5389:	4c 89 68 10          	mov    %r13,0x10(%rax)
    538d:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5395:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    539d:	48 89 70 20          	mov    %rsi,0x20(%rax)
    53a1:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    53a5:	e8 96 cf ff ff       	call   2340 <io_uring_submit@plt>
    53aa:	8b 45 64             	mov    0x64(%rbp),%eax
    53ad:	83 f8 01             	cmp    $0x1,%eax
    53b0:	0f 84 62 fe ff ff    	je     5218 <io_thread+0x2e8>
    53b6:	48 8d 3d 34 1e 00 00 	lea    0x1e34(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    53bd:	e8 2e cf ff ff       	call   22f0 <puts@plt>
    53c2:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    53ca:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    53d3:	0f 85 35 02 00 00    	jne    560e <io_thread+0x6de>
    53d9:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    53e0:	31 c0                	xor    %eax,%eax
    53e2:	5b                   	pop    %rbx
    53e3:	5d                   	pop    %rbp
    53e4:	41 5c                	pop    %r12
    53e6:	41 5d                	pop    %r13
    53e8:	41 5e                	pop    %r14
    53ea:	41 5f                	pop    %r15
    53ec:	c3                   	ret
    53ed:	0f 1f 00             	nopl   (%rax)
    53f0:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    53f5:	48 85 c0             	test   %rax,%rax
    53f8:	0f 84 92 fe ff ff    	je     5290 <io_thread+0x360>
    53fe:	48 83 38 01          	cmpq   $0x1,(%rax)
    5402:	0f 84 a0 01 00 00    	je     55a8 <io_thread+0x678>
    5408:	48 8d 3d a9 1d 00 00 	lea    0x1da9(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    540f:	e8 dc ce ff ff       	call   22f0 <puts@plt>
    5414:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5419:	4c 8b 22             	mov    (%rdx),%r12
    541c:	e9 b3 fe ff ff       	jmp    52d4 <io_thread+0x3a4>
    5421:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5428:	85 c0                	test   %eax,%eax
    542a:	0f 85 c0 00 00 00    	jne    54f0 <io_thread+0x5c0>
    5430:	48 8b 0d e9 4b 00 00 	mov    0x4be9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5437:	ba 0f 00 00 00       	mov    $0xf,%edx
    543c:	be 01 00 00 00       	mov    $0x1,%esi
    5441:	48 8d 3d 99 1d 00 00 	lea    0x1d99(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    5448:	e8 73 d0 ff ff       	call   24c0 <fwrite@plt>
    544d:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5452:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5458:	48 85 c0             	test   %rax,%rax
    545b:	0f 84 ae fe ff ff    	je     530f <io_thread+0x3df>
    5461:	e9 9a fe ff ff       	jmp    5300 <io_thread+0x3d0>
    5466:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5470:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    5475:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    547a:	48 89 d9             	mov    %rbx,%rcx
    547d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5481:	e8 0a fa ff ff       	call   4e90 <add_accept_request>
    5486:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    548b:	48 89 de             	mov    %rbx,%rsi
    548e:	8b 78 08             	mov    0x8(%rax),%edi
    5491:	e8 9a f3 ff ff       	call   4830 <add_read_request>
    5496:	4c 89 e7             	mov    %r12,%rdi
    5499:	e8 22 ce ff ff       	call   22c0 <free@plt>
    549e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    54a3:	eb b3                	jmp    5458 <io_thread+0x528>
    54a5:	0f 1f 00             	nopl   (%rax)
    54a8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    54ad:	45 31 ff             	xor    %r15d,%r15d
    54b0:	85 c0                	test   %eax,%eax
    54b2:	7e 20                	jle    54d4 <io_thread+0x5a4>
    54b4:	0f 1f 40 00          	nopl   0x0(%rax)
    54b8:	4c 89 f8             	mov    %r15,%rax
    54bb:	49 83 c7 01          	add    $0x1,%r15
    54bf:	48 c1 e0 04          	shl    $0x4,%rax
    54c3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    54c8:	e8 f3 cd ff ff       	call   22c0 <free@plt>
    54cd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    54d2:	7f e4                	jg     54b8 <io_thread+0x588>
    54d4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    54d9:	e8 92 ce ff ff       	call   2370 <close@plt>
    54de:	4c 89 e7             	mov    %r12,%rdi
    54e1:	e8 da cd ff ff       	call   22c0 <free@plt>
    54e6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    54eb:	e9 68 ff ff ff       	jmp    5458 <io_thread+0x528>
    54f0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    54f5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    54fa:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5502:	eb 11                	jmp    5515 <io_thread+0x5e5>
    5504:	0f 1f 40 00          	nopl   0x0(%rax)
    5508:	48 83 c0 01          	add    $0x1,%rax
    550c:	48 83 c2 01          	add    $0x1,%rdx
    5510:	48 39 c6             	cmp    %rax,%rsi
    5513:	74 4b                	je     5560 <io_thread+0x630>
    5515:	0f b6 0a             	movzbl (%rdx),%ecx
    5518:	88 08                	mov    %cl,(%rax)
    551a:	80 f9 0d             	cmp    $0xd,%cl
    551d:	75 e9                	jne    5508 <io_thread+0x5d8>
    551f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5523:	75 e3                	jne    5508 <io_thread+0x5d8>
    5525:	c6 00 00             	movb   $0x0,(%rax)
    5528:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    552d:	48 89 da             	mov    %rbx,%rdx
    5530:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5535:	e8 76 f7 ff ff       	call   4cb0 <handle_http_method>
    553a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    553f:	e8 7c cd ff ff       	call   22c0 <free@plt>
    5544:	4c 89 e7             	mov    %r12,%rdi
    5547:	e8 74 cd ff ff       	call   22c0 <free@plt>
    554c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5551:	e9 02 ff ff ff       	jmp    5458 <io_thread+0x528>
    5556:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5560:	48 8b 0d b9 4a 00 00 	mov    0x4ab9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5567:	ba 12 00 00 00       	mov    $0x12,%edx
    556c:	be 01 00 00 00       	mov    $0x1,%esi
    5571:	48 8d 3d bf 1b 00 00 	lea    0x1bbf(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5578:	e8 43 cf ff ff       	call   24c0 <fwrite@plt>
    557d:	bf 01 00 00 00       	mov    $0x1,%edi
    5582:	e8 19 cf ff ff       	call   24a0 <exit@plt>
    5587:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5590:	e9 d4 fb ff ff       	jmp    5169 <io_thread+0x239>
    5595:	0f 1f 00             	nopl   (%rax)
    5598:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    559d:	e9 5c fe ff ff       	jmp    53fe <io_thread+0x4ce>
    55a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    55a8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    55b0:	48 8d 3d ed 1b 00 00 	lea    0x1bed(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    55b7:	8b 02                	mov    (%rdx),%eax
    55b9:	83 c0 01             	add    $0x1,%eax
    55bc:	89 02                	mov    %eax,(%rdx)
    55be:	e8 2d cd ff ff       	call   22f0 <puts@plt>
    55c3:	e9 ee fd ff ff       	jmp    53b6 <io_thread+0x486>
    55c8:	f7 d8                	neg    %eax
    55ca:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    55cf:	89 c7                	mov    %eax,%edi
    55d1:	e8 2a cf ff ff       	call   2500 <strerror@plt>
    55d6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    55db:	be 01 00 00 00       	mov    $0x1,%esi
    55e0:	48 8b 3d 39 4a 00 00 	mov    0x4a39(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    55e7:	48 89 c1             	mov    %rax,%rcx
    55ea:	48 8d 15 3f 1e 00 00 	lea    0x1e3f(%rip),%rdx        # 7430 <_IO_stdin_used+0x430>
    55f1:	31 c0                	xor    %eax,%eax
    55f3:	e8 d8 ce ff ff       	call   24d0 <__fprintf_chk@plt>
    55f8:	bf 01 00 00 00       	mov    $0x1,%edi
    55fd:	e8 9e ce ff ff       	call   24a0 <exit@plt>
    5602:	48 8d 3d c6 1b 00 00 	lea    0x1bc6(%rip),%rdi        # 71cf <_IO_stdin_used+0x1cf>
    5609:	e8 a2 ea ff ff       	call   40b0 <fatal_error>
    560e:	e8 1d cd ff ff       	call   2330 <__stack_chk_fail@plt>
    5613:	48 8b 0d 06 4a 00 00 	mov    0x4a06(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    561a:	ba 28 00 00 00       	mov    $0x28,%edx
    561f:	be 01 00 00 00       	mov    $0x1,%esi
    5624:	48 8d 3d d5 1d 00 00 	lea    0x1dd5(%rip),%rdi        # 7400 <_IO_stdin_used+0x400>
    562b:	e8 90 ce ff ff       	call   24c0 <fwrite@plt>
    5630:	bf 01 00 00 00       	mov    $0x1,%edi
    5635:	e8 66 ce ff ff       	call   24a0 <exit@plt>
    563a:	48 8d 3d 32 1b 00 00 	lea    0x1b32(%rip),%rdi        # 7173 <_IO_stdin_used+0x173>
    5641:	e8 6a ea ff ff       	call   40b0 <fatal_error>
    5646:	48 8d 3d 1f 1b 00 00 	lea    0x1b1f(%rip),%rdi        # 716c <_IO_stdin_used+0x16c>
    564d:	e8 5e ea ff ff       	call   40b0 <fatal_error>
    5652:	48 8d 3d fa 1a 00 00 	lea    0x1afa(%rip),%rdi        # 7153 <_IO_stdin_used+0x153>
    5659:	e8 52 ea ff ff       	call   40b0 <fatal_error>
    565e:	48 8d 3d e5 1a 00 00 	lea    0x1ae5(%rip),%rdi        # 714a <_IO_stdin_used+0x14a>
    5665:	e8 46 ea ff ff       	call   40b0 <fatal_error>
    566a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005670 <sendm>:
    5670:	f3 0f 1e fa          	endbr64
    5674:	8b 97 78 01 00 00    	mov    0x178(%rdi),%edx
    567a:	48 89 f8             	mov    %rdi,%rax
    567d:	83 fa 01             	cmp    $0x1,%edx
    5680:	74 06                	je     5688 <sendm+0x18>
    5682:	31 c0                	xor    %eax,%eax
    5684:	c3                   	ret
    5685:	0f 1f 00             	nopl   (%rax)
    5688:	8b 97 34 01 00 00    	mov    0x134(%rdi),%edx
    568e:	85 d2                	test   %edx,%edx
    5690:	7e f0                	jle    5682 <sendm+0x12>
    5692:	45 31 d2             	xor    %r10d,%r10d
    5695:	0f 1f 00             	nopl   (%rax)
    5698:	8b 90 30 01 00 00    	mov    0x130(%rax),%edx
    569e:	44 39 d2             	cmp    %r10d,%edx
    56a1:	74 6c                	je     570f <sendm+0x9f>
    56a3:	48 8b 90 68 01 00 00 	mov    0x168(%rax),%rdx
    56aa:	4c 89 d6             	mov    %r10,%rsi
    56ad:	48 c1 e6 05          	shl    $0x5,%rsi
    56b1:	48 8b 4c 32 08       	mov    0x8(%rdx,%rsi,1),%rcx
    56b6:	48 8b 51 08          	mov    0x8(%rcx),%rdx
    56ba:	4c 63 41 10          	movslq 0x10(%rcx),%r8
    56be:	4c 39 c2             	cmp    %r8,%rdx
    56c1:	7d 4c                	jge    570f <sendm+0x9f>
    56c3:	4c 8b 09             	mov    (%rcx),%r9
    56c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    56d0:	48 8b 90 08 01 00 00 	mov    0x108(%rax),%rdx
    56d7:	48 83 c2 01          	add    $0x1,%rdx
    56db:	48 89 90 08 01 00 00 	mov    %rdx,0x108(%rax)
    56e2:	48 8b 90 68 01 00 00 	mov    0x168(%rax),%rdx
    56e9:	48 83 44 32 10 01    	addq   $0x1,0x10(%rdx,%rsi,1)
    56ef:	48 8b 51 08          	mov    0x8(%rcx),%rdx
    56f3:	48 8d 7a 01          	lea    0x1(%rdx),%rdi
    56f7:	48 89 79 08          	mov    %rdi,0x8(%rcx)
    56fb:	48 8b b8 80 01 00 00 	mov    0x180(%rax),%rdi
    5702:	49 89 3c d1          	mov    %rdi,(%r9,%rdx,8)
    5706:	48 8b 51 08          	mov    0x8(%rcx),%rdx
    570a:	49 39 d0             	cmp    %rdx,%r8
    570d:	7f c1                	jg     56d0 <sendm+0x60>
    570f:	8b 90 34 01 00 00    	mov    0x134(%rax),%edx
    5715:	49 83 c2 01          	add    $0x1,%r10
    5719:	44 39 d2             	cmp    %r10d,%edx
    571c:	0f 8f 76 ff ff ff    	jg     5698 <sendm+0x28>
    5722:	31 c0                	xor    %eax,%eax
    5724:	c3                   	ret
    5725:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005730 <receive>:
    5730:	f3 0f 1e fa          	endbr64
    5734:	8b 97 34 01 00 00    	mov    0x134(%rdi),%edx
    573a:	85 d2                	test   %edx,%edx
    573c:	0f 8e f9 00 00 00    	jle    583b <receive+0x10b>
    5742:	48 89 f8             	mov    %rdi,%rax
    5745:	45 31 db             	xor    %r11d,%r11d
    5748:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5750:	48 8b 90 68 01 00 00 	mov    0x168(%rax),%rdx
    5757:	4c 89 df             	mov    %r11,%rdi
    575a:	48 c1 e7 05          	shl    $0x5,%rdi
    575e:	4c 8b 0c 3a          	mov    (%rdx,%rdi,1),%r9
    5762:	49 8b 51 08          	mov    0x8(%r9),%rdx
    5766:	48 85 d2             	test   %rdx,%rdx
    5769:	0f 8e b1 00 00 00    	jle    5820 <receive+0xf0>
    576f:	4d 8b 11             	mov    (%r9),%r10
    5772:	31 d2                	xor    %edx,%edx
    5774:	eb 1b                	jmp    5791 <receive+0x61>
    5776:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5780:	49 8b 49 08          	mov    0x8(%r9),%rcx
    5784:	48 83 c2 01          	add    $0x1,%rdx
    5788:	48 39 d1             	cmp    %rdx,%rcx
    578b:	0f 8e 8f 00 00 00    	jle    5820 <receive+0xf0>
    5791:	48 8b 88 70 01 00 00 	mov    0x170(%rax),%rcx
    5798:	49 8b 34 d2          	mov    (%r10,%rdx,8),%rsi
    579c:	48 83 c1 01          	add    $0x1,%rcx
    57a0:	4c 8b 46 10          	mov    0x10(%rsi),%r8
    57a4:	48 89 88 70 01 00 00 	mov    %rcx,0x170(%rax)
    57ab:	48 8b 88 08 01 00 00 	mov    0x108(%rax),%rcx
    57b2:	48 83 c1 01          	add    $0x1,%rcx
    57b6:	48 89 88 08 01 00 00 	mov    %rcx,0x108(%rax)
    57bd:	48 8b 88 68 01 00 00 	mov    0x168(%rax),%rcx
    57c4:	48 83 44 39 18 01    	addq   $0x1,0x18(%rcx,%rdi,1)
    57ca:	48 63 08             	movslq (%rax),%rcx
    57cd:	49 39 c8             	cmp    %rcx,%r8
    57d0:	75 ae                	jne    5780 <receive+0x50>
    57d2:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    57d6:	48 63 88 30 01 00 00 	movslq 0x130(%rax),%rcx
    57dd:	48 39 ce             	cmp    %rcx,%rsi
    57e0:	75 9e                	jne    5780 <receive+0x50>
    57e2:	48 83 ec 08          	sub    $0x8,%rsp
    57e6:	48 63 90 30 01 00 00 	movslq 0x130(%rax),%rdx
    57ed:	48 63 00             	movslq (%rax),%rax
    57f0:	31 c9                	xor    %ecx,%ecx
    57f2:	bf 01 00 00 00       	mov    $0x1,%edi
    57f7:	48 39 f2             	cmp    %rsi,%rdx
    57fa:	48 8d 35 57 1c 00 00 	lea    0x1c57(%rip),%rsi        # 7458 <_IO_stdin_used+0x458>
    5801:	0f 94 c1             	sete   %cl
    5804:	31 d2                	xor    %edx,%edx
    5806:	4c 39 c0             	cmp    %r8,%rax
    5809:	0f 94 c2             	sete   %dl
    580c:	31 c0                	xor    %eax,%eax
    580e:	e8 3d cc ff ff       	call   2450 <__printf_chk@plt>
    5813:	bf 01 00 00 00       	mov    $0x1,%edi
    5818:	e8 83 cc ff ff       	call   24a0 <exit@plt>
    581d:	0f 1f 00             	nopl   (%rax)
    5820:	49 c7 41 08 00 00 00 00 	movq   $0x0,0x8(%r9)
    5828:	8b 90 34 01 00 00    	mov    0x134(%rax),%edx
    582e:	49 83 c3 01          	add    $0x1,%r11
    5832:	44 39 da             	cmp    %r11d,%edx
    5835:	0f 8f 15 ff ff ff    	jg     5750 <receive+0x20>
    583b:	c3                   	ret
    583c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005840 <barriered_work>:
    5840:	f3 0f 1e fa          	endbr64
    5844:	41 54                	push   %r12
    5846:	55                   	push   %rbp
    5847:	53                   	push   %rbx
    5848:	8b 97 30 01 00 00    	mov    0x130(%rdi),%edx
    584e:	48 89 fb             	mov    %rdi,%rbx
    5851:	8b 07                	mov    (%rdi),%eax
    5853:	39 c2                	cmp    %eax,%edx
    5855:	0f 84 dd 00 00 00    	je     5938 <barriered_work+0xf8>
    585b:	e8 d0 fe ff ff       	call   5730 <receive>
    5860:	8b 83 40 01 00 00    	mov    0x140(%rbx),%eax
    5866:	83 f8 01             	cmp    $0x1,%eax
    5869:	75 22                	jne    588d <barriered_work+0x4d>
    586b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5870:	48 8b 83 08 01 00 00 	mov    0x108(%rbx),%rax
    5877:	48 83 c0 01          	add    $0x1,%rax
    587b:	48 89 83 08 01 00 00 	mov    %rax,0x108(%rbx)
    5882:	8b 83 40 01 00 00    	mov    0x140(%rbx),%eax
    5888:	83 f8 01             	cmp    $0x1,%eax
    588b:	74 e3                	je     5870 <barriered_work+0x30>
    588d:	8b 83 78 01 00 00    	mov    0x178(%rbx),%eax
    5893:	83 f8 01             	cmp    $0x1,%eax
    5896:	74 0a                	je     58a2 <barriered_work+0x62>
    5898:	0f ae f8             	sfence
    589b:	31 c0                	xor    %eax,%eax
    589d:	5b                   	pop    %rbx
    589e:	5d                   	pop    %rbp
    589f:	41 5c                	pop    %r12
    58a1:	c3                   	ret
    58a2:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    58a8:	85 c0                	test   %eax,%eax
    58aa:	7e ec                	jle    5898 <barriered_work+0x58>
    58ac:	45 31 c9             	xor    %r9d,%r9d
    58af:	90                   	nop
    58b0:	8b 83 30 01 00 00    	mov    0x130(%rbx),%eax
    58b6:	44 39 c8             	cmp    %r9d,%eax
    58b9:	74 64                	je     591f <barriered_work+0xdf>
    58bb:	48 8b 83 68 01 00 00 	mov    0x168(%rbx),%rax
    58c2:	4c 89 c9             	mov    %r9,%rcx
    58c5:	48 c1 e1 05          	shl    $0x5,%rcx
    58c9:	48 8b 54 08 08       	mov    0x8(%rax,%rcx,1),%rdx
    58ce:	48 8b 42 08          	mov    0x8(%rdx),%rax
    58d2:	48 63 7a 10          	movslq 0x10(%rdx),%rdi
    58d6:	48 39 f8             	cmp    %rdi,%rax
    58d9:	7d 44                	jge    591f <barriered_work+0xdf>
    58db:	4c 8b 02             	mov    (%rdx),%r8
    58de:	66 90                	xchg   %ax,%ax
    58e0:	48 8b 83 08 01 00 00 	mov    0x108(%rbx),%rax
    58e7:	48 83 c0 01          	add    $0x1,%rax
    58eb:	48 89 83 08 01 00 00 	mov    %rax,0x108(%rbx)
    58f2:	48 8b 83 68 01 00 00 	mov    0x168(%rbx),%rax
    58f9:	48 83 44 08 10 01    	addq   $0x1,0x10(%rax,%rcx,1)
    58ff:	48 8b 42 08          	mov    0x8(%rdx),%rax
    5903:	48 8d 70 01          	lea    0x1(%rax),%rsi
    5907:	48 89 72 08          	mov    %rsi,0x8(%rdx)
    590b:	48 8b b3 80 01 00 00 	mov    0x180(%rbx),%rsi
    5912:	49 89 34 c0          	mov    %rsi,(%r8,%rax,8)
    5916:	48 8b 42 08          	mov    0x8(%rdx),%rax
    591a:	48 39 f8             	cmp    %rdi,%rax
    591d:	7c c1                	jl     58e0 <barriered_work+0xa0>
    591f:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5925:	49 83 c1 01          	add    $0x1,%r9
    5929:	44 39 c8             	cmp    %r9d,%eax
    592c:	7f 82                	jg     58b0 <barriered_work+0x70>
    592e:	e9 65 ff ff ff       	jmp    5898 <barriered_work+0x58>
    5933:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5938:	e8 f3 fd ff ff       	call   5730 <receive>
    593d:	8b 33                	mov    (%rbx),%esi
    593f:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5945:	85 c0                	test   %eax,%eax
    5947:	0f 8e b5 00 00 00    	jle    5a02 <barriered_work+0x1c2>
    594d:	4c 63 d6             	movslq %esi,%r10
    5950:	45 31 db             	xor    %r11d,%r11d
    5953:	83 c6 01             	add    $0x1,%esi
    5956:	49 c1 e2 09          	shl    $0x9,%r10
    595a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5960:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5966:	4d 89 d8             	mov    %r11,%r8
    5969:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    5971:	31 c9                	xor    %ecx,%ecx
    5973:	49 c1 e0 05          	shl    $0x5,%r8
    5977:	85 c0                	test   %eax,%eax
    5979:	7e 74                	jle    59ef <barriered_work+0x1af>
    597b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5980:	44 8b a3 34 01 00 00 	mov    0x134(%rbx),%r12d
    5987:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    598e:	48 8b 40 40          	mov    0x40(%rax),%rax
    5992:	4a 8b 04 08          	mov    (%rax,%r9,1),%rax
    5996:	48 8b 78 58          	mov    0x58(%rax),%rdi
    599a:	4c 01 d7             	add    %r10,%rdi
    599d:	48 8b bf 68 01 00 00 	mov    0x168(%rdi),%rdi
    59a4:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    59ab:	48 8b 40 40          	mov    0x40(%rax),%rax
    59af:	48 8b 2c c8          	mov    (%rax,%rcx,8),%rbp
    59b3:	89 f0                	mov    %esi,%eax
    59b5:	99                   	cltd
    59b6:	41 f7 fc             	idiv   %r12d
    59b9:	89 d0                	mov    %edx,%eax
    59bb:	f7 d8                	neg    %eax
    59bd:	0f 48 c2             	cmovs  %edx,%eax
    59c0:	48 89 ca             	mov    %rcx,%rdx
    59c3:	48 83 c1 01          	add    $0x1,%rcx
    59c7:	48 c1 e2 05          	shl    $0x5,%rdx
    59cb:	48 98                	cltq
    59cd:	48 8b 54 17 08       	mov    0x8(%rdi,%rdx,1),%rdx
    59d2:	48 c1 e0 09          	shl    $0x9,%rax
    59d6:	48 03 45 58          	add    0x58(%rbp),%rax
    59da:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    59e1:	4a 89 14 00          	mov    %rdx,(%rax,%r8,1)
    59e5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    59eb:	39 c8                	cmp    %ecx,%eax
    59ed:	7f 91                	jg     5980 <barriered_work+0x140>
    59ef:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    59f5:	49 83 c3 01          	add    $0x1,%r11
    59f9:	44 39 d8             	cmp    %r11d,%eax
    59fc:	0f 8f 5e ff ff ff    	jg     5960 <barriered_work+0x120>
    5a02:	0f ae f8             	sfence
    5a05:	48 8b b3 48 01 00 00 	mov    0x148(%rbx),%rsi
    5a0c:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    5a13:	31 ff                	xor    %edi,%edi
    5a15:	48 c1 e0 05          	shl    $0x5,%rax
    5a19:	48 01 c6             	add    %rax,%rsi
    5a1c:	e8 ef c8 ff ff       	call   2310 <clock_gettime@plt>
    5a21:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    5a28:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    5a2f:	8b 70 10             	mov    0x10(%rax),%esi
    5a32:	8d 6e 01             	lea    0x1(%rsi),%ebp
    5a35:	89 68 10             	mov    %ebp,0x10(%rax)
    5a38:	8b 83 40 01 00 00    	mov    0x140(%rbx),%eax
    5a3e:	83 f8 01             	cmp    $0x1,%eax
    5a41:	75 4c                	jne    5a8f <barriered_work+0x24f>
    5a43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5a48:	48 8b 83 08 01 00 00 	mov    0x108(%rbx),%rax
    5a4f:	48 83 c0 01          	add    $0x1,%rax
    5a53:	48 89 83 08 01 00 00 	mov    %rax,0x108(%rbx)
    5a5a:	48 8b 93 20 01 00 00 	mov    0x120(%rbx),%rdx
    5a61:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    5a68:	48 63 83 30 01 00 00 	movslq 0x130(%rbx),%rax
    5a6f:	48 63 3b             	movslq (%rbx),%rdi
    5a72:	48 8b 49 40          	mov    0x40(%rcx),%rcx
    5a76:	48 c1 e7 09          	shl    $0x9,%rdi
    5a7a:	48 8b 04 c1          	mov    (%rcx,%rax,8),%rax
    5a7e:	48 03 78 58          	add    0x58(%rax),%rdi
    5a82:	ff d2                	call   *%rdx
    5a84:	8b 83 40 01 00 00    	mov    0x140(%rbx),%eax
    5a8a:	83 f8 01             	cmp    $0x1,%eax
    5a8d:	74 b9                	je     5a48 <barriered_work+0x208>
    5a8f:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    5a96:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    5a9d:	3b 68 10             	cmp    0x10(%rax),%ebp
    5aa0:	0f 85 f1 00 00 00    	jne    5b97 <barriered_work+0x357>
    5aa6:	48 8b 93 48 01 00 00 	mov    0x148(%rbx),%rdx
    5aad:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    5ab4:	31 ff                	xor    %edi,%edi
    5ab6:	48 c1 e0 05          	shl    $0x5,%rax
    5aba:	48 8d 74 02 10       	lea    0x10(%rdx,%rax,1),%rsi
    5abf:	e8 4c c8 ff ff       	call   2310 <clock_gettime@plt>
    5ac4:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    5acb:	48 8b 8b 50 01 00 00 	mov    0x150(%rbx),%rcx
    5ad2:	48 83 c0 01          	add    $0x1,%rax
    5ad6:	48 99                	cqto
    5ad8:	48 f7 f9             	idiv   %rcx
    5adb:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
    5ae2:	8b 83 78 01 00 00    	mov    0x178(%rbx),%eax
    5ae8:	83 f8 01             	cmp    $0x1,%eax
    5aeb:	0f 85 a7 fd ff ff    	jne    5898 <barriered_work+0x58>
    5af1:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5af7:	85 c0                	test   %eax,%eax
    5af9:	0f 8e 99 fd ff ff    	jle    5898 <barriered_work+0x58>
    5aff:	45 31 c9             	xor    %r9d,%r9d
    5b02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5b08:	8b 83 30 01 00 00    	mov    0x130(%rbx),%eax
    5b0e:	44 39 c8             	cmp    %r9d,%eax
    5b11:	74 6c                	je     5b7f <barriered_work+0x33f>
    5b13:	48 8b 83 68 01 00 00 	mov    0x168(%rbx),%rax
    5b1a:	4c 89 c9             	mov    %r9,%rcx
    5b1d:	48 c1 e1 05          	shl    $0x5,%rcx
    5b21:	48 8b 54 08 08       	mov    0x8(%rax,%rcx,1),%rdx
    5b26:	48 8b 42 08          	mov    0x8(%rdx),%rax
    5b2a:	48 63 7a 10          	movslq 0x10(%rdx),%rdi
    5b2e:	48 39 c7             	cmp    %rax,%rdi
    5b31:	7e 4c                	jle    5b7f <barriered_work+0x33f>
    5b33:	4c 8b 02             	mov    (%rdx),%r8
    5b36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5b40:	48 8b 83 08 01 00 00 	mov    0x108(%rbx),%rax
    5b47:	48 83 c0 01          	add    $0x1,%rax
    5b4b:	48 89 83 08 01 00 00 	mov    %rax,0x108(%rbx)
    5b52:	48 8b 83 68 01 00 00 	mov    0x168(%rbx),%rax
    5b59:	48 83 44 08 10 01    	addq   $0x1,0x10(%rax,%rcx,1)
    5b5f:	48 8b 42 08          	mov    0x8(%rdx),%rax
    5b63:	48 8d 70 01          	lea    0x1(%rax),%rsi
    5b67:	48 89 72 08          	mov    %rsi,0x8(%rdx)
    5b6b:	48 8b b3 80 01 00 00 	mov    0x180(%rbx),%rsi
    5b72:	49 89 34 c0          	mov    %rsi,(%r8,%rax,8)
    5b76:	48 8b 42 08          	mov    0x8(%rdx),%rax
    5b7a:	48 39 f8             	cmp    %rdi,%rax
    5b7d:	7c c1                	jl     5b40 <barriered_work+0x300>
    5b7f:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5b85:	49 83 c1 01          	add    $0x1,%r9
    5b89:	44 39 c8             	cmp    %r9d,%eax
    5b8c:	0f 8f 76 ff ff ff    	jg     5b08 <barriered_work+0x2c8>
    5b92:	e9 01 fd ff ff       	jmp    5898 <barriered_work+0x58>
    5b97:	48 8d 3d 66 16 00 00 	lea    0x1666(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5b9e:	e8 4d c7 ff ff       	call   22f0 <puts@plt>
    5ba3:	e9 fe fe ff ff       	jmp    5aa6 <barriered_work+0x266>
    5ba8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000005bb0 <barriered_work_ingest>:
    5bb0:	f3 0f 1e fa          	endbr64
    5bb4:	48 83 ec 08          	sub    $0x8,%rsp
    5bb8:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5bbf:	48 8b 80 c0 00 00 00 	mov    0xc0(%rax),%rax
    5bc6:	8b 00                	mov    (%rax),%eax
    5bc8:	85 c0                	test   %eax,%eax
    5bca:	7e 69                	jle    5c35 <barriered_work_ingest+0x85>
    5bcc:	31 c0                	xor    %eax,%eax
    5bce:	66 90                	xchg   %ax,%ax
    5bd0:	48 8b 8f 28 01 00 00 	mov    0x128(%rdi),%rcx
    5bd7:	48 89 c2             	mov    %rax,%rdx
    5bda:	48 c1 e2 04          	shl    $0x4,%rdx
    5bde:	48 8b 89 c0 00 00 00 	mov    0xc0(%rcx),%rcx
    5be5:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    5be9:	48 01 d6             	add    %rdx,%rsi
    5bec:	8b 4e 08             	mov    0x8(%rsi),%ecx
    5bef:	83 f9 01             	cmp    $0x1,%ecx
    5bf2:	75 2b                	jne    5c1f <barriered_work_ingest+0x6f>
    5bf4:	48 8b 8f 60 01 00 00 	mov    0x160(%rdi),%rcx
    5bfb:	48 83 c1 01          	add    $0x1,%rcx
    5bff:	48 89 8f 60 01 00 00 	mov    %rcx,0x160(%rdi)
    5c06:	48 8b 8f 28 01 00 00 	mov    0x128(%rdi),%rcx
    5c0d:	48 8b 89 c0 00 00 00 	mov    0xc0(%rcx),%rcx
    5c14:	48 03 51 08          	add    0x8(%rcx),%rdx
    5c18:	c7 42 08 00 00 00 00 	movl   $0x0,0x8(%rdx)
    5c1f:	48 8b 97 28 01 00 00 	mov    0x128(%rdi),%rdx
    5c26:	48 83 c0 01          	add    $0x1,%rax
    5c2a:	48 8b 92 c0 00 00 00 	mov    0xc0(%rdx),%rdx
    5c31:	39 02                	cmp    %eax,(%rdx)
    5c33:	7f 9b                	jg     5bd0 <barriered_work_ingest+0x20>
    5c35:	0f ae f8             	sfence
    5c38:	e8 03 fc ff ff       	call   5840 <barriered_work>
    5c3d:	31 c0                	xor    %eax,%eax
    5c3f:	48 83 c4 08          	add    $0x8,%rsp
    5c43:	c3                   	ret
    5c44:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5c4f:	90                   	nop

0000000000005c50 <barriered_nulltask>:
    5c50:	f3 0f 1e fa          	endbr64
    5c54:	31 c0                	xor    %eax,%eax
    5c56:	c3                   	ret
    5c57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005c60 <barriered_steal>:
    5c60:	f3 0f 1e fa          	endbr64
    5c64:	31 c0                	xor    %eax,%eax
    5c66:	c3                   	ret
    5c67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005c70 <after>:
    5c70:	f3 0f 1e fa          	endbr64
    5c74:	31 c0                	xor    %eax,%eax
    5c76:	48 39 d7             	cmp    %rdx,%rdi
    5c79:	7e 08                	jle    5c83 <after+0x13>
    5c7b:	31 c0                	xor    %eax,%eax
    5c7d:	48 39 ce             	cmp    %rcx,%rsi
    5c80:	0f 9f c0             	setg   %al
    5c83:	c3                   	ret
    5c84:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5c8f:	90                   	nop

0000000000005c90 <within>:
    5c90:	f3 0f 1e fa          	endbr64
    5c94:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5c99:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    5c9e:	31 c0                	xor    %eax,%eax
    5ca0:	48 39 d7             	cmp    %rdx,%rdi
    5ca3:	7f 18                	jg     5cbd <within+0x2d>
    5ca5:	4d 39 d8             	cmp    %r11,%r8
    5ca8:	0f 9e c2             	setle  %dl
    5cab:	48 39 ce             	cmp    %rcx,%rsi
    5cae:	0f 9e c0             	setle  %al
    5cb1:	21 c2                	and    %eax,%edx
    5cb3:	31 c0                	xor    %eax,%eax
    5cb5:	4d 39 d1             	cmp    %r10,%r9
    5cb8:	0f 9e c0             	setle  %al
    5cbb:	21 d0                	and    %edx,%eax
    5cbd:	c3                   	ret
    5cbe:	66 90                	xchg   %ax,%ax

0000000000005cc0 <overlap>:
    5cc0:	f3 0f 1e fa          	endbr64
    5cc4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5cc9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5cce:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    5cd3:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    5cd8:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
    5cdd:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    5ce2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5ce7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    5cec:	48 39 fe             	cmp    %rdi,%rsi
    5cef:	7d 2f                	jge    5d20 <overlap+0x60>
    5cf1:	48 39 ca             	cmp    %rcx,%rdx
    5cf4:	7d 62                	jge    5d58 <overlap+0x98>
    5cf6:	4d 39 da             	cmp    %r11,%r10
    5cf9:	7e 0e                	jle    5d09 <overlap+0x49>
    5cfb:	b8 01 00 00 00       	mov    $0x1,%eax
    5d00:	4d 39 c1             	cmp    %r8,%r9
    5d03:	0f 8f 7f 00 00 00    	jg     5d88 <overlap+0xc8>
    5d09:	31 c0                	xor    %eax,%eax
    5d0b:	4d 39 c1             	cmp    %r8,%r9
    5d0e:	7c 4c                	jl     5d5c <overlap+0x9c>
    5d10:	31 c0                	xor    %eax,%eax
    5d12:	4d 39 da             	cmp    %r11,%r10
    5d15:	0f 9d c0             	setge  %al
    5d18:	c3                   	ret
    5d19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5d20:	7e 4e                	jle    5d70 <overlap+0xb0>
    5d22:	48 39 ca             	cmp    %rcx,%rdx
    5d25:	7f 39                	jg     5d60 <overlap+0xa0>
    5d27:	75 31                	jne    5d5a <overlap+0x9a>
    5d29:	4d 39 c1             	cmp    %r8,%r9
    5d2c:	7f 2c                	jg     5d5a <overlap+0x9a>
    5d2e:	b8 01 00 00 00       	mov    $0x1,%eax
    5d33:	4d 39 da             	cmp    %r11,%r10
    5d36:	7e 24                	jle    5d5c <overlap+0x9c>
    5d38:	48 39 ca             	cmp    %rcx,%rdx
    5d3b:	0f 94 c2             	sete   %dl
    5d3e:	48 39 fe             	cmp    %rdi,%rsi
    5d41:	0f 94 c0             	sete   %al
    5d44:	21 c2                	and    %eax,%edx
    5d46:	31 c0                	xor    %eax,%eax
    5d48:	4d 39 c1             	cmp    %r8,%r9
    5d4b:	0f 94 c0             	sete   %al
    5d4e:	21 d0                	and    %edx,%eax
    5d50:	c3                   	ret
    5d51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5d58:	74 af                	je     5d09 <overlap+0x49>
    5d5a:	31 c0                	xor    %eax,%eax
    5d5c:	c3                   	ret
    5d5d:	0f 1f 00             	nopl   (%rax)
    5d60:	4d 39 c1             	cmp    %r8,%r9
    5d63:	7d c4                	jge    5d29 <overlap+0x69>
    5d65:	b8 01 00 00 00       	mov    $0x1,%eax
    5d6a:	4d 39 da             	cmp    %r11,%r10
    5d6d:	7d ba                	jge    5d29 <overlap+0x69>
    5d6f:	c3                   	ret
    5d70:	48 39 ca             	cmp    %rcx,%rdx
    5d73:	7c 94                	jl     5d09 <overlap+0x49>
    5d75:	4d 39 c1             	cmp    %r8,%r9
    5d78:	7e b4                	jle    5d2e <overlap+0x6e>
    5d7a:	48 39 ca             	cmp    %rcx,%rdx
    5d7d:	74 91                	je     5d10 <overlap+0x50>
    5d7f:	eb d9                	jmp    5d5a <overlap+0x9a>
    5d81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5d88:	c3                   	ret
    5d89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005d90 <verify>:
    5d90:	f3 0f 1e fa          	endbr64
    5d94:	85 f6                	test   %esi,%esi
    5d96:	0f 8e 2b 03 00 00    	jle    60c7 <verify+0x337>
    5d9c:	41 57                	push   %r15
    5d9e:	41 56                	push   %r14
    5da0:	45 31 f6             	xor    %r14d,%r14d
    5da3:	41 55                	push   %r13
    5da5:	4c 8d 6f 58          	lea    0x58(%rdi),%r13
    5da9:	41 54                	push   %r12
    5dab:	41 89 f4             	mov    %esi,%r12d
    5dae:	55                   	push   %rbp
    5daf:	53                   	push   %rbx
    5db0:	48 83 ec 48          	sub    $0x48,%rsp
    5db4:	4c 89 6c 24 08       	mov    %r13,0x8(%rsp)
    5db9:	4c 89 2c 24          	mov    %r13,(%rsp)
    5dbd:	31 ed                	xor    %ebp,%ebp
    5dbf:	4d 89 ef             	mov    %r13,%r15
    5dc2:	41 39 ee             	cmp    %ebp,%r14d
    5dc5:	0f 84 5a 02 00 00    	je     6025 <verify+0x295>
    5dcb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5dd0:	8b 50 08             	mov    0x8(%rax),%edx
    5dd3:	85 d2                	test   %edx,%edx
    5dd5:	0f 8e 4a 02 00 00    	jle    6025 <verify+0x295>
    5ddb:	89 6c 24 24          	mov    %ebp,0x24(%rsp)
    5ddf:	31 db                	xor    %ebx,%ebx
    5de1:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    5de6:	44 89 f2             	mov    %r14d,%edx
    5de9:	48 8d 35 24 14 00 00 	lea    0x1424(%rip),%rsi        # 7214 <_IO_stdin_used+0x214>
    5df0:	bf 01 00 00 00       	mov    $0x1,%edi
    5df5:	31 c0                	xor    %eax,%eax
    5df7:	e8 54 c6 ff ff       	call   2450 <__printf_chk@plt>
    5dfc:	48 8b 04 24          	mov    (%rsp),%rax
    5e00:	8b 40 08             	mov    0x8(%rax),%eax
    5e03:	85 c0                	test   %eax,%eax
    5e05:	0f 8e ff 01 00 00    	jle    600a <verify+0x27a>
    5e0b:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5e10:	48 89 d8             	mov    %rbx,%rax
    5e13:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    5e18:	45 31 e4             	xor    %r12d,%r12d
    5e1b:	48 c1 e0 09          	shl    $0x9,%rax
    5e1f:	44 89 74 24 34       	mov    %r14d,0x34(%rsp)
    5e24:	4c 89 7c 24 38       	mov    %r15,0x38(%rsp)
    5e29:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5e2e:	48 03 07             	add    (%rdi),%rax
    5e31:	49 89 c5             	mov    %rax,%r13
    5e34:	0f 1f 40 00          	nopl   0x0(%rax)
    5e38:	48 8b 1c 24          	mov    (%rsp),%rbx
    5e3c:	4c 89 e5             	mov    %r12,%rbp
    5e3f:	49 8b 8d 58 01 00 00 	mov    0x158(%r13),%rcx
    5e46:	48 8d 35 dc 13 00 00 	lea    0x13dc(%rip),%rsi        # 7229 <_IO_stdin_used+0x229>
    5e4d:	48 c1 e5 09          	shl    $0x9,%rbp
    5e51:	bf 01 00 00 00       	mov    $0x1,%edi
    5e56:	48 8b 03             	mov    (%rbx),%rax
    5e59:	48 01 e8             	add    %rbp,%rax
    5e5c:	48 8b 90 58 01 00 00 	mov    0x158(%rax),%rdx
    5e63:	31 c0                	xor    %eax,%eax
    5e65:	e8 e6 c5 ff ff       	call   2450 <__printf_chk@plt>
    5e6a:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5e6f:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    5e74:	4c 03 28             	add    (%rax),%r13
    5e77:	49 8b 85 58 01 00 00 	mov    0x158(%r13),%rax
    5e7e:	48 85 c0             	test   %rax,%rax
    5e81:	0f 8e 62 01 00 00    	jle    5fe9 <verify+0x259>
    5e87:	48 8b 13             	mov    (%rbx),%rdx
    5e8a:	4c 89 64 24 18       	mov    %r12,0x18(%rsp)
    5e8f:	45 31 ff             	xor    %r15d,%r15d
    5e92:	48 01 ea             	add    %rbp,%rdx
    5e95:	0f 1f 00             	nopl   (%rax)
    5e98:	48 8b 82 58 01 00 00 	mov    0x158(%rdx),%rax
    5e9f:	4d 89 fc             	mov    %r15,%r12
    5ea2:	31 db                	xor    %ebx,%ebx
    5ea4:	49 c1 e4 05          	shl    $0x5,%r12
    5ea8:	48 85 c0             	test   %rax,%rax
    5eab:	7f 47                	jg     5ef4 <verify+0x164>
    5ead:	e9 1e 01 00 00       	jmp    5fd0 <verify+0x240>
    5eb2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5eb8:	48 39 f1             	cmp    %rsi,%rcx
    5ebb:	0f 8d 7f 01 00 00    	jge    6040 <verify+0x2b0>
    5ec1:	4d 39 da             	cmp    %r11,%r10
    5ec4:	7e 09                	jle    5ecf <verify+0x13f>
    5ec6:	49 39 c6             	cmp    %rax,%r14
    5ec9:	0f 8c 91 00 00 00    	jl     5f60 <verify+0x1d0>
    5ecf:	4d 39 da             	cmp    %r11,%r10
    5ed2:	0f 8d b3 01 00 00    	jge    608b <verify+0x2fb>
    5ed8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5ee0:	48 8b 82 58 01 00 00 	mov    0x158(%rdx),%rax
    5ee7:	48 83 c3 01          	add    $0x1,%rbx
    5eeb:	48 39 d8             	cmp    %rbx,%rax
    5eee:	0f 8e dc 00 00 00    	jle    5fd0 <verify+0x240>
    5ef4:	48 8b 82 48 01 00 00 	mov    0x148(%rdx),%rax
    5efb:	49 89 d9             	mov    %rbx,%r9
    5efe:	49 8b 8d 48 01 00 00 	mov    0x148(%r13),%rcx
    5f05:	49 c1 e1 05          	shl    $0x5,%r9
    5f09:	4c 01 e1             	add    %r12,%rcx
    5f0c:	4c 01 c8             	add    %r9,%rax
    5f0f:	4c 8b 01             	mov    (%rcx),%r8
    5f12:	48 8b 38             	mov    (%rax),%rdi
    5f15:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    5f19:	4c 8b 59 10          	mov    0x10(%rcx),%r11
    5f1d:	4c 8b 71 18          	mov    0x18(%rcx),%r14
    5f21:	4c 8b 50 10          	mov    0x10(%rax),%r10
    5f25:	48 8b 48 08          	mov    0x8(%rax),%rcx
    5f29:	48 8b 40 18          	mov    0x18(%rax),%rax
    5f2d:	4c 39 c7             	cmp    %r8,%rdi
    5f30:	7c 86                	jl     5eb8 <verify+0x128>
    5f32:	0f 8e 38 01 00 00    	jle    6070 <verify+0x2e0>
    5f38:	48 39 f1             	cmp    %rsi,%rcx
    5f3b:	0f 8f 0f 01 00 00    	jg     6050 <verify+0x2c0>
    5f41:	75 9d                	jne    5ee0 <verify+0x150>
    5f43:	4d 39 da             	cmp    %r11,%r10
    5f46:	7f 98                	jg     5ee0 <verify+0x150>
    5f48:	49 39 c6             	cmp    %rax,%r14
    5f4b:	7d 13                	jge    5f60 <verify+0x1d0>
    5f4d:	4c 39 c7             	cmp    %r8,%rdi
    5f50:	75 8e                	jne    5ee0 <verify+0x150>
    5f52:	48 39 f1             	cmp    %rsi,%rcx
    5f55:	75 89                	jne    5ee0 <verify+0x150>
    5f57:	4d 39 da             	cmp    %r11,%r10
    5f5a:	75 84                	jne    5ee0 <verify+0x150>
    5f5c:	0f 1f 40 00          	nopl   0x0(%rax)
    5f60:	48 8b b2 48 01 00 00 	mov    0x148(%rdx),%rsi
    5f67:	bf 01 00 00 00       	mov    $0x1,%edi
    5f6c:	48 83 c3 01          	add    $0x1,%rbx
    5f70:	49 8b 85 48 01 00 00 	mov    0x148(%r13),%rax
    5f77:	48 8b 8a 48 01 00 00 	mov    0x148(%rdx),%rcx
    5f7e:	49 8b 95 48 01 00 00 	mov    0x148(%r13),%rdx
    5f85:	4e 8b 44 20 08       	mov    0x8(%rax,%r12,1),%r8
    5f8a:	31 c0                	xor    %eax,%eax
    5f8c:	4a 8b 4c 09 10       	mov    0x10(%rcx,%r9,1),%rcx
    5f91:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    5f95:	4e 8b 4c 0e 18       	mov    0x18(%rsi,%r9,1),%r9
    5f9a:	48 8d 35 df 14 00 00 	lea    0x14df(%rip),%rsi        # 7480 <_IO_stdin_used+0x480>
    5fa1:	e8 aa c4 ff ff       	call   2450 <__printf_chk@plt>
    5fa6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5fab:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    5fb0:	4c 03 28             	add    (%rax),%r13
    5fb3:	48 8b 04 24          	mov    (%rsp),%rax
    5fb7:	48 8b 10             	mov    (%rax),%rdx
    5fba:	48 01 ea             	add    %rbp,%rdx
    5fbd:	48 8b 82 58 01 00 00 	mov    0x158(%rdx),%rax
    5fc4:	48 39 d8             	cmp    %rbx,%rax
    5fc7:	0f 8f 27 ff ff ff    	jg     5ef4 <verify+0x164>
    5fcd:	0f 1f 00             	nopl   (%rax)
    5fd0:	49 8b 85 58 01 00 00 	mov    0x158(%r13),%rax
    5fd7:	49 83 c7 01          	add    $0x1,%r15
    5fdb:	4c 39 f8             	cmp    %r15,%rax
    5fde:	0f 8f b4 fe ff ff    	jg     5e98 <verify+0x108>
    5fe4:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    5fe9:	48 8b 04 24          	mov    (%rsp),%rax
    5fed:	49 83 c4 01          	add    $0x1,%r12
    5ff1:	44 39 60 08          	cmp    %r12d,0x8(%rax)
    5ff5:	0f 8f 3d fe ff ff    	jg     5e38 <verify+0xa8>
    5ffb:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    6000:	44 8b 74 24 34       	mov    0x34(%rsp),%r14d
    6005:	4c 8b 7c 24 38       	mov    0x38(%rsp),%r15
    600a:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    600f:	48 83 c3 01          	add    $0x1,%rbx
    6013:	39 58 08             	cmp    %ebx,0x8(%rax)
    6016:	0f 8f ca fd ff ff    	jg     5de6 <verify+0x56>
    601c:	8b 6c 24 24          	mov    0x24(%rsp),%ebp
    6020:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    6025:	8d 45 01             	lea    0x1(%rbp),%eax
    6028:	48 81 04 24 40 01 00 00 	addq   $0x140,(%rsp)
    6030:	41 39 c4             	cmp    %eax,%r12d
    6033:	74 64                	je     6099 <verify+0x309>
    6035:	89 c5                	mov    %eax,%ebp
    6037:	e9 86 fd ff ff       	jmp    5dc2 <verify+0x32>
    603c:	0f 1f 40 00          	nopl   0x0(%rax)
    6040:	0f 85 9a fe ff ff    	jne    5ee0 <verify+0x150>
    6046:	e9 84 fe ff ff       	jmp    5ecf <verify+0x13f>
    604b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6050:	49 39 c6             	cmp    %rax,%r14
    6053:	0f 8e ea fe ff ff    	jle    5f43 <verify+0x1b3>
    6059:	4d 39 da             	cmp    %r11,%r10
    605c:	0f 8d e1 fe ff ff    	jge    5f43 <verify+0x1b3>
    6062:	e9 f9 fe ff ff       	jmp    5f60 <verify+0x1d0>
    6067:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    6070:	48 39 f1             	cmp    %rsi,%rcx
    6073:	0f 8c 56 fe ff ff    	jl     5ecf <verify+0x13f>
    6079:	4d 39 da             	cmp    %r11,%r10
    607c:	0f 8e c6 fe ff ff    	jle    5f48 <verify+0x1b8>
    6082:	48 39 f1             	cmp    %rsi,%rcx
    6085:	0f 85 55 fe ff ff    	jne    5ee0 <verify+0x150>
    608b:	49 39 c6             	cmp    %rax,%r14
    608e:	0f 8f 4c fe ff ff    	jg     5ee0 <verify+0x150>
    6094:	e9 c7 fe ff ff       	jmp    5f60 <verify+0x1d0>
    6099:	48 81 44 24 08 40 01 00 00 	addq   $0x140,0x8(%rsp)
    60a2:	4d 89 fd             	mov    %r15,%r13
    60a5:	41 8d 46 01          	lea    0x1(%r14),%eax
    60a9:	41 39 ee             	cmp    %ebp,%r14d
    60ac:	74 08                	je     60b6 <verify+0x326>
    60ae:	41 89 c6             	mov    %eax,%r14d
    60b1:	e9 03 fd ff ff       	jmp    5db9 <verify+0x29>
    60b6:	48 83 c4 48          	add    $0x48,%rsp
    60ba:	31 c0                	xor    %eax,%eax
    60bc:	5b                   	pop    %rbx
    60bd:	5d                   	pop    %rbp
    60be:	41 5c                	pop    %r12
    60c0:	41 5d                	pop    %r13
    60c2:	41 5e                	pop    %r14
    60c4:	41 5f                	pop    %r15
    60c6:	c3                   	ret
    60c7:	31 c0                	xor    %eax,%eax
    60c9:	c3                   	ret

Disassembly of section .fini:

00000000000060cc <_fini>:
    60cc:	f3 0f 1e fa          	endbr64
    60d0:	48 83 ec 08          	sub    $0x8,%rsp
    60d4:	48 83 c4 08          	add    $0x8,%rsp
    60d8:	c3                   	ret
