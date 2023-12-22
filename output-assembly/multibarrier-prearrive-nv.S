
multibarrier-prearrive-nv:     file format elf64-x86-64


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
    2556:	48 8d 3d a2 4c 00 00 	lea    0x4ca2(%rip),%rdi        # 71ff <_IO_stdin_used+0x1ff>
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
    2596:	48 8d 3d 32 4c 00 00 	lea    0x4c32(%rip),%rdi        # 71cf <_IO_stdin_used+0x1cf>
    259d:	e8 9e ff ff ff       	call   2540 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    25a2:	48 8d 3d aa 4b 00 00 	lea    0x4baa(%rip),%rdi        # 7153 <_IO_stdin_used+0x153>
    25a9:	e8 92 ff ff ff       	call   2540 <fatal_error>
    fatal_error("listen()");
    25ae:	48 8d 3d be 4b 00 00 	lea    0x4bbe(%rip),%rdi        # 7173 <_IO_stdin_used+0x173>
    25b5:	e8 86 ff ff ff       	call   2540 <fatal_error>
    25ba:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25c2:	0f 0b                	ud2
    25c4:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25cc:	0f 0b                	ud2
      fatal_error("socket()");
    25ce:	48 8d 3d 75 4b 00 00 	lea    0x4b75(%rip),%rdi        # 714a <_IO_stdin_used+0x14a>
    25d5:	e8 66 ff ff ff       	call   2540 <fatal_error>
      fatal_error("bind()");
    25da:	48 8d 3d 8b 4b 00 00 	lea    0x4b8b(%rip),%rdi        # 716c <_IO_stdin_used+0x16c>
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
    25f6:	48 8d 3d bb 4e 00 00 	lea    0x4ebb(%rip),%rdi        # 74b8 <_IO_stdin_used+0x4b8>
    25fd:	41 56                	push   %r14
    25ff:	41 55                	push   %r13
    2601:	41 54                	push   %r12
    2603:	55                   	push   %rbp
    2604:	53                   	push   %rbx
    2605:	48 83 ec 78          	sub    $0x78,%rsp
    2609:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2612:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    2617:	48 8d 05 d2 10 00 00 	lea    0x10d2(%rip),%rax        # 36f0 <barriered_reset>
    261e:	66 48 0f 6e e8       	movq   %rax,%xmm5
    2623:	0f 16 2d 4e 76 00 00 	movhps 0x764e(%rip),%xmm5        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    262a:	0f 29 6c 24 40       	movaps %xmm5,0x40(%rsp)
    262f:	e8 bc fc ff ff       	call   22f0 <puts@plt>
    2634:	bf 0a 00 00 00       	mov    $0xa,%edi
    2639:	e8 92 fc ff ff       	call   22d0 <putchar@plt>
    263e:	48 8d 3d f9 4b 00 00 	lea    0x4bf9(%rip),%rdi        # 723e <_IO_stdin_used+0x23e>
    2645:	e8 a6 fc ff ff       	call   22f0 <puts@plt>
    264a:	ba 02 00 00 00       	mov    $0x2,%edx
    264f:	48 8d 35 04 4c 00 00 	lea    0x4c04(%rip),%rsi        # 725a <_IO_stdin_used+0x25a>
    2656:	31 c0                	xor    %eax,%eax
    2658:	bf 01 00 00 00       	mov    $0x1,%edi
    265d:	e8 ee fd ff ff       	call   2450 <__printf_chk@plt>
    2662:	ba 06 00 00 00       	mov    $0x6,%edx
    2667:	48 8d 35 06 4c 00 00 	lea    0x4c06(%rip),%rsi        # 7274 <_IO_stdin_used+0x274>
    266e:	31 c0                	xor    %eax,%eax
    2670:	bf 01 00 00 00       	mov    $0x1,%edi
    2675:	e8 d6 fd ff ff       	call   2450 <__printf_chk@plt>
    267a:	ba 01 00 00 00       	mov    $0x1,%edx
    267f:	48 8d 35 02 4c 00 00 	lea    0x4c02(%rip),%rsi        # 7288 <_IO_stdin_used+0x288>
    2686:	31 c0                	xor    %eax,%eax
    2688:	bf 01 00 00 00       	mov    $0x1,%edi
    268d:	e8 be fd ff ff       	call   2450 <__printf_chk@plt>
    2692:	ba 01 00 00 00       	mov    $0x1,%edx
    2697:	48 8d 35 fb 4b 00 00 	lea    0x4bfb(%rip),%rsi        # 7299 <_IO_stdin_used+0x299>
    269e:	31 c0                	xor    %eax,%eax
    26a0:	bf 01 00 00 00       	mov    $0x1,%edi
    26a5:	e8 a6 fd ff ff       	call   2450 <__printf_chk@plt>
    26aa:	ba 02 00 00 00       	mov    $0x2,%edx
    26af:	48 8d 35 fb 4b 00 00 	lea    0x4bfb(%rip),%rsi        # 72b1 <_IO_stdin_used+0x2b1>
    26b6:	31 c0                	xor    %eax,%eax
    26b8:	bf 01 00 00 00       	mov    $0x1,%edi
    26bd:	e8 8e fd ff ff       	call   2450 <__printf_chk@plt>
    26c2:	ba 01 00 00 00       	mov    $0x1,%edx
    26c7:	48 8d 35 52 4e 00 00 	lea    0x4e52(%rip),%rsi        # 7520 <_IO_stdin_used+0x520>
    26ce:	31 c0                	xor    %eax,%eax
    26d0:	bf 01 00 00 00       	mov    $0x1,%edi
    26d5:	e8 76 fd ff ff       	call   2450 <__printf_chk@plt>
    26da:	ba 01 00 00 00       	mov    $0x1,%edx
    26df:	48 8d 35 6a 4e 00 00 	lea    0x4e6a(%rip),%rsi        # 7550 <_IO_stdin_used+0x550>
    26e6:	31 c0                	xor    %eax,%eax
    26e8:	bf 01 00 00 00       	mov    $0x1,%edi
    26ed:	e8 5e fd ff ff       	call   2450 <__printf_chk@plt>
    26f2:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    26f7:	48 8d 35 cf 4b 00 00 	lea    0x4bcf(%rip),%rsi        # 72cd <_IO_stdin_used+0x2cd>
    26fe:	31 c0                	xor    %eax,%eax
    2700:	bf 01 00 00 00       	mov    $0x1,%edi
    2705:	e8 46 fd ff ff       	call   2450 <__printf_chk@plt>
    270a:	ba 05 00 00 00       	mov    $0x5,%edx
    270f:	48 8d 35 d1 4b 00 00 	lea    0x4bd1(%rip),%rsi        # 72e7 <_IO_stdin_used+0x2e7>
    2716:	31 c0                	xor    %eax,%eax
    2718:	bf 01 00 00 00       	mov    $0x1,%edi
    271d:	e8 2e fd ff ff       	call   2450 <__printf_chk@plt>
    2722:	48 8d 3d a5 49 00 00 	lea    0x49a5(%rip),%rdi        # 70ce <_IO_stdin_used+0xce>
    2729:	e8 c2 fb ff ff       	call   22f0 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    272e:	be 18 00 00 00       	mov    $0x18,%esi
    2733:	bf 02 00 00 00       	mov    $0x2,%edi
    2738:	e8 63 fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    273d:	be b0 00 00 00       	mov    $0xb0,%esi
    2742:	bf 06 00 00 00       	mov    $0x6,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    2747:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    274c:	e8 4f fc ff ff       	call   23a0 <calloc@plt>
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  int buffers_required = thread_count * barrier_count;
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2751:	be 10 00 00 00       	mov    $0x10,%esi
    2756:	bf 04 00 00 00       	mov    $0x4,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    275b:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2760:	e8 3b fc ff ff       	call   23a0 <calloc@plt>
    2765:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  int snapshot_limit = 10;
  for (int x = 0 ; x < buffers_required; x++) {
    276a:	49 89 c4             	mov    %rax,%r12
    276d:	48 8d 68 40          	lea    0x40(%rax),%rbp
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2771:	be 20 00 00 00       	mov    $0x20,%esi
    buffers[x].count = buffer_size;
    2776:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    277e:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2783:	49 83 c4 10          	add    $0x10,%r12
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2787:	e8 14 fc ff ff       	call   23a0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    278c:	be 20 00 00 00       	mov    $0x20,%esi
    2791:	bf 0a 00 00 00       	mov    $0xa,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2796:	49 89 44 24 f8       	mov    %rax,-0x8(%r12)
    279b:	48 89 c3             	mov    %rax,%rbx
      buffers[x].buffer[y].available = 0;
    279e:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    27a5:	c7 40 18 0a 00 00 00 	movl   $0xa,0x18(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    27ac:	e8 ef fb ff ff       	call   23a0 <calloc@plt>
    27b1:	48 89 43 10          	mov    %rax,0x10(%rbx)
  for (int x = 0 ; x < buffers_required; x++) {
    27b5:	4c 39 e5             	cmp    %r12,%rbp
    27b8:	75 b7                	jne    2771 <main+0x181>
    27ba:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
  }
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  for (int x = 0 ; x < total_threads ; x++) {
    27bf:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
  int curcpu = 0;
    27c7:	c7 44 24 50 00 00 00 00 	movl   $0x0,0x50(%rsp)
    27cf:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
  int external_thread_index = 0;
    27d4:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
    27dc:	4c 8d 60 e8          	lea    -0x18(%rax),%r12
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27e0:	be 08 00 00 00       	mov    $0x8,%esi
    27e5:	bf 02 00 00 00       	mov    $0x2,%edi
    27ea:	e8 b1 fb ff ff       	call   23a0 <calloc@plt>
    int other = -1;
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27ef:	be 80 00 00 00       	mov    $0x80,%esi
    27f4:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27f9:	48 89 c3             	mov    %rax,%rbx
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27fc:	e8 9f fb ff ff       	call   23a0 <calloc@plt>
    CPU_ZERO(sendercpu);
    if (x % 2 == 1) {
    2801:	8b 74 24 20          	mov    0x20(%rsp),%esi
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2805:	48 89 c5             	mov    %rax,%rbp
    if (x % 2 == 1) {
    2808:	89 f0                	mov    %esi,%eax
    280a:	89 34 24             	mov    %esi,(%rsp)
    280d:	89 f7                	mov    %esi,%edi
      my_thread_data[1] = &thread_data[x]; 
      printf("odd %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
      thread_data[x].protected_state = &protected_state[other];
    } else {
      thread_data[x].thread_index = 0;
      other = (x + 1) % total_threads;
    280f:	83 c6 01             	add    $0x1,%esi
    if (x % 2 == 1) {
    2812:	83 e0 01             	and    $0x1,%eax
      other = (x + 1) % total_threads;
    2815:	89 74 24 20          	mov    %esi,0x20(%rsp)
    if (x % 2 == 1) {
    2819:	85 c0                	test   %eax,%eax
    281b:	0f 84 af 0b 00 00    	je     33d0 <main+0xde0>
      my_thread_data[0] = &thread_data[other]; 
    2821:	49 8d 8e 50 ff ff ff 	lea    -0xb0(%r14),%rcx
      my_thread_data[1] = &thread_data[x]; 
    2828:	4c 89 73 08          	mov    %r14,0x8(%rbx)
    282c:	89 fa                	mov    %edi,%edx
    282e:	4d 89 f0             	mov    %r14,%r8
      my_thread_data[0] = &thread_data[other]; 
    2831:	48 89 0b             	mov    %rcx,(%rbx)
      other = abs(x - 1) % total_threads;
    2834:	44 8d 7f ff          	lea    -0x1(%rdi),%r15d
    2838:	48 8d 35 bc 4a 00 00 	lea    0x4abc(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
    283f:	31 c0                	xor    %eax,%eax
      thread_data[x].thread_index = 1;
    2841:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
    2848:	bf 01 00 00 00       	mov    $0x1,%edi
    284d:	e8 fe fb ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    2852:	49 8d 7c 24 18       	lea    0x18(%r12),%rdi
    2857:	4c 89 e0             	mov    %r12,%rax
    285a:	48 89 7c 24 30       	mov    %rdi,0x30(%rsp)
    285f:	44 8b 24 24          	mov    (%rsp),%r12d
    2863:	49 89 46 38          	mov    %rax,0x38(%r14)
    2867:	44 89 f9             	mov    %r15d,%ecx
    286a:	bf 01 00 00 00       	mov    $0x1,%edi
    286f:	45 8b 06             	mov    (%r14),%r8d
    2872:	48 8d 35 ff 4c 00 00 	lea    0x4cff(%rip),%rsi        # 7578 <_IO_stdin_used+0x578>
    2879:	31 c0                	xor    %eax,%eax
    287b:	44 89 e2             	mov    %r12d,%edx
    287e:	e8 cd fb ff ff       	call   2450 <__printf_chk@plt>
    2883:	8b 4c 24 50          	mov    0x50(%rsp),%ecx
    2887:	31 c0                	xor    %eax,%eax
    2889:	44 89 e2             	mov    %r12d,%edx
      my_thread_data[1] = &thread_data[other]; 
      printf("even %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
      thread_data[x].protected_state = &protected_state[x];
    }
    printf("i am %d, other is %d my thread index is %d\n", x, other, thread_data[x].thread_index);
    thread_data[x].other = other;
    288c:	45 89 be a8 00 00 00 	mov    %r15d,0xa8(%r14)
    2893:	48 8d 35 0e 4d 00 00 	lea    0x4d0e(%rip),%rsi        # 75a8 <_IO_stdin_used+0x5a8>
    289a:	bf 01 00 00 00       	mov    $0x1,%edi
    289f:	e8 ac fb ff ff       	call   2450 <__printf_chk@plt>
    // for (int j = 0 ; j < cores ; j++) {
      printf("assigning thread %d to core %d\n", x, curcpu);
      if (x < thread_count) {
    28a4:	41 83 fc 01          	cmp    $0x1,%r12d
    28a8:	0f 86 92 0b 00 00    	jbe    3440 <main+0xe50>
        CPU_SET(curcpu, sendercpu);
        curcpu += 2;
      } else {
        for (int j = 0 ; j < cores ; j++) {
          CPU_SET(j, sendercpu);
    28ae:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
        }
      }
      
    // }
    thread_data[x].cpu_set = sendercpu;
    thread_data[x].real_thread_index = x;
    28b6:	8b 04 24             	mov    (%rsp),%eax
    thread_data[x].cpu_set = sendercpu;
    28b9:	49 89 ae a0 00 00 00 	mov    %rbp,0xa0(%r14)

      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
      thread_data[x].tasks = barriers;
      int assigned = 0;
      // external_thread_index = 0;
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28c0:	31 ed                	xor    %ebp,%ebp
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28c2:	be 10 00 00 00       	mov    $0x10,%esi
    thread_data[x].threads = my_thread_data;
    28c7:	49 89 5e 10          	mov    %rbx,0x10(%r14)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28cb:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].real_thread_index = x;
    28d0:	41 89 46 04          	mov    %eax,0x4(%r14)
    thread_data[x].thread_count = 2;
    28d4:	48 8b 05 c5 51 00 00 	mov    0x51c5(%rip),%rax        # 7aa0 <_IO_stdin_used+0xaa0>
    thread_data[x].task_count = total_barrier_count;
    28db:	41 c7 46 30 03 00 00 00 	movl   $0x3,0x30(%r14)
    thread_data[x].thread_count = 2;
    28e3:	49 89 46 18          	mov    %rax,0x18(%r14)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28e7:	e8 b4 fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28ec:	be 10 00 00 00       	mov    $0x10,%esi
    28f1:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28f6:	49 89 46 58          	mov    %rax,0x58(%r14)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28fa:	e8 a1 fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28ff:	be 28 00 00 00       	mov    $0x28,%esi
    2904:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    2909:	66 0f 6f 15 6f 51 00 00 	movdqa 0x516f(%rip),%xmm2        # 7a80 <_IO_stdin_used+0xa80>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2911:	49 89 46 60          	mov    %rax,0x60(%r14)
    thread_data[x].timestamp_count = 0;
    2915:	41 0f 11 56 70       	movups %xmm2,0x70(%r14)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    291a:	e8 81 fa ff ff       	call   23a0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    291f:	be 00 02 00 00       	mov    $0x200,%esi
    2924:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
    2929:	66 0f 6f 1d 4f 51 00 00 	movdqa 0x514f(%rip),%xmm3        # 7a80 <_IO_stdin_used+0xa80>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2931:	49 89 86 80 00 00 00 	mov    %rax,0x80(%r14)
    thread_data[x].task_timestamp_count = 0;
    2938:	41 0f 11 9e 88 00 00 00 	movups %xmm3,0x88(%r14)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2940:	e8 5b fa ff ff       	call   23a0 <calloc@plt>
      thread_data[x].tasks = barriers;
    2945:	49 89 46 28          	mov    %rax,0x28(%r14)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2949:	49 89 c4             	mov    %rax,%r12
              t     x
              a       x
              s         x
              k           x
        */
        thread_data[x].tasks[y].protected = do_protected_write; 
    294c:	4c 63 ed             	movslq %ebp,%r13
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    294f:	be 20 00 00 00       	mov    $0x20,%esi
    2954:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    2959:	4c 89 eb             	mov    %r13,%rbx
    295c:	48 8d 05 4d 0d 00 00 	lea    0xd4d(%rip),%rax        # 36b0 <do_protected_write>
    2963:	48 c1 e3 09          	shl    $0x9,%rbx
    2967:	49 01 dc             	add    %rbx,%r12
    296a:	49 89 84 24 20 01 00 00 	mov    %rax,0x120(%r12)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2972:	e8 29 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    2977:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    297c:	89 6c 24 10          	mov    %ebp,0x10(%rsp)
    2980:	49 89 c7             	mov    %rax,%r15
    2983:	49 89 84 24 68 01 00 00 	mov    %rax,0x168(%r12)
        // long messages_limit = 20;/*9999999;*/
        for (int b = 0 ; b < 2 ; b++) {
    298b:	4c 8d 60 40          	lea    0x40(%rax),%r12
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    298f:	be 08 00 00 00       	mov    $0x8,%esi
    2994:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    2999:	49 83 c7 20          	add    $0x20,%r15
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    299d:	e8 fe f9 ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29a2:	be 08 00 00 00       	mov    $0x8,%esi
    29a7:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29ac:	48 89 c5             	mov    %rax,%rbp
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29af:	e8 ec f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29b4:	be 18 00 00 00       	mov    $0x18,%esi
    29b9:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29be:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29c1:	e8 da f9 ff ff       	call   23a0 <calloc@plt>
          mailboxes[b].lower = &data[0];
          mailboxes[b].higher = &data[1];
          data[0].messages = messages;
          data[1].messages = messages2;
          data[0].messages_limit = messages_limit;
          data[0].messages_count = 0;
    29c6:	66 0f 6f 05 c2 50 00 00 	movdqa 0x50c2(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
          mailboxes[b].higher = &data[1];
    29ce:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29d2:	49 89 47 e0          	mov    %rax,-0x20(%r15)
          mailboxes[b].higher = &data[1];
    29d6:	49 89 77 e8          	mov    %rsi,-0x18(%r15)
          data[0].messages = messages;
    29da:	48 89 28             	mov    %rbp,(%rax)
          data[1].messages = messages2;
    29dd:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    29e1:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    29e5:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    29e9:	4d 39 fc             	cmp    %r15,%r12
    29ec:	75 a1                	jne    298f <main+0x39f>
          data[1].messages_limit = messages_limit;
        }

        char *message = malloc(sizeof(char) * 256);
    29ee:	be 01 00 00 00       	mov    $0x1,%esi
    29f3:	bf 00 01 00 00       	mov    $0x100,%edi
    29f8:	8b 6c 24 10          	mov    0x10(%rsp),%ebp
    29fc:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    2a01:	e8 9a f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a06:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a0b:	49 89 c4             	mov    %rax,%r12
        struct Message *messaged = malloc(sizeof(struct Message));
    2a0e:	e8 fd f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a13:	44 8b 04 24          	mov    (%rsp),%r8d
    2a17:	4c 89 e7             	mov    %r12,%rdi
    2a1a:	41 89 e9             	mov    %ebp,%r9d
    2a1d:	49 89 c7             	mov    %rax,%r15
    2a20:	48 8d 0d a1 4b 00 00 	lea    0x4ba1(%rip),%rcx        # 75c8 <_IO_stdin_used+0x5c8>
    2a27:	ba 00 01 00 00       	mov    $0x100,%edx
    2a2c:	31 c0                	xor    %eax,%eax
    2a2e:	be 01 00 00 00       	mov    $0x1,%esi
    2a33:	e8 e8 fa ff ff       	call   2520 <__sprintf_chk@plt>
        memset(message, '\0', 256);
        sprintf(message, "Sending message from thread %d task %d", x, y);
        messaged->message = message;
        messaged->task_index = y;
        messaged->thread_index = thread_data[x].thread_index;
    2a38:	49 63 06             	movslq (%r14),%rax
        messaged->message = message;
    2a3b:	4d 89 27             	mov    %r12,(%r15)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
        thread_data[x].tasks[y].message = messaged;
        thread_data[x].tasks[y].sending = 1;
        thread_data[x].tasks[y].snapshot_count = 99;
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a3e:	be 20 00 00 00       	mov    $0x20,%esi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a43:	4d 8b 66 28          	mov    0x28(%r14),%r12
        messaged->task_index = y;
    2a47:	4d 89 6f 10          	mov    %r13,0x10(%r15)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a4b:	bf 63 00 00 00       	mov    $0x63,%edi
        messaged->thread_index = thread_data[x].thread_index;
    2a50:	49 89 47 08          	mov    %rax,0x8(%r15)
    2a54:	49 89 c5             	mov    %rax,%r13
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a57:	8d 45 01             	lea    0x1(%rbp),%eax
    2a5a:	4c 01 e3             	add    %r12,%rbx
    2a5d:	83 e0 01             	and    $0x1,%eax
    2a60:	89 83 88 01 00 00    	mov    %eax,0x188(%rbx)
        thread_data[x].tasks[y].message = messaged;
    2a66:	4c 89 bb 80 01 00 00 	mov    %r15,0x180(%rbx)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a6d:	48 c7 83 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%rbx)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a78:	e8 23 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].current_snapshot = 0;
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a7d:	44 89 ab 30 01 00 00 	mov    %r13d,0x130(%rbx)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a84:	48 89 83 48 01 00 00 	mov    %rax,0x148(%rbx)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
        thread_data[x].tasks[y].available = 1;
    2a8b:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2a95:	48 89 83 38 01 00 00 	mov    %rax,0x138(%rbx)
        thread_data[x].tasks[y].sending = 1;
    2a9c:	48 b8 01 00 00 00 02 00 00 00 	movabs $0x200000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2aa6:	48 c7 83 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%rbx)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2ab1:	4c 89 b3 28 01 00 00 	mov    %r14,0x128(%rbx)
        thread_data[x].tasks[y].arrived = 0;
    2ab8:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
        thread_data[x].tasks[y].thread_count = 2;
    2ac2:	c7 83 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%rbx)
        thread_data[x].tasks[y].sending = 1;
    2acc:	48 89 83 78 01 00 00 	mov    %rax,0x178(%rbx)
        thread_data[x].tasks[y].task_count = total_barrier_count;
        thread_data[x].tasks[y].worker_count = thread_count;
        thread_data[x].tasks[y].task_index = y;
    2ad3:	89 2b                	mov    %ebp,(%rbx)
        if (y == barrier_count - 1) {
    2ad5:	83 fd 01             	cmp    $0x1,%ebp
    2ad8:	0f 84 d2 08 00 00    	je     33b0 <main+0xdc0>
            thread_data[x].tasks[y].run = barriered_nulltask; 
          }
          */
          thread_data[x].tasks[y].run = barriered_work; 
        } else {
          if (y < external_threads) { 
    2ade:	83 fd 02             	cmp    $0x2,%ebp
    2ae1:	74 55                	je     2b38 <main+0x548>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2ae3:	8b 14 24             	mov    (%rsp),%edx
    2ae6:	bf 01 00 00 00       	mov    $0x1,%edi
    2aeb:	31 c0                	xor    %eax,%eax
    2aed:	bd 01 00 00 00       	mov    $0x1,%ebp
    2af2:	48 8d 35 f7 4a 00 00 	lea    0x4af7(%rip),%rsi        # 75f0 <_IO_stdin_used+0x5f0>
    2af9:	e8 52 f9 ff ff       	call   2450 <__printf_chk@plt>
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++]; thread_data[x].tasks[y].run = barriered_work_ingest; 
    2afe:	48 63 44 24 28       	movslq 0x28(%rsp),%rax
    2b03:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    2b08:	4d 8b 66 28          	mov    0x28(%r14),%r12
    2b0c:	48 89 c7             	mov    %rax,%rdi
    2b0f:	48 c1 e0 04          	shl    $0x4,%rax
    2b13:	48 01 d8             	add    %rbx,%rax
    2b16:	49 89 46 40          	mov    %rax,0x40(%r14)
    2b1a:	48 8d 05 bf 30 00 00 	lea    0x30bf(%rip),%rax        # 5be0 <barriered_work_ingest>
    2b21:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
    2b29:	8d 47 01             	lea    0x1(%rdi),%eax
    2b2c:	89 44 24 28          	mov    %eax,0x28(%rsp)
    2b30:	e9 17 fe ff ff       	jmp    294c <main+0x35c>
    2b35:	0f 1f 00             	nopl   (%rax)
            assigned = 1;
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    2b38:	48 8d 05 a1 2b 00 00 	lea    0x2ba1(%rip),%rax        # 56e0 <barriered_work>

          }
        }
      }
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b3f:	66 0f 6f 64 24 40    	movdqa 0x40(%rsp),%xmm4
            thread_data[x].tasks[y].run = barriered_work; 
    2b45:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
    2b4c:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2b56:	4d 89 b4 24 28 05 00 00 	mov    %r14,0x528(%r12)
  for (int x = 0 ; x < total_threads ; x++) {
    2b5e:	49 81 c6 b0 00 00 00 	add    $0xb0,%r14
    2b65:	83 7c 24 20 06       	cmpl   $0x6,0x20(%rsp)
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2b6a:	41 c7 84 24 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r12)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2b76:	41 c7 84 24 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%r12)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2b82:	45 89 ac 24 30 05 00 00 	mov    %r13d,0x530(%r12)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2b8a:	41 c7 84 24 7c 05 00 00 02 00 00 00 	movl   $0x2,0x57c(%r12)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b96:	41 c7 84 24 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r12)
      thread_data[x].tasks[barrier_count].available = 1; 
    2ba2:	49 89 84 24 38 05 00 00 	mov    %rax,0x538(%r12)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2baa:	41 0f 11 a4 24 18 05 00 00 	movups %xmm4,0x518(%r12)
  for (int x = 0 ; x < total_threads ; x++) {
    2bb3:	4c 8b 64 24 30       	mov    0x30(%rsp),%r12
    2bb8:	0f 85 22 fc ff ff    	jne    27e0 <main+0x1f0>
    2bbe:	ba 03 00 00 00       	mov    $0x3,%edx
    2bc3:	48 8d 35 4e 47 00 00 	lea    0x474e(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2bca:	bf 01 00 00 00       	mov    $0x1,%edi
    2bcf:	31 c0                	xor    %eax,%eax
    2bd1:	e8 7a f8 ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2bd6:	be 08 00 00 00       	mov    $0x8,%esi
    2bdb:	bf 02 00 00 00       	mov    $0x2,%edi
    2be0:	e8 bb f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2be5:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bea:	be 38 00 00 00       	mov    $0x38,%esi
    my_thread_data[0] = &thread_data[x]; 
    2bef:	4c 8d b7 10 02 00 00 	lea    0x210(%rdi),%r14
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2bf6:	48 89 78 08          	mov    %rdi,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2bfa:	4c 8d a7 b0 00 00 00 	lea    0xb0(%rdi),%r12
    thread_data[x].threads = my_thread_data;
    2c01:	48 89 87 20 02 00 00 	mov    %rax,0x220(%rdi)
    my_thread_data[0] = &thread_data[x]; 
    2c08:	4c 89 30             	mov    %r14,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c0b:	48 8b 47 28          	mov    0x28(%rdi),%rax
    thread_data[x].thread_count = 2;
    2c0f:	c7 87 28 02 00 00 02 00 00 00 	movl   $0x2,0x228(%rdi)
    thread_data[x].thread_index = 0;
    2c19:	c7 87 10 02 00 00 00 00 00 00 	movl   $0x0,0x210(%rdi)
    thread_data[x].task_count = total_barrier_count;
    2c23:	c7 87 40 02 00 00 03 00 00 00 	movl   $0x3,0x240(%rdi)
    thread_data[n].tasks[0].scheduled = 1;
    2c2d:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2c37:	48 8b 87 d8 00 00 00 	mov    0xd8(%rdi),%rax
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c3e:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[n].tasks[0].scheduled = 1;
    2c43:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c4d:	e8 4e f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c52:	be 38 00 00 00       	mov    $0x38,%esi
    2c57:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c5c:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c5f:	e8 3c f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c64:	be 38 00 00 00       	mov    $0x38,%esi
    2c69:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c6e:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c71:	e8 2a f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c76:	be 38 00 00 00       	mov    $0x38,%esi
    2c7b:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c80:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c84:	e8 17 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2c89:	be 08 00 00 00       	mov    $0x8,%esi
    2c8e:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c93:	48 89 c5             	mov    %rax,%rbp
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2c96:	e8 05 f7 ff ff       	call   23a0 <calloc@plt>

  thread_data[thread_count].type = TIMER;
    2c9b:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2ca0:	be 08 00 00 00       	mov    $0x8,%esi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2ca5:	48 89 c3             	mov    %rax,%rbx
  thread_data[thread_count].task_count = total_barrier_count;
    2ca8:	48 8b 05 f9 4d 00 00 	mov    0x4df9(%rip),%rax        # 7aa8 <_IO_stdin_used+0xaa8>
  thread_data[thread_count].type = TIMER;
    2caf:	c7 87 68 01 00 00 00 00 00 00 	movl   $0x0,0x168(%rdi)
  thread_data[thread_count].task_count = total_barrier_count;
    2cb9:	48 89 87 90 01 00 00 	mov    %rax,0x190(%rdi)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2cc0:	bf 06 00 00 00       	mov    $0x6,%edi
    2cc5:	e8 d6 f6 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2cca:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    2ccf:	ba 02 00 00 00       	mov    $0x2,%edx
    2cd4:	48 8d 35 4c 46 00 00 	lea    0x464c(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2cdb:	4c 89 60 08          	mov    %r12,0x8(%rax)
    2cdf:	4c 8d 8f c0 02 00 00 	lea    0x2c0(%rdi),%r9
    2ce6:	4c 8d 87 70 03 00 00 	lea    0x370(%rdi),%r8
    2ced:	48 89 38             	mov    %rdi,(%rax)
    2cf0:	48 8d 8f 60 01 00 00 	lea    0x160(%rdi),%rcx
    2cf7:	4c 89 48 20          	mov    %r9,0x20(%rax)
    2cfb:	4c 89 40 28          	mov    %r8,0x28(%rax)
    2cff:	48 89 48 10          	mov    %rcx,0x10(%rax)
    2d03:	4c 89 70 18          	mov    %r14,0x18(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2d07:	48 89 87 70 01 00 00 	mov    %rax,0x170(%rdi)
    2d0e:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2d10:	c7 87 78 01 00 00 02 00 00 00 	movl   $0x2,0x178(%rdi)
  thread_data[thread_count].my_thread_count = 2;
    2d1a:	c7 87 80 01 00 00 02 00 00 00 	movl   $0x2,0x180(%rdi)
  thread_data[thread_count].thread_index = 0;
    2d24:	c7 87 60 01 00 00 00 00 00 00 	movl   $0x0,0x160(%rdi)
    2d2e:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    2d33:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2d38:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    2d3d:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    2d42:	e8 09 f7 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2d47:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    2d4c:	49 8d 75 70          	lea    0x70(%r13),%rsi
    2d50:	48 8d 7b 10          	lea    0x10(%rbx),%rdi
    2d54:	48 8d 15 55 0d 00 00 	lea    0xd55(%rip),%rdx        # 3ab0 <timer_thread>
    2d5b:	e8 10 f7 ff ff       	call   2470 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    thread_data[x].type = WORKER;
    2d60:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    2d65:	31 d2                	xor    %edx,%edx
    2d67:	31 c0                	xor    %eax,%eax
    2d69:	4c 8d 15 a0 48 00 00 	lea    0x48a0(%rip),%r10        # 7610 <_IO_stdin_used+0x610>
    2d70:	bf 01 00 00 00       	mov    $0x1,%edi
    2d75:	41 c7 45 08 01 00 00 00 	movl   $0x1,0x8(%r13)
    2d7d:	4c 89 d6             	mov    %r10,%rsi
    thread_data[x].running = 1;
    2d80:	41 c7 45 34 01 00 00 00 	movl   $0x1,0x34(%r13)
    2d88:	e8 c3 f6 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2d8d:	4c 89 e9             	mov    %r13,%rcx
    2d90:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
    2d95:	4c 89 fe             	mov    %r15,%rsi
    2d98:	4c 8d 2d c1 09 00 00 	lea    0x9c1(%rip),%r13        # 3760 <barriered_thread>
    2d9f:	48 89 df             	mov    %rbx,%rdi
    2da2:	4c 89 ea             	mov    %r13,%rdx
    2da5:	e8 c6 f6 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2daa:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    2daf:	be 08 00 00 00       	mov    $0x8,%esi
    2db4:	48 8b 97 a0 00 00 00 	mov    0xa0(%rdi),%rdx
    2dbb:	48 8b 3b             	mov    (%rbx),%rdi
    2dbe:	e8 1d f5 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    thread_data[x].type = WORKER;
    2dc3:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    2dc8:	4c 8d 15 41 48 00 00 	lea    0x4841(%rip),%r10        # 7610 <_IO_stdin_used+0x610>
    2dcf:	31 c0                	xor    %eax,%eax
    2dd1:	4c 89 d6             	mov    %r10,%rsi
    2dd4:	ba 01 00 00 00       	mov    $0x1,%edx
    2dd9:	c7 87 b8 00 00 00 01 00 00 00 	movl   $0x1,0xb8(%rdi)
    thread_data[x].running = 1;
    2de3:	c7 87 e4 00 00 00 01 00 00 00 	movl   $0x1,0xe4(%rdi)
    2ded:	bf 01 00 00 00       	mov    $0x1,%edi
    2df2:	e8 59 f6 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2df7:	4c 89 e1             	mov    %r12,%rcx
    2dfa:	49 8d 77 38          	lea    0x38(%r15),%rsi
    2dfe:	4c 89 ea             	mov    %r13,%rdx
    2e01:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    2e05:	e8 66 f6 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2e0a:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    2e0f:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    2e13:	be 08 00 00 00       	mov    $0x8,%esi
    2e18:	49 8b 95 50 01 00 00 	mov    0x150(%r13),%rdx
    2e1f:	e8 bc f4 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e24:	be d8 00 00 00       	mov    $0xd8,%esi
    2e29:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    2e2e:	4c 8b 3d 7b 4c 00 00 	mov    0x4c7b(%rip),%r15        # 7ab0 <_IO_stdin_used+0xab0>
    thread_data[x].type = IO;
    2e35:	41 c7 85 18 02 00 00 02 00 00 00 	movl   $0x2,0x218(%r13)
    thread_data[x].task_count = 0;
    2e40:	4d 89 bd 40 02 00 00 	mov    %r15,0x240(%r13)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e47:	e8 54 f5 ff ff       	call   23a0 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e4c:	31 ff                	xor    %edi,%edi
    2e4e:	be 00 08 00 00       	mov    $0x800,%esi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e53:	49 89 85 58 02 00 00 	mov    %rax,0x258(%r13)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e5a:	e8 51 f6 ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2e5f:	be 08 00 00 00       	mov    $0x8,%esi
    2e64:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e69:	41 89 85 60 02 00 00 	mov    %eax,0x260(%r13)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2e70:	e8 2b f5 ff ff       	call   23a0 <calloc@plt>
    2e75:	ba 03 00 00 00       	mov    $0x3,%edx
    2e7a:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    2e7f:	41 c7 85 28 02 00 00 02 00 00 00 	movl   $0x2,0x228(%r13)
      my_thread_data[n] = &thread_data[n]; 
    2e8a:	4c 89 28             	mov    %r13,(%rax)
    2e8d:	48 8d 35 b1 44 00 00 	lea    0x44b1(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    2e94:	4c 89 60 08          	mov    %r12,0x8(%rax)
    thread_data[x].threads = my_thread_data;
    2e98:	49 89 85 20 02 00 00 	mov    %rax,0x220(%r13)
    2e9f:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    2ea1:	41 c7 85 10 02 00 00 03 00 00 00 	movl   $0x3,0x210(%r13)
    2eac:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
    2eb1:	4c 8d 2d a4 44 00 00 	lea    0x44a4(%rip),%r13        # 735c <_IO_stdin_used+0x35c>
    2eb8:	e8 93 f5 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2ebd:	48 8b 34 24          	mov    (%rsp),%rsi
    2ec1:	4c 89 f1             	mov    %r14,%rcx
    2ec4:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    2ec8:	48 8d 15 51 1e 00 00 	lea    0x1e51(%rip),%rdx        # 4d20 <io_thread>
    2ecf:	48 81 c6 a8 00 00 00 	add    $0xa8,%rsi
    2ed6:	e8 95 f5 ff ff       	call   2470 <pthread_create@plt>
    2edb:	ba 04 00 00 00       	mov    $0x4,%edx
    2ee0:	4c 89 ee             	mov    %r13,%rsi
    2ee3:	31 c0                	xor    %eax,%eax
    2ee5:	bf 01 00 00 00       	mov    $0x1,%edi
    2eea:	e8 61 f5 ff ff       	call   2450 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    2eef:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    2ef4:	48 8b 44 24 38       	mov    0x38(%rsp),%rax

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2ef9:	be 08 00 00 00       	mov    $0x8,%esi
    2efe:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x].task_count = 0;
    2f03:	4d 89 be f0 02 00 00 	mov    %r15,0x2f0(%r14)
    thread_data[x].type = EXTERNAL;
    2f0a:	41 c7 86 c8 02 00 00 03 00 00 00 	movl   $0x3,0x2c8(%r14)
    thread_data[x].buffers = &buffers[buffer_index];
    2f15:	49 89 86 00 03 00 00 	mov    %rax,0x300(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f1c:	e8 7f f4 ff ff       	call   23a0 <calloc@plt>
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f21:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    thread_data[x].thread_count = thread_count;
    2f26:	48 8b 3d 73 4b 00 00 	mov    0x4b73(%rip),%rdi        # 7aa0 <_IO_stdin_used+0xaa0>
    thread_data[x].thread_index = x;
    2f2d:	41 c7 86 c0 02 00 00 04 00 00 00 	movl   $0x4,0x2c0(%r14)
      my_thread_data[n] = &thread_data[n]; 
    2f38:	4c 89 30             	mov    %r14,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f3b:	48 8d b5 e0 00 00 00 	lea    0xe0(%rbp),%rsi
    thread_data[x].thread_count = thread_count;
    2f42:	49 89 be d8 02 00 00 	mov    %rdi,0x2d8(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f49:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
      my_thread_data[n] = &thread_data[n]; 
    2f4d:	4c 89 60 08          	mov    %r12,0x8(%rax)
    thread_data[x].threads = my_thread_data;
    2f51:	49 89 86 d0 02 00 00 	mov    %rax,0x2d0(%r14)
    thread_data[x].thread_index = x;
    2f58:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f5d:	4c 8d 35 ac 0a 00 00 	lea    0xaac(%rip),%r14        # 3a10 <external_thread>
    2f64:	4c 89 f2             	mov    %r14,%rdx
    2f67:	e8 04 f5 ff ff       	call   2470 <pthread_create@plt>
    2f6c:	ba 05 00 00 00       	mov    $0x5,%edx
    2f71:	4c 89 ee             	mov    %r13,%rsi
    2f74:	31 c0                	xor    %eax,%eax
    2f76:	bf 01 00 00 00       	mov    $0x1,%edi
    2f7b:	4c 8d 6c 24 60       	lea    0x60(%rsp),%r13
    2f80:	e8 cb f4 ff ff       	call   2450 <__printf_chk@plt>
    thread_data[x].buffers = &buffers[buffer_index];
    2f85:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    thread_data[x].type = EXTERNAL;
    2f8a:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f8f:	be 08 00 00 00       	mov    $0x8,%esi
    thread_data[x].buffers = &buffers[buffer_index];
    2f94:	48 83 c0 10          	add    $0x10,%rax
    thread_data[x].task_count = 0;
    2f98:	4c 89 bf a0 03 00 00 	mov    %r15,0x3a0(%rdi)
    thread_data[x].buffers = &buffers[buffer_index];
    2f9f:	49 89 ff             	mov    %rdi,%r15
    thread_data[x].type = EXTERNAL;
    2fa2:	c7 87 78 03 00 00 03 00 00 00 	movl   $0x3,0x378(%rdi)
    thread_data[x].buffers = &buffers[buffer_index];
    2fac:	48 89 87 b0 03 00 00 	mov    %rax,0x3b0(%rdi)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2fb3:	bf 02 00 00 00       	mov    $0x2,%edi
    2fb8:	e8 e3 f3 ff ff       	call   23a0 <calloc@plt>
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2fbd:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    2fc2:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
    2fc6:	4c 89 f2             	mov    %r14,%rdx
      my_thread_data[n] = &thread_data[n]; 
    2fc9:	4c 89 60 08          	mov    %r12,0x8(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2fcd:	48 8d b5 18 01 00 00 	lea    0x118(%rbp),%rsi
    2fd4:	31 ed                	xor    %ebp,%ebp
    2fd6:	4c 8d 25 ba 43 00 00 	lea    0x43ba(%rip),%r12        # 7397 <_IO_stdin_used+0x397>
      my_thread_data[n] = &thread_data[n]; 
    2fdd:	4c 89 38             	mov    %r15,(%rax)
    thread_data[x].threads = my_thread_data;
    2fe0:	49 89 87 80 03 00 00 	mov    %rax,0x380(%r15)
    thread_data[x].thread_count = thread_count;
    2fe7:	48 8b 05 b2 4a 00 00 	mov    0x4ab2(%rip),%rax        # 7aa0 <_IO_stdin_used+0xaa0>
    thread_data[x].thread_index = x;
    2fee:	41 c7 87 70 03 00 00 05 00 00 00 	movl   $0x5,0x370(%r15)
    thread_data[x].thread_count = thread_count;
    2ff9:	49 89 87 88 03 00 00 	mov    %rax,0x388(%r15)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3000:	e8 6b f4 ff ff       	call   2470 <pthread_create@plt>
    3005:	48 8d 3d 6d 43 00 00 	lea    0x436d(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    300c:	e8 df f2 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3011:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    void * result; 
    pthread_join(thread[x], &result);
    3018:	48 8b 3c eb          	mov    (%rbx,%rbp,8),%rdi
    301c:	4c 89 ee             	mov    %r13,%rsi
    301f:	e8 cc f4 ff ff       	call   24f0 <pthread_join@plt>
    3024:	89 ea                	mov    %ebp,%edx
    3026:	4c 89 e6             	mov    %r12,%rsi
    3029:	bf 01 00 00 00       	mov    $0x1,%edi
    302e:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3030:	48 83 c5 01          	add    $0x1,%rbp
    3034:	e8 17 f4 ff ff       	call   2450 <__printf_chk@plt>
    3039:	48 83 fd 06          	cmp    $0x6,%rbp
    303d:	75 d9                	jne    3018 <main+0xa28>
    303f:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
    3044:	45 31 d2             	xor    %r10d,%r10d
  long ingests = 0;
    3047:	45 31 f6             	xor    %r14d,%r14d
  long total = 0;
    304a:	31 db                	xor    %ebx,%ebx
    304c:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    3051:	4c 89 f5             	mov    %r14,%rbp
  long sents = 0;
  long received = 0;
    3054:	45 31 c9             	xor    %r9d,%r9d
    3057:	49 89 dd             	mov    %rbx,%r13
    305a:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    305f:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3064:	4c 8d 25 3d 46 00 00 	lea    0x463d(%rip),%r12        # 76a8 <_IO_stdin_used+0x6a8>
  for (int x = 0 ; x < thread_count ; x++) {
    306b:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    3073:	4c 8d 78 28          	lea    0x28(%rax),%r15
    3077:	4d 89 fe             	mov    %r15,%r14
    307a:	bf 0a 00 00 00       	mov    $0xa,%edi
    307f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    3084:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    3088:	4c 89 0c 24          	mov    %r9,(%rsp)
    308c:	e8 3f f2 ff ff       	call   22d0 <putchar@plt>
    3091:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3096:	bf 01 00 00 00       	mov    $0x1,%edi
    309b:	83 f3 01             	xor    $0x1,%ebx
    309e:	48 8d 35 06 43 00 00 	lea    0x4306(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    30a5:	48 8b 10             	mov    (%rax),%rdx
    30a8:	31 c0                	xor    %eax,%eax
    30aa:	e8 a1 f3 ff ff       	call   2450 <__printf_chk@plt>
      other = (x + 1) % total_threads;
    }
    printf("\n");
    printf("Total Protected %ld\n", protected_state[me].protected);

    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    30af:	49 63 56 08          	movslq 0x8(%r14),%rdx
    30b3:	4c 8b 0c 24          	mov    (%rsp),%r9
    30b7:	4c 8b 54 24 28       	mov    0x28(%rsp),%r10
    30bc:	85 d2                	test   %edx,%edx
    30be:	0f 8e ec 04 00 00    	jle    35b0 <main+0xfc0>
    30c4:	49 8b 06             	mov    (%r14),%rax
    30c7:	48 c1 e2 09          	shl    $0x9,%rdx
    30cb:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    long v = 0;
    30cf:	31 d2                	xor    %edx,%edx
    30d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      v += thread_data[me].tasks[n].v;
    30d8:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    30df:	48 05 00 02 00 00    	add    $0x200,%rax
    30e5:	48 39 c8             	cmp    %rcx,%rax
    30e8:	75 ee                	jne    30d8 <main+0xae8>
    }
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    30ea:	48 63 c3             	movslq %ebx,%rax
    30ed:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    30f2:	48 f7 d8             	neg    %rax
    30f5:	25 b0 00 00 00       	and    $0xb0,%eax
    30fa:	48 01 d8             	add    %rbx,%rax
    30fd:	48 63 48 30          	movslq 0x30(%rax),%rcx
    3101:	85 c9                	test   %ecx,%ecx
    3103:	7e 1d                	jle    3122 <main+0xb32>
    3105:	48 8b 40 28          	mov    0x28(%rax),%rax
    3109:	48 c1 e1 09          	shl    $0x9,%rcx
    310d:	48 01 c1             	add    %rax,%rcx
      v += thread_data[other].tasks[n].v;
    3110:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3117:	48 05 00 02 00 00    	add    $0x200,%rax
    311d:	48 39 c8             	cmp    %rcx,%rax
    3120:	75 ee                	jne    3110 <main+0xb20>
    3122:	48 8d 35 97 42 00 00 	lea    0x4297(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    3129:	bf 01 00 00 00       	mov    $0x1,%edi
    312e:	31 c0                	xor    %eax,%eax
    3130:	4c 89 0c 24          	mov    %r9,(%rsp)
    3134:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    3139:	e8 12 f3 ff ff       	call   2450 <__printf_chk@plt>
    }
    printf("Total V %ld\n", v);
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    313e:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3143:	bf 01 00 00 00       	mov    $0x1,%edi
    3148:	48 8d 35 e9 44 00 00 	lea    0x44e9(%rip),%rsi        # 7638 <_IO_stdin_used+0x638>
    314f:	48 8b 08             	mov    (%rax),%rcx
    3152:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    315c:	48 f7 e9             	imul   %rcx
    315f:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3163:	31 c0                	xor    %eax,%eax
    3165:	48 d1 fa             	sar    %rdx
    3168:	48 29 ca             	sub    %rcx,%rdx
    316b:	e8 e0 f2 ff ff       	call   2450 <__printf_chk@plt>
    3170:	bf 0a 00 00 00       	mov    $0xa,%edi
    3175:	e8 56 f1 ff ff       	call   22d0 <putchar@plt>
    printf("\n");
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    317a:	49 63 56 08          	movslq 0x8(%r14),%rdx
    317e:	4c 8b 0c 24          	mov    (%rsp),%r9
    3182:	4c 8b 54 24 28       	mov    0x28(%rsp),%r10
    3187:	85 d2                	test   %edx,%edx
    3189:	7e 51                	jle    31dc <main+0xbec>
    318b:	49 8b 06             	mov    (%r14),%rax
    318e:	48 c1 e2 09          	shl    $0x9,%rdx
    3192:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    3197:	48 8d 3c 02          	lea    (%rdx,%rax,1),%rdi
    319b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      total += thread_data[x].tasks[n].n;
      ingests += thread_data[x].tasks[n].ingest_count;
      sends += thread_data[x].tasks[n].sends;
      for (int k = 0 ; k < thread_count ; k++) {
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    31a0:	48 8b 90 68 01 00 00 	mov    0x168(%rax),%rdx
      total += thread_data[x].tasks[n].n;
    31a7:	4c 03 a8 08 01 00 00 	add    0x108(%rax),%r13
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    31ae:	48 05 00 02 00 00    	add    $0x200,%rax
      ingests += thread_data[x].tasks[n].ingest_count;
    31b4:	48 03 a8 60 ff ff ff 	add    -0xa0(%rax),%rbp
      sends += thread_data[x].tasks[n].sends;
    31bb:	4c 03 98 70 ff ff ff 	add    -0x90(%rax),%r11
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    31c2:	4c 03 4a 10          	add    0x10(%rdx),%r9
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    31c6:	4c 03 52 18          	add    0x18(%rdx),%r10
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    31ca:	4c 03 4a 30          	add    0x30(%rdx),%r9
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    31ce:	4c 03 52 38          	add    0x38(%rdx),%r10
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    31d2:	48 39 c7             	cmp    %rax,%rdi
    31d5:	75 c9                	jne    31a0 <main+0xbb0>
    31d7:	4c 89 5c 24 20       	mov    %r11,0x20(%rsp)
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    31dc:	48 bb db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbx
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    31e6:	45 31 ff             	xor    %r15d,%r15d
    31e9:	49 83 7e 68 00       	cmpq   $0x0,0x68(%r14)
    31ee:	0f 8e 85 00 00 00    	jle    3279 <main+0xc89>
    31f4:	4c 89 2c 24          	mov    %r13,(%rsp)
    31f8:	4d 89 fd             	mov    %r15,%r13
    31fb:	4d 89 cf             	mov    %r9,%r15
    31fe:	48 89 6c 24 28       	mov    %rbp,0x28(%rsp)
    3203:	4c 89 f5             	mov    %r14,%rbp
    3206:	4d 89 d6             	mov    %r10,%r14
    3209:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3210:	48 8b 45 58          	mov    0x58(%rbp),%rax
    3214:	4b 8d 54 ad 00       	lea    0x0(%r13,%r13,4),%rdx
    3219:	48 83 ec 08          	sub    $0x8,%rsp
    321d:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3222:	49 83 c5 01          	add    $0x1,%r13
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3226:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    322a:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    322e:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3232:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3235:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3239:	4c 2b 01             	sub    (%rcx),%r8
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    323c:	48 f7 e3             	mul    %rbx
    323f:	8b 49 20             	mov    0x20(%rcx),%ecx
    3242:	56                   	push   %rsi
    3243:	31 c0                	xor    %eax,%eax
    3245:	48 8d 35 0c 44 00 00 	lea    0x440c(%rip),%rsi        # 7658 <_IO_stdin_used+0x658>
    324c:	48 c1 ea 12          	shr    $0x12,%rdx
    3250:	49 89 d1             	mov    %rdx,%r9
    3253:	ba 02 00 00 00       	mov    $0x2,%edx
    3258:	e8 f3 f1 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    325d:	41 59                	pop    %r9
    325f:	41 5a                	pop    %r10
    3261:	4c 39 6d 68          	cmp    %r13,0x68(%rbp)
    3265:	7f a9                	jg     3210 <main+0xc20>
    3267:	4d 89 f2             	mov    %r14,%r10
    326a:	4c 8b 2c 24          	mov    (%rsp),%r13
    326e:	49 89 ee             	mov    %rbp,%r14
    3271:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
    3276:	4d 89 f9             	mov    %r15,%r9
        for (int k = 0 ; k < thread_data[x].buffers->buffer[n].ingest_snapshot ; k++) {
          struct timespec end = thread_data[x].buffers->buffer[n].snapshots[k].end;
          struct timespec start = thread_data[x].buffers->buffer[n].snapshots[k].start;
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
          printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3279:	49 bf db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r15
      for (int n = 0 ; n < thread_data[x].buffers->count ; n++) {
    3283:	49 8b 46 18          	mov    0x18(%r14),%rax
    3287:	31 f6                	xor    %esi,%esi
    3289:	44 8b 18             	mov    (%rax),%r11d
    328c:	45 85 db             	test   %r11d,%r11d
    328f:	0f 8e eb 00 00 00    	jle    3380 <main+0xd90>
    3295:	4c 89 4c 24 28       	mov    %r9,0x28(%rsp)
    329a:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    329f:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    32a4:	48 89 6c 24 38       	mov    %rbp,0x38(%rsp)
    32a9:	4c 89 f5             	mov    %r14,%rbp
    32ac:	0f 1f 40 00          	nopl   0x0(%rax)
    32b0:	48 8d 3d 16 41 00 00 	lea    0x4116(%rip),%rdi        # 73cd <_IO_stdin_used+0x3cd>
    32b7:	48 89 34 24          	mov    %rsi,(%rsp)
    32bb:	e8 30 f0 ff ff       	call   22f0 <puts@plt>
        for (int k = 0 ; k < thread_data[x].buffers->buffer[n].ingest_snapshot ; k++) {
    32c0:	48 8b 55 18          	mov    0x18(%rbp),%rdx
    32c4:	48 8b 34 24          	mov    (%rsp),%rsi
    32c8:	48 8b 42 08          	mov    0x8(%rdx),%rax
    32cc:	49 89 f5             	mov    %rsi,%r13
    32cf:	49 c1 e5 05          	shl    $0x5,%r13
    32d3:	4c 01 e8             	add    %r13,%rax
    32d6:	8b 78 1c             	mov    0x1c(%rax),%edi
    32d9:	85 ff                	test   %edi,%edi
    32db:	0f 8e 7c 00 00 00    	jle    335d <main+0xd6d>
    32e1:	45 31 f6             	xor    %r14d,%r14d
    32e4:	48 89 ef             	mov    %rbp,%rdi
    32e7:	48 8d 1c b6          	lea    (%rsi,%rsi,4),%rbx
    32eb:	4c 89 f5             	mov    %r14,%rbp
    32ee:	48 c1 e3 03          	shl    $0x3,%rbx
    32f2:	49 89 fe             	mov    %rdi,%r14
    32f5:	0f 1f 00             	nopl   (%rax)
          struct timespec end = thread_data[x].buffers->buffer[n].snapshots[k].end;
    32f8:	48 89 e9             	mov    %rbp,%rcx
    32fb:	48 83 ec 08          	sub    $0x8,%rsp
    32ff:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int k = 0 ; k < thread_data[x].buffers->buffer[n].ingest_snapshot ; k++) {
    3304:	48 83 c5 01          	add    $0x1,%rbp
          struct timespec end = thread_data[x].buffers->buffer[n].snapshots[k].end;
    3308:	48 c1 e1 05          	shl    $0x5,%rcx
    330c:	48 03 48 10          	add    0x10(%rax),%rcx
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3310:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3314:	48 2b 71 08          	sub    0x8(%rcx),%rsi
          printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3318:	48 89 f0             	mov    %rsi,%rax
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    331b:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    331f:	4c 2b 01             	sub    (%rcx),%r8
          printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3322:	49 f7 e7             	mul    %r15
    3325:	49 8b 46 58          	mov    0x58(%r14),%rax
    3329:	8b 4c 18 20          	mov    0x20(%rax,%rbx,1),%ecx
    332d:	56                   	push   %rsi
    332e:	31 c0                	xor    %eax,%eax
    3330:	4c 89 e6             	mov    %r12,%rsi
    3333:	48 c1 ea 12          	shr    $0x12,%rdx
    3337:	49 89 d1             	mov    %rdx,%r9
    333a:	ba 02 00 00 00       	mov    $0x2,%edx
    333f:	e8 0c f1 ff ff       	call   2450 <__printf_chk@plt>
        for (int k = 0 ; k < thread_data[x].buffers->buffer[n].ingest_snapshot ; k++) {
    3344:	49 8b 56 18          	mov    0x18(%r14),%rdx
    3348:	59                   	pop    %rcx
    3349:	5e                   	pop    %rsi
    334a:	48 8b 42 08          	mov    0x8(%rdx),%rax
    334e:	4c 01 e8             	add    %r13,%rax
    3351:	39 68 1c             	cmp    %ebp,0x1c(%rax)
    3354:	7f a2                	jg     32f8 <main+0xd08>
    3356:	48 8b 34 24          	mov    (%rsp),%rsi
    335a:	4c 89 f5             	mov    %r14,%rbp
      for (int n = 0 ; n < thread_data[x].buffers->count ; n++) {
    335d:	48 83 c6 01          	add    $0x1,%rsi
    3361:	39 32                	cmp    %esi,(%rdx)
    3363:	0f 8f 47 ff ff ff    	jg     32b0 <main+0xcc0>
    3369:	49 89 ee             	mov    %rbp,%r14
    336c:	4c 8b 4c 24 28       	mov    0x28(%rsp),%r9
    3371:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    3376:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    337b:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
  for (int x = 0 ; x < thread_count ; x++) {
    3380:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
    3385:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    338b:	49 81 c6 b0 00 00 00 	add    $0xb0,%r14
    3392:	45 85 c0             	test   %r8d,%r8d
    3395:	0f 85 d2 00 00 00    	jne    346d <main+0xe7d>
    339b:	c7 44 24 10 01 00 00 00 	movl   $0x1,0x10(%rsp)
    33a3:	e9 d2 fc ff ff       	jmp    307a <main+0xa8a>
    33a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          thread_data[x].tasks[y].run = barriered_work; 
    33b0:	48 8d 05 29 23 00 00 	lea    0x2329(%rip),%rax        # 56e0 <barriered_work>
    33b7:	bd 02 00 00 00       	mov    $0x2,%ebp
    33bc:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
    33c3:	e9 84 f5 ff ff       	jmp    294c <main+0x35c>
    33c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    33d0:	41 89 f7             	mov    %esi,%r15d
      other = (x + 1) % total_threads;
    33d3:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
      my_thread_data[0] = &thread_data[x]; 
    33d8:	4c 89 33             	mov    %r14,(%rbx)
    33db:	4c 89 f1             	mov    %r14,%rcx
    33de:	4c 89 ff             	mov    %r15,%rdi
      other = (x + 1) % total_threads;
    33e1:	4c 0f af f8          	imul   %rax,%r15
      thread_data[x].thread_index = 0;
    33e5:	41 c7 06 00 00 00 00 	movl   $0x0,(%r14)
    33ec:	48 8d 35 16 3f 00 00 	lea    0x3f16(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      other = (x + 1) % total_threads;
    33f3:	49 c1 ef 22          	shr    $0x22,%r15
    33f7:	43 8d 04 7f          	lea    (%r15,%r15,2),%eax
    33fb:	01 c0                	add    %eax,%eax
    33fd:	29 c7                	sub    %eax,%edi
    33ff:	48 63 c7             	movslq %edi,%rax
    3402:	bf 01 00 00 00       	mov    $0x1,%edi
      my_thread_data[1] = &thread_data[other]; 
    3407:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
      other = (x + 1) % total_threads;
    340b:	49 89 c7             	mov    %rax,%r15
      my_thread_data[1] = &thread_data[other]; 
    340e:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    3412:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3417:	8b 14 24             	mov    (%rsp),%edx
    341a:	49 c1 e0 04          	shl    $0x4,%r8
    341e:	49 01 c0             	add    %rax,%r8
    3421:	31 c0                	xor    %eax,%eax
    3423:	4c 89 43 08          	mov    %r8,0x8(%rbx)
    3427:	e8 24 f0 ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    342c:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    3431:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    3436:	e9 24 f4 ff ff       	jmp    285f <main+0x26f>
    343b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        CPU_SET(curcpu, sendercpu);
    3440:	48 63 44 24 50       	movslq 0x50(%rsp),%rax
    3445:	48 89 c7             	mov    %rax,%rdi
    3448:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    344e:	77 13                	ja     3463 <main+0xe73>
    3450:	48 c1 e8 06          	shr    $0x6,%rax
    3454:	ba 01 00 00 00       	mov    $0x1,%edx
    3459:	89 f9                	mov    %edi,%ecx
    345b:	48 d3 e2             	shl    %cl,%rdx
    345e:	48 09 54 c5 00       	or     %rdx,0x0(%rbp,%rax,8)
        curcpu += 2;
    3463:	83 44 24 50 02       	addl   $0x2,0x50(%rsp)
    3468:	e9 49 f4 ff ff       	jmp    28b6 <main+0x2c6>
    346d:	4d 89 cb             	mov    %r9,%r11
    3470:	4d 89 d1             	mov    %r10,%r9
    3473:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    3478:	4c 89 ea             	mov    %r13,%rdx
    347b:	48 8d 35 53 3f 00 00 	lea    0x3f53(%rip),%rsi        # 73d5 <_IO_stdin_used+0x3d5>
    3482:	31 c0                	xor    %eax,%eax
    3484:	4c 89 1c 24          	mov    %r11,(%rsp)
    3488:	49 89 ee             	mov    %rbp,%r14
    348b:	bf 01 00 00 00       	mov    $0x1,%edi
    3490:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    3495:	4c 89 eb             	mov    %r13,%rbx
      }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3498:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
    34a2:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
  printf("Total Requests per second %ld\n", total / DURATION);
    34a7:	48 c1 fb 3f          	sar    $0x3f,%rbx
    34ab:	e8 a0 ef ff ff       	call   2450 <__printf_chk@plt>
    34b0:	bf 0a 00 00 00       	mov    $0xa,%edi
    34b5:	e8 16 ee ff ff       	call   22d0 <putchar@plt>
    34ba:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    34bf:	bf 01 00 00 00       	mov    $0x1,%edi
    34c4:	48 8d 35 35 42 00 00 	lea    0x4235(%rip),%rsi        # 7700 <_IO_stdin_used+0x700>
    34cb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    34cf:	31 c0                	xor    %eax,%eax
    34d1:	e8 7a ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    34d6:	4c 89 f0             	mov    %r14,%rax
    34d9:	49 c1 fe 3f          	sar    $0x3f,%r14
    34dd:	48 8d 35 44 42 00 00 	lea    0x4244(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    34e4:	48 f7 ed             	imul   %rbp
    34e7:	bf 01 00 00 00       	mov    $0x1,%edi
    34ec:	31 c0                	xor    %eax,%eax
    34ee:	48 d1 fa             	sar    %rdx
    34f1:	4c 29 f2             	sub    %r14,%rdx
    34f4:	e8 57 ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    34f9:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    34fe:	bf 01 00 00 00       	mov    $0x1,%edi
    3503:	48 8d 35 4e 42 00 00 	lea    0x424e(%rip),%rsi        # 7758 <_IO_stdin_used+0x758>
    350a:	4c 89 d0             	mov    %r10,%rax
    350d:	49 c1 fa 3f          	sar    $0x3f,%r10
    3511:	48 f7 ed             	imul   %rbp
    3514:	31 c0                	xor    %eax,%eax
    3516:	48 d1 fa             	sar    %rdx
    3519:	4c 29 d2             	sub    %r10,%rdx
    351c:	e8 2f ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3521:	4c 89 e8             	mov    %r13,%rax
    3524:	bf 01 00 00 00       	mov    $0x1,%edi
    3529:	48 8d 35 58 42 00 00 	lea    0x4258(%rip),%rsi        # 7788 <_IO_stdin_used+0x788>
    3530:	48 f7 ed             	imul   %rbp
    3533:	31 c0                	xor    %eax,%eax
    3535:	48 d1 fa             	sar    %rdx
    3538:	48 29 da             	sub    %rbx,%rdx
    353b:	e8 10 ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3540:	4c 8b 1c 24          	mov    (%rsp),%r11
    3544:	bf 01 00 00 00       	mov    $0x1,%edi
    3549:	48 8d 35 99 3e 00 00 	lea    0x3e99(%rip),%rsi        # 73e9 <_IO_stdin_used+0x3e9>
    3550:	4c 89 d8             	mov    %r11,%rax
    3553:	49 c1 fb 3f          	sar    $0x3f,%r11
    3557:	48 f7 ed             	imul   %rbp
    355a:	31 c0                	xor    %eax,%eax
    355c:	48 d1 fa             	sar    %rdx
    355f:	4c 29 da             	sub    %r11,%rdx
    3562:	e8 e9 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3567:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    356c:	bf 01 00 00 00       	mov    $0x1,%edi
    3571:	48 8d 35 82 3e 00 00 	lea    0x3e82(%rip),%rsi        # 73fa <_IO_stdin_used+0x3fa>
    3578:	4c 89 c8             	mov    %r9,%rax
    357b:	49 c1 f9 3f          	sar    $0x3f,%r9
    357f:	48 f7 ed             	imul   %rbp
    3582:	48 d1 fa             	sar    %rdx
    3585:	4c 29 ca             	sub    %r9,%rdx
    3588:	31 c0                	xor    %eax,%eax
    358a:	e8 c1 ee ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    358f:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    3594:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    359d:	75 18                	jne    35b7 <main+0xfc7>
    359f:	48 83 c4 78          	add    $0x78,%rsp
    35a3:	31 c0                	xor    %eax,%eax
    35a5:	5b                   	pop    %rbx
    35a6:	5d                   	pop    %rbp
    35a7:	41 5c                	pop    %r12
    35a9:	41 5d                	pop    %r13
    35ab:	41 5e                	pop    %r14
    35ad:	41 5f                	pop    %r15
    35af:	c3                   	ret
    long v = 0;
    35b0:	31 d2                	xor    %edx,%edx
    35b2:	e9 33 fb ff ff       	jmp    30ea <main+0xafa>
}
    35b7:	e8 74 ed ff ff       	call   2330 <__stack_chk_fail@plt>
    35bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000035c0 <_start>:
    35c0:	f3 0f 1e fa          	endbr64
    35c4:	31 ed                	xor    %ebp,%ebp
    35c6:	49 89 d1             	mov    %rdx,%r9
    35c9:	5e                   	pop    %rsi
    35ca:	48 89 e2             	mov    %rsp,%rdx
    35cd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    35d1:	50                   	push   %rax
    35d2:	54                   	push   %rsp
    35d3:	45 31 c0             	xor    %r8d,%r8d
    35d6:	31 c9                	xor    %ecx,%ecx
    35d8:	48 8d 3d 11 f0 ff ff 	lea    -0xfef(%rip),%rdi        # 25f0 <main>
    35df:	ff 15 f3 69 00 00    	call   *0x69f3(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    35e5:	f4                   	hlt
    35e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000035f0 <deregister_tm_clones>:
    35f0:	48 8d 3d 29 6a 00 00 	lea    0x6a29(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    35f7:	48 8d 05 22 6a 00 00 	lea    0x6a22(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    35fe:	48 39 f8             	cmp    %rdi,%rax
    3601:	74 15                	je     3618 <deregister_tm_clones+0x28>
    3603:	48 8b 05 d6 69 00 00 	mov    0x69d6(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    360a:	48 85 c0             	test   %rax,%rax
    360d:	74 09                	je     3618 <deregister_tm_clones+0x28>
    360f:	ff e0                	jmp    *%rax
    3611:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3618:	c3                   	ret
    3619:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003620 <register_tm_clones>:
    3620:	48 8d 3d f9 69 00 00 	lea    0x69f9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3627:	48 8d 35 f2 69 00 00 	lea    0x69f2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    362e:	48 29 fe             	sub    %rdi,%rsi
    3631:	48 89 f0             	mov    %rsi,%rax
    3634:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3638:	48 c1 f8 03          	sar    $0x3,%rax
    363c:	48 01 c6             	add    %rax,%rsi
    363f:	48 d1 fe             	sar    %rsi
    3642:	74 14                	je     3658 <register_tm_clones+0x38>
    3644:	48 8b 05 a5 69 00 00 	mov    0x69a5(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    364b:	48 85 c0             	test   %rax,%rax
    364e:	74 08                	je     3658 <register_tm_clones+0x38>
    3650:	ff e0                	jmp    *%rax
    3652:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3658:	c3                   	ret
    3659:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003660 <__do_global_dtors_aux>:
    3660:	f3 0f 1e fa          	endbr64
    3664:	80 3d bd 69 00 00 00 	cmpb   $0x0,0x69bd(%rip)        # a028 <completed.0>
    366b:	75 2b                	jne    3698 <__do_global_dtors_aux+0x38>
    366d:	55                   	push   %rbp
    366e:	48 83 3d 82 69 00 00 00 	cmpq   $0x0,0x6982(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3676:	48 89 e5             	mov    %rsp,%rbp
    3679:	74 0c                	je     3687 <__do_global_dtors_aux+0x27>
    367b:	48 8b 3d 86 69 00 00 	mov    0x6986(%rip),%rdi        # a008 <__dso_handle>
    3682:	e8 29 ec ff ff       	call   22b0 <__cxa_finalize@plt>
    3687:	e8 64 ff ff ff       	call   35f0 <deregister_tm_clones>
    368c:	c6 05 95 69 00 00 01 	movb   $0x1,0x6995(%rip)        # a028 <completed.0>
    3693:	5d                   	pop    %rbp
    3694:	c3                   	ret
    3695:	0f 1f 00             	nopl   (%rax)
    3698:	c3                   	ret
    3699:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000036a0 <frame_dummy>:
    36a0:	f3 0f 1e fa          	endbr64
    36a4:	e9 77 ff ff ff       	jmp    3620 <register_tm_clones>
    36a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000036b0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    36b0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    36b4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    36bb:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    36bf:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    36c7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    36cb:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    36cf:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    36d6:	48 85 c9             	test   %rcx,%rcx
    36d9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    36e0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    36e4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    36e8:	31 c0                	xor    %eax,%eax
    36ea:	c3                   	ret
    36eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000036f0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    36f0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    36f4:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    36fb:	85 c9                	test   %ecx,%ecx
    36fd:	7e 4f                	jle    374e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    36ff:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3706:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    370d:	48 c1 e1 09          	shl    $0x9,%rcx
    3711:	48 8b 50 10          	mov    0x10(%rax),%rdx
    3715:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3719:	48 8b 70 28          	mov    0x28(%rax),%rsi
    371d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    371f:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    3723:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3728:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3730:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3738:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3743:	48 05 00 02 00 00    	add    $0x200,%rax
    3749:	48 39 c1             	cmp    %rax,%rcx
    374c:	75 da                	jne    3728 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    374e:	0f ae f8             	sfence
}
    3751:	31 c0                	xor    %eax,%eax
    3753:	c3                   	ret
    3754:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    375f:	90                   	nop

0000000000003760 <barriered_thread>:
void* barriered_thread(void *arg) {
    3760:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3764:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    3768:	0f 85 90 02 00 00    	jne    39fe <barriered_thread+0x29e>
void* barriered_thread(void *arg) {
    376e:	41 56                	push   %r14
    3770:	41 55                	push   %r13
    3772:	49 89 fd             	mov    %rdi,%r13
    3775:	41 54                	push   %r12
    3777:	55                   	push   %rbp
    3778:	31 ed                	xor    %ebp,%ebp
    377a:	53                   	push   %rbx
    377b:	31 db                	xor    %ebx,%ebx
    377d:	0f 1f 00             	nopl   (%rax)
    if (t >= data->task_count) {
    3780:	41 8b 55 30          	mov    0x30(%r13),%edx
    3784:	39 da                	cmp    %ebx,%edx
    3786:	7f 12                	jg     379a <barriered_thread+0x3a>
      data->cycles++;
    3788:	49 83 85 98 00 00 00 01 	addq   $0x1,0x98(%r13)
    for (; t < data->task_count; t++) {
    3790:	31 db                	xor    %ebx,%ebx
    3792:	85 d2                	test   %edx,%edx
    3794:	0f 8e 56 01 00 00    	jle    38f0 <barriered_thread+0x190>
    379a:	4c 63 e3             	movslq %ebx,%r12
    379d:	49 c1 e4 09          	shl    $0x9,%r12
    37a1:	eb 17                	jmp    37ba <barriered_thread+0x5a>
    37a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    37a8:	83 c3 01             	add    $0x1,%ebx
    37ab:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    37b2:	39 d3                	cmp    %edx,%ebx
    37b4:	0f 8d 36 01 00 00    	jge    38f0 <barriered_thread+0x190>
      if (data->tasks[t].available == 1) {
    37ba:	49 8b 45 28          	mov    0x28(%r13),%rax
    37be:	4a 8d 34 20          	lea    (%rax,%r12,1),%rsi
    37c2:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    37c9:	75 dd                	jne    37a8 <barriered_thread+0x48>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    37cb:	41 8b 7d 18          	mov    0x18(%r13),%edi
          previous = t - 1;
    37cf:	83 ea 01             	sub    $0x1,%edx
    37d2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    37d5:	85 db                	test   %ebx,%ebx
    37d7:	0f 4f d1             	cmovg  %ecx,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    37da:	85 ff                	test   %edi,%edi
    37dc:	0f 8e 3e 01 00 00    	jle    3920 <barriered_thread+0x1c0>
    37e2:	49 8b 45 10          	mov    0x10(%r13),%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    37e6:	48 63 ca             	movslq %edx,%rcx
    37e9:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    37ec:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    37ef:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    37f6:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    37fd:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    3801:	45 31 f6             	xor    %r14d,%r14d
    3804:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3808:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3810:	48 8b 10             	mov    (%rax),%rdx
    3813:	4c 8b 5a 28          	mov    0x28(%rdx),%r11
    3817:	49 01 cb             	add    %rcx,%r11
    381a:	4c 89 da             	mov    %r11,%rdx
    381d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    3824:	75 04                	jne    382a <barriered_thread+0xca>
            arrived++;
    3826:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    382a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    3831:	75 04                	jne    3837 <barriered_thread+0xd7>
            prearrive++;
    3833:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3837:	48 83 c0 08          	add    $0x8,%rax
    383b:	48 39 f0             	cmp    %rsi,%rax
    383e:	75 d0                	jne    3810 <barriered_thread+0xb0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    3840:	44 39 d7             	cmp    %r10d,%edi
    3843:	0f 84 c7 00 00 00    	je     3910 <barriered_thread+0x1b0>
    3849:	45 85 d2             	test   %r10d,%r10d
    384c:	0f 84 be 00 00 00    	je     3910 <barriered_thread+0x1b0>
        if (arrived == 0 || arrived == data->thread_count) {
    3852:	45 85 f6             	test   %r14d,%r14d
    3855:	74 0a                	je     3861 <barriered_thread+0x101>
    3857:	45 39 75 18          	cmp    %r14d,0x18(%r13)
    385b:	0f 85 8f 00 00 00    	jne    38f0 <barriered_thread+0x190>
    3861:	49 8b 45 28          	mov    0x28(%r13),%rax
          data->tasks[t].prearrive++;
    3865:	4c 01 e0             	add    %r12,%rax
    3868:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    386f:	85 db                	test   %ebx,%ebx
    3871:	75 0e                	jne    3881 <barriered_thread+0x121>
    3873:	49 8b 75 70          	mov    0x70(%r13),%rsi
    3877:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    387b:	0f 8c 5f 01 00 00    	jl     39e0 <barriered_thread+0x280>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3881:	49 63 4d 00          	movslq 0x0(%r13),%rcx
    3885:	49 8b 55 10          	mov    0x10(%r13),%rdx
          data->tasks[t].available = 0;
    3889:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3893:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    3897:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
    389b:	4c 01 e7             	add    %r12,%rdi
    389e:	ff 90 18 01 00 00    	call   *0x118(%rax)
          data->tasks[t].arrived++;
    38a4:	49 8b 45 28          	mov    0x28(%r13),%rax
    38a8:	4c 01 e0             	add    %r12,%rax
    38ab:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    38b2:	41 8b 45 30          	mov    0x30(%r13),%eax
          data->iteration_count++;
    38b6:	49 83 45 68 01       	addq   $0x1,0x68(%r13)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    38bb:	83 e8 01             	sub    $0x1,%eax
    38be:	39 d8                	cmp    %ebx,%eax
    38c0:	0f 84 b2 00 00 00    	je     3978 <barriered_thread+0x218>
          asm volatile ("sfence" ::: "memory");
    38c6:	0f ae f8             	sfence
          if (waiting == 0) {
    38c9:	85 ed                	test   %ebp,%ebp
    38cb:	0f 84 d7 00 00 00    	je     39a8 <barriered_thread+0x248>
    for (; t < data->task_count; t++) {
    38d1:	41 8b 55 30          	mov    0x30(%r13),%edx
    38d5:	83 c3 01             	add    $0x1,%ebx
    38d8:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    38df:	39 d3                	cmp    %edx,%ebx
    38e1:	0f 8c d3 fe ff ff    	jl     37ba <barriered_thread+0x5a>
    38e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  while (data->running == 1) {
    38f0:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
    38f5:	0f 84 85 fe ff ff    	je     3780 <barriered_thread+0x20>
}
    38fb:	5b                   	pop    %rbx
    38fc:	31 c0                	xor    %eax,%eax
    38fe:	5d                   	pop    %rbp
    38ff:	41 5c                	pop    %r12
    3901:	41 5d                	pop    %r13
    3903:	41 5e                	pop    %r14
    3905:	c3                   	ret
    3906:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
    3910:	83 fd 01             	cmp    $0x1,%ebp
    3913:	74 1b                	je     3930 <barriered_thread+0x1d0>
        int arrived = 0; 
    3915:	31 ed                	xor    %ebp,%ebp
    3917:	e9 36 ff ff ff       	jmp    3852 <barriered_thread+0xf2>
    391c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    3920:	83 fd 01             	cmp    $0x1,%ebp
    3923:	0f 85 3c ff ff ff    	jne    3865 <barriered_thread+0x105>
        int arrived = 0; 
    3929:	45 31 f6             	xor    %r14d,%r14d
    392c:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3930:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    3937:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    393c:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    393e:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3942:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    3949:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    394e:	e8 bd e9 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3953:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    395a:	48 83 c0 01          	add    $0x1,%rax
    395e:	48 99                	cqto
    3960:	49 f7 bd 90 00 00 00 	idivq  0x90(%r13)
    3967:	49 89 95 88 00 00 00 	mov    %rdx,0x88(%r13)
            waiting = 0; 
    396e:	e9 df fe ff ff       	jmp    3852 <barriered_thread+0xf2>
    3973:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3978:	49 8b 75 70          	mov    0x70(%r13),%rsi
    397c:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    3980:	0f 8d 40 ff ff ff    	jge    38c6 <barriered_thread+0x166>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    3986:	48 c1 e6 04          	shl    $0x4,%rsi
    398a:	bf 04 00 00 00       	mov    $0x4,%edi
    398f:	49 03 75 60          	add    0x60(%r13),%rsi
    3993:	e8 78 e9 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3998:	49 83 45 70 01       	addq   $0x1,0x70(%r13)
    399d:	e9 24 ff ff ff       	jmp    38c6 <barriered_thread+0x166>
    39a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    39a8:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    39af:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    39b4:	bd 01 00 00 00       	mov    $0x1,%ebp
            data->task_snapshot[data->task_timestamp_count].task = t;
    39b9:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    39bd:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    39c4:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    39c8:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    39cb:	e8 40 e9 ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    39d0:	41 8b 55 30          	mov    0x30(%r13),%edx
    39d4:	e9 cf fd ff ff       	jmp    37a8 <barriered_thread+0x48>
    39d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    39e0:	48 c1 e6 04          	shl    $0x4,%rsi
    39e4:	bf 04 00 00 00       	mov    $0x4,%edi
    39e9:	49 03 75 58          	add    0x58(%r13),%rsi
    39ed:	e8 1e e9 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    39f2:	49 8b 45 28          	mov    0x28(%r13),%rax
    39f6:	4c 01 e0             	add    %r12,%rax
    39f9:	e9 83 fe ff ff       	jmp    3881 <barriered_thread+0x121>
}
    39fe:	31 c0                	xor    %eax,%eax
    3a00:	c3                   	ret
    3a01:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3a0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003a10 <external_thread>:
void * external_thread(void *arg) {
    3a10:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3a14:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    3a18:	0f 85 82 00 00 00    	jne    3aa0 <external_thread+0x90>
void * external_thread(void *arg) {
    3a1e:	41 54                	push   %r12
    3a20:	4c 8d 25 dd 35 00 00 	lea    0x35dd(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    3a27:	55                   	push   %rbp
    3a28:	48 89 fd             	mov    %rdi,%rbp
    3a2b:	53                   	push   %rbx
    3a2c:	0f 1f 40 00          	nopl   0x0(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3a30:	48 8b 45 40          	mov    0x40(%rbp),%rax
    3a34:	31 db                	xor    %ebx,%ebx
    3a36:	8b 10                	mov    (%rax),%edx
    3a38:	85 d2                	test   %edx,%edx
    3a3a:	7e 1d                	jle    3a59 <external_thread+0x49>
    3a3c:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->buffers->buffer[x].available == 0) {
    3a40:	48 89 d8             	mov    %rbx,%rax
    3a43:	48 c1 e0 05          	shl    $0x5,%rax
    3a47:	48 01 c8             	add    %rcx,%rax
    3a4a:	8b 70 08             	mov    0x8(%rax),%esi
    3a4d:	85 f6                	test   %esi,%esi
    3a4f:	74 1f                	je     3a70 <external_thread+0x60>
    for (int x = 0; x < data->buffers->count; x++) {
    3a51:	48 83 c3 01          	add    $0x1,%rbx
    3a55:	39 da                	cmp    %ebx,%edx
    3a57:	7f e7                	jg     3a40 <external_thread+0x30>
    asm volatile ("mfence" ::: "memory");
    3a59:	0f ae f0             	mfence
  while (data->running == 1) {
    3a5c:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    3a60:	74 ce                	je     3a30 <external_thread+0x20>
}
    3a62:	5b                   	pop    %rbx
    3a63:	31 c0                	xor    %eax,%eax
    3a65:	5d                   	pop    %rbp
    3a66:	41 5c                	pop    %r12
    3a68:	c3                   	ret
    3a69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers->buffer[x].snapshots[data->buffers->buffer[x].ingest_snapshot].start);
    3a70:	48 63 70 1c          	movslq 0x1c(%rax),%rsi
        data->buffers->buffer[x].data = "Hello world";
    3a74:	4c 89 20             	mov    %r12,(%rax)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers->buffer[x].snapshots[data->buffers->buffer[x].ingest_snapshot].start);
    3a77:	bf 04 00 00 00       	mov    $0x4,%edi
    for (int x = 0; x < data->buffers->count; x++) {
    3a7c:	48 83 c3 01          	add    $0x1,%rbx
        data->buffers->buffer[x].available = 1;
    3a80:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers->buffer[x].snapshots[data->buffers->buffer[x].ingest_snapshot].start);
    3a87:	48 c1 e6 05          	shl    $0x5,%rsi
    3a8b:	48 03 70 10          	add    0x10(%rax),%rsi
    3a8f:	e8 7c e8 ff ff       	call   2310 <clock_gettime@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3a94:	48 8b 45 40          	mov    0x40(%rbp),%rax
    3a98:	8b 10                	mov    (%rax),%edx
    3a9a:	39 da                	cmp    %ebx,%edx
    3a9c:	7f 9e                	jg     3a3c <external_thread+0x2c>
    3a9e:	eb b9                	jmp    3a59 <external_thread+0x49>
}
    3aa0:	31 c0                	xor    %eax,%eax
    3aa2:	c3                   	ret
    3aa3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3aae:	66 90                	xchg   %ax,%ax

0000000000003ab0 <timer_thread>:
void* timer_thread(void *arg) {
    3ab0:	f3 0f 1e fa          	endbr64
    3ab4:	41 57                	push   %r15
    3ab6:	48 8d 35 53 35 00 00 	lea    0x3553(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3abd:	49 89 ff             	mov    %rdi,%r15
    3ac0:	41 56                	push   %r14
    3ac2:	41 55                	push   %r13
    3ac4:	41 54                	push   %r12
    3ac6:	55                   	push   %rbp
    3ac7:	53                   	push   %rbx
    3ac8:	48 83 ec 58          	sub    $0x58,%rsp
    3acc:	8b 17                	mov    (%rdi),%edx
    3ace:	bf 01 00 00 00       	mov    $0x1,%edi
    3ad3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3adc:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3ae1:	31 c0                	xor    %eax,%eax
    3ae3:	e8 68 e9 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3ae8:	66 0f 6f 05 b0 3e 00 00 	movdqa 0x3eb0(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    3af0:	ba 88 13 00 00       	mov    $0x1388,%edx
    3af5:	31 c0                	xor    %eax,%eax
    3af7:	48 8d 35 24 35 00 00 	lea    0x3524(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3afe:	bf 01 00 00 00       	mov    $0x1,%edi
    3b03:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3b08:	e8 43 e9 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3b0d:	45 8b 67 34          	mov    0x34(%r15),%r12d
    3b11:	45 85 e4             	test   %r12d,%r12d
    3b14:	0f 84 9b 00 00 00    	je     3bb5 <timer_thread+0x105>
  int n = 0;
    3b1a:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    3b1d:	45 31 e4             	xor    %r12d,%r12d
    3b20:	49 89 e5             	mov    %rsp,%r13
    y++;
    3b23:	31 db                	xor    %ebx,%ebx
    3b25:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    3b2a:	48 89 ef             	mov    %rbp,%rdi
    3b2d:	4c 89 ee             	mov    %r13,%rsi
    n++;
    3b30:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3b34:	e8 17 e8 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b39:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3b3d:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b42:	85 c0                	test   %eax,%eax
    3b44:	7e 47                	jle    3b8d <timer_thread+0xdd>
    3b46:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3b4a:	49 c1 e4 09          	shl    $0x9,%r12
    3b4e:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3b52:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3b58:	4c 8b 11             	mov    (%rcx),%r10
    3b5b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b5d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3b61:	99                   	cltd
    3b62:	41 f7 7a 30          	idivl  0x30(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3b66:	49 8b 72 28          	mov    0x28(%r10),%rsi
    3b6a:	48 63 d2             	movslq %edx,%rdx
    3b6d:	48 c1 e2 09          	shl    $0x9,%rdx
    3b71:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3b7c:	42 c7 84 26 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b88:	49 39 c8             	cmp    %rcx,%r8
    3b8b:	75 cb                	jne    3b58 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    3b8d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3b90:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3b94:	41 8b 57 34          	mov    0x34(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3b98:	48 8b 00             	mov    (%rax),%rax
    y++;
    3b9b:	39 78 30             	cmp    %edi,0x30(%rax)
    3b9e:	0f 4e fb             	cmovle %ebx,%edi
    3ba1:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3ba4:	85 d2                	test   %edx,%edx
    3ba6:	74 0d                	je     3bb5 <timer_thread+0x105>
    3ba8:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3baf:	0f 85 75 ff ff ff    	jne    3b2a <timer_thread+0x7a>
    3bb5:	48 8d 3d 7c 34 00 00 	lea    0x347c(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3bbc:	e8 2f e7 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3bc1:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3bc5:	85 d2                	test   %edx,%edx
    3bc7:	7e 6b                	jle    3c34 <timer_thread+0x184>
    for (int y = 0 ; y < data->task_count ; y++) {
    3bc9:	49 63 47 30          	movslq 0x30(%r15),%rax
    3bcd:	85 c0                	test   %eax,%eax
    3bcf:	7e 63                	jle    3c34 <timer_thread+0x184>
    3bd1:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3bd5:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3bd9:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3be1:	31 ff                	xor    %edi,%edi
    3be3:	48 89 c2             	mov    %rax,%rdx
    3be6:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3bea:	48 8b 40 28          	mov    0x28(%rax),%rax
    3bee:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3bf2:	f6 c6 02             	test   $0x2,%dh
    3bf5:	74 15                	je     3c0c <timer_thread+0x15c>
    3bf7:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3c01:	48 05 00 02 00 00    	add    $0x200,%rax
    3c07:	48 39 c6             	cmp    %rax,%rsi
    3c0a:	74 1f                	je     3c2b <timer_thread+0x17b>
      data->threads[x]->tasks[y].sending = 0;
    3c0c:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3c16:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3c1c:	c7 80 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3c26:	48 39 c6             	cmp    %rax,%rsi
    3c29:	75 e1                	jne    3c0c <timer_thread+0x15c>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c2b:	48 83 c7 08          	add    $0x8,%rdi
    3c2f:	48 39 f9             	cmp    %rdi,%rcx
    3c32:	75 b2                	jne    3be6 <timer_thread+0x136>
  asm volatile ("mfence" ::: "memory");
    3c34:	0f ae f0             	mfence
  struct timespec drain = {
    3c37:	66 0f 6f 05 71 3d 00 00 	movdqa 0x3d71(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    3c3f:	48 8d 2d 17 34 00 00 	lea    0x3417(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3c46:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c4b:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3c4f:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c54:	85 c0                	test   %eax,%eax
    3c56:	7e 4c                	jle    3ca4 <timer_thread+0x1f4>
    3c58:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3c5c:	4d 63 c4             	movslq %r12d,%r8
    3c5f:	49 c1 e0 09          	shl    $0x9,%r8
    3c63:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3c67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3c70:	48 8b 19             	mov    (%rcx),%rbx
    3c73:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c75:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3c79:	99                   	cltd
    3c7a:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3c7d:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3c81:	48 63 d2             	movslq %edx,%rdx
    3c84:	48 c1 e2 09          	shl    $0x9,%rdx
    3c88:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3c93:	42 c7 84 06 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c9f:	4c 39 c9             	cmp    %r9,%rcx
    3ca2:	75 cc                	jne    3c70 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    3ca4:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3ca7:	49 8b 47 10          	mov    0x10(%r15),%rax
    y++;
    3cab:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3cae:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3cb1:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3cb4:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3cb8:	41 8b 7f 20          	mov    0x20(%r15),%edi
    3cbc:	85 ff                	test   %edi,%edi
    3cbe:	0f 8e bc 00 00 00    	jle    3d80 <timer_thread+0x2d0>
    3cc4:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    3cc7:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3ccd:	0f 1f 00             	nopl   (%rax)
    3cd0:	4a 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbx
            all_empty = 0;
    3cd8:	45 31 f6             	xor    %r14d,%r14d
    3cdb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3ce0:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3ce4:	4c 89 f0             	mov    %r14,%rax
    3ce7:	48 c1 e0 09          	shl    $0x9,%rax
    3ceb:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3cef:	31 d2                	xor    %edx,%edx
    3cf1:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3cf8:	eb 16                	jmp    3d10 <timer_thread+0x260>
    3cfa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3d00:	4d 85 c0             	test   %r8,%r8
    3d03:	7f 1f                	jg     3d24 <timer_thread+0x274>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3d05:	83 c2 01             	add    $0x1,%edx
    3d08:	48 83 c0 20          	add    $0x20,%rax
    3d0c:	39 fa                	cmp    %edi,%edx
    3d0e:	74 2a                	je     3d3a <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3d10:	48 8b 08             	mov    (%rax),%rcx
    3d13:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3d17:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3d1b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3d1f:	48 85 c9             	test   %rcx,%rcx
    3d22:	7e dc                	jle    3d00 <timer_thread+0x250>
    3d24:	bf 01 00 00 00       	mov    $0x1,%edi
    3d29:	48 89 ee             	mov    %rbp,%rsi
    3d2c:	31 c0                	xor    %eax,%eax
    3d2e:	e8 1d e7 ff ff       	call   2450 <__printf_chk@plt>
            break;
    3d33:	41 8b 7f 20          	mov    0x20(%r15),%edi
            all_empty = 0;
    3d37:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3d3a:	49 83 c6 01          	add    $0x1,%r14
    3d3e:	44 39 f7             	cmp    %r14d,%edi
    3d41:	7e 0d                	jle    3d50 <timer_thread+0x2a0>
    3d43:	49 8b 47 10          	mov    0x10(%r15),%rax
    3d47:	eb 97                	jmp    3ce0 <timer_thread+0x230>
    3d49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3d50:	49 83 c5 01          	add    $0x1,%r13
    3d54:	44 39 ef             	cmp    %r13d,%edi
    3d57:	7e 0d                	jle    3d66 <timer_thread+0x2b6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3d59:	85 ff                	test   %edi,%edi
    3d5b:	7e 09                	jle    3d66 <timer_thread+0x2b6>
    3d5d:	49 8b 47 10          	mov    0x10(%r15),%rax
    3d61:	e9 6a ff ff ff       	jmp    3cd0 <timer_thread+0x220>
    if (all_empty == 1) {
    3d66:	41 83 f9 01          	cmp    $0x1,%r9d
    3d6a:	74 14                	je     3d80 <timer_thread+0x2d0>
      nanosleep(&drain , &drainrem);
    3d6c:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3d71:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3d76:	e8 d5 e5 ff ff       	call   2350 <nanosleep@plt>
    3d7b:	e9 cb fe ff ff       	jmp    3c4b <timer_thread+0x19b>
    3d80:	48 8d 3d cd 32 00 00 	lea    0x32cd(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3d87:	e8 64 e5 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3d8c:	41 8b 47 34          	mov    0x34(%r15),%eax
    3d90:	85 c0                	test   %eax,%eax
    3d92:	0f 84 cf 00 00 00    	je     3e67 <timer_thread+0x3b7>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d98:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3d9c:	85 c9                	test   %ecx,%ecx
    3d9e:	7e 2d                	jle    3dcd <timer_thread+0x31d>
    3da0:	49 8b 47 10          	mov    0x10(%r15),%rax
    3da4:	31 db                	xor    %ebx,%ebx
    3da6:	48 8d 2d c1 32 00 00 	lea    0x32c1(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3dad:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->running = 0;
    3db0:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3db4:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3db8:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3dbf:	0f 84 cf 00 00 00    	je     3e94 <timer_thread+0x3e4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3dc5:	48 83 c3 01          	add    $0x1,%rbx
    3dc9:	39 d9                	cmp    %ebx,%ecx
    3dcb:	7f e3                	jg     3db0 <timer_thread+0x300>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3dcd:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3dd1:	85 d2                	test   %edx,%edx
    3dd3:	7e 7b                	jle    3e50 <timer_thread+0x3a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3dd5:	49 63 47 30          	movslq 0x30(%r15),%rax
    3dd9:	85 c0                	test   %eax,%eax
    3ddb:	7e 73                	jle    3e50 <timer_thread+0x3a0>
    3ddd:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3de1:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3de5:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3ded:	31 c9                	xor    %ecx,%ecx
    3def:	48 89 c6             	mov    %rax,%rsi
    3df2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3df8:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3dfc:	48 8b 40 28          	mov    0x28(%rax),%rax
    3e00:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3e04:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3e0a:	74 1c                	je     3e28 <timer_thread+0x378>
    3e0c:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3e16:	48 05 00 02 00 00    	add    $0x200,%rax
    3e1c:	48 39 d0             	cmp    %rdx,%rax
    3e1f:	74 26                	je     3e47 <timer_thread+0x397>
    3e21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3e28:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3e32:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3e38:	c7 80 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3e42:	48 39 d0             	cmp    %rdx,%rax
    3e45:	75 e1                	jne    3e28 <timer_thread+0x378>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3e47:	48 83 c1 08          	add    $0x8,%rcx
    3e4b:	48 39 f9             	cmp    %rdi,%rcx
    3e4e:	75 a8                	jne    3df8 <timer_thread+0x348>
    asm volatile ("mfence" ::: "memory");
    3e50:	0f ae f0             	mfence
    3e53:	48 8d 3d 26 32 00 00 	lea    0x3226(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3e5a:	e8 91 e4 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3e5f:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
    3e67:	48 8d 3d 19 32 00 00 	lea    0x3219(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3e6e:	e8 7d e4 ff ff       	call   22f0 <puts@plt>
}
    3e73:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3e78:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3e81:	75 47                	jne    3eca <timer_thread+0x41a>
    3e83:	48 83 c4 58          	add    $0x58,%rsp
    3e87:	31 c0                	xor    %eax,%eax
    3e89:	5b                   	pop    %rbx
    3e8a:	5d                   	pop    %rbp
    3e8b:	41 5c                	pop    %r12
    3e8d:	41 5d                	pop    %r13
    3e8f:	41 5e                	pop    %r14
    3e91:	41 5f                	pop    %r15
    3e93:	c3                   	ret
    3e94:	48 89 ef             	mov    %rbp,%rdi
    3e97:	e8 54 e4 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3e9c:	49 8b 47 10          	mov    0x10(%r15),%rax
    3ea0:	be 01 00 00 00       	mov    $0x1,%esi
    3ea5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ea9:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3ead:	8b 78 50             	mov    0x50(%rax),%edi
    3eb0:	e8 4b e5 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3eb5:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3eb9:	39 d9                	cmp    %ebx,%ecx
    3ebb:	0f 8e 0c ff ff ff    	jle    3dcd <timer_thread+0x31d>
    3ec1:	49 8b 47 10          	mov    0x10(%r15),%rax
    3ec5:	e9 e6 fe ff ff       	jmp    3db0 <timer_thread+0x300>
}
    3eca:	e8 61 e4 ff ff       	call   2330 <__stack_chk_fail@plt>
    3ecf:	90                   	nop

0000000000003ed0 <strtolower>:
void strtolower(char *str) {
    3ed0:	f3 0f 1e fa          	endbr64
    3ed4:	55                   	push   %rbp
    3ed5:	53                   	push   %rbx
    3ed6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3eda:	48 0f be 1f          	movsbq (%rdi),%rbx
    3ede:	84 db                	test   %bl,%bl
    3ee0:	74 24                	je     3f06 <strtolower+0x36>
    3ee2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3ee5:	e8 26 e6 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3eea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3ef0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3ef3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3ef7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3efa:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3efd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3f02:	84 db                	test   %bl,%bl
    3f04:	75 ea                	jne    3ef0 <strtolower+0x20>
}
    3f06:	48 83 c4 08          	add    $0x8,%rsp
    3f0a:	5b                   	pop    %rbx
    3f0b:	5d                   	pop    %rbp
    3f0c:	c3                   	ret
    3f0d:	0f 1f 00             	nopl   (%rax)

0000000000003f10 <zh_malloc>:
void *zh_malloc(size_t size) {
    3f10:	f3 0f 1e fa          	endbr64
    3f14:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3f18:	e8 f3 e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3f1d:	48 85 c0             	test   %rax,%rax
    3f20:	74 05                	je     3f27 <zh_malloc+0x17>
}
    3f22:	48 83 c4 08          	add    $0x8,%rsp
    3f26:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3f27:	48 8b 0d f2 60 00 00 	mov    0x60f2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    3f2e:	ba 28 00 00 00       	mov    $0x28,%edx
    3f33:	be 01 00 00 00       	mov    $0x1,%esi
    3f38:	48 8d 3d d1 34 00 00 	lea    0x34d1(%rip),%rdi        # 7410 <_IO_stdin_used+0x410>
    3f3f:	e8 7c e5 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    3f44:	bf 01 00 00 00       	mov    $0x1,%edi
    3f49:	e8 52 e5 ff ff       	call   24a0 <exit@plt>
    3f4e:	66 90                	xchg   %ax,%ax

0000000000003f50 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3f50:	f3 0f 1e fa          	endbr64
    3f54:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    3f55:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3f5a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3f5d:	e8 fe e3 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3f62:	48 85 c0             	test   %rax,%rax
    3f65:	74 11                	je     3f78 <get_filename_ext+0x28>
    3f67:	48 39 c3             	cmp    %rax,%rbx
    3f6a:	74 0c                	je     3f78 <get_filename_ext+0x28>
    return dot + 1;
    3f6c:	48 83 c0 01          	add    $0x1,%rax
}
    3f70:	5b                   	pop    %rbx
    3f71:	c3                   	ret
    3f72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    3f78:	48 8d 05 50 31 00 00 	lea    0x3150(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    3f7f:	5b                   	pop    %rbx
    3f80:	c3                   	ret
    3f81:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3f8c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003f90 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3f90:	f3 0f 1e fa          	endbr64
    3f94:	41 55                	push   %r13
    3f96:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3f99:	48 89 fe             	mov    %rdi,%rsi
    3f9c:	41 54                	push   %r12
    3f9e:	55                   	push   %rbp
    3f9f:	48 89 d5             	mov    %rdx,%rbp
    3fa2:	ba 00 04 00 00       	mov    $0x400,%edx
    3fa7:	53                   	push   %rbx
    3fa8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3faf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3fb8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3fc0:	31 c0                	xor    %eax,%eax
    3fc2:	49 89 e4             	mov    %rsp,%r12
    3fc5:	4c 89 e7             	mov    %r12,%rdi
    3fc8:	e8 63 e4 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    3fcd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3fd2:	84 db                	test   %bl,%bl
    3fd4:	74 24                	je     3ffa <send_headers+0x6a>
        *str = (char)tolower(*str);
    3fd6:	e8 35 e5 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3fdb:	48 8b 08             	mov    (%rax),%rcx
    3fde:	4c 89 e0             	mov    %r12,%rax
    3fe1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3fe8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3feb:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3fef:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3ff2:	48 0f be 18          	movsbq (%rax),%rbx
    3ff6:	84 db                	test   %bl,%bl
    3ff8:	75 ee                	jne    3fe8 <send_headers+0x58>
    void *buf = malloc(size);
    3ffa:	bf 11 00 00 00       	mov    $0x11,%edi
    3fff:	e8 0c e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4004:	48 85 c0             	test   %rax,%rax
    4007:	0f 84 7e 04 00 00    	je     448b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    400d:	66 0f 6f 05 ab 39 00 00 	movdqa 0x39ab(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    iov[0].iov_base = zh_malloc(slen);
    4015:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4019:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    401e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4026:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    402a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    402d:	e8 de e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4032:	48 85 c0             	test   %rax,%rax
    4035:	0f 84 50 04 00 00    	je     448b <send_headers+0x4fb>
    403b:	66 0f 6f 05 8d 39 00 00 	movdqa 0x398d(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    iov[1].iov_base = zh_malloc(slen);
    4043:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4047:	4c 89 e7             	mov    %r12,%rdi
    404a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4054:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    405c:	0f 11 00             	movups %xmm0,(%rax)
    405f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4063:	be 2e 00 00 00       	mov    $0x2e,%esi
    4068:	e8 f3 e2 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    406d:	48 85 c0             	test   %rax,%rax
    4070:	0f 84 ea 02 00 00    	je     4360 <send_headers+0x3d0>
    4076:	4c 39 e0             	cmp    %r12,%rax
    4079:	0f 84 e1 02 00 00    	je     4360 <send_headers+0x3d0>
    return dot + 1;
    407f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4083:	48 8d 3d 13 30 00 00 	lea    0x3013(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    408a:	48 89 de             	mov    %rbx,%rsi
    408d:	e8 1e e3 ff ff       	call   23b0 <strcmp@plt>
    4092:	85 c0                	test   %eax,%eax
    4094:	75 20                	jne    40b6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4096:	66 0f 6f 05 42 39 00 00 	movdqa 0x3942(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    409e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40a6:	66 0f 6f 05 42 39 00 00 	movdqa 0x3942(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    40ae:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    40b6:	48 89 de             	mov    %rbx,%rsi
    40b9:	48 8d 3d e1 2f 00 00 	lea    0x2fe1(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    40c0:	e8 eb e2 ff ff       	call   23b0 <strcmp@plt>
    40c5:	85 c0                	test   %eax,%eax
    40c7:	75 20                	jne    40e9 <send_headers+0x159>
    40c9:	66 0f 6f 05 0f 39 00 00 	movdqa 0x390f(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    40d1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40d9:	66 0f 6f 05 0f 39 00 00 	movdqa 0x390f(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    40e1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    40e9:	48 89 de             	mov    %rbx,%rsi
    40ec:	48 8d 3d b3 2f 00 00 	lea    0x2fb3(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    40f3:	e8 b8 e2 ff ff       	call   23b0 <strcmp@plt>
    40f8:	85 c0                	test   %eax,%eax
    40fa:	0f 84 10 02 00 00    	je     4310 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4100:	48 89 de             	mov    %rbx,%rsi
    4103:	48 8d 3d a0 2f 00 00 	lea    0x2fa0(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    410a:	e8 a1 e2 ff ff       	call   23b0 <strcmp@plt>
    410f:	85 c0                	test   %eax,%eax
    4111:	0f 84 a9 02 00 00    	je     43c0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4117:	48 89 de             	mov    %rbx,%rsi
    411a:	48 8d 3d 8d 2f 00 00 	lea    0x2f8d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4121:	e8 8a e2 ff ff       	call   23b0 <strcmp@plt>
    4126:	85 c0                	test   %eax,%eax
    4128:	0f 84 6a 02 00 00    	je     4398 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    412e:	48 89 de             	mov    %rbx,%rsi
    4131:	48 8d 3d b9 2f 00 00 	lea    0x2fb9(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4138:	e8 73 e2 ff ff       	call   23b0 <strcmp@plt>
    413d:	85 c0                	test   %eax,%eax
    413f:	0f 84 2b 02 00 00    	je     4370 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4145:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4148:	0f 84 52 01 00 00    	je     42a0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    414e:	48 89 de             	mov    %rbx,%rsi
    4151:	48 8d 3d 5a 2f 00 00 	lea    0x2f5a(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    4158:	e8 53 e2 ff ff       	call   23b0 <strcmp@plt>
    415d:	85 c0                	test   %eax,%eax
    415f:	0f 84 ab 02 00 00    	je     4410 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4165:	48 89 de             	mov    %rbx,%rsi
    4168:	48 8d 3d 47 2f 00 00 	lea    0x2f47(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    416f:	e8 3c e2 ff ff       	call   23b0 <strcmp@plt>
    4174:	85 c0                	test   %eax,%eax
    4176:	0f 84 6c 02 00 00    	je     43e8 <send_headers+0x458>
    slen = strlen(send_buffer);
    417c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4184:	4c 89 e7             	mov    %r12,%rdi
    4187:	e8 94 e1 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    418c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    418f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4192:	e8 79 e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4197:	48 85 c0             	test   %rax,%rax
    419a:	0f 84 eb 02 00 00    	je     448b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    41a0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    41a4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    41a8:	83 fb 08             	cmp    $0x8,%ebx
    41ab:	0f 83 3f 01 00 00    	jae    42f0 <send_headers+0x360>
    41b1:	f6 c3 04             	test   $0x4,%bl
    41b4:	0f 85 7b 02 00 00    	jne    4435 <send_headers+0x4a5>
    41ba:	85 db                	test   %ebx,%ebx
    41bc:	74 13                	je     41d1 <send_headers+0x241>
    41be:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    41c6:	88 10                	mov    %dl,(%rax)
    41c8:	f6 c3 02             	test   $0x2,%bl
    41cb:	0f 85 96 02 00 00    	jne    4467 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    41d1:	4d 89 e8             	mov    %r13,%r8
    41d4:	48 8d 0d df 2e 00 00 	lea    0x2edf(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    41db:	4c 89 e7             	mov    %r12,%rdi
    41de:	31 c0                	xor    %eax,%eax
    41e0:	ba 00 04 00 00       	mov    $0x400,%edx
    41e5:	be 01 00 00 00       	mov    $0x1,%esi
    41ea:	e8 31 e3 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    41ef:	4c 89 e7             	mov    %r12,%rdi
    41f2:	e8 29 e1 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    41f7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    41fa:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    41fd:	e8 0e e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4202:	48 85 c0             	test   %rax,%rax
    4205:	0f 84 80 02 00 00    	je     448b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    420b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    420f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4213:	83 fb 08             	cmp    $0x8,%ebx
    4216:	0f 83 1c 01 00 00    	jae    4338 <send_headers+0x3a8>
    421c:	f6 c3 04             	test   $0x4,%bl
    421f:	0f 85 29 02 00 00    	jne    444e <send_headers+0x4be>
    4225:	85 db                	test   %ebx,%ebx
    4227:	74 13                	je     423c <send_headers+0x2ac>
    4229:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4231:	88 10                	mov    %dl,(%rax)
    4233:	f6 c3 02             	test   $0x2,%bl
    4236:	0f 85 3d 02 00 00    	jne    4479 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    423c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4241:	bf 02 00 00 00       	mov    $0x2,%edi
    4246:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    424e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4256:	e8 b5 e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    425b:	48 85 c0             	test   %rax,%rax
    425e:	0f 84 27 02 00 00    	je     448b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4264:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    426c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4270:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4278:	66 89 10             	mov    %dx,(%rax)
}
    427b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4283:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    428c:	0f 85 20 02 00 00    	jne    44b2 <send_headers+0x522>
    4292:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4299:	5b                   	pop    %rbx
    429a:	5d                   	pop    %rbp
    429b:	41 5c                	pop    %r12
    429d:	41 5d                	pop    %r13
    429f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    42a0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    42a4:	0f 85 a4 fe ff ff    	jne    414e <send_headers+0x1be>
    42aa:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    42ae:	0f 85 9a fe ff ff    	jne    414e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    42b4:	66 0f 6f 05 84 37 00 00 	movdqa 0x3784(%rip),%xmm0        # 7a40 <_IO_stdin_used+0xa40>
    42bc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    42c6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    42ce:	66 0f 6f 05 7a 37 00 00 	movdqa 0x377a(%rip),%xmm0        # 7a50 <_IO_stdin_used+0xa50>
    42d6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    42de:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    42e6:	e9 63 fe ff ff       	jmp    414e <send_headers+0x1be>
    42eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    42f0:	89 da                	mov    %ebx,%edx
    42f2:	48 89 c7             	mov    %rax,%rdi
    42f5:	4c 89 e6             	mov    %r12,%rsi
    42f8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    42fd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4302:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4305:	c1 e9 03             	shr    $0x3,%ecx
    4308:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    430b:	e9 c1 fe ff ff       	jmp    41d1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4310:	66 0f 6f 05 c8 36 00 00 	movdqa 0x36c8(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    4318:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4320:	66 0f 6f 05 d8 36 00 00 	movdqa 0x36d8(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4328:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4330:	e9 cb fd ff ff       	jmp    4100 <send_headers+0x170>
    4335:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4338:	89 da                	mov    %ebx,%edx
    433a:	48 89 c7             	mov    %rax,%rdi
    433d:	4c 89 e6             	mov    %r12,%rsi
    4340:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4345:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    434a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    434d:	c1 e9 03             	shr    $0x3,%ecx
    4350:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4353:	e9 e4 fe ff ff       	jmp    423c <send_headers+0x2ac>
    4358:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4360:	48 8d 1d 68 2d 00 00 	lea    0x2d68(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4367:	e9 94 fd ff ff       	jmp    4100 <send_headers+0x170>
    436c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4370:	66 0f 6f 05 a8 36 00 00 	movdqa 0x36a8(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    4378:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4380:	66 0f 6f 05 a8 36 00 00 	movdqa 0x36a8(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
    4388:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4390:	e9 b0 fd ff ff       	jmp    4145 <send_headers+0x1b5>
    4395:	0f 1f 00             	nopl   (%rax)
    4398:	66 0f 6f 05 80 36 00 00 	movdqa 0x3680(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    43a0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    43a8:	66 0f 6f 05 80 36 00 00 	movdqa 0x3680(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
    43b0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    43b8:	e9 71 fd ff ff       	jmp    412e <send_headers+0x19e>
    43bd:	0f 1f 00             	nopl   (%rax)
    43c0:	66 0f 6f 05 18 36 00 00 	movdqa 0x3618(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    43c8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    43d0:	66 0f 6f 05 38 36 00 00 	movdqa 0x3638(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    43d8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    43e0:	e9 32 fd ff ff       	jmp    4117 <send_headers+0x187>
    43e5:	0f 1f 00             	nopl   (%rax)
    43e8:	66 0f 6f 05 30 36 00 00 	movdqa 0x3630(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    43f0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    43f8:	66 0f 6f 05 70 36 00 00 	movdqa 0x3670(%rip),%xmm0        # 7a70 <_IO_stdin_used+0xa70>
    4400:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4408:	e9 6f fd ff ff       	jmp    417c <send_headers+0x1ec>
    440d:	0f 1f 00             	nopl   (%rax)
    4410:	66 0f 6f 05 08 36 00 00 	movdqa 0x3608(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    4418:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4420:	66 0f 6f 05 38 36 00 00 	movdqa 0x3638(%rip),%xmm0        # 7a60 <_IO_stdin_used+0xa60>
    4428:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4430:	e9 30 fd ff ff       	jmp    4165 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4435:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    443c:	89 db                	mov    %ebx,%ebx
    443e:	89 10                	mov    %edx,(%rax)
    4440:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4445:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4449:	e9 83 fd ff ff       	jmp    41d1 <send_headers+0x241>
    444e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4455:	89 db                	mov    %ebx,%ebx
    4457:	89 10                	mov    %edx,(%rax)
    4459:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    445e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4462:	e9 d5 fd ff ff       	jmp    423c <send_headers+0x2ac>
    4467:	89 db                	mov    %ebx,%ebx
    4469:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    446f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4474:	e9 58 fd ff ff       	jmp    41d1 <send_headers+0x241>
    4479:	89 db                	mov    %ebx,%ebx
    447b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4481:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4486:	e9 b1 fd ff ff       	jmp    423c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    448b:	48 8b 0d 8e 5b 00 00 	mov    0x5b8e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4492:	ba 28 00 00 00       	mov    $0x28,%edx
    4497:	be 01 00 00 00       	mov    $0x1,%esi
    449c:	48 8d 3d 6d 2f 00 00 	lea    0x2f6d(%rip),%rdi        # 7410 <_IO_stdin_used+0x410>
    44a3:	e8 18 e0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    44a8:	bf 01 00 00 00       	mov    $0x1,%edi
    44ad:	e8 ee df ff ff       	call   24a0 <exit@plt>
}
    44b2:	e8 79 de ff ff       	call   2330 <__stack_chk_fail@plt>
    44b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000044c0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    44c0:	f3 0f 1e fa          	endbr64
    44c4:	41 55                	push   %r13
    44c6:	49 89 d5             	mov    %rdx,%r13
    44c9:	41 54                	push   %r12
    44cb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    44ce:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    44d1:	55                   	push   %rbp
    44d2:	53                   	push   %rbx
    44d3:	48 89 f3             	mov    %rsi,%rbx
    44d6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    44da:	e8 31 df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    44df:	48 85 c0             	test   %rax,%rax
    44e2:	74 6b                	je     454f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    44e4:	4c 89 e7             	mov    %r12,%rdi
    44e7:	48 89 c5             	mov    %rax,%rbp
    44ea:	31 f6                	xor    %esi,%esi
    44ec:	31 c0                	xor    %eax,%eax
    44ee:	e8 8d df ff ff       	call   2480 <open@plt>
    44f3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    44f6:	85 c0                	test   %eax,%eax
    44f8:	0f 88 58 e0 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    44fe:	48 89 da             	mov    %rbx,%rdx
    4501:	48 89 ee             	mov    %rbp,%rsi
    4504:	89 c7                	mov    %eax,%edi
    4506:	e8 85 de ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    450b:	48 98                	cltq
    450d:	48 39 d8             	cmp    %rbx,%rax
    4510:	7c 1e                	jl     4530 <copy_file_contents+0x70>
    close(fd);
    4512:	44 89 e7             	mov    %r12d,%edi
    4515:	e8 56 de ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    451a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    451e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4522:	48 83 c4 08          	add    $0x8,%rsp
    4526:	5b                   	pop    %rbx
    4527:	5d                   	pop    %rbp
    4528:	41 5c                	pop    %r12
    452a:	41 5d                	pop    %r13
    452c:	c3                   	ret
    452d:	0f 1f 00             	nopl   (%rax)
    4530:	48 8b 0d e9 5a 00 00 	mov    0x5ae9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4537:	ba 1a 00 00 00       	mov    $0x1a,%edx
    453c:	be 01 00 00 00       	mov    $0x1,%esi
    4541:	48 8d 3d 88 2b 00 00 	lea    0x2b88(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    4548:	e8 73 df ff ff       	call   24c0 <fwrite@plt>
    454d:	eb c3                	jmp    4512 <copy_file_contents+0x52>
    454f:	48 8b 0d ca 5a 00 00 	mov    0x5aca(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4556:	ba 28 00 00 00       	mov    $0x28,%edx
    455b:	be 01 00 00 00       	mov    $0x1,%esi
    4560:	48 8d 3d a9 2e 00 00 	lea    0x2ea9(%rip),%rdi        # 7410 <_IO_stdin_used+0x410>
    4567:	e8 54 df ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    456c:	bf 01 00 00 00       	mov    $0x1,%edi
    4571:	e8 2a df ff ff       	call   24a0 <exit@plt>
    4576:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004580 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4580:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4584:	8b 46 44             	mov    0x44(%rsi),%eax
    4587:	48 89 fa             	mov    %rdi,%rdx
    458a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    458d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4593:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4596:	48 8b 07             	mov    (%rdi),%rax
    4599:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    459c:	f6 c1 02             	test   $0x2,%cl
    459f:	74 00                	je     45a1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    45a1:	89 f0                	mov    %esi,%eax
    45a3:	44 29 c0             	sub    %r8d,%eax
    45a6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    45a9:	0f 82 b3 df ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    45af:	c1 e9 0a             	shr    $0xa,%ecx
    45b2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    45b6:	8b 47 44             	mov    0x44(%rdi),%eax
    45b9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    45bc:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    45bf:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    45c2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    45c5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    45c9:	d3 e0                	shl    %cl,%eax
    45cb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    45ce:	48 c1 e0 06          	shl    $0x6,%rax
    45d2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    45d6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    45dc:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    45df:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    45e3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    45e9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    45f1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    45f5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    45f8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    45ff:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4607:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    460b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    460f:	e8 2c dd ff ff       	call   2340 <io_uring_submit@plt>
}
    4614:	31 c0                	xor    %eax,%eax
    4616:	48 83 c4 08          	add    $0x8,%rsp
    461a:	c3                   	ret
    461b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004620 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4620:	f3 0f 1e fa          	endbr64
    4624:	41 55                	push   %r13
    4626:	41 89 fd             	mov    %edi,%r13d
    4629:	41 54                	push   %r12
    462b:	55                   	push   %rbp
    462c:	53                   	push   %rbx
    462d:	48 89 f3             	mov    %rsi,%rbx
    4630:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4634:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4637:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    463d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4640:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4643:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4645:	f6 c1 02             	test   $0x2,%cl
    4648:	74 00                	je     464a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    464a:	89 c2                	mov    %eax,%edx
    464c:	29 f2                	sub    %esi,%edx
    464e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4651:	0f 82 1b df ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4657:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    465a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    465d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4660:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4665:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4668:	23 6b 58             	and    0x58(%rbx),%ebp
    466b:	d3 e5                	shl    %cl,%ebp
    466d:	48 c1 e5 06          	shl    $0x6,%rbp
    4671:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4675:	e8 96 dd ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    467a:	be 01 00 00 00       	mov    $0x1,%esi
    467f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4684:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4687:	e8 14 dd ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    468c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4691:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4695:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4698:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    469d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    46a2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    46ab:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    46b3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    46b7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    46bb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    46c2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    46ca:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    46ce:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    46d6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    46de:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    46e2:	e8 59 dc ff ff       	call   2340 <io_uring_submit@plt>
}
    46e7:	48 83 c4 08          	add    $0x8,%rsp
    46eb:	31 c0                	xor    %eax,%eax
    46ed:	5b                   	pop    %rbx
    46ee:	5d                   	pop    %rbp
    46ef:	41 5c                	pop    %r12
    46f1:	41 5d                	pop    %r13
    46f3:	c3                   	ret
    46f4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    46ff:	90                   	nop

0000000000004700 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4700:	f3 0f 1e fa          	endbr64
    4704:	41 56                	push   %r14
    4706:	41 89 f6             	mov    %esi,%r14d
    4709:	41 55                	push   %r13
    470b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    470e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4713:	41 54                	push   %r12
    4715:	55                   	push   %rbp
    4716:	48 89 d5             	mov    %rdx,%rbp
    4719:	53                   	push   %rbx
    void *buf = malloc(size);
    471a:	e8 f1 dc ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    471f:	48 85 c0             	test   %rax,%rax
    4722:	0f 84 dd 00 00 00    	je     4805 <_send_static_string_content+0x105>
    4728:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    472b:	4c 89 ef             	mov    %r13,%rdi
    472e:	e8 ed db ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4733:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    473a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    473e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4741:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4744:	e8 c7 dc ff ff       	call   2410 <malloc@plt>
    4749:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    474c:	48 85 c0             	test   %rax,%rax
    474f:	0f 84 b0 00 00 00    	je     4805 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4755:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4759:	4c 89 e2             	mov    %r12,%rdx
    475c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    475f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4763:	e8 78 dc ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4768:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    476b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4771:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4774:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4778:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    477a:	f6 c1 02             	test   $0x2,%cl
    477d:	0f 85 7d 00 00 00    	jne    4800 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4783:	89 d0                	mov    %edx,%eax
    4785:	29 f0                	sub    %esi,%eax
    4787:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    478a:	0f 82 ec dd ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4790:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4793:	8b 45 44             	mov    0x44(%rbp),%eax
    4796:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4799:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    479c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    479f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    47a2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    47a8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    47ac:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    47ae:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    47b1:	48 89 ef             	mov    %rbp,%rdi
    47b4:	48 c1 e0 06          	shl    $0x6,%rax
    47b8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    47bc:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    47bf:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    47c3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    47c9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    47d1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    47d5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    47d8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    47df:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    47e7:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    47eb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    47ef:	5b                   	pop    %rbx
    47f0:	5d                   	pop    %rbp
    47f1:	41 5c                	pop    %r12
    47f3:	41 5d                	pop    %r13
    47f5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    47f7:	e9 44 db ff ff       	jmp    2340 <io_uring_submit@plt>
    47fc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4800:	e9 7e ff ff ff       	jmp    4783 <_send_static_string_content+0x83>
    4805:	48 8b 0d 14 58 00 00 	mov    0x5814(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    480c:	ba 28 00 00 00       	mov    $0x28,%edx
    4811:	be 01 00 00 00       	mov    $0x1,%esi
    4816:	48 8d 3d f3 2b 00 00 	lea    0x2bf3(%rip),%rdi        # 7410 <_IO_stdin_used+0x410>
    481d:	e8 9e dc ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4822:	bf 01 00 00 00       	mov    $0x1,%edi
    4827:	e8 74 dc ff ff       	call   24a0 <exit@plt>
    482c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004830 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4830:	f3 0f 1e fa          	endbr64
    4834:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4837:	89 fe                	mov    %edi,%esi
    4839:	48 8b 3d d8 57 00 00 	mov    0x57d8(%rip),%rdi        # a018 <unimplemented_content>
    4840:	e9 bb fe ff ff       	jmp    4700 <_send_static_string_content>
    4845:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004850 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4850:	f3 0f 1e fa          	endbr64
    4854:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4857:	89 fe                	mov    %edi,%esi
    4859:	48 8b 3d b0 57 00 00 	mov    0x57b0(%rip),%rdi        # a010 <http_404_content>
    4860:	e9 9b fe ff ff       	jmp    4700 <_send_static_string_content>
    4865:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004870 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4870:	f3 0f 1e fa          	endbr64
    4874:	41 56                	push   %r14
    4876:	41 55                	push   %r13
    4878:	49 89 d5             	mov    %rdx,%r13
    487b:	41 54                	push   %r12
    487d:	41 89 f4             	mov    %esi,%r12d
    4880:	55                   	push   %rbp
    4881:	48 89 fd             	mov    %rdi,%rbp
    4884:	53                   	push   %rbx
    4885:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    488c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4895:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    489d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    489f:	e8 7c da ff ff       	call   2320 <strlen@plt>
    48a4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    48a9:	48 89 c3             	mov    %rax,%rbx
    48ac:	0f 84 b6 00 00 00    	je     4968 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    48b2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    48b7:	48 89 ee             	mov    %rbp,%rsi
    48ba:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    48be:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    48c3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    48cb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    48d3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    48de:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    48e6:	e8 d5 da ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    48eb:	48 89 e6             	mov    %rsp,%rsi
    48ee:	4c 89 f7             	mov    %r14,%rdi
    48f1:	e8 da da ff ff       	call   23d0 <stat@plt>
    48f6:	83 f8 ff             	cmp    $0xffffffff,%eax
    48f9:	0f 84 d3 00 00 00    	je     49d2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    48ff:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4903:	25 00 f0 00 00       	and    $0xf000,%eax
    4908:	3d 00 80 00 00       	cmp    $0x8000,%eax
    490d:	0f 84 f5 00 00 00    	je     4a08 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4913:	48 8b 3d f6 56 00 00 	mov    0x56f6(%rip),%rdi        # a010 <http_404_content>
    491a:	4c 89 ea             	mov    %r13,%rdx
    491d:	44 89 e6             	mov    %r12d,%esi
    4920:	e8 db fd ff ff       	call   4700 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4925:	4c 89 f2             	mov    %r14,%rdx
    4928:	bf 01 00 00 00       	mov    $0x1,%edi
    492d:	31 c0                	xor    %eax,%eax
    492f:	48 8d 35 ea 27 00 00 	lea    0x27ea(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    4936:	e8 15 db ff ff       	call   2450 <__printf_chk@plt>
}
    493b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4943:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    494c:	0f 85 20 01 00 00    	jne    4a72 <handle_get_method+0x202>
    4952:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4959:	5b                   	pop    %rbx
    495a:	5d                   	pop    %rbp
    495b:	41 5c                	pop    %r12
    495d:	41 5d                	pop    %r13
    495f:	41 5e                	pop    %r14
    4961:	c3                   	ret
    4962:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4968:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    496d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4975:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    497a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    497d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4985:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4988:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4990:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    499b:	e8 20 da ff ff       	call   23c0 <__memcpy_chk@plt>
    49a0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    49a5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    49aa:	48 8d 35 3a 27 00 00 	lea    0x273a(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    49b1:	48 29 d9             	sub    %rbx,%rcx
    49b4:	ba 0b 00 00 00       	mov    $0xb,%edx
    49b9:	e8 02 da ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    49be:	48 89 e6             	mov    %rsp,%rsi
    49c1:	4c 89 f7             	mov    %r14,%rdi
    49c4:	e8 07 da ff ff       	call   23d0 <stat@plt>
    49c9:	83 f8 ff             	cmp    $0xffffffff,%eax
    49cc:	0f 85 2d ff ff ff    	jne    48ff <handle_get_method+0x8f>
    49d2:	4c 89 f2             	mov    %r14,%rdx
    49d5:	48 89 e9             	mov    %rbp,%rcx
    49d8:	48 8d 35 17 27 00 00 	lea    0x2717(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    49df:	31 c0                	xor    %eax,%eax
    49e1:	bf 01 00 00 00       	mov    $0x1,%edi
    49e6:	e8 65 da ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    49eb:	48 8b 3d 1e 56 00 00 	mov    0x561e(%rip),%rdi        # a010 <http_404_content>
    49f2:	4c 89 ea             	mov    %r13,%rdx
    49f5:	44 89 e6             	mov    %r12d,%esi
    49f8:	e8 03 fd ff ff       	call   4700 <_send_static_string_content>
}
    49fd:	e9 39 ff ff ff       	jmp    493b <handle_get_method+0xcb>
    4a02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4a08:	bf 70 00 00 00       	mov    $0x70,%edi
    4a0d:	e8 fe d9 ff ff       	call   2410 <malloc@plt>
    4a12:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4a15:	48 85 c0             	test   %rax,%rax
    4a18:	74 5d                	je     4a77 <handle_get_method+0x207>
            req->client_socket = client_socket;
    4a1a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4a1e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4a23:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4a27:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    4a2a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4a31:	e8 5a f5 ff ff       	call   3f90 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4a36:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4a3b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4a3f:	4c 89 f7             	mov    %r14,%rdi
    4a42:	e8 79 fa ff ff       	call   44c0 <copy_file_contents>
    4a47:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4a4c:	4c 89 f2             	mov    %r14,%rdx
    4a4f:	31 c0                	xor    %eax,%eax
    4a51:	48 8d 35 b6 26 00 00 	lea    0x26b6(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4a58:	bf 01 00 00 00       	mov    $0x1,%edi
    4a5d:	e8 ee d9 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    4a62:	4c 89 ee             	mov    %r13,%rsi
    4a65:	48 89 df             	mov    %rbx,%rdi
    4a68:	e8 13 fb ff ff       	call   4580 <add_write_request>
    4a6d:	e9 c9 fe ff ff       	jmp    493b <handle_get_method+0xcb>
}
    4a72:	e8 b9 d8 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4a77:	48 8b 0d a2 55 00 00 	mov    0x55a2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4a7e:	ba 28 00 00 00       	mov    $0x28,%edx
    4a83:	be 01 00 00 00       	mov    $0x1,%esi
    4a88:	48 8d 3d 81 29 00 00 	lea    0x2981(%rip),%rdi        # 7410 <_IO_stdin_used+0x410>
    4a8f:	e8 2c da ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4a94:	bf 01 00 00 00       	mov    $0x1,%edi
    4a99:	e8 02 da ff ff       	call   24a0 <exit@plt>
    4a9e:	66 90                	xchg   %ax,%ax

0000000000004aa0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4aa0:	f3 0f 1e fa          	endbr64
    4aa4:	41 57                	push   %r15
    4aa6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4aa8:	4c 8d 35 d6 25 00 00 	lea    0x25d6(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4aaf:	41 55                	push   %r13
    4ab1:	49 89 d5             	mov    %rdx,%r13
    4ab4:	41 54                	push   %r12
    4ab6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4ab9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4abc:	55                   	push   %rbp
    4abd:	53                   	push   %rbx
    4abe:	48 83 ec 18          	sub    $0x18,%rsp
    4ac2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4acb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4ad0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4ad2:	49 89 e7             	mov    %rsp,%r15
    4ad5:	4c 89 fa             	mov    %r15,%rdx
    4ad8:	e8 a3 d8 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4add:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4ae1:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4ae4:	84 db                	test   %bl,%bl
    4ae6:	74 1d                	je     4b05 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4ae8:	e8 23 da ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4aed:	48 89 ea             	mov    %rbp,%rdx
    4af0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4af3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4af7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4afa:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    4afd:	48 0f be 1a          	movsbq (%rdx),%rbx
    4b01:	84 db                	test   %bl,%bl
    4b03:	75 eb                	jne    4af0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4b05:	4c 89 fa             	mov    %r15,%rdx
    4b08:	4c 89 f6             	mov    %r14,%rsi
    4b0b:	31 ff                	xor    %edi,%edi
    4b0d:	e8 6e d8 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4b12:	48 8d 35 1a 26 00 00 	lea    0x261a(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4b19:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4b1c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    4b1f:	e8 8c d8 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4b24:	4c 89 ea             	mov    %r13,%rdx
    4b27:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4b2a:	85 c0                	test   %eax,%eax
    4b2c:	75 2a                	jne    4b58 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    4b2e:	48 89 df             	mov    %rbx,%rdi
    4b31:	e8 3a fd ff ff       	call   4870 <handle_get_method>
}
    4b36:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4b3b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b44:	75 20                	jne    4b66 <handle_http_method+0xc6>
    4b46:	48 83 c4 18          	add    $0x18,%rsp
    4b4a:	5b                   	pop    %rbx
    4b4b:	5d                   	pop    %rbp
    4b4c:	41 5c                	pop    %r12
    4b4e:	41 5d                	pop    %r13
    4b50:	41 5e                	pop    %r14
    4b52:	41 5f                	pop    %r15
    4b54:	c3                   	ret
    4b55:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4b58:	48 8b 3d b9 54 00 00 	mov    0x54b9(%rip),%rdi        # a018 <unimplemented_content>
    4b5f:	e8 9c fb ff ff       	call   4700 <_send_static_string_content>
}
    4b64:	eb d0                	jmp    4b36 <handle_http_method+0x96>
    4b66:	e8 c5 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
    4b6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004b70 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4b70:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4b74:	85 d2                	test   %edx,%edx
    4b76:	7e 38                	jle    4bb0 <get_line+0x40>
    4b78:	48 63 d2             	movslq %edx,%rdx
    4b7b:	48 83 c7 01          	add    $0x1,%rdi
    4b7f:	48 01 f2             	add    %rsi,%rdx
    4b82:	eb 11                	jmp    4b95 <get_line+0x25>
    4b84:	0f 1f 40 00          	nopl   0x0(%rax)
    4b88:	48 83 c6 01          	add    $0x1,%rsi
    4b8c:	48 83 c7 01          	add    $0x1,%rdi
    4b90:	48 39 d6             	cmp    %rdx,%rsi
    4b93:	74 1b                	je     4bb0 <get_line+0x40>
        dest[i] = src[i];
    4b95:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4b99:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4b9b:	3c 0d                	cmp    $0xd,%al
    4b9d:	75 e9                	jne    4b88 <get_line+0x18>
    4b9f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4ba2:	75 e4                	jne    4b88 <get_line+0x18>
            dest[i] = '\0';
    4ba4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4ba7:	31 c0                	xor    %eax,%eax
    4ba9:	c3                   	ret
    4baa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4bb0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4bb5:	c3                   	ret
    4bb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004bc0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4bc0:	f3 0f 1e fa          	endbr64
    4bc4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4bcb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4bcf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4bd8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4be0:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4be2:	49 89 e2             	mov    %rsp,%r10
    4be5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4bed:	4c 89 d0             	mov    %r10,%rax
    4bf0:	eb 13                	jmp    4c05 <handle_client_request+0x45>
    4bf2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4bf8:	48 83 c0 01          	add    $0x1,%rax
    4bfc:	48 83 c1 01          	add    $0x1,%rcx
    4c00:	4c 39 c8             	cmp    %r9,%rax
    4c03:	74 4b                	je     4c50 <handle_client_request+0x90>
        dest[i] = src[i];
    4c05:	44 0f b6 01          	movzbl (%rcx),%r8d
    4c09:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4c0c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4c10:	75 e6                	jne    4bf8 <handle_client_request+0x38>
    4c12:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4c16:	75 e0                	jne    4bf8 <handle_client_request+0x38>
            dest[i] = '\0';
    4c18:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4c1b:	8b 47 08             	mov    0x8(%rdi),%eax
    4c1e:	48 89 f2             	mov    %rsi,%rdx
    4c21:	4c 89 d7             	mov    %r10,%rdi
    4c24:	89 c6                	mov    %eax,%esi
    4c26:	e8 75 fe ff ff       	call   4aa0 <handle_http_method>
}
    4c2b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4c33:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4c3c:	75 39                	jne    4c77 <handle_client_request+0xb7>
    4c3e:	31 c0                	xor    %eax,%eax
    4c40:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4c47:	c3                   	ret
    4c48:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4c50:	48 8b 0d c9 53 00 00 	mov    0x53c9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c57:	ba 12 00 00 00       	mov    $0x12,%edx
    4c5c:	be 01 00 00 00       	mov    $0x1,%esi
    4c61:	48 8d 3d cf 24 00 00 	lea    0x24cf(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4c68:	e8 53 d8 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4c6d:	bf 01 00 00 00       	mov    $0x1,%edi
    4c72:	e8 29 d8 ff ff       	call   24a0 <exit@plt>
}
    4c77:	e8 b4 d6 ff ff       	call   2330 <__stack_chk_fail@plt>
    4c7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004c80 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4c80:	f3 0f 1e fa          	endbr64
    4c84:	55                   	push   %rbp
    4c85:	53                   	push   %rbx
    4c86:	48 89 cb             	mov    %rcx,%rbx
    4c89:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4c8d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4c90:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4c93:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4c99:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4c9c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4c9f:	f6 c1 02             	test   $0x2,%cl
    4ca2:	74 00                	je     4ca4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4ca4:	41 89 c0             	mov    %eax,%r8d
    4ca7:	45 29 c8             	sub    %r9d,%r8d
    4caa:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4cae:	0f 82 d8 d8 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4cb4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4cb7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4cba:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4cbd:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4cc0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4cc3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4cc7:	d3 e5                	shl    %cl,%ebp
    4cc9:	48 c1 e5 06          	shl    $0x6,%rbp
    4ccd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4cd1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4cd4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4cd9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4ce0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4ce4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4ce8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4cf0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4cf8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4cfc:	e8 0f d7 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4d01:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4d04:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4d0a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4d0e:	48 83 c4 08          	add    $0x8,%rsp
    4d12:	5b                   	pop    %rbx
    4d13:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4d14:	e9 27 d6 ff ff       	jmp    2340 <io_uring_submit@plt>
    4d19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004d20 <io_thread>:
void* io_thread(void *arg) {
    4d20:	f3 0f 1e fa          	endbr64
    4d24:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4d26:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4d28:	41 56                	push   %r14
    4d2a:	41 55                	push   %r13
    4d2c:	41 54                	push   %r12
    4d2e:	55                   	push   %rbp
    4d2f:	48 89 fd             	mov    %rdi,%rbp
    4d32:	53                   	push   %rbx
    4d33:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4d3a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4d43:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4d4b:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4d4f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4d54:	bf 00 01 00 00       	mov    $0x100,%edi
    4d59:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4d5c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4d60:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4d65:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4d6a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4d6f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4d74:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4d7c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4d81:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4d89:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4d8e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4d96:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4d9b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4da3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4da8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4db0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4db5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4dbd:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4dc5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4dcd:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4dd5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4ddd:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4de5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4ded:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4df5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4dfd:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4e05:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4e0d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4e14:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e1c:	e8 cf d5 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4e21:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
    4e25:	31 f6                	xor    %esi,%esi
    4e27:	e8 b4 d6 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4e2c:	31 d2                	xor    %edx,%edx
    4e2e:	be 01 00 00 00       	mov    $0x1,%esi
    4e33:	bf 02 00 00 00       	mov    $0x2,%edi
    4e38:	e8 f3 d6 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4e3d:	83 f8 ff             	cmp    $0xffffffff,%eax
    4e40:	0f 84 88 d7 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    4e46:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4e4b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4e51:	89 c7                	mov    %eax,%edi
    4e53:	41 89 c4             	mov    %eax,%r12d
    4e56:	ba 02 00 00 00       	mov    $0x2,%edx
    4e5b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4e60:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4e68:	e8 93 d4 ff ff       	call   2300 <setsockopt@plt>
    4e6d:	85 c0                	test   %eax,%eax
    4e6f:	0f 88 2d d7 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4e75:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4e7a:	ba 10 00 00 00       	mov    $0x10,%edx
    4e7f:	44 89 e7             	mov    %r12d,%edi
    4e82:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4e8b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4e93:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4e9b:	e8 c0 d5 ff ff       	call   2460 <bind@plt>
    4ea0:	85 c0                	test   %eax,%eax
    4ea2:	0f 88 32 d7 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4ea8:	be 0a 00 00 00       	mov    $0xa,%esi
    4ead:	44 89 e7             	mov    %r12d,%edi
    4eb0:	e8 6b d5 ff ff       	call   2420 <listen@plt>
    4eb5:	85 c0                	test   %eax,%eax
    4eb7:	0f 88 f1 d6 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4ebd:	ba db 18 00 00       	mov    $0x18db,%edx
    4ec2:	48 8d 35 b3 22 00 00 	lea    0x22b3(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4ec9:	bf 01 00 00 00       	mov    $0x1,%edi
    4ece:	31 c0                	xor    %eax,%eax
    4ed0:	e8 7b d5 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4ed5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4eda:	48 89 d9             	mov    %rbx,%rcx
    4edd:	44 89 e7             	mov    %r12d,%edi
    4ee0:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4ee5:	48 89 c6             	mov    %rax,%rsi
    4ee8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4eed:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4ef2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4efa:	e8 81 fd ff ff       	call   4c80 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4eff:	bf 01 00 00 00       	mov    $0x1,%edi
    4f04:	be 10 00 00 00       	mov    $0x10,%esi
    4f09:	e8 92 d4 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    4f0e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4f13:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4f16:	e8 f5 d4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4f1b:	48 85 c0             	test   %rax,%rax
    4f1e:	0f 84 ae 04 00 00    	je     53d2 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    4f24:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4f28:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4f2f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    4f36:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4f3e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4f41:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4f46:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4f48:	f6 c1 02             	test   $0x2,%cl
    4f4b:	0f 85 0f 04 00 00    	jne    5360 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    4f51:	89 d0                	mov    %edx,%eax
    4f53:	29 f0                	sub    %esi,%eax
    4f55:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4f5c:	0f 82 62 d6 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4f62:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4f65:	48 8d 75 50          	lea    0x50(%rbp),%rsi
	sqe->addr3 = 0;
    4f69:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4f6d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4f70:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4f77:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4f7a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4f81:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4f88:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4f8a:	8b 55 50             	mov    0x50(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4f8d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4f92:	48 c1 e0 06          	shl    $0x6,%rax
    4f96:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4f9e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4fa4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4fa7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4faf:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4fb3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4fbb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4fc3:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4fc7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4fcb:	e8 70 d3 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4fd0:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4fd4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4fd9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4fe1:	0f 85 d7 01 00 00    	jne    51be <io_thread+0x49e>
    4fe7:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4fec:	4d 89 ce             	mov    %r9,%r14
    4fef:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4ff4:	0f 1f 40 00          	nopl   0x0(%rax)
    4ff8:	48 8d 3d 93 21 00 00 	lea    0x2193(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    4fff:	e8 ec d2 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5004:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    500b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5012:	c1 e9 0b             	shr    $0xb,%ecx
    5015:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5018:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5020:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5022:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    502a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    502c:	39 d0                	cmp    %edx,%eax
    502e:	74 36                	je     5066 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5030:	89 f8                	mov    %edi,%eax
    5032:	21 d0                	and    %edx,%eax
    5034:	d3 e0                	shl    %cl,%eax
    5036:	48 c1 e0 04          	shl    $0x4,%rax
    503a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5042:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    504a:	0f 85 a8 01 00 00    	jne    51f8 <io_thread+0x4d8>
    5050:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5054:	0f 85 0e 03 00 00    	jne    5368 <io_thread+0x648>
			if (cqe->res < 0)
    505a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    505d:	83 c2 01             	add    $0x1,%edx
    5060:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5062:	85 c0                	test   %eax,%eax
    5064:	79 b2                	jns    5018 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5066:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    506f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5070:	45 31 c0             	xor    %r8d,%r8d
    5073:	31 d2                	xor    %edx,%edx
    5075:	b9 01 00 00 00       	mov    $0x1,%ecx
    507a:	4c 89 f6             	mov    %r14,%rsi
    507d:	48 89 df             	mov    %rbx,%rdi
    5080:	e8 bb d3 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5085:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5088:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    508d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5091:	0f 84 e1 02 00 00    	je     5378 <io_thread+0x658>
    5097:	48 8d 3d 1a 21 00 00 	lea    0x211a(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    509e:	e8 4d d2 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    50a3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    50a8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    50ab:	45 85 ff             	test   %r15d,%r15d
    50ae:	0f 88 e2 d4 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    50b4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    50b7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    50bb:	85 c0                	test   %eax,%eax
    50bd:	0f 88 d5 02 00 00    	js     5398 <io_thread+0x678>
      switch (req->event_type) {
    50c3:	41 83 f8 01          	cmp    $0x1,%r8d
    50c7:	0f 84 7b 01 00 00    	je     5248 <io_thread+0x528>
    50cd:	41 83 f8 02          	cmp    $0x2,%r8d
    50d1:	0f 84 a1 01 00 00    	je     5278 <io_thread+0x558>
    50d7:	45 85 c0             	test   %r8d,%r8d
    50da:	0f 85 50 01 00 00    	jne    5230 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    50e0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    50e5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    50ea:	48 89 d9             	mov    %rbx,%rcx
    50ed:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    50f1:	e8 8a fb ff ff       	call   4c80 <add_accept_request>
              add_read_request(cqe->res, &ring);
    50f6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    50fb:	48 89 de             	mov    %rbx,%rsi
    50fe:	8b 78 08             	mov    0x8(%rax),%edi
    5101:	e8 1a f5 ff ff       	call   4620 <add_read_request>
              free(req);
    5106:	4c 89 e7             	mov    %r12,%rdi
    5109:	e8 b2 d1 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    510e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5113:	48 85 c0             	test   %rax,%rax
    5116:	0f 85 14 01 00 00    	jne    5230 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    511c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5123:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    512a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    512d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5132:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5134:	f6 c1 02             	test   $0x2,%cl
    5137:	74 00                	je     5139 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5139:	89 d0                	mov    %edx,%eax
    513b:	29 f0                	sub    %esi,%eax
    513d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5144:	0f 82 70 d4 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    514a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    514d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5152:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5156:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5159:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5160:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5163:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    516a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5171:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5173:	8b 55 50             	mov    0x50(%rbp),%edx
    5176:	48 c1 e0 06          	shl    $0x6,%rax
    517a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5182:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5188:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    518b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5193:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5197:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    519f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    51a7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    51ab:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    51af:	e8 8c d1 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    51b4:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    51b8:	0f 84 3a fe ff ff    	je     4ff8 <io_thread+0x2d8>
    51be:	48 8d 3d 2c 20 00 00 	lea    0x202c(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    51c5:	e8 26 d1 ff ff       	call   22f0 <puts@plt>
}
    51ca:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    51d2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    51db:	0f 85 18 02 00 00    	jne    53f9 <io_thread+0x6d9>
    51e1:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    51e8:	31 c0                	xor    %eax,%eax
    51ea:	5b                   	pop    %rbx
    51eb:	5d                   	pop    %rbp
    51ec:	41 5c                	pop    %r12
    51ee:	41 5d                	pop    %r13
    51f0:	41 5e                	pop    %r14
    51f2:	41 5f                	pop    %r15
    51f4:	c3                   	ret
    51f5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    51f8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    51fd:	48 85 c0             	test   %rax,%rax
    5200:	0f 84 6a fe ff ff    	je     5070 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5206:	48 83 38 01          	cmpq   $0x1,(%rax)
    520a:	0f 84 68 01 00 00    	je     5378 <io_thread+0x658>
    5210:	48 8d 3d a1 1f 00 00 	lea    0x1fa1(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    5217:	e8 d4 d0 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    521c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5221:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5224:	e9 8b fe ff ff       	jmp    50b4 <io_thread+0x394>
    5229:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5230:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5238:	8b 02                	mov    (%rdx),%eax
    523a:	83 c0 01             	add    $0x1,%eax
    523d:	89 02                	mov    %eax,(%rdx)
}
    523f:	e9 d8 fe ff ff       	jmp    511c <io_thread+0x3fc>
    5244:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5248:	85 c0                	test   %eax,%eax
    524a:	75 74                	jne    52c0 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    524c:	48 8b 0d cd 4d 00 00 	mov    0x4dcd(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5253:	ba 0f 00 00 00       	mov    $0xf,%edx
    5258:	be 01 00 00 00       	mov    $0x1,%esi
    525d:	48 8d 3d 7d 1f 00 00 	lea    0x1f7d(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    5264:	e8 57 d2 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5269:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    526e:	e9 a0 fe ff ff       	jmp    5113 <io_thread+0x3f3>
    5273:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5278:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    527d:	45 31 ff             	xor    %r15d,%r15d
    5280:	85 c0                	test   %eax,%eax
    5282:	7e 20                	jle    52a4 <io_thread+0x584>
    5284:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5288:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    528b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    528f:	48 c1 e0 04          	shl    $0x4,%rax
    5293:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5298:	e8 23 d0 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    529d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    52a2:	7f e4                	jg     5288 <io_thread+0x568>
              close(req->client_socket);
    52a4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    52a9:	e8 c2 d0 ff ff       	call   2370 <close@plt>
              free(req);
    52ae:	4c 89 e7             	mov    %r12,%rdi
    52b1:	e8 0a d0 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    52b6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    52bb:	e9 53 fe ff ff       	jmp    5113 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    52c0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    52c5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    52ca:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    52d2:	eb 11                	jmp    52e5 <io_thread+0x5c5>
    52d4:	0f 1f 40 00          	nopl   0x0(%rax)
    52d8:	48 83 c0 01          	add    $0x1,%rax
    52dc:	48 83 c2 01          	add    $0x1,%rdx
    52e0:	48 39 c6             	cmp    %rax,%rsi
    52e3:	74 4b                	je     5330 <io_thread+0x610>
        dest[i] = src[i];
    52e5:	0f b6 0a             	movzbl (%rdx),%ecx
    52e8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    52ea:	80 f9 0d             	cmp    $0xd,%cl
    52ed:	75 e9                	jne    52d8 <io_thread+0x5b8>
    52ef:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    52f3:	75 e3                	jne    52d8 <io_thread+0x5b8>
            dest[i] = '\0';
    52f5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    52f8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    52fd:	48 89 da             	mov    %rbx,%rdx
    5300:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5305:	e8 96 f7 ff ff       	call   4aa0 <handle_http_method>
              free(req->iov[0].iov_base);
    530a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    530f:	e8 ac cf ff ff       	call   22c0 <free@plt>
              free(req);
    5314:	4c 89 e7             	mov    %r12,%rdi
    5317:	e8 a4 cf ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    531c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5321:	e9 ed fd ff ff       	jmp    5113 <io_thread+0x3f3>
    5326:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5330:	48 8b 0d e9 4c 00 00 	mov    0x4ce9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5337:	ba 12 00 00 00       	mov    $0x12,%edx
    533c:	be 01 00 00 00       	mov    $0x1,%esi
    5341:	48 8d 3d ef 1d 00 00 	lea    0x1def(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5348:	e8 73 d1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    534d:	bf 01 00 00 00       	mov    $0x1,%edi
    5352:	e8 49 d1 ff ff       	call   24a0 <exit@plt>
    5357:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5360:	e9 ec fb ff ff       	jmp    4f51 <io_thread+0x231>
    5365:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5368:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    536d:	e9 94 fe ff ff       	jmp    5206 <io_thread+0x4e6>
    5372:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5378:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5380:	48 8d 3d 1d 1e 00 00 	lea    0x1e1d(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    5387:	8b 02                	mov    (%rdx),%eax
    5389:	83 c0 01             	add    $0x1,%eax
    538c:	89 02                	mov    %eax,(%rdx)
    538e:	e8 5d cf ff ff       	call   22f0 <puts@plt>
    5393:	e9 26 fe ff ff       	jmp    51be <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5398:	f7 d8                	neg    %eax
    539a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    539f:	89 c7                	mov    %eax,%edi
    53a1:	e8 5a d1 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    53a6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    53ab:	be 01 00 00 00       	mov    $0x1,%esi
    53b0:	48 8b 3d 69 4c 00 00 	mov    0x4c69(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    53b7:	48 89 c1             	mov    %rax,%rcx
    53ba:	48 8d 15 7f 20 00 00 	lea    0x207f(%rip),%rdx        # 7440 <_IO_stdin_used+0x440>
    53c1:	31 c0                	xor    %eax,%eax
    53c3:	e8 08 d1 ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    53c8:	bf 01 00 00 00       	mov    $0x1,%edi
    53cd:	e8 ce d0 ff ff       	call   24a0 <exit@plt>
    53d2:	48 8b 0d 47 4c 00 00 	mov    0x4c47(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    53d9:	ba 28 00 00 00       	mov    $0x28,%edx
    53de:	be 01 00 00 00       	mov    $0x1,%esi
    53e3:	48 8d 3d 26 20 00 00 	lea    0x2026(%rip),%rdi        # 7410 <_IO_stdin_used+0x410>
    53ea:	e8 d1 d0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    53ef:	bf 01 00 00 00       	mov    $0x1,%edi
    53f4:	e8 a7 d0 ff ff       	call   24a0 <exit@plt>
}
    53f9:	e8 32 cf ff ff       	call   2330 <__stack_chk_fail@plt>
    53fe:	66 90                	xchg   %ax,%ax

0000000000005400 <sendm>:
int sendm(struct BarrierTask *data) {
    5400:	f3 0f 1e fa          	endbr64
    5404:	41 57                	push   %r15
    5406:	41 56                	push   %r14
    5408:	41 55                	push   %r13
    540a:	41 54                	push   %r12
    540c:	55                   	push   %rbp
    540d:	53                   	push   %rbx
    540e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5412:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
    5419:	0f 85 99 01 00 00    	jne    55b8 <sendm+0x1b8>
    541f:	48 8d b7 80 01 00 00 	lea    0x180(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5426:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    542c:	48 89 fa             	mov    %rdi,%rdx
    542f:	31 c9                	xor    %ecx,%ecx
    5431:	48 89 34 24          	mov    %rsi,(%rsp)
    5435:	48 8d b7 88 01 00 00 	lea    0x188(%rdi),%rsi
    543c:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5441:	85 c0                	test   %eax,%eax
    5443:	0f 8e ce 00 00 00    	jle    5517 <sendm+0x117>
    5449:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5450:	39 8a 30 01 00 00    	cmp    %ecx,0x130(%rdx)
    5456:	0f 84 af 00 00 00    	je     550b <sendm+0x10b>
        struct Data *them = data->mailboxes[n].higher;
    545c:	49 89 ca             	mov    %rcx,%r10
    545f:	49 c1 e2 05          	shl    $0x5,%r10
    5463:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
    546a:	4d 8b 5a 08          	mov    0x8(%r10),%r11
        for (; them->messages_count < min;) {
    546e:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    5472:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    5476:	4c 39 cb             	cmp    %r9,%rbx
    5479:	0f 8d 83 00 00 00    	jge    5502 <sendm+0x102>
    547f:	4c 89 cf             	mov    %r9,%rdi
    5482:	48 8b aa 08 01 00 00 	mov    0x108(%rdx),%rbp
    5489:	4d 8b 72 10          	mov    0x10(%r10),%r14
    548d:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    5490:	49 8b 33             	mov    (%r11),%rsi
    5493:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    5497:	48 83 f8 02          	cmp    $0x2,%rax
    549b:	0f 86 ff 00 00 00    	jbe    55a0 <sendm+0x1a0>
    54a1:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    54a9:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    54b1:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    54b5:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    54b9:	4c 39 2c 24          	cmp    %r13,(%rsp)
    54bd:	73 71                	jae    5530 <sendm+0x130>
    54bf:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    54c4:	4d 39 fc             	cmp    %r15,%r12
    54c7:	73 67                	jae    5530 <sendm+0x130>
    54c9:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    54cd:	49 01 f0             	add    %rsi,%r8
    54d0:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    54d7:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    54db:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    54df:	49 39 d8             	cmp    %rbx,%r8
    54e2:	75 ec                	jne    54d0 <sendm+0xd0>
    54e4:	0f 1f 40 00          	nopl   0x0(%rax)
    54e8:	48 01 fd             	add    %rdi,%rbp
    54eb:	4c 01 f7             	add    %r14,%rdi
    54ee:	48 89 aa 08 01 00 00 	mov    %rbp,0x108(%rdx)
    54f5:	49 89 7a 10          	mov    %rdi,0x10(%r10)
    54f9:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    54fd:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5502:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5505:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    550b:	48 83 c1 01          	add    $0x1,%rcx
    550f:	39 c8                	cmp    %ecx,%eax
    5511:	0f 8f 39 ff ff ff    	jg     5450 <sendm+0x50>
}
    5517:	48 83 c4 18          	add    $0x18,%rsp
    551b:	31 c0                	xor    %eax,%eax
    551d:	5b                   	pop    %rbx
    551e:	5d                   	pop    %rbp
    551f:	41 5c                	pop    %r12
    5521:	41 5d                	pop    %r13
    5523:	41 5e                	pop    %r14
    5525:	41 5f                	pop    %r15
    5527:	c3                   	ret
    5528:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5530:	49 89 fd             	mov    %rdi,%r13
    5533:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    553a:	4d 89 e0             	mov    %r12,%r8
    553d:	49 d1 ed             	shr    %r13
    5540:	49 c1 e5 04          	shl    $0x4,%r13
    5544:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5549:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    554d:	41 83 e5 10          	and    $0x10,%r13d
    5551:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5555:	74 11                	je     5568 <sendm+0x168>
          them->messages[them->messages_count++] = data->message; 
    5557:	49 83 c0 10          	add    $0x10,%r8
    555b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5560:	4d 39 f8             	cmp    %r15,%r8
    5563:	74 15                	je     557a <sendm+0x17a>
    5565:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5568:	41 0f 11 00          	movups %xmm0,(%r8)
    556c:	49 83 c0 20          	add    $0x20,%r8
    5570:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    5575:	4d 39 f8             	cmp    %r15,%r8
    5578:	75 ee                	jne    5568 <sendm+0x168>
    557a:	49 89 f8             	mov    %rdi,%r8
    557d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    5581:	49 01 d8             	add    %rbx,%r8
    5584:	40 f6 c7 01          	test   $0x1,%dil
    5588:	0f 84 5a ff ff ff    	je     54e8 <sendm+0xe8>
          them->messages[them->messages_count++] = data->message; 
    558e:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    5595:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    5599:	e9 4a ff ff ff       	jmp    54e8 <sendm+0xe8>
    559e:	66 90                	xchg   %ax,%ax
    55a0:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    55a8:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    55b0:	e9 14 ff ff ff       	jmp    54c9 <sendm+0xc9>
    55b5:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    55b8:	48 8d 3d 45 1c 00 00 	lea    0x1c45(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    55bf:	e8 2c cd ff ff       	call   22f0 <puts@plt>
    55c4:	e9 4e ff ff ff       	jmp    5517 <sendm+0x117>
    55c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000055d0 <receive>:
int receive(struct BarrierTask *data) {
    55d0:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    55d4:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    55da:	85 c0                	test   %eax,%eax
    55dc:	0f 8e f1 00 00 00    	jle    56d3 <receive+0x103>
int receive(struct BarrierTask *data) {
    55e2:	41 54                	push   %r12
    55e4:	48 89 fa             	mov    %rdi,%rdx
    55e7:	55                   	push   %rbp
    55e8:	31 ed                	xor    %ebp,%ebp
    55ea:	53                   	push   %rbx
    55eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    55f0:	48 89 ee             	mov    %rbp,%rsi
    55f3:	48 c1 e6 05          	shl    $0x5,%rsi
    55f7:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    55fe:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5601:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    5606:	48 85 ff             	test   %rdi,%rdi
    5609:	0f 8e a1 00 00 00    	jle    56b0 <receive+0xe0>
      data->sends++;
    560f:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    5616:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    561a:	4c 63 1a             	movslq (%rdx),%r11
    561d:	49 89 c9             	mov    %rcx,%r9
    5620:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5624:	49 f7 d9             	neg    %r9
    5627:	48 01 c7             	add    %rax,%rdi
    562a:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    562e:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    5635:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    5639:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    563c:	49 29 c8             	sub    %rcx,%r8
    563f:	eb 10                	jmp    5651 <receive+0x81>
    5641:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5648:	48 83 c0 01          	add    $0x1,%rax
    564c:	48 39 c7             	cmp    %rax,%rdi
    564f:	74 5f                	je     56b0 <receive+0xe0>
      data->n++;
    5651:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    5655:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
      data->n++;
    565c:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5663:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5667:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    566b:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5670:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5674:	75 d2                	jne    5648 <receive+0x78>
    5676:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    567d:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5681:	75 c5                	jne    5648 <receive+0x78>
    5683:	bf 01 00 00 00       	mov    $0x1,%edi
    5688:	b9 01 00 00 00       	mov    $0x1,%ecx
    568d:	ba 01 00 00 00       	mov    $0x1,%edx
    5692:	31 c0                	xor    %eax,%eax
    5694:	48 8d 35 cd 1d 00 00 	lea    0x1dcd(%rip),%rsi        # 7468 <_IO_stdin_used+0x468>
    569b:	e8 b0 cd ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    56a0:	bf 01 00 00 00       	mov    $0x1,%edi
    56a5:	e8 f6 cd ff ff       	call   24a0 <exit@plt>
    56aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    56b0:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    56b9:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    56bc:	48 83 c5 01          	add    $0x1,%rbp
    56c0:	39 aa 34 01 00 00    	cmp    %ebp,0x134(%rdx)
    56c6:	0f 8f 24 ff ff ff    	jg     55f0 <receive+0x20>
}
    56cc:	5b                   	pop    %rbx
    56cd:	31 c0                	xor    %eax,%eax
    56cf:	5d                   	pop    %rbp
    56d0:	41 5c                	pop    %r12
    56d2:	c3                   	ret
    56d3:	31 c0                	xor    %eax,%eax
    56d5:	c3                   	ret
    56d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000056e0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    56e0:	f3 0f 1e fa          	endbr64
    56e4:	41 57                	push   %r15
    56e6:	41 56                	push   %r14
    56e8:	41 55                	push   %r13
    56ea:	41 54                	push   %r12
    56ec:	55                   	push   %rbp
    56ed:	53                   	push   %rbx
    56ee:	48 89 fb             	mov    %rdi,%rbx
    56f1:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    56f5:	8b 07                	mov    (%rdi),%eax
    56f7:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    56fd:	0f 84 3d 01 00 00    	je     5840 <barriered_work+0x160>
    receive(data);
    5703:	e8 c8 fe ff ff       	call   55d0 <receive>
    while (data->scheduled == 1) {
    5708:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    570f:	75 1b                	jne    572c <barriered_work+0x4c>
    5711:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    5718:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    5720:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5723:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    572a:	74 ec                	je     5718 <barriered_work+0x38>
  if (data->sending == 1) {
    572c:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    5733:	0f 85 74 02 00 00    	jne    59ad <barriered_work+0x2cd>
      for (int n = 0 ; n < data->thread_count; n++) {
    5739:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    573f:	85 c0                	test   %eax,%eax
    5741:	0f 8e 72 02 00 00    	jle    59b9 <barriered_work+0x2d9>
    5747:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    574e:	31 d2                	xor    %edx,%edx
    5750:	48 89 0c 24          	mov    %rcx,(%rsp)
    5754:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    575b:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    5760:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5766:	0f 84 bf 00 00 00    	je     582b <barriered_work+0x14b>
        struct Data *them = data->mailboxes[n].higher;
    576c:	49 89 d1             	mov    %rdx,%r9
    576f:	49 c1 e1 05          	shl    $0x5,%r9
    5773:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    577a:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    577e:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5782:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5786:	4d 39 c3             	cmp    %r8,%r11
    5789:	0f 8d 93 00 00 00    	jge    5822 <barriered_work+0x142>
    578f:	4c 89 c6             	mov    %r8,%rsi
    5792:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5799:	4d 8b 71 10          	mov    0x10(%r9),%r14
    579d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    57a0:	49 8b 0a             	mov    (%r10),%rcx
    57a3:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    57a7:	48 83 f8 02          	cmp    $0x2,%rax
    57ab:	0f 86 8f 02 00 00    	jbe    5a40 <barriered_work+0x360>
    57b1:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    57b9:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    57c1:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    57c5:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    57c9:	4c 39 2c 24          	cmp    %r13,(%rsp)
    57cd:	0f 83 fd 01 00 00    	jae    59d0 <barriered_work+0x2f0>
    57d3:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    57d8:	4d 39 fc             	cmp    %r15,%r12
    57db:	0f 83 ef 01 00 00    	jae    59d0 <barriered_work+0x2f0>
    57e1:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    57e5:	48 01 cf             	add    %rcx,%rdi
    57e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    57f0:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    57f7:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    57fb:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    57ff:	49 39 fb             	cmp    %rdi,%r11
    5802:	75 ec                	jne    57f0 <barriered_work+0x110>
    5804:	0f 1f 40 00          	nopl   0x0(%rax)
    5808:	48 01 f5             	add    %rsi,%rbp
    580b:	4c 01 f6             	add    %r14,%rsi
    580e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5815:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5819:	4d 89 42 08          	mov    %r8,0x8(%r10)
    581d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5822:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5825:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    582b:	48 83 c2 01          	add    $0x1,%rdx
    582f:	39 d0                	cmp    %edx,%eax
    5831:	0f 8f 29 ff ff ff    	jg     5760 <barriered_work+0x80>
    5837:	e9 7d 01 00 00       	jmp    59b9 <barriered_work+0x2d9>
    583c:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    5840:	e8 8b fd ff ff       	call   55d0 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    5845:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    584c:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    584e:	45 85 c9             	test   %r9d,%r9d
    5851:	0f 8e 85 00 00 00    	jle    58dc <barriered_work+0x1fc>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5857:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    585e:	4c 63 d8             	movslq %eax,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    5861:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5864:	49 c1 e3 09          	shl    $0x9,%r11
    5868:	4c 8b 52 10          	mov    0x10(%rdx),%r10
              int next_task = abs((t + 1) % (data->thread_count));
    586c:	99                   	cltd
    586d:	41 f7 f9             	idiv   %r9d
    5870:	4c 89 d7             	mov    %r10,%rdi
    5873:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
    5877:	89 d0                	mov    %edx,%eax
    5879:	f7 d8                	neg    %eax
    587b:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    587e:	45 31 c0             	xor    %r8d,%r8d
              int next_task = abs((t + 1) % (data->thread_count));
    5881:	48 63 ea             	movslq %edx,%rbp
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5884:	48 c1 e5 09          	shl    $0x9,%rbp
    5888:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    5890:	31 c0                	xor    %eax,%eax
    5892:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5898:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    589c:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    58a0:	48 8b 8c 2a 68 01 00 00 	mov    0x168(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    58a8:	48 8b 17             	mov    (%rdi),%rdx
    58ab:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    58af:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    58b2:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    58b6:	48 c1 e2 05          	shl    $0x5,%rdx
    58ba:	4a 03 94 1e 68 01 00 00 	add    0x168(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    58c2:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    58c6:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    58ca:	49 39 c1             	cmp    %rax,%r9
    58cd:	75 c9                	jne    5898 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    58cf:	48 83 c7 08          	add    $0x8,%rdi
    58d3:	49 83 c0 20          	add    $0x20,%r8
    58d7:	49 39 fc             	cmp    %rdi,%r12
    58da:	75 b4                	jne    5890 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    58dc:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    58df:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    58e6:	31 ff                	xor    %edi,%edi
    58e8:	48 c1 e6 05          	shl    $0x5,%rsi
    58ec:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    58f3:	e8 18 ca ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    58f8:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    58ff:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5906:	48 8b 50 38          	mov    0x38(%rax),%rdx
    590a:	8b 4a 10             	mov    0x10(%rdx),%ecx
    590d:	8d 69 01             	lea    0x1(%rcx),%ebp
    5910:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5913:	75 53                	jne    5968 <barriered_work+0x288>
    5915:	0f 1f 00             	nopl   (%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5918:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    591f:	48 8b 40 10          	mov    0x10(%rax),%rax
    5923:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    5926:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    592e:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5932:	48 c1 e7 09          	shl    $0x9,%rdi
    5936:	48 03 78 28          	add    0x28(%rax),%rdi
    593a:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    5940:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5943:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    594a:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5951:	74 c5                	je     5918 <barriered_work+0x238>
    if (modcount != data->thread->protected_state->modcount) {
    5953:	48 8b 40 38          	mov    0x38(%rax),%rax
    5957:	3b 68 10             	cmp    0x10(%rax),%ebp
    595a:	74 0c                	je     5968 <barriered_work+0x288>
    595c:	48 8d 3d ad 18 00 00 	lea    0x18ad(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    5963:	e8 88 c9 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5968:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    596f:	31 ff                	xor    %edi,%edi
    5971:	48 c1 e6 05          	shl    $0x5,%rsi
    5975:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    597c:	48 83 c6 10          	add    $0x10,%rsi
    5980:	e8 8b c9 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5985:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    598c:	48 83 c0 01          	add    $0x1,%rax
    5990:	48 99                	cqto
    5992:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    5999:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    59a0:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    59a7:	0f 84 a8 00 00 00    	je     5a55 <barriered_work+0x375>
    59ad:	48 8d 3d 50 18 00 00 	lea    0x1850(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    59b4:	e8 37 c9 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    59b9:	0f ae f8             	sfence
}
    59bc:	48 83 c4 18          	add    $0x18,%rsp
    59c0:	31 c0                	xor    %eax,%eax
    59c2:	5b                   	pop    %rbx
    59c3:	5d                   	pop    %rbp
    59c4:	41 5c                	pop    %r12
    59c6:	41 5d                	pop    %r13
    59c8:	41 5e                	pop    %r14
    59ca:	41 5f                	pop    %r15
    59cc:	c3                   	ret
    59cd:	0f 1f 00             	nopl   (%rax)
    59d0:	49 89 f5             	mov    %rsi,%r13
    59d3:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    59da:	4c 89 e7             	mov    %r12,%rdi
    59dd:	49 d1 ed             	shr    %r13
    59e0:	49 c1 e5 04          	shl    $0x4,%r13
    59e4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    59e9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    59ed:	41 83 e5 10          	and    $0x10,%r13d
    59f1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    59f5:	74 11                	je     5a08 <barriered_work+0x328>
          them->messages[them->messages_count++] = data->message; 
    59f7:	48 83 c7 10          	add    $0x10,%rdi
    59fb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5a00:	49 39 ff             	cmp    %rdi,%r15
    5a03:	74 13                	je     5a18 <barriered_work+0x338>
    5a05:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5a08:	0f 11 07             	movups %xmm0,(%rdi)
    5a0b:	48 83 c7 20          	add    $0x20,%rdi
    5a0f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5a13:	49 39 ff             	cmp    %rdi,%r15
    5a16:	75 f0                	jne    5a08 <barriered_work+0x328>
    5a18:	48 89 f7             	mov    %rsi,%rdi
    5a1b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5a1f:	4c 01 df             	add    %r11,%rdi
    5a22:	40 f6 c6 01          	test   $0x1,%sil
    5a26:	0f 84 dc fd ff ff    	je     5808 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    5a2c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5a33:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5a37:	e9 cc fd ff ff       	jmp    5808 <barriered_work+0x128>
    5a3c:	0f 1f 40 00          	nopl   0x0(%rax)
    5a40:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5a48:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5a50:	e9 8c fd ff ff       	jmp    57e1 <barriered_work+0x101>
      for (int n = 0 ; n < data->thread_count; n++) {
    5a55:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    5a5c:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5a62:	31 d2                	xor    %edx,%edx
    5a64:	48 89 0c 24          	mov    %rcx,(%rsp)
    5a68:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    5a6f:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5a74:	85 c0                	test   %eax,%eax
    5a76:	0f 8e 3d ff ff ff    	jle    59b9 <barriered_work+0x2d9>
    5a7c:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5a80:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5a86:	0f 84 af 00 00 00    	je     5b3b <barriered_work+0x45b>
        struct Data *them = data->mailboxes[n].higher;
    5a8c:	49 89 d1             	mov    %rdx,%r9
    5a8f:	49 c1 e1 05          	shl    $0x5,%r9
    5a93:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    5a9a:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    5a9e:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5aa2:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5aa6:	4d 39 d8             	cmp    %r11,%r8
    5aa9:	0f 8e 83 00 00 00    	jle    5b32 <barriered_work+0x452>
    5aaf:	4c 89 c6             	mov    %r8,%rsi
    5ab2:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5ab9:	4d 8b 71 10          	mov    0x10(%r9),%r14
    5abd:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5ac0:	49 8b 0a             	mov    (%r10),%rcx
    5ac3:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5ac7:	48 83 f8 02          	cmp    $0x2,%rax
    5acb:	0f 86 ef 00 00 00    	jbe    5bc0 <barriered_work+0x4e0>
    5ad1:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5ad9:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5ae1:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5ae5:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5ae9:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5aed:	73 61                	jae    5b50 <barriered_work+0x470>
    5aef:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5af4:	4d 39 fc             	cmp    %r15,%r12
    5af7:	73 57                	jae    5b50 <barriered_work+0x470>
    5af9:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5afd:	48 01 cf             	add    %rcx,%rdi
    5b00:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5b07:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5b0b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5b0f:	49 39 fb             	cmp    %rdi,%r11
    5b12:	75 ec                	jne    5b00 <barriered_work+0x420>
    5b14:	0f 1f 40 00          	nopl   0x0(%rax)
    5b18:	48 01 f5             	add    %rsi,%rbp
    5b1b:	4c 01 f6             	add    %r14,%rsi
    5b1e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5b25:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5b29:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5b2d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5b32:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5b35:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5b3b:	48 83 c2 01          	add    $0x1,%rdx
    5b3f:	39 d0                	cmp    %edx,%eax
    5b41:	0f 8f 39 ff ff ff    	jg     5a80 <barriered_work+0x3a0>
    5b47:	e9 6d fe ff ff       	jmp    59b9 <barriered_work+0x2d9>
    5b4c:	0f 1f 40 00          	nopl   0x0(%rax)
    5b50:	49 89 f5             	mov    %rsi,%r13
    5b53:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b5a:	4c 89 e7             	mov    %r12,%rdi
    5b5d:	49 d1 ed             	shr    %r13
    5b60:	49 c1 e5 04          	shl    $0x4,%r13
    5b64:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5b69:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5b6d:	41 83 e5 10          	and    $0x10,%r13d
    5b71:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5b75:	74 11                	je     5b88 <barriered_work+0x4a8>
          them->messages[them->messages_count++] = data->message; 
    5b77:	48 83 c7 10          	add    $0x10,%rdi
    5b7b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5b80:	4c 39 ff             	cmp    %r15,%rdi
    5b83:	74 13                	je     5b98 <barriered_work+0x4b8>
    5b85:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5b88:	0f 11 07             	movups %xmm0,(%rdi)
    5b8b:	48 83 c7 20          	add    $0x20,%rdi
    5b8f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5b93:	4c 39 ff             	cmp    %r15,%rdi
    5b96:	75 f0                	jne    5b88 <barriered_work+0x4a8>
    5b98:	48 89 f7             	mov    %rsi,%rdi
    5b9b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5b9f:	4c 01 df             	add    %r11,%rdi
    5ba2:	40 f6 c6 01          	test   $0x1,%sil
    5ba6:	0f 84 6c ff ff ff    	je     5b18 <barriered_work+0x438>
          them->messages[them->messages_count++] = data->message; 
    5bac:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5bb3:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5bb7:	e9 5c ff ff ff       	jmp    5b18 <barriered_work+0x438>
    5bbc:	0f 1f 40 00          	nopl   0x0(%rax)
    5bc0:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5bc8:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5bd0:	e9 24 ff ff ff       	jmp    5af9 <barriered_work+0x419>
    5bd5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005be0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5be0:	f3 0f 1e fa          	endbr64
    5be4:	41 54                	push   %r12
    5be6:	49 89 fc             	mov    %rdi,%r12
    5be9:	55                   	push   %rbp
    5bea:	53                   	push   %rbx
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5beb:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5bf2:	48 8b 48 40          	mov    0x40(%rax),%rcx
    5bf6:	8b 11                	mov    (%rcx),%edx
    5bf8:	85 d2                	test   %edx,%edx
    5bfa:	7e 1f                	jle    5c1b <barriered_work_ingest+0x3b>
    5bfc:	31 db                	xor    %ebx,%ebx
    5bfe:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    if (data->thread->buffers->buffer[x].available == 1) {
    5c02:	48 89 dd             	mov    %rbx,%rbp
    5c05:	48 c1 e5 05          	shl    $0x5,%rbp
    5c09:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    5c0d:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5c11:	74 1d                	je     5c30 <barriered_work_ingest+0x50>
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5c13:	48 83 c3 01          	add    $0x1,%rbx
    5c17:	39 da                	cmp    %ebx,%edx
    5c19:	7f e7                	jg     5c02 <barriered_work_ingest+0x22>
  asm volatile ("sfence" ::: "memory");
    5c1b:	0f ae f8             	sfence
  barriered_work(data);
    5c1e:	4c 89 e7             	mov    %r12,%rdi
    5c21:	e8 ba fa ff ff       	call   56e0 <barriered_work>
}
    5c26:	5b                   	pop    %rbx
    5c27:	31 c0                	xor    %eax,%eax
    5c29:	5d                   	pop    %rbp
    5c2a:	41 5c                	pop    %r12
    5c2c:	c3                   	ret
    5c2d:	0f 1f 00             	nopl   (%rax)
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers->buffer[x].snapshots[data->thread->buffers->buffer[x].ingest_snapshot].end);
    5c30:	48 63 70 1c          	movslq 0x1c(%rax),%rsi
    5c34:	bf 04 00 00 00       	mov    $0x4,%edi
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5c39:	48 83 c3 01          	add    $0x1,%rbx
      data->ingest_count++;
    5c3d:	49 83 84 24 60 01 00 00 01 	addq   $0x1,0x160(%r12)
      data->thread->buffers->buffer[x].available = 0;
    5c46:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers->buffer[x].snapshots[data->thread->buffers->buffer[x].ingest_snapshot].end);
    5c4d:	48 c1 e6 05          	shl    $0x5,%rsi
    5c51:	48 03 70 10          	add    0x10(%rax),%rsi
    5c55:	48 83 c6 10          	add    $0x10,%rsi
    5c59:	e8 b2 c6 ff ff       	call   2310 <clock_gettime@plt>
      data->thread->buffers->buffer[x].ingest_snapshot = (data->thread->buffers->buffer[x].ingest_snapshot + 1) % data->thread->buffers->buffer[x].snapshot_limit;
    5c5e:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5c66:	48 8b 48 40          	mov    0x40(%rax),%rcx
    5c6a:	48 03 69 08          	add    0x8(%rcx),%rbp
    5c6e:	8b 45 1c             	mov    0x1c(%rbp),%eax
    5c71:	83 c0 01             	add    $0x1,%eax
    5c74:	99                   	cltd
    5c75:	f7 7d 18             	idivl  0x18(%rbp)
    5c78:	89 55 1c             	mov    %edx,0x1c(%rbp)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5c7b:	8b 11                	mov    (%rcx),%edx
    5c7d:	39 da                	cmp    %ebx,%edx
    5c7f:	0f 8f 79 ff ff ff    	jg     5bfe <barriered_work_ingest+0x1e>
    5c85:	eb 94                	jmp    5c1b <barriered_work_ingest+0x3b>
    5c87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005c90 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5c90:	f3 0f 1e fa          	endbr64
}
    5c94:	31 c0                	xor    %eax,%eax
    5c96:	c3                   	ret
    5c97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005ca0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5ca0:	f3 0f 1e fa          	endbr64
    5ca4:	31 c0                	xor    %eax,%eax
    5ca6:	c3                   	ret
    5ca7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005cb0 <after>:
int after(struct timespec left, struct timespec right) {
    5cb0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5cb4:	31 c0                	xor    %eax,%eax
    5cb6:	48 39 d7             	cmp    %rdx,%rdi
    5cb9:	7e 08                	jle    5cc3 <after+0x13>
    5cbb:	31 c0                	xor    %eax,%eax
    5cbd:	48 39 ce             	cmp    %rcx,%rsi
    5cc0:	0f 9f c0             	setg   %al
}
    5cc3:	c3                   	ret
    5cc4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5ccf:	90                   	nop

0000000000005cd0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5cd0:	f3 0f 1e fa          	endbr64
    5cd4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5cd9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5cde:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ce0:	48 39 d7             	cmp    %rdx,%rdi
    5ce3:	7f 18                	jg     5cfd <within+0x2d>
    5ce5:	4d 39 d8             	cmp    %r11,%r8
    5ce8:	0f 9e c2             	setle  %dl
    5ceb:	48 39 ce             	cmp    %rcx,%rsi
    5cee:	0f 9e c0             	setle  %al
    5cf1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5cf3:	31 c0                	xor    %eax,%eax
    5cf5:	4d 39 d1             	cmp    %r10,%r9
    5cf8:	0f 9e c0             	setle  %al
    5cfb:	21 d0                	and    %edx,%eax
}
    5cfd:	c3                   	ret
    5cfe:	66 90                	xchg   %ax,%ax

0000000000005d00 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5d00:	f3 0f 1e fa          	endbr64
    5d04:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5d09:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5d0e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5d13:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5d18:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5d1d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5d22:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5d27:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5d2c:	48 39 fe             	cmp    %rdi,%rsi
    5d2f:	7d 2f                	jge    5d60 <overlap+0x60>
    5d31:	48 39 ca             	cmp    %rcx,%rdx
    5d34:	7d 62                	jge    5d98 <overlap+0x98>
    5d36:	4d 39 da             	cmp    %r11,%r10
    5d39:	7d 0e                	jge    5d49 <overlap+0x49>
    return 1;
    5d3b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5d40:	4d 39 c1             	cmp    %r8,%r9
    5d43:	0f 8c 7f 00 00 00    	jl     5dc8 <overlap+0xc8>
  return 0;
    5d49:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5d4b:	4d 39 c1             	cmp    %r8,%r9
    5d4e:	7f 4c                	jg     5d9c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5d50:	31 c0                	xor    %eax,%eax
    5d52:	4d 39 da             	cmp    %r11,%r10
    5d55:	0f 9e c0             	setle  %al
    5d58:	c3                   	ret
    5d59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5d60:	7e 4e                	jle    5db0 <overlap+0xb0>
    5d62:	48 39 ca             	cmp    %rcx,%rdx
    5d65:	7f 39                	jg     5da0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5d67:	75 31                	jne    5d9a <overlap+0x9a>
    5d69:	4d 39 c1             	cmp    %r8,%r9
    5d6c:	7c 2c                	jl     5d9a <overlap+0x9a>
    return 1;
    5d6e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5d73:	4d 39 da             	cmp    %r11,%r10
    5d76:	7d 24                	jge    5d9c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5d78:	48 39 ca             	cmp    %rcx,%rdx
    5d7b:	0f 94 c2             	sete   %dl
    5d7e:	48 39 fe             	cmp    %rdi,%rsi
    5d81:	0f 94 c0             	sete   %al
    5d84:	21 c2                	and    %eax,%edx
    5d86:	31 c0                	xor    %eax,%eax
    5d88:	4d 39 c1             	cmp    %r8,%r9
    5d8b:	0f 94 c0             	sete   %al
    5d8e:	21 d0                	and    %edx,%eax
    5d90:	c3                   	ret
    5d91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5d98:	74 af                	je     5d49 <overlap+0x49>
  return 0;
    5d9a:	31 c0                	xor    %eax,%eax
}
    5d9c:	c3                   	ret
    5d9d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5da0:	4d 39 da             	cmp    %r11,%r10
    5da3:	7e c4                	jle    5d69 <overlap+0x69>
    return 1;
    5da5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5daa:	4d 39 c1             	cmp    %r8,%r9
    5dad:	7e ba                	jle    5d69 <overlap+0x69>
    5daf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5db0:	48 39 ca             	cmp    %rcx,%rdx
    5db3:	7c 94                	jl     5d49 <overlap+0x49>
    5db5:	4d 39 c1             	cmp    %r8,%r9
    5db8:	7d b4                	jge    5d6e <overlap+0x6e>
    5dba:	48 39 ca             	cmp    %rcx,%rdx
    5dbd:	74 91                	je     5d50 <overlap+0x50>
    5dbf:	eb d9                	jmp    5d9a <overlap+0x9a>
    5dc1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5dc8:	c3                   	ret
    5dc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005dd0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5dd0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5dd4:	85 f6                	test   %esi,%esi
    5dd6:	0f 8e 44 03 00 00    	jle    6120 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    5ddc:	41 57                	push   %r15
    5dde:	41 89 f7             	mov    %esi,%r15d
    5de1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5de3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5de6:	41 55                	push   %r13
    5de8:	41 54                	push   %r12
    5dea:	55                   	push   %rbp
    5deb:	53                   	push   %rbx
    5dec:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5df0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5df4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5df9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5dfe:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    5e01:	45 39 e6             	cmp    %r12d,%r14d
    5e04:	0f 84 4e 02 00 00    	je     6058 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5e0a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5e0f:	8b 50 08             	mov    0x8(%rax),%edx
    5e12:	85 d2                	test   %edx,%edx
    5e14:	0f 8e 3e 02 00 00    	jle    6058 <verify+0x288>
    5e1a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    5e1f:	31 c9                	xor    %ecx,%ecx
    5e21:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    5e26:	31 c0                	xor    %eax,%eax
    5e28:	44 89 f2             	mov    %r14d,%edx
    5e2b:	bf 01 00 00 00       	mov    $0x1,%edi
    5e30:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5e35:	48 8d 35 e4 13 00 00 	lea    0x13e4(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    5e3c:	e8 0f c6 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5e41:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5e46:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    5e4b:	8b 40 08             	mov    0x8(%rax),%eax
    5e4e:	85 c0                	test   %eax,%eax
    5e50:	0f 8e e6 01 00 00    	jle    603c <verify+0x26c>
    5e56:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5e59:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    5e5e:	31 db                	xor    %ebx,%ebx
    5e60:	48 c1 e0 09          	shl    $0x9,%rax
    5e64:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    5e69:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5e6e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5e73:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    5e78:	4c 8b 20             	mov    (%rax),%r12
    5e7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5e80:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    5e85:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5e8a:	49 89 de             	mov    %rbx,%r14
    5e8d:	48 8d 35 a1 13 00 00 	lea    0x13a1(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5e94:	49 c1 e6 09          	shl    $0x9,%r14
    5e98:	bf 01 00 00 00       	mov    $0x1,%edi
    5e9d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5ea1:	4b 8b 8c 3c 58 01 00 00 	mov    0x158(%r12,%r15,1),%rcx
    5ea9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    5eae:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    5eb6:	31 c0                	xor    %eax,%eax
    5eb8:	e8 93 c5 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5ebd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5ec2:	4c 8b 20             	mov    (%rax),%r12
    5ec5:	4b 83 bc 3c 58 01 00 00 00 	cmpq   $0x0,0x158(%r12,%r15,1)
    5ece:	0f 8e 47 01 00 00    	jle    601b <verify+0x24b>
    5ed4:	4c 03 75 00          	add    0x0(%rbp),%r14
    5ed8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5edd:	ba 01 00 00 00       	mov    $0x1,%edx
    5ee2:	4d 89 f5             	mov    %r14,%r13
    5ee5:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    5eec:	4d 85 f6             	test   %r14,%r14
    5eef:	0f 8e 21 01 00 00    	jle    6016 <verify+0x246>
    5ef5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5ef8:	48 89 d5             	mov    %rdx,%rbp
    5efb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5f00:	31 db                	xor    %ebx,%ebx
    5f02:	4d 89 f2             	mov    %r14,%r10
    5f05:	48 c1 e5 05          	shl    $0x5,%rbp
    5f09:	48 83 ed 20          	sub    $0x20,%rbp
    5f0d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    5f11:	49 89 ee             	mov    %rbp,%r14
    5f14:	48 89 dd             	mov    %rbx,%rbp
    5f17:	48 89 d3             	mov    %rdx,%rbx
    5f1a:	eb 31                	jmp    5f4d <verify+0x17d>
    5f1c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5f20:	4c 39 c2             	cmp    %r8,%rdx
    5f23:	0f 8d 57 01 00 00    	jge    6080 <verify+0x2b0>
    5f29:	4c 39 df             	cmp    %r11,%rdi
    5f2c:	7e 05                	jle    5f33 <verify+0x163>
    5f2e:	49 39 c1             	cmp    %rax,%r9
    5f31:	7c 75                	jl     5fa8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f33:	4c 39 df             	cmp    %r11,%rdi
    5f36:	0f 8d ab 01 00 00    	jge    60e7 <verify+0x317>
    5f3c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5f40:	48 83 c5 01          	add    $0x1,%rbp
    5f44:	49 39 ea             	cmp    %rbp,%r10
    5f47:	0f 8e a9 00 00 00    	jle    5ff6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5f4d:	49 8b 97 48 01 00 00 	mov    0x148(%r15),%rdx
    5f54:	48 89 e8             	mov    %rbp,%rax
    5f57:	48 c1 e0 05          	shl    $0x5,%rax
    5f5b:	49 03 85 48 01 00 00 	add    0x148(%r13),%rax
    5f62:	4c 01 f2             	add    %r14,%rdx
    5f65:	48 8b 08             	mov    (%rax),%rcx
    5f68:	48 8b 78 10          	mov    0x10(%rax),%rdi
    5f6c:	48 8b 32             	mov    (%rdx),%rsi
    5f6f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    5f73:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    5f77:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    5f7b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    5f7f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    5f83:	48 39 f1             	cmp    %rsi,%rcx
    5f86:	7c 98                	jl     5f20 <verify+0x150>
    5f88:	0f 8e 42 01 00 00    	jle    60d0 <verify+0x300>
    5f8e:	4c 39 c2             	cmp    %r8,%rdx
    5f91:	0f 8f f9 00 00 00    	jg     6090 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f97:	75 a7                	jne    5f40 <verify+0x170>
    5f99:	4c 39 df             	cmp    %r11,%rdi
    5f9c:	7f a2                	jg     5f40 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5f9e:	49 39 c1             	cmp    %rax,%r9
    5fa1:	7c 9d                	jl     5f40 <verify+0x170>
    5fa3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5fa8:	49 89 c1             	mov    %rax,%r9
    5fab:	48 89 f9             	mov    %rdi,%rcx
    5fae:	48 89 f2             	mov    %rsi,%rdx
    5fb1:	bf 01 00 00 00       	mov    $0x1,%edi
    5fb6:	48 8d 35 d3 14 00 00 	lea    0x14d3(%rip),%rsi        # 7490 <_IO_stdin_used+0x490>
    5fbd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5fbf:	48 83 c5 01          	add    $0x1,%rbp
    5fc3:	e8 88 c4 ff ff       	call   2450 <__printf_chk@plt>
    5fc8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5fcd:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    5fd2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5fd5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5fda:	4d 8b 95 58 01 00 00 	mov    0x158(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5fe1:	4c 8b 20             	mov    (%rax),%r12
    5fe4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5fe9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5fed:	49 39 ea             	cmp    %rbp,%r10
    5ff0:	0f 8f 57 ff ff ff    	jg     5f4d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5ff6:	48 89 da             	mov    %rbx,%rdx
    5ff9:	49 3b 9f 58 01 00 00 	cmp    0x158(%r15),%rbx
    6000:	7d 14                	jge    6016 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6002:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    6009:	48 83 c2 01          	add    $0x1,%rdx
    600d:	4d 85 f6             	test   %r14,%r14
    6010:	0f 8f e2 fe ff ff    	jg     5ef8 <verify+0x128>
    6016:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    601b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6020:	48 83 c3 01          	add    $0x1,%rbx
    6024:	39 58 08             	cmp    %ebx,0x8(%rax)
    6027:	0f 8f 53 fe ff ff    	jg     5e80 <verify+0xb0>
    602d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6032:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6037:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    603c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6041:	48 83 c1 01          	add    $0x1,%rcx
    6045:	39 48 08             	cmp    %ecx,0x8(%rax)
    6048:	0f 8f d8 fd ff ff    	jg     5e26 <verify+0x56>
    604e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6053:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6058:	48 81 44 24 10 b0 00 00 00 	addq   $0xb0,0x10(%rsp)
    6061:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6066:	41 39 c7             	cmp    %eax,%r15d
    6069:	0f 84 86 00 00 00    	je     60f5 <verify+0x325>
    606f:	41 89 c4             	mov    %eax,%r12d
    6072:	e9 8a fd ff ff       	jmp    5e01 <verify+0x31>
    6077:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6080:	0f 85 ba fe ff ff    	jne    5f40 <verify+0x170>
    6086:	e9 a8 fe ff ff       	jmp    5f33 <verify+0x163>
    608b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6090:	49 39 c1             	cmp    %rax,%r9
    6093:	7e 09                	jle    609e <verify+0x2ce>
    6095:	4c 39 df             	cmp    %r11,%rdi
    6098:	0f 8c 0a ff ff ff    	jl     5fa8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    609e:	4c 39 df             	cmp    %r11,%rdi
    60a1:	0f 8f 99 fe ff ff    	jg     5f40 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    60a7:	49 39 c1             	cmp    %rax,%r9
    60aa:	0f 8d f8 fe ff ff    	jge    5fa8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    60b0:	48 39 f1             	cmp    %rsi,%rcx
    60b3:	0f 85 87 fe ff ff    	jne    5f40 <verify+0x170>
    60b9:	4c 39 c2             	cmp    %r8,%rdx
    60bc:	0f 85 7e fe ff ff    	jne    5f40 <verify+0x170>
    60c2:	4c 39 df             	cmp    %r11,%rdi
    60c5:	0f 84 dd fe ff ff    	je     5fa8 <verify+0x1d8>
    60cb:	e9 70 fe ff ff       	jmp    5f40 <verify+0x170>
    60d0:	4c 39 c2             	cmp    %r8,%rdx
    60d3:	0f 8c 5a fe ff ff    	jl     5f33 <verify+0x163>
    60d9:	4c 39 df             	cmp    %r11,%rdi
    60dc:	7e c9                	jle    60a7 <verify+0x2d7>
    60de:	4c 39 c2             	cmp    %r8,%rdx
    60e1:	0f 85 59 fe ff ff    	jne    5f40 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    60e7:	49 39 c1             	cmp    %rax,%r9
    60ea:	0f 8f 50 fe ff ff    	jg     5f40 <verify+0x170>
    60f0:	e9 b3 fe ff ff       	jmp    5fa8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    60f5:	48 81 44 24 18 b0 00 00 00 	addq   $0xb0,0x18(%rsp)
    60fe:	41 8d 46 01          	lea    0x1(%r14),%eax
    6102:	45 39 e6             	cmp    %r12d,%r14d
    6105:	74 08                	je     610f <verify+0x33f>
    6107:	41 89 c6             	mov    %eax,%r14d
    610a:	e9 ea fc ff ff       	jmp    5df9 <verify+0x29>
}
    610f:	48 83 c4 58          	add    $0x58,%rsp
    6113:	31 c0                	xor    %eax,%eax
    6115:	5b                   	pop    %rbx
    6116:	5d                   	pop    %rbp
    6117:	41 5c                	pop    %r12
    6119:	41 5d                	pop    %r13
    611b:	41 5e                	pop    %r14
    611d:	41 5f                	pop    %r15
    611f:	c3                   	ret
    6120:	31 c0                	xor    %eax,%eax
    6122:	c3                   	ret

Disassembly of section .fini:

0000000000006124 <_fini>:
    6124:	f3 0f 1e fa          	endbr64
    6128:	48 83 ec 08          	sub    $0x8,%rsp
    612c:	48 83 c4 08          	add    $0x8,%rsp
    6130:	c3                   	ret
