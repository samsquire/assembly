
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
    25f6:	48 8d 3d b3 4e 00 00 	lea    0x4eb3(%rip),%rdi        # 74b0 <_IO_stdin_used+0x4b0>
    25fd:	41 56                	push   %r14
    25ff:	41 55                	push   %r13
    2601:	41 54                	push   %r12
    2603:	55                   	push   %rbp
    2604:	53                   	push   %rbx
    2605:	48 81 ec b8 00 00 00 	sub    $0xb8,%rsp
    260c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2615:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
    261d:	48 8d 05 0c 12 00 00 	lea    0x120c(%rip),%rax        # 3830 <barriered_reset>
    2624:	66 48 0f 6e e8       	movq   %rax,%xmm5
    2629:	0f 16 2d 48 76 00 00 	movhps 0x7648(%rip),%xmm5        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    2630:	0f 29 6c 24 30       	movaps %xmm5,0x30(%rsp)
    2635:	e8 b6 fc ff ff       	call   22f0 <puts@plt>
    263a:	bf 0a 00 00 00       	mov    $0xa,%edi
    263f:	e8 8c fc ff ff       	call   22d0 <putchar@plt>
    2644:	48 8d 3d f3 4b 00 00 	lea    0x4bf3(%rip),%rdi        # 723e <_IO_stdin_used+0x23e>
    264b:	e8 a0 fc ff ff       	call   22f0 <puts@plt>
    2650:	ba 0c 00 00 00       	mov    $0xc,%edx
    2655:	48 8d 35 fe 4b 00 00 	lea    0x4bfe(%rip),%rsi        # 725a <_IO_stdin_used+0x25a>
    265c:	31 c0                	xor    %eax,%eax
    265e:	bf 01 00 00 00       	mov    $0x1,%edi
    2663:	e8 e8 fd ff ff       	call   2450 <__printf_chk@plt>
    2668:	ba 0f 00 00 00       	mov    $0xf,%edx
    266d:	48 8d 35 00 4c 00 00 	lea    0x4c00(%rip),%rsi        # 7274 <_IO_stdin_used+0x274>
    2674:	31 c0                	xor    %eax,%eax
    2676:	bf 01 00 00 00       	mov    $0x1,%edi
    267b:	e8 d0 fd ff ff       	call   2450 <__printf_chk@plt>
    2680:	ba 01 00 00 00       	mov    $0x1,%edx
    2685:	48 8d 35 fc 4b 00 00 	lea    0x4bfc(%rip),%rsi        # 7288 <_IO_stdin_used+0x288>
    268c:	31 c0                	xor    %eax,%eax
    268e:	bf 01 00 00 00       	mov    $0x1,%edi
    2693:	e8 b8 fd ff ff       	call   2450 <__printf_chk@plt>
    2698:	ba 01 00 00 00       	mov    $0x1,%edx
    269d:	48 8d 35 f5 4b 00 00 	lea    0x4bf5(%rip),%rsi        # 7299 <_IO_stdin_used+0x299>
    26a4:	31 c0                	xor    %eax,%eax
    26a6:	bf 01 00 00 00       	mov    $0x1,%edi
    26ab:	e8 a0 fd ff ff       	call   2450 <__printf_chk@plt>
    26b0:	ba 01 00 00 00       	mov    $0x1,%edx
    26b5:	48 8d 35 f5 4b 00 00 	lea    0x4bf5(%rip),%rsi        # 72b1 <_IO_stdin_used+0x2b1>
    26bc:	31 c0                	xor    %eax,%eax
    26be:	bf 01 00 00 00       	mov    $0x1,%edi
    26c3:	e8 88 fd ff ff       	call   2450 <__printf_chk@plt>
    26c8:	ba 01 00 00 00       	mov    $0x1,%edx
    26cd:	48 8d 35 44 4e 00 00 	lea    0x4e44(%rip),%rsi        # 7518 <_IO_stdin_used+0x518>
    26d4:	31 c0                	xor    %eax,%eax
    26d6:	bf 01 00 00 00       	mov    $0x1,%edi
    26db:	e8 70 fd ff ff       	call   2450 <__printf_chk@plt>
    26e0:	ba 01 00 00 00       	mov    $0x1,%edx
    26e5:	48 8d 35 5c 4e 00 00 	lea    0x4e5c(%rip),%rsi        # 7548 <_IO_stdin_used+0x548>
    26ec:	31 c0                	xor    %eax,%eax
    26ee:	bf 01 00 00 00       	mov    $0x1,%edi
    26f3:	e8 58 fd ff ff       	call   2450 <__printf_chk@plt>
    26f8:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    26fd:	48 8d 35 c9 4b 00 00 	lea    0x4bc9(%rip),%rsi        # 72cd <_IO_stdin_used+0x2cd>
    2704:	31 c0                	xor    %eax,%eax
    2706:	bf 01 00 00 00       	mov    $0x1,%edi
    270b:	e8 40 fd ff ff       	call   2450 <__printf_chk@plt>
    2710:	ba 05 00 00 00       	mov    $0x5,%edx
    2715:	48 8d 35 cb 4b 00 00 	lea    0x4bcb(%rip),%rsi        # 72e7 <_IO_stdin_used+0x2e7>
    271c:	31 c0                	xor    %eax,%eax
    271e:	bf 01 00 00 00       	mov    $0x1,%edi
    2723:	e8 28 fd ff ff       	call   2450 <__printf_chk@plt>
    2728:	48 8d 3d 9f 49 00 00 	lea    0x499f(%rip),%rdi        # 70ce <_IO_stdin_used+0xce>
    272f:	e8 bc fb ff ff       	call   22f0 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    2734:	be 18 00 00 00       	mov    $0x18,%esi
    2739:	bf 0c 00 00 00       	mov    $0xc,%edi
    273e:	e8 5d fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2743:	be 80 02 00 00       	mov    $0x280,%esi
    2748:	bf 0f 00 00 00       	mov    $0xf,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    274d:	49 89 c7             	mov    %rax,%r15
    2750:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2755:	e8 46 fc ff ff       	call   23a0 <calloc@plt>
  int barrier_count = 2;
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    275a:	be 10 00 00 00       	mov    $0x10,%esi
    275f:	bf 01 00 00 00       	mov    $0x1,%edi
    2764:	4d 8d 67 e8          	lea    -0x18(%r15),%r12
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2768:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    276d:	45 31 ff             	xor    %r15d,%r15d
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2770:	e8 2b fc ff ff       	call   23a0 <calloc@plt>
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2775:	be 10 00 00 00       	mov    $0x10,%esi
    277a:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    277f:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2785:	48 89 c3             	mov    %rax,%rbx
    2788:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    278d:	e8 0e fc ff ff       	call   23a0 <calloc@plt>
    2792:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    }
  }
  int external_thread_index = 0;
    2797:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    279f:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
    27a3:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    27aa:	4d 89 d5             	mov    %r10,%r13
    27ad:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    27b2:	4c 89 54 24 58       	mov    %r10,0x58(%rsp)
    27b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27c0:	be 08 00 00 00       	mov    $0x8,%esi
    27c5:	bf 02 00 00 00       	mov    $0x2,%edi
    27ca:	44 89 fd             	mov    %r15d,%ebp
    27cd:	e8 ce fb ff ff       	call   23a0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27d2:	be 80 00 00 00       	mov    $0x80,%esi
    27d7:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27dc:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27e1:	e8 ba fb ff ff       	call   23a0 <calloc@plt>
    27e6:	48 89 c3             	mov    %rax,%rbx
    if (x % 2 == 1) {
    27e9:	44 89 f8             	mov    %r15d,%eax
    27ec:	41 83 c7 01          	add    $0x1,%r15d
    27f0:	83 e0 01             	and    $0x1,%eax
    27f3:	85 c0                	test   %eax,%eax
    27f5:	0f 84 84 0e 00 00    	je     367f <main+0x108f>
      my_thread_data[0] = &thread_data[other]; 
    27fb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    2800:	4d 89 e8             	mov    %r13,%r8
    2803:	89 ea                	mov    %ebp,%edx
    2805:	bf 01 00 00 00       	mov    $0x1,%edi
    280a:	49 8d 8d 80 fd ff ff 	lea    -0x280(%r13),%rcx
      thread_data[x].thread_index = 1;
    2811:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    2819:	48 8d 35 db 4a 00 00 	lea    0x4adb(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
      my_thread_data[0] = &thread_data[other]; 
    2820:	48 89 08             	mov    %rcx,(%rax)
      other = abs(x - 1) % total_threads;
    2823:	44 8d 75 ff          	lea    -0x1(%rbp),%r14d
      my_thread_data[1] = &thread_data[x]; 
    2827:	4c 89 68 08          	mov    %r13,0x8(%rax)
    282b:	31 c0                	xor    %eax,%eax
    282d:	e8 1e fc ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    2832:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    2837:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    283c:	4d 89 a5 00 01 00 00 	mov    %r12,0x100(%r13)
    2843:	45 8b 45 00          	mov    0x0(%r13),%r8d
    2847:	44 89 f1             	mov    %r14d,%ecx
    284a:	89 ea                	mov    %ebp,%edx
    284c:	48 8d 35 1d 4d 00 00 	lea    0x4d1d(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    2853:	bf 01 00 00 00       	mov    $0x1,%edi
    2858:	31 c0                	xor    %eax,%eax
      CPU_SET(j, sendercpu);
    285a:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    2860:	e8 eb fb ff ff       	call   2450 <__printf_chk@plt>
    thread_data[x].other = other;
    2865:	45 89 b5 28 02 00 00 	mov    %r14d,0x228(%r13)
    for (int j = 0 ; j < cores / 2 ; j++) {
    286c:	45 31 f6             	xor    %r14d,%r14d
    286f:	90                   	nop
    2870:	44 89 f1             	mov    %r14d,%ecx
    2873:	89 ea                	mov    %ebp,%edx
    2875:	48 8d 35 24 4d 00 00 	lea    0x4d24(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    287c:	31 c0                	xor    %eax,%eax
    287e:	bf 01 00 00 00       	mov    $0x1,%edi
    2883:	e8 c8 fb ff ff       	call   2450 <__printf_chk@plt>
      CPU_SET(j, sendercpu);
    2888:	44 89 f1             	mov    %r14d,%ecx
    288b:	4c 89 e0             	mov    %r12,%rax
    for (int j = 0 ; j < cores / 2 ; j++) {
    288e:	41 83 c6 01          	add    $0x1,%r14d
      CPU_SET(j, sendercpu);
    2892:	48 d3 e0             	shl    %cl,%rax
    2895:	48 09 03             	or     %rax,(%rbx)
    for (int j = 0 ; j < cores / 2 ; j++) {
    2898:	41 83 fe 06          	cmp    $0x6,%r14d
    289c:	75 d2                	jne    2870 <main+0x280>
    thread_data[x].threads = my_thread_data;
    289e:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    thread_data[x].real_thread_index = x;
    28a3:	41 89 6d 04          	mov    %ebp,0x4(%r13)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28a7:	be 10 00 00 00       	mov    $0x10,%esi
    28ac:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].cpu_set = sendercpu;
    28b1:	49 89 9d 20 02 00 00 	mov    %rbx,0x220(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28b8:	31 db                	xor    %ebx,%ebx
    thread_data[x].threads = my_thread_data;
    28ba:	49 89 85 80 00 00 00 	mov    %rax,0x80(%r13)
    thread_data[x].thread_count = 2;
    28c1:	48 8b 05 78 51 00 00 	mov    0x5178(%rip),%rax        # 7a40 <_IO_stdin_used+0xa40>
    thread_data[x].task_count = total_barrier_count;
    28c8:	41 c7 85 a0 00 00 00 03 00 00 00 	movl   $0x3,0xa0(%r13)
    thread_data[x].thread_count = 2;
    28d3:	49 89 85 88 00 00 00 	mov    %rax,0x88(%r13)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28da:	e8 c1 fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28df:	be 10 00 00 00       	mov    $0x10,%esi
    28e4:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28e9:	49 89 85 98 01 00 00 	mov    %rax,0x198(%r13)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28f0:	e8 ab fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28f5:	be 28 00 00 00       	mov    $0x28,%esi
    28fa:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    28ff:	66 0f 6f 15 19 51 00 00 	movdqa 0x5119(%rip),%xmm2        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2907:	49 89 85 a0 01 00 00 	mov    %rax,0x1a0(%r13)
    thread_data[x].timestamp_count = 0;
    290e:	41 0f 29 95 b0 01 00 00 	movaps %xmm2,0x1b0(%r13)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2916:	e8 85 fa ff ff       	call   23a0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    291b:	be 00 02 00 00       	mov    $0x200,%esi
    2920:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
    2925:	66 0f 6f 1d f3 50 00 00 	movdqa 0x50f3(%rip),%xmm3        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    292d:	49 89 85 00 02 00 00 	mov    %rax,0x200(%r13)
    thread_data[x].task_timestamp_count = 0;
    2934:	41 0f 11 9d 08 02 00 00 	movups %xmm3,0x208(%r13)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    293c:	e8 5f fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    2941:	44 89 7c 24 28       	mov    %r15d,0x28(%rsp)
      thread_data[x].tasks = barriers;
    2946:	49 89 85 98 00 00 00 	mov    %rax,0x98(%r13)
        thread_data[x].tasks[y].sending = 1;
    294d:	49 89 c4             	mov    %rax,%r12
    2950:	89 6c 24 08          	mov    %ebp,0x8(%rsp)
        thread_data[x].tasks[y].protected = do_protected_write; 
    2954:	48 63 eb             	movslq %ebx,%rbp
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2957:	be 00 01 00 00       	mov    $0x100,%esi
    295c:	bf 0c 00 00 00       	mov    $0xc,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    2961:	49 89 ef             	mov    %rbp,%r15
    2964:	48 8d 05 85 0e 00 00 	lea    0xe85(%rip),%rax        # 37f0 <do_protected_write>
    296b:	49 c1 e7 09          	shl    $0x9,%r15
    296f:	4d 01 fc             	add    %r15,%r12
    2972:	49 89 84 24 20 01 00 00 	mov    %rax,0x120(%r12)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    297a:	e8 21 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    297f:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    2983:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    2988:	49 89 c6             	mov    %rax,%r14
    298b:	49 89 84 24 68 01 00 00 	mov    %rax,0x168(%r12)
        for (int b = 0 ; b < 2 ; b++) {
    2993:	4c 8d a0 00 02 00 00 	lea    0x200(%rax),%r12
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    299a:	be 08 00 00 00       	mov    $0x8,%esi
    299f:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    29a4:	49 81 c6 00 01 00 00 	add    $0x100,%r14
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29ab:	e8 f0 f9 ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29b0:	be 08 00 00 00       	mov    $0x8,%esi
    29b5:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29ba:	48 89 c5             	mov    %rax,%rbp
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29bd:	e8 de f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29c2:	be 18 00 00 00       	mov    $0x18,%esi
    29c7:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29cc:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29cf:	e8 cc f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    29d4:	66 0f 6f 05 54 50 00 00 	movdqa 0x5054(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
          mailboxes[b].higher = &data[1];
    29dc:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29e0:	49 89 86 00 ff ff ff 	mov    %rax,-0x100(%r14)
          mailboxes[b].higher = &data[1];
    29e7:	49 89 76 80          	mov    %rsi,-0x80(%r14)
          data[0].messages = messages;
    29eb:	48 89 28             	mov    %rbp,(%rax)
          data[1].messages = messages2;
    29ee:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    29f2:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    29f6:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    29fa:	4d 39 e6             	cmp    %r12,%r14
    29fd:	75 9b                	jne    299a <main+0x3aa>
        char *message = malloc(sizeof(char) * 256);
    29ff:	be 01 00 00 00       	mov    $0x1,%esi
    2a04:	bf 00 01 00 00       	mov    $0x100,%edi
    2a09:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    2a0d:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    2a12:	e8 89 f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a17:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a1c:	49 89 c4             	mov    %rax,%r12
        struct Message *messaged = malloc(sizeof(struct Message));
    2a1f:	e8 ec f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a24:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    2a29:	4c 89 e7             	mov    %r12,%rdi
    2a2c:	41 89 d9             	mov    %ebx,%r9d
    2a2f:	ba 00 01 00 00       	mov    $0x100,%edx
    2a34:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2a39:	be 01 00 00 00       	mov    $0x1,%esi
    2a3e:	31 c0                	xor    %eax,%eax
    2a40:	48 8d 0d 79 4b 00 00 	lea    0x4b79(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a47:	e8 d4 fa ff ff       	call   2520 <__sprintf_chk@plt>
        messaged->message = message;
    2a4c:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
        messaged->thread_index = thread_data[x].thread_index;
    2a51:	49 63 45 00          	movslq 0x0(%r13),%rax
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a55:	8d 4b 01             	lea    0x1(%rbx),%ecx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a58:	be 20 00 00 00       	mov    $0x20,%esi
    2a5d:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a62:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
        messaged->message = message;
    2a66:	4d 89 22             	mov    %r12,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a69:	4d 8b a5 98 00 00 00 	mov    0x98(%r13),%r12
        messaged->task_index = y;
    2a70:	49 89 6a 10          	mov    %rbp,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a74:	4b 8d 2c 3c          	lea    (%r12,%r15,1),%rbp
        messaged->thread_index = thread_data[x].thread_index;
    2a78:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a7c:	89 8d 88 01 00 00    	mov    %ecx,0x188(%rbp)
        thread_data[x].tasks[y].message = messaged;
    2a82:	4c 89 95 80 01 00 00 	mov    %r10,0x180(%rbp)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a89:	48 c7 85 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%rbp)
        messaged->thread_index = thread_data[x].thread_index;
    2a94:	89 44 24 18          	mov    %eax,0x18(%rsp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a98:	e8 03 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a9d:	8b 54 24 18          	mov    0x18(%rsp),%edx
        if (y == barrier_count - 1) {
    2aa1:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2aa4:	89 5d 00             	mov    %ebx,0x0(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2aa7:	48 89 85 48 01 00 00 	mov    %rax,0x148(%rbp)
        if (y == barrier_count - 1) {
    2aae:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
        thread_data[x].tasks[y].available = 1;
    2ab2:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2abc:	48 89 85 38 01 00 00 	mov    %rax,0x138(%rbp)
        thread_data[x].tasks[y].sending = 1;
    2ac3:	48 b8 01 00 00 00 0c 00 00 00 	movabs $0xc00000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2acd:	48 c7 85 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%rbp)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2ad8:	89 95 30 01 00 00    	mov    %edx,0x130(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2ade:	4c 89 ad 28 01 00 00 	mov    %r13,0x128(%rbp)
        thread_data[x].tasks[y].arrived = 0;
    2ae5:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        thread_data[x].tasks[y].thread_count = 2;
    2aef:	c7 85 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%rbp)
        thread_data[x].tasks[y].sending = 1;
    2af9:	48 89 85 78 01 00 00 	mov    %rax,0x178(%rbp)
        if (y == barrier_count - 1) {
    2b00:	0f 84 61 0b 00 00    	je     3667 <main+0x1077>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2b06:	8b 54 24 08          	mov    0x8(%rsp),%edx
    2b0a:	39 d3                	cmp    %edx,%ebx
    2b0c:	75 72                	jne    2b80 <main+0x590>
    2b0e:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    2b12:	85 db                	test   %ebx,%ebx
    2b14:	7f 6a                	jg     2b80 <main+0x590>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2b16:	bf 01 00 00 00       	mov    $0x1,%edi
    2b1b:	48 8d 35 c6 4a 00 00 	lea    0x4ac6(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2b22:	31 c0                	xor    %eax,%eax
    2b24:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
    2b28:	e8 23 f9 ff ff       	call   2450 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b2d:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    2b32:	48 63 c3             	movslq %ebx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b35:	4d 8b a5 98 00 00 00 	mov    0x98(%r13),%r12
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b3c:	48 89 c7             	mov    %rax,%rdi
    2b3f:	48 c1 e0 04          	shl    $0x4,%rax
    2b43:	48 01 c8             	add    %rcx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b46:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b4a:	49 89 85 80 01 00 00 	mov    %rax,0x180(%r13)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b51:	48 8d 05 e8 32 00 00 	lea    0x32e8(%rip),%rax        # 5e40 <barriered_work_ingest>
    2b58:	4b 89 84 3c 18 01 00 00 	mov    %rax,0x118(%r12,%r15,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b60:	8d 47 01             	lea    0x1(%rdi),%eax
    2b63:	89 44 24 20          	mov    %eax,0x20(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b67:	83 f9 03             	cmp    $0x3,%ecx
    2b6a:	74 27                	je     2b93 <main+0x5a3>
    2b6c:	bb 01 00 00 00       	mov    $0x1,%ebx
    2b71:	e9 de fd ff ff       	jmp    2954 <main+0x364>
    2b76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            thread_data[x].tasks[y].run = barriered_work; 
    2b80:	48 8d 05 89 2d 00 00 	lea    0x2d89(%rip),%rax        # 5910 <barriered_work>
    2b87:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b8e:	83 f9 03             	cmp    $0x3,%ecx
    2b91:	75 d9                	jne    2b6c <main+0x57c>
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b93:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b9d:	66 0f 6f 64 24 30    	movdqa 0x30(%rsp),%xmm4
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2ba3:	41 c7 84 24 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r12)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2baf:	49 89 84 24 34 05 00 00 	mov    %rax,0x534(%r12)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2bb7:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2bbc:	41 c7 84 24 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%r12)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bc8:	41 8b 45 00          	mov    0x0(%r13),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2bcc:	4d 89 ac 24 28 05 00 00 	mov    %r13,0x528(%r12)
  for (int x = 0 ; x < total_threads ; x++) {
    2bd4:	49 81 c5 80 02 00 00 	add    $0x280,%r13
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bdb:	41 89 84 24 30 05 00 00 	mov    %eax,0x530(%r12)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2be3:	41 c7 84 24 7c 05 00 00 0c 00 00 00 	movl   $0xc,0x57c(%r12)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2bef:	41 c7 84 24 3c 05 00 00 03 00 00 00 	movl   $0x3,0x53c(%r12)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2bfb:	41 0f 11 a4 24 18 05 00 00 	movups %xmm4,0x518(%r12)
  for (int x = 0 ; x < total_threads ; x++) {
    2c04:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    2c09:	41 83 ff 0f          	cmp    $0xf,%r15d
    2c0d:	0f 85 ad fb ff ff    	jne    27c0 <main+0x1d0>
    2c13:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    2c18:	ba 0d 00 00 00       	mov    $0xd,%edx
    2c1d:	48 8d 35 f4 46 00 00 	lea    0x46f4(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2c24:	31 c0                	xor    %eax,%eax
    2c26:	bf 01 00 00 00       	mov    $0x1,%edi
    2c2b:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    2c30:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2c35:	e8 16 f8 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c3a:	be 08 00 00 00       	mov    $0x8,%esi
    2c3f:	bf 02 00 00 00       	mov    $0x2,%edi
    2c44:	e8 57 f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2c49:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c4e:	bf 0f 00 00 00       	mov    $0xf,%edi
    my_thread_data[0] = &thread_data[x]; 
    2c53:	4d 8d ba 80 20 00 00 	lea    0x2080(%r10),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c5a:	4d 8d b2 00 05 00 00 	lea    0x500(%r10),%r14
    thread_data[x].threads = my_thread_data;
    2c61:	49 89 82 00 21 00 00 	mov    %rax,0x2100(%r10)
    my_thread_data[0] = &thread_data[x]; 
    2c68:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c6b:	49 8d 8a 80 07 00 00 	lea    0x780(%r10),%rcx
    2c72:	49 8d 92 80 0c 00 00 	lea    0xc80(%r10),%rdx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c79:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c7d:	49 8b 82 98 00 00 00 	mov    0x98(%r10),%rax
    2c84:	4d 8d 9a 80 11 00 00 	lea    0x1180(%r10),%r11
    2c8b:	4d 8d 8a 00 14 00 00 	lea    0x1400(%r10),%r9
    2c92:	49 8d b2 00 0a 00 00 	lea    0xa00(%r10),%rsi
    2c99:	49 8d 9a 00 0f 00 00 	lea    0xf00(%r10),%rbx
    thread_data[x].thread_count = 2;
    2ca0:	41 c7 82 08 21 00 00 02 00 00 00 	movl   $0x2,0x2108(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2cab:	48 89 4c 24 58       	mov    %rcx,0x58(%rsp)
    2cb0:	4d 8d 82 80 16 00 00 	lea    0x1680(%r10),%r8
    2cb7:	4d 8d aa 00 19 00 00 	lea    0x1900(%r10),%r13
    2cbe:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    2cc3:	4d 8d a2 80 1b 00 00 	lea    0x1b80(%r10),%r12
    thread_data[x].thread_index = 0;
    2cca:	41 c7 82 80 20 00 00 00 00 00 00 	movl   $0x0,0x2080(%r10)
    thread_data[x].task_count = total_barrier_count;
    2cd5:	41 c7 82 20 21 00 00 03 00 00 00 	movl   $0x3,0x2120(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2ce0:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cea:	49 8d 82 80 02 00 00 	lea    0x280(%r10),%rax
    2cf1:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2cf6:	49 8b 82 18 03 00 00 	mov    0x318(%r10),%rax
    2cfd:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    2d02:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d0c:	49 8b 82 98 05 00 00 	mov    0x598(%r10),%rax
    2d13:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2d18:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d22:	49 8b 82 18 08 00 00 	mov    0x818(%r10),%rax
    my_thread_data[0] = &thread_data[x]; 
    2d29:	4c 89 7c 24 70       	mov    %r15,0x70(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d2e:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d38:	49 8b 82 98 0a 00 00 	mov    0xa98(%r10),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2d3f:	4c 89 74 24 78       	mov    %r14,0x78(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d44:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d4e:	49 8b 82 18 0d 00 00 	mov    0xd18(%r10),%rax
    2d55:	48 89 74 24 50       	mov    %rsi,0x50(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d5a:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2d5f:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d69:	49 8b 82 98 0f 00 00 	mov    0xf98(%r10),%rax
    2d70:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    2d75:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d7f:	49 8b 82 18 12 00 00 	mov    0x1218(%r10),%rax
    2d86:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d90:	49 8b 82 98 14 00 00 	mov    0x1498(%r10),%rax
    2d97:	4c 89 44 24 30       	mov    %r8,0x30(%rsp)
    2d9c:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2da6:	49 8b 82 18 17 00 00 	mov    0x1718(%r10),%rax
    2dad:	4c 89 94 24 80 00 00 00 	mov    %r10,0x80(%rsp)
    2db5:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2dbf:	49 8b 82 98 19 00 00 	mov    0x1998(%r10),%rax
    2dc6:	4c 89 6c 24 20       	mov    %r13,0x20(%rsp)
    2dcb:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2dd5:	49 8b 82 18 1c 00 00 	mov    0x1c18(%r10),%rax
    2ddc:	4c 89 64 24 10       	mov    %r12,0x10(%rsp)
    2de1:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2deb:	e8 b0 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2df0:	be 38 00 00 00       	mov    $0x38,%esi
    2df5:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dfa:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dfd:	e8 9e f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e02:	be 38 00 00 00       	mov    $0x38,%esi
    2e07:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e0c:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e0f:	e8 8c f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e14:	be 38 00 00 00       	mov    $0x38,%esi
    2e19:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e1e:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e26:	e8 75 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e2b:	be 08 00 00 00       	mov    $0x8,%esi
    2e30:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e35:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e3d:	e8 5e f5 ff ff       	call   23a0 <calloc@plt>
  thread_data[thread_count].type = TIMER;
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2e42:	be 08 00 00 00       	mov    $0x8,%esi
    2e47:	bf 0f 00 00 00       	mov    $0xf,%edi
  thread_data[thread_count].type = TIMER;
    2e4c:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e54:	49 89 c5             	mov    %rax,%r13
  thread_data[thread_count].task_count = total_barrier_count;
    2e57:	48 8b 05 ea 4b 00 00 	mov    0x4bea(%rip),%rax        # 7a48 <_IO_stdin_used+0xa48>
  thread_data[thread_count].type = TIMER;
    2e5e:	41 c7 82 08 1e 00 00 00 00 00 00 	movl   $0x0,0x1e08(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2e69:	49 89 82 a0 1e 00 00 	mov    %rax,0x1ea0(%r10)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2e70:	e8 2b f5 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2e75:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    2e7a:	48 8b 4c 24 58       	mov    0x58(%rsp),%rcx
    2e7f:	48 8b 74 24 50       	mov    0x50(%rsp),%rsi
    2e84:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    2e89:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2e8d:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    2e92:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2e97:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2e9b:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    2ea0:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
    2ea8:	48 89 48 18          	mov    %rcx,0x18(%rax)
    2eac:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
    2eb1:	48 89 70 20          	mov    %rsi,0x20(%rax)
    2eb5:	48 8d 35 6b 44 00 00 	lea    0x446b(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2ebc:	48 89 78 30          	mov    %rdi,0x30(%rax)
    2ec0:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    2ec5:	4d 8d b2 00 1e 00 00 	lea    0x1e00(%r10),%r14
    2ecc:	4c 89 10             	mov    %r10,(%rax)
    2ecf:	48 89 78 50          	mov    %rdi,0x50(%rax)
    2ed3:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    2ed8:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2edc:	ba 0c 00 00 00       	mov    $0xc,%edx
    2ee1:	48 89 78 58          	mov    %rdi,0x58(%rax)
    2ee5:	49 8d ba 00 23 00 00 	lea    0x2300(%r10),%rdi
    2eec:	4c 89 58 38          	mov    %r11,0x38(%rax)
    2ef0:	4c 89 48 40          	mov    %r9,0x40(%rax)
    2ef4:	4c 89 40 48          	mov    %r8,0x48(%rax)
    2ef8:	4c 89 70 60          	mov    %r14,0x60(%rax)
    2efc:	4c 89 78 68          	mov    %r15,0x68(%rax)
    2f00:	4c 8d 3d 99 09 00 00 	lea    0x999(%rip),%r15        # 38a0 <barriered_thread>
    2f07:	48 89 78 70          	mov    %rdi,0x70(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2f0b:	49 89 82 80 1e 00 00 	mov    %rax,0x1e80(%r10)
    2f12:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2f14:	41 c7 82 88 1e 00 00 0c 00 00 00 	movl   $0xc,0x1e88(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2f1f:	41 c7 82 90 1e 00 00 02 00 00 00 	movl   $0x2,0x1e90(%r10)
  thread_data[thread_count].thread_index = 0;
    2f2a:	41 c7 82 00 1e 00 00 00 00 00 00 	movl   $0x0,0x1e00(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2f35:	48 89 bc 24 80 00 00 00 	mov    %rdi,0x80(%rsp)
    2f3d:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].thread_index = 0;
    2f42:	4c 89 94 24 98 00 00 00 	mov    %r10,0x98(%rsp)
    2f4a:	e8 01 f5 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2f4f:	48 8d b3 a0 02 00 00 	lea    0x2a0(%rbx),%rsi
    2f56:	49 8d 7d 60          	lea    0x60(%r13),%rdi
    2f5a:	4c 89 f1             	mov    %r14,%rcx
    2f5d:	48 8d 15 dc 0c 00 00 	lea    0xcdc(%rip),%rdx        # 3c40 <timer_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    2f64:	45 31 f6             	xor    %r14d,%r14d
    2f67:	4c 89 eb             	mov    %r13,%rbx
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2f6a:	e8 01 f5 ff ff       	call   2470 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2f6f:	44 89 f0             	mov    %r14d,%eax
    2f72:	4d 89 ee             	mov    %r13,%r14
    2f75:	41 89 c5             	mov    %eax,%r13d
    thread_data[x].type = WORKER;
    2f78:	c7 45 08 01 00 00 00 	movl   $0x1,0x8(%rbp)
    2f7f:	44 89 ea             	mov    %r13d,%edx
    2f82:	bf 01 00 00 00       	mov    $0x1,%edi
    2f87:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2f89:	c7 85 a4 00 00 00 01 00 00 00 	movl   $0x1,0xa4(%rbp)
    2f93:	48 8d 35 6e 46 00 00 	lea    0x466e(%rip),%rsi        # 7608 <_IO_stdin_used+0x608>
  for (int x = 0 ; x < thread_count ; x++) {
    2f9a:	41 83 c5 01          	add    $0x1,%r13d
    2f9e:	e8 ad f4 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2fa3:	48 89 e9             	mov    %rbp,%rcx
    2fa6:	4c 89 e6             	mov    %r12,%rsi
    2fa9:	48 89 df             	mov    %rbx,%rdi
    2fac:	4c 89 fa             	mov    %r15,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2faf:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    2fb6:	48 83 c3 08          	add    $0x8,%rbx
    2fba:	49 83 c4 38          	add    $0x38,%r12
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2fbe:	e8 ad f4 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2fc3:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
    2fc7:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    2fcb:	be 08 00 00 00       	mov    $0x8,%esi
    2fd0:	e8 0b f3 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2fd5:	41 83 fd 0c          	cmp    $0xc,%r13d
    2fd9:	75 9d                	jne    2f78 <main+0x988>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2fdb:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2fe3:	48 8b 1d 66 4a 00 00 	mov    0x4a66(%rip),%rbx        # 7a50 <_IO_stdin_used+0xa50>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2fea:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    2fef:	4d 89 f5             	mov    %r14,%r13
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ff2:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    2ff7:	49 89 9a 20 21 00 00 	mov    %rbx,0x2120(%r10)
    thread_data[x].type = IO;
    2ffe:	41 c7 82 88 20 00 00 02 00 00 00 	movl   $0x2,0x2088(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3009:	e8 92 f3 ff ff       	call   23a0 <calloc@plt>
    300e:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3016:	be 00 08 00 00       	mov    $0x800,%esi
    301b:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    301d:	49 89 82 08 22 00 00 	mov    %rax,0x2208(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3024:	e8 87 f4 ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3029:	be 08 00 00 00       	mov    $0x8,%esi
    302e:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3033:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    303b:	41 89 82 10 22 00 00 	mov    %eax,0x2210(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3042:	e8 59 f3 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3047:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    304c:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    3051:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    3059:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    305e:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    3063:	4c 8b 74 24 78       	mov    0x78(%rsp),%r14
    3068:	4c 89 58 48          	mov    %r11,0x48(%rax)
    306c:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    3071:	4c 8b 7c 24 60       	mov    0x60(%rsp),%r15
    3076:	4c 89 48 50          	mov    %r9,0x50(%rax)
    307a:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    307f:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3084:	4c 89 40 58          	mov    %r8,0x58(%rax)
    3088:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    308d:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    3092:	4c 89 10             	mov    %r10,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    3095:	49 89 82 00 21 00 00 	mov    %rax,0x2100(%r10)
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    309c:	41 c7 82 08 21 00 00 0c 00 00 00 	movl   $0xc,0x2108(%r10)
    thread_data[x].thread_index = x;
    30a7:	41 c7 82 80 20 00 00 0d 00 00 00 	movl   $0xd,0x2080(%r10)
      my_thread_data[n] = &thread_data[n]; 
    30b2:	4c 89 70 10          	mov    %r14,0x10(%rax)
    30b6:	48 89 68 18          	mov    %rbp,0x18(%rax)
    30ba:	4c 89 60 20          	mov    %r12,0x20(%rax)
    30be:	48 89 78 28          	mov    %rdi,0x28(%rax)
    30c2:	bf 01 00 00 00       	mov    $0x1,%edi
    30c7:	48 89 48 30          	mov    %rcx,0x30(%rax)
    30cb:	48 89 70 38          	mov    %rsi,0x38(%rax)
    30cf:	48 8d 35 6f 42 00 00 	lea    0x426f(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    30d6:	48 89 50 40          	mov    %rdx,0x40(%rax)
    30da:	ba 0d 00 00 00       	mov    $0xd,%edx
    30df:	4c 89 78 08          	mov    %r15,0x8(%rax)
    30e3:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    30e5:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    30ea:	e8 61 f3 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    30ef:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    30f4:	49 8d 7d 68          	lea    0x68(%r13),%rdi
    30f8:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    3100:	48 8d 15 19 1e 00 00 	lea    0x1e19(%rip),%rdx        # 4f20 <io_thread>
    3107:	48 05 d8 02 00 00    	add    $0x2d8,%rax
    310d:	48 89 c6             	mov    %rax,%rsi
    3110:	e8 5b f3 ff ff       	call   2470 <pthread_create@plt>
    3115:	ba 0e 00 00 00       	mov    $0xe,%edx
    311a:	48 8d 35 3b 42 00 00 	lea    0x423b(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    3121:	31 c0                	xor    %eax,%eax
    3123:	bf 01 00 00 00       	mov    $0x1,%edi
    3128:	e8 23 f3 ff ff       	call   2450 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    312d:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    3132:	48 8b 44 24 48       	mov    0x48(%rsp),%rax

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3137:	be 08 00 00 00       	mov    $0x8,%esi
    313c:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x].task_count = 0;
    3141:	49 89 9a a0 23 00 00 	mov    %rbx,0x23a0(%r10)
    3148:	31 db                	xor    %ebx,%ebx
    thread_data[x].type = EXTERNAL;
    314a:	41 c7 82 08 23 00 00 03 00 00 00 	movl   $0x3,0x2308(%r10)
    thread_data[x].buffers = &buffers[buffer_index];
    3155:	49 89 82 80 24 00 00 	mov    %rax,0x2480(%r10)
    315c:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3161:	e8 3a f2 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3166:	4c 8b 54 24 48       	mov    0x48(%rsp),%r10
    316b:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    3170:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    3175:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    317a:	4c 89 70 10          	mov    %r14,0x10(%rax)
    317e:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3183:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    3188:	4c 89 10             	mov    %r10,(%rax)
    318b:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    3190:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    3195:	48 89 68 18          	mov    %rbp,0x18(%rax)
    3199:	48 8d 2d f7 41 00 00 	lea    0x41f7(%rip),%rbp        # 7397 <_IO_stdin_used+0x397>
    31a0:	4c 89 60 20          	mov    %r12,0x20(%rax)
    31a4:	4c 8d a4 24 a0 00 00 00 	lea    0xa0(%rsp),%r12
    31ac:	48 89 78 28          	mov    %rdi,0x28(%rax)
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31b0:	49 8d 7d 70          	lea    0x70(%r13),%rdi
      my_thread_data[n] = &thread_data[n]; 
    31b4:	48 89 48 30          	mov    %rcx,0x30(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31b8:	48 8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%rcx
      my_thread_data[n] = &thread_data[n]; 
    31c0:	48 89 70 38          	mov    %rsi,0x38(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31c4:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    31cc:	48 89 50 40          	mov    %rdx,0x40(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31d0:	48 8d 15 a9 09 00 00 	lea    0x9a9(%rip),%rdx        # 3b80 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    31d7:	4c 89 58 48          	mov    %r11,0x48(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31db:	48 81 c6 10 03 00 00 	add    $0x310,%rsi
      my_thread_data[n] = &thread_data[n]; 
    31e2:	4c 89 48 50          	mov    %r9,0x50(%rax)
    31e6:	4c 89 40 58          	mov    %r8,0x58(%rax)
    thread_data[x].threads = my_thread_data;
    31ea:	49 89 82 80 23 00 00 	mov    %rax,0x2380(%r10)
      my_thread_data[n] = &thread_data[n]; 
    31f1:	4c 89 78 08          	mov    %r15,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    31f5:	48 8b 05 5c 48 00 00 	mov    0x485c(%rip),%rax        # 7a58 <_IO_stdin_used+0xa58>
    thread_data[x].thread_index = x;
    31fc:	41 c7 82 00 23 00 00 0e 00 00 00 	movl   $0xe,0x2300(%r10)
    thread_data[x].thread_count = thread_count;
    3207:	49 89 82 88 23 00 00 	mov    %rax,0x2388(%r10)
    thread_data[x].thread_index = x;
    320e:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3213:	e8 58 f2 ff ff       	call   2470 <pthread_create@plt>
    3218:	48 8d 3d 5a 41 00 00 	lea    0x415a(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    321f:	e8 cc f0 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3224:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    3229:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    void * result; 
    pthread_join(thread[x], &result);
    3230:	49 8b 7c dd 00       	mov    0x0(%r13,%rbx,8),%rdi
    3235:	4c 89 e6             	mov    %r12,%rsi
    3238:	e8 b3 f2 ff ff       	call   24f0 <pthread_join@plt>
    323d:	89 da                	mov    %ebx,%edx
    323f:	48 89 ee             	mov    %rbp,%rsi
    3242:	bf 01 00 00 00       	mov    $0x1,%edi
    3247:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3249:	48 83 c3 01          	add    $0x1,%rbx
    324d:	e8 fe f1 ff ff       	call   2450 <__printf_chk@plt>
    3252:	48 83 fb 0f          	cmp    $0xf,%rbx
    3256:	75 d8                	jne    3230 <main+0xc40>
    3258:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    325d:	4d 89 f2             	mov    %r14,%r10
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    3260:	31 db                	xor    %ebx,%ebx
  long sents = 0;
    3262:	31 ed                	xor    %ebp,%ebp
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3264:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    3269:	4d 8d ae 98 00 00 00 	lea    0x98(%r14),%r13
  long total = 0;
    3270:	45 31 f6             	xor    %r14d,%r14d
  long ingests = 0;
    3273:	45 31 c9             	xor    %r9d,%r9d
    3276:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    327b:	4d 89 ef             	mov    %r13,%r15
    327e:	4d 89 f5             	mov    %r14,%r13
  for (int x = 0 ; x < thread_count ; x++) {
    3281:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    if (x % 2 == 1) {
    3289:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    328d:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    3292:	89 f8                	mov    %edi,%eax
    3294:	41 89 fc             	mov    %edi,%r12d
      other = (x + 1) % total_threads;
    3297:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
    329a:	83 e0 01             	and    $0x1,%eax
      other = abs(x - 1) % total_threads;
    329d:	41 83 ec 01          	sub    $0x1,%r12d
      other = (x + 1) % total_threads;
    32a1:	89 7c 24 10          	mov    %edi,0x10(%rsp)
      other = abs(x - 1) % total_threads;
    32a5:	85 c0                	test   %eax,%eax
    32a7:	44 0f 44 e7          	cmove  %edi,%r12d
    32ab:	bf 0a 00 00 00       	mov    $0xa,%edi
    32b0:	e8 1b f0 ff ff       	call   22d0 <putchar@plt>
    32b5:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    32ba:	bf 01 00 00 00       	mov    $0x1,%edi
    32bf:	48 8d 35 e5 40 00 00 	lea    0x40e5(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    32c6:	48 8b 10             	mov    (%rax),%rdx
    32c9:	31 c0                	xor    %eax,%eax
    32cb:	e8 80 f1 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    32d0:	49 63 57 08          	movslq 0x8(%r15),%rdx
    32d4:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    32d9:	85 d2                	test   %edx,%edx
    32db:	0f 8e 0e 04 00 00    	jle    36ef <main+0x10ff>
    32e1:	49 8b 07             	mov    (%r15),%rax
    32e4:	48 c1 e2 09          	shl    $0x9,%rdx
    32e8:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    long v = 0;
    32ec:	31 d2                	xor    %edx,%edx
    32ee:	66 90                	xchg   %ax,%ax
      v += thread_data[me].tasks[n].v;
    32f0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    32f7:	48 05 00 02 00 00    	add    $0x200,%rax
    32fd:	48 39 f0             	cmp    %rsi,%rax
    3300:	75 ee                	jne    32f0 <main+0xd00>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3302:	4d 63 e4             	movslq %r12d,%r12
    3305:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    330a:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    330e:	48 c1 e0 07          	shl    $0x7,%rax
    3312:	48 01 f8             	add    %rdi,%rax
    3315:	48 63 b0 a0 00 00 00 	movslq 0xa0(%rax),%rsi
    331c:	85 f6                	test   %esi,%esi
    331e:	7e 22                	jle    3342 <main+0xd52>
    3320:	48 8b 80 98 00 00 00 	mov    0x98(%rax),%rax
    3327:	48 c1 e6 09          	shl    $0x9,%rsi
    332b:	48 01 c6             	add    %rax,%rsi
    332e:	66 90                	xchg   %ax,%ax
      v += thread_data[other].tasks[n].v;
    3330:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3337:	48 05 00 02 00 00    	add    $0x200,%rax
    333d:	48 39 f0             	cmp    %rsi,%rax
    3340:	75 ee                	jne    3330 <main+0xd40>
    3342:	48 8d 35 77 40 00 00 	lea    0x4077(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    3349:	bf 01 00 00 00       	mov    $0x1,%edi
    334e:	31 c0                	xor    %eax,%eax
    3350:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    3355:	e8 f6 f0 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    335a:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    335f:	bf 01 00 00 00       	mov    $0x1,%edi
    3364:	48 8b 30             	mov    (%rax),%rsi
    3367:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3371:	48 f7 ee             	imul   %rsi
    3374:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3378:	31 c0                	xor    %eax,%eax
    337a:	48 d1 fa             	sar    %rdx
    337d:	48 29 f2             	sub    %rsi,%rdx
    3380:	48 8d 35 a9 42 00 00 	lea    0x42a9(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    3387:	e8 c4 f0 ff ff       	call   2450 <__printf_chk@plt>
    338c:	bf 0a 00 00 00       	mov    $0xa,%edi
    3391:	e8 3a ef ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3396:	49 63 47 08          	movslq 0x8(%r15),%rax
    339a:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    339f:	85 c0                	test   %eax,%eax
    33a1:	0f 8e e5 00 00 00    	jle    348c <main+0xe9c>
    33a7:	49 8b 17             	mov    (%r15),%rdx
    33aa:	48 c1 e0 09          	shl    $0x9,%rax
    33ae:	48 8d 34 10          	lea    (%rax,%rdx,1),%rsi
    33b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33b8:	48 8b 82 68 01 00 00 	mov    0x168(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    33bf:	4c 03 aa 08 01 00 00 	add    0x108(%rdx),%r13
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    33c6:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
      ingests += thread_data[x].tasks[n].ingest_count;
    33cd:	4c 03 b2 60 ff ff ff 	add    -0xa0(%rdx),%r14
      sends += thread_data[x].tasks[n].sends;
    33d4:	4c 03 8a 70 ff ff ff 	add    -0x90(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33db:	48 03 a8 88 00 00 00 	add    0x88(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33e2:	48 03 98 90 00 00 00 	add    0x90(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33e9:	48 03 a8 88 01 00 00 	add    0x188(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33f0:	48 03 98 90 01 00 00 	add    0x190(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33f7:	48 03 a8 88 02 00 00 	add    0x288(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33fe:	48 03 98 90 02 00 00 	add    0x290(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3405:	48 03 a8 88 03 00 00 	add    0x388(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    340c:	48 03 98 90 03 00 00 	add    0x390(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3413:	48 03 a8 88 04 00 00 	add    0x488(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    341a:	48 03 98 90 04 00 00 	add    0x490(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3421:	48 03 a8 88 05 00 00 	add    0x588(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3428:	48 03 98 90 05 00 00 	add    0x590(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    342f:	48 03 a8 88 06 00 00 	add    0x688(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3436:	48 03 98 90 06 00 00 	add    0x690(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    343d:	48 03 a8 88 07 00 00 	add    0x788(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3444:	48 03 98 90 07 00 00 	add    0x790(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    344b:	48 03 a8 88 08 00 00 	add    0x888(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3452:	48 03 98 90 08 00 00 	add    0x890(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3459:	48 03 a8 88 09 00 00 	add    0x988(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3460:	48 03 98 90 09 00 00 	add    0x990(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3467:	48 03 a8 88 0a 00 00 	add    0xa88(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    346e:	48 03 98 90 0a 00 00 	add    0xa90(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3475:	48 03 a8 88 0b 00 00 	add    0xb88(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    347c:	48 03 98 90 0b 00 00 	add    0xb90(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3483:	48 39 f2             	cmp    %rsi,%rdx
    3486:	0f 85 2c ff ff ff    	jne    33b8 <main+0xdc8>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    348c:	45 31 e4             	xor    %r12d,%r12d
    348f:	49 83 bf 78 01 00 00 00 	cmpq   $0x0,0x178(%r15)
    3497:	0f 8e 7f 00 00 00    	jle    351c <main+0xf2c>
    349d:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    34a2:	4c 89 fb             	mov    %r15,%rbx
    34a5:	4d 89 e7             	mov    %r12,%r15
    34a8:	4d 89 cc             	mov    %r9,%r12
    34ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    34b0:	48 8b 83 68 01 00 00 	mov    0x168(%rbx),%rax
    34b7:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    34bb:	48 83 ec 08          	sub    $0x8,%rsp
    34bf:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    34c4:	49 83 c7 01          	add    $0x1,%r15
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    34c8:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    34cc:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    34d6:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    34da:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    34de:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    34e1:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    34e5:	4c 2b 01             	sub    (%rcx),%r8
    34e8:	31 c0                	xor    %eax,%eax
    34ea:	8b 49 20             	mov    0x20(%rcx),%ecx
    34ed:	56                   	push   %rsi
    34ee:	48 8d 35 5b 41 00 00 	lea    0x415b(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    34f5:	48 c1 ea 12          	shr    $0x12,%rdx
    34f9:	49 89 d1             	mov    %rdx,%r9
    34fc:	ba 02 00 00 00       	mov    $0x2,%edx
    3501:	e8 4a ef ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3506:	58                   	pop    %rax
    3507:	5a                   	pop    %rdx
    3508:	4c 39 bb 78 01 00 00 	cmp    %r15,0x178(%rbx)
    350f:	7f 9f                	jg     34b0 <main+0xec0>
    3511:	49 89 df             	mov    %rbx,%r15
    3514:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    3519:	4d 89 e1             	mov    %r12,%r9
  for (int x = 0 ; x < thread_count ; x++) {
    351c:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    3522:	49 81 c7 80 02 00 00 	add    $0x280,%r15
    3529:	83 7c 24 10 0c       	cmpl   $0xc,0x10(%rsp)
    352e:	0f 85 55 fd ff ff    	jne    3289 <main+0xc99>
    3534:	4c 89 ea             	mov    %r13,%rdx
    3537:	48 8d 35 8f 3e 00 00 	lea    0x3e8f(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    353e:	31 c0                	xor    %eax,%eax
    3540:	4d 89 cf             	mov    %r9,%r15
    3543:	bf 01 00 00 00       	mov    $0x1,%edi
    3548:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    354d:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    3557:	e8 f4 ee ff ff       	call   2450 <__printf_chk@plt>
    355c:	bf 0a 00 00 00       	mov    $0xa,%edi
    3561:	e8 6a ed ff ff       	call   22d0 <putchar@plt>
    3566:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    356b:	bf 01 00 00 00       	mov    $0x1,%edi
    3570:	48 8d 35 29 41 00 00 	lea    0x4129(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    3577:	48 8b 50 08          	mov    0x8(%rax),%rdx
    357b:	31 c0                	xor    %eax,%eax
    357d:	e8 ce ee ff ff       	call   2450 <__printf_chk@plt>
    3582:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3587:	bf 01 00 00 00       	mov    $0x1,%edi
    358c:	48 8d 35 35 41 00 00 	lea    0x4135(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    3593:	4c 89 c8             	mov    %r9,%rax
    3596:	49 c1 f9 3f          	sar    $0x3f,%r9
    359a:	49 f7 ec             	imul   %r12
    359d:	31 c0                	xor    %eax,%eax
    359f:	48 d1 fa             	sar    %rdx
    35a2:	4c 29 ca             	sub    %r9,%rdx
    35a5:	e8 a6 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    35aa:	4c 89 f8             	mov    %r15,%rax
    35ad:	4d 89 fb             	mov    %r15,%r11
    35b0:	bf 01 00 00 00       	mov    $0x1,%edi
    35b5:	49 f7 ec             	imul   %r12
    35b8:	49 c1 fb 3f          	sar    $0x3f,%r11
    35bc:	48 8d 35 35 41 00 00 	lea    0x4135(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    35c3:	31 c0                	xor    %eax,%eax
    35c5:	48 d1 fa             	sar    %rdx
    35c8:	4c 29 da             	sub    %r11,%rdx
    35cb:	e8 80 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    35d0:	4c 89 e8             	mov    %r13,%rax
    35d3:	4c 89 e9             	mov    %r13,%rcx
    35d6:	bf 01 00 00 00       	mov    $0x1,%edi
    35db:	49 f7 ec             	imul   %r12
    35de:	48 c1 f9 3f          	sar    $0x3f,%rcx
    35e2:	48 8d 35 3f 41 00 00 	lea    0x413f(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    35e9:	31 c0                	xor    %eax,%eax
    35eb:	48 d1 fa             	sar    %rdx
    35ee:	48 29 ca             	sub    %rcx,%rdx
    35f1:	e8 5a ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    35f6:	48 89 e8             	mov    %rbp,%rax
    35f9:	48 c1 fd 3f          	sar    $0x3f,%rbp
    35fd:	48 8d 35 dd 3d 00 00 	lea    0x3ddd(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    3604:	49 f7 ec             	imul   %r12
    3607:	bf 01 00 00 00       	mov    $0x1,%edi
    360c:	31 c0                	xor    %eax,%eax
    360e:	48 d1 fa             	sar    %rdx
    3611:	48 29 ea             	sub    %rbp,%rdx
    3614:	e8 37 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3619:	48 89 d8             	mov    %rbx,%rax
    361c:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3620:	48 8d 35 cb 3d 00 00 	lea    0x3dcb(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    3627:	49 f7 ec             	imul   %r12
    362a:	bf 01 00 00 00       	mov    $0x1,%edi
    362f:	48 d1 fa             	sar    %rdx
    3632:	48 29 da             	sub    %rbx,%rdx
    3635:	31 c0                	xor    %eax,%eax
    3637:	e8 14 ee ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    363c:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    3644:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    364d:	0f 85 a3 00 00 00    	jne    36f6 <main+0x1106>
    3653:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    365a:	31 c0                	xor    %eax,%eax
    365c:	5b                   	pop    %rbx
    365d:	5d                   	pop    %rbp
    365e:	41 5c                	pop    %r12
    3660:	41 5d                	pop    %r13
    3662:	41 5e                	pop    %r14
    3664:	41 5f                	pop    %r15
    3666:	c3                   	ret
          thread_data[x].tasks[y].run = barriered_work; 
    3667:	48 8d 05 a2 22 00 00 	lea    0x22a2(%rip),%rax        # 5910 <barriered_work>
    366e:	bb 02 00 00 00       	mov    $0x2,%ebx
    3673:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    367a:	e9 d5 f2 ff ff       	jmp    2954 <main+0x364>
      other = (x + 1) % total_threads;
    367f:	b8 89 88 88 88       	mov    $0x88888889,%eax
    3684:	45 89 fe             	mov    %r15d,%r14d
      my_thread_data[0] = &thread_data[x]; 
    3687:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    368c:	4c 89 e9             	mov    %r13,%rcx
      other = (x + 1) % total_threads;
    368f:	4c 0f af f0          	imul   %rax,%r14
    3693:	89 ea                	mov    %ebp,%edx
      thread_data[x].thread_index = 0;
    3695:	41 c7 45 00 00 00 00 00 	movl   $0x0,0x0(%r13)
    369d:	48 8d 35 65 3c 00 00 	lea    0x3c65(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      my_thread_data[0] = &thread_data[x]; 
    36a4:	4c 89 2f             	mov    %r13,(%rdi)
      other = (x + 1) % total_threads;
    36a7:	49 c1 ee 23          	shr    $0x23,%r14
    36ab:	44 89 f0             	mov    %r14d,%eax
    36ae:	c1 e0 04             	shl    $0x4,%eax
    36b1:	44 29 f0             	sub    %r14d,%eax
    36b4:	45 89 fe             	mov    %r15d,%r14d
    36b7:	41 29 c6             	sub    %eax,%r14d
      my_thread_data[1] = &thread_data[other]; 
    36ba:	49 63 c6             	movslq %r14d,%rax
    36bd:	4c 8d 04 80          	lea    (%rax,%rax,4),%r8
    36c1:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    36c6:	49 c1 e0 07          	shl    $0x7,%r8
    36ca:	49 01 c0             	add    %rax,%r8
    36cd:	31 c0                	xor    %eax,%eax
    36cf:	4c 89 47 08          	mov    %r8,0x8(%rdi)
    36d3:	bf 01 00 00 00       	mov    $0x1,%edi
    36d8:	e8 73 ed ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    36dd:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    36e2:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    36e7:	49 89 c4             	mov    %rax,%r12
    36ea:	e9 4d f1 ff ff       	jmp    283c <main+0x24c>
    long v = 0;
    36ef:	31 d2                	xor    %edx,%edx
    36f1:	e9 0c fc ff ff       	jmp    3302 <main+0xd12>
}
    36f6:	e8 35 ec ff ff       	call   2330 <__stack_chk_fail@plt>
    36fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003700 <_start>:
    3700:	f3 0f 1e fa          	endbr64
    3704:	31 ed                	xor    %ebp,%ebp
    3706:	49 89 d1             	mov    %rdx,%r9
    3709:	5e                   	pop    %rsi
    370a:	48 89 e2             	mov    %rsp,%rdx
    370d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3711:	50                   	push   %rax
    3712:	54                   	push   %rsp
    3713:	45 31 c0             	xor    %r8d,%r8d
    3716:	31 c9                	xor    %ecx,%ecx
    3718:	48 8d 3d d1 ee ff ff 	lea    -0x112f(%rip),%rdi        # 25f0 <main>
    371f:	ff 15 b3 68 00 00    	call   *0x68b3(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3725:	f4                   	hlt
    3726:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003730 <deregister_tm_clones>:
    3730:	48 8d 3d e9 68 00 00 	lea    0x68e9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3737:	48 8d 05 e2 68 00 00 	lea    0x68e2(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    373e:	48 39 f8             	cmp    %rdi,%rax
    3741:	74 15                	je     3758 <deregister_tm_clones+0x28>
    3743:	48 8b 05 96 68 00 00 	mov    0x6896(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    374a:	48 85 c0             	test   %rax,%rax
    374d:	74 09                	je     3758 <deregister_tm_clones+0x28>
    374f:	ff e0                	jmp    *%rax
    3751:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3758:	c3                   	ret
    3759:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003760 <register_tm_clones>:
    3760:	48 8d 3d b9 68 00 00 	lea    0x68b9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3767:	48 8d 35 b2 68 00 00 	lea    0x68b2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    376e:	48 29 fe             	sub    %rdi,%rsi
    3771:	48 89 f0             	mov    %rsi,%rax
    3774:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3778:	48 c1 f8 03          	sar    $0x3,%rax
    377c:	48 01 c6             	add    %rax,%rsi
    377f:	48 d1 fe             	sar    %rsi
    3782:	74 14                	je     3798 <register_tm_clones+0x38>
    3784:	48 8b 05 65 68 00 00 	mov    0x6865(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    378b:	48 85 c0             	test   %rax,%rax
    378e:	74 08                	je     3798 <register_tm_clones+0x38>
    3790:	ff e0                	jmp    *%rax
    3792:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3798:	c3                   	ret
    3799:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037a0 <__do_global_dtors_aux>:
    37a0:	f3 0f 1e fa          	endbr64
    37a4:	80 3d 7d 68 00 00 00 	cmpb   $0x0,0x687d(%rip)        # a028 <completed.0>
    37ab:	75 2b                	jne    37d8 <__do_global_dtors_aux+0x38>
    37ad:	55                   	push   %rbp
    37ae:	48 83 3d 42 68 00 00 00 	cmpq   $0x0,0x6842(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    37b6:	48 89 e5             	mov    %rsp,%rbp
    37b9:	74 0c                	je     37c7 <__do_global_dtors_aux+0x27>
    37bb:	48 8b 3d 46 68 00 00 	mov    0x6846(%rip),%rdi        # a008 <__dso_handle>
    37c2:	e8 e9 ea ff ff       	call   22b0 <__cxa_finalize@plt>
    37c7:	e8 64 ff ff ff       	call   3730 <deregister_tm_clones>
    37cc:	c6 05 55 68 00 00 01 	movb   $0x1,0x6855(%rip)        # a028 <completed.0>
    37d3:	5d                   	pop    %rbp
    37d4:	c3                   	ret
    37d5:	0f 1f 00             	nopl   (%rax)
    37d8:	c3                   	ret
    37d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037e0 <frame_dummy>:
    37e0:	f3 0f 1e fa          	endbr64
    37e4:	e9 77 ff ff ff       	jmp    3760 <register_tm_clones>
    37e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037f0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    37f0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    37f4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    37fb:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
  data->v++; // thread local
    3802:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    380a:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    380e:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3812:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3819:	48 85 c9             	test   %rcx,%rcx
    381c:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3823:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3827:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    382b:	31 c0                	xor    %eax,%eax
    382d:	c3                   	ret
    382e:	66 90                	xchg   %ax,%ax

0000000000003830 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3830:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3834:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    383b:	85 c9                	test   %ecx,%ecx
    383d:	7e 57                	jle    3896 <barriered_reset+0x66>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    383f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3846:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    384d:	48 c1 e1 09          	shl    $0x9,%rcx
    3851:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    3858:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    385c:	48 8b b0 98 00 00 00 	mov    0x98(%rax),%rsi
    3863:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    3865:	48 8b 92 98 00 00 00 	mov    0x98(%rdx),%rdx
    386c:	0f 1f 40 00          	nopl   0x0(%rax)
    3870:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3878:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3880:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    388b:	48 05 00 02 00 00    	add    $0x200,%rax
    3891:	48 39 c1             	cmp    %rax,%rcx
    3894:	75 da                	jne    3870 <barriered_reset+0x40>
  asm volatile ("sfence" ::: "memory");
    3896:	0f ae f8             	sfence
}
    3899:	31 c0                	xor    %eax,%eax
    389b:	c3                   	ret
    389c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000038a0 <barriered_thread>:
void* barriered_thread(void *arg) {
    38a0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    38a4:	83 bf a4 00 00 00 01 	cmpl   $0x1,0xa4(%rdi)
    38ab:	0f 85 cb 02 00 00    	jne    3b7c <barriered_thread+0x2dc>
void* barriered_thread(void *arg) {
    38b1:	41 56                	push   %r14
    38b3:	41 55                	push   %r13
    38b5:	49 89 fd             	mov    %rdi,%r13
    38b8:	41 54                	push   %r12
    38ba:	55                   	push   %rbp
    38bb:	31 ed                	xor    %ebp,%ebp
    38bd:	53                   	push   %rbx
    38be:	31 db                	xor    %ebx,%ebx
    if (t >= data->task_count) {
    38c0:	41 8b 95 a0 00 00 00 	mov    0xa0(%r13),%edx
    38c7:	39 da                	cmp    %ebx,%edx
    38c9:	7f 12                	jg     38dd <barriered_thread+0x3d>
      data->cycles++;
    38cb:	49 83 85 18 02 00 00 01 	addq   $0x1,0x218(%r13)
    for (; t < data->task_count; t++) {
    38d3:	31 db                	xor    %ebx,%ebx
    38d5:	85 d2                	test   %edx,%edx
    38d7:	0f 8e 83 01 00 00    	jle    3a60 <barriered_thread+0x1c0>
    38dd:	4c 63 e3             	movslq %ebx,%r12
    38e0:	49 c1 e4 09          	shl    $0x9,%r12
    38e4:	eb 1c                	jmp    3902 <barriered_thread+0x62>
    38e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    38f0:	83 c3 01             	add    $0x1,%ebx
    38f3:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    38fa:	39 d3                	cmp    %edx,%ebx
    38fc:	0f 8d 5e 01 00 00    	jge    3a60 <barriered_thread+0x1c0>
      if (data->tasks[t].available == 1) {
    3902:	49 8b 85 98 00 00 00 	mov    0x98(%r13),%rax
    3909:	4a 8d 34 20          	lea    (%rax,%r12,1),%rsi
    390d:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    3914:	75 da                	jne    38f0 <barriered_thread+0x50>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3916:	41 8b bd 88 00 00 00 	mov    0x88(%r13),%edi
          previous = t - 1;
    391d:	83 ea 01             	sub    $0x1,%edx
    3920:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3923:	85 db                	test   %ebx,%ebx
    3925:	0f 4f d1             	cmovg  %ecx,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3928:	85 ff                	test   %edi,%edi
    392a:	0f 8e 60 01 00 00    	jle    3a90 <barriered_thread+0x1f0>
    3930:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3937:	48 63 ca             	movslq %edx,%rcx
    393a:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    393d:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3940:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    3947:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    394e:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    3952:	45 31 f6             	xor    %r14d,%r14d
    3955:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3959:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3960:	48 8b 10             	mov    (%rax),%rdx
    3963:	4c 8b 9a 98 00 00 00 	mov    0x98(%rdx),%r11
    396a:	49 01 cb             	add    %rcx,%r11
    396d:	4c 89 da             	mov    %r11,%rdx
    3970:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    3977:	75 04                	jne    397d <barriered_thread+0xdd>
            arrived++;
    3979:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    397d:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    3984:	75 04                	jne    398a <barriered_thread+0xea>
            prearrive++;
    3986:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    398a:	48 83 c0 08          	add    $0x8,%rax
    398e:	48 39 f0             	cmp    %rsi,%rax
    3991:	75 cd                	jne    3960 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    3993:	44 39 d7             	cmp    %r10d,%edi
    3996:	0f 84 e4 00 00 00    	je     3a80 <barriered_thread+0x1e0>
    399c:	45 85 d2             	test   %r10d,%r10d
    399f:	0f 84 db 00 00 00    	je     3a80 <barriered_thread+0x1e0>
        if (arrived == 0 || arrived == data->thread_count) {
    39a5:	45 85 f6             	test   %r14d,%r14d
    39a8:	74 0d                	je     39b7 <barriered_thread+0x117>
    39aa:	45 39 b5 88 00 00 00 	cmp    %r14d,0x88(%r13)
    39b1:	0f 85 a9 00 00 00    	jne    3a60 <barriered_thread+0x1c0>
    39b7:	49 8b 85 98 00 00 00 	mov    0x98(%r13),%rax
          data->tasks[t].prearrive++;
    39be:	4c 01 e0             	add    %r12,%rax
    39c1:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    39c8:	85 db                	test   %ebx,%ebx
    39ca:	75 14                	jne    39e0 <barriered_thread+0x140>
    39cc:	49 8b b5 b0 01 00 00 	mov    0x1b0(%r13),%rsi
    39d3:	49 3b b5 b8 01 00 00 	cmp    0x1b8(%r13),%rsi
    39da:	0f 8c 78 01 00 00    	jl     3b58 <barriered_thread+0x2b8>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    39e0:	49 63 4d 00          	movslq 0x0(%r13),%rcx
    39e4:	49 8b 95 80 00 00 00 	mov    0x80(%r13),%rdx
          data->tasks[t].available = 0;
    39eb:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    39f5:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    39f9:	48 8b ba 98 00 00 00 	mov    0x98(%rdx),%rdi
    3a00:	4c 01 e7             	add    %r12,%rdi
    3a03:	ff 90 18 01 00 00    	call   *0x118(%rax)
          data->tasks[t].arrived++;
    3a09:	49 8b 85 98 00 00 00 	mov    0x98(%r13),%rax
    3a10:	4c 01 e0             	add    %r12,%rax
    3a13:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3a1a:	41 8b 85 a0 00 00 00 	mov    0xa0(%r13),%eax
          data->iteration_count++;
    3a21:	49 83 85 a8 01 00 00 01 	addq   $0x1,0x1a8(%r13)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3a29:	83 e8 01             	sub    $0x1,%eax
    3a2c:	39 d8                	cmp    %ebx,%eax
    3a2e:	0f 84 b4 00 00 00    	je     3ae8 <barriered_thread+0x248>
          asm volatile ("sfence" ::: "memory");
    3a34:	0f ae f8             	sfence
          if (waiting == 0) {
    3a37:	85 ed                	test   %ebp,%ebp
    3a39:	0f 84 e1 00 00 00    	je     3b20 <barriered_thread+0x280>
    for (; t < data->task_count; t++) {
    3a3f:	41 8b 95 a0 00 00 00 	mov    0xa0(%r13),%edx
    3a46:	83 c3 01             	add    $0x1,%ebx
    3a49:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    3a50:	39 d3                	cmp    %edx,%ebx
    3a52:	0f 8c aa fe ff ff    	jl     3902 <barriered_thread+0x62>
    3a58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  while (data->running == 1) {
    3a60:	41 83 bd a4 00 00 00 01 	cmpl   $0x1,0xa4(%r13)
    3a68:	0f 84 52 fe ff ff    	je     38c0 <barriered_thread+0x20>
}
    3a6e:	5b                   	pop    %rbx
    3a6f:	31 c0                	xor    %eax,%eax
    3a71:	5d                   	pop    %rbp
    3a72:	41 5c                	pop    %r12
    3a74:	41 5d                	pop    %r13
    3a76:	41 5e                	pop    %r14
    3a78:	c3                   	ret
    3a79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          if (waiting == 1) {
    3a80:	83 fd 01             	cmp    $0x1,%ebp
    3a83:	74 1b                	je     3aa0 <barriered_thread+0x200>
        int arrived = 0; 
    3a85:	31 ed                	xor    %ebp,%ebp
    3a87:	e9 19 ff ff ff       	jmp    39a5 <barriered_thread+0x105>
    3a8c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    3a90:	83 fd 01             	cmp    $0x1,%ebp
    3a93:	0f 85 25 ff ff ff    	jne    39be <barriered_thread+0x11e>
        int arrived = 0; 
    3a99:	45 31 f6             	xor    %r14d,%r14d
    3a9c:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3aa0:	49 8b 85 08 02 00 00 	mov    0x208(%r13),%rax
    3aa7:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    3aac:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3aae:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3ab2:	49 8b 85 00 02 00 00 	mov    0x200(%r13),%rax
    3ab9:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3abe:	e8 4d e8 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3ac3:	49 8b 85 08 02 00 00 	mov    0x208(%r13),%rax
    3aca:	48 83 c0 01          	add    $0x1,%rax
    3ace:	48 99                	cqto
    3ad0:	49 f7 bd 10 02 00 00 	idivq  0x210(%r13)
    3ad7:	49 89 95 08 02 00 00 	mov    %rdx,0x208(%r13)
            waiting = 0; 
    3ade:	e9 c2 fe ff ff       	jmp    39a5 <barriered_thread+0x105>
    3ae3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3ae8:	49 8b b5 b0 01 00 00 	mov    0x1b0(%r13),%rsi
    3aef:	49 3b b5 b8 01 00 00 	cmp    0x1b8(%r13),%rsi
    3af6:	0f 8d 38 ff ff ff    	jge    3a34 <barriered_thread+0x194>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    3afc:	48 c1 e6 04          	shl    $0x4,%rsi
    3b00:	bf 04 00 00 00       	mov    $0x4,%edi
    3b05:	49 03 b5 a0 01 00 00 	add    0x1a0(%r13),%rsi
    3b0c:	e8 ff e7 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3b11:	49 83 85 b0 01 00 00 01 	addq   $0x1,0x1b0(%r13)
    3b19:	e9 16 ff ff ff       	jmp    3a34 <barriered_thread+0x194>
    3b1e:	66 90                	xchg   %ax,%ax
            data->task_snapshot[data->task_timestamp_count].task = t;
    3b20:	49 8b 85 08 02 00 00 	mov    0x208(%r13),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3b27:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3b2c:	bd 01 00 00 00       	mov    $0x1,%ebp
            data->task_snapshot[data->task_timestamp_count].task = t;
    3b31:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3b35:	49 8b 85 00 02 00 00 	mov    0x200(%r13),%rax
    3b3c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3b40:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3b43:	e8 c8 e7 ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3b48:	41 8b 95 a0 00 00 00 	mov    0xa0(%r13),%edx
    3b4f:	e9 9c fd ff ff       	jmp    38f0 <barriered_thread+0x50>
    3b54:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3b58:	48 c1 e6 04          	shl    $0x4,%rsi
    3b5c:	bf 04 00 00 00       	mov    $0x4,%edi
    3b61:	49 03 b5 98 01 00 00 	add    0x198(%r13),%rsi
    3b68:	e8 a3 e7 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3b6d:	49 8b 85 98 00 00 00 	mov    0x98(%r13),%rax
    3b74:	4c 01 e0             	add    %r12,%rax
    3b77:	e9 64 fe ff ff       	jmp    39e0 <barriered_thread+0x140>
}
    3b7c:	31 c0                	xor    %eax,%eax
    3b7e:	c3                   	ret
    3b7f:	90                   	nop

0000000000003b80 <external_thread>:
void * external_thread(void *arg) {
    3b80:	f3 0f 1e fa          	endbr64
    3b84:	41 55                	push   %r13
    3b86:	41 54                	push   %r12
    3b88:	55                   	push   %rbp
    3b89:	53                   	push   %rbx
    3b8a:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    3b8e:	66 0f 6f 05 aa 3d 00 00 	movdqa 0x3daa(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
void * external_thread(void *arg) {
    3b96:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3b9f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3ba4:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3ba6:	83 bf a4 00 00 00 01 	cmpl   $0x1,0xa4(%rdi)
  struct timespec req = {
    3bad:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    3bb1:	75 64                	jne    3c17 <external_thread+0x97>
    3bb3:	49 89 fd             	mov    %rdi,%r13
    3bb6:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3bbb:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    3bbe:	4c 8d 25 3f 34 00 00 	lea    0x343f(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    3bc5:	0f 1f 00             	nopl   (%rax)
    nanosleep(&req , &rem);
    3bc8:	48 89 ee             	mov    %rbp,%rsi
    3bcb:	48 89 df             	mov    %rbx,%rdi
    3bce:	e8 7d e7 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3bd3:	49 8b 85 80 01 00 00 	mov    0x180(%r13),%rax
    3bda:	48 63 10             	movslq (%rax),%rdx
    3bdd:	85 d2                	test   %edx,%edx
    3bdf:	7e 29                	jle    3c0a <external_thread+0x8a>
    3be1:	48 8b 40 08          	mov    0x8(%rax),%rax
    3be5:	48 c1 e2 04          	shl    $0x4,%rdx
    3be9:	48 01 c2             	add    %rax,%rdx
    3bec:	0f 1f 40 00          	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    3bf0:	8b 48 08             	mov    0x8(%rax),%ecx
    3bf3:	85 c9                	test   %ecx,%ecx
    3bf5:	75 0a                	jne    3c01 <external_thread+0x81>
        data->buffers->buffer[x].data = "Hello world";
    3bf7:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    3bfa:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3c01:	48 83 c0 10          	add    $0x10,%rax
    3c05:	48 39 c2             	cmp    %rax,%rdx
    3c08:	75 e6                	jne    3bf0 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    3c0a:	0f ae f0             	mfence
  while (data->running == 1) {
    3c0d:	41 83 bd a4 00 00 00 01 	cmpl   $0x1,0xa4(%r13)
    3c15:	74 b1                	je     3bc8 <external_thread+0x48>
}
    3c17:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3c1c:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3c25:	75 0d                	jne    3c34 <external_thread+0xb4>
    3c27:	48 83 c4 38          	add    $0x38,%rsp
    3c2b:	31 c0                	xor    %eax,%eax
    3c2d:	5b                   	pop    %rbx
    3c2e:	5d                   	pop    %rbp
    3c2f:	41 5c                	pop    %r12
    3c31:	41 5d                	pop    %r13
    3c33:	c3                   	ret
    3c34:	e8 f7 e6 ff ff       	call   2330 <__stack_chk_fail@plt>
    3c39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c40 <timer_thread>:
void* timer_thread(void *arg) {
    3c40:	f3 0f 1e fa          	endbr64
    3c44:	41 57                	push   %r15
    3c46:	48 8d 35 c3 33 00 00 	lea    0x33c3(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3c4d:	49 89 ff             	mov    %rdi,%r15
    3c50:	41 56                	push   %r14
    3c52:	41 55                	push   %r13
    3c54:	41 54                	push   %r12
    3c56:	55                   	push   %rbp
    3c57:	53                   	push   %rbx
    3c58:	48 83 ec 58          	sub    $0x58,%rsp
    3c5c:	8b 17                	mov    (%rdi),%edx
    3c5e:	bf 01 00 00 00       	mov    $0x1,%edi
    3c63:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3c6c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3c71:	31 c0                	xor    %eax,%eax
    3c73:	e8 d8 e7 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3c78:	66 0f 6f 05 c0 3c 00 00 	movdqa 0x3cc0(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3c80:	ba 88 13 00 00       	mov    $0x1388,%edx
    3c85:	31 c0                	xor    %eax,%eax
    3c87:	48 8d 35 94 33 00 00 	lea    0x3394(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3c8e:	bf 01 00 00 00       	mov    $0x1,%edi
    3c93:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3c98:	e8 b3 e7 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3c9d:	45 8b a7 a4 00 00 00 	mov    0xa4(%r15),%r12d
    3ca4:	45 85 e4             	test   %r12d,%r12d
    3ca7:	0f 84 af 00 00 00    	je     3d5c <timer_thread+0x11c>
  int n = 0;
    3cad:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    3cb0:	45 31 e4             	xor    %r12d,%r12d
    3cb3:	49 89 e5             	mov    %rsp,%r13
    y++;
    3cb6:	31 db                	xor    %ebx,%ebx
    3cb8:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    3cbd:	48 89 ef             	mov    %rbp,%rdi
    3cc0:	4c 89 ee             	mov    %r13,%rsi
    n++;
    3cc3:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3cc7:	e8 84 e6 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ccc:	49 63 87 88 00 00 00 	movslq 0x88(%r15),%rax
    y++;
    3cd3:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3cd8:	85 c0                	test   %eax,%eax
    3cda:	7e 4f                	jle    3d2b <timer_thread+0xeb>
    3cdc:	49 8b 8f 80 00 00 00 	mov    0x80(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3ce3:	49 c1 e4 09          	shl    $0x9,%r12
    3ce7:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3ceb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3cf0:	4c 8b 11             	mov    (%rcx),%r10
    3cf3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3cf5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3cf9:	99                   	cltd
    3cfa:	41 f7 ba a0 00 00 00 	idivl  0xa0(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3d01:	49 8b b2 98 00 00 00 	mov    0x98(%r10),%rsi
    3d08:	48 63 d2             	movslq %edx,%rdx
    3d0b:	48 c1 e2 09          	shl    $0x9,%rdx
    3d0f:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3d1a:	42 c7 84 26 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d26:	49 39 c8             	cmp    %rcx,%r8
    3d29:	75 c5                	jne    3cf0 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    3d2b:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3d2e:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
  while (data->running && n < times) {
    3d35:	41 8b 97 a4 00 00 00 	mov    0xa4(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3d3c:	48 8b 00             	mov    (%rax),%rax
    y++;
    3d3f:	39 b8 a0 00 00 00    	cmp    %edi,0xa0(%rax)
    3d45:	0f 4e fb             	cmovle %ebx,%edi
    3d48:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3d4b:	85 d2                	test   %edx,%edx
    3d4d:	74 0d                	je     3d5c <timer_thread+0x11c>
    3d4f:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3d56:	0f 85 61 ff ff ff    	jne    3cbd <timer_thread+0x7d>
    3d5c:	48 8d 3d d5 32 00 00 	lea    0x32d5(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3d63:	e8 88 e5 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d68:	49 63 97 8c 00 00 00 	movslq 0x8c(%r15),%rdx
    3d6f:	85 d2                	test   %edx,%edx
    3d71:	7e 74                	jle    3de7 <timer_thread+0x1a7>
    for (int y = 0 ; y < data->task_count ; y++) {
    3d73:	49 63 87 a0 00 00 00 	movslq 0xa0(%r15),%rax
    3d7a:	85 c0                	test   %eax,%eax
    3d7c:	7e 69                	jle    3de7 <timer_thread+0x1a7>
    3d7e:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3d82:	4d 8b 87 80 00 00 00 	mov    0x80(%r15),%r8
    3d89:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3d91:	31 ff                	xor    %edi,%edi
    3d93:	48 89 c2             	mov    %rax,%rdx
    3d96:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3d9a:	48 8b 80 98 00 00 00 	mov    0x98(%rax),%rax
    3da1:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3da5:	f6 c6 02             	test   $0x2,%dh
    3da8:	74 15                	je     3dbf <timer_thread+0x17f>
    3daa:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3db4:	48 05 00 02 00 00    	add    $0x200,%rax
    3dba:	48 39 c6             	cmp    %rax,%rsi
    3dbd:	74 1f                	je     3dde <timer_thread+0x19e>
      data->threads[x]->tasks[y].sending = 0;
    3dbf:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3dc9:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3dcf:	c7 80 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3dd9:	48 39 c6             	cmp    %rax,%rsi
    3ddc:	75 e1                	jne    3dbf <timer_thread+0x17f>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3dde:	48 83 c7 08          	add    $0x8,%rdi
    3de2:	48 39 f9             	cmp    %rdi,%rcx
    3de5:	75 af                	jne    3d96 <timer_thread+0x156>
  asm volatile ("mfence" ::: "memory");
    3de7:	0f ae f0             	mfence
  struct timespec drain = {
    3dea:	66 0f 6f 05 5e 3b 00 00 	movdqa 0x3b5e(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3df2:	48 8d 2d 64 32 00 00 	lea    0x3264(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3df9:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3dfe:	49 63 87 88 00 00 00 	movslq 0x88(%r15),%rax
    y++;
    3e05:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3e0a:	85 c0                	test   %eax,%eax
    3e0c:	7e 4c                	jle    3e5a <timer_thread+0x21a>
    3e0e:	49 8b 8f 80 00 00 00 	mov    0x80(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3e15:	4d 63 c4             	movslq %r12d,%r8
    3e18:	49 c1 e0 09          	shl    $0x9,%r8
    3e1c:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
        int next = (y + 1) % data->threads[x]->task_count;
    3e20:	48 8b 19             	mov    (%rcx),%rbx
    3e23:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3e25:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3e29:	99                   	cltd
    3e2a:	f7 bb a0 00 00 00    	idivl  0xa0(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3e30:	48 8b b3 98 00 00 00 	mov    0x98(%rbx),%rsi
    3e37:	48 63 d2             	movslq %edx,%rdx
    3e3a:	48 c1 e2 09          	shl    $0x9,%rdx
    3e3e:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3e49:	42 c7 84 06 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3e55:	4c 39 c9             	cmp    %r9,%rcx
    3e58:	75 c6                	jne    3e20 <timer_thread+0x1e0>
    asm volatile ("mfence" ::: "memory");
    3e5a:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3e5d:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    y++;
    3e64:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3e67:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3e6a:	39 ba a0 00 00 00    	cmp    %edi,0xa0(%rdx)
    3e70:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3e74:	41 8b bf 90 00 00 00 	mov    0x90(%r15),%edi
    3e7b:	85 ff                	test   %edi,%edi
    3e7d:	0f 8e c8 00 00 00    	jle    3f4b <timer_thread+0x30b>
    3e83:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    3e86:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3e8c:	0f 1f 40 00          	nopl   0x0(%rax)
    3e90:	4a 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbx
            all_empty = 0;
    3e98:	45 31 f6             	xor    %r14d,%r14d
    3e9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3ea0:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3ea4:	4c 89 f0             	mov    %r14,%rax
    3ea7:	48 c1 e0 09          	shl    $0x9,%rax
    3eab:	48 03 82 98 00 00 00 	add    0x98(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3eb2:	31 d2                	xor    %edx,%edx
    3eb4:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3ebb:	eb 15                	jmp    3ed2 <timer_thread+0x292>
    3ebd:	0f 1f 00             	nopl   (%rax)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3ec0:	4d 85 c0             	test   %r8,%r8
    3ec3:	7f 24                	jg     3ee9 <timer_thread+0x2a9>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3ec5:	83 c2 01             	add    $0x1,%edx
    3ec8:	48 05 00 01 00 00    	add    $0x100,%rax
    3ece:	39 fa                	cmp    %edi,%edx
    3ed0:	74 30                	je     3f02 <timer_thread+0x2c2>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3ed2:	48 8b 08             	mov    (%rax),%rcx
    3ed5:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    3edc:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3ee0:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3ee4:	48 85 c9             	test   %rcx,%rcx
    3ee7:	7e d7                	jle    3ec0 <timer_thread+0x280>
    3ee9:	bf 01 00 00 00       	mov    $0x1,%edi
    3eee:	48 89 ee             	mov    %rbp,%rsi
    3ef1:	31 c0                	xor    %eax,%eax
    3ef3:	e8 58 e5 ff ff       	call   2450 <__printf_chk@plt>
            break;
    3ef8:	41 8b bf 90 00 00 00 	mov    0x90(%r15),%edi
            all_empty = 0;
    3eff:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3f02:	49 83 c6 01          	add    $0x1,%r14
    3f06:	44 39 f7             	cmp    %r14d,%edi
    3f09:	7e 0d                	jle    3f18 <timer_thread+0x2d8>
    3f0b:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    3f12:	eb 8c                	jmp    3ea0 <timer_thread+0x260>
    3f14:	0f 1f 40 00          	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f18:	49 83 c5 01          	add    $0x1,%r13
    3f1c:	44 39 ef             	cmp    %r13d,%edi
    3f1f:	7e 10                	jle    3f31 <timer_thread+0x2f1>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3f21:	85 ff                	test   %edi,%edi
    3f23:	7e 0c                	jle    3f31 <timer_thread+0x2f1>
    3f25:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    3f2c:	e9 5f ff ff ff       	jmp    3e90 <timer_thread+0x250>
    if (all_empty == 1) {
    3f31:	41 83 f9 01          	cmp    $0x1,%r9d
    3f35:	74 14                	je     3f4b <timer_thread+0x30b>
      nanosleep(&drain , &drainrem);
    3f37:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3f3c:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3f41:	e8 0a e4 ff ff       	call   2350 <nanosleep@plt>
    3f46:	e9 b3 fe ff ff       	jmp    3dfe <timer_thread+0x1be>
    3f4b:	48 8d 3d 02 31 00 00 	lea    0x3102(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3f52:	e8 99 e3 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3f57:	41 8b 87 a4 00 00 00 	mov    0xa4(%r15),%eax
    3f5e:	85 c0                	test   %eax,%eax
    3f60:	0f 84 ec 00 00 00    	je     4052 <timer_thread+0x412>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3f66:	41 8b 8f 8c 00 00 00 	mov    0x8c(%r15),%ecx
    3f6d:	85 c9                	test   %ecx,%ecx
    3f6f:	7e 37                	jle    3fa8 <timer_thread+0x368>
    3f71:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    3f78:	31 db                	xor    %ebx,%ebx
    3f7a:	48 8d 2d ed 30 00 00 	lea    0x30ed(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3f81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->threads[x]->running = 0;
    3f88:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
    3f8c:	c7 82 a4 00 00 00 00 00 00 00 	movl   $0x0,0xa4(%rdx)
      if (data->threads[x]->type == IO) {
    3f96:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
    3f9a:	0f 84 df 00 00 00    	je     407f <timer_thread+0x43f>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3fa0:	48 83 c3 01          	add    $0x1,%rbx
    3fa4:	39 d9                	cmp    %ebx,%ecx
    3fa6:	7f e0                	jg     3f88 <timer_thread+0x348>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3fa8:	49 63 97 88 00 00 00 	movslq 0x88(%r15),%rdx
    3faf:	85 d2                	test   %edx,%edx
    3fb1:	0f 8e 81 00 00 00    	jle    4038 <timer_thread+0x3f8>
      for (int y = 0 ; y < data->task_count ; y++) {
    3fb7:	49 63 87 a0 00 00 00 	movslq 0xa0(%r15),%rax
    3fbe:	85 c0                	test   %eax,%eax
    3fc0:	7e 76                	jle    4038 <timer_thread+0x3f8>
    3fc2:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3fc6:	4d 8b 87 80 00 00 00 	mov    0x80(%r15),%r8
    3fcd:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3fd5:	31 c9                	xor    %ecx,%ecx
    3fd7:	48 89 c6             	mov    %rax,%rsi
    3fda:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3fe0:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3fe4:	48 8b 80 98 00 00 00 	mov    0x98(%rax),%rax
    3feb:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3fef:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3ff5:	74 19                	je     4010 <timer_thread+0x3d0>
    3ff7:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4001:	48 05 00 02 00 00    	add    $0x200,%rax
    4007:	48 39 d0             	cmp    %rdx,%rax
    400a:	74 23                	je     402f <timer_thread+0x3ef>
    400c:	0f 1f 40 00          	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4010:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    401a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4020:	c7 80 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    402a:	48 39 d0             	cmp    %rdx,%rax
    402d:	75 e1                	jne    4010 <timer_thread+0x3d0>
    for (int x = 0 ; x < data->thread_count ; x++) {
    402f:	48 83 c1 08          	add    $0x8,%rcx
    4033:	48 39 f9             	cmp    %rdi,%rcx
    4036:	75 a8                	jne    3fe0 <timer_thread+0x3a0>
    asm volatile ("mfence" ::: "memory");
    4038:	0f ae f0             	mfence
    403b:	48 8d 3d 3e 30 00 00 	lea    0x303e(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    4042:	e8 a9 e2 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    4047:	41 c7 87 a4 00 00 00 00 00 00 00 	movl   $0x0,0xa4(%r15)
    4052:	48 8d 3d 2e 30 00 00 	lea    0x302e(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    4059:	e8 92 e2 ff ff       	call   22f0 <puts@plt>
}
    405e:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    4063:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    406c:	75 53                	jne    40c1 <timer_thread+0x481>
    406e:	48 83 c4 58          	add    $0x58,%rsp
    4072:	31 c0                	xor    %eax,%eax
    4074:	5b                   	pop    %rbx
    4075:	5d                   	pop    %rbp
    4076:	41 5c                	pop    %r12
    4078:	41 5d                	pop    %r13
    407a:	41 5e                	pop    %r14
    407c:	41 5f                	pop    %r15
    407e:	c3                   	ret
    407f:	48 89 ef             	mov    %rbp,%rdi
    4082:	e8 69 e2 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4087:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    408e:	be 01 00 00 00       	mov    $0x1,%esi
    4093:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4097:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    409b:	8b b8 90 01 00 00    	mov    0x190(%rax),%edi
    40a1:	e8 5a e3 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    40a6:	41 8b 8f 8c 00 00 00 	mov    0x8c(%r15),%ecx
    40ad:	39 d9                	cmp    %ebx,%ecx
    40af:	0f 8e f3 fe ff ff    	jle    3fa8 <timer_thread+0x368>
    40b5:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    40bc:	e9 c7 fe ff ff       	jmp    3f88 <timer_thread+0x348>
}
    40c1:	e8 6a e2 ff ff       	call   2330 <__stack_chk_fail@plt>
    40c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000040d0 <strtolower>:
void strtolower(char *str) {
    40d0:	f3 0f 1e fa          	endbr64
    40d4:	55                   	push   %rbp
    40d5:	53                   	push   %rbx
    40d6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    40da:	48 0f be 1f          	movsbq (%rdi),%rbx
    40de:	84 db                	test   %bl,%bl
    40e0:	74 24                	je     4106 <strtolower+0x36>
    40e2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    40e5:	e8 26 e4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    40ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    40f0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    40f3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    40f7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    40fa:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    40fd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4102:	84 db                	test   %bl,%bl
    4104:	75 ea                	jne    40f0 <strtolower+0x20>
}
    4106:	48 83 c4 08          	add    $0x8,%rsp
    410a:	5b                   	pop    %rbx
    410b:	5d                   	pop    %rbp
    410c:	c3                   	ret
    410d:	0f 1f 00             	nopl   (%rax)

0000000000004110 <zh_malloc>:
void *zh_malloc(size_t size) {
    4110:	f3 0f 1e fa          	endbr64
    4114:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4118:	e8 f3 e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    411d:	48 85 c0             	test   %rax,%rax
    4120:	74 05                	je     4127 <zh_malloc+0x17>
}
    4122:	48 83 c4 08          	add    $0x8,%rsp
    4126:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4127:	48 8b 0d f2 5e 00 00 	mov    0x5ef2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    412e:	ba 28 00 00 00       	mov    $0x28,%edx
    4133:	be 01 00 00 00       	mov    $0x1,%esi
    4138:	48 8d 3d c9 32 00 00 	lea    0x32c9(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    413f:	e8 7c e3 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4144:	bf 01 00 00 00       	mov    $0x1,%edi
    4149:	e8 52 e3 ff ff       	call   24a0 <exit@plt>
    414e:	66 90                	xchg   %ax,%ax

0000000000004150 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4150:	f3 0f 1e fa          	endbr64
    4154:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4155:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    415a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    415d:	e8 fe e1 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4162:	48 85 c0             	test   %rax,%rax
    4165:	74 11                	je     4178 <get_filename_ext+0x28>
    4167:	48 39 c3             	cmp    %rax,%rbx
    416a:	74 0c                	je     4178 <get_filename_ext+0x28>
    return dot + 1;
    416c:	48 83 c0 01          	add    $0x1,%rax
}
    4170:	5b                   	pop    %rbx
    4171:	c3                   	ret
    4172:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4178:	48 8d 05 50 2f 00 00 	lea    0x2f50(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    417f:	5b                   	pop    %rbx
    4180:	c3                   	ret
    4181:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    418c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004190 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4190:	f3 0f 1e fa          	endbr64
    4194:	41 55                	push   %r13
    4196:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
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
    for (; *str; ++str)
    41cd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    41d2:	84 db                	test   %bl,%bl
    41d4:	74 24                	je     41fa <send_headers+0x6a>
        *str = (char)tolower(*str);
    41d6:	e8 35 e3 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    41db:	48 8b 08             	mov    (%rax),%rcx
    41de:	4c 89 e0             	mov    %r12,%rax
    41e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    41e8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    41eb:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    41ef:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    41f2:	48 0f be 18          	movsbq (%rax),%rbx
    41f6:	84 db                	test   %bl,%bl
    41f8:	75 ee                	jne    41e8 <send_headers+0x58>
    void *buf = malloc(size);
    41fa:	bf 11 00 00 00       	mov    $0x11,%edi
    41ff:	e8 0c e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4204:	48 85 c0             	test   %rax,%rax
    4207:	0f 84 7e 04 00 00    	je     468b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    420d:	66 0f 6f 05 4b 37 00 00 	movdqa 0x374b(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    4215:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4219:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    421e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4226:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    422a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    422d:	e8 de e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4232:	48 85 c0             	test   %rax,%rax
    4235:	0f 84 50 04 00 00    	je     468b <send_headers+0x4fb>
    423b:	66 0f 6f 05 2d 37 00 00 	movdqa 0x372d(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    4243:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4247:	4c 89 e7             	mov    %r12,%rdi
    424a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4254:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    425c:	0f 11 00             	movups %xmm0,(%rax)
    425f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4263:	be 2e 00 00 00       	mov    $0x2e,%esi
    4268:	e8 f3 e0 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    426d:	48 85 c0             	test   %rax,%rax
    4270:	0f 84 ea 02 00 00    	je     4560 <send_headers+0x3d0>
    4276:	4c 39 e0             	cmp    %r12,%rax
    4279:	0f 84 e1 02 00 00    	je     4560 <send_headers+0x3d0>
    return dot + 1;
    427f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4283:	48 8d 3d 13 2e 00 00 	lea    0x2e13(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    428a:	48 89 de             	mov    %rbx,%rsi
    428d:	e8 1e e1 ff ff       	call   23b0 <strcmp@plt>
    4292:	85 c0                	test   %eax,%eax
    4294:	75 20                	jne    42b6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4296:	66 0f 6f 05 e2 36 00 00 	movdqa 0x36e2(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    429e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    42a6:	66 0f 6f 05 e2 36 00 00 	movdqa 0x36e2(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    42ae:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    42b6:	48 89 de             	mov    %rbx,%rsi
    42b9:	48 8d 3d e1 2d 00 00 	lea    0x2de1(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    42c0:	e8 eb e0 ff ff       	call   23b0 <strcmp@plt>
    42c5:	85 c0                	test   %eax,%eax
    42c7:	75 20                	jne    42e9 <send_headers+0x159>
    42c9:	66 0f 6f 05 af 36 00 00 	movdqa 0x36af(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    42d1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    42d9:	66 0f 6f 05 af 36 00 00 	movdqa 0x36af(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    42e1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    42e9:	48 89 de             	mov    %rbx,%rsi
    42ec:	48 8d 3d b3 2d 00 00 	lea    0x2db3(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    42f3:	e8 b8 e0 ff ff       	call   23b0 <strcmp@plt>
    42f8:	85 c0                	test   %eax,%eax
    42fa:	0f 84 10 02 00 00    	je     4510 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4300:	48 89 de             	mov    %rbx,%rsi
    4303:	48 8d 3d a0 2d 00 00 	lea    0x2da0(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    430a:	e8 a1 e0 ff ff       	call   23b0 <strcmp@plt>
    430f:	85 c0                	test   %eax,%eax
    4311:	0f 84 a9 02 00 00    	je     45c0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4317:	48 89 de             	mov    %rbx,%rsi
    431a:	48 8d 3d 8d 2d 00 00 	lea    0x2d8d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4321:	e8 8a e0 ff ff       	call   23b0 <strcmp@plt>
    4326:	85 c0                	test   %eax,%eax
    4328:	0f 84 6a 02 00 00    	je     4598 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    432e:	48 89 de             	mov    %rbx,%rsi
    4331:	48 8d 3d b9 2d 00 00 	lea    0x2db9(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4338:	e8 73 e0 ff ff       	call   23b0 <strcmp@plt>
    433d:	85 c0                	test   %eax,%eax
    433f:	0f 84 2b 02 00 00    	je     4570 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4345:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4348:	0f 84 52 01 00 00    	je     44a0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    434e:	48 89 de             	mov    %rbx,%rsi
    4351:	48 8d 3d 5a 2d 00 00 	lea    0x2d5a(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    4358:	e8 53 e0 ff ff       	call   23b0 <strcmp@plt>
    435d:	85 c0                	test   %eax,%eax
    435f:	0f 84 ab 02 00 00    	je     4610 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4365:	48 89 de             	mov    %rbx,%rsi
    4368:	48 8d 3d 47 2d 00 00 	lea    0x2d47(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    436f:	e8 3c e0 ff ff       	call   23b0 <strcmp@plt>
    4374:	85 c0                	test   %eax,%eax
    4376:	0f 84 6c 02 00 00    	je     45e8 <send_headers+0x458>
    slen = strlen(send_buffer);
    437c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4384:	4c 89 e7             	mov    %r12,%rdi
    4387:	e8 94 df ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    438c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    438f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4392:	e8 79 e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4397:	48 85 c0             	test   %rax,%rax
    439a:	0f 84 eb 02 00 00    	je     468b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    43a0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    43a4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
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
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    43d1:	4d 89 e8             	mov    %r13,%r8
    43d4:	48 8d 0d df 2c 00 00 	lea    0x2cdf(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    43db:	4c 89 e7             	mov    %r12,%rdi
    43de:	31 c0                	xor    %eax,%eax
    43e0:	ba 00 04 00 00       	mov    $0x400,%edx
    43e5:	be 01 00 00 00       	mov    $0x1,%esi
    43ea:	e8 31 e1 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    43ef:	4c 89 e7             	mov    %r12,%rdi
    43f2:	e8 29 df ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    43f7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    43fa:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    43fd:	e8 0e e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4402:	48 85 c0             	test   %rax,%rax
    4405:	0f 84 80 02 00 00    	je     468b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    440b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
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
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    443c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4441:	bf 02 00 00 00       	mov    $0x2,%edi
    4446:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    444e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4456:	e8 b5 df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    445b:	48 85 c0             	test   %rax,%rax
    445e:	0f 84 27 02 00 00    	je     468b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4464:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    446c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4470:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4478:	66 89 10             	mov    %dx,(%rax)
}
    447b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4483:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    448c:	0f 85 20 02 00 00    	jne    46b2 <send_headers+0x522>
    4492:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4499:	5b                   	pop    %rbx
    449a:	5d                   	pop    %rbp
    449b:	41 5c                	pop    %r12
    449d:	41 5d                	pop    %r13
    449f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    44a0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    44a4:	0f 85 a4 fe ff ff    	jne    434e <send_headers+0x1be>
    44aa:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    44ae:	0f 85 9a fe ff ff    	jne    434e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    44b4:	66 0f 6f 05 24 35 00 00 	movdqa 0x3524(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    44bc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    44c6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44ce:	66 0f 6f 05 1a 35 00 00 	movdqa 0x351a(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    44d6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    44de:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    44e6:	e9 63 fe ff ff       	jmp    434e <send_headers+0x1be>
    44eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    44f0:	89 da                	mov    %ebx,%edx
    44f2:	48 89 c7             	mov    %rax,%rdi
    44f5:	4c 89 e6             	mov    %r12,%rsi
    44f8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    44fd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4502:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4505:	c1 e9 03             	shr    $0x3,%ecx
    4508:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    450b:	e9 c1 fe ff ff       	jmp    43d1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4510:	66 0f 6f 05 68 34 00 00 	movdqa 0x3468(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4518:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4520:	66 0f 6f 05 78 34 00 00 	movdqa 0x3478(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4528:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4530:	e9 cb fd ff ff       	jmp    4300 <send_headers+0x170>
    4535:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
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
        return "";
    4560:	48 8d 1d 68 2b 00 00 	lea    0x2b68(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4567:	e9 94 fd ff ff       	jmp    4300 <send_headers+0x170>
    456c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
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
  return __builtin___memcpy_chk (__dest, __src, __len,
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
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    468b:	48 8b 0d 8e 59 00 00 	mov    0x598e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4692:	ba 28 00 00 00       	mov    $0x28,%edx
    4697:	be 01 00 00 00       	mov    $0x1,%esi
    469c:	48 8d 3d 65 2d 00 00 	lea    0x2d65(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    46a3:	e8 18 de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    46a8:	bf 01 00 00 00       	mov    $0x1,%edi
    46ad:	e8 ee dd ff ff       	call   24a0 <exit@plt>
}
    46b2:	e8 79 dc ff ff       	call   2330 <__stack_chk_fail@plt>
    46b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000046c0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    46c0:	f3 0f 1e fa          	endbr64
    46c4:	41 55                	push   %r13
    46c6:	49 89 d5             	mov    %rdx,%r13
    46c9:	41 54                	push   %r12
    46cb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    46ce:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    46d1:	55                   	push   %rbp
    46d2:	53                   	push   %rbx
    46d3:	48 89 f3             	mov    %rsi,%rbx
    46d6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    46da:	e8 31 dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    46df:	48 85 c0             	test   %rax,%rax
    46e2:	74 6b                	je     474f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    46e4:	4c 89 e7             	mov    %r12,%rdi
    46e7:	48 89 c5             	mov    %rax,%rbp
    46ea:	31 f6                	xor    %esi,%esi
    46ec:	31 c0                	xor    %eax,%eax
    46ee:	e8 8d dd ff ff       	call   2480 <open@plt>
    46f3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    46f6:	85 c0                	test   %eax,%eax
    46f8:	0f 88 58 de ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    46fe:	48 89 da             	mov    %rbx,%rdx
    4701:	48 89 ee             	mov    %rbp,%rsi
    4704:	89 c7                	mov    %eax,%edi
    4706:	e8 85 dc ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    470b:	48 98                	cltq
    470d:	48 39 d8             	cmp    %rbx,%rax
    4710:	7c 1e                	jl     4730 <copy_file_contents+0x70>
    close(fd);
    4712:	44 89 e7             	mov    %r12d,%edi
    4715:	e8 56 dc ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    471a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    471e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4722:	48 83 c4 08          	add    $0x8,%rsp
    4726:	5b                   	pop    %rbx
    4727:	5d                   	pop    %rbp
    4728:	41 5c                	pop    %r12
    472a:	41 5d                	pop    %r13
    472c:	c3                   	ret
    472d:	0f 1f 00             	nopl   (%rax)
    4730:	48 8b 0d e9 58 00 00 	mov    0x58e9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4737:	ba 1a 00 00 00       	mov    $0x1a,%edx
    473c:	be 01 00 00 00       	mov    $0x1,%esi
    4741:	48 8d 3d 88 29 00 00 	lea    0x2988(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    4748:	e8 73 dd ff ff       	call   24c0 <fwrite@plt>
    474d:	eb c3                	jmp    4712 <copy_file_contents+0x52>
    474f:	48 8b 0d ca 58 00 00 	mov    0x58ca(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4756:	ba 28 00 00 00       	mov    $0x28,%edx
    475b:	be 01 00 00 00       	mov    $0x1,%esi
    4760:	48 8d 3d a1 2c 00 00 	lea    0x2ca1(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4767:	e8 54 dd ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    476c:	bf 01 00 00 00       	mov    $0x1,%edi
    4771:	e8 2a dd ff ff       	call   24a0 <exit@plt>
    4776:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004780 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4780:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
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
    47a9:	0f 82 b3 dd ff ff    	jb     2562 <add_write_request.cold>
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
    4851:	0f 82 1b dd ff ff    	jb     2572 <add_read_request.cold>
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
    498a:	0f 82 ec db ff ff    	jb     257c <_send_static_string_content.cold>
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
    4a16:	48 8d 3d eb 29 00 00 	lea    0x29eb(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
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
    4c31:	e8 5a f5 ff ff       	call   4190 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4c36:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4c3b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4c3f:	4c 89 f7             	mov    %r14,%rdi
    4c42:	e8 79 fa ff ff       	call   46c0 <copy_file_contents>
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
    4c88:	48 8d 3d 79 27 00 00 	lea    0x2779(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
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
    4eae:	0f 82 d8 d6 ff ff    	jb     258c <add_accept_request.cold>
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
    4f4b:	48 8b 87 88 01 00 00 	mov    0x188(%rdi),%rax
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
    5024:	48 8b bd 88 01 00 00 	mov    0x188(%rbp),%rdi
    502b:	31 f6                	xor    %esi,%esi
    502d:	e8 ae d4 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    5032:	31 d2                	xor    %edx,%edx
    5034:	be 01 00 00 00       	mov    $0x1,%esi
    5039:	bf 02 00 00 00       	mov    $0x2,%edi
    503e:	e8 ed d4 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    5043:	83 f8 ff             	cmp    $0xffffffff,%eax
    5046:	0f 84 82 d5 ff ff    	je     25ce <io_thread.cold+0x38>
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
    5075:	0f 88 27 d5 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    507b:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    5080:	ba 10 00 00 00       	mov    $0x10,%edx
    5085:	44 89 e7             	mov    %r12d,%edi
    5088:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5091:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5099:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    50a1:	e8 ba d3 ff ff       	call   2460 <bind@plt>
    50a6:	85 c0                	test   %eax,%eax
    50a8:	0f 88 2c d5 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    50ae:	be 0a 00 00 00       	mov    $0xa,%esi
    50b3:	44 89 e7             	mov    %r12d,%edi
    50b6:	e8 65 d3 ff ff       	call   2420 <listen@plt>
    50bb:	85 c0                	test   %eax,%eax
    50bd:	0f 88 eb d4 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    50c3:	ba db 18 00 00       	mov    $0x18db,%edx
    50c8:	48 8d 35 ad 20 00 00 	lea    0x20ad(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    50cf:	bf 01 00 00 00       	mov    $0x1,%edi
    50d4:	31 c0                	xor    %eax,%eax
    50d6:	e8 75 d3 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    50db:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    50e0:	48 89 d9             	mov    %rbx,%rcx
    50e3:	44 89 e7             	mov    %r12d,%edi
    50e6:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    50eb:	48 89 c6             	mov    %rax,%rsi
    50ee:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    50f3:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    50f8:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5100:	e8 7b fd ff ff       	call   4e80 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5105:	bf 01 00 00 00       	mov    $0x1,%edi
    510a:	be 10 00 00 00       	mov    $0x10,%esi
    510f:	e8 8c d2 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    5114:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5119:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    511c:	e8 ef d2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    5121:	48 85 c0             	test   %rax,%rax
    5124:	0f 84 c8 04 00 00    	je     55f2 <io_thread+0x6d2>
  iov->iov_base = zh_malloc(10);
    512a:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    512e:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5135:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    513c:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5144:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5147:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    514c:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    514e:	f6 c1 02             	test   $0x2,%cl
    5151:	0f 85 29 04 00 00    	jne    5580 <io_thread+0x660>
	if (next - head <= sq->ring_entries) {
    5157:	89 d0                	mov    %edx,%eax
    5159:	29 f0                	sub    %esi,%eax
    515b:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5162:	0f 82 5c d4 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5168:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    516b:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	sqe->addr3 = 0;
    5172:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5176:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5179:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5180:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    5183:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    518a:	48 8d b5 90 01 00 00 	lea    0x190(%rbp),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5191:	8b 95 90 01 00 00    	mov    0x190(%rbp),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5197:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5199:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    519e:	48 c1 e0 06          	shl    $0x6,%rax
    51a2:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    51aa:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    51b0:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    51b3:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    51bb:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    51bf:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    51c7:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    51cf:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    51d3:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    51d7:	e8 64 d1 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    51dc:	83 bd a4 00 00 00 01 	cmpl   $0x1,0xa4(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    51e3:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    51e8:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    51f0:	0f 85 de 01 00 00    	jne    53d4 <io_thread+0x4b4>
    51f6:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    51fb:	4d 89 ce             	mov    %r9,%r14
    51fe:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5203:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
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
    525a:	0f 85 b0 01 00 00    	jne    5410 <io_thread+0x4f0>
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
    52be:	0f 88 d2 d2 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    52c4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    52c7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    52cb:	85 c0                	test   %eax,%eax
    52cd:	0f 88 e5 02 00 00    	js     55b8 <io_thread+0x698>
      switch (req->event_type) {
    52d3:	41 83 f8 01          	cmp    $0x1,%r8d
    52d7:	0f 84 83 01 00 00    	je     5460 <io_thread+0x540>
    52dd:	41 83 f8 02          	cmp    $0x2,%r8d
    52e1:	0f 84 a9 01 00 00    	je     5490 <io_thread+0x570>
    52e7:	45 85 c0             	test   %r8d,%r8d
    52ea:	0f 85 58 01 00 00    	jne    5448 <io_thread+0x528>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    52f0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    52f5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    52fa:	48 89 d9             	mov    %rbx,%rcx
    52fd:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5301:	e8 7a fb ff ff       	call   4e80 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5306:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    530b:	48 89 de             	mov    %rbx,%rsi
    530e:	8b 78 08             	mov    0x8(%rax),%edi
    5311:	e8 0a f5 ff ff       	call   4820 <add_read_request>
              free(req);
    5316:	4c 89 e7             	mov    %r12,%rdi
    5319:	e8 a2 cf ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    531e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5323:	48 85 c0             	test   %rax,%rax
    5326:	0f 85 1c 01 00 00    	jne    5448 <io_thread+0x528>
	unsigned int head, next = sq->sqe_tail + 1;
    532c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5333:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    533a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    533d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5342:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5344:	f6 c1 02             	test   $0x2,%cl
    5347:	74 00                	je     5349 <io_thread+0x429>
	if (next - head <= sq->ring_entries) {
    5349:	89 d0                	mov    %edx,%eax
    534b:	29 f0                	sub    %esi,%eax
    534d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5354:	0f 82 60 d2 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    535a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    535d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5362:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5366:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5369:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5370:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5373:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    537a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5381:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5383:	8b 95 90 01 00 00    	mov    0x190(%rbp),%edx
    5389:	48 c1 e0 06          	shl    $0x6,%rax
    538d:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5395:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    539b:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    539e:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    53a6:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    53aa:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    53b2:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    53ba:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    53be:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    53c2:	e8 79 cf ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    53c7:	83 bd a4 00 00 00 01 	cmpl   $0x1,0xa4(%rbp)
    53ce:	0f 84 34 fe ff ff    	je     5208 <io_thread+0x2e8>
    53d4:	48 8d 3d 16 1e 00 00 	lea    0x1e16(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    53db:	e8 10 cf ff ff       	call   22f0 <puts@plt>
}
    53e0:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    53e8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    53f1:	0f 85 22 02 00 00    	jne    5619 <io_thread+0x6f9>
    53f7:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    53fe:	31 c0                	xor    %eax,%eax
    5400:	5b                   	pop    %rbx
    5401:	5d                   	pop    %rbp
    5402:	41 5c                	pop    %r12
    5404:	41 5d                	pop    %r13
    5406:	41 5e                	pop    %r14
    5408:	41 5f                	pop    %r15
    540a:	c3                   	ret
    540b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    5410:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5415:	48 85 c0             	test   %rax,%rax
    5418:	0f 84 62 fe ff ff    	je     5280 <io_thread+0x360>
      if (cqe->user_data == 1) {
    541e:	48 83 38 01          	cmpq   $0x1,(%rax)
    5422:	0f 84 70 01 00 00    	je     5598 <io_thread+0x678>
    5428:	48 8d 3d 89 1d 00 00 	lea    0x1d89(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    542f:	e8 bc ce ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5434:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5439:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    543c:	e9 83 fe ff ff       	jmp    52c4 <io_thread+0x3a4>
    5441:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5448:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5450:	8b 02                	mov    (%rdx),%eax
    5452:	83 c0 01             	add    $0x1,%eax
    5455:	89 02                	mov    %eax,(%rdx)
}
    5457:	e9 d0 fe ff ff       	jmp    532c <io_thread+0x40c>
    545c:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5460:	85 c0                	test   %eax,%eax
    5462:	75 7c                	jne    54e0 <io_thread+0x5c0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5464:	48 8b 0d b5 4b 00 00 	mov    0x4bb5(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    546b:	ba 0f 00 00 00       	mov    $0xf,%edx
    5470:	be 01 00 00 00       	mov    $0x1,%esi
    5475:	48 8d 3d 65 1d 00 00 	lea    0x1d65(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    547c:	e8 3f d0 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5481:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5486:	e9 98 fe ff ff       	jmp    5323 <io_thread+0x403>
    548b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5490:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5495:	45 31 ff             	xor    %r15d,%r15d
    5498:	85 c0                	test   %eax,%eax
    549a:	7e 20                	jle    54bc <io_thread+0x59c>
    549c:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    54a0:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    54a3:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    54a7:	48 c1 e0 04          	shl    $0x4,%rax
    54ab:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    54b0:	e8 0b ce ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    54b5:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    54ba:	7f e4                	jg     54a0 <io_thread+0x580>
              close(req->client_socket);
    54bc:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    54c1:	e8 aa ce ff ff       	call   2370 <close@plt>
              free(req);
    54c6:	4c 89 e7             	mov    %r12,%rdi
    54c9:	e8 f2 cd ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    54ce:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    54d3:	e9 4b fe ff ff       	jmp    5323 <io_thread+0x403>
    54d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
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
    5541:	e9 dd fd ff ff       	jmp    5323 <io_thread+0x403>
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
    5580:	e9 d2 fb ff ff       	jmp    5157 <io_thread+0x237>
    5585:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5588:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    558d:	e9 8c fe ff ff       	jmp    541e <io_thread+0x4fe>
    5592:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5598:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    55a0:	48 8d 3d fd 1b 00 00 	lea    0x1bfd(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    55a7:	8b 02                	mov    (%rdx),%eax
    55a9:	83 c0 01             	add    $0x1,%eax
    55ac:	89 02                	mov    %eax,(%rdx)
    55ae:	e8 3d cd ff ff       	call   22f0 <puts@plt>
    55b3:	e9 1c fe ff ff       	jmp    53d4 <io_thread+0x4b4>
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
    55da:	48 8d 15 57 1e 00 00 	lea    0x1e57(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    55e1:	31 c0                	xor    %eax,%eax
    55e3:	e8 e8 ce ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    55e8:	bf 01 00 00 00       	mov    $0x1,%edi
    55ed:	e8 ae ce ff ff       	call   24a0 <exit@plt>
    55f2:	48 8b 0d 27 4a 00 00 	mov    0x4a27(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    55f9:	ba 28 00 00 00       	mov    $0x28,%edx
    55fe:	be 01 00 00 00       	mov    $0x1,%esi
    5603:	48 8d 3d fe 1d 00 00 	lea    0x1dfe(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    560a:	e8 b1 ce ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    560f:	bf 01 00 00 00       	mov    $0x1,%edi
    5614:	e8 87 ce ff ff       	call   24a0 <exit@plt>
}
    5619:	e8 12 cd ff ff       	call   2330 <__stack_chk_fail@plt>
    561e:	66 90                	xchg   %ax,%ax

0000000000005620 <sendm>:
int sendm(struct BarrierTask *data) {
    5620:	f3 0f 1e fa          	endbr64
    5624:	41 57                	push   %r15
    5626:	41 56                	push   %r14
    5628:	41 55                	push   %r13
    562a:	41 54                	push   %r12
    562c:	55                   	push   %rbp
    562d:	53                   	push   %rbx
    562e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5632:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
    5639:	0f 85 a9 01 00 00    	jne    57e8 <sendm+0x1c8>
    563f:	48 8d b7 80 01 00 00 	lea    0x180(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5646:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    564c:	48 89 fa             	mov    %rdi,%rdx
    564f:	31 c9                	xor    %ecx,%ecx
    5651:	48 89 34 24          	mov    %rsi,(%rsp)
    5655:	48 8d b7 88 01 00 00 	lea    0x188(%rdi),%rsi
    565c:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5661:	85 c0                	test   %eax,%eax
    5663:	0f 8e e1 00 00 00    	jle    574a <sendm+0x12a>
    5669:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5670:	39 8a 30 01 00 00    	cmp    %ecx,0x130(%rdx)
    5676:	0f 84 c2 00 00 00    	je     573e <sendm+0x11e>
        struct Data *them = data->mailboxes[n].higher;
    567c:	49 89 ca             	mov    %rcx,%r10
    567f:	49 c1 e2 08          	shl    $0x8,%r10
    5683:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
    568a:	4d 8b 9a 80 00 00 00 	mov    0x80(%r10),%r11
        for (; them->messages_count < min;) {
    5691:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    5695:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    5699:	4c 39 cb             	cmp    %r9,%rbx
    569c:	0f 8d 93 00 00 00    	jge    5735 <sendm+0x115>
    56a2:	4c 89 cf             	mov    %r9,%rdi
    56a5:	48 8b aa 08 01 00 00 	mov    0x108(%rdx),%rbp
    56ac:	4d 8b b2 88 00 00 00 	mov    0x88(%r10),%r14
    56b3:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    56b6:	49 8b 33             	mov    (%r11),%rsi
    56b9:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    56bd:	48 83 f8 02          	cmp    $0x2,%rax
    56c1:	0f 86 09 01 00 00    	jbe    57d0 <sendm+0x1b0>
    56c7:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    56cf:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    56d7:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    56db:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    56df:	4c 39 2c 24          	cmp    %r13,(%rsp)
    56e3:	73 7b                	jae    5760 <sendm+0x140>
    56e5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    56ea:	4d 39 fc             	cmp    %r15,%r12
    56ed:	73 71                	jae    5760 <sendm+0x140>
    56ef:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    56f3:	49 01 f0             	add    %rsi,%r8
    56f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5700:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    5707:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    570b:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    570f:	49 39 d8             	cmp    %rbx,%r8
    5712:	75 ec                	jne    5700 <sendm+0xe0>
    5714:	0f 1f 40 00          	nopl   0x0(%rax)
    5718:	48 01 fd             	add    %rdi,%rbp
    571b:	4c 01 f7             	add    %r14,%rdi
    571e:	48 89 aa 08 01 00 00 	mov    %rbp,0x108(%rdx)
    5725:	49 89 ba 88 00 00 00 	mov    %rdi,0x88(%r10)
    572c:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    5730:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5735:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5738:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    573e:	48 83 c1 01          	add    $0x1,%rcx
    5742:	39 c8                	cmp    %ecx,%eax
    5744:	0f 8f 26 ff ff ff    	jg     5670 <sendm+0x50>
}
    574a:	48 83 c4 18          	add    $0x18,%rsp
    574e:	31 c0                	xor    %eax,%eax
    5750:	5b                   	pop    %rbx
    5751:	5d                   	pop    %rbp
    5752:	41 5c                	pop    %r12
    5754:	41 5d                	pop    %r13
    5756:	41 5e                	pop    %r14
    5758:	41 5f                	pop    %r15
    575a:	c3                   	ret
    575b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5760:	49 89 fd             	mov    %rdi,%r13
    5763:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    576a:	4d 89 e0             	mov    %r12,%r8
    576d:	49 d1 ed             	shr    %r13
    5770:	49 c1 e5 04          	shl    $0x4,%r13
    5774:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5779:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    577d:	41 83 e5 10          	and    $0x10,%r13d
    5781:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5785:	74 11                	je     5798 <sendm+0x178>
          them->messages[them->messages_count++] = data->message; 
    5787:	49 83 c0 10          	add    $0x10,%r8
    578b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5790:	4d 39 f8             	cmp    %r15,%r8
    5793:	74 15                	je     57aa <sendm+0x18a>
    5795:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5798:	41 0f 11 00          	movups %xmm0,(%r8)
    579c:	49 83 c0 20          	add    $0x20,%r8
    57a0:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    57a5:	4d 39 f8             	cmp    %r15,%r8
    57a8:	75 ee                	jne    5798 <sendm+0x178>
    57aa:	49 89 f8             	mov    %rdi,%r8
    57ad:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    57b1:	49 01 d8             	add    %rbx,%r8
    57b4:	40 f6 c7 01          	test   $0x1,%dil
    57b8:	0f 84 5a ff ff ff    	je     5718 <sendm+0xf8>
          them->messages[them->messages_count++] = data->message; 
    57be:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    57c5:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    57c9:	e9 4a ff ff ff       	jmp    5718 <sendm+0xf8>
    57ce:	66 90                	xchg   %ax,%ax
    57d0:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    57d8:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    57e0:	e9 0a ff ff ff       	jmp    56ef <sendm+0xcf>
    57e5:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    57e8:	48 8d 3d 15 1a 00 00 	lea    0x1a15(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    57ef:	e8 fc ca ff ff       	call   22f0 <puts@plt>
    57f4:	e9 51 ff ff ff       	jmp    574a <sendm+0x12a>
    57f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005800 <receive>:
int receive(struct BarrierTask *data) {
    5800:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5804:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    580a:	85 c0                	test   %eax,%eax
    580c:	0f 8e f1 00 00 00    	jle    5903 <receive+0x103>
int receive(struct BarrierTask *data) {
    5812:	41 54                	push   %r12
    5814:	48 89 fa             	mov    %rdi,%rdx
    5817:	55                   	push   %rbp
    5818:	31 ed                	xor    %ebp,%ebp
    581a:	53                   	push   %rbx
    581b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5820:	48 89 ee             	mov    %rbp,%rsi
    5823:	48 c1 e6 08          	shl    $0x8,%rsi
    5827:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    582e:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5831:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    5836:	48 85 ff             	test   %rdi,%rdi
    5839:	0f 8e a1 00 00 00    	jle    58e0 <receive+0xe0>
      data->sends++;
    583f:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    5846:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    584a:	4c 63 1a             	movslq (%rdx),%r11
    584d:	49 89 c9             	mov    %rcx,%r9
    5850:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5854:	49 f7 d9             	neg    %r9
    5857:	48 01 c7             	add    %rax,%rdi
    585a:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    585e:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    5865:	4c 8b 86 90 00 00 00 	mov    0x90(%rsi),%r8
      data->n++;
    586c:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    586f:	49 29 c8             	sub    %rcx,%r8
    5872:	eb 0d                	jmp    5881 <receive+0x81>
    5874:	0f 1f 40 00          	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5878:	48 83 c0 01          	add    $0x1,%rax
    587c:	48 39 c7             	cmp    %rax,%rdi
    587f:	74 5f                	je     58e0 <receive+0xe0>
      data->n++;
    5881:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    5885:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
      data->n++;
    588c:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5893:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5897:	48 89 8e 90 00 00 00 	mov    %rcx,0x90(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    589e:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    58a3:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    58a7:	75 cf                	jne    5878 <receive+0x78>
    58a9:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    58b0:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    58b4:	75 c2                	jne    5878 <receive+0x78>
    58b6:	bf 01 00 00 00       	mov    $0x1,%edi
    58bb:	b9 01 00 00 00       	mov    $0x1,%ecx
    58c0:	ba 01 00 00 00       	mov    $0x1,%edx
    58c5:	31 c0                	xor    %eax,%eax
    58c7:	48 8d 35 92 1b 00 00 	lea    0x1b92(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    58ce:	e8 7d cb ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    58d3:	bf 01 00 00 00       	mov    $0x1,%edi
    58d8:	e8 c3 cb ff ff       	call   24a0 <exit@plt>
    58dd:	0f 1f 00             	nopl   (%rax)
    me->messages_count = 0;
    58e0:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    58e9:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    58ec:	48 83 c5 01          	add    $0x1,%rbp
    58f0:	39 aa 34 01 00 00    	cmp    %ebp,0x134(%rdx)
    58f6:	0f 8f 24 ff ff ff    	jg     5820 <receive+0x20>
}
    58fc:	5b                   	pop    %rbx
    58fd:	31 c0                	xor    %eax,%eax
    58ff:	5d                   	pop    %rbp
    5900:	41 5c                	pop    %r12
    5902:	c3                   	ret
    5903:	31 c0                	xor    %eax,%eax
    5905:	c3                   	ret
    5906:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005910 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5910:	f3 0f 1e fa          	endbr64
    5914:	41 57                	push   %r15
    5916:	41 56                	push   %r14
    5918:	41 55                	push   %r13
    591a:	41 54                	push   %r12
    591c:	55                   	push   %rbp
    591d:	53                   	push   %rbx
    591e:	48 89 fb             	mov    %rdi,%rbx
    5921:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    5925:	8b 07                	mov    (%rdi),%eax
    5927:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    592d:	0f 84 3d 01 00 00    	je     5a70 <barriered_work+0x160>
    receive(data);
    5933:	e8 c8 fe ff ff       	call   5800 <receive>
    while (data->scheduled == 1) {
    5938:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    593f:	75 1b                	jne    595c <barriered_work+0x4c>
    5941:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    5948:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    5950:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5953:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    595a:	74 ec                	je     5948 <barriered_work+0x38>
  if (data->sending == 1) {
    595c:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    5963:	0f 85 8d 02 00 00    	jne    5bf6 <barriered_work+0x2e6>
      for (int n = 0 ; n < data->thread_count; n++) {
    5969:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    596f:	85 c0                	test   %eax,%eax
    5971:	0f 8e 8b 02 00 00    	jle    5c02 <barriered_work+0x2f2>
    5977:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    597e:	31 d2                	xor    %edx,%edx
    5980:	48 89 0c 24          	mov    %rcx,(%rsp)
    5984:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    598b:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    5990:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5996:	0f 84 c2 00 00 00    	je     5a5e <barriered_work+0x14e>
        struct Data *them = data->mailboxes[n].higher;
    599c:	49 89 d1             	mov    %rdx,%r9
    599f:	49 c1 e1 08          	shl    $0x8,%r9
    59a3:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    59aa:	4d 8b 91 80 00 00 00 	mov    0x80(%r9),%r10
        for (; them->messages_count < min;) {
    59b1:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    59b5:	4d 63 42 10          	movslq 0x10(%r10),%r8
    59b9:	4d 39 c3             	cmp    %r8,%r11
    59bc:	0f 8d 93 00 00 00    	jge    5a55 <barriered_work+0x145>
    59c2:	4c 89 c6             	mov    %r8,%rsi
    59c5:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    59cc:	4d 8b b1 88 00 00 00 	mov    0x88(%r9),%r14
    59d3:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    59d6:	49 8b 0a             	mov    (%r10),%rcx
    59d9:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    59dd:	48 83 f8 02          	cmp    $0x2,%rax
    59e1:	0f 86 a9 02 00 00    	jbe    5c90 <barriered_work+0x380>
    59e7:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    59ef:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    59f7:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    59fb:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    59ff:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5a03:	0f 83 17 02 00 00    	jae    5c20 <barriered_work+0x310>
    5a09:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5a0e:	4d 39 fc             	cmp    %r15,%r12
    5a11:	0f 83 09 02 00 00    	jae    5c20 <barriered_work+0x310>
    5a17:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5a1b:	48 01 cf             	add    %rcx,%rdi
    5a1e:	66 90                	xchg   %ax,%ax
    5a20:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5a27:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5a2b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5a2f:	49 39 fb             	cmp    %rdi,%r11
    5a32:	75 ec                	jne    5a20 <barriered_work+0x110>
    5a34:	0f 1f 40 00          	nopl   0x0(%rax)
    5a38:	48 01 f5             	add    %rsi,%rbp
    5a3b:	4c 01 f6             	add    %r14,%rsi
    5a3e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5a45:	49 89 b1 88 00 00 00 	mov    %rsi,0x88(%r9)
    5a4c:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5a50:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5a55:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5a58:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5a5e:	48 83 c2 01          	add    $0x1,%rdx
    5a62:	39 d0                	cmp    %edx,%eax
    5a64:	0f 8f 26 ff ff ff    	jg     5990 <barriered_work+0x80>
    5a6a:	e9 93 01 00 00       	jmp    5c02 <barriered_work+0x2f2>
    5a6f:	90                   	nop
      receive(data);
    5a70:	e8 8b fd ff ff       	call   5800 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    5a75:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    5a7c:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    5a7e:	45 85 c9             	test   %r9d,%r9d
    5a81:	0f 8e 91 00 00 00    	jle    5b18 <barriered_work+0x208>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5a87:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    5a8e:	4c 63 d8             	movslq %eax,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    5a91:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5a94:	49 c1 e3 09          	shl    $0x9,%r11
    5a98:	4c 8b 92 80 00 00 00 	mov    0x80(%rdx),%r10
              int next_task = abs((t + 1) % (data->thread_count));
    5a9f:	99                   	cltd
    5aa0:	41 f7 f9             	idiv   %r9d
    5aa3:	4c 89 d7             	mov    %r10,%rdi
    5aa6:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
    5aaa:	89 d0                	mov    %edx,%eax
    5aac:	f7 d8                	neg    %eax
    5aae:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5ab1:	45 31 c0             	xor    %r8d,%r8d
              int next_task = abs((t + 1) % (data->thread_count));
    5ab4:	48 63 ea             	movslq %edx,%rbp
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5ab7:	48 c1 e5 09          	shl    $0x9,%rbp
    5abb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    5ac0:	31 c0                	xor    %eax,%eax
    5ac2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5ac8:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    5acc:	48 8b 92 98 00 00 00 	mov    0x98(%rdx),%rdx
    5ad3:	48 8b 8c 2a 68 01 00 00 	mov    0x168(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5adb:	48 8b 17             	mov    (%rdi),%rdx
    5ade:	48 8b b2 98 00 00 00 	mov    0x98(%rdx),%rsi
    5ae5:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5ae8:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5aec:	48 c1 e2 08          	shl    $0x8,%rdx
    5af0:	4a 03 94 1e 68 01 00 00 	add    0x168(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5af8:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    5aff:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    5b03:	49 39 c1             	cmp    %rax,%r9
    5b06:	75 c0                	jne    5ac8 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    5b08:	48 83 c7 08          	add    $0x8,%rdi
    5b0c:	49 81 c0 00 01 00 00 	add    $0x100,%r8
    5b13:	49 39 fc             	cmp    %rdi,%r12
    5b16:	75 a8                	jne    5ac0 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    5b18:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5b1b:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5b22:	31 ff                	xor    %edi,%edi
    5b24:	48 c1 e6 05          	shl    $0x5,%rsi
    5b28:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5b2f:	e8 dc c7 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5b34:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5b3b:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5b42:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
    5b49:	8b 4a 10             	mov    0x10(%rdx),%ecx
    5b4c:	8d 69 01             	lea    0x1(%rcx),%ebp
    5b4f:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5b52:	75 5d                	jne    5bb1 <barriered_work+0x2a1>
    5b54:	0f 1f 40 00          	nopl   0x0(%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5b58:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    5b5f:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    5b66:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    5b69:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5b71:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5b75:	48 c1 e7 09          	shl    $0x9,%rdi
    5b79:	48 03 b8 98 00 00 00 	add    0x98(%rax),%rdi
    5b80:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    5b86:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5b89:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    5b90:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5b97:	74 bf                	je     5b58 <barriered_work+0x248>
    if (modcount != data->thread->protected_state->modcount) {
    5b99:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
    5ba0:	3b 68 10             	cmp    0x10(%rax),%ebp
    5ba3:	74 0c                	je     5bb1 <barriered_work+0x2a1>
    5ba5:	48 8d 3d 64 16 00 00 	lea    0x1664(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    5bac:	e8 3f c7 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5bb1:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5bb8:	31 ff                	xor    %edi,%edi
    5bba:	48 c1 e6 05          	shl    $0x5,%rsi
    5bbe:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5bc5:	48 83 c6 10          	add    $0x10,%rsi
    5bc9:	e8 42 c7 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5bce:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    5bd5:	48 83 c0 01          	add    $0x1,%rax
    5bd9:	48 99                	cqto
    5bdb:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    5be2:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5be9:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    5bf0:	0f 84 af 00 00 00    	je     5ca5 <barriered_work+0x395>
    5bf6:	48 8d 3d 07 16 00 00 	lea    0x1607(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5bfd:	e8 ee c6 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5c02:	0f ae f8             	sfence
}
    5c05:	48 83 c4 18          	add    $0x18,%rsp
    5c09:	31 c0                	xor    %eax,%eax
    5c0b:	5b                   	pop    %rbx
    5c0c:	5d                   	pop    %rbp
    5c0d:	41 5c                	pop    %r12
    5c0f:	41 5d                	pop    %r13
    5c11:	41 5e                	pop    %r14
    5c13:	41 5f                	pop    %r15
    5c15:	c3                   	ret
    5c16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5c20:	49 89 f5             	mov    %rsi,%r13
    5c23:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5c2a:	4c 89 e7             	mov    %r12,%rdi
    5c2d:	49 d1 ed             	shr    %r13
    5c30:	49 c1 e5 04          	shl    $0x4,%r13
    5c34:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5c39:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5c3d:	41 83 e5 10          	and    $0x10,%r13d
    5c41:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5c45:	74 11                	je     5c58 <barriered_work+0x348>
          them->messages[them->messages_count++] = data->message; 
    5c47:	48 83 c7 10          	add    $0x10,%rdi
    5c4b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5c50:	49 39 ff             	cmp    %rdi,%r15
    5c53:	74 13                	je     5c68 <barriered_work+0x358>
    5c55:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5c58:	0f 11 07             	movups %xmm0,(%rdi)
    5c5b:	48 83 c7 20          	add    $0x20,%rdi
    5c5f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5c63:	49 39 ff             	cmp    %rdi,%r15
    5c66:	75 f0                	jne    5c58 <barriered_work+0x348>
    5c68:	48 89 f7             	mov    %rsi,%rdi
    5c6b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5c6f:	4c 01 df             	add    %r11,%rdi
    5c72:	40 f6 c6 01          	test   $0x1,%sil
    5c76:	0f 84 bc fd ff ff    	je     5a38 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    5c7c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5c83:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5c87:	e9 ac fd ff ff       	jmp    5a38 <barriered_work+0x128>
    5c8c:	0f 1f 40 00          	nopl   0x0(%rax)
    5c90:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5c98:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5ca0:	e9 72 fd ff ff       	jmp    5a17 <barriered_work+0x107>
      for (int n = 0 ; n < data->thread_count; n++) {
    5ca5:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    5cac:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5cb2:	31 d2                	xor    %edx,%edx
    5cb4:	48 89 0c 24          	mov    %rcx,(%rsp)
    5cb8:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    5cbf:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5cc4:	85 c0                	test   %eax,%eax
    5cc6:	0f 8e 36 ff ff ff    	jle    5c02 <barriered_work+0x2f2>
    5ccc:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5cd0:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5cd6:	0f 84 c2 00 00 00    	je     5d9e <barriered_work+0x48e>
        struct Data *them = data->mailboxes[n].higher;
    5cdc:	49 89 d1             	mov    %rdx,%r9
    5cdf:	49 c1 e1 08          	shl    $0x8,%r9
    5ce3:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    5cea:	4d 8b 91 80 00 00 00 	mov    0x80(%r9),%r10
        for (; them->messages_count < min;) {
    5cf1:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5cf5:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5cf9:	4d 39 d8             	cmp    %r11,%r8
    5cfc:	0f 8e 93 00 00 00    	jle    5d95 <barriered_work+0x485>
    5d02:	4c 89 c6             	mov    %r8,%rsi
    5d05:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5d0c:	4d 8b b1 88 00 00 00 	mov    0x88(%r9),%r14
    5d13:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5d16:	49 8b 0a             	mov    (%r10),%rcx
    5d19:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5d1d:	48 83 f8 02          	cmp    $0x2,%rax
    5d21:	0f 86 f9 00 00 00    	jbe    5e20 <barriered_work+0x510>
    5d27:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5d2f:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5d37:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5d3b:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5d3f:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5d43:	73 6b                	jae    5db0 <barriered_work+0x4a0>
    5d45:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5d4a:	4d 39 fc             	cmp    %r15,%r12
    5d4d:	73 61                	jae    5db0 <barriered_work+0x4a0>
    5d4f:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5d53:	48 01 cf             	add    %rcx,%rdi
    5d56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5d60:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5d67:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5d6b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5d6f:	49 39 fb             	cmp    %rdi,%r11
    5d72:	75 ec                	jne    5d60 <barriered_work+0x450>
    5d74:	0f 1f 40 00          	nopl   0x0(%rax)
    5d78:	48 01 f5             	add    %rsi,%rbp
    5d7b:	4c 01 f6             	add    %r14,%rsi
    5d7e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5d85:	49 89 b1 88 00 00 00 	mov    %rsi,0x88(%r9)
    5d8c:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5d90:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5d95:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5d98:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5d9e:	48 83 c2 01          	add    $0x1,%rdx
    5da2:	39 d0                	cmp    %edx,%eax
    5da4:	0f 8f 26 ff ff ff    	jg     5cd0 <barriered_work+0x3c0>
    5daa:	e9 53 fe ff ff       	jmp    5c02 <barriered_work+0x2f2>
    5daf:	90                   	nop
    5db0:	49 89 f5             	mov    %rsi,%r13
    5db3:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5dba:	4c 89 e7             	mov    %r12,%rdi
    5dbd:	49 d1 ed             	shr    %r13
    5dc0:	49 c1 e5 04          	shl    $0x4,%r13
    5dc4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5dc9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5dcd:	41 83 e5 10          	and    $0x10,%r13d
    5dd1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5dd5:	74 11                	je     5de8 <barriered_work+0x4d8>
          them->messages[them->messages_count++] = data->message; 
    5dd7:	48 83 c7 10          	add    $0x10,%rdi
    5ddb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5de0:	4c 39 ff             	cmp    %r15,%rdi
    5de3:	74 13                	je     5df8 <barriered_work+0x4e8>
    5de5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5de8:	0f 11 07             	movups %xmm0,(%rdi)
    5deb:	48 83 c7 20          	add    $0x20,%rdi
    5def:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5df3:	4c 39 ff             	cmp    %r15,%rdi
    5df6:	75 f0                	jne    5de8 <barriered_work+0x4d8>
    5df8:	48 89 f7             	mov    %rsi,%rdi
    5dfb:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5dff:	4c 01 df             	add    %r11,%rdi
    5e02:	40 f6 c6 01          	test   $0x1,%sil
    5e06:	0f 84 6c ff ff ff    	je     5d78 <barriered_work+0x468>
          them->messages[them->messages_count++] = data->message; 
    5e0c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5e13:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5e17:	e9 5c ff ff ff       	jmp    5d78 <barriered_work+0x468>
    5e1c:	0f 1f 40 00          	nopl   0x0(%rax)
    5e20:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5e28:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5e30:	e9 1a ff ff ff       	jmp    5d4f <barriered_work+0x43f>
    5e35:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005e40 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5e40:	f3 0f 1e fa          	endbr64
    5e44:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5e48:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5e4f:	48 8b 80 80 01 00 00 	mov    0x180(%rax),%rax
    5e56:	48 63 10             	movslq (%rax),%rdx
    5e59:	85 d2                	test   %edx,%edx
    5e5b:	7e 31                	jle    5e8e <barriered_work_ingest+0x4e>
    5e5d:	48 8b 40 08          	mov    0x8(%rax),%rax
    5e61:	48 c1 e2 04          	shl    $0x4,%rdx
    5e65:	48 01 c2             	add    %rax,%rdx
    5e68:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    if (data->thread->buffers->buffer[x].available == 1) {
    5e70:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5e74:	75 0f                	jne    5e85 <barriered_work_ingest+0x45>
      data->ingest_count++;
    5e76:	48 83 87 60 01 00 00 01 	addq   $0x1,0x160(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5e7e:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5e85:	48 83 c0 10          	add    $0x10,%rax
    5e89:	48 39 d0             	cmp    %rdx,%rax
    5e8c:	75 e2                	jne    5e70 <barriered_work_ingest+0x30>
  asm volatile ("sfence" ::: "memory");
    5e8e:	0f ae f8             	sfence
  barriered_work(data);
    5e91:	e8 7a fa ff ff       	call   5910 <barriered_work>
}
    5e96:	31 c0                	xor    %eax,%eax
    5e98:	48 83 c4 08          	add    $0x8,%rsp
    5e9c:	c3                   	ret
    5e9d:	0f 1f 00             	nopl   (%rax)

0000000000005ea0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5ea0:	f3 0f 1e fa          	endbr64
}
    5ea4:	31 c0                	xor    %eax,%eax
    5ea6:	c3                   	ret
    5ea7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005eb0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5eb0:	f3 0f 1e fa          	endbr64
    5eb4:	31 c0                	xor    %eax,%eax
    5eb6:	c3                   	ret
    5eb7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005ec0 <after>:
int after(struct timespec left, struct timespec right) {
    5ec0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5ec4:	31 c0                	xor    %eax,%eax
    5ec6:	48 39 d7             	cmp    %rdx,%rdi
    5ec9:	7e 08                	jle    5ed3 <after+0x13>
    5ecb:	31 c0                	xor    %eax,%eax
    5ecd:	48 39 ce             	cmp    %rcx,%rsi
    5ed0:	0f 9f c0             	setg   %al
}
    5ed3:	c3                   	ret
    5ed4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5edf:	90                   	nop

0000000000005ee0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5ee0:	f3 0f 1e fa          	endbr64
    5ee4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5ee9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5eee:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ef0:	48 39 d7             	cmp    %rdx,%rdi
    5ef3:	7f 18                	jg     5f0d <within+0x2d>
    5ef5:	4d 39 d8             	cmp    %r11,%r8
    5ef8:	0f 9e c2             	setle  %dl
    5efb:	48 39 ce             	cmp    %rcx,%rsi
    5efe:	0f 9e c0             	setle  %al
    5f01:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5f03:	31 c0                	xor    %eax,%eax
    5f05:	4d 39 d1             	cmp    %r10,%r9
    5f08:	0f 9e c0             	setle  %al
    5f0b:	21 d0                	and    %edx,%eax
}
    5f0d:	c3                   	ret
    5f0e:	66 90                	xchg   %ax,%ax

0000000000005f10 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5f10:	f3 0f 1e fa          	endbr64
    5f14:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5f19:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5f1e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5f23:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5f28:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5f2d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5f32:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5f37:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5f3c:	48 39 fe             	cmp    %rdi,%rsi
    5f3f:	7d 2f                	jge    5f70 <overlap+0x60>
    5f41:	48 39 ca             	cmp    %rcx,%rdx
    5f44:	7d 62                	jge    5fa8 <overlap+0x98>
    5f46:	4d 39 da             	cmp    %r11,%r10
    5f49:	7d 0e                	jge    5f59 <overlap+0x49>
    return 1;
    5f4b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5f50:	4d 39 c1             	cmp    %r8,%r9
    5f53:	0f 8c 7f 00 00 00    	jl     5fd8 <overlap+0xc8>
  return 0;
    5f59:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f5b:	4d 39 c1             	cmp    %r8,%r9
    5f5e:	7f 4c                	jg     5fac <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5f60:	31 c0                	xor    %eax,%eax
    5f62:	4d 39 da             	cmp    %r11,%r10
    5f65:	0f 9e c0             	setle  %al
    5f68:	c3                   	ret
    5f69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5f70:	7e 4e                	jle    5fc0 <overlap+0xb0>
    5f72:	48 39 ca             	cmp    %rcx,%rdx
    5f75:	7f 39                	jg     5fb0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f77:	75 31                	jne    5faa <overlap+0x9a>
    5f79:	4d 39 c1             	cmp    %r8,%r9
    5f7c:	7c 2c                	jl     5faa <overlap+0x9a>
    return 1;
    5f7e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5f83:	4d 39 da             	cmp    %r11,%r10
    5f86:	7d 24                	jge    5fac <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f88:	48 39 ca             	cmp    %rcx,%rdx
    5f8b:	0f 94 c2             	sete   %dl
    5f8e:	48 39 fe             	cmp    %rdi,%rsi
    5f91:	0f 94 c0             	sete   %al
    5f94:	21 c2                	and    %eax,%edx
    5f96:	31 c0                	xor    %eax,%eax
    5f98:	4d 39 c1             	cmp    %r8,%r9
    5f9b:	0f 94 c0             	sete   %al
    5f9e:	21 d0                	and    %edx,%eax
    5fa0:	c3                   	ret
    5fa1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5fa8:	74 af                	je     5f59 <overlap+0x49>
  return 0;
    5faa:	31 c0                	xor    %eax,%eax
}
    5fac:	c3                   	ret
    5fad:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5fb0:	4d 39 da             	cmp    %r11,%r10
    5fb3:	7e c4                	jle    5f79 <overlap+0x69>
    return 1;
    5fb5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5fba:	4d 39 c1             	cmp    %r8,%r9
    5fbd:	7e ba                	jle    5f79 <overlap+0x69>
    5fbf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5fc0:	48 39 ca             	cmp    %rcx,%rdx
    5fc3:	7c 94                	jl     5f59 <overlap+0x49>
    5fc5:	4d 39 c1             	cmp    %r8,%r9
    5fc8:	7d b4                	jge    5f7e <overlap+0x6e>
    5fca:	48 39 ca             	cmp    %rcx,%rdx
    5fcd:	74 91                	je     5f60 <overlap+0x50>
    5fcf:	eb d9                	jmp    5faa <overlap+0x9a>
    5fd1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5fd8:	c3                   	ret
    5fd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005fe0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5fe0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5fe4:	85 f6                	test   %esi,%esi
    5fe6:	0f 8e 44 03 00 00    	jle    6330 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    5fec:	41 57                	push   %r15
    5fee:	41 89 f7             	mov    %esi,%r15d
    5ff1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5ff3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5ff6:	41 55                	push   %r13
    5ff8:	41 54                	push   %r12
    5ffa:	55                   	push   %rbp
    5ffb:	53                   	push   %rbx
    5ffc:	48 8d 9f 98 00 00 00 	lea    0x98(%rdi),%rbx
    6003:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6007:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    600c:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    6011:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6014:	45 39 e6             	cmp    %r12d,%r14d
    6017:	0f 84 4b 02 00 00    	je     6268 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    601d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6022:	8b 50 08             	mov    0x8(%rax),%edx
    6025:	85 d2                	test   %edx,%edx
    6027:	0f 8e 3b 02 00 00    	jle    6268 <verify+0x288>
    602d:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    6032:	31 c9                	xor    %ecx,%ecx
    6034:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    6039:	31 c0                	xor    %eax,%eax
    603b:	44 89 f2             	mov    %r14d,%edx
    603e:	bf 01 00 00 00       	mov    $0x1,%edi
    6043:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6048:	48 8d 35 d1 11 00 00 	lea    0x11d1(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    604f:	e8 fc c3 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6054:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6059:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    605e:	8b 40 08             	mov    0x8(%rax),%eax
    6061:	85 c0                	test   %eax,%eax
    6063:	0f 8e e3 01 00 00    	jle    624c <verify+0x26c>
    6069:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    606c:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    6071:	31 db                	xor    %ebx,%ebx
    6073:	48 c1 e0 09          	shl    $0x9,%rax
    6077:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    607c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    6081:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6086:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    608b:	4c 8b 20             	mov    (%rax),%r12
    608e:	66 90                	xchg   %ax,%ax
    6090:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6095:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    609a:	49 89 de             	mov    %rbx,%r14
    609d:	48 8d 35 91 11 00 00 	lea    0x1191(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    60a4:	49 c1 e6 09          	shl    $0x9,%r14
    60a8:	bf 01 00 00 00       	mov    $0x1,%edi
    60ad:	48 8b 45 00          	mov    0x0(%rbp),%rax
    60b1:	4b 8b 8c 3c 58 01 00 00 	mov    0x158(%r12,%r15,1),%rcx
    60b9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    60be:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    60c6:	31 c0                	xor    %eax,%eax
    60c8:	e8 83 c3 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60cd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    60d2:	4c 8b 20             	mov    (%rax),%r12
    60d5:	4b 83 bc 3c 58 01 00 00 00 	cmpq   $0x0,0x158(%r12,%r15,1)
    60de:	0f 8e 47 01 00 00    	jle    622b <verify+0x24b>
    60e4:	4c 03 75 00          	add    0x0(%rbp),%r14
    60e8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60ed:	ba 01 00 00 00       	mov    $0x1,%edx
    60f2:	4d 89 f5             	mov    %r14,%r13
    60f5:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    60fc:	4d 85 f6             	test   %r14,%r14
    60ff:	0f 8e 21 01 00 00    	jle    6226 <verify+0x246>
    6105:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6108:	48 89 d5             	mov    %rdx,%rbp
    610b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6110:	31 db                	xor    %ebx,%ebx
    6112:	4d 89 f2             	mov    %r14,%r10
    6115:	48 c1 e5 05          	shl    $0x5,%rbp
    6119:	48 83 ed 20          	sub    $0x20,%rbp
    611d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6121:	49 89 ee             	mov    %rbp,%r14
    6124:	48 89 dd             	mov    %rbx,%rbp
    6127:	48 89 d3             	mov    %rdx,%rbx
    612a:	eb 31                	jmp    615d <verify+0x17d>
    612c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6130:	4c 39 c2             	cmp    %r8,%rdx
    6133:	0f 8d 57 01 00 00    	jge    6290 <verify+0x2b0>
    6139:	4c 39 df             	cmp    %r11,%rdi
    613c:	7e 05                	jle    6143 <verify+0x163>
    613e:	49 39 c1             	cmp    %rax,%r9
    6141:	7c 75                	jl     61b8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6143:	4c 39 df             	cmp    %r11,%rdi
    6146:	0f 8d ab 01 00 00    	jge    62f7 <verify+0x317>
    614c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6150:	48 83 c5 01          	add    $0x1,%rbp
    6154:	49 39 ea             	cmp    %rbp,%r10
    6157:	0f 8e a9 00 00 00    	jle    6206 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    615d:	49 8b 97 48 01 00 00 	mov    0x148(%r15),%rdx
    6164:	48 89 e8             	mov    %rbp,%rax
    6167:	48 c1 e0 05          	shl    $0x5,%rax
    616b:	49 03 85 48 01 00 00 	add    0x148(%r13),%rax
    6172:	4c 01 f2             	add    %r14,%rdx
    6175:	48 8b 08             	mov    (%rax),%rcx
    6178:	48 8b 78 10          	mov    0x10(%rax),%rdi
    617c:	48 8b 32             	mov    (%rdx),%rsi
    617f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6183:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6187:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    618b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    618f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6193:	48 39 f1             	cmp    %rsi,%rcx
    6196:	7c 98                	jl     6130 <verify+0x150>
    6198:	0f 8e 42 01 00 00    	jle    62e0 <verify+0x300>
    619e:	4c 39 c2             	cmp    %r8,%rdx
    61a1:	0f 8f f9 00 00 00    	jg     62a0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    61a7:	75 a7                	jne    6150 <verify+0x170>
    61a9:	4c 39 df             	cmp    %r11,%rdi
    61ac:	7f a2                	jg     6150 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    61ae:	49 39 c1             	cmp    %rax,%r9
    61b1:	7c 9d                	jl     6150 <verify+0x170>
    61b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    61b8:	49 89 c1             	mov    %rax,%r9
    61bb:	48 89 f9             	mov    %rdi,%rcx
    61be:	48 89 f2             	mov    %rsi,%rdx
    61c1:	bf 01 00 00 00       	mov    $0x1,%edi
    61c6:	48 8d 35 bb 12 00 00 	lea    0x12bb(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    61cd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    61cf:	48 83 c5 01          	add    $0x1,%rbp
    61d3:	e8 78 c2 ff ff       	call   2450 <__printf_chk@plt>
    61d8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    61dd:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    61e2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    61e5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    61ea:	4d 8b 95 58 01 00 00 	mov    0x158(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    61f1:	4c 8b 20             	mov    (%rax),%r12
    61f4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    61f9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    61fd:	49 39 ea             	cmp    %rbp,%r10
    6200:	0f 8f 57 ff ff ff    	jg     615d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6206:	48 89 da             	mov    %rbx,%rdx
    6209:	49 3b 9f 58 01 00 00 	cmp    0x158(%r15),%rbx
    6210:	7d 14                	jge    6226 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6212:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    6219:	48 83 c2 01          	add    $0x1,%rdx
    621d:	4d 85 f6             	test   %r14,%r14
    6220:	0f 8f e2 fe ff ff    	jg     6108 <verify+0x128>
    6226:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    622b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6230:	48 83 c3 01          	add    $0x1,%rbx
    6234:	39 58 08             	cmp    %ebx,0x8(%rax)
    6237:	0f 8f 53 fe ff ff    	jg     6090 <verify+0xb0>
    623d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6242:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6247:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    624c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6251:	48 83 c1 01          	add    $0x1,%rcx
    6255:	39 48 08             	cmp    %ecx,0x8(%rax)
    6258:	0f 8f db fd ff ff    	jg     6039 <verify+0x59>
    625e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6263:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6268:	48 81 44 24 10 80 02 00 00 	addq   $0x280,0x10(%rsp)
    6271:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6276:	41 39 c7             	cmp    %eax,%r15d
    6279:	0f 84 86 00 00 00    	je     6305 <verify+0x325>
    627f:	41 89 c4             	mov    %eax,%r12d
    6282:	e9 8d fd ff ff       	jmp    6014 <verify+0x34>
    6287:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6290:	0f 85 ba fe ff ff    	jne    6150 <verify+0x170>
    6296:	e9 a8 fe ff ff       	jmp    6143 <verify+0x163>
    629b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    62a0:	49 39 c1             	cmp    %rax,%r9
    62a3:	7e 09                	jle    62ae <verify+0x2ce>
    62a5:	4c 39 df             	cmp    %r11,%rdi
    62a8:	0f 8c 0a ff ff ff    	jl     61b8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    62ae:	4c 39 df             	cmp    %r11,%rdi
    62b1:	0f 8f 99 fe ff ff    	jg     6150 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    62b7:	49 39 c1             	cmp    %rax,%r9
    62ba:	0f 8d f8 fe ff ff    	jge    61b8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    62c0:	48 39 f1             	cmp    %rsi,%rcx
    62c3:	0f 85 87 fe ff ff    	jne    6150 <verify+0x170>
    62c9:	4c 39 c2             	cmp    %r8,%rdx
    62cc:	0f 85 7e fe ff ff    	jne    6150 <verify+0x170>
    62d2:	4c 39 df             	cmp    %r11,%rdi
    62d5:	0f 84 dd fe ff ff    	je     61b8 <verify+0x1d8>
    62db:	e9 70 fe ff ff       	jmp    6150 <verify+0x170>
    62e0:	4c 39 c2             	cmp    %r8,%rdx
    62e3:	0f 8c 5a fe ff ff    	jl     6143 <verify+0x163>
    62e9:	4c 39 df             	cmp    %r11,%rdi
    62ec:	7e c9                	jle    62b7 <verify+0x2d7>
    62ee:	4c 39 c2             	cmp    %r8,%rdx
    62f1:	0f 85 59 fe ff ff    	jne    6150 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    62f7:	49 39 c1             	cmp    %rax,%r9
    62fa:	0f 8f 50 fe ff ff    	jg     6150 <verify+0x170>
    6300:	e9 b3 fe ff ff       	jmp    61b8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    6305:	48 81 44 24 18 80 02 00 00 	addq   $0x280,0x18(%rsp)
    630e:	41 8d 46 01          	lea    0x1(%r14),%eax
    6312:	45 39 e6             	cmp    %r12d,%r14d
    6315:	74 08                	je     631f <verify+0x33f>
    6317:	41 89 c6             	mov    %eax,%r14d
    631a:	e9 ed fc ff ff       	jmp    600c <verify+0x2c>
}
    631f:	48 83 c4 58          	add    $0x58,%rsp
    6323:	31 c0                	xor    %eax,%eax
    6325:	5b                   	pop    %rbx
    6326:	5d                   	pop    %rbp
    6327:	41 5c                	pop    %r12
    6329:	41 5d                	pop    %r13
    632b:	41 5e                	pop    %r14
    632d:	41 5f                	pop    %r15
    632f:	c3                   	ret
    6330:	31 c0                	xor    %eax,%eax
    6332:	c3                   	ret

Disassembly of section .fini:

0000000000006334 <_fini>:
    6334:	f3 0f 1e fa          	endbr64
    6338:	48 83 ec 08          	sub    $0x8,%rsp
    633c:	48 83 c4 08          	add    $0x8,%rsp
    6340:	c3                   	ret
