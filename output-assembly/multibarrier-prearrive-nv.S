
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
    261d:	48 8d 05 4c 12 00 00 	lea    0x124c(%rip),%rax        # 3870 <barriered_reset>
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
    2743:	be 00 04 00 00       	mov    $0x400,%esi
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
    275a:	be 00 01 00 00       	mov    $0x100,%esi
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
    2775:	be 00 01 00 00       	mov    $0x100,%esi
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
    279f:	48 89 83 80 00 00 00 	mov    %rax,0x80(%rbx)
      buffers[x].buffer[y].available = 0;
    27a6:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    27b0:	4d 89 d1             	mov    %r10,%r9
    27b3:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    27b8:	4c 89 54 24 58       	mov    %r10,0x58(%rsp)
    27bd:	0f 1f 00             	nopl   (%rax)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27c0:	be 08 00 00 00       	mov    $0x8,%esi
    27c5:	bf 02 00 00 00       	mov    $0x2,%edi
    27ca:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    27cf:	44 89 fd             	mov    %r15d,%ebp
    27d2:	e8 c9 fb ff ff       	call   23a0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27d7:	be 80 00 00 00       	mov    $0x80,%esi
    27dc:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27e1:	49 89 c5             	mov    %rax,%r13
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27e4:	e8 b7 fb ff ff       	call   23a0 <calloc@plt>
    if (x % 2 == 1) {
    27e9:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27ee:	48 89 c3             	mov    %rax,%rbx
    if (x % 2 == 1) {
    27f1:	44 89 f8             	mov    %r15d,%eax
    27f4:	41 83 c7 01          	add    $0x1,%r15d
    27f8:	83 e0 01             	and    $0x1,%eax
    27fb:	85 c0                	test   %eax,%eax
    27fd:	0f 84 bc 0e 00 00    	je     36bf <main+0x10cf>
      my_thread_data[0] = &thread_data[other]; 
    2803:	49 8d 89 00 fc ff ff 	lea    -0x400(%r9),%rcx
      my_thread_data[1] = &thread_data[x]; 
    280a:	4d 89 4d 08          	mov    %r9,0x8(%r13)
    280e:	4d 89 c8             	mov    %r9,%r8
    2811:	89 ea                	mov    %ebp,%edx
      my_thread_data[0] = &thread_data[other]; 
    2813:	49 89 4d 00          	mov    %rcx,0x0(%r13)
    2817:	bf 01 00 00 00       	mov    $0x1,%edi
    281c:	31 c0                	xor    %eax,%eax
      other = abs(x - 1) % total_threads;
    281e:	44 8d 75 ff          	lea    -0x1(%rbp),%r14d
      thread_data[x].thread_index = 1;
    2822:	41 c7 01 01 00 00 00 	movl   $0x1,(%r9)
    2829:	48 8d 35 cb 4a 00 00 	lea    0x4acb(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
    2830:	e8 1b fc ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    2835:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    283a:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    283f:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2844:	4d 89 a1 00 01 00 00 	mov    %r12,0x100(%r9)
    284b:	45 8b 01             	mov    (%r9),%r8d
    284e:	44 89 f1             	mov    %r14d,%ecx
    2851:	89 ea                	mov    %ebp,%edx
    2853:	48 8d 35 16 4d 00 00 	lea    0x4d16(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    285a:	bf 01 00 00 00       	mov    $0x1,%edi
    285f:	31 c0                	xor    %eax,%eax
    2861:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      CPU_SET(j, sendercpu);
    2866:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    286c:	e8 df fb ff ff       	call   2450 <__printf_chk@plt>
    thread_data[x].other = other;
    2871:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2876:	45 89 b1 90 03 00 00 	mov    %r14d,0x390(%r9)
    for (int j = 0 ; j < cores / 2 ; j++) {
    287d:	45 31 f6             	xor    %r14d,%r14d
    2880:	44 89 f1             	mov    %r14d,%ecx
    2883:	89 ea                	mov    %ebp,%edx
    2885:	48 8d 35 14 4d 00 00 	lea    0x4d14(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    288c:	31 c0                	xor    %eax,%eax
    288e:	bf 01 00 00 00       	mov    $0x1,%edi
    2893:	e8 b8 fb ff ff       	call   2450 <__printf_chk@plt>
      CPU_SET(j, sendercpu);
    2898:	44 89 f1             	mov    %r14d,%ecx
    289b:	4c 89 e0             	mov    %r12,%rax
    for (int j = 0 ; j < cores / 2 ; j++) {
    289e:	41 83 c6 01          	add    $0x1,%r14d
      CPU_SET(j, sendercpu);
    28a2:	48 d3 e0             	shl    %cl,%rax
    28a5:	48 09 03             	or     %rax,(%rbx)
    for (int j = 0 ; j < cores / 2 ; j++) {
    28a8:	41 83 fe 06          	cmp    $0x6,%r14d
    28ac:	75 d2                	jne    2880 <main+0x290>
    thread_data[x].cpu_set = sendercpu;
    28ae:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    thread_data[x].thread_count = 2;
    28b3:	48 8b 05 86 51 00 00 	mov    0x5186(%rip),%rax        # 7a40 <_IO_stdin_used+0xa40>
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28ba:	be 10 00 00 00       	mov    $0x10,%esi
        thread_data[x].tasks[y].sending = 1;
    28bf:	41 89 ee             	mov    %ebp,%r14d
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28c2:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].cpu_set = sendercpu;
    28c7:	49 89 99 88 03 00 00 	mov    %rbx,0x388(%r9)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28ce:	31 db                	xor    %ebx,%ebx
    thread_data[x].real_thread_index = x;
    28d0:	41 89 69 04          	mov    %ebp,0x4(%r9)
    thread_data[x].threads = my_thread_data;
    28d4:	4d 89 a9 80 00 00 00 	mov    %r13,0x80(%r9)
    thread_data[x].thread_count = 2;
    28db:	49 89 81 88 00 00 00 	mov    %rax,0x88(%r9)
    thread_data[x].task_count = total_barrier_count;
    28e2:	41 c7 81 a0 00 00 00 03 00 00 00 	movl   $0x3,0xa0(%r9)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28ed:	e8 ae fa ff ff       	call   23a0 <calloc@plt>
    28f2:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28f7:	be 10 00 00 00       	mov    $0x10,%esi
    28fc:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2901:	49 89 81 98 01 00 00 	mov    %rax,0x198(%r9)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2908:	e8 93 fa ff ff       	call   23a0 <calloc@plt>
    290d:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2912:	be 28 00 00 00       	mov    $0x28,%esi
    thread_data[x].timestamp_count = 0;
    2917:	66 0f 6f 15 01 51 00 00 	movdqa 0x5101(%rip),%xmm2        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    291f:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2924:	49 89 81 a0 01 00 00 	mov    %rax,0x1a0(%r9)
    thread_data[x].timestamp_count = 0;
    292b:	41 0f 29 91 00 02 00 00 	movaps %xmm2,0x200(%r9)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2933:	e8 68 fa ff ff       	call   23a0 <calloc@plt>
    2938:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    293d:	be 80 04 00 00       	mov    $0x480,%esi
    thread_data[x].task_timestamp_count = 0;
    2942:	66 0f 6f 1d d6 50 00 00 	movdqa 0x50d6(%rip),%xmm3        # 7a20 <_IO_stdin_used+0xa20>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    294a:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    294f:	49 89 81 80 02 00 00 	mov    %rax,0x280(%r9)
    thread_data[x].task_timestamp_count = 0;
    2956:	41 0f 29 99 00 03 00 00 	movaps %xmm3,0x300(%r9)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    295e:	e8 3d fa ff ff       	call   23a0 <calloc@plt>
      thread_data[x].tasks = barriers;
    2963:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        thread_data[x].tasks[y].sending = 1;
    2968:	44 89 7c 24 28       	mov    %r15d,0x28(%rsp)
    296d:	48 89 c2             	mov    %rax,%rdx
      thread_data[x].tasks = barriers;
    2970:	49 89 81 98 00 00 00 	mov    %rax,0x98(%r9)
        thread_data[x].tasks[y].sending = 1;
    2977:	4c 89 cd             	mov    %r9,%rbp
        thread_data[x].tasks[y].protected = do_protected_write; 
    297a:	4c 63 fb             	movslq %ebx,%r15
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    297d:	be 00 02 00 00       	mov    $0x200,%esi
    2982:	bf 0c 00 00 00       	mov    $0xc,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    2987:	4f 8d 24 ff          	lea    (%r15,%r15,8),%r12
    298b:	48 8d 05 9e 0e 00 00 	lea    0xe9e(%rip),%rax        # 3830 <do_protected_write>
    2992:	49 c1 e4 07          	shl    $0x7,%r12
    2996:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
    299a:	49 89 85 10 02 00 00 	mov    %rax,0x210(%r13)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    29a1:	e8 fa f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    29a6:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    29aa:	49 89 85 88 03 00 00 	mov    %rax,0x388(%r13)
        for (int b = 0 ; b < 2 ; b++) {
    29b1:	49 89 c5             	mov    %rax,%r13
    29b4:	48 8d 80 00 04 00 00 	lea    0x400(%rax),%rax
    29bb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    29c0:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29c5:	be 08 00 00 00       	mov    $0x8,%esi
    29ca:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    29cf:	49 81 c5 00 02 00 00 	add    $0x200,%r13
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29d6:	e8 c5 f9 ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29db:	be 08 00 00 00       	mov    $0x8,%esi
    29e0:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29e5:	48 89 c5             	mov    %rax,%rbp
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29e8:	e8 b3 f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29ed:	be 00 01 00 00       	mov    $0x100,%esi
    29f2:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29f7:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29fa:	e8 a1 f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    29ff:	66 0f 6f 05 29 50 00 00 	movdqa 0x5029(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
          mailboxes[b].higher = &data[1];
    2a07:	48 8d b0 00 01 00 00 	lea    0x100(%rax),%rsi
          mailboxes[b].lower = &data[0];
    2a0e:	49 89 85 00 fe ff ff 	mov    %rax,-0x200(%r13)
          mailboxes[b].higher = &data[1];
    2a15:	49 89 b5 80 fe ff ff 	mov    %rsi,-0x180(%r13)
          data[0].messages = messages;
    2a1c:	48 89 28             	mov    %rbp,(%rax)
          data[1].messages = messages2;
    2a1f:	48 89 98 00 01 00 00 	mov    %rbx,0x100(%rax)
          data[0].messages_count = 0;
    2a26:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
          data[1].messages_count = 0;
    2a2d:	0f 29 80 80 01 00 00 	movaps %xmm0,0x180(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    2a34:	4c 39 6c 24 08       	cmp    %r13,0x8(%rsp)
    2a39:	75 8a                	jne    29c5 <main+0x3d5>
        char *message = malloc(sizeof(char) * 256);
    2a3b:	be 01 00 00 00       	mov    $0x1,%esi
    2a40:	bf 00 01 00 00       	mov    $0x100,%edi
    2a45:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    2a49:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    2a4e:	e8 4d f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a53:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a58:	49 89 c5             	mov    %rax,%r13
        struct Message *messaged = malloc(sizeof(struct Message));
    2a5b:	e8 b0 f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a60:	4c 89 ef             	mov    %r13,%rdi
    2a63:	41 89 d9             	mov    %ebx,%r9d
    2a66:	45 89 f0             	mov    %r14d,%r8d
    2a69:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2a6e:	48 8d 0d 4b 4b 00 00 	lea    0x4b4b(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a75:	ba 00 01 00 00       	mov    $0x100,%edx
    2a7a:	31 c0                	xor    %eax,%eax
    2a7c:	be 01 00 00 00       	mov    $0x1,%esi
    2a81:	e8 9a fa ff ff       	call   2520 <__sprintf_chk@plt>
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a86:	48 8b 95 98 00 00 00 	mov    0x98(%rbp),%rdx
        messaged->message = message;
    2a8d:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a92:	8d 4b 01             	lea    0x1(%rbx),%ecx
        messaged->thread_index = thread_data[x].thread_index;
    2a95:	48 63 45 00          	movslq 0x0(%rbp),%rax
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a99:	be 20 00 00 00       	mov    $0x20,%esi
    2a9e:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2aa3:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
        messaged->message = message;
    2aa7:	4d 89 2a             	mov    %r13,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2aaa:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
        messaged->task_index = y;
    2aae:	4d 89 7a 10          	mov    %r15,0x10(%r10)
        messaged->thread_index = thread_data[x].thread_index;
    2ab2:	49 89 c7             	mov    %rax,%r15
    2ab5:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2ab9:	41 89 8d 18 04 00 00 	mov    %ecx,0x418(%r13)
        thread_data[x].tasks[y].message = messaged;
    2ac0:	4d 89 95 10 04 00 00 	mov    %r10,0x410(%r13)
        thread_data[x].tasks[y].snapshot_count = 99;
    2ac7:	49 c7 85 00 03 00 00 63 00 00 00 	movq   $0x63,0x300(%r13)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2ad2:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2ad7:	e8 c4 f8 ff ff       	call   23a0 <calloc@plt>
        if (y == barrier_count - 1) {
    2adc:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2adf:	41 89 5d 00          	mov    %ebx,0x0(%r13)
        if (y == barrier_count - 1) {
    2ae3:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2ae7:	49 89 85 88 02 00 00 	mov    %rax,0x288(%r13)
        if (y == barrier_count - 1) {
    2aee:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
        thread_data[x].tasks[y].available = 1;
    2af3:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2afd:	49 89 85 28 02 00 00 	mov    %rax,0x228(%r13)
        thread_data[x].tasks[y].sending = 1;
    2b04:	48 b8 01 00 00 00 0c 00 00 00 	movabs $0xc00000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2b0e:	49 c7 85 08 03 00 00 00 00 00 00 	movq   $0x0,0x308(%r13)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2b19:	45 89 bd 20 02 00 00 	mov    %r15d,0x220(%r13)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2b20:	49 89 ad 18 02 00 00 	mov    %rbp,0x218(%r13)
        thread_data[x].tasks[y].arrived = 0;
    2b27:	41 c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r13)
        thread_data[x].tasks[y].thread_count = 2;
    2b32:	41 c7 85 24 02 00 00 02 00 00 00 	movl   $0x2,0x224(%r13)
        thread_data[x].tasks[y].sending = 1;
    2b3d:	49 89 85 08 04 00 00 	mov    %rax,0x408(%r13)
        if (y == barrier_count - 1) {
    2b44:	0f 84 5d 0b 00 00    	je     36a7 <main+0x10b7>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2b4a:	44 39 f3             	cmp    %r14d,%ebx
    2b4d:	75 71                	jne    2bc0 <main+0x5d0>
    2b4f:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    2b53:	85 db                	test   %ebx,%ebx
    2b55:	7f 69                	jg     2bc0 <main+0x5d0>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2b57:	44 89 f2             	mov    %r14d,%edx
    2b5a:	bf 01 00 00 00       	mov    $0x1,%edi
    2b5f:	31 c0                	xor    %eax,%eax
    2b61:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2b65:	48 8d 35 7c 4a 00 00 	lea    0x4a7c(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2b6c:	e8 df f8 ff ff       	call   2450 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b71:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    2b76:	48 63 c3             	movslq %ebx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b79:	48 8b 95 98 00 00 00 	mov    0x98(%rbp),%rdx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b80:	48 89 c7             	mov    %rax,%rdi
    2b83:	48 c1 e0 08          	shl    $0x8,%rax
    2b87:	48 01 c8             	add    %rcx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b8a:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b8e:	48 89 85 80 01 00 00 	mov    %rax,0x180(%rbp)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b95:	48 8d 05 c4 33 00 00 	lea    0x33c4(%rip),%rax        # 5f60 <barriered_work_ingest>
    2b9c:	4a 89 84 22 08 02 00 00 	mov    %rax,0x208(%rdx,%r12,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2ba4:	8d 47 01             	lea    0x1(%rdi),%eax
    2ba7:	89 44 24 20          	mov    %eax,0x20(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2bab:	83 f9 03             	cmp    $0x3,%ecx
    2bae:	74 23                	je     2bd3 <main+0x5e3>
    2bb0:	bb 01 00 00 00       	mov    $0x1,%ebx
    2bb5:	e9 c0 fd ff ff       	jmp    297a <main+0x38a>
    2bba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            thread_data[x].tasks[y].run = barriered_work; 
    2bc0:	48 8d 05 49 2e 00 00 	lea    0x2e49(%rip),%rax        # 5a10 <barriered_work>
    2bc7:	49 89 85 08 02 00 00 	mov    %rax,0x208(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2bce:	83 f9 03             	cmp    $0x3,%ecx
    2bd1:	75 dd                	jne    2bb0 <main+0x5c0>

          }
        }
      }
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2bd3:	66 0f 6f 64 24 30    	movdqa 0x30(%rsp),%xmm4
    2bd9:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
    2bde:	49 89 e9             	mov    %rbp,%r9
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2be1:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2beb:	c7 82 80 09 00 00 00 00 00 00 	movl   $0x0,0x980(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2bf5:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    2bfa:	49 81 c1 00 04 00 00 	add    $0x400,%r9
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2c01:	c7 82 00 09 00 00 02 00 00 00 	movl   $0x2,0x900(%rdx)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2c0b:	48 89 82 24 0b 00 00 	mov    %rax,0xb24(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2c12:	8b 45 00             	mov    0x0(%rbp),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2c15:	48 89 aa 18 0b 00 00 	mov    %rbp,0xb18(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2c1c:	89 82 20 0b 00 00    	mov    %eax,0xb20(%rdx)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2c22:	c7 82 0c 0d 00 00 0c 00 00 00 	movl   $0xc,0xd0c(%rdx)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2c2c:	c7 82 2c 0b 00 00 03 00 00 00 	movl   $0x3,0xb2c(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2c36:	0f 11 a2 08 0b 00 00 	movups %xmm4,0xb08(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2c3d:	41 83 ff 0f          	cmp    $0xf,%r15d
    2c41:	0f 85 79 fb ff ff    	jne    27c0 <main+0x1d0>
    2c47:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    2c4c:	ba 0d 00 00 00       	mov    $0xd,%edx
    2c51:	48 8d 35 c0 46 00 00 	lea    0x46c0(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2c58:	31 c0                	xor    %eax,%eax
    2c5a:	bf 01 00 00 00       	mov    $0x1,%edi
    2c5f:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    2c64:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2c69:	e8 e2 f7 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c6e:	be 08 00 00 00       	mov    $0x8,%esi
    2c73:	bf 02 00 00 00       	mov    $0x2,%edi
    2c78:	e8 23 f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2c7d:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c82:	bf 0f 00 00 00       	mov    $0xf,%edi
    my_thread_data[0] = &thread_data[x]; 
    2c87:	4d 8d ba 00 34 00 00 	lea    0x3400(%r10),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c8e:	4d 8d b2 00 08 00 00 	lea    0x800(%r10),%r14
    thread_data[x].threads = my_thread_data;
    2c95:	49 89 82 80 34 00 00 	mov    %rax,0x3480(%r10)
    my_thread_data[0] = &thread_data[x]; 
    2c9c:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c9f:	49 8d 8a 00 0c 00 00 	lea    0xc00(%r10),%rcx
    2ca6:	49 8d 92 00 14 00 00 	lea    0x1400(%r10),%rdx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2cad:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2cb1:	49 8b 82 98 00 00 00 	mov    0x98(%r10),%rax
    2cb8:	4d 8d 9a 00 1c 00 00 	lea    0x1c00(%r10),%r11
    2cbf:	4d 8d 82 00 20 00 00 	lea    0x2000(%r10),%r8
    2cc6:	49 8d b2 00 10 00 00 	lea    0x1000(%r10),%rsi
    2ccd:	49 8d 9a 00 18 00 00 	lea    0x1800(%r10),%rbx
    thread_data[x].thread_count = 2;
    2cd4:	41 c7 82 88 34 00 00 02 00 00 00 	movl   $0x2,0x3488(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2cdf:	48 89 4c 24 58       	mov    %rcx,0x58(%rsp)
    2ce4:	4d 8d 8a 00 24 00 00 	lea    0x2400(%r10),%r9
    2ceb:	4d 8d a2 00 28 00 00 	lea    0x2800(%r10),%r12
    2cf2:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    2cf7:	4d 8d aa 00 2c 00 00 	lea    0x2c00(%r10),%r13
    thread_data[x].thread_index = 0;
    2cfe:	41 c7 82 00 34 00 00 00 00 00 00 	movl   $0x0,0x3400(%r10)
    thread_data[x].task_count = total_barrier_count;
    2d09:	41 c7 82 a0 34 00 00 03 00 00 00 	movl   $0x3,0x34a0(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2d14:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2d1e:	49 8d 82 00 04 00 00 	lea    0x400(%r10),%rax
    2d25:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2d2a:	49 8b 82 98 04 00 00 	mov    0x498(%r10),%rax
    2d31:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    2d36:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2d40:	49 8b 82 98 08 00 00 	mov    0x898(%r10),%rax
    2d47:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    2d4c:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2d56:	49 8b 82 98 0c 00 00 	mov    0xc98(%r10),%rax
    my_thread_data[0] = &thread_data[x]; 
    2d5d:	4c 89 7c 24 70       	mov    %r15,0x70(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d62:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2d6c:	49 8b 82 98 10 00 00 	mov    0x1098(%r10),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2d73:	4c 89 74 24 78       	mov    %r14,0x78(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d78:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2d82:	49 8b 82 98 14 00 00 	mov    0x1498(%r10),%rax
    2d89:	48 89 74 24 50       	mov    %rsi,0x50(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d8e:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2d93:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2d9d:	49 8b 82 98 18 00 00 	mov    0x1898(%r10),%rax
    2da4:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    2da9:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2db3:	49 8b 82 98 1c 00 00 	mov    0x1c98(%r10),%rax
    2dba:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2dc4:	49 8b 82 98 20 00 00 	mov    0x2098(%r10),%rax
    2dcb:	4c 89 4c 24 30       	mov    %r9,0x30(%rsp)
    2dd0:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2dda:	49 8b 82 98 24 00 00 	mov    0x2498(%r10),%rax
    2de1:	4c 89 94 24 80 00 00 00 	mov    %r10,0x80(%rsp)
    2de9:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2df3:	49 8b 82 98 28 00 00 	mov    0x2898(%r10),%rax
    2dfa:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    2dff:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2e09:	49 8b 82 98 2c 00 00 	mov    0x2c98(%r10),%rax
    2e10:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    2e15:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e1f:	e8 7c f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e24:	be 38 00 00 00       	mov    $0x38,%esi
    2e29:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e2e:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e31:	e8 6a f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e36:	be 38 00 00 00       	mov    $0x38,%esi
    2e3b:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e40:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e43:	e8 58 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e48:	be 38 00 00 00       	mov    $0x38,%esi
    2e4d:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e52:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e5a:	e8 41 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e5f:	be 08 00 00 00       	mov    $0x8,%esi
    2e64:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e69:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e71:	e8 2a f5 ff ff       	call   23a0 <calloc@plt>
  thread_data[thread_count].type = TIMER;
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2e76:	be 08 00 00 00       	mov    $0x8,%esi
    2e7b:	bf 0f 00 00 00       	mov    $0xf,%edi
  thread_data[thread_count].type = TIMER;
    2e80:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e88:	49 89 c5             	mov    %rax,%r13
  thread_data[thread_count].task_count = total_barrier_count;
    2e8b:	48 8b 05 b6 4b 00 00 	mov    0x4bb6(%rip),%rax        # 7a48 <_IO_stdin_used+0xa48>
  thread_data[thread_count].type = TIMER;
    2e92:	41 c7 82 08 30 00 00 00 00 00 00 	movl   $0x0,0x3008(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2e9d:	49 89 82 a0 30 00 00 	mov    %rax,0x30a0(%r10)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2ea4:	e8 f7 f4 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2ea9:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    2eae:	48 8b 4c 24 58       	mov    0x58(%rsp),%rcx
    2eb3:	48 8b 74 24 50       	mov    0x50(%rsp),%rsi
    2eb8:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    2ebd:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2ec1:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    2ec6:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    2ecb:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2ecf:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    2ed4:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
    2edc:	48 89 48 18          	mov    %rcx,0x18(%rax)
    2ee0:	4c 8b 4c 24 30       	mov    0x30(%rsp),%r9
    2ee5:	48 89 70 20          	mov    %rsi,0x20(%rax)
    2ee9:	48 8d 35 37 44 00 00 	lea    0x4437(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2ef0:	48 89 78 30          	mov    %rdi,0x30(%rax)
    2ef4:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    2ef9:	4d 8d b2 00 30 00 00 	lea    0x3000(%r10),%r14
    2f00:	4c 89 10             	mov    %r10,(%rax)
    2f03:	48 89 78 50          	mov    %rdi,0x50(%rax)
    2f07:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    2f0c:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2f10:	ba 0c 00 00 00       	mov    $0xc,%edx
    2f15:	48 89 78 58          	mov    %rdi,0x58(%rax)
    2f19:	49 8d ba 00 38 00 00 	lea    0x3800(%r10),%rdi
    2f20:	4c 89 58 38          	mov    %r11,0x38(%rax)
    2f24:	4c 89 40 40          	mov    %r8,0x40(%rax)
    2f28:	4c 89 48 48          	mov    %r9,0x48(%rax)
    2f2c:	4c 89 70 60          	mov    %r14,0x60(%rax)
    2f30:	4c 89 78 68          	mov    %r15,0x68(%rax)
    2f34:	4c 8d 3d c5 09 00 00 	lea    0x9c5(%rip),%r15        # 3900 <barriered_thread>
    2f3b:	48 89 78 70          	mov    %rdi,0x70(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2f3f:	49 89 82 80 30 00 00 	mov    %rax,0x3080(%r10)
    2f46:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2f48:	41 c7 82 88 30 00 00 0c 00 00 00 	movl   $0xc,0x3088(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2f53:	41 c7 82 90 30 00 00 02 00 00 00 	movl   $0x2,0x3090(%r10)
  thread_data[thread_count].thread_index = 0;
    2f5e:	41 c7 82 00 30 00 00 00 00 00 00 	movl   $0x0,0x3000(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2f69:	48 89 bc 24 80 00 00 00 	mov    %rdi,0x80(%rsp)
    2f71:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].thread_index = 0;
    2f76:	4c 89 94 24 98 00 00 00 	mov    %r10,0x98(%rsp)
    2f7e:	e8 cd f4 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2f83:	48 8d b3 a0 02 00 00 	lea    0x2a0(%rbx),%rsi
    2f8a:	49 8d 7d 60          	lea    0x60(%r13),%rdi
    2f8e:	4c 89 f1             	mov    %r14,%rcx
    2f91:	48 8d 15 48 0d 00 00 	lea    0xd48(%rip),%rdx        # 3ce0 <timer_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    2f98:	45 31 f6             	xor    %r14d,%r14d
    2f9b:	4c 89 eb             	mov    %r13,%rbx
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2f9e:	e8 cd f4 ff ff       	call   2470 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2fa3:	44 89 f0             	mov    %r14d,%eax
    2fa6:	4d 89 ee             	mov    %r13,%r14
    2fa9:	41 89 c5             	mov    %eax,%r13d
    thread_data[x].type = WORKER;
    2fac:	c7 45 08 01 00 00 00 	movl   $0x1,0x8(%rbp)
    2fb3:	44 89 ea             	mov    %r13d,%edx
    2fb6:	bf 01 00 00 00       	mov    $0x1,%edi
    2fbb:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2fbd:	c7 85 a4 00 00 00 01 00 00 00 	movl   $0x1,0xa4(%rbp)
    2fc7:	48 8d 35 3a 46 00 00 	lea    0x463a(%rip),%rsi        # 7608 <_IO_stdin_used+0x608>
  for (int x = 0 ; x < thread_count ; x++) {
    2fce:	41 83 c5 01          	add    $0x1,%r13d
    2fd2:	e8 79 f4 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2fd7:	48 89 e9             	mov    %rbp,%rcx
    2fda:	4c 89 e6             	mov    %r12,%rsi
    2fdd:	48 89 df             	mov    %rbx,%rdi
    2fe0:	4c 89 fa             	mov    %r15,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2fe3:	48 81 c5 00 04 00 00 	add    $0x400,%rbp
    2fea:	48 83 c3 08          	add    $0x8,%rbx
    2fee:	49 83 c4 38          	add    $0x38,%r12
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2ff2:	e8 79 f4 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2ff7:	48 8b 55 88          	mov    -0x78(%rbp),%rdx
    2ffb:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    2fff:	be 08 00 00 00       	mov    $0x8,%esi
    3004:	e8 d7 f2 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    3009:	41 83 fd 0c          	cmp    $0xc,%r13d
    300d:	75 9d                	jne    2fac <main+0x9bc>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    300f:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    3017:	48 8b 1d 32 4a 00 00 	mov    0x4a32(%rip),%rbx        # 7a50 <_IO_stdin_used+0xa50>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    301e:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    3023:	4d 89 f5             	mov    %r14,%r13
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3026:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    302b:	49 89 9a a0 34 00 00 	mov    %rbx,0x34a0(%r10)
    thread_data[x].type = IO;
    3032:	41 c7 82 08 34 00 00 02 00 00 00 	movl   $0x2,0x3408(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    303d:	e8 5e f3 ff ff       	call   23a0 <calloc@plt>
    3042:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    304a:	be 00 08 00 00       	mov    $0x800,%esi
    304f:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3051:	49 89 82 88 35 00 00 	mov    %rax,0x3588(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3058:	e8 53 f4 ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    305d:	be 08 00 00 00       	mov    $0x8,%esi
    3062:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3067:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    306f:	41 89 82 90 35 00 00 	mov    %eax,0x3590(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3076:	e8 25 f3 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    307b:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    3080:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    3085:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    308d:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3092:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    3097:	4c 8b 74 24 78       	mov    0x78(%rsp),%r14
    309c:	4c 89 58 48          	mov    %r11,0x48(%rax)
    30a0:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    30a5:	4c 8b 7c 24 60       	mov    0x60(%rsp),%r15
    30aa:	4c 89 40 50          	mov    %r8,0x50(%rax)
    30ae:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    30b3:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    30b8:	4c 89 48 58          	mov    %r9,0x58(%rax)
    30bc:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    30c1:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    30c6:	4c 89 10             	mov    %r10,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    30c9:	49 89 82 80 34 00 00 	mov    %rax,0x3480(%r10)
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    30d0:	41 c7 82 88 34 00 00 0c 00 00 00 	movl   $0xc,0x3488(%r10)
    thread_data[x].thread_index = x;
    30db:	41 c7 82 00 34 00 00 0d 00 00 00 	movl   $0xd,0x3400(%r10)
      my_thread_data[n] = &thread_data[n]; 
    30e6:	4c 89 70 10          	mov    %r14,0x10(%rax)
    30ea:	48 89 68 18          	mov    %rbp,0x18(%rax)
    30ee:	4c 89 60 20          	mov    %r12,0x20(%rax)
    30f2:	48 89 78 28          	mov    %rdi,0x28(%rax)
    30f6:	bf 01 00 00 00       	mov    $0x1,%edi
    30fb:	48 89 48 30          	mov    %rcx,0x30(%rax)
    30ff:	48 89 70 38          	mov    %rsi,0x38(%rax)
    3103:	48 8d 35 3b 42 00 00 	lea    0x423b(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    310a:	48 89 50 40          	mov    %rdx,0x40(%rax)
    310e:	ba 0d 00 00 00       	mov    $0xd,%edx
    3113:	4c 89 78 08          	mov    %r15,0x8(%rax)
    3117:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3119:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    311e:	e8 2d f3 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3123:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    3128:	49 8d 7d 68          	lea    0x68(%r13),%rdi
    312c:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    3134:	48 8d 15 d5 1e 00 00 	lea    0x1ed5(%rip),%rdx        # 5010 <io_thread>
    313b:	48 05 d8 02 00 00    	add    $0x2d8,%rax
    3141:	48 89 c6             	mov    %rax,%rsi
    3144:	e8 27 f3 ff ff       	call   2470 <pthread_create@plt>
    3149:	ba 0e 00 00 00       	mov    $0xe,%edx
    314e:	48 8d 35 07 42 00 00 	lea    0x4207(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    3155:	31 c0                	xor    %eax,%eax
    3157:	bf 01 00 00 00       	mov    $0x1,%edi
    315c:	e8 ef f2 ff ff       	call   2450 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    3161:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    3166:	48 8b 44 24 48       	mov    0x48(%rsp),%rax

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    316b:	be 08 00 00 00       	mov    $0x8,%esi
    3170:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x].task_count = 0;
    3175:	49 89 9a a0 38 00 00 	mov    %rbx,0x38a0(%r10)
    317c:	31 db                	xor    %ebx,%ebx
    thread_data[x].type = EXTERNAL;
    317e:	41 c7 82 08 38 00 00 03 00 00 00 	movl   $0x3,0x3808(%r10)
    thread_data[x].buffers = &buffers[buffer_index];
    3189:	49 89 82 80 39 00 00 	mov    %rax,0x3980(%r10)
    3190:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3195:	e8 06 f2 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    319a:	4c 8b 54 24 48       	mov    0x48(%rsp),%r10
    319f:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    31a4:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    31a9:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    31ae:	4c 89 70 10          	mov    %r14,0x10(%rax)
    31b2:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    31b7:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    31bc:	4c 89 10             	mov    %r10,(%rax)
    31bf:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    31c4:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    31c9:	48 89 68 18          	mov    %rbp,0x18(%rax)
    31cd:	48 8d 2d c3 41 00 00 	lea    0x41c3(%rip),%rbp        # 7397 <_IO_stdin_used+0x397>
    31d4:	4c 89 60 20          	mov    %r12,0x20(%rax)
    31d8:	4c 8d a4 24 a0 00 00 00 	lea    0xa0(%rsp),%r12
    31e0:	48 89 78 28          	mov    %rdi,0x28(%rax)
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31e4:	49 8d 7d 70          	lea    0x70(%r13),%rdi
      my_thread_data[n] = &thread_data[n]; 
    31e8:	48 89 48 30          	mov    %rcx,0x30(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31ec:	48 8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%rcx
      my_thread_data[n] = &thread_data[n]; 
    31f4:	48 89 70 38          	mov    %rsi,0x38(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31f8:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3200:	48 89 50 40          	mov    %rdx,0x40(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3204:	48 8d 15 05 0a 00 00 	lea    0xa05(%rip),%rdx        # 3c10 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    320b:	4c 89 58 48          	mov    %r11,0x48(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    320f:	48 81 c6 10 03 00 00 	add    $0x310,%rsi
      my_thread_data[n] = &thread_data[n]; 
    3216:	4c 89 40 50          	mov    %r8,0x50(%rax)
    321a:	4c 89 48 58          	mov    %r9,0x58(%rax)
    thread_data[x].threads = my_thread_data;
    321e:	49 89 82 80 38 00 00 	mov    %rax,0x3880(%r10)
      my_thread_data[n] = &thread_data[n]; 
    3225:	4c 89 78 08          	mov    %r15,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3229:	48 8b 05 28 48 00 00 	mov    0x4828(%rip),%rax        # 7a58 <_IO_stdin_used+0xa58>
    thread_data[x].thread_index = x;
    3230:	41 c7 82 00 38 00 00 0e 00 00 00 	movl   $0xe,0x3800(%r10)
    thread_data[x].thread_count = thread_count;
    323b:	49 89 82 88 38 00 00 	mov    %rax,0x3888(%r10)
    thread_data[x].thread_index = x;
    3242:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3247:	e8 24 f2 ff ff       	call   2470 <pthread_create@plt>
    324c:	48 8d 3d 26 41 00 00 	lea    0x4126(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    3253:	e8 98 f0 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3258:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    325d:	0f 1f 00             	nopl   (%rax)
    void * result; 
    pthread_join(thread[x], &result);
    3260:	49 8b 7c dd 00       	mov    0x0(%r13,%rbx,8),%rdi
    3265:	4c 89 e6             	mov    %r12,%rsi
    3268:	e8 83 f2 ff ff       	call   24f0 <pthread_join@plt>
    326d:	89 da                	mov    %ebx,%edx
    326f:	48 89 ee             	mov    %rbp,%rsi
    3272:	bf 01 00 00 00       	mov    $0x1,%edi
    3277:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3279:	48 83 c3 01          	add    $0x1,%rbx
    327d:	e8 ce f1 ff ff       	call   2450 <__printf_chk@plt>
    3282:	48 83 fb 0f          	cmp    $0xf,%rbx
    3286:	75 d8                	jne    3260 <main+0xc70>
    3288:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    328d:	4d 89 f2             	mov    %r14,%r10
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    3290:	31 db                	xor    %ebx,%ebx
  long sents = 0;
    3292:	31 ed                	xor    %ebp,%ebp
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3294:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    3299:	4d 8d ae 98 00 00 00 	lea    0x98(%r14),%r13
  long total = 0;
    32a0:	45 31 f6             	xor    %r14d,%r14d
  long ingests = 0;
    32a3:	45 31 c9             	xor    %r9d,%r9d
    32a6:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32ab:	4d 89 ef             	mov    %r13,%r15
    32ae:	4d 89 f5             	mov    %r14,%r13
  for (int x = 0 ; x < thread_count ; x++) {
    32b1:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    if (x % 2 == 1) {
    32b9:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    32bd:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    32c2:	89 f8                	mov    %edi,%eax
    32c4:	41 89 fc             	mov    %edi,%r12d
      other = (x + 1) % total_threads;
    32c7:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
    32ca:	83 e0 01             	and    $0x1,%eax
      other = abs(x - 1) % total_threads;
    32cd:	41 83 ec 01          	sub    $0x1,%r12d
      other = (x + 1) % total_threads;
    32d1:	89 7c 24 10          	mov    %edi,0x10(%rsp)
      other = abs(x - 1) % total_threads;
    32d5:	85 c0                	test   %eax,%eax
    32d7:	44 0f 44 e7          	cmove  %edi,%r12d
    32db:	bf 0a 00 00 00       	mov    $0xa,%edi
    32e0:	e8 eb ef ff ff       	call   22d0 <putchar@plt>
    32e5:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    32ea:	bf 01 00 00 00       	mov    $0x1,%edi
    32ef:	48 8d 35 b5 40 00 00 	lea    0x40b5(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    32f6:	48 8b 10             	mov    (%rax),%rdx
    32f9:	31 c0                	xor    %eax,%eax
    32fb:	e8 50 f1 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3300:	49 63 57 08          	movslq 0x8(%r15),%rdx
    3304:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3309:	85 d2                	test   %edx,%edx
    330b:	0f 8e 1f 04 00 00    	jle    3730 <main+0x1140>
    3311:	49 8b 07             	mov    (%r15),%rax
    3314:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
    long v = 0;
    3318:	31 d2                	xor    %edx,%edx
    331a:	48 c1 e6 07          	shl    $0x7,%rsi
    331e:	48 05 00 02 00 00    	add    $0x200,%rax
    3324:	48 01 c6             	add    %rax,%rsi
    3327:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      v += thread_data[me].tasks[n].v;
    3330:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3333:	48 05 80 04 00 00    	add    $0x480,%rax
    3339:	48 39 f0             	cmp    %rsi,%rax
    333c:	75 f2                	jne    3330 <main+0xd40>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    333e:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    3343:	4d 63 e4             	movslq %r12d,%r12
    3346:	49 c1 e4 0a          	shl    $0xa,%r12
    334a:	4c 01 e0             	add    %r12,%rax
    334d:	48 63 b0 a0 00 00 00 	movslq 0xa0(%rax),%rsi
    3354:	85 f6                	test   %esi,%esi
    3356:	7e 26                	jle    337e <main+0xd8e>
      v += thread_data[other].tasks[n].v;
    3358:	48 8b 80 98 00 00 00 	mov    0x98(%rax),%rax
    335f:	48 8d 34 f6          	lea    (%rsi,%rsi,8),%rsi
    3363:	48 c1 e6 07          	shl    $0x7,%rsi
    3367:	48 05 00 02 00 00    	add    $0x200,%rax
    336d:	48 01 c6             	add    %rax,%rsi
    3370:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3373:	48 05 80 04 00 00    	add    $0x480,%rax
    3379:	48 39 f0             	cmp    %rsi,%rax
    337c:	75 f2                	jne    3370 <main+0xd80>
    337e:	48 8d 35 3b 40 00 00 	lea    0x403b(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    3385:	bf 01 00 00 00       	mov    $0x1,%edi
    338a:	31 c0                	xor    %eax,%eax
    338c:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    3391:	e8 ba f0 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3396:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    339b:	bf 01 00 00 00       	mov    $0x1,%edi
    33a0:	48 8b 30             	mov    (%rax),%rsi
    33a3:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    33ad:	48 f7 ee             	imul   %rsi
    33b0:	48 c1 fe 3f          	sar    $0x3f,%rsi
    33b4:	31 c0                	xor    %eax,%eax
    33b6:	48 d1 fa             	sar    %rdx
    33b9:	48 29 f2             	sub    %rsi,%rdx
    33bc:	48 8d 35 6d 42 00 00 	lea    0x426d(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    33c3:	e8 88 f0 ff ff       	call   2450 <__printf_chk@plt>
    33c8:	bf 0a 00 00 00       	mov    $0xa,%edi
    33cd:	e8 fe ee ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    33d2:	49 63 47 08          	movslq 0x8(%r15),%rax
    33d6:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    33db:	85 c0                	test   %eax,%eax
    33dd:	0f 8e ed 00 00 00    	jle    34d0 <main+0xee0>
    33e3:	49 8b 3f             	mov    (%r15),%rdi
    33e6:	48 8d 34 c0          	lea    (%rax,%rax,8),%rsi
    33ea:	48 c1 e6 07          	shl    $0x7,%rsi
    33ee:	48 8d 97 80 01 00 00 	lea    0x180(%rdi),%rdx
    33f5:	48 01 d6             	add    %rdx,%rsi
    33f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3400:	48 8b 82 08 02 00 00 	mov    0x208(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    3407:	4c 03 2a             	add    (%rdx),%r13
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    340a:	48 81 c2 80 04 00 00 	add    $0x480,%rdx
      ingests += thread_data[x].tasks[n].ingest_count;
    3411:	4c 03 b2 80 fd ff ff 	add    -0x280(%rdx),%r14
      sends += thread_data[x].tasks[n].sends;
    3418:	4c 03 8a 00 fe ff ff 	add    -0x200(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    341f:	48 03 a8 00 01 00 00 	add    0x100(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3426:	48 03 98 80 01 00 00 	add    0x180(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    342d:	48 03 a8 00 03 00 00 	add    0x300(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3434:	48 03 98 80 03 00 00 	add    0x380(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    343b:	48 03 a8 00 05 00 00 	add    0x500(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3442:	48 03 98 80 05 00 00 	add    0x580(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3449:	48 03 a8 00 07 00 00 	add    0x700(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3450:	48 03 98 80 07 00 00 	add    0x780(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3457:	48 03 a8 00 09 00 00 	add    0x900(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    345e:	48 03 98 80 09 00 00 	add    0x980(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3465:	48 03 a8 00 0b 00 00 	add    0xb00(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    346c:	48 03 98 80 0b 00 00 	add    0xb80(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3473:	48 03 a8 00 0d 00 00 	add    0xd00(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    347a:	48 03 98 80 0d 00 00 	add    0xd80(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3481:	48 03 a8 00 0f 00 00 	add    0xf00(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3488:	48 03 98 80 0f 00 00 	add    0xf80(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    348f:	48 03 a8 00 11 00 00 	add    0x1100(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3496:	48 03 98 80 11 00 00 	add    0x1180(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    349d:	48 03 a8 00 13 00 00 	add    0x1300(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    34a4:	48 03 98 80 13 00 00 	add    0x1380(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    34ab:	48 03 a8 00 15 00 00 	add    0x1500(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    34b2:	48 03 98 80 15 00 00 	add    0x1580(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    34b9:	48 03 a8 00 17 00 00 	add    0x1700(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    34c0:	48 03 98 80 17 00 00 	add    0x1780(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    34c7:	48 39 f2             	cmp    %rsi,%rdx
    34ca:	0f 85 30 ff ff ff    	jne    3400 <main+0xe10>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    34d0:	45 31 e4             	xor    %r12d,%r12d
    34d3:	49 83 bf 70 02 00 00 00 	cmpq   $0x0,0x270(%r15)
    34db:	7e 7f                	jle    355c <main+0xf6c>
    34dd:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    34e2:	4c 89 fb             	mov    %r15,%rbx
    34e5:	4d 89 e7             	mov    %r12,%r15
    34e8:	4d 89 cc             	mov    %r9,%r12
    34eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    34f0:	48 8b 83 e8 01 00 00 	mov    0x1e8(%rbx),%rax
    34f7:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    34fb:	48 83 ec 08          	sub    $0x8,%rsp
    34ff:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3504:	49 83 c7 01          	add    $0x1,%r15
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3508:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    350c:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3516:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    351a:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    351e:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3521:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3525:	4c 2b 01             	sub    (%rcx),%r8
    3528:	31 c0                	xor    %eax,%eax
    352a:	8b 49 20             	mov    0x20(%rcx),%ecx
    352d:	56                   	push   %rsi
    352e:	48 8d 35 1b 41 00 00 	lea    0x411b(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    3535:	48 c1 ea 12          	shr    $0x12,%rdx
    3539:	49 89 d1             	mov    %rdx,%r9
    353c:	ba 02 00 00 00       	mov    $0x2,%edx
    3541:	e8 0a ef ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3546:	58                   	pop    %rax
    3547:	5a                   	pop    %rdx
    3548:	4c 39 bb 70 02 00 00 	cmp    %r15,0x270(%rbx)
    354f:	7f 9f                	jg     34f0 <main+0xf00>
    3551:	49 89 df             	mov    %rbx,%r15
    3554:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    3559:	4d 89 e1             	mov    %r12,%r9
  for (int x = 0 ; x < thread_count ; x++) {
    355c:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    3562:	49 81 c7 00 04 00 00 	add    $0x400,%r15
    3569:	83 7c 24 10 0c       	cmpl   $0xc,0x10(%rsp)
    356e:	0f 85 45 fd ff ff    	jne    32b9 <main+0xcc9>
    3574:	4c 89 ea             	mov    %r13,%rdx
    3577:	48 8d 35 4f 3e 00 00 	lea    0x3e4f(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    357e:	31 c0                	xor    %eax,%eax
    3580:	4d 89 cf             	mov    %r9,%r15
    3583:	bf 01 00 00 00       	mov    $0x1,%edi
    3588:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    358d:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    3597:	e8 b4 ee ff ff       	call   2450 <__printf_chk@plt>
    359c:	bf 0a 00 00 00       	mov    $0xa,%edi
    35a1:	e8 2a ed ff ff       	call   22d0 <putchar@plt>
    35a6:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    35ab:	bf 01 00 00 00       	mov    $0x1,%edi
    35b0:	48 8d 35 e9 40 00 00 	lea    0x40e9(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    35b7:	48 8b 50 08          	mov    0x8(%rax),%rdx
    35bb:	31 c0                	xor    %eax,%eax
    35bd:	e8 8e ee ff ff       	call   2450 <__printf_chk@plt>
    35c2:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    35c7:	bf 01 00 00 00       	mov    $0x1,%edi
    35cc:	48 8d 35 f5 40 00 00 	lea    0x40f5(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    35d3:	4c 89 c8             	mov    %r9,%rax
    35d6:	49 c1 f9 3f          	sar    $0x3f,%r9
    35da:	49 f7 ec             	imul   %r12
    35dd:	31 c0                	xor    %eax,%eax
    35df:	48 d1 fa             	sar    %rdx
    35e2:	4c 29 ca             	sub    %r9,%rdx
    35e5:	e8 66 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    35ea:	4c 89 f8             	mov    %r15,%rax
    35ed:	4d 89 fb             	mov    %r15,%r11
    35f0:	bf 01 00 00 00       	mov    $0x1,%edi
    35f5:	49 f7 ec             	imul   %r12
    35f8:	49 c1 fb 3f          	sar    $0x3f,%r11
    35fc:	48 8d 35 f5 40 00 00 	lea    0x40f5(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    3603:	31 c0                	xor    %eax,%eax
    3605:	48 d1 fa             	sar    %rdx
    3608:	4c 29 da             	sub    %r11,%rdx
    360b:	e8 40 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3610:	4c 89 e8             	mov    %r13,%rax
    3613:	4c 89 e9             	mov    %r13,%rcx
    3616:	bf 01 00 00 00       	mov    $0x1,%edi
    361b:	49 f7 ec             	imul   %r12
    361e:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3622:	48 8d 35 ff 40 00 00 	lea    0x40ff(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    3629:	31 c0                	xor    %eax,%eax
    362b:	48 d1 fa             	sar    %rdx
    362e:	48 29 ca             	sub    %rcx,%rdx
    3631:	e8 1a ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3636:	48 89 e8             	mov    %rbp,%rax
    3639:	48 c1 fd 3f          	sar    $0x3f,%rbp
    363d:	48 8d 35 9d 3d 00 00 	lea    0x3d9d(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    3644:	49 f7 ec             	imul   %r12
    3647:	bf 01 00 00 00       	mov    $0x1,%edi
    364c:	31 c0                	xor    %eax,%eax
    364e:	48 d1 fa             	sar    %rdx
    3651:	48 29 ea             	sub    %rbp,%rdx
    3654:	e8 f7 ed ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3659:	48 89 d8             	mov    %rbx,%rax
    365c:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3660:	48 8d 35 8b 3d 00 00 	lea    0x3d8b(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    3667:	49 f7 ec             	imul   %r12
    366a:	bf 01 00 00 00       	mov    $0x1,%edi
    366f:	48 d1 fa             	sar    %rdx
    3672:	48 29 da             	sub    %rbx,%rdx
    3675:	31 c0                	xor    %eax,%eax
    3677:	e8 d4 ed ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    367c:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    3684:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    368d:	0f 85 a4 00 00 00    	jne    3737 <main+0x1147>
    3693:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    369a:	31 c0                	xor    %eax,%eax
    369c:	5b                   	pop    %rbx
    369d:	5d                   	pop    %rbp
    369e:	41 5c                	pop    %r12
    36a0:	41 5d                	pop    %r13
    36a2:	41 5e                	pop    %r14
    36a4:	41 5f                	pop    %r15
    36a6:	c3                   	ret
          thread_data[x].tasks[y].run = barriered_work; 
    36a7:	48 8d 05 62 23 00 00 	lea    0x2362(%rip),%rax        # 5a10 <barriered_work>
    36ae:	bb 02 00 00 00       	mov    $0x2,%ebx
    36b3:	49 89 85 08 02 00 00 	mov    %rax,0x208(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    36ba:	e9 bb f2 ff ff       	jmp    297a <main+0x38a>
      other = (x + 1) % total_threads;
    36bf:	b8 89 88 88 88       	mov    $0x88888889,%eax
    36c4:	45 89 fe             	mov    %r15d,%r14d
      my_thread_data[0] = &thread_data[x]; 
    36c7:	4d 89 4d 00          	mov    %r9,0x0(%r13)
    36cb:	4c 89 c9             	mov    %r9,%rcx
      other = (x + 1) % total_threads;
    36ce:	4c 0f af f0          	imul   %rax,%r14
    36d2:	89 ea                	mov    %ebp,%edx
    36d4:	bf 01 00 00 00       	mov    $0x1,%edi
    36d9:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].thread_index = 0;
    36de:	41 c7 01 00 00 00 00 	movl   $0x0,(%r9)
    36e5:	48 8d 35 1d 3c 00 00 	lea    0x3c1d(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      other = (x + 1) % total_threads;
    36ec:	49 c1 ee 23          	shr    $0x23,%r14
    36f0:	44 89 f0             	mov    %r14d,%eax
    36f3:	c1 e0 04             	shl    $0x4,%eax
    36f6:	44 29 f0             	sub    %r14d,%eax
    36f9:	45 89 fe             	mov    %r15d,%r14d
    36fc:	41 29 c6             	sub    %eax,%r14d
      my_thread_data[1] = &thread_data[other]; 
    36ff:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    3704:	4d 63 c6             	movslq %r14d,%r8
    3707:	49 c1 e0 0a          	shl    $0xa,%r8
    370b:	49 01 c0             	add    %rax,%r8
    370e:	31 c0                	xor    %eax,%eax
    3710:	4d 89 45 08          	mov    %r8,0x8(%r13)
    3714:	e8 37 ed ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    3719:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    371e:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3723:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    3728:	49 89 c4             	mov    %rax,%r12
    372b:	e9 14 f1 ff ff       	jmp    2844 <main+0x254>
    long v = 0;
    3730:	31 d2                	xor    %edx,%edx
    3732:	e9 07 fc ff ff       	jmp    333e <main+0xd4e>
}
    3737:	e8 f4 eb ff ff       	call   2330 <__stack_chk_fail@plt>
    373c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003740 <_start>:
    3740:	f3 0f 1e fa          	endbr64
    3744:	31 ed                	xor    %ebp,%ebp
    3746:	49 89 d1             	mov    %rdx,%r9
    3749:	5e                   	pop    %rsi
    374a:	48 89 e2             	mov    %rsp,%rdx
    374d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3751:	50                   	push   %rax
    3752:	54                   	push   %rsp
    3753:	45 31 c0             	xor    %r8d,%r8d
    3756:	31 c9                	xor    %ecx,%ecx
    3758:	48 8d 3d 91 ee ff ff 	lea    -0x116f(%rip),%rdi        # 25f0 <main>
    375f:	ff 15 73 68 00 00    	call   *0x6873(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3765:	f4                   	hlt
    3766:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003770 <deregister_tm_clones>:
    3770:	48 8d 3d a9 68 00 00 	lea    0x68a9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3777:	48 8d 05 a2 68 00 00 	lea    0x68a2(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    377e:	48 39 f8             	cmp    %rdi,%rax
    3781:	74 15                	je     3798 <deregister_tm_clones+0x28>
    3783:	48 8b 05 56 68 00 00 	mov    0x6856(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    378a:	48 85 c0             	test   %rax,%rax
    378d:	74 09                	je     3798 <deregister_tm_clones+0x28>
    378f:	ff e0                	jmp    *%rax
    3791:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3798:	c3                   	ret
    3799:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037a0 <register_tm_clones>:
    37a0:	48 8d 3d 79 68 00 00 	lea    0x6879(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    37a7:	48 8d 35 72 68 00 00 	lea    0x6872(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    37ae:	48 29 fe             	sub    %rdi,%rsi
    37b1:	48 89 f0             	mov    %rsi,%rax
    37b4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    37b8:	48 c1 f8 03          	sar    $0x3,%rax
    37bc:	48 01 c6             	add    %rax,%rsi
    37bf:	48 d1 fe             	sar    %rsi
    37c2:	74 14                	je     37d8 <register_tm_clones+0x38>
    37c4:	48 8b 05 25 68 00 00 	mov    0x6825(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    37cb:	48 85 c0             	test   %rax,%rax
    37ce:	74 08                	je     37d8 <register_tm_clones+0x38>
    37d0:	ff e0                	jmp    *%rax
    37d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    37d8:	c3                   	ret
    37d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037e0 <__do_global_dtors_aux>:
    37e0:	f3 0f 1e fa          	endbr64
    37e4:	80 3d 3d 68 00 00 00 	cmpb   $0x0,0x683d(%rip)        # a028 <completed.0>
    37eb:	75 2b                	jne    3818 <__do_global_dtors_aux+0x38>
    37ed:	55                   	push   %rbp
    37ee:	48 83 3d 02 68 00 00 00 	cmpq   $0x0,0x6802(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    37f6:	48 89 e5             	mov    %rsp,%rbp
    37f9:	74 0c                	je     3807 <__do_global_dtors_aux+0x27>
    37fb:	48 8b 3d 06 68 00 00 	mov    0x6806(%rip),%rdi        # a008 <__dso_handle>
    3802:	e8 a9 ea ff ff       	call   22b0 <__cxa_finalize@plt>
    3807:	e8 64 ff ff ff       	call   3770 <deregister_tm_clones>
    380c:	c6 05 15 68 00 00 01 	movb   $0x1,0x6815(%rip)        # a028 <completed.0>
    3813:	5d                   	pop    %rbp
    3814:	c3                   	ret
    3815:	0f 1f 00             	nopl   (%rax)
    3818:	c3                   	ret
    3819:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003820 <frame_dummy>:
    3820:	f3 0f 1e fa          	endbr64
    3824:	e9 77 ff ff ff       	jmp    37a0 <register_tm_clones>
    3829:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003830 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3830:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3834:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    383b:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
  data->v++; // thread local
    3842:	48 83 87 00 02 00 00 01 	addq   $0x1,0x200(%rdi)
  if (protected->balance > 0) {
    384a:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    384e:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3852:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3859:	48 85 c9             	test   %rcx,%rcx
    385c:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3863:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3867:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    386b:	31 c0                	xor    %eax,%eax
    386d:	c3                   	ret
    386e:	66 90                	xchg   %ax,%ax

0000000000003870 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3870:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3874:	48 63 8f 2c 02 00 00 	movslq 0x22c(%rdi),%rcx
    387b:	85 c9                	test   %ecx,%ecx
    387d:	7e 6c                	jle    38eb <barriered_reset+0x7b>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    387f:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    3886:	48 63 bf 20 02 00 00 	movslq 0x220(%rdi),%rdi
    388d:	48 8d 0c c9          	lea    (%rcx,%rcx,8),%rcx
    3891:	48 c1 e1 07          	shl    $0x7,%rcx
      data->thread->tasks[x].available = 1; 
    3895:	48 8b b0 98 00 00 00 	mov    0x98(%rax),%rsi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    389c:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    38a3:	48 8b 04 f8          	mov    (%rax,%rdi,8),%rax
    38a7:	48 8d 96 28 02 00 00 	lea    0x228(%rsi),%rdx
    38ae:	48 8d 8c 0e 28 02 00 00 	lea    0x228(%rsi,%rcx,1),%rcx
    38b6:	48 8b 80 98 00 00 00 	mov    0x98(%rax),%rax
    38bd:	48 05 00 01 00 00    	add    $0x100,%rax
    38c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    38c8:	83 40 80 01          	addl   $0x1,-0x80(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
    38cc:	48 81 c2 80 04 00 00 	add    $0x480,%rdx
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    38d3:	83 00 01             	addl   $0x1,(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
    38d6:	48 05 80 04 00 00    	add    $0x480,%rax
      data->thread->tasks[x].available = 1; 
    38dc:	c7 82 80 fb ff ff 01 00 00 00 	movl   $0x1,-0x480(%rdx)
    for (int x = 0 ; x < data->task_count ; x++) {
    38e6:	48 39 ca             	cmp    %rcx,%rdx
    38e9:	75 dd                	jne    38c8 <barriered_reset+0x58>
  asm volatile ("sfence" ::: "memory");
    38eb:	0f ae f8             	sfence
}
    38ee:	31 c0                	xor    %eax,%eax
    38f0:	c3                   	ret
    38f1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    38fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003900 <barriered_thread>:
void* barriered_thread(void *arg) {
    3900:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3904:	83 bf a4 00 00 00 01 	cmpl   $0x1,0xa4(%rdi)
    390b:	0f 85 f5 02 00 00    	jne    3c06 <barriered_thread+0x306>
void* barriered_thread(void *arg) {
    3911:	41 56                	push   %r14
    3913:	41 55                	push   %r13
    3915:	45 31 ed             	xor    %r13d,%r13d
    3918:	41 54                	push   %r12
    391a:	49 89 fc             	mov    %rdi,%r12
    391d:	55                   	push   %rbp
    391e:	53                   	push   %rbx
    391f:	31 db                	xor    %ebx,%ebx
    3921:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    if (t >= data->task_count) {
    3928:	41 8b 94 24 a0 00 00 00 	mov    0xa0(%r12),%edx
    3930:	39 da                	cmp    %ebx,%edx
    3932:	7f 13                	jg     3947 <barriered_thread+0x47>
      data->cycles++;
    3934:	49 83 84 24 80 03 00 00 01 	addq   $0x1,0x380(%r12)
    for (; t < data->task_count; t++) {
    393d:	31 db                	xor    %ebx,%ebx
    393f:	85 d2                	test   %edx,%edx
    3941:	0f 8e 89 01 00 00    	jle    3ad0 <barriered_thread+0x1d0>
    3947:	48 63 c3             	movslq %ebx,%rax
    394a:	48 8d 2c c0          	lea    (%rax,%rax,8),%rbp
    394e:	48 c1 e5 07          	shl    $0x7,%rbp
    3952:	eb 16                	jmp    396a <barriered_thread+0x6a>
    3954:	0f 1f 40 00          	nopl   0x0(%rax)
    3958:	83 c3 01             	add    $0x1,%ebx
    395b:	48 81 c5 80 04 00 00 	add    $0x480,%rbp
    3962:	39 d3                	cmp    %edx,%ebx
    3964:	0f 8d 66 01 00 00    	jge    3ad0 <barriered_thread+0x1d0>
      if (data->tasks[t].available == 1) {
    396a:	49 8b 84 24 98 00 00 00 	mov    0x98(%r12),%rax
    3972:	48 8d 0c 28          	lea    (%rax,%rbp,1),%rcx
    3976:	83 b9 28 02 00 00 01 	cmpl   $0x1,0x228(%rcx)
    397d:	75 d9                	jne    3958 <barriered_thread+0x58>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    397f:	41 8b bc 24 88 00 00 00 	mov    0x88(%r12),%edi
          previous = t - 1;
    3987:	83 ea 01             	sub    $0x1,%edx
    398a:	8d 73 ff             	lea    -0x1(%rbx),%esi
    398d:	85 db                	test   %ebx,%ebx
    398f:	0f 4f d6             	cmovg  %esi,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3992:	85 ff                	test   %edi,%edi
    3994:	0f 8e 16 02 00 00    	jle    3bb0 <barriered_thread+0x2b0>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    399a:	48 63 d2             	movslq %edx,%rdx
    399d:	44 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9d
        int prearrive = 0; 
    39a4:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    39a7:	45 31 f6             	xor    %r14d,%r14d
    39aa:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    39b2:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
    39b6:	48 63 d7             	movslq %edi,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    39b9:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    39c0:	48 c1 e6 07          	shl    $0x7,%rsi
    39c4:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    39c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    39d0:	48 8b 10             	mov    (%rax),%rdx
    39d3:	4c 8b 9a 98 00 00 00 	mov    0x98(%rdx),%r11
    39da:	49 01 f3             	add    %rsi,%r11
    39dd:	4c 89 da             	mov    %r11,%rdx
    39e0:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    39e7:	75 04                	jne    39ed <barriered_thread+0xed>
            arrived++;
    39e9:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    39ed:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    39f4:	75 04                	jne    39fa <barriered_thread+0xfa>
            prearrive++;
    39f6:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    39fa:	48 83 c0 08          	add    $0x8,%rax
    39fe:	48 39 c8             	cmp    %rcx,%rax
    3a01:	75 cd                	jne    39d0 <barriered_thread+0xd0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    3a03:	44 39 d7             	cmp    %r10d,%edi
    3a06:	0f 84 e4 00 00 00    	je     3af0 <barriered_thread+0x1f0>
    3a0c:	45 85 d2             	test   %r10d,%r10d
    3a0f:	0f 84 db 00 00 00    	je     3af0 <barriered_thread+0x1f0>
        if (arrived == 0 || arrived == data->thread_count) {
    3a15:	45 85 f6             	test   %r14d,%r14d
    3a18:	74 0e                	je     3a28 <barriered_thread+0x128>
    3a1a:	45 39 b4 24 88 00 00 00 	cmp    %r14d,0x88(%r12)
    3a22:	0f 85 a8 00 00 00    	jne    3ad0 <barriered_thread+0x1d0>
    3a28:	49 8b 84 24 98 00 00 00 	mov    0x98(%r12),%rax
          data->tasks[t].prearrive++;
    3a30:	48 01 e8             	add    %rbp,%rax
    3a33:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    3a3a:	85 db                	test   %ebx,%ebx
    3a3c:	75 16                	jne    3a54 <barriered_thread+0x154>
    3a3e:	49 8b b4 24 00 02 00 00 	mov    0x200(%r12),%rsi
    3a46:	49 3b b4 24 08 02 00 00 	cmp    0x208(%r12),%rsi
    3a4e:	0f 8c 2c 01 00 00    	jl     3b80 <barriered_thread+0x280>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3a54:	49 63 0c 24          	movslq (%r12),%rcx
    3a58:	49 8b 94 24 80 00 00 00 	mov    0x80(%r12),%rdx
          data->tasks[t].available = 0;
    3a60:	c7 80 28 02 00 00 00 00 00 00 	movl   $0x0,0x228(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3a6a:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    3a6e:	48 8b ba 98 00 00 00 	mov    0x98(%rdx),%rdi
    3a75:	48 01 ef             	add    %rbp,%rdi
    3a78:	ff 90 08 02 00 00    	call   *0x208(%rax)
          data->tasks[t].arrived++;
    3a7e:	49 8b 84 24 98 00 00 00 	mov    0x98(%r12),%rax
    3a86:	48 01 e8             	add    %rbp,%rax
    3a89:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3a90:	41 8b 84 24 a0 00 00 00 	mov    0xa0(%r12),%eax
          data->iteration_count++;
    3a98:	49 83 84 24 a8 01 00 00 01 	addq   $0x1,0x1a8(%r12)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3aa1:	83 e8 01             	sub    $0x1,%eax
    3aa4:	39 d8                	cmp    %ebx,%eax
    3aa6:	74 60                	je     3b08 <barriered_thread+0x208>
          asm volatile ("sfence" ::: "memory");
    3aa8:	0f ae f8             	sfence
          if (waiting == 0) {
    3aab:	45 85 ed             	test   %r13d,%r13d
    3aae:	0f 84 8c 00 00 00    	je     3b40 <barriered_thread+0x240>
    for (; t < data->task_count; t++) {
    3ab4:	41 8b 94 24 a0 00 00 00 	mov    0xa0(%r12),%edx
    3abc:	83 c3 01             	add    $0x1,%ebx
    3abf:	48 81 c5 80 04 00 00 	add    $0x480,%rbp
    3ac6:	39 d3                	cmp    %edx,%ebx
    3ac8:	0f 8c 9c fe ff ff    	jl     396a <barriered_thread+0x6a>
    3ace:	66 90                	xchg   %ax,%ax
  while (data->running == 1) {
    3ad0:	41 83 bc 24 a4 00 00 00 01 	cmpl   $0x1,0xa4(%r12)
    3ad9:	0f 84 49 fe ff ff    	je     3928 <barriered_thread+0x28>
}
    3adf:	5b                   	pop    %rbx
    3ae0:	31 c0                	xor    %eax,%eax
    3ae2:	5d                   	pop    %rbp
    3ae3:	41 5c                	pop    %r12
    3ae5:	41 5d                	pop    %r13
    3ae7:	41 5e                	pop    %r14
    3ae9:	c3                   	ret
    3aea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (waiting == 1) {
    3af0:	41 83 fd 01          	cmp    $0x1,%r13d
    3af4:	0f 84 c6 00 00 00    	je     3bc0 <barriered_thread+0x2c0>
        int arrived = 0; 
    3afa:	45 31 ed             	xor    %r13d,%r13d
    3afd:	e9 13 ff ff ff       	jmp    3a15 <barriered_thread+0x115>
    3b02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3b08:	49 8b b4 24 00 02 00 00 	mov    0x200(%r12),%rsi
    3b10:	49 3b b4 24 08 02 00 00 	cmp    0x208(%r12),%rsi
    3b18:	7d 8e                	jge    3aa8 <barriered_thread+0x1a8>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    3b1a:	48 c1 e6 04          	shl    $0x4,%rsi
    3b1e:	bf 04 00 00 00       	mov    $0x4,%edi
    3b23:	49 03 b4 24 a0 01 00 00 	add    0x1a0(%r12),%rsi
    3b2b:	e8 e0 e7 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3b30:	49 83 84 24 00 02 00 00 01 	addq   $0x1,0x200(%r12)
    3b39:	e9 6a ff ff ff       	jmp    3aa8 <barriered_thread+0x1a8>
    3b3e:	66 90                	xchg   %ax,%ax
            data->task_snapshot[data->task_timestamp_count].task = t;
    3b40:	49 8b 84 24 00 03 00 00 	mov    0x300(%r12),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3b48:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3b4d:	41 bd 01 00 00 00    	mov    $0x1,%r13d
            data->task_snapshot[data->task_timestamp_count].task = t;
    3b53:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3b57:	49 8b 84 24 80 02 00 00 	mov    0x280(%r12),%rax
    3b5f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3b63:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3b66:	e8 a5 e7 ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3b6b:	41 8b 94 24 a0 00 00 00 	mov    0xa0(%r12),%edx
    3b73:	e9 e0 fd ff ff       	jmp    3958 <barriered_thread+0x58>
    3b78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3b80:	48 c1 e6 04          	shl    $0x4,%rsi
    3b84:	bf 04 00 00 00       	mov    $0x4,%edi
    3b89:	49 03 b4 24 98 01 00 00 	add    0x198(%r12),%rsi
    3b91:	e8 7a e7 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3b96:	49 8b 84 24 98 00 00 00 	mov    0x98(%r12),%rax
    3b9e:	48 01 e8             	add    %rbp,%rax
    3ba1:	e9 ae fe ff ff       	jmp    3a54 <barriered_thread+0x154>
    3ba6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
    3bb0:	41 83 fd 01          	cmp    $0x1,%r13d
    3bb4:	0f 85 76 fe ff ff    	jne    3a30 <barriered_thread+0x130>
        int arrived = 0; 
    3bba:	45 31 f6             	xor    %r14d,%r14d
    3bbd:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3bc0:	49 8b 84 24 00 03 00 00 	mov    0x300(%r12),%rax
    3bc8:	bf 04 00 00 00       	mov    $0x4,%edi
    3bcd:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3bd1:	49 8b 84 24 80 02 00 00 	mov    0x280(%r12),%rax
    3bd9:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3bde:	e8 2d e7 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3be3:	49 8b 84 24 00 03 00 00 	mov    0x300(%r12),%rax
    3beb:	48 83 c0 01          	add    $0x1,%rax
    3bef:	48 99                	cqto
    3bf1:	49 f7 bc 24 08 03 00 00 	idivq  0x308(%r12)
    3bf9:	49 89 94 24 00 03 00 00 	mov    %rdx,0x300(%r12)
            waiting = 0; 
    3c01:	e9 f4 fe ff ff       	jmp    3afa <barriered_thread+0x1fa>
}
    3c06:	31 c0                	xor    %eax,%eax
    3c08:	c3                   	ret
    3c09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003c10 <external_thread>:
void * external_thread(void *arg) {
    3c10:	f3 0f 1e fa          	endbr64
    3c14:	41 55                	push   %r13
    3c16:	41 54                	push   %r12
    3c18:	55                   	push   %rbp
    3c19:	53                   	push   %rbx
    3c1a:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    3c1e:	66 0f 6f 05 1a 3d 00 00 	movdqa 0x3d1a(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
void * external_thread(void *arg) {
    3c26:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3c2f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3c34:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3c36:	83 bf a4 00 00 00 01 	cmpl   $0x1,0xa4(%rdi)
  struct timespec req = {
    3c3d:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    3c41:	75 6c                	jne    3caf <external_thread+0x9f>
    3c43:	49 89 fd             	mov    %rdi,%r13
    3c46:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3c4b:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    3c4e:	4c 8d 25 af 33 00 00 	lea    0x33af(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    3c55:	0f 1f 00             	nopl   (%rax)
    nanosleep(&req , &rem);
    3c58:	48 89 ee             	mov    %rbp,%rsi
    3c5b:	48 89 df             	mov    %rbx,%rdi
    3c5e:	e8 ed e6 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3c63:	49 8b 85 80 01 00 00 	mov    0x180(%r13),%rax
    3c6a:	48 63 10             	movslq (%rax),%rdx
    3c6d:	85 d2                	test   %edx,%edx
    3c6f:	7e 31                	jle    3ca2 <external_thread+0x92>
    3c71:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    3c78:	48 c1 e2 08          	shl    $0x8,%rdx
    3c7c:	48 01 c2             	add    %rax,%rdx
    3c7f:	90                   	nop
      if (data->buffers->buffer[x].available == 0) {
    3c80:	8b 88 80 00 00 00    	mov    0x80(%rax),%ecx
    3c86:	85 c9                	test   %ecx,%ecx
    3c88:	75 0d                	jne    3c97 <external_thread+0x87>
        data->buffers->buffer[x].data = "Hello world";
    3c8a:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    3c8d:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3c97:	48 05 00 01 00 00    	add    $0x100,%rax
    3c9d:	48 39 c2             	cmp    %rax,%rdx
    3ca0:	75 de                	jne    3c80 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    3ca2:	0f ae f0             	mfence
  while (data->running == 1) {
    3ca5:	41 83 bd a4 00 00 00 01 	cmpl   $0x1,0xa4(%r13)
    3cad:	74 a9                	je     3c58 <external_thread+0x48>
}
    3caf:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3cb4:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3cbd:	75 0d                	jne    3ccc <external_thread+0xbc>
    3cbf:	48 83 c4 38          	add    $0x38,%rsp
    3cc3:	31 c0                	xor    %eax,%eax
    3cc5:	5b                   	pop    %rbx
    3cc6:	5d                   	pop    %rbp
    3cc7:	41 5c                	pop    %r12
    3cc9:	41 5d                	pop    %r13
    3ccb:	c3                   	ret
    3ccc:	e8 5f e6 ff ff       	call   2330 <__stack_chk_fail@plt>
    3cd1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3cdc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003ce0 <timer_thread>:
void* timer_thread(void *arg) {
    3ce0:	f3 0f 1e fa          	endbr64
    3ce4:	41 57                	push   %r15
    3ce6:	48 8d 35 23 33 00 00 	lea    0x3323(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3ced:	49 89 ff             	mov    %rdi,%r15
    3cf0:	41 56                	push   %r14
    3cf2:	41 55                	push   %r13
    3cf4:	41 54                	push   %r12
    3cf6:	55                   	push   %rbp
    3cf7:	53                   	push   %rbx
    3cf8:	48 83 ec 58          	sub    $0x58,%rsp
    3cfc:	8b 17                	mov    (%rdi),%edx
    3cfe:	bf 01 00 00 00       	mov    $0x1,%edi
    3d03:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3d0c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3d11:	31 c0                	xor    %eax,%eax
    3d13:	e8 38 e7 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3d18:	66 0f 6f 05 20 3c 00 00 	movdqa 0x3c20(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3d20:	ba 88 13 00 00       	mov    $0x1388,%edx
    3d25:	31 c0                	xor    %eax,%eax
    3d27:	48 8d 35 f4 32 00 00 	lea    0x32f4(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3d2e:	bf 01 00 00 00       	mov    $0x1,%edi
    3d33:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3d38:	e8 13 e7 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3d3d:	45 8b af a4 00 00 00 	mov    0xa4(%r15),%r13d
    3d44:	45 85 ed             	test   %r13d,%r13d
    3d47:	0f 84 b3 00 00 00    	je     3e00 <timer_thread+0x120>
  int n = 0;
    3d4d:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    3d50:	45 31 ed             	xor    %r13d,%r13d
    3d53:	49 89 e4             	mov    %rsp,%r12
    y++;
    3d56:	31 db                	xor    %ebx,%ebx
    3d58:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    3d5d:	48 89 ef             	mov    %rbp,%rdi
    3d60:	4c 89 e6             	mov    %r12,%rsi
    n++;
    3d63:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3d67:	e8 e4 e5 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d6c:	49 63 87 88 00 00 00 	movslq 0x88(%r15),%rax
    y++;
    3d73:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d77:	85 c0                	test   %eax,%eax
    3d79:	7e 54                	jle    3dcf <timer_thread+0xef>
    3d7b:	49 8b 8f 80 00 00 00 	mov    0x80(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3d82:	4f 8d 44 ed 00       	lea    0x0(%r13,%r13,8),%r8
    3d87:	49 c1 e0 07          	shl    $0x7,%r8
    3d8b:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3d8f:	90                   	nop
        int next = (y + 1) % data->threads[x]->task_count;
    3d90:	4c 8b 19             	mov    (%rcx),%r11
    3d93:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d95:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3d99:	99                   	cltd
    3d9a:	41 f7 bb a0 00 00 00 	idivl  0xa0(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    3da1:	49 8b b3 98 00 00 00 	mov    0x98(%r11),%rsi
    3da8:	48 63 d2             	movslq %edx,%rdx
    3dab:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    3daf:	48 c1 e0 07          	shl    $0x7,%rax
    3db3:	c7 84 06 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rsi,%rax,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3dbe:	42 c7 84 06 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3dca:	49 39 c9             	cmp    %rcx,%r9
    3dcd:	75 c1                	jne    3d90 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    3dcf:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3dd2:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
  while (data->running && n < times) {
    3dd9:	41 8b 97 a4 00 00 00 	mov    0xa4(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3de0:	48 8b 00             	mov    (%rax),%rax
    y++;
    3de3:	39 b8 a0 00 00 00    	cmp    %edi,0xa0(%rax)
    3de9:	0f 4e fb             	cmovle %ebx,%edi
    3dec:	4c 63 ef             	movslq %edi,%r13
  while (data->running && n < times) {
    3def:	85 d2                	test   %edx,%edx
    3df1:	74 0d                	je     3e00 <timer_thread+0x120>
    3df3:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3dfa:	0f 85 5d ff ff ff    	jne    3d5d <timer_thread+0x7d>
    3e00:	48 8d 3d 31 32 00 00 	lea    0x3231(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3e07:	e8 e4 e4 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3e0c:	49 63 87 8c 00 00 00 	movslq 0x8c(%r15),%rax
    3e13:	85 c0                	test   %eax,%eax
    3e15:	0f 8e 91 00 00 00    	jle    3eac <timer_thread+0x1cc>
    for (int y = 0 ; y < data->task_count ; y++) {
    3e1b:	41 8b 97 a0 00 00 00 	mov    0xa0(%r15),%edx
    3e22:	85 d2                	test   %edx,%edx
    3e24:	0f 8e 82 00 00 00    	jle    3eac <timer_thread+0x1cc>
    3e2a:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    3e32:	48 63 c2             	movslq %edx,%rax
      data->threads[x]->tasks[y].sending = 0;
    3e35:	4d 8b 8f 80 00 00 00 	mov    0x80(%r15),%r9
    3e3c:	31 f6                	xor    %esi,%esi
    3e3e:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3e42:	48 c1 e0 07          	shl    $0x7,%rax
    3e46:	4c 8d 80 08 04 00 00 	lea    0x408(%rax),%r8
    3e4d:	49 8b 04 31          	mov    (%r9,%rsi,1),%rax
    3e51:	48 8b b8 98 00 00 00 	mov    0x98(%rax),%rdi
    3e58:	4a 8d 14 07          	lea    (%rdi,%r8,1),%rdx
    3e5c:	48 8d 87 08 04 00 00 	lea    0x408(%rdi),%rax
    3e63:	49 89 d2             	mov    %rdx,%r10
    3e66:	49 29 c2             	sub    %rax,%r10
    3e69:	41 81 e2 80 00 00 00 	and    $0x80,%r10d
    3e70:	74 16                	je     3e88 <timer_thread+0x1a8>
    for (int y = 0 ; y < data->task_count ; y++) {
    3e72:	48 8d 87 88 08 00 00 	lea    0x888(%rdi),%rax
      data->threads[x]->tasks[y].sending = 0;
    3e79:	c7 87 08 04 00 00 00 00 00 00 	movl   $0x0,0x408(%rdi)
    for (int y = 0 ; y < data->task_count ; y++) {
    3e83:	48 39 c2             	cmp    %rax,%rdx
    3e86:	74 1b                	je     3ea3 <timer_thread+0x1c3>
      data->threads[x]->tasks[y].sending = 0;
    3e88:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3e8e:	48 05 00 09 00 00    	add    $0x900,%rax
      data->threads[x]->tasks[y].sending = 0;
    3e94:	c7 80 80 fb ff ff 00 00 00 00 	movl   $0x0,-0x480(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3e9e:	48 39 c2             	cmp    %rax,%rdx
    3ea1:	75 e5                	jne    3e88 <timer_thread+0x1a8>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ea3:	48 83 c6 08          	add    $0x8,%rsi
    3ea7:	48 39 f1             	cmp    %rsi,%rcx
    3eaa:	75 a1                	jne    3e4d <timer_thread+0x16d>
  asm volatile ("mfence" ::: "memory");
    3eac:	0f ae f0             	mfence
  struct timespec drain = {
    3eaf:	66 0f 6f 05 99 3a 00 00 	movdqa 0x3a99(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3eb7:	48 8d 2d 9f 31 00 00 	lea    0x319f(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3ebe:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ec3:	49 63 87 88 00 00 00 	movslq 0x88(%r15),%rax
    y++;
    3eca:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ece:	85 c0                	test   %eax,%eax
    3ed0:	7e 5c                	jle    3f2e <timer_thread+0x24e>
    3ed2:	49 8b 8f 80 00 00 00 	mov    0x80(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3ed9:	4d 63 ed             	movslq %r13d,%r13
    3edc:	4f 8d 44 ed 00       	lea    0x0(%r13,%r13,8),%r8
    3ee1:	49 c1 e0 07          	shl    $0x7,%r8
    3ee5:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3ee9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3ef0:	48 8b 19             	mov    (%rcx),%rbx
    3ef3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ef5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3ef9:	99                   	cltd
    3efa:	f7 bb a0 00 00 00    	idivl  0xa0(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3f00:	48 8b b3 98 00 00 00 	mov    0x98(%rbx),%rsi
    3f07:	48 63 c2             	movslq %edx,%rax
    3f0a:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3f0e:	48 c1 e0 07          	shl    $0x7,%rax
    3f12:	c7 84 06 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rsi,%rax,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3f1d:	42 c7 84 06 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f29:	49 39 c9             	cmp    %rcx,%r9
    3f2c:	75 c2                	jne    3ef0 <timer_thread+0x210>
    asm volatile ("mfence" ::: "memory");
    3f2e:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3f31:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    y++;
    3f38:	45 31 ed             	xor    %r13d,%r13d
    if (y >= data->threads[0]->task_count) {
    3f3b:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3f3e:	39 ba a0 00 00 00    	cmp    %edi,0xa0(%rdx)
    3f44:	44 0f 4f ef          	cmovg  %edi,%r13d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f48:	41 8b bf 90 00 00 00 	mov    0x90(%r15),%edi
    3f4f:	85 ff                	test   %edi,%edi
    3f51:	0f 8e cc 00 00 00    	jle    4023 <timer_thread+0x343>
    3f57:	45 31 e4             	xor    %r12d,%r12d
    int all_empty = 1;
    3f5a:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3f60:	4a 8d 1c e5 00 00 00 00 	lea    0x0(,%r12,8),%rbx
            all_empty = 0;
    3f68:	45 31 f6             	xor    %r14d,%r14d
    3f6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3f70:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3f74:	4b 8d 04 f6          	lea    (%r14,%r14,8),%rax
    3f78:	48 c1 e0 07          	shl    $0x7,%rax
    3f7c:	48 03 82 98 00 00 00 	add    0x98(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3f83:	31 d2                	xor    %edx,%edx
    3f85:	48 8b 80 88 03 00 00 	mov    0x388(%rax),%rax
    3f8c:	eb 14                	jmp    3fa2 <timer_thread+0x2c2>
    3f8e:	66 90                	xchg   %ax,%ax
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3f90:	4d 85 c0             	test   %r8,%r8
    3f93:	7f 2a                	jg     3fbf <timer_thread+0x2df>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3f95:	83 c2 01             	add    $0x1,%edx
    3f98:	48 05 00 02 00 00    	add    $0x200,%rax
    3f9e:	39 fa                	cmp    %edi,%edx
    3fa0:	74 36                	je     3fd8 <timer_thread+0x2f8>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3fa2:	48 8b 08             	mov    (%rax),%rcx
    3fa5:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    3fac:	48 8b 89 80 00 00 00 	mov    0x80(%rcx),%rcx
    3fb3:	4c 8b 86 80 00 00 00 	mov    0x80(%rsi),%r8
    3fba:	48 85 c9             	test   %rcx,%rcx
    3fbd:	7e d1                	jle    3f90 <timer_thread+0x2b0>
    3fbf:	bf 01 00 00 00       	mov    $0x1,%edi
    3fc4:	48 89 ee             	mov    %rbp,%rsi
    3fc7:	31 c0                	xor    %eax,%eax
    3fc9:	e8 82 e4 ff ff       	call   2450 <__printf_chk@plt>
            break;
    3fce:	41 8b bf 90 00 00 00 	mov    0x90(%r15),%edi
            all_empty = 0;
    3fd5:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3fd8:	49 83 c6 01          	add    $0x1,%r14
    3fdc:	44 39 f7             	cmp    %r14d,%edi
    3fdf:	7e 0f                	jle    3ff0 <timer_thread+0x310>
    3fe1:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    3fe8:	eb 86                	jmp    3f70 <timer_thread+0x290>
    3fea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3ff0:	49 83 c4 01          	add    $0x1,%r12
    3ff4:	44 39 e7             	cmp    %r12d,%edi
    3ff7:	7e 10                	jle    4009 <timer_thread+0x329>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3ff9:	85 ff                	test   %edi,%edi
    3ffb:	7e 0c                	jle    4009 <timer_thread+0x329>
    3ffd:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    4004:	e9 57 ff ff ff       	jmp    3f60 <timer_thread+0x280>
    if (all_empty == 1) {
    4009:	41 83 f9 01          	cmp    $0x1,%r9d
    400d:	74 14                	je     4023 <timer_thread+0x343>
      nanosleep(&drain , &drainrem);
    400f:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4014:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4019:	e8 32 e3 ff ff       	call   2350 <nanosleep@plt>
    401e:	e9 a0 fe ff ff       	jmp    3ec3 <timer_thread+0x1e3>
    4023:	48 8d 3d 2a 30 00 00 	lea    0x302a(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    402a:	e8 c1 e2 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    402f:	41 8b 87 a4 00 00 00 	mov    0xa4(%r15),%eax
    4036:	85 c0                	test   %eax,%eax
    4038:	0f 84 08 01 00 00    	je     4146 <timer_thread+0x466>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    403e:	41 8b 8f 8c 00 00 00 	mov    0x8c(%r15),%ecx
    4045:	85 c9                	test   %ecx,%ecx
    4047:	7e 37                	jle    4080 <timer_thread+0x3a0>
    4049:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    4050:	31 db                	xor    %ebx,%ebx
    4052:	48 8d 2d 15 30 00 00 	lea    0x3015(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    4059:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->threads[x]->running = 0;
    4060:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
    4064:	c7 82 a4 00 00 00 00 00 00 00 	movl   $0x0,0xa4(%rdx)
      if (data->threads[x]->type == IO) {
    406e:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
    4072:	0f 84 fb 00 00 00    	je     4173 <timer_thread+0x493>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4078:	48 83 c3 01          	add    $0x1,%rbx
    407c:	39 d9                	cmp    %ebx,%ecx
    407e:	7f e0                	jg     4060 <timer_thread+0x380>
    for (int x = 0 ; x < data->thread_count ; x++) {
    4080:	49 63 87 88 00 00 00 	movslq 0x88(%r15),%rax
    4087:	85 c0                	test   %eax,%eax
    4089:	0f 8e 9d 00 00 00    	jle    412c <timer_thread+0x44c>
      for (int y = 0 ; y < data->task_count ; y++) {
    408f:	41 8b 97 a0 00 00 00 	mov    0xa0(%r15),%edx
    4096:	85 d2                	test   %edx,%edx
    4098:	0f 8e 8e 00 00 00    	jle    412c <timer_thread+0x44c>
    409e:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
    40a6:	48 63 c2             	movslq %edx,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    40a9:	4d 8b 97 80 00 00 00 	mov    0x80(%r15),%r10
    40b0:	31 c9                	xor    %ecx,%ecx
    40b2:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    40b6:	48 c1 e0 07          	shl    $0x7,%rax
    40ba:	4c 8d 88 80 02 00 00 	lea    0x280(%rax),%r9
    40c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    40c8:	49 8b 04 0a          	mov    (%r10,%rcx,1),%rax
    40cc:	48 8b b0 98 00 00 00 	mov    0x98(%rax),%rsi
    40d3:	4a 8d 14 0e          	lea    (%rsi,%r9,1),%rdx
    40d7:	48 8d 86 80 02 00 00 	lea    0x280(%rsi),%rax
    40de:	48 89 d7             	mov    %rdx,%rdi
    40e1:	48 29 c7             	sub    %rax,%rdi
    40e4:	81 e7 80 00 00 00    	and    $0x80,%edi
    40ea:	74 1c                	je     4108 <timer_thread+0x428>
      for (int y = 0 ; y < data->task_count ; y++) {
    40ec:	48 8d 86 00 07 00 00 	lea    0x700(%rsi),%rax
        data->threads[x]->tasks[y].scheduled = 0;
    40f3:	c7 86 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rsi)
      for (int y = 0 ; y < data->task_count ; y++) {
    40fd:	48 39 d0             	cmp    %rdx,%rax
    4100:	74 21                	je     4123 <timer_thread+0x443>
    4102:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4108:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    410e:	48 05 00 09 00 00    	add    $0x900,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4114:	c7 80 80 fb ff ff 00 00 00 00 	movl   $0x0,-0x480(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    411e:	48 39 d0             	cmp    %rdx,%rax
    4121:	75 e5                	jne    4108 <timer_thread+0x428>
    for (int x = 0 ; x < data->thread_count ; x++) {
    4123:	48 83 c1 08          	add    $0x8,%rcx
    4127:	4c 39 c1             	cmp    %r8,%rcx
    412a:	75 9c                	jne    40c8 <timer_thread+0x3e8>
    asm volatile ("mfence" ::: "memory");
    412c:	0f ae f0             	mfence
    412f:	48 8d 3d 4a 2f 00 00 	lea    0x2f4a(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    4136:	e8 b5 e1 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    413b:	41 c7 87 a4 00 00 00 00 00 00 00 	movl   $0x0,0xa4(%r15)
    4146:	48 8d 3d 3a 2f 00 00 	lea    0x2f3a(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    414d:	e8 9e e1 ff ff       	call   22f0 <puts@plt>
}
    4152:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    4157:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4160:	75 53                	jne    41b5 <timer_thread+0x4d5>
    4162:	48 83 c4 58          	add    $0x58,%rsp
    4166:	31 c0                	xor    %eax,%eax
    4168:	5b                   	pop    %rbx
    4169:	5d                   	pop    %rbp
    416a:	41 5c                	pop    %r12
    416c:	41 5d                	pop    %r13
    416e:	41 5e                	pop    %r14
    4170:	41 5f                	pop    %r15
    4172:	c3                   	ret
    4173:	48 89 ef             	mov    %rbp,%rdi
    4176:	e8 75 e1 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    417b:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    4182:	be 01 00 00 00       	mov    $0x1,%esi
    4187:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    418b:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    418f:	8b b8 90 01 00 00    	mov    0x190(%rax),%edi
    4195:	e8 66 e2 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    419a:	41 8b 8f 8c 00 00 00 	mov    0x8c(%r15),%ecx
    41a1:	39 d9                	cmp    %ebx,%ecx
    41a3:	0f 8e d7 fe ff ff    	jle    4080 <timer_thread+0x3a0>
    41a9:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    41b0:	e9 ab fe ff ff       	jmp    4060 <timer_thread+0x380>
}
    41b5:	e8 76 e1 ff ff       	call   2330 <__stack_chk_fail@plt>
    41ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000041c0 <strtolower>:
void strtolower(char *str) {
    41c0:	f3 0f 1e fa          	endbr64
    41c4:	55                   	push   %rbp
    41c5:	53                   	push   %rbx
    41c6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    41ca:	48 0f be 1f          	movsbq (%rdi),%rbx
    41ce:	84 db                	test   %bl,%bl
    41d0:	74 24                	je     41f6 <strtolower+0x36>
    41d2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    41d5:	e8 36 e3 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    41da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    41e0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    41e3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    41e7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    41ea:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    41ed:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    41f2:	84 db                	test   %bl,%bl
    41f4:	75 ea                	jne    41e0 <strtolower+0x20>
}
    41f6:	48 83 c4 08          	add    $0x8,%rsp
    41fa:	5b                   	pop    %rbx
    41fb:	5d                   	pop    %rbp
    41fc:	c3                   	ret
    41fd:	0f 1f 00             	nopl   (%rax)

0000000000004200 <zh_malloc>:
void *zh_malloc(size_t size) {
    4200:	f3 0f 1e fa          	endbr64
    4204:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4208:	e8 03 e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    420d:	48 85 c0             	test   %rax,%rax
    4210:	74 05                	je     4217 <zh_malloc+0x17>
}
    4212:	48 83 c4 08          	add    $0x8,%rsp
    4216:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4217:	48 8b 0d 02 5e 00 00 	mov    0x5e02(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    421e:	ba 28 00 00 00       	mov    $0x28,%edx
    4223:	be 01 00 00 00       	mov    $0x1,%esi
    4228:	48 8d 3d d9 31 00 00 	lea    0x31d9(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    422f:	e8 8c e2 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4234:	bf 01 00 00 00       	mov    $0x1,%edi
    4239:	e8 62 e2 ff ff       	call   24a0 <exit@plt>
    423e:	66 90                	xchg   %ax,%ax

0000000000004240 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4240:	f3 0f 1e fa          	endbr64
    4244:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4245:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    424a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    424d:	e8 0e e1 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4252:	48 85 c0             	test   %rax,%rax
    4255:	74 11                	je     4268 <get_filename_ext+0x28>
    4257:	48 39 c3             	cmp    %rax,%rbx
    425a:	74 0c                	je     4268 <get_filename_ext+0x28>
    return dot + 1;
    425c:	48 83 c0 01          	add    $0x1,%rax
}
    4260:	5b                   	pop    %rbx
    4261:	c3                   	ret
    4262:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4268:	48 8d 05 60 2e 00 00 	lea    0x2e60(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    426f:	5b                   	pop    %rbx
    4270:	c3                   	ret
    4271:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    427c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004280 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4280:	f3 0f 1e fa          	endbr64
    4284:	41 55                	push   %r13
    4286:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4289:	48 89 fe             	mov    %rdi,%rsi
    428c:	41 54                	push   %r12
    428e:	55                   	push   %rbp
    428f:	48 89 d5             	mov    %rdx,%rbp
    4292:	ba 00 04 00 00       	mov    $0x400,%edx
    4297:	53                   	push   %rbx
    4298:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    429f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    42a8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    42b0:	31 c0                	xor    %eax,%eax
    42b2:	49 89 e4             	mov    %rsp,%r12
    42b5:	4c 89 e7             	mov    %r12,%rdi
    42b8:	e8 73 e1 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    42bd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    42c2:	84 db                	test   %bl,%bl
    42c4:	74 24                	je     42ea <send_headers+0x6a>
        *str = (char)tolower(*str);
    42c6:	e8 45 e2 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    42cb:	48 8b 08             	mov    (%rax),%rcx
    42ce:	4c 89 e0             	mov    %r12,%rax
    42d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    42d8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    42db:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    42df:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    42e2:	48 0f be 18          	movsbq (%rax),%rbx
    42e6:	84 db                	test   %bl,%bl
    42e8:	75 ee                	jne    42d8 <send_headers+0x58>
    void *buf = malloc(size);
    42ea:	bf 11 00 00 00       	mov    $0x11,%edi
    42ef:	e8 1c e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    42f4:	48 85 c0             	test   %rax,%rax
    42f7:	0f 84 7e 04 00 00    	je     477b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    42fd:	66 0f 6f 05 5b 36 00 00 	movdqa 0x365b(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    4305:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4309:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    430e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4316:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    431a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    431d:	e8 ee e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4322:	48 85 c0             	test   %rax,%rax
    4325:	0f 84 50 04 00 00    	je     477b <send_headers+0x4fb>
    432b:	66 0f 6f 05 3d 36 00 00 	movdqa 0x363d(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    4333:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4337:	4c 89 e7             	mov    %r12,%rdi
    433a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4344:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    434c:	0f 11 00             	movups %xmm0,(%rax)
    434f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4353:	be 2e 00 00 00       	mov    $0x2e,%esi
    4358:	e8 03 e0 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    435d:	48 85 c0             	test   %rax,%rax
    4360:	0f 84 ea 02 00 00    	je     4650 <send_headers+0x3d0>
    4366:	4c 39 e0             	cmp    %r12,%rax
    4369:	0f 84 e1 02 00 00    	je     4650 <send_headers+0x3d0>
    return dot + 1;
    436f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4373:	48 8d 3d 23 2d 00 00 	lea    0x2d23(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    437a:	48 89 de             	mov    %rbx,%rsi
    437d:	e8 2e e0 ff ff       	call   23b0 <strcmp@plt>
    4382:	85 c0                	test   %eax,%eax
    4384:	75 20                	jne    43a6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4386:	66 0f 6f 05 f2 35 00 00 	movdqa 0x35f2(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    438e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4396:	66 0f 6f 05 f2 35 00 00 	movdqa 0x35f2(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    439e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    43a6:	48 89 de             	mov    %rbx,%rsi
    43a9:	48 8d 3d f1 2c 00 00 	lea    0x2cf1(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    43b0:	e8 fb df ff ff       	call   23b0 <strcmp@plt>
    43b5:	85 c0                	test   %eax,%eax
    43b7:	75 20                	jne    43d9 <send_headers+0x159>
    43b9:	66 0f 6f 05 bf 35 00 00 	movdqa 0x35bf(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    43c1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    43c9:	66 0f 6f 05 bf 35 00 00 	movdqa 0x35bf(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    43d1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    43d9:	48 89 de             	mov    %rbx,%rsi
    43dc:	48 8d 3d c3 2c 00 00 	lea    0x2cc3(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    43e3:	e8 c8 df ff ff       	call   23b0 <strcmp@plt>
    43e8:	85 c0                	test   %eax,%eax
    43ea:	0f 84 10 02 00 00    	je     4600 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    43f0:	48 89 de             	mov    %rbx,%rsi
    43f3:	48 8d 3d b0 2c 00 00 	lea    0x2cb0(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    43fa:	e8 b1 df ff ff       	call   23b0 <strcmp@plt>
    43ff:	85 c0                	test   %eax,%eax
    4401:	0f 84 a9 02 00 00    	je     46b0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4407:	48 89 de             	mov    %rbx,%rsi
    440a:	48 8d 3d 9d 2c 00 00 	lea    0x2c9d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4411:	e8 9a df ff ff       	call   23b0 <strcmp@plt>
    4416:	85 c0                	test   %eax,%eax
    4418:	0f 84 6a 02 00 00    	je     4688 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    441e:	48 89 de             	mov    %rbx,%rsi
    4421:	48 8d 3d c9 2c 00 00 	lea    0x2cc9(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4428:	e8 83 df ff ff       	call   23b0 <strcmp@plt>
    442d:	85 c0                	test   %eax,%eax
    442f:	0f 84 2b 02 00 00    	je     4660 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4435:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4438:	0f 84 52 01 00 00    	je     4590 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    443e:	48 89 de             	mov    %rbx,%rsi
    4441:	48 8d 3d 6a 2c 00 00 	lea    0x2c6a(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    4448:	e8 63 df ff ff       	call   23b0 <strcmp@plt>
    444d:	85 c0                	test   %eax,%eax
    444f:	0f 84 ab 02 00 00    	je     4700 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4455:	48 89 de             	mov    %rbx,%rsi
    4458:	48 8d 3d 57 2c 00 00 	lea    0x2c57(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    445f:	e8 4c df ff ff       	call   23b0 <strcmp@plt>
    4464:	85 c0                	test   %eax,%eax
    4466:	0f 84 6c 02 00 00    	je     46d8 <send_headers+0x458>
    slen = strlen(send_buffer);
    446c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4474:	4c 89 e7             	mov    %r12,%rdi
    4477:	e8 a4 de ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    447c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    447f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4482:	e8 89 df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4487:	48 85 c0             	test   %rax,%rax
    448a:	0f 84 eb 02 00 00    	je     477b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4490:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4494:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4498:	83 fb 08             	cmp    $0x8,%ebx
    449b:	0f 83 3f 01 00 00    	jae    45e0 <send_headers+0x360>
    44a1:	f6 c3 04             	test   $0x4,%bl
    44a4:	0f 85 7b 02 00 00    	jne    4725 <send_headers+0x4a5>
    44aa:	85 db                	test   %ebx,%ebx
    44ac:	74 13                	je     44c1 <send_headers+0x241>
    44ae:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    44b6:	88 10                	mov    %dl,(%rax)
    44b8:	f6 c3 02             	test   $0x2,%bl
    44bb:	0f 85 96 02 00 00    	jne    4757 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    44c1:	4d 89 e8             	mov    %r13,%r8
    44c4:	48 8d 0d ef 2b 00 00 	lea    0x2bef(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    44cb:	4c 89 e7             	mov    %r12,%rdi
    44ce:	31 c0                	xor    %eax,%eax
    44d0:	ba 00 04 00 00       	mov    $0x400,%edx
    44d5:	be 01 00 00 00       	mov    $0x1,%esi
    44da:	e8 41 e0 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    44df:	4c 89 e7             	mov    %r12,%rdi
    44e2:	e8 39 de ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    44e7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    44ea:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    44ed:	e8 1e df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    44f2:	48 85 c0             	test   %rax,%rax
    44f5:	0f 84 80 02 00 00    	je     477b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    44fb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    44ff:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4503:	83 fb 08             	cmp    $0x8,%ebx
    4506:	0f 83 1c 01 00 00    	jae    4628 <send_headers+0x3a8>
    450c:	f6 c3 04             	test   $0x4,%bl
    450f:	0f 85 29 02 00 00    	jne    473e <send_headers+0x4be>
    4515:	85 db                	test   %ebx,%ebx
    4517:	74 13                	je     452c <send_headers+0x2ac>
    4519:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4521:	88 10                	mov    %dl,(%rax)
    4523:	f6 c3 02             	test   $0x2,%bl
    4526:	0f 85 3d 02 00 00    	jne    4769 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    452c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4531:	bf 02 00 00 00       	mov    $0x2,%edi
    4536:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    453e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4546:	e8 c5 de ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    454b:	48 85 c0             	test   %rax,%rax
    454e:	0f 84 27 02 00 00    	je     477b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4554:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    455c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4560:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4568:	66 89 10             	mov    %dx,(%rax)
}
    456b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4573:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    457c:	0f 85 20 02 00 00    	jne    47a2 <send_headers+0x522>
    4582:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4589:	5b                   	pop    %rbx
    458a:	5d                   	pop    %rbp
    458b:	41 5c                	pop    %r12
    458d:	41 5d                	pop    %r13
    458f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4590:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4594:	0f 85 a4 fe ff ff    	jne    443e <send_headers+0x1be>
    459a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    459e:	0f 85 9a fe ff ff    	jne    443e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    45a4:	66 0f 6f 05 34 34 00 00 	movdqa 0x3434(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    45ac:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    45b6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    45be:	66 0f 6f 05 2a 34 00 00 	movdqa 0x342a(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    45c6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    45ce:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    45d6:	e9 63 fe ff ff       	jmp    443e <send_headers+0x1be>
    45db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    45e0:	89 da                	mov    %ebx,%edx
    45e2:	48 89 c7             	mov    %rax,%rdi
    45e5:	4c 89 e6             	mov    %r12,%rsi
    45e8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    45ed:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    45f2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    45f5:	c1 e9 03             	shr    $0x3,%ecx
    45f8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    45fb:	e9 c1 fe ff ff       	jmp    44c1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4600:	66 0f 6f 05 78 33 00 00 	movdqa 0x3378(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4608:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4610:	66 0f 6f 05 88 33 00 00 	movdqa 0x3388(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4618:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4620:	e9 cb fd ff ff       	jmp    43f0 <send_headers+0x170>
    4625:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4628:	89 da                	mov    %ebx,%edx
    462a:	48 89 c7             	mov    %rax,%rdi
    462d:	4c 89 e6             	mov    %r12,%rsi
    4630:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4635:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    463a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    463d:	c1 e9 03             	shr    $0x3,%ecx
    4640:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4643:	e9 e4 fe ff ff       	jmp    452c <send_headers+0x2ac>
    4648:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4650:	48 8d 1d 78 2a 00 00 	lea    0x2a78(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4657:	e9 94 fd ff ff       	jmp    43f0 <send_headers+0x170>
    465c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4660:	66 0f 6f 05 58 33 00 00 	movdqa 0x3358(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4668:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4670:	66 0f 6f 05 58 33 00 00 	movdqa 0x3358(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4678:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4680:	e9 b0 fd ff ff       	jmp    4435 <send_headers+0x1b5>
    4685:	0f 1f 00             	nopl   (%rax)
    4688:	66 0f 6f 05 30 33 00 00 	movdqa 0x3330(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4690:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4698:	66 0f 6f 05 30 33 00 00 	movdqa 0x3330(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    46a0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    46a8:	e9 71 fd ff ff       	jmp    441e <send_headers+0x19e>
    46ad:	0f 1f 00             	nopl   (%rax)
    46b0:	66 0f 6f 05 c8 32 00 00 	movdqa 0x32c8(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    46b8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    46c0:	66 0f 6f 05 e8 32 00 00 	movdqa 0x32e8(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    46c8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    46d0:	e9 32 fd ff ff       	jmp    4407 <send_headers+0x187>
    46d5:	0f 1f 00             	nopl   (%rax)
    46d8:	66 0f 6f 05 e0 32 00 00 	movdqa 0x32e0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    46e0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    46e8:	66 0f 6f 05 20 33 00 00 	movdqa 0x3320(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    46f0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    46f8:	e9 6f fd ff ff       	jmp    446c <send_headers+0x1ec>
    46fd:	0f 1f 00             	nopl   (%rax)
    4700:	66 0f 6f 05 b8 32 00 00 	movdqa 0x32b8(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4708:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4710:	66 0f 6f 05 e8 32 00 00 	movdqa 0x32e8(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4718:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4720:	e9 30 fd ff ff       	jmp    4455 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4725:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    472c:	89 db                	mov    %ebx,%ebx
    472e:	89 10                	mov    %edx,(%rax)
    4730:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4735:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4739:	e9 83 fd ff ff       	jmp    44c1 <send_headers+0x241>
    473e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4745:	89 db                	mov    %ebx,%ebx
    4747:	89 10                	mov    %edx,(%rax)
    4749:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    474e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4752:	e9 d5 fd ff ff       	jmp    452c <send_headers+0x2ac>
    4757:	89 db                	mov    %ebx,%ebx
    4759:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    475f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4764:	e9 58 fd ff ff       	jmp    44c1 <send_headers+0x241>
    4769:	89 db                	mov    %ebx,%ebx
    476b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4771:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4776:	e9 b1 fd ff ff       	jmp    452c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    477b:	48 8b 0d 9e 58 00 00 	mov    0x589e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4782:	ba 28 00 00 00       	mov    $0x28,%edx
    4787:	be 01 00 00 00       	mov    $0x1,%esi
    478c:	48 8d 3d 75 2c 00 00 	lea    0x2c75(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4793:	e8 28 dd ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4798:	bf 01 00 00 00       	mov    $0x1,%edi
    479d:	e8 fe dc ff ff       	call   24a0 <exit@plt>
}
    47a2:	e8 89 db ff ff       	call   2330 <__stack_chk_fail@plt>
    47a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000047b0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    47b0:	f3 0f 1e fa          	endbr64
    47b4:	41 55                	push   %r13
    47b6:	49 89 d5             	mov    %rdx,%r13
    47b9:	41 54                	push   %r12
    47bb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    47be:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    47c1:	55                   	push   %rbp
    47c2:	53                   	push   %rbx
    47c3:	48 89 f3             	mov    %rsi,%rbx
    47c6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    47ca:	e8 41 dc ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    47cf:	48 85 c0             	test   %rax,%rax
    47d2:	74 6b                	je     483f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    47d4:	4c 89 e7             	mov    %r12,%rdi
    47d7:	48 89 c5             	mov    %rax,%rbp
    47da:	31 f6                	xor    %esi,%esi
    47dc:	31 c0                	xor    %eax,%eax
    47de:	e8 9d dc ff ff       	call   2480 <open@plt>
    47e3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    47e6:	85 c0                	test   %eax,%eax
    47e8:	0f 88 68 dd ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    47ee:	48 89 da             	mov    %rbx,%rdx
    47f1:	48 89 ee             	mov    %rbp,%rsi
    47f4:	89 c7                	mov    %eax,%edi
    47f6:	e8 95 db ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    47fb:	48 98                	cltq
    47fd:	48 39 d8             	cmp    %rbx,%rax
    4800:	7c 1e                	jl     4820 <copy_file_contents+0x70>
    close(fd);
    4802:	44 89 e7             	mov    %r12d,%edi
    4805:	e8 66 db ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    480a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    480e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4812:	48 83 c4 08          	add    $0x8,%rsp
    4816:	5b                   	pop    %rbx
    4817:	5d                   	pop    %rbp
    4818:	41 5c                	pop    %r12
    481a:	41 5d                	pop    %r13
    481c:	c3                   	ret
    481d:	0f 1f 00             	nopl   (%rax)
    4820:	48 8b 0d f9 57 00 00 	mov    0x57f9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4827:	ba 1a 00 00 00       	mov    $0x1a,%edx
    482c:	be 01 00 00 00       	mov    $0x1,%esi
    4831:	48 8d 3d 98 28 00 00 	lea    0x2898(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    4838:	e8 83 dc ff ff       	call   24c0 <fwrite@plt>
    483d:	eb c3                	jmp    4802 <copy_file_contents+0x52>
    483f:	48 8b 0d da 57 00 00 	mov    0x57da(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4846:	ba 28 00 00 00       	mov    $0x28,%edx
    484b:	be 01 00 00 00       	mov    $0x1,%esi
    4850:	48 8d 3d b1 2b 00 00 	lea    0x2bb1(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4857:	e8 64 dc ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    485c:	bf 01 00 00 00       	mov    $0x1,%edi
    4861:	e8 3a dc ff ff       	call   24a0 <exit@plt>
    4866:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004870 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4870:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4874:	8b 46 44             	mov    0x44(%rsi),%eax
    4877:	48 89 fa             	mov    %rdi,%rdx
    487a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    487d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4883:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4886:	48 8b 07             	mov    (%rdi),%rax
    4889:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    488c:	f6 c1 02             	test   $0x2,%cl
    488f:	74 00                	je     4891 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4891:	89 f0                	mov    %esi,%eax
    4893:	44 29 c0             	sub    %r8d,%eax
    4896:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4899:	0f 82 c3 dc ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    489f:	c1 e9 0a             	shr    $0xa,%ecx
    48a2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    48a6:	8b 47 44             	mov    0x44(%rdi),%eax
    48a9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    48ac:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    48af:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    48b2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    48b5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    48b9:	d3 e0                	shl    %cl,%eax
    48bb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    48be:	48 c1 e0 06          	shl    $0x6,%rax
    48c2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    48c6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    48cc:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    48cf:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    48d3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    48d9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    48e1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    48e5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    48e8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    48ef:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    48f7:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    48fb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    48ff:	e8 3c da ff ff       	call   2340 <io_uring_submit@plt>
}
    4904:	31 c0                	xor    %eax,%eax
    4906:	48 83 c4 08          	add    $0x8,%rsp
    490a:	c3                   	ret
    490b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004910 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4910:	f3 0f 1e fa          	endbr64
    4914:	41 55                	push   %r13
    4916:	41 89 fd             	mov    %edi,%r13d
    4919:	41 54                	push   %r12
    491b:	55                   	push   %rbp
    491c:	53                   	push   %rbx
    491d:	48 89 f3             	mov    %rsi,%rbx
    4920:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4924:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4927:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    492d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4930:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4933:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4935:	f6 c1 02             	test   $0x2,%cl
    4938:	74 00                	je     493a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    493a:	89 c2                	mov    %eax,%edx
    493c:	29 f2                	sub    %esi,%edx
    493e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4941:	0f 82 2b dc ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4947:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    494a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    494d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4950:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4955:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4958:	23 6b 58             	and    0x58(%rbx),%ebp
    495b:	d3 e5                	shl    %cl,%ebp
    495d:	48 c1 e5 06          	shl    $0x6,%rbp
    4961:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4965:	e8 a6 da ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    496a:	be 01 00 00 00       	mov    $0x1,%esi
    496f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4974:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4977:	e8 24 da ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    497c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4981:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4985:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4988:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    498d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4992:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    499b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    49a3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    49a7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    49ab:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    49b2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    49ba:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    49be:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    49c6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    49ce:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    49d2:	e8 69 d9 ff ff       	call   2340 <io_uring_submit@plt>
}
    49d7:	48 83 c4 08          	add    $0x8,%rsp
    49db:	31 c0                	xor    %eax,%eax
    49dd:	5b                   	pop    %rbx
    49de:	5d                   	pop    %rbp
    49df:	41 5c                	pop    %r12
    49e1:	41 5d                	pop    %r13
    49e3:	c3                   	ret
    49e4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    49ef:	90                   	nop

00000000000049f0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    49f0:	f3 0f 1e fa          	endbr64
    49f4:	41 56                	push   %r14
    49f6:	41 89 f6             	mov    %esi,%r14d
    49f9:	41 55                	push   %r13
    49fb:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    49fe:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4a03:	41 54                	push   %r12
    4a05:	55                   	push   %rbp
    4a06:	48 89 d5             	mov    %rdx,%rbp
    4a09:	53                   	push   %rbx
    void *buf = malloc(size);
    4a0a:	e8 01 da ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4a0f:	48 85 c0             	test   %rax,%rax
    4a12:	0f 84 dd 00 00 00    	je     4af5 <_send_static_string_content+0x105>
    4a18:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    4a1b:	4c 89 ef             	mov    %r13,%rdi
    4a1e:	e8 fd d8 ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4a23:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    4a2a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    4a2e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4a31:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4a34:	e8 d7 d9 ff ff       	call   2410 <malloc@plt>
    4a39:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    4a3c:	48 85 c0             	test   %rax,%rax
    4a3f:	0f 84 b0 00 00 00    	je     4af5 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4a45:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4a49:	4c 89 e2             	mov    %r12,%rdx
    4a4c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    4a4f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4a53:	e8 88 d9 ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4a58:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4a5b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4a61:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4a64:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4a68:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4a6a:	f6 c1 02             	test   $0x2,%cl
    4a6d:	0f 85 7d 00 00 00    	jne    4af0 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4a73:	89 d0                	mov    %edx,%eax
    4a75:	29 f0                	sub    %esi,%eax
    4a77:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    4a7a:	0f 82 fc da ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4a80:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4a83:	8b 45 44             	mov    0x44(%rbp),%eax
    4a86:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4a89:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    4a8c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4a8f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4a92:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4a98:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4a9c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4a9e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4aa1:	48 89 ef             	mov    %rbp,%rdi
    4aa4:	48 c1 e0 06          	shl    $0x6,%rax
    4aa8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    4aac:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4aaf:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4ab3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4ab9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4ac1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4ac5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4ac8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4acf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4ad7:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    4adb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    4adf:	5b                   	pop    %rbx
    4ae0:	5d                   	pop    %rbp
    4ae1:	41 5c                	pop    %r12
    4ae3:	41 5d                	pop    %r13
    4ae5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4ae7:	e9 54 d8 ff ff       	jmp    2340 <io_uring_submit@plt>
    4aec:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4af0:	e9 7e ff ff ff       	jmp    4a73 <_send_static_string_content+0x83>
    4af5:	48 8b 0d 24 55 00 00 	mov    0x5524(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4afc:	ba 28 00 00 00       	mov    $0x28,%edx
    4b01:	be 01 00 00 00       	mov    $0x1,%esi
    4b06:	48 8d 3d fb 28 00 00 	lea    0x28fb(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4b0d:	e8 ae d9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4b12:	bf 01 00 00 00       	mov    $0x1,%edi
    4b17:	e8 84 d9 ff ff       	call   24a0 <exit@plt>
    4b1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004b20 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4b20:	f3 0f 1e fa          	endbr64
    4b24:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4b27:	89 fe                	mov    %edi,%esi
    4b29:	48 8b 3d e8 54 00 00 	mov    0x54e8(%rip),%rdi        # a018 <unimplemented_content>
    4b30:	e9 bb fe ff ff       	jmp    49f0 <_send_static_string_content>
    4b35:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004b40 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4b40:	f3 0f 1e fa          	endbr64
    4b44:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4b47:	89 fe                	mov    %edi,%esi
    4b49:	48 8b 3d c0 54 00 00 	mov    0x54c0(%rip),%rdi        # a010 <http_404_content>
    4b50:	e9 9b fe ff ff       	jmp    49f0 <_send_static_string_content>
    4b55:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004b60 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4b60:	f3 0f 1e fa          	endbr64
    4b64:	41 56                	push   %r14
    4b66:	41 55                	push   %r13
    4b68:	49 89 d5             	mov    %rdx,%r13
    4b6b:	41 54                	push   %r12
    4b6d:	41 89 f4             	mov    %esi,%r12d
    4b70:	55                   	push   %rbp
    4b71:	48 89 fd             	mov    %rdi,%rbp
    4b74:	53                   	push   %rbx
    4b75:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    4b7c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b85:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    4b8d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    4b8f:	e8 8c d7 ff ff       	call   2320 <strlen@plt>
    4b94:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4b99:	48 89 c3             	mov    %rax,%rbx
    4b9c:	0f 84 b6 00 00 00    	je     4c58 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ba2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4ba7:	48 89 ee             	mov    %rbp,%rsi
    4baa:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4bae:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4bb3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4bbb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4bc3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4bce:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4bd6:	e8 e5 d7 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4bdb:	48 89 e6             	mov    %rsp,%rsi
    4bde:	4c 89 f7             	mov    %r14,%rdi
    4be1:	e8 ea d7 ff ff       	call   23d0 <stat@plt>
    4be6:	83 f8 ff             	cmp    $0xffffffff,%eax
    4be9:	0f 84 d3 00 00 00    	je     4cc2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    4bef:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4bf3:	25 00 f0 00 00       	and    $0xf000,%eax
    4bf8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4bfd:	0f 84 f5 00 00 00    	je     4cf8 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4c03:	48 8b 3d 06 54 00 00 	mov    0x5406(%rip),%rdi        # a010 <http_404_content>
    4c0a:	4c 89 ea             	mov    %r13,%rdx
    4c0d:	44 89 e6             	mov    %r12d,%esi
    4c10:	e8 db fd ff ff       	call   49f0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4c15:	4c 89 f2             	mov    %r14,%rdx
    4c18:	bf 01 00 00 00       	mov    $0x1,%edi
    4c1d:	31 c0                	xor    %eax,%eax
    4c1f:	48 8d 35 fa 24 00 00 	lea    0x24fa(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    4c26:	e8 25 d8 ff ff       	call   2450 <__printf_chk@plt>
}
    4c2b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4c33:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4c3c:	0f 85 20 01 00 00    	jne    4d62 <handle_get_method+0x202>
    4c42:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4c49:	5b                   	pop    %rbx
    4c4a:	5d                   	pop    %rbp
    4c4b:	41 5c                	pop    %r12
    4c4d:	41 5d                	pop    %r13
    4c4f:	41 5e                	pop    %r14
    4c51:	c3                   	ret
    4c52:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4c58:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4c5d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4c65:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4c6a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4c6d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4c75:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4c78:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4c80:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4c8b:	e8 30 d7 ff ff       	call   23c0 <__memcpy_chk@plt>
    4c90:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4c95:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4c9a:	48 8d 35 4a 24 00 00 	lea    0x244a(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4ca1:	48 29 d9             	sub    %rbx,%rcx
    4ca4:	ba 0b 00 00 00       	mov    $0xb,%edx
    4ca9:	e8 12 d7 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4cae:	48 89 e6             	mov    %rsp,%rsi
    4cb1:	4c 89 f7             	mov    %r14,%rdi
    4cb4:	e8 17 d7 ff ff       	call   23d0 <stat@plt>
    4cb9:	83 f8 ff             	cmp    $0xffffffff,%eax
    4cbc:	0f 85 2d ff ff ff    	jne    4bef <handle_get_method+0x8f>
    4cc2:	4c 89 f2             	mov    %r14,%rdx
    4cc5:	48 89 e9             	mov    %rbp,%rcx
    4cc8:	48 8d 35 27 24 00 00 	lea    0x2427(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    4ccf:	31 c0                	xor    %eax,%eax
    4cd1:	bf 01 00 00 00       	mov    $0x1,%edi
    4cd6:	e8 75 d7 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    4cdb:	48 8b 3d 2e 53 00 00 	mov    0x532e(%rip),%rdi        # a010 <http_404_content>
    4ce2:	4c 89 ea             	mov    %r13,%rdx
    4ce5:	44 89 e6             	mov    %r12d,%esi
    4ce8:	e8 03 fd ff ff       	call   49f0 <_send_static_string_content>
}
    4ced:	e9 39 ff ff ff       	jmp    4c2b <handle_get_method+0xcb>
    4cf2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4cf8:	bf 70 00 00 00       	mov    $0x70,%edi
    4cfd:	e8 0e d7 ff ff       	call   2410 <malloc@plt>
    4d02:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4d05:	48 85 c0             	test   %rax,%rax
    4d08:	74 5d                	je     4d67 <handle_get_method+0x207>
            req->client_socket = client_socket;
    4d0a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4d0e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4d13:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4d17:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    4d1a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4d21:	e8 5a f5 ff ff       	call   4280 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4d26:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4d2b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4d2f:	4c 89 f7             	mov    %r14,%rdi
    4d32:	e8 79 fa ff ff       	call   47b0 <copy_file_contents>
    4d37:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4d3c:	4c 89 f2             	mov    %r14,%rdx
    4d3f:	31 c0                	xor    %eax,%eax
    4d41:	48 8d 35 c6 23 00 00 	lea    0x23c6(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4d48:	bf 01 00 00 00       	mov    $0x1,%edi
    4d4d:	e8 fe d6 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    4d52:	4c 89 ee             	mov    %r13,%rsi
    4d55:	48 89 df             	mov    %rbx,%rdi
    4d58:	e8 13 fb ff ff       	call   4870 <add_write_request>
    4d5d:	e9 c9 fe ff ff       	jmp    4c2b <handle_get_method+0xcb>
}
    4d62:	e8 c9 d5 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4d67:	48 8b 0d b2 52 00 00 	mov    0x52b2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4d6e:	ba 28 00 00 00       	mov    $0x28,%edx
    4d73:	be 01 00 00 00       	mov    $0x1,%esi
    4d78:	48 8d 3d 89 26 00 00 	lea    0x2689(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4d7f:	e8 3c d7 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4d84:	bf 01 00 00 00       	mov    $0x1,%edi
    4d89:	e8 12 d7 ff ff       	call   24a0 <exit@plt>
    4d8e:	66 90                	xchg   %ax,%ax

0000000000004d90 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4d90:	f3 0f 1e fa          	endbr64
    4d94:	41 57                	push   %r15
    4d96:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4d98:	4c 8d 35 e6 22 00 00 	lea    0x22e6(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4d9f:	41 55                	push   %r13
    4da1:	49 89 d5             	mov    %rdx,%r13
    4da4:	41 54                	push   %r12
    4da6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4da9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4dac:	55                   	push   %rbp
    4dad:	53                   	push   %rbx
    4dae:	48 83 ec 18          	sub    $0x18,%rsp
    4db2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4dbb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4dc0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4dc2:	49 89 e7             	mov    %rsp,%r15
    4dc5:	4c 89 fa             	mov    %r15,%rdx
    4dc8:	e8 b3 d5 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4dcd:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4dd1:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4dd4:	84 db                	test   %bl,%bl
    4dd6:	74 1d                	je     4df5 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4dd8:	e8 33 d7 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4ddd:	48 89 ea             	mov    %rbp,%rdx
    4de0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4de3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4de7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4dea:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    4ded:	48 0f be 1a          	movsbq (%rdx),%rbx
    4df1:	84 db                	test   %bl,%bl
    4df3:	75 eb                	jne    4de0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4df5:	4c 89 fa             	mov    %r15,%rdx
    4df8:	4c 89 f6             	mov    %r14,%rsi
    4dfb:	31 ff                	xor    %edi,%edi
    4dfd:	e8 7e d5 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4e02:	48 8d 35 2a 23 00 00 	lea    0x232a(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4e09:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4e0c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    4e0f:	e8 9c d5 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4e14:	4c 89 ea             	mov    %r13,%rdx
    4e17:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4e1a:	85 c0                	test   %eax,%eax
    4e1c:	75 2a                	jne    4e48 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    4e1e:	48 89 df             	mov    %rbx,%rdi
    4e21:	e8 3a fd ff ff       	call   4b60 <handle_get_method>
}
    4e26:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4e2b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4e34:	75 20                	jne    4e56 <handle_http_method+0xc6>
    4e36:	48 83 c4 18          	add    $0x18,%rsp
    4e3a:	5b                   	pop    %rbx
    4e3b:	5d                   	pop    %rbp
    4e3c:	41 5c                	pop    %r12
    4e3e:	41 5d                	pop    %r13
    4e40:	41 5e                	pop    %r14
    4e42:	41 5f                	pop    %r15
    4e44:	c3                   	ret
    4e45:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4e48:	48 8b 3d c9 51 00 00 	mov    0x51c9(%rip),%rdi        # a018 <unimplemented_content>
    4e4f:	e8 9c fb ff ff       	call   49f0 <_send_static_string_content>
}
    4e54:	eb d0                	jmp    4e26 <handle_http_method+0x96>
    4e56:	e8 d5 d4 ff ff       	call   2330 <__stack_chk_fail@plt>
    4e5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004e60 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4e60:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4e64:	85 d2                	test   %edx,%edx
    4e66:	7e 38                	jle    4ea0 <get_line+0x40>
    4e68:	48 63 d2             	movslq %edx,%rdx
    4e6b:	48 83 c7 01          	add    $0x1,%rdi
    4e6f:	48 01 f2             	add    %rsi,%rdx
    4e72:	eb 11                	jmp    4e85 <get_line+0x25>
    4e74:	0f 1f 40 00          	nopl   0x0(%rax)
    4e78:	48 83 c6 01          	add    $0x1,%rsi
    4e7c:	48 83 c7 01          	add    $0x1,%rdi
    4e80:	48 39 d6             	cmp    %rdx,%rsi
    4e83:	74 1b                	je     4ea0 <get_line+0x40>
        dest[i] = src[i];
    4e85:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4e89:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4e8b:	3c 0d                	cmp    $0xd,%al
    4e8d:	75 e9                	jne    4e78 <get_line+0x18>
    4e8f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4e92:	75 e4                	jne    4e78 <get_line+0x18>
            dest[i] = '\0';
    4e94:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4e97:	31 c0                	xor    %eax,%eax
    4e99:	c3                   	ret
    4e9a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4ea0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4ea5:	c3                   	ret
    4ea6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004eb0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4eb0:	f3 0f 1e fa          	endbr64
    4eb4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4ebb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4ebf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4ec8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4ed0:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4ed2:	49 89 e2             	mov    %rsp,%r10
    4ed5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4edd:	4c 89 d0             	mov    %r10,%rax
    4ee0:	eb 13                	jmp    4ef5 <handle_client_request+0x45>
    4ee2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4ee8:	48 83 c0 01          	add    $0x1,%rax
    4eec:	48 83 c1 01          	add    $0x1,%rcx
    4ef0:	4c 39 c8             	cmp    %r9,%rax
    4ef3:	74 4b                	je     4f40 <handle_client_request+0x90>
        dest[i] = src[i];
    4ef5:	44 0f b6 01          	movzbl (%rcx),%r8d
    4ef9:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4efc:	41 80 f8 0d          	cmp    $0xd,%r8b
    4f00:	75 e6                	jne    4ee8 <handle_client_request+0x38>
    4f02:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4f06:	75 e0                	jne    4ee8 <handle_client_request+0x38>
            dest[i] = '\0';
    4f08:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4f0b:	8b 47 08             	mov    0x8(%rdi),%eax
    4f0e:	48 89 f2             	mov    %rsi,%rdx
    4f11:	4c 89 d7             	mov    %r10,%rdi
    4f14:	89 c6                	mov    %eax,%esi
    4f16:	e8 75 fe ff ff       	call   4d90 <handle_http_method>
}
    4f1b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4f23:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4f2c:	75 39                	jne    4f67 <handle_client_request+0xb7>
    4f2e:	31 c0                	xor    %eax,%eax
    4f30:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4f37:	c3                   	ret
    4f38:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4f40:	48 8b 0d d9 50 00 00 	mov    0x50d9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4f47:	ba 12 00 00 00       	mov    $0x12,%edx
    4f4c:	be 01 00 00 00       	mov    $0x1,%esi
    4f51:	48 8d 3d df 21 00 00 	lea    0x21df(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4f58:	e8 63 d5 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4f5d:	bf 01 00 00 00       	mov    $0x1,%edi
    4f62:	e8 39 d5 ff ff       	call   24a0 <exit@plt>
}
    4f67:	e8 c4 d3 ff ff       	call   2330 <__stack_chk_fail@plt>
    4f6c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004f70 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4f70:	f3 0f 1e fa          	endbr64
    4f74:	55                   	push   %rbp
    4f75:	53                   	push   %rbx
    4f76:	48 89 cb             	mov    %rcx,%rbx
    4f79:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4f7d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4f80:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4f83:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4f89:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4f8c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4f8f:	f6 c1 02             	test   $0x2,%cl
    4f92:	74 00                	je     4f94 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4f94:	41 89 c0             	mov    %eax,%r8d
    4f97:	45 29 c8             	sub    %r9d,%r8d
    4f9a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4f9e:	0f 82 e8 d5 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4fa4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4fa7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4faa:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4fad:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4fb0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4fb3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4fb7:	d3 e5                	shl    %cl,%ebp
    4fb9:	48 c1 e5 06          	shl    $0x6,%rbp
    4fbd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4fc1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4fc4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4fc9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4fd0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4fd4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4fd8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4fe0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4fe8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4fec:	e8 1f d4 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4ff1:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4ff4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4ffa:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4ffe:	48 83 c4 08          	add    $0x8,%rsp
    5002:	5b                   	pop    %rbx
    5003:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5004:	e9 37 d3 ff ff       	jmp    2340 <io_uring_submit@plt>
    5009:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005010 <io_thread>:
void* io_thread(void *arg) {
    5010:	f3 0f 1e fa          	endbr64
    5014:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5016:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5018:	41 56                	push   %r14
    501a:	41 55                	push   %r13
    501c:	41 54                	push   %r12
    501e:	55                   	push   %rbp
    501f:	48 89 fd             	mov    %rdi,%rbp
    5022:	53                   	push   %rbx
    5023:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    502a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5033:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    503b:	48 8b 87 88 01 00 00 	mov    0x188(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5042:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5047:	bf 00 01 00 00       	mov    $0x100,%edi
    504c:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    504f:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5053:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5058:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    505d:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    5062:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5067:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    506f:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5074:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    507c:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5081:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5089:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    508e:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5096:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    509b:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    50a3:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    50a8:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    50b0:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    50b8:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    50c0:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    50c8:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    50d0:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    50d8:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    50e0:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    50e8:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    50f0:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    50f8:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5100:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5107:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    510f:	e8 dc d2 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5114:	48 8b bd 88 01 00 00 	mov    0x188(%rbp),%rdi
    511b:	31 f6                	xor    %esi,%esi
    511d:	e8 be d3 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    5122:	31 d2                	xor    %edx,%edx
    5124:	be 01 00 00 00       	mov    $0x1,%esi
    5129:	bf 02 00 00 00       	mov    $0x2,%edi
    512e:	e8 fd d3 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    5133:	83 f8 ff             	cmp    $0xffffffff,%eax
    5136:	0f 84 92 d4 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    513c:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5141:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5147:	89 c7                	mov    %eax,%edi
    5149:	41 89 c4             	mov    %eax,%r12d
    514c:	ba 02 00 00 00       	mov    $0x2,%edx
    5151:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5156:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    515e:	e8 9d d1 ff ff       	call   2300 <setsockopt@plt>
    5163:	85 c0                	test   %eax,%eax
    5165:	0f 88 37 d4 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    516b:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    5170:	ba 10 00 00 00       	mov    $0x10,%edx
    5175:	44 89 e7             	mov    %r12d,%edi
    5178:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5181:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5189:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    5191:	e8 ca d2 ff ff       	call   2460 <bind@plt>
    5196:	85 c0                	test   %eax,%eax
    5198:	0f 88 3c d4 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    519e:	be 0a 00 00 00       	mov    $0xa,%esi
    51a3:	44 89 e7             	mov    %r12d,%edi
    51a6:	e8 75 d2 ff ff       	call   2420 <listen@plt>
    51ab:	85 c0                	test   %eax,%eax
    51ad:	0f 88 fb d3 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    51b3:	ba db 18 00 00       	mov    $0x18db,%edx
    51b8:	48 8d 35 bd 1f 00 00 	lea    0x1fbd(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    51bf:	bf 01 00 00 00       	mov    $0x1,%edi
    51c4:	31 c0                	xor    %eax,%eax
    51c6:	e8 85 d2 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    51cb:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    51d0:	48 89 d9             	mov    %rbx,%rcx
    51d3:	44 89 e7             	mov    %r12d,%edi
    51d6:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    51db:	48 89 c6             	mov    %rax,%rsi
    51de:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    51e3:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    51e8:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    51f0:	e8 7b fd ff ff       	call   4f70 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    51f5:	bf 01 00 00 00       	mov    $0x1,%edi
    51fa:	be 10 00 00 00       	mov    $0x10,%esi
    51ff:	e8 9c d1 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    5204:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5209:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    520c:	e8 ff d1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    5211:	48 85 c0             	test   %rax,%rax
    5214:	0f 84 c8 04 00 00    	je     56e2 <io_thread+0x6d2>
  iov->iov_base = zh_malloc(10);
    521a:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    521e:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5225:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    522c:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5234:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5237:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    523c:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    523e:	f6 c1 02             	test   $0x2,%cl
    5241:	0f 85 29 04 00 00    	jne    5670 <io_thread+0x660>
	if (next - head <= sq->ring_entries) {
    5247:	89 d0                	mov    %edx,%eax
    5249:	29 f0                	sub    %esi,%eax
    524b:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5252:	0f 82 6c d3 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5258:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    525b:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	sqe->addr3 = 0;
    5262:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5266:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5269:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5270:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    5273:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    527a:	48 8d b5 90 01 00 00 	lea    0x190(%rbp),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5281:	8b 95 90 01 00 00    	mov    0x190(%rbp),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5287:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5289:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    528e:	48 c1 e0 06          	shl    $0x6,%rax
    5292:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    529a:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    52a0:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    52a3:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    52ab:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    52af:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    52b7:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    52bf:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    52c3:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    52c7:	e8 74 d0 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    52cc:	83 bd a4 00 00 00 01 	cmpl   $0x1,0xa4(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    52d3:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    52d8:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    52e0:	0f 85 de 01 00 00    	jne    54c4 <io_thread+0x4b4>
    52e6:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    52eb:	4d 89 ce             	mov    %r9,%r14
    52ee:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    52f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    52f8:	48 8d 3d 93 1e 00 00 	lea    0x1e93(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    52ff:	e8 ec cf ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5304:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    530b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5312:	c1 e9 0b             	shr    $0xb,%ecx
    5315:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5318:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5320:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5322:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    532a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    532c:	39 d0                	cmp    %edx,%eax
    532e:	74 36                	je     5366 <io_thread+0x356>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5330:	89 f8                	mov    %edi,%eax
    5332:	21 d0                	and    %edx,%eax
    5334:	d3 e0                	shl    %cl,%eax
    5336:	48 c1 e0 04          	shl    $0x4,%rax
    533a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5342:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    534a:	0f 85 b0 01 00 00    	jne    5500 <io_thread+0x4f0>
    5350:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5354:	0f 85 1e 03 00 00    	jne    5678 <io_thread+0x668>
			if (cqe->res < 0)
    535a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    535d:	83 c2 01             	add    $0x1,%edx
    5360:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5362:	85 c0                	test   %eax,%eax
    5364:	79 b2                	jns    5318 <io_thread+0x308>
	*cqe_ptr = cqe;
    5366:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    536f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5370:	45 31 c0             	xor    %r8d,%r8d
    5373:	31 d2                	xor    %edx,%edx
    5375:	b9 01 00 00 00       	mov    $0x1,%ecx
    537a:	4c 89 f6             	mov    %r14,%rsi
    537d:	48 89 df             	mov    %rbx,%rdi
    5380:	e8 bb d0 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5385:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5388:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    538d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5391:	0f 84 f1 02 00 00    	je     5688 <io_thread+0x678>
    5397:	48 8d 3d 1a 1e 00 00 	lea    0x1e1a(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    539e:	e8 4d cf ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    53a3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    53a8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    53ab:	45 85 ff             	test   %r15d,%r15d
    53ae:	0f 88 e2 d1 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    53b4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    53b7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    53bb:	85 c0                	test   %eax,%eax
    53bd:	0f 88 e5 02 00 00    	js     56a8 <io_thread+0x698>
      switch (req->event_type) {
    53c3:	41 83 f8 01          	cmp    $0x1,%r8d
    53c7:	0f 84 83 01 00 00    	je     5550 <io_thread+0x540>
    53cd:	41 83 f8 02          	cmp    $0x2,%r8d
    53d1:	0f 84 a9 01 00 00    	je     5580 <io_thread+0x570>
    53d7:	45 85 c0             	test   %r8d,%r8d
    53da:	0f 85 58 01 00 00    	jne    5538 <io_thread+0x528>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    53e0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    53e5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    53ea:	48 89 d9             	mov    %rbx,%rcx
    53ed:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    53f1:	e8 7a fb ff ff       	call   4f70 <add_accept_request>
              add_read_request(cqe->res, &ring);
    53f6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    53fb:	48 89 de             	mov    %rbx,%rsi
    53fe:	8b 78 08             	mov    0x8(%rax),%edi
    5401:	e8 0a f5 ff ff       	call   4910 <add_read_request>
              free(req);
    5406:	4c 89 e7             	mov    %r12,%rdi
    5409:	e8 b2 ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    540e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5413:	48 85 c0             	test   %rax,%rax
    5416:	0f 85 1c 01 00 00    	jne    5538 <io_thread+0x528>
	unsigned int head, next = sq->sqe_tail + 1;
    541c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5423:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    542a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    542d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5432:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5434:	f6 c1 02             	test   $0x2,%cl
    5437:	74 00                	je     5439 <io_thread+0x429>
	if (next - head <= sq->ring_entries) {
    5439:	89 d0                	mov    %edx,%eax
    543b:	29 f0                	sub    %esi,%eax
    543d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5444:	0f 82 70 d1 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    544a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    544d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5452:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5456:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5459:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5460:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5463:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    546a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5471:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5473:	8b 95 90 01 00 00    	mov    0x190(%rbp),%edx
    5479:	48 c1 e0 06          	shl    $0x6,%rax
    547d:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5485:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    548b:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    548e:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5496:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    549a:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    54a2:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    54aa:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    54ae:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    54b2:	e8 89 ce ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    54b7:	83 bd a4 00 00 00 01 	cmpl   $0x1,0xa4(%rbp)
    54be:	0f 84 34 fe ff ff    	je     52f8 <io_thread+0x2e8>
    54c4:	48 8d 3d 26 1d 00 00 	lea    0x1d26(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    54cb:	e8 20 ce ff ff       	call   22f0 <puts@plt>
}
    54d0:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    54d8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    54e1:	0f 85 22 02 00 00    	jne    5709 <io_thread+0x6f9>
    54e7:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    54ee:	31 c0                	xor    %eax,%eax
    54f0:	5b                   	pop    %rbx
    54f1:	5d                   	pop    %rbp
    54f2:	41 5c                	pop    %r12
    54f4:	41 5d                	pop    %r13
    54f6:	41 5e                	pop    %r14
    54f8:	41 5f                	pop    %r15
    54fa:	c3                   	ret
    54fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    5500:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5505:	48 85 c0             	test   %rax,%rax
    5508:	0f 84 62 fe ff ff    	je     5370 <io_thread+0x360>
      if (cqe->user_data == 1) {
    550e:	48 83 38 01          	cmpq   $0x1,(%rax)
    5512:	0f 84 70 01 00 00    	je     5688 <io_thread+0x678>
    5518:	48 8d 3d 99 1c 00 00 	lea    0x1c99(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    551f:	e8 cc cd ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5524:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5529:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    552c:	e9 83 fe ff ff       	jmp    53b4 <io_thread+0x3a4>
    5531:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5538:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5540:	8b 02                	mov    (%rdx),%eax
    5542:	83 c0 01             	add    $0x1,%eax
    5545:	89 02                	mov    %eax,(%rdx)
}
    5547:	e9 d0 fe ff ff       	jmp    541c <io_thread+0x40c>
    554c:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5550:	85 c0                	test   %eax,%eax
    5552:	75 7c                	jne    55d0 <io_thread+0x5c0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5554:	48 8b 0d c5 4a 00 00 	mov    0x4ac5(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    555b:	ba 0f 00 00 00       	mov    $0xf,%edx
    5560:	be 01 00 00 00       	mov    $0x1,%esi
    5565:	48 8d 3d 75 1c 00 00 	lea    0x1c75(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    556c:	e8 4f cf ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5571:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5576:	e9 98 fe ff ff       	jmp    5413 <io_thread+0x403>
    557b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5580:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5585:	45 31 ff             	xor    %r15d,%r15d
    5588:	85 c0                	test   %eax,%eax
    558a:	7e 20                	jle    55ac <io_thread+0x59c>
    558c:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5590:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5593:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    5597:	48 c1 e0 04          	shl    $0x4,%rax
    559b:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    55a0:	e8 1b cd ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    55a5:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    55aa:	7f e4                	jg     5590 <io_thread+0x580>
              close(req->client_socket);
    55ac:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    55b1:	e8 ba cd ff ff       	call   2370 <close@plt>
              free(req);
    55b6:	4c 89 e7             	mov    %r12,%rdi
    55b9:	e8 02 cd ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    55be:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    55c3:	e9 4b fe ff ff       	jmp    5413 <io_thread+0x403>
    55c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int i = 0; i < dest_sz; i++) {
    55d0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    55d5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    55da:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    55e2:	eb 11                	jmp    55f5 <io_thread+0x5e5>
    55e4:	0f 1f 40 00          	nopl   0x0(%rax)
    55e8:	48 83 c0 01          	add    $0x1,%rax
    55ec:	48 83 c2 01          	add    $0x1,%rdx
    55f0:	48 39 c6             	cmp    %rax,%rsi
    55f3:	74 4b                	je     5640 <io_thread+0x630>
        dest[i] = src[i];
    55f5:	0f b6 0a             	movzbl (%rdx),%ecx
    55f8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    55fa:	80 f9 0d             	cmp    $0xd,%cl
    55fd:	75 e9                	jne    55e8 <io_thread+0x5d8>
    55ff:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5603:	75 e3                	jne    55e8 <io_thread+0x5d8>
            dest[i] = '\0';
    5605:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5608:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    560d:	48 89 da             	mov    %rbx,%rdx
    5610:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5615:	e8 76 f7 ff ff       	call   4d90 <handle_http_method>
              free(req->iov[0].iov_base);
    561a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    561f:	e8 9c cc ff ff       	call   22c0 <free@plt>
              free(req);
    5624:	4c 89 e7             	mov    %r12,%rdi
    5627:	e8 94 cc ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    562c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5631:	e9 dd fd ff ff       	jmp    5413 <io_thread+0x403>
    5636:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5640:	48 8b 0d d9 49 00 00 	mov    0x49d9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5647:	ba 12 00 00 00       	mov    $0x12,%edx
    564c:	be 01 00 00 00       	mov    $0x1,%esi
    5651:	48 8d 3d df 1a 00 00 	lea    0x1adf(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5658:	e8 63 ce ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    565d:	bf 01 00 00 00       	mov    $0x1,%edi
    5662:	e8 39 ce ff ff       	call   24a0 <exit@plt>
    5667:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5670:	e9 d2 fb ff ff       	jmp    5247 <io_thread+0x237>
    5675:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5678:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    567d:	e9 8c fe ff ff       	jmp    550e <io_thread+0x4fe>
    5682:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5688:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5690:	48 8d 3d 0d 1b 00 00 	lea    0x1b0d(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    5697:	8b 02                	mov    (%rdx),%eax
    5699:	83 c0 01             	add    $0x1,%eax
    569c:	89 02                	mov    %eax,(%rdx)
    569e:	e8 4d cc ff ff       	call   22f0 <puts@plt>
    56a3:	e9 1c fe ff ff       	jmp    54c4 <io_thread+0x4b4>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    56a8:	f7 d8                	neg    %eax
    56aa:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    56af:	89 c7                	mov    %eax,%edi
    56b1:	e8 4a ce ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    56b6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    56bb:	be 01 00 00 00       	mov    $0x1,%esi
    56c0:	48 8b 3d 59 49 00 00 	mov    0x4959(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    56c7:	48 89 c1             	mov    %rax,%rcx
    56ca:	48 8d 15 67 1d 00 00 	lea    0x1d67(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    56d1:	31 c0                	xor    %eax,%eax
    56d3:	e8 f8 cd ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    56d8:	bf 01 00 00 00       	mov    $0x1,%edi
    56dd:	e8 be cd ff ff       	call   24a0 <exit@plt>
    56e2:	48 8b 0d 37 49 00 00 	mov    0x4937(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    56e9:	ba 28 00 00 00       	mov    $0x28,%edx
    56ee:	be 01 00 00 00       	mov    $0x1,%esi
    56f3:	48 8d 3d 0e 1d 00 00 	lea    0x1d0e(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    56fa:	e8 c1 cd ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    56ff:	bf 01 00 00 00       	mov    $0x1,%edi
    5704:	e8 97 cd ff ff       	call   24a0 <exit@plt>
}
    5709:	e8 22 cc ff ff       	call   2330 <__stack_chk_fail@plt>
    570e:	66 90                	xchg   %ax,%ax

0000000000005710 <sendm>:
int sendm(struct BarrierTask *data) {
    5710:	f3 0f 1e fa          	endbr64
    5714:	41 57                	push   %r15
    5716:	41 56                	push   %r14
    5718:	41 55                	push   %r13
    571a:	41 54                	push   %r12
    571c:	55                   	push   %rbp
    571d:	53                   	push   %rbx
    571e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5722:	83 bf 08 04 00 00 01 	cmpl   $0x1,0x408(%rdi)
    5729:	0f 85 a9 01 00 00    	jne    58d8 <sendm+0x1c8>
    572f:	48 8d b7 10 04 00 00 	lea    0x410(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5736:	8b 87 24 02 00 00    	mov    0x224(%rdi),%eax
    573c:	48 89 fa             	mov    %rdi,%rdx
    573f:	31 c9                	xor    %ecx,%ecx
    5741:	48 89 34 24          	mov    %rsi,(%rsp)
    5745:	48 8d b7 18 04 00 00 	lea    0x418(%rdi),%rsi
    574c:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5751:	85 c0                	test   %eax,%eax
    5753:	0f 8e e4 00 00 00    	jle    583d <sendm+0x12d>
    5759:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5760:	39 8a 20 02 00 00    	cmp    %ecx,0x220(%rdx)
    5766:	0f 84 c5 00 00 00    	je     5831 <sendm+0x121>
        struct Data *them = data->mailboxes[n].higher;
    576c:	49 89 ca             	mov    %rcx,%r10
    576f:	49 c1 e2 09          	shl    $0x9,%r10
    5773:	4c 03 92 88 03 00 00 	add    0x388(%rdx),%r10
    577a:	4d 8b 9a 80 00 00 00 	mov    0x80(%r10),%r11
        for (; them->messages_count < min;) {
    5781:	49 8b 9b 80 00 00 00 	mov    0x80(%r11),%rbx
    5788:	4d 63 8b 88 00 00 00 	movslq 0x88(%r11),%r9
    578f:	4c 39 cb             	cmp    %r9,%rbx
    5792:	0f 8d 90 00 00 00    	jge    5828 <sendm+0x118>
    5798:	4c 89 cf             	mov    %r9,%rdi
    579b:	48 8b aa 80 01 00 00 	mov    0x180(%rdx),%rbp
    57a2:	4d 8b b2 00 01 00 00 	mov    0x100(%r10),%r14
    57a9:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    57ac:	49 8b 33             	mov    (%r11),%rsi
    57af:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    57b3:	48 83 f8 02          	cmp    $0x2,%rax
    57b7:	0f 86 03 01 00 00    	jbe    58c0 <sendm+0x1b0>
    57bd:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    57c5:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    57cd:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    57d1:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    57d5:	4c 39 2c 24          	cmp    %r13,(%rsp)
    57d9:	73 75                	jae    5850 <sendm+0x140>
    57db:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    57e0:	4d 39 fc             	cmp    %r15,%r12
    57e3:	73 6b                	jae    5850 <sendm+0x140>
    57e5:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    57e9:	49 01 f0             	add    %rsi,%r8
    57ec:	0f 1f 40 00          	nopl   0x0(%rax)
    57f0:	48 8b 82 10 04 00 00 	mov    0x410(%rdx),%rax
        for (; them->messages_count < min;) {
    57f7:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    57fb:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    57ff:	49 39 d8             	cmp    %rbx,%r8
    5802:	75 ec                	jne    57f0 <sendm+0xe0>
    5804:	0f 1f 40 00          	nopl   0x0(%rax)
    5808:	48 01 fd             	add    %rdi,%rbp
    580b:	4c 01 f7             	add    %r14,%rdi
    580e:	48 89 aa 80 01 00 00 	mov    %rbp,0x180(%rdx)
    5815:	49 89 ba 00 01 00 00 	mov    %rdi,0x100(%r10)
    581c:	4d 89 8b 80 00 00 00 	mov    %r9,0x80(%r11)
    5823:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5828:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    582b:	8b 82 24 02 00 00    	mov    0x224(%rdx),%eax
    5831:	48 83 c1 01          	add    $0x1,%rcx
    5835:	39 c8                	cmp    %ecx,%eax
    5837:	0f 8f 23 ff ff ff    	jg     5760 <sendm+0x50>
}
    583d:	48 83 c4 18          	add    $0x18,%rsp
    5841:	31 c0                	xor    %eax,%eax
    5843:	5b                   	pop    %rbx
    5844:	5d                   	pop    %rbp
    5845:	41 5c                	pop    %r12
    5847:	41 5d                	pop    %r13
    5849:	41 5e                	pop    %r14
    584b:	41 5f                	pop    %r15
    584d:	c3                   	ret
    584e:	66 90                	xchg   %ax,%ax
    5850:	49 89 fd             	mov    %rdi,%r13
    5853:	48 8b 82 10 04 00 00 	mov    0x410(%rdx),%rax
    585a:	4d 89 e0             	mov    %r12,%r8
    585d:	49 d1 ed             	shr    %r13
    5860:	49 c1 e5 04          	shl    $0x4,%r13
    5864:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5869:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    586d:	41 83 e5 10          	and    $0x10,%r13d
    5871:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5875:	74 11                	je     5888 <sendm+0x178>
          them->messages[them->messages_count++] = data->message; 
    5877:	49 83 c0 10          	add    $0x10,%r8
    587b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5880:	4d 39 f8             	cmp    %r15,%r8
    5883:	74 15                	je     589a <sendm+0x18a>
    5885:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5888:	41 0f 11 00          	movups %xmm0,(%r8)
    588c:	49 83 c0 20          	add    $0x20,%r8
    5890:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    5895:	4d 39 f8             	cmp    %r15,%r8
    5898:	75 ee                	jne    5888 <sendm+0x178>
    589a:	49 89 f8             	mov    %rdi,%r8
    589d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    58a1:	49 01 d8             	add    %rbx,%r8
    58a4:	40 f6 c7 01          	test   $0x1,%dil
    58a8:	0f 84 5a ff ff ff    	je     5808 <sendm+0xf8>
          them->messages[them->messages_count++] = data->message; 
    58ae:	48 8b 82 10 04 00 00 	mov    0x410(%rdx),%rax
    58b5:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    58b9:	e9 4a ff ff ff       	jmp    5808 <sendm+0xf8>
    58be:	66 90                	xchg   %ax,%ax
    58c0:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    58c8:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    58d0:	e9 10 ff ff ff       	jmp    57e5 <sendm+0xd5>
    58d5:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    58d8:	48 8d 3d 25 19 00 00 	lea    0x1925(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    58df:	e8 0c ca ff ff       	call   22f0 <puts@plt>
    58e4:	e9 54 ff ff ff       	jmp    583d <sendm+0x12d>
    58e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000058f0 <receive>:
int receive(struct BarrierTask *data) {
    58f0:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    58f4:	8b 87 24 02 00 00    	mov    0x224(%rdi),%eax
    58fa:	85 c0                	test   %eax,%eax
    58fc:	0f 8e fc 00 00 00    	jle    59fe <receive+0x10e>
int receive(struct BarrierTask *data) {
    5902:	41 54                	push   %r12
    5904:	48 89 fa             	mov    %rdi,%rdx
    5907:	55                   	push   %rbp
    5908:	31 ed                	xor    %ebp,%ebp
    590a:	53                   	push   %rbx
    590b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5910:	48 89 ee             	mov    %rbp,%rsi
    5913:	48 c1 e6 09          	shl    $0x9,%rsi
    5917:	48 03 b2 88 03 00 00 	add    0x388(%rdx),%rsi
    591e:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5921:	49 8b bc 24 80 00 00 00 	mov    0x80(%r12),%rdi
    5929:	48 85 ff             	test   %rdi,%rdi
    592c:	0f 8e a6 00 00 00    	jle    59d8 <receive+0xe8>
      data->sends++;
    5932:	48 8b 8a 00 04 00 00 	mov    0x400(%rdx),%rcx
    5939:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    593d:	4c 63 1a             	movslq (%rdx),%r11
    5940:	49 89 c9             	mov    %rcx,%r9
    5943:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5947:	49 f7 d9             	neg    %r9
    594a:	48 01 c7             	add    %rax,%rdi
    594d:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    5951:	4c 8b 8a 80 01 00 00 	mov    0x180(%rdx),%r9
      data->mailboxes[n].received++;
    5958:	4c 8b 86 80 01 00 00 	mov    0x180(%rsi),%r8
      data->n++;
    595f:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    5962:	49 29 c8             	sub    %rcx,%r8
    5965:	eb 12                	jmp    5979 <receive+0x89>
    5967:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5970:	48 83 c0 01          	add    $0x1,%rax
    5974:	48 39 c7             	cmp    %rax,%rdi
    5977:	74 5f                	je     59d8 <receive+0xe8>
      data->n++;
    5979:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    597d:	48 89 82 00 04 00 00 	mov    %rax,0x400(%rdx)
      data->n++;
    5984:	48 89 8a 80 01 00 00 	mov    %rcx,0x180(%rdx)
      data->mailboxes[n].received++;
    598b:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    598f:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5996:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    599b:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    599f:	75 cf                	jne    5970 <receive+0x80>
    59a1:	48 63 9a 20 02 00 00 	movslq 0x220(%rdx),%rbx
    59a8:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    59ac:	75 c2                	jne    5970 <receive+0x80>
    59ae:	bf 01 00 00 00       	mov    $0x1,%edi
    59b3:	b9 01 00 00 00       	mov    $0x1,%ecx
    59b8:	ba 01 00 00 00       	mov    $0x1,%edx
    59bd:	31 c0                	xor    %eax,%eax
    59bf:	48 8d 35 9a 1a 00 00 	lea    0x1a9a(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    59c6:	e8 85 ca ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    59cb:	bf 01 00 00 00       	mov    $0x1,%edi
    59d0:	e8 cb ca ff ff       	call   24a0 <exit@plt>
    59d5:	0f 1f 00             	nopl   (%rax)
    me->messages_count = 0;
    59d8:	49 c7 84 24 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%r12)
    asm volatile ("sfence" ::: "memory");
    59e4:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    59e7:	48 83 c5 01          	add    $0x1,%rbp
    59eb:	39 aa 24 02 00 00    	cmp    %ebp,0x224(%rdx)
    59f1:	0f 8f 19 ff ff ff    	jg     5910 <receive+0x20>
}
    59f7:	5b                   	pop    %rbx
    59f8:	31 c0                	xor    %eax,%eax
    59fa:	5d                   	pop    %rbp
    59fb:	41 5c                	pop    %r12
    59fd:	c3                   	ret
    59fe:	31 c0                	xor    %eax,%eax
    5a00:	c3                   	ret
    5a01:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5a0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005a10 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5a10:	f3 0f 1e fa          	endbr64
    5a14:	41 57                	push   %r15
    5a16:	41 56                	push   %r14
    5a18:	41 55                	push   %r13
    5a1a:	41 54                	push   %r12
    5a1c:	55                   	push   %rbp
    5a1d:	53                   	push   %rbx
    5a1e:	48 89 fb             	mov    %rdi,%rbx
    5a21:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    5a25:	8b 07                	mov    (%rdi),%eax
    5a27:	39 87 20 02 00 00    	cmp    %eax,0x220(%rdi)
    5a2d:	0f 84 4d 01 00 00    	je     5b80 <barriered_work+0x170>
    receive(data);
    5a33:	e8 b8 fe ff ff       	call   58f0 <receive>
    while (data->scheduled == 1) {
    5a38:	83 bb 80 02 00 00 01 	cmpl   $0x1,0x280(%rbx)
    5a3f:	75 1b                	jne    5a5c <barriered_work+0x4c>
    5a41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    5a48:	48 83 83 80 01 00 00 01 	addq   $0x1,0x180(%rbx)
      asm volatile ("sfence" ::: "memory");
    5a50:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5a53:	83 bb 80 02 00 00 01 	cmpl   $0x1,0x280(%rbx)
    5a5a:	74 ec                	je     5a48 <barriered_work+0x38>
  if (data->sending == 1) {
    5a5c:	83 bb 08 04 00 00 01 	cmpl   $0x1,0x408(%rbx)
    5a63:	0f 85 a9 02 00 00    	jne    5d12 <barriered_work+0x302>
      for (int n = 0 ; n < data->thread_count; n++) {
    5a69:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    5a6f:	85 c0                	test   %eax,%eax
    5a71:	0f 8e a7 02 00 00    	jle    5d1e <barriered_work+0x30e>
    5a77:	48 8d 8b 10 04 00 00 	lea    0x410(%rbx),%rcx
    5a7e:	31 d2                	xor    %edx,%edx
    5a80:	48 89 0c 24          	mov    %rcx,(%rsp)
    5a84:	48 8d 8b 18 04 00 00 	lea    0x418(%rbx),%rcx
    5a8b:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    5a90:	39 93 20 02 00 00    	cmp    %edx,0x220(%rbx)
    5a96:	0f 84 cd 00 00 00    	je     5b69 <barriered_work+0x159>
        struct Data *them = data->mailboxes[n].higher;
    5a9c:	49 89 d1             	mov    %rdx,%r9
    5a9f:	49 c1 e1 09          	shl    $0x9,%r9
    5aa3:	4c 03 8b 88 03 00 00 	add    0x388(%rbx),%r9
    5aaa:	4d 8b 91 80 00 00 00 	mov    0x80(%r9),%r10
        for (; them->messages_count < min;) {
    5ab1:	4d 8b 9a 80 00 00 00 	mov    0x80(%r10),%r11
    5ab8:	4d 63 82 88 00 00 00 	movslq 0x88(%r10),%r8
    5abf:	4d 39 c3             	cmp    %r8,%r11
    5ac2:	0f 8d 98 00 00 00    	jge    5b60 <barriered_work+0x150>
    5ac8:	4c 89 c6             	mov    %r8,%rsi
    5acb:	48 8b ab 80 01 00 00 	mov    0x180(%rbx),%rbp
    5ad2:	4d 8b b1 00 01 00 00 	mov    0x100(%r9),%r14
    5ad9:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5adc:	49 8b 0a             	mov    (%r10),%rcx
    5adf:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5ae3:	48 83 f8 02          	cmp    $0x2,%rax
    5ae7:	0f 86 bb 02 00 00    	jbe    5da8 <barriered_work+0x398>
    5aed:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5af5:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5afd:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5b01:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5b05:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5b09:	0f 83 29 02 00 00    	jae    5d38 <barriered_work+0x328>
    5b0f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5b14:	4d 39 fc             	cmp    %r15,%r12
    5b17:	0f 83 1b 02 00 00    	jae    5d38 <barriered_work+0x328>
    5b1d:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5b21:	48 01 cf             	add    %rcx,%rdi
    5b24:	0f 1f 40 00          	nopl   0x0(%rax)
    5b28:	48 8b 83 10 04 00 00 	mov    0x410(%rbx),%rax
        for (; them->messages_count < min;) {
    5b2f:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5b33:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5b37:	49 39 fb             	cmp    %rdi,%r11
    5b3a:	75 ec                	jne    5b28 <barriered_work+0x118>
    5b3c:	0f 1f 40 00          	nopl   0x0(%rax)
    5b40:	48 01 f5             	add    %rsi,%rbp
    5b43:	4c 01 f6             	add    %r14,%rsi
    5b46:	48 89 ab 80 01 00 00 	mov    %rbp,0x180(%rbx)
    5b4d:	49 89 b1 00 01 00 00 	mov    %rsi,0x100(%r9)
    5b54:	4d 89 82 80 00 00 00 	mov    %r8,0x80(%r10)
    5b5b:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5b60:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5b63:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    5b69:	48 83 c2 01          	add    $0x1,%rdx
    5b6d:	39 d0                	cmp    %edx,%eax
    5b6f:	0f 8f 1b ff ff ff    	jg     5a90 <barriered_work+0x80>
    5b75:	e9 a4 01 00 00       	jmp    5d1e <barriered_work+0x30e>
    5b7a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      receive(data);
    5b80:	e8 6b fd ff ff       	call   58f0 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    5b85:	4c 63 8b 24 02 00 00 	movslq 0x224(%rbx),%r9
        int t = data->task_index;
    5b8c:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    5b8e:	45 85 c9             	test   %r9d,%r9d
    5b91:	0f 8e 99 00 00 00    	jle    5c30 <barriered_work+0x220>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5b97:	48 8b 93 18 02 00 00 	mov    0x218(%rbx),%rdx
    5b9e:	4c 8b 92 80 00 00 00 	mov    0x80(%rdx),%r10
    5ba5:	48 63 d0             	movslq %eax,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
    5ba8:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5bab:	4c 8d 1c d2          	lea    (%rdx,%rdx,8),%r11
              int next_task = abs((t + 1) % (data->thread_count));
    5baf:	99                   	cltd
    5bb0:	41 f7 f9             	idiv   %r9d
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5bb3:	49 c1 e3 07          	shl    $0x7,%r11
    5bb7:	4c 89 d7             	mov    %r10,%rdi
    5bba:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
              int next_task = abs((t + 1) % (data->thread_count));
    5bbe:	89 d0                	mov    %edx,%eax
    5bc0:	f7 d8                	neg    %eax
    5bc2:	0f 48 c2             	cmovs  %edx,%eax
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5bc5:	45 31 c0             	xor    %r8d,%r8d
    5bc8:	48 98                	cltq
    5bca:	48 8d 2c c0          	lea    (%rax,%rax,8),%rbp
    5bce:	48 c1 e5 07          	shl    $0x7,%rbp
    5bd2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    5bd8:	31 c0                	xor    %eax,%eax
    5bda:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5be0:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    5be4:	48 8b 92 98 00 00 00 	mov    0x98(%rdx),%rdx
    5beb:	48 8b 8c 2a 88 03 00 00 	mov    0x388(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5bf3:	48 8b 17             	mov    (%rdi),%rdx
    5bf6:	48 8b b2 98 00 00 00 	mov    0x98(%rdx),%rsi
    5bfd:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5c00:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5c04:	48 c1 e2 09          	shl    $0x9,%rdx
    5c08:	4a 03 94 1e 88 03 00 00 	add    0x388(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5c10:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    5c17:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    5c1b:	49 39 c1             	cmp    %rax,%r9
    5c1e:	75 c0                	jne    5be0 <barriered_work+0x1d0>
        for (int y = 0; y < data->thread_count ; y++) {
    5c20:	48 83 c7 08          	add    $0x8,%rdi
    5c24:	49 81 c0 00 02 00 00 	add    $0x200,%r8
    5c2b:	49 39 fc             	cmp    %rdi,%r12
    5c2e:	75 a8                	jne    5bd8 <barriered_work+0x1c8>
      asm volatile ("sfence" ::: "memory");
    5c30:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5c33:	48 8b b3 08 03 00 00 	mov    0x308(%rbx),%rsi
    5c3a:	31 ff                	xor    %edi,%edi
    5c3c:	48 c1 e6 05          	shl    $0x5,%rsi
    5c40:	48 03 b3 88 02 00 00 	add    0x288(%rbx),%rsi
    5c47:	e8 c4 c6 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5c4c:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    while (data->scheduled == 1) {
    5c53:	83 bb 80 02 00 00 01 	cmpl   $0x1,0x280(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5c5a:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
    5c61:	8b 4a 10             	mov    0x10(%rdx),%ecx
    5c64:	8d 69 01             	lea    0x1(%rcx),%ebp
    5c67:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5c6a:	75 61                	jne    5ccd <barriered_work+0x2bd>
    5c6c:	0f 1f 40 00          	nopl   0x0(%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5c70:	48 63 93 20 02 00 00 	movslq 0x220(%rbx),%rdx
    5c77:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
      data->n++;
    5c7e:	48 83 83 80 01 00 00 01 	addq   $0x1,0x180(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5c86:	48 8b 14 d0          	mov    (%rax,%rdx,8),%rdx
    5c8a:	48 63 03             	movslq (%rbx),%rax
    5c8d:	48 8d 3c c0          	lea    (%rax,%rax,8),%rdi
    5c91:	48 c1 e7 07          	shl    $0x7,%rdi
    5c95:	48 03 ba 98 00 00 00 	add    0x98(%rdx),%rdi
    5c9c:	ff 93 10 02 00 00    	call   *0x210(%rbx)
      asm volatile ("sfence" ::: "memory");
    5ca2:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5ca5:	83 bb 80 02 00 00 01 	cmpl   $0x1,0x280(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    5cac:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    while (data->scheduled == 1) {
    5cb3:	74 bb                	je     5c70 <barriered_work+0x260>
    if (modcount != data->thread->protected_state->modcount) {
    5cb5:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
    5cbc:	3b 68 10             	cmp    0x10(%rax),%ebp
    5cbf:	74 0c                	je     5ccd <barriered_work+0x2bd>
    5cc1:	48 8d 3d 48 15 00 00 	lea    0x1548(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    5cc8:	e8 23 c6 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5ccd:	48 8b b3 08 03 00 00 	mov    0x308(%rbx),%rsi
    5cd4:	31 ff                	xor    %edi,%edi
    5cd6:	48 c1 e6 05          	shl    $0x5,%rsi
    5cda:	48 03 b3 88 02 00 00 	add    0x288(%rbx),%rsi
    5ce1:	48 83 c6 10          	add    $0x10,%rsi
    5ce5:	e8 26 c6 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5cea:	48 8b 83 08 03 00 00 	mov    0x308(%rbx),%rax
    5cf1:	48 83 c0 01          	add    $0x1,%rax
    5cf5:	48 99                	cqto
    5cf7:	48 f7 bb 00 03 00 00 	idivq  0x300(%rbx)
  if (data->sending == 1) {
    5cfe:	83 bb 08 04 00 00 01 	cmpl   $0x1,0x408(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5d05:	48 89 93 08 03 00 00 	mov    %rdx,0x308(%rbx)
  if (data->sending == 1) {
    5d0c:	0f 84 ab 00 00 00    	je     5dbd <barriered_work+0x3ad>
    5d12:	48 8d 3d eb 14 00 00 	lea    0x14eb(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5d19:	e8 d2 c5 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5d1e:	0f ae f8             	sfence
}
    5d21:	48 83 c4 18          	add    $0x18,%rsp
    5d25:	31 c0                	xor    %eax,%eax
    5d27:	5b                   	pop    %rbx
    5d28:	5d                   	pop    %rbp
    5d29:	41 5c                	pop    %r12
    5d2b:	41 5d                	pop    %r13
    5d2d:	41 5e                	pop    %r14
    5d2f:	41 5f                	pop    %r15
    5d31:	c3                   	ret
    5d32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5d38:	49 89 f5             	mov    %rsi,%r13
    5d3b:	48 8b 83 10 04 00 00 	mov    0x410(%rbx),%rax
    5d42:	4c 89 e7             	mov    %r12,%rdi
    5d45:	49 d1 ed             	shr    %r13
    5d48:	49 c1 e5 04          	shl    $0x4,%r13
    5d4c:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5d51:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5d55:	41 83 e5 10          	and    $0x10,%r13d
    5d59:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5d5d:	74 11                	je     5d70 <barriered_work+0x360>
          them->messages[them->messages_count++] = data->message; 
    5d5f:	48 83 c7 10          	add    $0x10,%rdi
    5d63:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5d68:	49 39 ff             	cmp    %rdi,%r15
    5d6b:	74 13                	je     5d80 <barriered_work+0x370>
    5d6d:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5d70:	0f 11 07             	movups %xmm0,(%rdi)
    5d73:	48 83 c7 20          	add    $0x20,%rdi
    5d77:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5d7b:	49 39 ff             	cmp    %rdi,%r15
    5d7e:	75 f0                	jne    5d70 <barriered_work+0x360>
    5d80:	48 89 f7             	mov    %rsi,%rdi
    5d83:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5d87:	4c 01 df             	add    %r11,%rdi
    5d8a:	40 f6 c6 01          	test   $0x1,%sil
    5d8e:	0f 84 ac fd ff ff    	je     5b40 <barriered_work+0x130>
          them->messages[them->messages_count++] = data->message; 
    5d94:	48 8b 83 10 04 00 00 	mov    0x410(%rbx),%rax
    5d9b:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5d9f:	e9 9c fd ff ff       	jmp    5b40 <barriered_work+0x130>
    5da4:	0f 1f 40 00          	nopl   0x0(%rax)
    5da8:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5db0:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5db8:	e9 60 fd ff ff       	jmp    5b1d <barriered_work+0x10d>
      for (int n = 0 ; n < data->thread_count; n++) {
    5dbd:	48 8d 8b 10 04 00 00 	lea    0x410(%rbx),%rcx
    5dc4:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    5dca:	31 d2                	xor    %edx,%edx
    5dcc:	48 89 0c 24          	mov    %rcx,(%rsp)
    5dd0:	48 8d 8b 18 04 00 00 	lea    0x418(%rbx),%rcx
    5dd7:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5ddc:	85 c0                	test   %eax,%eax
    5dde:	0f 8e 3a ff ff ff    	jle    5d1e <barriered_work+0x30e>
    5de4:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5de8:	39 93 20 02 00 00    	cmp    %edx,0x220(%rbx)
    5dee:	0f 84 c5 00 00 00    	je     5eb9 <barriered_work+0x4a9>
        struct Data *them = data->mailboxes[n].higher;
    5df4:	49 89 d1             	mov    %rdx,%r9
    5df7:	49 c1 e1 09          	shl    $0x9,%r9
    5dfb:	4c 03 8b 88 03 00 00 	add    0x388(%rbx),%r9
    5e02:	4d 8b 91 80 00 00 00 	mov    0x80(%r9),%r10
        for (; them->messages_count < min;) {
    5e09:	4d 8b 9a 80 00 00 00 	mov    0x80(%r10),%r11
    5e10:	4d 63 82 88 00 00 00 	movslq 0x88(%r10),%r8
    5e17:	4d 39 d8             	cmp    %r11,%r8
    5e1a:	0f 8e 90 00 00 00    	jle    5eb0 <barriered_work+0x4a0>
    5e20:	4c 89 c6             	mov    %r8,%rsi
    5e23:	48 8b ab 80 01 00 00 	mov    0x180(%rbx),%rbp
    5e2a:	4d 8b b1 00 01 00 00 	mov    0x100(%r9),%r14
    5e31:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5e34:	49 8b 0a             	mov    (%r10),%rcx
    5e37:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5e3b:	48 83 f8 02          	cmp    $0x2,%rax
    5e3f:	0f 86 fb 00 00 00    	jbe    5f40 <barriered_work+0x530>
    5e45:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5e4d:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5e55:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5e59:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5e5d:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5e61:	73 6d                	jae    5ed0 <barriered_work+0x4c0>
    5e63:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5e68:	4d 39 fc             	cmp    %r15,%r12
    5e6b:	73 63                	jae    5ed0 <barriered_work+0x4c0>
    5e6d:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5e71:	48 01 cf             	add    %rcx,%rdi
    5e74:	0f 1f 40 00          	nopl   0x0(%rax)
    5e78:	48 8b 83 10 04 00 00 	mov    0x410(%rbx),%rax
        for (; them->messages_count < min;) {
    5e7f:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5e83:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5e87:	49 39 fb             	cmp    %rdi,%r11
    5e8a:	75 ec                	jne    5e78 <barriered_work+0x468>
    5e8c:	0f 1f 40 00          	nopl   0x0(%rax)
    5e90:	48 01 f5             	add    %rsi,%rbp
    5e93:	4c 01 f6             	add    %r14,%rsi
    5e96:	48 89 ab 80 01 00 00 	mov    %rbp,0x180(%rbx)
    5e9d:	49 89 b1 00 01 00 00 	mov    %rsi,0x100(%r9)
    5ea4:	4d 89 82 80 00 00 00 	mov    %r8,0x80(%r10)
    5eab:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5eb0:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5eb3:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    5eb9:	48 83 c2 01          	add    $0x1,%rdx
    5ebd:	39 d0                	cmp    %edx,%eax
    5ebf:	0f 8f 23 ff ff ff    	jg     5de8 <barriered_work+0x3d8>
    5ec5:	e9 54 fe ff ff       	jmp    5d1e <barriered_work+0x30e>
    5eca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5ed0:	49 89 f5             	mov    %rsi,%r13
    5ed3:	48 8b 83 10 04 00 00 	mov    0x410(%rbx),%rax
    5eda:	4c 89 e7             	mov    %r12,%rdi
    5edd:	49 d1 ed             	shr    %r13
    5ee0:	49 c1 e5 04          	shl    $0x4,%r13
    5ee4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5ee9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5eed:	41 83 e5 10          	and    $0x10,%r13d
    5ef1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5ef5:	74 11                	je     5f08 <barriered_work+0x4f8>
          them->messages[them->messages_count++] = data->message; 
    5ef7:	48 83 c7 10          	add    $0x10,%rdi
    5efb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5f00:	4c 39 ff             	cmp    %r15,%rdi
    5f03:	74 13                	je     5f18 <barriered_work+0x508>
    5f05:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5f08:	0f 11 07             	movups %xmm0,(%rdi)
    5f0b:	48 83 c7 20          	add    $0x20,%rdi
    5f0f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5f13:	4c 39 ff             	cmp    %r15,%rdi
    5f16:	75 f0                	jne    5f08 <barriered_work+0x4f8>
    5f18:	48 89 f7             	mov    %rsi,%rdi
    5f1b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5f1f:	4c 01 df             	add    %r11,%rdi
    5f22:	40 f6 c6 01          	test   $0x1,%sil
    5f26:	0f 84 64 ff ff ff    	je     5e90 <barriered_work+0x480>
          them->messages[them->messages_count++] = data->message; 
    5f2c:	48 8b 83 10 04 00 00 	mov    0x410(%rbx),%rax
    5f33:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5f37:	e9 54 ff ff ff       	jmp    5e90 <barriered_work+0x480>
    5f3c:	0f 1f 40 00          	nopl   0x0(%rax)
    5f40:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5f48:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5f50:	e9 18 ff ff ff       	jmp    5e6d <barriered_work+0x45d>
    5f55:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005f60 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5f60:	f3 0f 1e fa          	endbr64
    5f64:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5f68:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    5f6f:	48 8b 80 80 01 00 00 	mov    0x180(%rax),%rax
    5f76:	48 63 10             	movslq (%rax),%rdx
    5f79:	85 d2                	test   %edx,%edx
    5f7b:	7e 39                	jle    5fb6 <barriered_work_ingest+0x56>
    5f7d:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    5f84:	48 c1 e2 08          	shl    $0x8,%rdx
    5f88:	48 01 c2             	add    %rax,%rdx
    5f8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread->buffers->buffer[x].available == 1) {
    5f90:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    5f97:	75 12                	jne    5fab <barriered_work_ingest+0x4b>
      data->ingest_count++;
    5f99:	48 83 87 80 03 00 00 01 	addq   $0x1,0x380(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5fa1:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5fab:	48 05 00 01 00 00    	add    $0x100,%rax
    5fb1:	48 39 d0             	cmp    %rdx,%rax
    5fb4:	75 da                	jne    5f90 <barriered_work_ingest+0x30>
  asm volatile ("sfence" ::: "memory");
    5fb6:	0f ae f8             	sfence
  barriered_work(data);
    5fb9:	e8 52 fa ff ff       	call   5a10 <barriered_work>
}
    5fbe:	31 c0                	xor    %eax,%eax
    5fc0:	48 83 c4 08          	add    $0x8,%rsp
    5fc4:	c3                   	ret
    5fc5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005fd0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5fd0:	f3 0f 1e fa          	endbr64
}
    5fd4:	31 c0                	xor    %eax,%eax
    5fd6:	c3                   	ret
    5fd7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005fe0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5fe0:	f3 0f 1e fa          	endbr64
    5fe4:	31 c0                	xor    %eax,%eax
    5fe6:	c3                   	ret
    5fe7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005ff0 <after>:
int after(struct timespec left, struct timespec right) {
    5ff0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5ff4:	31 c0                	xor    %eax,%eax
    5ff6:	48 39 d7             	cmp    %rdx,%rdi
    5ff9:	7e 08                	jle    6003 <after+0x13>
    5ffb:	31 c0                	xor    %eax,%eax
    5ffd:	48 39 ce             	cmp    %rcx,%rsi
    6000:	0f 9f c0             	setg   %al
}
    6003:	c3                   	ret
    6004:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    600f:	90                   	nop

0000000000006010 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6010:	f3 0f 1e fa          	endbr64
    6014:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6019:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    601e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6020:	48 39 d7             	cmp    %rdx,%rdi
    6023:	7f 18                	jg     603d <within+0x2d>
    6025:	4d 39 d8             	cmp    %r11,%r8
    6028:	0f 9e c2             	setle  %dl
    602b:	48 39 ce             	cmp    %rcx,%rsi
    602e:	0f 9e c0             	setle  %al
    6031:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6033:	31 c0                	xor    %eax,%eax
    6035:	4d 39 d1             	cmp    %r10,%r9
    6038:	0f 9e c0             	setle  %al
    603b:	21 d0                	and    %edx,%eax
}
    603d:	c3                   	ret
    603e:	66 90                	xchg   %ax,%ax

0000000000006040 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6040:	f3 0f 1e fa          	endbr64
    6044:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6049:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    604e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6053:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6058:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    605d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6062:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6067:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    606c:	48 39 fe             	cmp    %rdi,%rsi
    606f:	7d 2f                	jge    60a0 <overlap+0x60>
    6071:	48 39 ca             	cmp    %rcx,%rdx
    6074:	7d 62                	jge    60d8 <overlap+0x98>
    6076:	4d 39 da             	cmp    %r11,%r10
    6079:	7d 0e                	jge    6089 <overlap+0x49>
    return 1;
    607b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6080:	4d 39 c1             	cmp    %r8,%r9
    6083:	0f 8c 7f 00 00 00    	jl     6108 <overlap+0xc8>
  return 0;
    6089:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    608b:	4d 39 c1             	cmp    %r8,%r9
    608e:	7f 4c                	jg     60dc <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6090:	31 c0                	xor    %eax,%eax
    6092:	4d 39 da             	cmp    %r11,%r10
    6095:	0f 9e c0             	setle  %al
    6098:	c3                   	ret
    6099:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    60a0:	7e 4e                	jle    60f0 <overlap+0xb0>
    60a2:	48 39 ca             	cmp    %rcx,%rdx
    60a5:	7f 39                	jg     60e0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    60a7:	75 31                	jne    60da <overlap+0x9a>
    60a9:	4d 39 c1             	cmp    %r8,%r9
    60ac:	7c 2c                	jl     60da <overlap+0x9a>
    return 1;
    60ae:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    60b3:	4d 39 da             	cmp    %r11,%r10
    60b6:	7d 24                	jge    60dc <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    60b8:	48 39 ca             	cmp    %rcx,%rdx
    60bb:	0f 94 c2             	sete   %dl
    60be:	48 39 fe             	cmp    %rdi,%rsi
    60c1:	0f 94 c0             	sete   %al
    60c4:	21 c2                	and    %eax,%edx
    60c6:	31 c0                	xor    %eax,%eax
    60c8:	4d 39 c1             	cmp    %r8,%r9
    60cb:	0f 94 c0             	sete   %al
    60ce:	21 d0                	and    %edx,%eax
    60d0:	c3                   	ret
    60d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    60d8:	74 af                	je     6089 <overlap+0x49>
  return 0;
    60da:	31 c0                	xor    %eax,%eax
}
    60dc:	c3                   	ret
    60dd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    60e0:	4d 39 da             	cmp    %r11,%r10
    60e3:	7e c4                	jle    60a9 <overlap+0x69>
    return 1;
    60e5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    60ea:	4d 39 c1             	cmp    %r8,%r9
    60ed:	7e ba                	jle    60a9 <overlap+0x69>
    60ef:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    60f0:	48 39 ca             	cmp    %rcx,%rdx
    60f3:	7c 94                	jl     6089 <overlap+0x49>
    60f5:	4d 39 c1             	cmp    %r8,%r9
    60f8:	7d b4                	jge    60ae <overlap+0x6e>
    60fa:	48 39 ca             	cmp    %rcx,%rdx
    60fd:	74 91                	je     6090 <overlap+0x50>
    60ff:	eb d9                	jmp    60da <overlap+0x9a>
    6101:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6108:	c3                   	ret
    6109:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006110 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6110:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6114:	85 f6                	test   %esi,%esi
    6116:	0f 8e 59 03 00 00    	jle    6475 <verify+0x365>
int verify(struct KernelThread *thread_data, int thread_count) {
    611c:	41 57                	push   %r15
    611e:	41 89 f7             	mov    %esi,%r15d
    6121:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6123:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6126:	41 55                	push   %r13
    6128:	41 54                	push   %r12
    612a:	55                   	push   %rbp
    612b:	53                   	push   %rbx
    612c:	48 8d 9f 98 00 00 00 	lea    0x98(%rdi),%rbx
    6133:	48 83 ec 48          	sub    $0x48,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6137:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    613c:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    6141:	45 31 e4             	xor    %r12d,%r12d
    6144:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
      if (z != x)  {
    6149:	45 39 e6             	cmp    %r12d,%r14d
    614c:	0f 84 54 02 00 00    	je     63a6 <verify+0x296>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6152:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6157:	8b 50 08             	mov    0x8(%rax),%edx
    615a:	85 d2                	test   %edx,%edx
    615c:	0f 8e 44 02 00 00    	jle    63a6 <verify+0x296>
    6162:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    616a:	31 ed                	xor    %ebp,%ebp
    616c:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    6171:	44 89 7c 24 34       	mov    %r15d,0x34(%rsp)
    6176:	45 89 f7             	mov    %r14d,%r15d
    6179:	41 89 ee             	mov    %ebp,%r14d
    617c:	44 89 fa             	mov    %r15d,%edx
    617f:	48 8d 35 9a 10 00 00 	lea    0x109a(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    6186:	bf 01 00 00 00       	mov    $0x1,%edi
    618b:	31 c0                	xor    %eax,%eax
    618d:	e8 be c2 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6192:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6197:	8b 40 08             	mov    0x8(%rax),%eax
    619a:	85 c0                	test   %eax,%eax
    619c:	0f 8e dc 01 00 00    	jle    637e <verify+0x26e>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    61a2:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    61a7:	44 89 74 24 38       	mov    %r14d,0x38(%rsp)
    61ac:	31 db                	xor    %ebx,%ebx
    61ae:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    61b3:	4c 8b 20             	mov    (%rax),%r12
    61b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    61c0:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    61c5:	48 8d 04 db          	lea    (%rbx,%rbx,8),%rax
    61c9:	4c 8b 3c 24          	mov    (%rsp),%r15
    61cd:	48 8d 35 61 10 00 00 	lea    0x1061(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    61d4:	49 89 c6             	mov    %rax,%r14
    61d7:	bf 01 00 00 00       	mov    $0x1,%edi
    61dc:	48 8b 45 00          	mov    0x0(%rbp),%rax
    61e0:	49 c1 e6 07          	shl    $0x7,%r14
    61e4:	4b 8b 8c 3c 08 03 00 00 	mov    0x308(%r12,%r15,1),%rcx
    61ec:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    61f1:	4a 8b 94 30 08 03 00 00 	mov    0x308(%rax,%r14,1),%rdx
    61f9:	31 c0                	xor    %eax,%eax
    61fb:	e8 50 c2 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6200:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6205:	4c 8b 20             	mov    (%rax),%r12
    6208:	4b 83 bc 3c 08 03 00 00 00 	cmpq   $0x0,0x308(%r12,%r15,1)
    6211:	0f 8e 4b 01 00 00    	jle    6362 <verify+0x252>
    6217:	4c 03 75 00          	add    0x0(%rbp),%r14
    621b:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6220:	ba 01 00 00 00       	mov    $0x1,%edx
    6225:	4d 89 f5             	mov    %r14,%r13
    6228:	4d 8b b5 08 03 00 00 	mov    0x308(%r13),%r14
    622f:	4d 85 f6             	test   %r14,%r14
    6232:	0f 8e 25 01 00 00    	jle    635d <verify+0x24d>
    6238:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6240:	48 89 d5             	mov    %rdx,%rbp
    6243:	48 8b 04 24          	mov    (%rsp),%rax
    6247:	31 db                	xor    %ebx,%ebx
    6249:	4d 89 f2             	mov    %r14,%r10
    624c:	48 c1 e5 05          	shl    $0x5,%rbp
    6250:	48 83 ed 20          	sub    $0x20,%rbp
    6254:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6258:	49 89 ee             	mov    %rbp,%r14
    625b:	48 89 dd             	mov    %rbx,%rbp
    625e:	48 89 d3             	mov    %rdx,%rbx
    6261:	eb 32                	jmp    6295 <verify+0x185>
    6263:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6268:	4c 39 c2             	cmp    %r8,%rdx
    626b:	0f 8d 57 01 00 00    	jge    63c8 <verify+0x2b8>
    6271:	4c 39 df             	cmp    %r11,%rdi
    6274:	7e 05                	jle    627b <verify+0x16b>
    6276:	49 39 c1             	cmp    %rax,%r9
    6279:	7c 75                	jl     62f0 <verify+0x1e0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    627b:	4c 39 df             	cmp    %r11,%rdi
    627e:	0f 8d b3 01 00 00    	jge    6437 <verify+0x327>
    6284:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6288:	48 83 c5 01          	add    $0x1,%rbp
    628c:	49 39 ea             	cmp    %rbp,%r10
    628f:	0f 8e a8 00 00 00    	jle    633d <verify+0x22d>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6295:	49 8b 97 88 02 00 00 	mov    0x288(%r15),%rdx
    629c:	48 89 e8             	mov    %rbp,%rax
    629f:	48 c1 e0 05          	shl    $0x5,%rax
    62a3:	49 03 85 88 02 00 00 	add    0x288(%r13),%rax
    62aa:	4c 01 f2             	add    %r14,%rdx
    62ad:	48 8b 08             	mov    (%rax),%rcx
    62b0:	48 8b 78 10          	mov    0x10(%rax),%rdi
    62b4:	48 8b 32             	mov    (%rdx),%rsi
    62b7:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    62bb:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    62bf:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    62c3:	48 8b 50 08          	mov    0x8(%rax),%rdx
    62c7:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    62cb:	48 39 f1             	cmp    %rsi,%rcx
    62ce:	7c 98                	jl     6268 <verify+0x158>
    62d0:	0f 8e 4a 01 00 00    	jle    6420 <verify+0x310>
    62d6:	4c 39 c2             	cmp    %r8,%rdx
    62d9:	0f 8f f9 00 00 00    	jg     63d8 <verify+0x2c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    62df:	75 a7                	jne    6288 <verify+0x178>
    62e1:	4c 39 df             	cmp    %r11,%rdi
    62e4:	7f a2                	jg     6288 <verify+0x178>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    62e6:	49 39 c1             	cmp    %rax,%r9
    62e9:	7c 9d                	jl     6288 <verify+0x178>
    62eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    62f0:	49 89 c1             	mov    %rax,%r9
    62f3:	48 89 f9             	mov    %rdi,%rcx
    62f6:	48 89 f2             	mov    %rsi,%rdx
    62f9:	bf 01 00 00 00       	mov    $0x1,%edi
    62fe:	48 8d 35 83 11 00 00 	lea    0x1183(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    6305:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6307:	48 83 c5 01          	add    $0x1,%rbp
    630b:	e8 40 c1 ff ff       	call   2450 <__printf_chk@plt>
    6310:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6315:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    631a:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    631d:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6322:	4d 8b 95 08 03 00 00 	mov    0x308(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6329:	4c 8b 20             	mov    (%rax),%r12
    632c:	48 8b 04 24          	mov    (%rsp),%rax
    6330:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6334:	49 39 ea             	cmp    %rbp,%r10
    6337:	0f 8f 58 ff ff ff    	jg     6295 <verify+0x185>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    633d:	48 89 da             	mov    %rbx,%rdx
    6340:	49 3b 9f 08 03 00 00 	cmp    0x308(%r15),%rbx
    6347:	7d 14                	jge    635d <verify+0x24d>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6349:	4d 8b b5 08 03 00 00 	mov    0x308(%r13),%r14
    6350:	48 83 c2 01          	add    $0x1,%rdx
    6354:	4d 85 f6             	test   %r14,%r14
    6357:	0f 8f e3 fe ff ff    	jg     6240 <verify+0x130>
    635d:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6362:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6367:	48 83 c3 01          	add    $0x1,%rbx
    636b:	39 58 08             	cmp    %ebx,0x8(%rax)
    636e:	0f 8f 4c fe ff ff    	jg     61c0 <verify+0xb0>
    6374:	44 8b 74 24 38       	mov    0x38(%rsp),%r14d
    6379:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    637e:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6383:	48 81 04 24 80 04 00 00 	addq   $0x480,(%rsp)
    638b:	41 83 c6 01          	add    $0x1,%r14d
    638f:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    6393:	0f 8f e3 fd ff ff    	jg     617c <verify+0x6c>
    6399:	45 89 fe             	mov    %r15d,%r14d
    639c:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    63a1:	44 8b 7c 24 34       	mov    0x34(%rsp),%r15d
    for (int z = 0 ; z < thread_count; z++) {
    63a6:	48 81 44 24 08 00 04 00 00 	addq   $0x400,0x8(%rsp)
    63af:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    63b4:	41 39 c7             	cmp    %eax,%r15d
    63b7:	0f 84 88 00 00 00    	je     6445 <verify+0x335>
    63bd:	41 89 c4             	mov    %eax,%r12d
    63c0:	e9 84 fd ff ff       	jmp    6149 <verify+0x39>
    63c5:	0f 1f 00             	nopl   (%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    63c8:	0f 85 ba fe ff ff    	jne    6288 <verify+0x178>
    63ce:	e9 a8 fe ff ff       	jmp    627b <verify+0x16b>
    63d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    63d8:	49 39 c1             	cmp    %rax,%r9
    63db:	7e 09                	jle    63e6 <verify+0x2d6>
    63dd:	4c 39 df             	cmp    %r11,%rdi
    63e0:	0f 8c 0a ff ff ff    	jl     62f0 <verify+0x1e0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    63e6:	4c 39 df             	cmp    %r11,%rdi
    63e9:	0f 8f 99 fe ff ff    	jg     6288 <verify+0x178>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    63ef:	49 39 c1             	cmp    %rax,%r9
    63f2:	0f 8d f8 fe ff ff    	jge    62f0 <verify+0x1e0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    63f8:	48 39 f1             	cmp    %rsi,%rcx
    63fb:	0f 85 87 fe ff ff    	jne    6288 <verify+0x178>
    6401:	4c 39 c2             	cmp    %r8,%rdx
    6404:	0f 85 7e fe ff ff    	jne    6288 <verify+0x178>
    640a:	4c 39 df             	cmp    %r11,%rdi
    640d:	0f 84 dd fe ff ff    	je     62f0 <verify+0x1e0>
    6413:	e9 70 fe ff ff       	jmp    6288 <verify+0x178>
    6418:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6420:	4c 39 c2             	cmp    %r8,%rdx
    6423:	0f 8c 52 fe ff ff    	jl     627b <verify+0x16b>
    6429:	4c 39 df             	cmp    %r11,%rdi
    642c:	7e c1                	jle    63ef <verify+0x2df>
    642e:	4c 39 c2             	cmp    %r8,%rdx
    6431:	0f 85 51 fe ff ff    	jne    6288 <verify+0x178>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6437:	49 39 c1             	cmp    %rax,%r9
    643a:	0f 8f 48 fe ff ff    	jg     6288 <verify+0x178>
    6440:	e9 ab fe ff ff       	jmp    62f0 <verify+0x1e0>
  for (int x = 0 ; x < thread_count; x++) {
    6445:	48 81 44 24 10 00 04 00 00 	addq   $0x400,0x10(%rsp)
    644e:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    6453:	41 8d 46 01          	lea    0x1(%r14),%eax
    6457:	45 39 e6             	cmp    %r12d,%r14d
    645a:	74 08                	je     6464 <verify+0x354>
    645c:	41 89 c6             	mov    %eax,%r14d
    645f:	e9 d8 fc ff ff       	jmp    613c <verify+0x2c>
}
    6464:	48 83 c4 48          	add    $0x48,%rsp
    6468:	31 c0                	xor    %eax,%eax
    646a:	5b                   	pop    %rbx
    646b:	5d                   	pop    %rbp
    646c:	41 5c                	pop    %r12
    646e:	41 5d                	pop    %r13
    6470:	41 5e                	pop    %r14
    6472:	41 5f                	pop    %r15
    6474:	c3                   	ret
    6475:	31 c0                	xor    %eax,%eax
    6477:	c3                   	ret

Disassembly of section .fini:

0000000000006478 <_fini>:
    6478:	f3 0f 1e fa          	endbr64
    647c:	48 83 ec 08          	sub    $0x8,%rsp
    6480:	48 83 c4 08          	add    $0x8,%rsp
    6484:	c3                   	ret
