
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
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    2604:	31 ed                	xor    %ebp,%ebp
int main() {
    2606:	53                   	push   %rbx
    2607:	48 81 ec 98 00 00 00 	sub    $0x98,%rsp
    260e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2617:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    261f:	48 8d 05 fa 0f 00 00 	lea    0xffa(%rip),%rax        # 3620 <barriered_reset>
    2626:	66 48 0f 6e e8       	movq   %rax,%xmm5
    262b:	0f 16 2d 46 76 00 00 	movhps 0x7646(%rip),%xmm5        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    2632:	0f 29 6c 24 30       	movaps %xmm5,0x30(%rsp)
    2637:	e8 b4 fc ff ff       	call   22f0 <puts@plt>
    263c:	bf 0a 00 00 00       	mov    $0xa,%edi
    2641:	e8 8a fc ff ff       	call   22d0 <putchar@plt>
    2646:	48 8d 3d f1 4b 00 00 	lea    0x4bf1(%rip),%rdi        # 723e <_IO_stdin_used+0x23e>
    264d:	e8 9e fc ff ff       	call   22f0 <puts@plt>
    2652:	ba 06 00 00 00       	mov    $0x6,%edx
    2657:	48 8d 35 fc 4b 00 00 	lea    0x4bfc(%rip),%rsi        # 725a <_IO_stdin_used+0x25a>
    265e:	31 c0                	xor    %eax,%eax
    2660:	bf 01 00 00 00       	mov    $0x1,%edi
    2665:	e8 e6 fd ff ff       	call   2450 <__printf_chk@plt>
    266a:	ba 09 00 00 00       	mov    $0x9,%edx
    266f:	48 8d 35 fe 4b 00 00 	lea    0x4bfe(%rip),%rsi        # 7274 <_IO_stdin_used+0x274>
    2676:	31 c0                	xor    %eax,%eax
    2678:	bf 01 00 00 00       	mov    $0x1,%edi
    267d:	e8 ce fd ff ff       	call   2450 <__printf_chk@plt>
    2682:	ba 01 00 00 00       	mov    $0x1,%edx
    2687:	48 8d 35 fa 4b 00 00 	lea    0x4bfa(%rip),%rsi        # 7288 <_IO_stdin_used+0x288>
    268e:	31 c0                	xor    %eax,%eax
    2690:	bf 01 00 00 00       	mov    $0x1,%edi
    2695:	e8 b6 fd ff ff       	call   2450 <__printf_chk@plt>
    269a:	ba 01 00 00 00       	mov    $0x1,%edx
    269f:	48 8d 35 f3 4b 00 00 	lea    0x4bf3(%rip),%rsi        # 7299 <_IO_stdin_used+0x299>
    26a6:	31 c0                	xor    %eax,%eax
    26a8:	bf 01 00 00 00       	mov    $0x1,%edi
    26ad:	e8 9e fd ff ff       	call   2450 <__printf_chk@plt>
    26b2:	ba 01 00 00 00       	mov    $0x1,%edx
    26b7:	48 8d 35 f3 4b 00 00 	lea    0x4bf3(%rip),%rsi        # 72b1 <_IO_stdin_used+0x2b1>
    26be:	31 c0                	xor    %eax,%eax
    26c0:	bf 01 00 00 00       	mov    $0x1,%edi
    26c5:	e8 86 fd ff ff       	call   2450 <__printf_chk@plt>
    26ca:	ba 01 00 00 00       	mov    $0x1,%edx
    26cf:	48 8d 35 42 4e 00 00 	lea    0x4e42(%rip),%rsi        # 7518 <_IO_stdin_used+0x518>
    26d6:	31 c0                	xor    %eax,%eax
    26d8:	bf 01 00 00 00       	mov    $0x1,%edi
    26dd:	e8 6e fd ff ff       	call   2450 <__printf_chk@plt>
    26e2:	ba 01 00 00 00       	mov    $0x1,%edx
    26e7:	48 8d 35 5a 4e 00 00 	lea    0x4e5a(%rip),%rsi        # 7548 <_IO_stdin_used+0x548>
    26ee:	31 c0                	xor    %eax,%eax
    26f0:	bf 01 00 00 00       	mov    $0x1,%edi
    26f5:	e8 56 fd ff ff       	call   2450 <__printf_chk@plt>
    26fa:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    26ff:	48 8d 35 c7 4b 00 00 	lea    0x4bc7(%rip),%rsi        # 72cd <_IO_stdin_used+0x2cd>
    2706:	31 c0                	xor    %eax,%eax
    2708:	bf 01 00 00 00       	mov    $0x1,%edi
    270d:	e8 3e fd ff ff       	call   2450 <__printf_chk@plt>
    2712:	ba 05 00 00 00       	mov    $0x5,%edx
    2717:	48 8d 35 c9 4b 00 00 	lea    0x4bc9(%rip),%rsi        # 72e7 <_IO_stdin_used+0x2e7>
    271e:	31 c0                	xor    %eax,%eax
    2720:	bf 01 00 00 00       	mov    $0x1,%edi
    2725:	e8 26 fd ff ff       	call   2450 <__printf_chk@plt>
    272a:	48 8d 3d 9d 49 00 00 	lea    0x499d(%rip),%rdi        # 70ce <_IO_stdin_used+0xce>
    2731:	e8 ba fb ff ff       	call   22f0 <puts@plt>
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    2736:	be 18 00 00 00       	mov    $0x18,%esi
    273b:	bf 06 00 00 00       	mov    $0x6,%edi
    2740:	e8 5b fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2745:	be b0 00 00 00       	mov    $0xb0,%esi
    274a:	bf 09 00 00 00       	mov    $0x9,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    274f:	49 89 c6             	mov    %rax,%r14
    2752:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2757:	e8 44 fc ff ff       	call   23a0 <calloc@plt>
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    275c:	be 10 00 00 00       	mov    $0x10,%esi
    2761:	bf 01 00 00 00       	mov    $0x1,%edi
    2766:	49 83 ee 18          	sub    $0x18,%r14
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    276a:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    276f:	4d 89 f4             	mov    %r14,%r12
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2772:	e8 29 fc ff ff       	call   23a0 <calloc@plt>
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2777:	be 10 00 00 00       	mov    $0x10,%esi
    277c:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    2781:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2787:	48 89 c3             	mov    %rax,%rbx
    278a:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    278f:	e8 0c fc ff ff       	call   23a0 <calloc@plt>
    2794:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
  int external_thread_index = 0;
    2799:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27a1:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
    27a5:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
            thread_data[x].tasks[y].run = barriered_work; 
    27ac:	4d 89 d1             	mov    %r10,%r9
    27af:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    27b4:	4c 89 54 24 60       	mov    %r10,0x60(%rsp)
    27b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27c0:	be 08 00 00 00       	mov    $0x8,%esi
    27c5:	bf 02 00 00 00       	mov    $0x2,%edi
    27ca:	89 6c 24 08          	mov    %ebp,0x8(%rsp)
    27ce:	41 89 ef             	mov    %ebp,%r15d
    27d1:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    27d6:	44 8d 6c 2d 00       	lea    0x0(%rbp,%rbp,1),%r13d
    27db:	e8 c0 fb ff ff       	call   23a0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27e0:	be 80 00 00 00       	mov    $0x80,%esi
    27e5:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27ea:	48 89 c3             	mov    %rax,%rbx
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27ed:	e8 ae fb ff ff       	call   23a0 <calloc@plt>
    if (x % 2 == 1) {
    27f2:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27f7:	49 89 c6             	mov    %rax,%r14
    if (x % 2 == 1) {
    27fa:	89 e8                	mov    %ebp,%eax
    27fc:	83 c5 01             	add    $0x1,%ebp
    27ff:	83 e0 01             	and    $0x1,%eax
    2802:	85 c0                	test   %eax,%eax
    2804:	0f 84 66 0c 00 00    	je     3470 <main+0xe80>
      my_thread_data[0] = &thread_data[other]; 
    280a:	49 8d 89 50 ff ff ff 	lea    -0xb0(%r9),%rcx
      my_thread_data[1] = &thread_data[x]; 
    2811:	4c 89 4b 08          	mov    %r9,0x8(%rbx)
      other = abs(x - 1) % total_threads;
    2815:	44 89 fa             	mov    %r15d,%edx
    2818:	31 c0                	xor    %eax,%eax
      my_thread_data[0] = &thread_data[other]; 
    281a:	48 89 0b             	mov    %rcx,(%rbx)
    281d:	4d 89 c8             	mov    %r9,%r8
    2820:	bf 01 00 00 00       	mov    $0x1,%edi
      other = abs(x - 1) % total_threads;
    2825:	45 8d 7f ff          	lea    -0x1(%r15),%r15d
      thread_data[x].thread_index = 1;
    2829:	41 c7 01 01 00 00 00 	movl   $0x1,(%r9)
    2830:	48 8d 35 c4 4a 00 00 	lea    0x4ac4(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
    2837:	e8 14 fc ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    283c:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2841:	4c 89 e0             	mov    %r12,%rax
    2844:	4d 8d 64 24 18       	lea    0x18(%r12),%r12
    2849:	49 89 41 38          	mov    %rax,0x38(%r9)
    284d:	45 8b 01             	mov    (%r9),%r8d
    2850:	44 89 f9             	mov    %r15d,%ecx
    2853:	bf 01 00 00 00       	mov    $0x1,%edi
    2858:	8b 54 24 08          	mov    0x8(%rsp),%edx
    285c:	48 8d 35 0d 4d 00 00 	lea    0x4d0d(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    2863:	31 c0                	xor    %eax,%eax
    2865:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    286a:	e8 e1 fb ff ff       	call   2450 <__printf_chk@plt>
    thread_data[x].other = other;
    286f:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2874:	44 89 e9             	mov    %r13d,%ecx
    2877:	31 c0                	xor    %eax,%eax
    2879:	48 8d 35 20 4d 00 00 	lea    0x4d20(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    2880:	bf 01 00 00 00       	mov    $0x1,%edi
    2885:	45 89 b9 a8 00 00 00 	mov    %r15d,0xa8(%r9)
    288c:	44 8b 7c 24 08       	mov    0x8(%rsp),%r15d
    2891:	44 89 fa             	mov    %r15d,%edx
    2894:	e8 b7 fb ff ff       	call   2450 <__printf_chk@plt>
      CPU_SET(curcpu, sendercpu);
    2899:	44 89 e9             	mov    %r13d,%ecx
    289c:	b8 01 00 00 00       	mov    $0x1,%eax
    thread_data[x].cpu_set = sendercpu;
    28a1:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
      CPU_SET(curcpu, sendercpu);
    28a6:	48 d3 e0             	shl    %cl,%rax
    28a9:	49 09 06             	or     %rax,(%r14)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28ac:	be 10 00 00 00       	mov    $0x10,%esi
    28b1:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].thread_count = 2;
    28b6:	48 8b 05 83 51 00 00 	mov    0x5183(%rip),%rax        # 7a40 <_IO_stdin_used+0xa40>
    thread_data[x].real_thread_index = x;
    28bd:	45 89 79 04          	mov    %r15d,0x4(%r9)
    thread_data[x].threads = my_thread_data;
    28c1:	49 89 59 10          	mov    %rbx,0x10(%r9)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28c5:	31 db                	xor    %ebx,%ebx
    thread_data[x].cpu_set = sendercpu;
    28c7:	4d 89 b1 a0 00 00 00 	mov    %r14,0xa0(%r9)
    thread_data[x].thread_count = 2;
    28ce:	49 89 41 18          	mov    %rax,0x18(%r9)
    thread_data[x].task_count = total_barrier_count;
    28d2:	41 c7 41 30 03 00 00 00 	movl   $0x3,0x30(%r9)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28da:	e8 c1 fa ff ff       	call   23a0 <calloc@plt>
    28df:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28e4:	be 10 00 00 00       	mov    $0x10,%esi
    28e9:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28ee:	49 89 41 58          	mov    %rax,0x58(%r9)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28f2:	e8 a9 fa ff ff       	call   23a0 <calloc@plt>
    28f7:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28fc:	be 28 00 00 00       	mov    $0x28,%esi
    thread_data[x].timestamp_count = 0;
    2901:	66 0f 6f 15 17 51 00 00 	movdqa 0x5117(%rip),%xmm2        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2909:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    290e:	49 89 41 60          	mov    %rax,0x60(%r9)
    thread_data[x].timestamp_count = 0;
    2912:	41 0f 11 51 70       	movups %xmm2,0x70(%r9)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2917:	e8 84 fa ff ff       	call   23a0 <calloc@plt>
    291c:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2921:	be 00 02 00 00       	mov    $0x200,%esi
    thread_data[x].task_timestamp_count = 0;
    2926:	66 0f 6f 1d f2 50 00 00 	movdqa 0x50f2(%rip),%xmm3        # 7a20 <_IO_stdin_used+0xa20>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    292e:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2933:	49 89 81 80 00 00 00 	mov    %rax,0x80(%r9)
    thread_data[x].task_timestamp_count = 0;
    293a:	41 0f 11 99 88 00 00 00 	movups %xmm3,0x88(%r9)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2942:	e8 59 fa ff ff       	call   23a0 <calloc@plt>
      thread_data[x].tasks = barriers;
    2947:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
        thread_data[x].tasks[y].sending = 1;
    294c:	89 6c 24 28          	mov    %ebp,0x28(%rsp)
    2950:	4c 89 64 24 40       	mov    %r12,0x40(%rsp)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2955:	49 89 c7             	mov    %rax,%r15
      thread_data[x].tasks = barriers;
    2958:	49 89 41 28          	mov    %rax,0x28(%r9)
        thread_data[x].tasks[y].sending = 1;
    295c:	4d 89 cd             	mov    %r9,%r13
        thread_data[x].tasks[y].protected = do_protected_write; 
    295f:	4c 63 e3             	movslq %ebx,%r12
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2962:	be 20 00 00 00       	mov    $0x20,%esi
    2967:	bf 06 00 00 00       	mov    $0x6,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    296c:	4d 89 e6             	mov    %r12,%r14
    296f:	48 8d 05 6a 0c 00 00 	lea    0xc6a(%rip),%rax        # 35e0 <do_protected_write>
    2976:	49 c1 e6 09          	shl    $0x9,%r14
    297a:	4d 01 f7             	add    %r14,%r15
    297d:	49 89 87 20 01 00 00 	mov    %rax,0x120(%r15)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2984:	e8 17 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    2989:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    298d:	4c 89 64 24 18       	mov    %r12,0x18(%rsp)
    2992:	48 8d 68 40          	lea    0x40(%rax),%rbp
    2996:	49 89 87 68 01 00 00 	mov    %rax,0x168(%r15)
        for (int b = 0 ; b < 2 ; b++) {
    299d:	49 89 c7             	mov    %rax,%r15
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29a0:	be 08 00 00 00       	mov    $0x8,%esi
    29a5:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    29aa:	49 83 c7 20          	add    $0x20,%r15
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29ae:	e8 ed f9 ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29b3:	be 08 00 00 00       	mov    $0x8,%esi
    29b8:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29bd:	49 89 c4             	mov    %rax,%r12
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29c0:	e8 db f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29c5:	be 18 00 00 00       	mov    $0x18,%esi
    29ca:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29cf:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29d2:	e8 c9 f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    29d7:	66 0f 6f 05 51 50 00 00 	movdqa 0x5051(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
          mailboxes[b].higher = &data[1];
    29df:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29e3:	49 89 47 e0          	mov    %rax,-0x20(%r15)
          mailboxes[b].higher = &data[1];
    29e7:	49 89 77 e8          	mov    %rsi,-0x18(%r15)
          data[0].messages = messages;
    29eb:	4c 89 20             	mov    %r12,(%rax)
          data[1].messages = messages2;
    29ee:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    29f2:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    29f6:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    29fa:	4c 39 fd             	cmp    %r15,%rbp
    29fd:	75 a1                	jne    29a0 <main+0x3b0>
        char *message = malloc(sizeof(char) * 256);
    29ff:	be 01 00 00 00       	mov    $0x1,%esi
    2a04:	bf 00 01 00 00       	mov    $0x100,%edi
    2a09:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    2a0d:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    2a12:	e8 89 f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a17:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a1c:	48 89 c5             	mov    %rax,%rbp
        struct Message *messaged = malloc(sizeof(struct Message));
    2a1f:	e8 ec f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a24:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    2a29:	48 89 ef             	mov    %rbp,%rdi
    2a2c:	41 89 d9             	mov    %ebx,%r9d
    2a2f:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2a34:	48 8d 0d 85 4b 00 00 	lea    0x4b85(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a3b:	ba 00 01 00 00       	mov    $0x100,%edx
    2a40:	31 c0                	xor    %eax,%eax
    2a42:	be 01 00 00 00       	mov    $0x1,%esi
    2a47:	e8 d4 fa ff ff       	call   2520 <__sprintf_chk@plt>
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a4c:	4d 8b 7d 28          	mov    0x28(%r13),%r15
        messaged->thread_index = thread_data[x].thread_index;
    2a50:	49 63 45 00          	movslq 0x0(%r13),%rax
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a54:	8d 4b 01             	lea    0x1(%rbx),%ecx
        messaged->message = message;
    2a57:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a5c:	be 20 00 00 00       	mov    $0x20,%esi
    2a61:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a66:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
        messaged->message = message;
    2a6a:	49 89 2a             	mov    %rbp,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a6d:	4b 8d 2c 37          	lea    (%r15,%r14,1),%rbp
        messaged->task_index = y;
    2a71:	4d 89 62 10          	mov    %r12,0x10(%r10)
        messaged->thread_index = thread_data[x].thread_index;
    2a75:	49 89 c4             	mov    %rax,%r12
    2a78:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a7c:	89 8d 88 01 00 00    	mov    %ecx,0x188(%rbp)
        thread_data[x].tasks[y].message = messaged;
    2a82:	4c 89 95 80 01 00 00 	mov    %r10,0x180(%rbp)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a89:	48 c7 85 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a94:	e8 07 f9 ff ff       	call   23a0 <calloc@plt>
        if (y == barrier_count - 1) {
    2a99:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2a9c:	89 5d 00             	mov    %ebx,0x0(%rbp)
        if (y == barrier_count - 1) {
    2a9f:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2aa3:	48 89 85 48 01 00 00 	mov    %rax,0x148(%rbp)
        thread_data[x].tasks[y].available = 1;
    2aaa:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2ab4:	48 89 85 38 01 00 00 	mov    %rax,0x138(%rbp)
        thread_data[x].tasks[y].sending = 1;
    2abb:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2ac5:	48 c7 85 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%rbp)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2ad0:	44 89 a5 30 01 00 00 	mov    %r12d,0x130(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2ad7:	4c 89 ad 28 01 00 00 	mov    %r13,0x128(%rbp)
        thread_data[x].tasks[y].arrived = 0;
    2ade:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        thread_data[x].tasks[y].thread_count = 2;
    2ae8:	c7 85 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%rbp)
        thread_data[x].tasks[y].sending = 1;
    2af2:	48 89 85 78 01 00 00 	mov    %rax,0x178(%rbp)
        if (y == barrier_count - 1) {
    2af9:	0f 84 51 09 00 00    	je     3450 <main+0xe60>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2aff:	8b 54 24 08          	mov    0x8(%rsp),%edx
    2b03:	39 d3                	cmp    %edx,%ebx
    2b05:	75 69                	jne    2b70 <main+0x580>
    2b07:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    2b0b:	85 db                	test   %ebx,%ebx
    2b0d:	7f 61                	jg     2b70 <main+0x580>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2b0f:	bf 01 00 00 00       	mov    $0x1,%edi
    2b14:	48 8d 35 cd 4a 00 00 	lea    0x4acd(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2b1b:	31 c0                	xor    %eax,%eax
    2b1d:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
    2b21:	e8 2a f9 ff ff       	call   2450 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b26:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    2b2b:	48 63 c3             	movslq %ebx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b2e:	4d 8b 7d 28          	mov    0x28(%r13),%r15
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b32:	48 89 c7             	mov    %rax,%rdi
    2b35:	48 c1 e0 04          	shl    $0x4,%rax
    2b39:	48 01 c8             	add    %rcx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b3c:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b40:	49 89 45 40          	mov    %rax,0x40(%r13)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b44:	48 8d 05 e5 2f 00 00 	lea    0x2fe5(%rip),%rax        # 5b30 <barriered_work_ingest>
    2b4b:	4b 89 84 37 18 01 00 00 	mov    %rax,0x118(%r15,%r14,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b53:	8d 47 01             	lea    0x1(%rdi),%eax
    2b56:	89 44 24 20          	mov    %eax,0x20(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b5a:	83 f9 03             	cmp    $0x3,%ecx
    2b5d:	74 24                	je     2b83 <main+0x593>
    2b5f:	bb 01 00 00 00       	mov    $0x1,%ebx
    2b64:	e9 f6 fd ff ff       	jmp    295f <main+0x36f>
    2b69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            thread_data[x].tasks[y].run = barriered_work; 
    2b70:	48 8d 05 b9 2a 00 00 	lea    0x2ab9(%rip),%rax        # 5630 <barriered_work>
    2b77:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b7e:	83 f9 03             	cmp    $0x3,%ecx
    2b81:	75 dc                	jne    2b5f <main+0x56f>

          }
        }
      }
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b83:	66 0f 6f 64 24 30    	movdqa 0x30(%rsp),%xmm4
    2b89:	8b 6c 24 28          	mov    0x28(%rsp),%ebp
    2b8d:	4d 89 e9             	mov    %r13,%r9
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b90:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2b9a:	41 c7 87 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r15)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2ba5:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
  for (int x = 0 ; x < total_threads ; x++) {
    2baa:	49 81 c1 b0 00 00 00 	add    $0xb0,%r9
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2bb1:	41 c7 87 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%r15)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2bbc:	49 89 87 34 05 00 00 	mov    %rax,0x534(%r15)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bc3:	41 8b 45 00          	mov    0x0(%r13),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2bc7:	4d 89 af 28 05 00 00 	mov    %r13,0x528(%r15)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bce:	41 89 87 30 05 00 00 	mov    %eax,0x530(%r15)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2bd5:	41 c7 87 7c 05 00 00 06 00 00 00 	movl   $0x6,0x57c(%r15)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2be0:	41 c7 87 3c 05 00 00 03 00 00 00 	movl   $0x3,0x53c(%r15)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2beb:	41 0f 11 a7 18 05 00 00 	movups %xmm4,0x518(%r15)
  for (int x = 0 ; x < total_threads ; x++) {
    2bf3:	83 fd 09             	cmp    $0x9,%ebp
    2bf6:	0f 85 c4 fb ff ff    	jne    27c0 <main+0x1d0>
    2bfc:	4c 8b 44 24 60       	mov    0x60(%rsp),%r8
    2c01:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    2c06:	31 c0                	xor    %eax,%eax
    2c08:	ba 07 00 00 00       	mov    $0x7,%edx
    2c0d:	48 8d 35 04 47 00 00 	lea    0x4704(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2c14:	bf 01 00 00 00       	mov    $0x1,%edi
    2c19:	4c 89 44 24 78       	mov    %r8,0x78(%rsp)
    2c1e:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2c23:	e8 28 f8 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c28:	be 08 00 00 00       	mov    $0x8,%esi
    2c2d:	bf 02 00 00 00       	mov    $0x2,%edi
    2c32:	e8 69 f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2c37:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c3c:	bf 09 00 00 00       	mov    $0x9,%edi
    my_thread_data[0] = &thread_data[x]; 
    2c41:	4d 8d ba d0 04 00 00 	lea    0x4d0(%r10),%r15
    thread_data[n].tasks[0].scheduled = 1;
    2c48:	4c 89 54 24 40       	mov    %r10,0x40(%rsp)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c4d:	4d 8d b2 60 01 00 00 	lea    0x160(%r10),%r14
    thread_data[x].threads = my_thread_data;
    2c54:	49 89 82 e0 04 00 00 	mov    %rax,0x4e0(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2c5b:	49 8d b2 70 03 00 00 	lea    0x370(%r10),%rsi
    2c62:	4d 8d a2 b0 00 00 00 	lea    0xb0(%r10),%r12
    my_thread_data[0] = &thread_data[x]; 
    2c69:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c6c:	49 8d 8a c0 02 00 00 	lea    0x2c0(%r10),%rcx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c73:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c77:	49 8b 42 28          	mov    0x28(%r10),%rax
    thread_data[x].thread_count = 2;
    2c7b:	41 c7 82 e8 04 00 00 02 00 00 00 	movl   $0x2,0x4e8(%r10)
    thread_data[x].thread_index = 0;
    2c86:	41 c7 82 d0 04 00 00 00 00 00 00 	movl   $0x0,0x4d0(%r10)
    thread_data[x].task_count = total_barrier_count;
    2c91:	41 c7 82 00 05 00 00 03 00 00 00 	movl   $0x3,0x500(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2c9c:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2ca6:	49 8b 82 d8 00 00 00 	mov    0xd8(%r10),%rax
    2cad:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cb2:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2cb7:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cc1:	49 8b 82 88 01 00 00 	mov    0x188(%r10),%rax
    2cc8:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    2ccd:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cd7:	49 8d 82 10 02 00 00 	lea    0x210(%r10),%rax
    2cde:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2ce3:	49 8b 82 38 02 00 00 	mov    0x238(%r10),%rax
    my_thread_data[0] = &thread_data[x]; 
    2cea:	4c 89 7c 24 20       	mov    %r15,0x20(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2cef:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cf9:	49 8b 82 e8 02 00 00 	mov    0x2e8(%r10),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2d00:	4c 89 74 24 28       	mov    %r14,0x28(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d05:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d0f:	49 8b 82 98 03 00 00 	mov    0x398(%r10),%rax
    2d16:	4c 89 64 24 30       	mov    %r12,0x30(%rsp)
    2d1b:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d25:	e8 76 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d2a:	be 38 00 00 00       	mov    $0x38,%esi
    2d2f:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d34:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d37:	e8 64 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d3c:	be 38 00 00 00       	mov    $0x38,%esi
    2d41:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d46:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d49:	e8 52 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d4e:	be 38 00 00 00       	mov    $0x38,%esi
    2d53:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d58:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d5d:	e8 3e f6 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d62:	be 08 00 00 00       	mov    $0x8,%esi
    2d67:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d6c:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d71:	e8 2a f6 ff ff       	call   23a0 <calloc@plt>

  thread_data[thread_count].type = TIMER;
    2d76:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2d7b:	be 08 00 00 00       	mov    $0x8,%esi
    2d80:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d85:	49 89 c5             	mov    %rax,%r13
  thread_data[thread_count].task_count = total_barrier_count;
    2d88:	48 8b 05 b9 4c 00 00 	mov    0x4cb9(%rip),%rax        # 7a48 <_IO_stdin_used+0xa48>
  thread_data[thread_count].type = TIMER;
    2d8f:	41 c7 82 28 04 00 00 00 00 00 00 	movl   $0x0,0x428(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2d9a:	49 89 82 50 04 00 00 	mov    %rax,0x450(%r10)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2da1:	e8 fa f5 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2da6:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    2dab:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    2db0:	ba 06 00 00 00       	mov    $0x6,%edx
    2db5:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2dba:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2dbf:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2dc3:	48 89 78 18          	mov    %rdi,0x18(%rax)
    2dc7:	4d 8d b2 20 04 00 00 	lea    0x420(%r10),%r14
    2dce:	49 8d ba 80 05 00 00 	lea    0x580(%r10),%rdi
    2dd5:	4c 89 10             	mov    %r10,(%rax)
    2dd8:	4c 89 60 08          	mov    %r12,0x8(%rax)
    2ddc:	4c 8d 25 ad 08 00 00 	lea    0x8ad(%rip),%r12        # 3690 <barriered_thread>
    2de3:	48 89 48 20          	mov    %rcx,0x20(%rax)
    2de7:	48 89 70 28          	mov    %rsi,0x28(%rax)
    2deb:	48 8d 35 35 45 00 00 	lea    0x4535(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2df2:	4c 89 70 30          	mov    %r14,0x30(%rax)
    2df6:	4c 89 78 38          	mov    %r15,0x38(%rax)
    2dfa:	4c 8d 3d 07 48 00 00 	lea    0x4807(%rip),%r15        # 7608 <_IO_stdin_used+0x608>
    2e01:	48 89 78 40          	mov    %rdi,0x40(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2e05:	49 89 82 30 04 00 00 	mov    %rax,0x430(%r10)
    2e0c:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2e0e:	41 c7 82 38 04 00 00 06 00 00 00 	movl   $0x6,0x438(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2e19:	41 c7 82 40 04 00 00 02 00 00 00 	movl   $0x2,0x440(%r10)
  thread_data[thread_count].thread_index = 0;
    2e24:	41 c7 82 20 04 00 00 00 00 00 00 	movl   $0x0,0x420(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2e2f:	48 89 7c 24 40       	mov    %rdi,0x40(%rsp)
    2e34:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].thread_index = 0;
    2e39:	4c 89 54 24 68       	mov    %r10,0x68(%rsp)
    2e3e:	e8 0d f6 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2e43:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2e4a:	49 8d 7d 30          	lea    0x30(%r13),%rdi
    2e4e:	4c 89 f1             	mov    %r14,%rcx
    2e51:	48 8d 15 a8 0b 00 00 	lea    0xba8(%rip),%rdx        # 3a00 <timer_thread>
    2e58:	4c 89 eb             	mov    %r13,%rbx
  for (int x = 0 ; x < thread_count ; x++) {
    2e5b:	45 31 f6             	xor    %r14d,%r14d
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2e5e:	e8 0d f6 ff ff       	call   2470 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2e63:	4c 89 6c 24 70       	mov    %r13,0x70(%rsp)
    2e68:	4c 8b 6c 24 78       	mov    0x78(%rsp),%r13
    2e6d:	0f 1f 00             	nopl   (%rax)
    thread_data[x].type = WORKER;
    2e70:	41 c7 45 08 01 00 00 00 	movl   $0x1,0x8(%r13)
    2e78:	44 89 f2             	mov    %r14d,%edx
    2e7b:	4c 89 fe             	mov    %r15,%rsi
    2e7e:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2e80:	41 c7 45 34 01 00 00 00 	movl   $0x1,0x34(%r13)
    2e88:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < thread_count ; x++) {
    2e8d:	41 83 c6 01          	add    $0x1,%r14d
    2e91:	e8 ba f5 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2e96:	4c 89 e9             	mov    %r13,%rcx
    2e99:	48 89 ee             	mov    %rbp,%rsi
    2e9c:	48 89 df             	mov    %rbx,%rdi
    2e9f:	4c 89 e2             	mov    %r12,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2ea2:	49 81 c5 b0 00 00 00 	add    $0xb0,%r13
    2ea9:	48 83 c3 08          	add    $0x8,%rbx
    2ead:	48 83 c5 38          	add    $0x38,%rbp
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2eb1:	e8 ba f5 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2eb6:	49 8b 55 f0          	mov    -0x10(%r13),%rdx
    2eba:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    2ebe:	be 08 00 00 00       	mov    $0x8,%esi
    2ec3:	e8 18 f4 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2ec8:	41 83 fe 06          	cmp    $0x6,%r14d
    2ecc:	75 a2                	jne    2e70 <main+0x880>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2ece:	4c 8b 54 24 68       	mov    0x68(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ed3:	be d8 00 00 00       	mov    $0xd8,%esi
    2ed8:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    2edd:	48 8b 1d 6c 4b 00 00 	mov    0x4b6c(%rip),%rbx        # 7a50 <_IO_stdin_used+0xa50>
    thread_data[x].type = IO;
    2ee4:	4c 8b 6c 24 70       	mov    0x70(%rsp),%r13
    thread_data[x].task_count = 0;
    2ee9:	49 89 9a 00 05 00 00 	mov    %rbx,0x500(%r10)
    thread_data[x].type = IO;
    2ef0:	41 c7 82 d8 04 00 00 02 00 00 00 	movl   $0x2,0x4d8(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2efb:	e8 a0 f4 ff ff       	call   23a0 <calloc@plt>
    2f00:	4c 8b 54 24 68       	mov    0x68(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f05:	be 00 08 00 00       	mov    $0x800,%esi
    2f0a:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f0c:	49 89 82 18 05 00 00 	mov    %rax,0x518(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f13:	e8 98 f5 ff ff       	call   24b0 <eventfd@plt>
    2f18:	4c 8b 54 24 68       	mov    0x68(%rsp),%r10
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f1d:	be 08 00 00 00       	mov    $0x8,%esi
    2f22:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f27:	41 89 82 20 05 00 00 	mov    %eax,0x520(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f2e:	e8 6d f4 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    2f33:	4c 8b 54 24 68       	mov    0x68(%rsp),%r10
    2f38:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
    2f3d:	ba 07 00 00 00       	mov    $0x7,%edx
    2f42:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    2f47:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    2f4c:	48 8d 35 f2 43 00 00 	lea    0x43f2(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    2f53:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    2f58:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    2f5d:	4c 89 10             	mov    %r10,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    2f60:	49 89 82 e0 04 00 00 	mov    %rax,0x4e0(%r10)
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    2f67:	41 c7 82 e8 04 00 00 06 00 00 00 	movl   $0x6,0x4e8(%r10)
    thread_data[x].thread_index = x;
    2f72:	41 c7 82 d0 04 00 00 07 00 00 00 	movl   $0x7,0x4d0(%r10)
      my_thread_data[n] = &thread_data[n]; 
    2f7d:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2f81:	48 89 68 18          	mov    %rbp,0x18(%rax)
    2f85:	4c 89 60 20          	mov    %r12,0x20(%rax)
    2f89:	48 89 78 28          	mov    %rdi,0x28(%rax)
    2f8d:	bf 01 00 00 00       	mov    $0x1,%edi
    2f92:	4c 89 78 10          	mov    %r15,0x10(%rax)
    2f96:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    2f98:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    2f9d:	e8 ae f4 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2fa2:	48 8b 74 24 50       	mov    0x50(%rsp),%rsi
    2fa7:	49 8d 7d 38          	lea    0x38(%r13),%rdi
    2fab:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    2fb0:	48 8d 15 b9 1c 00 00 	lea    0x1cb9(%rip),%rdx        # 4c70 <io_thread>
    2fb7:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2fbe:	e8 ad f4 ff ff       	call   2470 <pthread_create@plt>
    2fc3:	ba 08 00 00 00       	mov    $0x8,%edx
    2fc8:	48 8d 35 8d 43 00 00 	lea    0x438d(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    2fcf:	31 c0                	xor    %eax,%eax
    2fd1:	bf 01 00 00 00       	mov    $0x1,%edi
    2fd6:	e8 75 f4 ff ff       	call   2450 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    2fdb:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    2fe0:	48 8b 44 24 48       	mov    0x48(%rsp),%rax

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2fe5:	be 08 00 00 00       	mov    $0x8,%esi
    2fea:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[x].task_count = 0;
    2fef:	49 89 9a b0 05 00 00 	mov    %rbx,0x5b0(%r10)
    2ff6:	31 db                	xor    %ebx,%ebx
    thread_data[x].type = EXTERNAL;
    2ff8:	41 c7 82 88 05 00 00 03 00 00 00 	movl   $0x3,0x588(%r10)
    thread_data[x].buffers = &buffers[buffer_index];
    3003:	49 89 82 c0 05 00 00 	mov    %rax,0x5c0(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    300a:	e8 91 f3 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    300f:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    3014:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3019:	48 8d 15 20 09 00 00 	lea    0x920(%rip),%rdx        # 3940 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    3020:	4c 89 70 08          	mov    %r14,0x8(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3024:	48 8b 74 24 60       	mov    0x60(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3029:	4c 89 10             	mov    %r10,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    302c:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
      my_thread_data[n] = &thread_data[n]; 
    3031:	48 89 68 18          	mov    %rbp,0x18(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3035:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    303c:	48 8d 2d 54 43 00 00 	lea    0x4354(%rip),%rbp        # 7397 <_IO_stdin_used+0x397>
      my_thread_data[n] = &thread_data[n]; 
    3043:	4c 89 60 20          	mov    %r12,0x20(%rax)
    3047:	4c 8d a4 24 80 00 00 00 	lea    0x80(%rsp),%r12
    304f:	48 89 78 28          	mov    %rdi,0x28(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3053:	49 8d 7d 40          	lea    0x40(%r13),%rdi
    thread_data[x].threads = my_thread_data;
    3057:	49 89 82 90 05 00 00 	mov    %rax,0x590(%r10)
      my_thread_data[n] = &thread_data[n]; 
    305e:	4c 89 78 10          	mov    %r15,0x10(%rax)
    thread_data[x].thread_count = thread_count;
    3062:	48 8b 05 ef 49 00 00 	mov    0x49ef(%rip),%rax        # 7a58 <_IO_stdin_used+0xa58>
    thread_data[x].thread_index = x;
    3069:	41 c7 82 80 05 00 00 08 00 00 00 	movl   $0x8,0x580(%r10)
    thread_data[x].thread_count = thread_count;
    3074:	49 89 82 98 05 00 00 	mov    %rax,0x598(%r10)
    thread_data[x].thread_index = x;
    307b:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3080:	e8 eb f3 ff ff       	call   2470 <pthread_create@plt>
    3085:	48 8d 3d ed 42 00 00 	lea    0x42ed(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    308c:	e8 5f f2 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3091:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    3096:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    void * result; 
    pthread_join(thread[x], &result);
    30a0:	49 8b 7c dd 00       	mov    0x0(%r13,%rbx,8),%rdi
    30a5:	4c 89 e6             	mov    %r12,%rsi
    30a8:	e8 43 f4 ff ff       	call   24f0 <pthread_join@plt>
    30ad:	89 da                	mov    %ebx,%edx
    30af:	48 89 ee             	mov    %rbp,%rsi
    30b2:	bf 01 00 00 00       	mov    $0x1,%edi
    30b7:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    30b9:	48 83 c3 01          	add    $0x1,%rbx
    30bd:	e8 8e f3 ff ff       	call   2450 <__printf_chk@plt>
    30c2:	48 83 fb 09          	cmp    $0x9,%rbx
    30c6:	75 d8                	jne    30a0 <main+0xab0>
    30c8:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    30cd:	4d 89 f2             	mov    %r14,%r10
    30d0:	4d 8d 6e 28          	lea    0x28(%r14),%r13
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    30d4:	31 db                	xor    %ebx,%ebx
  for (int x = 0 ; x < thread_count ; x++) {
    30d6:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
  long sents = 0;
    30de:	31 ed                	xor    %ebp,%ebp
  long sends = 0;
    30e0:	45 31 ff             	xor    %r15d,%r15d
  long ingests = 0;
    30e3:	45 31 c9             	xor    %r9d,%r9d
    30e6:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  long total = 0;
    30eb:	45 31 f6             	xor    %r14d,%r14d
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    30ee:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    30f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (x % 2 == 1) {
    30f8:	8b 7c 24 08          	mov    0x8(%rsp),%edi
    30fc:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    3101:	89 f8                	mov    %edi,%eax
    3103:	41 89 fc             	mov    %edi,%r12d
      other = (x + 1) % total_threads;
    3106:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
    3109:	83 e0 01             	and    $0x1,%eax
      other = abs(x - 1) % total_threads;
    310c:	41 83 ec 01          	sub    $0x1,%r12d
      other = (x + 1) % total_threads;
    3110:	89 7c 24 08          	mov    %edi,0x8(%rsp)
      other = abs(x - 1) % total_threads;
    3114:	85 c0                	test   %eax,%eax
    3116:	44 0f 44 e7          	cmove  %edi,%r12d
    311a:	bf 0a 00 00 00       	mov    $0xa,%edi
    311f:	e8 ac f1 ff ff       	call   22d0 <putchar@plt>
    3124:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3129:	bf 01 00 00 00       	mov    $0x1,%edi
    312e:	48 8d 35 76 42 00 00 	lea    0x4276(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    3135:	48 8b 10             	mov    (%rax),%rdx
    3138:	31 c0                	xor    %eax,%eax
    313a:	e8 11 f3 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    313f:	49 63 55 08          	movslq 0x8(%r13),%rdx
    3143:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3148:	85 d2                	test   %edx,%edx
    314a:	0f 8e 8d 03 00 00    	jle    34dd <main+0xeed>
    3150:	49 8b 45 00          	mov    0x0(%r13),%rax
    3154:	48 c1 e2 09          	shl    $0x9,%rdx
    3158:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    long v = 0;
    315c:	31 d2                	xor    %edx,%edx
    315e:	66 90                	xchg   %ax,%ax
      v += thread_data[me].tasks[n].v;
    3160:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3167:	48 05 00 02 00 00    	add    $0x200,%rax
    316d:	48 39 f0             	cmp    %rsi,%rax
    3170:	75 ee                	jne    3160 <main+0xb70>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3172:	4d 63 e4             	movslq %r12d,%r12
    3175:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    317a:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    317e:	49 8d 04 44          	lea    (%r12,%rax,2),%rax
    3182:	48 c1 e0 04          	shl    $0x4,%rax
    3186:	48 01 f8             	add    %rdi,%rax
    3189:	48 63 70 30          	movslq 0x30(%rax),%rsi
    318d:	85 f6                	test   %esi,%esi
    318f:	7e 21                	jle    31b2 <main+0xbc2>
    3191:	48 8b 40 28          	mov    0x28(%rax),%rax
    3195:	48 c1 e6 09          	shl    $0x9,%rsi
    3199:	48 01 c6             	add    %rax,%rsi
    319c:	0f 1f 40 00          	nopl   0x0(%rax)
      v += thread_data[other].tasks[n].v;
    31a0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    31a7:	48 05 00 02 00 00    	add    $0x200,%rax
    31ad:	48 39 c6             	cmp    %rax,%rsi
    31b0:	75 ee                	jne    31a0 <main+0xbb0>
    31b2:	48 8d 35 07 42 00 00 	lea    0x4207(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    31b9:	bf 01 00 00 00       	mov    $0x1,%edi
    31be:	31 c0                	xor    %eax,%eax
    31c0:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    31c5:	e8 86 f2 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    31ca:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    31cf:	bf 01 00 00 00       	mov    $0x1,%edi
    31d4:	48 8b 30             	mov    (%rax),%rsi
    31d7:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    31e1:	48 f7 ee             	imul   %rsi
    31e4:	48 c1 fe 3f          	sar    $0x3f,%rsi
    31e8:	31 c0                	xor    %eax,%eax
    31ea:	48 d1 fa             	sar    %rdx
    31ed:	48 29 f2             	sub    %rsi,%rdx
    31f0:	48 8d 35 39 44 00 00 	lea    0x4439(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    31f7:	e8 54 f2 ff ff       	call   2450 <__printf_chk@plt>
    31fc:	bf 0a 00 00 00       	mov    $0xa,%edi
    3201:	e8 ca f0 ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3206:	49 63 45 08          	movslq 0x8(%r13),%rax
    320a:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    320f:	85 c0                	test   %eax,%eax
    3211:	7e 71                	jle    3284 <main+0xc94>
    3213:	49 8b 55 00          	mov    0x0(%r13),%rdx
    3217:	48 c1 e0 09          	shl    $0x9,%rax
    321b:	48 8d 34 10          	lea    (%rax,%rdx,1),%rsi
    321f:	90                   	nop
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3220:	48 8b 82 68 01 00 00 	mov    0x168(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    3227:	4c 03 b2 08 01 00 00 	add    0x108(%rdx),%r14
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    322e:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
      ingests += thread_data[x].tasks[n].ingest_count;
    3235:	4c 03 8a 60 ff ff ff 	add    -0xa0(%rdx),%r9
      sends += thread_data[x].tasks[n].sends;
    323c:	4c 03 ba 70 ff ff ff 	add    -0x90(%rdx),%r15
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3243:	48 03 68 10          	add    0x10(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3247:	48 03 58 18          	add    0x18(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    324b:	48 03 68 30          	add    0x30(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    324f:	48 03 58 38          	add    0x38(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3253:	48 03 68 50          	add    0x50(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3257:	48 03 58 58          	add    0x58(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    325b:	48 03 68 70          	add    0x70(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    325f:	48 03 58 78          	add    0x78(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3263:	48 03 a8 90 00 00 00 	add    0x90(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    326a:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3271:	48 03 a8 b0 00 00 00 	add    0xb0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3278:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    327f:	48 39 f2             	cmp    %rsi,%rdx
    3282:	75 9c                	jne    3220 <main+0xc30>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3284:	45 31 e4             	xor    %r12d,%r12d
    3287:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    328c:	7e 79                	jle    3307 <main+0xd17>
    328e:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    3293:	4c 89 eb             	mov    %r13,%rbx
    3296:	4d 89 e5             	mov    %r12,%r13
    3299:	4d 89 cc             	mov    %r9,%r12
    329c:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    32a0:	48 8b 43 58          	mov    0x58(%rbx),%rax
    32a4:	4b 8d 54 ad 00       	lea    0x0(%r13,%r13,4),%rdx
    32a9:	48 83 ec 08          	sub    $0x8,%rsp
    32ad:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    32b2:	49 83 c5 01          	add    $0x1,%r13
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    32b6:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32ba:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    32c4:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    32c8:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32cc:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    32cf:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    32d3:	4c 2b 01             	sub    (%rcx),%r8
    32d6:	31 c0                	xor    %eax,%eax
    32d8:	8b 49 20             	mov    0x20(%rcx),%ecx
    32db:	56                   	push   %rsi
    32dc:	48 8d 35 6d 43 00 00 	lea    0x436d(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    32e3:	48 c1 ea 12          	shr    $0x12,%rdx
    32e7:	49 89 d1             	mov    %rdx,%r9
    32ea:	ba 02 00 00 00       	mov    $0x2,%edx
    32ef:	e8 5c f1 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    32f4:	58                   	pop    %rax
    32f5:	5a                   	pop    %rdx
    32f6:	4c 39 6b 68          	cmp    %r13,0x68(%rbx)
    32fa:	7f a4                	jg     32a0 <main+0xcb0>
    32fc:	49 89 dd             	mov    %rbx,%r13
    32ff:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    3304:	4d 89 e1             	mov    %r12,%r9
  for (int x = 0 ; x < thread_count ; x++) {
    3307:	48 83 44 24 10 18    	addq   $0x18,0x10(%rsp)
    330d:	49 81 c5 b0 00 00 00 	add    $0xb0,%r13
    3314:	83 7c 24 08 06       	cmpl   $0x6,0x8(%rsp)
    3319:	0f 85 d9 fd ff ff    	jne    30f8 <main+0xb08>
    331f:	4c 89 f2             	mov    %r14,%rdx
    3322:	bf 01 00 00 00       	mov    $0x1,%edi
    3327:	31 c0                	xor    %eax,%eax
    3329:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    332e:	48 8d 35 98 40 00 00 	lea    0x4098(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3335:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    333f:	e8 0c f1 ff ff       	call   2450 <__printf_chk@plt>
    3344:	bf 0a 00 00 00       	mov    $0xa,%edi
    3349:	e8 82 ef ff ff       	call   22d0 <putchar@plt>
    334e:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    3353:	bf 01 00 00 00       	mov    $0x1,%edi
    3358:	48 8d 35 41 43 00 00 	lea    0x4341(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    335f:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3363:	31 c0                	xor    %eax,%eax
    3365:	e8 e6 f0 ff ff       	call   2450 <__printf_chk@plt>
    336a:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    336f:	bf 01 00 00 00       	mov    $0x1,%edi
    3374:	48 8d 35 4d 43 00 00 	lea    0x434d(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    337b:	4c 89 c8             	mov    %r9,%rax
    337e:	49 c1 f9 3f          	sar    $0x3f,%r9
    3382:	49 f7 ec             	imul   %r12
    3385:	31 c0                	xor    %eax,%eax
    3387:	48 d1 fa             	sar    %rdx
    338a:	4c 29 ca             	sub    %r9,%rdx
    338d:	e8 be f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3392:	4c 89 f8             	mov    %r15,%rax
    3395:	4d 89 fb             	mov    %r15,%r11
    3398:	bf 01 00 00 00       	mov    $0x1,%edi
    339d:	49 f7 ec             	imul   %r12
    33a0:	49 c1 fb 3f          	sar    $0x3f,%r11
    33a4:	48 8d 35 4d 43 00 00 	lea    0x434d(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    33ab:	31 c0                	xor    %eax,%eax
    33ad:	48 d1 fa             	sar    %rdx
    33b0:	4c 29 da             	sub    %r11,%rdx
    33b3:	e8 98 f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    33b8:	4c 89 f0             	mov    %r14,%rax
    33bb:	4c 89 f1             	mov    %r14,%rcx
    33be:	bf 01 00 00 00       	mov    $0x1,%edi
    33c3:	49 f7 ec             	imul   %r12
    33c6:	48 c1 f9 3f          	sar    $0x3f,%rcx
    33ca:	48 8d 35 57 43 00 00 	lea    0x4357(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    33d1:	31 c0                	xor    %eax,%eax
    33d3:	48 d1 fa             	sar    %rdx
    33d6:	48 29 ca             	sub    %rcx,%rdx
    33d9:	e8 72 f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    33de:	48 89 e8             	mov    %rbp,%rax
    33e1:	48 c1 fd 3f          	sar    $0x3f,%rbp
    33e5:	48 8d 35 f5 3f 00 00 	lea    0x3ff5(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    33ec:	49 f7 ec             	imul   %r12
    33ef:	bf 01 00 00 00       	mov    $0x1,%edi
    33f4:	31 c0                	xor    %eax,%eax
    33f6:	48 d1 fa             	sar    %rdx
    33f9:	48 29 ea             	sub    %rbp,%rdx
    33fc:	e8 4f f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3401:	48 89 d8             	mov    %rbx,%rax
    3404:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3408:	48 8d 35 e3 3f 00 00 	lea    0x3fe3(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    340f:	49 f7 ec             	imul   %r12
    3412:	bf 01 00 00 00       	mov    $0x1,%edi
    3417:	48 d1 fa             	sar    %rdx
    341a:	48 29 da             	sub    %rbx,%rdx
    341d:	31 c0                	xor    %eax,%eax
    341f:	e8 2c f0 ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3424:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    342c:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3435:	0f 85 a9 00 00 00    	jne    34e4 <main+0xef4>
    343b:	48 81 c4 98 00 00 00 	add    $0x98,%rsp
    3442:	31 c0                	xor    %eax,%eax
    3444:	5b                   	pop    %rbx
    3445:	5d                   	pop    %rbp
    3446:	41 5c                	pop    %r12
    3448:	41 5d                	pop    %r13
    344a:	41 5e                	pop    %r14
    344c:	41 5f                	pop    %r15
    344e:	c3                   	ret
    344f:	90                   	nop
          thread_data[x].tasks[y].run = barriered_work; 
    3450:	48 8d 05 d9 21 00 00 	lea    0x21d9(%rip),%rax        # 5630 <barriered_work>
    3457:	bb 02 00 00 00       	mov    $0x2,%ebx
    345c:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3463:	e9 f7 f4 ff ff       	jmp    295f <main+0x36f>
    3468:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      other = (x + 1) % total_threads;
    3470:	41 89 ef             	mov    %ebp,%r15d
      my_thread_data[0] = &thread_data[x]; 
    3473:	4c 89 0b             	mov    %r9,(%rbx)
    3476:	4c 89 c9             	mov    %r9,%rcx
    3479:	48 8d 35 89 3e 00 00 	lea    0x3e89(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      other = (x + 1) % total_threads;
    3480:	4d 69 ff 39 8e e3 38 	imul   $0x38e38e39,%r15,%r15
      thread_data[x].thread_index = 0;
    3487:	41 c7 01 00 00 00 00 	movl   $0x0,(%r9)
    348e:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].protected_state = &protected_state[x];
    3493:	49 83 c4 18          	add    $0x18,%r12
    3497:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
      other = (x + 1) % total_threads;
    349c:	49 c1 ef 21          	shr    $0x21,%r15
    34a0:	43 8d 04 ff          	lea    (%r15,%r15,8),%eax
    34a4:	41 89 ef             	mov    %ebp,%r15d
    34a7:	41 29 c7             	sub    %eax,%r15d
      my_thread_data[1] = &thread_data[other]; 
    34aa:	49 63 c7             	movslq %r15d,%rax
    34ad:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    34b1:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    34b5:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    34ba:	8b 54 24 08          	mov    0x8(%rsp),%edx
    34be:	49 c1 e0 04          	shl    $0x4,%r8
    34c2:	49 01 c0             	add    %rax,%r8
    34c5:	31 c0                	xor    %eax,%eax
    34c7:	4c 89 43 08          	mov    %r8,0x8(%rbx)
    34cb:	e8 80 ef ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    34d0:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    34d5:	4c 89 e0             	mov    %r12,%rax
    34d8:	e9 6c f3 ff ff       	jmp    2849 <main+0x259>
    long v = 0;
    34dd:	31 d2                	xor    %edx,%edx
    34df:	e9 8e fc ff ff       	jmp    3172 <main+0xb82>
}
    34e4:	e8 47 ee ff ff       	call   2330 <__stack_chk_fail@plt>
    34e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000034f0 <_start>:
    34f0:	f3 0f 1e fa          	endbr64
    34f4:	31 ed                	xor    %ebp,%ebp
    34f6:	49 89 d1             	mov    %rdx,%r9
    34f9:	5e                   	pop    %rsi
    34fa:	48 89 e2             	mov    %rsp,%rdx
    34fd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3501:	50                   	push   %rax
    3502:	54                   	push   %rsp
    3503:	45 31 c0             	xor    %r8d,%r8d
    3506:	31 c9                	xor    %ecx,%ecx
    3508:	48 8d 3d e1 f0 ff ff 	lea    -0xf1f(%rip),%rdi        # 25f0 <main>
    350f:	ff 15 c3 6a 00 00    	call   *0x6ac3(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3515:	f4                   	hlt
    3516:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003520 <deregister_tm_clones>:
    3520:	48 8d 3d f9 6a 00 00 	lea    0x6af9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3527:	48 8d 05 f2 6a 00 00 	lea    0x6af2(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    352e:	48 39 f8             	cmp    %rdi,%rax
    3531:	74 15                	je     3548 <deregister_tm_clones+0x28>
    3533:	48 8b 05 a6 6a 00 00 	mov    0x6aa6(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    353a:	48 85 c0             	test   %rax,%rax
    353d:	74 09                	je     3548 <deregister_tm_clones+0x28>
    353f:	ff e0                	jmp    *%rax
    3541:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3548:	c3                   	ret
    3549:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003550 <register_tm_clones>:
    3550:	48 8d 3d c9 6a 00 00 	lea    0x6ac9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3557:	48 8d 35 c2 6a 00 00 	lea    0x6ac2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    355e:	48 29 fe             	sub    %rdi,%rsi
    3561:	48 89 f0             	mov    %rsi,%rax
    3564:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3568:	48 c1 f8 03          	sar    $0x3,%rax
    356c:	48 01 c6             	add    %rax,%rsi
    356f:	48 d1 fe             	sar    %rsi
    3572:	74 14                	je     3588 <register_tm_clones+0x38>
    3574:	48 8b 05 75 6a 00 00 	mov    0x6a75(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    357b:	48 85 c0             	test   %rax,%rax
    357e:	74 08                	je     3588 <register_tm_clones+0x38>
    3580:	ff e0                	jmp    *%rax
    3582:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3588:	c3                   	ret
    3589:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003590 <__do_global_dtors_aux>:
    3590:	f3 0f 1e fa          	endbr64
    3594:	80 3d 8d 6a 00 00 00 	cmpb   $0x0,0x6a8d(%rip)        # a028 <completed.0>
    359b:	75 2b                	jne    35c8 <__do_global_dtors_aux+0x38>
    359d:	55                   	push   %rbp
    359e:	48 83 3d 52 6a 00 00 00 	cmpq   $0x0,0x6a52(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    35a6:	48 89 e5             	mov    %rsp,%rbp
    35a9:	74 0c                	je     35b7 <__do_global_dtors_aux+0x27>
    35ab:	48 8b 3d 56 6a 00 00 	mov    0x6a56(%rip),%rdi        # a008 <__dso_handle>
    35b2:	e8 f9 ec ff ff       	call   22b0 <__cxa_finalize@plt>
    35b7:	e8 64 ff ff ff       	call   3520 <deregister_tm_clones>
    35bc:	c6 05 65 6a 00 00 01 	movb   $0x1,0x6a65(%rip)        # a028 <completed.0>
    35c3:	5d                   	pop    %rbp
    35c4:	c3                   	ret
    35c5:	0f 1f 00             	nopl   (%rax)
    35c8:	c3                   	ret
    35c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000035d0 <frame_dummy>:
    35d0:	f3 0f 1e fa          	endbr64
    35d4:	e9 77 ff ff ff       	jmp    3550 <register_tm_clones>
    35d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000035e0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    35e0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    35e4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    35eb:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    35ef:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    35f7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    35fb:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    35ff:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3606:	48 85 c9             	test   %rcx,%rcx
    3609:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3610:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3614:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3618:	31 c0                	xor    %eax,%eax
    361a:	c3                   	ret
    361b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003620 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3620:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3624:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    362b:	85 c9                	test   %ecx,%ecx
    362d:	7e 4f                	jle    367e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    362f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3636:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    363d:	48 c1 e1 09          	shl    $0x9,%rcx
    3641:	48 8b 50 10          	mov    0x10(%rax),%rdx
    3645:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3649:	48 8b 70 28          	mov    0x28(%rax),%rsi
    364d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    364f:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    3653:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3658:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3660:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3668:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3673:	48 05 00 02 00 00    	add    $0x200,%rax
    3679:	48 39 c1             	cmp    %rax,%rcx
    367c:	75 da                	jne    3658 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    367e:	0f ae f8             	sfence
}
    3681:	31 c0                	xor    %eax,%eax
    3683:	c3                   	ret
    3684:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    368f:	90                   	nop

0000000000003690 <barriered_thread>:
void* barriered_thread(void *arg) {
    3690:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3694:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    3698:	0f 85 90 02 00 00    	jne    392e <barriered_thread+0x29e>
void* barriered_thread(void *arg) {
    369e:	41 56                	push   %r14
    36a0:	41 55                	push   %r13
    36a2:	49 89 fd             	mov    %rdi,%r13
    36a5:	41 54                	push   %r12
    36a7:	55                   	push   %rbp
    36a8:	31 ed                	xor    %ebp,%ebp
    36aa:	53                   	push   %rbx
    36ab:	31 db                	xor    %ebx,%ebx
    36ad:	0f 1f 00             	nopl   (%rax)
    if (t >= data->task_count) {
    36b0:	41 8b 55 30          	mov    0x30(%r13),%edx
    36b4:	39 da                	cmp    %ebx,%edx
    36b6:	7f 12                	jg     36ca <barriered_thread+0x3a>
      data->cycles++;
    36b8:	49 83 85 98 00 00 00 01 	addq   $0x1,0x98(%r13)
    for (; t < data->task_count; t++) {
    36c0:	31 db                	xor    %ebx,%ebx
    36c2:	85 d2                	test   %edx,%edx
    36c4:	0f 8e 56 01 00 00    	jle    3820 <barriered_thread+0x190>
    36ca:	4c 63 e3             	movslq %ebx,%r12
    36cd:	49 c1 e4 09          	shl    $0x9,%r12
    36d1:	eb 17                	jmp    36ea <barriered_thread+0x5a>
    36d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    36d8:	83 c3 01             	add    $0x1,%ebx
    36db:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    36e2:	39 d3                	cmp    %edx,%ebx
    36e4:	0f 8d 36 01 00 00    	jge    3820 <barriered_thread+0x190>
      if (data->tasks[t].available == 1) {
    36ea:	49 8b 45 28          	mov    0x28(%r13),%rax
    36ee:	4a 8d 34 20          	lea    (%rax,%r12,1),%rsi
    36f2:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    36f9:	75 dd                	jne    36d8 <barriered_thread+0x48>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    36fb:	41 8b 7d 18          	mov    0x18(%r13),%edi
          previous = t - 1;
    36ff:	83 ea 01             	sub    $0x1,%edx
    3702:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3705:	85 db                	test   %ebx,%ebx
    3707:	0f 4f d1             	cmovg  %ecx,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    370a:	85 ff                	test   %edi,%edi
    370c:	0f 8e 3e 01 00 00    	jle    3850 <barriered_thread+0x1c0>
    3712:	49 8b 45 10          	mov    0x10(%r13),%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3716:	48 63 ca             	movslq %edx,%rcx
    3719:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    371c:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    371f:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    3726:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    372d:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    3731:	45 31 f6             	xor    %r14d,%r14d
    3734:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3738:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3740:	48 8b 10             	mov    (%rax),%rdx
    3743:	4c 8b 5a 28          	mov    0x28(%rdx),%r11
    3747:	49 01 cb             	add    %rcx,%r11
    374a:	4c 89 da             	mov    %r11,%rdx
    374d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    3754:	75 04                	jne    375a <barriered_thread+0xca>
            arrived++;
    3756:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    375a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    3761:	75 04                	jne    3767 <barriered_thread+0xd7>
            prearrive++;
    3763:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3767:	48 83 c0 08          	add    $0x8,%rax
    376b:	48 39 f0             	cmp    %rsi,%rax
    376e:	75 d0                	jne    3740 <barriered_thread+0xb0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    3770:	44 39 d7             	cmp    %r10d,%edi
    3773:	0f 84 c7 00 00 00    	je     3840 <barriered_thread+0x1b0>
    3779:	45 85 d2             	test   %r10d,%r10d
    377c:	0f 84 be 00 00 00    	je     3840 <barriered_thread+0x1b0>
        if (arrived == 0 || arrived == data->thread_count) {
    3782:	45 85 f6             	test   %r14d,%r14d
    3785:	74 0a                	je     3791 <barriered_thread+0x101>
    3787:	45 39 75 18          	cmp    %r14d,0x18(%r13)
    378b:	0f 85 8f 00 00 00    	jne    3820 <barriered_thread+0x190>
    3791:	49 8b 45 28          	mov    0x28(%r13),%rax
          data->tasks[t].prearrive++;
    3795:	4c 01 e0             	add    %r12,%rax
    3798:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    379f:	85 db                	test   %ebx,%ebx
    37a1:	75 0e                	jne    37b1 <barriered_thread+0x121>
    37a3:	49 8b 75 70          	mov    0x70(%r13),%rsi
    37a7:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    37ab:	0f 8c 5f 01 00 00    	jl     3910 <barriered_thread+0x280>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    37b1:	49 63 4d 00          	movslq 0x0(%r13),%rcx
    37b5:	49 8b 55 10          	mov    0x10(%r13),%rdx
          data->tasks[t].available = 0;
    37b9:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    37c3:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    37c7:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
    37cb:	4c 01 e7             	add    %r12,%rdi
    37ce:	ff 90 18 01 00 00    	call   *0x118(%rax)
          data->tasks[t].arrived++;
    37d4:	49 8b 45 28          	mov    0x28(%r13),%rax
    37d8:	4c 01 e0             	add    %r12,%rax
    37db:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    37e2:	41 8b 45 30          	mov    0x30(%r13),%eax
          data->iteration_count++;
    37e6:	49 83 45 68 01       	addq   $0x1,0x68(%r13)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    37eb:	83 e8 01             	sub    $0x1,%eax
    37ee:	39 d8                	cmp    %ebx,%eax
    37f0:	0f 84 b2 00 00 00    	je     38a8 <barriered_thread+0x218>
          asm volatile ("sfence" ::: "memory");
    37f6:	0f ae f8             	sfence
          if (waiting == 0) {
    37f9:	85 ed                	test   %ebp,%ebp
    37fb:	0f 84 d7 00 00 00    	je     38d8 <barriered_thread+0x248>
    for (; t < data->task_count; t++) {
    3801:	41 8b 55 30          	mov    0x30(%r13),%edx
    3805:	83 c3 01             	add    $0x1,%ebx
    3808:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    380f:	39 d3                	cmp    %edx,%ebx
    3811:	0f 8c d3 fe ff ff    	jl     36ea <barriered_thread+0x5a>
    3817:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  while (data->running == 1) {
    3820:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
    3825:	0f 84 85 fe ff ff    	je     36b0 <barriered_thread+0x20>
}
    382b:	5b                   	pop    %rbx
    382c:	31 c0                	xor    %eax,%eax
    382e:	5d                   	pop    %rbp
    382f:	41 5c                	pop    %r12
    3831:	41 5d                	pop    %r13
    3833:	41 5e                	pop    %r14
    3835:	c3                   	ret
    3836:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
    3840:	83 fd 01             	cmp    $0x1,%ebp
    3843:	74 1b                	je     3860 <barriered_thread+0x1d0>
        int arrived = 0; 
    3845:	31 ed                	xor    %ebp,%ebp
    3847:	e9 36 ff ff ff       	jmp    3782 <barriered_thread+0xf2>
    384c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    3850:	83 fd 01             	cmp    $0x1,%ebp
    3853:	0f 85 3c ff ff ff    	jne    3795 <barriered_thread+0x105>
        int arrived = 0; 
    3859:	45 31 f6             	xor    %r14d,%r14d
    385c:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3860:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    3867:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    386c:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    386e:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3872:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    3879:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    387e:	e8 8d ea ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3883:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    388a:	48 83 c0 01          	add    $0x1,%rax
    388e:	48 99                	cqto
    3890:	49 f7 bd 90 00 00 00 	idivq  0x90(%r13)
    3897:	49 89 95 88 00 00 00 	mov    %rdx,0x88(%r13)
            waiting = 0; 
    389e:	e9 df fe ff ff       	jmp    3782 <barriered_thread+0xf2>
    38a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    38a8:	49 8b 75 70          	mov    0x70(%r13),%rsi
    38ac:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    38b0:	0f 8d 40 ff ff ff    	jge    37f6 <barriered_thread+0x166>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    38b6:	48 c1 e6 04          	shl    $0x4,%rsi
    38ba:	bf 04 00 00 00       	mov    $0x4,%edi
    38bf:	49 03 75 60          	add    0x60(%r13),%rsi
    38c3:	e8 48 ea ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    38c8:	49 83 45 70 01       	addq   $0x1,0x70(%r13)
    38cd:	e9 24 ff ff ff       	jmp    37f6 <barriered_thread+0x166>
    38d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    38d8:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    38df:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    38e4:	bd 01 00 00 00       	mov    $0x1,%ebp
            data->task_snapshot[data->task_timestamp_count].task = t;
    38e9:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    38ed:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    38f4:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    38f8:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    38fb:	e8 10 ea ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3900:	41 8b 55 30          	mov    0x30(%r13),%edx
    3904:	e9 cf fd ff ff       	jmp    36d8 <barriered_thread+0x48>
    3909:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3910:	48 c1 e6 04          	shl    $0x4,%rsi
    3914:	bf 04 00 00 00       	mov    $0x4,%edi
    3919:	49 03 75 58          	add    0x58(%r13),%rsi
    391d:	e8 ee e9 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3922:	49 8b 45 28          	mov    0x28(%r13),%rax
    3926:	4c 01 e0             	add    %r12,%rax
    3929:	e9 83 fe ff ff       	jmp    37b1 <barriered_thread+0x121>
}
    392e:	31 c0                	xor    %eax,%eax
    3930:	c3                   	ret
    3931:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    393c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003940 <external_thread>:
void * external_thread(void *arg) {
    3940:	f3 0f 1e fa          	endbr64
    3944:	41 55                	push   %r13
    3946:	41 54                	push   %r12
    3948:	55                   	push   %rbp
    3949:	53                   	push   %rbx
    394a:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    394e:	66 0f 6f 05 ea 3f 00 00 	movdqa 0x3fea(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
void * external_thread(void *arg) {
    3956:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    395f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3964:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3966:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
  struct timespec req = {
    396a:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    396e:	75 64                	jne    39d4 <external_thread+0x94>
    3970:	49 89 fd             	mov    %rdi,%r13
    3973:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3978:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    397b:	4c 8d 25 82 36 00 00 	lea    0x3682(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    3982:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    nanosleep(&req , &rem);
    3988:	48 89 ee             	mov    %rbp,%rsi
    398b:	48 89 df             	mov    %rbx,%rdi
    398e:	e8 bd e9 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3993:	49 8b 45 40          	mov    0x40(%r13),%rax
    3997:	48 63 10             	movslq (%rax),%rdx
    399a:	85 d2                	test   %edx,%edx
    399c:	7e 2c                	jle    39ca <external_thread+0x8a>
    399e:	48 8b 40 08          	mov    0x8(%rax),%rax
    39a2:	48 c1 e2 04          	shl    $0x4,%rdx
    39a6:	48 01 c2             	add    %rax,%rdx
    39a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    39b0:	8b 48 08             	mov    0x8(%rax),%ecx
    39b3:	85 c9                	test   %ecx,%ecx
    39b5:	75 0a                	jne    39c1 <external_thread+0x81>
        data->buffers->buffer[x].data = "Hello world";
    39b7:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    39ba:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    39c1:	48 83 c0 10          	add    $0x10,%rax
    39c5:	48 39 c2             	cmp    %rax,%rdx
    39c8:	75 e6                	jne    39b0 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    39ca:	0f ae f0             	mfence
  while (data->running == 1) {
    39cd:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
    39d2:	74 b4                	je     3988 <external_thread+0x48>
}
    39d4:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    39d9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    39e2:	75 0d                	jne    39f1 <external_thread+0xb1>
    39e4:	48 83 c4 38          	add    $0x38,%rsp
    39e8:	31 c0                	xor    %eax,%eax
    39ea:	5b                   	pop    %rbx
    39eb:	5d                   	pop    %rbp
    39ec:	41 5c                	pop    %r12
    39ee:	41 5d                	pop    %r13
    39f0:	c3                   	ret
    39f1:	e8 3a e9 ff ff       	call   2330 <__stack_chk_fail@plt>
    39f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003a00 <timer_thread>:
void* timer_thread(void *arg) {
    3a00:	f3 0f 1e fa          	endbr64
    3a04:	41 57                	push   %r15
    3a06:	48 8d 35 03 36 00 00 	lea    0x3603(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3a0d:	49 89 ff             	mov    %rdi,%r15
    3a10:	41 56                	push   %r14
    3a12:	41 55                	push   %r13
    3a14:	41 54                	push   %r12
    3a16:	55                   	push   %rbp
    3a17:	53                   	push   %rbx
    3a18:	48 83 ec 58          	sub    $0x58,%rsp
    3a1c:	8b 17                	mov    (%rdi),%edx
    3a1e:	bf 01 00 00 00       	mov    $0x1,%edi
    3a23:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3a2c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3a31:	31 c0                	xor    %eax,%eax
    3a33:	e8 18 ea ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3a38:	66 0f 6f 05 00 3f 00 00 	movdqa 0x3f00(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3a40:	ba 88 13 00 00       	mov    $0x1388,%edx
    3a45:	31 c0                	xor    %eax,%eax
    3a47:	48 8d 35 d4 35 00 00 	lea    0x35d4(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3a4e:	bf 01 00 00 00       	mov    $0x1,%edi
    3a53:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3a58:	e8 f3 e9 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3a5d:	45 8b 67 34          	mov    0x34(%r15),%r12d
    3a61:	45 85 e4             	test   %r12d,%r12d
    3a64:	0f 84 9b 00 00 00    	je     3b05 <timer_thread+0x105>
  int n = 0;
    3a6a:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    3a6d:	45 31 e4             	xor    %r12d,%r12d
    3a70:	49 89 e5             	mov    %rsp,%r13
    y++;
    3a73:	31 db                	xor    %ebx,%ebx
    3a75:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    3a7a:	48 89 ef             	mov    %rbp,%rdi
    3a7d:	4c 89 ee             	mov    %r13,%rsi
    n++;
    3a80:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3a84:	e8 c7 e8 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a89:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3a8d:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a92:	85 c0                	test   %eax,%eax
    3a94:	7e 47                	jle    3add <timer_thread+0xdd>
    3a96:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3a9a:	49 c1 e4 09          	shl    $0x9,%r12
    3a9e:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3aa2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3aa8:	4c 8b 11             	mov    (%rcx),%r10
    3aab:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3aad:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3ab1:	99                   	cltd
    3ab2:	41 f7 7a 30          	idivl  0x30(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3ab6:	49 8b 72 28          	mov    0x28(%r10),%rsi
    3aba:	48 63 d2             	movslq %edx,%rdx
    3abd:	48 c1 e2 09          	shl    $0x9,%rdx
    3ac1:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3acc:	42 c7 84 26 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ad8:	49 39 c8             	cmp    %rcx,%r8
    3adb:	75 cb                	jne    3aa8 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    3add:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3ae0:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3ae4:	41 8b 57 34          	mov    0x34(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3ae8:	48 8b 00             	mov    (%rax),%rax
    y++;
    3aeb:	39 78 30             	cmp    %edi,0x30(%rax)
    3aee:	0f 4e fb             	cmovle %ebx,%edi
    3af1:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3af4:	85 d2                	test   %edx,%edx
    3af6:	74 0d                	je     3b05 <timer_thread+0x105>
    3af8:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3aff:	0f 85 75 ff ff ff    	jne    3a7a <timer_thread+0x7a>
    3b05:	48 8d 3d 2c 35 00 00 	lea    0x352c(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3b0c:	e8 df e7 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b11:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3b15:	85 d2                	test   %edx,%edx
    3b17:	7e 6b                	jle    3b84 <timer_thread+0x184>
    for (int y = 0 ; y < data->task_count ; y++) {
    3b19:	49 63 47 30          	movslq 0x30(%r15),%rax
    3b1d:	85 c0                	test   %eax,%eax
    3b1f:	7e 63                	jle    3b84 <timer_thread+0x184>
    3b21:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3b25:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3b29:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3b31:	31 ff                	xor    %edi,%edi
    3b33:	48 89 c2             	mov    %rax,%rdx
    3b36:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3b3a:	48 8b 40 28          	mov    0x28(%rax),%rax
    3b3e:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3b42:	f6 c6 02             	test   $0x2,%dh
    3b45:	74 15                	je     3b5c <timer_thread+0x15c>
    3b47:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3b51:	48 05 00 02 00 00    	add    $0x200,%rax
    3b57:	48 39 c6             	cmp    %rax,%rsi
    3b5a:	74 1f                	je     3b7b <timer_thread+0x17b>
      data->threads[x]->tasks[y].sending = 0;
    3b5c:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3b66:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3b6c:	c7 80 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3b76:	48 39 c6             	cmp    %rax,%rsi
    3b79:	75 e1                	jne    3b5c <timer_thread+0x15c>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b7b:	48 83 c7 08          	add    $0x8,%rdi
    3b7f:	48 39 f9             	cmp    %rdi,%rcx
    3b82:	75 b2                	jne    3b36 <timer_thread+0x136>
  asm volatile ("mfence" ::: "memory");
    3b84:	0f ae f0             	mfence
  struct timespec drain = {
    3b87:	66 0f 6f 05 c1 3d 00 00 	movdqa 0x3dc1(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3b8f:	48 8d 2d c7 34 00 00 	lea    0x34c7(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3b96:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b9b:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3b9f:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ba4:	85 c0                	test   %eax,%eax
    3ba6:	7e 4c                	jle    3bf4 <timer_thread+0x1f4>
    3ba8:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3bac:	4d 63 c4             	movslq %r12d,%r8
    3baf:	49 c1 e0 09          	shl    $0x9,%r8
    3bb3:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3bb7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3bc0:	48 8b 19             	mov    (%rcx),%rbx
    3bc3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bc5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3bc9:	99                   	cltd
    3bca:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3bcd:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3bd1:	48 63 d2             	movslq %edx,%rdx
    3bd4:	48 c1 e2 09          	shl    $0x9,%rdx
    3bd8:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3be3:	42 c7 84 06 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bef:	4c 39 c9             	cmp    %r9,%rcx
    3bf2:	75 cc                	jne    3bc0 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    3bf4:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3bf7:	49 8b 47 10          	mov    0x10(%r15),%rax
    y++;
    3bfb:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3bfe:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3c01:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3c04:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3c08:	41 8b 7f 20          	mov    0x20(%r15),%edi
    3c0c:	85 ff                	test   %edi,%edi
    3c0e:	0f 8e bc 00 00 00    	jle    3cd0 <timer_thread+0x2d0>
    3c14:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    3c17:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3c1d:	0f 1f 00             	nopl   (%rax)
    3c20:	4a 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbx
            all_empty = 0;
    3c28:	45 31 f6             	xor    %r14d,%r14d
    3c2b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3c30:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3c34:	4c 89 f0             	mov    %r14,%rax
    3c37:	48 c1 e0 09          	shl    $0x9,%rax
    3c3b:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3c3f:	31 d2                	xor    %edx,%edx
    3c41:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3c48:	eb 16                	jmp    3c60 <timer_thread+0x260>
    3c4a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3c50:	4d 85 c0             	test   %r8,%r8
    3c53:	7f 1f                	jg     3c74 <timer_thread+0x274>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3c55:	83 c2 01             	add    $0x1,%edx
    3c58:	48 83 c0 20          	add    $0x20,%rax
    3c5c:	39 fa                	cmp    %edi,%edx
    3c5e:	74 2a                	je     3c8a <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3c60:	48 8b 08             	mov    (%rax),%rcx
    3c63:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3c67:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3c6b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3c6f:	48 85 c9             	test   %rcx,%rcx
    3c72:	7e dc                	jle    3c50 <timer_thread+0x250>
    3c74:	bf 01 00 00 00       	mov    $0x1,%edi
    3c79:	48 89 ee             	mov    %rbp,%rsi
    3c7c:	31 c0                	xor    %eax,%eax
    3c7e:	e8 cd e7 ff ff       	call   2450 <__printf_chk@plt>
            break;
    3c83:	41 8b 7f 20          	mov    0x20(%r15),%edi
            all_empty = 0;
    3c87:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3c8a:	49 83 c6 01          	add    $0x1,%r14
    3c8e:	44 39 f7             	cmp    %r14d,%edi
    3c91:	7e 0d                	jle    3ca0 <timer_thread+0x2a0>
    3c93:	49 8b 47 10          	mov    0x10(%r15),%rax
    3c97:	eb 97                	jmp    3c30 <timer_thread+0x230>
    3c99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3ca0:	49 83 c5 01          	add    $0x1,%r13
    3ca4:	44 39 ef             	cmp    %r13d,%edi
    3ca7:	7e 0d                	jle    3cb6 <timer_thread+0x2b6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3ca9:	85 ff                	test   %edi,%edi
    3cab:	7e 09                	jle    3cb6 <timer_thread+0x2b6>
    3cad:	49 8b 47 10          	mov    0x10(%r15),%rax
    3cb1:	e9 6a ff ff ff       	jmp    3c20 <timer_thread+0x220>
    if (all_empty == 1) {
    3cb6:	41 83 f9 01          	cmp    $0x1,%r9d
    3cba:	74 14                	je     3cd0 <timer_thread+0x2d0>
      nanosleep(&drain , &drainrem);
    3cbc:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3cc1:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3cc6:	e8 85 e6 ff ff       	call   2350 <nanosleep@plt>
    3ccb:	e9 cb fe ff ff       	jmp    3b9b <timer_thread+0x19b>
    3cd0:	48 8d 3d 7d 33 00 00 	lea    0x337d(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3cd7:	e8 14 e6 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3cdc:	41 8b 47 34          	mov    0x34(%r15),%eax
    3ce0:	85 c0                	test   %eax,%eax
    3ce2:	0f 84 cf 00 00 00    	je     3db7 <timer_thread+0x3b7>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ce8:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3cec:	85 c9                	test   %ecx,%ecx
    3cee:	7e 2d                	jle    3d1d <timer_thread+0x31d>
    3cf0:	49 8b 47 10          	mov    0x10(%r15),%rax
    3cf4:	31 db                	xor    %ebx,%ebx
    3cf6:	48 8d 2d 71 33 00 00 	lea    0x3371(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3cfd:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->running = 0;
    3d00:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3d04:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3d08:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3d0f:	0f 84 cf 00 00 00    	je     3de4 <timer_thread+0x3e4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d15:	48 83 c3 01          	add    $0x1,%rbx
    3d19:	39 d9                	cmp    %ebx,%ecx
    3d1b:	7f e3                	jg     3d00 <timer_thread+0x300>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d1d:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3d21:	85 d2                	test   %edx,%edx
    3d23:	7e 7b                	jle    3da0 <timer_thread+0x3a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3d25:	49 63 47 30          	movslq 0x30(%r15),%rax
    3d29:	85 c0                	test   %eax,%eax
    3d2b:	7e 73                	jle    3da0 <timer_thread+0x3a0>
    3d2d:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3d31:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3d35:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3d3d:	31 c9                	xor    %ecx,%ecx
    3d3f:	48 89 c6             	mov    %rax,%rsi
    3d42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3d48:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3d4c:	48 8b 40 28          	mov    0x28(%rax),%rax
    3d50:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3d54:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3d5a:	74 1c                	je     3d78 <timer_thread+0x378>
    3d5c:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3d66:	48 05 00 02 00 00    	add    $0x200,%rax
    3d6c:	48 39 d0             	cmp    %rdx,%rax
    3d6f:	74 26                	je     3d97 <timer_thread+0x397>
    3d71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3d78:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3d82:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3d88:	c7 80 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3d92:	48 39 d0             	cmp    %rdx,%rax
    3d95:	75 e1                	jne    3d78 <timer_thread+0x378>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d97:	48 83 c1 08          	add    $0x8,%rcx
    3d9b:	48 39 f9             	cmp    %rdi,%rcx
    3d9e:	75 a8                	jne    3d48 <timer_thread+0x348>
    asm volatile ("mfence" ::: "memory");
    3da0:	0f ae f0             	mfence
    3da3:	48 8d 3d d6 32 00 00 	lea    0x32d6(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3daa:	e8 41 e5 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3daf:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
    3db7:	48 8d 3d c9 32 00 00 	lea    0x32c9(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3dbe:	e8 2d e5 ff ff       	call   22f0 <puts@plt>
}
    3dc3:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3dc8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3dd1:	75 47                	jne    3e1a <timer_thread+0x41a>
    3dd3:	48 83 c4 58          	add    $0x58,%rsp
    3dd7:	31 c0                	xor    %eax,%eax
    3dd9:	5b                   	pop    %rbx
    3dda:	5d                   	pop    %rbp
    3ddb:	41 5c                	pop    %r12
    3ddd:	41 5d                	pop    %r13
    3ddf:	41 5e                	pop    %r14
    3de1:	41 5f                	pop    %r15
    3de3:	c3                   	ret
    3de4:	48 89 ef             	mov    %rbp,%rdi
    3de7:	e8 04 e5 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3dec:	49 8b 47 10          	mov    0x10(%r15),%rax
    3df0:	be 01 00 00 00       	mov    $0x1,%esi
    3df5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3df9:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3dfd:	8b 78 50             	mov    0x50(%rax),%edi
    3e00:	e8 fb e5 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3e05:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3e09:	39 d9                	cmp    %ebx,%ecx
    3e0b:	0f 8e 0c ff ff ff    	jle    3d1d <timer_thread+0x31d>
    3e11:	49 8b 47 10          	mov    0x10(%r15),%rax
    3e15:	e9 e6 fe ff ff       	jmp    3d00 <timer_thread+0x300>
}
    3e1a:	e8 11 e5 ff ff       	call   2330 <__stack_chk_fail@plt>
    3e1f:	90                   	nop

0000000000003e20 <strtolower>:
void strtolower(char *str) {
    3e20:	f3 0f 1e fa          	endbr64
    3e24:	55                   	push   %rbp
    3e25:	53                   	push   %rbx
    3e26:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3e2a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3e2e:	84 db                	test   %bl,%bl
    3e30:	74 24                	je     3e56 <strtolower+0x36>
    3e32:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3e35:	e8 d6 e6 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3e3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3e40:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3e43:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3e47:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3e4a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3e4d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3e52:	84 db                	test   %bl,%bl
    3e54:	75 ea                	jne    3e40 <strtolower+0x20>
}
    3e56:	48 83 c4 08          	add    $0x8,%rsp
    3e5a:	5b                   	pop    %rbx
    3e5b:	5d                   	pop    %rbp
    3e5c:	c3                   	ret
    3e5d:	0f 1f 00             	nopl   (%rax)

0000000000003e60 <zh_malloc>:
void *zh_malloc(size_t size) {
    3e60:	f3 0f 1e fa          	endbr64
    3e64:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3e68:	e8 a3 e5 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3e6d:	48 85 c0             	test   %rax,%rax
    3e70:	74 05                	je     3e77 <zh_malloc+0x17>
}
    3e72:	48 83 c4 08          	add    $0x8,%rsp
    3e76:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3e77:	48 8b 0d a2 61 00 00 	mov    0x61a2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    3e7e:	ba 28 00 00 00       	mov    $0x28,%edx
    3e83:	be 01 00 00 00       	mov    $0x1,%esi
    3e88:	48 8d 3d 79 35 00 00 	lea    0x3579(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    3e8f:	e8 2c e6 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    3e94:	bf 01 00 00 00       	mov    $0x1,%edi
    3e99:	e8 02 e6 ff ff       	call   24a0 <exit@plt>
    3e9e:	66 90                	xchg   %ax,%ax

0000000000003ea0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3ea0:	f3 0f 1e fa          	endbr64
    3ea4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    3ea5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3eaa:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3ead:	e8 ae e4 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3eb2:	48 85 c0             	test   %rax,%rax
    3eb5:	74 11                	je     3ec8 <get_filename_ext+0x28>
    3eb7:	48 39 c3             	cmp    %rax,%rbx
    3eba:	74 0c                	je     3ec8 <get_filename_ext+0x28>
    return dot + 1;
    3ebc:	48 83 c0 01          	add    $0x1,%rax
}
    3ec0:	5b                   	pop    %rbx
    3ec1:	c3                   	ret
    3ec2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    3ec8:	48 8d 05 00 32 00 00 	lea    0x3200(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    3ecf:	5b                   	pop    %rbx
    3ed0:	c3                   	ret
    3ed1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3edc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003ee0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3ee0:	f3 0f 1e fa          	endbr64
    3ee4:	41 55                	push   %r13
    3ee6:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3ee9:	48 89 fe             	mov    %rdi,%rsi
    3eec:	41 54                	push   %r12
    3eee:	55                   	push   %rbp
    3eef:	48 89 d5             	mov    %rdx,%rbp
    3ef2:	ba 00 04 00 00       	mov    $0x400,%edx
    3ef7:	53                   	push   %rbx
    3ef8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3eff:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3f08:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3f10:	31 c0                	xor    %eax,%eax
    3f12:	49 89 e4             	mov    %rsp,%r12
    3f15:	4c 89 e7             	mov    %r12,%rdi
    3f18:	e8 13 e5 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    3f1d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3f22:	84 db                	test   %bl,%bl
    3f24:	74 24                	je     3f4a <send_headers+0x6a>
        *str = (char)tolower(*str);
    3f26:	e8 e5 e5 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3f2b:	48 8b 08             	mov    (%rax),%rcx
    3f2e:	4c 89 e0             	mov    %r12,%rax
    3f31:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3f38:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3f3b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3f3f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3f42:	48 0f be 18          	movsbq (%rax),%rbx
    3f46:	84 db                	test   %bl,%bl
    3f48:	75 ee                	jne    3f38 <send_headers+0x58>
    void *buf = malloc(size);
    3f4a:	bf 11 00 00 00       	mov    $0x11,%edi
    3f4f:	e8 bc e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3f54:	48 85 c0             	test   %rax,%rax
    3f57:	0f 84 7e 04 00 00    	je     43db <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3f5d:	66 0f 6f 05 fb 39 00 00 	movdqa 0x39fb(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    3f65:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    3f69:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3f6e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3f76:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3f7a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3f7d:	e8 8e e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3f82:	48 85 c0             	test   %rax,%rax
    3f85:	0f 84 50 04 00 00    	je     43db <send_headers+0x4fb>
    3f8b:	66 0f 6f 05 dd 39 00 00 	movdqa 0x39dd(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    3f93:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    3f97:	4c 89 e7             	mov    %r12,%rdi
    3f9a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3fa4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3fac:	0f 11 00             	movups %xmm0,(%rax)
    3faf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3fb3:	be 2e 00 00 00       	mov    $0x2e,%esi
    3fb8:	e8 a3 e3 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3fbd:	48 85 c0             	test   %rax,%rax
    3fc0:	0f 84 ea 02 00 00    	je     42b0 <send_headers+0x3d0>
    3fc6:	4c 39 e0             	cmp    %r12,%rax
    3fc9:	0f 84 e1 02 00 00    	je     42b0 <send_headers+0x3d0>
    return dot + 1;
    3fcf:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3fd3:	48 8d 3d c3 30 00 00 	lea    0x30c3(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    3fda:	48 89 de             	mov    %rbx,%rsi
    3fdd:	e8 ce e3 ff ff       	call   23b0 <strcmp@plt>
    3fe2:	85 c0                	test   %eax,%eax
    3fe4:	75 20                	jne    4006 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3fe6:	66 0f 6f 05 92 39 00 00 	movdqa 0x3992(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    3fee:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3ff6:	66 0f 6f 05 92 39 00 00 	movdqa 0x3992(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    3ffe:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4006:	48 89 de             	mov    %rbx,%rsi
    4009:	48 8d 3d 91 30 00 00 	lea    0x3091(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    4010:	e8 9b e3 ff ff       	call   23b0 <strcmp@plt>
    4015:	85 c0                	test   %eax,%eax
    4017:	75 20                	jne    4039 <send_headers+0x159>
    4019:	66 0f 6f 05 5f 39 00 00 	movdqa 0x395f(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4021:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4029:	66 0f 6f 05 5f 39 00 00 	movdqa 0x395f(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    4031:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4039:	48 89 de             	mov    %rbx,%rsi
    403c:	48 8d 3d 63 30 00 00 	lea    0x3063(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    4043:	e8 68 e3 ff ff       	call   23b0 <strcmp@plt>
    4048:	85 c0                	test   %eax,%eax
    404a:	0f 84 10 02 00 00    	je     4260 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4050:	48 89 de             	mov    %rbx,%rsi
    4053:	48 8d 3d 50 30 00 00 	lea    0x3050(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    405a:	e8 51 e3 ff ff       	call   23b0 <strcmp@plt>
    405f:	85 c0                	test   %eax,%eax
    4061:	0f 84 a9 02 00 00    	je     4310 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4067:	48 89 de             	mov    %rbx,%rsi
    406a:	48 8d 3d 3d 30 00 00 	lea    0x303d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4071:	e8 3a e3 ff ff       	call   23b0 <strcmp@plt>
    4076:	85 c0                	test   %eax,%eax
    4078:	0f 84 6a 02 00 00    	je     42e8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    407e:	48 89 de             	mov    %rbx,%rsi
    4081:	48 8d 3d 69 30 00 00 	lea    0x3069(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4088:	e8 23 e3 ff ff       	call   23b0 <strcmp@plt>
    408d:	85 c0                	test   %eax,%eax
    408f:	0f 84 2b 02 00 00    	je     42c0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4095:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4098:	0f 84 52 01 00 00    	je     41f0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    409e:	48 89 de             	mov    %rbx,%rsi
    40a1:	48 8d 3d 0a 30 00 00 	lea    0x300a(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    40a8:	e8 03 e3 ff ff       	call   23b0 <strcmp@plt>
    40ad:	85 c0                	test   %eax,%eax
    40af:	0f 84 ab 02 00 00    	je     4360 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    40b5:	48 89 de             	mov    %rbx,%rsi
    40b8:	48 8d 3d f7 2f 00 00 	lea    0x2ff7(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    40bf:	e8 ec e2 ff ff       	call   23b0 <strcmp@plt>
    40c4:	85 c0                	test   %eax,%eax
    40c6:	0f 84 6c 02 00 00    	je     4338 <send_headers+0x458>
    slen = strlen(send_buffer);
    40cc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    40d4:	4c 89 e7             	mov    %r12,%rdi
    40d7:	e8 44 e2 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    40dc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    40df:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    40e2:	e8 29 e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    40e7:	48 85 c0             	test   %rax,%rax
    40ea:	0f 84 eb 02 00 00    	je     43db <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    40f0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    40f4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    40f8:	83 fb 08             	cmp    $0x8,%ebx
    40fb:	0f 83 3f 01 00 00    	jae    4240 <send_headers+0x360>
    4101:	f6 c3 04             	test   $0x4,%bl
    4104:	0f 85 7b 02 00 00    	jne    4385 <send_headers+0x4a5>
    410a:	85 db                	test   %ebx,%ebx
    410c:	74 13                	je     4121 <send_headers+0x241>
    410e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4116:	88 10                	mov    %dl,(%rax)
    4118:	f6 c3 02             	test   $0x2,%bl
    411b:	0f 85 96 02 00 00    	jne    43b7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4121:	4d 89 e8             	mov    %r13,%r8
    4124:	48 8d 0d 8f 2f 00 00 	lea    0x2f8f(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    412b:	4c 89 e7             	mov    %r12,%rdi
    412e:	31 c0                	xor    %eax,%eax
    4130:	ba 00 04 00 00       	mov    $0x400,%edx
    4135:	be 01 00 00 00       	mov    $0x1,%esi
    413a:	e8 e1 e3 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    413f:	4c 89 e7             	mov    %r12,%rdi
    4142:	e8 d9 e1 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4147:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    414a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    414d:	e8 be e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4152:	48 85 c0             	test   %rax,%rax
    4155:	0f 84 80 02 00 00    	je     43db <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    415b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    415f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4163:	83 fb 08             	cmp    $0x8,%ebx
    4166:	0f 83 1c 01 00 00    	jae    4288 <send_headers+0x3a8>
    416c:	f6 c3 04             	test   $0x4,%bl
    416f:	0f 85 29 02 00 00    	jne    439e <send_headers+0x4be>
    4175:	85 db                	test   %ebx,%ebx
    4177:	74 13                	je     418c <send_headers+0x2ac>
    4179:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4181:	88 10                	mov    %dl,(%rax)
    4183:	f6 c3 02             	test   $0x2,%bl
    4186:	0f 85 3d 02 00 00    	jne    43c9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    418c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4191:	bf 02 00 00 00       	mov    $0x2,%edi
    4196:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    419e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    41a6:	e8 65 e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    41ab:	48 85 c0             	test   %rax,%rax
    41ae:	0f 84 27 02 00 00    	je     43db <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    41b4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    41bc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    41c0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    41c8:	66 89 10             	mov    %dx,(%rax)
}
    41cb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    41d3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    41dc:	0f 85 20 02 00 00    	jne    4402 <send_headers+0x522>
    41e2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    41e9:	5b                   	pop    %rbx
    41ea:	5d                   	pop    %rbp
    41eb:	41 5c                	pop    %r12
    41ed:	41 5d                	pop    %r13
    41ef:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    41f0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    41f4:	0f 85 a4 fe ff ff    	jne    409e <send_headers+0x1be>
    41fa:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    41fe:	0f 85 9a fe ff ff    	jne    409e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4204:	66 0f 6f 05 d4 37 00 00 	movdqa 0x37d4(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    420c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4216:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    421e:	66 0f 6f 05 ca 37 00 00 	movdqa 0x37ca(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    4226:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    422e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4236:	e9 63 fe ff ff       	jmp    409e <send_headers+0x1be>
    423b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4240:	89 da                	mov    %ebx,%edx
    4242:	48 89 c7             	mov    %rax,%rdi
    4245:	4c 89 e6             	mov    %r12,%rsi
    4248:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    424d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4252:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4255:	c1 e9 03             	shr    $0x3,%ecx
    4258:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    425b:	e9 c1 fe ff ff       	jmp    4121 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4260:	66 0f 6f 05 18 37 00 00 	movdqa 0x3718(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4268:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4270:	66 0f 6f 05 28 37 00 00 	movdqa 0x3728(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4278:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4280:	e9 cb fd ff ff       	jmp    4050 <send_headers+0x170>
    4285:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4288:	89 da                	mov    %ebx,%edx
    428a:	48 89 c7             	mov    %rax,%rdi
    428d:	4c 89 e6             	mov    %r12,%rsi
    4290:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4295:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    429a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    429d:	c1 e9 03             	shr    $0x3,%ecx
    42a0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    42a3:	e9 e4 fe ff ff       	jmp    418c <send_headers+0x2ac>
    42a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    42b0:	48 8d 1d 18 2e 00 00 	lea    0x2e18(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    42b7:	e9 94 fd ff ff       	jmp    4050 <send_headers+0x170>
    42bc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    42c0:	66 0f 6f 05 f8 36 00 00 	movdqa 0x36f8(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    42c8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    42d0:	66 0f 6f 05 f8 36 00 00 	movdqa 0x36f8(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    42d8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    42e0:	e9 b0 fd ff ff       	jmp    4095 <send_headers+0x1b5>
    42e5:	0f 1f 00             	nopl   (%rax)
    42e8:	66 0f 6f 05 d0 36 00 00 	movdqa 0x36d0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    42f0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    42f8:	66 0f 6f 05 d0 36 00 00 	movdqa 0x36d0(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4300:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4308:	e9 71 fd ff ff       	jmp    407e <send_headers+0x19e>
    430d:	0f 1f 00             	nopl   (%rax)
    4310:	66 0f 6f 05 68 36 00 00 	movdqa 0x3668(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4318:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4320:	66 0f 6f 05 88 36 00 00 	movdqa 0x3688(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    4328:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4330:	e9 32 fd ff ff       	jmp    4067 <send_headers+0x187>
    4335:	0f 1f 00             	nopl   (%rax)
    4338:	66 0f 6f 05 80 36 00 00 	movdqa 0x3680(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4340:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4348:	66 0f 6f 05 c0 36 00 00 	movdqa 0x36c0(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4350:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4358:	e9 6f fd ff ff       	jmp    40cc <send_headers+0x1ec>
    435d:	0f 1f 00             	nopl   (%rax)
    4360:	66 0f 6f 05 58 36 00 00 	movdqa 0x3658(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4368:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4370:	66 0f 6f 05 88 36 00 00 	movdqa 0x3688(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4378:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4380:	e9 30 fd ff ff       	jmp    40b5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4385:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    438c:	89 db                	mov    %ebx,%ebx
    438e:	89 10                	mov    %edx,(%rax)
    4390:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4395:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4399:	e9 83 fd ff ff       	jmp    4121 <send_headers+0x241>
    439e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    43a5:	89 db                	mov    %ebx,%ebx
    43a7:	89 10                	mov    %edx,(%rax)
    43a9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    43ae:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    43b2:	e9 d5 fd ff ff       	jmp    418c <send_headers+0x2ac>
    43b7:	89 db                	mov    %ebx,%ebx
    43b9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    43bf:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    43c4:	e9 58 fd ff ff       	jmp    4121 <send_headers+0x241>
    43c9:	89 db                	mov    %ebx,%ebx
    43cb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    43d1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    43d6:	e9 b1 fd ff ff       	jmp    418c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    43db:	48 8b 0d 3e 5c 00 00 	mov    0x5c3e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    43e2:	ba 28 00 00 00       	mov    $0x28,%edx
    43e7:	be 01 00 00 00       	mov    $0x1,%esi
    43ec:	48 8d 3d 15 30 00 00 	lea    0x3015(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    43f3:	e8 c8 e0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    43f8:	bf 01 00 00 00       	mov    $0x1,%edi
    43fd:	e8 9e e0 ff ff       	call   24a0 <exit@plt>
}
    4402:	e8 29 df ff ff       	call   2330 <__stack_chk_fail@plt>
    4407:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004410 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4410:	f3 0f 1e fa          	endbr64
    4414:	41 55                	push   %r13
    4416:	49 89 d5             	mov    %rdx,%r13
    4419:	41 54                	push   %r12
    441b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    441e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4421:	55                   	push   %rbp
    4422:	53                   	push   %rbx
    4423:	48 89 f3             	mov    %rsi,%rbx
    4426:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    442a:	e8 e1 df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    442f:	48 85 c0             	test   %rax,%rax
    4432:	74 6b                	je     449f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4434:	4c 89 e7             	mov    %r12,%rdi
    4437:	48 89 c5             	mov    %rax,%rbp
    443a:	31 f6                	xor    %esi,%esi
    443c:	31 c0                	xor    %eax,%eax
    443e:	e8 3d e0 ff ff       	call   2480 <open@plt>
    4443:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4446:	85 c0                	test   %eax,%eax
    4448:	0f 88 08 e1 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    444e:	48 89 da             	mov    %rbx,%rdx
    4451:	48 89 ee             	mov    %rbp,%rsi
    4454:	89 c7                	mov    %eax,%edi
    4456:	e8 35 df ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    445b:	48 98                	cltq
    445d:	48 39 d8             	cmp    %rbx,%rax
    4460:	7c 1e                	jl     4480 <copy_file_contents+0x70>
    close(fd);
    4462:	44 89 e7             	mov    %r12d,%edi
    4465:	e8 06 df ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    446a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    446e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4472:	48 83 c4 08          	add    $0x8,%rsp
    4476:	5b                   	pop    %rbx
    4477:	5d                   	pop    %rbp
    4478:	41 5c                	pop    %r12
    447a:	41 5d                	pop    %r13
    447c:	c3                   	ret
    447d:	0f 1f 00             	nopl   (%rax)
    4480:	48 8b 0d 99 5b 00 00 	mov    0x5b99(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4487:	ba 1a 00 00 00       	mov    $0x1a,%edx
    448c:	be 01 00 00 00       	mov    $0x1,%esi
    4491:	48 8d 3d 38 2c 00 00 	lea    0x2c38(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    4498:	e8 23 e0 ff ff       	call   24c0 <fwrite@plt>
    449d:	eb c3                	jmp    4462 <copy_file_contents+0x52>
    449f:	48 8b 0d 7a 5b 00 00 	mov    0x5b7a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    44a6:	ba 28 00 00 00       	mov    $0x28,%edx
    44ab:	be 01 00 00 00       	mov    $0x1,%esi
    44b0:	48 8d 3d 51 2f 00 00 	lea    0x2f51(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    44b7:	e8 04 e0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    44bc:	bf 01 00 00 00       	mov    $0x1,%edi
    44c1:	e8 da df ff ff       	call   24a0 <exit@plt>
    44c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000044d0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    44d0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    44d4:	8b 46 44             	mov    0x44(%rsi),%eax
    44d7:	48 89 fa             	mov    %rdi,%rdx
    44da:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    44dd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    44e3:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    44e6:	48 8b 07             	mov    (%rdi),%rax
    44e9:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    44ec:	f6 c1 02             	test   $0x2,%cl
    44ef:	74 00                	je     44f1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    44f1:	89 f0                	mov    %esi,%eax
    44f3:	44 29 c0             	sub    %r8d,%eax
    44f6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    44f9:	0f 82 63 e0 ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    44ff:	c1 e9 0a             	shr    $0xa,%ecx
    4502:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4506:	8b 47 44             	mov    0x44(%rdi),%eax
    4509:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    450c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    450f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4512:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4515:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4519:	d3 e0                	shl    %cl,%eax
    451b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    451e:	48 c1 e0 06          	shl    $0x6,%rax
    4522:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4526:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    452c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    452f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4533:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4539:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4541:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4545:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4548:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    454f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4557:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    455b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    455f:	e8 dc dd ff ff       	call   2340 <io_uring_submit@plt>
}
    4564:	31 c0                	xor    %eax,%eax
    4566:	48 83 c4 08          	add    $0x8,%rsp
    456a:	c3                   	ret
    456b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004570 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4570:	f3 0f 1e fa          	endbr64
    4574:	41 55                	push   %r13
    4576:	41 89 fd             	mov    %edi,%r13d
    4579:	41 54                	push   %r12
    457b:	55                   	push   %rbp
    457c:	53                   	push   %rbx
    457d:	48 89 f3             	mov    %rsi,%rbx
    4580:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4584:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4587:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    458d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4590:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4593:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4595:	f6 c1 02             	test   $0x2,%cl
    4598:	74 00                	je     459a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    459a:	89 c2                	mov    %eax,%edx
    459c:	29 f2                	sub    %esi,%edx
    459e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    45a1:	0f 82 cb df ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    45a7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    45aa:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    45ad:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    45b0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    45b5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    45b8:	23 6b 58             	and    0x58(%rbx),%ebp
    45bb:	d3 e5                	shl    %cl,%ebp
    45bd:	48 c1 e5 06          	shl    $0x6,%rbp
    45c1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    45c5:	e8 46 de ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    45ca:	be 01 00 00 00       	mov    $0x1,%esi
    45cf:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    45d4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    45d7:	e8 c4 dd ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    45dc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    45e1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    45e5:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    45e8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    45ed:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    45f2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    45fb:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4603:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4607:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    460b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4612:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    461a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    461e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4626:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    462e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4632:	e8 09 dd ff ff       	call   2340 <io_uring_submit@plt>
}
    4637:	48 83 c4 08          	add    $0x8,%rsp
    463b:	31 c0                	xor    %eax,%eax
    463d:	5b                   	pop    %rbx
    463e:	5d                   	pop    %rbp
    463f:	41 5c                	pop    %r12
    4641:	41 5d                	pop    %r13
    4643:	c3                   	ret
    4644:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    464f:	90                   	nop

0000000000004650 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4650:	f3 0f 1e fa          	endbr64
    4654:	41 56                	push   %r14
    4656:	41 89 f6             	mov    %esi,%r14d
    4659:	41 55                	push   %r13
    465b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    465e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4663:	41 54                	push   %r12
    4665:	55                   	push   %rbp
    4666:	48 89 d5             	mov    %rdx,%rbp
    4669:	53                   	push   %rbx
    void *buf = malloc(size);
    466a:	e8 a1 dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    466f:	48 85 c0             	test   %rax,%rax
    4672:	0f 84 dd 00 00 00    	je     4755 <_send_static_string_content+0x105>
    4678:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    467b:	4c 89 ef             	mov    %r13,%rdi
    467e:	e8 9d dc ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4683:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    468a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    468e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4691:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4694:	e8 77 dd ff ff       	call   2410 <malloc@plt>
    4699:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    469c:	48 85 c0             	test   %rax,%rax
    469f:	0f 84 b0 00 00 00    	je     4755 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    46a5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    46a9:	4c 89 e2             	mov    %r12,%rdx
    46ac:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    46af:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    46b3:	e8 28 dd ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    46b8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    46bb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    46c1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    46c4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    46c8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    46ca:	f6 c1 02             	test   $0x2,%cl
    46cd:	0f 85 7d 00 00 00    	jne    4750 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    46d3:	89 d0                	mov    %edx,%eax
    46d5:	29 f0                	sub    %esi,%eax
    46d7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    46da:	0f 82 9c de ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    46e0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    46e3:	8b 45 44             	mov    0x44(%rbp),%eax
    46e6:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    46e9:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    46ec:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    46ef:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    46f2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    46f8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    46fc:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    46fe:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4701:	48 89 ef             	mov    %rbp,%rdi
    4704:	48 c1 e0 06          	shl    $0x6,%rax
    4708:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    470c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    470f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4713:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4719:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4721:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4725:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4728:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    472f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4737:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    473b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    473f:	5b                   	pop    %rbx
    4740:	5d                   	pop    %rbp
    4741:	41 5c                	pop    %r12
    4743:	41 5d                	pop    %r13
    4745:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4747:	e9 f4 db ff ff       	jmp    2340 <io_uring_submit@plt>
    474c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4750:	e9 7e ff ff ff       	jmp    46d3 <_send_static_string_content+0x83>
    4755:	48 8b 0d c4 58 00 00 	mov    0x58c4(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    475c:	ba 28 00 00 00       	mov    $0x28,%edx
    4761:	be 01 00 00 00       	mov    $0x1,%esi
    4766:	48 8d 3d 9b 2c 00 00 	lea    0x2c9b(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    476d:	e8 4e dd ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4772:	bf 01 00 00 00       	mov    $0x1,%edi
    4777:	e8 24 dd ff ff       	call   24a0 <exit@plt>
    477c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004780 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4780:	f3 0f 1e fa          	endbr64
    4784:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4787:	89 fe                	mov    %edi,%esi
    4789:	48 8b 3d 88 58 00 00 	mov    0x5888(%rip),%rdi        # a018 <unimplemented_content>
    4790:	e9 bb fe ff ff       	jmp    4650 <_send_static_string_content>
    4795:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000047a0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    47a0:	f3 0f 1e fa          	endbr64
    47a4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    47a7:	89 fe                	mov    %edi,%esi
    47a9:	48 8b 3d 60 58 00 00 	mov    0x5860(%rip),%rdi        # a010 <http_404_content>
    47b0:	e9 9b fe ff ff       	jmp    4650 <_send_static_string_content>
    47b5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000047c0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    47c0:	f3 0f 1e fa          	endbr64
    47c4:	41 56                	push   %r14
    47c6:	41 55                	push   %r13
    47c8:	49 89 d5             	mov    %rdx,%r13
    47cb:	41 54                	push   %r12
    47cd:	41 89 f4             	mov    %esi,%r12d
    47d0:	55                   	push   %rbp
    47d1:	48 89 fd             	mov    %rdi,%rbp
    47d4:	53                   	push   %rbx
    47d5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    47dc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    47e5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    47ed:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    47ef:	e8 2c db ff ff       	call   2320 <strlen@plt>
    47f4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    47f9:	48 89 c3             	mov    %rax,%rbx
    47fc:	0f 84 b6 00 00 00    	je     48b8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4802:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4807:	48 89 ee             	mov    %rbp,%rsi
    480a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    480e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4813:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    481b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4823:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    482e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4836:	e8 85 db ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    483b:	48 89 e6             	mov    %rsp,%rsi
    483e:	4c 89 f7             	mov    %r14,%rdi
    4841:	e8 8a db ff ff       	call   23d0 <stat@plt>
    4846:	83 f8 ff             	cmp    $0xffffffff,%eax
    4849:	0f 84 d3 00 00 00    	je     4922 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    484f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4853:	25 00 f0 00 00       	and    $0xf000,%eax
    4858:	3d 00 80 00 00       	cmp    $0x8000,%eax
    485d:	0f 84 f5 00 00 00    	je     4958 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4863:	48 8b 3d a6 57 00 00 	mov    0x57a6(%rip),%rdi        # a010 <http_404_content>
    486a:	4c 89 ea             	mov    %r13,%rdx
    486d:	44 89 e6             	mov    %r12d,%esi
    4870:	e8 db fd ff ff       	call   4650 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4875:	4c 89 f2             	mov    %r14,%rdx
    4878:	bf 01 00 00 00       	mov    $0x1,%edi
    487d:	31 c0                	xor    %eax,%eax
    487f:	48 8d 35 9a 28 00 00 	lea    0x289a(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    4886:	e8 c5 db ff ff       	call   2450 <__printf_chk@plt>
}
    488b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4893:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    489c:	0f 85 20 01 00 00    	jne    49c2 <handle_get_method+0x202>
    48a2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    48a9:	5b                   	pop    %rbx
    48aa:	5d                   	pop    %rbp
    48ab:	41 5c                	pop    %r12
    48ad:	41 5d                	pop    %r13
    48af:	41 5e                	pop    %r14
    48b1:	c3                   	ret
    48b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    48b8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    48bd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    48c5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    48ca:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    48cd:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    48d5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    48d8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    48e0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    48eb:	e8 d0 da ff ff       	call   23c0 <__memcpy_chk@plt>
    48f0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    48f5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    48fa:	48 8d 35 ea 27 00 00 	lea    0x27ea(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4901:	48 29 d9             	sub    %rbx,%rcx
    4904:	ba 0b 00 00 00       	mov    $0xb,%edx
    4909:	e8 b2 da ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    490e:	48 89 e6             	mov    %rsp,%rsi
    4911:	4c 89 f7             	mov    %r14,%rdi
    4914:	e8 b7 da ff ff       	call   23d0 <stat@plt>
    4919:	83 f8 ff             	cmp    $0xffffffff,%eax
    491c:	0f 85 2d ff ff ff    	jne    484f <handle_get_method+0x8f>
    4922:	4c 89 f2             	mov    %r14,%rdx
    4925:	48 89 e9             	mov    %rbp,%rcx
    4928:	48 8d 35 c7 27 00 00 	lea    0x27c7(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    492f:	31 c0                	xor    %eax,%eax
    4931:	bf 01 00 00 00       	mov    $0x1,%edi
    4936:	e8 15 db ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    493b:	48 8b 3d ce 56 00 00 	mov    0x56ce(%rip),%rdi        # a010 <http_404_content>
    4942:	4c 89 ea             	mov    %r13,%rdx
    4945:	44 89 e6             	mov    %r12d,%esi
    4948:	e8 03 fd ff ff       	call   4650 <_send_static_string_content>
}
    494d:	e9 39 ff ff ff       	jmp    488b <handle_get_method+0xcb>
    4952:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4958:	bf 70 00 00 00       	mov    $0x70,%edi
    495d:	e8 ae da ff ff       	call   2410 <malloc@plt>
    4962:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4965:	48 85 c0             	test   %rax,%rax
    4968:	74 5d                	je     49c7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    496a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    496e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4973:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4977:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    497a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4981:	e8 5a f5 ff ff       	call   3ee0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4986:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    498b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    498f:	4c 89 f7             	mov    %r14,%rdi
    4992:	e8 79 fa ff ff       	call   4410 <copy_file_contents>
    4997:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    499c:	4c 89 f2             	mov    %r14,%rdx
    499f:	31 c0                	xor    %eax,%eax
    49a1:	48 8d 35 66 27 00 00 	lea    0x2766(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    49a8:	bf 01 00 00 00       	mov    $0x1,%edi
    49ad:	e8 9e da ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    49b2:	4c 89 ee             	mov    %r13,%rsi
    49b5:	48 89 df             	mov    %rbx,%rdi
    49b8:	e8 13 fb ff ff       	call   44d0 <add_write_request>
    49bd:	e9 c9 fe ff ff       	jmp    488b <handle_get_method+0xcb>
}
    49c2:	e8 69 d9 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    49c7:	48 8b 0d 52 56 00 00 	mov    0x5652(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    49ce:	ba 28 00 00 00       	mov    $0x28,%edx
    49d3:	be 01 00 00 00       	mov    $0x1,%esi
    49d8:	48 8d 3d 29 2a 00 00 	lea    0x2a29(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    49df:	e8 dc da ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    49e4:	bf 01 00 00 00       	mov    $0x1,%edi
    49e9:	e8 b2 da ff ff       	call   24a0 <exit@plt>
    49ee:	66 90                	xchg   %ax,%ax

00000000000049f0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    49f0:	f3 0f 1e fa          	endbr64
    49f4:	41 57                	push   %r15
    49f6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    49f8:	4c 8d 35 86 26 00 00 	lea    0x2686(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    49ff:	41 55                	push   %r13
    4a01:	49 89 d5             	mov    %rdx,%r13
    4a04:	41 54                	push   %r12
    4a06:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4a09:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4a0c:	55                   	push   %rbp
    4a0d:	53                   	push   %rbx
    4a0e:	48 83 ec 18          	sub    $0x18,%rsp
    4a12:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a1b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4a20:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4a22:	49 89 e7             	mov    %rsp,%r15
    4a25:	4c 89 fa             	mov    %r15,%rdx
    4a28:	e8 53 d9 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4a2d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4a31:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4a34:	84 db                	test   %bl,%bl
    4a36:	74 1d                	je     4a55 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4a38:	e8 d3 da ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4a3d:	48 89 ea             	mov    %rbp,%rdx
    4a40:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4a43:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4a47:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4a4a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    4a4d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4a51:	84 db                	test   %bl,%bl
    4a53:	75 eb                	jne    4a40 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4a55:	4c 89 fa             	mov    %r15,%rdx
    4a58:	4c 89 f6             	mov    %r14,%rsi
    4a5b:	31 ff                	xor    %edi,%edi
    4a5d:	e8 1e d9 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4a62:	48 8d 35 ca 26 00 00 	lea    0x26ca(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4a69:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4a6c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    4a6f:	e8 3c d9 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4a74:	4c 89 ea             	mov    %r13,%rdx
    4a77:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4a7a:	85 c0                	test   %eax,%eax
    4a7c:	75 2a                	jne    4aa8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    4a7e:	48 89 df             	mov    %rbx,%rdi
    4a81:	e8 3a fd ff ff       	call   47c0 <handle_get_method>
}
    4a86:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4a8b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4a94:	75 20                	jne    4ab6 <handle_http_method+0xc6>
    4a96:	48 83 c4 18          	add    $0x18,%rsp
    4a9a:	5b                   	pop    %rbx
    4a9b:	5d                   	pop    %rbp
    4a9c:	41 5c                	pop    %r12
    4a9e:	41 5d                	pop    %r13
    4aa0:	41 5e                	pop    %r14
    4aa2:	41 5f                	pop    %r15
    4aa4:	c3                   	ret
    4aa5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4aa8:	48 8b 3d 69 55 00 00 	mov    0x5569(%rip),%rdi        # a018 <unimplemented_content>
    4aaf:	e8 9c fb ff ff       	call   4650 <_send_static_string_content>
}
    4ab4:	eb d0                	jmp    4a86 <handle_http_method+0x96>
    4ab6:	e8 75 d8 ff ff       	call   2330 <__stack_chk_fail@plt>
    4abb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004ac0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4ac0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4ac4:	85 d2                	test   %edx,%edx
    4ac6:	7e 38                	jle    4b00 <get_line+0x40>
    4ac8:	48 63 d2             	movslq %edx,%rdx
    4acb:	48 83 c7 01          	add    $0x1,%rdi
    4acf:	48 01 f2             	add    %rsi,%rdx
    4ad2:	eb 11                	jmp    4ae5 <get_line+0x25>
    4ad4:	0f 1f 40 00          	nopl   0x0(%rax)
    4ad8:	48 83 c6 01          	add    $0x1,%rsi
    4adc:	48 83 c7 01          	add    $0x1,%rdi
    4ae0:	48 39 d6             	cmp    %rdx,%rsi
    4ae3:	74 1b                	je     4b00 <get_line+0x40>
        dest[i] = src[i];
    4ae5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4ae9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4aeb:	3c 0d                	cmp    $0xd,%al
    4aed:	75 e9                	jne    4ad8 <get_line+0x18>
    4aef:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4af2:	75 e4                	jne    4ad8 <get_line+0x18>
            dest[i] = '\0';
    4af4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4af7:	31 c0                	xor    %eax,%eax
    4af9:	c3                   	ret
    4afa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4b00:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4b05:	c3                   	ret
    4b06:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004b10 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4b10:	f3 0f 1e fa          	endbr64
    4b14:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4b1b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4b1f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b28:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4b30:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4b32:	49 89 e2             	mov    %rsp,%r10
    4b35:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4b3d:	4c 89 d0             	mov    %r10,%rax
    4b40:	eb 13                	jmp    4b55 <handle_client_request+0x45>
    4b42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b48:	48 83 c0 01          	add    $0x1,%rax
    4b4c:	48 83 c1 01          	add    $0x1,%rcx
    4b50:	4c 39 c8             	cmp    %r9,%rax
    4b53:	74 4b                	je     4ba0 <handle_client_request+0x90>
        dest[i] = src[i];
    4b55:	44 0f b6 01          	movzbl (%rcx),%r8d
    4b59:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4b5c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4b60:	75 e6                	jne    4b48 <handle_client_request+0x38>
    4b62:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4b66:	75 e0                	jne    4b48 <handle_client_request+0x38>
            dest[i] = '\0';
    4b68:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4b6b:	8b 47 08             	mov    0x8(%rdi),%eax
    4b6e:	48 89 f2             	mov    %rsi,%rdx
    4b71:	4c 89 d7             	mov    %r10,%rdi
    4b74:	89 c6                	mov    %eax,%esi
    4b76:	e8 75 fe ff ff       	call   49f0 <handle_http_method>
}
    4b7b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4b83:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b8c:	75 39                	jne    4bc7 <handle_client_request+0xb7>
    4b8e:	31 c0                	xor    %eax,%eax
    4b90:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4b97:	c3                   	ret
    4b98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4ba0:	48 8b 0d 79 54 00 00 	mov    0x5479(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4ba7:	ba 12 00 00 00       	mov    $0x12,%edx
    4bac:	be 01 00 00 00       	mov    $0x1,%esi
    4bb1:	48 8d 3d 7f 25 00 00 	lea    0x257f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4bb8:	e8 03 d9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4bbd:	bf 01 00 00 00       	mov    $0x1,%edi
    4bc2:	e8 d9 d8 ff ff       	call   24a0 <exit@plt>
}
    4bc7:	e8 64 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
    4bcc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004bd0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4bd0:	f3 0f 1e fa          	endbr64
    4bd4:	55                   	push   %rbp
    4bd5:	53                   	push   %rbx
    4bd6:	48 89 cb             	mov    %rcx,%rbx
    4bd9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4bdd:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4be0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4be3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4be9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4bec:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4bef:	f6 c1 02             	test   $0x2,%cl
    4bf2:	74 00                	je     4bf4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4bf4:	41 89 c0             	mov    %eax,%r8d
    4bf7:	45 29 c8             	sub    %r9d,%r8d
    4bfa:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4bfe:	0f 82 88 d9 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4c04:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c07:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4c0a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4c0d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4c10:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4c13:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c17:	d3 e5                	shl    %cl,%ebp
    4c19:	48 c1 e5 06          	shl    $0x6,%rbp
    4c1d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4c21:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4c24:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4c29:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4c30:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4c34:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4c38:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4c40:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4c48:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4c4c:	e8 bf d7 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4c51:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4c54:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4c5a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4c5e:	48 83 c4 08          	add    $0x8,%rsp
    4c62:	5b                   	pop    %rbx
    4c63:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4c64:	e9 d7 d6 ff ff       	jmp    2340 <io_uring_submit@plt>
    4c69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004c70 <io_thread>:
void* io_thread(void *arg) {
    4c70:	f3 0f 1e fa          	endbr64
    4c74:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4c76:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4c78:	41 56                	push   %r14
    4c7a:	41 55                	push   %r13
    4c7c:	41 54                	push   %r12
    4c7e:	55                   	push   %rbp
    4c7f:	48 89 fd             	mov    %rdi,%rbp
    4c82:	53                   	push   %rbx
    4c83:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4c8a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4c93:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4c9b:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4c9f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4ca4:	bf 00 01 00 00       	mov    $0x100,%edi
    4ca9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4cac:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4cb0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4cb5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4cba:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4cbf:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4cc4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4ccc:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4cd1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4cd9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4cde:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4ce6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4ceb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4cf3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4cf8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4d00:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4d05:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4d0d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4d15:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4d1d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4d25:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4d2d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4d35:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4d3d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4d45:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4d4d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4d55:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4d5d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4d64:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4d6c:	e8 7f d6 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4d71:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
    4d75:	31 f6                	xor    %esi,%esi
    4d77:	e8 64 d7 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4d7c:	31 d2                	xor    %edx,%edx
    4d7e:	be 01 00 00 00       	mov    $0x1,%esi
    4d83:	bf 02 00 00 00       	mov    $0x2,%edi
    4d88:	e8 a3 d7 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4d8d:	83 f8 ff             	cmp    $0xffffffff,%eax
    4d90:	0f 84 38 d8 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    4d96:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4d9b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4da1:	89 c7                	mov    %eax,%edi
    4da3:	41 89 c4             	mov    %eax,%r12d
    4da6:	ba 02 00 00 00       	mov    $0x2,%edx
    4dab:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4db0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4db8:	e8 43 d5 ff ff       	call   2300 <setsockopt@plt>
    4dbd:	85 c0                	test   %eax,%eax
    4dbf:	0f 88 dd d7 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4dc5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4dca:	ba 10 00 00 00       	mov    $0x10,%edx
    4dcf:	44 89 e7             	mov    %r12d,%edi
    4dd2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4ddb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4de3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4deb:	e8 70 d6 ff ff       	call   2460 <bind@plt>
    4df0:	85 c0                	test   %eax,%eax
    4df2:	0f 88 e2 d7 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4df8:	be 0a 00 00 00       	mov    $0xa,%esi
    4dfd:	44 89 e7             	mov    %r12d,%edi
    4e00:	e8 1b d6 ff ff       	call   2420 <listen@plt>
    4e05:	85 c0                	test   %eax,%eax
    4e07:	0f 88 a1 d7 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4e0d:	ba db 18 00 00       	mov    $0x18db,%edx
    4e12:	48 8d 35 63 23 00 00 	lea    0x2363(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4e19:	bf 01 00 00 00       	mov    $0x1,%edi
    4e1e:	31 c0                	xor    %eax,%eax
    4e20:	e8 2b d6 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4e25:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4e2a:	48 89 d9             	mov    %rbx,%rcx
    4e2d:	44 89 e7             	mov    %r12d,%edi
    4e30:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4e35:	48 89 c6             	mov    %rax,%rsi
    4e38:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4e3d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4e42:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4e4a:	e8 81 fd ff ff       	call   4bd0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4e4f:	bf 01 00 00 00       	mov    $0x1,%edi
    4e54:	be 10 00 00 00       	mov    $0x10,%esi
    4e59:	e8 42 d5 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    4e5e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4e63:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4e66:	e8 a5 d5 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4e6b:	48 85 c0             	test   %rax,%rax
    4e6e:	0f 84 ae 04 00 00    	je     5322 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    4e74:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4e78:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e7f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    4e86:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4e8e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4e91:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4e96:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4e98:	f6 c1 02             	test   $0x2,%cl
    4e9b:	0f 85 0f 04 00 00    	jne    52b0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    4ea1:	89 d0                	mov    %edx,%eax
    4ea3:	29 f0                	sub    %esi,%eax
    4ea5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4eac:	0f 82 12 d7 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4eb2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4eb5:	48 8d 75 50          	lea    0x50(%rbp),%rsi
	sqe->addr3 = 0;
    4eb9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4ebd:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ec0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4ec7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4eca:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4ed1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ed8:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4eda:	8b 55 50             	mov    0x50(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4edd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4ee2:	48 c1 e0 06          	shl    $0x6,%rax
    4ee6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4eee:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4ef4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4ef7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4eff:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4f03:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4f0b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4f13:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4f17:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4f1b:	e8 20 d4 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4f20:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4f24:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4f29:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4f31:	0f 85 d7 01 00 00    	jne    510e <io_thread+0x49e>
    4f37:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4f3c:	4d 89 ce             	mov    %r9,%r14
    4f3f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4f44:	0f 1f 40 00          	nopl   0x0(%rax)
    4f48:	48 8d 3d 43 22 00 00 	lea    0x2243(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    4f4f:	e8 9c d3 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4f54:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4f5b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4f62:	c1 e9 0b             	shr    $0xb,%ecx
    4f65:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4f68:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4f70:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4f72:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4f7a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4f7c:	39 d0                	cmp    %edx,%eax
    4f7e:	74 36                	je     4fb6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4f80:	89 f8                	mov    %edi,%eax
    4f82:	21 d0                	and    %edx,%eax
    4f84:	d3 e0                	shl    %cl,%eax
    4f86:	48 c1 e0 04          	shl    $0x4,%rax
    4f8a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4f92:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4f9a:	0f 85 a8 01 00 00    	jne    5148 <io_thread+0x4d8>
    4fa0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4fa4:	0f 85 0e 03 00 00    	jne    52b8 <io_thread+0x648>
			if (cqe->res < 0)
    4faa:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4fad:	83 c2 01             	add    $0x1,%edx
    4fb0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4fb2:	85 c0                	test   %eax,%eax
    4fb4:	79 b2                	jns    4f68 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    4fb6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    4fbf:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4fc0:	45 31 c0             	xor    %r8d,%r8d
    4fc3:	31 d2                	xor    %edx,%edx
    4fc5:	b9 01 00 00 00       	mov    $0x1,%ecx
    4fca:	4c 89 f6             	mov    %r14,%rsi
    4fcd:	48 89 df             	mov    %rbx,%rdi
    4fd0:	e8 6b d4 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    4fd5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    4fd8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4fdd:	48 83 38 01          	cmpq   $0x1,(%rax)
    4fe1:	0f 84 e1 02 00 00    	je     52c8 <io_thread+0x658>
    4fe7:	48 8d 3d ca 21 00 00 	lea    0x21ca(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    4fee:	e8 fd d2 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4ff3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4ff8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4ffb:	45 85 ff             	test   %r15d,%r15d
    4ffe:	0f 88 92 d5 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    5004:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5007:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    500b:	85 c0                	test   %eax,%eax
    500d:	0f 88 d5 02 00 00    	js     52e8 <io_thread+0x678>
      switch (req->event_type) {
    5013:	41 83 f8 01          	cmp    $0x1,%r8d
    5017:	0f 84 7b 01 00 00    	je     5198 <io_thread+0x528>
    501d:	41 83 f8 02          	cmp    $0x2,%r8d
    5021:	0f 84 a1 01 00 00    	je     51c8 <io_thread+0x558>
    5027:	45 85 c0             	test   %r8d,%r8d
    502a:	0f 85 50 01 00 00    	jne    5180 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5030:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5035:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    503a:	48 89 d9             	mov    %rbx,%rcx
    503d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5041:	e8 8a fb ff ff       	call   4bd0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5046:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    504b:	48 89 de             	mov    %rbx,%rsi
    504e:	8b 78 08             	mov    0x8(%rax),%edi
    5051:	e8 1a f5 ff ff       	call   4570 <add_read_request>
              free(req);
    5056:	4c 89 e7             	mov    %r12,%rdi
    5059:	e8 62 d2 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    505e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5063:	48 85 c0             	test   %rax,%rax
    5066:	0f 85 14 01 00 00    	jne    5180 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    506c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5073:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    507a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    507d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5082:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5084:	f6 c1 02             	test   $0x2,%cl
    5087:	74 00                	je     5089 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5089:	89 d0                	mov    %edx,%eax
    508b:	29 f0                	sub    %esi,%eax
    508d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5094:	0f 82 20 d5 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    509a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    509d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    50a2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    50a6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50a9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    50b0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50b3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    50ba:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50c1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    50c3:	8b 55 50             	mov    0x50(%rbp),%edx
    50c6:	48 c1 e0 06          	shl    $0x6,%rax
    50ca:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    50d2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    50d8:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    50db:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    50e3:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    50e7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    50ef:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    50f7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    50fb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    50ff:	e8 3c d2 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5104:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    5108:	0f 84 3a fe ff ff    	je     4f48 <io_thread+0x2d8>
    510e:	48 8d 3d dc 20 00 00 	lea    0x20dc(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    5115:	e8 d6 d1 ff ff       	call   22f0 <puts@plt>
}
    511a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5122:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    512b:	0f 85 18 02 00 00    	jne    5349 <io_thread+0x6d9>
    5131:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5138:	31 c0                	xor    %eax,%eax
    513a:	5b                   	pop    %rbx
    513b:	5d                   	pop    %rbp
    513c:	41 5c                	pop    %r12
    513e:	41 5d                	pop    %r13
    5140:	41 5e                	pop    %r14
    5142:	41 5f                	pop    %r15
    5144:	c3                   	ret
    5145:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5148:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    514d:	48 85 c0             	test   %rax,%rax
    5150:	0f 84 6a fe ff ff    	je     4fc0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5156:	48 83 38 01          	cmpq   $0x1,(%rax)
    515a:	0f 84 68 01 00 00    	je     52c8 <io_thread+0x658>
    5160:	48 8d 3d 51 20 00 00 	lea    0x2051(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    5167:	e8 84 d1 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    516c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5171:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5174:	e9 8b fe ff ff       	jmp    5004 <io_thread+0x394>
    5179:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5180:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5188:	8b 02                	mov    (%rdx),%eax
    518a:	83 c0 01             	add    $0x1,%eax
    518d:	89 02                	mov    %eax,(%rdx)
}
    518f:	e9 d8 fe ff ff       	jmp    506c <io_thread+0x3fc>
    5194:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5198:	85 c0                	test   %eax,%eax
    519a:	75 74                	jne    5210 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    519c:	48 8b 0d 7d 4e 00 00 	mov    0x4e7d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    51a3:	ba 0f 00 00 00       	mov    $0xf,%edx
    51a8:	be 01 00 00 00       	mov    $0x1,%esi
    51ad:	48 8d 3d 2d 20 00 00 	lea    0x202d(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    51b4:	e8 07 d3 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    51b9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    51be:	e9 a0 fe ff ff       	jmp    5063 <io_thread+0x3f3>
    51c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    51c8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    51cd:	45 31 ff             	xor    %r15d,%r15d
    51d0:	85 c0                	test   %eax,%eax
    51d2:	7e 20                	jle    51f4 <io_thread+0x584>
    51d4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    51d8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    51db:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    51df:	48 c1 e0 04          	shl    $0x4,%rax
    51e3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    51e8:	e8 d3 d0 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    51ed:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    51f2:	7f e4                	jg     51d8 <io_thread+0x568>
              close(req->client_socket);
    51f4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    51f9:	e8 72 d1 ff ff       	call   2370 <close@plt>
              free(req);
    51fe:	4c 89 e7             	mov    %r12,%rdi
    5201:	e8 ba d0 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5206:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    520b:	e9 53 fe ff ff       	jmp    5063 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5210:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5215:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    521a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5222:	eb 11                	jmp    5235 <io_thread+0x5c5>
    5224:	0f 1f 40 00          	nopl   0x0(%rax)
    5228:	48 83 c0 01          	add    $0x1,%rax
    522c:	48 83 c2 01          	add    $0x1,%rdx
    5230:	48 39 c6             	cmp    %rax,%rsi
    5233:	74 4b                	je     5280 <io_thread+0x610>
        dest[i] = src[i];
    5235:	0f b6 0a             	movzbl (%rdx),%ecx
    5238:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    523a:	80 f9 0d             	cmp    $0xd,%cl
    523d:	75 e9                	jne    5228 <io_thread+0x5b8>
    523f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5243:	75 e3                	jne    5228 <io_thread+0x5b8>
            dest[i] = '\0';
    5245:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5248:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    524d:	48 89 da             	mov    %rbx,%rdx
    5250:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5255:	e8 96 f7 ff ff       	call   49f0 <handle_http_method>
              free(req->iov[0].iov_base);
    525a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    525f:	e8 5c d0 ff ff       	call   22c0 <free@plt>
              free(req);
    5264:	4c 89 e7             	mov    %r12,%rdi
    5267:	e8 54 d0 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    526c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5271:	e9 ed fd ff ff       	jmp    5063 <io_thread+0x3f3>
    5276:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5280:	48 8b 0d 99 4d 00 00 	mov    0x4d99(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5287:	ba 12 00 00 00       	mov    $0x12,%edx
    528c:	be 01 00 00 00       	mov    $0x1,%esi
    5291:	48 8d 3d 9f 1e 00 00 	lea    0x1e9f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5298:	e8 23 d2 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    529d:	bf 01 00 00 00       	mov    $0x1,%edi
    52a2:	e8 f9 d1 ff ff       	call   24a0 <exit@plt>
    52a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    52b0:	e9 ec fb ff ff       	jmp    4ea1 <io_thread+0x231>
    52b5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    52b8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    52bd:	e9 94 fe ff ff       	jmp    5156 <io_thread+0x4e6>
    52c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    52c8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    52d0:	48 8d 3d cd 1e 00 00 	lea    0x1ecd(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    52d7:	8b 02                	mov    (%rdx),%eax
    52d9:	83 c0 01             	add    $0x1,%eax
    52dc:	89 02                	mov    %eax,(%rdx)
    52de:	e8 0d d0 ff ff       	call   22f0 <puts@plt>
    52e3:	e9 26 fe ff ff       	jmp    510e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    52e8:	f7 d8                	neg    %eax
    52ea:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    52ef:	89 c7                	mov    %eax,%edi
    52f1:	e8 0a d2 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    52f6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    52fb:	be 01 00 00 00       	mov    $0x1,%esi
    5300:	48 8b 3d 19 4d 00 00 	mov    0x4d19(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5307:	48 89 c1             	mov    %rax,%rcx
    530a:	48 8d 15 27 21 00 00 	lea    0x2127(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    5311:	31 c0                	xor    %eax,%eax
    5313:	e8 b8 d1 ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5318:	bf 01 00 00 00       	mov    $0x1,%edi
    531d:	e8 7e d1 ff ff       	call   24a0 <exit@plt>
    5322:	48 8b 0d f7 4c 00 00 	mov    0x4cf7(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5329:	ba 28 00 00 00       	mov    $0x28,%edx
    532e:	be 01 00 00 00       	mov    $0x1,%esi
    5333:	48 8d 3d ce 20 00 00 	lea    0x20ce(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    533a:	e8 81 d1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    533f:	bf 01 00 00 00       	mov    $0x1,%edi
    5344:	e8 57 d1 ff ff       	call   24a0 <exit@plt>
}
    5349:	e8 e2 cf ff ff       	call   2330 <__stack_chk_fail@plt>
    534e:	66 90                	xchg   %ax,%ax

0000000000005350 <sendm>:
int sendm(struct BarrierTask *data) {
    5350:	f3 0f 1e fa          	endbr64
    5354:	41 57                	push   %r15
    5356:	41 56                	push   %r14
    5358:	41 55                	push   %r13
    535a:	41 54                	push   %r12
    535c:	55                   	push   %rbp
    535d:	53                   	push   %rbx
    535e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5362:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
    5369:	0f 85 99 01 00 00    	jne    5508 <sendm+0x1b8>
    536f:	48 8d b7 80 01 00 00 	lea    0x180(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5376:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    537c:	48 89 fa             	mov    %rdi,%rdx
    537f:	31 c9                	xor    %ecx,%ecx
    5381:	48 89 34 24          	mov    %rsi,(%rsp)
    5385:	48 8d b7 88 01 00 00 	lea    0x188(%rdi),%rsi
    538c:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5391:	85 c0                	test   %eax,%eax
    5393:	0f 8e ce 00 00 00    	jle    5467 <sendm+0x117>
    5399:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    53a0:	39 8a 30 01 00 00    	cmp    %ecx,0x130(%rdx)
    53a6:	0f 84 af 00 00 00    	je     545b <sendm+0x10b>
        struct Data *them = data->mailboxes[n].higher;
    53ac:	49 89 ca             	mov    %rcx,%r10
    53af:	49 c1 e2 05          	shl    $0x5,%r10
    53b3:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
    53ba:	4d 8b 5a 08          	mov    0x8(%r10),%r11
        for (; them->messages_count < min;) {
    53be:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    53c2:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    53c6:	4c 39 cb             	cmp    %r9,%rbx
    53c9:	0f 8d 83 00 00 00    	jge    5452 <sendm+0x102>
    53cf:	4c 89 cf             	mov    %r9,%rdi
    53d2:	48 8b aa 08 01 00 00 	mov    0x108(%rdx),%rbp
    53d9:	4d 8b 72 10          	mov    0x10(%r10),%r14
    53dd:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    53e0:	49 8b 33             	mov    (%r11),%rsi
    53e3:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    53e7:	48 83 f8 02          	cmp    $0x2,%rax
    53eb:	0f 86 ff 00 00 00    	jbe    54f0 <sendm+0x1a0>
    53f1:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    53f9:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5401:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    5405:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    5409:	4c 39 2c 24          	cmp    %r13,(%rsp)
    540d:	73 71                	jae    5480 <sendm+0x130>
    540f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5414:	4d 39 fc             	cmp    %r15,%r12
    5417:	73 67                	jae    5480 <sendm+0x130>
    5419:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    541d:	49 01 f0             	add    %rsi,%r8
    5420:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    5427:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    542b:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    542f:	49 39 d8             	cmp    %rbx,%r8
    5432:	75 ec                	jne    5420 <sendm+0xd0>
    5434:	0f 1f 40 00          	nopl   0x0(%rax)
    5438:	48 01 fd             	add    %rdi,%rbp
    543b:	4c 01 f7             	add    %r14,%rdi
    543e:	48 89 aa 08 01 00 00 	mov    %rbp,0x108(%rdx)
    5445:	49 89 7a 10          	mov    %rdi,0x10(%r10)
    5449:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    544d:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5452:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5455:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    545b:	48 83 c1 01          	add    $0x1,%rcx
    545f:	39 c8                	cmp    %ecx,%eax
    5461:	0f 8f 39 ff ff ff    	jg     53a0 <sendm+0x50>
}
    5467:	48 83 c4 18          	add    $0x18,%rsp
    546b:	31 c0                	xor    %eax,%eax
    546d:	5b                   	pop    %rbx
    546e:	5d                   	pop    %rbp
    546f:	41 5c                	pop    %r12
    5471:	41 5d                	pop    %r13
    5473:	41 5e                	pop    %r14
    5475:	41 5f                	pop    %r15
    5477:	c3                   	ret
    5478:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5480:	49 89 fd             	mov    %rdi,%r13
    5483:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    548a:	4d 89 e0             	mov    %r12,%r8
    548d:	49 d1 ed             	shr    %r13
    5490:	49 c1 e5 04          	shl    $0x4,%r13
    5494:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5499:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    549d:	41 83 e5 10          	and    $0x10,%r13d
    54a1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    54a5:	74 11                	je     54b8 <sendm+0x168>
          them->messages[them->messages_count++] = data->message; 
    54a7:	49 83 c0 10          	add    $0x10,%r8
    54ab:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    54b0:	4d 39 f8             	cmp    %r15,%r8
    54b3:	74 15                	je     54ca <sendm+0x17a>
    54b5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    54b8:	41 0f 11 00          	movups %xmm0,(%r8)
    54bc:	49 83 c0 20          	add    $0x20,%r8
    54c0:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    54c5:	4d 39 f8             	cmp    %r15,%r8
    54c8:	75 ee                	jne    54b8 <sendm+0x168>
    54ca:	49 89 f8             	mov    %rdi,%r8
    54cd:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    54d1:	49 01 d8             	add    %rbx,%r8
    54d4:	40 f6 c7 01          	test   $0x1,%dil
    54d8:	0f 84 5a ff ff ff    	je     5438 <sendm+0xe8>
          them->messages[them->messages_count++] = data->message; 
    54de:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    54e5:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    54e9:	e9 4a ff ff ff       	jmp    5438 <sendm+0xe8>
    54ee:	66 90                	xchg   %ax,%ax
    54f0:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    54f8:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5500:	e9 14 ff ff ff       	jmp    5419 <sendm+0xc9>
    5505:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5508:	48 8d 3d f5 1c 00 00 	lea    0x1cf5(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    550f:	e8 dc cd ff ff       	call   22f0 <puts@plt>
    5514:	e9 4e ff ff ff       	jmp    5467 <sendm+0x117>
    5519:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005520 <receive>:
int receive(struct BarrierTask *data) {
    5520:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5524:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    552a:	85 c0                	test   %eax,%eax
    552c:	0f 8e f1 00 00 00    	jle    5623 <receive+0x103>
int receive(struct BarrierTask *data) {
    5532:	41 54                	push   %r12
    5534:	48 89 fa             	mov    %rdi,%rdx
    5537:	55                   	push   %rbp
    5538:	31 ed                	xor    %ebp,%ebp
    553a:	53                   	push   %rbx
    553b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5540:	48 89 ee             	mov    %rbp,%rsi
    5543:	48 c1 e6 05          	shl    $0x5,%rsi
    5547:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    554e:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5551:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    5556:	48 85 ff             	test   %rdi,%rdi
    5559:	0f 8e a1 00 00 00    	jle    5600 <receive+0xe0>
      data->sends++;
    555f:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    5566:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    556a:	4c 63 1a             	movslq (%rdx),%r11
    556d:	49 89 c9             	mov    %rcx,%r9
    5570:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5574:	49 f7 d9             	neg    %r9
    5577:	48 01 c7             	add    %rax,%rdi
    557a:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    557e:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    5585:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    5589:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    558c:	49 29 c8             	sub    %rcx,%r8
    558f:	eb 10                	jmp    55a1 <receive+0x81>
    5591:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5598:	48 83 c0 01          	add    $0x1,%rax
    559c:	48 39 c7             	cmp    %rax,%rdi
    559f:	74 5f                	je     5600 <receive+0xe0>
      data->n++;
    55a1:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    55a5:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
      data->n++;
    55ac:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    55b3:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    55b7:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    55bb:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    55c0:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    55c4:	75 d2                	jne    5598 <receive+0x78>
    55c6:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    55cd:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    55d1:	75 c5                	jne    5598 <receive+0x78>
    55d3:	bf 01 00 00 00       	mov    $0x1,%edi
    55d8:	b9 01 00 00 00       	mov    $0x1,%ecx
    55dd:	ba 01 00 00 00       	mov    $0x1,%edx
    55e2:	31 c0                	xor    %eax,%eax
    55e4:	48 8d 35 75 1e 00 00 	lea    0x1e75(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    55eb:	e8 60 ce ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    55f0:	bf 01 00 00 00       	mov    $0x1,%edi
    55f5:	e8 a6 ce ff ff       	call   24a0 <exit@plt>
    55fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5600:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    5609:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    560c:	48 83 c5 01          	add    $0x1,%rbp
    5610:	39 aa 34 01 00 00    	cmp    %ebp,0x134(%rdx)
    5616:	0f 8f 24 ff ff ff    	jg     5540 <receive+0x20>
}
    561c:	5b                   	pop    %rbx
    561d:	31 c0                	xor    %eax,%eax
    561f:	5d                   	pop    %rbp
    5620:	41 5c                	pop    %r12
    5622:	c3                   	ret
    5623:	31 c0                	xor    %eax,%eax
    5625:	c3                   	ret
    5626:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005630 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5630:	f3 0f 1e fa          	endbr64
    5634:	41 57                	push   %r15
    5636:	41 56                	push   %r14
    5638:	41 55                	push   %r13
    563a:	41 54                	push   %r12
    563c:	55                   	push   %rbp
    563d:	53                   	push   %rbx
    563e:	48 89 fb             	mov    %rdi,%rbx
    5641:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    5645:	8b 07                	mov    (%rdi),%eax
    5647:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    564d:	0f 84 3d 01 00 00    	je     5790 <barriered_work+0x160>
    receive(data);
    5653:	e8 c8 fe ff ff       	call   5520 <receive>
    while (data->scheduled == 1) {
    5658:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    565f:	75 1b                	jne    567c <barriered_work+0x4c>
    5661:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    5668:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    5670:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5673:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    567a:	74 ec                	je     5668 <barriered_work+0x38>
  if (data->sending == 1) {
    567c:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    5683:	0f 85 74 02 00 00    	jne    58fd <barriered_work+0x2cd>
      for (int n = 0 ; n < data->thread_count; n++) {
    5689:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    568f:	85 c0                	test   %eax,%eax
    5691:	0f 8e 72 02 00 00    	jle    5909 <barriered_work+0x2d9>
    5697:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    569e:	31 d2                	xor    %edx,%edx
    56a0:	48 89 0c 24          	mov    %rcx,(%rsp)
    56a4:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    56ab:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    56b0:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    56b6:	0f 84 bf 00 00 00    	je     577b <barriered_work+0x14b>
        struct Data *them = data->mailboxes[n].higher;
    56bc:	49 89 d1             	mov    %rdx,%r9
    56bf:	49 c1 e1 05          	shl    $0x5,%r9
    56c3:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    56ca:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    56ce:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    56d2:	4d 63 42 10          	movslq 0x10(%r10),%r8
    56d6:	4d 39 c3             	cmp    %r8,%r11
    56d9:	0f 8d 93 00 00 00    	jge    5772 <barriered_work+0x142>
    56df:	4c 89 c6             	mov    %r8,%rsi
    56e2:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    56e9:	4d 8b 71 10          	mov    0x10(%r9),%r14
    56ed:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    56f0:	49 8b 0a             	mov    (%r10),%rcx
    56f3:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    56f7:	48 83 f8 02          	cmp    $0x2,%rax
    56fb:	0f 86 8f 02 00 00    	jbe    5990 <barriered_work+0x360>
    5701:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5709:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5711:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5715:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5719:	4c 39 2c 24          	cmp    %r13,(%rsp)
    571d:	0f 83 fd 01 00 00    	jae    5920 <barriered_work+0x2f0>
    5723:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5728:	4d 39 fc             	cmp    %r15,%r12
    572b:	0f 83 ef 01 00 00    	jae    5920 <barriered_work+0x2f0>
    5731:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5735:	48 01 cf             	add    %rcx,%rdi
    5738:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5740:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5747:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    574b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    574f:	49 39 fb             	cmp    %rdi,%r11
    5752:	75 ec                	jne    5740 <barriered_work+0x110>
    5754:	0f 1f 40 00          	nopl   0x0(%rax)
    5758:	48 01 f5             	add    %rsi,%rbp
    575b:	4c 01 f6             	add    %r14,%rsi
    575e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5765:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5769:	4d 89 42 08          	mov    %r8,0x8(%r10)
    576d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5772:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5775:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    577b:	48 83 c2 01          	add    $0x1,%rdx
    577f:	39 d0                	cmp    %edx,%eax
    5781:	0f 8f 29 ff ff ff    	jg     56b0 <barriered_work+0x80>
    5787:	e9 7d 01 00 00       	jmp    5909 <barriered_work+0x2d9>
    578c:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    5790:	e8 8b fd ff ff       	call   5520 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    5795:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    579c:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    579e:	45 85 c9             	test   %r9d,%r9d
    57a1:	0f 8e 85 00 00 00    	jle    582c <barriered_work+0x1fc>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    57a7:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    57ae:	4c 63 d8             	movslq %eax,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    57b1:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    57b4:	49 c1 e3 09          	shl    $0x9,%r11
    57b8:	4c 8b 52 10          	mov    0x10(%rdx),%r10
              int next_task = abs((t + 1) % (data->thread_count));
    57bc:	99                   	cltd
    57bd:	41 f7 f9             	idiv   %r9d
    57c0:	4c 89 d7             	mov    %r10,%rdi
    57c3:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
    57c7:	89 d0                	mov    %edx,%eax
    57c9:	f7 d8                	neg    %eax
    57cb:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    57ce:	45 31 c0             	xor    %r8d,%r8d
              int next_task = abs((t + 1) % (data->thread_count));
    57d1:	48 63 ea             	movslq %edx,%rbp
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    57d4:	48 c1 e5 09          	shl    $0x9,%rbp
    57d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    57e0:	31 c0                	xor    %eax,%eax
    57e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    57e8:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    57ec:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    57f0:	48 8b 8c 2a 68 01 00 00 	mov    0x168(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    57f8:	48 8b 17             	mov    (%rdi),%rdx
    57fb:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    57ff:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5802:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5806:	48 c1 e2 05          	shl    $0x5,%rdx
    580a:	4a 03 94 1e 68 01 00 00 	add    0x168(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5812:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    5816:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    581a:	49 39 c1             	cmp    %rax,%r9
    581d:	75 c9                	jne    57e8 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    581f:	48 83 c7 08          	add    $0x8,%rdi
    5823:	49 83 c0 20          	add    $0x20,%r8
    5827:	49 39 fc             	cmp    %rdi,%r12
    582a:	75 b4                	jne    57e0 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    582c:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    582f:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5836:	31 ff                	xor    %edi,%edi
    5838:	48 c1 e6 05          	shl    $0x5,%rsi
    583c:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5843:	e8 c8 ca ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5848:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    584f:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5856:	48 8b 50 38          	mov    0x38(%rax),%rdx
    585a:	8b 4a 10             	mov    0x10(%rdx),%ecx
    585d:	8d 69 01             	lea    0x1(%rcx),%ebp
    5860:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5863:	75 53                	jne    58b8 <barriered_work+0x288>
    5865:	0f 1f 00             	nopl   (%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5868:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    586f:	48 8b 40 10          	mov    0x10(%rax),%rax
    5873:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    5876:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    587e:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5882:	48 c1 e7 09          	shl    $0x9,%rdi
    5886:	48 03 78 28          	add    0x28(%rax),%rdi
    588a:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    5890:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5893:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    589a:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    58a1:	74 c5                	je     5868 <barriered_work+0x238>
    if (modcount != data->thread->protected_state->modcount) {
    58a3:	48 8b 40 38          	mov    0x38(%rax),%rax
    58a7:	3b 68 10             	cmp    0x10(%rax),%ebp
    58aa:	74 0c                	je     58b8 <barriered_work+0x288>
    58ac:	48 8d 3d 5d 19 00 00 	lea    0x195d(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    58b3:	e8 38 ca ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    58b8:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    58bf:	31 ff                	xor    %edi,%edi
    58c1:	48 c1 e6 05          	shl    $0x5,%rsi
    58c5:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    58cc:	48 83 c6 10          	add    $0x10,%rsi
    58d0:	e8 3b ca ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    58d5:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    58dc:	48 83 c0 01          	add    $0x1,%rax
    58e0:	48 99                	cqto
    58e2:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    58e9:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    58f0:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    58f7:	0f 84 a8 00 00 00    	je     59a5 <barriered_work+0x375>
    58fd:	48 8d 3d 00 19 00 00 	lea    0x1900(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5904:	e8 e7 c9 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5909:	0f ae f8             	sfence
}
    590c:	48 83 c4 18          	add    $0x18,%rsp
    5910:	31 c0                	xor    %eax,%eax
    5912:	5b                   	pop    %rbx
    5913:	5d                   	pop    %rbp
    5914:	41 5c                	pop    %r12
    5916:	41 5d                	pop    %r13
    5918:	41 5e                	pop    %r14
    591a:	41 5f                	pop    %r15
    591c:	c3                   	ret
    591d:	0f 1f 00             	nopl   (%rax)
    5920:	49 89 f5             	mov    %rsi,%r13
    5923:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    592a:	4c 89 e7             	mov    %r12,%rdi
    592d:	49 d1 ed             	shr    %r13
    5930:	49 c1 e5 04          	shl    $0x4,%r13
    5934:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5939:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    593d:	41 83 e5 10          	and    $0x10,%r13d
    5941:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5945:	74 11                	je     5958 <barriered_work+0x328>
          them->messages[them->messages_count++] = data->message; 
    5947:	48 83 c7 10          	add    $0x10,%rdi
    594b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5950:	49 39 ff             	cmp    %rdi,%r15
    5953:	74 13                	je     5968 <barriered_work+0x338>
    5955:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5958:	0f 11 07             	movups %xmm0,(%rdi)
    595b:	48 83 c7 20          	add    $0x20,%rdi
    595f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5963:	49 39 ff             	cmp    %rdi,%r15
    5966:	75 f0                	jne    5958 <barriered_work+0x328>
    5968:	48 89 f7             	mov    %rsi,%rdi
    596b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    596f:	4c 01 df             	add    %r11,%rdi
    5972:	40 f6 c6 01          	test   $0x1,%sil
    5976:	0f 84 dc fd ff ff    	je     5758 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    597c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5983:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5987:	e9 cc fd ff ff       	jmp    5758 <barriered_work+0x128>
    598c:	0f 1f 40 00          	nopl   0x0(%rax)
    5990:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5998:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    59a0:	e9 8c fd ff ff       	jmp    5731 <barriered_work+0x101>
      for (int n = 0 ; n < data->thread_count; n++) {
    59a5:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    59ac:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    59b2:	31 d2                	xor    %edx,%edx
    59b4:	48 89 0c 24          	mov    %rcx,(%rsp)
    59b8:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    59bf:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    59c4:	85 c0                	test   %eax,%eax
    59c6:	0f 8e 3d ff ff ff    	jle    5909 <barriered_work+0x2d9>
    59cc:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    59d0:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    59d6:	0f 84 af 00 00 00    	je     5a8b <barriered_work+0x45b>
        struct Data *them = data->mailboxes[n].higher;
    59dc:	49 89 d1             	mov    %rdx,%r9
    59df:	49 c1 e1 05          	shl    $0x5,%r9
    59e3:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    59ea:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    59ee:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    59f2:	4d 63 42 10          	movslq 0x10(%r10),%r8
    59f6:	4d 39 d8             	cmp    %r11,%r8
    59f9:	0f 8e 83 00 00 00    	jle    5a82 <barriered_work+0x452>
    59ff:	4c 89 c6             	mov    %r8,%rsi
    5a02:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5a09:	4d 8b 71 10          	mov    0x10(%r9),%r14
    5a0d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5a10:	49 8b 0a             	mov    (%r10),%rcx
    5a13:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5a17:	48 83 f8 02          	cmp    $0x2,%rax
    5a1b:	0f 86 ef 00 00 00    	jbe    5b10 <barriered_work+0x4e0>
    5a21:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5a29:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5a31:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5a35:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5a39:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5a3d:	73 61                	jae    5aa0 <barriered_work+0x470>
    5a3f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5a44:	4d 39 fc             	cmp    %r15,%r12
    5a47:	73 57                	jae    5aa0 <barriered_work+0x470>
    5a49:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5a4d:	48 01 cf             	add    %rcx,%rdi
    5a50:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5a57:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5a5b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5a5f:	49 39 fb             	cmp    %rdi,%r11
    5a62:	75 ec                	jne    5a50 <barriered_work+0x420>
    5a64:	0f 1f 40 00          	nopl   0x0(%rax)
    5a68:	48 01 f5             	add    %rsi,%rbp
    5a6b:	4c 01 f6             	add    %r14,%rsi
    5a6e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5a75:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5a79:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5a7d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5a82:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5a85:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5a8b:	48 83 c2 01          	add    $0x1,%rdx
    5a8f:	39 d0                	cmp    %edx,%eax
    5a91:	0f 8f 39 ff ff ff    	jg     59d0 <barriered_work+0x3a0>
    5a97:	e9 6d fe ff ff       	jmp    5909 <barriered_work+0x2d9>
    5a9c:	0f 1f 40 00          	nopl   0x0(%rax)
    5aa0:	49 89 f5             	mov    %rsi,%r13
    5aa3:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5aaa:	4c 89 e7             	mov    %r12,%rdi
    5aad:	49 d1 ed             	shr    %r13
    5ab0:	49 c1 e5 04          	shl    $0x4,%r13
    5ab4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5ab9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5abd:	41 83 e5 10          	and    $0x10,%r13d
    5ac1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5ac5:	74 11                	je     5ad8 <barriered_work+0x4a8>
          them->messages[them->messages_count++] = data->message; 
    5ac7:	48 83 c7 10          	add    $0x10,%rdi
    5acb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5ad0:	4c 39 ff             	cmp    %r15,%rdi
    5ad3:	74 13                	je     5ae8 <barriered_work+0x4b8>
    5ad5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5ad8:	0f 11 07             	movups %xmm0,(%rdi)
    5adb:	48 83 c7 20          	add    $0x20,%rdi
    5adf:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5ae3:	4c 39 ff             	cmp    %r15,%rdi
    5ae6:	75 f0                	jne    5ad8 <barriered_work+0x4a8>
    5ae8:	48 89 f7             	mov    %rsi,%rdi
    5aeb:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5aef:	4c 01 df             	add    %r11,%rdi
    5af2:	40 f6 c6 01          	test   $0x1,%sil
    5af6:	0f 84 6c ff ff ff    	je     5a68 <barriered_work+0x438>
          them->messages[them->messages_count++] = data->message; 
    5afc:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b03:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5b07:	e9 5c ff ff ff       	jmp    5a68 <barriered_work+0x438>
    5b0c:	0f 1f 40 00          	nopl   0x0(%rax)
    5b10:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5b18:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5b20:	e9 24 ff ff ff       	jmp    5a49 <barriered_work+0x419>
    5b25:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005b30 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5b30:	f3 0f 1e fa          	endbr64
    5b34:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5b38:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5b3f:	48 8b 40 40          	mov    0x40(%rax),%rax
    5b43:	48 63 10             	movslq (%rax),%rdx
    5b46:	85 d2                	test   %edx,%edx
    5b48:	7e 2c                	jle    5b76 <barriered_work_ingest+0x46>
    5b4a:	48 8b 40 08          	mov    0x8(%rax),%rax
    5b4e:	48 c1 e2 04          	shl    $0x4,%rdx
    5b52:	48 01 c2             	add    %rax,%rdx
    5b55:	0f 1f 00             	nopl   (%rax)
    if (data->thread->buffers->buffer[x].available == 1) {
    5b58:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5b5c:	75 0f                	jne    5b6d <barriered_work_ingest+0x3d>
      data->ingest_count++;
    5b5e:	48 83 87 60 01 00 00 01 	addq   $0x1,0x160(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5b66:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5b6d:	48 83 c0 10          	add    $0x10,%rax
    5b71:	48 39 d0             	cmp    %rdx,%rax
    5b74:	75 e2                	jne    5b58 <barriered_work_ingest+0x28>
  asm volatile ("sfence" ::: "memory");
    5b76:	0f ae f8             	sfence
  barriered_work(data);
    5b79:	e8 b2 fa ff ff       	call   5630 <barriered_work>
}
    5b7e:	31 c0                	xor    %eax,%eax
    5b80:	48 83 c4 08          	add    $0x8,%rsp
    5b84:	c3                   	ret
    5b85:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005b90 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5b90:	f3 0f 1e fa          	endbr64
}
    5b94:	31 c0                	xor    %eax,%eax
    5b96:	c3                   	ret
    5b97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005ba0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5ba0:	f3 0f 1e fa          	endbr64
    5ba4:	31 c0                	xor    %eax,%eax
    5ba6:	c3                   	ret
    5ba7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005bb0 <after>:
int after(struct timespec left, struct timespec right) {
    5bb0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5bb4:	31 c0                	xor    %eax,%eax
    5bb6:	48 39 d7             	cmp    %rdx,%rdi
    5bb9:	7e 08                	jle    5bc3 <after+0x13>
    5bbb:	31 c0                	xor    %eax,%eax
    5bbd:	48 39 ce             	cmp    %rcx,%rsi
    5bc0:	0f 9f c0             	setg   %al
}
    5bc3:	c3                   	ret
    5bc4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5bcf:	90                   	nop

0000000000005bd0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5bd0:	f3 0f 1e fa          	endbr64
    5bd4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5bd9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5bde:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5be0:	48 39 d7             	cmp    %rdx,%rdi
    5be3:	7f 18                	jg     5bfd <within+0x2d>
    5be5:	4d 39 d8             	cmp    %r11,%r8
    5be8:	0f 9e c2             	setle  %dl
    5beb:	48 39 ce             	cmp    %rcx,%rsi
    5bee:	0f 9e c0             	setle  %al
    5bf1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5bf3:	31 c0                	xor    %eax,%eax
    5bf5:	4d 39 d1             	cmp    %r10,%r9
    5bf8:	0f 9e c0             	setle  %al
    5bfb:	21 d0                	and    %edx,%eax
}
    5bfd:	c3                   	ret
    5bfe:	66 90                	xchg   %ax,%ax

0000000000005c00 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5c00:	f3 0f 1e fa          	endbr64
    5c04:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5c09:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5c0e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5c13:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5c18:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5c1d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5c22:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5c27:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5c2c:	48 39 fe             	cmp    %rdi,%rsi
    5c2f:	7d 2f                	jge    5c60 <overlap+0x60>
    5c31:	48 39 ca             	cmp    %rcx,%rdx
    5c34:	7d 62                	jge    5c98 <overlap+0x98>
    5c36:	4d 39 da             	cmp    %r11,%r10
    5c39:	7d 0e                	jge    5c49 <overlap+0x49>
    return 1;
    5c3b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5c40:	4d 39 c1             	cmp    %r8,%r9
    5c43:	0f 8c 7f 00 00 00    	jl     5cc8 <overlap+0xc8>
  return 0;
    5c49:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5c4b:	4d 39 c1             	cmp    %r8,%r9
    5c4e:	7f 4c                	jg     5c9c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5c50:	31 c0                	xor    %eax,%eax
    5c52:	4d 39 da             	cmp    %r11,%r10
    5c55:	0f 9e c0             	setle  %al
    5c58:	c3                   	ret
    5c59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5c60:	7e 4e                	jle    5cb0 <overlap+0xb0>
    5c62:	48 39 ca             	cmp    %rcx,%rdx
    5c65:	7f 39                	jg     5ca0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5c67:	75 31                	jne    5c9a <overlap+0x9a>
    5c69:	4d 39 c1             	cmp    %r8,%r9
    5c6c:	7c 2c                	jl     5c9a <overlap+0x9a>
    return 1;
    5c6e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5c73:	4d 39 da             	cmp    %r11,%r10
    5c76:	7d 24                	jge    5c9c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5c78:	48 39 ca             	cmp    %rcx,%rdx
    5c7b:	0f 94 c2             	sete   %dl
    5c7e:	48 39 fe             	cmp    %rdi,%rsi
    5c81:	0f 94 c0             	sete   %al
    5c84:	21 c2                	and    %eax,%edx
    5c86:	31 c0                	xor    %eax,%eax
    5c88:	4d 39 c1             	cmp    %r8,%r9
    5c8b:	0f 94 c0             	sete   %al
    5c8e:	21 d0                	and    %edx,%eax
    5c90:	c3                   	ret
    5c91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5c98:	74 af                	je     5c49 <overlap+0x49>
  return 0;
    5c9a:	31 c0                	xor    %eax,%eax
}
    5c9c:	c3                   	ret
    5c9d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5ca0:	4d 39 da             	cmp    %r11,%r10
    5ca3:	7e c4                	jle    5c69 <overlap+0x69>
    return 1;
    5ca5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5caa:	4d 39 c1             	cmp    %r8,%r9
    5cad:	7e ba                	jle    5c69 <overlap+0x69>
    5caf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5cb0:	48 39 ca             	cmp    %rcx,%rdx
    5cb3:	7c 94                	jl     5c49 <overlap+0x49>
    5cb5:	4d 39 c1             	cmp    %r8,%r9
    5cb8:	7d b4                	jge    5c6e <overlap+0x6e>
    5cba:	48 39 ca             	cmp    %rcx,%rdx
    5cbd:	74 91                	je     5c50 <overlap+0x50>
    5cbf:	eb d9                	jmp    5c9a <overlap+0x9a>
    5cc1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5cc8:	c3                   	ret
    5cc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005cd0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5cd0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5cd4:	85 f6                	test   %esi,%esi
    5cd6:	0f 8e 44 03 00 00    	jle    6020 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    5cdc:	41 57                	push   %r15
    5cde:	41 89 f7             	mov    %esi,%r15d
    5ce1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5ce3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5ce6:	41 55                	push   %r13
    5ce8:	41 54                	push   %r12
    5cea:	55                   	push   %rbp
    5ceb:	53                   	push   %rbx
    5cec:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5cf0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5cf4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5cf9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5cfe:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    5d01:	45 39 e6             	cmp    %r12d,%r14d
    5d04:	0f 84 4e 02 00 00    	je     5f58 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5d0a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5d0f:	8b 50 08             	mov    0x8(%rax),%edx
    5d12:	85 d2                	test   %edx,%edx
    5d14:	0f 8e 3e 02 00 00    	jle    5f58 <verify+0x288>
    5d1a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    5d1f:	31 c9                	xor    %ecx,%ecx
    5d21:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    5d26:	31 c0                	xor    %eax,%eax
    5d28:	44 89 f2             	mov    %r14d,%edx
    5d2b:	bf 01 00 00 00       	mov    $0x1,%edi
    5d30:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5d35:	48 8d 35 e4 14 00 00 	lea    0x14e4(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    5d3c:	e8 0f c7 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5d41:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5d46:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    5d4b:	8b 40 08             	mov    0x8(%rax),%eax
    5d4e:	85 c0                	test   %eax,%eax
    5d50:	0f 8e e6 01 00 00    	jle    5f3c <verify+0x26c>
    5d56:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5d59:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    5d5e:	31 db                	xor    %ebx,%ebx
    5d60:	48 c1 e0 09          	shl    $0x9,%rax
    5d64:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    5d69:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5d6e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5d73:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    5d78:	4c 8b 20             	mov    (%rax),%r12
    5d7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5d80:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    5d85:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5d8a:	49 89 de             	mov    %rbx,%r14
    5d8d:	48 8d 35 a1 14 00 00 	lea    0x14a1(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5d94:	49 c1 e6 09          	shl    $0x9,%r14
    5d98:	bf 01 00 00 00       	mov    $0x1,%edi
    5d9d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5da1:	4b 8b 8c 3c 58 01 00 00 	mov    0x158(%r12,%r15,1),%rcx
    5da9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    5dae:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    5db6:	31 c0                	xor    %eax,%eax
    5db8:	e8 93 c6 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5dbd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5dc2:	4c 8b 20             	mov    (%rax),%r12
    5dc5:	4b 83 bc 3c 58 01 00 00 00 	cmpq   $0x0,0x158(%r12,%r15,1)
    5dce:	0f 8e 47 01 00 00    	jle    5f1b <verify+0x24b>
    5dd4:	4c 03 75 00          	add    0x0(%rbp),%r14
    5dd8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5ddd:	ba 01 00 00 00       	mov    $0x1,%edx
    5de2:	4d 89 f5             	mov    %r14,%r13
    5de5:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    5dec:	4d 85 f6             	test   %r14,%r14
    5def:	0f 8e 21 01 00 00    	jle    5f16 <verify+0x246>
    5df5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5df8:	48 89 d5             	mov    %rdx,%rbp
    5dfb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5e00:	31 db                	xor    %ebx,%ebx
    5e02:	4d 89 f2             	mov    %r14,%r10
    5e05:	48 c1 e5 05          	shl    $0x5,%rbp
    5e09:	48 83 ed 20          	sub    $0x20,%rbp
    5e0d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    5e11:	49 89 ee             	mov    %rbp,%r14
    5e14:	48 89 dd             	mov    %rbx,%rbp
    5e17:	48 89 d3             	mov    %rdx,%rbx
    5e1a:	eb 31                	jmp    5e4d <verify+0x17d>
    5e1c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5e20:	4c 39 c2             	cmp    %r8,%rdx
    5e23:	0f 8d 57 01 00 00    	jge    5f80 <verify+0x2b0>
    5e29:	4c 39 df             	cmp    %r11,%rdi
    5e2c:	7e 05                	jle    5e33 <verify+0x163>
    5e2e:	49 39 c1             	cmp    %rax,%r9
    5e31:	7c 75                	jl     5ea8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e33:	4c 39 df             	cmp    %r11,%rdi
    5e36:	0f 8d ab 01 00 00    	jge    5fe7 <verify+0x317>
    5e3c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5e40:	48 83 c5 01          	add    $0x1,%rbp
    5e44:	49 39 ea             	cmp    %rbp,%r10
    5e47:	0f 8e a9 00 00 00    	jle    5ef6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5e4d:	49 8b 97 48 01 00 00 	mov    0x148(%r15),%rdx
    5e54:	48 89 e8             	mov    %rbp,%rax
    5e57:	48 c1 e0 05          	shl    $0x5,%rax
    5e5b:	49 03 85 48 01 00 00 	add    0x148(%r13),%rax
    5e62:	4c 01 f2             	add    %r14,%rdx
    5e65:	48 8b 08             	mov    (%rax),%rcx
    5e68:	48 8b 78 10          	mov    0x10(%rax),%rdi
    5e6c:	48 8b 32             	mov    (%rdx),%rsi
    5e6f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    5e73:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    5e77:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    5e7b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    5e7f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    5e83:	48 39 f1             	cmp    %rsi,%rcx
    5e86:	7c 98                	jl     5e20 <verify+0x150>
    5e88:	0f 8e 42 01 00 00    	jle    5fd0 <verify+0x300>
    5e8e:	4c 39 c2             	cmp    %r8,%rdx
    5e91:	0f 8f f9 00 00 00    	jg     5f90 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e97:	75 a7                	jne    5e40 <verify+0x170>
    5e99:	4c 39 df             	cmp    %r11,%rdi
    5e9c:	7f a2                	jg     5e40 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e9e:	49 39 c1             	cmp    %rax,%r9
    5ea1:	7c 9d                	jl     5e40 <verify+0x170>
    5ea3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5ea8:	49 89 c1             	mov    %rax,%r9
    5eab:	48 89 f9             	mov    %rdi,%rcx
    5eae:	48 89 f2             	mov    %rsi,%rdx
    5eb1:	bf 01 00 00 00       	mov    $0x1,%edi
    5eb6:	48 8d 35 cb 15 00 00 	lea    0x15cb(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    5ebd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5ebf:	48 83 c5 01          	add    $0x1,%rbp
    5ec3:	e8 88 c5 ff ff       	call   2450 <__printf_chk@plt>
    5ec8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5ecd:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    5ed2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5ed5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5eda:	4d 8b 95 58 01 00 00 	mov    0x158(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5ee1:	4c 8b 20             	mov    (%rax),%r12
    5ee4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5ee9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5eed:	49 39 ea             	cmp    %rbp,%r10
    5ef0:	0f 8f 57 ff ff ff    	jg     5e4d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5ef6:	48 89 da             	mov    %rbx,%rdx
    5ef9:	49 3b 9f 58 01 00 00 	cmp    0x158(%r15),%rbx
    5f00:	7d 14                	jge    5f16 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5f02:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    5f09:	48 83 c2 01          	add    $0x1,%rdx
    5f0d:	4d 85 f6             	test   %r14,%r14
    5f10:	0f 8f e2 fe ff ff    	jg     5df8 <verify+0x128>
    5f16:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5f1b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5f20:	48 83 c3 01          	add    $0x1,%rbx
    5f24:	39 58 08             	cmp    %ebx,0x8(%rax)
    5f27:	0f 8f 53 fe ff ff    	jg     5d80 <verify+0xb0>
    5f2d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    5f32:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    5f37:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5f3c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5f41:	48 83 c1 01          	add    $0x1,%rcx
    5f45:	39 48 08             	cmp    %ecx,0x8(%rax)
    5f48:	0f 8f d8 fd ff ff    	jg     5d26 <verify+0x56>
    5f4e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    5f53:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    5f58:	48 81 44 24 10 b0 00 00 00 	addq   $0xb0,0x10(%rsp)
    5f61:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    5f66:	41 39 c7             	cmp    %eax,%r15d
    5f69:	0f 84 86 00 00 00    	je     5ff5 <verify+0x325>
    5f6f:	41 89 c4             	mov    %eax,%r12d
    5f72:	e9 8a fd ff ff       	jmp    5d01 <verify+0x31>
    5f77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f80:	0f 85 ba fe ff ff    	jne    5e40 <verify+0x170>
    5f86:	e9 a8 fe ff ff       	jmp    5e33 <verify+0x163>
    5f8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5f90:	49 39 c1             	cmp    %rax,%r9
    5f93:	7e 09                	jle    5f9e <verify+0x2ce>
    5f95:	4c 39 df             	cmp    %r11,%rdi
    5f98:	0f 8c 0a ff ff ff    	jl     5ea8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5f9e:	4c 39 df             	cmp    %r11,%rdi
    5fa1:	0f 8f 99 fe ff ff    	jg     5e40 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5fa7:	49 39 c1             	cmp    %rax,%r9
    5faa:	0f 8d f8 fe ff ff    	jge    5ea8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5fb0:	48 39 f1             	cmp    %rsi,%rcx
    5fb3:	0f 85 87 fe ff ff    	jne    5e40 <verify+0x170>
    5fb9:	4c 39 c2             	cmp    %r8,%rdx
    5fbc:	0f 85 7e fe ff ff    	jne    5e40 <verify+0x170>
    5fc2:	4c 39 df             	cmp    %r11,%rdi
    5fc5:	0f 84 dd fe ff ff    	je     5ea8 <verify+0x1d8>
    5fcb:	e9 70 fe ff ff       	jmp    5e40 <verify+0x170>
    5fd0:	4c 39 c2             	cmp    %r8,%rdx
    5fd3:	0f 8c 5a fe ff ff    	jl     5e33 <verify+0x163>
    5fd9:	4c 39 df             	cmp    %r11,%rdi
    5fdc:	7e c9                	jle    5fa7 <verify+0x2d7>
    5fde:	4c 39 c2             	cmp    %r8,%rdx
    5fe1:	0f 85 59 fe ff ff    	jne    5e40 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5fe7:	49 39 c1             	cmp    %rax,%r9
    5fea:	0f 8f 50 fe ff ff    	jg     5e40 <verify+0x170>
    5ff0:	e9 b3 fe ff ff       	jmp    5ea8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    5ff5:	48 81 44 24 18 b0 00 00 00 	addq   $0xb0,0x18(%rsp)
    5ffe:	41 8d 46 01          	lea    0x1(%r14),%eax
    6002:	45 39 e6             	cmp    %r12d,%r14d
    6005:	74 08                	je     600f <verify+0x33f>
    6007:	41 89 c6             	mov    %eax,%r14d
    600a:	e9 ea fc ff ff       	jmp    5cf9 <verify+0x29>
}
    600f:	48 83 c4 58          	add    $0x58,%rsp
    6013:	31 c0                	xor    %eax,%eax
    6015:	5b                   	pop    %rbx
    6016:	5d                   	pop    %rbp
    6017:	41 5c                	pop    %r12
    6019:	41 5d                	pop    %r13
    601b:	41 5e                	pop    %r14
    601d:	41 5f                	pop    %r15
    601f:	c3                   	ret
    6020:	31 c0                	xor    %eax,%eax
    6022:	c3                   	ret

Disassembly of section .fini:

0000000000006024 <_fini>:
    6024:	f3 0f 1e fa          	endbr64
    6028:	48 83 ec 08          	sub    $0x8,%rsp
    602c:	48 83 c4 08          	add    $0x8,%rsp
    6030:	c3                   	ret
