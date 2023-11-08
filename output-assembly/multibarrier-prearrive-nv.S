
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
    261d:	48 8d 05 8c 12 00 00 	lea    0x128c(%rip),%rax        # 38b0 <barriered_reset>
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
    2734:	be 80 01 00 00       	mov    $0x180,%esi
    2739:	bf 0c 00 00 00       	mov    $0xc,%edi
    273e:	e8 5d fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2743:	be 80 05 00 00       	mov    $0x580,%esi
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
    2764:	4d 8d a7 80 fe ff ff 	lea    -0x180(%r15),%r12
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    276b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    2770:	45 31 ff             	xor    %r15d,%r15d
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2773:	e8 28 fc ff ff       	call   23a0 <calloc@plt>
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2778:	be 00 01 00 00       	mov    $0x100,%esi
    277d:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    2782:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2788:	48 89 c3             	mov    %rax,%rbx
    278b:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2790:	e8 0b fc ff ff       	call   23a0 <calloc@plt>
    2795:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    }
  }
  int external_thread_index = 0;
    279a:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27a2:	48 89 83 80 00 00 00 	mov    %rax,0x80(%rbx)
      buffers[x].buffer[y].available = 0;
    27a9:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    27b3:	4d 89 d1             	mov    %r10,%r9
    27b6:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    27bb:	4c 89 54 24 58       	mov    %r10,0x58(%rsp)
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
    27fd:	0f 84 da 0e 00 00    	je     36dd <main+0x10ed>
      my_thread_data[0] = &thread_data[other]; 
    2803:	49 8d 89 80 fa ff ff 	lea    -0x580(%r9),%rcx
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
    2835:	49 8d 84 24 80 01 00 00 	lea    0x180(%r12),%rax
    283d:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2842:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2847:	4d 89 a1 00 01 00 00 	mov    %r12,0x100(%r9)
    284e:	45 8b 01             	mov    (%r9),%r8d
    2851:	44 89 f1             	mov    %r14d,%ecx
    2854:	89 ea                	mov    %ebp,%edx
    2856:	48 8d 35 13 4d 00 00 	lea    0x4d13(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    285d:	bf 01 00 00 00       	mov    $0x1,%edi
    2862:	31 c0                	xor    %eax,%eax
    2864:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      CPU_SET(j, sendercpu);
    2869:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    286f:	e8 dc fb ff ff       	call   2450 <__printf_chk@plt>
    thread_data[x].other = other;
    2874:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2879:	45 89 b1 10 05 00 00 	mov    %r14d,0x510(%r9)
    for (int j = 0 ; j < cores / 2 ; j++) {
    2880:	45 31 f6             	xor    %r14d,%r14d
    2883:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2888:	44 89 f1             	mov    %r14d,%ecx
    288b:	89 ea                	mov    %ebp,%edx
    288d:	48 8d 35 0c 4d 00 00 	lea    0x4d0c(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    2894:	31 c0                	xor    %eax,%eax
    2896:	bf 01 00 00 00       	mov    $0x1,%edi
    289b:	e8 b0 fb ff ff       	call   2450 <__printf_chk@plt>
      CPU_SET(j, sendercpu);
    28a0:	44 89 f1             	mov    %r14d,%ecx
    28a3:	4c 89 e0             	mov    %r12,%rax
    for (int j = 0 ; j < cores / 2 ; j++) {
    28a6:	41 83 c6 01          	add    $0x1,%r14d
      CPU_SET(j, sendercpu);
    28aa:	48 d3 e0             	shl    %cl,%rax
    28ad:	48 09 03             	or     %rax,(%rbx)
    for (int j = 0 ; j < cores / 2 ; j++) {
    28b0:	41 83 fe 06          	cmp    $0x6,%r14d
    28b4:	75 d2                	jne    2888 <main+0x298>
    thread_data[x].cpu_set = sendercpu;
    28b6:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    thread_data[x].thread_count = 2;
    28bb:	48 8b 05 7e 51 00 00 	mov    0x517e(%rip),%rax        # 7a40 <_IO_stdin_used+0xa40>
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28c2:	be 10 00 00 00       	mov    $0x10,%esi
        thread_data[x].tasks[y].sending = 1;
    28c7:	41 89 ee             	mov    %ebp,%r14d
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28ca:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].cpu_set = sendercpu;
    28cf:	49 89 99 08 05 00 00 	mov    %rbx,0x508(%r9)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28d6:	31 db                	xor    %ebx,%ebx
    thread_data[x].real_thread_index = x;
    28d8:	41 89 69 04          	mov    %ebp,0x4(%r9)
    thread_data[x].threads = my_thread_data;
    28dc:	4d 89 a9 80 00 00 00 	mov    %r13,0x80(%r9)
    thread_data[x].thread_count = 2;
    28e3:	49 89 81 88 00 00 00 	mov    %rax,0x88(%r9)
    thread_data[x].task_count = total_barrier_count;
    28ea:	41 c7 81 a0 00 00 00 03 00 00 00 	movl   $0x3,0xa0(%r9)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28f5:	e8 a6 fa ff ff       	call   23a0 <calloc@plt>
    28fa:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28ff:	be 10 00 00 00       	mov    $0x10,%esi
    2904:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2909:	49 89 81 00 02 00 00 	mov    %rax,0x200(%r9)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2910:	e8 8b fa ff ff       	call   23a0 <calloc@plt>
    2915:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    291a:	be 00 01 00 00       	mov    $0x100,%esi
    thread_data[x].timestamp_count = 0;
    291f:	66 0f 6f 15 f9 50 00 00 	movdqa 0x50f9(%rip),%xmm2        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2927:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    292c:	49 89 81 80 02 00 00 	mov    %rax,0x280(%r9)
    thread_data[x].timestamp_count = 0;
    2933:	41 0f 29 91 80 03 00 00 	movaps %xmm2,0x380(%r9)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    293b:	e8 60 fa ff ff       	call   23a0 <calloc@plt>
    2940:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2945:	be 80 04 00 00       	mov    $0x480,%esi
    thread_data[x].task_timestamp_count = 0;
    294a:	66 0f 6f 1d ce 50 00 00 	movdqa 0x50ce(%rip),%xmm3        # 7a20 <_IO_stdin_used+0xa20>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2952:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2957:	49 89 81 00 04 00 00 	mov    %rax,0x400(%r9)
    thread_data[x].task_timestamp_count = 0;
    295e:	41 0f 29 99 80 04 00 00 	movaps %xmm3,0x480(%r9)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2966:	e8 35 fa ff ff       	call   23a0 <calloc@plt>
      thread_data[x].tasks = barriers;
    296b:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        thread_data[x].tasks[y].sending = 1;
    2970:	44 89 7c 24 28       	mov    %r15d,0x28(%rsp)
    2975:	48 89 c2             	mov    %rax,%rdx
      thread_data[x].tasks = barriers;
    2978:	49 89 81 98 00 00 00 	mov    %rax,0x98(%r9)
        thread_data[x].tasks[y].sending = 1;
    297f:	4c 89 cd             	mov    %r9,%rbp
        thread_data[x].tasks[y].protected = do_protected_write; 
    2982:	4c 63 fb             	movslq %ebx,%r15
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2985:	be 00 02 00 00       	mov    $0x200,%esi
    298a:	bf 0c 00 00 00       	mov    $0xc,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    298f:	4f 8d 24 ff          	lea    (%r15,%r15,8),%r12
    2993:	48 8d 05 c6 0e 00 00 	lea    0xec6(%rip),%rax        # 3860 <do_protected_write>
    299a:	49 c1 e4 07          	shl    $0x7,%r12
    299e:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
    29a2:	49 89 85 10 02 00 00 	mov    %rax,0x210(%r13)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    29a9:	e8 f2 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    29ae:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    29b2:	49 89 85 88 03 00 00 	mov    %rax,0x388(%r13)
        for (int b = 0 ; b < 2 ; b++) {
    29b9:	49 89 c5             	mov    %rax,%r13
    29bc:	48 8d 80 00 04 00 00 	lea    0x400(%rax),%rax
    29c3:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    29c8:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29cd:	be 08 00 00 00       	mov    $0x8,%esi
    29d2:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    29d7:	49 81 c5 00 02 00 00 	add    $0x200,%r13
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29de:	e8 bd f9 ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29e3:	be 08 00 00 00       	mov    $0x8,%esi
    29e8:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29ed:	48 89 c5             	mov    %rax,%rbp
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29f0:	e8 ab f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29f5:	be 00 01 00 00       	mov    $0x100,%esi
    29fa:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29ff:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    2a02:	e8 99 f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    2a07:	66 0f 6f 05 21 50 00 00 	movdqa 0x5021(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
          mailboxes[b].higher = &data[1];
    2a0f:	48 8d b0 00 01 00 00 	lea    0x100(%rax),%rsi
          mailboxes[b].lower = &data[0];
    2a16:	49 89 85 00 fe ff ff 	mov    %rax,-0x200(%r13)
          mailboxes[b].higher = &data[1];
    2a1d:	49 89 b5 80 fe ff ff 	mov    %rsi,-0x180(%r13)
          data[0].messages = messages;
    2a24:	48 89 28             	mov    %rbp,(%rax)
          data[1].messages = messages2;
    2a27:	48 89 98 00 01 00 00 	mov    %rbx,0x100(%rax)
          data[0].messages_count = 0;
    2a2e:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
          data[1].messages_count = 0;
    2a35:	0f 29 80 80 01 00 00 	movaps %xmm0,0x180(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    2a3c:	4c 39 6c 24 08       	cmp    %r13,0x8(%rsp)
    2a41:	75 8a                	jne    29cd <main+0x3dd>
        char *message = malloc(sizeof(char) * 256);
    2a43:	be 01 00 00 00       	mov    $0x1,%esi
    2a48:	bf 00 01 00 00       	mov    $0x100,%edi
    2a4d:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    2a51:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    2a56:	e8 45 f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a5b:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a60:	49 89 c5             	mov    %rax,%r13
        struct Message *messaged = malloc(sizeof(struct Message));
    2a63:	e8 a8 f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a68:	4c 89 ef             	mov    %r13,%rdi
    2a6b:	41 89 d9             	mov    %ebx,%r9d
    2a6e:	45 89 f0             	mov    %r14d,%r8d
    2a71:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2a76:	48 8d 0d 43 4b 00 00 	lea    0x4b43(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a7d:	ba 00 01 00 00       	mov    $0x100,%edx
    2a82:	31 c0                	xor    %eax,%eax
    2a84:	be 01 00 00 00       	mov    $0x1,%esi
    2a89:	e8 92 fa ff ff       	call   2520 <__sprintf_chk@plt>
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a8e:	48 8b 95 98 00 00 00 	mov    0x98(%rbp),%rdx
        messaged->message = message;
    2a95:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a9a:	8d 4b 01             	lea    0x1(%rbx),%ecx
        messaged->thread_index = thread_data[x].thread_index;
    2a9d:	48 63 45 00          	movslq 0x0(%rbp),%rax
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2aa1:	be 20 00 00 00       	mov    $0x20,%esi
    2aa6:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2aab:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
        messaged->message = message;
    2aaf:	4d 89 2a             	mov    %r13,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2ab2:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
        messaged->task_index = y;
    2ab6:	4d 89 7a 10          	mov    %r15,0x10(%r10)
        messaged->thread_index = thread_data[x].thread_index;
    2aba:	49 89 c7             	mov    %rax,%r15
    2abd:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2ac1:	41 89 8d 18 04 00 00 	mov    %ecx,0x418(%r13)
        thread_data[x].tasks[y].message = messaged;
    2ac8:	4d 89 95 10 04 00 00 	mov    %r10,0x410(%r13)
        thread_data[x].tasks[y].snapshot_count = 99;
    2acf:	49 c7 85 00 03 00 00 63 00 00 00 	movq   $0x63,0x300(%r13)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2ada:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2adf:	e8 bc f8 ff ff       	call   23a0 <calloc@plt>
        if (y == barrier_count - 1) {
    2ae4:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2ae7:	41 89 5d 00          	mov    %ebx,0x0(%r13)
        if (y == barrier_count - 1) {
    2aeb:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2aef:	49 89 85 88 02 00 00 	mov    %rax,0x288(%r13)
        if (y == barrier_count - 1) {
    2af6:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
        thread_data[x].tasks[y].available = 1;
    2afb:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2b05:	49 89 85 28 02 00 00 	mov    %rax,0x228(%r13)
        thread_data[x].tasks[y].sending = 1;
    2b0c:	48 b8 01 00 00 00 0c 00 00 00 	movabs $0xc00000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2b16:	49 c7 85 08 03 00 00 00 00 00 00 	movq   $0x0,0x308(%r13)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2b21:	45 89 bd 20 02 00 00 	mov    %r15d,0x220(%r13)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2b28:	49 89 ad 18 02 00 00 	mov    %rbp,0x218(%r13)
        thread_data[x].tasks[y].arrived = 0;
    2b2f:	41 c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r13)
        thread_data[x].tasks[y].thread_count = 2;
    2b3a:	41 c7 85 24 02 00 00 02 00 00 00 	movl   $0x2,0x224(%r13)
        thread_data[x].tasks[y].sending = 1;
    2b45:	49 89 85 08 04 00 00 	mov    %rax,0x408(%r13)
        if (y == barrier_count - 1) {
    2b4c:	0f 84 73 0b 00 00    	je     36c5 <main+0x10d5>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2b52:	44 39 f3             	cmp    %r14d,%ebx
    2b55:	75 71                	jne    2bc8 <main+0x5d8>
    2b57:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    2b5b:	85 db                	test   %ebx,%ebx
    2b5d:	7f 69                	jg     2bc8 <main+0x5d8>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2b5f:	44 89 f2             	mov    %r14d,%edx
    2b62:	bf 01 00 00 00       	mov    $0x1,%edi
    2b67:	31 c0                	xor    %eax,%eax
    2b69:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2b6d:	48 8d 35 74 4a 00 00 	lea    0x4a74(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2b74:	e8 d7 f8 ff ff       	call   2450 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b79:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    2b7e:	48 63 c3             	movslq %ebx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b81:	48 8b 95 98 00 00 00 	mov    0x98(%rbp),%rdx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b88:	48 89 c7             	mov    %rax,%rdi
    2b8b:	48 c1 e0 08          	shl    $0x8,%rax
    2b8f:	48 01 c8             	add    %rcx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b92:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b96:	48 89 85 80 01 00 00 	mov    %rax,0x180(%rbp)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b9d:	48 8d 05 fc 33 00 00 	lea    0x33fc(%rip),%rax        # 5fa0 <barriered_work_ingest>
    2ba4:	4a 89 84 22 08 02 00 00 	mov    %rax,0x208(%rdx,%r12,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2bac:	8d 47 01             	lea    0x1(%rdi),%eax
    2baf:	89 44 24 20          	mov    %eax,0x20(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2bb3:	83 f9 03             	cmp    $0x3,%ecx
    2bb6:	74 23                	je     2bdb <main+0x5eb>
    2bb8:	bb 01 00 00 00       	mov    $0x1,%ebx
    2bbd:	e9 c0 fd ff ff       	jmp    2982 <main+0x392>
    2bc2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            thread_data[x].tasks[y].run = barriered_work; 
    2bc8:	48 8d 05 81 2e 00 00 	lea    0x2e81(%rip),%rax        # 5a50 <barriered_work>
    2bcf:	49 89 85 08 02 00 00 	mov    %rax,0x208(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2bd6:	83 f9 03             	cmp    $0x3,%ecx
    2bd9:	75 dd                	jne    2bb8 <main+0x5c8>

          }
        }
      }
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2bdb:	66 0f 6f 64 24 30    	movdqa 0x30(%rsp),%xmm4
    2be1:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
    2be6:	49 89 e9             	mov    %rbp,%r9
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2be9:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2bf3:	c7 82 80 09 00 00 00 00 00 00 	movl   $0x0,0x980(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2bfd:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    2c02:	49 81 c1 80 05 00 00 	add    $0x580,%r9
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2c09:	c7 82 00 09 00 00 02 00 00 00 	movl   $0x2,0x900(%rdx)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2c13:	48 89 82 24 0b 00 00 	mov    %rax,0xb24(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2c1a:	8b 45 00             	mov    0x0(%rbp),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2c1d:	48 89 aa 18 0b 00 00 	mov    %rbp,0xb18(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2c24:	89 82 20 0b 00 00    	mov    %eax,0xb20(%rdx)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2c2a:	c7 82 0c 0d 00 00 0c 00 00 00 	movl   $0xc,0xd0c(%rdx)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2c34:	c7 82 2c 0b 00 00 03 00 00 00 	movl   $0x3,0xb2c(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2c3e:	0f 11 a2 08 0b 00 00 	movups %xmm4,0xb08(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2c45:	41 83 ff 0f          	cmp    $0xf,%r15d
    2c49:	0f 85 71 fb ff ff    	jne    27c0 <main+0x1d0>
    2c4f:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    2c54:	ba 0d 00 00 00       	mov    $0xd,%edx
    2c59:	48 8d 35 b8 46 00 00 	lea    0x46b8(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2c60:	31 c0                	xor    %eax,%eax
    2c62:	bf 01 00 00 00       	mov    $0x1,%edi
    2c67:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    2c6c:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2c71:	e8 da f7 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c76:	be 08 00 00 00       	mov    $0x8,%esi
    2c7b:	bf 02 00 00 00       	mov    $0x2,%edi
    2c80:	e8 1b f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2c85:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c8a:	bf 0f 00 00 00       	mov    $0xf,%edi
    my_thread_data[0] = &thread_data[x]; 
    2c8f:	4d 8d ba 80 47 00 00 	lea    0x4780(%r10),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c96:	4d 8d b2 00 0b 00 00 	lea    0xb00(%r10),%r14
    thread_data[x].threads = my_thread_data;
    2c9d:	49 89 82 00 48 00 00 	mov    %rax,0x4800(%r10)
    my_thread_data[0] = &thread_data[x]; 
    2ca4:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2ca7:	49 8d 8a 80 10 00 00 	lea    0x1080(%r10),%rcx
    2cae:	49 8d 92 80 1b 00 00 	lea    0x1b80(%r10),%rdx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2cb5:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2cb9:	49 8b 82 98 00 00 00 	mov    0x98(%r10),%rax
    2cc0:	4d 8d 9a 80 26 00 00 	lea    0x2680(%r10),%r11
    2cc7:	4d 8d 82 00 2c 00 00 	lea    0x2c00(%r10),%r8
    2cce:	49 8d b2 00 16 00 00 	lea    0x1600(%r10),%rsi
    2cd5:	49 8d 9a 00 21 00 00 	lea    0x2100(%r10),%rbx
    thread_data[x].thread_count = 2;
    2cdc:	41 c7 82 08 48 00 00 02 00 00 00 	movl   $0x2,0x4808(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2ce7:	48 89 4c 24 58       	mov    %rcx,0x58(%rsp)
    2cec:	4d 8d 8a 80 31 00 00 	lea    0x3180(%r10),%r9
    2cf3:	4d 8d a2 00 37 00 00 	lea    0x3700(%r10),%r12
    2cfa:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    2cff:	4d 8d aa 80 3c 00 00 	lea    0x3c80(%r10),%r13
    thread_data[x].thread_index = 0;
    2d06:	41 c7 82 80 47 00 00 00 00 00 00 	movl   $0x0,0x4780(%r10)
    thread_data[x].task_count = total_barrier_count;
    2d11:	41 c7 82 20 48 00 00 03 00 00 00 	movl   $0x3,0x4820(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2d1c:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2d26:	49 8d 82 80 05 00 00 	lea    0x580(%r10),%rax
    2d2d:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2d32:	49 8b 82 18 06 00 00 	mov    0x618(%r10),%rax
    2d39:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    2d3e:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2d48:	49 8b 82 98 0b 00 00 	mov    0xb98(%r10),%rax
    2d4f:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    2d54:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2d5e:	49 8b 82 18 11 00 00 	mov    0x1118(%r10),%rax
    my_thread_data[0] = &thread_data[x]; 
    2d65:	4c 89 7c 24 70       	mov    %r15,0x70(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d6a:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2d74:	49 8b 82 98 16 00 00 	mov    0x1698(%r10),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2d7b:	4c 89 74 24 78       	mov    %r14,0x78(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d80:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2d8a:	49 8b 82 18 1c 00 00 	mov    0x1c18(%r10),%rax
    2d91:	48 89 74 24 50       	mov    %rsi,0x50(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d96:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2d9b:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2da5:	49 8b 82 98 21 00 00 	mov    0x2198(%r10),%rax
    2dac:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    2db1:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2dbb:	49 8b 82 18 27 00 00 	mov    0x2718(%r10),%rax
    2dc2:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2dcc:	49 8b 82 98 2c 00 00 	mov    0x2c98(%r10),%rax
    2dd3:	4c 89 4c 24 30       	mov    %r9,0x30(%rsp)
    2dd8:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2de2:	49 8b 82 18 32 00 00 	mov    0x3218(%r10),%rax
    2de9:	4c 89 94 24 80 00 00 00 	mov    %r10,0x80(%rsp)
    2df1:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2dfb:	49 8b 82 98 37 00 00 	mov    0x3798(%r10),%rax
    2e02:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    2e07:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
    2e11:	49 8b 82 18 3d 00 00 	mov    0x3d18(%r10),%rax
    2e18:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    2e1d:	c7 80 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e27:	e8 74 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e2c:	be 38 00 00 00       	mov    $0x38,%esi
    2e31:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e36:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e39:	e8 62 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e3e:	be 38 00 00 00       	mov    $0x38,%esi
    2e43:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e48:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e4b:	e8 50 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e50:	be 38 00 00 00       	mov    $0x38,%esi
    2e55:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e5a:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e62:	e8 39 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e67:	be 08 00 00 00       	mov    $0x8,%esi
    2e6c:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e71:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e79:	e8 22 f5 ff ff       	call   23a0 <calloc@plt>
  thread_data[thread_count].type = TIMER;
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2e7e:	be 08 00 00 00       	mov    $0x8,%esi
    2e83:	bf 0f 00 00 00       	mov    $0xf,%edi
  thread_data[thread_count].type = TIMER;
    2e88:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e90:	49 89 c5             	mov    %rax,%r13
  thread_data[thread_count].task_count = total_barrier_count;
    2e93:	48 8b 05 ae 4b 00 00 	mov    0x4bae(%rip),%rax        # 7a48 <_IO_stdin_used+0xa48>
  thread_data[thread_count].type = TIMER;
    2e9a:	41 c7 82 08 42 00 00 00 00 00 00 	movl   $0x0,0x4208(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2ea5:	49 89 82 a0 42 00 00 	mov    %rax,0x42a0(%r10)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2eac:	e8 ef f4 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2eb1:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    2eb6:	48 8b 4c 24 58       	mov    0x58(%rsp),%rcx
    2ebb:	48 8b 74 24 50       	mov    0x50(%rsp),%rsi
    2ec0:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    2ec5:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2ec9:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    2ece:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    2ed3:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2ed7:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    2edc:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
    2ee4:	48 89 48 18          	mov    %rcx,0x18(%rax)
    2ee8:	4c 8b 4c 24 30       	mov    0x30(%rsp),%r9
    2eed:	48 89 70 20          	mov    %rsi,0x20(%rax)
    2ef1:	48 8d 35 2f 44 00 00 	lea    0x442f(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2ef8:	48 89 78 30          	mov    %rdi,0x30(%rax)
    2efc:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    2f01:	4d 8d b2 00 42 00 00 	lea    0x4200(%r10),%r14
    2f08:	4c 89 10             	mov    %r10,(%rax)
    2f0b:	48 89 78 50          	mov    %rdi,0x50(%rax)
    2f0f:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    2f14:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2f18:	ba 0c 00 00 00       	mov    $0xc,%edx
    2f1d:	48 89 78 58          	mov    %rdi,0x58(%rax)
    2f21:	49 8d ba 00 4d 00 00 	lea    0x4d00(%r10),%rdi
    2f28:	4c 89 58 38          	mov    %r11,0x38(%rax)
    2f2c:	4c 89 40 40          	mov    %r8,0x40(%rax)
    2f30:	4c 89 48 48          	mov    %r9,0x48(%rax)
    2f34:	4c 89 70 60          	mov    %r14,0x60(%rax)
    2f38:	4c 89 78 68          	mov    %r15,0x68(%rax)
    2f3c:	4c 8d 3d fd 09 00 00 	lea    0x9fd(%rip),%r15        # 3940 <barriered_thread>
    2f43:	48 89 78 70          	mov    %rdi,0x70(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2f47:	49 89 82 80 42 00 00 	mov    %rax,0x4280(%r10)
    2f4e:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2f50:	41 c7 82 88 42 00 00 0c 00 00 00 	movl   $0xc,0x4288(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2f5b:	41 c7 82 90 42 00 00 02 00 00 00 	movl   $0x2,0x4290(%r10)
  thread_data[thread_count].thread_index = 0;
    2f66:	41 c7 82 00 42 00 00 00 00 00 00 	movl   $0x0,0x4200(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2f71:	48 89 bc 24 80 00 00 00 	mov    %rdi,0x80(%rsp)
    2f79:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].thread_index = 0;
    2f7e:	4c 89 94 24 98 00 00 00 	mov    %r10,0x98(%rsp)
    2f86:	e8 c5 f4 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2f8b:	48 8d b3 a0 02 00 00 	lea    0x2a0(%rbx),%rsi
    2f92:	49 8d 7d 60          	lea    0x60(%r13),%rdi
    2f96:	4c 89 f1             	mov    %r14,%rcx
    2f99:	48 8d 15 80 0d 00 00 	lea    0xd80(%rip),%rdx        # 3d20 <timer_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    2fa0:	45 31 f6             	xor    %r14d,%r14d
    2fa3:	4c 89 eb             	mov    %r13,%rbx
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2fa6:	e8 c5 f4 ff ff       	call   2470 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2fab:	44 89 f0             	mov    %r14d,%eax
    2fae:	4d 89 ee             	mov    %r13,%r14
    2fb1:	41 89 c5             	mov    %eax,%r13d
    thread_data[x].type = WORKER;
    2fb4:	c7 45 08 01 00 00 00 	movl   $0x1,0x8(%rbp)
    2fbb:	44 89 ea             	mov    %r13d,%edx
    2fbe:	bf 01 00 00 00       	mov    $0x1,%edi
    2fc3:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2fc5:	c7 85 a4 00 00 00 01 00 00 00 	movl   $0x1,0xa4(%rbp)
    2fcf:	48 8d 35 32 46 00 00 	lea    0x4632(%rip),%rsi        # 7608 <_IO_stdin_used+0x608>
  for (int x = 0 ; x < thread_count ; x++) {
    2fd6:	41 83 c5 01          	add    $0x1,%r13d
    2fda:	e8 71 f4 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2fdf:	48 89 e9             	mov    %rbp,%rcx
    2fe2:	4c 89 e6             	mov    %r12,%rsi
    2fe5:	48 89 df             	mov    %rbx,%rdi
    2fe8:	4c 89 fa             	mov    %r15,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2feb:	48 81 c5 80 05 00 00 	add    $0x580,%rbp
    2ff2:	48 83 c3 08          	add    $0x8,%rbx
    2ff6:	49 83 c4 38          	add    $0x38,%r12
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2ffa:	e8 71 f4 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2fff:	48 8b 55 88          	mov    -0x78(%rbp),%rdx
    3003:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    3007:	be 08 00 00 00       	mov    $0x8,%esi
    300c:	e8 cf f2 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    3011:	41 83 fd 0c          	cmp    $0xc,%r13d
    3015:	75 9d                	jne    2fb4 <main+0x9c4>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    3017:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    301f:	48 8b 1d 2a 4a 00 00 	mov    0x4a2a(%rip),%rbx        # 7a50 <_IO_stdin_used+0xa50>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3026:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    302b:	4d 89 f5             	mov    %r14,%r13
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    302e:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3033:	49 89 9a 20 48 00 00 	mov    %rbx,0x4820(%r10)
    thread_data[x].type = IO;
    303a:	41 c7 82 88 47 00 00 02 00 00 00 	movl   $0x2,0x4788(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3045:	e8 56 f3 ff ff       	call   23a0 <calloc@plt>
    304a:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3052:	be 00 08 00 00       	mov    $0x800,%esi
    3057:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3059:	49 89 82 08 49 00 00 	mov    %rax,0x4908(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3060:	e8 4b f4 ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3065:	be 08 00 00 00       	mov    $0x8,%esi
    306a:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    306f:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    3077:	41 89 82 10 49 00 00 	mov    %eax,0x4910(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    307e:	e8 1d f3 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3083:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    3088:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    308d:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    3095:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    309a:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    309f:	4c 8b 74 24 78       	mov    0x78(%rsp),%r14
    30a4:	4c 89 58 48          	mov    %r11,0x48(%rax)
    30a8:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    30ad:	4c 8b 7c 24 60       	mov    0x60(%rsp),%r15
    30b2:	4c 89 40 50          	mov    %r8,0x50(%rax)
    30b6:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    30bb:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    30c0:	4c 89 48 58          	mov    %r9,0x58(%rax)
    30c4:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    30c9:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    30ce:	4c 89 10             	mov    %r10,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    30d1:	49 89 82 00 48 00 00 	mov    %rax,0x4800(%r10)
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    30d8:	41 c7 82 08 48 00 00 0c 00 00 00 	movl   $0xc,0x4808(%r10)
    thread_data[x].thread_index = x;
    30e3:	41 c7 82 80 47 00 00 0d 00 00 00 	movl   $0xd,0x4780(%r10)
      my_thread_data[n] = &thread_data[n]; 
    30ee:	4c 89 70 10          	mov    %r14,0x10(%rax)
    30f2:	48 89 68 18          	mov    %rbp,0x18(%rax)
    30f6:	4c 89 60 20          	mov    %r12,0x20(%rax)
    30fa:	48 89 78 28          	mov    %rdi,0x28(%rax)
    30fe:	bf 01 00 00 00       	mov    $0x1,%edi
    3103:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3107:	48 89 70 38          	mov    %rsi,0x38(%rax)
    310b:	48 8d 35 33 42 00 00 	lea    0x4233(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    3112:	48 89 50 40          	mov    %rdx,0x40(%rax)
    3116:	ba 0d 00 00 00       	mov    $0xd,%edx
    311b:	4c 89 78 08          	mov    %r15,0x8(%rax)
    311f:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3121:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    3126:	e8 25 f3 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    312b:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    3130:	49 8d 7d 68          	lea    0x68(%r13),%rdi
    3134:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    313c:	48 8d 15 0d 1f 00 00 	lea    0x1f0d(%rip),%rdx        # 5050 <io_thread>
    3143:	48 05 d8 02 00 00    	add    $0x2d8,%rax
    3149:	48 89 c6             	mov    %rax,%rsi
    314c:	e8 1f f3 ff ff       	call   2470 <pthread_create@plt>
    3151:	ba 0e 00 00 00       	mov    $0xe,%edx
    3156:	48 8d 35 ff 41 00 00 	lea    0x41ff(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    315d:	31 c0                	xor    %eax,%eax
    315f:	bf 01 00 00 00       	mov    $0x1,%edi
    3164:	e8 e7 f2 ff ff       	call   2450 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    3169:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    316e:	48 8b 44 24 48       	mov    0x48(%rsp),%rax

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3173:	be 08 00 00 00       	mov    $0x8,%esi
    3178:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x].task_count = 0;
    317d:	49 89 9a a0 4d 00 00 	mov    %rbx,0x4da0(%r10)
    3184:	31 db                	xor    %ebx,%ebx
    thread_data[x].type = EXTERNAL;
    3186:	41 c7 82 08 4d 00 00 03 00 00 00 	movl   $0x3,0x4d08(%r10)
    thread_data[x].buffers = &buffers[buffer_index];
    3191:	49 89 82 80 4e 00 00 	mov    %rax,0x4e80(%r10)
    3198:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    319d:	e8 fe f1 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    31a2:	4c 8b 54 24 48       	mov    0x48(%rsp),%r10
    31a7:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    31ac:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    31b1:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    31b6:	4c 89 70 10          	mov    %r14,0x10(%rax)
    31ba:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    31bf:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    31c4:	4c 89 10             	mov    %r10,(%rax)
    31c7:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    31cc:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    31d1:	48 89 68 18          	mov    %rbp,0x18(%rax)
    31d5:	48 8d 2d bb 41 00 00 	lea    0x41bb(%rip),%rbp        # 7397 <_IO_stdin_used+0x397>
    31dc:	4c 89 60 20          	mov    %r12,0x20(%rax)
    31e0:	4c 8d a4 24 a0 00 00 00 	lea    0xa0(%rsp),%r12
    31e8:	48 89 78 28          	mov    %rdi,0x28(%rax)
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31ec:	49 8d 7d 70          	lea    0x70(%r13),%rdi
      my_thread_data[n] = &thread_data[n]; 
    31f0:	48 89 48 30          	mov    %rcx,0x30(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31f4:	48 8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%rcx
      my_thread_data[n] = &thread_data[n]; 
    31fc:	48 89 70 38          	mov    %rsi,0x38(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3200:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3208:	48 89 50 40          	mov    %rdx,0x40(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    320c:	48 8d 15 3d 0a 00 00 	lea    0xa3d(%rip),%rdx        # 3c50 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    3213:	4c 89 58 48          	mov    %r11,0x48(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3217:	48 81 c6 10 03 00 00 	add    $0x310,%rsi
      my_thread_data[n] = &thread_data[n]; 
    321e:	4c 89 40 50          	mov    %r8,0x50(%rax)
    3222:	4c 89 48 58          	mov    %r9,0x58(%rax)
    thread_data[x].threads = my_thread_data;
    3226:	49 89 82 80 4d 00 00 	mov    %rax,0x4d80(%r10)
      my_thread_data[n] = &thread_data[n]; 
    322d:	4c 89 78 08          	mov    %r15,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3231:	48 8b 05 20 48 00 00 	mov    0x4820(%rip),%rax        # 7a58 <_IO_stdin_used+0xa58>
    thread_data[x].thread_index = x;
    3238:	41 c7 82 00 4d 00 00 0e 00 00 00 	movl   $0xe,0x4d00(%r10)
    thread_data[x].thread_count = thread_count;
    3243:	49 89 82 88 4d 00 00 	mov    %rax,0x4d88(%r10)
    thread_data[x].thread_index = x;
    324a:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    324f:	e8 1c f2 ff ff       	call   2470 <pthread_create@plt>
    3254:	48 8d 3d 1e 41 00 00 	lea    0x411e(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    325b:	e8 90 f0 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3260:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    3265:	0f 1f 00             	nopl   (%rax)
    void * result; 
    pthread_join(thread[x], &result);
    3268:	49 8b 7c dd 00       	mov    0x0(%r13,%rbx,8),%rdi
    326d:	4c 89 e6             	mov    %r12,%rsi
    3270:	e8 7b f2 ff ff       	call   24f0 <pthread_join@plt>
    3275:	89 da                	mov    %ebx,%edx
    3277:	48 89 ee             	mov    %rbp,%rsi
    327a:	bf 01 00 00 00       	mov    $0x1,%edi
    327f:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3281:	48 83 c3 01          	add    $0x1,%rbx
    3285:	e8 c6 f1 ff ff       	call   2450 <__printf_chk@plt>
    328a:	48 83 fb 0f          	cmp    $0xf,%rbx
    328e:	75 d8                	jne    3268 <main+0xc78>
    3290:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    3295:	4d 89 f2             	mov    %r14,%r10
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    3298:	31 db                	xor    %ebx,%ebx
  long sents = 0;
    329a:	31 ed                	xor    %ebp,%ebp
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    329c:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    32a1:	4d 8d ae 98 00 00 00 	lea    0x98(%r14),%r13
  long total = 0;
    32a8:	45 31 f6             	xor    %r14d,%r14d
  long ingests = 0;
    32ab:	45 31 c9             	xor    %r9d,%r9d
    32ae:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32b3:	4d 89 ef             	mov    %r13,%r15
    32b6:	4d 89 f5             	mov    %r14,%r13
  for (int x = 0 ; x < thread_count ; x++) {
    32b9:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    if (x % 2 == 1) {
    32c1:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    32c5:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    32ca:	89 f8                	mov    %edi,%eax
    32cc:	41 89 fc             	mov    %edi,%r12d
      other = (x + 1) % total_threads;
    32cf:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
    32d2:	83 e0 01             	and    $0x1,%eax
      other = abs(x - 1) % total_threads;
    32d5:	41 83 ec 01          	sub    $0x1,%r12d
      other = (x + 1) % total_threads;
    32d9:	89 7c 24 10          	mov    %edi,0x10(%rsp)
      other = abs(x - 1) % total_threads;
    32dd:	85 c0                	test   %eax,%eax
    32df:	44 0f 44 e7          	cmove  %edi,%r12d
    32e3:	bf 0a 00 00 00       	mov    $0xa,%edi
    32e8:	e8 e3 ef ff ff       	call   22d0 <putchar@plt>
    32ed:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    32f2:	bf 01 00 00 00       	mov    $0x1,%edi
    32f7:	48 8d 35 ad 40 00 00 	lea    0x40ad(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    32fe:	48 8b 10             	mov    (%rax),%rdx
    3301:	31 c0                	xor    %eax,%eax
    3303:	e8 48 f1 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3308:	49 63 57 08          	movslq 0x8(%r15),%rdx
    330c:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3311:	85 d2                	test   %edx,%edx
    3313:	0f 8e 40 04 00 00    	jle    3759 <main+0x1169>
    3319:	49 8b 07             	mov    (%r15),%rax
    331c:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
    long v = 0;
    3320:	31 d2                	xor    %edx,%edx
    3322:	48 c1 e6 07          	shl    $0x7,%rsi
    3326:	48 05 00 02 00 00    	add    $0x200,%rax
    332c:	48 01 c6             	add    %rax,%rsi
    332f:	90                   	nop
      v += thread_data[me].tasks[n].v;
    3330:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3333:	48 05 80 04 00 00    	add    $0x480,%rax
    3339:	48 39 f0             	cmp    %rsi,%rax
    333c:	75 f2                	jne    3330 <main+0xd40>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    333e:	4d 63 e4             	movslq %r12d,%r12
    3341:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3346:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    334a:	49 8d 04 44          	lea    (%r12,%rax,2),%rax
    334e:	48 c1 e0 07          	shl    $0x7,%rax
    3352:	48 01 f8             	add    %rdi,%rax
    3355:	48 63 b0 a0 00 00 00 	movslq 0xa0(%rax),%rsi
    335c:	85 f6                	test   %esi,%esi
    335e:	7e 2e                	jle    338e <main+0xd9e>
      v += thread_data[other].tasks[n].v;
    3360:	48 8b 80 98 00 00 00 	mov    0x98(%rax),%rax
    3367:	48 8d 34 f6          	lea    (%rsi,%rsi,8),%rsi
    336b:	48 c1 e6 07          	shl    $0x7,%rsi
    336f:	48 05 00 02 00 00    	add    $0x200,%rax
    3375:	48 01 c6             	add    %rax,%rsi
    3378:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3380:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3383:	48 05 80 04 00 00    	add    $0x480,%rax
    3389:	48 39 f0             	cmp    %rsi,%rax
    338c:	75 f2                	jne    3380 <main+0xd90>
    338e:	48 8d 35 2b 40 00 00 	lea    0x402b(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    3395:	bf 01 00 00 00       	mov    $0x1,%edi
    339a:	31 c0                	xor    %eax,%eax
    339c:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    33a1:	e8 aa f0 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    33a6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    33ab:	bf 01 00 00 00       	mov    $0x1,%edi
    33b0:	48 8b 30             	mov    (%rax),%rsi
    33b3:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    33bd:	48 f7 ee             	imul   %rsi
    33c0:	48 c1 fe 3f          	sar    $0x3f,%rsi
    33c4:	31 c0                	xor    %eax,%eax
    33c6:	48 d1 fa             	sar    %rdx
    33c9:	48 29 f2             	sub    %rsi,%rdx
    33cc:	48 8d 35 5d 42 00 00 	lea    0x425d(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    33d3:	e8 78 f0 ff ff       	call   2450 <__printf_chk@plt>
    33d8:	bf 0a 00 00 00       	mov    $0xa,%edi
    33dd:	e8 ee ee ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    33e2:	49 63 47 08          	movslq 0x8(%r15),%rax
    33e6:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    33eb:	85 c0                	test   %eax,%eax
    33ed:	0f 8e ed 00 00 00    	jle    34e0 <main+0xef0>
    33f3:	49 8b 3f             	mov    (%r15),%rdi
    33f6:	48 8d 34 c0          	lea    (%rax,%rax,8),%rsi
    33fa:	48 c1 e6 07          	shl    $0x7,%rsi
    33fe:	48 8d 97 80 01 00 00 	lea    0x180(%rdi),%rdx
    3405:	48 01 d6             	add    %rdx,%rsi
    3408:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3410:	48 8b 82 08 02 00 00 	mov    0x208(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    3417:	4c 03 2a             	add    (%rdx),%r13
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    341a:	48 81 c2 80 04 00 00 	add    $0x480,%rdx
      ingests += thread_data[x].tasks[n].ingest_count;
    3421:	4c 03 b2 80 fd ff ff 	add    -0x280(%rdx),%r14
      sends += thread_data[x].tasks[n].sends;
    3428:	4c 03 8a 00 fe ff ff 	add    -0x200(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    342f:	48 03 a8 00 01 00 00 	add    0x100(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3436:	48 03 98 80 01 00 00 	add    0x180(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    343d:	48 03 a8 00 03 00 00 	add    0x300(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3444:	48 03 98 80 03 00 00 	add    0x380(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    344b:	48 03 a8 00 05 00 00 	add    0x500(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3452:	48 03 98 80 05 00 00 	add    0x580(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3459:	48 03 a8 00 07 00 00 	add    0x700(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3460:	48 03 98 80 07 00 00 	add    0x780(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3467:	48 03 a8 00 09 00 00 	add    0x900(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    346e:	48 03 98 80 09 00 00 	add    0x980(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3475:	48 03 a8 00 0b 00 00 	add    0xb00(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    347c:	48 03 98 80 0b 00 00 	add    0xb80(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3483:	48 03 a8 00 0d 00 00 	add    0xd00(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    348a:	48 03 98 80 0d 00 00 	add    0xd80(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3491:	48 03 a8 00 0f 00 00 	add    0xf00(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3498:	48 03 98 80 0f 00 00 	add    0xf80(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    349f:	48 03 a8 00 11 00 00 	add    0x1100(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    34a6:	48 03 98 80 11 00 00 	add    0x1180(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    34ad:	48 03 a8 00 13 00 00 	add    0x1300(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    34b4:	48 03 98 80 13 00 00 	add    0x1380(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    34bb:	48 03 a8 00 15 00 00 	add    0x1500(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    34c2:	48 03 98 80 15 00 00 	add    0x1580(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    34c9:	48 03 a8 00 17 00 00 	add    0x1700(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    34d0:	48 03 98 80 17 00 00 	add    0x1780(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    34d7:	48 39 f2             	cmp    %rsi,%rdx
    34da:	0f 85 30 ff ff ff    	jne    3410 <main+0xe20>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    34e0:	45 31 e4             	xor    %r12d,%r12d
    34e3:	49 83 bf f0 03 00 00 00 	cmpq   $0x0,0x3f0(%r15)
    34eb:	0f 8e 83 00 00 00    	jle    3574 <main+0xf84>
    34f1:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    34f6:	4c 89 fb             	mov    %r15,%rbx
    34f9:	4d 89 e7             	mov    %r12,%r15
    34fc:	4d 89 cc             	mov    %r9,%r12
    34ff:	90                   	nop
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3500:	4c 89 f9             	mov    %r15,%rcx
    3503:	48 83 ec 08          	sub    $0x8,%rsp
    3507:	bf 01 00 00 00       	mov    $0x1,%edi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    350c:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3516:	48 c1 e1 08          	shl    $0x8,%rcx
    351a:	48 03 8b 68 03 00 00 	add    0x368(%rbx),%rcx
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3521:	49 83 c7 01          	add    $0x1,%r15
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3525:	48 8b b1 88 00 00 00 	mov    0x88(%rcx),%rsi
    352c:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3530:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3533:	4c 8b 81 80 00 00 00 	mov    0x80(%rcx),%r8
    353a:	4c 2b 01             	sub    (%rcx),%r8
    353d:	31 c0                	xor    %eax,%eax
    353f:	8b 89 90 00 00 00    	mov    0x90(%rcx),%ecx
    3545:	56                   	push   %rsi
    3546:	48 8d 35 03 41 00 00 	lea    0x4103(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    354d:	48 c1 ea 12          	shr    $0x12,%rdx
    3551:	49 89 d1             	mov    %rdx,%r9
    3554:	ba 02 00 00 00       	mov    $0x2,%edx
    3559:	e8 f2 ee ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    355e:	58                   	pop    %rax
    355f:	5a                   	pop    %rdx
    3560:	4c 39 bb f0 03 00 00 	cmp    %r15,0x3f0(%rbx)
    3567:	7f 97                	jg     3500 <main+0xf10>
    3569:	49 89 df             	mov    %rbx,%r15
    356c:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    3571:	4d 89 e1             	mov    %r12,%r9
  for (int x = 0 ; x < thread_count ; x++) {
    3574:	48 81 44 24 08 80 01 00 00 	addq   $0x180,0x8(%rsp)
    357d:	49 81 c7 80 05 00 00 	add    $0x580,%r15
    3584:	83 7c 24 10 0c       	cmpl   $0xc,0x10(%rsp)
    3589:	0f 85 32 fd ff ff    	jne    32c1 <main+0xcd1>
    358f:	4c 89 ea             	mov    %r13,%rdx
    3592:	48 8d 35 34 3e 00 00 	lea    0x3e34(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    3599:	31 c0                	xor    %eax,%eax
    359b:	4d 89 cf             	mov    %r9,%r15
    359e:	bf 01 00 00 00       	mov    $0x1,%edi
    35a3:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    35a8:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    35b2:	e8 99 ee ff ff       	call   2450 <__printf_chk@plt>
    35b7:	bf 0a 00 00 00       	mov    $0xa,%edi
    35bc:	e8 0f ed ff ff       	call   22d0 <putchar@plt>
    35c1:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    35c6:	bf 01 00 00 00       	mov    $0x1,%edi
    35cb:	48 8d 35 ce 40 00 00 	lea    0x40ce(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    35d2:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    35d9:	31 c0                	xor    %eax,%eax
    35db:	e8 70 ee ff ff       	call   2450 <__printf_chk@plt>
    35e0:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    35e5:	bf 01 00 00 00       	mov    $0x1,%edi
    35ea:	48 8d 35 d7 40 00 00 	lea    0x40d7(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    35f1:	4c 89 c8             	mov    %r9,%rax
    35f4:	49 c1 f9 3f          	sar    $0x3f,%r9
    35f8:	49 f7 ec             	imul   %r12
    35fb:	31 c0                	xor    %eax,%eax
    35fd:	48 d1 fa             	sar    %rdx
    3600:	4c 29 ca             	sub    %r9,%rdx
    3603:	e8 48 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3608:	4c 89 f8             	mov    %r15,%rax
    360b:	4d 89 fb             	mov    %r15,%r11
    360e:	bf 01 00 00 00       	mov    $0x1,%edi
    3613:	49 f7 ec             	imul   %r12
    3616:	49 c1 fb 3f          	sar    $0x3f,%r11
    361a:	48 8d 35 d7 40 00 00 	lea    0x40d7(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    3621:	31 c0                	xor    %eax,%eax
    3623:	48 d1 fa             	sar    %rdx
    3626:	4c 29 da             	sub    %r11,%rdx
    3629:	e8 22 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    362e:	4c 89 e8             	mov    %r13,%rax
    3631:	4c 89 e9             	mov    %r13,%rcx
    3634:	bf 01 00 00 00       	mov    $0x1,%edi
    3639:	49 f7 ec             	imul   %r12
    363c:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3640:	48 8d 35 e1 40 00 00 	lea    0x40e1(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    3647:	31 c0                	xor    %eax,%eax
    3649:	48 d1 fa             	sar    %rdx
    364c:	48 29 ca             	sub    %rcx,%rdx
    364f:	e8 fc ed ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3654:	48 89 e8             	mov    %rbp,%rax
    3657:	48 c1 fd 3f          	sar    $0x3f,%rbp
    365b:	48 8d 35 7f 3d 00 00 	lea    0x3d7f(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    3662:	49 f7 ec             	imul   %r12
    3665:	bf 01 00 00 00       	mov    $0x1,%edi
    366a:	31 c0                	xor    %eax,%eax
    366c:	48 d1 fa             	sar    %rdx
    366f:	48 29 ea             	sub    %rbp,%rdx
    3672:	e8 d9 ed ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3677:	48 89 d8             	mov    %rbx,%rax
    367a:	48 c1 fb 3f          	sar    $0x3f,%rbx
    367e:	48 8d 35 6d 3d 00 00 	lea    0x3d6d(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    3685:	49 f7 ec             	imul   %r12
    3688:	bf 01 00 00 00       	mov    $0x1,%edi
    368d:	48 d1 fa             	sar    %rdx
    3690:	48 29 da             	sub    %rbx,%rdx
    3693:	31 c0                	xor    %eax,%eax
    3695:	e8 b6 ed ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    369a:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    36a2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    36ab:	0f 85 af 00 00 00    	jne    3760 <main+0x1170>
    36b1:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    36b8:	31 c0                	xor    %eax,%eax
    36ba:	5b                   	pop    %rbx
    36bb:	5d                   	pop    %rbp
    36bc:	41 5c                	pop    %r12
    36be:	41 5d                	pop    %r13
    36c0:	41 5e                	pop    %r14
    36c2:	41 5f                	pop    %r15
    36c4:	c3                   	ret
          thread_data[x].tasks[y].run = barriered_work; 
    36c5:	48 8d 05 84 23 00 00 	lea    0x2384(%rip),%rax        # 5a50 <barriered_work>
    36cc:	bb 02 00 00 00       	mov    $0x2,%ebx
    36d1:	49 89 85 08 02 00 00 	mov    %rax,0x208(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    36d8:	e9 a5 f2 ff ff       	jmp    2982 <main+0x392>
      other = (x + 1) % total_threads;
    36dd:	b8 89 88 88 88       	mov    $0x88888889,%eax
    36e2:	45 89 fe             	mov    %r15d,%r14d
      my_thread_data[0] = &thread_data[x]; 
    36e5:	4d 89 4d 00          	mov    %r9,0x0(%r13)
    36e9:	4c 89 c9             	mov    %r9,%rcx
      other = (x + 1) % total_threads;
    36ec:	4c 0f af f0          	imul   %rax,%r14
    36f0:	bf 01 00 00 00       	mov    $0x1,%edi
    36f5:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    36fa:	48 8d 35 08 3c 00 00 	lea    0x3c08(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      thread_data[x].thread_index = 0;
    3701:	41 c7 01 00 00 00 00 	movl   $0x0,(%r9)
      other = (x + 1) % total_threads;
    3708:	49 c1 ee 23          	shr    $0x23,%r14
    370c:	44 89 f0             	mov    %r14d,%eax
    370f:	c1 e0 04             	shl    $0x4,%eax
    3712:	44 29 f0             	sub    %r14d,%eax
    3715:	45 89 fe             	mov    %r15d,%r14d
    3718:	41 29 c6             	sub    %eax,%r14d
      my_thread_data[1] = &thread_data[other]; 
    371b:	49 63 c6             	movslq %r14d,%rax
    371e:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3722:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    3726:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    372b:	89 ea                	mov    %ebp,%edx
    372d:	49 c1 e0 07          	shl    $0x7,%r8
    3731:	49 01 c0             	add    %rax,%r8
    3734:	31 c0                	xor    %eax,%eax
    3736:	4d 89 45 08          	mov    %r8,0x8(%r13)
    373a:	e8 11 ed ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    373f:	49 8d 84 24 80 01 00 00 	lea    0x180(%r12),%rax
    3747:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    374c:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    3751:	49 89 c4             	mov    %rax,%r12
    3754:	e9 ee f0 ff ff       	jmp    2847 <main+0x257>
    long v = 0;
    3759:	31 d2                	xor    %edx,%edx
    375b:	e9 de fb ff ff       	jmp    333e <main+0xd4e>
}
    3760:	e8 cb eb ff ff       	call   2330 <__stack_chk_fail@plt>
    3765:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    376f:	90                   	nop

0000000000003770 <_start>:
    3770:	f3 0f 1e fa          	endbr64
    3774:	31 ed                	xor    %ebp,%ebp
    3776:	49 89 d1             	mov    %rdx,%r9
    3779:	5e                   	pop    %rsi
    377a:	48 89 e2             	mov    %rsp,%rdx
    377d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3781:	50                   	push   %rax
    3782:	54                   	push   %rsp
    3783:	45 31 c0             	xor    %r8d,%r8d
    3786:	31 c9                	xor    %ecx,%ecx
    3788:	48 8d 3d 61 ee ff ff 	lea    -0x119f(%rip),%rdi        # 25f0 <main>
    378f:	ff 15 43 68 00 00    	call   *0x6843(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3795:	f4                   	hlt
    3796:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000037a0 <deregister_tm_clones>:
    37a0:	48 8d 3d 79 68 00 00 	lea    0x6879(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    37a7:	48 8d 05 72 68 00 00 	lea    0x6872(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    37ae:	48 39 f8             	cmp    %rdi,%rax
    37b1:	74 15                	je     37c8 <deregister_tm_clones+0x28>
    37b3:	48 8b 05 26 68 00 00 	mov    0x6826(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    37ba:	48 85 c0             	test   %rax,%rax
    37bd:	74 09                	je     37c8 <deregister_tm_clones+0x28>
    37bf:	ff e0                	jmp    *%rax
    37c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    37c8:	c3                   	ret
    37c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037d0 <register_tm_clones>:
    37d0:	48 8d 3d 49 68 00 00 	lea    0x6849(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    37d7:	48 8d 35 42 68 00 00 	lea    0x6842(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    37de:	48 29 fe             	sub    %rdi,%rsi
    37e1:	48 89 f0             	mov    %rsi,%rax
    37e4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    37e8:	48 c1 f8 03          	sar    $0x3,%rax
    37ec:	48 01 c6             	add    %rax,%rsi
    37ef:	48 d1 fe             	sar    %rsi
    37f2:	74 14                	je     3808 <register_tm_clones+0x38>
    37f4:	48 8b 05 f5 67 00 00 	mov    0x67f5(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    37fb:	48 85 c0             	test   %rax,%rax
    37fe:	74 08                	je     3808 <register_tm_clones+0x38>
    3800:	ff e0                	jmp    *%rax
    3802:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3808:	c3                   	ret
    3809:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003810 <__do_global_dtors_aux>:
    3810:	f3 0f 1e fa          	endbr64
    3814:	80 3d 0d 68 00 00 00 	cmpb   $0x0,0x680d(%rip)        # a028 <completed.0>
    381b:	75 2b                	jne    3848 <__do_global_dtors_aux+0x38>
    381d:	55                   	push   %rbp
    381e:	48 83 3d d2 67 00 00 00 	cmpq   $0x0,0x67d2(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3826:	48 89 e5             	mov    %rsp,%rbp
    3829:	74 0c                	je     3837 <__do_global_dtors_aux+0x27>
    382b:	48 8b 3d d6 67 00 00 	mov    0x67d6(%rip),%rdi        # a008 <__dso_handle>
    3832:	e8 79 ea ff ff       	call   22b0 <__cxa_finalize@plt>
    3837:	e8 64 ff ff ff       	call   37a0 <deregister_tm_clones>
    383c:	c6 05 e5 67 00 00 01 	movb   $0x1,0x67e5(%rip)        # a028 <completed.0>
    3843:	5d                   	pop    %rbp
    3844:	c3                   	ret
    3845:	0f 1f 00             	nopl   (%rax)
    3848:	c3                   	ret
    3849:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003850 <frame_dummy>:
    3850:	f3 0f 1e fa          	endbr64
    3854:	e9 77 ff ff ff       	jmp    37d0 <register_tm_clones>
    3859:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003860 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3860:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3864:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    386b:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
  data->v++; // thread local
    3872:	48 83 87 00 02 00 00 01 	addq   $0x1,0x200(%rdi)
  if (protected->balance > 0) {
    387a:	48 8b 88 80 00 00 00 	mov    0x80(%rax),%rcx
  protected->protected++; // shared between all threads
    3881:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3885:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    388c:	48 85 c9             	test   %rcx,%rcx
    388f:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3896:	48 0f 4f d6          	cmovg  %rsi,%rdx
    389a:	48 89 90 80 00 00 00 	mov    %rdx,0x80(%rax)
}
    38a1:	31 c0                	xor    %eax,%eax
    38a3:	c3                   	ret
    38a4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    38af:	90                   	nop

00000000000038b0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    38b0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    38b4:	48 63 8f 2c 02 00 00 	movslq 0x22c(%rdi),%rcx
    38bb:	85 c9                	test   %ecx,%ecx
    38bd:	7e 6c                	jle    392b <barriered_reset+0x7b>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    38bf:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    38c6:	48 63 bf 20 02 00 00 	movslq 0x220(%rdi),%rdi
    38cd:	48 8d 0c c9          	lea    (%rcx,%rcx,8),%rcx
    38d1:	48 c1 e1 07          	shl    $0x7,%rcx
      data->thread->tasks[x].available = 1; 
    38d5:	48 8b b0 98 00 00 00 	mov    0x98(%rax),%rsi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    38dc:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    38e3:	48 8b 04 f8          	mov    (%rax,%rdi,8),%rax
    38e7:	48 8d 96 28 02 00 00 	lea    0x228(%rsi),%rdx
    38ee:	48 8d 8c 0e 28 02 00 00 	lea    0x228(%rsi,%rcx,1),%rcx
    38f6:	48 8b 80 98 00 00 00 	mov    0x98(%rax),%rax
    38fd:	48 05 00 01 00 00    	add    $0x100,%rax
    3903:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3908:	83 40 80 01          	addl   $0x1,-0x80(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
    390c:	48 81 c2 80 04 00 00 	add    $0x480,%rdx
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3913:	83 00 01             	addl   $0x1,(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
    3916:	48 05 80 04 00 00    	add    $0x480,%rax
      data->thread->tasks[x].available = 1; 
    391c:	c7 82 80 fb ff ff 01 00 00 00 	movl   $0x1,-0x480(%rdx)
    for (int x = 0 ; x < data->task_count ; x++) {
    3926:	48 39 ca             	cmp    %rcx,%rdx
    3929:	75 dd                	jne    3908 <barriered_reset+0x58>
  asm volatile ("sfence" ::: "memory");
    392b:	0f ae f8             	sfence
}
    392e:	31 c0                	xor    %eax,%eax
    3930:	c3                   	ret
    3931:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    393c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003940 <barriered_thread>:
void* barriered_thread(void *arg) {
    3940:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3944:	83 bf a4 00 00 00 01 	cmpl   $0x1,0xa4(%rdi)
    394b:	0f 85 f4 02 00 00    	jne    3c45 <barriered_thread+0x305>
void* barriered_thread(void *arg) {
    3951:	41 56                	push   %r14
    3953:	41 55                	push   %r13
    3955:	45 31 ed             	xor    %r13d,%r13d
    3958:	41 54                	push   %r12
    395a:	49 89 fc             	mov    %rdi,%r12
    395d:	55                   	push   %rbp
    395e:	53                   	push   %rbx
    395f:	31 db                	xor    %ebx,%ebx
    3961:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    if (t >= data->task_count) {
    3968:	41 8b 94 24 a0 00 00 00 	mov    0xa0(%r12),%edx
    3970:	39 da                	cmp    %ebx,%edx
    3972:	7f 13                	jg     3987 <barriered_thread+0x47>
      data->cycles++;
    3974:	49 83 84 24 00 05 00 00 01 	addq   $0x1,0x500(%r12)
    for (; t < data->task_count; t++) {
    397d:	31 db                	xor    %ebx,%ebx
    397f:	85 d2                	test   %edx,%edx
    3981:	0f 8e 89 01 00 00    	jle    3b10 <barriered_thread+0x1d0>
    3987:	48 63 c3             	movslq %ebx,%rax
    398a:	48 8d 2c c0          	lea    (%rax,%rax,8),%rbp
    398e:	48 c1 e5 07          	shl    $0x7,%rbp
    3992:	eb 16                	jmp    39aa <barriered_thread+0x6a>
    3994:	0f 1f 40 00          	nopl   0x0(%rax)
    3998:	83 c3 01             	add    $0x1,%ebx
    399b:	48 81 c5 80 04 00 00 	add    $0x480,%rbp
    39a2:	39 d3                	cmp    %edx,%ebx
    39a4:	0f 8d 66 01 00 00    	jge    3b10 <barriered_thread+0x1d0>
      if (data->tasks[t].available == 1) {
    39aa:	49 8b 84 24 98 00 00 00 	mov    0x98(%r12),%rax
    39b2:	48 8d 0c 28          	lea    (%rax,%rbp,1),%rcx
    39b6:	83 b9 28 02 00 00 01 	cmpl   $0x1,0x228(%rcx)
    39bd:	75 d9                	jne    3998 <barriered_thread+0x58>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    39bf:	41 8b bc 24 88 00 00 00 	mov    0x88(%r12),%edi
          previous = t - 1;
    39c7:	83 ea 01             	sub    $0x1,%edx
    39ca:	8d 73 ff             	lea    -0x1(%rbx),%esi
    39cd:	85 db                	test   %ebx,%ebx
    39cf:	0f 4f d6             	cmovg  %esi,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    39d2:	85 ff                	test   %edi,%edi
    39d4:	0f 8e 16 02 00 00    	jle    3bf0 <barriered_thread+0x2b0>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    39da:	48 63 d2             	movslq %edx,%rdx
    39dd:	44 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9d
        int prearrive = 0; 
    39e4:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    39e7:	45 31 f6             	xor    %r14d,%r14d
    39ea:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    39f2:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
    39f6:	48 63 d7             	movslq %edi,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    39f9:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3a00:	48 c1 e6 07          	shl    $0x7,%rsi
    3a04:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    3a08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3a10:	48 8b 10             	mov    (%rax),%rdx
    3a13:	4c 8b 9a 98 00 00 00 	mov    0x98(%rdx),%r11
    3a1a:	49 01 f3             	add    %rsi,%r11
    3a1d:	4c 89 da             	mov    %r11,%rdx
    3a20:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    3a27:	75 04                	jne    3a2d <barriered_thread+0xed>
            arrived++;
    3a29:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    3a2d:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    3a34:	75 04                	jne    3a3a <barriered_thread+0xfa>
            prearrive++;
    3a36:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3a3a:	48 83 c0 08          	add    $0x8,%rax
    3a3e:	48 39 c8             	cmp    %rcx,%rax
    3a41:	75 cd                	jne    3a10 <barriered_thread+0xd0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    3a43:	44 39 d7             	cmp    %r10d,%edi
    3a46:	0f 84 e4 00 00 00    	je     3b30 <barriered_thread+0x1f0>
    3a4c:	45 85 d2             	test   %r10d,%r10d
    3a4f:	0f 84 db 00 00 00    	je     3b30 <barriered_thread+0x1f0>
        if (arrived == 0 || arrived == data->thread_count) {
    3a55:	45 85 f6             	test   %r14d,%r14d
    3a58:	74 0e                	je     3a68 <barriered_thread+0x128>
    3a5a:	45 39 b4 24 88 00 00 00 	cmp    %r14d,0x88(%r12)
    3a62:	0f 85 a8 00 00 00    	jne    3b10 <barriered_thread+0x1d0>
    3a68:	49 8b 84 24 98 00 00 00 	mov    0x98(%r12),%rax
          data->tasks[t].prearrive++;
    3a70:	48 01 e8             	add    %rbp,%rax
    3a73:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    3a7a:	85 db                	test   %ebx,%ebx
    3a7c:	75 16                	jne    3a94 <barriered_thread+0x154>
    3a7e:	49 8b b4 24 80 03 00 00 	mov    0x380(%r12),%rsi
    3a86:	49 3b b4 24 88 03 00 00 	cmp    0x388(%r12),%rsi
    3a8e:	0f 8c 2c 01 00 00    	jl     3bc0 <barriered_thread+0x280>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3a94:	49 63 0c 24          	movslq (%r12),%rcx
    3a98:	49 8b 94 24 80 00 00 00 	mov    0x80(%r12),%rdx
          data->tasks[t].available = 0;
    3aa0:	c7 80 28 02 00 00 00 00 00 00 	movl   $0x0,0x228(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3aaa:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    3aae:	48 8b ba 98 00 00 00 	mov    0x98(%rdx),%rdi
    3ab5:	48 01 ef             	add    %rbp,%rdi
    3ab8:	ff 90 08 02 00 00    	call   *0x208(%rax)
          data->tasks[t].arrived++;
    3abe:	49 8b 84 24 98 00 00 00 	mov    0x98(%r12),%rax
    3ac6:	48 01 e8             	add    %rbp,%rax
    3ac9:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3ad0:	41 8b 84 24 a0 00 00 00 	mov    0xa0(%r12),%eax
          data->iteration_count++;
    3ad8:	49 83 84 24 00 03 00 00 01 	addq   $0x1,0x300(%r12)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3ae1:	83 e8 01             	sub    $0x1,%eax
    3ae4:	39 d8                	cmp    %ebx,%eax
    3ae6:	74 60                	je     3b48 <barriered_thread+0x208>
          asm volatile ("sfence" ::: "memory");
    3ae8:	0f ae f8             	sfence
          if (waiting == 0) {
    3aeb:	45 85 ed             	test   %r13d,%r13d
    3aee:	0f 84 8c 00 00 00    	je     3b80 <barriered_thread+0x240>
    for (; t < data->task_count; t++) {
    3af4:	41 8b 94 24 a0 00 00 00 	mov    0xa0(%r12),%edx
    3afc:	83 c3 01             	add    $0x1,%ebx
    3aff:	48 81 c5 80 04 00 00 	add    $0x480,%rbp
    3b06:	39 d3                	cmp    %edx,%ebx
    3b08:	0f 8c 9c fe ff ff    	jl     39aa <barriered_thread+0x6a>
    3b0e:	66 90                	xchg   %ax,%ax
  while (data->running == 1) {
    3b10:	41 83 bc 24 a4 00 00 00 01 	cmpl   $0x1,0xa4(%r12)
    3b19:	0f 84 49 fe ff ff    	je     3968 <barriered_thread+0x28>
}
    3b1f:	5b                   	pop    %rbx
    3b20:	31 c0                	xor    %eax,%eax
    3b22:	5d                   	pop    %rbp
    3b23:	41 5c                	pop    %r12
    3b25:	41 5d                	pop    %r13
    3b27:	41 5e                	pop    %r14
    3b29:	c3                   	ret
    3b2a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (waiting == 1) {
    3b30:	41 83 fd 01          	cmp    $0x1,%r13d
    3b34:	0f 84 c6 00 00 00    	je     3c00 <barriered_thread+0x2c0>
        int arrived = 0; 
    3b3a:	45 31 ed             	xor    %r13d,%r13d
    3b3d:	e9 13 ff ff ff       	jmp    3a55 <barriered_thread+0x115>
    3b42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3b48:	49 8b b4 24 80 03 00 00 	mov    0x380(%r12),%rsi
    3b50:	49 3b b4 24 88 03 00 00 	cmp    0x388(%r12),%rsi
    3b58:	7d 8e                	jge    3ae8 <barriered_thread+0x1a8>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    3b5a:	48 c1 e6 04          	shl    $0x4,%rsi
    3b5e:	bf 04 00 00 00       	mov    $0x4,%edi
    3b63:	49 03 b4 24 80 02 00 00 	add    0x280(%r12),%rsi
    3b6b:	e8 a0 e7 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3b70:	49 83 84 24 80 03 00 00 01 	addq   $0x1,0x380(%r12)
    3b79:	e9 6a ff ff ff       	jmp    3ae8 <barriered_thread+0x1a8>
    3b7e:	66 90                	xchg   %ax,%ax
            data->task_snapshot[data->task_timestamp_count].task = t;
    3b80:	49 8b b4 24 80 04 00 00 	mov    0x480(%r12),%rsi
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3b88:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3b8d:	41 bd 01 00 00 00    	mov    $0x1,%r13d
            data->task_snapshot[data->task_timestamp_count].task = t;
    3b93:	48 c1 e6 08          	shl    $0x8,%rsi
    3b97:	49 03 b4 24 00 04 00 00 	add    0x400(%r12),%rsi
    3b9f:	89 9e 90 00 00 00    	mov    %ebx,0x90(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3ba5:	e8 66 e7 ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3baa:	41 8b 94 24 a0 00 00 00 	mov    0xa0(%r12),%edx
    3bb2:	e9 e1 fd ff ff       	jmp    3998 <barriered_thread+0x58>
    3bb7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3bc0:	48 c1 e6 04          	shl    $0x4,%rsi
    3bc4:	bf 04 00 00 00       	mov    $0x4,%edi
    3bc9:	49 03 b4 24 00 02 00 00 	add    0x200(%r12),%rsi
    3bd1:	e8 3a e7 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3bd6:	49 8b 84 24 98 00 00 00 	mov    0x98(%r12),%rax
    3bde:	48 01 e8             	add    %rbp,%rax
    3be1:	e9 ae fe ff ff       	jmp    3a94 <barriered_thread+0x154>
    3be6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
    3bf0:	41 83 fd 01          	cmp    $0x1,%r13d
    3bf4:	0f 85 76 fe ff ff    	jne    3a70 <barriered_thread+0x130>
        int arrived = 0; 
    3bfa:	45 31 f6             	xor    %r14d,%r14d
    3bfd:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3c00:	49 8b b4 24 80 04 00 00 	mov    0x480(%r12),%rsi
    3c08:	bf 04 00 00 00       	mov    $0x4,%edi
    3c0d:	48 c1 e6 08          	shl    $0x8,%rsi
    3c11:	49 03 b4 24 00 04 00 00 	add    0x400(%r12),%rsi
    3c19:	48 83 ee 80          	sub    $0xffffffffffffff80,%rsi
    3c1d:	e8 ee e6 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3c22:	49 8b 84 24 80 04 00 00 	mov    0x480(%r12),%rax
    3c2a:	48 83 c0 01          	add    $0x1,%rax
    3c2e:	48 99                	cqto
    3c30:	49 f7 bc 24 88 04 00 00 	idivq  0x488(%r12)
    3c38:	49 89 94 24 80 04 00 00 	mov    %rdx,0x480(%r12)
            waiting = 0; 
    3c40:	e9 f5 fe ff ff       	jmp    3b3a <barriered_thread+0x1fa>
}
    3c45:	31 c0                	xor    %eax,%eax
    3c47:	c3                   	ret
    3c48:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000003c50 <external_thread>:
void * external_thread(void *arg) {
    3c50:	f3 0f 1e fa          	endbr64
    3c54:	41 55                	push   %r13
    3c56:	41 54                	push   %r12
    3c58:	55                   	push   %rbp
    3c59:	53                   	push   %rbx
    3c5a:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    3c5e:	66 0f 6f 05 da 3c 00 00 	movdqa 0x3cda(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
void * external_thread(void *arg) {
    3c66:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3c6f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3c74:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3c76:	83 bf a4 00 00 00 01 	cmpl   $0x1,0xa4(%rdi)
  struct timespec req = {
    3c7d:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    3c81:	75 6c                	jne    3cef <external_thread+0x9f>
    3c83:	49 89 fd             	mov    %rdi,%r13
    3c86:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3c8b:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    3c8e:	4c 8d 25 6f 33 00 00 	lea    0x336f(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    3c95:	0f 1f 00             	nopl   (%rax)
    nanosleep(&req , &rem);
    3c98:	48 89 ee             	mov    %rbp,%rsi
    3c9b:	48 89 df             	mov    %rbx,%rdi
    3c9e:	e8 ad e6 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3ca3:	49 8b 85 80 01 00 00 	mov    0x180(%r13),%rax
    3caa:	48 63 10             	movslq (%rax),%rdx
    3cad:	85 d2                	test   %edx,%edx
    3caf:	7e 31                	jle    3ce2 <external_thread+0x92>
    3cb1:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    3cb8:	48 c1 e2 08          	shl    $0x8,%rdx
    3cbc:	48 01 c2             	add    %rax,%rdx
    3cbf:	90                   	nop
      if (data->buffers->buffer[x].available == 0) {
    3cc0:	8b 88 80 00 00 00    	mov    0x80(%rax),%ecx
    3cc6:	85 c9                	test   %ecx,%ecx
    3cc8:	75 0d                	jne    3cd7 <external_thread+0x87>
        data->buffers->buffer[x].data = "Hello world";
    3cca:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    3ccd:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3cd7:	48 05 00 01 00 00    	add    $0x100,%rax
    3cdd:	48 39 c2             	cmp    %rax,%rdx
    3ce0:	75 de                	jne    3cc0 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    3ce2:	0f ae f0             	mfence
  while (data->running == 1) {
    3ce5:	41 83 bd a4 00 00 00 01 	cmpl   $0x1,0xa4(%r13)
    3ced:	74 a9                	je     3c98 <external_thread+0x48>
}
    3cef:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3cf4:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3cfd:	75 0d                	jne    3d0c <external_thread+0xbc>
    3cff:	48 83 c4 38          	add    $0x38,%rsp
    3d03:	31 c0                	xor    %eax,%eax
    3d05:	5b                   	pop    %rbx
    3d06:	5d                   	pop    %rbp
    3d07:	41 5c                	pop    %r12
    3d09:	41 5d                	pop    %r13
    3d0b:	c3                   	ret
    3d0c:	e8 1f e6 ff ff       	call   2330 <__stack_chk_fail@plt>
    3d11:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3d1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003d20 <timer_thread>:
void* timer_thread(void *arg) {
    3d20:	f3 0f 1e fa          	endbr64
    3d24:	41 57                	push   %r15
    3d26:	48 8d 35 e3 32 00 00 	lea    0x32e3(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3d2d:	49 89 ff             	mov    %rdi,%r15
    3d30:	41 56                	push   %r14
    3d32:	41 55                	push   %r13
    3d34:	41 54                	push   %r12
    3d36:	55                   	push   %rbp
    3d37:	53                   	push   %rbx
    3d38:	48 83 ec 58          	sub    $0x58,%rsp
    3d3c:	8b 17                	mov    (%rdi),%edx
    3d3e:	bf 01 00 00 00       	mov    $0x1,%edi
    3d43:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3d4c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3d51:	31 c0                	xor    %eax,%eax
    3d53:	e8 f8 e6 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3d58:	66 0f 6f 05 e0 3b 00 00 	movdqa 0x3be0(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3d60:	ba 88 13 00 00       	mov    $0x1388,%edx
    3d65:	31 c0                	xor    %eax,%eax
    3d67:	48 8d 35 b4 32 00 00 	lea    0x32b4(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3d6e:	bf 01 00 00 00       	mov    $0x1,%edi
    3d73:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3d78:	e8 d3 e6 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3d7d:	45 8b af a4 00 00 00 	mov    0xa4(%r15),%r13d
    3d84:	45 85 ed             	test   %r13d,%r13d
    3d87:	0f 84 b3 00 00 00    	je     3e40 <timer_thread+0x120>
  int n = 0;
    3d8d:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    3d90:	45 31 ed             	xor    %r13d,%r13d
    3d93:	49 89 e4             	mov    %rsp,%r12
    y++;
    3d96:	31 db                	xor    %ebx,%ebx
    3d98:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    3d9d:	48 89 ef             	mov    %rbp,%rdi
    3da0:	4c 89 e6             	mov    %r12,%rsi
    n++;
    3da3:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3da7:	e8 a4 e5 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3dac:	49 63 87 88 00 00 00 	movslq 0x88(%r15),%rax
    y++;
    3db3:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3db7:	85 c0                	test   %eax,%eax
    3db9:	7e 54                	jle    3e0f <timer_thread+0xef>
    3dbb:	49 8b 8f 80 00 00 00 	mov    0x80(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3dc2:	4f 8d 44 ed 00       	lea    0x0(%r13,%r13,8),%r8
    3dc7:	49 c1 e0 07          	shl    $0x7,%r8
    3dcb:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3dcf:	90                   	nop
        int next = (y + 1) % data->threads[x]->task_count;
    3dd0:	4c 8b 19             	mov    (%rcx),%r11
    3dd3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3dd5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3dd9:	99                   	cltd
    3dda:	41 f7 bb a0 00 00 00 	idivl  0xa0(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    3de1:	49 8b b3 98 00 00 00 	mov    0x98(%r11),%rsi
    3de8:	48 63 d2             	movslq %edx,%rdx
    3deb:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    3def:	48 c1 e0 07          	shl    $0x7,%rax
    3df3:	c7 84 06 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rsi,%rax,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3dfe:	42 c7 84 06 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3e0a:	49 39 c9             	cmp    %rcx,%r9
    3e0d:	75 c1                	jne    3dd0 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    3e0f:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3e12:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
  while (data->running && n < times) {
    3e19:	41 8b 97 a4 00 00 00 	mov    0xa4(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3e20:	48 8b 00             	mov    (%rax),%rax
    y++;
    3e23:	39 b8 a0 00 00 00    	cmp    %edi,0xa0(%rax)
    3e29:	0f 4e fb             	cmovle %ebx,%edi
    3e2c:	4c 63 ef             	movslq %edi,%r13
  while (data->running && n < times) {
    3e2f:	85 d2                	test   %edx,%edx
    3e31:	74 0d                	je     3e40 <timer_thread+0x120>
    3e33:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3e3a:	0f 85 5d ff ff ff    	jne    3d9d <timer_thread+0x7d>
    3e40:	48 8d 3d f1 31 00 00 	lea    0x31f1(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3e47:	e8 a4 e4 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3e4c:	49 63 87 8c 00 00 00 	movslq 0x8c(%r15),%rax
    3e53:	85 c0                	test   %eax,%eax
    3e55:	0f 8e 91 00 00 00    	jle    3eec <timer_thread+0x1cc>
    for (int y = 0 ; y < data->task_count ; y++) {
    3e5b:	41 8b 97 a0 00 00 00 	mov    0xa0(%r15),%edx
    3e62:	85 d2                	test   %edx,%edx
    3e64:	0f 8e 82 00 00 00    	jle    3eec <timer_thread+0x1cc>
    3e6a:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    3e72:	48 63 c2             	movslq %edx,%rax
      data->threads[x]->tasks[y].sending = 0;
    3e75:	4d 8b 8f 80 00 00 00 	mov    0x80(%r15),%r9
    3e7c:	31 f6                	xor    %esi,%esi
    3e7e:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3e82:	48 c1 e0 07          	shl    $0x7,%rax
    3e86:	4c 8d 80 08 04 00 00 	lea    0x408(%rax),%r8
    3e8d:	49 8b 04 31          	mov    (%r9,%rsi,1),%rax
    3e91:	48 8b b8 98 00 00 00 	mov    0x98(%rax),%rdi
    3e98:	4a 8d 14 07          	lea    (%rdi,%r8,1),%rdx
    3e9c:	48 8d 87 08 04 00 00 	lea    0x408(%rdi),%rax
    3ea3:	49 89 d2             	mov    %rdx,%r10
    3ea6:	49 29 c2             	sub    %rax,%r10
    3ea9:	41 81 e2 80 00 00 00 	and    $0x80,%r10d
    3eb0:	74 16                	je     3ec8 <timer_thread+0x1a8>
    for (int y = 0 ; y < data->task_count ; y++) {
    3eb2:	48 8d 87 88 08 00 00 	lea    0x888(%rdi),%rax
      data->threads[x]->tasks[y].sending = 0;
    3eb9:	c7 87 08 04 00 00 00 00 00 00 	movl   $0x0,0x408(%rdi)
    for (int y = 0 ; y < data->task_count ; y++) {
    3ec3:	48 39 c2             	cmp    %rax,%rdx
    3ec6:	74 1b                	je     3ee3 <timer_thread+0x1c3>
      data->threads[x]->tasks[y].sending = 0;
    3ec8:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3ece:	48 05 00 09 00 00    	add    $0x900,%rax
      data->threads[x]->tasks[y].sending = 0;
    3ed4:	c7 80 80 fb ff ff 00 00 00 00 	movl   $0x0,-0x480(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3ede:	48 39 c2             	cmp    %rax,%rdx
    3ee1:	75 e5                	jne    3ec8 <timer_thread+0x1a8>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ee3:	48 83 c6 08          	add    $0x8,%rsi
    3ee7:	48 39 f1             	cmp    %rsi,%rcx
    3eea:	75 a1                	jne    3e8d <timer_thread+0x16d>
  asm volatile ("mfence" ::: "memory");
    3eec:	0f ae f0             	mfence
  struct timespec drain = {
    3eef:	66 0f 6f 05 59 3a 00 00 	movdqa 0x3a59(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3ef7:	48 8d 2d 5f 31 00 00 	lea    0x315f(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3efe:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f03:	49 63 87 88 00 00 00 	movslq 0x88(%r15),%rax
    y++;
    3f0a:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f0e:	85 c0                	test   %eax,%eax
    3f10:	7e 5c                	jle    3f6e <timer_thread+0x24e>
    3f12:	49 8b 8f 80 00 00 00 	mov    0x80(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3f19:	4d 63 ed             	movslq %r13d,%r13
    3f1c:	4f 8d 44 ed 00       	lea    0x0(%r13,%r13,8),%r8
    3f21:	49 c1 e0 07          	shl    $0x7,%r8
    3f25:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3f29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3f30:	48 8b 19             	mov    (%rcx),%rbx
    3f33:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f35:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3f39:	99                   	cltd
    3f3a:	f7 bb a0 00 00 00    	idivl  0xa0(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3f40:	48 8b b3 98 00 00 00 	mov    0x98(%rbx),%rsi
    3f47:	48 63 c2             	movslq %edx,%rax
    3f4a:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3f4e:	48 c1 e0 07          	shl    $0x7,%rax
    3f52:	c7 84 06 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rsi,%rax,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3f5d:	42 c7 84 06 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f69:	49 39 c9             	cmp    %rcx,%r9
    3f6c:	75 c2                	jne    3f30 <timer_thread+0x210>
    asm volatile ("mfence" ::: "memory");
    3f6e:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3f71:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    y++;
    3f78:	45 31 ed             	xor    %r13d,%r13d
    if (y >= data->threads[0]->task_count) {
    3f7b:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3f7e:	39 ba a0 00 00 00    	cmp    %edi,0xa0(%rdx)
    3f84:	44 0f 4f ef          	cmovg  %edi,%r13d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3f88:	41 8b bf 90 00 00 00 	mov    0x90(%r15),%edi
    3f8f:	85 ff                	test   %edi,%edi
    3f91:	0f 8e cc 00 00 00    	jle    4063 <timer_thread+0x343>
    3f97:	45 31 e4             	xor    %r12d,%r12d
    int all_empty = 1;
    3f9a:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3fa0:	4a 8d 1c e5 00 00 00 00 	lea    0x0(,%r12,8),%rbx
            all_empty = 0;
    3fa8:	45 31 f6             	xor    %r14d,%r14d
    3fab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3fb0:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3fb4:	4b 8d 04 f6          	lea    (%r14,%r14,8),%rax
    3fb8:	48 c1 e0 07          	shl    $0x7,%rax
    3fbc:	48 03 82 98 00 00 00 	add    0x98(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3fc3:	31 d2                	xor    %edx,%edx
    3fc5:	48 8b 80 88 03 00 00 	mov    0x388(%rax),%rax
    3fcc:	eb 14                	jmp    3fe2 <timer_thread+0x2c2>
    3fce:	66 90                	xchg   %ax,%ax
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3fd0:	4d 85 c0             	test   %r8,%r8
    3fd3:	7f 2a                	jg     3fff <timer_thread+0x2df>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3fd5:	83 c2 01             	add    $0x1,%edx
    3fd8:	48 05 00 02 00 00    	add    $0x200,%rax
    3fde:	39 fa                	cmp    %edi,%edx
    3fe0:	74 36                	je     4018 <timer_thread+0x2f8>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3fe2:	48 8b 08             	mov    (%rax),%rcx
    3fe5:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    3fec:	48 8b 89 80 00 00 00 	mov    0x80(%rcx),%rcx
    3ff3:	4c 8b 86 80 00 00 00 	mov    0x80(%rsi),%r8
    3ffa:	48 85 c9             	test   %rcx,%rcx
    3ffd:	7e d1                	jle    3fd0 <timer_thread+0x2b0>
    3fff:	bf 01 00 00 00       	mov    $0x1,%edi
    4004:	48 89 ee             	mov    %rbp,%rsi
    4007:	31 c0                	xor    %eax,%eax
    4009:	e8 42 e4 ff ff       	call   2450 <__printf_chk@plt>
            break;
    400e:	41 8b bf 90 00 00 00 	mov    0x90(%r15),%edi
            all_empty = 0;
    4015:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    4018:	49 83 c6 01          	add    $0x1,%r14
    401c:	44 39 f7             	cmp    %r14d,%edi
    401f:	7e 0f                	jle    4030 <timer_thread+0x310>
    4021:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    4028:	eb 86                	jmp    3fb0 <timer_thread+0x290>
    402a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4030:	49 83 c4 01          	add    $0x1,%r12
    4034:	44 39 e7             	cmp    %r12d,%edi
    4037:	7e 10                	jle    4049 <timer_thread+0x329>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    4039:	85 ff                	test   %edi,%edi
    403b:	7e 0c                	jle    4049 <timer_thread+0x329>
    403d:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    4044:	e9 57 ff ff ff       	jmp    3fa0 <timer_thread+0x280>
    if (all_empty == 1) {
    4049:	41 83 f9 01          	cmp    $0x1,%r9d
    404d:	74 14                	je     4063 <timer_thread+0x343>
      nanosleep(&drain , &drainrem);
    404f:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4054:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4059:	e8 f2 e2 ff ff       	call   2350 <nanosleep@plt>
    405e:	e9 a0 fe ff ff       	jmp    3f03 <timer_thread+0x1e3>
    4063:	48 8d 3d ea 2f 00 00 	lea    0x2fea(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    406a:	e8 81 e2 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    406f:	41 8b 87 a4 00 00 00 	mov    0xa4(%r15),%eax
    4076:	85 c0                	test   %eax,%eax
    4078:	0f 84 08 01 00 00    	je     4186 <timer_thread+0x466>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    407e:	41 8b 8f 8c 00 00 00 	mov    0x8c(%r15),%ecx
    4085:	85 c9                	test   %ecx,%ecx
    4087:	7e 37                	jle    40c0 <timer_thread+0x3a0>
    4089:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    4090:	31 db                	xor    %ebx,%ebx
    4092:	48 8d 2d d5 2f 00 00 	lea    0x2fd5(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    4099:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->threads[x]->running = 0;
    40a0:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
    40a4:	c7 82 a4 00 00 00 00 00 00 00 	movl   $0x0,0xa4(%rdx)
      if (data->threads[x]->type == IO) {
    40ae:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
    40b2:	0f 84 fb 00 00 00    	je     41b3 <timer_thread+0x493>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    40b8:	48 83 c3 01          	add    $0x1,%rbx
    40bc:	39 d9                	cmp    %ebx,%ecx
    40be:	7f e0                	jg     40a0 <timer_thread+0x380>
    for (int x = 0 ; x < data->thread_count ; x++) {
    40c0:	49 63 87 88 00 00 00 	movslq 0x88(%r15),%rax
    40c7:	85 c0                	test   %eax,%eax
    40c9:	0f 8e 9d 00 00 00    	jle    416c <timer_thread+0x44c>
      for (int y = 0 ; y < data->task_count ; y++) {
    40cf:	41 8b 97 a0 00 00 00 	mov    0xa0(%r15),%edx
    40d6:	85 d2                	test   %edx,%edx
    40d8:	0f 8e 8e 00 00 00    	jle    416c <timer_thread+0x44c>
    40de:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
    40e6:	48 63 c2             	movslq %edx,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    40e9:	4d 8b 97 80 00 00 00 	mov    0x80(%r15),%r10
    40f0:	31 c9                	xor    %ecx,%ecx
    40f2:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    40f6:	48 c1 e0 07          	shl    $0x7,%rax
    40fa:	4c 8d 88 80 02 00 00 	lea    0x280(%rax),%r9
    4101:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4108:	49 8b 04 0a          	mov    (%r10,%rcx,1),%rax
    410c:	48 8b b0 98 00 00 00 	mov    0x98(%rax),%rsi
    4113:	4a 8d 14 0e          	lea    (%rsi,%r9,1),%rdx
    4117:	48 8d 86 80 02 00 00 	lea    0x280(%rsi),%rax
    411e:	48 89 d7             	mov    %rdx,%rdi
    4121:	48 29 c7             	sub    %rax,%rdi
    4124:	81 e7 80 00 00 00    	and    $0x80,%edi
    412a:	74 1c                	je     4148 <timer_thread+0x428>
      for (int y = 0 ; y < data->task_count ; y++) {
    412c:	48 8d 86 00 07 00 00 	lea    0x700(%rsi),%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4133:	c7 86 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rsi)
      for (int y = 0 ; y < data->task_count ; y++) {
    413d:	48 39 d0             	cmp    %rdx,%rax
    4140:	74 21                	je     4163 <timer_thread+0x443>
    4142:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4148:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    414e:	48 05 00 09 00 00    	add    $0x900,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4154:	c7 80 80 fb ff ff 00 00 00 00 	movl   $0x0,-0x480(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    415e:	48 39 d0             	cmp    %rdx,%rax
    4161:	75 e5                	jne    4148 <timer_thread+0x428>
    for (int x = 0 ; x < data->thread_count ; x++) {
    4163:	48 83 c1 08          	add    $0x8,%rcx
    4167:	4c 39 c1             	cmp    %r8,%rcx
    416a:	75 9c                	jne    4108 <timer_thread+0x3e8>
    asm volatile ("mfence" ::: "memory");
    416c:	0f ae f0             	mfence
    416f:	48 8d 3d 0a 2f 00 00 	lea    0x2f0a(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    4176:	e8 75 e1 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    417b:	41 c7 87 a4 00 00 00 00 00 00 00 	movl   $0x0,0xa4(%r15)
    4186:	48 8d 3d fa 2e 00 00 	lea    0x2efa(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    418d:	e8 5e e1 ff ff       	call   22f0 <puts@plt>
}
    4192:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    4197:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    41a0:	75 53                	jne    41f5 <timer_thread+0x4d5>
    41a2:	48 83 c4 58          	add    $0x58,%rsp
    41a6:	31 c0                	xor    %eax,%eax
    41a8:	5b                   	pop    %rbx
    41a9:	5d                   	pop    %rbp
    41aa:	41 5c                	pop    %r12
    41ac:	41 5d                	pop    %r13
    41ae:	41 5e                	pop    %r14
    41b0:	41 5f                	pop    %r15
    41b2:	c3                   	ret
    41b3:	48 89 ef             	mov    %rbp,%rdi
    41b6:	e8 35 e1 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    41bb:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    41c2:	be 01 00 00 00       	mov    $0x1,%esi
    41c7:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    41cb:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    41cf:	8b b8 90 01 00 00    	mov    0x190(%rax),%edi
    41d5:	e8 26 e2 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    41da:	41 8b 8f 8c 00 00 00 	mov    0x8c(%r15),%ecx
    41e1:	39 d9                	cmp    %ebx,%ecx
    41e3:	0f 8e d7 fe ff ff    	jle    40c0 <timer_thread+0x3a0>
    41e9:	49 8b 87 80 00 00 00 	mov    0x80(%r15),%rax
    41f0:	e9 ab fe ff ff       	jmp    40a0 <timer_thread+0x380>
}
    41f5:	e8 36 e1 ff ff       	call   2330 <__stack_chk_fail@plt>
    41fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004200 <strtolower>:
void strtolower(char *str) {
    4200:	f3 0f 1e fa          	endbr64
    4204:	55                   	push   %rbp
    4205:	53                   	push   %rbx
    4206:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    420a:	48 0f be 1f          	movsbq (%rdi),%rbx
    420e:	84 db                	test   %bl,%bl
    4210:	74 24                	je     4236 <strtolower+0x36>
    4212:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4215:	e8 f6 e2 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    421a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4220:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4223:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4227:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    422a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    422d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4232:	84 db                	test   %bl,%bl
    4234:	75 ea                	jne    4220 <strtolower+0x20>
}
    4236:	48 83 c4 08          	add    $0x8,%rsp
    423a:	5b                   	pop    %rbx
    423b:	5d                   	pop    %rbp
    423c:	c3                   	ret
    423d:	0f 1f 00             	nopl   (%rax)

0000000000004240 <zh_malloc>:
void *zh_malloc(size_t size) {
    4240:	f3 0f 1e fa          	endbr64
    4244:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4248:	e8 c3 e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    424d:	48 85 c0             	test   %rax,%rax
    4250:	74 05                	je     4257 <zh_malloc+0x17>
}
    4252:	48 83 c4 08          	add    $0x8,%rsp
    4256:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4257:	48 8b 0d c2 5d 00 00 	mov    0x5dc2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    425e:	ba 28 00 00 00       	mov    $0x28,%edx
    4263:	be 01 00 00 00       	mov    $0x1,%esi
    4268:	48 8d 3d 99 31 00 00 	lea    0x3199(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    426f:	e8 4c e2 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4274:	bf 01 00 00 00       	mov    $0x1,%edi
    4279:	e8 22 e2 ff ff       	call   24a0 <exit@plt>
    427e:	66 90                	xchg   %ax,%ax

0000000000004280 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4280:	f3 0f 1e fa          	endbr64
    4284:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4285:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    428a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    428d:	e8 ce e0 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4292:	48 85 c0             	test   %rax,%rax
    4295:	74 11                	je     42a8 <get_filename_ext+0x28>
    4297:	48 39 c3             	cmp    %rax,%rbx
    429a:	74 0c                	je     42a8 <get_filename_ext+0x28>
    return dot + 1;
    429c:	48 83 c0 01          	add    $0x1,%rax
}
    42a0:	5b                   	pop    %rbx
    42a1:	c3                   	ret
    42a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    42a8:	48 8d 05 20 2e 00 00 	lea    0x2e20(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    42af:	5b                   	pop    %rbx
    42b0:	c3                   	ret
    42b1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    42bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000042c0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    42c0:	f3 0f 1e fa          	endbr64
    42c4:	41 55                	push   %r13
    42c6:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    42c9:	48 89 fe             	mov    %rdi,%rsi
    42cc:	41 54                	push   %r12
    42ce:	55                   	push   %rbp
    42cf:	48 89 d5             	mov    %rdx,%rbp
    42d2:	ba 00 04 00 00       	mov    $0x400,%edx
    42d7:	53                   	push   %rbx
    42d8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    42df:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    42e8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    42f0:	31 c0                	xor    %eax,%eax
    42f2:	49 89 e4             	mov    %rsp,%r12
    42f5:	4c 89 e7             	mov    %r12,%rdi
    42f8:	e8 33 e1 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    42fd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4302:	84 db                	test   %bl,%bl
    4304:	74 24                	je     432a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4306:	e8 05 e2 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    430b:	48 8b 08             	mov    (%rax),%rcx
    430e:	4c 89 e0             	mov    %r12,%rax
    4311:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4318:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    431b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    431f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4322:	48 0f be 18          	movsbq (%rax),%rbx
    4326:	84 db                	test   %bl,%bl
    4328:	75 ee                	jne    4318 <send_headers+0x58>
    void *buf = malloc(size);
    432a:	bf 11 00 00 00       	mov    $0x11,%edi
    432f:	e8 dc e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4334:	48 85 c0             	test   %rax,%rax
    4337:	0f 84 7e 04 00 00    	je     47bb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    433d:	66 0f 6f 05 1b 36 00 00 	movdqa 0x361b(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    4345:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4349:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    434e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4356:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    435a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    435d:	e8 ae e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4362:	48 85 c0             	test   %rax,%rax
    4365:	0f 84 50 04 00 00    	je     47bb <send_headers+0x4fb>
    436b:	66 0f 6f 05 fd 35 00 00 	movdqa 0x35fd(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    4373:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4377:	4c 89 e7             	mov    %r12,%rdi
    437a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4384:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    438c:	0f 11 00             	movups %xmm0,(%rax)
    438f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4393:	be 2e 00 00 00       	mov    $0x2e,%esi
    4398:	e8 c3 df ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    439d:	48 85 c0             	test   %rax,%rax
    43a0:	0f 84 ea 02 00 00    	je     4690 <send_headers+0x3d0>
    43a6:	4c 39 e0             	cmp    %r12,%rax
    43a9:	0f 84 e1 02 00 00    	je     4690 <send_headers+0x3d0>
    return dot + 1;
    43af:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    43b3:	48 8d 3d e3 2c 00 00 	lea    0x2ce3(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    43ba:	48 89 de             	mov    %rbx,%rsi
    43bd:	e8 ee df ff ff       	call   23b0 <strcmp@plt>
    43c2:	85 c0                	test   %eax,%eax
    43c4:	75 20                	jne    43e6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    43c6:	66 0f 6f 05 b2 35 00 00 	movdqa 0x35b2(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    43ce:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    43d6:	66 0f 6f 05 b2 35 00 00 	movdqa 0x35b2(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    43de:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    43e6:	48 89 de             	mov    %rbx,%rsi
    43e9:	48 8d 3d b1 2c 00 00 	lea    0x2cb1(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    43f0:	e8 bb df ff ff       	call   23b0 <strcmp@plt>
    43f5:	85 c0                	test   %eax,%eax
    43f7:	75 20                	jne    4419 <send_headers+0x159>
    43f9:	66 0f 6f 05 7f 35 00 00 	movdqa 0x357f(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4401:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4409:	66 0f 6f 05 7f 35 00 00 	movdqa 0x357f(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    4411:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4419:	48 89 de             	mov    %rbx,%rsi
    441c:	48 8d 3d 83 2c 00 00 	lea    0x2c83(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    4423:	e8 88 df ff ff       	call   23b0 <strcmp@plt>
    4428:	85 c0                	test   %eax,%eax
    442a:	0f 84 10 02 00 00    	je     4640 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4430:	48 89 de             	mov    %rbx,%rsi
    4433:	48 8d 3d 70 2c 00 00 	lea    0x2c70(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    443a:	e8 71 df ff ff       	call   23b0 <strcmp@plt>
    443f:	85 c0                	test   %eax,%eax
    4441:	0f 84 a9 02 00 00    	je     46f0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4447:	48 89 de             	mov    %rbx,%rsi
    444a:	48 8d 3d 5d 2c 00 00 	lea    0x2c5d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4451:	e8 5a df ff ff       	call   23b0 <strcmp@plt>
    4456:	85 c0                	test   %eax,%eax
    4458:	0f 84 6a 02 00 00    	je     46c8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    445e:	48 89 de             	mov    %rbx,%rsi
    4461:	48 8d 3d 89 2c 00 00 	lea    0x2c89(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4468:	e8 43 df ff ff       	call   23b0 <strcmp@plt>
    446d:	85 c0                	test   %eax,%eax
    446f:	0f 84 2b 02 00 00    	je     46a0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4475:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4478:	0f 84 52 01 00 00    	je     45d0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    447e:	48 89 de             	mov    %rbx,%rsi
    4481:	48 8d 3d 2a 2c 00 00 	lea    0x2c2a(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    4488:	e8 23 df ff ff       	call   23b0 <strcmp@plt>
    448d:	85 c0                	test   %eax,%eax
    448f:	0f 84 ab 02 00 00    	je     4740 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4495:	48 89 de             	mov    %rbx,%rsi
    4498:	48 8d 3d 17 2c 00 00 	lea    0x2c17(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    449f:	e8 0c df ff ff       	call   23b0 <strcmp@plt>
    44a4:	85 c0                	test   %eax,%eax
    44a6:	0f 84 6c 02 00 00    	je     4718 <send_headers+0x458>
    slen = strlen(send_buffer);
    44ac:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    44b4:	4c 89 e7             	mov    %r12,%rdi
    44b7:	e8 64 de ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    44bc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    44bf:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    44c2:	e8 49 df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    44c7:	48 85 c0             	test   %rax,%rax
    44ca:	0f 84 eb 02 00 00    	je     47bb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    44d0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    44d4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    44d8:	83 fb 08             	cmp    $0x8,%ebx
    44db:	0f 83 3f 01 00 00    	jae    4620 <send_headers+0x360>
    44e1:	f6 c3 04             	test   $0x4,%bl
    44e4:	0f 85 7b 02 00 00    	jne    4765 <send_headers+0x4a5>
    44ea:	85 db                	test   %ebx,%ebx
    44ec:	74 13                	je     4501 <send_headers+0x241>
    44ee:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    44f6:	88 10                	mov    %dl,(%rax)
    44f8:	f6 c3 02             	test   $0x2,%bl
    44fb:	0f 85 96 02 00 00    	jne    4797 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4501:	4d 89 e8             	mov    %r13,%r8
    4504:	48 8d 0d af 2b 00 00 	lea    0x2baf(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    450b:	4c 89 e7             	mov    %r12,%rdi
    450e:	31 c0                	xor    %eax,%eax
    4510:	ba 00 04 00 00       	mov    $0x400,%edx
    4515:	be 01 00 00 00       	mov    $0x1,%esi
    451a:	e8 01 e0 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    451f:	4c 89 e7             	mov    %r12,%rdi
    4522:	e8 f9 dd ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4527:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    452a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    452d:	e8 de de ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4532:	48 85 c0             	test   %rax,%rax
    4535:	0f 84 80 02 00 00    	je     47bb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    453b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    453f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4543:	83 fb 08             	cmp    $0x8,%ebx
    4546:	0f 83 1c 01 00 00    	jae    4668 <send_headers+0x3a8>
    454c:	f6 c3 04             	test   $0x4,%bl
    454f:	0f 85 29 02 00 00    	jne    477e <send_headers+0x4be>
    4555:	85 db                	test   %ebx,%ebx
    4557:	74 13                	je     456c <send_headers+0x2ac>
    4559:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4561:	88 10                	mov    %dl,(%rax)
    4563:	f6 c3 02             	test   $0x2,%bl
    4566:	0f 85 3d 02 00 00    	jne    47a9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    456c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4571:	bf 02 00 00 00       	mov    $0x2,%edi
    4576:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    457e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4586:	e8 85 de ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    458b:	48 85 c0             	test   %rax,%rax
    458e:	0f 84 27 02 00 00    	je     47bb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4594:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    459c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    45a0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    45a8:	66 89 10             	mov    %dx,(%rax)
}
    45ab:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    45b3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    45bc:	0f 85 20 02 00 00    	jne    47e2 <send_headers+0x522>
    45c2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    45c9:	5b                   	pop    %rbx
    45ca:	5d                   	pop    %rbp
    45cb:	41 5c                	pop    %r12
    45cd:	41 5d                	pop    %r13
    45cf:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    45d0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    45d4:	0f 85 a4 fe ff ff    	jne    447e <send_headers+0x1be>
    45da:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    45de:	0f 85 9a fe ff ff    	jne    447e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    45e4:	66 0f 6f 05 f4 33 00 00 	movdqa 0x33f4(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    45ec:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    45f6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    45fe:	66 0f 6f 05 ea 33 00 00 	movdqa 0x33ea(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    4606:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    460e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4616:	e9 63 fe ff ff       	jmp    447e <send_headers+0x1be>
    461b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4620:	89 da                	mov    %ebx,%edx
    4622:	48 89 c7             	mov    %rax,%rdi
    4625:	4c 89 e6             	mov    %r12,%rsi
    4628:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    462d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4632:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4635:	c1 e9 03             	shr    $0x3,%ecx
    4638:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    463b:	e9 c1 fe ff ff       	jmp    4501 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4640:	66 0f 6f 05 38 33 00 00 	movdqa 0x3338(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4648:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4650:	66 0f 6f 05 48 33 00 00 	movdqa 0x3348(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4658:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4660:	e9 cb fd ff ff       	jmp    4430 <send_headers+0x170>
    4665:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4668:	89 da                	mov    %ebx,%edx
    466a:	48 89 c7             	mov    %rax,%rdi
    466d:	4c 89 e6             	mov    %r12,%rsi
    4670:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4675:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    467a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    467d:	c1 e9 03             	shr    $0x3,%ecx
    4680:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4683:	e9 e4 fe ff ff       	jmp    456c <send_headers+0x2ac>
    4688:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4690:	48 8d 1d 38 2a 00 00 	lea    0x2a38(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4697:	e9 94 fd ff ff       	jmp    4430 <send_headers+0x170>
    469c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    46a0:	66 0f 6f 05 18 33 00 00 	movdqa 0x3318(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    46a8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    46b0:	66 0f 6f 05 18 33 00 00 	movdqa 0x3318(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    46b8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    46c0:	e9 b0 fd ff ff       	jmp    4475 <send_headers+0x1b5>
    46c5:	0f 1f 00             	nopl   (%rax)
    46c8:	66 0f 6f 05 f0 32 00 00 	movdqa 0x32f0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    46d0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    46d8:	66 0f 6f 05 f0 32 00 00 	movdqa 0x32f0(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    46e0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    46e8:	e9 71 fd ff ff       	jmp    445e <send_headers+0x19e>
    46ed:	0f 1f 00             	nopl   (%rax)
    46f0:	66 0f 6f 05 88 32 00 00 	movdqa 0x3288(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    46f8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4700:	66 0f 6f 05 a8 32 00 00 	movdqa 0x32a8(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    4708:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4710:	e9 32 fd ff ff       	jmp    4447 <send_headers+0x187>
    4715:	0f 1f 00             	nopl   (%rax)
    4718:	66 0f 6f 05 a0 32 00 00 	movdqa 0x32a0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4720:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4728:	66 0f 6f 05 e0 32 00 00 	movdqa 0x32e0(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4730:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4738:	e9 6f fd ff ff       	jmp    44ac <send_headers+0x1ec>
    473d:	0f 1f 00             	nopl   (%rax)
    4740:	66 0f 6f 05 78 32 00 00 	movdqa 0x3278(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4748:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4750:	66 0f 6f 05 a8 32 00 00 	movdqa 0x32a8(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4758:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4760:	e9 30 fd ff ff       	jmp    4495 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4765:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    476c:	89 db                	mov    %ebx,%ebx
    476e:	89 10                	mov    %edx,(%rax)
    4770:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4775:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4779:	e9 83 fd ff ff       	jmp    4501 <send_headers+0x241>
    477e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4785:	89 db                	mov    %ebx,%ebx
    4787:	89 10                	mov    %edx,(%rax)
    4789:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    478e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4792:	e9 d5 fd ff ff       	jmp    456c <send_headers+0x2ac>
    4797:	89 db                	mov    %ebx,%ebx
    4799:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    479f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    47a4:	e9 58 fd ff ff       	jmp    4501 <send_headers+0x241>
    47a9:	89 db                	mov    %ebx,%ebx
    47ab:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    47b1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    47b6:	e9 b1 fd ff ff       	jmp    456c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    47bb:	48 8b 0d 5e 58 00 00 	mov    0x585e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    47c2:	ba 28 00 00 00       	mov    $0x28,%edx
    47c7:	be 01 00 00 00       	mov    $0x1,%esi
    47cc:	48 8d 3d 35 2c 00 00 	lea    0x2c35(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    47d3:	e8 e8 dc ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    47d8:	bf 01 00 00 00       	mov    $0x1,%edi
    47dd:	e8 be dc ff ff       	call   24a0 <exit@plt>
}
    47e2:	e8 49 db ff ff       	call   2330 <__stack_chk_fail@plt>
    47e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000047f0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    47f0:	f3 0f 1e fa          	endbr64
    47f4:	41 55                	push   %r13
    47f6:	49 89 d5             	mov    %rdx,%r13
    47f9:	41 54                	push   %r12
    47fb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    47fe:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4801:	55                   	push   %rbp
    4802:	53                   	push   %rbx
    4803:	48 89 f3             	mov    %rsi,%rbx
    4806:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    480a:	e8 01 dc ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    480f:	48 85 c0             	test   %rax,%rax
    4812:	74 6b                	je     487f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4814:	4c 89 e7             	mov    %r12,%rdi
    4817:	48 89 c5             	mov    %rax,%rbp
    481a:	31 f6                	xor    %esi,%esi
    481c:	31 c0                	xor    %eax,%eax
    481e:	e8 5d dc ff ff       	call   2480 <open@plt>
    4823:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4826:	85 c0                	test   %eax,%eax
    4828:	0f 88 28 dd ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    482e:	48 89 da             	mov    %rbx,%rdx
    4831:	48 89 ee             	mov    %rbp,%rsi
    4834:	89 c7                	mov    %eax,%edi
    4836:	e8 55 db ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    483b:	48 98                	cltq
    483d:	48 39 d8             	cmp    %rbx,%rax
    4840:	7c 1e                	jl     4860 <copy_file_contents+0x70>
    close(fd);
    4842:	44 89 e7             	mov    %r12d,%edi
    4845:	e8 26 db ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    484a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    484e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4852:	48 83 c4 08          	add    $0x8,%rsp
    4856:	5b                   	pop    %rbx
    4857:	5d                   	pop    %rbp
    4858:	41 5c                	pop    %r12
    485a:	41 5d                	pop    %r13
    485c:	c3                   	ret
    485d:	0f 1f 00             	nopl   (%rax)
    4860:	48 8b 0d b9 57 00 00 	mov    0x57b9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4867:	ba 1a 00 00 00       	mov    $0x1a,%edx
    486c:	be 01 00 00 00       	mov    $0x1,%esi
    4871:	48 8d 3d 58 28 00 00 	lea    0x2858(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    4878:	e8 43 dc ff ff       	call   24c0 <fwrite@plt>
    487d:	eb c3                	jmp    4842 <copy_file_contents+0x52>
    487f:	48 8b 0d 9a 57 00 00 	mov    0x579a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4886:	ba 28 00 00 00       	mov    $0x28,%edx
    488b:	be 01 00 00 00       	mov    $0x1,%esi
    4890:	48 8d 3d 71 2b 00 00 	lea    0x2b71(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4897:	e8 24 dc ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    489c:	bf 01 00 00 00       	mov    $0x1,%edi
    48a1:	e8 fa db ff ff       	call   24a0 <exit@plt>
    48a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000048b0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    48b0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    48b4:	8b 46 44             	mov    0x44(%rsi),%eax
    48b7:	48 89 fa             	mov    %rdi,%rdx
    48ba:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    48bd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    48c3:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    48c6:	48 8b 07             	mov    (%rdi),%rax
    48c9:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    48cc:	f6 c1 02             	test   $0x2,%cl
    48cf:	74 00                	je     48d1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    48d1:	89 f0                	mov    %esi,%eax
    48d3:	44 29 c0             	sub    %r8d,%eax
    48d6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    48d9:	0f 82 83 dc ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    48df:	c1 e9 0a             	shr    $0xa,%ecx
    48e2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    48e6:	8b 47 44             	mov    0x44(%rdi),%eax
    48e9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    48ec:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    48ef:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    48f2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    48f5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    48f9:	d3 e0                	shl    %cl,%eax
    48fb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    48fe:	48 c1 e0 06          	shl    $0x6,%rax
    4902:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4906:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    490c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    490f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4913:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4919:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4921:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4925:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4928:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    492f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4937:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    493b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    493f:	e8 fc d9 ff ff       	call   2340 <io_uring_submit@plt>
}
    4944:	31 c0                	xor    %eax,%eax
    4946:	48 83 c4 08          	add    $0x8,%rsp
    494a:	c3                   	ret
    494b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004950 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4950:	f3 0f 1e fa          	endbr64
    4954:	41 55                	push   %r13
    4956:	41 89 fd             	mov    %edi,%r13d
    4959:	41 54                	push   %r12
    495b:	55                   	push   %rbp
    495c:	53                   	push   %rbx
    495d:	48 89 f3             	mov    %rsi,%rbx
    4960:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4964:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4967:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    496d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4970:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4973:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4975:	f6 c1 02             	test   $0x2,%cl
    4978:	74 00                	je     497a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    497a:	89 c2                	mov    %eax,%edx
    497c:	29 f2                	sub    %esi,%edx
    497e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4981:	0f 82 eb db ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4987:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    498a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    498d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4990:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4995:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4998:	23 6b 58             	and    0x58(%rbx),%ebp
    499b:	d3 e5                	shl    %cl,%ebp
    499d:	48 c1 e5 06          	shl    $0x6,%rbp
    49a1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    49a5:	e8 66 da ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    49aa:	be 01 00 00 00       	mov    $0x1,%esi
    49af:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    49b4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    49b7:	e8 e4 d9 ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    49bc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    49c1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    49c5:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    49c8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    49cd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    49d2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    49db:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    49e3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    49e7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    49eb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    49f2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    49fa:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    49fe:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4a06:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    4a0e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4a12:	e8 29 d9 ff ff       	call   2340 <io_uring_submit@plt>
}
    4a17:	48 83 c4 08          	add    $0x8,%rsp
    4a1b:	31 c0                	xor    %eax,%eax
    4a1d:	5b                   	pop    %rbx
    4a1e:	5d                   	pop    %rbp
    4a1f:	41 5c                	pop    %r12
    4a21:	41 5d                	pop    %r13
    4a23:	c3                   	ret
    4a24:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4a2f:	90                   	nop

0000000000004a30 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4a30:	f3 0f 1e fa          	endbr64
    4a34:	41 56                	push   %r14
    4a36:	41 89 f6             	mov    %esi,%r14d
    4a39:	41 55                	push   %r13
    4a3b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    4a3e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4a43:	41 54                	push   %r12
    4a45:	55                   	push   %rbp
    4a46:	48 89 d5             	mov    %rdx,%rbp
    4a49:	53                   	push   %rbx
    void *buf = malloc(size);
    4a4a:	e8 c1 d9 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4a4f:	48 85 c0             	test   %rax,%rax
    4a52:	0f 84 dd 00 00 00    	je     4b35 <_send_static_string_content+0x105>
    4a58:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    4a5b:	4c 89 ef             	mov    %r13,%rdi
    4a5e:	e8 bd d8 ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4a63:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    4a6a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    4a6e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4a71:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4a74:	e8 97 d9 ff ff       	call   2410 <malloc@plt>
    4a79:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    4a7c:	48 85 c0             	test   %rax,%rax
    4a7f:	0f 84 b0 00 00 00    	je     4b35 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4a85:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4a89:	4c 89 e2             	mov    %r12,%rdx
    4a8c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    4a8f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4a93:	e8 48 d9 ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4a98:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4a9b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4aa1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4aa4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4aa8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4aaa:	f6 c1 02             	test   $0x2,%cl
    4aad:	0f 85 7d 00 00 00    	jne    4b30 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4ab3:	89 d0                	mov    %edx,%eax
    4ab5:	29 f0                	sub    %esi,%eax
    4ab7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    4aba:	0f 82 bc da ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4ac0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ac3:	8b 45 44             	mov    0x44(%rbp),%eax
    4ac6:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4ac9:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    4acc:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4acf:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4ad2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4ad8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4adc:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4ade:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4ae1:	48 89 ef             	mov    %rbp,%rdi
    4ae4:	48 c1 e0 06          	shl    $0x6,%rax
    4ae8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    4aec:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4aef:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4af3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4af9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4b01:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4b05:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4b08:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    4b0f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4b17:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    4b1b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    4b1f:	5b                   	pop    %rbx
    4b20:	5d                   	pop    %rbp
    4b21:	41 5c                	pop    %r12
    4b23:	41 5d                	pop    %r13
    4b25:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4b27:	e9 14 d8 ff ff       	jmp    2340 <io_uring_submit@plt>
    4b2c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4b30:	e9 7e ff ff ff       	jmp    4ab3 <_send_static_string_content+0x83>
    4b35:	48 8b 0d e4 54 00 00 	mov    0x54e4(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4b3c:	ba 28 00 00 00       	mov    $0x28,%edx
    4b41:	be 01 00 00 00       	mov    $0x1,%esi
    4b46:	48 8d 3d bb 28 00 00 	lea    0x28bb(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4b4d:	e8 6e d9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4b52:	bf 01 00 00 00       	mov    $0x1,%edi
    4b57:	e8 44 d9 ff ff       	call   24a0 <exit@plt>
    4b5c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004b60 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4b60:	f3 0f 1e fa          	endbr64
    4b64:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4b67:	89 fe                	mov    %edi,%esi
    4b69:	48 8b 3d a8 54 00 00 	mov    0x54a8(%rip),%rdi        # a018 <unimplemented_content>
    4b70:	e9 bb fe ff ff       	jmp    4a30 <_send_static_string_content>
    4b75:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004b80 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4b80:	f3 0f 1e fa          	endbr64
    4b84:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4b87:	89 fe                	mov    %edi,%esi
    4b89:	48 8b 3d 80 54 00 00 	mov    0x5480(%rip),%rdi        # a010 <http_404_content>
    4b90:	e9 9b fe ff ff       	jmp    4a30 <_send_static_string_content>
    4b95:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004ba0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4ba0:	f3 0f 1e fa          	endbr64
    4ba4:	41 56                	push   %r14
    4ba6:	41 55                	push   %r13
    4ba8:	49 89 d5             	mov    %rdx,%r13
    4bab:	41 54                	push   %r12
    4bad:	41 89 f4             	mov    %esi,%r12d
    4bb0:	55                   	push   %rbp
    4bb1:	48 89 fd             	mov    %rdi,%rbp
    4bb4:	53                   	push   %rbx
    4bb5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    4bbc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4bc5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    4bcd:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    4bcf:	e8 4c d7 ff ff       	call   2320 <strlen@plt>
    4bd4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4bd9:	48 89 c3             	mov    %rax,%rbx
    4bdc:	0f 84 b6 00 00 00    	je     4c98 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4be2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4be7:	48 89 ee             	mov    %rbp,%rsi
    4bea:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4bee:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4bf3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4bfb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4c03:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4c0e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4c16:	e8 a5 d7 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4c1b:	48 89 e6             	mov    %rsp,%rsi
    4c1e:	4c 89 f7             	mov    %r14,%rdi
    4c21:	e8 aa d7 ff ff       	call   23d0 <stat@plt>
    4c26:	83 f8 ff             	cmp    $0xffffffff,%eax
    4c29:	0f 84 d3 00 00 00    	je     4d02 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    4c2f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4c33:	25 00 f0 00 00       	and    $0xf000,%eax
    4c38:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4c3d:	0f 84 f5 00 00 00    	je     4d38 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4c43:	48 8b 3d c6 53 00 00 	mov    0x53c6(%rip),%rdi        # a010 <http_404_content>
    4c4a:	4c 89 ea             	mov    %r13,%rdx
    4c4d:	44 89 e6             	mov    %r12d,%esi
    4c50:	e8 db fd ff ff       	call   4a30 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4c55:	4c 89 f2             	mov    %r14,%rdx
    4c58:	bf 01 00 00 00       	mov    $0x1,%edi
    4c5d:	31 c0                	xor    %eax,%eax
    4c5f:	48 8d 35 ba 24 00 00 	lea    0x24ba(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    4c66:	e8 e5 d7 ff ff       	call   2450 <__printf_chk@plt>
}
    4c6b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4c73:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4c7c:	0f 85 20 01 00 00    	jne    4da2 <handle_get_method+0x202>
    4c82:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4c89:	5b                   	pop    %rbx
    4c8a:	5d                   	pop    %rbp
    4c8b:	41 5c                	pop    %r12
    4c8d:	41 5d                	pop    %r13
    4c8f:	41 5e                	pop    %r14
    4c91:	c3                   	ret
    4c92:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4c98:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4c9d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4ca5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4caa:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4cad:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4cb5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4cb8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4cc0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4ccb:	e8 f0 d6 ff ff       	call   23c0 <__memcpy_chk@plt>
    4cd0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4cd5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4cda:	48 8d 35 0a 24 00 00 	lea    0x240a(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4ce1:	48 29 d9             	sub    %rbx,%rcx
    4ce4:	ba 0b 00 00 00       	mov    $0xb,%edx
    4ce9:	e8 d2 d6 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4cee:	48 89 e6             	mov    %rsp,%rsi
    4cf1:	4c 89 f7             	mov    %r14,%rdi
    4cf4:	e8 d7 d6 ff ff       	call   23d0 <stat@plt>
    4cf9:	83 f8 ff             	cmp    $0xffffffff,%eax
    4cfc:	0f 85 2d ff ff ff    	jne    4c2f <handle_get_method+0x8f>
    4d02:	4c 89 f2             	mov    %r14,%rdx
    4d05:	48 89 e9             	mov    %rbp,%rcx
    4d08:	48 8d 35 e7 23 00 00 	lea    0x23e7(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    4d0f:	31 c0                	xor    %eax,%eax
    4d11:	bf 01 00 00 00       	mov    $0x1,%edi
    4d16:	e8 35 d7 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    4d1b:	48 8b 3d ee 52 00 00 	mov    0x52ee(%rip),%rdi        # a010 <http_404_content>
    4d22:	4c 89 ea             	mov    %r13,%rdx
    4d25:	44 89 e6             	mov    %r12d,%esi
    4d28:	e8 03 fd ff ff       	call   4a30 <_send_static_string_content>
}
    4d2d:	e9 39 ff ff ff       	jmp    4c6b <handle_get_method+0xcb>
    4d32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4d38:	bf 70 00 00 00       	mov    $0x70,%edi
    4d3d:	e8 ce d6 ff ff       	call   2410 <malloc@plt>
    4d42:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4d45:	48 85 c0             	test   %rax,%rax
    4d48:	74 5d                	je     4da7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    4d4a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4d4e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4d53:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4d57:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    4d5a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4d61:	e8 5a f5 ff ff       	call   42c0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4d66:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4d6b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4d6f:	4c 89 f7             	mov    %r14,%rdi
    4d72:	e8 79 fa ff ff       	call   47f0 <copy_file_contents>
    4d77:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4d7c:	4c 89 f2             	mov    %r14,%rdx
    4d7f:	31 c0                	xor    %eax,%eax
    4d81:	48 8d 35 86 23 00 00 	lea    0x2386(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4d88:	bf 01 00 00 00       	mov    $0x1,%edi
    4d8d:	e8 be d6 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    4d92:	4c 89 ee             	mov    %r13,%rsi
    4d95:	48 89 df             	mov    %rbx,%rdi
    4d98:	e8 13 fb ff ff       	call   48b0 <add_write_request>
    4d9d:	e9 c9 fe ff ff       	jmp    4c6b <handle_get_method+0xcb>
}
    4da2:	e8 89 d5 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4da7:	48 8b 0d 72 52 00 00 	mov    0x5272(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4dae:	ba 28 00 00 00       	mov    $0x28,%edx
    4db3:	be 01 00 00 00       	mov    $0x1,%esi
    4db8:	48 8d 3d 49 26 00 00 	lea    0x2649(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4dbf:	e8 fc d6 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4dc4:	bf 01 00 00 00       	mov    $0x1,%edi
    4dc9:	e8 d2 d6 ff ff       	call   24a0 <exit@plt>
    4dce:	66 90                	xchg   %ax,%ax

0000000000004dd0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4dd0:	f3 0f 1e fa          	endbr64
    4dd4:	41 57                	push   %r15
    4dd6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4dd8:	4c 8d 35 a6 22 00 00 	lea    0x22a6(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4ddf:	41 55                	push   %r13
    4de1:	49 89 d5             	mov    %rdx,%r13
    4de4:	41 54                	push   %r12
    4de6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4de9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4dec:	55                   	push   %rbp
    4ded:	53                   	push   %rbx
    4dee:	48 83 ec 18          	sub    $0x18,%rsp
    4df2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4dfb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4e00:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4e02:	49 89 e7             	mov    %rsp,%r15
    4e05:	4c 89 fa             	mov    %r15,%rdx
    4e08:	e8 73 d5 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4e0d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4e11:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4e14:	84 db                	test   %bl,%bl
    4e16:	74 1d                	je     4e35 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4e18:	e8 f3 d6 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4e1d:	48 89 ea             	mov    %rbp,%rdx
    4e20:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4e23:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4e27:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4e2a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    4e2d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4e31:	84 db                	test   %bl,%bl
    4e33:	75 eb                	jne    4e20 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4e35:	4c 89 fa             	mov    %r15,%rdx
    4e38:	4c 89 f6             	mov    %r14,%rsi
    4e3b:	31 ff                	xor    %edi,%edi
    4e3d:	e8 3e d5 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4e42:	48 8d 35 ea 22 00 00 	lea    0x22ea(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4e49:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4e4c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    4e4f:	e8 5c d5 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4e54:	4c 89 ea             	mov    %r13,%rdx
    4e57:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4e5a:	85 c0                	test   %eax,%eax
    4e5c:	75 2a                	jne    4e88 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    4e5e:	48 89 df             	mov    %rbx,%rdi
    4e61:	e8 3a fd ff ff       	call   4ba0 <handle_get_method>
}
    4e66:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4e6b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4e74:	75 20                	jne    4e96 <handle_http_method+0xc6>
    4e76:	48 83 c4 18          	add    $0x18,%rsp
    4e7a:	5b                   	pop    %rbx
    4e7b:	5d                   	pop    %rbp
    4e7c:	41 5c                	pop    %r12
    4e7e:	41 5d                	pop    %r13
    4e80:	41 5e                	pop    %r14
    4e82:	41 5f                	pop    %r15
    4e84:	c3                   	ret
    4e85:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4e88:	48 8b 3d 89 51 00 00 	mov    0x5189(%rip),%rdi        # a018 <unimplemented_content>
    4e8f:	e8 9c fb ff ff       	call   4a30 <_send_static_string_content>
}
    4e94:	eb d0                	jmp    4e66 <handle_http_method+0x96>
    4e96:	e8 95 d4 ff ff       	call   2330 <__stack_chk_fail@plt>
    4e9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004ea0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4ea0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4ea4:	85 d2                	test   %edx,%edx
    4ea6:	7e 38                	jle    4ee0 <get_line+0x40>
    4ea8:	48 63 d2             	movslq %edx,%rdx
    4eab:	48 83 c7 01          	add    $0x1,%rdi
    4eaf:	48 01 f2             	add    %rsi,%rdx
    4eb2:	eb 11                	jmp    4ec5 <get_line+0x25>
    4eb4:	0f 1f 40 00          	nopl   0x0(%rax)
    4eb8:	48 83 c6 01          	add    $0x1,%rsi
    4ebc:	48 83 c7 01          	add    $0x1,%rdi
    4ec0:	48 39 d6             	cmp    %rdx,%rsi
    4ec3:	74 1b                	je     4ee0 <get_line+0x40>
        dest[i] = src[i];
    4ec5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4ec9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4ecb:	3c 0d                	cmp    $0xd,%al
    4ecd:	75 e9                	jne    4eb8 <get_line+0x18>
    4ecf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4ed2:	75 e4                	jne    4eb8 <get_line+0x18>
            dest[i] = '\0';
    4ed4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4ed7:	31 c0                	xor    %eax,%eax
    4ed9:	c3                   	ret
    4eda:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4ee0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4ee5:	c3                   	ret
    4ee6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004ef0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4ef0:	f3 0f 1e fa          	endbr64
    4ef4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4efb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4eff:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4f08:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4f10:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4f12:	49 89 e2             	mov    %rsp,%r10
    4f15:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4f1d:	4c 89 d0             	mov    %r10,%rax
    4f20:	eb 13                	jmp    4f35 <handle_client_request+0x45>
    4f22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4f28:	48 83 c0 01          	add    $0x1,%rax
    4f2c:	48 83 c1 01          	add    $0x1,%rcx
    4f30:	4c 39 c8             	cmp    %r9,%rax
    4f33:	74 4b                	je     4f80 <handle_client_request+0x90>
        dest[i] = src[i];
    4f35:	44 0f b6 01          	movzbl (%rcx),%r8d
    4f39:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4f3c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4f40:	75 e6                	jne    4f28 <handle_client_request+0x38>
    4f42:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4f46:	75 e0                	jne    4f28 <handle_client_request+0x38>
            dest[i] = '\0';
    4f48:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4f4b:	8b 47 08             	mov    0x8(%rdi),%eax
    4f4e:	48 89 f2             	mov    %rsi,%rdx
    4f51:	4c 89 d7             	mov    %r10,%rdi
    4f54:	89 c6                	mov    %eax,%esi
    4f56:	e8 75 fe ff ff       	call   4dd0 <handle_http_method>
}
    4f5b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4f63:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4f6c:	75 39                	jne    4fa7 <handle_client_request+0xb7>
    4f6e:	31 c0                	xor    %eax,%eax
    4f70:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4f77:	c3                   	ret
    4f78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4f80:	48 8b 0d 99 50 00 00 	mov    0x5099(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4f87:	ba 12 00 00 00       	mov    $0x12,%edx
    4f8c:	be 01 00 00 00       	mov    $0x1,%esi
    4f91:	48 8d 3d 9f 21 00 00 	lea    0x219f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4f98:	e8 23 d5 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4f9d:	bf 01 00 00 00       	mov    $0x1,%edi
    4fa2:	e8 f9 d4 ff ff       	call   24a0 <exit@plt>
}
    4fa7:	e8 84 d3 ff ff       	call   2330 <__stack_chk_fail@plt>
    4fac:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004fb0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4fb0:	f3 0f 1e fa          	endbr64
    4fb4:	55                   	push   %rbp
    4fb5:	53                   	push   %rbx
    4fb6:	48 89 cb             	mov    %rcx,%rbx
    4fb9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4fbd:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4fc0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4fc3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4fc9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4fcc:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4fcf:	f6 c1 02             	test   $0x2,%cl
    4fd2:	74 00                	je     4fd4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4fd4:	41 89 c0             	mov    %eax,%r8d
    4fd7:	45 29 c8             	sub    %r9d,%r8d
    4fda:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4fde:	0f 82 a8 d5 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4fe4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4fe7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4fea:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4fed:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4ff0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4ff3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ff7:	d3 e5                	shl    %cl,%ebp
    4ff9:	48 c1 e5 06          	shl    $0x6,%rbp
    4ffd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5001:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5004:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5009:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5010:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5014:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5018:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    5020:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    5028:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    502c:	e8 df d3 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    5031:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5034:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    503a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    503e:	48 83 c4 08          	add    $0x8,%rsp
    5042:	5b                   	pop    %rbx
    5043:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5044:	e9 f7 d2 ff ff       	jmp    2340 <io_uring_submit@plt>
    5049:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005050 <io_thread>:
void* io_thread(void *arg) {
    5050:	f3 0f 1e fa          	endbr64
    5054:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5056:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5058:	41 56                	push   %r14
    505a:	41 55                	push   %r13
    505c:	41 54                	push   %r12
    505e:	55                   	push   %rbp
    505f:	48 89 fd             	mov    %rdi,%rbp
    5062:	53                   	push   %rbx
    5063:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    506a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5073:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    507b:	48 8b 87 88 01 00 00 	mov    0x188(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5082:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5087:	bf 00 01 00 00       	mov    $0x100,%edi
    508c:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    508f:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5093:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5098:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    509d:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    50a2:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    50a7:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    50af:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    50b4:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    50bc:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    50c1:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    50c9:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    50ce:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    50d6:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    50db:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    50e3:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    50e8:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    50f0:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    50f8:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    5100:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5108:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    5110:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5118:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5120:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5128:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5130:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5138:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5140:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5147:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    514f:	e8 9c d2 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5154:	48 8b bd 88 01 00 00 	mov    0x188(%rbp),%rdi
    515b:	31 f6                	xor    %esi,%esi
    515d:	e8 7e d3 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    5162:	31 d2                	xor    %edx,%edx
    5164:	be 01 00 00 00       	mov    $0x1,%esi
    5169:	bf 02 00 00 00       	mov    $0x2,%edi
    516e:	e8 bd d3 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    5173:	83 f8 ff             	cmp    $0xffffffff,%eax
    5176:	0f 84 52 d4 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    517c:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5181:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5187:	89 c7                	mov    %eax,%edi
    5189:	41 89 c4             	mov    %eax,%r12d
    518c:	ba 02 00 00 00       	mov    $0x2,%edx
    5191:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5196:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    519e:	e8 5d d1 ff ff       	call   2300 <setsockopt@plt>
    51a3:	85 c0                	test   %eax,%eax
    51a5:	0f 88 f7 d3 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    51ab:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    51b0:	ba 10 00 00 00       	mov    $0x10,%edx
    51b5:	44 89 e7             	mov    %r12d,%edi
    51b8:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    51c1:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    51c9:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    51d1:	e8 8a d2 ff ff       	call   2460 <bind@plt>
    51d6:	85 c0                	test   %eax,%eax
    51d8:	0f 88 fc d3 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    51de:	be 0a 00 00 00       	mov    $0xa,%esi
    51e3:	44 89 e7             	mov    %r12d,%edi
    51e6:	e8 35 d2 ff ff       	call   2420 <listen@plt>
    51eb:	85 c0                	test   %eax,%eax
    51ed:	0f 88 bb d3 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    51f3:	ba db 18 00 00       	mov    $0x18db,%edx
    51f8:	48 8d 35 7d 1f 00 00 	lea    0x1f7d(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    51ff:	bf 01 00 00 00       	mov    $0x1,%edi
    5204:	31 c0                	xor    %eax,%eax
    5206:	e8 45 d2 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    520b:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5210:	48 89 d9             	mov    %rbx,%rcx
    5213:	44 89 e7             	mov    %r12d,%edi
    5216:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    521b:	48 89 c6             	mov    %rax,%rsi
    521e:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5223:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5228:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5230:	e8 7b fd ff ff       	call   4fb0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5235:	bf 01 00 00 00       	mov    $0x1,%edi
    523a:	be 10 00 00 00       	mov    $0x10,%esi
    523f:	e8 5c d1 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    5244:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5249:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    524c:	e8 bf d1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    5251:	48 85 c0             	test   %rax,%rax
    5254:	0f 84 c8 04 00 00    	je     5722 <io_thread+0x6d2>
  iov->iov_base = zh_malloc(10);
    525a:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    525e:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5265:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    526c:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5274:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5277:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    527c:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    527e:	f6 c1 02             	test   $0x2,%cl
    5281:	0f 85 29 04 00 00    	jne    56b0 <io_thread+0x660>
	if (next - head <= sq->ring_entries) {
    5287:	89 d0                	mov    %edx,%eax
    5289:	29 f0                	sub    %esi,%eax
    528b:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5292:	0f 82 2c d3 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5298:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    529b:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	sqe->addr3 = 0;
    52a2:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    52a6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52a9:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    52b0:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    52b3:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    52ba:	48 8d b5 90 01 00 00 	lea    0x190(%rbp),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    52c1:	8b 95 90 01 00 00    	mov    0x190(%rbp),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52c7:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    52c9:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    52ce:	48 c1 e0 06          	shl    $0x6,%rax
    52d2:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    52da:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    52e0:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    52e3:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    52eb:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    52ef:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    52f7:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    52ff:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5303:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5307:	e8 34 d0 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    530c:	83 bd a4 00 00 00 01 	cmpl   $0x1,0xa4(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5313:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5318:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5320:	0f 85 de 01 00 00    	jne    5504 <io_thread+0x4b4>
    5326:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    532b:	4d 89 ce             	mov    %r9,%r14
    532e:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5333:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5338:	48 8d 3d 53 1e 00 00 	lea    0x1e53(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    533f:	e8 ac cf ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5344:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    534b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5352:	c1 e9 0b             	shr    $0xb,%ecx
    5355:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5358:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5360:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5362:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    536a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    536c:	39 d0                	cmp    %edx,%eax
    536e:	74 36                	je     53a6 <io_thread+0x356>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5370:	89 f8                	mov    %edi,%eax
    5372:	21 d0                	and    %edx,%eax
    5374:	d3 e0                	shl    %cl,%eax
    5376:	48 c1 e0 04          	shl    $0x4,%rax
    537a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5382:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    538a:	0f 85 b0 01 00 00    	jne    5540 <io_thread+0x4f0>
    5390:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5394:	0f 85 1e 03 00 00    	jne    56b8 <io_thread+0x668>
			if (cqe->res < 0)
    539a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    539d:	83 c2 01             	add    $0x1,%edx
    53a0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    53a2:	85 c0                	test   %eax,%eax
    53a4:	79 b2                	jns    5358 <io_thread+0x308>
	*cqe_ptr = cqe;
    53a6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    53af:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    53b0:	45 31 c0             	xor    %r8d,%r8d
    53b3:	31 d2                	xor    %edx,%edx
    53b5:	b9 01 00 00 00       	mov    $0x1,%ecx
    53ba:	4c 89 f6             	mov    %r14,%rsi
    53bd:	48 89 df             	mov    %rbx,%rdi
    53c0:	e8 7b d0 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    53c5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    53c8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    53cd:	48 83 38 01          	cmpq   $0x1,(%rax)
    53d1:	0f 84 f1 02 00 00    	je     56c8 <io_thread+0x678>
    53d7:	48 8d 3d da 1d 00 00 	lea    0x1dda(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    53de:	e8 0d cf ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    53e3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    53e8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    53eb:	45 85 ff             	test   %r15d,%r15d
    53ee:	0f 88 a2 d1 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    53f4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    53f7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    53fb:	85 c0                	test   %eax,%eax
    53fd:	0f 88 e5 02 00 00    	js     56e8 <io_thread+0x698>
      switch (req->event_type) {
    5403:	41 83 f8 01          	cmp    $0x1,%r8d
    5407:	0f 84 83 01 00 00    	je     5590 <io_thread+0x540>
    540d:	41 83 f8 02          	cmp    $0x2,%r8d
    5411:	0f 84 a9 01 00 00    	je     55c0 <io_thread+0x570>
    5417:	45 85 c0             	test   %r8d,%r8d
    541a:	0f 85 58 01 00 00    	jne    5578 <io_thread+0x528>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5420:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5425:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    542a:	48 89 d9             	mov    %rbx,%rcx
    542d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5431:	e8 7a fb ff ff       	call   4fb0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5436:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    543b:	48 89 de             	mov    %rbx,%rsi
    543e:	8b 78 08             	mov    0x8(%rax),%edi
    5441:	e8 0a f5 ff ff       	call   4950 <add_read_request>
              free(req);
    5446:	4c 89 e7             	mov    %r12,%rdi
    5449:	e8 72 ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    544e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5453:	48 85 c0             	test   %rax,%rax
    5456:	0f 85 1c 01 00 00    	jne    5578 <io_thread+0x528>
	unsigned int head, next = sq->sqe_tail + 1;
    545c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5463:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    546a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    546d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5472:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5474:	f6 c1 02             	test   $0x2,%cl
    5477:	74 00                	je     5479 <io_thread+0x429>
	if (next - head <= sq->ring_entries) {
    5479:	89 d0                	mov    %edx,%eax
    547b:	29 f0                	sub    %esi,%eax
    547d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5484:	0f 82 30 d1 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    548a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    548d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5492:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5496:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5499:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    54a0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    54a3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    54aa:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    54b1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    54b3:	8b 95 90 01 00 00    	mov    0x190(%rbp),%edx
    54b9:	48 c1 e0 06          	shl    $0x6,%rax
    54bd:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    54c5:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    54cb:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    54ce:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    54d6:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    54da:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    54e2:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    54ea:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    54ee:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    54f2:	e8 49 ce ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    54f7:	83 bd a4 00 00 00 01 	cmpl   $0x1,0xa4(%rbp)
    54fe:	0f 84 34 fe ff ff    	je     5338 <io_thread+0x2e8>
    5504:	48 8d 3d e6 1c 00 00 	lea    0x1ce6(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    550b:	e8 e0 cd ff ff       	call   22f0 <puts@plt>
}
    5510:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5518:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5521:	0f 85 22 02 00 00    	jne    5749 <io_thread+0x6f9>
    5527:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    552e:	31 c0                	xor    %eax,%eax
    5530:	5b                   	pop    %rbx
    5531:	5d                   	pop    %rbp
    5532:	41 5c                	pop    %r12
    5534:	41 5d                	pop    %r13
    5536:	41 5e                	pop    %r14
    5538:	41 5f                	pop    %r15
    553a:	c3                   	ret
    553b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    5540:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5545:	48 85 c0             	test   %rax,%rax
    5548:	0f 84 62 fe ff ff    	je     53b0 <io_thread+0x360>
      if (cqe->user_data == 1) {
    554e:	48 83 38 01          	cmpq   $0x1,(%rax)
    5552:	0f 84 70 01 00 00    	je     56c8 <io_thread+0x678>
    5558:	48 8d 3d 59 1c 00 00 	lea    0x1c59(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    555f:	e8 8c cd ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5564:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5569:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    556c:	e9 83 fe ff ff       	jmp    53f4 <io_thread+0x3a4>
    5571:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5578:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5580:	8b 02                	mov    (%rdx),%eax
    5582:	83 c0 01             	add    $0x1,%eax
    5585:	89 02                	mov    %eax,(%rdx)
}
    5587:	e9 d0 fe ff ff       	jmp    545c <io_thread+0x40c>
    558c:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5590:	85 c0                	test   %eax,%eax
    5592:	75 7c                	jne    5610 <io_thread+0x5c0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5594:	48 8b 0d 85 4a 00 00 	mov    0x4a85(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    559b:	ba 0f 00 00 00       	mov    $0xf,%edx
    55a0:	be 01 00 00 00       	mov    $0x1,%esi
    55a5:	48 8d 3d 35 1c 00 00 	lea    0x1c35(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    55ac:	e8 0f cf ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    55b1:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    55b6:	e9 98 fe ff ff       	jmp    5453 <io_thread+0x403>
    55bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    55c0:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    55c5:	45 31 ff             	xor    %r15d,%r15d
    55c8:	85 c0                	test   %eax,%eax
    55ca:	7e 20                	jle    55ec <io_thread+0x59c>
    55cc:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    55d0:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    55d3:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    55d7:	48 c1 e0 04          	shl    $0x4,%rax
    55db:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    55e0:	e8 db cc ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    55e5:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    55ea:	7f e4                	jg     55d0 <io_thread+0x580>
              close(req->client_socket);
    55ec:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    55f1:	e8 7a cd ff ff       	call   2370 <close@plt>
              free(req);
    55f6:	4c 89 e7             	mov    %r12,%rdi
    55f9:	e8 c2 cc ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    55fe:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5603:	e9 4b fe ff ff       	jmp    5453 <io_thread+0x403>
    5608:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int i = 0; i < dest_sz; i++) {
    5610:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5615:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    561a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5622:	eb 11                	jmp    5635 <io_thread+0x5e5>
    5624:	0f 1f 40 00          	nopl   0x0(%rax)
    5628:	48 83 c0 01          	add    $0x1,%rax
    562c:	48 83 c2 01          	add    $0x1,%rdx
    5630:	48 39 c6             	cmp    %rax,%rsi
    5633:	74 4b                	je     5680 <io_thread+0x630>
        dest[i] = src[i];
    5635:	0f b6 0a             	movzbl (%rdx),%ecx
    5638:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    563a:	80 f9 0d             	cmp    $0xd,%cl
    563d:	75 e9                	jne    5628 <io_thread+0x5d8>
    563f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5643:	75 e3                	jne    5628 <io_thread+0x5d8>
            dest[i] = '\0';
    5645:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5648:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    564d:	48 89 da             	mov    %rbx,%rdx
    5650:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5655:	e8 76 f7 ff ff       	call   4dd0 <handle_http_method>
              free(req->iov[0].iov_base);
    565a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    565f:	e8 5c cc ff ff       	call   22c0 <free@plt>
              free(req);
    5664:	4c 89 e7             	mov    %r12,%rdi
    5667:	e8 54 cc ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    566c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5671:	e9 dd fd ff ff       	jmp    5453 <io_thread+0x403>
    5676:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5680:	48 8b 0d 99 49 00 00 	mov    0x4999(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5687:	ba 12 00 00 00       	mov    $0x12,%edx
    568c:	be 01 00 00 00       	mov    $0x1,%esi
    5691:	48 8d 3d 9f 1a 00 00 	lea    0x1a9f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5698:	e8 23 ce ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    569d:	bf 01 00 00 00       	mov    $0x1,%edi
    56a2:	e8 f9 cd ff ff       	call   24a0 <exit@plt>
    56a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    56b0:	e9 d2 fb ff ff       	jmp    5287 <io_thread+0x237>
    56b5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    56b8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    56bd:	e9 8c fe ff ff       	jmp    554e <io_thread+0x4fe>
    56c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    56c8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    56d0:	48 8d 3d cd 1a 00 00 	lea    0x1acd(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    56d7:	8b 02                	mov    (%rdx),%eax
    56d9:	83 c0 01             	add    $0x1,%eax
    56dc:	89 02                	mov    %eax,(%rdx)
    56de:	e8 0d cc ff ff       	call   22f0 <puts@plt>
    56e3:	e9 1c fe ff ff       	jmp    5504 <io_thread+0x4b4>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    56e8:	f7 d8                	neg    %eax
    56ea:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    56ef:	89 c7                	mov    %eax,%edi
    56f1:	e8 0a ce ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    56f6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    56fb:	be 01 00 00 00       	mov    $0x1,%esi
    5700:	48 8b 3d 19 49 00 00 	mov    0x4919(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5707:	48 89 c1             	mov    %rax,%rcx
    570a:	48 8d 15 27 1d 00 00 	lea    0x1d27(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    5711:	31 c0                	xor    %eax,%eax
    5713:	e8 b8 cd ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5718:	bf 01 00 00 00       	mov    $0x1,%edi
    571d:	e8 7e cd ff ff       	call   24a0 <exit@plt>
    5722:	48 8b 0d f7 48 00 00 	mov    0x48f7(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5729:	ba 28 00 00 00       	mov    $0x28,%edx
    572e:	be 01 00 00 00       	mov    $0x1,%esi
    5733:	48 8d 3d ce 1c 00 00 	lea    0x1cce(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    573a:	e8 81 cd ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    573f:	bf 01 00 00 00       	mov    $0x1,%edi
    5744:	e8 57 cd ff ff       	call   24a0 <exit@plt>
}
    5749:	e8 e2 cb ff ff       	call   2330 <__stack_chk_fail@plt>
    574e:	66 90                	xchg   %ax,%ax

0000000000005750 <sendm>:
int sendm(struct BarrierTask *data) {
    5750:	f3 0f 1e fa          	endbr64
    5754:	41 57                	push   %r15
    5756:	41 56                	push   %r14
    5758:	41 55                	push   %r13
    575a:	41 54                	push   %r12
    575c:	55                   	push   %rbp
    575d:	53                   	push   %rbx
    575e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5762:	83 bf 08 04 00 00 01 	cmpl   $0x1,0x408(%rdi)
    5769:	0f 85 a9 01 00 00    	jne    5918 <sendm+0x1c8>
    576f:	48 8d b7 10 04 00 00 	lea    0x410(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5776:	8b 87 24 02 00 00    	mov    0x224(%rdi),%eax
    577c:	48 89 fa             	mov    %rdi,%rdx
    577f:	31 c9                	xor    %ecx,%ecx
    5781:	48 89 34 24          	mov    %rsi,(%rsp)
    5785:	48 8d b7 18 04 00 00 	lea    0x418(%rdi),%rsi
    578c:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5791:	85 c0                	test   %eax,%eax
    5793:	0f 8e e4 00 00 00    	jle    587d <sendm+0x12d>
    5799:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    57a0:	39 8a 20 02 00 00    	cmp    %ecx,0x220(%rdx)
    57a6:	0f 84 c5 00 00 00    	je     5871 <sendm+0x121>
        struct Data *them = data->mailboxes[n].higher;
    57ac:	49 89 ca             	mov    %rcx,%r10
    57af:	49 c1 e2 09          	shl    $0x9,%r10
    57b3:	4c 03 92 88 03 00 00 	add    0x388(%rdx),%r10
    57ba:	4d 8b 9a 80 00 00 00 	mov    0x80(%r10),%r11
        for (; them->messages_count < min;) {
    57c1:	49 8b 9b 80 00 00 00 	mov    0x80(%r11),%rbx
    57c8:	4d 63 8b 88 00 00 00 	movslq 0x88(%r11),%r9
    57cf:	4c 39 cb             	cmp    %r9,%rbx
    57d2:	0f 8d 90 00 00 00    	jge    5868 <sendm+0x118>
    57d8:	4c 89 cf             	mov    %r9,%rdi
    57db:	48 8b aa 80 01 00 00 	mov    0x180(%rdx),%rbp
    57e2:	4d 8b b2 00 01 00 00 	mov    0x100(%r10),%r14
    57e9:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    57ec:	49 8b 33             	mov    (%r11),%rsi
    57ef:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    57f3:	48 83 f8 02          	cmp    $0x2,%rax
    57f7:	0f 86 03 01 00 00    	jbe    5900 <sendm+0x1b0>
    57fd:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5805:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    580d:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    5811:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    5815:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5819:	73 75                	jae    5890 <sendm+0x140>
    581b:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5820:	4d 39 fc             	cmp    %r15,%r12
    5823:	73 6b                	jae    5890 <sendm+0x140>
    5825:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    5829:	49 01 f0             	add    %rsi,%r8
    582c:	0f 1f 40 00          	nopl   0x0(%rax)
    5830:	48 8b 82 10 04 00 00 	mov    0x410(%rdx),%rax
        for (; them->messages_count < min;) {
    5837:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    583b:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    583f:	49 39 d8             	cmp    %rbx,%r8
    5842:	75 ec                	jne    5830 <sendm+0xe0>
    5844:	0f 1f 40 00          	nopl   0x0(%rax)
    5848:	48 01 fd             	add    %rdi,%rbp
    584b:	4c 01 f7             	add    %r14,%rdi
    584e:	48 89 aa 80 01 00 00 	mov    %rbp,0x180(%rdx)
    5855:	49 89 ba 00 01 00 00 	mov    %rdi,0x100(%r10)
    585c:	4d 89 8b 80 00 00 00 	mov    %r9,0x80(%r11)
    5863:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5868:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    586b:	8b 82 24 02 00 00    	mov    0x224(%rdx),%eax
    5871:	48 83 c1 01          	add    $0x1,%rcx
    5875:	39 c8                	cmp    %ecx,%eax
    5877:	0f 8f 23 ff ff ff    	jg     57a0 <sendm+0x50>
}
    587d:	48 83 c4 18          	add    $0x18,%rsp
    5881:	31 c0                	xor    %eax,%eax
    5883:	5b                   	pop    %rbx
    5884:	5d                   	pop    %rbp
    5885:	41 5c                	pop    %r12
    5887:	41 5d                	pop    %r13
    5889:	41 5e                	pop    %r14
    588b:	41 5f                	pop    %r15
    588d:	c3                   	ret
    588e:	66 90                	xchg   %ax,%ax
    5890:	49 89 fd             	mov    %rdi,%r13
    5893:	48 8b 82 10 04 00 00 	mov    0x410(%rdx),%rax
    589a:	4d 89 e0             	mov    %r12,%r8
    589d:	49 d1 ed             	shr    %r13
    58a0:	49 c1 e5 04          	shl    $0x4,%r13
    58a4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    58a9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    58ad:	41 83 e5 10          	and    $0x10,%r13d
    58b1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    58b5:	74 11                	je     58c8 <sendm+0x178>
          them->messages[them->messages_count++] = data->message; 
    58b7:	49 83 c0 10          	add    $0x10,%r8
    58bb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    58c0:	4d 39 f8             	cmp    %r15,%r8
    58c3:	74 15                	je     58da <sendm+0x18a>
    58c5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    58c8:	41 0f 11 00          	movups %xmm0,(%r8)
    58cc:	49 83 c0 20          	add    $0x20,%r8
    58d0:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    58d5:	4d 39 f8             	cmp    %r15,%r8
    58d8:	75 ee                	jne    58c8 <sendm+0x178>
    58da:	49 89 f8             	mov    %rdi,%r8
    58dd:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    58e1:	49 01 d8             	add    %rbx,%r8
    58e4:	40 f6 c7 01          	test   $0x1,%dil
    58e8:	0f 84 5a ff ff ff    	je     5848 <sendm+0xf8>
          them->messages[them->messages_count++] = data->message; 
    58ee:	48 8b 82 10 04 00 00 	mov    0x410(%rdx),%rax
    58f5:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    58f9:	e9 4a ff ff ff       	jmp    5848 <sendm+0xf8>
    58fe:	66 90                	xchg   %ax,%ax
    5900:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5908:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5910:	e9 10 ff ff ff       	jmp    5825 <sendm+0xd5>
    5915:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5918:	48 8d 3d e5 18 00 00 	lea    0x18e5(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    591f:	e8 cc c9 ff ff       	call   22f0 <puts@plt>
    5924:	e9 54 ff ff ff       	jmp    587d <sendm+0x12d>
    5929:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005930 <receive>:
int receive(struct BarrierTask *data) {
    5930:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5934:	8b 87 24 02 00 00    	mov    0x224(%rdi),%eax
    593a:	85 c0                	test   %eax,%eax
    593c:	0f 8e fc 00 00 00    	jle    5a3e <receive+0x10e>
int receive(struct BarrierTask *data) {
    5942:	41 54                	push   %r12
    5944:	48 89 fa             	mov    %rdi,%rdx
    5947:	55                   	push   %rbp
    5948:	31 ed                	xor    %ebp,%ebp
    594a:	53                   	push   %rbx
    594b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5950:	48 89 ee             	mov    %rbp,%rsi
    5953:	48 c1 e6 09          	shl    $0x9,%rsi
    5957:	48 03 b2 88 03 00 00 	add    0x388(%rdx),%rsi
    595e:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5961:	49 8b bc 24 80 00 00 00 	mov    0x80(%r12),%rdi
    5969:	48 85 ff             	test   %rdi,%rdi
    596c:	0f 8e a6 00 00 00    	jle    5a18 <receive+0xe8>
      data->sends++;
    5972:	48 8b 8a 00 04 00 00 	mov    0x400(%rdx),%rcx
    5979:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    597d:	4c 63 1a             	movslq (%rdx),%r11
    5980:	49 89 c9             	mov    %rcx,%r9
    5983:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5987:	49 f7 d9             	neg    %r9
    598a:	48 01 c7             	add    %rax,%rdi
    598d:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    5991:	4c 8b 8a 80 01 00 00 	mov    0x180(%rdx),%r9
      data->mailboxes[n].received++;
    5998:	4c 8b 86 80 01 00 00 	mov    0x180(%rsi),%r8
      data->n++;
    599f:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    59a2:	49 29 c8             	sub    %rcx,%r8
    59a5:	eb 12                	jmp    59b9 <receive+0x89>
    59a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    59b0:	48 83 c0 01          	add    $0x1,%rax
    59b4:	48 39 c7             	cmp    %rax,%rdi
    59b7:	74 5f                	je     5a18 <receive+0xe8>
      data->n++;
    59b9:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    59bd:	48 89 82 00 04 00 00 	mov    %rax,0x400(%rdx)
      data->n++;
    59c4:	48 89 8a 80 01 00 00 	mov    %rcx,0x180(%rdx)
      data->mailboxes[n].received++;
    59cb:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    59cf:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    59d6:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    59db:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    59df:	75 cf                	jne    59b0 <receive+0x80>
    59e1:	48 63 9a 20 02 00 00 	movslq 0x220(%rdx),%rbx
    59e8:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    59ec:	75 c2                	jne    59b0 <receive+0x80>
    59ee:	bf 01 00 00 00       	mov    $0x1,%edi
    59f3:	b9 01 00 00 00       	mov    $0x1,%ecx
    59f8:	ba 01 00 00 00       	mov    $0x1,%edx
    59fd:	31 c0                	xor    %eax,%eax
    59ff:	48 8d 35 5a 1a 00 00 	lea    0x1a5a(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    5a06:	e8 45 ca ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5a0b:	bf 01 00 00 00       	mov    $0x1,%edi
    5a10:	e8 8b ca ff ff       	call   24a0 <exit@plt>
    5a15:	0f 1f 00             	nopl   (%rax)
    me->messages_count = 0;
    5a18:	49 c7 84 24 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%r12)
    asm volatile ("sfence" ::: "memory");
    5a24:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    5a27:	48 83 c5 01          	add    $0x1,%rbp
    5a2b:	39 aa 24 02 00 00    	cmp    %ebp,0x224(%rdx)
    5a31:	0f 8f 19 ff ff ff    	jg     5950 <receive+0x20>
}
    5a37:	5b                   	pop    %rbx
    5a38:	31 c0                	xor    %eax,%eax
    5a3a:	5d                   	pop    %rbp
    5a3b:	41 5c                	pop    %r12
    5a3d:	c3                   	ret
    5a3e:	31 c0                	xor    %eax,%eax
    5a40:	c3                   	ret
    5a41:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5a4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005a50 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5a50:	f3 0f 1e fa          	endbr64
    5a54:	41 57                	push   %r15
    5a56:	41 56                	push   %r14
    5a58:	41 55                	push   %r13
    5a5a:	41 54                	push   %r12
    5a5c:	55                   	push   %rbp
    5a5d:	53                   	push   %rbx
    5a5e:	48 89 fb             	mov    %rdi,%rbx
    5a61:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    5a65:	8b 07                	mov    (%rdi),%eax
    5a67:	39 87 20 02 00 00    	cmp    %eax,0x220(%rdi)
    5a6d:	0f 84 4d 01 00 00    	je     5bc0 <barriered_work+0x170>
    receive(data);
    5a73:	e8 b8 fe ff ff       	call   5930 <receive>
    while (data->scheduled == 1) {
    5a78:	83 bb 80 02 00 00 01 	cmpl   $0x1,0x280(%rbx)
    5a7f:	75 1b                	jne    5a9c <barriered_work+0x4c>
    5a81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    5a88:	48 83 83 80 01 00 00 01 	addq   $0x1,0x180(%rbx)
      asm volatile ("sfence" ::: "memory");
    5a90:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5a93:	83 bb 80 02 00 00 01 	cmpl   $0x1,0x280(%rbx)
    5a9a:	74 ec                	je     5a88 <barriered_work+0x38>
  if (data->sending == 1) {
    5a9c:	83 bb 08 04 00 00 01 	cmpl   $0x1,0x408(%rbx)
    5aa3:	0f 85 b4 02 00 00    	jne    5d5d <barriered_work+0x30d>
      for (int n = 0 ; n < data->thread_count; n++) {
    5aa9:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    5aaf:	85 c0                	test   %eax,%eax
    5ab1:	0f 8e b2 02 00 00    	jle    5d69 <barriered_work+0x319>
    5ab7:	48 8d 8b 10 04 00 00 	lea    0x410(%rbx),%rcx
    5abe:	31 d2                	xor    %edx,%edx
    5ac0:	48 89 0c 24          	mov    %rcx,(%rsp)
    5ac4:	48 8d 8b 18 04 00 00 	lea    0x418(%rbx),%rcx
    5acb:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    5ad0:	39 93 20 02 00 00    	cmp    %edx,0x220(%rbx)
    5ad6:	0f 84 cd 00 00 00    	je     5ba9 <barriered_work+0x159>
        struct Data *them = data->mailboxes[n].higher;
    5adc:	49 89 d1             	mov    %rdx,%r9
    5adf:	49 c1 e1 09          	shl    $0x9,%r9
    5ae3:	4c 03 8b 88 03 00 00 	add    0x388(%rbx),%r9
    5aea:	4d 8b 91 80 00 00 00 	mov    0x80(%r9),%r10
        for (; them->messages_count < min;) {
    5af1:	4d 8b 9a 80 00 00 00 	mov    0x80(%r10),%r11
    5af8:	4d 63 82 88 00 00 00 	movslq 0x88(%r10),%r8
    5aff:	4d 39 c3             	cmp    %r8,%r11
    5b02:	0f 8d 98 00 00 00    	jge    5ba0 <barriered_work+0x150>
    5b08:	4c 89 c6             	mov    %r8,%rsi
    5b0b:	48 8b ab 80 01 00 00 	mov    0x180(%rbx),%rbp
    5b12:	4d 8b b1 00 01 00 00 	mov    0x100(%r9),%r14
    5b19:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5b1c:	49 8b 0a             	mov    (%r10),%rcx
    5b1f:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5b23:	48 83 f8 02          	cmp    $0x2,%rax
    5b27:	0f 86 c3 02 00 00    	jbe    5df0 <barriered_work+0x3a0>
    5b2d:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5b35:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5b3d:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5b41:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5b45:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5b49:	0f 83 31 02 00 00    	jae    5d80 <barriered_work+0x330>
    5b4f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5b54:	4d 39 fc             	cmp    %r15,%r12
    5b57:	0f 83 23 02 00 00    	jae    5d80 <barriered_work+0x330>
    5b5d:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5b61:	48 01 cf             	add    %rcx,%rdi
    5b64:	0f 1f 40 00          	nopl   0x0(%rax)
    5b68:	48 8b 83 10 04 00 00 	mov    0x410(%rbx),%rax
        for (; them->messages_count < min;) {
    5b6f:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5b73:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5b77:	49 39 fb             	cmp    %rdi,%r11
    5b7a:	75 ec                	jne    5b68 <barriered_work+0x118>
    5b7c:	0f 1f 40 00          	nopl   0x0(%rax)
    5b80:	48 01 f5             	add    %rsi,%rbp
    5b83:	4c 01 f6             	add    %r14,%rsi
    5b86:	48 89 ab 80 01 00 00 	mov    %rbp,0x180(%rbx)
    5b8d:	49 89 b1 00 01 00 00 	mov    %rsi,0x100(%r9)
    5b94:	4d 89 82 80 00 00 00 	mov    %r8,0x80(%r10)
    5b9b:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5ba0:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5ba3:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    5ba9:	48 83 c2 01          	add    $0x1,%rdx
    5bad:	39 d0                	cmp    %edx,%eax
    5baf:	0f 8f 1b ff ff ff    	jg     5ad0 <barriered_work+0x80>
    5bb5:	e9 af 01 00 00       	jmp    5d69 <barriered_work+0x319>
    5bba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      receive(data);
    5bc0:	e8 6b fd ff ff       	call   5930 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    5bc5:	4c 63 8b 24 02 00 00 	movslq 0x224(%rbx),%r9
        int t = data->task_index;
    5bcc:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    5bce:	45 85 c9             	test   %r9d,%r9d
    5bd1:	0f 8e 99 00 00 00    	jle    5c70 <barriered_work+0x220>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5bd7:	48 8b 93 18 02 00 00 	mov    0x218(%rbx),%rdx
    5bde:	4c 8b 92 80 00 00 00 	mov    0x80(%rdx),%r10
    5be5:	48 63 d0             	movslq %eax,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
    5be8:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5beb:	4c 8d 1c d2          	lea    (%rdx,%rdx,8),%r11
              int next_task = abs((t + 1) % (data->thread_count));
    5bef:	99                   	cltd
    5bf0:	41 f7 f9             	idiv   %r9d
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5bf3:	49 c1 e3 07          	shl    $0x7,%r11
    5bf7:	4c 89 d7             	mov    %r10,%rdi
    5bfa:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
              int next_task = abs((t + 1) % (data->thread_count));
    5bfe:	89 d0                	mov    %edx,%eax
    5c00:	f7 d8                	neg    %eax
    5c02:	0f 48 c2             	cmovs  %edx,%eax
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5c05:	45 31 c0             	xor    %r8d,%r8d
    5c08:	48 98                	cltq
    5c0a:	48 8d 2c c0          	lea    (%rax,%rax,8),%rbp
    5c0e:	48 c1 e5 07          	shl    $0x7,%rbp
    5c12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    5c18:	31 c0                	xor    %eax,%eax
    5c1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5c20:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    5c24:	48 8b 92 98 00 00 00 	mov    0x98(%rdx),%rdx
    5c2b:	48 8b 8c 2a 88 03 00 00 	mov    0x388(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5c33:	48 8b 17             	mov    (%rdi),%rdx
    5c36:	48 8b b2 98 00 00 00 	mov    0x98(%rdx),%rsi
    5c3d:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5c40:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5c44:	48 c1 e2 09          	shl    $0x9,%rdx
    5c48:	4a 03 94 1e 88 03 00 00 	add    0x388(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5c50:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    5c57:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    5c5b:	49 39 c1             	cmp    %rax,%r9
    5c5e:	75 c0                	jne    5c20 <barriered_work+0x1d0>
        for (int y = 0; y < data->thread_count ; y++) {
    5c60:	48 83 c7 08          	add    $0x8,%rdi
    5c64:	49 81 c0 00 02 00 00 	add    $0x200,%r8
    5c6b:	49 39 fc             	cmp    %rdi,%r12
    5c6e:	75 a8                	jne    5c18 <barriered_work+0x1c8>
      asm volatile ("sfence" ::: "memory");
    5c70:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5c73:	48 8b b3 08 03 00 00 	mov    0x308(%rbx),%rsi
    5c7a:	31 ff                	xor    %edi,%edi
    5c7c:	48 c1 e6 05          	shl    $0x5,%rsi
    5c80:	48 03 b3 88 02 00 00 	add    0x288(%rbx),%rsi
    5c87:	e8 84 c6 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5c8c:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    while (data->scheduled == 1) {
    5c93:	83 bb 80 02 00 00 01 	cmpl   $0x1,0x280(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5c9a:	48 8b 90 00 01 00 00 	mov    0x100(%rax),%rdx
    5ca1:	8b 8a 00 01 00 00    	mov    0x100(%rdx),%ecx
    5ca7:	8d 69 01             	lea    0x1(%rcx),%ebp
    5caa:	89 aa 00 01 00 00    	mov    %ebp,0x100(%rdx)
    while (data->scheduled == 1) {
    5cb0:	75 66                	jne    5d18 <barriered_work+0x2c8>
    5cb2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5cb8:	48 63 93 20 02 00 00 	movslq 0x220(%rbx),%rdx
    5cbf:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
      data->n++;
    5cc6:	48 83 83 80 01 00 00 01 	addq   $0x1,0x180(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5cce:	48 8b 14 d0          	mov    (%rax,%rdx,8),%rdx
    5cd2:	48 63 03             	movslq (%rbx),%rax
    5cd5:	48 8d 3c c0          	lea    (%rax,%rax,8),%rdi
    5cd9:	48 c1 e7 07          	shl    $0x7,%rdi
    5cdd:	48 03 ba 98 00 00 00 	add    0x98(%rdx),%rdi
    5ce4:	ff 93 10 02 00 00    	call   *0x210(%rbx)
      asm volatile ("sfence" ::: "memory");
    5cea:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5ced:	83 bb 80 02 00 00 01 	cmpl   $0x1,0x280(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    5cf4:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    while (data->scheduled == 1) {
    5cfb:	74 bb                	je     5cb8 <barriered_work+0x268>
    if (modcount != data->thread->protected_state->modcount) {
    5cfd:	48 8b 80 00 01 00 00 	mov    0x100(%rax),%rax
    5d04:	3b a8 00 01 00 00    	cmp    0x100(%rax),%ebp
    5d0a:	74 0c                	je     5d18 <barriered_work+0x2c8>
    5d0c:	48 8d 3d fd 14 00 00 	lea    0x14fd(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    5d13:	e8 d8 c5 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5d18:	48 8b b3 08 03 00 00 	mov    0x308(%rbx),%rsi
    5d1f:	31 ff                	xor    %edi,%edi
    5d21:	48 c1 e6 05          	shl    $0x5,%rsi
    5d25:	48 03 b3 88 02 00 00 	add    0x288(%rbx),%rsi
    5d2c:	48 83 c6 10          	add    $0x10,%rsi
    5d30:	e8 db c5 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5d35:	48 8b 83 08 03 00 00 	mov    0x308(%rbx),%rax
    5d3c:	48 83 c0 01          	add    $0x1,%rax
    5d40:	48 99                	cqto
    5d42:	48 f7 bb 00 03 00 00 	idivq  0x300(%rbx)
  if (data->sending == 1) {
    5d49:	83 bb 08 04 00 00 01 	cmpl   $0x1,0x408(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5d50:	48 89 93 08 03 00 00 	mov    %rdx,0x308(%rbx)
  if (data->sending == 1) {
    5d57:	0f 84 a8 00 00 00    	je     5e05 <barriered_work+0x3b5>
    5d5d:	48 8d 3d a0 14 00 00 	lea    0x14a0(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5d64:	e8 87 c5 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5d69:	0f ae f8             	sfence
}
    5d6c:	48 83 c4 18          	add    $0x18,%rsp
    5d70:	31 c0                	xor    %eax,%eax
    5d72:	5b                   	pop    %rbx
    5d73:	5d                   	pop    %rbp
    5d74:	41 5c                	pop    %r12
    5d76:	41 5d                	pop    %r13
    5d78:	41 5e                	pop    %r14
    5d7a:	41 5f                	pop    %r15
    5d7c:	c3                   	ret
    5d7d:	0f 1f 00             	nopl   (%rax)
    5d80:	49 89 f5             	mov    %rsi,%r13
    5d83:	48 8b 83 10 04 00 00 	mov    0x410(%rbx),%rax
    5d8a:	4c 89 e7             	mov    %r12,%rdi
    5d8d:	49 d1 ed             	shr    %r13
    5d90:	49 c1 e5 04          	shl    $0x4,%r13
    5d94:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5d99:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5d9d:	41 83 e5 10          	and    $0x10,%r13d
    5da1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5da5:	74 11                	je     5db8 <barriered_work+0x368>
          them->messages[them->messages_count++] = data->message; 
    5da7:	48 83 c7 10          	add    $0x10,%rdi
    5dab:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5db0:	49 39 ff             	cmp    %rdi,%r15
    5db3:	74 13                	je     5dc8 <barriered_work+0x378>
    5db5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5db8:	0f 11 07             	movups %xmm0,(%rdi)
    5dbb:	48 83 c7 20          	add    $0x20,%rdi
    5dbf:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5dc3:	49 39 ff             	cmp    %rdi,%r15
    5dc6:	75 f0                	jne    5db8 <barriered_work+0x368>
    5dc8:	48 89 f7             	mov    %rsi,%rdi
    5dcb:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5dcf:	4c 01 df             	add    %r11,%rdi
    5dd2:	40 f6 c6 01          	test   $0x1,%sil
    5dd6:	0f 84 a4 fd ff ff    	je     5b80 <barriered_work+0x130>
          them->messages[them->messages_count++] = data->message; 
    5ddc:	48 8b 83 10 04 00 00 	mov    0x410(%rbx),%rax
    5de3:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5de7:	e9 94 fd ff ff       	jmp    5b80 <barriered_work+0x130>
    5dec:	0f 1f 40 00          	nopl   0x0(%rax)
    5df0:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5df8:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5e00:	e9 58 fd ff ff       	jmp    5b5d <barriered_work+0x10d>
      for (int n = 0 ; n < data->thread_count; n++) {
    5e05:	48 8d 8b 10 04 00 00 	lea    0x410(%rbx),%rcx
    5e0c:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    5e12:	31 d2                	xor    %edx,%edx
    5e14:	48 89 0c 24          	mov    %rcx,(%rsp)
    5e18:	48 8d 8b 18 04 00 00 	lea    0x418(%rbx),%rcx
    5e1f:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5e24:	85 c0                	test   %eax,%eax
    5e26:	0f 8e 3d ff ff ff    	jle    5d69 <barriered_work+0x319>
    5e2c:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5e30:	39 93 20 02 00 00    	cmp    %edx,0x220(%rbx)
    5e36:	0f 84 c5 00 00 00    	je     5f01 <barriered_work+0x4b1>
        struct Data *them = data->mailboxes[n].higher;
    5e3c:	49 89 d1             	mov    %rdx,%r9
    5e3f:	49 c1 e1 09          	shl    $0x9,%r9
    5e43:	4c 03 8b 88 03 00 00 	add    0x388(%rbx),%r9
    5e4a:	4d 8b 91 80 00 00 00 	mov    0x80(%r9),%r10
        for (; them->messages_count < min;) {
    5e51:	4d 8b 9a 80 00 00 00 	mov    0x80(%r10),%r11
    5e58:	4d 63 82 88 00 00 00 	movslq 0x88(%r10),%r8
    5e5f:	4d 39 d8             	cmp    %r11,%r8
    5e62:	0f 8e 90 00 00 00    	jle    5ef8 <barriered_work+0x4a8>
    5e68:	4c 89 c6             	mov    %r8,%rsi
    5e6b:	48 8b ab 80 01 00 00 	mov    0x180(%rbx),%rbp
    5e72:	4d 8b b1 00 01 00 00 	mov    0x100(%r9),%r14
    5e79:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5e7c:	49 8b 0a             	mov    (%r10),%rcx
    5e7f:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5e83:	48 83 f8 02          	cmp    $0x2,%rax
    5e87:	0f 86 fb 00 00 00    	jbe    5f88 <barriered_work+0x538>
    5e8d:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5e95:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5e9d:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5ea1:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5ea5:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5ea9:	73 6d                	jae    5f18 <barriered_work+0x4c8>
    5eab:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5eb0:	4d 39 fc             	cmp    %r15,%r12
    5eb3:	73 63                	jae    5f18 <barriered_work+0x4c8>
    5eb5:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5eb9:	48 01 cf             	add    %rcx,%rdi
    5ebc:	0f 1f 40 00          	nopl   0x0(%rax)
    5ec0:	48 8b 83 10 04 00 00 	mov    0x410(%rbx),%rax
        for (; them->messages_count < min;) {
    5ec7:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5ecb:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5ecf:	49 39 fb             	cmp    %rdi,%r11
    5ed2:	75 ec                	jne    5ec0 <barriered_work+0x470>
    5ed4:	0f 1f 40 00          	nopl   0x0(%rax)
    5ed8:	48 01 f5             	add    %rsi,%rbp
    5edb:	4c 01 f6             	add    %r14,%rsi
    5ede:	48 89 ab 80 01 00 00 	mov    %rbp,0x180(%rbx)
    5ee5:	49 89 b1 00 01 00 00 	mov    %rsi,0x100(%r9)
    5eec:	4d 89 82 80 00 00 00 	mov    %r8,0x80(%r10)
    5ef3:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5ef8:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5efb:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    5f01:	48 83 c2 01          	add    $0x1,%rdx
    5f05:	39 d0                	cmp    %edx,%eax
    5f07:	0f 8f 23 ff ff ff    	jg     5e30 <barriered_work+0x3e0>
    5f0d:	e9 57 fe ff ff       	jmp    5d69 <barriered_work+0x319>
    5f12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5f18:	49 89 f5             	mov    %rsi,%r13
    5f1b:	48 8b 83 10 04 00 00 	mov    0x410(%rbx),%rax
    5f22:	4c 89 e7             	mov    %r12,%rdi
    5f25:	49 d1 ed             	shr    %r13
    5f28:	49 c1 e5 04          	shl    $0x4,%r13
    5f2c:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5f31:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5f35:	41 83 e5 10          	and    $0x10,%r13d
    5f39:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5f3d:	74 11                	je     5f50 <barriered_work+0x500>
          them->messages[them->messages_count++] = data->message; 
    5f3f:	48 83 c7 10          	add    $0x10,%rdi
    5f43:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5f48:	4c 39 ff             	cmp    %r15,%rdi
    5f4b:	74 13                	je     5f60 <barriered_work+0x510>
    5f4d:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5f50:	0f 11 07             	movups %xmm0,(%rdi)
    5f53:	48 83 c7 20          	add    $0x20,%rdi
    5f57:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5f5b:	4c 39 ff             	cmp    %r15,%rdi
    5f5e:	75 f0                	jne    5f50 <barriered_work+0x500>
    5f60:	48 89 f7             	mov    %rsi,%rdi
    5f63:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5f67:	4c 01 df             	add    %r11,%rdi
    5f6a:	40 f6 c6 01          	test   $0x1,%sil
    5f6e:	0f 84 64 ff ff ff    	je     5ed8 <barriered_work+0x488>
          them->messages[them->messages_count++] = data->message; 
    5f74:	48 8b 83 10 04 00 00 	mov    0x410(%rbx),%rax
    5f7b:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5f7f:	e9 54 ff ff ff       	jmp    5ed8 <barriered_work+0x488>
    5f84:	0f 1f 40 00          	nopl   0x0(%rax)
    5f88:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5f90:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5f98:	e9 18 ff ff ff       	jmp    5eb5 <barriered_work+0x465>
    5f9d:	0f 1f 00             	nopl   (%rax)

0000000000005fa0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5fa0:	f3 0f 1e fa          	endbr64
    5fa4:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5fa8:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    5faf:	48 8b 80 80 01 00 00 	mov    0x180(%rax),%rax
    5fb6:	48 63 10             	movslq (%rax),%rdx
    5fb9:	85 d2                	test   %edx,%edx
    5fbb:	7e 39                	jle    5ff6 <barriered_work_ingest+0x56>
    5fbd:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    5fc4:	48 c1 e2 08          	shl    $0x8,%rdx
    5fc8:	48 01 c2             	add    %rax,%rdx
    5fcb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread->buffers->buffer[x].available == 1) {
    5fd0:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    5fd7:	75 12                	jne    5feb <barriered_work_ingest+0x4b>
      data->ingest_count++;
    5fd9:	48 83 87 80 03 00 00 01 	addq   $0x1,0x380(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5fe1:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5feb:	48 05 00 01 00 00    	add    $0x100,%rax
    5ff1:	48 39 d0             	cmp    %rdx,%rax
    5ff4:	75 da                	jne    5fd0 <barriered_work_ingest+0x30>
  asm volatile ("sfence" ::: "memory");
    5ff6:	0f ae f8             	sfence
  barriered_work(data);
    5ff9:	e8 52 fa ff ff       	call   5a50 <barriered_work>
}
    5ffe:	31 c0                	xor    %eax,%eax
    6000:	48 83 c4 08          	add    $0x8,%rsp
    6004:	c3                   	ret
    6005:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000006010 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6010:	f3 0f 1e fa          	endbr64
}
    6014:	31 c0                	xor    %eax,%eax
    6016:	c3                   	ret
    6017:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006020 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6020:	f3 0f 1e fa          	endbr64
    6024:	31 c0                	xor    %eax,%eax
    6026:	c3                   	ret
    6027:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006030 <after>:
int after(struct timespec left, struct timespec right) {
    6030:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6034:	31 c0                	xor    %eax,%eax
    6036:	48 39 d7             	cmp    %rdx,%rdi
    6039:	7e 08                	jle    6043 <after+0x13>
    603b:	31 c0                	xor    %eax,%eax
    603d:	48 39 ce             	cmp    %rcx,%rsi
    6040:	0f 9f c0             	setg   %al
}
    6043:	c3                   	ret
    6044:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    604f:	90                   	nop

0000000000006050 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6050:	f3 0f 1e fa          	endbr64
    6054:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6059:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    605e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6060:	48 39 d7             	cmp    %rdx,%rdi
    6063:	7f 18                	jg     607d <within+0x2d>
    6065:	4d 39 d8             	cmp    %r11,%r8
    6068:	0f 9e c2             	setle  %dl
    606b:	48 39 ce             	cmp    %rcx,%rsi
    606e:	0f 9e c0             	setle  %al
    6071:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6073:	31 c0                	xor    %eax,%eax
    6075:	4d 39 d1             	cmp    %r10,%r9
    6078:	0f 9e c0             	setle  %al
    607b:	21 d0                	and    %edx,%eax
}
    607d:	c3                   	ret
    607e:	66 90                	xchg   %ax,%ax

0000000000006080 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6080:	f3 0f 1e fa          	endbr64
    6084:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6089:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    608e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6093:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6098:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    609d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    60a2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    60a7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    60ac:	48 39 fe             	cmp    %rdi,%rsi
    60af:	7d 2f                	jge    60e0 <overlap+0x60>
    60b1:	48 39 ca             	cmp    %rcx,%rdx
    60b4:	7d 62                	jge    6118 <overlap+0x98>
    60b6:	4d 39 da             	cmp    %r11,%r10
    60b9:	7d 0e                	jge    60c9 <overlap+0x49>
    return 1;
    60bb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    60c0:	4d 39 c1             	cmp    %r8,%r9
    60c3:	0f 8c 7f 00 00 00    	jl     6148 <overlap+0xc8>
  return 0;
    60c9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    60cb:	4d 39 c1             	cmp    %r8,%r9
    60ce:	7f 4c                	jg     611c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    60d0:	31 c0                	xor    %eax,%eax
    60d2:	4d 39 da             	cmp    %r11,%r10
    60d5:	0f 9e c0             	setle  %al
    60d8:	c3                   	ret
    60d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    60e0:	7e 4e                	jle    6130 <overlap+0xb0>
    60e2:	48 39 ca             	cmp    %rcx,%rdx
    60e5:	7f 39                	jg     6120 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    60e7:	75 31                	jne    611a <overlap+0x9a>
    60e9:	4d 39 c1             	cmp    %r8,%r9
    60ec:	7c 2c                	jl     611a <overlap+0x9a>
    return 1;
    60ee:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    60f3:	4d 39 da             	cmp    %r11,%r10
    60f6:	7d 24                	jge    611c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    60f8:	48 39 ca             	cmp    %rcx,%rdx
    60fb:	0f 94 c2             	sete   %dl
    60fe:	48 39 fe             	cmp    %rdi,%rsi
    6101:	0f 94 c0             	sete   %al
    6104:	21 c2                	and    %eax,%edx
    6106:	31 c0                	xor    %eax,%eax
    6108:	4d 39 c1             	cmp    %r8,%r9
    610b:	0f 94 c0             	sete   %al
    610e:	21 d0                	and    %edx,%eax
    6110:	c3                   	ret
    6111:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6118:	74 af                	je     60c9 <overlap+0x49>
  return 0;
    611a:	31 c0                	xor    %eax,%eax
}
    611c:	c3                   	ret
    611d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6120:	4d 39 da             	cmp    %r11,%r10
    6123:	7e c4                	jle    60e9 <overlap+0x69>
    return 1;
    6125:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    612a:	4d 39 c1             	cmp    %r8,%r9
    612d:	7e ba                	jle    60e9 <overlap+0x69>
    612f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6130:	48 39 ca             	cmp    %rcx,%rdx
    6133:	7c 94                	jl     60c9 <overlap+0x49>
    6135:	4d 39 c1             	cmp    %r8,%r9
    6138:	7d b4                	jge    60ee <overlap+0x6e>
    613a:	48 39 ca             	cmp    %rcx,%rdx
    613d:	74 91                	je     60d0 <overlap+0x50>
    613f:	eb d9                	jmp    611a <overlap+0x9a>
    6141:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6148:	c3                   	ret
    6149:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006150 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6150:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6154:	85 f6                	test   %esi,%esi
    6156:	0f 8e 59 03 00 00    	jle    64b5 <verify+0x365>
int verify(struct KernelThread *thread_data, int thread_count) {
    615c:	41 57                	push   %r15
    615e:	41 89 f7             	mov    %esi,%r15d
    6161:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6163:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6166:	41 55                	push   %r13
    6168:	41 54                	push   %r12
    616a:	55                   	push   %rbp
    616b:	53                   	push   %rbx
    616c:	48 8d 9f 98 00 00 00 	lea    0x98(%rdi),%rbx
    6173:	48 83 ec 48          	sub    $0x48,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6177:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    617c:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    6181:	45 31 e4             	xor    %r12d,%r12d
    6184:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
      if (z != x)  {
    6189:	45 39 e6             	cmp    %r12d,%r14d
    618c:	0f 84 54 02 00 00    	je     63e6 <verify+0x296>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6192:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6197:	8b 50 08             	mov    0x8(%rax),%edx
    619a:	85 d2                	test   %edx,%edx
    619c:	0f 8e 44 02 00 00    	jle    63e6 <verify+0x296>
    61a2:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    61aa:	31 ed                	xor    %ebp,%ebp
    61ac:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    61b1:	44 89 7c 24 34       	mov    %r15d,0x34(%rsp)
    61b6:	45 89 f7             	mov    %r14d,%r15d
    61b9:	41 89 ee             	mov    %ebp,%r14d
    61bc:	44 89 fa             	mov    %r15d,%edx
    61bf:	48 8d 35 5a 10 00 00 	lea    0x105a(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    61c6:	bf 01 00 00 00       	mov    $0x1,%edi
    61cb:	31 c0                	xor    %eax,%eax
    61cd:	e8 7e c2 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    61d2:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    61d7:	8b 40 08             	mov    0x8(%rax),%eax
    61da:	85 c0                	test   %eax,%eax
    61dc:	0f 8e dc 01 00 00    	jle    63be <verify+0x26e>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    61e2:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    61e7:	44 89 74 24 38       	mov    %r14d,0x38(%rsp)
    61ec:	31 db                	xor    %ebx,%ebx
    61ee:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    61f3:	4c 8b 20             	mov    (%rax),%r12
    61f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6200:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    6205:	48 8d 04 db          	lea    (%rbx,%rbx,8),%rax
    6209:	4c 8b 3c 24          	mov    (%rsp),%r15
    620d:	48 8d 35 21 10 00 00 	lea    0x1021(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    6214:	49 89 c6             	mov    %rax,%r14
    6217:	bf 01 00 00 00       	mov    $0x1,%edi
    621c:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6220:	49 c1 e6 07          	shl    $0x7,%r14
    6224:	4b 8b 8c 3c 08 03 00 00 	mov    0x308(%r12,%r15,1),%rcx
    622c:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    6231:	4a 8b 94 30 08 03 00 00 	mov    0x308(%rax,%r14,1),%rdx
    6239:	31 c0                	xor    %eax,%eax
    623b:	e8 10 c2 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6240:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6245:	4c 8b 20             	mov    (%rax),%r12
    6248:	4b 83 bc 3c 08 03 00 00 00 	cmpq   $0x0,0x308(%r12,%r15,1)
    6251:	0f 8e 4b 01 00 00    	jle    63a2 <verify+0x252>
    6257:	4c 03 75 00          	add    0x0(%rbp),%r14
    625b:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6260:	ba 01 00 00 00       	mov    $0x1,%edx
    6265:	4d 89 f5             	mov    %r14,%r13
    6268:	4d 8b b5 08 03 00 00 	mov    0x308(%r13),%r14
    626f:	4d 85 f6             	test   %r14,%r14
    6272:	0f 8e 25 01 00 00    	jle    639d <verify+0x24d>
    6278:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6280:	48 89 d5             	mov    %rdx,%rbp
    6283:	48 8b 04 24          	mov    (%rsp),%rax
    6287:	31 db                	xor    %ebx,%ebx
    6289:	4d 89 f2             	mov    %r14,%r10
    628c:	48 c1 e5 05          	shl    $0x5,%rbp
    6290:	48 83 ed 20          	sub    $0x20,%rbp
    6294:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6298:	49 89 ee             	mov    %rbp,%r14
    629b:	48 89 dd             	mov    %rbx,%rbp
    629e:	48 89 d3             	mov    %rdx,%rbx
    62a1:	eb 32                	jmp    62d5 <verify+0x185>
    62a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    62a8:	4c 39 c2             	cmp    %r8,%rdx
    62ab:	0f 8d 57 01 00 00    	jge    6408 <verify+0x2b8>
    62b1:	4c 39 df             	cmp    %r11,%rdi
    62b4:	7e 05                	jle    62bb <verify+0x16b>
    62b6:	49 39 c1             	cmp    %rax,%r9
    62b9:	7c 75                	jl     6330 <verify+0x1e0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    62bb:	4c 39 df             	cmp    %r11,%rdi
    62be:	0f 8d b3 01 00 00    	jge    6477 <verify+0x327>
    62c4:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    62c8:	48 83 c5 01          	add    $0x1,%rbp
    62cc:	49 39 ea             	cmp    %rbp,%r10
    62cf:	0f 8e a8 00 00 00    	jle    637d <verify+0x22d>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    62d5:	49 8b 97 88 02 00 00 	mov    0x288(%r15),%rdx
    62dc:	48 89 e8             	mov    %rbp,%rax
    62df:	48 c1 e0 05          	shl    $0x5,%rax
    62e3:	49 03 85 88 02 00 00 	add    0x288(%r13),%rax
    62ea:	4c 01 f2             	add    %r14,%rdx
    62ed:	48 8b 08             	mov    (%rax),%rcx
    62f0:	48 8b 78 10          	mov    0x10(%rax),%rdi
    62f4:	48 8b 32             	mov    (%rdx),%rsi
    62f7:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    62fb:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    62ff:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    6303:	48 8b 50 08          	mov    0x8(%rax),%rdx
    6307:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    630b:	48 39 f1             	cmp    %rsi,%rcx
    630e:	7c 98                	jl     62a8 <verify+0x158>
    6310:	0f 8e 4a 01 00 00    	jle    6460 <verify+0x310>
    6316:	4c 39 c2             	cmp    %r8,%rdx
    6319:	0f 8f f9 00 00 00    	jg     6418 <verify+0x2c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    631f:	75 a7                	jne    62c8 <verify+0x178>
    6321:	4c 39 df             	cmp    %r11,%rdi
    6324:	7f a2                	jg     62c8 <verify+0x178>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6326:	49 39 c1             	cmp    %rax,%r9
    6329:	7c 9d                	jl     62c8 <verify+0x178>
    632b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6330:	49 89 c1             	mov    %rax,%r9
    6333:	48 89 f9             	mov    %rdi,%rcx
    6336:	48 89 f2             	mov    %rsi,%rdx
    6339:	bf 01 00 00 00       	mov    $0x1,%edi
    633e:	48 8d 35 43 11 00 00 	lea    0x1143(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    6345:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6347:	48 83 c5 01          	add    $0x1,%rbp
    634b:	e8 00 c1 ff ff       	call   2450 <__printf_chk@plt>
    6350:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6355:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    635a:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    635d:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6362:	4d 8b 95 08 03 00 00 	mov    0x308(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6369:	4c 8b 20             	mov    (%rax),%r12
    636c:	48 8b 04 24          	mov    (%rsp),%rax
    6370:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6374:	49 39 ea             	cmp    %rbp,%r10
    6377:	0f 8f 58 ff ff ff    	jg     62d5 <verify+0x185>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    637d:	48 89 da             	mov    %rbx,%rdx
    6380:	49 3b 9f 08 03 00 00 	cmp    0x308(%r15),%rbx
    6387:	7d 14                	jge    639d <verify+0x24d>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6389:	4d 8b b5 08 03 00 00 	mov    0x308(%r13),%r14
    6390:	48 83 c2 01          	add    $0x1,%rdx
    6394:	4d 85 f6             	test   %r14,%r14
    6397:	0f 8f e3 fe ff ff    	jg     6280 <verify+0x130>
    639d:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    63a2:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    63a7:	48 83 c3 01          	add    $0x1,%rbx
    63ab:	39 58 08             	cmp    %ebx,0x8(%rax)
    63ae:	0f 8f 4c fe ff ff    	jg     6200 <verify+0xb0>
    63b4:	44 8b 74 24 38       	mov    0x38(%rsp),%r14d
    63b9:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    63be:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    63c3:	48 81 04 24 80 04 00 00 	addq   $0x480,(%rsp)
    63cb:	41 83 c6 01          	add    $0x1,%r14d
    63cf:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    63d3:	0f 8f e3 fd ff ff    	jg     61bc <verify+0x6c>
    63d9:	45 89 fe             	mov    %r15d,%r14d
    63dc:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    63e1:	44 8b 7c 24 34       	mov    0x34(%rsp),%r15d
    for (int z = 0 ; z < thread_count; z++) {
    63e6:	48 81 44 24 08 80 05 00 00 	addq   $0x580,0x8(%rsp)
    63ef:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    63f4:	41 39 c7             	cmp    %eax,%r15d
    63f7:	0f 84 88 00 00 00    	je     6485 <verify+0x335>
    63fd:	41 89 c4             	mov    %eax,%r12d
    6400:	e9 84 fd ff ff       	jmp    6189 <verify+0x39>
    6405:	0f 1f 00             	nopl   (%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6408:	0f 85 ba fe ff ff    	jne    62c8 <verify+0x178>
    640e:	e9 a8 fe ff ff       	jmp    62bb <verify+0x16b>
    6413:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6418:	49 39 c1             	cmp    %rax,%r9
    641b:	7e 09                	jle    6426 <verify+0x2d6>
    641d:	4c 39 df             	cmp    %r11,%rdi
    6420:	0f 8c 0a ff ff ff    	jl     6330 <verify+0x1e0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6426:	4c 39 df             	cmp    %r11,%rdi
    6429:	0f 8f 99 fe ff ff    	jg     62c8 <verify+0x178>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    642f:	49 39 c1             	cmp    %rax,%r9
    6432:	0f 8d f8 fe ff ff    	jge    6330 <verify+0x1e0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6438:	48 39 f1             	cmp    %rsi,%rcx
    643b:	0f 85 87 fe ff ff    	jne    62c8 <verify+0x178>
    6441:	4c 39 c2             	cmp    %r8,%rdx
    6444:	0f 85 7e fe ff ff    	jne    62c8 <verify+0x178>
    644a:	4c 39 df             	cmp    %r11,%rdi
    644d:	0f 84 dd fe ff ff    	je     6330 <verify+0x1e0>
    6453:	e9 70 fe ff ff       	jmp    62c8 <verify+0x178>
    6458:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6460:	4c 39 c2             	cmp    %r8,%rdx
    6463:	0f 8c 52 fe ff ff    	jl     62bb <verify+0x16b>
    6469:	4c 39 df             	cmp    %r11,%rdi
    646c:	7e c1                	jle    642f <verify+0x2df>
    646e:	4c 39 c2             	cmp    %r8,%rdx
    6471:	0f 85 51 fe ff ff    	jne    62c8 <verify+0x178>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6477:	49 39 c1             	cmp    %rax,%r9
    647a:	0f 8f 48 fe ff ff    	jg     62c8 <verify+0x178>
    6480:	e9 ab fe ff ff       	jmp    6330 <verify+0x1e0>
  for (int x = 0 ; x < thread_count; x++) {
    6485:	48 81 44 24 10 80 05 00 00 	addq   $0x580,0x10(%rsp)
    648e:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    6493:	41 8d 46 01          	lea    0x1(%r14),%eax
    6497:	45 39 e6             	cmp    %r12d,%r14d
    649a:	74 08                	je     64a4 <verify+0x354>
    649c:	41 89 c6             	mov    %eax,%r14d
    649f:	e9 d8 fc ff ff       	jmp    617c <verify+0x2c>
}
    64a4:	48 83 c4 48          	add    $0x48,%rsp
    64a8:	31 c0                	xor    %eax,%eax
    64aa:	5b                   	pop    %rbx
    64ab:	5d                   	pop    %rbp
    64ac:	41 5c                	pop    %r12
    64ae:	41 5d                	pop    %r13
    64b0:	41 5e                	pop    %r14
    64b2:	41 5f                	pop    %r15
    64b4:	c3                   	ret
    64b5:	31 c0                	xor    %eax,%eax
    64b7:	c3                   	ret

Disassembly of section .fini:

00000000000064b8 <_fini>:
    64b8:	f3 0f 1e fa          	endbr64
    64bc:	48 83 ec 08          	sub    $0x8,%rsp
    64c0:	48 83 c4 08          	add    $0x8,%rsp
    64c4:	c3                   	ret
