
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
    2586:	48 8d 3d 23 4f 00 00 	lea    0x4f23(%rip),%rdi        # 74b0 <_IO_stdin_used+0x4b0>
    258d:	41 56                	push   %r14
    258f:	41 55                	push   %r13
    2591:	41 54                	push   %r12
    2593:	55                   	push   %rbp
    2594:	53                   	push   %rbx
    2595:	48 81 ec b8 00 00 00 	sub    $0xb8,%rsp
    259c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    25a5:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
    25ad:	48 8d 05 ec 11 00 00 	lea    0x11ec(%rip),%rax        # 37a0 <barriered_reset>
    25b4:	66 48 0f 6e e8       	movq   %rax,%xmm5
    25b9:	0f 16 2d b8 76 00 00 	movhps 0x76b8(%rip),%xmm5        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    25c0:	0f 29 6c 24 30       	movaps %xmm5,0x30(%rsp)
    25c5:	e8 26 fd ff ff       	call   22f0 <puts@plt>
    25ca:	bf 0a 00 00 00       	mov    $0xa,%edi
    25cf:	e8 fc fc ff ff       	call   22d0 <putchar@plt>
    25d4:	48 8d 3d 63 4c 00 00 	lea    0x4c63(%rip),%rdi        # 723e <_IO_stdin_used+0x23e>
    25db:	e8 10 fd ff ff       	call   22f0 <puts@plt>
    25e0:	ba 0c 00 00 00       	mov    $0xc,%edx
    25e5:	48 8d 35 6e 4c 00 00 	lea    0x4c6e(%rip),%rsi        # 725a <_IO_stdin_used+0x25a>
    25ec:	31 c0                	xor    %eax,%eax
    25ee:	bf 01 00 00 00       	mov    $0x1,%edi
    25f3:	e8 58 fe ff ff       	call   2450 <__printf_chk@plt>
    25f8:	ba 0f 00 00 00       	mov    $0xf,%edx
    25fd:	48 8d 35 70 4c 00 00 	lea    0x4c70(%rip),%rsi        # 7274 <_IO_stdin_used+0x274>
    2604:	31 c0                	xor    %eax,%eax
    2606:	bf 01 00 00 00       	mov    $0x1,%edi
    260b:	e8 40 fe ff ff       	call   2450 <__printf_chk@plt>
    2610:	ba 01 00 00 00       	mov    $0x1,%edx
    2615:	48 8d 35 6c 4c 00 00 	lea    0x4c6c(%rip),%rsi        # 7288 <_IO_stdin_used+0x288>
    261c:	31 c0                	xor    %eax,%eax
    261e:	bf 01 00 00 00       	mov    $0x1,%edi
    2623:	e8 28 fe ff ff       	call   2450 <__printf_chk@plt>
    2628:	ba 01 00 00 00       	mov    $0x1,%edx
    262d:	48 8d 35 65 4c 00 00 	lea    0x4c65(%rip),%rsi        # 7299 <_IO_stdin_used+0x299>
    2634:	31 c0                	xor    %eax,%eax
    2636:	bf 01 00 00 00       	mov    $0x1,%edi
    263b:	e8 10 fe ff ff       	call   2450 <__printf_chk@plt>
    2640:	ba 01 00 00 00       	mov    $0x1,%edx
    2645:	48 8d 35 65 4c 00 00 	lea    0x4c65(%rip),%rsi        # 72b1 <_IO_stdin_used+0x2b1>
    264c:	31 c0                	xor    %eax,%eax
    264e:	bf 01 00 00 00       	mov    $0x1,%edi
    2653:	e8 f8 fd ff ff       	call   2450 <__printf_chk@plt>
    2658:	ba 01 00 00 00       	mov    $0x1,%edx
    265d:	48 8d 35 b4 4e 00 00 	lea    0x4eb4(%rip),%rsi        # 7518 <_IO_stdin_used+0x518>
    2664:	31 c0                	xor    %eax,%eax
    2666:	bf 01 00 00 00       	mov    $0x1,%edi
    266b:	e8 e0 fd ff ff       	call   2450 <__printf_chk@plt>
    2670:	ba 01 00 00 00       	mov    $0x1,%edx
    2675:	48 8d 35 cc 4e 00 00 	lea    0x4ecc(%rip),%rsi        # 7548 <_IO_stdin_used+0x548>
    267c:	31 c0                	xor    %eax,%eax
    267e:	bf 01 00 00 00       	mov    $0x1,%edi
    2683:	e8 c8 fd ff ff       	call   2450 <__printf_chk@plt>
    2688:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    268d:	48 8d 35 39 4c 00 00 	lea    0x4c39(%rip),%rsi        # 72cd <_IO_stdin_used+0x2cd>
    2694:	31 c0                	xor    %eax,%eax
    2696:	bf 01 00 00 00       	mov    $0x1,%edi
    269b:	e8 b0 fd ff ff       	call   2450 <__printf_chk@plt>
    26a0:	ba 05 00 00 00       	mov    $0x5,%edx
    26a5:	48 8d 35 3b 4c 00 00 	lea    0x4c3b(%rip),%rsi        # 72e7 <_IO_stdin_used+0x2e7>
    26ac:	31 c0                	xor    %eax,%eax
    26ae:	bf 01 00 00 00       	mov    $0x1,%edi
    26b3:	e8 98 fd ff ff       	call   2450 <__printf_chk@plt>
    26b8:	48 8d 3d 0f 4a 00 00 	lea    0x4a0f(%rip),%rdi        # 70ce <_IO_stdin_used+0xce>
    26bf:	e8 2c fc ff ff       	call   22f0 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    26c4:	be 18 00 00 00       	mov    $0x18,%esi
    26c9:	bf 0c 00 00 00       	mov    $0xc,%edi
    26ce:	e8 cd fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    26d3:	be 40 01 00 00       	mov    $0x140,%esi
    26d8:	bf 0f 00 00 00       	mov    $0xf,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    26dd:	49 89 c7             	mov    %rax,%r15
    26e0:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    26e5:	e8 b6 fc ff ff       	call   23a0 <calloc@plt>
  int barrier_count = 2;
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    26ea:	be 10 00 00 00       	mov    $0x10,%esi
    26ef:	bf 01 00 00 00       	mov    $0x1,%edi
    26f4:	4d 8d 67 e8          	lea    -0x18(%r15),%r12
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    26f8:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    26fd:	45 31 ff             	xor    %r15d,%r15d
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2700:	e8 9b fc ff ff       	call   23a0 <calloc@plt>
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2705:	be 10 00 00 00       	mov    $0x10,%esi
    270a:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    270f:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2715:	48 89 c3             	mov    %rax,%rbx
    2718:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    271d:	e8 7e fc ff ff       	call   23a0 <calloc@plt>
    2722:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    }
  }
  int external_thread_index = 0;
    2727:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    272f:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
    2733:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    273a:	4d 89 d1             	mov    %r10,%r9
    273d:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    2742:	4c 89 54 24 58       	mov    %r10,0x58(%rsp)
    2747:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2750:	be 08 00 00 00       	mov    $0x8,%esi
    2755:	bf 02 00 00 00       	mov    $0x2,%edi
    275a:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    275f:	44 89 fd             	mov    %r15d,%ebp
    2762:	e8 39 fc ff ff       	call   23a0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2767:	be 80 00 00 00       	mov    $0x80,%esi
    276c:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2771:	49 89 c5             	mov    %rax,%r13
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2774:	e8 27 fc ff ff       	call   23a0 <calloc@plt>
    if (x % 2 == 1) {
    2779:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    277e:	48 89 c3             	mov    %rax,%rbx
    if (x % 2 == 1) {
    2781:	44 89 f8             	mov    %r15d,%eax
    2784:	41 83 c7 01          	add    $0x1,%r15d
    2788:	83 e0 01             	and    $0x1,%eax
    278b:	85 c0                	test   %eax,%eax
    278d:	0f 84 5c 0e 00 00    	je     35ef <main+0x106f>
      my_thread_data[0] = &thread_data[other]; 
    2793:	49 8d 89 c0 fe ff ff 	lea    -0x140(%r9),%rcx
      my_thread_data[1] = &thread_data[x]; 
    279a:	4d 89 4d 08          	mov    %r9,0x8(%r13)
    279e:	4d 89 c8             	mov    %r9,%r8
    27a1:	89 ea                	mov    %ebp,%edx
      my_thread_data[0] = &thread_data[other]; 
    27a3:	49 89 4d 00          	mov    %rcx,0x0(%r13)
    27a7:	bf 01 00 00 00       	mov    $0x1,%edi
    27ac:	31 c0                	xor    %eax,%eax
      other = abs(x - 1) % total_threads;
    27ae:	44 8d 75 ff          	lea    -0x1(%rbp),%r14d
      thread_data[x].thread_index = 1;
    27b2:	41 c7 01 01 00 00 00 	movl   $0x1,(%r9)
    27b9:	48 8d 35 3b 4b 00 00 	lea    0x4b3b(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
    27c0:	e8 8b fc ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    27c5:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    27ca:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    27cf:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    27d4:	4d 89 a1 80 00 00 00 	mov    %r12,0x80(%r9)
    27db:	45 8b 01             	mov    (%r9),%r8d
    27de:	44 89 f1             	mov    %r14d,%ecx
    27e1:	89 ea                	mov    %ebp,%edx
    27e3:	48 8d 35 86 4d 00 00 	lea    0x4d86(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    27ea:	bf 01 00 00 00       	mov    $0x1,%edi
    27ef:	31 c0                	xor    %eax,%eax
    27f1:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      CPU_SET(j, sendercpu);
    27f6:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    27fc:	e8 4f fc ff ff       	call   2450 <__printf_chk@plt>
    thread_data[x].other = other;
    2801:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2806:	45 89 b1 28 01 00 00 	mov    %r14d,0x128(%r9)
    for (int j = 0 ; j < cores / 2 ; j++) {
    280d:	45 31 f6             	xor    %r14d,%r14d
    2810:	44 89 f1             	mov    %r14d,%ecx
    2813:	89 ea                	mov    %ebp,%edx
    2815:	48 8d 35 84 4d 00 00 	lea    0x4d84(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    281c:	31 c0                	xor    %eax,%eax
    281e:	bf 01 00 00 00       	mov    $0x1,%edi
    2823:	e8 28 fc ff ff       	call   2450 <__printf_chk@plt>
      CPU_SET(j, sendercpu);
    2828:	44 89 f1             	mov    %r14d,%ecx
    282b:	4c 89 e0             	mov    %r12,%rax
    for (int j = 0 ; j < cores / 2 ; j++) {
    282e:	41 83 c6 01          	add    $0x1,%r14d
      CPU_SET(j, sendercpu);
    2832:	48 d3 e0             	shl    %cl,%rax
    2835:	48 09 03             	or     %rax,(%rbx)
    for (int j = 0 ; j < cores / 2 ; j++) {
    2838:	41 83 fe 06          	cmp    $0x6,%r14d
    283c:	75 d2                	jne    2810 <main+0x290>
    thread_data[x].cpu_set = sendercpu;
    283e:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2843:	be 10 00 00 00       	mov    $0x10,%esi
    2848:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].thread_count = 2;
    284d:	48 8b 05 f4 51 00 00 	mov    0x51f4(%rip),%rax        # 7a48 <_IO_stdin_used+0xa48>
    thread_data[x].cpu_set = sendercpu;
    2854:	49 89 99 20 01 00 00 	mov    %rbx,0x120(%r9)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    285b:	31 db                	xor    %ebx,%ebx
    thread_data[x].real_thread_index = x;
    285d:	41 89 69 04          	mov    %ebp,0x4(%r9)
    thread_data[x].threads = my_thread_data;
    2861:	4d 89 69 40          	mov    %r13,0x40(%r9)
    thread_data[x].thread_count = 2;
    2865:	49 89 41 48          	mov    %rax,0x48(%r9)
    thread_data[x].task_count = total_barrier_count;
    2869:	41 c7 41 60 03 00 00 00 	movl   $0x3,0x60(%r9)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2871:	e8 2a fb ff ff       	call   23a0 <calloc@plt>
    2876:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    287b:	be 10 00 00 00       	mov    $0x10,%esi
    2880:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2885:	49 89 81 d8 00 00 00 	mov    %rax,0xd8(%r9)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    288c:	e8 0f fb ff ff       	call   23a0 <calloc@plt>
    2891:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2896:	be 28 00 00 00       	mov    $0x28,%esi
    thread_data[x].timestamp_count = 0;
    289b:	66 0f 6f 15 7d 51 00 00 	movdqa 0x517d(%rip),%xmm2        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28a3:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28a8:	49 89 81 e0 00 00 00 	mov    %rax,0xe0(%r9)
    thread_data[x].timestamp_count = 0;
    28af:	41 0f 29 91 f0 00 00 00 	movaps %xmm2,0xf0(%r9)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28b7:	e8 e4 fa ff ff       	call   23a0 <calloc@plt>
    28bc:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    28c1:	be 80 01 00 00       	mov    $0x180,%esi
    thread_data[x].task_timestamp_count = 0;
    28c6:	66 0f 6f 1d 52 51 00 00 	movdqa 0x5152(%rip),%xmm3        # 7a20 <_IO_stdin_used+0xa20>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    28ce:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28d3:	49 89 81 00 01 00 00 	mov    %rax,0x100(%r9)
    thread_data[x].task_timestamp_count = 0;
    28da:	41 0f 11 99 08 01 00 00 	movups %xmm3,0x108(%r9)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    28e2:	e8 b9 fa ff ff       	call   23a0 <calloc@plt>
      thread_data[x].tasks = barriers;
    28e7:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        thread_data[x].tasks[y].sending = 1;
    28ec:	44 89 7c 24 28       	mov    %r15d,0x28(%rsp)
    28f1:	89 6c 24 08          	mov    %ebp,0x8(%rsp)
    28f5:	48 89 c2             	mov    %rax,%rdx
      thread_data[x].tasks = barriers;
    28f8:	49 89 41 58          	mov    %rax,0x58(%r9)
        thread_data[x].tasks[y].sending = 1;
    28fc:	4c 89 cd             	mov    %r9,%rbp
        thread_data[x].tasks[y].protected = do_protected_write; 
    28ff:	4c 63 fb             	movslq %ebx,%r15
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2902:	be 20 00 00 00       	mov    $0x20,%esi
    2907:	bf 0c 00 00 00       	mov    $0xc,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    290c:	4f 8d 24 7f          	lea    (%r15,%r15,2),%r12
    2910:	48 8d 05 49 0e 00 00 	lea    0xe49(%rip),%rax        # 3760 <do_protected_write>
    2917:	49 c1 e4 07          	shl    $0x7,%r12
    291b:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
    291f:	49 89 85 e0 00 00 00 	mov    %rax,0xe0(%r13)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2926:	e8 75 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    292b:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    292f:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    2934:	49 89 c6             	mov    %rax,%r14
    2937:	49 89 85 28 01 00 00 	mov    %rax,0x128(%r13)
        for (int b = 0 ; b < 2 ; b++) {
    293e:	4c 8d 68 40          	lea    0x40(%rax),%r13
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2942:	be 08 00 00 00       	mov    $0x8,%esi
    2947:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    294c:	49 83 c6 20          	add    $0x20,%r14
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2950:	e8 4b fa ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2955:	be 08 00 00 00       	mov    $0x8,%esi
    295a:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    295f:	48 89 c5             	mov    %rax,%rbp
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2962:	e8 39 fa ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    2967:	be 18 00 00 00       	mov    $0x18,%esi
    296c:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2971:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    2974:	e8 27 fa ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    2979:	66 0f 6f 05 af 50 00 00 	movdqa 0x50af(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
          mailboxes[b].higher = &data[1];
    2981:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    2985:	49 89 46 e0          	mov    %rax,-0x20(%r14)
          mailboxes[b].higher = &data[1];
    2989:	49 89 76 e8          	mov    %rsi,-0x18(%r14)
          data[0].messages = messages;
    298d:	48 89 28             	mov    %rbp,(%rax)
          data[1].messages = messages2;
    2990:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    2994:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    2998:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    299c:	4d 39 f5             	cmp    %r14,%r13
    299f:	75 a1                	jne    2942 <main+0x3c2>
        char *message = malloc(sizeof(char) * 256);
    29a1:	be 01 00 00 00       	mov    $0x1,%esi
    29a6:	bf 00 01 00 00       	mov    $0x100,%edi
    29ab:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    29af:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    29b4:	e8 e7 f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    29b9:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    29be:	49 89 c5             	mov    %rax,%r13
        struct Message *messaged = malloc(sizeof(struct Message));
    29c1:	e8 4a fa ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    29c6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    29cb:	4c 89 ef             	mov    %r13,%rdi
    29ce:	41 89 d9             	mov    %ebx,%r9d
    29d1:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    29d6:	48 8d 0d e3 4b 00 00 	lea    0x4be3(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    29dd:	ba 00 01 00 00       	mov    $0x100,%edx
    29e2:	31 c0                	xor    %eax,%eax
    29e4:	be 01 00 00 00       	mov    $0x1,%esi
    29e9:	e8 32 fb ff ff       	call   2520 <__sprintf_chk@plt>
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    29ee:	48 8b 55 58          	mov    0x58(%rbp),%rdx
        messaged->thread_index = thread_data[x].thread_index;
    29f2:	48 63 45 00          	movslq 0x0(%rbp),%rax
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    29f6:	8d 4b 01             	lea    0x1(%rbx),%ecx
        messaged->message = message;
    29f9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    29fe:	be 20 00 00 00       	mov    $0x20,%esi
    2a03:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a08:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
    2a0c:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
        messaged->message = message;
    2a11:	4d 89 2a             	mov    %r13,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a14:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
        messaged->task_index = y;
    2a18:	4d 89 7a 10          	mov    %r15,0x10(%r10)
        messaged->thread_index = thread_data[x].thread_index;
    2a1c:	49 89 c7             	mov    %rax,%r15
    2a1f:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a23:	41 89 8d 48 01 00 00 	mov    %ecx,0x148(%r13)
        thread_data[x].tasks[y].message = messaged;
    2a2a:	4d 89 95 40 01 00 00 	mov    %r10,0x140(%r13)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a31:	49 c7 85 10 01 00 00 63 00 00 00 	movq   $0x63,0x110(%r13)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a3c:	e8 5f f9 ff ff       	call   23a0 <calloc@plt>
        if (y == barrier_count - 1) {
    2a41:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2a44:	41 89 5d 00          	mov    %ebx,0x0(%r13)
        if (y == barrier_count - 1) {
    2a48:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a4c:	49 89 85 08 01 00 00 	mov    %rax,0x108(%r13)
        if (y == barrier_count - 1) {
    2a53:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
        thread_data[x].tasks[y].available = 1;
    2a58:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2a62:	49 89 85 f8 00 00 00 	mov    %rax,0xf8(%r13)
        thread_data[x].tasks[y].sending = 1;
    2a69:	48 b8 01 00 00 00 0c 00 00 00 	movabs $0xc00000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2a73:	49 c7 85 18 01 00 00 00 00 00 00 	movq   $0x0,0x118(%r13)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a7e:	45 89 bd f0 00 00 00 	mov    %r15d,0xf0(%r13)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2a85:	49 89 ad e8 00 00 00 	mov    %rbp,0xe8(%r13)
        thread_data[x].tasks[y].arrived = 0;
    2a8c:	41 c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r13)
        thread_data[x].tasks[y].thread_count = 2;
    2a97:	41 c7 85 f4 00 00 00 02 00 00 00 	movl   $0x2,0xf4(%r13)
        thread_data[x].tasks[y].sending = 1;
    2aa2:	49 89 85 38 01 00 00 	mov    %rax,0x138(%r13)
        if (y == barrier_count - 1) {
    2aa9:	0f 84 28 0b 00 00    	je     35d7 <main+0x1057>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2aaf:	8b 44 24 08          	mov    0x8(%rsp),%eax
    2ab3:	39 d8                	cmp    %ebx,%eax
    2ab5:	75 61                	jne    2b18 <main+0x598>
    2ab7:	8b 74 24 20          	mov    0x20(%rsp),%esi
    2abb:	85 f6                	test   %esi,%esi
    2abd:	75 59                	jne    2b18 <main+0x598>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2abf:	89 c2                	mov    %eax,%edx
    2ac1:	bf 01 00 00 00       	mov    $0x1,%edi
    2ac6:	31 c0                	xor    %eax,%eax
    2ac8:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
    2acc:	48 8d 35 15 4b 00 00 	lea    0x4b15(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2ad3:	e8 78 f9 ff ff       	call   2450 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2ad8:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2add:	48 8b 55 58          	mov    0x58(%rbp),%rdx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2ae1:	c7 44 24 20 01 00 00 00 	movl   $0x1,0x20(%rsp)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2ae9:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2aed:	48 89 85 c0 00 00 00 	mov    %rax,0xc0(%rbp)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2af4:	48 8d 05 15 32 00 00 	lea    0x3215(%rip),%rax        # 5d10 <barriered_work_ingest>
    2afb:	4a 89 84 22 d8 00 00 00 	mov    %rax,0xd8(%rdx,%r12,1)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b03:	83 f9 03             	cmp    $0x3,%ecx
    2b06:	74 23                	je     2b2b <main+0x5ab>
    2b08:	bb 01 00 00 00       	mov    $0x1,%ebx
    2b0d:	e9 ed fd ff ff       	jmp    28ff <main+0x37f>
    2b12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            thread_data[x].tasks[y].run = barriered_work; 
    2b18:	48 8d 05 11 2d 00 00 	lea    0x2d11(%rip),%rax        # 5830 <barriered_work>
    2b1f:	49 89 85 d8 00 00 00 	mov    %rax,0xd8(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b26:	83 f9 03             	cmp    $0x3,%ecx
    2b29:	75 dd                	jne    2b08 <main+0x588>

          }
        }
      }
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b2b:	66 0f 6f 64 24 30    	movdqa 0x30(%rsp),%xmm4
    2b31:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
    2b36:	49 89 e9             	mov    %rbp,%r9
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b39:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2b43:	c7 82 80 03 00 00 00 00 00 00 	movl   $0x0,0x380(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2b4d:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    2b52:	49 81 c1 40 01 00 00 	add    $0x140,%r9
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2b59:	c7 82 00 03 00 00 02 00 00 00 	movl   $0x2,0x300(%rdx)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b63:	48 89 82 f4 03 00 00 	mov    %rax,0x3f4(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2b6a:	8b 45 00             	mov    0x0(%rbp),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2b6d:	48 89 aa e8 03 00 00 	mov    %rbp,0x3e8(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2b74:	89 82 f0 03 00 00    	mov    %eax,0x3f0(%rdx)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2b7a:	c7 82 3c 04 00 00 0c 00 00 00 	movl   $0xc,0x43c(%rdx)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2b84:	c7 82 fc 03 00 00 03 00 00 00 	movl   $0x3,0x3fc(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b8e:	0f 11 a2 d8 03 00 00 	movups %xmm4,0x3d8(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2b95:	41 83 ff 0f          	cmp    $0xf,%r15d
    2b99:	0f 85 b1 fb ff ff    	jne    2750 <main+0x1d0>
    2b9f:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    2ba4:	ba 0d 00 00 00       	mov    $0xd,%edx
    2ba9:	48 8d 35 68 47 00 00 	lea    0x4768(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2bb0:	31 c0                	xor    %eax,%eax
    2bb2:	bf 01 00 00 00       	mov    $0x1,%edi
    2bb7:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    2bbc:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2bc1:	e8 8a f8 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2bc6:	be 08 00 00 00       	mov    $0x8,%esi
    2bcb:	bf 02 00 00 00       	mov    $0x2,%edi
    2bd0:	e8 cb f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2bd5:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bda:	bf 0f 00 00 00       	mov    $0xf,%edi
    my_thread_data[0] = &thread_data[x]; 
    2bdf:	4d 8d ba 40 10 00 00 	lea    0x1040(%r10),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2be6:	4d 8d b2 80 02 00 00 	lea    0x280(%r10),%r14
    thread_data[x].threads = my_thread_data;
    2bed:	49 89 82 80 10 00 00 	mov    %rax,0x1080(%r10)
    my_thread_data[0] = &thread_data[x]; 
    2bf4:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2bf7:	49 8d 8a c0 03 00 00 	lea    0x3c0(%r10),%rcx
    2bfe:	49 8d 92 40 06 00 00 	lea    0x640(%r10),%rdx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c05:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c09:	49 8b 42 58          	mov    0x58(%r10),%rax
    2c0d:	4d 8d 9a c0 08 00 00 	lea    0x8c0(%r10),%r11
    2c14:	4d 8d 82 00 0a 00 00 	lea    0xa00(%r10),%r8
    2c1b:	49 8d b2 00 05 00 00 	lea    0x500(%r10),%rsi
    2c22:	49 8d 9a 80 07 00 00 	lea    0x780(%r10),%rbx
    thread_data[x].thread_count = 2;
    2c29:	41 c7 82 88 10 00 00 02 00 00 00 	movl   $0x2,0x1088(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2c34:	48 89 4c 24 58       	mov    %rcx,0x58(%rsp)
    2c39:	4d 8d 8a 40 0b 00 00 	lea    0xb40(%r10),%r9
    2c40:	4d 8d a2 80 0c 00 00 	lea    0xc80(%r10),%r12
    2c47:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    2c4c:	4d 8d aa c0 0d 00 00 	lea    0xdc0(%r10),%r13
    thread_data[x].thread_index = 0;
    2c53:	41 c7 82 40 10 00 00 00 00 00 00 	movl   $0x0,0x1040(%r10)
    thread_data[x].task_count = total_barrier_count;
    2c5e:	41 c7 82 a0 10 00 00 03 00 00 00 	movl   $0x3,0x10a0(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2c69:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2c73:	49 8d 82 40 01 00 00 	lea    0x140(%r10),%rax
    2c7a:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2c7f:	49 8b 82 98 01 00 00 	mov    0x198(%r10),%rax
    2c86:	4c 89 5c 24 20       	mov    %r11,0x20(%rsp)
    2c8b:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2c95:	49 8b 82 d8 02 00 00 	mov    0x2d8(%r10),%rax
    2c9c:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    2ca1:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2cab:	49 8b 82 18 04 00 00 	mov    0x418(%r10),%rax
    my_thread_data[0] = &thread_data[x]; 
    2cb2:	4c 89 7c 24 70       	mov    %r15,0x70(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2cb7:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2cc1:	49 8b 82 58 05 00 00 	mov    0x558(%r10),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2cc8:	4c 89 74 24 78       	mov    %r14,0x78(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2ccd:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2cd7:	49 8b 82 98 06 00 00 	mov    0x698(%r10),%rax
    2cde:	48 89 74 24 50       	mov    %rsi,0x50(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ce3:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2ce8:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2cf2:	49 8b 82 d8 07 00 00 	mov    0x7d8(%r10),%rax
    2cf9:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    2cfe:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2d08:	49 8b 82 18 09 00 00 	mov    0x918(%r10),%rax
    2d0f:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2d19:	49 8b 82 58 0a 00 00 	mov    0xa58(%r10),%rax
    2d20:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2d25:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2d2f:	49 8b 82 98 0b 00 00 	mov    0xb98(%r10),%rax
    2d36:	4c 89 94 24 80 00 00 00 	mov    %r10,0x80(%rsp)
    2d3e:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2d48:	49 8b 82 d8 0c 00 00 	mov    0xcd8(%r10),%rax
    2d4f:	4c 89 64 24 30       	mov    %r12,0x30(%rsp)
    2d54:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    2d5e:	49 8b 82 18 0e 00 00 	mov    0xe18(%r10),%rax
    2d65:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    2d6a:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d74:	e8 27 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d79:	be 38 00 00 00       	mov    $0x38,%esi
    2d7e:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d83:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d86:	e8 15 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d8b:	be 38 00 00 00       	mov    $0x38,%esi
    2d90:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d95:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d98:	e8 03 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d9d:	be 38 00 00 00       	mov    $0x38,%esi
    2da2:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2da7:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2daf:	e8 ec f5 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2db4:	be 08 00 00 00       	mov    $0x8,%esi
    2db9:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dbe:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2dc6:	e8 d5 f5 ff ff       	call   23a0 <calloc@plt>
  thread_data[thread_count].type = TIMER;
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2dcb:	be 08 00 00 00       	mov    $0x8,%esi
    2dd0:	bf 0f 00 00 00       	mov    $0xf,%edi
  thread_data[thread_count].type = TIMER;
    2dd5:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2ddd:	49 89 c5             	mov    %rax,%r13
  thread_data[thread_count].task_count = total_barrier_count;
    2de0:	48 8b 05 69 4c 00 00 	mov    0x4c69(%rip),%rax        # 7a50 <_IO_stdin_used+0xa50>
  thread_data[thread_count].type = TIMER;
    2de7:	41 c7 82 08 0f 00 00 00 00 00 00 	movl   $0x0,0xf08(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2df2:	49 89 82 60 0f 00 00 	mov    %rax,0xf60(%r10)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2df9:	e8 a2 f5 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2dfe:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    2e03:	48 8b 4c 24 58       	mov    0x58(%rsp),%rcx
    2e08:	48 8b 74 24 50       	mov    0x50(%rsp),%rsi
    2e0d:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    2e12:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2e16:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    2e1b:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2e20:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2e24:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    2e29:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
    2e31:	48 89 48 18          	mov    %rcx,0x18(%rax)
    2e35:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2e3a:	48 89 70 20          	mov    %rsi,0x20(%rax)
    2e3e:	48 8d 35 e2 44 00 00 	lea    0x44e2(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2e45:	48 89 78 30          	mov    %rdi,0x30(%rax)
    2e49:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    2e4e:	4d 8d b2 00 0f 00 00 	lea    0xf00(%r10),%r14
    2e55:	4c 89 10             	mov    %r10,(%rax)
    2e58:	48 89 78 50          	mov    %rdi,0x50(%rax)
    2e5c:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    2e61:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2e65:	ba 0c 00 00 00       	mov    $0xc,%edx
    2e6a:	48 89 78 58          	mov    %rdi,0x58(%rax)
    2e6e:	49 8d ba 80 11 00 00 	lea    0x1180(%r10),%rdi
    2e75:	4c 89 58 38          	mov    %r11,0x38(%rax)
    2e79:	4c 89 40 40          	mov    %r8,0x40(%rax)
    2e7d:	4c 89 48 48          	mov    %r9,0x48(%rax)
    2e81:	4c 89 70 60          	mov    %r14,0x60(%rax)
    2e85:	4c 89 78 68          	mov    %r15,0x68(%rax)
    2e89:	4c 8d 3d 90 09 00 00 	lea    0x990(%rip),%r15        # 3820 <barriered_thread>
    2e90:	48 89 78 70          	mov    %rdi,0x70(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2e94:	49 89 82 40 0f 00 00 	mov    %rax,0xf40(%r10)
    2e9b:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2e9d:	41 c7 82 48 0f 00 00 0c 00 00 00 	movl   $0xc,0xf48(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2ea8:	41 c7 82 50 0f 00 00 02 00 00 00 	movl   $0x2,0xf50(%r10)
  thread_data[thread_count].thread_index = 0;
    2eb3:	41 c7 82 00 0f 00 00 00 00 00 00 	movl   $0x0,0xf00(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2ebe:	48 89 bc 24 80 00 00 00 	mov    %rdi,0x80(%rsp)
    2ec6:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].thread_index = 0;
    2ecb:	4c 89 94 24 98 00 00 00 	mov    %r10,0x98(%rsp)
    2ed3:	e8 78 f5 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2ed8:	48 8d b3 a0 02 00 00 	lea    0x2a0(%rbx),%rsi
    2edf:	49 8d 7d 60          	lea    0x60(%r13),%rdi
    2ee3:	4c 89 f1             	mov    %r14,%rcx
    2ee6:	4c 89 eb             	mov    %r13,%rbx
  for (int x = 0 ; x < thread_count ; x++) {
    2ee9:	45 31 f6             	xor    %r14d,%r14d
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2eec:	48 8d 15 cd 0c 00 00 	lea    0xccd(%rip),%rdx        # 3bc0 <timer_thread>
    2ef3:	e8 78 f5 ff ff       	call   2470 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2ef8:	45 89 f5             	mov    %r14d,%r13d
    2efb:	49 89 de             	mov    %rbx,%r14
    thread_data[x].type = WORKER;
    2efe:	c7 45 08 01 00 00 00 	movl   $0x1,0x8(%rbp)
    2f05:	44 89 ea             	mov    %r13d,%edx
    2f08:	bf 01 00 00 00       	mov    $0x1,%edi
    2f0d:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2f0f:	c7 45 64 01 00 00 00 	movl   $0x1,0x64(%rbp)
    2f16:	48 8d 35 eb 46 00 00 	lea    0x46eb(%rip),%rsi        # 7608 <_IO_stdin_used+0x608>
  for (int x = 0 ; x < thread_count ; x++) {
    2f1d:	41 83 c5 01          	add    $0x1,%r13d
    2f21:	e8 2a f5 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2f26:	48 89 e9             	mov    %rbp,%rcx
    2f29:	4c 89 e6             	mov    %r12,%rsi
    2f2c:	48 89 df             	mov    %rbx,%rdi
    2f2f:	4c 89 fa             	mov    %r15,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2f32:	48 81 c5 40 01 00 00 	add    $0x140,%rbp
    2f39:	48 83 c3 08          	add    $0x8,%rbx
    2f3d:	49 83 c4 38          	add    $0x38,%r12
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2f41:	e8 2a f5 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2f46:	48 8b 55 e0          	mov    -0x20(%rbp),%rdx
    2f4a:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    2f4e:	be 08 00 00 00       	mov    $0x8,%esi
    2f53:	e8 88 f3 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2f58:	41 83 fd 0c          	cmp    $0xc,%r13d
    2f5c:	75 a0                	jne    2efe <main+0x97e>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2f5e:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2f66:	48 8b 1d eb 4a 00 00 	mov    0x4aeb(%rip),%rbx        # 7a58 <_IO_stdin_used+0xa58>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f6d:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    2f72:	4d 89 f5             	mov    %r14,%r13
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f75:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    2f7a:	49 89 9a a0 10 00 00 	mov    %rbx,0x10a0(%r10)
    thread_data[x].type = IO;
    2f81:	41 c7 82 48 10 00 00 02 00 00 00 	movl   $0x2,0x1048(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f8c:	e8 0f f4 ff ff       	call   23a0 <calloc@plt>
    2f91:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f99:	be 00 08 00 00       	mov    $0x800,%esi
    2f9e:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2fa0:	49 89 82 08 11 00 00 	mov    %rax,0x1108(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2fa7:	e8 04 f5 ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2fac:	be 08 00 00 00       	mov    $0x8,%esi
    2fb1:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2fb6:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    2fbe:	41 89 82 10 11 00 00 	mov    %eax,0x1110(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2fc5:	e8 d6 f3 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    2fca:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    2fcf:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
    2fd4:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    2fdc:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2fe1:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    2fe6:	4c 8b 74 24 78       	mov    0x78(%rsp),%r14
    2feb:	4c 89 58 48          	mov    %r11,0x48(%rax)
    2fef:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    2ff4:	4c 8b 7c 24 60       	mov    0x60(%rsp),%r15
    2ff9:	4c 89 40 50          	mov    %r8,0x50(%rax)
    2ffd:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    3002:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3007:	4c 89 48 58          	mov    %r9,0x58(%rax)
    300b:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    3010:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    3015:	4c 89 10             	mov    %r10,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    3018:	49 89 82 80 10 00 00 	mov    %rax,0x1080(%r10)
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    301f:	41 c7 82 88 10 00 00 0c 00 00 00 	movl   $0xc,0x1088(%r10)
    thread_data[x].thread_index = x;
    302a:	41 c7 82 40 10 00 00 0d 00 00 00 	movl   $0xd,0x1040(%r10)
      my_thread_data[n] = &thread_data[n]; 
    3035:	4c 89 70 10          	mov    %r14,0x10(%rax)
    3039:	48 89 68 18          	mov    %rbp,0x18(%rax)
    303d:	4c 89 60 20          	mov    %r12,0x20(%rax)
    3041:	48 89 78 28          	mov    %rdi,0x28(%rax)
    3045:	bf 01 00 00 00       	mov    $0x1,%edi
    304a:	48 89 48 30          	mov    %rcx,0x30(%rax)
    304e:	48 89 70 38          	mov    %rsi,0x38(%rax)
    3052:	48 8d 35 ec 42 00 00 	lea    0x42ec(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    3059:	48 89 50 40          	mov    %rdx,0x40(%rax)
    305d:	ba 0d 00 00 00       	mov    $0xd,%edx
    3062:	4c 89 78 08          	mov    %r15,0x8(%rax)
    3066:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3068:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    306d:	e8 de f3 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3072:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    3077:	49 8d 7d 68          	lea    0x68(%r13),%rdi
    307b:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    3083:	48 8d 15 a6 1d 00 00 	lea    0x1da6(%rip),%rdx        # 4e30 <io_thread>
    308a:	48 05 d8 02 00 00    	add    $0x2d8,%rax
    3090:	48 89 c6             	mov    %rax,%rsi
    3093:	e8 d8 f3 ff ff       	call   2470 <pthread_create@plt>
    3098:	ba 0e 00 00 00       	mov    $0xe,%edx
    309d:	48 8d 35 b8 42 00 00 	lea    0x42b8(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    30a4:	31 c0                	xor    %eax,%eax
    30a6:	bf 01 00 00 00       	mov    $0x1,%edi
    30ab:	e8 a0 f3 ff ff       	call   2450 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    30b0:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    30b5:	48 8b 44 24 48       	mov    0x48(%rsp),%rax

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    30ba:	be 08 00 00 00       	mov    $0x8,%esi
    30bf:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x].task_count = 0;
    30c4:	49 89 9a e0 11 00 00 	mov    %rbx,0x11e0(%r10)
    30cb:	31 db                	xor    %ebx,%ebx
    thread_data[x].type = EXTERNAL;
    30cd:	41 c7 82 88 11 00 00 03 00 00 00 	movl   $0x3,0x1188(%r10)
    thread_data[x].buffers = &buffers[buffer_index];
    30d8:	49 89 82 40 12 00 00 	mov    %rax,0x1240(%r10)
    30df:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    30e4:	e8 b7 f2 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    30e9:	4c 8b 54 24 48       	mov    0x48(%rsp),%r10
    30ee:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    30f3:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    30f8:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    30fd:	4c 89 70 10          	mov    %r14,0x10(%rax)
    3101:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    3106:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    310b:	4c 89 10             	mov    %r10,(%rax)
    310e:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
    3113:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3118:	48 89 68 18          	mov    %rbp,0x18(%rax)
    311c:	48 8d 2d 74 42 00 00 	lea    0x4274(%rip),%rbp        # 7397 <_IO_stdin_used+0x397>
    3123:	4c 89 60 20          	mov    %r12,0x20(%rax)
    3127:	4c 8d a4 24 a0 00 00 00 	lea    0xa0(%rsp),%r12
    312f:	48 89 78 28          	mov    %rdi,0x28(%rax)
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3133:	49 8d 7d 70          	lea    0x70(%r13),%rdi
      my_thread_data[n] = &thread_data[n]; 
    3137:	48 89 48 30          	mov    %rcx,0x30(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    313b:	48 8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%rcx
      my_thread_data[n] = &thread_data[n]; 
    3143:	48 89 70 38          	mov    %rsi,0x38(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3147:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    314f:	48 89 50 40          	mov    %rdx,0x40(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3153:	48 8d 15 a6 09 00 00 	lea    0x9a6(%rip),%rdx        # 3b00 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    315a:	4c 89 58 48          	mov    %r11,0x48(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    315e:	48 81 c6 10 03 00 00 	add    $0x310,%rsi
      my_thread_data[n] = &thread_data[n]; 
    3165:	4c 89 40 50          	mov    %r8,0x50(%rax)
    3169:	4c 89 48 58          	mov    %r9,0x58(%rax)
    thread_data[x].threads = my_thread_data;
    316d:	49 89 82 c0 11 00 00 	mov    %rax,0x11c0(%r10)
      my_thread_data[n] = &thread_data[n]; 
    3174:	4c 89 78 08          	mov    %r15,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3178:	48 8b 05 e1 48 00 00 	mov    0x48e1(%rip),%rax        # 7a60 <_IO_stdin_used+0xa60>
    thread_data[x].thread_index = x;
    317f:	41 c7 82 80 11 00 00 0e 00 00 00 	movl   $0xe,0x1180(%r10)
    thread_data[x].thread_count = thread_count;
    318a:	49 89 82 c8 11 00 00 	mov    %rax,0x11c8(%r10)
    thread_data[x].thread_index = x;
    3191:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3196:	e8 d5 f2 ff ff       	call   2470 <pthread_create@plt>
    319b:	48 8d 3d d7 41 00 00 	lea    0x41d7(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    31a2:	e8 49 f1 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    31a7:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    31ac:	0f 1f 40 00          	nopl   0x0(%rax)
    void * result; 
    pthread_join(thread[x], &result);
    31b0:	49 8b 7c dd 00       	mov    0x0(%r13,%rbx,8),%rdi
    31b5:	4c 89 e6             	mov    %r12,%rsi
    31b8:	e8 33 f3 ff ff       	call   24f0 <pthread_join@plt>
    31bd:	89 da                	mov    %ebx,%edx
    31bf:	48 89 ee             	mov    %rbp,%rsi
    31c2:	bf 01 00 00 00       	mov    $0x1,%edi
    31c7:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    31c9:	48 83 c3 01          	add    $0x1,%rbx
    31cd:	e8 7e f2 ff ff       	call   2450 <__printf_chk@plt>
    31d2:	48 83 fb 0f          	cmp    $0xf,%rbx
    31d6:	75 d8                	jne    31b0 <main+0xc30>
    31d8:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    31dd:	4d 8d 6e 58          	lea    0x58(%r14),%r13
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
    31e1:	45 31 ff             	xor    %r15d,%r15d
  long sents = 0;
  long received = 0;
    31e4:	31 db                	xor    %ebx,%ebx
  for (int x = 0 ; x < thread_count ; x++) {
    31e6:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  long sents = 0;
    31ee:	31 ed                	xor    %ebp,%ebp
  long ingests = 0;
    31f0:	45 31 c9             	xor    %r9d,%r9d
    31f3:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    31f8:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    31fd:	4d 89 ee             	mov    %r13,%r14
    3200:	4d 89 fd             	mov    %r15,%r13
    if (x % 2 == 1) {
    3203:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    3207:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    320c:	89 f8                	mov    %edi,%eax
    320e:	41 89 fc             	mov    %edi,%r12d
      other = (x + 1) % total_threads;
    3211:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
    3214:	83 e0 01             	and    $0x1,%eax
      other = abs(x - 1) % total_threads;
    3217:	41 83 ec 01          	sub    $0x1,%r12d
      other = (x + 1) % total_threads;
    321b:	89 7c 24 10          	mov    %edi,0x10(%rsp)
      other = abs(x - 1) % total_threads;
    321f:	85 c0                	test   %eax,%eax
    3221:	44 0f 44 e7          	cmove  %edi,%r12d
    3225:	bf 0a 00 00 00       	mov    $0xa,%edi
    322a:	e8 a1 f0 ff ff       	call   22d0 <putchar@plt>
    322f:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3234:	bf 01 00 00 00       	mov    $0x1,%edi
    3239:	48 8d 35 6b 41 00 00 	lea    0x416b(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    3240:	48 8b 10             	mov    (%rax),%rdx
    3243:	31 c0                	xor    %eax,%eax
    3245:	e8 06 f2 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    324a:	49 63 56 08          	movslq 0x8(%r14),%rdx
    324e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3253:	85 d2                	test   %edx,%edx
    3255:	0f 8e 09 04 00 00    	jle    3664 <main+0x10e4>
    325b:	49 8b 06             	mov    (%r14),%rax
    325e:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
    long v = 0;
    3262:	31 d2                	xor    %edx,%edx
    3264:	48 c1 e6 07          	shl    $0x7,%rsi
    3268:	48 05 d0 00 00 00    	add    $0xd0,%rax
    326e:	48 01 c6             	add    %rax,%rsi
    3271:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      v += thread_data[me].tasks[n].v;
    3278:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    327b:	48 05 80 01 00 00    	add    $0x180,%rax
    3281:	48 39 f0             	cmp    %rsi,%rax
    3284:	75 f2                	jne    3278 <main+0xcf8>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3286:	4d 63 e4             	movslq %r12d,%r12
    3289:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    328e:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    3292:	48 c1 e0 06          	shl    $0x6,%rax
    3296:	48 01 f8             	add    %rdi,%rax
    3299:	48 63 70 60          	movslq 0x60(%rax),%rsi
    329d:	85 f6                	test   %esi,%esi
    329f:	7e 2d                	jle    32ce <main+0xd4e>
      v += thread_data[other].tasks[n].v;
    32a1:	48 8b 40 58          	mov    0x58(%rax),%rax
    32a5:	48 8d 34 76          	lea    (%rsi,%rsi,2),%rsi
    32a9:	48 c1 e6 07          	shl    $0x7,%rsi
    32ad:	48 05 d0 00 00 00    	add    $0xd0,%rax
    32b3:	48 01 c6             	add    %rax,%rsi
    32b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    32c0:	48 03 10             	add    (%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    32c3:	48 05 80 01 00 00    	add    $0x180,%rax
    32c9:	48 39 f0             	cmp    %rsi,%rax
    32cc:	75 f2                	jne    32c0 <main+0xd40>
    32ce:	48 8d 35 eb 40 00 00 	lea    0x40eb(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    32d5:	bf 01 00 00 00       	mov    $0x1,%edi
    32da:	31 c0                	xor    %eax,%eax
    32dc:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    32e1:	e8 6a f1 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    32e6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    32eb:	bf 01 00 00 00       	mov    $0x1,%edi
    32f0:	48 8b 30             	mov    (%rax),%rsi
    32f3:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    32fd:	48 f7 ee             	imul   %rsi
    3300:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3304:	31 c0                	xor    %eax,%eax
    3306:	48 d1 fa             	sar    %rdx
    3309:	48 29 f2             	sub    %rsi,%rdx
    330c:	48 8d 35 1d 43 00 00 	lea    0x431d(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    3313:	e8 38 f1 ff ff       	call   2450 <__printf_chk@plt>
    3318:	bf 0a 00 00 00       	mov    $0xa,%edi
    331d:	e8 ae ef ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3322:	49 63 46 08          	movslq 0x8(%r14),%rax
    3326:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    332b:	85 c0                	test   %eax,%eax
    332d:	0f 8e d2 00 00 00    	jle    3405 <main+0xe85>
    3333:	49 8b 3e             	mov    (%r14),%rdi
    3336:	48 8d 34 40          	lea    (%rax,%rax,2),%rsi
    333a:	48 c1 e6 07          	shl    $0x7,%rsi
    333e:	48 8d 97 c8 00 00 00 	lea    0xc8(%rdi),%rdx
    3345:	48 01 d6             	add    %rdx,%rsi
    3348:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3350:	48 8b 42 60          	mov    0x60(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    3354:	4c 03 0a             	add    (%rdx),%r9
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3357:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
      ingests += thread_data[x].tasks[n].ingest_count;
    335e:	4c 03 ba d8 fe ff ff 	add    -0x128(%rdx),%r15
      sends += thread_data[x].tasks[n].sends;
    3365:	4c 03 aa e8 fe ff ff 	add    -0x118(%rdx),%r13
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    336c:	48 03 68 10          	add    0x10(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3370:	48 03 58 18          	add    0x18(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3374:	48 03 68 30          	add    0x30(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3378:	48 03 58 38          	add    0x38(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    337c:	48 03 68 50          	add    0x50(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3380:	48 03 58 58          	add    0x58(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3384:	48 03 68 70          	add    0x70(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3388:	48 03 58 78          	add    0x78(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    338c:	48 03 a8 90 00 00 00 	add    0x90(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3393:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    339a:	48 03 a8 b0 00 00 00 	add    0xb0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33a1:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33a8:	48 03 a8 d0 00 00 00 	add    0xd0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33af:	48 03 98 d8 00 00 00 	add    0xd8(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33b6:	48 03 a8 f0 00 00 00 	add    0xf0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33bd:	48 03 98 f8 00 00 00 	add    0xf8(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33c4:	48 03 a8 10 01 00 00 	add    0x110(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33cb:	48 03 98 18 01 00 00 	add    0x118(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33d2:	48 03 a8 30 01 00 00 	add    0x130(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33d9:	48 03 98 38 01 00 00 	add    0x138(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33e0:	48 03 a8 50 01 00 00 	add    0x150(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33e7:	48 03 98 58 01 00 00 	add    0x158(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33ee:	48 03 a8 70 01 00 00 	add    0x170(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33f5:	48 03 98 78 01 00 00 	add    0x178(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    33fc:	48 39 f2             	cmp    %rsi,%rdx
    33ff:	0f 85 4b ff ff ff    	jne    3350 <main+0xdd0>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3405:	45 31 e4             	xor    %r12d,%r12d
    3408:	49 83 be b8 00 00 00 00 	cmpq   $0x0,0xb8(%r14)
    3410:	7e 7a                	jle    348c <main+0xf0c>
    3412:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    3417:	4c 89 f3             	mov    %r14,%rbx
    341a:	4d 89 e6             	mov    %r12,%r14
    341d:	4d 89 cc             	mov    %r9,%r12
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3420:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    3427:	4b 8d 14 b6          	lea    (%r14,%r14,4),%rdx
    342b:	48 83 ec 08          	sub    $0x8,%rsp
    342f:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3434:	49 83 c6 01          	add    $0x1,%r14
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3438:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    343c:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3446:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    344a:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    344e:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3451:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3455:	4c 2b 01             	sub    (%rcx),%r8
    3458:	31 c0                	xor    %eax,%eax
    345a:	8b 49 20             	mov    0x20(%rcx),%ecx
    345d:	56                   	push   %rsi
    345e:	48 8d 35 eb 41 00 00 	lea    0x41eb(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    3465:	48 c1 ea 12          	shr    $0x12,%rdx
    3469:	49 89 d1             	mov    %rdx,%r9
    346c:	ba 02 00 00 00       	mov    $0x2,%edx
    3471:	e8 da ef ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3476:	58                   	pop    %rax
    3477:	5a                   	pop    %rdx
    3478:	4c 3b b3 b8 00 00 00 	cmp    0xb8(%rbx),%r14
    347f:	7c 9f                	jl     3420 <main+0xea0>
    3481:	49 89 de             	mov    %rbx,%r14
    3484:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    3489:	4d 89 e1             	mov    %r12,%r9
  for (int x = 0 ; x < thread_count ; x++) {
    348c:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    3492:	49 81 c6 40 01 00 00 	add    $0x140,%r14
    3499:	83 7c 24 10 0c       	cmpl   $0xc,0x10(%rsp)
    349e:	0f 85 5f fd ff ff    	jne    3203 <main+0xc83>
    34a4:	4d 89 ce             	mov    %r9,%r14
    34a7:	bf 01 00 00 00       	mov    $0x1,%edi
    34ac:	31 c0                	xor    %eax,%eax
    34ae:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    34b3:	4c 89 f2             	mov    %r14,%rdx
    34b6:	48 8d 35 10 3f 00 00 	lea    0x3f10(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    34bd:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    34c7:	e8 84 ef ff ff       	call   2450 <__printf_chk@plt>
    34cc:	bf 0a 00 00 00       	mov    $0xa,%edi
    34d1:	e8 fa ed ff ff       	call   22d0 <putchar@plt>
    34d6:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    34db:	bf 01 00 00 00       	mov    $0x1,%edi
    34e0:	48 8d 35 b9 41 00 00 	lea    0x41b9(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    34e7:	48 8b 50 08          	mov    0x8(%rax),%rdx
    34eb:	31 c0                	xor    %eax,%eax
    34ed:	e8 5e ef ff ff       	call   2450 <__printf_chk@plt>
    34f2:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    34f7:	bf 01 00 00 00       	mov    $0x1,%edi
    34fc:	48 8d 35 c5 41 00 00 	lea    0x41c5(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    3503:	4c 89 c8             	mov    %r9,%rax
    3506:	49 c1 f9 3f          	sar    $0x3f,%r9
    350a:	49 f7 ec             	imul   %r12
    350d:	31 c0                	xor    %eax,%eax
    350f:	48 d1 fa             	sar    %rdx
    3512:	4c 29 ca             	sub    %r9,%rdx
    3515:	e8 36 ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    351a:	4c 89 e8             	mov    %r13,%rax
    351d:	4d 89 eb             	mov    %r13,%r11
    3520:	bf 01 00 00 00       	mov    $0x1,%edi
    3525:	49 f7 ec             	imul   %r12
    3528:	49 c1 fb 3f          	sar    $0x3f,%r11
    352c:	48 8d 35 c5 41 00 00 	lea    0x41c5(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    3533:	31 c0                	xor    %eax,%eax
    3535:	48 d1 fa             	sar    %rdx
    3538:	4c 29 da             	sub    %r11,%rdx
    353b:	e8 10 ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3540:	4c 89 f0             	mov    %r14,%rax
    3543:	4c 89 f1             	mov    %r14,%rcx
    3546:	bf 01 00 00 00       	mov    $0x1,%edi
    354b:	49 f7 ec             	imul   %r12
    354e:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3552:	48 8d 35 cf 41 00 00 	lea    0x41cf(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    3559:	31 c0                	xor    %eax,%eax
    355b:	48 d1 fa             	sar    %rdx
    355e:	48 29 ca             	sub    %rcx,%rdx
    3561:	e8 ea ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3566:	48 89 e8             	mov    %rbp,%rax
    3569:	48 c1 fd 3f          	sar    $0x3f,%rbp
    356d:	48 8d 35 6d 3e 00 00 	lea    0x3e6d(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    3574:	49 f7 ec             	imul   %r12
    3577:	bf 01 00 00 00       	mov    $0x1,%edi
    357c:	31 c0                	xor    %eax,%eax
    357e:	48 d1 fa             	sar    %rdx
    3581:	48 29 ea             	sub    %rbp,%rdx
    3584:	e8 c7 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3589:	48 89 d8             	mov    %rbx,%rax
    358c:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3590:	48 8d 35 5b 3e 00 00 	lea    0x3e5b(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    3597:	49 f7 ec             	imul   %r12
    359a:	bf 01 00 00 00       	mov    $0x1,%edi
    359f:	48 d1 fa             	sar    %rdx
    35a2:	48 29 da             	sub    %rbx,%rdx
    35a5:	31 c0                	xor    %eax,%eax
    35a7:	e8 a4 ee ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    35ac:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    35b4:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    35bd:	0f 85 a8 00 00 00    	jne    366b <main+0x10eb>
    35c3:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    35ca:	31 c0                	xor    %eax,%eax
    35cc:	5b                   	pop    %rbx
    35cd:	5d                   	pop    %rbp
    35ce:	41 5c                	pop    %r12
    35d0:	41 5d                	pop    %r13
    35d2:	41 5e                	pop    %r14
    35d4:	41 5f                	pop    %r15
    35d6:	c3                   	ret
          thread_data[x].tasks[y].run = barriered_work; 
    35d7:	48 8d 05 52 22 00 00 	lea    0x2252(%rip),%rax        # 5830 <barriered_work>
    35de:	bb 02 00 00 00       	mov    $0x2,%ebx
    35e3:	49 89 85 d8 00 00 00 	mov    %rax,0xd8(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    35ea:	e9 10 f3 ff ff       	jmp    28ff <main+0x37f>
      other = (x + 1) % total_threads;
    35ef:	b8 89 88 88 88       	mov    $0x88888889,%eax
    35f4:	45 89 fe             	mov    %r15d,%r14d
      my_thread_data[0] = &thread_data[x]; 
    35f7:	4d 89 4d 00          	mov    %r9,0x0(%r13)
    35fb:	4c 89 c9             	mov    %r9,%rcx
      other = (x + 1) % total_threads;
    35fe:	4c 0f af f0          	imul   %rax,%r14
    3602:	89 ea                	mov    %ebp,%edx
    3604:	bf 01 00 00 00       	mov    $0x1,%edi
    3609:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].thread_index = 0;
    360e:	41 c7 01 00 00 00 00 	movl   $0x0,(%r9)
    3615:	48 8d 35 ed 3c 00 00 	lea    0x3ced(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      other = (x + 1) % total_threads;
    361c:	49 c1 ee 23          	shr    $0x23,%r14
    3620:	44 89 f0             	mov    %r14d,%eax
    3623:	c1 e0 04             	shl    $0x4,%eax
    3626:	44 29 f0             	sub    %r14d,%eax
    3629:	45 89 fe             	mov    %r15d,%r14d
    362c:	41 29 c6             	sub    %eax,%r14d
      my_thread_data[1] = &thread_data[other]; 
    362f:	49 63 c6             	movslq %r14d,%rax
    3632:	4c 8d 04 80          	lea    (%rax,%rax,4),%r8
    3636:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    363b:	49 c1 e0 06          	shl    $0x6,%r8
    363f:	49 01 c0             	add    %rax,%r8
    3642:	31 c0                	xor    %eax,%eax
    3644:	4d 89 45 08          	mov    %r8,0x8(%r13)
    3648:	e8 03 ee ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    364d:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    3652:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3657:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    365c:	49 89 c4             	mov    %rax,%r12
    365f:	e9 70 f1 ff ff       	jmp    27d4 <main+0x254>
    long v = 0;
    3664:	31 d2                	xor    %edx,%edx
    3666:	e9 1b fc ff ff       	jmp    3286 <main+0xd06>
}
    366b:	e8 c0 ec ff ff       	call   2330 <__stack_chk_fail@plt>

0000000000003670 <_start>:
    3670:	f3 0f 1e fa          	endbr64
    3674:	31 ed                	xor    %ebp,%ebp
    3676:	49 89 d1             	mov    %rdx,%r9
    3679:	5e                   	pop    %rsi
    367a:	48 89 e2             	mov    %rsp,%rdx
    367d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3681:	50                   	push   %rax
    3682:	54                   	push   %rsp
    3683:	45 31 c0             	xor    %r8d,%r8d
    3686:	31 c9                	xor    %ecx,%ecx
    3688:	48 8d 3d f1 ee ff ff 	lea    -0x110f(%rip),%rdi        # 2580 <main>
    368f:	ff 15 43 69 00 00    	call   *0x6943(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3695:	f4                   	hlt
    3696:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000036a0 <deregister_tm_clones>:
    36a0:	48 8d 3d 79 69 00 00 	lea    0x6979(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    36a7:	48 8d 05 72 69 00 00 	lea    0x6972(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    36ae:	48 39 f8             	cmp    %rdi,%rax
    36b1:	74 15                	je     36c8 <deregister_tm_clones+0x28>
    36b3:	48 8b 05 26 69 00 00 	mov    0x6926(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    36ba:	48 85 c0             	test   %rax,%rax
    36bd:	74 09                	je     36c8 <deregister_tm_clones+0x28>
    36bf:	ff e0                	jmp    *%rax
    36c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    36c8:	c3                   	ret
    36c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000036d0 <register_tm_clones>:
    36d0:	48 8d 3d 49 69 00 00 	lea    0x6949(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    36d7:	48 8d 35 42 69 00 00 	lea    0x6942(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    36de:	48 29 fe             	sub    %rdi,%rsi
    36e1:	48 89 f0             	mov    %rsi,%rax
    36e4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    36e8:	48 c1 f8 03          	sar    $0x3,%rax
    36ec:	48 01 c6             	add    %rax,%rsi
    36ef:	48 d1 fe             	sar    %rsi
    36f2:	74 14                	je     3708 <register_tm_clones+0x38>
    36f4:	48 8b 05 f5 68 00 00 	mov    0x68f5(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    36fb:	48 85 c0             	test   %rax,%rax
    36fe:	74 08                	je     3708 <register_tm_clones+0x38>
    3700:	ff e0                	jmp    *%rax
    3702:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3708:	c3                   	ret
    3709:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003710 <__do_global_dtors_aux>:
    3710:	f3 0f 1e fa          	endbr64
    3714:	80 3d 0d 69 00 00 00 	cmpb   $0x0,0x690d(%rip)        # a028 <completed.0>
    371b:	75 2b                	jne    3748 <__do_global_dtors_aux+0x38>
    371d:	55                   	push   %rbp
    371e:	48 83 3d d2 68 00 00 00 	cmpq   $0x0,0x68d2(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3726:	48 89 e5             	mov    %rsp,%rbp
    3729:	74 0c                	je     3737 <__do_global_dtors_aux+0x27>
    372b:	48 8b 3d d6 68 00 00 	mov    0x68d6(%rip),%rdi        # a008 <__dso_handle>
    3732:	e8 79 eb ff ff       	call   22b0 <__cxa_finalize@plt>
    3737:	e8 64 ff ff ff       	call   36a0 <deregister_tm_clones>
    373c:	c6 05 e5 68 00 00 01 	movb   $0x1,0x68e5(%rip)        # a028 <completed.0>
    3743:	5d                   	pop    %rbp
    3744:	c3                   	ret
    3745:	0f 1f 00             	nopl   (%rax)
    3748:	c3                   	ret
    3749:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003750 <frame_dummy>:
    3750:	f3 0f 1e fa          	endbr64
    3754:	e9 77 ff ff ff       	jmp    36d0 <register_tm_clones>
    3759:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003760 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3760:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3764:	48 8b 87 e8 00 00 00 	mov    0xe8(%rdi),%rax
    376b:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
  data->v++; // thread local
    3772:	48 83 87 d0 00 00 00 01 	addq   $0x1,0xd0(%rdi)
  if (protected->balance > 0) {
    377a:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    377e:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3782:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3789:	48 85 c9             	test   %rcx,%rcx
    378c:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3793:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3797:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    379b:	31 c0                	xor    %eax,%eax
    379d:	c3                   	ret
    379e:	66 90                	xchg   %ax,%ax

00000000000037a0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    37a0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    37a4:	48 63 8f fc 00 00 00 	movslq 0xfc(%rdi),%rcx
    37ab:	85 c9                	test   %ecx,%ecx
    37ad:	7e 64                	jle    3813 <barriered_reset+0x73>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    37af:	48 8b 87 e8 00 00 00 	mov    0xe8(%rdi),%rax
    37b6:	48 63 bf f0 00 00 00 	movslq 0xf0(%rdi),%rdi
    37bd:	48 8d 0c 49          	lea    (%rcx,%rcx,2),%rcx
    37c1:	48 c1 e1 07          	shl    $0x7,%rcx
      data->thread->tasks[x].available = 1; 
    37c5:	48 8b 70 58          	mov    0x58(%rax),%rsi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    37c9:	48 8b 40 40          	mov    0x40(%rax),%rax
    37cd:	48 8b 04 f8          	mov    (%rax,%rdi,8),%rax
    37d1:	48 8d 96 f8 00 00 00 	lea    0xf8(%rsi),%rdx
    37d8:	48 8d 8c 0e f8 00 00 00 	lea    0xf8(%rsi,%rcx,1),%rcx
    37e0:	48 8b 40 58          	mov    0x58(%rax),%rax
    37e4:	48 05 c0 00 00 00    	add    $0xc0,%rax
    37ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    37f0:	83 40 c0 01          	addl   $0x1,-0x40(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
    37f4:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    37fb:	83 00 01             	addl   $0x1,(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
    37fe:	48 05 80 01 00 00    	add    $0x180,%rax
      data->thread->tasks[x].available = 1; 
    3804:	c7 82 80 fe ff ff 01 00 00 00 	movl   $0x1,-0x180(%rdx)
    for (int x = 0 ; x < data->task_count ; x++) {
    380e:	48 39 ca             	cmp    %rcx,%rdx
    3811:	75 dd                	jne    37f0 <barriered_reset+0x50>
  asm volatile ("sfence" ::: "memory");
    3813:	0f ae f8             	sfence
}
    3816:	31 c0                	xor    %eax,%eax
    3818:	c3                   	ret
    3819:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003820 <barriered_thread>:
void* barriered_thread(void *arg) {
    3820:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3824:	83 7f 64 01          	cmpl   $0x1,0x64(%rdi)
    3828:	0f 85 c8 02 00 00    	jne    3af6 <barriered_thread+0x2d6>
void* barriered_thread(void *arg) {
    382e:	41 56                	push   %r14
    3830:	41 55                	push   %r13
    3832:	45 31 ed             	xor    %r13d,%r13d
    3835:	41 54                	push   %r12
    3837:	49 89 fc             	mov    %rdi,%r12
    383a:	55                   	push   %rbp
    383b:	53                   	push   %rbx
    383c:	31 db                	xor    %ebx,%ebx
    383e:	66 90                	xchg   %ax,%ax
    if (t >= data->task_count) {
    3840:	41 8b 54 24 60       	mov    0x60(%r12),%edx
    3845:	39 da                	cmp    %ebx,%edx
    3847:	7f 13                	jg     385c <barriered_thread+0x3c>
      data->cycles++;
    3849:	49 83 84 24 18 01 00 00 01 	addq   $0x1,0x118(%r12)
      t = 0;
    3852:	31 db                	xor    %ebx,%ebx
    for (; t < data->task_count; t++) {
    3854:	85 d2                	test   %edx,%edx
    3856:	0f 8e 74 01 00 00    	jle    39d0 <barriered_thread+0x1b0>
    385c:	48 63 c3             	movslq %ebx,%rax
    385f:	48 8d 2c 40          	lea    (%rax,%rax,2),%rbp
    3863:	48 c1 e5 07          	shl    $0x7,%rbp
    3867:	eb 19                	jmp    3882 <barriered_thread+0x62>
    3869:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3870:	83 c3 01             	add    $0x1,%ebx
    3873:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    387a:	39 d3                	cmp    %edx,%ebx
    387c:	0f 8d 4e 01 00 00    	jge    39d0 <barriered_thread+0x1b0>
      if (data->tasks[t].available == 1) {
    3882:	49 8b 44 24 58       	mov    0x58(%r12),%rax
    3887:	48 8d 0c 28          	lea    (%rax,%rbp,1),%rcx
    388b:	83 b9 f8 00 00 00 01 	cmpl   $0x1,0xf8(%rcx)
    3892:	75 dc                	jne    3870 <barriered_thread+0x50>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3894:	41 8b 7c 24 48       	mov    0x48(%r12),%edi
          previous = t - 1;
    3899:	83 ea 01             	sub    $0x1,%edx
    389c:	8d 73 ff             	lea    -0x1(%rbx),%esi
    389f:	85 db                	test   %ebx,%ebx
    38a1:	0f 4f d6             	cmovg  %esi,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    38a4:	85 ff                	test   %edi,%edi
    38a6:	0f 8e f4 01 00 00    	jle    3aa0 <barriered_thread+0x280>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    38ac:	48 63 d2             	movslq %edx,%rdx
    38af:	49 8b 44 24 40       	mov    0x40(%r12),%rax
        int prearrive = 0; 
    38b4:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    38b7:	45 31 f6             	xor    %r14d,%r14d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    38ba:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
    38be:	48 63 d7             	movslq %edi,%rdx
    38c1:	44 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    38c8:	44 8b 81 c0 00 00 00 	mov    0xc0(%rcx),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    38cf:	48 c1 e6 07          	shl    $0x7,%rsi
    38d3:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    38d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    38e0:	48 8b 10             	mov    (%rax),%rdx
    38e3:	4c 8b 5a 58          	mov    0x58(%rdx),%r11
    38e7:	49 01 f3             	add    %rsi,%r11
    38ea:	4c 89 da             	mov    %r11,%rdx
    38ed:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    38f4:	75 04                	jne    38fa <barriered_thread+0xda>
            arrived++;
    38f6:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    38fa:	44 3b 82 c0 00 00 00 	cmp    0xc0(%rdx),%r8d
    3901:	75 04                	jne    3907 <barriered_thread+0xe7>
            prearrive++;
    3903:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3907:	48 83 c0 08          	add    $0x8,%rax
    390b:	48 39 c8             	cmp    %rcx,%rax
    390e:	75 d0                	jne    38e0 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    3910:	44 39 d7             	cmp    %r10d,%edi
    3913:	0f 84 d7 00 00 00    	je     39f0 <barriered_thread+0x1d0>
    3919:	45 85 d2             	test   %r10d,%r10d
    391c:	0f 84 ce 00 00 00    	je     39f0 <barriered_thread+0x1d0>
        if (arrived == 0 || arrived == data->thread_count) {
    3922:	45 85 f6             	test   %r14d,%r14d
    3925:	74 0b                	je     3932 <barriered_thread+0x112>
    3927:	45 39 74 24 48       	cmp    %r14d,0x48(%r12)
    392c:	0f 85 9e 00 00 00    	jne    39d0 <barriered_thread+0x1b0>
    3932:	49 8b 44 24 58       	mov    0x58(%r12),%rax
          data->tasks[t].prearrive++;
    3937:	48 01 e8             	add    %rbp,%rax
    393a:	83 80 c0 00 00 00 01 	addl   $0x1,0xc0(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    3941:	85 db                	test   %ebx,%ebx
    3943:	75 16                	jne    395b <barriered_thread+0x13b>
    3945:	49 8b b4 24 f0 00 00 00 	mov    0xf0(%r12),%rsi
    394d:	49 3b b4 24 f8 00 00 00 	cmp    0xf8(%r12),%rsi
    3955:	0f 8c 1d 01 00 00    	jl     3a78 <barriered_thread+0x258>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    395b:	49 63 0c 24          	movslq (%r12),%rcx
    395f:	49 8b 54 24 40       	mov    0x40(%r12),%rdx
          data->tasks[t].available = 0;
    3964:	c7 80 f8 00 00 00 00 00 00 00 	movl   $0x0,0xf8(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    396e:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    3972:	48 8b 7a 58          	mov    0x58(%rdx),%rdi
    3976:	48 01 ef             	add    %rbp,%rdi
    3979:	ff 90 d8 00 00 00    	call   *0xd8(%rax)
          data->tasks[t].arrived++;
    397f:	49 8b 44 24 58       	mov    0x58(%r12),%rax
    3984:	48 01 e8             	add    %rbp,%rax
    3987:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    398e:	41 8b 44 24 60       	mov    0x60(%r12),%eax
          data->iteration_count++;
    3993:	49 83 84 24 e8 00 00 00 01 	addq   $0x1,0xe8(%r12)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    399c:	83 e8 01             	sub    $0x1,%eax
    399f:	39 d8                	cmp    %ebx,%eax
    39a1:	74 65                	je     3a08 <barriered_thread+0x1e8>
          asm volatile ("sfence" ::: "memory");
    39a3:	0f ae f8             	sfence
          if (waiting == 0) {
    39a6:	45 85 ed             	test   %r13d,%r13d
    39a9:	0f 84 91 00 00 00    	je     3a40 <barriered_thread+0x220>
    for (; t < data->task_count; t++) {
    39af:	41 8b 54 24 60       	mov    0x60(%r12),%edx
    39b4:	83 c3 01             	add    $0x1,%ebx
    39b7:	48 81 c5 80 01 00 00 	add    $0x180,%rbp
    39be:	39 d3                	cmp    %edx,%ebx
    39c0:	0f 8c bc fe ff ff    	jl     3882 <barriered_thread+0x62>
    39c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  while (data->running == 1) {
    39d0:	41 83 7c 24 64 01    	cmpl   $0x1,0x64(%r12)
    39d6:	0f 84 64 fe ff ff    	je     3840 <barriered_thread+0x20>
}
    39dc:	5b                   	pop    %rbx
    39dd:	31 c0                	xor    %eax,%eax
    39df:	5d                   	pop    %rbp
    39e0:	41 5c                	pop    %r12
    39e2:	41 5d                	pop    %r13
    39e4:	41 5e                	pop    %r14
    39e6:	c3                   	ret
    39e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          if (waiting == 1) {
    39f0:	41 83 fd 01          	cmp    $0x1,%r13d
    39f4:	0f 84 b6 00 00 00    	je     3ab0 <barriered_thread+0x290>
        int arrived = 0; 
    39fa:	45 31 ed             	xor    %r13d,%r13d
    39fd:	e9 20 ff ff ff       	jmp    3922 <barriered_thread+0x102>
    3a02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3a08:	49 8b b4 24 f0 00 00 00 	mov    0xf0(%r12),%rsi
    3a10:	49 3b b4 24 f8 00 00 00 	cmp    0xf8(%r12),%rsi
    3a18:	7d 89                	jge    39a3 <barriered_thread+0x183>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    3a1a:	48 c1 e6 04          	shl    $0x4,%rsi
    3a1e:	bf 04 00 00 00       	mov    $0x4,%edi
    3a23:	49 03 b4 24 e0 00 00 00 	add    0xe0(%r12),%rsi
    3a2b:	e8 e0 e8 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3a30:	49 83 84 24 f0 00 00 00 01 	addq   $0x1,0xf0(%r12)
    3a39:	e9 65 ff ff ff       	jmp    39a3 <barriered_thread+0x183>
    3a3e:	66 90                	xchg   %ax,%ax
            data->task_snapshot[data->task_timestamp_count].task = t;
    3a40:	49 8b 84 24 08 01 00 00 	mov    0x108(%r12),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3a48:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3a4d:	41 bd 01 00 00 00    	mov    $0x1,%r13d
            data->task_snapshot[data->task_timestamp_count].task = t;
    3a53:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3a57:	49 8b 84 24 00 01 00 00 	mov    0x100(%r12),%rax
    3a5f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3a63:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3a66:	e8 a5 e8 ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3a6b:	41 8b 54 24 60       	mov    0x60(%r12),%edx
    3a70:	e9 fb fd ff ff       	jmp    3870 <barriered_thread+0x50>
    3a75:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3a78:	48 c1 e6 04          	shl    $0x4,%rsi
    3a7c:	bf 04 00 00 00       	mov    $0x4,%edi
    3a81:	49 03 b4 24 d8 00 00 00 	add    0xd8(%r12),%rsi
    3a89:	e8 82 e8 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3a8e:	49 8b 44 24 58       	mov    0x58(%r12),%rax
    3a93:	48 01 e8             	add    %rbp,%rax
    3a96:	e9 c0 fe ff ff       	jmp    395b <barriered_thread+0x13b>
    3a9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (waiting == 1) {
    3aa0:	41 83 fd 01          	cmp    $0x1,%r13d
    3aa4:	0f 85 8d fe ff ff    	jne    3937 <barriered_thread+0x117>
        int arrived = 0; 
    3aaa:	45 31 f6             	xor    %r14d,%r14d
    3aad:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3ab0:	49 8b 84 24 08 01 00 00 	mov    0x108(%r12),%rax
    3ab8:	bf 04 00 00 00       	mov    $0x4,%edi
    3abd:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3ac1:	49 8b 84 24 00 01 00 00 	mov    0x100(%r12),%rax
    3ac9:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3ace:	e8 3d e8 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3ad3:	49 8b 84 24 08 01 00 00 	mov    0x108(%r12),%rax
    3adb:	48 83 c0 01          	add    $0x1,%rax
    3adf:	48 99                	cqto
    3ae1:	49 f7 bc 24 10 01 00 00 	idivq  0x110(%r12)
    3ae9:	49 89 94 24 08 01 00 00 	mov    %rdx,0x108(%r12)
            waiting = 0; 
    3af1:	e9 04 ff ff ff       	jmp    39fa <barriered_thread+0x1da>
}
    3af6:	31 c0                	xor    %eax,%eax
    3af8:	c3                   	ret
    3af9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003b00 <external_thread>:
void * external_thread(void *arg) {
    3b00:	f3 0f 1e fa          	endbr64
    3b04:	41 55                	push   %r13
    3b06:	41 54                	push   %r12
    3b08:	55                   	push   %rbp
    3b09:	53                   	push   %rbx
    3b0a:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    3b0e:	66 0f 6f 05 2a 3e 00 00 	movdqa 0x3e2a(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
void * external_thread(void *arg) {
    3b16:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3b1f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3b24:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3b26:	83 7f 64 01          	cmpl   $0x1,0x64(%rdi)
  struct timespec req = {
    3b2a:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    3b2e:	75 64                	jne    3b94 <external_thread+0x94>
    3b30:	49 89 fd             	mov    %rdi,%r13
    3b33:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3b38:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    3b3b:	4c 8d 25 c2 34 00 00 	lea    0x34c2(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    3b42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    nanosleep(&req , &rem);
    3b48:	48 89 ee             	mov    %rbp,%rsi
    3b4b:	48 89 df             	mov    %rbx,%rdi
    3b4e:	e8 fd e7 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3b53:	49 8b 85 c0 00 00 00 	mov    0xc0(%r13),%rax
    3b5a:	48 63 10             	movslq (%rax),%rdx
    3b5d:	85 d2                	test   %edx,%edx
    3b5f:	7e 29                	jle    3b8a <external_thread+0x8a>
    3b61:	48 8b 40 08          	mov    0x8(%rax),%rax
    3b65:	48 c1 e2 04          	shl    $0x4,%rdx
    3b69:	48 01 c2             	add    %rax,%rdx
    3b6c:	0f 1f 40 00          	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    3b70:	8b 48 08             	mov    0x8(%rax),%ecx
    3b73:	85 c9                	test   %ecx,%ecx
    3b75:	75 0a                	jne    3b81 <external_thread+0x81>
        data->buffers->buffer[x].data = "Hello world";
    3b77:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    3b7a:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3b81:	48 83 c0 10          	add    $0x10,%rax
    3b85:	48 39 c2             	cmp    %rax,%rdx
    3b88:	75 e6                	jne    3b70 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    3b8a:	0f ae f0             	mfence
  while (data->running == 1) {
    3b8d:	41 83 7d 64 01       	cmpl   $0x1,0x64(%r13)
    3b92:	74 b4                	je     3b48 <external_thread+0x48>
}
    3b94:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3b99:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3ba2:	75 0d                	jne    3bb1 <external_thread+0xb1>
    3ba4:	48 83 c4 38          	add    $0x38,%rsp
    3ba8:	31 c0                	xor    %eax,%eax
    3baa:	5b                   	pop    %rbx
    3bab:	5d                   	pop    %rbp
    3bac:	41 5c                	pop    %r12
    3bae:	41 5d                	pop    %r13
    3bb0:	c3                   	ret
    3bb1:	e8 7a e7 ff ff       	call   2330 <__stack_chk_fail@plt>
    3bb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003bc0 <timer_thread>:
void* timer_thread(void *arg) {
    3bc0:	f3 0f 1e fa          	endbr64
    3bc4:	41 57                	push   %r15
    3bc6:	48 8d 35 43 34 00 00 	lea    0x3443(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3bcd:	49 89 ff             	mov    %rdi,%r15
    3bd0:	41 56                	push   %r14
    3bd2:	41 55                	push   %r13
    3bd4:	41 54                	push   %r12
    3bd6:	55                   	push   %rbp
    3bd7:	53                   	push   %rbx
    3bd8:	48 83 ec 58          	sub    $0x58,%rsp
    3bdc:	8b 17                	mov    (%rdi),%edx
    3bde:	bf 01 00 00 00       	mov    $0x1,%edi
    3be3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3bec:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3bf1:	31 c0                	xor    %eax,%eax
    3bf3:	e8 58 e8 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3bf8:	66 0f 6f 05 40 3d 00 00 	movdqa 0x3d40(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3c00:	ba 88 13 00 00       	mov    $0x1388,%edx
    3c05:	31 c0                	xor    %eax,%eax
    3c07:	48 8d 35 14 34 00 00 	lea    0x3414(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3c0e:	bf 01 00 00 00       	mov    $0x1,%edi
    3c13:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3c18:	e8 33 e8 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3c1d:	4d 63 77 64          	movslq 0x64(%r15),%r14
    3c21:	45 85 f6             	test   %r14d,%r14d
    3c24:	0f 84 a2 00 00 00    	je     3ccc <timer_thread+0x10c>
  int n = 0;
    3c2a:	45 31 ed             	xor    %r13d,%r13d
  int y = 0;
    3c2d:	45 31 f6             	xor    %r14d,%r14d
    3c30:	49 89 e4             	mov    %rsp,%r12
    if (y >= data->threads[0]->task_count) {
    3c33:	31 db                	xor    %ebx,%ebx
    3c35:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    3c3a:	48 89 ef             	mov    %rbp,%rdi
    3c3d:	4c 89 e6             	mov    %r12,%rsi
    n++;
    3c40:	41 83 c5 01          	add    $0x1,%r13d
    nanosleep(&preempt , &rem2);
    3c44:	e8 07 e7 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c49:	49 63 47 48          	movslq 0x48(%r15),%rax
    y++;
    3c4d:	41 8d 7e 01          	lea    0x1(%r14),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c51:	85 c0                	test   %eax,%eax
    3c53:	7e 4f                	jle    3ca4 <timer_thread+0xe4>
    3c55:	49 8b 77 40          	mov    0x40(%r15),%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    3c59:	4f 8d 04 76          	lea    (%r14,%r14,2),%r8
    3c5d:	49 c1 e0 07          	shl    $0x7,%r8
    3c61:	4c 8d 0c c6          	lea    (%rsi,%rax,8),%r9
    3c65:	0f 1f 00             	nopl   (%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3c68:	4c 8b 16             	mov    (%rsi),%r10
    3c6b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c6d:	48 83 c6 08          	add    $0x8,%rsi
        int next = (y + 1) % data->threads[x]->task_count;
    3c71:	99                   	cltd
    3c72:	41 f7 7a 60          	idivl  0x60(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3c76:	49 8b 4a 58          	mov    0x58(%r10),%rcx
    3c7a:	48 63 d2             	movslq %edx,%rdx
    3c7d:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
    3c81:	48 c1 e0 07          	shl    $0x7,%rax
    3c85:	48 01 c8             	add    %rcx,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3c88:	4c 01 c1             	add    %r8,%rcx
        data->threads[x]->tasks[next].scheduled = 1;
    3c8b:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3c95:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c9f:	49 39 f1             	cmp    %rsi,%r9
    3ca2:	75 c4                	jne    3c68 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    3ca4:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3ca7:	49 8b 47 40          	mov    0x40(%r15),%rax
  while (data->running && n < times) {
    3cab:	41 8b 57 64          	mov    0x64(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3caf:	48 8b 00             	mov    (%rax),%rax
    3cb2:	39 78 60             	cmp    %edi,0x60(%rax)
    3cb5:	0f 4e fb             	cmovle %ebx,%edi
    3cb8:	4c 63 f7             	movslq %edi,%r14
  while (data->running && n < times) {
    3cbb:	85 d2                	test   %edx,%edx
    3cbd:	74 0d                	je     3ccc <timer_thread+0x10c>
    3cbf:	41 81 fd 88 13 00 00 	cmp    $0x1388,%r13d
    3cc6:	0f 85 6e ff ff ff    	jne    3c3a <timer_thread+0x7a>
    3ccc:	48 8d 3d 65 33 00 00 	lea    0x3365(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3cd3:	e8 18 e6 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3cd8:	49 63 47 4c          	movslq 0x4c(%r15),%rax
    3cdc:	85 c0                	test   %eax,%eax
    3cde:	7e 5a                	jle    3d3a <timer_thread+0x17a>
    for (int y = 0 ; y < data->task_count ; y++) {
    3ce0:	41 8b 57 60          	mov    0x60(%r15),%edx
    3ce4:	85 d2                	test   %edx,%edx
    3ce6:	7e 52                	jle    3d3a <timer_thread+0x17a>
    3ce8:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    3cf0:	48 63 c2             	movslq %edx,%rax
      data->threads[x]->tasks[y].sending = 0;
    3cf3:	4d 8b 47 40          	mov    0x40(%r15),%r8
    3cf7:	31 f6                	xor    %esi,%esi
    3cf9:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    3cfd:	48 c1 e0 07          	shl    $0x7,%rax
    3d01:	48 8d b8 38 01 00 00 	lea    0x138(%rax),%rdi
    3d08:	49 8b 04 30          	mov    (%r8,%rsi,1),%rax
    3d0c:	48 8b 50 58          	mov    0x58(%rax),%rdx
    3d10:	48 8d 82 38 01 00 00 	lea    0x138(%rdx),%rax
    3d17:	48 01 fa             	add    %rdi,%rdx
    3d1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3d20:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3d26:	48 05 80 01 00 00    	add    $0x180,%rax
    3d2c:	48 39 d0             	cmp    %rdx,%rax
    3d2f:	75 ef                	jne    3d20 <timer_thread+0x160>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d31:	48 83 c6 08          	add    $0x8,%rsi
    3d35:	48 39 f1             	cmp    %rsi,%rcx
    3d38:	75 ce                	jne    3d08 <timer_thread+0x148>
  asm volatile ("mfence" ::: "memory");
    3d3a:	0f ae f0             	mfence
  struct timespec drain = {
    3d3d:	66 0f 6f 05 0b 3c 00 00 	movdqa 0x3c0b(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3d45:	48 8d 2d 11 33 00 00 	lea    0x3311(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3d4c:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d51:	49 63 47 48          	movslq 0x48(%r15),%rax
    y++;
    3d55:	45 8d 6e 01          	lea    0x1(%r14),%r13d
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d59:	85 c0                	test   %eax,%eax
    3d5b:	7e 4f                	jle    3dac <timer_thread+0x1ec>
    3d5d:	49 8b 77 40          	mov    0x40(%r15),%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    3d61:	4b 8d 3c 76          	lea    (%r14,%r14,2),%rdi
    3d65:	48 c1 e7 07          	shl    $0x7,%rdi
    3d69:	4c 8d 04 c6          	lea    (%rsi,%rax,8),%r8
    3d6d:	0f 1f 00             	nopl   (%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    3d70:	48 8b 1e             	mov    (%rsi),%rbx
    3d73:	44 89 e8             	mov    %r13d,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d76:	48 83 c6 08          	add    $0x8,%rsi
        int next = (y + 1) % data->threads[x]->task_count;
    3d7a:	99                   	cltd
    3d7b:	f7 7b 60             	idivl  0x60(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3d7e:	48 8b 4b 58          	mov    0x58(%rbx),%rcx
    3d82:	48 63 c2             	movslq %edx,%rax
    3d85:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    3d89:	48 c1 e0 07          	shl    $0x7,%rax
    3d8d:	48 01 c8             	add    %rcx,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3d90:	48 01 f9             	add    %rdi,%rcx
        data->threads[x]->tasks[next].scheduled = 1;
    3d93:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3d9d:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3da7:	49 39 f0             	cmp    %rsi,%r8
    3daa:	75 c4                	jne    3d70 <timer_thread+0x1b0>
    asm volatile ("mfence" ::: "memory");
    3dac:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3daf:	49 8b 47 40          	mov    0x40(%r15),%rax
    3db3:	48 8b 00             	mov    (%rax),%rax
    3db6:	44 39 68 60          	cmp    %r13d,0x60(%rax)
    3dba:	7f 03                	jg     3dbf <timer_thread+0x1ff>
      y = 0;
    3dbc:	45 31 ed             	xor    %r13d,%r13d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3dbf:	41 8b 7f 50          	mov    0x50(%r15),%edi
    3dc3:	85 ff                	test   %edi,%edi
    3dc5:	0f 8e b7 00 00 00    	jle    3e82 <timer_thread+0x2c2>
    3dcb:	31 db                	xor    %ebx,%ebx
    3dcd:	45 31 e4             	xor    %r12d,%r12d
    int all_empty = 1;
    3dd0:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3dd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            all_empty = 0;
    3de0:	45 31 f6             	xor    %r14d,%r14d
    3de3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3de8:	85 ff                	test   %edi,%edi
    3dea:	7e 5e                	jle    3e4a <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3dec:	49 8b 47 40          	mov    0x40(%r15),%rax
    3df0:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3df4:	4b 8d 04 76          	lea    (%r14,%r14,2),%rax
    3df8:	48 c1 e0 07          	shl    $0x7,%rax
    3dfc:	48 03 42 58          	add    0x58(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3e00:	31 d2                	xor    %edx,%edx
    3e02:	48 8b 80 28 01 00 00 	mov    0x128(%rax),%rax
    3e09:	eb 15                	jmp    3e20 <timer_thread+0x260>
    3e0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3e10:	4d 85 c0             	test   %r8,%r8
    3e13:	7f 1f                	jg     3e34 <timer_thread+0x274>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3e15:	83 c2 01             	add    $0x1,%edx
    3e18:	48 83 c0 20          	add    $0x20,%rax
    3e1c:	39 fa                	cmp    %edi,%edx
    3e1e:	74 2a                	je     3e4a <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3e20:	48 8b 08             	mov    (%rax),%rcx
    3e23:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3e27:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3e2b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3e2f:	48 85 c9             	test   %rcx,%rcx
    3e32:	7e dc                	jle    3e10 <timer_thread+0x250>
    3e34:	bf 01 00 00 00       	mov    $0x1,%edi
    3e39:	48 89 ee             	mov    %rbp,%rsi
    3e3c:	31 c0                	xor    %eax,%eax
    3e3e:	e8 0d e6 ff ff       	call   2450 <__printf_chk@plt>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3e43:	41 8b 7f 50          	mov    0x50(%r15),%edi
            all_empty = 0;
    3e47:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3e4a:	49 83 c6 01          	add    $0x1,%r14
    3e4e:	44 39 f7             	cmp    %r14d,%edi
    3e51:	7f 95                	jg     3de8 <timer_thread+0x228>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3e53:	41 83 c4 01          	add    $0x1,%r12d
    3e57:	41 39 fc             	cmp    %edi,%r12d
    3e5a:	7d 09                	jge    3e65 <timer_thread+0x2a5>
    3e5c:	48 83 c3 08          	add    $0x8,%rbx
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3e60:	e9 7b ff ff ff       	jmp    3de0 <timer_thread+0x220>
    if (all_empty == 1) {
    3e65:	41 83 f9 01          	cmp    $0x1,%r9d
    3e69:	74 17                	je     3e82 <timer_thread+0x2c2>
      nanosleep(&drain , &drainrem);
    3e6b:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3e70:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3e75:	4d 63 f5             	movslq %r13d,%r14
    3e78:	e8 d3 e4 ff ff       	call   2350 <nanosleep@plt>
    3e7d:	e9 cf fe ff ff       	jmp    3d51 <timer_thread+0x191>
    3e82:	48 8d 3d cb 31 00 00 	lea    0x31cb(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3e89:	e8 62 e4 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3e8e:	41 8b 47 64          	mov    0x64(%r15),%eax
    3e92:	85 c0                	test   %eax,%eax
    3e94:	0f 84 ab 00 00 00    	je     3f45 <timer_thread+0x385>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3e9a:	41 8b 57 4c          	mov    0x4c(%r15),%edx
    3e9e:	85 d2                	test   %edx,%edx
    3ea0:	7e 2b                	jle    3ecd <timer_thread+0x30d>
    3ea2:	49 8b 4f 40          	mov    0x40(%r15),%rcx
    3ea6:	31 db                	xor    %ebx,%ebx
    3ea8:	48 8d 2d bf 31 00 00 	lea    0x31bf(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3eaf:	90                   	nop
      data->threads[x]->running = 0;
    3eb0:	48 8b 04 d9          	mov    (%rcx,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    3eb4:	83 78 08 02          	cmpl   $0x2,0x8(%rax)
      data->threads[x]->running = 0;
    3eb8:	c7 40 64 00 00 00 00 	movl   $0x0,0x64(%rax)
      if (data->threads[x]->type == IO) {
    3ebf:	0f 84 ad 00 00 00    	je     3f72 <timer_thread+0x3b2>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ec5:	48 83 c3 01          	add    $0x1,%rbx
    3ec9:	39 da                	cmp    %ebx,%edx
    3ecb:	7f e3                	jg     3eb0 <timer_thread+0x2f0>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ecd:	49 63 47 48          	movslq 0x48(%r15),%rax
    3ed1:	85 c0                	test   %eax,%eax
    3ed3:	7e 59                	jle    3f2e <timer_thread+0x36e>
      for (int y = 0 ; y < data->task_count ; y++) {
    3ed5:	41 8b 57 60          	mov    0x60(%r15),%edx
    3ed9:	85 d2                	test   %edx,%edx
    3edb:	7e 51                	jle    3f2e <timer_thread+0x36e>
    3edd:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
    3ee5:	48 63 c2             	movslq %edx,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3ee8:	4d 8b 47 40          	mov    0x40(%r15),%r8
    3eec:	31 c9                	xor    %ecx,%ecx
    3eee:	48 8d 3c 40          	lea    (%rax,%rax,2),%rdi
    3ef2:	48 c1 e7 07          	shl    $0x7,%rdi
    3ef6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3f00:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3f04:	48 8b 40 58          	mov    0x58(%rax),%rax
    3f08:	48 8d 14 07          	lea    (%rdi,%rax,1),%rdx
    3f0c:	0f 1f 40 00          	nopl   0x0(%rax)
    3f10:	c7 80 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3f1a:	48 05 80 01 00 00    	add    $0x180,%rax
    3f20:	48 39 c2             	cmp    %rax,%rdx
    3f23:	75 eb                	jne    3f10 <timer_thread+0x350>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f25:	48 83 c1 08          	add    $0x8,%rcx
    3f29:	48 39 ce             	cmp    %rcx,%rsi
    3f2c:	75 d2                	jne    3f00 <timer_thread+0x340>
    asm volatile ("mfence" ::: "memory");
    3f2e:	0f ae f0             	mfence
    3f31:	48 8d 3d 48 31 00 00 	lea    0x3148(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3f38:	e8 b3 e3 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3f3d:	41 c7 47 64 00 00 00 00 	movl   $0x0,0x64(%r15)
    3f45:	48 8d 3d 3b 31 00 00 	lea    0x313b(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3f4c:	e8 9f e3 ff ff       	call   22f0 <puts@plt>
}
    3f51:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3f56:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3f5f:	75 4a                	jne    3fab <timer_thread+0x3eb>
    3f61:	48 83 c4 58          	add    $0x58,%rsp
    3f65:	31 c0                	xor    %eax,%eax
    3f67:	5b                   	pop    %rbx
    3f68:	5d                   	pop    %rbp
    3f69:	41 5c                	pop    %r12
    3f6b:	41 5d                	pop    %r13
    3f6d:	41 5e                	pop    %r14
    3f6f:	41 5f                	pop    %r15
    3f71:	c3                   	ret
    3f72:	48 89 ef             	mov    %rbp,%rdi
    3f75:	e8 76 e3 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3f7a:	49 8b 47 40          	mov    0x40(%r15),%rax
    3f7e:	be 01 00 00 00       	mov    $0x1,%esi
    3f83:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3f87:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3f8b:	8b b8 d0 00 00 00    	mov    0xd0(%rax),%edi
    3f91:	e8 6a e4 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3f96:	41 8b 57 4c          	mov    0x4c(%r15),%edx
    3f9a:	39 da                	cmp    %ebx,%edx
    3f9c:	0f 8e 2b ff ff ff    	jle    3ecd <timer_thread+0x30d>
    3fa2:	49 8b 4f 40          	mov    0x40(%r15),%rcx
    3fa6:	e9 05 ff ff ff       	jmp    3eb0 <timer_thread+0x2f0>
}
    3fab:	e8 80 e3 ff ff       	call   2330 <__stack_chk_fail@plt>

0000000000003fb0 <fatal_error>:
void fatal_error(const char *syscall) {
    3fb0:	f3 0f 1e fa          	endbr64
    3fb4:	50                   	push   %rax
    3fb5:	58                   	pop    %rax
    3fb6:	48 83 ec 08          	sub    $0x8,%rsp
    perror(syscall);
    3fba:	e8 d1 e4 ff ff       	call   2490 <perror@plt>
    exit(1);
    3fbf:	bf 01 00 00 00       	mov    $0x1,%edi
    3fc4:	e8 d7 e4 ff ff       	call   24a0 <exit@plt>
    3fc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003fd0 <strtolower>:
void strtolower(char *str) {
    3fd0:	f3 0f 1e fa          	endbr64
    3fd4:	55                   	push   %rbp
    3fd5:	53                   	push   %rbx
    3fd6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3fda:	48 0f be 1f          	movsbq (%rdi),%rbx
    3fde:	84 db                	test   %bl,%bl
    3fe0:	74 24                	je     4006 <strtolower+0x36>
    3fe2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3fe5:	e8 26 e5 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3fea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3ff0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3ff3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3ff7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3ffa:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3ffd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4002:	84 db                	test   %bl,%bl
    4004:	75 ea                	jne    3ff0 <strtolower+0x20>
}
    4006:	48 83 c4 08          	add    $0x8,%rsp
    400a:	5b                   	pop    %rbx
    400b:	5d                   	pop    %rbp
    400c:	c3                   	ret
    400d:	0f 1f 00             	nopl   (%rax)

0000000000004010 <zh_malloc>:
void *zh_malloc(size_t size) {
    4010:	f3 0f 1e fa          	endbr64
    4014:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4018:	e8 f3 e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    401d:	48 85 c0             	test   %rax,%rax
    4020:	74 05                	je     4027 <zh_malloc+0x17>
}
    4022:	48 83 c4 08          	add    $0x8,%rsp
    4026:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4027:	48 8b 0d f2 5f 00 00 	mov    0x5ff2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    402e:	ba 28 00 00 00       	mov    $0x28,%edx
    4033:	be 01 00 00 00       	mov    $0x1,%esi
    4038:	48 8d 3d c9 33 00 00 	lea    0x33c9(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    403f:	e8 7c e4 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4044:	bf 01 00 00 00       	mov    $0x1,%edi
    4049:	e8 52 e4 ff ff       	call   24a0 <exit@plt>
    404e:	66 90                	xchg   %ax,%ax

0000000000004050 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4050:	f3 0f 1e fa          	endbr64
    4054:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4055:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    405a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    405d:	e8 fe e2 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4062:	48 85 c0             	test   %rax,%rax
    4065:	74 11                	je     4078 <get_filename_ext+0x28>
    4067:	48 39 c3             	cmp    %rax,%rbx
    406a:	74 0c                	je     4078 <get_filename_ext+0x28>
    return dot + 1;
    406c:	48 83 c0 01          	add    $0x1,%rax
}
    4070:	5b                   	pop    %rbx
    4071:	c3                   	ret
    4072:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4078:	48 8d 05 50 30 00 00 	lea    0x3050(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    407f:	5b                   	pop    %rbx
    4080:	c3                   	ret
    4081:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    408c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004090 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4090:	f3 0f 1e fa          	endbr64
    4094:	41 55                	push   %r13
    4096:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4099:	48 89 fe             	mov    %rdi,%rsi
    409c:	41 54                	push   %r12
    409e:	55                   	push   %rbp
    409f:	48 89 d5             	mov    %rdx,%rbp
    40a2:	ba 00 04 00 00       	mov    $0x400,%edx
    40a7:	53                   	push   %rbx
    40a8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    40af:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    40b8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    40c0:	31 c0                	xor    %eax,%eax
    40c2:	49 89 e4             	mov    %rsp,%r12
    40c5:	4c 89 e7             	mov    %r12,%rdi
    40c8:	e8 63 e3 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    40cd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    40d2:	84 db                	test   %bl,%bl
    40d4:	74 24                	je     40fa <send_headers+0x6a>
        *str = (char)tolower(*str);
    40d6:	e8 35 e4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    40db:	48 8b 08             	mov    (%rax),%rcx
    40de:	4c 89 e0             	mov    %r12,%rax
    40e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    40e8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    40eb:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    40ef:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    40f2:	48 0f be 18          	movsbq (%rax),%rbx
    40f6:	84 db                	test   %bl,%bl
    40f8:	75 ee                	jne    40e8 <send_headers+0x58>
    void *buf = malloc(size);
    40fa:	bf 11 00 00 00       	mov    $0x11,%edi
    40ff:	e8 0c e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4104:	48 85 c0             	test   %rax,%rax
    4107:	0f 84 7e 04 00 00    	je     458b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    410d:	66 0f 6f 05 4b 38 00 00 	movdqa 0x384b(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    4115:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4119:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    411e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4126:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    412a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    412d:	e8 de e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4132:	48 85 c0             	test   %rax,%rax
    4135:	0f 84 50 04 00 00    	je     458b <send_headers+0x4fb>
    413b:	66 0f 6f 05 2d 38 00 00 	movdqa 0x382d(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    4143:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4147:	4c 89 e7             	mov    %r12,%rdi
    414a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4154:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    415c:	0f 11 00             	movups %xmm0,(%rax)
    415f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4163:	be 2e 00 00 00       	mov    $0x2e,%esi
    4168:	e8 f3 e1 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    416d:	48 85 c0             	test   %rax,%rax
    4170:	0f 84 ea 02 00 00    	je     4460 <send_headers+0x3d0>
    4176:	4c 39 e0             	cmp    %r12,%rax
    4179:	0f 84 e1 02 00 00    	je     4460 <send_headers+0x3d0>
    return dot + 1;
    417f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4183:	48 8d 3d 13 2f 00 00 	lea    0x2f13(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    418a:	48 89 de             	mov    %rbx,%rsi
    418d:	e8 1e e2 ff ff       	call   23b0 <strcmp@plt>
    4192:	85 c0                	test   %eax,%eax
    4194:	75 20                	jne    41b6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4196:	66 0f 6f 05 e2 37 00 00 	movdqa 0x37e2(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    419e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41a6:	66 0f 6f 05 e2 37 00 00 	movdqa 0x37e2(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    41ae:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    41b6:	48 89 de             	mov    %rbx,%rsi
    41b9:	48 8d 3d e1 2e 00 00 	lea    0x2ee1(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    41c0:	e8 eb e1 ff ff       	call   23b0 <strcmp@plt>
    41c5:	85 c0                	test   %eax,%eax
    41c7:	75 20                	jne    41e9 <send_headers+0x159>
    41c9:	66 0f 6f 05 af 37 00 00 	movdqa 0x37af(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    41d1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41d9:	66 0f 6f 05 af 37 00 00 	movdqa 0x37af(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    41e1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    41e9:	48 89 de             	mov    %rbx,%rsi
    41ec:	48 8d 3d b3 2e 00 00 	lea    0x2eb3(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    41f3:	e8 b8 e1 ff ff       	call   23b0 <strcmp@plt>
    41f8:	85 c0                	test   %eax,%eax
    41fa:	0f 84 10 02 00 00    	je     4410 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4200:	48 89 de             	mov    %rbx,%rsi
    4203:	48 8d 3d a0 2e 00 00 	lea    0x2ea0(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    420a:	e8 a1 e1 ff ff       	call   23b0 <strcmp@plt>
    420f:	85 c0                	test   %eax,%eax
    4211:	0f 84 a9 02 00 00    	je     44c0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4217:	48 89 de             	mov    %rbx,%rsi
    421a:	48 8d 3d 8d 2e 00 00 	lea    0x2e8d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4221:	e8 8a e1 ff ff       	call   23b0 <strcmp@plt>
    4226:	85 c0                	test   %eax,%eax
    4228:	0f 84 6a 02 00 00    	je     4498 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    422e:	48 89 de             	mov    %rbx,%rsi
    4231:	48 8d 3d b9 2e 00 00 	lea    0x2eb9(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4238:	e8 73 e1 ff ff       	call   23b0 <strcmp@plt>
    423d:	85 c0                	test   %eax,%eax
    423f:	0f 84 2b 02 00 00    	je     4470 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4245:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4248:	0f 84 52 01 00 00    	je     43a0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    424e:	48 89 de             	mov    %rbx,%rsi
    4251:	48 8d 3d 5a 2e 00 00 	lea    0x2e5a(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    4258:	e8 53 e1 ff ff       	call   23b0 <strcmp@plt>
    425d:	85 c0                	test   %eax,%eax
    425f:	0f 84 ab 02 00 00    	je     4510 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4265:	48 89 de             	mov    %rbx,%rsi
    4268:	48 8d 3d 47 2e 00 00 	lea    0x2e47(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    426f:	e8 3c e1 ff ff       	call   23b0 <strcmp@plt>
    4274:	85 c0                	test   %eax,%eax
    4276:	0f 84 6c 02 00 00    	je     44e8 <send_headers+0x458>
    slen = strlen(send_buffer);
    427c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4284:	4c 89 e7             	mov    %r12,%rdi
    4287:	e8 94 e0 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    428c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    428f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4292:	e8 79 e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4297:	48 85 c0             	test   %rax,%rax
    429a:	0f 84 eb 02 00 00    	je     458b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    42a0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    42a4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    42a8:	83 fb 08             	cmp    $0x8,%ebx
    42ab:	0f 83 3f 01 00 00    	jae    43f0 <send_headers+0x360>
    42b1:	f6 c3 04             	test   $0x4,%bl
    42b4:	0f 85 7b 02 00 00    	jne    4535 <send_headers+0x4a5>
    42ba:	85 db                	test   %ebx,%ebx
    42bc:	74 13                	je     42d1 <send_headers+0x241>
    42be:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    42c6:	88 10                	mov    %dl,(%rax)
    42c8:	f6 c3 02             	test   $0x2,%bl
    42cb:	0f 85 96 02 00 00    	jne    4567 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    42d1:	4d 89 e8             	mov    %r13,%r8
    42d4:	48 8d 0d df 2d 00 00 	lea    0x2ddf(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    42db:	4c 89 e7             	mov    %r12,%rdi
    42de:	31 c0                	xor    %eax,%eax
    42e0:	ba 00 04 00 00       	mov    $0x400,%edx
    42e5:	be 01 00 00 00       	mov    $0x1,%esi
    42ea:	e8 31 e2 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    42ef:	4c 89 e7             	mov    %r12,%rdi
    42f2:	e8 29 e0 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    42f7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    42fa:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    42fd:	e8 0e e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4302:	48 85 c0             	test   %rax,%rax
    4305:	0f 84 80 02 00 00    	je     458b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    430b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    430f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4313:	83 fb 08             	cmp    $0x8,%ebx
    4316:	0f 83 1c 01 00 00    	jae    4438 <send_headers+0x3a8>
    431c:	f6 c3 04             	test   $0x4,%bl
    431f:	0f 85 29 02 00 00    	jne    454e <send_headers+0x4be>
    4325:	85 db                	test   %ebx,%ebx
    4327:	74 13                	je     433c <send_headers+0x2ac>
    4329:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4331:	88 10                	mov    %dl,(%rax)
    4333:	f6 c3 02             	test   $0x2,%bl
    4336:	0f 85 3d 02 00 00    	jne    4579 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    433c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4341:	bf 02 00 00 00       	mov    $0x2,%edi
    4346:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    434e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4356:	e8 b5 e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    435b:	48 85 c0             	test   %rax,%rax
    435e:	0f 84 27 02 00 00    	je     458b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4364:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    436c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4370:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4378:	66 89 10             	mov    %dx,(%rax)
}
    437b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4383:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    438c:	0f 85 20 02 00 00    	jne    45b2 <send_headers+0x522>
    4392:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4399:	5b                   	pop    %rbx
    439a:	5d                   	pop    %rbp
    439b:	41 5c                	pop    %r12
    439d:	41 5d                	pop    %r13
    439f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    43a0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    43a4:	0f 85 a4 fe ff ff    	jne    424e <send_headers+0x1be>
    43aa:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    43ae:	0f 85 9a fe ff ff    	jne    424e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    43b4:	66 0f 6f 05 24 36 00 00 	movdqa 0x3624(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    43bc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    43c6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    43ce:	66 0f 6f 05 1a 36 00 00 	movdqa 0x361a(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    43d6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    43de:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    43e6:	e9 63 fe ff ff       	jmp    424e <send_headers+0x1be>
    43eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    43f0:	89 da                	mov    %ebx,%edx
    43f2:	48 89 c7             	mov    %rax,%rdi
    43f5:	4c 89 e6             	mov    %r12,%rsi
    43f8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    43fd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4402:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4405:	c1 e9 03             	shr    $0x3,%ecx
    4408:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    440b:	e9 c1 fe ff ff       	jmp    42d1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4410:	66 0f 6f 05 68 35 00 00 	movdqa 0x3568(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4418:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4420:	66 0f 6f 05 78 35 00 00 	movdqa 0x3578(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4428:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4430:	e9 cb fd ff ff       	jmp    4200 <send_headers+0x170>
    4435:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4438:	89 da                	mov    %ebx,%edx
    443a:	48 89 c7             	mov    %rax,%rdi
    443d:	4c 89 e6             	mov    %r12,%rsi
    4440:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4445:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    444a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    444d:	c1 e9 03             	shr    $0x3,%ecx
    4450:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4453:	e9 e4 fe ff ff       	jmp    433c <send_headers+0x2ac>
    4458:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4460:	48 8d 1d 68 2c 00 00 	lea    0x2c68(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4467:	e9 94 fd ff ff       	jmp    4200 <send_headers+0x170>
    446c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4470:	66 0f 6f 05 48 35 00 00 	movdqa 0x3548(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4478:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4480:	66 0f 6f 05 48 35 00 00 	movdqa 0x3548(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4488:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4490:	e9 b0 fd ff ff       	jmp    4245 <send_headers+0x1b5>
    4495:	0f 1f 00             	nopl   (%rax)
    4498:	66 0f 6f 05 20 35 00 00 	movdqa 0x3520(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    44a0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44a8:	66 0f 6f 05 20 35 00 00 	movdqa 0x3520(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    44b0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44b8:	e9 71 fd ff ff       	jmp    422e <send_headers+0x19e>
    44bd:	0f 1f 00             	nopl   (%rax)
    44c0:	66 0f 6f 05 b8 34 00 00 	movdqa 0x34b8(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    44c8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44d0:	66 0f 6f 05 d8 34 00 00 	movdqa 0x34d8(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    44d8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44e0:	e9 32 fd ff ff       	jmp    4217 <send_headers+0x187>
    44e5:	0f 1f 00             	nopl   (%rax)
    44e8:	66 0f 6f 05 d0 34 00 00 	movdqa 0x34d0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    44f0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44f8:	66 0f 6f 05 10 35 00 00 	movdqa 0x3510(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4500:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4508:	e9 6f fd ff ff       	jmp    427c <send_headers+0x1ec>
    450d:	0f 1f 00             	nopl   (%rax)
    4510:	66 0f 6f 05 a8 34 00 00 	movdqa 0x34a8(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4518:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4520:	66 0f 6f 05 d8 34 00 00 	movdqa 0x34d8(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4528:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4530:	e9 30 fd ff ff       	jmp    4265 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4535:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    453c:	89 db                	mov    %ebx,%ebx
    453e:	89 10                	mov    %edx,(%rax)
    4540:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4545:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4549:	e9 83 fd ff ff       	jmp    42d1 <send_headers+0x241>
    454e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4555:	89 db                	mov    %ebx,%ebx
    4557:	89 10                	mov    %edx,(%rax)
    4559:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    455e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4562:	e9 d5 fd ff ff       	jmp    433c <send_headers+0x2ac>
    4567:	89 db                	mov    %ebx,%ebx
    4569:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    456f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4574:	e9 58 fd ff ff       	jmp    42d1 <send_headers+0x241>
    4579:	89 db                	mov    %ebx,%ebx
    457b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4581:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4586:	e9 b1 fd ff ff       	jmp    433c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    458b:	48 8b 0d 8e 5a 00 00 	mov    0x5a8e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4592:	ba 28 00 00 00       	mov    $0x28,%edx
    4597:	be 01 00 00 00       	mov    $0x1,%esi
    459c:	48 8d 3d 65 2e 00 00 	lea    0x2e65(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    45a3:	e8 18 df ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    45a8:	bf 01 00 00 00       	mov    $0x1,%edi
    45ad:	e8 ee de ff ff       	call   24a0 <exit@plt>
}
    45b2:	e8 79 dd ff ff       	call   2330 <__stack_chk_fail@plt>
    45b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000045c0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    45c0:	f3 0f 1e fa          	endbr64
    45c4:	41 55                	push   %r13
    45c6:	49 89 d5             	mov    %rdx,%r13
    45c9:	41 54                	push   %r12
    45cb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    45ce:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    45d1:	55                   	push   %rbp
    45d2:	53                   	push   %rbx
    45d3:	48 89 f3             	mov    %rsi,%rbx
    45d6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    45da:	e8 31 de ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    45df:	48 85 c0             	test   %rax,%rax
    45e2:	74 77                	je     465b <copy_file_contents+0x9b>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    45e4:	4c 89 e7             	mov    %r12,%rdi
    45e7:	48 89 c5             	mov    %rax,%rbp
    45ea:	31 f6                	xor    %esi,%esi
    45ec:	31 c0                	xor    %eax,%eax
    45ee:	e8 8d de ff ff       	call   2480 <open@plt>
    45f3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    45f6:	85 c0                	test   %eax,%eax
    45f8:	78 55                	js     464f <copy_file_contents+0x8f>
		       "the destination buffer");

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    45fa:	48 89 da             	mov    %rbx,%rdx
    45fd:	48 89 ee             	mov    %rbp,%rsi
    4600:	89 c7                	mov    %eax,%edi
    4602:	e8 89 dd ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    4607:	48 98                	cltq
    4609:	48 39 d8             	cmp    %rbx,%rax
    460c:	7c 22                	jl     4630 <copy_file_contents+0x70>
    close(fd);
    460e:	44 89 e7             	mov    %r12d,%edi
    4611:	e8 5a dd ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    4616:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    461a:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    461e:	48 83 c4 08          	add    $0x8,%rsp
    4622:	5b                   	pop    %rbx
    4623:	5d                   	pop    %rbp
    4624:	41 5c                	pop    %r12
    4626:	41 5d                	pop    %r13
    4628:	c3                   	ret
    4629:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4630:	48 8b 0d e9 59 00 00 	mov    0x59e9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4637:	ba 1a 00 00 00       	mov    $0x1a,%edx
    463c:	be 01 00 00 00       	mov    $0x1,%esi
    4641:	48 8d 3d 88 2a 00 00 	lea    0x2a88(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    4648:	e8 73 de ff ff       	call   24c0 <fwrite@plt>
    464d:	eb bf                	jmp    460e <copy_file_contents+0x4e>
        fatal_error("read");
    464f:	48 8d 3d a9 2b 00 00 	lea    0x2ba9(%rip),%rdi        # 71ff <_IO_stdin_used+0x1ff>
    4656:	e8 55 f9 ff ff       	call   3fb0 <fatal_error>
    465b:	48 8b 0d be 59 00 00 	mov    0x59be(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4662:	ba 28 00 00 00       	mov    $0x28,%edx
    4667:	be 01 00 00 00       	mov    $0x1,%esi
    466c:	48 8d 3d 95 2d 00 00 	lea    0x2d95(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4673:	e8 48 de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4678:	bf 01 00 00 00       	mov    $0x1,%edi
    467d:	e8 1e de ff ff       	call   24a0 <exit@plt>
    4682:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    468d:	0f 1f 00             	nopl   (%rax)

0000000000004690 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4690:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
static inline struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4694:	8b 46 44             	mov    0x44(%rsi),%eax
    4697:	48 89 fa             	mov    %rdi,%rdx
    469a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    469d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    46a3:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    46a6:	48 8b 07             	mov    (%rdi),%rax
    46a9:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    46ac:	f6 c1 02             	test   $0x2,%cl
    46af:	74 00                	je     46b1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    46b1:	89 f0                	mov    %esi,%eax
    46b3:	44 29 c0             	sub    %r8d,%eax
    46b6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    46b9:	0f 82 81 de ff ff    	jb     2540 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    46bf:	c1 e9 0a             	shr    $0xa,%ecx
    46c2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    46c6:	8b 47 44             	mov    0x44(%rdi),%eax
    46c9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    46cc:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    46cf:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    46d2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    46d5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    46d9:	d3 e0                	shl    %cl,%eax
    46db:	8b 4a 04             	mov    0x4(%rdx),%ecx
    46de:	48 c1 e0 06          	shl    $0x6,%rax
    46e2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    46e6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    46ec:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    46ef:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    46f3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    46f9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4701:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4705:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4708:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    470f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4717:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    471b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    471f:	e8 1c dc ff ff       	call   2340 <io_uring_submit@plt>
}
    4724:	31 c0                	xor    %eax,%eax
    4726:	48 83 c4 08          	add    $0x8,%rsp
    472a:	c3                   	ret
    472b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004730 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4730:	f3 0f 1e fa          	endbr64
    4734:	41 55                	push   %r13
    4736:	41 89 fd             	mov    %edi,%r13d
    4739:	41 54                	push   %r12
    473b:	55                   	push   %rbp
    473c:	53                   	push   %rbx
    473d:	48 89 f3             	mov    %rsi,%rbx
    4740:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4744:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4747:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    474d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4750:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4753:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4755:	f6 c1 02             	test   $0x2,%cl
    4758:	74 00                	je     475a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    475a:	89 c2                	mov    %eax,%edx
    475c:	29 f2                	sub    %esi,%edx
    475e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4761:	0f 82 e9 dd ff ff    	jb     2550 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4767:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    476a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    476d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4770:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4775:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4778:	23 6b 58             	and    0x58(%rbx),%ebp
    477b:	d3 e5                	shl    %cl,%ebp
    477d:	48 c1 e5 06          	shl    $0x6,%rbp
    4781:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4785:	e8 86 dc ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    478a:	be 01 00 00 00       	mov    $0x1,%esi
    478f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4794:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4797:	e8 04 dc ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    479c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    47a1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    47a5:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    47a8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    47ad:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    47b2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    47bb:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    47c3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    47c7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    47cb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    47d2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    47da:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    47de:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    47e6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    47ee:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    47f2:	e8 49 db ff ff       	call   2340 <io_uring_submit@plt>
}
    47f7:	48 83 c4 08          	add    $0x8,%rsp
    47fb:	31 c0                	xor    %eax,%eax
    47fd:	5b                   	pop    %rbx
    47fe:	5d                   	pop    %rbp
    47ff:	41 5c                	pop    %r12
    4801:	41 5d                	pop    %r13
    4803:	c3                   	ret
    4804:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    480f:	90                   	nop

0000000000004810 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4810:	f3 0f 1e fa          	endbr64
    4814:	41 56                	push   %r14
    4816:	41 89 f6             	mov    %esi,%r14d
    4819:	41 55                	push   %r13
    481b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    481e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4823:	41 54                	push   %r12
    4825:	55                   	push   %rbp
    4826:	48 89 d5             	mov    %rdx,%rbp
    4829:	53                   	push   %rbx
    void *buf = malloc(size);
    482a:	e8 e1 db ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    482f:	48 85 c0             	test   %rax,%rax
    4832:	0f 84 dd 00 00 00    	je     4915 <_send_static_string_content+0x105>
    4838:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    483b:	4c 89 ef             	mov    %r13,%rdi
    483e:	e8 dd da ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4843:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    484a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    484e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4851:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4854:	e8 b7 db ff ff       	call   2410 <malloc@plt>
    4859:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    485c:	48 85 c0             	test   %rax,%rax
    485f:	0f 84 b0 00 00 00    	je     4915 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4865:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4869:	4c 89 e2             	mov    %r12,%rdx
    486c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    486f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4873:	e8 68 db ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4878:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    487b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4881:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4884:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4888:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    488a:	f6 c1 02             	test   $0x2,%cl
    488d:	0f 85 7d 00 00 00    	jne    4910 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4893:	89 d0                	mov    %edx,%eax
    4895:	29 f0                	sub    %esi,%eax
    4897:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    489a:	0f 82 ba dc ff ff    	jb     255a <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    48a0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    48a3:	8b 45 44             	mov    0x44(%rbp),%eax
    48a6:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    48a9:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    48ac:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    48af:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    48b2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    48b8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    48bc:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    48be:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    48c1:	48 89 ef             	mov    %rbp,%rdi
    48c4:	48 c1 e0 06          	shl    $0x6,%rax
    48c8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    48cc:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    48cf:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    48d3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    48d9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    48e1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    48e5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    48e8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    48ef:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    48f7:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    48fb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    48ff:	5b                   	pop    %rbx
    4900:	5d                   	pop    %rbp
    4901:	41 5c                	pop    %r12
    4903:	41 5d                	pop    %r13
    4905:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4907:	e9 34 da ff ff       	jmp    2340 <io_uring_submit@plt>
    490c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4910:	e9 7e ff ff ff       	jmp    4893 <_send_static_string_content+0x83>
    4915:	48 8b 0d 04 57 00 00 	mov    0x5704(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    491c:	ba 28 00 00 00       	mov    $0x28,%edx
    4921:	be 01 00 00 00       	mov    $0x1,%esi
    4926:	48 8d 3d db 2a 00 00 	lea    0x2adb(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    492d:	e8 8e db ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4932:	bf 01 00 00 00       	mov    $0x1,%edi
    4937:	e8 64 db ff ff       	call   24a0 <exit@plt>
    493c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004940 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4940:	f3 0f 1e fa          	endbr64
    4944:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4947:	89 fe                	mov    %edi,%esi
    4949:	48 8b 3d c8 56 00 00 	mov    0x56c8(%rip),%rdi        # a018 <unimplemented_content>
    4950:	e9 bb fe ff ff       	jmp    4810 <_send_static_string_content>
    4955:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004960 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4960:	f3 0f 1e fa          	endbr64
    4964:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4967:	89 fe                	mov    %edi,%esi
    4969:	48 8b 3d a0 56 00 00 	mov    0x56a0(%rip),%rdi        # a010 <http_404_content>
    4970:	e9 9b fe ff ff       	jmp    4810 <_send_static_string_content>
    4975:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004980 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4980:	f3 0f 1e fa          	endbr64
    4984:	41 56                	push   %r14
    4986:	41 55                	push   %r13
    4988:	49 89 d5             	mov    %rdx,%r13
    498b:	41 54                	push   %r12
    498d:	41 89 f4             	mov    %esi,%r12d
    4990:	55                   	push   %rbp
    4991:	48 89 fd             	mov    %rdi,%rbp
    4994:	53                   	push   %rbx
    4995:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    499c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    49a5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    49ad:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    49af:	e8 6c d9 ff ff       	call   2320 <strlen@plt>
    49b4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    49b9:	48 89 c3             	mov    %rax,%rbx
    49bc:	0f 84 b6 00 00 00    	je     4a78 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    49c2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    49c7:	48 89 ee             	mov    %rbp,%rsi
    49ca:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    49ce:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    49d3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    49db:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    49e3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    49ee:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    49f6:	e8 c5 d9 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    49fb:	48 89 e6             	mov    %rsp,%rsi
    49fe:	4c 89 f7             	mov    %r14,%rdi
    4a01:	e8 ca d9 ff ff       	call   23d0 <stat@plt>
    4a06:	83 f8 ff             	cmp    $0xffffffff,%eax
    4a09:	0f 84 d3 00 00 00    	je     4ae2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    4a0f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4a13:	25 00 f0 00 00       	and    $0xf000,%eax
    4a18:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4a1d:	0f 84 f5 00 00 00    	je     4b18 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4a23:	48 8b 3d e6 55 00 00 	mov    0x55e6(%rip),%rdi        # a010 <http_404_content>
    4a2a:	4c 89 ea             	mov    %r13,%rdx
    4a2d:	44 89 e6             	mov    %r12d,%esi
    4a30:	e8 db fd ff ff       	call   4810 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4a35:	4c 89 f2             	mov    %r14,%rdx
    4a38:	bf 01 00 00 00       	mov    $0x1,%edi
    4a3d:	31 c0                	xor    %eax,%eax
    4a3f:	48 8d 35 da 26 00 00 	lea    0x26da(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    4a46:	e8 05 da ff ff       	call   2450 <__printf_chk@plt>
}
    4a4b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4a53:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4a5c:	0f 85 20 01 00 00    	jne    4b82 <handle_get_method+0x202>
    4a62:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4a69:	5b                   	pop    %rbx
    4a6a:	5d                   	pop    %rbp
    4a6b:	41 5c                	pop    %r12
    4a6d:	41 5d                	pop    %r13
    4a6f:	41 5e                	pop    %r14
    4a71:	c3                   	ret
    4a72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a78:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a7d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4a85:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4a8a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a8d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a95:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a98:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4aa0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4aab:	e8 10 d9 ff ff       	call   23c0 <__memcpy_chk@plt>
    4ab0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4ab5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4aba:	48 8d 35 2a 26 00 00 	lea    0x262a(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4ac1:	48 29 d9             	sub    %rbx,%rcx
    4ac4:	ba 0b 00 00 00       	mov    $0xb,%edx
    4ac9:	e8 f2 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4ace:	48 89 e6             	mov    %rsp,%rsi
    4ad1:	4c 89 f7             	mov    %r14,%rdi
    4ad4:	e8 f7 d8 ff ff       	call   23d0 <stat@plt>
    4ad9:	83 f8 ff             	cmp    $0xffffffff,%eax
    4adc:	0f 85 2d ff ff ff    	jne    4a0f <handle_get_method+0x8f>
    4ae2:	4c 89 f2             	mov    %r14,%rdx
    4ae5:	48 89 e9             	mov    %rbp,%rcx
    4ae8:	48 8d 35 07 26 00 00 	lea    0x2607(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    4aef:	31 c0                	xor    %eax,%eax
    4af1:	bf 01 00 00 00       	mov    $0x1,%edi
    4af6:	e8 55 d9 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    4afb:	48 8b 3d 0e 55 00 00 	mov    0x550e(%rip),%rdi        # a010 <http_404_content>
    4b02:	4c 89 ea             	mov    %r13,%rdx
    4b05:	44 89 e6             	mov    %r12d,%esi
    4b08:	e8 03 fd ff ff       	call   4810 <_send_static_string_content>
}
    4b0d:	e9 39 ff ff ff       	jmp    4a4b <handle_get_method+0xcb>
    4b12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4b18:	bf 70 00 00 00       	mov    $0x70,%edi
    4b1d:	e8 ee d8 ff ff       	call   2410 <malloc@plt>
    4b22:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4b25:	48 85 c0             	test   %rax,%rax
    4b28:	74 5d                	je     4b87 <handle_get_method+0x207>
            req->client_socket = client_socket;
    4b2a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4b2e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4b33:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4b37:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    4b3a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4b41:	e8 4a f5 ff ff       	call   4090 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4b46:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4b4b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4b4f:	4c 89 f7             	mov    %r14,%rdi
    4b52:	e8 69 fa ff ff       	call   45c0 <copy_file_contents>
    4b57:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4b5c:	4c 89 f2             	mov    %r14,%rdx
    4b5f:	31 c0                	xor    %eax,%eax
    4b61:	48 8d 35 a6 25 00 00 	lea    0x25a6(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4b68:	bf 01 00 00 00       	mov    $0x1,%edi
    4b6d:	e8 de d8 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    4b72:	4c 89 ee             	mov    %r13,%rsi
    4b75:	48 89 df             	mov    %rbx,%rdi
    4b78:	e8 13 fb ff ff       	call   4690 <add_write_request>
    4b7d:	e9 c9 fe ff ff       	jmp    4a4b <handle_get_method+0xcb>
}
    4b82:	e8 a9 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4b87:	48 8b 0d 92 54 00 00 	mov    0x5492(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4b8e:	ba 28 00 00 00       	mov    $0x28,%edx
    4b93:	be 01 00 00 00       	mov    $0x1,%esi
    4b98:	48 8d 3d 69 28 00 00 	lea    0x2869(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4b9f:	e8 1c d9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4ba4:	bf 01 00 00 00       	mov    $0x1,%edi
    4ba9:	e8 f2 d8 ff ff       	call   24a0 <exit@plt>
    4bae:	66 90                	xchg   %ax,%ax

0000000000004bb0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4bb0:	f3 0f 1e fa          	endbr64
    4bb4:	41 57                	push   %r15
    4bb6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4bb8:	4c 8d 35 c6 24 00 00 	lea    0x24c6(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4bbf:	41 55                	push   %r13
    4bc1:	49 89 d5             	mov    %rdx,%r13
    4bc4:	41 54                	push   %r12
    4bc6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4bc9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4bcc:	55                   	push   %rbp
    4bcd:	53                   	push   %rbx
    4bce:	48 83 ec 18          	sub    $0x18,%rsp
    4bd2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4bdb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4be0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4be2:	49 89 e7             	mov    %rsp,%r15
    4be5:	4c 89 fa             	mov    %r15,%rdx
    4be8:	e8 93 d7 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4bed:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4bf1:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4bf4:	84 db                	test   %bl,%bl
    4bf6:	74 1d                	je     4c15 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4bf8:	e8 13 d9 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4bfd:	48 89 ea             	mov    %rbp,%rdx
    4c00:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4c03:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4c07:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4c0a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    4c0d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4c11:	84 db                	test   %bl,%bl
    4c13:	75 eb                	jne    4c00 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4c15:	4c 89 fa             	mov    %r15,%rdx
    4c18:	4c 89 f6             	mov    %r14,%rsi
    4c1b:	31 ff                	xor    %edi,%edi
    4c1d:	e8 5e d7 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4c22:	48 8d 35 0a 25 00 00 	lea    0x250a(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4c29:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4c2c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    4c2f:	e8 7c d7 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4c34:	4c 89 ea             	mov    %r13,%rdx
    4c37:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4c3a:	85 c0                	test   %eax,%eax
    4c3c:	75 2a                	jne    4c68 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    4c3e:	48 89 df             	mov    %rbx,%rdi
    4c41:	e8 3a fd ff ff       	call   4980 <handle_get_method>
}
    4c46:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4c4b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4c54:	75 20                	jne    4c76 <handle_http_method+0xc6>
    4c56:	48 83 c4 18          	add    $0x18,%rsp
    4c5a:	5b                   	pop    %rbx
    4c5b:	5d                   	pop    %rbp
    4c5c:	41 5c                	pop    %r12
    4c5e:	41 5d                	pop    %r13
    4c60:	41 5e                	pop    %r14
    4c62:	41 5f                	pop    %r15
    4c64:	c3                   	ret
    4c65:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4c68:	48 8b 3d a9 53 00 00 	mov    0x53a9(%rip),%rdi        # a018 <unimplemented_content>
    4c6f:	e8 9c fb ff ff       	call   4810 <_send_static_string_content>
}
    4c74:	eb d0                	jmp    4c46 <handle_http_method+0x96>
    4c76:	e8 b5 d6 ff ff       	call   2330 <__stack_chk_fail@plt>
    4c7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004c80 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4c80:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4c84:	85 d2                	test   %edx,%edx
    4c86:	7e 38                	jle    4cc0 <get_line+0x40>
    4c88:	48 63 d2             	movslq %edx,%rdx
    4c8b:	48 83 c7 01          	add    $0x1,%rdi
    4c8f:	48 01 f2             	add    %rsi,%rdx
    4c92:	eb 11                	jmp    4ca5 <get_line+0x25>
    4c94:	0f 1f 40 00          	nopl   0x0(%rax)
    4c98:	48 83 c6 01          	add    $0x1,%rsi
    4c9c:	48 83 c7 01          	add    $0x1,%rdi
    4ca0:	48 39 d6             	cmp    %rdx,%rsi
    4ca3:	74 1b                	je     4cc0 <get_line+0x40>
        dest[i] = src[i];
    4ca5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4ca9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4cab:	3c 0d                	cmp    $0xd,%al
    4cad:	75 e9                	jne    4c98 <get_line+0x18>
    4caf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4cb2:	75 e4                	jne    4c98 <get_line+0x18>
            dest[i] = '\0';
    4cb4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4cb7:	31 c0                	xor    %eax,%eax
    4cb9:	c3                   	ret
    4cba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4cc0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4cc5:	c3                   	ret
    4cc6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004cd0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4cd0:	f3 0f 1e fa          	endbr64
    4cd4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4cdb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4cdf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4ce8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4cf0:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4cf2:	49 89 e2             	mov    %rsp,%r10
    4cf5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4cfd:	4c 89 d0             	mov    %r10,%rax
    4d00:	eb 13                	jmp    4d15 <handle_client_request+0x45>
    4d02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4d08:	48 83 c0 01          	add    $0x1,%rax
    4d0c:	48 83 c1 01          	add    $0x1,%rcx
    4d10:	4c 39 c8             	cmp    %r9,%rax
    4d13:	74 4b                	je     4d60 <handle_client_request+0x90>
        dest[i] = src[i];
    4d15:	44 0f b6 01          	movzbl (%rcx),%r8d
    4d19:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4d1c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4d20:	75 e6                	jne    4d08 <handle_client_request+0x38>
    4d22:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4d26:	75 e0                	jne    4d08 <handle_client_request+0x38>
            dest[i] = '\0';
    4d28:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4d2b:	8b 47 08             	mov    0x8(%rdi),%eax
    4d2e:	48 89 f2             	mov    %rsi,%rdx
    4d31:	4c 89 d7             	mov    %r10,%rdi
    4d34:	89 c6                	mov    %eax,%esi
    4d36:	e8 75 fe ff ff       	call   4bb0 <handle_http_method>
}
    4d3b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4d43:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d4c:	75 39                	jne    4d87 <handle_client_request+0xb7>
    4d4e:	31 c0                	xor    %eax,%eax
    4d50:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4d57:	c3                   	ret
    4d58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4d60:	48 8b 0d b9 52 00 00 	mov    0x52b9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4d67:	ba 12 00 00 00       	mov    $0x12,%edx
    4d6c:	be 01 00 00 00       	mov    $0x1,%esi
    4d71:	48 8d 3d bf 23 00 00 	lea    0x23bf(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4d78:	e8 43 d7 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4d7d:	bf 01 00 00 00       	mov    $0x1,%edi
    4d82:	e8 19 d7 ff ff       	call   24a0 <exit@plt>
}
    4d87:	e8 a4 d5 ff ff       	call   2330 <__stack_chk_fail@plt>
    4d8c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004d90 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4d90:	f3 0f 1e fa          	endbr64
    4d94:	55                   	push   %rbp
    4d95:	53                   	push   %rbx
    4d96:	48 89 cb             	mov    %rcx,%rbx
    4d99:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4d9d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4da0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4da3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4da9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4dac:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4daf:	f6 c1 02             	test   $0x2,%cl
    4db2:	74 00                	je     4db4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4db4:	41 89 c0             	mov    %eax,%r8d
    4db7:	45 29 c8             	sub    %r9d,%r8d
    4dba:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4dbe:	0f 82 a6 d7 ff ff    	jb     256a <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4dc4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4dc7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4dca:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4dcd:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4dd0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4dd3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4dd7:	d3 e5                	shl    %cl,%ebp
    4dd9:	48 c1 e5 06          	shl    $0x6,%rbp
    4ddd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4de1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4de4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4de9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4df0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4df4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4df8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4e00:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4e08:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4e0c:	e8 ff d5 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4e11:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4e14:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4e1a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4e1e:	48 83 c4 08          	add    $0x8,%rsp
    4e22:	5b                   	pop    %rbx
    4e23:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4e24:	e9 17 d5 ff ff       	jmp    2340 <io_uring_submit@plt>
    4e29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004e30 <io_thread>:
void* io_thread(void *arg) {
    4e30:	f3 0f 1e fa          	endbr64
    4e34:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e36:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4e38:	41 56                	push   %r14
    4e3a:	41 55                	push   %r13
    4e3c:	41 54                	push   %r12
    4e3e:	55                   	push   %rbp
    4e3f:	48 89 fd             	mov    %rdi,%rbp
    4e42:	53                   	push   %rbx
    4e43:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4e4a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4e53:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4e5b:	48 8b 87 c8 00 00 00 	mov    0xc8(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e62:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4e67:	bf 00 01 00 00       	mov    $0x100,%edi
    4e6c:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4e6f:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4e73:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4e78:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4e7d:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4e82:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4e87:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4e8f:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4e94:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4e9c:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4ea1:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4ea9:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4eae:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4eb6:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4ebb:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4ec3:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4ec8:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4ed0:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4ed8:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4ee0:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4ee8:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4ef0:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4ef8:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4f00:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4f08:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4f10:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4f18:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4f20:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4f27:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4f2f:	e8 bc d4 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4f34:	48 8b bd c8 00 00 00 	mov    0xc8(%rbp),%rdi
    4f3b:	31 f6                	xor    %esi,%esi
    4f3d:	e8 9e d5 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4f42:	31 d2                	xor    %edx,%edx
    4f44:	be 01 00 00 00       	mov    $0x1,%esi
    4f49:	bf 02 00 00 00       	mov    $0x2,%edi
    4f4e:	e8 dd d5 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4f53:	83 f8 ff             	cmp    $0xffffffff,%eax
    4f56:	0f 84 02 06 00 00    	je     555e <io_thread+0x72e>
  if (setsockopt(sock,
    4f5c:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4f61:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4f67:	89 c7                	mov    %eax,%edi
    4f69:	41 89 c4             	mov    %eax,%r12d
    4f6c:	ba 02 00 00 00       	mov    $0x2,%edx
    4f71:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4f76:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4f7e:	e8 7d d3 ff ff       	call   2300 <setsockopt@plt>
    4f83:	85 c0                	test   %eax,%eax
    4f85:	0f 88 c7 05 00 00    	js     5552 <io_thread+0x722>
  srv_addr.sin_family = AF_INET;
    4f8b:	8b 05 af 2a 00 00    	mov    0x2aaf(%rip),%eax        # 7a40 <_IO_stdin_used+0xa40>
  return __builtin___memset_chk (__dest, __ch, __len,
    4f91:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4f96:	ba 10 00 00 00       	mov    $0x10,%edx
    4f9b:	44 89 e7             	mov    %r12d,%edi
    4f9e:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4fa7:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4faf:	89 44 24 40          	mov    %eax,0x40(%rsp)
  if (bind(sock,
    4fb3:	e8 a8 d4 ff ff       	call   2460 <bind@plt>
    4fb8:	85 c0                	test   %eax,%eax
    4fba:	0f 88 86 05 00 00    	js     5546 <io_thread+0x716>
  if (listen(sock, 10) < 0) {
    4fc0:	be 0a 00 00 00       	mov    $0xa,%esi
    4fc5:	44 89 e7             	mov    %r12d,%edi
    4fc8:	e8 53 d4 ff ff       	call   2420 <listen@plt>
    4fcd:	85 c0                	test   %eax,%eax
    4fcf:	0f 88 65 05 00 00    	js     553a <io_thread+0x70a>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4fd5:	ba db 18 00 00       	mov    $0x18db,%edx
    4fda:	48 8d 35 9b 21 00 00 	lea    0x219b(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4fe1:	bf 01 00 00 00       	mov    $0x1,%edi
    4fe6:	31 c0                	xor    %eax,%eax
    4fe8:	e8 63 d4 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4fed:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4ff2:	48 89 d9             	mov    %rbx,%rcx
    4ff5:	44 89 e7             	mov    %r12d,%edi
    4ff8:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4ffd:	48 89 c6             	mov    %rax,%rsi
    5000:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5005:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    500a:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5012:	e8 79 fd ff ff       	call   4d90 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5017:	bf 01 00 00 00       	mov    $0x1,%edi
    501c:	be 10 00 00 00       	mov    $0x10,%esi
    5021:	e8 7a d3 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    5026:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    502b:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    502e:	e8 dd d3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    5033:	48 85 c0             	test   %rax,%rax
    5036:	0f 84 d7 04 00 00    	je     5513 <io_thread+0x6e3>
  iov->iov_base = zh_malloc(10);
    503c:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5040:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5047:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    504e:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5056:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5059:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    505e:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5060:	f6 c1 02             	test   $0x2,%cl
    5063:	0f 85 27 04 00 00    	jne    5490 <io_thread+0x660>
	if (next - head <= sq->ring_entries) {
    5069:	89 d0                	mov    %edx,%eax
    506b:	29 f0                	sub    %esi,%eax
    506d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5074:	0f 82 fa d4 ff ff    	jb     2574 <io_thread.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    507a:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    507d:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	sqe->addr3 = 0;
    5084:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5088:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    508b:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5092:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    5095:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    509c:	48 8d b5 d0 00 00 00 	lea    0xd0(%rbp),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    50a3:	8b 95 d0 00 00 00    	mov    0xd0(%rbp),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50a9:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    50ab:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    50b0:	48 c1 e0 06          	shl    $0x6,%rax
    50b4:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    50bc:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    50c2:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    50c5:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    50cd:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    50d1:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    50d9:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    50e1:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    50e5:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    50e9:	e8 52 d2 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    50ee:	83 7d 64 01          	cmpl   $0x1,0x64(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    50f2:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    50f7:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    50ff:	0f 85 af 01 00 00    	jne    52b4 <io_thread+0x484>
    5105:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    510a:	4d 89 ce             	mov    %r9,%r14
    510d:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5112:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5118:	48 8d 3d 73 20 00 00 	lea    0x2073(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    511f:	e8 cc d1 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5124:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    512b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5132:	c1 e9 0b             	shr    $0xb,%ecx
    5135:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5138:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5140:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5142:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    514a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    514c:	39 d0                	cmp    %edx,%eax
    514e:	74 36                	je     5186 <io_thread+0x356>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5150:	89 f8                	mov    %edi,%eax
    5152:	21 d0                	and    %edx,%eax
    5154:	d3 e0                	shl    %cl,%eax
    5156:	48 c1 e0 04          	shl    $0x4,%rax
    515a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5162:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    516a:	0f 85 80 01 00 00    	jne    52f0 <io_thread+0x4c0>
    5170:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5174:	0f 85 1e 03 00 00    	jne    5498 <io_thread+0x668>
			if (cqe->res < 0)
    517a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    517d:	83 c2 01             	add    $0x1,%edx
    5180:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5182:	85 c0                	test   %eax,%eax
    5184:	79 b2                	jns    5138 <io_thread+0x308>
	*cqe_ptr = cqe;
    5186:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    518f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5190:	45 31 c0             	xor    %r8d,%r8d
    5193:	31 d2                	xor    %edx,%edx
    5195:	b9 01 00 00 00       	mov    $0x1,%ecx
    519a:	4c 89 f6             	mov    %r14,%rsi
    519d:	48 89 df             	mov    %rbx,%rdi
    51a0:	e8 9b d2 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    51a5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    51a8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    51ad:	48 83 38 01          	cmpq   $0x1,(%rax)
    51b1:	0f 84 f1 02 00 00    	je     54a8 <io_thread+0x678>
    51b7:	48 8d 3d fa 1f 00 00 	lea    0x1ffa(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    51be:	e8 2d d1 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    51c3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    51c8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    51cb:	45 85 ff             	test   %r15d,%r15d
    51ce:	0f 88 2e 03 00 00    	js     5502 <io_thread+0x6d2>
      if (cqe->res < 0) {
    51d4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    51d7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    51db:	85 c0                	test   %eax,%eax
    51dd:	0f 88 e5 02 00 00    	js     54c8 <io_thread+0x698>
      switch (req->event_type) {
    51e3:	41 83 f8 01          	cmp    $0x1,%r8d
    51e7:	0f 84 3b 01 00 00    	je     5328 <io_thread+0x4f8>
    51ed:	41 83 f8 02          	cmp    $0x2,%r8d
    51f1:	0f 84 b1 01 00 00    	je     53a8 <io_thread+0x578>
    51f7:	45 85 c0             	test   %r8d,%r8d
    51fa:	0f 84 70 01 00 00    	je     5370 <io_thread+0x540>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5200:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5208:	8b 02                	mov    (%rdx),%eax
    520a:	83 c0 01             	add    $0x1,%eax
    520d:	89 02                	mov    %eax,(%rdx)
	unsigned int head, next = sq->sqe_tail + 1;
    520f:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5216:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    521d:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5220:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5225:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5227:	f6 c1 02             	test   $0x2,%cl
    522a:	74 00                	je     522c <io_thread+0x3fc>
	if (next - head <= sq->ring_entries) {
    522c:	89 d0                	mov    %edx,%eax
    522e:	29 f0                	sub    %esi,%eax
    5230:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5237:	0f 82 37 d3 ff ff    	jb     2574 <io_thread.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    523d:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    5240:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5245:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5249:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    524c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5253:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5256:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    525d:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5264:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5266:	8b 95 d0 00 00 00    	mov    0xd0(%rbp),%edx
    526c:	48 c1 e0 06          	shl    $0x6,%rax
    5270:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5278:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    527e:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5281:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5289:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    528d:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5295:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    529d:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    52a1:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    52a5:	e8 96 d0 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    52aa:	83 7d 64 01          	cmpl   $0x1,0x64(%rbp)
    52ae:	0f 84 64 fe ff ff    	je     5118 <io_thread+0x2e8>
    52b4:	48 8d 3d 36 1f 00 00 	lea    0x1f36(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    52bb:	e8 30 d0 ff ff       	call   22f0 <puts@plt>
}
    52c0:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    52c8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    52d1:	0f 85 37 02 00 00    	jne    550e <io_thread+0x6de>
    52d7:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    52de:	31 c0                	xor    %eax,%eax
    52e0:	5b                   	pop    %rbx
    52e1:	5d                   	pop    %rbp
    52e2:	41 5c                	pop    %r12
    52e4:	41 5d                	pop    %r13
    52e6:	41 5e                	pop    %r14
    52e8:	41 5f                	pop    %r15
    52ea:	c3                   	ret
    52eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    52f0:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    52f5:	48 85 c0             	test   %rax,%rax
    52f8:	0f 84 92 fe ff ff    	je     5190 <io_thread+0x360>
      if (cqe->user_data == 1) {
    52fe:	48 83 38 01          	cmpq   $0x1,(%rax)
    5302:	0f 84 a0 01 00 00    	je     54a8 <io_thread+0x678>
    5308:	48 8d 3d a9 1e 00 00 	lea    0x1ea9(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    530f:	e8 dc cf ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5314:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5319:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    531c:	e9 b3 fe ff ff       	jmp    51d4 <io_thread+0x3a4>
    5321:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
              if (!cqe->res) {
    5328:	85 c0                	test   %eax,%eax
    532a:	0f 85 c0 00 00 00    	jne    53f0 <io_thread+0x5c0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5330:	48 8b 0d e9 4c 00 00 	mov    0x4ce9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5337:	ba 0f 00 00 00       	mov    $0xf,%edx
    533c:	be 01 00 00 00       	mov    $0x1,%esi
    5341:	48 8d 3d 99 1e 00 00 	lea    0x1e99(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    5348:	e8 73 d1 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    534d:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5352:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
	if (cqe)
    5358:	48 85 c0             	test   %rax,%rax
    535b:	0f 84 ae fe ff ff    	je     520f <io_thread+0x3df>
    5361:	e9 9a fe ff ff       	jmp    5200 <io_thread+0x3d0>
    5366:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5370:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5375:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    537a:	48 89 d9             	mov    %rbx,%rcx
    537d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5381:	e8 0a fa ff ff       	call   4d90 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5386:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    538b:	48 89 de             	mov    %rbx,%rsi
    538e:	8b 78 08             	mov    0x8(%rax),%edi
    5391:	e8 9a f3 ff ff       	call   4730 <add_read_request>
              free(req);
    5396:	4c 89 e7             	mov    %r12,%rdi
    5399:	e8 22 cf ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    539e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    53a3:	eb b3                	jmp    5358 <io_thread+0x528>
    53a5:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    53a8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    53ad:	45 31 ff             	xor    %r15d,%r15d
    53b0:	85 c0                	test   %eax,%eax
    53b2:	7e 20                	jle    53d4 <io_thread+0x5a4>
    53b4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    53b8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    53bb:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    53bf:	48 c1 e0 04          	shl    $0x4,%rax
    53c3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    53c8:	e8 f3 ce ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    53cd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    53d2:	7f e4                	jg     53b8 <io_thread+0x588>
              close(req->client_socket);
    53d4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    53d9:	e8 92 cf ff ff       	call   2370 <close@plt>
              free(req);
    53de:	4c 89 e7             	mov    %r12,%rdi
    53e1:	e8 da ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    53e6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    53eb:	e9 68 ff ff ff       	jmp    5358 <io_thread+0x528>
    for (int i = 0; i < dest_sz; i++) {
    53f0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    53f5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    53fa:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5402:	eb 11                	jmp    5415 <io_thread+0x5e5>
    5404:	0f 1f 40 00          	nopl   0x0(%rax)
    5408:	48 83 c0 01          	add    $0x1,%rax
    540c:	48 83 c2 01          	add    $0x1,%rdx
    5410:	48 39 c6             	cmp    %rax,%rsi
    5413:	74 4b                	je     5460 <io_thread+0x630>
        dest[i] = src[i];
    5415:	0f b6 0a             	movzbl (%rdx),%ecx
    5418:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    541a:	80 f9 0d             	cmp    $0xd,%cl
    541d:	75 e9                	jne    5408 <io_thread+0x5d8>
    541f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5423:	75 e3                	jne    5408 <io_thread+0x5d8>
            dest[i] = '\0';
    5425:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5428:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    542d:	48 89 da             	mov    %rbx,%rdx
    5430:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5435:	e8 76 f7 ff ff       	call   4bb0 <handle_http_method>
              free(req->iov[0].iov_base);
    543a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    543f:	e8 7c ce ff ff       	call   22c0 <free@plt>
              free(req);
    5444:	4c 89 e7             	mov    %r12,%rdi
    5447:	e8 74 ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    544c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5451:	e9 02 ff ff ff       	jmp    5358 <io_thread+0x528>
    5456:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5460:	48 8b 0d b9 4b 00 00 	mov    0x4bb9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5467:	ba 12 00 00 00       	mov    $0x12,%edx
    546c:	be 01 00 00 00       	mov    $0x1,%esi
    5471:	48 8d 3d bf 1c 00 00 	lea    0x1cbf(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5478:	e8 43 d0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    547d:	bf 01 00 00 00       	mov    $0x1,%edi
    5482:	e8 19 d0 ff ff       	call   24a0 <exit@plt>
    5487:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5490:	e9 d4 fb ff ff       	jmp    5069 <io_thread+0x239>
    5495:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5498:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    549d:	e9 5c fe ff ff       	jmp    52fe <io_thread+0x4ce>
    54a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    54a8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    54b0:	48 8d 3d ed 1c 00 00 	lea    0x1ced(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    54b7:	8b 02                	mov    (%rdx),%eax
    54b9:	83 c0 01             	add    $0x1,%eax
    54bc:	89 02                	mov    %eax,(%rdx)
    54be:	e8 2d ce ff ff       	call   22f0 <puts@plt>
    54c3:	e9 ec fd ff ff       	jmp    52b4 <io_thread+0x484>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    54c8:	f7 d8                	neg    %eax
    54ca:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    54cf:	89 c7                	mov    %eax,%edi
    54d1:	e8 2a d0 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    54d6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    54db:	be 01 00 00 00       	mov    $0x1,%esi
    54e0:	48 8b 3d 39 4b 00 00 	mov    0x4b39(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    54e7:	48 89 c1             	mov    %rax,%rcx
    54ea:	48 8d 15 47 1f 00 00 	lea    0x1f47(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    54f1:	31 c0                	xor    %eax,%eax
    54f3:	e8 d8 cf ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    54f8:	bf 01 00 00 00       	mov    $0x1,%edi
    54fd:	e8 9e cf ff ff       	call   24a0 <exit@plt>
          fatal_error("io_uring_wait_cqe");
    5502:	48 8d 3d c6 1c 00 00 	lea    0x1cc6(%rip),%rdi        # 71cf <_IO_stdin_used+0x1cf>
    5509:	e8 a2 ea ff ff       	call   3fb0 <fatal_error>
}
    550e:	e8 1d ce ff ff       	call   2330 <__stack_chk_fail@plt>
    5513:	48 8b 0d 06 4b 00 00 	mov    0x4b06(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    551a:	ba 28 00 00 00       	mov    $0x28,%edx
    551f:	be 01 00 00 00       	mov    $0x1,%esi
    5524:	48 8d 3d dd 1e 00 00 	lea    0x1edd(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    552b:	e8 90 cf ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    5530:	bf 01 00 00 00       	mov    $0x1,%edi
    5535:	e8 66 cf ff ff       	call   24a0 <exit@plt>
    fatal_error("listen()");
    553a:	48 8d 3d 32 1c 00 00 	lea    0x1c32(%rip),%rdi        # 7173 <_IO_stdin_used+0x173>
    5541:	e8 6a ea ff ff       	call   3fb0 <fatal_error>
      fatal_error("bind()");
    5546:	48 8d 3d 1f 1c 00 00 	lea    0x1c1f(%rip),%rdi        # 716c <_IO_stdin_used+0x16c>
    554d:	e8 5e ea ff ff       	call   3fb0 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    5552:	48 8d 3d fa 1b 00 00 	lea    0x1bfa(%rip),%rdi        # 7153 <_IO_stdin_used+0x153>
    5559:	e8 52 ea ff ff       	call   3fb0 <fatal_error>
      fatal_error("socket()");
    555e:	48 8d 3d e5 1b 00 00 	lea    0x1be5(%rip),%rdi        # 714a <_IO_stdin_used+0x14a>
    5565:	e8 46 ea ff ff       	call   3fb0 <fatal_error>
    556a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005570 <sendm>:
int sendm(struct BarrierTask *data) {
    5570:	f3 0f 1e fa          	endbr64
    5574:	41 57                	push   %r15
    5576:	41 56                	push   %r14
    5578:	41 55                	push   %r13
    557a:	41 54                	push   %r12
    557c:	55                   	push   %rbp
    557d:	53                   	push   %rbx
    557e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5582:	83 bf 38 01 00 00 01 	cmpl   $0x1,0x138(%rdi)
    5589:	0f 85 79 01 00 00    	jne    5708 <sendm+0x198>
      for (int n = 0 ; n < data->thread_count; n++) {
    558f:	8b 87 f4 00 00 00    	mov    0xf4(%rdi),%eax
    5595:	48 89 fa             	mov    %rdi,%rdx
    5598:	4c 8d bf 40 01 00 00 	lea    0x140(%rdi),%r15
    559f:	31 f6                	xor    %esi,%esi
    55a1:	48 8d bf 48 01 00 00 	lea    0x148(%rdi),%rdi
    55a8:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    55ad:	85 c0                	test   %eax,%eax
    55af:	0f 8e d2 00 00 00    	jle    5687 <sendm+0x117>
    55b5:	0f 1f 00             	nopl   (%rax)
        if (n == data->thread_index) { continue; }
    55b8:	39 b2 f0 00 00 00    	cmp    %esi,0xf0(%rdx)
    55be:	0f 84 b7 00 00 00    	je     567b <sendm+0x10b>
        struct Data *them = data->mailboxes[n].higher;
    55c4:	49 89 f2             	mov    %rsi,%r10
    55c7:	49 c1 e2 05          	shl    $0x5,%r10
    55cb:	4c 03 92 28 01 00 00 	add    0x128(%rdx),%r10
    55d2:	4d 8b 5a 08          	mov    0x8(%r10),%r11
        for (; them->messages_count < min;) {
    55d6:	49 8b 6b 08          	mov    0x8(%r11),%rbp
    55da:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    55de:	49 39 e9             	cmp    %rbp,%r9
    55e1:	0f 8e 8b 00 00 00    	jle    5672 <sendm+0x102>
    55e7:	4c 89 cb             	mov    %r9,%rbx
    55ea:	4c 8b aa c8 00 00 00 	mov    0xc8(%rdx),%r13
    55f1:	4d 8b 62 10          	mov    0x10(%r10),%r12
    55f5:	48 29 eb             	sub    %rbp,%rbx
          them->messages[them->messages_count++] = data->message; 
    55f8:	4d 8b 03             	mov    (%r11),%r8
    55fb:	48 8d 43 ff          	lea    -0x1(%rbx),%rax
    55ff:	48 83 f8 02          	cmp    $0x2,%rax
    5603:	0f 86 e7 00 00 00    	jbe    56f0 <sendm+0x180>
    5609:	4a 8d 3c cd 00 00 00 00 	lea    0x0(,%r9,8),%rdi
    5611:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    5619:	4d 8d 34 38          	lea    (%r8,%rdi,1),%r14
    561d:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5621:	4d 39 f7             	cmp    %r14,%r15
    5624:	73 7a                	jae    56a0 <sendm+0x130>
    5626:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    562b:	4c 39 f1             	cmp    %r14,%rcx
    562e:	73 70                	jae    56a0 <sendm+0x130>
    5630:	4c 01 c0             	add    %r8,%rax
    5633:	4c 01 c7             	add    %r8,%rdi
    5636:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5640:	4c 8b b2 40 01 00 00 	mov    0x140(%rdx),%r14
        for (; them->messages_count < min;) {
    5647:	48 83 c0 08          	add    $0x8,%rax
          them->messages[them->messages_count++] = data->message; 
    564b:	4c 89 70 f8          	mov    %r14,-0x8(%rax)
        for (; them->messages_count < min;) {
    564f:	48 39 c7             	cmp    %rax,%rdi
    5652:	75 ec                	jne    5640 <sendm+0xd0>
    5654:	0f 1f 40 00          	nopl   0x0(%rax)
          data->n++;
    5658:	49 01 dd             	add    %rbx,%r13
          data->mailboxes[n].sent++;
    565b:	49 01 dc             	add    %rbx,%r12
          data->n++;
    565e:	4c 89 aa c8 00 00 00 	mov    %r13,0xc8(%rdx)
          data->mailboxes[n].sent++;
    5665:	4d 89 62 10          	mov    %r12,0x10(%r10)
    5669:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    566d:	4f 89 74 c8 f8       	mov    %r14,-0x8(%r8,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5672:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5675:	8b 82 f4 00 00 00    	mov    0xf4(%rdx),%eax
    567b:	48 83 c6 01          	add    $0x1,%rsi
    567f:	39 f0                	cmp    %esi,%eax
    5681:	0f 8f 31 ff ff ff    	jg     55b8 <sendm+0x48>
}
    5687:	48 83 c4 18          	add    $0x18,%rsp
    568b:	31 c0                	xor    %eax,%eax
    568d:	5b                   	pop    %rbx
    568e:	5d                   	pop    %rbp
    568f:	41 5c                	pop    %r12
    5691:	41 5d                	pop    %r13
    5693:	41 5e                	pop    %r14
    5695:	41 5f                	pop    %r15
    5697:	c3                   	ret
    5698:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    56a0:	4c 8b b2 40 01 00 00 	mov    0x140(%rdx),%r14
    56a7:	48 89 d8             	mov    %rbx,%rax
    56aa:	48 d1 e8             	shr    %rax
    56ad:	66 49 0f 6e c6       	movq   %r14,%xmm0
    56b2:	48 c1 e0 04          	shl    $0x4,%rax
    56b6:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    56ba:	48 01 c8             	add    %rcx,%rax
    56bd:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    56c0:	0f 11 01             	movups %xmm0,(%rcx)
        for (; them->messages_count < min;) {
    56c3:	48 83 c1 10          	add    $0x10,%rcx
    56c7:	48 39 c8             	cmp    %rcx,%rax
    56ca:	75 f4                	jne    56c0 <sendm+0x150>
    56cc:	48 89 d8             	mov    %rbx,%rax
    56cf:	48 83 e0 fe          	and    $0xfffffffffffffffe,%rax
    56d3:	48 01 e8             	add    %rbp,%rax
    56d6:	f6 c3 01             	test   $0x1,%bl
    56d9:	0f 84 79 ff ff ff    	je     5658 <sendm+0xe8>
          them->messages[them->messages_count++] = data->message; 
    56df:	4c 8b b2 40 01 00 00 	mov    0x140(%rdx),%r14
    56e6:	4d 89 34 c0          	mov    %r14,(%r8,%rax,8)
        for (; them->messages_count < min;) {
    56ea:	e9 69 ff ff ff       	jmp    5658 <sendm+0xe8>
    56ef:	90                   	nop
    56f0:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    56f8:	4a 8d 3c cd 00 00 00 00 	lea    0x0(,%r9,8),%rdi
    5700:	e9 2b ff ff ff       	jmp    5630 <sendm+0xc0>
    5705:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5708:	48 8d 3d f5 1a 00 00 	lea    0x1af5(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    570f:	e8 dc cb ff ff       	call   22f0 <puts@plt>
    5714:	e9 6e ff ff ff       	jmp    5687 <sendm+0x117>
    5719:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005720 <receive>:
int receive(struct BarrierTask *data) {
    5720:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5724:	8b 87 f4 00 00 00    	mov    0xf4(%rdi),%eax
    572a:	85 c0                	test   %eax,%eax
    572c:	0f 8e f1 00 00 00    	jle    5823 <receive+0x103>
int receive(struct BarrierTask *data) {
    5732:	41 54                	push   %r12
    5734:	48 89 fa             	mov    %rdi,%rdx
    5737:	55                   	push   %rbp
    5738:	31 ed                	xor    %ebp,%ebp
    573a:	53                   	push   %rbx
    573b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5740:	48 89 ee             	mov    %rbp,%rsi
    5743:	48 c1 e6 05          	shl    $0x5,%rsi
    5747:	48 03 b2 28 01 00 00 	add    0x128(%rdx),%rsi
    574e:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5751:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    5756:	48 85 ff             	test   %rdi,%rdi
    5759:	0f 8e a1 00 00 00    	jle    5800 <receive+0xe0>
      data->sends++;
    575f:	48 8b 8a 30 01 00 00 	mov    0x130(%rdx),%rcx
    5766:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    576a:	4c 63 1a             	movslq (%rdx),%r11
    576d:	49 89 c9             	mov    %rcx,%r9
    5770:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5774:	49 f7 d9             	neg    %r9
    5777:	48 01 c7             	add    %rax,%rdi
    577a:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    577e:	4c 8b 8a c8 00 00 00 	mov    0xc8(%rdx),%r9
      data->mailboxes[n].received++;
    5785:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    5789:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    578c:	49 29 c8             	sub    %rcx,%r8
    578f:	eb 10                	jmp    57a1 <receive+0x81>
    5791:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5798:	48 83 c0 01          	add    $0x1,%rax
    579c:	48 39 f8             	cmp    %rdi,%rax
    579f:	74 5f                	je     5800 <receive+0xe0>
      data->n++;
    57a1:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    57a5:	48 89 82 30 01 00 00 	mov    %rax,0x130(%rdx)
      data->n++;
    57ac:	48 89 8a c8 00 00 00 	mov    %rcx,0xc8(%rdx)
      data->mailboxes[n].received++;
    57b3:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    57b7:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    57bb:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    57c0:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    57c4:	75 d2                	jne    5798 <receive+0x78>
    57c6:	48 63 9a f0 00 00 00 	movslq 0xf0(%rdx),%rbx
    57cd:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    57d1:	75 c5                	jne    5798 <receive+0x78>
    57d3:	bf 01 00 00 00       	mov    $0x1,%edi
    57d8:	b9 01 00 00 00       	mov    $0x1,%ecx
    57dd:	ba 01 00 00 00       	mov    $0x1,%edx
    57e2:	31 c0                	xor    %eax,%eax
    57e4:	48 8d 35 75 1c 00 00 	lea    0x1c75(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    57eb:	e8 60 cc ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    57f0:	bf 01 00 00 00       	mov    $0x1,%edi
    57f5:	e8 a6 cc ff ff       	call   24a0 <exit@plt>
    57fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5800:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    5809:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    580c:	48 83 c5 01          	add    $0x1,%rbp
    5810:	39 aa f4 00 00 00    	cmp    %ebp,0xf4(%rdx)
    5816:	0f 8f 24 ff ff ff    	jg     5740 <receive+0x20>
}
    581c:	5b                   	pop    %rbx
    581d:	31 c0                	xor    %eax,%eax
    581f:	5d                   	pop    %rbp
    5820:	41 5c                	pop    %r12
    5822:	c3                   	ret
    5823:	31 c0                	xor    %eax,%eax
    5825:	c3                   	ret
    5826:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005830 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5830:	f3 0f 1e fa          	endbr64
    5834:	41 57                	push   %r15
    5836:	41 56                	push   %r14
    5838:	41 55                	push   %r13
    583a:	41 54                	push   %r12
    583c:	55                   	push   %rbp
    583d:	53                   	push   %rbx
    583e:	48 89 fb             	mov    %rdi,%rbx
    5841:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    5845:	8b 07                	mov    (%rdi),%eax
    5847:	39 87 f0 00 00 00    	cmp    %eax,0xf0(%rdi)
    584d:	0f 84 4d 01 00 00    	je     59a0 <barriered_work+0x170>
    receive(data);
    5853:	e8 c8 fe ff ff       	call   5720 <receive>
    while (data->scheduled == 1) {
    5858:	8b 83 00 01 00 00    	mov    0x100(%rbx),%eax
    585e:	83 f8 01             	cmp    $0x1,%eax
    5861:	75 26                	jne    5889 <barriered_work+0x59>
    5863:	48 8b 83 c8 00 00 00 	mov    0xc8(%rbx),%rax
    586a:	48 83 c0 01          	add    $0x1,%rax
    586e:	66 90                	xchg   %ax,%ax
    5870:	8b 93 00 01 00 00    	mov    0x100(%rbx),%edx
    5876:	48 89 c1             	mov    %rax,%rcx
    5879:	48 83 c0 01          	add    $0x1,%rax
    587d:	83 fa 01             	cmp    $0x1,%edx
    5880:	74 ee                	je     5870 <barriered_work+0x40>
    5882:	48 89 8b c8 00 00 00 	mov    %rcx,0xc8(%rbx)
  if (data->sending == 1) {
    5889:	83 bb 38 01 00 00 01 	cmpl   $0x1,0x138(%rbx)
    5890:	0f 85 85 02 00 00    	jne    5b1b <barriered_work+0x2eb>
      for (int n = 0 ; n < data->thread_count; n++) {
    5896:	8b 83 f4 00 00 00    	mov    0xf4(%rbx),%eax
    589c:	85 c0                	test   %eax,%eax
    589e:	0f 8e 83 02 00 00    	jle    5b27 <barriered_work+0x2f7>
    58a4:	48 8d b3 48 01 00 00 	lea    0x148(%rbx),%rsi
    58ab:	31 c9                	xor    %ecx,%ecx
    58ad:	4c 8d bb 40 01 00 00 	lea    0x140(%rbx),%r15
    58b4:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    58b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    58c0:	39 8b f0 00 00 00    	cmp    %ecx,0xf0(%rbx)
    58c6:	0f 84 bf 00 00 00    	je     598b <barriered_work+0x15b>
        struct Data *them = data->mailboxes[n].higher;
    58cc:	49 89 c9             	mov    %rcx,%r9
    58cf:	49 c1 e1 05          	shl    $0x5,%r9
    58d3:	4c 03 8b 28 01 00 00 	add    0x128(%rbx),%r9
    58da:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    58de:	49 8b 6a 08          	mov    0x8(%r10),%rbp
    58e2:	4d 63 42 10          	movslq 0x10(%r10),%r8
    58e6:	4c 39 c5             	cmp    %r8,%rbp
    58e9:	0f 8d 93 00 00 00    	jge    5982 <barriered_work+0x152>
    58ef:	4d 89 c3             	mov    %r8,%r11
    58f2:	4c 8b ab c8 00 00 00 	mov    0xc8(%rbx),%r13
    58f9:	4d 8b 61 10          	mov    0x10(%r9),%r12
    58fd:	49 29 eb             	sub    %rbp,%r11
          them->messages[them->messages_count++] = data->message; 
    5900:	49 8b 3a             	mov    (%r10),%rdi
    5903:	49 8d 43 ff          	lea    -0x1(%r11),%rax
    5907:	48 83 f8 02          	cmp    $0x2,%rax
    590b:	0f 86 7f 02 00 00    	jbe    5b90 <barriered_work+0x360>
    5911:	4a 8d 34 c5 00 00 00 00 	lea    0x0(,%r8,8),%rsi
    5919:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    5921:	4c 8d 34 37          	lea    (%rdi,%rsi,1),%r14
    5925:	48 8d 14 07          	lea    (%rdi,%rax,1),%rdx
    5929:	4d 39 f7             	cmp    %r14,%r15
    592c:	0f 83 0e 02 00 00    	jae    5b40 <barriered_work+0x310>
    5932:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    5937:	4c 39 f2             	cmp    %r14,%rdx
    593a:	0f 83 00 02 00 00    	jae    5b40 <barriered_work+0x310>
    5940:	48 01 f8             	add    %rdi,%rax
    5943:	48 01 fe             	add    %rdi,%rsi
    5946:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5950:	4c 8b b3 40 01 00 00 	mov    0x140(%rbx),%r14
        for (; them->messages_count < min;) {
    5957:	48 83 c0 08          	add    $0x8,%rax
          them->messages[them->messages_count++] = data->message; 
    595b:	4c 89 70 f8          	mov    %r14,-0x8(%rax)
        for (; them->messages_count < min;) {
    595f:	48 39 f0             	cmp    %rsi,%rax
    5962:	75 ec                	jne    5950 <barriered_work+0x120>
    5964:	0f 1f 40 00          	nopl   0x0(%rax)
          data->n++;
    5968:	4d 01 dd             	add    %r11,%r13
          data->mailboxes[n].sent++;
    596b:	4d 01 dc             	add    %r11,%r12
          data->n++;
    596e:	4c 89 ab c8 00 00 00 	mov    %r13,0xc8(%rbx)
          data->mailboxes[n].sent++;
    5975:	4d 89 61 10          	mov    %r12,0x10(%r9)
    5979:	4d 89 42 08          	mov    %r8,0x8(%r10)
    597d:	4e 89 74 c7 f8       	mov    %r14,-0x8(%rdi,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5982:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5985:	8b 83 f4 00 00 00    	mov    0xf4(%rbx),%eax
    598b:	48 83 c1 01          	add    $0x1,%rcx
    598f:	39 c8                	cmp    %ecx,%eax
    5991:	0f 8f 29 ff ff ff    	jg     58c0 <barriered_work+0x90>
    5997:	e9 8b 01 00 00       	jmp    5b27 <barriered_work+0x2f7>
    599c:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    59a0:	e8 7b fd ff ff       	call   5720 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    59a5:	8b 8b f4 00 00 00    	mov    0xf4(%rbx),%ecx
        int t = data->task_index;
    59ab:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    59ad:	85 c9                	test   %ecx,%ecx
    59af:	0f 8e 8b 00 00 00    	jle    5a40 <barriered_work+0x210>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59b5:	48 63 d0             	movslq %eax,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
    59b8:	83 c0 01             	add    $0x1,%eax
    59bb:	4c 63 d9             	movslq %ecx,%r11
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59be:	4c 8d 14 52          	lea    (%rdx,%rdx,2),%r10
    59c2:	48 8b 93 e8 00 00 00 	mov    0xe8(%rbx),%rdx
    59c9:	4a 8d 2c dd 00 00 00 00 	lea    0x0(,%r11,8),%rbp
    59d1:	49 c1 e2 07          	shl    $0x7,%r10
    59d5:	48 8b 7a 40          	mov    0x40(%rdx),%rdi
              int next_task = abs((t + 1) % (data->thread_count));
    59d9:	99                   	cltd
    59da:	f7 f9                	idiv   %ecx
    59dc:	89 d0                	mov    %edx,%eax
    59de:	f7 d8                	neg    %eax
    59e0:	0f 48 c2             	cmovs  %edx,%eax
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59e3:	45 31 ed             	xor    %r13d,%r13d
    59e6:	48 98                	cltq
    59e8:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
    59ec:	49 c1 e4 07          	shl    $0x7,%r12
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59f0:	4e 8d 0c 2f          	lea    (%rdi,%r13,1),%r9
    59f4:	4e 8d 04 ad 00 00 00 00 	lea    0x0(,%r13,4),%r8
    59fc:	31 c0                	xor    %eax,%eax
    59fe:	66 90                	xchg   %ax,%ax
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5a00:	48 8b 14 c7          	mov    (%rdi,%rax,8),%rdx
    5a04:	48 8b 52 58          	mov    0x58(%rdx),%rdx
    5a08:	4a 8b 8c 22 28 01 00 00 	mov    0x128(%rdx,%r12,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5a10:	49 8b 11             	mov    (%r9),%rdx
    5a13:	48 8b 72 58          	mov    0x58(%rdx),%rsi
    5a17:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5a1a:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5a1e:	48 c1 e2 05          	shl    $0x5,%rdx
    5a22:	4a 03 94 16 28 01 00 00 	add    0x128(%rsi,%r10,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5a2a:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    5a2e:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    5a32:	49 39 c3             	cmp    %rax,%r11
    5a35:	75 c9                	jne    5a00 <barriered_work+0x1d0>
        for (int y = 0; y < data->thread_count ; y++) {
    5a37:	49 83 c5 08          	add    $0x8,%r13
    5a3b:	4c 39 ed             	cmp    %r13,%rbp
    5a3e:	75 b0                	jne    59f0 <barriered_work+0x1c0>
      asm volatile ("sfence" ::: "memory");
    5a40:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5a43:	48 8b b3 18 01 00 00 	mov    0x118(%rbx),%rsi
    5a4a:	31 ff                	xor    %edi,%edi
    5a4c:	48 c1 e6 05          	shl    $0x5,%rsi
    5a50:	48 03 b3 08 01 00 00 	add    0x108(%rbx),%rsi
    5a57:	e8 b4 c8 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5a5c:	48 8b 83 e8 00 00 00 	mov    0xe8(%rbx),%rax
    5a63:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    5a6a:	8b 72 10             	mov    0x10(%rdx),%esi
    5a6d:	8d 6e 01             	lea    0x1(%rsi),%ebp
    5a70:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5a73:	8b 93 00 01 00 00    	mov    0x100(%rbx),%edx
    5a79:	83 fa 01             	cmp    $0x1,%edx
    5a7c:	75 58                	jne    5ad6 <barriered_work+0x2a6>
    5a7e:	66 90                	xchg   %ax,%ax
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a80:	48 8b 40 40          	mov    0x40(%rax),%rax
    5a84:	48 63 93 f0 00 00 00 	movslq 0xf0(%rbx),%rdx
      data->n++;
    5a8b:	48 83 83 c8 00 00 00 01 	addq   $0x1,0xc8(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a93:	48 8b 14 d0          	mov    (%rax,%rdx,8),%rdx
    5a97:	48 63 03             	movslq (%rbx),%rax
    5a9a:	48 8d 3c 40          	lea    (%rax,%rax,2),%rdi
    5a9e:	48 c1 e7 07          	shl    $0x7,%rdi
    5aa2:	48 03 7a 58          	add    0x58(%rdx),%rdi
    5aa6:	ff 93 e0 00 00 00    	call   *0xe0(%rbx)
    while (data->scheduled == 1) {
    5aac:	8b 83 00 01 00 00    	mov    0x100(%rbx),%eax
    5ab2:	83 f8 01             	cmp    $0x1,%eax
    if (modcount != data->thread->protected_state->modcount) {
    5ab5:	48 8b 83 e8 00 00 00 	mov    0xe8(%rbx),%rax
    while (data->scheduled == 1) {
    5abc:	74 c2                	je     5a80 <barriered_work+0x250>
    if (modcount != data->thread->protected_state->modcount) {
    5abe:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    5ac5:	3b 68 10             	cmp    0x10(%rax),%ebp
    5ac8:	74 0c                	je     5ad6 <barriered_work+0x2a6>
    5aca:	48 8d 3d 3f 17 00 00 	lea    0x173f(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    5ad1:	e8 1a c8 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5ad6:	48 8b b3 18 01 00 00 	mov    0x118(%rbx),%rsi
    5add:	31 ff                	xor    %edi,%edi
    5adf:	48 c1 e6 05          	shl    $0x5,%rsi
    5ae3:	48 03 b3 08 01 00 00 	add    0x108(%rbx),%rsi
    5aea:	48 83 c6 10          	add    $0x10,%rsi
    5aee:	e8 1d c8 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5af3:	48 8b 83 18 01 00 00 	mov    0x118(%rbx),%rax
    5afa:	48 83 c0 01          	add    $0x1,%rax
    5afe:	48 99                	cqto
    5b00:	48 f7 bb 10 01 00 00 	idivq  0x110(%rbx)
  if (data->sending == 1) {
    5b07:	83 bb 38 01 00 00 01 	cmpl   $0x1,0x138(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5b0e:	48 89 93 18 01 00 00 	mov    %rdx,0x118(%rbx)
  if (data->sending == 1) {
    5b15:	0f 84 8a 00 00 00    	je     5ba5 <barriered_work+0x375>
    5b1b:	48 8d 3d e2 16 00 00 	lea    0x16e2(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5b22:	e8 c9 c7 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5b27:	0f ae f8             	sfence
}
    5b2a:	48 83 c4 18          	add    $0x18,%rsp
    5b2e:	31 c0                	xor    %eax,%eax
    5b30:	5b                   	pop    %rbx
    5b31:	5d                   	pop    %rbp
    5b32:	41 5c                	pop    %r12
    5b34:	41 5d                	pop    %r13
    5b36:	41 5e                	pop    %r14
    5b38:	41 5f                	pop    %r15
    5b3a:	c3                   	ret
    5b3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5b40:	4c 8b b3 40 01 00 00 	mov    0x140(%rbx),%r14
    5b47:	4c 89 d8             	mov    %r11,%rax
    5b4a:	48 d1 e8             	shr    %rax
    5b4d:	66 49 0f 6e c6       	movq   %r14,%xmm0
    5b52:	48 c1 e0 04          	shl    $0x4,%rax
    5b56:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5b5a:	48 01 d0             	add    %rdx,%rax
    5b5d:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5b60:	0f 11 02             	movups %xmm0,(%rdx)
        for (; them->messages_count < min;) {
    5b63:	48 83 c2 10          	add    $0x10,%rdx
    5b67:	48 39 d0             	cmp    %rdx,%rax
    5b6a:	75 f4                	jne    5b60 <barriered_work+0x330>
    5b6c:	4c 89 d8             	mov    %r11,%rax
    5b6f:	48 83 e0 fe          	and    $0xfffffffffffffffe,%rax
    5b73:	48 01 e8             	add    %rbp,%rax
    5b76:	41 f6 c3 01          	test   $0x1,%r11b
    5b7a:	0f 84 e8 fd ff ff    	je     5968 <barriered_work+0x138>
          them->messages[them->messages_count++] = data->message; 
    5b80:	4c 8b b3 40 01 00 00 	mov    0x140(%rbx),%r14
    5b87:	4c 89 34 c7          	mov    %r14,(%rdi,%rax,8)
        for (; them->messages_count < min;) {
    5b8b:	e9 d8 fd ff ff       	jmp    5968 <barriered_work+0x138>
    5b90:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    5b98:	4a 8d 34 c5 00 00 00 00 	lea    0x0(,%r8,8),%rsi
    5ba0:	e9 9b fd ff ff       	jmp    5940 <barriered_work+0x110>
      for (int n = 0 ; n < data->thread_count; n++) {
    5ba5:	8b 83 f4 00 00 00    	mov    0xf4(%rbx),%eax
    5bab:	48 8d b3 48 01 00 00 	lea    0x148(%rbx),%rsi
    5bb2:	31 c9                	xor    %ecx,%ecx
    5bb4:	4c 8d bb 40 01 00 00 	lea    0x140(%rbx),%r15
    5bbb:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5bc0:	85 c0                	test   %eax,%eax
    5bc2:	0f 8e 5f ff ff ff    	jle    5b27 <barriered_work+0x2f7>
    5bc8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        if (n == data->thread_index) { continue; }
    5bd0:	39 8b f0 00 00 00    	cmp    %ecx,0xf0(%rbx)
    5bd6:	0f 84 af 00 00 00    	je     5c8b <barriered_work+0x45b>
        struct Data *them = data->mailboxes[n].higher;
    5bdc:	49 89 c9             	mov    %rcx,%r9
    5bdf:	49 c1 e1 05          	shl    $0x5,%r9
    5be3:	4c 03 8b 28 01 00 00 	add    0x128(%rbx),%r9
    5bea:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    5bee:	49 8b 6a 08          	mov    0x8(%r10),%rbp
    5bf2:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5bf6:	49 39 e8             	cmp    %rbp,%r8
    5bf9:	0f 8e 83 00 00 00    	jle    5c82 <barriered_work+0x452>
    5bff:	4d 89 c3             	mov    %r8,%r11
    5c02:	4c 8b ab c8 00 00 00 	mov    0xc8(%rbx),%r13
    5c09:	4d 8b 61 10          	mov    0x10(%r9),%r12
    5c0d:	49 29 eb             	sub    %rbp,%r11
          them->messages[them->messages_count++] = data->message; 
    5c10:	49 8b 3a             	mov    (%r10),%rdi
    5c13:	49 8d 43 ff          	lea    -0x1(%r11),%rax
    5c17:	48 83 f8 02          	cmp    $0x2,%rax
    5c1b:	0f 86 cf 00 00 00    	jbe    5cf0 <barriered_work+0x4c0>
    5c21:	4a 8d 34 c5 00 00 00 00 	lea    0x0(,%r8,8),%rsi
    5c29:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    5c31:	4c 8d 34 37          	lea    (%rdi,%rsi,1),%r14
    5c35:	48 8d 14 07          	lea    (%rdi,%rax,1),%rdx
    5c39:	4d 39 f7             	cmp    %r14,%r15
    5c3c:	73 62                	jae    5ca0 <barriered_work+0x470>
    5c3e:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    5c43:	4c 39 f2             	cmp    %r14,%rdx
    5c46:	73 58                	jae    5ca0 <barriered_work+0x470>
    5c48:	48 01 f8             	add    %rdi,%rax
    5c4b:	48 01 fe             	add    %rdi,%rsi
    5c4e:	66 90                	xchg   %ax,%ax
    5c50:	4c 8b b3 40 01 00 00 	mov    0x140(%rbx),%r14
        for (; them->messages_count < min;) {
    5c57:	48 83 c0 08          	add    $0x8,%rax
          them->messages[them->messages_count++] = data->message; 
    5c5b:	4c 89 70 f8          	mov    %r14,-0x8(%rax)
        for (; them->messages_count < min;) {
    5c5f:	48 39 f0             	cmp    %rsi,%rax
    5c62:	75 ec                	jne    5c50 <barriered_work+0x420>
    5c64:	0f 1f 40 00          	nopl   0x0(%rax)
          data->n++;
    5c68:	4d 01 dd             	add    %r11,%r13
          data->mailboxes[n].sent++;
    5c6b:	4d 01 dc             	add    %r11,%r12
          data->n++;
    5c6e:	4c 89 ab c8 00 00 00 	mov    %r13,0xc8(%rbx)
          data->mailboxes[n].sent++;
    5c75:	4d 89 61 10          	mov    %r12,0x10(%r9)
    5c79:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5c7d:	4e 89 74 c7 f8       	mov    %r14,-0x8(%rdi,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5c82:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5c85:	8b 83 f4 00 00 00    	mov    0xf4(%rbx),%eax
    5c8b:	48 83 c1 01          	add    $0x1,%rcx
    5c8f:	39 c8                	cmp    %ecx,%eax
    5c91:	0f 8f 39 ff ff ff    	jg     5bd0 <barriered_work+0x3a0>
    5c97:	e9 8b fe ff ff       	jmp    5b27 <barriered_work+0x2f7>
    5c9c:	0f 1f 40 00          	nopl   0x0(%rax)
    5ca0:	4c 8b b3 40 01 00 00 	mov    0x140(%rbx),%r14
    5ca7:	4c 89 d8             	mov    %r11,%rax
    5caa:	48 d1 e8             	shr    %rax
    5cad:	66 49 0f 6e c6       	movq   %r14,%xmm0
    5cb2:	48 c1 e0 04          	shl    $0x4,%rax
    5cb6:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5cba:	48 01 d0             	add    %rdx,%rax
    5cbd:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5cc0:	0f 11 02             	movups %xmm0,(%rdx)
        for (; them->messages_count < min;) {
    5cc3:	48 83 c2 10          	add    $0x10,%rdx
    5cc7:	48 39 c2             	cmp    %rax,%rdx
    5cca:	75 f4                	jne    5cc0 <barriered_work+0x490>
    5ccc:	4c 89 d8             	mov    %r11,%rax
    5ccf:	48 83 e0 fe          	and    $0xfffffffffffffffe,%rax
    5cd3:	48 01 e8             	add    %rbp,%rax
    5cd6:	41 f6 c3 01          	test   $0x1,%r11b
    5cda:	74 8c                	je     5c68 <barriered_work+0x438>
          them->messages[them->messages_count++] = data->message; 
    5cdc:	4c 8b b3 40 01 00 00 	mov    0x140(%rbx),%r14
    5ce3:	4c 89 34 c7          	mov    %r14,(%rdi,%rax,8)
        for (; them->messages_count < min;) {
    5ce7:	e9 7c ff ff ff       	jmp    5c68 <barriered_work+0x438>
    5cec:	0f 1f 40 00          	nopl   0x0(%rax)
    5cf0:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    5cf8:	4a 8d 34 c5 00 00 00 00 	lea    0x0(,%r8,8),%rsi
    5d00:	e9 43 ff ff ff       	jmp    5c48 <barriered_work+0x418>
    5d05:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005d10 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5d10:	f3 0f 1e fa          	endbr64
    5d14:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5d18:	48 8b 87 e8 00 00 00 	mov    0xe8(%rdi),%rax
    5d1f:	48 8b 80 c0 00 00 00 	mov    0xc0(%rax),%rax
    5d26:	48 63 10             	movslq (%rax),%rdx
    5d29:	85 d2                	test   %edx,%edx
    5d2b:	7e 31                	jle    5d5e <barriered_work_ingest+0x4e>
    5d2d:	48 8b 40 08          	mov    0x8(%rax),%rax
    5d31:	48 c1 e2 04          	shl    $0x4,%rdx
    5d35:	48 01 c2             	add    %rax,%rdx
    5d38:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    if (data->thread->buffers->buffer[x].available == 1) {
    5d40:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5d44:	75 0f                	jne    5d55 <barriered_work_ingest+0x45>
      data->ingest_count++;
    5d46:	48 83 87 20 01 00 00 01 	addq   $0x1,0x120(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5d4e:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5d55:	48 83 c0 10          	add    $0x10,%rax
    5d59:	48 39 d0             	cmp    %rdx,%rax
    5d5c:	75 e2                	jne    5d40 <barriered_work_ingest+0x30>
  asm volatile ("sfence" ::: "memory");
    5d5e:	0f ae f8             	sfence
  barriered_work(data);
    5d61:	e8 ca fa ff ff       	call   5830 <barriered_work>
}
    5d66:	31 c0                	xor    %eax,%eax
    5d68:	48 83 c4 08          	add    $0x8,%rsp
    5d6c:	c3                   	ret
    5d6d:	0f 1f 00             	nopl   (%rax)

0000000000005d70 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5d70:	f3 0f 1e fa          	endbr64
}
    5d74:	31 c0                	xor    %eax,%eax
    5d76:	c3                   	ret
    5d77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005d80 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5d80:	f3 0f 1e fa          	endbr64
    5d84:	31 c0                	xor    %eax,%eax
    5d86:	c3                   	ret
    5d87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005d90 <after>:
int after(struct timespec left, struct timespec right) {
    5d90:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5d94:	31 c0                	xor    %eax,%eax
    5d96:	48 39 d7             	cmp    %rdx,%rdi
    5d99:	7e 08                	jle    5da3 <after+0x13>
    5d9b:	31 c0                	xor    %eax,%eax
    5d9d:	48 39 ce             	cmp    %rcx,%rsi
    5da0:	0f 9f c0             	setg   %al
}
    5da3:	c3                   	ret
    5da4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5daf:	90                   	nop

0000000000005db0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5db0:	f3 0f 1e fa          	endbr64
    5db4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5db9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5dbe:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5dc0:	48 39 d7             	cmp    %rdx,%rdi
    5dc3:	7f 18                	jg     5ddd <within+0x2d>
    5dc5:	4d 39 d8             	cmp    %r11,%r8
    5dc8:	0f 9e c2             	setle  %dl
    5dcb:	48 39 ce             	cmp    %rcx,%rsi
    5dce:	0f 9e c0             	setle  %al
    5dd1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5dd3:	31 c0                	xor    %eax,%eax
    5dd5:	4d 39 d1             	cmp    %r10,%r9
    5dd8:	0f 9e c0             	setle  %al
    5ddb:	21 d0                	and    %edx,%eax
}
    5ddd:	c3                   	ret
    5dde:	66 90                	xchg   %ax,%ax

0000000000005de0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5de0:	f3 0f 1e fa          	endbr64
    5de4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5de9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5dee:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    5df3:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    5df8:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
    5dfd:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5e02:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5e07:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5e0c:	48 39 fe             	cmp    %rdi,%rsi
    5e0f:	7d 2f                	jge    5e40 <overlap+0x60>
    5e11:	48 39 ca             	cmp    %rcx,%rdx
    5e14:	7d 62                	jge    5e78 <overlap+0x98>
    5e16:	4d 39 da             	cmp    %r11,%r10
    5e19:	7e 0e                	jle    5e29 <overlap+0x49>
    return 1;
    5e1b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e20:	4d 39 c1             	cmp    %r8,%r9
    5e23:	0f 8f 7f 00 00 00    	jg     5ea8 <overlap+0xc8>
  return 0;
    5e29:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e2b:	4d 39 c1             	cmp    %r8,%r9
    5e2e:	7c 4c                	jl     5e7c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e30:	31 c0                	xor    %eax,%eax
    5e32:	4d 39 da             	cmp    %r11,%r10
    5e35:	0f 9d c0             	setge  %al
    5e38:	c3                   	ret
    5e39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5e40:	7e 4e                	jle    5e90 <overlap+0xb0>
    5e42:	48 39 ca             	cmp    %rcx,%rdx
    5e45:	7f 39                	jg     5e80 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e47:	75 31                	jne    5e7a <overlap+0x9a>
    5e49:	4d 39 c1             	cmp    %r8,%r9
    5e4c:	7f 2c                	jg     5e7a <overlap+0x9a>
    return 1;
    5e4e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e53:	4d 39 da             	cmp    %r11,%r10
    5e56:	7e 24                	jle    5e7c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e58:	48 39 ca             	cmp    %rcx,%rdx
    5e5b:	0f 94 c2             	sete   %dl
    5e5e:	48 39 fe             	cmp    %rdi,%rsi
    5e61:	0f 94 c0             	sete   %al
    5e64:	21 c2                	and    %eax,%edx
    5e66:	31 c0                	xor    %eax,%eax
    5e68:	4d 39 c1             	cmp    %r8,%r9
    5e6b:	0f 94 c0             	sete   %al
    5e6e:	21 d0                	and    %edx,%eax
    5e70:	c3                   	ret
    5e71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5e78:	74 af                	je     5e29 <overlap+0x49>
  return 0;
    5e7a:	31 c0                	xor    %eax,%eax
}
    5e7c:	c3                   	ret
    5e7d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5e80:	4d 39 c1             	cmp    %r8,%r9
    5e83:	7d c4                	jge    5e49 <overlap+0x69>
    return 1;
    5e85:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e8a:	4d 39 da             	cmp    %r11,%r10
    5e8d:	7d ba                	jge    5e49 <overlap+0x69>
    5e8f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e90:	48 39 ca             	cmp    %rcx,%rdx
    5e93:	7c 94                	jl     5e29 <overlap+0x49>
    5e95:	4d 39 c1             	cmp    %r8,%r9
    5e98:	7e b4                	jle    5e4e <overlap+0x6e>
    5e9a:	48 39 ca             	cmp    %rcx,%rdx
    5e9d:	74 91                	je     5e30 <overlap+0x50>
    5e9f:	eb d9                	jmp    5e7a <overlap+0x9a>
    5ea1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5ea8:	c3                   	ret
    5ea9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005eb0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5eb0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5eb4:	85 f6                	test   %esi,%esi
    5eb6:	0f 8e 2d 03 00 00    	jle    61e9 <verify+0x339>
int verify(struct KernelThread *thread_data, int thread_count) {
    5ebc:	41 57                	push   %r15
    5ebe:	41 89 f7             	mov    %esi,%r15d
    5ec1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5ec3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5ec6:	41 55                	push   %r13
    5ec8:	41 54                	push   %r12
    5eca:	55                   	push   %rbp
    5ecb:	53                   	push   %rbx
    5ecc:	48 8d 5f 58          	lea    0x58(%rdi),%rbx
    5ed0:	48 83 ec 48          	sub    $0x48,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5ed4:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5ed9:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    5ede:	31 ed                	xor    %ebp,%ebp
    5ee0:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    5ee5:	41 89 ec             	mov    %ebp,%r12d
      if (z != x)  {
    5ee8:	45 39 f4             	cmp    %r14d,%r12d
    5eeb:	0f 84 4b 02 00 00    	je     613c <verify+0x28c>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5ef1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5ef6:	8b 50 08             	mov    0x8(%rax),%edx
    5ef9:	85 d2                	test   %edx,%edx
    5efb:	0f 8e 3b 02 00 00    	jle    613c <verify+0x28c>
    5f01:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    5f09:	45 31 ed             	xor    %r13d,%r13d
    5f0c:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    5f11:	44 89 f2             	mov    %r14d,%edx
    5f14:	48 8d 35 05 13 00 00 	lea    0x1305(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    5f1b:	bf 01 00 00 00       	mov    $0x1,%edi
    5f20:	31 c0                	xor    %eax,%eax
    5f22:	e8 29 c5 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5f27:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5f2c:	8b 40 08             	mov    0x8(%rax),%eax
    5f2f:	85 c0                	test   %eax,%eax
    5f31:	0f 8e e5 01 00 00    	jle    611c <verify+0x26c>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5f37:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5f3c:	44 89 6c 24 34       	mov    %r13d,0x34(%rsp)
    5f41:	31 db                	xor    %ebx,%ebx
    5f43:	44 89 74 24 38       	mov    %r14d,0x38(%rsp)
    5f48:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    5f4d:	48 8b 28             	mov    (%rax),%rbp
    5f50:	4c 8b 6c 24 08       	mov    0x8(%rsp),%r13
    5f55:	48 8d 04 5b          	lea    (%rbx,%rbx,2),%rax
    5f59:	4c 8b 3c 24          	mov    (%rsp),%r15
    5f5d:	48 8d 35 d1 12 00 00 	lea    0x12d1(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5f64:	49 89 c6             	mov    %rax,%r14
    5f67:	bf 01 00 00 00       	mov    $0x1,%edi
    5f6c:	49 8b 45 00          	mov    0x0(%r13),%rax
    5f70:	49 c1 e6 07          	shl    $0x7,%r14
    5f74:	4a 8b 8c 3d 18 01 00 00 	mov    0x118(%rbp,%r15,1),%rcx
    5f7c:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    5f81:	4a 8b 94 30 18 01 00 00 	mov    0x118(%rax,%r14,1),%rdx
    5f89:	31 c0                	xor    %eax,%eax
    5f8b:	e8 c0 c4 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5f90:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5f95:	48 8b 28             	mov    (%rax),%rbp
    5f98:	4a 83 bc 3d 18 01 00 00 00 	cmpq   $0x0,0x118(%rbp,%r15,1)
    5fa1:	0f 8e 54 01 00 00    	jle    60fb <verify+0x24b>
    5fa7:	4d 03 75 00          	add    0x0(%r13),%r14
    5fab:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5fb0:	ba 01 00 00 00       	mov    $0x1,%edx
    5fb5:	4d 89 f3             	mov    %r14,%r11
    5fb8:	4d 8b b3 18 01 00 00 	mov    0x118(%r11),%r14
    5fbf:	4d 85 f6             	test   %r14,%r14
    5fc2:	0f 8e 2e 01 00 00    	jle    60f6 <verify+0x246>
    5fc8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5fd0:	48 8b 04 24          	mov    (%rsp),%rax
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5fd4:	49 89 d4             	mov    %rdx,%r12
    5fd7:	31 db                	xor    %ebx,%ebx
    5fd9:	49 89 d5             	mov    %rdx,%r13
    5fdc:	49 c1 e4 05          	shl    $0x5,%r12
    5fe0:	49 83 ec 20          	sub    $0x20,%r12
    5fe4:	4c 8d 7c 05 00       	lea    0x0(%rbp,%rax,1),%r15
    5fe9:	eb 32                	jmp    601d <verify+0x16d>
    5feb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5ff0:	4c 39 c2             	cmp    %r8,%rdx
    5ff3:	0f 8d 67 01 00 00    	jge    6160 <verify+0x2b0>
    5ff9:	4c 39 d7             	cmp    %r10,%rdi
    5ffc:	7e 09                	jle    6007 <verify+0x157>
    5ffe:	49 39 c1             	cmp    %rax,%r9
    6001:	0f 8c 81 00 00 00    	jl     6088 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6007:	4c 39 d7             	cmp    %r10,%rdi
    600a:	0f 8d 9b 01 00 00    	jge    61ab <verify+0x2fb>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6010:	48 83 c3 01          	add    $0x1,%rbx
    6014:	49 39 de             	cmp    %rbx,%r14
    6017:	0f 8e b9 00 00 00    	jle    60d6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    601d:	49 8b 97 08 01 00 00 	mov    0x108(%r15),%rdx
    6024:	48 89 d8             	mov    %rbx,%rax
    6027:	48 c1 e0 05          	shl    $0x5,%rax
    602b:	49 03 83 08 01 00 00 	add    0x108(%r11),%rax
    6032:	4c 01 e2             	add    %r12,%rdx
    6035:	48 8b 08             	mov    (%rax),%rcx
    6038:	48 8b 78 10          	mov    0x10(%rax),%rdi
    603c:	48 8b 32             	mov    (%rdx),%rsi
    603f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6043:	4c 8b 52 10          	mov    0x10(%rdx),%r10
    6047:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    604b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    604f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6053:	48 39 f1             	cmp    %rsi,%rcx
    6056:	7c 98                	jl     5ff0 <verify+0x140>
    6058:	0f 8e 32 01 00 00    	jle    6190 <verify+0x2e0>
    605e:	4c 39 c2             	cmp    %r8,%rdx
    6061:	0f 8f 09 01 00 00    	jg     6170 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6067:	75 a7                	jne    6010 <verify+0x160>
    6069:	4c 39 d7             	cmp    %r10,%rdi
    606c:	7f a2                	jg     6010 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    606e:	49 39 c1             	cmp    %rax,%r9
    6071:	7d 15                	jge    6088 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6073:	48 39 f1             	cmp    %rsi,%rcx
    6076:	75 98                	jne    6010 <verify+0x160>
    6078:	4c 39 c2             	cmp    %r8,%rdx
    607b:	75 93                	jne    6010 <verify+0x160>
    607d:	4c 39 d7             	cmp    %r10,%rdi
    6080:	75 8e                	jne    6010 <verify+0x160>
    6082:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6088:	49 89 c1             	mov    %rax,%r9
    608b:	48 89 f9             	mov    %rdi,%rcx
    608e:	48 89 f2             	mov    %rsi,%rdx
    6091:	bf 01 00 00 00       	mov    $0x1,%edi
    6096:	48 8d 35 eb 13 00 00 	lea    0x13eb(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    609d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    609f:	48 83 c3 01          	add    $0x1,%rbx
    60a3:	e8 a8 c3 ff ff       	call   2450 <__printf_chk@plt>
    60a8:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    60ad:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    60b2:	4c 03 18             	add    (%rax),%r11
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60b5:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60ba:	4d 8b b3 18 01 00 00 	mov    0x118(%r11),%r14
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60c1:	48 8b 28             	mov    (%rax),%rbp
    60c4:	48 8b 04 24          	mov    (%rsp),%rax
    60c8:	4c 8d 7c 05 00       	lea    0x0(%rbp,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60cd:	49 39 de             	cmp    %rbx,%r14
    60d0:	0f 8f 47 ff ff ff    	jg     601d <verify+0x16d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60d6:	4c 89 ea             	mov    %r13,%rdx
    60d9:	4d 3b af 18 01 00 00 	cmp    0x118(%r15),%r13
    60e0:	7d 14                	jge    60f6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60e2:	4d 8b b3 18 01 00 00 	mov    0x118(%r11),%r14
    60e9:	48 83 c2 01          	add    $0x1,%rdx
    60ed:	4d 85 f6             	test   %r14,%r14
    60f0:	0f 8f da fe ff ff    	jg     5fd0 <verify+0x120>
    60f6:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    60fb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6100:	48 83 c3 01          	add    $0x1,%rbx
    6104:	39 58 08             	cmp    %ebx,0x8(%rax)
    6107:	0f 8f 43 fe ff ff    	jg     5f50 <verify+0xa0>
    610d:	44 8b 6c 24 34       	mov    0x34(%rsp),%r13d
    6112:	44 8b 74 24 38       	mov    0x38(%rsp),%r14d
    6117:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    611c:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6121:	48 81 04 24 80 01 00 00 	addq   $0x180,(%rsp)
    6129:	41 83 c5 01          	add    $0x1,%r13d
    612d:	44 39 68 08          	cmp    %r13d,0x8(%rax)
    6131:	0f 8f da fd ff ff    	jg     5f11 <verify+0x61>
    6137:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    613c:	48 81 44 24 08 40 01 00 00 	addq   $0x140,0x8(%rsp)
    6145:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    614a:	41 39 c7             	cmp    %eax,%r15d
    614d:	74 6a                	je     61b9 <verify+0x309>
    614f:	41 89 c4             	mov    %eax,%r12d
    6152:	e9 91 fd ff ff       	jmp    5ee8 <verify+0x38>
    6157:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6160:	0f 85 aa fe ff ff    	jne    6010 <verify+0x160>
    6166:	e9 9c fe ff ff       	jmp    6007 <verify+0x157>
    616b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6170:	4c 39 d7             	cmp    %r10,%rdi
    6173:	0f 8d f0 fe ff ff    	jge    6069 <verify+0x1b9>
    6179:	49 39 c1             	cmp    %rax,%r9
    617c:	0f 8e e7 fe ff ff    	jle    6069 <verify+0x1b9>
    6182:	e9 01 ff ff ff       	jmp    6088 <verify+0x1d8>
    6187:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6190:	4c 39 c2             	cmp    %r8,%rdx
    6193:	0f 8c 6e fe ff ff    	jl     6007 <verify+0x157>
    6199:	4c 39 d7             	cmp    %r10,%rdi
    619c:	0f 8e cc fe ff ff    	jle    606e <verify+0x1be>
    61a2:	4c 39 c2             	cmp    %r8,%rdx
    61a5:	0f 85 65 fe ff ff    	jne    6010 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    61ab:	49 39 c1             	cmp    %rax,%r9
    61ae:	0f 8f 5c fe ff ff    	jg     6010 <verify+0x160>
    61b4:	e9 cf fe ff ff       	jmp    6088 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    61b9:	48 81 44 24 10 40 01 00 00 	addq   $0x140,0x10(%rsp)
    61c2:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    61c7:	41 8d 46 01          	lea    0x1(%r14),%eax
    61cb:	45 39 f4             	cmp    %r14d,%r12d
    61ce:	74 08                	je     61d8 <verify+0x328>
    61d0:	41 89 c6             	mov    %eax,%r14d
    61d3:	e9 01 fd ff ff       	jmp    5ed9 <verify+0x29>
}
    61d8:	48 83 c4 48          	add    $0x48,%rsp
    61dc:	31 c0                	xor    %eax,%eax
    61de:	5b                   	pop    %rbx
    61df:	5d                   	pop    %rbp
    61e0:	41 5c                	pop    %r12
    61e2:	41 5d                	pop    %r13
    61e4:	41 5e                	pop    %r14
    61e6:	41 5f                	pop    %r15
    61e8:	c3                   	ret
    61e9:	31 c0                	xor    %eax,%eax
    61eb:	c3                   	ret

Disassembly of section .fini:

00000000000061ec <_fini>:
    61ec:	f3 0f 1e fa          	endbr64
    61f0:	48 83 ec 08          	sub    $0x8,%rsp
    61f4:	48 83 c4 08          	add    $0x8,%rsp
    61f8:	c3                   	ret
