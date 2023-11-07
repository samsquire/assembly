
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
    261d:	48 8d 05 bc 11 00 00 	lea    0x11bc(%rip),%rax        # 37e0 <barriered_reset>
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
    2743:	be 40 01 00 00       	mov    $0x140,%esi
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
    27f5:	0f 84 34 0e 00 00    	je     362f <main+0x103f>
      my_thread_data[0] = &thread_data[other]; 
    27fb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    2800:	4d 89 e8             	mov    %r13,%r8
    2803:	89 ea                	mov    %ebp,%edx
    2805:	bf 01 00 00 00       	mov    $0x1,%edi
    280a:	49 8d 8d c0 fe ff ff 	lea    -0x140(%r13),%rcx
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
    283c:	4d 89 a5 80 00 00 00 	mov    %r12,0x80(%r13)
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
    2865:	45 89 b5 28 01 00 00 	mov    %r14d,0x128(%r13)
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
    thread_data[x].cpu_set = sendercpu;
    28a3:	49 89 9d 20 01 00 00 	mov    %rbx,0x120(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28aa:	31 db                	xor    %ebx,%ebx
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28ac:	be 10 00 00 00       	mov    $0x10,%esi
    thread_data[x].real_thread_index = x;
    28b1:	41 89 6d 04          	mov    %ebp,0x4(%r13)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28b5:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].threads = my_thread_data;
    28ba:	49 89 45 40          	mov    %rax,0x40(%r13)
    thread_data[x].thread_count = 2;
    28be:	48 8b 05 7b 51 00 00 	mov    0x517b(%rip),%rax        # 7a40 <_IO_stdin_used+0xa40>
    thread_data[x].task_count = total_barrier_count;
    28c5:	41 c7 45 60 03 00 00 00 	movl   $0x3,0x60(%r13)
    thread_data[x].thread_count = 2;
    28cd:	49 89 45 48          	mov    %rax,0x48(%r13)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28d1:	e8 ca fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28d6:	be 10 00 00 00       	mov    $0x10,%esi
    28db:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28e0:	49 89 85 d8 00 00 00 	mov    %rax,0xd8(%r13)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28e7:	e8 b4 fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28ec:	be 28 00 00 00       	mov    $0x28,%esi
    28f1:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    28f6:	66 0f 6f 15 22 51 00 00 	movdqa 0x5122(%rip),%xmm2        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28fe:	49 89 85 e0 00 00 00 	mov    %rax,0xe0(%r13)
    thread_data[x].timestamp_count = 0;
    2905:	41 0f 29 95 f0 00 00 00 	movaps %xmm2,0xf0(%r13)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    290d:	e8 8e fa ff ff       	call   23a0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2912:	be 00 02 00 00       	mov    $0x200,%esi
    2917:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
    291c:	66 0f 6f 1d fc 50 00 00 	movdqa 0x50fc(%rip),%xmm3        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2924:	49 89 85 00 01 00 00 	mov    %rax,0x100(%r13)
    thread_data[x].task_timestamp_count = 0;
    292b:	41 0f 11 9d 08 01 00 00 	movups %xmm3,0x108(%r13)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2933:	e8 68 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    2938:	44 89 7c 24 28       	mov    %r15d,0x28(%rsp)
      thread_data[x].tasks = barriers;
    293d:	49 89 45 58          	mov    %rax,0x58(%r13)
        thread_data[x].tasks[y].sending = 1;
    2941:	49 89 c4             	mov    %rax,%r12
    2944:	89 6c 24 08          	mov    %ebp,0x8(%rsp)
        thread_data[x].tasks[y].protected = do_protected_write; 
    2948:	48 63 eb             	movslq %ebx,%rbp
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    294b:	be 20 00 00 00       	mov    $0x20,%esi
    2950:	bf 0c 00 00 00       	mov    $0xc,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    2955:	49 89 ef             	mov    %rbp,%r15
    2958:	48 8d 05 41 0e 00 00 	lea    0xe41(%rip),%rax        # 37a0 <do_protected_write>
    295f:	49 c1 e7 09          	shl    $0x9,%r15
    2963:	4d 01 fc             	add    %r15,%r12
    2966:	49 89 84 24 20 01 00 00 	mov    %rax,0x120(%r12)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    296e:	e8 2d fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    2973:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    2977:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    297c:	49 89 c6             	mov    %rax,%r14
    297f:	49 89 84 24 68 01 00 00 	mov    %rax,0x168(%r12)
        for (int b = 0 ; b < 2 ; b++) {
    2987:	4c 8d 60 40          	lea    0x40(%rax),%r12
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    298b:	be 08 00 00 00       	mov    $0x8,%esi
    2990:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    2995:	49 83 c6 20          	add    $0x20,%r14
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2999:	e8 02 fa ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    299e:	be 08 00 00 00       	mov    $0x8,%esi
    29a3:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29a8:	48 89 c5             	mov    %rax,%rbp
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29ab:	e8 f0 f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29b0:	be 18 00 00 00       	mov    $0x18,%esi
    29b5:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29ba:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29bd:	e8 de f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    29c2:	66 0f 6f 05 66 50 00 00 	movdqa 0x5066(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
          mailboxes[b].higher = &data[1];
    29ca:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29ce:	49 89 46 e0          	mov    %rax,-0x20(%r14)
          mailboxes[b].higher = &data[1];
    29d2:	49 89 76 e8          	mov    %rsi,-0x18(%r14)
          data[0].messages = messages;
    29d6:	48 89 28             	mov    %rbp,(%rax)
          data[1].messages = messages2;
    29d9:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    29dd:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    29e1:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    29e5:	4d 39 e6             	cmp    %r12,%r14
    29e8:	75 a1                	jne    298b <main+0x39b>
        char *message = malloc(sizeof(char) * 256);
    29ea:	be 01 00 00 00       	mov    $0x1,%esi
    29ef:	bf 00 01 00 00       	mov    $0x100,%edi
    29f4:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    29f8:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    29fd:	e8 9e f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a02:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a07:	49 89 c4             	mov    %rax,%r12
        struct Message *messaged = malloc(sizeof(struct Message));
    2a0a:	e8 01 fa ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a0f:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    2a14:	4c 89 e7             	mov    %r12,%rdi
    2a17:	41 89 d9             	mov    %ebx,%r9d
    2a1a:	ba 00 01 00 00       	mov    $0x100,%edx
    2a1f:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2a24:	be 01 00 00 00       	mov    $0x1,%esi
    2a29:	31 c0                	xor    %eax,%eax
    2a2b:	48 8d 0d 8e 4b 00 00 	lea    0x4b8e(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a32:	e8 e9 fa ff ff       	call   2520 <__sprintf_chk@plt>
        messaged->message = message;
    2a37:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
        messaged->thread_index = thread_data[x].thread_index;
    2a3c:	49 63 45 00          	movslq 0x0(%r13),%rax
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a40:	8d 4b 01             	lea    0x1(%rbx),%ecx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a43:	be 20 00 00 00       	mov    $0x20,%esi
    2a48:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a4d:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
        messaged->message = message;
    2a51:	4d 89 22             	mov    %r12,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a54:	4d 8b 65 58          	mov    0x58(%r13),%r12
        messaged->task_index = y;
    2a58:	49 89 6a 10          	mov    %rbp,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a5c:	4b 8d 2c 3c          	lea    (%r12,%r15,1),%rbp
        messaged->thread_index = thread_data[x].thread_index;
    2a60:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a64:	89 8d 88 01 00 00    	mov    %ecx,0x188(%rbp)
        thread_data[x].tasks[y].message = messaged;
    2a6a:	4c 89 95 80 01 00 00 	mov    %r10,0x180(%rbp)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a71:	48 c7 85 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%rbp)
        messaged->thread_index = thread_data[x].thread_index;
    2a7c:	89 44 24 18          	mov    %eax,0x18(%rsp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a80:	e8 1b f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a85:	8b 54 24 18          	mov    0x18(%rsp),%edx
        if (y == barrier_count - 1) {
    2a89:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2a8c:	89 5d 00             	mov    %ebx,0x0(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a8f:	48 89 85 48 01 00 00 	mov    %rax,0x148(%rbp)
        if (y == barrier_count - 1) {
    2a96:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
        thread_data[x].tasks[y].available = 1;
    2a9a:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2aa4:	48 89 85 38 01 00 00 	mov    %rax,0x138(%rbp)
        thread_data[x].tasks[y].sending = 1;
    2aab:	48 b8 01 00 00 00 0c 00 00 00 	movabs $0xc00000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2ab5:	48 c7 85 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%rbp)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2ac0:	89 95 30 01 00 00    	mov    %edx,0x130(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2ac6:	4c 89 ad 28 01 00 00 	mov    %r13,0x128(%rbp)
        thread_data[x].tasks[y].arrived = 0;
    2acd:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        thread_data[x].tasks[y].thread_count = 2;
    2ad7:	c7 85 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%rbp)
        thread_data[x].tasks[y].sending = 1;
    2ae1:	48 89 85 78 01 00 00 	mov    %rax,0x178(%rbp)
        if (y == barrier_count - 1) {
    2ae8:	0f 84 29 0b 00 00    	je     3617 <main+0x1027>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2aee:	8b 54 24 08          	mov    0x8(%rsp),%edx
    2af2:	39 d3                	cmp    %edx,%ebx
    2af4:	75 6a                	jne    2b60 <main+0x570>
    2af6:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    2afa:	85 db                	test   %ebx,%ebx
    2afc:	7f 62                	jg     2b60 <main+0x570>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2afe:	bf 01 00 00 00       	mov    $0x1,%edi
    2b03:	48 8d 35 de 4a 00 00 	lea    0x4ade(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2b0a:	31 c0                	xor    %eax,%eax
    2b0c:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
    2b10:	e8 3b f9 ff ff       	call   2450 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b15:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    2b1a:	48 63 c3             	movslq %ebx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b1d:	4d 8b 65 58          	mov    0x58(%r13),%r12
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b21:	48 89 c7             	mov    %rax,%rdi
    2b24:	48 c1 e0 04          	shl    $0x4,%rax
    2b28:	48 01 c8             	add    %rcx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b2b:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b2f:	49 89 85 c0 00 00 00 	mov    %rax,0xc0(%r13)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b36:	48 8d 05 f3 31 00 00 	lea    0x31f3(%rip),%rax        # 5d30 <barriered_work_ingest>
    2b3d:	4b 89 84 3c 18 01 00 00 	mov    %rax,0x118(%r12,%r15,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b45:	8d 47 01             	lea    0x1(%rdi),%eax
    2b48:	89 44 24 20          	mov    %eax,0x20(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b4c:	83 f9 03             	cmp    $0x3,%ecx
    2b4f:	74 22                	je     2b73 <main+0x583>
    2b51:	bb 01 00 00 00       	mov    $0x1,%ebx
    2b56:	e9 ed fd ff ff       	jmp    2948 <main+0x358>
    2b5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            thread_data[x].tasks[y].run = barriered_work; 
    2b60:	48 8d 05 b9 2c 00 00 	lea    0x2cb9(%rip),%rax        # 5820 <barriered_work>
    2b67:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b6e:	83 f9 03             	cmp    $0x3,%ecx
    2b71:	75 de                	jne    2b51 <main+0x561>
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b73:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b7d:	66 0f 6f 64 24 30    	movdqa 0x30(%rsp),%xmm4
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2b83:	41 c7 84 24 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r12)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b8f:	49 89 84 24 34 05 00 00 	mov    %rax,0x534(%r12)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b97:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2b9c:	41 c7 84 24 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%r12)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2ba8:	41 8b 45 00          	mov    0x0(%r13),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2bac:	4d 89 ac 24 28 05 00 00 	mov    %r13,0x528(%r12)
  for (int x = 0 ; x < total_threads ; x++) {
    2bb4:	49 81 c5 40 01 00 00 	add    $0x140,%r13
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bbb:	41 89 84 24 30 05 00 00 	mov    %eax,0x530(%r12)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2bc3:	41 c7 84 24 7c 05 00 00 0c 00 00 00 	movl   $0xc,0x57c(%r12)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2bcf:	41 c7 84 24 3c 05 00 00 03 00 00 00 	movl   $0x3,0x53c(%r12)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2bdb:	41 0f 11 a4 24 18 05 00 00 	movups %xmm4,0x518(%r12)
  for (int x = 0 ; x < total_threads ; x++) {
    2be4:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    2be9:	41 83 ff 0f          	cmp    $0xf,%r15d
    2bed:	0f 85 cd fb ff ff    	jne    27c0 <main+0x1d0>
    2bf3:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    2bf8:	ba 0d 00 00 00       	mov    $0xd,%edx
    2bfd:	48 8d 35 14 47 00 00 	lea    0x4714(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2c04:	31 c0                	xor    %eax,%eax
    2c06:	bf 01 00 00 00       	mov    $0x1,%edi
    2c0b:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    2c10:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2c15:	e8 36 f8 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c1a:	be 08 00 00 00       	mov    $0x8,%esi
    2c1f:	bf 02 00 00 00       	mov    $0x2,%edi
    2c24:	e8 77 f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2c29:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c2e:	bf 0f 00 00 00       	mov    $0xf,%edi
    my_thread_data[0] = &thread_data[x]; 
    2c33:	4d 8d ba 40 10 00 00 	lea    0x1040(%r10),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c3a:	4d 8d b2 80 02 00 00 	lea    0x280(%r10),%r14
    thread_data[x].threads = my_thread_data;
    2c41:	49 89 82 80 10 00 00 	mov    %rax,0x1080(%r10)
    my_thread_data[0] = &thread_data[x]; 
    2c48:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c4b:	49 8d 8a c0 03 00 00 	lea    0x3c0(%r10),%rcx
    2c52:	49 8d 92 40 06 00 00 	lea    0x640(%r10),%rdx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c59:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c5d:	49 8b 42 58          	mov    0x58(%r10),%rax
    2c61:	4d 8d 9a c0 08 00 00 	lea    0x8c0(%r10),%r11
    2c68:	4d 8d 8a 00 0a 00 00 	lea    0xa00(%r10),%r9
    2c6f:	49 8d b2 00 05 00 00 	lea    0x500(%r10),%rsi
    2c76:	49 8d 9a 80 07 00 00 	lea    0x780(%r10),%rbx
    thread_data[x].thread_count = 2;
    2c7d:	41 c7 82 88 10 00 00 02 00 00 00 	movl   $0x2,0x1088(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2c88:	48 89 4c 24 58       	mov    %rcx,0x58(%rsp)
    2c8d:	4d 8d 82 40 0b 00 00 	lea    0xb40(%r10),%r8
    2c94:	4d 8d aa 80 0c 00 00 	lea    0xc80(%r10),%r13
    2c9b:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    2ca0:	4d 8d a2 c0 0d 00 00 	lea    0xdc0(%r10),%r12
    thread_data[x].thread_index = 0;
    2ca7:	41 c7 82 40 10 00 00 00 00 00 00 	movl   $0x0,0x1040(%r10)
    thread_data[x].task_count = total_barrier_count;
    2cb2:	41 c7 82 a0 10 00 00 03 00 00 00 	movl   $0x3,0x10a0(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2cbd:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cc7:	49 8d 82 40 01 00 00 	lea    0x140(%r10),%rax
    2cce:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2cd3:	49 8b 82 98 01 00 00 	mov    0x198(%r10),%rax
    2cda:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    2cdf:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2ce9:	49 8b 82 d8 02 00 00 	mov    0x2d8(%r10),%rax
    2cf0:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2cf5:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cff:	49 8b 82 18 04 00 00 	mov    0x418(%r10),%rax
    my_thread_data[0] = &thread_data[x]; 
    2d06:	4c 89 7c 24 70       	mov    %r15,0x70(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d0b:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d15:	49 8b 82 58 05 00 00 	mov    0x558(%r10),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2d1c:	4c 89 74 24 78       	mov    %r14,0x78(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d21:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d2b:	49 8b 82 98 06 00 00 	mov    0x698(%r10),%rax
    2d32:	48 89 74 24 50       	mov    %rsi,0x50(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d37:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2d3c:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d46:	49 8b 82 d8 07 00 00 	mov    0x7d8(%r10),%rax
    2d4d:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    2d52:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d5c:	49 8b 82 18 09 00 00 	mov    0x918(%r10),%rax
    2d63:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d6d:	49 8b 82 58 0a 00 00 	mov    0xa58(%r10),%rax
    2d74:	4c 89 44 24 30       	mov    %r8,0x30(%rsp)
    2d79:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d83:	49 8b 82 98 0b 00 00 	mov    0xb98(%r10),%rax
    2d8a:	4c 89 94 24 80 00 00 00 	mov    %r10,0x80(%rsp)
    2d92:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d9c:	49 8b 82 d8 0c 00 00 	mov    0xcd8(%r10),%rax
    2da3:	4c 89 6c 24 20       	mov    %r13,0x20(%rsp)
    2da8:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2db2:	49 8b 82 18 0e 00 00 	mov    0xe18(%r10),%rax
    2db9:	4c 89 64 24 10       	mov    %r12,0x10(%rsp)
    2dbe:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dc8:	e8 d3 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dcd:	be 38 00 00 00       	mov    $0x38,%esi
    2dd2:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dd7:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dda:	e8 c1 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ddf:	be 38 00 00 00       	mov    $0x38,%esi
    2de4:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2de9:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dec:	e8 af f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2df1:	be 38 00 00 00       	mov    $0x38,%esi
    2df6:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dfb:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e03:	e8 98 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e08:	be 08 00 00 00       	mov    $0x8,%esi
    2e0d:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e12:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e1a:	e8 81 f5 ff ff       	call   23a0 <calloc@plt>
  thread_data[thread_count].type = TIMER;
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2e1f:	be 08 00 00 00       	mov    $0x8,%esi
    2e24:	bf 0f 00 00 00       	mov    $0xf,%edi
  thread_data[thread_count].type = TIMER;
    2e29:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e31:	49 89 c5             	mov    %rax,%r13
  thread_data[thread_count].task_count = total_barrier_count;
    2e34:	48 8b 05 0d 4c 00 00 	mov    0x4c0d(%rip),%rax        # 7a48 <_IO_stdin_used+0xa48>
  thread_data[thread_count].type = TIMER;
    2e3b:	41 c7 82 08 0f 00 00 00 00 00 00 	movl   $0x0,0xf08(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2e46:	49 89 82 60 0f 00 00 	mov    %rax,0xf60(%r10)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2e4d:	e8 4e f5 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2e52:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    2e57:	48 8b 4c 24 58       	mov    0x58(%rsp),%rcx
    2e5c:	48 8b 74 24 50       	mov    0x50(%rsp),%rsi
    2e61:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    2e66:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2e6a:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    2e6f:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2e74:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2e78:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    2e7d:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
    2e85:	48 89 48 18          	mov    %rcx,0x18(%rax)
    2e89:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
    2e8e:	48 89 70 20          	mov    %rsi,0x20(%rax)
    2e92:	48 8d 35 8e 44 00 00 	lea    0x448e(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2e99:	48 89 78 30          	mov    %rdi,0x30(%rax)
    2e9d:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    2ea2:	4d 8d b2 00 0f 00 00 	lea    0xf00(%r10),%r14
    2ea9:	4c 89 10             	mov    %r10,(%rax)
    2eac:	48 89 78 50          	mov    %rdi,0x50(%rax)
    2eb0:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    2eb5:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2eb9:	ba 0c 00 00 00       	mov    $0xc,%edx
    2ebe:	48 89 78 58          	mov    %rdi,0x58(%rax)
    2ec2:	49 8d ba 80 11 00 00 	lea    0x1180(%r10),%rdi
    2ec9:	4c 89 58 38          	mov    %r11,0x38(%rax)
    2ecd:	4c 89 48 40          	mov    %r9,0x40(%rax)
    2ed1:	4c 89 40 48          	mov    %r8,0x48(%rax)
    2ed5:	4c 89 70 60          	mov    %r14,0x60(%rax)
    2ed9:	4c 89 78 68          	mov    %r15,0x68(%rax)
    2edd:	4c 8d 3d 6c 09 00 00 	lea    0x96c(%rip),%r15        # 3850 <barriered_thread>
    2ee4:	48 89 78 70          	mov    %rdi,0x70(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2ee8:	49 89 82 40 0f 00 00 	mov    %rax,0xf40(%r10)
    2eef:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2ef1:	41 c7 82 48 0f 00 00 0c 00 00 00 	movl   $0xc,0xf48(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2efc:	41 c7 82 50 0f 00 00 02 00 00 00 	movl   $0x2,0xf50(%r10)
  thread_data[thread_count].thread_index = 0;
    2f07:	41 c7 82 00 0f 00 00 00 00 00 00 	movl   $0x0,0xf00(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2f12:	48 89 bc 24 80 00 00 00 	mov    %rdi,0x80(%rsp)
    2f1a:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].thread_index = 0;
    2f1f:	4c 89 94 24 98 00 00 00 	mov    %r10,0x98(%rsp)
    2f27:	e8 24 f5 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2f2c:	48 8d b3 a0 02 00 00 	lea    0x2a0(%rbx),%rsi
    2f33:	49 8d 7d 60          	lea    0x60(%r13),%rdi
    2f37:	4c 89 f1             	mov    %r14,%rcx
    2f3a:	48 8d 15 7f 0c 00 00 	lea    0xc7f(%rip),%rdx        # 3bc0 <timer_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    2f41:	45 31 f6             	xor    %r14d,%r14d
    2f44:	4c 89 eb             	mov    %r13,%rbx
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2f47:	e8 24 f5 ff ff       	call   2470 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2f4c:	44 89 f0             	mov    %r14d,%eax
    2f4f:	4d 89 ee             	mov    %r13,%r14
    2f52:	41 89 c5             	mov    %eax,%r13d
    thread_data[x].type = WORKER;
    2f55:	c7 45 08 01 00 00 00 	movl   $0x1,0x8(%rbp)
    2f5c:	44 89 ea             	mov    %r13d,%edx
    2f5f:	bf 01 00 00 00       	mov    $0x1,%edi
    2f64:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2f66:	c7 45 64 01 00 00 00 	movl   $0x1,0x64(%rbp)
    2f6d:	48 8d 35 94 46 00 00 	lea    0x4694(%rip),%rsi        # 7608 <_IO_stdin_used+0x608>
  for (int x = 0 ; x < thread_count ; x++) {
    2f74:	41 83 c5 01          	add    $0x1,%r13d
    2f78:	e8 d3 f4 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2f7d:	48 89 e9             	mov    %rbp,%rcx
    2f80:	4c 89 e6             	mov    %r12,%rsi
    2f83:	48 89 df             	mov    %rbx,%rdi
    2f86:	4c 89 fa             	mov    %r15,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2f89:	48 81 c5 40 01 00 00 	add    $0x140,%rbp
    2f90:	48 83 c3 08          	add    $0x8,%rbx
    2f94:	49 83 c4 38          	add    $0x38,%r12
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2f98:	e8 d3 f4 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2f9d:	48 8b 55 e0          	mov    -0x20(%rbp),%rdx
    2fa1:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    2fa5:	be 08 00 00 00       	mov    $0x8,%esi
    2faa:	e8 31 f3 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2faf:	41 83 fd 0c          	cmp    $0xc,%r13d
    2fb3:	75 a0                	jne    2f55 <main+0x965>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2fb5:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2fbd:	48 8b 1d 8c 4a 00 00 	mov    0x4a8c(%rip),%rbx        # 7a50 <_IO_stdin_used+0xa50>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2fc4:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    2fc9:	4d 89 f5             	mov    %r14,%r13
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2fcc:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    2fd1:	49 89 9a a0 10 00 00 	mov    %rbx,0x10a0(%r10)
    thread_data[x].type = IO;
    2fd8:	41 c7 82 48 10 00 00 02 00 00 00 	movl   $0x2,0x1048(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2fe3:	e8 b8 f3 ff ff       	call   23a0 <calloc@plt>
    2fe8:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2ff0:	be 00 08 00 00       	mov    $0x800,%esi
    2ff5:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ff7:	49 89 82 08 11 00 00 	mov    %rax,0x1108(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2ffe:	e8 ad f4 ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3003:	be 08 00 00 00       	mov    $0x8,%esi
    3008:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    300d:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    3015:	41 89 82 10 11 00 00 	mov    %eax,0x1110(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    301c:	e8 7f f3 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3021:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    3026:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    302b:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    3033:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    3038:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    303d:	4c 8b 74 24 78       	mov    0x78(%rsp),%r14
    3042:	4c 89 58 48          	mov    %r11,0x48(%rax)
    3046:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    304b:	4c 8b 7c 24 60       	mov    0x60(%rsp),%r15
    3050:	4c 89 48 50          	mov    %r9,0x50(%rax)
    3054:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    3059:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    305e:	4c 89 40 58          	mov    %r8,0x58(%rax)
    3062:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3067:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    306c:	4c 89 10             	mov    %r10,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    306f:	49 89 82 80 10 00 00 	mov    %rax,0x1080(%r10)
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3076:	41 c7 82 88 10 00 00 0c 00 00 00 	movl   $0xc,0x1088(%r10)
    thread_data[x].thread_index = x;
    3081:	41 c7 82 40 10 00 00 0d 00 00 00 	movl   $0xd,0x1040(%r10)
      my_thread_data[n] = &thread_data[n]; 
    308c:	4c 89 70 10          	mov    %r14,0x10(%rax)
    3090:	48 89 68 18          	mov    %rbp,0x18(%rax)
    3094:	4c 89 60 20          	mov    %r12,0x20(%rax)
    3098:	48 89 78 28          	mov    %rdi,0x28(%rax)
    309c:	bf 01 00 00 00       	mov    $0x1,%edi
    30a1:	48 89 48 30          	mov    %rcx,0x30(%rax)
    30a5:	48 89 70 38          	mov    %rsi,0x38(%rax)
    30a9:	48 8d 35 95 42 00 00 	lea    0x4295(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    30b0:	48 89 50 40          	mov    %rdx,0x40(%rax)
    30b4:	ba 0d 00 00 00       	mov    $0xd,%edx
    30b9:	4c 89 78 08          	mov    %r15,0x8(%rax)
    30bd:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    30bf:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    30c4:	e8 87 f3 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    30c9:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    30ce:	49 8d 7d 68          	lea    0x68(%r13),%rdi
    30d2:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    30da:	48 8d 15 5f 1d 00 00 	lea    0x1d5f(%rip),%rdx        # 4e40 <io_thread>
    30e1:	48 05 d8 02 00 00    	add    $0x2d8,%rax
    30e7:	48 89 c6             	mov    %rax,%rsi
    30ea:	e8 81 f3 ff ff       	call   2470 <pthread_create@plt>
    30ef:	ba 0e 00 00 00       	mov    $0xe,%edx
    30f4:	48 8d 35 61 42 00 00 	lea    0x4261(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    30fb:	31 c0                	xor    %eax,%eax
    30fd:	bf 01 00 00 00       	mov    $0x1,%edi
    3102:	e8 49 f3 ff ff       	call   2450 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    3107:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    310c:	48 8b 44 24 48       	mov    0x48(%rsp),%rax

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3111:	be 08 00 00 00       	mov    $0x8,%esi
    3116:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x].task_count = 0;
    311b:	49 89 9a e0 11 00 00 	mov    %rbx,0x11e0(%r10)
    3122:	31 db                	xor    %ebx,%ebx
    thread_data[x].type = EXTERNAL;
    3124:	41 c7 82 88 11 00 00 03 00 00 00 	movl   $0x3,0x1188(%r10)
    thread_data[x].buffers = &buffers[buffer_index];
    312f:	49 89 82 40 12 00 00 	mov    %rax,0x1240(%r10)
    3136:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    313b:	e8 60 f2 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3140:	4c 8b 54 24 48       	mov    0x48(%rsp),%r10
    3145:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    314a:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    314f:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3154:	4c 89 70 10          	mov    %r14,0x10(%rax)
    3158:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    315d:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    3162:	4c 89 10             	mov    %r10,(%rax)
    3165:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    316a:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    316f:	48 89 68 18          	mov    %rbp,0x18(%rax)
    3173:	48 8d 2d 1d 42 00 00 	lea    0x421d(%rip),%rbp        # 7397 <_IO_stdin_used+0x397>
    317a:	4c 89 60 20          	mov    %r12,0x20(%rax)
    317e:	4c 8d a4 24 a0 00 00 00 	lea    0xa0(%rsp),%r12
    3186:	48 89 78 28          	mov    %rdi,0x28(%rax)
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    318a:	49 8d 7d 70          	lea    0x70(%r13),%rdi
      my_thread_data[n] = &thread_data[n]; 
    318e:	48 89 48 30          	mov    %rcx,0x30(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3192:	48 8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%rcx
      my_thread_data[n] = &thread_data[n]; 
    319a:	48 89 70 38          	mov    %rsi,0x38(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    319e:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    31a6:	48 89 50 40          	mov    %rdx,0x40(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31aa:	48 8d 15 4f 09 00 00 	lea    0x94f(%rip),%rdx        # 3b00 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    31b1:	4c 89 58 48          	mov    %r11,0x48(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31b5:	48 81 c6 10 03 00 00 	add    $0x310,%rsi
      my_thread_data[n] = &thread_data[n]; 
    31bc:	4c 89 48 50          	mov    %r9,0x50(%rax)
    31c0:	4c 89 40 58          	mov    %r8,0x58(%rax)
    thread_data[x].threads = my_thread_data;
    31c4:	49 89 82 c0 11 00 00 	mov    %rax,0x11c0(%r10)
      my_thread_data[n] = &thread_data[n]; 
    31cb:	4c 89 78 08          	mov    %r15,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    31cf:	48 8b 05 82 48 00 00 	mov    0x4882(%rip),%rax        # 7a58 <_IO_stdin_used+0xa58>
    thread_data[x].thread_index = x;
    31d6:	41 c7 82 80 11 00 00 0e 00 00 00 	movl   $0xe,0x1180(%r10)
    thread_data[x].thread_count = thread_count;
    31e1:	49 89 82 c8 11 00 00 	mov    %rax,0x11c8(%r10)
    thread_data[x].thread_index = x;
    31e8:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31ed:	e8 7e f2 ff ff       	call   2470 <pthread_create@plt>
    31f2:	48 8d 3d 80 41 00 00 	lea    0x4180(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    31f9:	e8 f2 f0 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    31fe:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    3203:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    void * result; 
    pthread_join(thread[x], &result);
    3208:	49 8b 7c dd 00       	mov    0x0(%r13,%rbx,8),%rdi
    320d:	4c 89 e6             	mov    %r12,%rsi
    3210:	e8 db f2 ff ff       	call   24f0 <pthread_join@plt>
    3215:	89 da                	mov    %ebx,%edx
    3217:	48 89 ee             	mov    %rbp,%rsi
    321a:	bf 01 00 00 00       	mov    $0x1,%edi
    321f:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3221:	48 83 c3 01          	add    $0x1,%rbx
    3225:	e8 26 f2 ff ff       	call   2450 <__printf_chk@plt>
    322a:	48 83 fb 0f          	cmp    $0xf,%rbx
    322e:	75 d8                	jne    3208 <main+0xc18>
    3230:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    3235:	4d 89 f2             	mov    %r14,%r10
    3238:	4d 8d 6e 58          	lea    0x58(%r14),%r13
    printf("Finished thread %d\n", x);
  }
  long total = 0;
    323c:	45 31 f6             	xor    %r14d,%r14d
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    323f:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3247:	4d 89 ef             	mov    %r13,%r15
  long received = 0;
    324a:	31 db                	xor    %ebx,%ebx
  long sents = 0;
    324c:	31 ed                	xor    %ebp,%ebp
    324e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  long ingests = 0;
    3253:	45 31 c9             	xor    %r9d,%r9d
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3256:	4d 89 f5             	mov    %r14,%r13
    3259:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    if (x % 2 == 1) {
    325e:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    3262:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    3267:	89 f8                	mov    %edi,%eax
    3269:	41 89 fc             	mov    %edi,%r12d
      other = (x + 1) % total_threads;
    326c:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
    326f:	83 e0 01             	and    $0x1,%eax
      other = abs(x - 1) % total_threads;
    3272:	41 83 ec 01          	sub    $0x1,%r12d
      other = (x + 1) % total_threads;
    3276:	89 7c 24 10          	mov    %edi,0x10(%rsp)
      other = abs(x - 1) % total_threads;
    327a:	85 c0                	test   %eax,%eax
    327c:	44 0f 44 e7          	cmove  %edi,%r12d
    3280:	bf 0a 00 00 00       	mov    $0xa,%edi
    3285:	e8 46 f0 ff ff       	call   22d0 <putchar@plt>
    328a:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    328f:	bf 01 00 00 00       	mov    $0x1,%edi
    3294:	48 8d 35 10 41 00 00 	lea    0x4110(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    329b:	48 8b 10             	mov    (%rax),%rdx
    329e:	31 c0                	xor    %eax,%eax
    32a0:	e8 ab f1 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    32a5:	49 63 57 08          	movslq 0x8(%r15),%rdx
    32a9:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    32ae:	85 d2                	test   %edx,%edx
    32b0:	0f 8e e9 03 00 00    	jle    369f <main+0x10af>
    32b6:	49 8b 07             	mov    (%r15),%rax
    32b9:	48 c1 e2 09          	shl    $0x9,%rdx
    32bd:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    long v = 0;
    32c1:	31 d2                	xor    %edx,%edx
    32c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      v += thread_data[me].tasks[n].v;
    32c8:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    32cf:	48 05 00 02 00 00    	add    $0x200,%rax
    32d5:	48 39 f0             	cmp    %rsi,%rax
    32d8:	75 ee                	jne    32c8 <main+0xcd8>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    32da:	4d 63 e4             	movslq %r12d,%r12
    32dd:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    32e2:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    32e6:	48 c1 e0 06          	shl    $0x6,%rax
    32ea:	48 01 f8             	add    %rdi,%rax
    32ed:	48 63 70 60          	movslq 0x60(%rax),%rsi
    32f1:	85 f6                	test   %esi,%esi
    32f3:	7e 1d                	jle    3312 <main+0xd22>
    32f5:	48 8b 40 58          	mov    0x58(%rax),%rax
    32f9:	48 c1 e6 09          	shl    $0x9,%rsi
    32fd:	48 01 c6             	add    %rax,%rsi
      v += thread_data[other].tasks[n].v;
    3300:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3307:	48 05 00 02 00 00    	add    $0x200,%rax
    330d:	48 39 f0             	cmp    %rsi,%rax
    3310:	75 ee                	jne    3300 <main+0xd10>
    3312:	48 8d 35 a7 40 00 00 	lea    0x40a7(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    3319:	bf 01 00 00 00       	mov    $0x1,%edi
    331e:	31 c0                	xor    %eax,%eax
    3320:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    3325:	e8 26 f1 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    332a:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    332f:	bf 01 00 00 00       	mov    $0x1,%edi
    3334:	48 8b 30             	mov    (%rax),%rsi
    3337:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3341:	48 f7 ee             	imul   %rsi
    3344:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3348:	31 c0                	xor    %eax,%eax
    334a:	48 d1 fa             	sar    %rdx
    334d:	48 29 f2             	sub    %rsi,%rdx
    3350:	48 8d 35 d9 42 00 00 	lea    0x42d9(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    3357:	e8 f4 f0 ff ff       	call   2450 <__printf_chk@plt>
    335c:	bf 0a 00 00 00       	mov    $0xa,%edi
    3361:	e8 6a ef ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3366:	49 63 47 08          	movslq 0x8(%r15),%rax
    336a:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    336f:	85 c0                	test   %eax,%eax
    3371:	0f 8e cd 00 00 00    	jle    3444 <main+0xe54>
    3377:	49 8b 17             	mov    (%r15),%rdx
    337a:	48 c1 e0 09          	shl    $0x9,%rax
    337e:	48 8d 34 10          	lea    (%rax,%rdx,1),%rsi
    3382:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3388:	48 8b 82 68 01 00 00 	mov    0x168(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    338f:	4c 03 aa 08 01 00 00 	add    0x108(%rdx),%r13
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3396:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
      ingests += thread_data[x].tasks[n].ingest_count;
    339d:	4c 03 b2 60 ff ff ff 	add    -0xa0(%rdx),%r14
      sends += thread_data[x].tasks[n].sends;
    33a4:	4c 03 8a 70 ff ff ff 	add    -0x90(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33ab:	48 03 68 10          	add    0x10(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33af:	48 03 58 18          	add    0x18(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33b3:	48 03 68 30          	add    0x30(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33b7:	48 03 58 38          	add    0x38(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33bb:	48 03 68 50          	add    0x50(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33bf:	48 03 58 58          	add    0x58(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33c3:	48 03 68 70          	add    0x70(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33c7:	48 03 58 78          	add    0x78(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33cb:	48 03 a8 90 00 00 00 	add    0x90(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33d2:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33d9:	48 03 a8 b0 00 00 00 	add    0xb0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33e0:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33e7:	48 03 a8 d0 00 00 00 	add    0xd0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33ee:	48 03 98 d8 00 00 00 	add    0xd8(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33f5:	48 03 a8 f0 00 00 00 	add    0xf0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33fc:	48 03 98 f8 00 00 00 	add    0xf8(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3403:	48 03 a8 10 01 00 00 	add    0x110(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    340a:	48 03 98 18 01 00 00 	add    0x118(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3411:	48 03 a8 30 01 00 00 	add    0x130(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3418:	48 03 98 38 01 00 00 	add    0x138(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    341f:	48 03 a8 50 01 00 00 	add    0x150(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3426:	48 03 98 58 01 00 00 	add    0x158(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    342d:	48 03 a8 70 01 00 00 	add    0x170(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3434:	48 03 98 78 01 00 00 	add    0x178(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    343b:	48 39 f2             	cmp    %rsi,%rdx
    343e:	0f 85 44 ff ff ff    	jne    3388 <main+0xd98>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3444:	45 31 e4             	xor    %r12d,%r12d
    3447:	49 83 bf b8 00 00 00 00 	cmpq   $0x0,0xb8(%r15)
    344f:	7e 7b                	jle    34cc <main+0xedc>
    3451:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    3456:	4c 89 fb             	mov    %r15,%rbx
    3459:	4d 89 e7             	mov    %r12,%r15
    345c:	4d 89 cc             	mov    %r9,%r12
    345f:	90                   	nop
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3460:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    3467:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    346b:	48 83 ec 08          	sub    $0x8,%rsp
    346f:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3474:	49 83 c7 01          	add    $0x1,%r15
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3478:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    347c:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3486:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    348a:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    348e:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3491:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3495:	4c 2b 01             	sub    (%rcx),%r8
    3498:	31 c0                	xor    %eax,%eax
    349a:	8b 49 20             	mov    0x20(%rcx),%ecx
    349d:	56                   	push   %rsi
    349e:	48 8d 35 ab 41 00 00 	lea    0x41ab(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    34a5:	48 c1 ea 12          	shr    $0x12,%rdx
    34a9:	49 89 d1             	mov    %rdx,%r9
    34ac:	ba 02 00 00 00       	mov    $0x2,%edx
    34b1:	e8 9a ef ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    34b6:	58                   	pop    %rax
    34b7:	5a                   	pop    %rdx
    34b8:	4c 39 bb b8 00 00 00 	cmp    %r15,0xb8(%rbx)
    34bf:	7f 9f                	jg     3460 <main+0xe70>
    34c1:	49 89 df             	mov    %rbx,%r15
    34c4:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    34c9:	4d 89 e1             	mov    %r12,%r9
  for (int x = 0 ; x < thread_count ; x++) {
    34cc:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    34d2:	49 81 c7 40 01 00 00 	add    $0x140,%r15
    34d9:	83 7c 24 10 0c       	cmpl   $0xc,0x10(%rsp)
    34de:	0f 85 7a fd ff ff    	jne    325e <main+0xc6e>
    34e4:	4c 89 ea             	mov    %r13,%rdx
    34e7:	48 8d 35 df 3e 00 00 	lea    0x3edf(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    34ee:	31 c0                	xor    %eax,%eax
    34f0:	4d 89 cf             	mov    %r9,%r15
    34f3:	bf 01 00 00 00       	mov    $0x1,%edi
    34f8:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    34fd:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    3507:	e8 44 ef ff ff       	call   2450 <__printf_chk@plt>
    350c:	bf 0a 00 00 00       	mov    $0xa,%edi
    3511:	e8 ba ed ff ff       	call   22d0 <putchar@plt>
    3516:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    351b:	bf 01 00 00 00       	mov    $0x1,%edi
    3520:	48 8d 35 79 41 00 00 	lea    0x4179(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    3527:	48 8b 50 08          	mov    0x8(%rax),%rdx
    352b:	31 c0                	xor    %eax,%eax
    352d:	e8 1e ef ff ff       	call   2450 <__printf_chk@plt>
    3532:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3537:	bf 01 00 00 00       	mov    $0x1,%edi
    353c:	48 8d 35 85 41 00 00 	lea    0x4185(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    3543:	4c 89 c8             	mov    %r9,%rax
    3546:	49 c1 f9 3f          	sar    $0x3f,%r9
    354a:	49 f7 ec             	imul   %r12
    354d:	31 c0                	xor    %eax,%eax
    354f:	48 d1 fa             	sar    %rdx
    3552:	4c 29 ca             	sub    %r9,%rdx
    3555:	e8 f6 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    355a:	4c 89 f8             	mov    %r15,%rax
    355d:	4d 89 fb             	mov    %r15,%r11
    3560:	bf 01 00 00 00       	mov    $0x1,%edi
    3565:	49 f7 ec             	imul   %r12
    3568:	49 c1 fb 3f          	sar    $0x3f,%r11
    356c:	48 8d 35 85 41 00 00 	lea    0x4185(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    3573:	31 c0                	xor    %eax,%eax
    3575:	48 d1 fa             	sar    %rdx
    3578:	4c 29 da             	sub    %r11,%rdx
    357b:	e8 d0 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3580:	4c 89 e8             	mov    %r13,%rax
    3583:	4c 89 e9             	mov    %r13,%rcx
    3586:	bf 01 00 00 00       	mov    $0x1,%edi
    358b:	49 f7 ec             	imul   %r12
    358e:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3592:	48 8d 35 8f 41 00 00 	lea    0x418f(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    3599:	31 c0                	xor    %eax,%eax
    359b:	48 d1 fa             	sar    %rdx
    359e:	48 29 ca             	sub    %rcx,%rdx
    35a1:	e8 aa ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    35a6:	48 89 e8             	mov    %rbp,%rax
    35a9:	48 c1 fd 3f          	sar    $0x3f,%rbp
    35ad:	48 8d 35 2d 3e 00 00 	lea    0x3e2d(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    35b4:	49 f7 ec             	imul   %r12
    35b7:	bf 01 00 00 00       	mov    $0x1,%edi
    35bc:	31 c0                	xor    %eax,%eax
    35be:	48 d1 fa             	sar    %rdx
    35c1:	48 29 ea             	sub    %rbp,%rdx
    35c4:	e8 87 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    35c9:	48 89 d8             	mov    %rbx,%rax
    35cc:	48 c1 fb 3f          	sar    $0x3f,%rbx
    35d0:	48 8d 35 1b 3e 00 00 	lea    0x3e1b(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    35d7:	49 f7 ec             	imul   %r12
    35da:	bf 01 00 00 00       	mov    $0x1,%edi
    35df:	48 d1 fa             	sar    %rdx
    35e2:	48 29 da             	sub    %rbx,%rdx
    35e5:	31 c0                	xor    %eax,%eax
    35e7:	e8 64 ee ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    35ec:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    35f4:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    35fd:	0f 85 a3 00 00 00    	jne    36a6 <main+0x10b6>
    3603:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    360a:	31 c0                	xor    %eax,%eax
    360c:	5b                   	pop    %rbx
    360d:	5d                   	pop    %rbp
    360e:	41 5c                	pop    %r12
    3610:	41 5d                	pop    %r13
    3612:	41 5e                	pop    %r14
    3614:	41 5f                	pop    %r15
    3616:	c3                   	ret
          thread_data[x].tasks[y].run = barriered_work; 
    3617:	48 8d 05 02 22 00 00 	lea    0x2202(%rip),%rax        # 5820 <barriered_work>
    361e:	bb 02 00 00 00       	mov    $0x2,%ebx
    3623:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    362a:	e9 19 f3 ff ff       	jmp    2948 <main+0x358>
      other = (x + 1) % total_threads;
    362f:	b8 89 88 88 88       	mov    $0x88888889,%eax
    3634:	45 89 fe             	mov    %r15d,%r14d
      my_thread_data[0] = &thread_data[x]; 
    3637:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    363c:	4c 89 e9             	mov    %r13,%rcx
      other = (x + 1) % total_threads;
    363f:	4c 0f af f0          	imul   %rax,%r14
    3643:	89 ea                	mov    %ebp,%edx
      thread_data[x].thread_index = 0;
    3645:	41 c7 45 00 00 00 00 00 	movl   $0x0,0x0(%r13)
    364d:	48 8d 35 b5 3c 00 00 	lea    0x3cb5(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      my_thread_data[0] = &thread_data[x]; 
    3654:	4c 89 2f             	mov    %r13,(%rdi)
      other = (x + 1) % total_threads;
    3657:	49 c1 ee 23          	shr    $0x23,%r14
    365b:	44 89 f0             	mov    %r14d,%eax
    365e:	c1 e0 04             	shl    $0x4,%eax
    3661:	44 29 f0             	sub    %r14d,%eax
    3664:	45 89 fe             	mov    %r15d,%r14d
    3667:	41 29 c6             	sub    %eax,%r14d
      my_thread_data[1] = &thread_data[other]; 
    366a:	49 63 c6             	movslq %r14d,%rax
    366d:	4c 8d 04 80          	lea    (%rax,%rax,4),%r8
    3671:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    3676:	49 c1 e0 06          	shl    $0x6,%r8
    367a:	49 01 c0             	add    %rax,%r8
    367d:	31 c0                	xor    %eax,%eax
    367f:	4c 89 47 08          	mov    %r8,0x8(%rdi)
    3683:	bf 01 00 00 00       	mov    $0x1,%edi
    3688:	e8 c3 ed ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    368d:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    3692:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    3697:	49 89 c4             	mov    %rax,%r12
    369a:	e9 9d f1 ff ff       	jmp    283c <main+0x24c>
    long v = 0;
    369f:	31 d2                	xor    %edx,%edx
    36a1:	e9 34 fc ff ff       	jmp    32da <main+0xcea>
}
    36a6:	e8 85 ec ff ff       	call   2330 <__stack_chk_fail@plt>
    36ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000036b0 <_start>:
    36b0:	f3 0f 1e fa          	endbr64
    36b4:	31 ed                	xor    %ebp,%ebp
    36b6:	49 89 d1             	mov    %rdx,%r9
    36b9:	5e                   	pop    %rsi
    36ba:	48 89 e2             	mov    %rsp,%rdx
    36bd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    36c1:	50                   	push   %rax
    36c2:	54                   	push   %rsp
    36c3:	45 31 c0             	xor    %r8d,%r8d
    36c6:	31 c9                	xor    %ecx,%ecx
    36c8:	48 8d 3d 21 ef ff ff 	lea    -0x10df(%rip),%rdi        # 25f0 <main>
    36cf:	ff 15 03 69 00 00    	call   *0x6903(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    36d5:	f4                   	hlt
    36d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000036e0 <deregister_tm_clones>:
    36e0:	48 8d 3d 39 69 00 00 	lea    0x6939(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    36e7:	48 8d 05 32 69 00 00 	lea    0x6932(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    36ee:	48 39 f8             	cmp    %rdi,%rax
    36f1:	74 15                	je     3708 <deregister_tm_clones+0x28>
    36f3:	48 8b 05 e6 68 00 00 	mov    0x68e6(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    36fa:	48 85 c0             	test   %rax,%rax
    36fd:	74 09                	je     3708 <deregister_tm_clones+0x28>
    36ff:	ff e0                	jmp    *%rax
    3701:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3708:	c3                   	ret
    3709:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003710 <register_tm_clones>:
    3710:	48 8d 3d 09 69 00 00 	lea    0x6909(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3717:	48 8d 35 02 69 00 00 	lea    0x6902(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    371e:	48 29 fe             	sub    %rdi,%rsi
    3721:	48 89 f0             	mov    %rsi,%rax
    3724:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3728:	48 c1 f8 03          	sar    $0x3,%rax
    372c:	48 01 c6             	add    %rax,%rsi
    372f:	48 d1 fe             	sar    %rsi
    3732:	74 14                	je     3748 <register_tm_clones+0x38>
    3734:	48 8b 05 b5 68 00 00 	mov    0x68b5(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    373b:	48 85 c0             	test   %rax,%rax
    373e:	74 08                	je     3748 <register_tm_clones+0x38>
    3740:	ff e0                	jmp    *%rax
    3742:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3748:	c3                   	ret
    3749:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003750 <__do_global_dtors_aux>:
    3750:	f3 0f 1e fa          	endbr64
    3754:	80 3d cd 68 00 00 00 	cmpb   $0x0,0x68cd(%rip)        # a028 <completed.0>
    375b:	75 2b                	jne    3788 <__do_global_dtors_aux+0x38>
    375d:	55                   	push   %rbp
    375e:	48 83 3d 92 68 00 00 00 	cmpq   $0x0,0x6892(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3766:	48 89 e5             	mov    %rsp,%rbp
    3769:	74 0c                	je     3777 <__do_global_dtors_aux+0x27>
    376b:	48 8b 3d 96 68 00 00 	mov    0x6896(%rip),%rdi        # a008 <__dso_handle>
    3772:	e8 39 eb ff ff       	call   22b0 <__cxa_finalize@plt>
    3777:	e8 64 ff ff ff       	call   36e0 <deregister_tm_clones>
    377c:	c6 05 a5 68 00 00 01 	movb   $0x1,0x68a5(%rip)        # a028 <completed.0>
    3783:	5d                   	pop    %rbp
    3784:	c3                   	ret
    3785:	0f 1f 00             	nopl   (%rax)
    3788:	c3                   	ret
    3789:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003790 <frame_dummy>:
    3790:	f3 0f 1e fa          	endbr64
    3794:	e9 77 ff ff ff       	jmp    3710 <register_tm_clones>
    3799:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037a0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    37a0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    37a4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    37ab:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
  data->v++; // thread local
    37b2:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    37ba:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    37be:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    37c2:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    37c9:	48 85 c9             	test   %rcx,%rcx
    37cc:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    37d3:	48 0f 4f d6          	cmovg  %rsi,%rdx
    37d7:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    37db:	31 c0                	xor    %eax,%eax
    37dd:	c3                   	ret
    37de:	66 90                	xchg   %ax,%ax

00000000000037e0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    37e0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    37e4:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    37eb:	85 c9                	test   %ecx,%ecx
    37ed:	7e 4f                	jle    383e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    37ef:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    37f6:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    37fd:	48 c1 e1 09          	shl    $0x9,%rcx
    3801:	48 8b 50 40          	mov    0x40(%rax),%rdx
    3805:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3809:	48 8b 70 58          	mov    0x58(%rax),%rsi
    380d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    380f:	48 8b 52 58          	mov    0x58(%rdx),%rdx
    3813:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3818:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3820:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3828:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3833:	48 05 00 02 00 00    	add    $0x200,%rax
    3839:	48 39 c1             	cmp    %rax,%rcx
    383c:	75 da                	jne    3818 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    383e:	0f ae f8             	sfence
}
    3841:	31 c0                	xor    %eax,%eax
    3843:	c3                   	ret
    3844:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    384f:	90                   	nop

0000000000003850 <barriered_thread>:
void* barriered_thread(void *arg) {
    3850:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3854:	83 7f 64 01          	cmpl   $0x1,0x64(%rdi)
    3858:	0f 85 9b 02 00 00    	jne    3af9 <barriered_thread+0x2a9>
void* barriered_thread(void *arg) {
    385e:	41 56                	push   %r14
    3860:	41 55                	push   %r13
    3862:	49 89 fd             	mov    %rdi,%r13
    3865:	41 54                	push   %r12
    3867:	55                   	push   %rbp
    3868:	31 ed                	xor    %ebp,%ebp
    386a:	53                   	push   %rbx
    386b:	31 db                	xor    %ebx,%ebx
    386d:	0f 1f 00             	nopl   (%rax)
    if (t >= data->task_count) {
    3870:	41 8b 55 60          	mov    0x60(%r13),%edx
    3874:	39 da                	cmp    %ebx,%edx
    3876:	7f 12                	jg     388a <barriered_thread+0x3a>
      data->cycles++;
    3878:	49 83 85 18 01 00 00 01 	addq   $0x1,0x118(%r13)
    for (; t < data->task_count; t++) {
    3880:	31 db                	xor    %ebx,%ebx
    3882:	85 d2                	test   %edx,%edx
    3884:	0f 8e 56 01 00 00    	jle    39e0 <barriered_thread+0x190>
    388a:	4c 63 e3             	movslq %ebx,%r12
    388d:	49 c1 e4 09          	shl    $0x9,%r12
    3891:	eb 17                	jmp    38aa <barriered_thread+0x5a>
    3893:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3898:	83 c3 01             	add    $0x1,%ebx
    389b:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    38a2:	39 d3                	cmp    %edx,%ebx
    38a4:	0f 8d 36 01 00 00    	jge    39e0 <barriered_thread+0x190>
      if (data->tasks[t].available == 1) {
    38aa:	49 8b 45 58          	mov    0x58(%r13),%rax
    38ae:	4a 8d 34 20          	lea    (%rax,%r12,1),%rsi
    38b2:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    38b9:	75 dd                	jne    3898 <barriered_thread+0x48>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    38bb:	41 8b 7d 48          	mov    0x48(%r13),%edi
          previous = t - 1;
    38bf:	83 ea 01             	sub    $0x1,%edx
    38c2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    38c5:	85 db                	test   %ebx,%ebx
    38c7:	0f 4f d1             	cmovg  %ecx,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    38ca:	85 ff                	test   %edi,%edi
    38cc:	0f 8e 3e 01 00 00    	jle    3a10 <barriered_thread+0x1c0>
    38d2:	49 8b 45 40          	mov    0x40(%r13),%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    38d6:	48 63 ca             	movslq %edx,%rcx
    38d9:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    38dc:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    38df:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    38e6:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    38ed:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    38f1:	45 31 f6             	xor    %r14d,%r14d
    38f4:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    38f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3900:	48 8b 10             	mov    (%rax),%rdx
    3903:	4c 8b 5a 58          	mov    0x58(%rdx),%r11
    3907:	49 01 cb             	add    %rcx,%r11
    390a:	4c 89 da             	mov    %r11,%rdx
    390d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    3914:	75 04                	jne    391a <barriered_thread+0xca>
            arrived++;
    3916:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    391a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    3921:	75 04                	jne    3927 <barriered_thread+0xd7>
            prearrive++;
    3923:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3927:	48 83 c0 08          	add    $0x8,%rax
    392b:	48 39 f0             	cmp    %rsi,%rax
    392e:	75 d0                	jne    3900 <barriered_thread+0xb0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    3930:	44 39 d7             	cmp    %r10d,%edi
    3933:	0f 84 c7 00 00 00    	je     3a00 <barriered_thread+0x1b0>
    3939:	45 85 d2             	test   %r10d,%r10d
    393c:	0f 84 be 00 00 00    	je     3a00 <barriered_thread+0x1b0>
        if (arrived == 0 || arrived == data->thread_count) {
    3942:	45 85 f6             	test   %r14d,%r14d
    3945:	74 0a                	je     3951 <barriered_thread+0x101>
    3947:	45 39 75 48          	cmp    %r14d,0x48(%r13)
    394b:	0f 85 8f 00 00 00    	jne    39e0 <barriered_thread+0x190>
    3951:	49 8b 45 58          	mov    0x58(%r13),%rax
          data->tasks[t].prearrive++;
    3955:	4c 01 e0             	add    %r12,%rax
    3958:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    395f:	85 db                	test   %ebx,%ebx
    3961:	75 14                	jne    3977 <barriered_thread+0x127>
    3963:	49 8b b5 f0 00 00 00 	mov    0xf0(%r13),%rsi
    396a:	49 3b b5 f8 00 00 00 	cmp    0xf8(%r13),%rsi
    3971:	0f 8c 61 01 00 00    	jl     3ad8 <barriered_thread+0x288>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3977:	49 63 4d 00          	movslq 0x0(%r13),%rcx
    397b:	49 8b 55 40          	mov    0x40(%r13),%rdx
          data->tasks[t].available = 0;
    397f:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3989:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    398d:	48 8b 7a 58          	mov    0x58(%rdx),%rdi
    3991:	4c 01 e7             	add    %r12,%rdi
    3994:	ff 90 18 01 00 00    	call   *0x118(%rax)
          data->tasks[t].arrived++;
    399a:	49 8b 45 58          	mov    0x58(%r13),%rax
    399e:	4c 01 e0             	add    %r12,%rax
    39a1:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    39a8:	41 8b 45 60          	mov    0x60(%r13),%eax
          data->iteration_count++;
    39ac:	49 83 85 e8 00 00 00 01 	addq   $0x1,0xe8(%r13)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    39b4:	83 e8 01             	sub    $0x1,%eax
    39b7:	39 d8                	cmp    %ebx,%eax
    39b9:	0f 84 a9 00 00 00    	je     3a68 <barriered_thread+0x218>
          asm volatile ("sfence" ::: "memory");
    39bf:	0f ae f8             	sfence
          if (waiting == 0) {
    39c2:	85 ed                	test   %ebp,%ebp
    39c4:	0f 84 d6 00 00 00    	je     3aa0 <barriered_thread+0x250>
    for (; t < data->task_count; t++) {
    39ca:	41 8b 55 60          	mov    0x60(%r13),%edx
    39ce:	83 c3 01             	add    $0x1,%ebx
    39d1:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    39d8:	39 d3                	cmp    %edx,%ebx
    39da:	0f 8c ca fe ff ff    	jl     38aa <barriered_thread+0x5a>
  while (data->running == 1) {
    39e0:	41 83 7d 64 01       	cmpl   $0x1,0x64(%r13)
    39e5:	0f 84 85 fe ff ff    	je     3870 <barriered_thread+0x20>
}
    39eb:	5b                   	pop    %rbx
    39ec:	31 c0                	xor    %eax,%eax
    39ee:	5d                   	pop    %rbp
    39ef:	41 5c                	pop    %r12
    39f1:	41 5d                	pop    %r13
    39f3:	41 5e                	pop    %r14
    39f5:	c3                   	ret
    39f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
    3a00:	83 fd 01             	cmp    $0x1,%ebp
    3a03:	74 1b                	je     3a20 <barriered_thread+0x1d0>
        int arrived = 0; 
    3a05:	31 ed                	xor    %ebp,%ebp
    3a07:	e9 36 ff ff ff       	jmp    3942 <barriered_thread+0xf2>
    3a0c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    3a10:	83 fd 01             	cmp    $0x1,%ebp
    3a13:	0f 85 3c ff ff ff    	jne    3955 <barriered_thread+0x105>
        int arrived = 0; 
    3a19:	45 31 f6             	xor    %r14d,%r14d
    3a1c:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3a20:	49 8b 85 08 01 00 00 	mov    0x108(%r13),%rax
    3a27:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    3a2c:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3a2e:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3a32:	49 8b 85 00 01 00 00 	mov    0x100(%r13),%rax
    3a39:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3a3e:	e8 cd e8 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3a43:	49 8b 85 08 01 00 00 	mov    0x108(%r13),%rax
    3a4a:	48 83 c0 01          	add    $0x1,%rax
    3a4e:	48 99                	cqto
    3a50:	49 f7 bd 10 01 00 00 	idivq  0x110(%r13)
    3a57:	49 89 95 08 01 00 00 	mov    %rdx,0x108(%r13)
            waiting = 0; 
    3a5e:	e9 df fe ff ff       	jmp    3942 <barriered_thread+0xf2>
    3a63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3a68:	49 8b b5 f0 00 00 00 	mov    0xf0(%r13),%rsi
    3a6f:	49 3b b5 f8 00 00 00 	cmp    0xf8(%r13),%rsi
    3a76:	0f 8d 43 ff ff ff    	jge    39bf <barriered_thread+0x16f>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    3a7c:	48 c1 e6 04          	shl    $0x4,%rsi
    3a80:	bf 04 00 00 00       	mov    $0x4,%edi
    3a85:	49 03 b5 e0 00 00 00 	add    0xe0(%r13),%rsi
    3a8c:	e8 7f e8 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3a91:	49 83 85 f0 00 00 00 01 	addq   $0x1,0xf0(%r13)
    3a99:	e9 21 ff ff ff       	jmp    39bf <barriered_thread+0x16f>
    3a9e:	66 90                	xchg   %ax,%ax
            data->task_snapshot[data->task_timestamp_count].task = t;
    3aa0:	49 8b 85 08 01 00 00 	mov    0x108(%r13),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3aa7:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3aac:	bd 01 00 00 00       	mov    $0x1,%ebp
            data->task_snapshot[data->task_timestamp_count].task = t;
    3ab1:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3ab5:	49 8b 85 00 01 00 00 	mov    0x100(%r13),%rax
    3abc:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3ac0:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3ac3:	e8 48 e8 ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3ac8:	41 8b 55 60          	mov    0x60(%r13),%edx
    3acc:	e9 c7 fd ff ff       	jmp    3898 <barriered_thread+0x48>
    3ad1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3ad8:	48 c1 e6 04          	shl    $0x4,%rsi
    3adc:	bf 04 00 00 00       	mov    $0x4,%edi
    3ae1:	49 03 b5 d8 00 00 00 	add    0xd8(%r13),%rsi
    3ae8:	e8 23 e8 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3aed:	49 8b 45 58          	mov    0x58(%r13),%rax
    3af1:	4c 01 e0             	add    %r12,%rax
    3af4:	e9 7e fe ff ff       	jmp    3977 <barriered_thread+0x127>
}
    3af9:	31 c0                	xor    %eax,%eax
    3afb:	c3                   	ret
    3afc:	0f 1f 40 00          	nopl   0x0(%rax)

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
    3c1d:	45 8b 67 64          	mov    0x64(%r15),%r12d
    3c21:	45 85 e4             	test   %r12d,%r12d
    3c24:	0f 84 9b 00 00 00    	je     3cc5 <timer_thread+0x105>
  int n = 0;
    3c2a:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    3c2d:	45 31 e4             	xor    %r12d,%r12d
    3c30:	49 89 e5             	mov    %rsp,%r13
    y++;
    3c33:	31 db                	xor    %ebx,%ebx
    3c35:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    3c3a:	48 89 ef             	mov    %rbp,%rdi
    3c3d:	4c 89 ee             	mov    %r13,%rsi
    n++;
    3c40:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3c44:	e8 07 e7 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c49:	49 63 47 48          	movslq 0x48(%r15),%rax
    y++;
    3c4d:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c52:	85 c0                	test   %eax,%eax
    3c54:	7e 47                	jle    3c9d <timer_thread+0xdd>
    3c56:	49 8b 4f 40          	mov    0x40(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3c5a:	49 c1 e4 09          	shl    $0x9,%r12
    3c5e:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3c62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3c68:	4c 8b 11             	mov    (%rcx),%r10
    3c6b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c6d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3c71:	99                   	cltd
    3c72:	41 f7 7a 60          	idivl  0x60(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3c76:	49 8b 72 58          	mov    0x58(%r10),%rsi
    3c7a:	48 63 d2             	movslq %edx,%rdx
    3c7d:	48 c1 e2 09          	shl    $0x9,%rdx
    3c81:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3c8c:	42 c7 84 26 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c98:	49 39 c8             	cmp    %rcx,%r8
    3c9b:	75 cb                	jne    3c68 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    3c9d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3ca0:	49 8b 47 40          	mov    0x40(%r15),%rax
  while (data->running && n < times) {
    3ca4:	41 8b 57 64          	mov    0x64(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3ca8:	48 8b 00             	mov    (%rax),%rax
    y++;
    3cab:	39 78 60             	cmp    %edi,0x60(%rax)
    3cae:	0f 4e fb             	cmovle %ebx,%edi
    3cb1:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3cb4:	85 d2                	test   %edx,%edx
    3cb6:	74 0d                	je     3cc5 <timer_thread+0x105>
    3cb8:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3cbf:	0f 85 75 ff ff ff    	jne    3c3a <timer_thread+0x7a>
    3cc5:	48 8d 3d 6c 33 00 00 	lea    0x336c(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3ccc:	e8 1f e6 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3cd1:	49 63 57 4c          	movslq 0x4c(%r15),%rdx
    3cd5:	85 d2                	test   %edx,%edx
    3cd7:	7e 6b                	jle    3d44 <timer_thread+0x184>
    for (int y = 0 ; y < data->task_count ; y++) {
    3cd9:	49 63 47 60          	movslq 0x60(%r15),%rax
    3cdd:	85 c0                	test   %eax,%eax
    3cdf:	7e 63                	jle    3d44 <timer_thread+0x184>
    3ce1:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3ce5:	4d 8b 47 40          	mov    0x40(%r15),%r8
    3ce9:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3cf1:	31 ff                	xor    %edi,%edi
    3cf3:	48 89 c2             	mov    %rax,%rdx
    3cf6:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3cfa:	48 8b 40 58          	mov    0x58(%rax),%rax
    3cfe:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3d02:	f6 c6 02             	test   $0x2,%dh
    3d05:	74 15                	je     3d1c <timer_thread+0x15c>
    3d07:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3d11:	48 05 00 02 00 00    	add    $0x200,%rax
    3d17:	48 39 c6             	cmp    %rax,%rsi
    3d1a:	74 1f                	je     3d3b <timer_thread+0x17b>
      data->threads[x]->tasks[y].sending = 0;
    3d1c:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3d26:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3d2c:	c7 80 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3d36:	48 39 c6             	cmp    %rax,%rsi
    3d39:	75 e1                	jne    3d1c <timer_thread+0x15c>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d3b:	48 83 c7 08          	add    $0x8,%rdi
    3d3f:	48 39 f9             	cmp    %rdi,%rcx
    3d42:	75 b2                	jne    3cf6 <timer_thread+0x136>
  asm volatile ("mfence" ::: "memory");
    3d44:	0f ae f0             	mfence
  struct timespec drain = {
    3d47:	66 0f 6f 05 01 3c 00 00 	movdqa 0x3c01(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3d4f:	48 8d 2d 07 33 00 00 	lea    0x3307(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3d56:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d5b:	49 63 47 48          	movslq 0x48(%r15),%rax
    y++;
    3d5f:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d64:	85 c0                	test   %eax,%eax
    3d66:	7e 4c                	jle    3db4 <timer_thread+0x1f4>
    3d68:	49 8b 4f 40          	mov    0x40(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3d6c:	4d 63 c4             	movslq %r12d,%r8
    3d6f:	49 c1 e0 09          	shl    $0x9,%r8
    3d73:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3d77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3d80:	48 8b 19             	mov    (%rcx),%rbx
    3d83:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d85:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3d89:	99                   	cltd
    3d8a:	f7 7b 60             	idivl  0x60(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3d8d:	48 8b 73 58          	mov    0x58(%rbx),%rsi
    3d91:	48 63 d2             	movslq %edx,%rdx
    3d94:	48 c1 e2 09          	shl    $0x9,%rdx
    3d98:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3da3:	42 c7 84 06 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3daf:	4c 39 c9             	cmp    %r9,%rcx
    3db2:	75 cc                	jne    3d80 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    3db4:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3db7:	49 8b 47 40          	mov    0x40(%r15),%rax
    y++;
    3dbb:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3dbe:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3dc1:	39 7a 60             	cmp    %edi,0x60(%rdx)
    3dc4:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3dc8:	41 8b 7f 50          	mov    0x50(%r15),%edi
    3dcc:	85 ff                	test   %edi,%edi
    3dce:	0f 8e bc 00 00 00    	jle    3e90 <timer_thread+0x2d0>
    3dd4:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    3dd7:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3ddd:	0f 1f 00             	nopl   (%rax)
    3de0:	4a 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbx
            all_empty = 0;
    3de8:	45 31 f6             	xor    %r14d,%r14d
    3deb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3df0:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3df4:	4c 89 f0             	mov    %r14,%rax
    3df7:	48 c1 e0 09          	shl    $0x9,%rax
    3dfb:	48 03 42 58          	add    0x58(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3dff:	31 d2                	xor    %edx,%edx
    3e01:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3e08:	eb 16                	jmp    3e20 <timer_thread+0x260>
    3e0a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
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
            break;
    3e43:	41 8b 7f 50          	mov    0x50(%r15),%edi
            all_empty = 0;
    3e47:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3e4a:	49 83 c6 01          	add    $0x1,%r14
    3e4e:	44 39 f7             	cmp    %r14d,%edi
    3e51:	7e 0d                	jle    3e60 <timer_thread+0x2a0>
    3e53:	49 8b 47 40          	mov    0x40(%r15),%rax
    3e57:	eb 97                	jmp    3df0 <timer_thread+0x230>
    3e59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3e60:	49 83 c5 01          	add    $0x1,%r13
    3e64:	44 39 ef             	cmp    %r13d,%edi
    3e67:	7e 0d                	jle    3e76 <timer_thread+0x2b6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3e69:	85 ff                	test   %edi,%edi
    3e6b:	7e 09                	jle    3e76 <timer_thread+0x2b6>
    3e6d:	49 8b 47 40          	mov    0x40(%r15),%rax
    3e71:	e9 6a ff ff ff       	jmp    3de0 <timer_thread+0x220>
    if (all_empty == 1) {
    3e76:	41 83 f9 01          	cmp    $0x1,%r9d
    3e7a:	74 14                	je     3e90 <timer_thread+0x2d0>
      nanosleep(&drain , &drainrem);
    3e7c:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3e81:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3e86:	e8 c5 e4 ff ff       	call   2350 <nanosleep@plt>
    3e8b:	e9 cb fe ff ff       	jmp    3d5b <timer_thread+0x19b>
    3e90:	48 8d 3d bd 31 00 00 	lea    0x31bd(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3e97:	e8 54 e4 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3e9c:	41 8b 47 64          	mov    0x64(%r15),%eax
    3ea0:	85 c0                	test   %eax,%eax
    3ea2:	0f 84 cf 00 00 00    	je     3f77 <timer_thread+0x3b7>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ea8:	41 8b 4f 4c          	mov    0x4c(%r15),%ecx
    3eac:	85 c9                	test   %ecx,%ecx
    3eae:	7e 2d                	jle    3edd <timer_thread+0x31d>
    3eb0:	49 8b 47 40          	mov    0x40(%r15),%rax
    3eb4:	31 db                	xor    %ebx,%ebx
    3eb6:	48 8d 2d b1 31 00 00 	lea    0x31b1(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3ebd:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->running = 0;
    3ec0:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3ec4:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3ec8:	c7 42 64 00 00 00 00 	movl   $0x0,0x64(%rdx)
      if (data->threads[x]->type == IO) {
    3ecf:	0f 84 cf 00 00 00    	je     3fa4 <timer_thread+0x3e4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ed5:	48 83 c3 01          	add    $0x1,%rbx
    3ed9:	39 d9                	cmp    %ebx,%ecx
    3edb:	7f e3                	jg     3ec0 <timer_thread+0x300>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3edd:	49 63 57 48          	movslq 0x48(%r15),%rdx
    3ee1:	85 d2                	test   %edx,%edx
    3ee3:	7e 7b                	jle    3f60 <timer_thread+0x3a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3ee5:	49 63 47 60          	movslq 0x60(%r15),%rax
    3ee9:	85 c0                	test   %eax,%eax
    3eeb:	7e 73                	jle    3f60 <timer_thread+0x3a0>
    3eed:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3ef1:	4d 8b 47 40          	mov    0x40(%r15),%r8
    3ef5:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3efd:	31 c9                	xor    %ecx,%ecx
    3eff:	48 89 c6             	mov    %rax,%rsi
    3f02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3f08:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3f0c:	48 8b 40 58          	mov    0x58(%rax),%rax
    3f10:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3f14:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3f1a:	74 1c                	je     3f38 <timer_thread+0x378>
    3f1c:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3f26:	48 05 00 02 00 00    	add    $0x200,%rax
    3f2c:	48 39 d0             	cmp    %rdx,%rax
    3f2f:	74 26                	je     3f57 <timer_thread+0x397>
    3f31:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3f38:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3f42:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3f48:	c7 80 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3f52:	48 39 d0             	cmp    %rdx,%rax
    3f55:	75 e1                	jne    3f38 <timer_thread+0x378>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f57:	48 83 c1 08          	add    $0x8,%rcx
    3f5b:	48 39 f9             	cmp    %rdi,%rcx
    3f5e:	75 a8                	jne    3f08 <timer_thread+0x348>
    asm volatile ("mfence" ::: "memory");
    3f60:	0f ae f0             	mfence
    3f63:	48 8d 3d 16 31 00 00 	lea    0x3116(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3f6a:	e8 81 e3 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3f6f:	41 c7 47 64 00 00 00 00 	movl   $0x0,0x64(%r15)
    3f77:	48 8d 3d 09 31 00 00 	lea    0x3109(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3f7e:	e8 6d e3 ff ff       	call   22f0 <puts@plt>
}
    3f83:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3f88:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3f91:	75 4a                	jne    3fdd <timer_thread+0x41d>
    3f93:	48 83 c4 58          	add    $0x58,%rsp
    3f97:	31 c0                	xor    %eax,%eax
    3f99:	5b                   	pop    %rbx
    3f9a:	5d                   	pop    %rbp
    3f9b:	41 5c                	pop    %r12
    3f9d:	41 5d                	pop    %r13
    3f9f:	41 5e                	pop    %r14
    3fa1:	41 5f                	pop    %r15
    3fa3:	c3                   	ret
    3fa4:	48 89 ef             	mov    %rbp,%rdi
    3fa7:	e8 44 e3 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3fac:	49 8b 47 40          	mov    0x40(%r15),%rax
    3fb0:	be 01 00 00 00       	mov    $0x1,%esi
    3fb5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3fb9:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3fbd:	8b b8 d0 00 00 00    	mov    0xd0(%rax),%edi
    3fc3:	e8 38 e4 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3fc8:	41 8b 4f 4c          	mov    0x4c(%r15),%ecx
    3fcc:	39 d9                	cmp    %ebx,%ecx
    3fce:	0f 8e 09 ff ff ff    	jle    3edd <timer_thread+0x31d>
    3fd4:	49 8b 47 40          	mov    0x40(%r15),%rax
    3fd8:	e9 e3 fe ff ff       	jmp    3ec0 <timer_thread+0x300>
}
    3fdd:	e8 4e e3 ff ff       	call   2330 <__stack_chk_fail@plt>
    3fe2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3fed:	0f 1f 00             	nopl   (%rax)

0000000000003ff0 <strtolower>:
void strtolower(char *str) {
    3ff0:	f3 0f 1e fa          	endbr64
    3ff4:	55                   	push   %rbp
    3ff5:	53                   	push   %rbx
    3ff6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3ffa:	48 0f be 1f          	movsbq (%rdi),%rbx
    3ffe:	84 db                	test   %bl,%bl
    4000:	74 24                	je     4026 <strtolower+0x36>
    4002:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4005:	e8 06 e5 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    400a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4010:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4013:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4017:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    401a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    401d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4022:	84 db                	test   %bl,%bl
    4024:	75 ea                	jne    4010 <strtolower+0x20>
}
    4026:	48 83 c4 08          	add    $0x8,%rsp
    402a:	5b                   	pop    %rbx
    402b:	5d                   	pop    %rbp
    402c:	c3                   	ret
    402d:	0f 1f 00             	nopl   (%rax)

0000000000004030 <zh_malloc>:
void *zh_malloc(size_t size) {
    4030:	f3 0f 1e fa          	endbr64
    4034:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4038:	e8 d3 e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    403d:	48 85 c0             	test   %rax,%rax
    4040:	74 05                	je     4047 <zh_malloc+0x17>
}
    4042:	48 83 c4 08          	add    $0x8,%rsp
    4046:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4047:	48 8b 0d d2 5f 00 00 	mov    0x5fd2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    404e:	ba 28 00 00 00       	mov    $0x28,%edx
    4053:	be 01 00 00 00       	mov    $0x1,%esi
    4058:	48 8d 3d a9 33 00 00 	lea    0x33a9(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    405f:	e8 5c e4 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4064:	bf 01 00 00 00       	mov    $0x1,%edi
    4069:	e8 32 e4 ff ff       	call   24a0 <exit@plt>
    406e:	66 90                	xchg   %ax,%ax

0000000000004070 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4070:	f3 0f 1e fa          	endbr64
    4074:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4075:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    407a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    407d:	e8 de e2 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4082:	48 85 c0             	test   %rax,%rax
    4085:	74 11                	je     4098 <get_filename_ext+0x28>
    4087:	48 39 c3             	cmp    %rax,%rbx
    408a:	74 0c                	je     4098 <get_filename_ext+0x28>
    return dot + 1;
    408c:	48 83 c0 01          	add    $0x1,%rax
}
    4090:	5b                   	pop    %rbx
    4091:	c3                   	ret
    4092:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4098:	48 8d 05 30 30 00 00 	lea    0x3030(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    409f:	5b                   	pop    %rbx
    40a0:	c3                   	ret
    40a1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    40ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000040b0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    40b0:	f3 0f 1e fa          	endbr64
    40b4:	41 55                	push   %r13
    40b6:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40b9:	48 89 fe             	mov    %rdi,%rsi
    40bc:	41 54                	push   %r12
    40be:	55                   	push   %rbp
    40bf:	48 89 d5             	mov    %rdx,%rbp
    40c2:	ba 00 04 00 00       	mov    $0x400,%edx
    40c7:	53                   	push   %rbx
    40c8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    40cf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    40d8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    40e0:	31 c0                	xor    %eax,%eax
    40e2:	49 89 e4             	mov    %rsp,%r12
    40e5:	4c 89 e7             	mov    %r12,%rdi
    40e8:	e8 43 e3 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    40ed:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    40f2:	84 db                	test   %bl,%bl
    40f4:	74 24                	je     411a <send_headers+0x6a>
        *str = (char)tolower(*str);
    40f6:	e8 15 e4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    40fb:	48 8b 08             	mov    (%rax),%rcx
    40fe:	4c 89 e0             	mov    %r12,%rax
    4101:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4108:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    410b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    410f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4112:	48 0f be 18          	movsbq (%rax),%rbx
    4116:	84 db                	test   %bl,%bl
    4118:	75 ee                	jne    4108 <send_headers+0x58>
    void *buf = malloc(size);
    411a:	bf 11 00 00 00       	mov    $0x11,%edi
    411f:	e8 ec e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4124:	48 85 c0             	test   %rax,%rax
    4127:	0f 84 7e 04 00 00    	je     45ab <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    412d:	66 0f 6f 05 2b 38 00 00 	movdqa 0x382b(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    4135:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4139:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    413e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4146:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    414a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    414d:	e8 be e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4152:	48 85 c0             	test   %rax,%rax
    4155:	0f 84 50 04 00 00    	je     45ab <send_headers+0x4fb>
    415b:	66 0f 6f 05 0d 38 00 00 	movdqa 0x380d(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    4163:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4167:	4c 89 e7             	mov    %r12,%rdi
    416a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4174:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    417c:	0f 11 00             	movups %xmm0,(%rax)
    417f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4183:	be 2e 00 00 00       	mov    $0x2e,%esi
    4188:	e8 d3 e1 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    418d:	48 85 c0             	test   %rax,%rax
    4190:	0f 84 ea 02 00 00    	je     4480 <send_headers+0x3d0>
    4196:	4c 39 e0             	cmp    %r12,%rax
    4199:	0f 84 e1 02 00 00    	je     4480 <send_headers+0x3d0>
    return dot + 1;
    419f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    41a3:	48 8d 3d f3 2e 00 00 	lea    0x2ef3(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    41aa:	48 89 de             	mov    %rbx,%rsi
    41ad:	e8 fe e1 ff ff       	call   23b0 <strcmp@plt>
    41b2:	85 c0                	test   %eax,%eax
    41b4:	75 20                	jne    41d6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    41b6:	66 0f 6f 05 c2 37 00 00 	movdqa 0x37c2(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    41be:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41c6:	66 0f 6f 05 c2 37 00 00 	movdqa 0x37c2(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    41ce:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    41d6:	48 89 de             	mov    %rbx,%rsi
    41d9:	48 8d 3d c1 2e 00 00 	lea    0x2ec1(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    41e0:	e8 cb e1 ff ff       	call   23b0 <strcmp@plt>
    41e5:	85 c0                	test   %eax,%eax
    41e7:	75 20                	jne    4209 <send_headers+0x159>
    41e9:	66 0f 6f 05 8f 37 00 00 	movdqa 0x378f(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    41f1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41f9:	66 0f 6f 05 8f 37 00 00 	movdqa 0x378f(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    4201:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4209:	48 89 de             	mov    %rbx,%rsi
    420c:	48 8d 3d 93 2e 00 00 	lea    0x2e93(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    4213:	e8 98 e1 ff ff       	call   23b0 <strcmp@plt>
    4218:	85 c0                	test   %eax,%eax
    421a:	0f 84 10 02 00 00    	je     4430 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4220:	48 89 de             	mov    %rbx,%rsi
    4223:	48 8d 3d 80 2e 00 00 	lea    0x2e80(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    422a:	e8 81 e1 ff ff       	call   23b0 <strcmp@plt>
    422f:	85 c0                	test   %eax,%eax
    4231:	0f 84 a9 02 00 00    	je     44e0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4237:	48 89 de             	mov    %rbx,%rsi
    423a:	48 8d 3d 6d 2e 00 00 	lea    0x2e6d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4241:	e8 6a e1 ff ff       	call   23b0 <strcmp@plt>
    4246:	85 c0                	test   %eax,%eax
    4248:	0f 84 6a 02 00 00    	je     44b8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    424e:	48 89 de             	mov    %rbx,%rsi
    4251:	48 8d 3d 99 2e 00 00 	lea    0x2e99(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4258:	e8 53 e1 ff ff       	call   23b0 <strcmp@plt>
    425d:	85 c0                	test   %eax,%eax
    425f:	0f 84 2b 02 00 00    	je     4490 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4265:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4268:	0f 84 52 01 00 00    	je     43c0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    426e:	48 89 de             	mov    %rbx,%rsi
    4271:	48 8d 3d 3a 2e 00 00 	lea    0x2e3a(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    4278:	e8 33 e1 ff ff       	call   23b0 <strcmp@plt>
    427d:	85 c0                	test   %eax,%eax
    427f:	0f 84 ab 02 00 00    	je     4530 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4285:	48 89 de             	mov    %rbx,%rsi
    4288:	48 8d 3d 27 2e 00 00 	lea    0x2e27(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    428f:	e8 1c e1 ff ff       	call   23b0 <strcmp@plt>
    4294:	85 c0                	test   %eax,%eax
    4296:	0f 84 6c 02 00 00    	je     4508 <send_headers+0x458>
    slen = strlen(send_buffer);
    429c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    42a4:	4c 89 e7             	mov    %r12,%rdi
    42a7:	e8 74 e0 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    42ac:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    42af:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    42b2:	e8 59 e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    42b7:	48 85 c0             	test   %rax,%rax
    42ba:	0f 84 eb 02 00 00    	je     45ab <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    42c0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    42c4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    42c8:	83 fb 08             	cmp    $0x8,%ebx
    42cb:	0f 83 3f 01 00 00    	jae    4410 <send_headers+0x360>
    42d1:	f6 c3 04             	test   $0x4,%bl
    42d4:	0f 85 7b 02 00 00    	jne    4555 <send_headers+0x4a5>
    42da:	85 db                	test   %ebx,%ebx
    42dc:	74 13                	je     42f1 <send_headers+0x241>
    42de:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    42e6:	88 10                	mov    %dl,(%rax)
    42e8:	f6 c3 02             	test   $0x2,%bl
    42eb:	0f 85 96 02 00 00    	jne    4587 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    42f1:	4d 89 e8             	mov    %r13,%r8
    42f4:	48 8d 0d bf 2d 00 00 	lea    0x2dbf(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    42fb:	4c 89 e7             	mov    %r12,%rdi
    42fe:	31 c0                	xor    %eax,%eax
    4300:	ba 00 04 00 00       	mov    $0x400,%edx
    4305:	be 01 00 00 00       	mov    $0x1,%esi
    430a:	e8 11 e2 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    430f:	4c 89 e7             	mov    %r12,%rdi
    4312:	e8 09 e0 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4317:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    431a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    431d:	e8 ee e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4322:	48 85 c0             	test   %rax,%rax
    4325:	0f 84 80 02 00 00    	je     45ab <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    432b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    432f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4333:	83 fb 08             	cmp    $0x8,%ebx
    4336:	0f 83 1c 01 00 00    	jae    4458 <send_headers+0x3a8>
    433c:	f6 c3 04             	test   $0x4,%bl
    433f:	0f 85 29 02 00 00    	jne    456e <send_headers+0x4be>
    4345:	85 db                	test   %ebx,%ebx
    4347:	74 13                	je     435c <send_headers+0x2ac>
    4349:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4351:	88 10                	mov    %dl,(%rax)
    4353:	f6 c3 02             	test   $0x2,%bl
    4356:	0f 85 3d 02 00 00    	jne    4599 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    435c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4361:	bf 02 00 00 00       	mov    $0x2,%edi
    4366:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    436e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4376:	e8 95 e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    437b:	48 85 c0             	test   %rax,%rax
    437e:	0f 84 27 02 00 00    	je     45ab <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4384:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    438c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4390:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4398:	66 89 10             	mov    %dx,(%rax)
}
    439b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    43a3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    43ac:	0f 85 20 02 00 00    	jne    45d2 <send_headers+0x522>
    43b2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    43b9:	5b                   	pop    %rbx
    43ba:	5d                   	pop    %rbp
    43bb:	41 5c                	pop    %r12
    43bd:	41 5d                	pop    %r13
    43bf:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    43c0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    43c4:	0f 85 a4 fe ff ff    	jne    426e <send_headers+0x1be>
    43ca:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    43ce:	0f 85 9a fe ff ff    	jne    426e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    43d4:	66 0f 6f 05 04 36 00 00 	movdqa 0x3604(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    43dc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    43e6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    43ee:	66 0f 6f 05 fa 35 00 00 	movdqa 0x35fa(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    43f6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    43fe:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4406:	e9 63 fe ff ff       	jmp    426e <send_headers+0x1be>
    440b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4410:	89 da                	mov    %ebx,%edx
    4412:	48 89 c7             	mov    %rax,%rdi
    4415:	4c 89 e6             	mov    %r12,%rsi
    4418:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    441d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4422:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4425:	c1 e9 03             	shr    $0x3,%ecx
    4428:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    442b:	e9 c1 fe ff ff       	jmp    42f1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4430:	66 0f 6f 05 48 35 00 00 	movdqa 0x3548(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4438:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4440:	66 0f 6f 05 58 35 00 00 	movdqa 0x3558(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4448:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4450:	e9 cb fd ff ff       	jmp    4220 <send_headers+0x170>
    4455:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4458:	89 da                	mov    %ebx,%edx
    445a:	48 89 c7             	mov    %rax,%rdi
    445d:	4c 89 e6             	mov    %r12,%rsi
    4460:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4465:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    446a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    446d:	c1 e9 03             	shr    $0x3,%ecx
    4470:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4473:	e9 e4 fe ff ff       	jmp    435c <send_headers+0x2ac>
    4478:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4480:	48 8d 1d 48 2c 00 00 	lea    0x2c48(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4487:	e9 94 fd ff ff       	jmp    4220 <send_headers+0x170>
    448c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4490:	66 0f 6f 05 28 35 00 00 	movdqa 0x3528(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4498:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44a0:	66 0f 6f 05 28 35 00 00 	movdqa 0x3528(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    44a8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44b0:	e9 b0 fd ff ff       	jmp    4265 <send_headers+0x1b5>
    44b5:	0f 1f 00             	nopl   (%rax)
    44b8:	66 0f 6f 05 00 35 00 00 	movdqa 0x3500(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    44c0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44c8:	66 0f 6f 05 00 35 00 00 	movdqa 0x3500(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    44d0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44d8:	e9 71 fd ff ff       	jmp    424e <send_headers+0x19e>
    44dd:	0f 1f 00             	nopl   (%rax)
    44e0:	66 0f 6f 05 98 34 00 00 	movdqa 0x3498(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    44e8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44f0:	66 0f 6f 05 b8 34 00 00 	movdqa 0x34b8(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    44f8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4500:	e9 32 fd ff ff       	jmp    4237 <send_headers+0x187>
    4505:	0f 1f 00             	nopl   (%rax)
    4508:	66 0f 6f 05 b0 34 00 00 	movdqa 0x34b0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4510:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4518:	66 0f 6f 05 f0 34 00 00 	movdqa 0x34f0(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4520:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4528:	e9 6f fd ff ff       	jmp    429c <send_headers+0x1ec>
    452d:	0f 1f 00             	nopl   (%rax)
    4530:	66 0f 6f 05 88 34 00 00 	movdqa 0x3488(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4538:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4540:	66 0f 6f 05 b8 34 00 00 	movdqa 0x34b8(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4548:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4550:	e9 30 fd ff ff       	jmp    4285 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4555:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    455c:	89 db                	mov    %ebx,%ebx
    455e:	89 10                	mov    %edx,(%rax)
    4560:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4565:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4569:	e9 83 fd ff ff       	jmp    42f1 <send_headers+0x241>
    456e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4575:	89 db                	mov    %ebx,%ebx
    4577:	89 10                	mov    %edx,(%rax)
    4579:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    457e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4582:	e9 d5 fd ff ff       	jmp    435c <send_headers+0x2ac>
    4587:	89 db                	mov    %ebx,%ebx
    4589:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    458f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4594:	e9 58 fd ff ff       	jmp    42f1 <send_headers+0x241>
    4599:	89 db                	mov    %ebx,%ebx
    459b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    45a1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    45a6:	e9 b1 fd ff ff       	jmp    435c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    45ab:	48 8b 0d 6e 5a 00 00 	mov    0x5a6e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    45b2:	ba 28 00 00 00       	mov    $0x28,%edx
    45b7:	be 01 00 00 00       	mov    $0x1,%esi
    45bc:	48 8d 3d 45 2e 00 00 	lea    0x2e45(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    45c3:	e8 f8 de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    45c8:	bf 01 00 00 00       	mov    $0x1,%edi
    45cd:	e8 ce de ff ff       	call   24a0 <exit@plt>
}
    45d2:	e8 59 dd ff ff       	call   2330 <__stack_chk_fail@plt>
    45d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000045e0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    45e0:	f3 0f 1e fa          	endbr64
    45e4:	41 55                	push   %r13
    45e6:	49 89 d5             	mov    %rdx,%r13
    45e9:	41 54                	push   %r12
    45eb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    45ee:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    45f1:	55                   	push   %rbp
    45f2:	53                   	push   %rbx
    45f3:	48 89 f3             	mov    %rsi,%rbx
    45f6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    45fa:	e8 11 de ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    45ff:	48 85 c0             	test   %rax,%rax
    4602:	74 6b                	je     466f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4604:	4c 89 e7             	mov    %r12,%rdi
    4607:	48 89 c5             	mov    %rax,%rbp
    460a:	31 f6                	xor    %esi,%esi
    460c:	31 c0                	xor    %eax,%eax
    460e:	e8 6d de ff ff       	call   2480 <open@plt>
    4613:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4616:	85 c0                	test   %eax,%eax
    4618:	0f 88 38 df ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    461e:	48 89 da             	mov    %rbx,%rdx
    4621:	48 89 ee             	mov    %rbp,%rsi
    4624:	89 c7                	mov    %eax,%edi
    4626:	e8 65 dd ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    462b:	48 98                	cltq
    462d:	48 39 d8             	cmp    %rbx,%rax
    4630:	7c 1e                	jl     4650 <copy_file_contents+0x70>
    close(fd);
    4632:	44 89 e7             	mov    %r12d,%edi
    4635:	e8 36 dd ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    463a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    463e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4642:	48 83 c4 08          	add    $0x8,%rsp
    4646:	5b                   	pop    %rbx
    4647:	5d                   	pop    %rbp
    4648:	41 5c                	pop    %r12
    464a:	41 5d                	pop    %r13
    464c:	c3                   	ret
    464d:	0f 1f 00             	nopl   (%rax)
    4650:	48 8b 0d c9 59 00 00 	mov    0x59c9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4657:	ba 1a 00 00 00       	mov    $0x1a,%edx
    465c:	be 01 00 00 00       	mov    $0x1,%esi
    4661:	48 8d 3d 68 2a 00 00 	lea    0x2a68(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    4668:	e8 53 de ff ff       	call   24c0 <fwrite@plt>
    466d:	eb c3                	jmp    4632 <copy_file_contents+0x52>
    466f:	48 8b 0d aa 59 00 00 	mov    0x59aa(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4676:	ba 28 00 00 00       	mov    $0x28,%edx
    467b:	be 01 00 00 00       	mov    $0x1,%esi
    4680:	48 8d 3d 81 2d 00 00 	lea    0x2d81(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4687:	e8 34 de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    468c:	bf 01 00 00 00       	mov    $0x1,%edi
    4691:	e8 0a de ff ff       	call   24a0 <exit@plt>
    4696:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000046a0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    46a0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    46a4:	8b 46 44             	mov    0x44(%rsi),%eax
    46a7:	48 89 fa             	mov    %rdi,%rdx
    46aa:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    46ad:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    46b3:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    46b6:	48 8b 07             	mov    (%rdi),%rax
    46b9:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    46bc:	f6 c1 02             	test   $0x2,%cl
    46bf:	74 00                	je     46c1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    46c1:	89 f0                	mov    %esi,%eax
    46c3:	44 29 c0             	sub    %r8d,%eax
    46c6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    46c9:	0f 82 93 de ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    46cf:	c1 e9 0a             	shr    $0xa,%ecx
    46d2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    46d6:	8b 47 44             	mov    0x44(%rdi),%eax
    46d9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    46dc:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    46df:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    46e2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    46e5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    46e9:	d3 e0                	shl    %cl,%eax
    46eb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    46ee:	48 c1 e0 06          	shl    $0x6,%rax
    46f2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    46f6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    46fc:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    46ff:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4703:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4709:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4711:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4715:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4718:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    471f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4727:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    472b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    472f:	e8 0c dc ff ff       	call   2340 <io_uring_submit@plt>
}
    4734:	31 c0                	xor    %eax,%eax
    4736:	48 83 c4 08          	add    $0x8,%rsp
    473a:	c3                   	ret
    473b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004740 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4740:	f3 0f 1e fa          	endbr64
    4744:	41 55                	push   %r13
    4746:	41 89 fd             	mov    %edi,%r13d
    4749:	41 54                	push   %r12
    474b:	55                   	push   %rbp
    474c:	53                   	push   %rbx
    474d:	48 89 f3             	mov    %rsi,%rbx
    4750:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4754:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4757:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    475d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4760:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4763:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4765:	f6 c1 02             	test   $0x2,%cl
    4768:	74 00                	je     476a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    476a:	89 c2                	mov    %eax,%edx
    476c:	29 f2                	sub    %esi,%edx
    476e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4771:	0f 82 fb dd ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4777:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    477a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    477d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4780:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4785:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4788:	23 6b 58             	and    0x58(%rbx),%ebp
    478b:	d3 e5                	shl    %cl,%ebp
    478d:	48 c1 e5 06          	shl    $0x6,%rbp
    4791:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4795:	e8 76 dc ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    479a:	be 01 00 00 00       	mov    $0x1,%esi
    479f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    47a4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    47a7:	e8 f4 db ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    47ac:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    47b1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    47b5:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    47b8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    47bd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    47c2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    47cb:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    47d3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    47d7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    47db:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    47e2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    47ea:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    47ee:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    47f6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    47fe:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4802:	e8 39 db ff ff       	call   2340 <io_uring_submit@plt>
}
    4807:	48 83 c4 08          	add    $0x8,%rsp
    480b:	31 c0                	xor    %eax,%eax
    480d:	5b                   	pop    %rbx
    480e:	5d                   	pop    %rbp
    480f:	41 5c                	pop    %r12
    4811:	41 5d                	pop    %r13
    4813:	c3                   	ret
    4814:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    481f:	90                   	nop

0000000000004820 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4820:	f3 0f 1e fa          	endbr64
    4824:	41 56                	push   %r14
    4826:	41 89 f6             	mov    %esi,%r14d
    4829:	41 55                	push   %r13
    482b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    482e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4833:	41 54                	push   %r12
    4835:	55                   	push   %rbp
    4836:	48 89 d5             	mov    %rdx,%rbp
    4839:	53                   	push   %rbx
    void *buf = malloc(size);
    483a:	e8 d1 db ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    483f:	48 85 c0             	test   %rax,%rax
    4842:	0f 84 dd 00 00 00    	je     4925 <_send_static_string_content+0x105>
    4848:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    484b:	4c 89 ef             	mov    %r13,%rdi
    484e:	e8 cd da ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4853:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    485a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    485e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4861:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4864:	e8 a7 db ff ff       	call   2410 <malloc@plt>
    4869:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    486c:	48 85 c0             	test   %rax,%rax
    486f:	0f 84 b0 00 00 00    	je     4925 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4875:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4879:	4c 89 e2             	mov    %r12,%rdx
    487c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    487f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4883:	e8 58 db ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4888:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    488b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4891:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4894:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4898:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    489a:	f6 c1 02             	test   $0x2,%cl
    489d:	0f 85 7d 00 00 00    	jne    4920 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    48a3:	89 d0                	mov    %edx,%eax
    48a5:	29 f0                	sub    %esi,%eax
    48a7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    48aa:	0f 82 cc dc ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    48b0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    48b3:	8b 45 44             	mov    0x44(%rbp),%eax
    48b6:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    48b9:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    48bc:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    48bf:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    48c2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    48c8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    48cc:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    48ce:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    48d1:	48 89 ef             	mov    %rbp,%rdi
    48d4:	48 c1 e0 06          	shl    $0x6,%rax
    48d8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    48dc:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    48df:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    48e3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    48e9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    48f1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    48f5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    48f8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    48ff:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4907:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    490b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    490f:	5b                   	pop    %rbx
    4910:	5d                   	pop    %rbp
    4911:	41 5c                	pop    %r12
    4913:	41 5d                	pop    %r13
    4915:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4917:	e9 24 da ff ff       	jmp    2340 <io_uring_submit@plt>
    491c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4920:	e9 7e ff ff ff       	jmp    48a3 <_send_static_string_content+0x83>
    4925:	48 8b 0d f4 56 00 00 	mov    0x56f4(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    492c:	ba 28 00 00 00       	mov    $0x28,%edx
    4931:	be 01 00 00 00       	mov    $0x1,%esi
    4936:	48 8d 3d cb 2a 00 00 	lea    0x2acb(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    493d:	e8 7e db ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4942:	bf 01 00 00 00       	mov    $0x1,%edi
    4947:	e8 54 db ff ff       	call   24a0 <exit@plt>
    494c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004950 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4950:	f3 0f 1e fa          	endbr64
    4954:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4957:	89 fe                	mov    %edi,%esi
    4959:	48 8b 3d b8 56 00 00 	mov    0x56b8(%rip),%rdi        # a018 <unimplemented_content>
    4960:	e9 bb fe ff ff       	jmp    4820 <_send_static_string_content>
    4965:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004970 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4970:	f3 0f 1e fa          	endbr64
    4974:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4977:	89 fe                	mov    %edi,%esi
    4979:	48 8b 3d 90 56 00 00 	mov    0x5690(%rip),%rdi        # a010 <http_404_content>
    4980:	e9 9b fe ff ff       	jmp    4820 <_send_static_string_content>
    4985:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004990 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4990:	f3 0f 1e fa          	endbr64
    4994:	41 56                	push   %r14
    4996:	41 55                	push   %r13
    4998:	49 89 d5             	mov    %rdx,%r13
    499b:	41 54                	push   %r12
    499d:	41 89 f4             	mov    %esi,%r12d
    49a0:	55                   	push   %rbp
    49a1:	48 89 fd             	mov    %rdi,%rbp
    49a4:	53                   	push   %rbx
    49a5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    49ac:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    49b5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    49bd:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    49bf:	e8 5c d9 ff ff       	call   2320 <strlen@plt>
    49c4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    49c9:	48 89 c3             	mov    %rax,%rbx
    49cc:	0f 84 b6 00 00 00    	je     4a88 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    49d2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    49d7:	48 89 ee             	mov    %rbp,%rsi
    49da:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    49de:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    49e3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    49eb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    49f3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    49fe:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a06:	e8 b5 d9 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4a0b:	48 89 e6             	mov    %rsp,%rsi
    4a0e:	4c 89 f7             	mov    %r14,%rdi
    4a11:	e8 ba d9 ff ff       	call   23d0 <stat@plt>
    4a16:	83 f8 ff             	cmp    $0xffffffff,%eax
    4a19:	0f 84 d3 00 00 00    	je     4af2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    4a1f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4a23:	25 00 f0 00 00       	and    $0xf000,%eax
    4a28:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4a2d:	0f 84 f5 00 00 00    	je     4b28 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4a33:	48 8b 3d d6 55 00 00 	mov    0x55d6(%rip),%rdi        # a010 <http_404_content>
    4a3a:	4c 89 ea             	mov    %r13,%rdx
    4a3d:	44 89 e6             	mov    %r12d,%esi
    4a40:	e8 db fd ff ff       	call   4820 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4a45:	4c 89 f2             	mov    %r14,%rdx
    4a48:	bf 01 00 00 00       	mov    $0x1,%edi
    4a4d:	31 c0                	xor    %eax,%eax
    4a4f:	48 8d 35 ca 26 00 00 	lea    0x26ca(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    4a56:	e8 f5 d9 ff ff       	call   2450 <__printf_chk@plt>
}
    4a5b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4a63:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4a6c:	0f 85 20 01 00 00    	jne    4b92 <handle_get_method+0x202>
    4a72:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4a79:	5b                   	pop    %rbx
    4a7a:	5d                   	pop    %rbp
    4a7b:	41 5c                	pop    %r12
    4a7d:	41 5d                	pop    %r13
    4a7f:	41 5e                	pop    %r14
    4a81:	c3                   	ret
    4a82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a88:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a8d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4a95:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4a9a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a9d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4aa5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4aa8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4ab0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4abb:	e8 00 d9 ff ff       	call   23c0 <__memcpy_chk@plt>
    4ac0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4ac5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4aca:	48 8d 35 1a 26 00 00 	lea    0x261a(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4ad1:	48 29 d9             	sub    %rbx,%rcx
    4ad4:	ba 0b 00 00 00       	mov    $0xb,%edx
    4ad9:	e8 e2 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4ade:	48 89 e6             	mov    %rsp,%rsi
    4ae1:	4c 89 f7             	mov    %r14,%rdi
    4ae4:	e8 e7 d8 ff ff       	call   23d0 <stat@plt>
    4ae9:	83 f8 ff             	cmp    $0xffffffff,%eax
    4aec:	0f 85 2d ff ff ff    	jne    4a1f <handle_get_method+0x8f>
    4af2:	4c 89 f2             	mov    %r14,%rdx
    4af5:	48 89 e9             	mov    %rbp,%rcx
    4af8:	48 8d 35 f7 25 00 00 	lea    0x25f7(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    4aff:	31 c0                	xor    %eax,%eax
    4b01:	bf 01 00 00 00       	mov    $0x1,%edi
    4b06:	e8 45 d9 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    4b0b:	48 8b 3d fe 54 00 00 	mov    0x54fe(%rip),%rdi        # a010 <http_404_content>
    4b12:	4c 89 ea             	mov    %r13,%rdx
    4b15:	44 89 e6             	mov    %r12d,%esi
    4b18:	e8 03 fd ff ff       	call   4820 <_send_static_string_content>
}
    4b1d:	e9 39 ff ff ff       	jmp    4a5b <handle_get_method+0xcb>
    4b22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4b28:	bf 70 00 00 00       	mov    $0x70,%edi
    4b2d:	e8 de d8 ff ff       	call   2410 <malloc@plt>
    4b32:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4b35:	48 85 c0             	test   %rax,%rax
    4b38:	74 5d                	je     4b97 <handle_get_method+0x207>
            req->client_socket = client_socket;
    4b3a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4b3e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4b43:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4b47:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    4b4a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4b51:	e8 5a f5 ff ff       	call   40b0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4b56:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4b5b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4b5f:	4c 89 f7             	mov    %r14,%rdi
    4b62:	e8 79 fa ff ff       	call   45e0 <copy_file_contents>
    4b67:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4b6c:	4c 89 f2             	mov    %r14,%rdx
    4b6f:	31 c0                	xor    %eax,%eax
    4b71:	48 8d 35 96 25 00 00 	lea    0x2596(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4b78:	bf 01 00 00 00       	mov    $0x1,%edi
    4b7d:	e8 ce d8 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    4b82:	4c 89 ee             	mov    %r13,%rsi
    4b85:	48 89 df             	mov    %rbx,%rdi
    4b88:	e8 13 fb ff ff       	call   46a0 <add_write_request>
    4b8d:	e9 c9 fe ff ff       	jmp    4a5b <handle_get_method+0xcb>
}
    4b92:	e8 99 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4b97:	48 8b 0d 82 54 00 00 	mov    0x5482(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4b9e:	ba 28 00 00 00       	mov    $0x28,%edx
    4ba3:	be 01 00 00 00       	mov    $0x1,%esi
    4ba8:	48 8d 3d 59 28 00 00 	lea    0x2859(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4baf:	e8 0c d9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4bb4:	bf 01 00 00 00       	mov    $0x1,%edi
    4bb9:	e8 e2 d8 ff ff       	call   24a0 <exit@plt>
    4bbe:	66 90                	xchg   %ax,%ax

0000000000004bc0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4bc0:	f3 0f 1e fa          	endbr64
    4bc4:	41 57                	push   %r15
    4bc6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4bc8:	4c 8d 35 b6 24 00 00 	lea    0x24b6(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4bcf:	41 55                	push   %r13
    4bd1:	49 89 d5             	mov    %rdx,%r13
    4bd4:	41 54                	push   %r12
    4bd6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4bd9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4bdc:	55                   	push   %rbp
    4bdd:	53                   	push   %rbx
    4bde:	48 83 ec 18          	sub    $0x18,%rsp
    4be2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4beb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4bf0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4bf2:	49 89 e7             	mov    %rsp,%r15
    4bf5:	4c 89 fa             	mov    %r15,%rdx
    4bf8:	e8 83 d7 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4bfd:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4c01:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4c04:	84 db                	test   %bl,%bl
    4c06:	74 1d                	je     4c25 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4c08:	e8 03 d9 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4c0d:	48 89 ea             	mov    %rbp,%rdx
    4c10:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4c13:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4c17:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4c1a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    4c1d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4c21:	84 db                	test   %bl,%bl
    4c23:	75 eb                	jne    4c10 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4c25:	4c 89 fa             	mov    %r15,%rdx
    4c28:	4c 89 f6             	mov    %r14,%rsi
    4c2b:	31 ff                	xor    %edi,%edi
    4c2d:	e8 4e d7 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4c32:	48 8d 35 fa 24 00 00 	lea    0x24fa(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4c39:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4c3c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    4c3f:	e8 6c d7 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4c44:	4c 89 ea             	mov    %r13,%rdx
    4c47:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4c4a:	85 c0                	test   %eax,%eax
    4c4c:	75 2a                	jne    4c78 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    4c4e:	48 89 df             	mov    %rbx,%rdi
    4c51:	e8 3a fd ff ff       	call   4990 <handle_get_method>
}
    4c56:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4c5b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4c64:	75 20                	jne    4c86 <handle_http_method+0xc6>
    4c66:	48 83 c4 18          	add    $0x18,%rsp
    4c6a:	5b                   	pop    %rbx
    4c6b:	5d                   	pop    %rbp
    4c6c:	41 5c                	pop    %r12
    4c6e:	41 5d                	pop    %r13
    4c70:	41 5e                	pop    %r14
    4c72:	41 5f                	pop    %r15
    4c74:	c3                   	ret
    4c75:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4c78:	48 8b 3d 99 53 00 00 	mov    0x5399(%rip),%rdi        # a018 <unimplemented_content>
    4c7f:	e8 9c fb ff ff       	call   4820 <_send_static_string_content>
}
    4c84:	eb d0                	jmp    4c56 <handle_http_method+0x96>
    4c86:	e8 a5 d6 ff ff       	call   2330 <__stack_chk_fail@plt>
    4c8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004c90 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4c90:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4c94:	85 d2                	test   %edx,%edx
    4c96:	7e 38                	jle    4cd0 <get_line+0x40>
    4c98:	48 63 d2             	movslq %edx,%rdx
    4c9b:	48 83 c7 01          	add    $0x1,%rdi
    4c9f:	48 01 f2             	add    %rsi,%rdx
    4ca2:	eb 11                	jmp    4cb5 <get_line+0x25>
    4ca4:	0f 1f 40 00          	nopl   0x0(%rax)
    4ca8:	48 83 c6 01          	add    $0x1,%rsi
    4cac:	48 83 c7 01          	add    $0x1,%rdi
    4cb0:	48 39 d6             	cmp    %rdx,%rsi
    4cb3:	74 1b                	je     4cd0 <get_line+0x40>
        dest[i] = src[i];
    4cb5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4cb9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4cbb:	3c 0d                	cmp    $0xd,%al
    4cbd:	75 e9                	jne    4ca8 <get_line+0x18>
    4cbf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4cc2:	75 e4                	jne    4ca8 <get_line+0x18>
            dest[i] = '\0';
    4cc4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4cc7:	31 c0                	xor    %eax,%eax
    4cc9:	c3                   	ret
    4cca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4cd0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4cd5:	c3                   	ret
    4cd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004ce0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4ce0:	f3 0f 1e fa          	endbr64
    4ce4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4ceb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4cef:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4cf8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4d00:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4d02:	49 89 e2             	mov    %rsp,%r10
    4d05:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4d0d:	4c 89 d0             	mov    %r10,%rax
    4d10:	eb 13                	jmp    4d25 <handle_client_request+0x45>
    4d12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4d18:	48 83 c0 01          	add    $0x1,%rax
    4d1c:	48 83 c1 01          	add    $0x1,%rcx
    4d20:	4c 39 c8             	cmp    %r9,%rax
    4d23:	74 4b                	je     4d70 <handle_client_request+0x90>
        dest[i] = src[i];
    4d25:	44 0f b6 01          	movzbl (%rcx),%r8d
    4d29:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4d2c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4d30:	75 e6                	jne    4d18 <handle_client_request+0x38>
    4d32:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4d36:	75 e0                	jne    4d18 <handle_client_request+0x38>
            dest[i] = '\0';
    4d38:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4d3b:	8b 47 08             	mov    0x8(%rdi),%eax
    4d3e:	48 89 f2             	mov    %rsi,%rdx
    4d41:	4c 89 d7             	mov    %r10,%rdi
    4d44:	89 c6                	mov    %eax,%esi
    4d46:	e8 75 fe ff ff       	call   4bc0 <handle_http_method>
}
    4d4b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4d53:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d5c:	75 39                	jne    4d97 <handle_client_request+0xb7>
    4d5e:	31 c0                	xor    %eax,%eax
    4d60:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4d67:	c3                   	ret
    4d68:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4d70:	48 8b 0d a9 52 00 00 	mov    0x52a9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4d77:	ba 12 00 00 00       	mov    $0x12,%edx
    4d7c:	be 01 00 00 00       	mov    $0x1,%esi
    4d81:	48 8d 3d af 23 00 00 	lea    0x23af(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4d88:	e8 33 d7 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4d8d:	bf 01 00 00 00       	mov    $0x1,%edi
    4d92:	e8 09 d7 ff ff       	call   24a0 <exit@plt>
}
    4d97:	e8 94 d5 ff ff       	call   2330 <__stack_chk_fail@plt>
    4d9c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004da0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4da0:	f3 0f 1e fa          	endbr64
    4da4:	55                   	push   %rbp
    4da5:	53                   	push   %rbx
    4da6:	48 89 cb             	mov    %rcx,%rbx
    4da9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4dad:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4db0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4db3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4db9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4dbc:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4dbf:	f6 c1 02             	test   $0x2,%cl
    4dc2:	74 00                	je     4dc4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4dc4:	41 89 c0             	mov    %eax,%r8d
    4dc7:	45 29 c8             	sub    %r9d,%r8d
    4dca:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4dce:	0f 82 b8 d7 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4dd4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4dd7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4dda:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4ddd:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4de0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4de3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4de7:	d3 e5                	shl    %cl,%ebp
    4de9:	48 c1 e5 06          	shl    $0x6,%rbp
    4ded:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4df1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4df4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4df9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4e00:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4e04:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4e08:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4e10:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4e18:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4e1c:	e8 ef d5 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4e21:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4e24:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4e2a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4e2e:	48 83 c4 08          	add    $0x8,%rsp
    4e32:	5b                   	pop    %rbx
    4e33:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4e34:	e9 07 d5 ff ff       	jmp    2340 <io_uring_submit@plt>
    4e39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004e40 <io_thread>:
void* io_thread(void *arg) {
    4e40:	f3 0f 1e fa          	endbr64
    4e44:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e46:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4e48:	41 56                	push   %r14
    4e4a:	41 55                	push   %r13
    4e4c:	41 54                	push   %r12
    4e4e:	55                   	push   %rbp
    4e4f:	48 89 fd             	mov    %rdi,%rbp
    4e52:	53                   	push   %rbx
    4e53:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4e5a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4e63:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4e6b:	48 8b 87 c8 00 00 00 	mov    0xc8(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e72:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4e77:	bf 00 01 00 00       	mov    $0x100,%edi
    4e7c:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4e7f:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4e83:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4e88:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4e8d:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4e92:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4e97:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4e9f:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4ea4:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4eac:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4eb1:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4eb9:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4ebe:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4ec6:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4ecb:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4ed3:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4ed8:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4ee0:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4ee8:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4ef0:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4ef8:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4f00:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4f08:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4f10:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4f18:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4f20:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4f28:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4f30:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4f37:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4f3f:	e8 ac d4 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4f44:	48 8b bd c8 00 00 00 	mov    0xc8(%rbp),%rdi
    4f4b:	31 f6                	xor    %esi,%esi
    4f4d:	e8 8e d5 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4f52:	31 d2                	xor    %edx,%edx
    4f54:	be 01 00 00 00       	mov    $0x1,%esi
    4f59:	bf 02 00 00 00       	mov    $0x2,%edi
    4f5e:	e8 cd d5 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4f63:	83 f8 ff             	cmp    $0xffffffff,%eax
    4f66:	0f 84 62 d6 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    4f6c:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4f71:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4f77:	89 c7                	mov    %eax,%edi
    4f79:	41 89 c4             	mov    %eax,%r12d
    4f7c:	ba 02 00 00 00       	mov    $0x2,%edx
    4f81:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4f86:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4f8e:	e8 6d d3 ff ff       	call   2300 <setsockopt@plt>
    4f93:	85 c0                	test   %eax,%eax
    4f95:	0f 88 07 d6 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4f9b:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4fa0:	ba 10 00 00 00       	mov    $0x10,%edx
    4fa5:	44 89 e7             	mov    %r12d,%edi
    4fa8:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4fb1:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4fb9:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4fc1:	e8 9a d4 ff ff       	call   2460 <bind@plt>
    4fc6:	85 c0                	test   %eax,%eax
    4fc8:	0f 88 0c d6 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4fce:	be 0a 00 00 00       	mov    $0xa,%esi
    4fd3:	44 89 e7             	mov    %r12d,%edi
    4fd6:	e8 45 d4 ff ff       	call   2420 <listen@plt>
    4fdb:	85 c0                	test   %eax,%eax
    4fdd:	0f 88 cb d5 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4fe3:	ba db 18 00 00       	mov    $0x18db,%edx
    4fe8:	48 8d 35 8d 21 00 00 	lea    0x218d(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4fef:	bf 01 00 00 00       	mov    $0x1,%edi
    4ff4:	31 c0                	xor    %eax,%eax
    4ff6:	e8 55 d4 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4ffb:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5000:	48 89 d9             	mov    %rbx,%rcx
    5003:	44 89 e7             	mov    %r12d,%edi
    5006:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    500b:	48 89 c6             	mov    %rax,%rsi
    500e:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5013:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5018:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5020:	e8 7b fd ff ff       	call   4da0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5025:	bf 01 00 00 00       	mov    $0x1,%edi
    502a:	be 10 00 00 00       	mov    $0x10,%esi
    502f:	e8 6c d3 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    5034:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5039:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    503c:	e8 cf d3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    5041:	48 85 c0             	test   %rax,%rax
    5044:	0f 84 c8 04 00 00    	je     5512 <io_thread+0x6d2>
  iov->iov_base = zh_malloc(10);
    504a:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    504e:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5055:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    505c:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5064:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5067:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    506c:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    506e:	f6 c1 02             	test   $0x2,%cl
    5071:	0f 85 29 04 00 00    	jne    54a0 <io_thread+0x660>
	if (next - head <= sq->ring_entries) {
    5077:	89 d0                	mov    %edx,%eax
    5079:	29 f0                	sub    %esi,%eax
    507b:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5082:	0f 82 3c d5 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5088:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    508b:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	sqe->addr3 = 0;
    5092:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5096:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5099:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    50a0:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    50a3:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    50aa:	48 8d b5 d0 00 00 00 	lea    0xd0(%rbp),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    50b1:	8b 95 d0 00 00 00    	mov    0xd0(%rbp),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50b7:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    50b9:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    50be:	48 c1 e0 06          	shl    $0x6,%rax
    50c2:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    50ca:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    50d0:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    50d3:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    50db:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    50df:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    50e7:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    50ef:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    50f3:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    50f7:	e8 44 d2 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    50fc:	83 7d 64 01          	cmpl   $0x1,0x64(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5100:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5105:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    510d:	0f 85 de 01 00 00    	jne    52f1 <io_thread+0x4b1>
    5113:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5118:	4d 89 ce             	mov    %r9,%r14
    511b:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5120:	48 8d 3d 6b 20 00 00 	lea    0x206b(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    5127:	e8 c4 d1 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    512c:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5133:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    513a:	c1 e9 0b             	shr    $0xb,%ecx
    513d:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5140:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5148:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    514a:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5152:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5154:	39 d0                	cmp    %edx,%eax
    5156:	74 36                	je     518e <io_thread+0x34e>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5158:	89 f8                	mov    %edi,%eax
    515a:	21 d0                	and    %edx,%eax
    515c:	d3 e0                	shl    %cl,%eax
    515e:	48 c1 e0 04          	shl    $0x4,%rax
    5162:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    516a:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5172:	0f 85 b8 01 00 00    	jne    5330 <io_thread+0x4f0>
    5178:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    517c:	0f 85 26 03 00 00    	jne    54a8 <io_thread+0x668>
			if (cqe->res < 0)
    5182:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5185:	83 c2 01             	add    $0x1,%edx
    5188:	89 16                	mov    %edx,(%rsi)
			if (!err)
    518a:	85 c0                	test   %eax,%eax
    518c:	79 b2                	jns    5140 <io_thread+0x300>
	*cqe_ptr = cqe;
    518e:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    5197:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    51a0:	45 31 c0             	xor    %r8d,%r8d
    51a3:	31 d2                	xor    %edx,%edx
    51a5:	b9 01 00 00 00       	mov    $0x1,%ecx
    51aa:	4c 89 f6             	mov    %r14,%rsi
    51ad:	48 89 df             	mov    %rbx,%rdi
    51b0:	e8 8b d2 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    51b5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    51b8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    51bd:	48 83 38 01          	cmpq   $0x1,(%rax)
    51c1:	0f 84 f1 02 00 00    	je     54b8 <io_thread+0x678>
    51c7:	48 8d 3d ea 1f 00 00 	lea    0x1fea(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    51ce:	e8 1d d1 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    51d3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    51d8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    51db:	45 85 ff             	test   %r15d,%r15d
    51de:	0f 88 b2 d3 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    51e4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    51e7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    51eb:	85 c0                	test   %eax,%eax
    51ed:	0f 88 e5 02 00 00    	js     54d8 <io_thread+0x698>
      switch (req->event_type) {
    51f3:	41 83 f8 01          	cmp    $0x1,%r8d
    51f7:	0f 84 83 01 00 00    	je     5380 <io_thread+0x540>
    51fd:	41 83 f8 02          	cmp    $0x2,%r8d
    5201:	0f 84 a9 01 00 00    	je     53b0 <io_thread+0x570>
    5207:	45 85 c0             	test   %r8d,%r8d
    520a:	0f 85 58 01 00 00    	jne    5368 <io_thread+0x528>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5210:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5215:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    521a:	48 89 d9             	mov    %rbx,%rcx
    521d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5221:	e8 7a fb ff ff       	call   4da0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5226:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    522b:	48 89 de             	mov    %rbx,%rsi
    522e:	8b 78 08             	mov    0x8(%rax),%edi
    5231:	e8 0a f5 ff ff       	call   4740 <add_read_request>
              free(req);
    5236:	4c 89 e7             	mov    %r12,%rdi
    5239:	e8 82 d0 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    523e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5243:	48 85 c0             	test   %rax,%rax
    5246:	0f 85 1c 01 00 00    	jne    5368 <io_thread+0x528>
	unsigned int head, next = sq->sqe_tail + 1;
    524c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5253:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    525a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    525d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5262:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5264:	f6 c1 02             	test   $0x2,%cl
    5267:	74 00                	je     5269 <io_thread+0x429>
	if (next - head <= sq->ring_entries) {
    5269:	89 d0                	mov    %edx,%eax
    526b:	29 f0                	sub    %esi,%eax
    526d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5274:	0f 82 40 d3 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    527a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    527d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5282:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5286:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5289:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5290:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5293:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    529a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52a1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    52a3:	8b 95 d0 00 00 00    	mov    0xd0(%rbp),%edx
    52a9:	48 c1 e0 06          	shl    $0x6,%rax
    52ad:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    52b5:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    52bb:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    52be:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    52c6:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    52ca:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    52d2:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    52da:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    52de:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    52e2:	e8 59 d0 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    52e7:	83 7d 64 01          	cmpl   $0x1,0x64(%rbp)
    52eb:	0f 84 2f fe ff ff    	je     5120 <io_thread+0x2e0>
    52f1:	48 8d 3d f9 1e 00 00 	lea    0x1ef9(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    52f8:	e8 f3 cf ff ff       	call   22f0 <puts@plt>
}
    52fd:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5305:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    530e:	0f 85 25 02 00 00    	jne    5539 <io_thread+0x6f9>
    5314:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    531b:	31 c0                	xor    %eax,%eax
    531d:	5b                   	pop    %rbx
    531e:	5d                   	pop    %rbp
    531f:	41 5c                	pop    %r12
    5321:	41 5d                	pop    %r13
    5323:	41 5e                	pop    %r14
    5325:	41 5f                	pop    %r15
    5327:	c3                   	ret
    5328:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    5330:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5335:	48 85 c0             	test   %rax,%rax
    5338:	0f 84 62 fe ff ff    	je     51a0 <io_thread+0x360>
      if (cqe->user_data == 1) {
    533e:	48 83 38 01          	cmpq   $0x1,(%rax)
    5342:	0f 84 70 01 00 00    	je     54b8 <io_thread+0x678>
    5348:	48 8d 3d 69 1e 00 00 	lea    0x1e69(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    534f:	e8 9c cf ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5354:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5359:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    535c:	e9 83 fe ff ff       	jmp    51e4 <io_thread+0x3a4>
    5361:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5368:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5370:	8b 02                	mov    (%rdx),%eax
    5372:	83 c0 01             	add    $0x1,%eax
    5375:	89 02                	mov    %eax,(%rdx)
}
    5377:	e9 d0 fe ff ff       	jmp    524c <io_thread+0x40c>
    537c:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5380:	85 c0                	test   %eax,%eax
    5382:	75 7c                	jne    5400 <io_thread+0x5c0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5384:	48 8b 0d 95 4c 00 00 	mov    0x4c95(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    538b:	ba 0f 00 00 00       	mov    $0xf,%edx
    5390:	be 01 00 00 00       	mov    $0x1,%esi
    5395:	48 8d 3d 45 1e 00 00 	lea    0x1e45(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    539c:	e8 1f d1 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    53a1:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    53a6:	e9 98 fe ff ff       	jmp    5243 <io_thread+0x403>
    53ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    53b0:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    53b5:	45 31 ff             	xor    %r15d,%r15d
    53b8:	85 c0                	test   %eax,%eax
    53ba:	7e 20                	jle    53dc <io_thread+0x59c>
    53bc:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    53c0:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    53c3:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    53c7:	48 c1 e0 04          	shl    $0x4,%rax
    53cb:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    53d0:	e8 eb ce ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    53d5:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    53da:	7f e4                	jg     53c0 <io_thread+0x580>
              close(req->client_socket);
    53dc:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    53e1:	e8 8a cf ff ff       	call   2370 <close@plt>
              free(req);
    53e6:	4c 89 e7             	mov    %r12,%rdi
    53e9:	e8 d2 ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    53ee:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    53f3:	e9 4b fe ff ff       	jmp    5243 <io_thread+0x403>
    53f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int i = 0; i < dest_sz; i++) {
    5400:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5405:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    540a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5412:	eb 11                	jmp    5425 <io_thread+0x5e5>
    5414:	0f 1f 40 00          	nopl   0x0(%rax)
    5418:	48 83 c0 01          	add    $0x1,%rax
    541c:	48 83 c2 01          	add    $0x1,%rdx
    5420:	48 39 c6             	cmp    %rax,%rsi
    5423:	74 4b                	je     5470 <io_thread+0x630>
        dest[i] = src[i];
    5425:	0f b6 0a             	movzbl (%rdx),%ecx
    5428:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    542a:	80 f9 0d             	cmp    $0xd,%cl
    542d:	75 e9                	jne    5418 <io_thread+0x5d8>
    542f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5433:	75 e3                	jne    5418 <io_thread+0x5d8>
            dest[i] = '\0';
    5435:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5438:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    543d:	48 89 da             	mov    %rbx,%rdx
    5440:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5445:	e8 76 f7 ff ff       	call   4bc0 <handle_http_method>
              free(req->iov[0].iov_base);
    544a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    544f:	e8 6c ce ff ff       	call   22c0 <free@plt>
              free(req);
    5454:	4c 89 e7             	mov    %r12,%rdi
    5457:	e8 64 ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    545c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5461:	e9 dd fd ff ff       	jmp    5243 <io_thread+0x403>
    5466:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5470:	48 8b 0d a9 4b 00 00 	mov    0x4ba9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5477:	ba 12 00 00 00       	mov    $0x12,%edx
    547c:	be 01 00 00 00       	mov    $0x1,%esi
    5481:	48 8d 3d af 1c 00 00 	lea    0x1caf(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5488:	e8 33 d0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    548d:	bf 01 00 00 00       	mov    $0x1,%edi
    5492:	e8 09 d0 ff ff       	call   24a0 <exit@plt>
    5497:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    54a0:	e9 d2 fb ff ff       	jmp    5077 <io_thread+0x237>
    54a5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    54a8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    54ad:	e9 8c fe ff ff       	jmp    533e <io_thread+0x4fe>
    54b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    54b8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    54c0:	48 8d 3d dd 1c 00 00 	lea    0x1cdd(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    54c7:	8b 02                	mov    (%rdx),%eax
    54c9:	83 c0 01             	add    $0x1,%eax
    54cc:	89 02                	mov    %eax,(%rdx)
    54ce:	e8 1d ce ff ff       	call   22f0 <puts@plt>
    54d3:	e9 19 fe ff ff       	jmp    52f1 <io_thread+0x4b1>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    54d8:	f7 d8                	neg    %eax
    54da:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    54df:	89 c7                	mov    %eax,%edi
    54e1:	e8 1a d0 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    54e6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    54eb:	be 01 00 00 00       	mov    $0x1,%esi
    54f0:	48 8b 3d 29 4b 00 00 	mov    0x4b29(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    54f7:	48 89 c1             	mov    %rax,%rcx
    54fa:	48 8d 15 37 1f 00 00 	lea    0x1f37(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    5501:	31 c0                	xor    %eax,%eax
    5503:	e8 c8 cf ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5508:	bf 01 00 00 00       	mov    $0x1,%edi
    550d:	e8 8e cf ff ff       	call   24a0 <exit@plt>
    5512:	48 8b 0d 07 4b 00 00 	mov    0x4b07(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5519:	ba 28 00 00 00       	mov    $0x28,%edx
    551e:	be 01 00 00 00       	mov    $0x1,%esi
    5523:	48 8d 3d de 1e 00 00 	lea    0x1ede(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    552a:	e8 91 cf ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    552f:	bf 01 00 00 00       	mov    $0x1,%edi
    5534:	e8 67 cf ff ff       	call   24a0 <exit@plt>
}
    5539:	e8 f2 cd ff ff       	call   2330 <__stack_chk_fail@plt>
    553e:	66 90                	xchg   %ax,%ax

0000000000005540 <sendm>:
int sendm(struct BarrierTask *data) {
    5540:	f3 0f 1e fa          	endbr64
    5544:	41 57                	push   %r15
    5546:	41 56                	push   %r14
    5548:	41 55                	push   %r13
    554a:	41 54                	push   %r12
    554c:	55                   	push   %rbp
    554d:	53                   	push   %rbx
    554e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5552:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
    5559:	0f 85 99 01 00 00    	jne    56f8 <sendm+0x1b8>
    555f:	48 8d b7 80 01 00 00 	lea    0x180(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5566:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    556c:	48 89 fa             	mov    %rdi,%rdx
    556f:	31 c9                	xor    %ecx,%ecx
    5571:	48 89 34 24          	mov    %rsi,(%rsp)
    5575:	48 8d b7 88 01 00 00 	lea    0x188(%rdi),%rsi
    557c:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5581:	85 c0                	test   %eax,%eax
    5583:	0f 8e ce 00 00 00    	jle    5657 <sendm+0x117>
    5589:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5590:	39 8a 30 01 00 00    	cmp    %ecx,0x130(%rdx)
    5596:	0f 84 af 00 00 00    	je     564b <sendm+0x10b>
        struct Data *them = data->mailboxes[n].higher;
    559c:	49 89 ca             	mov    %rcx,%r10
    559f:	49 c1 e2 05          	shl    $0x5,%r10
    55a3:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
    55aa:	4d 8b 5a 08          	mov    0x8(%r10),%r11
        for (; them->messages_count < min;) {
    55ae:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    55b2:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    55b6:	4c 39 cb             	cmp    %r9,%rbx
    55b9:	0f 8d 83 00 00 00    	jge    5642 <sendm+0x102>
    55bf:	4c 89 cf             	mov    %r9,%rdi
    55c2:	48 8b aa 08 01 00 00 	mov    0x108(%rdx),%rbp
    55c9:	4d 8b 72 10          	mov    0x10(%r10),%r14
    55cd:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    55d0:	49 8b 33             	mov    (%r11),%rsi
    55d3:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    55d7:	48 83 f8 02          	cmp    $0x2,%rax
    55db:	0f 86 ff 00 00 00    	jbe    56e0 <sendm+0x1a0>
    55e1:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    55e9:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    55f1:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    55f5:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    55f9:	4c 39 2c 24          	cmp    %r13,(%rsp)
    55fd:	73 71                	jae    5670 <sendm+0x130>
    55ff:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5604:	4d 39 fc             	cmp    %r15,%r12
    5607:	73 67                	jae    5670 <sendm+0x130>
    5609:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    560d:	49 01 f0             	add    %rsi,%r8
    5610:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    5617:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    561b:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    561f:	49 39 d8             	cmp    %rbx,%r8
    5622:	75 ec                	jne    5610 <sendm+0xd0>
    5624:	0f 1f 40 00          	nopl   0x0(%rax)
    5628:	48 01 fd             	add    %rdi,%rbp
    562b:	4c 01 f7             	add    %r14,%rdi
    562e:	48 89 aa 08 01 00 00 	mov    %rbp,0x108(%rdx)
    5635:	49 89 7a 10          	mov    %rdi,0x10(%r10)
    5639:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    563d:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5642:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5645:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    564b:	48 83 c1 01          	add    $0x1,%rcx
    564f:	39 c8                	cmp    %ecx,%eax
    5651:	0f 8f 39 ff ff ff    	jg     5590 <sendm+0x50>
}
    5657:	48 83 c4 18          	add    $0x18,%rsp
    565b:	31 c0                	xor    %eax,%eax
    565d:	5b                   	pop    %rbx
    565e:	5d                   	pop    %rbp
    565f:	41 5c                	pop    %r12
    5661:	41 5d                	pop    %r13
    5663:	41 5e                	pop    %r14
    5665:	41 5f                	pop    %r15
    5667:	c3                   	ret
    5668:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5670:	49 89 fd             	mov    %rdi,%r13
    5673:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    567a:	4d 89 e0             	mov    %r12,%r8
    567d:	49 d1 ed             	shr    %r13
    5680:	49 c1 e5 04          	shl    $0x4,%r13
    5684:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5689:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    568d:	41 83 e5 10          	and    $0x10,%r13d
    5691:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5695:	74 11                	je     56a8 <sendm+0x168>
          them->messages[them->messages_count++] = data->message; 
    5697:	49 83 c0 10          	add    $0x10,%r8
    569b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    56a0:	4d 39 f8             	cmp    %r15,%r8
    56a3:	74 15                	je     56ba <sendm+0x17a>
    56a5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    56a8:	41 0f 11 00          	movups %xmm0,(%r8)
    56ac:	49 83 c0 20          	add    $0x20,%r8
    56b0:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    56b5:	4d 39 f8             	cmp    %r15,%r8
    56b8:	75 ee                	jne    56a8 <sendm+0x168>
    56ba:	49 89 f8             	mov    %rdi,%r8
    56bd:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    56c1:	49 01 d8             	add    %rbx,%r8
    56c4:	40 f6 c7 01          	test   $0x1,%dil
    56c8:	0f 84 5a ff ff ff    	je     5628 <sendm+0xe8>
          them->messages[them->messages_count++] = data->message; 
    56ce:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    56d5:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    56d9:	e9 4a ff ff ff       	jmp    5628 <sendm+0xe8>
    56de:	66 90                	xchg   %ax,%ax
    56e0:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    56e8:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    56f0:	e9 14 ff ff ff       	jmp    5609 <sendm+0xc9>
    56f5:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    56f8:	48 8d 3d 05 1b 00 00 	lea    0x1b05(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    56ff:	e8 ec cb ff ff       	call   22f0 <puts@plt>
    5704:	e9 4e ff ff ff       	jmp    5657 <sendm+0x117>
    5709:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005710 <receive>:
int receive(struct BarrierTask *data) {
    5710:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5714:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    571a:	85 c0                	test   %eax,%eax
    571c:	0f 8e f1 00 00 00    	jle    5813 <receive+0x103>
int receive(struct BarrierTask *data) {
    5722:	41 54                	push   %r12
    5724:	48 89 fa             	mov    %rdi,%rdx
    5727:	55                   	push   %rbp
    5728:	31 ed                	xor    %ebp,%ebp
    572a:	53                   	push   %rbx
    572b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5730:	48 89 ee             	mov    %rbp,%rsi
    5733:	48 c1 e6 05          	shl    $0x5,%rsi
    5737:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    573e:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5741:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    5746:	48 85 ff             	test   %rdi,%rdi
    5749:	0f 8e a1 00 00 00    	jle    57f0 <receive+0xe0>
      data->sends++;
    574f:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    5756:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    575a:	4c 63 1a             	movslq (%rdx),%r11
    575d:	49 89 c9             	mov    %rcx,%r9
    5760:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5764:	49 f7 d9             	neg    %r9
    5767:	48 01 c7             	add    %rax,%rdi
    576a:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    576e:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    5775:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    5779:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    577c:	49 29 c8             	sub    %rcx,%r8
    577f:	eb 10                	jmp    5791 <receive+0x81>
    5781:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5788:	48 83 c0 01          	add    $0x1,%rax
    578c:	48 39 c7             	cmp    %rax,%rdi
    578f:	74 5f                	je     57f0 <receive+0xe0>
      data->n++;
    5791:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    5795:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
      data->n++;
    579c:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    57a3:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    57a7:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    57ab:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    57b0:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    57b4:	75 d2                	jne    5788 <receive+0x78>
    57b6:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    57bd:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    57c1:	75 c5                	jne    5788 <receive+0x78>
    57c3:	bf 01 00 00 00       	mov    $0x1,%edi
    57c8:	b9 01 00 00 00       	mov    $0x1,%ecx
    57cd:	ba 01 00 00 00       	mov    $0x1,%edx
    57d2:	31 c0                	xor    %eax,%eax
    57d4:	48 8d 35 85 1c 00 00 	lea    0x1c85(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    57db:	e8 70 cc ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    57e0:	bf 01 00 00 00       	mov    $0x1,%edi
    57e5:	e8 b6 cc ff ff       	call   24a0 <exit@plt>
    57ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    57f0:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    57f9:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    57fc:	48 83 c5 01          	add    $0x1,%rbp
    5800:	39 aa 34 01 00 00    	cmp    %ebp,0x134(%rdx)
    5806:	0f 8f 24 ff ff ff    	jg     5730 <receive+0x20>
}
    580c:	5b                   	pop    %rbx
    580d:	31 c0                	xor    %eax,%eax
    580f:	5d                   	pop    %rbp
    5810:	41 5c                	pop    %r12
    5812:	c3                   	ret
    5813:	31 c0                	xor    %eax,%eax
    5815:	c3                   	ret
    5816:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005820 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5820:	f3 0f 1e fa          	endbr64
    5824:	41 57                	push   %r15
    5826:	41 56                	push   %r14
    5828:	41 55                	push   %r13
    582a:	41 54                	push   %r12
    582c:	55                   	push   %rbp
    582d:	53                   	push   %rbx
    582e:	48 89 fb             	mov    %rdi,%rbx
    5831:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    5835:	8b 07                	mov    (%rdi),%eax
    5837:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    583d:	0f 84 3d 01 00 00    	je     5980 <barriered_work+0x160>
    receive(data);
    5843:	e8 c8 fe ff ff       	call   5710 <receive>
    while (data->scheduled == 1) {
    5848:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    584f:	75 1b                	jne    586c <barriered_work+0x4c>
    5851:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    5858:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    5860:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5863:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    586a:	74 ec                	je     5858 <barriered_work+0x38>
  if (data->sending == 1) {
    586c:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    5873:	0f 85 7f 02 00 00    	jne    5af8 <barriered_work+0x2d8>
      for (int n = 0 ; n < data->thread_count; n++) {
    5879:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    587f:	85 c0                	test   %eax,%eax
    5881:	0f 8e 7d 02 00 00    	jle    5b04 <barriered_work+0x2e4>
    5887:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    588e:	31 d2                	xor    %edx,%edx
    5890:	48 89 0c 24          	mov    %rcx,(%rsp)
    5894:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    589b:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    58a0:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    58a6:	0f 84 bf 00 00 00    	je     596b <barriered_work+0x14b>
        struct Data *them = data->mailboxes[n].higher;
    58ac:	49 89 d1             	mov    %rdx,%r9
    58af:	49 c1 e1 05          	shl    $0x5,%r9
    58b3:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    58ba:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    58be:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    58c2:	4d 63 42 10          	movslq 0x10(%r10),%r8
    58c6:	4d 39 c3             	cmp    %r8,%r11
    58c9:	0f 8d 93 00 00 00    	jge    5962 <barriered_work+0x142>
    58cf:	4c 89 c6             	mov    %r8,%rsi
    58d2:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    58d9:	4d 8b 71 10          	mov    0x10(%r9),%r14
    58dd:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    58e0:	49 8b 0a             	mov    (%r10),%rcx
    58e3:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    58e7:	48 83 f8 02          	cmp    $0x2,%rax
    58eb:	0f 86 9f 02 00 00    	jbe    5b90 <barriered_work+0x370>
    58f1:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    58f9:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5901:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5905:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5909:	4c 39 2c 24          	cmp    %r13,(%rsp)
    590d:	0f 83 0d 02 00 00    	jae    5b20 <barriered_work+0x300>
    5913:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5918:	4d 39 fc             	cmp    %r15,%r12
    591b:	0f 83 ff 01 00 00    	jae    5b20 <barriered_work+0x300>
    5921:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5925:	48 01 cf             	add    %rcx,%rdi
    5928:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5930:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5937:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    593b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    593f:	49 39 fb             	cmp    %rdi,%r11
    5942:	75 ec                	jne    5930 <barriered_work+0x110>
    5944:	0f 1f 40 00          	nopl   0x0(%rax)
    5948:	48 01 f5             	add    %rsi,%rbp
    594b:	4c 01 f6             	add    %r14,%rsi
    594e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5955:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5959:	4d 89 42 08          	mov    %r8,0x8(%r10)
    595d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5962:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5965:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    596b:	48 83 c2 01          	add    $0x1,%rdx
    596f:	39 d0                	cmp    %edx,%eax
    5971:	0f 8f 29 ff ff ff    	jg     58a0 <barriered_work+0x80>
    5977:	e9 88 01 00 00       	jmp    5b04 <barriered_work+0x2e4>
    597c:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    5980:	e8 8b fd ff ff       	call   5710 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    5985:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    598c:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    598e:	45 85 c9             	test   %r9d,%r9d
    5991:	0f 8e 85 00 00 00    	jle    5a1c <barriered_work+0x1fc>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5997:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    599e:	4c 63 d8             	movslq %eax,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    59a1:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59a4:	49 c1 e3 09          	shl    $0x9,%r11
    59a8:	4c 8b 52 40          	mov    0x40(%rdx),%r10
              int next_task = abs((t + 1) % (data->thread_count));
    59ac:	99                   	cltd
    59ad:	41 f7 f9             	idiv   %r9d
    59b0:	4c 89 d7             	mov    %r10,%rdi
    59b3:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
    59b7:	89 d0                	mov    %edx,%eax
    59b9:	f7 d8                	neg    %eax
    59bb:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59be:	45 31 c0             	xor    %r8d,%r8d
              int next_task = abs((t + 1) % (data->thread_count));
    59c1:	48 63 ea             	movslq %edx,%rbp
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59c4:	48 c1 e5 09          	shl    $0x9,%rbp
    59c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    59d0:	31 c0                	xor    %eax,%eax
    59d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59d8:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    59dc:	48 8b 52 58          	mov    0x58(%rdx),%rdx
    59e0:	48 8b 8c 2a 68 01 00 00 	mov    0x168(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59e8:	48 8b 17             	mov    (%rdi),%rdx
    59eb:	48 8b 72 58          	mov    0x58(%rdx),%rsi
    59ef:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    59f2:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59f6:	48 c1 e2 05          	shl    $0x5,%rdx
    59fa:	4a 03 94 1e 68 01 00 00 	add    0x168(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5a02:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    5a06:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    5a0a:	49 39 c1             	cmp    %rax,%r9
    5a0d:	75 c9                	jne    59d8 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    5a0f:	48 83 c7 08          	add    $0x8,%rdi
    5a13:	49 83 c0 20          	add    $0x20,%r8
    5a17:	49 39 fc             	cmp    %rdi,%r12
    5a1a:	75 b4                	jne    59d0 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    5a1c:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5a1f:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5a26:	31 ff                	xor    %edi,%edi
    5a28:	48 c1 e6 05          	shl    $0x5,%rsi
    5a2c:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5a33:	e8 d8 c8 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5a38:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5a3f:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5a46:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    5a4d:	8b 4a 10             	mov    0x10(%rdx),%ecx
    5a50:	8d 69 01             	lea    0x1(%rcx),%ebp
    5a53:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5a56:	75 5b                	jne    5ab3 <barriered_work+0x293>
    5a58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a60:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    5a67:	48 8b 40 40          	mov    0x40(%rax),%rax
    5a6b:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    5a6e:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a76:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5a7a:	48 c1 e7 09          	shl    $0x9,%rdi
    5a7e:	48 03 78 58          	add    0x58(%rax),%rdi
    5a82:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    5a88:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5a8b:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    5a92:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5a99:	74 c5                	je     5a60 <barriered_work+0x240>
    if (modcount != data->thread->protected_state->modcount) {
    5a9b:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    5aa2:	3b 68 10             	cmp    0x10(%rax),%ebp
    5aa5:	74 0c                	je     5ab3 <barriered_work+0x293>
    5aa7:	48 8d 3d 62 17 00 00 	lea    0x1762(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    5aae:	e8 3d c8 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5ab3:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5aba:	31 ff                	xor    %edi,%edi
    5abc:	48 c1 e6 05          	shl    $0x5,%rsi
    5ac0:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5ac7:	48 83 c6 10          	add    $0x10,%rsi
    5acb:	e8 40 c8 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5ad0:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    5ad7:	48 83 c0 01          	add    $0x1,%rax
    5adb:	48 99                	cqto
    5add:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    5ae4:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5aeb:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    5af2:	0f 84 ad 00 00 00    	je     5ba5 <barriered_work+0x385>
    5af8:	48 8d 3d 05 17 00 00 	lea    0x1705(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5aff:	e8 ec c7 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5b04:	0f ae f8             	sfence
}
    5b07:	48 83 c4 18          	add    $0x18,%rsp
    5b0b:	31 c0                	xor    %eax,%eax
    5b0d:	5b                   	pop    %rbx
    5b0e:	5d                   	pop    %rbp
    5b0f:	41 5c                	pop    %r12
    5b11:	41 5d                	pop    %r13
    5b13:	41 5e                	pop    %r14
    5b15:	41 5f                	pop    %r15
    5b17:	c3                   	ret
    5b18:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5b20:	49 89 f5             	mov    %rsi,%r13
    5b23:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b2a:	4c 89 e7             	mov    %r12,%rdi
    5b2d:	49 d1 ed             	shr    %r13
    5b30:	49 c1 e5 04          	shl    $0x4,%r13
    5b34:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5b39:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5b3d:	41 83 e5 10          	and    $0x10,%r13d
    5b41:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5b45:	74 11                	je     5b58 <barriered_work+0x338>
          them->messages[them->messages_count++] = data->message; 
    5b47:	48 83 c7 10          	add    $0x10,%rdi
    5b4b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5b50:	49 39 ff             	cmp    %rdi,%r15
    5b53:	74 13                	je     5b68 <barriered_work+0x348>
    5b55:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5b58:	0f 11 07             	movups %xmm0,(%rdi)
    5b5b:	48 83 c7 20          	add    $0x20,%rdi
    5b5f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5b63:	49 39 ff             	cmp    %rdi,%r15
    5b66:	75 f0                	jne    5b58 <barriered_work+0x338>
    5b68:	48 89 f7             	mov    %rsi,%rdi
    5b6b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5b6f:	4c 01 df             	add    %r11,%rdi
    5b72:	40 f6 c6 01          	test   $0x1,%sil
    5b76:	0f 84 cc fd ff ff    	je     5948 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    5b7c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b83:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5b87:	e9 bc fd ff ff       	jmp    5948 <barriered_work+0x128>
    5b8c:	0f 1f 40 00          	nopl   0x0(%rax)
    5b90:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5b98:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5ba0:	e9 7c fd ff ff       	jmp    5921 <barriered_work+0x101>
      for (int n = 0 ; n < data->thread_count; n++) {
    5ba5:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    5bac:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5bb2:	31 d2                	xor    %edx,%edx
    5bb4:	48 89 0c 24          	mov    %rcx,(%rsp)
    5bb8:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    5bbf:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5bc4:	85 c0                	test   %eax,%eax
    5bc6:	0f 8e 38 ff ff ff    	jle    5b04 <barriered_work+0x2e4>
    5bcc:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5bd0:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5bd6:	0f 84 af 00 00 00    	je     5c8b <barriered_work+0x46b>
        struct Data *them = data->mailboxes[n].higher;
    5bdc:	49 89 d1             	mov    %rdx,%r9
    5bdf:	49 c1 e1 05          	shl    $0x5,%r9
    5be3:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    5bea:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    5bee:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5bf2:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5bf6:	4d 39 d8             	cmp    %r11,%r8
    5bf9:	0f 8e 83 00 00 00    	jle    5c82 <barriered_work+0x462>
    5bff:	4c 89 c6             	mov    %r8,%rsi
    5c02:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5c09:	4d 8b 71 10          	mov    0x10(%r9),%r14
    5c0d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5c10:	49 8b 0a             	mov    (%r10),%rcx
    5c13:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5c17:	48 83 f8 02          	cmp    $0x2,%rax
    5c1b:	0f 86 ef 00 00 00    	jbe    5d10 <barriered_work+0x4f0>
    5c21:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5c29:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5c31:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5c35:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5c39:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5c3d:	73 61                	jae    5ca0 <barriered_work+0x480>
    5c3f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5c44:	4d 39 fc             	cmp    %r15,%r12
    5c47:	73 57                	jae    5ca0 <barriered_work+0x480>
    5c49:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5c4d:	48 01 cf             	add    %rcx,%rdi
    5c50:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5c57:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5c5b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5c5f:	49 39 fb             	cmp    %rdi,%r11
    5c62:	75 ec                	jne    5c50 <barriered_work+0x430>
    5c64:	0f 1f 40 00          	nopl   0x0(%rax)
    5c68:	48 01 f5             	add    %rsi,%rbp
    5c6b:	4c 01 f6             	add    %r14,%rsi
    5c6e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5c75:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5c79:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5c7d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5c82:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5c85:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5c8b:	48 83 c2 01          	add    $0x1,%rdx
    5c8f:	39 d0                	cmp    %edx,%eax
    5c91:	0f 8f 39 ff ff ff    	jg     5bd0 <barriered_work+0x3b0>
    5c97:	e9 68 fe ff ff       	jmp    5b04 <barriered_work+0x2e4>
    5c9c:	0f 1f 40 00          	nopl   0x0(%rax)
    5ca0:	49 89 f5             	mov    %rsi,%r13
    5ca3:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5caa:	4c 89 e7             	mov    %r12,%rdi
    5cad:	49 d1 ed             	shr    %r13
    5cb0:	49 c1 e5 04          	shl    $0x4,%r13
    5cb4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5cb9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5cbd:	41 83 e5 10          	and    $0x10,%r13d
    5cc1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5cc5:	74 11                	je     5cd8 <barriered_work+0x4b8>
          them->messages[them->messages_count++] = data->message; 
    5cc7:	48 83 c7 10          	add    $0x10,%rdi
    5ccb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5cd0:	4c 39 ff             	cmp    %r15,%rdi
    5cd3:	74 13                	je     5ce8 <barriered_work+0x4c8>
    5cd5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5cd8:	0f 11 07             	movups %xmm0,(%rdi)
    5cdb:	48 83 c7 20          	add    $0x20,%rdi
    5cdf:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5ce3:	4c 39 ff             	cmp    %r15,%rdi
    5ce6:	75 f0                	jne    5cd8 <barriered_work+0x4b8>
    5ce8:	48 89 f7             	mov    %rsi,%rdi
    5ceb:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5cef:	4c 01 df             	add    %r11,%rdi
    5cf2:	40 f6 c6 01          	test   $0x1,%sil
    5cf6:	0f 84 6c ff ff ff    	je     5c68 <barriered_work+0x448>
          them->messages[them->messages_count++] = data->message; 
    5cfc:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5d03:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5d07:	e9 5c ff ff ff       	jmp    5c68 <barriered_work+0x448>
    5d0c:	0f 1f 40 00          	nopl   0x0(%rax)
    5d10:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5d18:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5d20:	e9 24 ff ff ff       	jmp    5c49 <barriered_work+0x429>
    5d25:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005d30 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5d30:	f3 0f 1e fa          	endbr64
    5d34:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5d38:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5d3f:	48 8b 80 c0 00 00 00 	mov    0xc0(%rax),%rax
    5d46:	48 63 10             	movslq (%rax),%rdx
    5d49:	85 d2                	test   %edx,%edx
    5d4b:	7e 31                	jle    5d7e <barriered_work_ingest+0x4e>
    5d4d:	48 8b 40 08          	mov    0x8(%rax),%rax
    5d51:	48 c1 e2 04          	shl    $0x4,%rdx
    5d55:	48 01 c2             	add    %rax,%rdx
    5d58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    if (data->thread->buffers->buffer[x].available == 1) {
    5d60:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5d64:	75 0f                	jne    5d75 <barriered_work_ingest+0x45>
      data->ingest_count++;
    5d66:	48 83 87 60 01 00 00 01 	addq   $0x1,0x160(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5d6e:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5d75:	48 83 c0 10          	add    $0x10,%rax
    5d79:	48 39 d0             	cmp    %rdx,%rax
    5d7c:	75 e2                	jne    5d60 <barriered_work_ingest+0x30>
  asm volatile ("sfence" ::: "memory");
    5d7e:	0f ae f8             	sfence
  barriered_work(data);
    5d81:	e8 9a fa ff ff       	call   5820 <barriered_work>
}
    5d86:	31 c0                	xor    %eax,%eax
    5d88:	48 83 c4 08          	add    $0x8,%rsp
    5d8c:	c3                   	ret
    5d8d:	0f 1f 00             	nopl   (%rax)

0000000000005d90 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5d90:	f3 0f 1e fa          	endbr64
}
    5d94:	31 c0                	xor    %eax,%eax
    5d96:	c3                   	ret
    5d97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005da0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5da0:	f3 0f 1e fa          	endbr64
    5da4:	31 c0                	xor    %eax,%eax
    5da6:	c3                   	ret
    5da7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005db0 <after>:
int after(struct timespec left, struct timespec right) {
    5db0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5db4:	31 c0                	xor    %eax,%eax
    5db6:	48 39 d7             	cmp    %rdx,%rdi
    5db9:	7e 08                	jle    5dc3 <after+0x13>
    5dbb:	31 c0                	xor    %eax,%eax
    5dbd:	48 39 ce             	cmp    %rcx,%rsi
    5dc0:	0f 9f c0             	setg   %al
}
    5dc3:	c3                   	ret
    5dc4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5dcf:	90                   	nop

0000000000005dd0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5dd0:	f3 0f 1e fa          	endbr64
    5dd4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5dd9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5dde:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5de0:	48 39 d7             	cmp    %rdx,%rdi
    5de3:	7f 18                	jg     5dfd <within+0x2d>
    5de5:	4d 39 d8             	cmp    %r11,%r8
    5de8:	0f 9e c2             	setle  %dl
    5deb:	48 39 ce             	cmp    %rcx,%rsi
    5dee:	0f 9e c0             	setle  %al
    5df1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5df3:	31 c0                	xor    %eax,%eax
    5df5:	4d 39 d1             	cmp    %r10,%r9
    5df8:	0f 9e c0             	setle  %al
    5dfb:	21 d0                	and    %edx,%eax
}
    5dfd:	c3                   	ret
    5dfe:	66 90                	xchg   %ax,%ax

0000000000005e00 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5e00:	f3 0f 1e fa          	endbr64
    5e04:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5e09:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5e0e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5e13:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5e18:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5e1d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5e22:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5e27:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5e2c:	48 39 fe             	cmp    %rdi,%rsi
    5e2f:	7d 2f                	jge    5e60 <overlap+0x60>
    5e31:	48 39 ca             	cmp    %rcx,%rdx
    5e34:	7d 62                	jge    5e98 <overlap+0x98>
    5e36:	4d 39 da             	cmp    %r11,%r10
    5e39:	7d 0e                	jge    5e49 <overlap+0x49>
    return 1;
    5e3b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e40:	4d 39 c1             	cmp    %r8,%r9
    5e43:	0f 8c 7f 00 00 00    	jl     5ec8 <overlap+0xc8>
  return 0;
    5e49:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e4b:	4d 39 c1             	cmp    %r8,%r9
    5e4e:	7f 4c                	jg     5e9c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e50:	31 c0                	xor    %eax,%eax
    5e52:	4d 39 da             	cmp    %r11,%r10
    5e55:	0f 9e c0             	setle  %al
    5e58:	c3                   	ret
    5e59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5e60:	7e 4e                	jle    5eb0 <overlap+0xb0>
    5e62:	48 39 ca             	cmp    %rcx,%rdx
    5e65:	7f 39                	jg     5ea0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e67:	75 31                	jne    5e9a <overlap+0x9a>
    5e69:	4d 39 c1             	cmp    %r8,%r9
    5e6c:	7c 2c                	jl     5e9a <overlap+0x9a>
    return 1;
    5e6e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e73:	4d 39 da             	cmp    %r11,%r10
    5e76:	7d 24                	jge    5e9c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e78:	48 39 ca             	cmp    %rcx,%rdx
    5e7b:	0f 94 c2             	sete   %dl
    5e7e:	48 39 fe             	cmp    %rdi,%rsi
    5e81:	0f 94 c0             	sete   %al
    5e84:	21 c2                	and    %eax,%edx
    5e86:	31 c0                	xor    %eax,%eax
    5e88:	4d 39 c1             	cmp    %r8,%r9
    5e8b:	0f 94 c0             	sete   %al
    5e8e:	21 d0                	and    %edx,%eax
    5e90:	c3                   	ret
    5e91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5e98:	74 af                	je     5e49 <overlap+0x49>
  return 0;
    5e9a:	31 c0                	xor    %eax,%eax
}
    5e9c:	c3                   	ret
    5e9d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5ea0:	4d 39 da             	cmp    %r11,%r10
    5ea3:	7e c4                	jle    5e69 <overlap+0x69>
    return 1;
    5ea5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5eaa:	4d 39 c1             	cmp    %r8,%r9
    5ead:	7e ba                	jle    5e69 <overlap+0x69>
    5eaf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5eb0:	48 39 ca             	cmp    %rcx,%rdx
    5eb3:	7c 94                	jl     5e49 <overlap+0x49>
    5eb5:	4d 39 c1             	cmp    %r8,%r9
    5eb8:	7d b4                	jge    5e6e <overlap+0x6e>
    5eba:	48 39 ca             	cmp    %rcx,%rdx
    5ebd:	74 91                	je     5e50 <overlap+0x50>
    5ebf:	eb d9                	jmp    5e9a <overlap+0x9a>
    5ec1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5ec8:	c3                   	ret
    5ec9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005ed0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5ed0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5ed4:	85 f6                	test   %esi,%esi
    5ed6:	0f 8e 44 03 00 00    	jle    6220 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    5edc:	41 57                	push   %r15
    5ede:	41 89 f7             	mov    %esi,%r15d
    5ee1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5ee3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5ee6:	41 55                	push   %r13
    5ee8:	41 54                	push   %r12
    5eea:	55                   	push   %rbp
    5eeb:	53                   	push   %rbx
    5eec:	48 8d 5f 58          	lea    0x58(%rdi),%rbx
    5ef0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5ef4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5ef9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5efe:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    5f01:	45 39 e6             	cmp    %r12d,%r14d
    5f04:	0f 84 4e 02 00 00    	je     6158 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5f0a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5f0f:	8b 50 08             	mov    0x8(%rax),%edx
    5f12:	85 d2                	test   %edx,%edx
    5f14:	0f 8e 3e 02 00 00    	jle    6158 <verify+0x288>
    5f1a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    5f1f:	31 c9                	xor    %ecx,%ecx
    5f21:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    5f26:	31 c0                	xor    %eax,%eax
    5f28:	44 89 f2             	mov    %r14d,%edx
    5f2b:	bf 01 00 00 00       	mov    $0x1,%edi
    5f30:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5f35:	48 8d 35 e4 12 00 00 	lea    0x12e4(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    5f3c:	e8 0f c5 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5f41:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5f46:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    5f4b:	8b 40 08             	mov    0x8(%rax),%eax
    5f4e:	85 c0                	test   %eax,%eax
    5f50:	0f 8e e6 01 00 00    	jle    613c <verify+0x26c>
    5f56:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5f59:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    5f5e:	31 db                	xor    %ebx,%ebx
    5f60:	48 c1 e0 09          	shl    $0x9,%rax
    5f64:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    5f69:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5f6e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5f73:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    5f78:	4c 8b 20             	mov    (%rax),%r12
    5f7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5f80:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    5f85:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5f8a:	49 89 de             	mov    %rbx,%r14
    5f8d:	48 8d 35 a1 12 00 00 	lea    0x12a1(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5f94:	49 c1 e6 09          	shl    $0x9,%r14
    5f98:	bf 01 00 00 00       	mov    $0x1,%edi
    5f9d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5fa1:	4b 8b 8c 3c 58 01 00 00 	mov    0x158(%r12,%r15,1),%rcx
    5fa9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    5fae:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    5fb6:	31 c0                	xor    %eax,%eax
    5fb8:	e8 93 c4 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5fbd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5fc2:	4c 8b 20             	mov    (%rax),%r12
    5fc5:	4b 83 bc 3c 58 01 00 00 00 	cmpq   $0x0,0x158(%r12,%r15,1)
    5fce:	0f 8e 47 01 00 00    	jle    611b <verify+0x24b>
    5fd4:	4c 03 75 00          	add    0x0(%rbp),%r14
    5fd8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5fdd:	ba 01 00 00 00       	mov    $0x1,%edx
    5fe2:	4d 89 f5             	mov    %r14,%r13
    5fe5:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    5fec:	4d 85 f6             	test   %r14,%r14
    5fef:	0f 8e 21 01 00 00    	jle    6116 <verify+0x246>
    5ff5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5ff8:	48 89 d5             	mov    %rdx,%rbp
    5ffb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6000:	31 db                	xor    %ebx,%ebx
    6002:	4d 89 f2             	mov    %r14,%r10
    6005:	48 c1 e5 05          	shl    $0x5,%rbp
    6009:	48 83 ed 20          	sub    $0x20,%rbp
    600d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6011:	49 89 ee             	mov    %rbp,%r14
    6014:	48 89 dd             	mov    %rbx,%rbp
    6017:	48 89 d3             	mov    %rdx,%rbx
    601a:	eb 31                	jmp    604d <verify+0x17d>
    601c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6020:	4c 39 c2             	cmp    %r8,%rdx
    6023:	0f 8d 57 01 00 00    	jge    6180 <verify+0x2b0>
    6029:	4c 39 df             	cmp    %r11,%rdi
    602c:	7e 05                	jle    6033 <verify+0x163>
    602e:	49 39 c1             	cmp    %rax,%r9
    6031:	7c 75                	jl     60a8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6033:	4c 39 df             	cmp    %r11,%rdi
    6036:	0f 8d ab 01 00 00    	jge    61e7 <verify+0x317>
    603c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6040:	48 83 c5 01          	add    $0x1,%rbp
    6044:	49 39 ea             	cmp    %rbp,%r10
    6047:	0f 8e a9 00 00 00    	jle    60f6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    604d:	49 8b 97 48 01 00 00 	mov    0x148(%r15),%rdx
    6054:	48 89 e8             	mov    %rbp,%rax
    6057:	48 c1 e0 05          	shl    $0x5,%rax
    605b:	49 03 85 48 01 00 00 	add    0x148(%r13),%rax
    6062:	4c 01 f2             	add    %r14,%rdx
    6065:	48 8b 08             	mov    (%rax),%rcx
    6068:	48 8b 78 10          	mov    0x10(%rax),%rdi
    606c:	48 8b 32             	mov    (%rdx),%rsi
    606f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6073:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6077:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    607b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    607f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6083:	48 39 f1             	cmp    %rsi,%rcx
    6086:	7c 98                	jl     6020 <verify+0x150>
    6088:	0f 8e 42 01 00 00    	jle    61d0 <verify+0x300>
    608e:	4c 39 c2             	cmp    %r8,%rdx
    6091:	0f 8f f9 00 00 00    	jg     6190 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6097:	75 a7                	jne    6040 <verify+0x170>
    6099:	4c 39 df             	cmp    %r11,%rdi
    609c:	7f a2                	jg     6040 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    609e:	49 39 c1             	cmp    %rax,%r9
    60a1:	7c 9d                	jl     6040 <verify+0x170>
    60a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    60a8:	49 89 c1             	mov    %rax,%r9
    60ab:	48 89 f9             	mov    %rdi,%rcx
    60ae:	48 89 f2             	mov    %rsi,%rdx
    60b1:	bf 01 00 00 00       	mov    $0x1,%edi
    60b6:	48 8d 35 cb 13 00 00 	lea    0x13cb(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    60bd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60bf:	48 83 c5 01          	add    $0x1,%rbp
    60c3:	e8 88 c3 ff ff       	call   2450 <__printf_chk@plt>
    60c8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    60cd:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    60d2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60d5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60da:	4d 8b 95 58 01 00 00 	mov    0x158(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60e1:	4c 8b 20             	mov    (%rax),%r12
    60e4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    60e9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60ed:	49 39 ea             	cmp    %rbp,%r10
    60f0:	0f 8f 57 ff ff ff    	jg     604d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60f6:	48 89 da             	mov    %rbx,%rdx
    60f9:	49 3b 9f 58 01 00 00 	cmp    0x158(%r15),%rbx
    6100:	7d 14                	jge    6116 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6102:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    6109:	48 83 c2 01          	add    $0x1,%rdx
    610d:	4d 85 f6             	test   %r14,%r14
    6110:	0f 8f e2 fe ff ff    	jg     5ff8 <verify+0x128>
    6116:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    611b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6120:	48 83 c3 01          	add    $0x1,%rbx
    6124:	39 58 08             	cmp    %ebx,0x8(%rax)
    6127:	0f 8f 53 fe ff ff    	jg     5f80 <verify+0xb0>
    612d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6132:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6137:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    613c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6141:	48 83 c1 01          	add    $0x1,%rcx
    6145:	39 48 08             	cmp    %ecx,0x8(%rax)
    6148:	0f 8f d8 fd ff ff    	jg     5f26 <verify+0x56>
    614e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6153:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6158:	48 81 44 24 10 40 01 00 00 	addq   $0x140,0x10(%rsp)
    6161:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6166:	41 39 c7             	cmp    %eax,%r15d
    6169:	0f 84 86 00 00 00    	je     61f5 <verify+0x325>
    616f:	41 89 c4             	mov    %eax,%r12d
    6172:	e9 8a fd ff ff       	jmp    5f01 <verify+0x31>
    6177:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6180:	0f 85 ba fe ff ff    	jne    6040 <verify+0x170>
    6186:	e9 a8 fe ff ff       	jmp    6033 <verify+0x163>
    618b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6190:	49 39 c1             	cmp    %rax,%r9
    6193:	7e 09                	jle    619e <verify+0x2ce>
    6195:	4c 39 df             	cmp    %r11,%rdi
    6198:	0f 8c 0a ff ff ff    	jl     60a8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    619e:	4c 39 df             	cmp    %r11,%rdi
    61a1:	0f 8f 99 fe ff ff    	jg     6040 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    61a7:	49 39 c1             	cmp    %rax,%r9
    61aa:	0f 8d f8 fe ff ff    	jge    60a8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    61b0:	48 39 f1             	cmp    %rsi,%rcx
    61b3:	0f 85 87 fe ff ff    	jne    6040 <verify+0x170>
    61b9:	4c 39 c2             	cmp    %r8,%rdx
    61bc:	0f 85 7e fe ff ff    	jne    6040 <verify+0x170>
    61c2:	4c 39 df             	cmp    %r11,%rdi
    61c5:	0f 84 dd fe ff ff    	je     60a8 <verify+0x1d8>
    61cb:	e9 70 fe ff ff       	jmp    6040 <verify+0x170>
    61d0:	4c 39 c2             	cmp    %r8,%rdx
    61d3:	0f 8c 5a fe ff ff    	jl     6033 <verify+0x163>
    61d9:	4c 39 df             	cmp    %r11,%rdi
    61dc:	7e c9                	jle    61a7 <verify+0x2d7>
    61de:	4c 39 c2             	cmp    %r8,%rdx
    61e1:	0f 85 59 fe ff ff    	jne    6040 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    61e7:	49 39 c1             	cmp    %rax,%r9
    61ea:	0f 8f 50 fe ff ff    	jg     6040 <verify+0x170>
    61f0:	e9 b3 fe ff ff       	jmp    60a8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    61f5:	48 81 44 24 18 40 01 00 00 	addq   $0x140,0x18(%rsp)
    61fe:	41 8d 46 01          	lea    0x1(%r14),%eax
    6202:	45 39 e6             	cmp    %r12d,%r14d
    6205:	74 08                	je     620f <verify+0x33f>
    6207:	41 89 c6             	mov    %eax,%r14d
    620a:	e9 ea fc ff ff       	jmp    5ef9 <verify+0x29>
}
    620f:	48 83 c4 58          	add    $0x58,%rsp
    6213:	31 c0                	xor    %eax,%eax
    6215:	5b                   	pop    %rbx
    6216:	5d                   	pop    %rbp
    6217:	41 5c                	pop    %r12
    6219:	41 5d                	pop    %r13
    621b:	41 5e                	pop    %r14
    621d:	41 5f                	pop    %r15
    621f:	c3                   	ret
    6220:	31 c0                	xor    %eax,%eax
    6222:	c3                   	ret

Disassembly of section .fini:

0000000000006224 <_fini>:
    6224:	f3 0f 1e fa          	endbr64
    6228:	48 83 ec 08          	sub    $0x8,%rsp
    622c:	48 83 c4 08          	add    $0x8,%rsp
    6230:	c3                   	ret
