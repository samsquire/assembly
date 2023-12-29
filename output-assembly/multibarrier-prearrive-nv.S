
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
    2605:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
    260c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2615:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    261a:	48 8d 05 3f 11 00 00 	lea    0x113f(%rip),%rax        # 3760 <barriered_reset>
    2621:	66 48 0f 6e e8       	movq   %rax,%xmm5
    2626:	0f 16 2d 4b 76 00 00 	movhps 0x764b(%rip),%xmm5        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    262d:	0f 29 6c 24 40       	movaps %xmm5,0x40(%rsp)
    2632:	e8 b9 fc ff ff       	call   22f0 <puts@plt>
    2637:	bf 0a 00 00 00       	mov    $0xa,%edi
    263c:	e8 8f fc ff ff       	call   22d0 <putchar@plt>
    2641:	48 8d 3d f6 4b 00 00 	lea    0x4bf6(%rip),%rdi        # 723e <_IO_stdin_used+0x23e>
    2648:	e8 a3 fc ff ff       	call   22f0 <puts@plt>
    264d:	ba 02 00 00 00       	mov    $0x2,%edx
    2652:	48 8d 35 01 4c 00 00 	lea    0x4c01(%rip),%rsi        # 725a <_IO_stdin_used+0x25a>
    2659:	31 c0                	xor    %eax,%eax
    265b:	bf 01 00 00 00       	mov    $0x1,%edi
    2660:	e8 eb fd ff ff       	call   2450 <__printf_chk@plt>
    2665:	ba 08 00 00 00       	mov    $0x8,%edx
    266a:	48 8d 35 03 4c 00 00 	lea    0x4c03(%rip),%rsi        # 7274 <_IO_stdin_used+0x274>
    2671:	31 c0                	xor    %eax,%eax
    2673:	bf 01 00 00 00       	mov    $0x1,%edi
    2678:	e8 d3 fd ff ff       	call   2450 <__printf_chk@plt>
    267d:	ba 01 00 00 00       	mov    $0x1,%edx
    2682:	48 8d 35 ff 4b 00 00 	lea    0x4bff(%rip),%rsi        # 7288 <_IO_stdin_used+0x288>
    2689:	31 c0                	xor    %eax,%eax
    268b:	bf 01 00 00 00       	mov    $0x1,%edi
    2690:	e8 bb fd ff ff       	call   2450 <__printf_chk@plt>
    2695:	ba 01 00 00 00       	mov    $0x1,%edx
    269a:	48 8d 35 f8 4b 00 00 	lea    0x4bf8(%rip),%rsi        # 7299 <_IO_stdin_used+0x299>
    26a1:	31 c0                	xor    %eax,%eax
    26a3:	bf 01 00 00 00       	mov    $0x1,%edi
    26a8:	e8 a3 fd ff ff       	call   2450 <__printf_chk@plt>
    26ad:	ba 04 00 00 00       	mov    $0x4,%edx
    26b2:	48 8d 35 f8 4b 00 00 	lea    0x4bf8(%rip),%rsi        # 72b1 <_IO_stdin_used+0x2b1>
    26b9:	31 c0                	xor    %eax,%eax
    26bb:	bf 01 00 00 00       	mov    $0x1,%edi
    26c0:	e8 8b fd ff ff       	call   2450 <__printf_chk@plt>
    26c5:	ba 01 00 00 00       	mov    $0x1,%edx
    26ca:	48 8d 35 4f 4e 00 00 	lea    0x4e4f(%rip),%rsi        # 7520 <_IO_stdin_used+0x520>
    26d1:	31 c0                	xor    %eax,%eax
    26d3:	bf 01 00 00 00       	mov    $0x1,%edi
    26d8:	e8 73 fd ff ff       	call   2450 <__printf_chk@plt>
    26dd:	ba 01 00 00 00       	mov    $0x1,%edx
    26e2:	48 8d 35 67 4e 00 00 	lea    0x4e67(%rip),%rsi        # 7550 <_IO_stdin_used+0x550>
    26e9:	31 c0                	xor    %eax,%eax
    26eb:	bf 01 00 00 00       	mov    $0x1,%edi
    26f0:	e8 5b fd ff ff       	call   2450 <__printf_chk@plt>
    26f5:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    26fa:	48 8d 35 cc 4b 00 00 	lea    0x4bcc(%rip),%rsi        # 72cd <_IO_stdin_used+0x2cd>
    2701:	31 c0                	xor    %eax,%eax
    2703:	bf 01 00 00 00       	mov    $0x1,%edi
    2708:	e8 43 fd ff ff       	call   2450 <__printf_chk@plt>
    270d:	ba 05 00 00 00       	mov    $0x5,%edx
    2712:	48 8d 35 ce 4b 00 00 	lea    0x4bce(%rip),%rsi        # 72e7 <_IO_stdin_used+0x2e7>
    2719:	31 c0                	xor    %eax,%eax
    271b:	bf 01 00 00 00       	mov    $0x1,%edi
    2720:	e8 2b fd ff ff       	call   2450 <__printf_chk@plt>
    2725:	48 8d 3d a2 49 00 00 	lea    0x49a2(%rip),%rdi        # 70ce <_IO_stdin_used+0xce>
    272c:	e8 bf fb ff ff       	call   22f0 <puts@plt>
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    2731:	be 18 00 00 00       	mov    $0x18,%esi
    2736:	bf 02 00 00 00       	mov    $0x2,%edi
    273b:	e8 60 fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2740:	be b0 00 00 00       	mov    $0xb0,%esi
    2745:	bf 08 00 00 00       	mov    $0x8,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    274a:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    274f:	e8 4c fc ff ff       	call   23a0 <calloc@plt>
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  int buffers_required = thread_count * barrier_count;
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2754:	be 10 00 00 00       	mov    $0x10,%esi
    2759:	bf 04 00 00 00       	mov    $0x4,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    275e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2763:	e8 38 fc ff ff       	call   23a0 <calloc@plt>
    2768:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    276d:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2772:	49 89 c5             	mov    %rax,%r13
  int snapshot_limit = 10;
  for (int x = 0 ; x < buffers_required; x++) {
    2775:	48 8d 68 40          	lea    0x40(%rax),%rbp
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2779:	49 89 c4             	mov    %rax,%r12
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    277c:	be 20 00 00 00       	mov    $0x20,%esi
    buffers[x].count = buffer_size;
    2781:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2789:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    278e:	49 83 c4 10          	add    $0x10,%r12
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2792:	e8 09 fc ff ff       	call   23a0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2797:	be 20 00 00 00       	mov    $0x20,%esi
    279c:	bf 0a 00 00 00       	mov    $0xa,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27a1:	49 89 44 24 f8       	mov    %rax,-0x8(%r12)
    27a6:	48 89 c3             	mov    %rax,%rbx
      buffers[x].buffer[y].available = 0;
    27a9:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    27b0:	c7 40 18 0a 00 00 00 	movl   $0xa,0x18(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    27b7:	e8 e4 fb ff ff       	call   23a0 <calloc@plt>
    27bc:	48 89 43 10          	mov    %rax,0x10(%rbx)
  for (int x = 0 ; x < buffers_required; x++) {
    27c0:	4c 39 e5             	cmp    %r12,%rbp
    27c3:	75 b7                	jne    277c <main+0x18c>
    27c5:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    27ca:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
  for (int x = 0 ; x < total_threads ; x++) {
    27cf:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
  int curcpu = 0;
    27d7:	c7 44 24 50 00 00 00 00 	movl   $0x0,0x50(%rsp)
    27df:	48 8d 68 e8          	lea    -0x18(%rax),%rbp
            thread_data[x].tasks[y].run = barriered_steal; 
          } else {
            thread_data[x].tasks[y].run = barriered_nulltask; 
          }
          */
          thread_data[x].tasks[y].run = barriered_work; 
    27e3:	4c 89 74 24 68       	mov    %r14,0x68(%rsp)
    27e8:	49 89 ec             	mov    %rbp,%r12
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27eb:	be 08 00 00 00       	mov    $0x8,%esi
    27f0:	bf 02 00 00 00       	mov    $0x2,%edi
    27f5:	e8 a6 fb ff ff       	call   23a0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27fa:	bf 01 00 00 00       	mov    $0x1,%edi
    27ff:	be 80 00 00 00       	mov    $0x80,%esi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2804:	48 89 c3             	mov    %rax,%rbx
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2807:	e8 94 fb ff ff       	call   23a0 <calloc@plt>
    if (x % 2 == 1) {
    280c:	8b 7c 24 20          	mov    0x20(%rsp),%edi
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2810:	48 89 c5             	mov    %rax,%rbp
    if (x % 2 == 1) {
    2813:	89 f8                	mov    %edi,%eax
    2815:	41 89 fd             	mov    %edi,%r13d
      other = (x + 1) % total_threads;
    2818:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
    281b:	83 e0 01             	and    $0x1,%eax
      other = (x + 1) % total_threads;
    281e:	89 7c 24 20          	mov    %edi,0x20(%rsp)
    if (x % 2 == 1) {
    2822:	85 c0                	test   %eax,%eax
    2824:	0f 84 35 0c 00 00    	je     345f <main+0xe6f>
      my_thread_data[1] = &thread_data[x]; 
    282a:	4c 89 73 08          	mov    %r14,0x8(%rbx)
      other = abs(x - 1) % total_threads;
    282e:	41 8d 45 ff          	lea    -0x1(%r13),%eax
    2832:	4d 89 f0             	mov    %r14,%r8
    2835:	44 89 ea             	mov    %r13d,%edx
      my_thread_data[0] = &thread_data[other]; 
    2838:	49 8d 8e 50 ff ff ff 	lea    -0xb0(%r14),%rcx
      other = abs(x - 1) % total_threads;
    283f:	41 89 c7             	mov    %eax,%r15d
    2842:	31 c0                	xor    %eax,%eax
      thread_data[x].thread_index = 1;
    2844:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
      my_thread_data[0] = &thread_data[other]; 
    284b:	48 89 0b             	mov    %rcx,(%rbx)
    284e:	48 8d 35 a6 4a 00 00 	lea    0x4aa6(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
    2855:	bf 01 00 00 00       	mov    $0x1,%edi
    285a:	e8 f1 fb ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    285f:	49 8d 86 b0 00 00 00 	lea    0xb0(%r14),%rax
    2866:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    286b:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    2870:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2875:	4d 89 66 38          	mov    %r12,0x38(%r14)
    2879:	45 8b 06             	mov    (%r14),%r8d
    287c:	44 89 f9             	mov    %r15d,%ecx
    287f:	44 89 ea             	mov    %r13d,%edx
    2882:	48 8d 35 ef 4c 00 00 	lea    0x4cef(%rip),%rsi        # 7578 <_IO_stdin_used+0x578>
    2889:	bf 01 00 00 00       	mov    $0x1,%edi
    288e:	31 c0                	xor    %eax,%eax
    2890:	e8 bb fb ff ff       	call   2450 <__printf_chk@plt>
    2895:	8b 4c 24 50          	mov    0x50(%rsp),%ecx
    2899:	31 c0                	xor    %eax,%eax
    289b:	44 89 ea             	mov    %r13d,%edx
    thread_data[x].other = other;
    289e:	45 89 be a8 00 00 00 	mov    %r15d,0xa8(%r14)
    28a5:	48 8d 35 fc 4c 00 00 	lea    0x4cfc(%rip),%rsi        # 75a8 <_IO_stdin_used+0x5a8>
    28ac:	bf 01 00 00 00       	mov    $0x1,%edi
    28b1:	e8 9a fb ff ff       	call   2450 <__printf_chk@plt>
      if (x < thread_count) {
    28b6:	41 83 fd 01          	cmp    $0x1,%r13d
    28ba:	0f 86 ec 0b 00 00    	jbe    34ac <main+0xebc>
          CPU_SET(j, sendercpu);
    28c0:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
    thread_data[x].thread_count = 2;
    28c8:	48 8b 05 d1 51 00 00 	mov    0x51d1(%rip),%rax        # 7aa0 <_IO_stdin_used+0xaa0>
    thread_data[x].threads = my_thread_data;
    28cf:	49 89 5e 10          	mov    %rbx,0x10(%r14)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28d3:	31 db                	xor    %ebx,%ebx
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28d5:	be 10 00 00 00       	mov    $0x10,%esi
    thread_data[x].cpu_set = sendercpu;
    28da:	49 89 ae a0 00 00 00 	mov    %rbp,0xa0(%r14)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28e1:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].real_thread_index = x;
    28e6:	45 89 6e 04          	mov    %r13d,0x4(%r14)
    thread_data[x].thread_count = 2;
    28ea:	49 89 46 18          	mov    %rax,0x18(%r14)
    thread_data[x].task_count = total_barrier_count;
    28ee:	41 c7 46 30 03 00 00 00 	movl   $0x3,0x30(%r14)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28f6:	e8 a5 fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28fb:	be 10 00 00 00       	mov    $0x10,%esi
    2900:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2905:	49 89 46 58          	mov    %rax,0x58(%r14)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2909:	e8 92 fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    290e:	be 28 00 00 00       	mov    $0x28,%esi
    2913:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    2918:	66 0f 6f 15 60 51 00 00 	movdqa 0x5160(%rip),%xmm2        # 7a80 <_IO_stdin_used+0xa80>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2920:	49 89 46 60          	mov    %rax,0x60(%r14)
    thread_data[x].timestamp_count = 0;
    2924:	41 0f 11 56 70       	movups %xmm2,0x70(%r14)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2929:	e8 72 fa ff ff       	call   23a0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    292e:	be 00 02 00 00       	mov    $0x200,%esi
    2933:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
    2938:	66 0f 6f 1d 40 51 00 00 	movdqa 0x5140(%rip),%xmm3        # 7a80 <_IO_stdin_used+0xa80>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2940:	49 89 86 80 00 00 00 	mov    %rax,0x80(%r14)
    thread_data[x].task_timestamp_count = 0;
    2947:	41 0f 11 9e 88 00 00 00 	movups %xmm3,0x88(%r14)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    294f:	e8 4c fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    2954:	44 89 6c 24 18       	mov    %r13d,0x18(%rsp)
      thread_data[x].tasks = barriers;
    2959:	49 89 46 28          	mov    %rax,0x28(%r14)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    295d:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks[y].protected = do_protected_write; 
    2960:	4c 63 fb             	movslq %ebx,%r15
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2963:	be 20 00 00 00       	mov    $0x20,%esi
    2968:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    296d:	4d 89 fc             	mov    %r15,%r12
    2970:	48 8d 05 a9 0d 00 00 	lea    0xda9(%rip),%rax        # 3720 <do_protected_write>
    2977:	49 c1 e4 09          	shl    $0x9,%r12
    297b:	4a 8d 2c 22          	lea    (%rdx,%r12,1),%rbp
    297f:	48 89 85 20 01 00 00 	mov    %rax,0x120(%rbp)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2986:	e8 15 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    298b:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
    2990:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    2994:	49 89 c5             	mov    %rax,%r13
    2997:	48 89 85 68 01 00 00 	mov    %rax,0x168(%rbp)
        for (int b = 0 ; b < 2 ; b++) {
    299e:	48 8d 68 40          	lea    0x40(%rax),%rbp
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29a2:	be 08 00 00 00       	mov    $0x8,%esi
    29a7:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    29ac:	49 83 c5 20          	add    $0x20,%r13
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29b0:	e8 eb f9 ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29b5:	be 08 00 00 00       	mov    $0x8,%esi
    29ba:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29bf:	49 89 c4             	mov    %rax,%r12
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29c2:	e8 d9 f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29c7:	be 18 00 00 00       	mov    $0x18,%esi
    29cc:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29d1:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29d4:	e8 c7 f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    29d9:	66 0f 6f 05 af 50 00 00 	movdqa 0x50af(%rip),%xmm0        # 7a90 <_IO_stdin_used+0xa90>
          mailboxes[b].higher = &data[1];
    29e1:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29e5:	49 89 45 e0          	mov    %rax,-0x20(%r13)
          mailboxes[b].higher = &data[1];
    29e9:	49 89 75 e8          	mov    %rsi,-0x18(%r13)
          data[0].messages = messages;
    29ed:	4c 89 20             	mov    %r12,(%rax)
          data[1].messages = messages2;
    29f0:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    29f4:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    29f8:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    29fc:	4c 39 ed             	cmp    %r13,%rbp
    29ff:	75 a1                	jne    29a2 <main+0x3b2>
        char *message = malloc(sizeof(char) * 256);
    2a01:	be 01 00 00 00       	mov    $0x1,%esi
    2a06:	bf 00 01 00 00       	mov    $0x100,%edi
    2a0b:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    2a0f:	4c 8b 64 24 08       	mov    0x8(%rsp),%r12
    2a14:	e8 87 f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a19:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a1e:	48 89 c5             	mov    %rax,%rbp
        struct Message *messaged = malloc(sizeof(struct Message));
    2a21:	e8 ea f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a26:	44 8b 44 24 18       	mov    0x18(%rsp),%r8d
    2a2b:	48 89 ef             	mov    %rbp,%rdi
    2a2e:	41 89 d9             	mov    %ebx,%r9d
    2a31:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2a36:	48 8d 0d 8b 4b 00 00 	lea    0x4b8b(%rip),%rcx        # 75c8 <_IO_stdin_used+0x5c8>
    2a3d:	ba 00 01 00 00       	mov    $0x100,%edx
    2a42:	31 c0                	xor    %eax,%eax
    2a44:	be 01 00 00 00       	mov    $0x1,%esi
    2a49:	e8 d2 fa ff ff       	call   2520 <__sprintf_chk@plt>
        messaged->message = message;
    2a4e:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
        messaged->thread_index = thread_data[x].thread_index;
    2a53:	49 63 06             	movslq (%r14),%rax
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a56:	be 20 00 00 00       	mov    $0x20,%esi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a5b:	49 8b 56 28          	mov    0x28(%r14),%rdx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a5f:	bf 63 00 00 00       	mov    $0x63,%edi
        messaged->message = message;
    2a64:	49 89 2a             	mov    %rbp,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a67:	8d 6b 01             	lea    0x1(%rbx),%ebp
        messaged->thread_index = thread_data[x].thread_index;
    2a6a:	49 89 42 08          	mov    %rax,0x8(%r10)
    2a6e:	89 44 24 10          	mov    %eax,0x10(%rsp)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a72:	89 e8                	mov    %ebp,%eax
        messaged->task_index = y;
    2a74:	4d 89 7a 10          	mov    %r15,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a78:	83 e0 01             	and    $0x1,%eax
    2a7b:	4e 8d 3c 22          	lea    (%rdx,%r12,1),%r15
    2a7f:	41 89 87 88 01 00 00 	mov    %eax,0x188(%r15)
        thread_data[x].tasks[y].message = messaged;
    2a86:	4d 89 97 80 01 00 00 	mov    %r10,0x180(%r15)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a8d:	49 c7 87 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%r15)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a98:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a9d:	e8 fe f8 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2aa2:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
        if (y == barrier_count - 1) {
    2aa6:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2aa9:	41 89 1f             	mov    %ebx,(%r15)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2aac:	49 89 87 48 01 00 00 	mov    %rax,0x148(%r15)
        if (y == barrier_count - 1) {
    2ab3:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
        thread_data[x].tasks[y].available = 1;
    2ab8:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2ac2:	49 89 87 38 01 00 00 	mov    %rax,0x138(%r15)
        thread_data[x].tasks[y].sending = 1;
    2ac9:	48 b8 01 00 00 00 02 00 00 00 	movabs $0x200000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2ad3:	49 c7 87 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%r15)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2ade:	41 89 8f 30 01 00 00 	mov    %ecx,0x130(%r15)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2ae5:	4d 89 b7 28 01 00 00 	mov    %r14,0x128(%r15)
        thread_data[x].tasks[y].arrived = 0;
    2aec:	41 c7 87 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r15)
        thread_data[x].tasks[y].thread_count = 2;
    2af7:	41 c7 87 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%r15)
        thread_data[x].tasks[y].sending = 1;
    2b02:	49 89 87 78 01 00 00 	mov    %rax,0x178(%r15)
        if (y == barrier_count - 1) {
    2b09:	74 39                	je     2b44 <main+0x554>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2b0b:	8b 54 24 18          	mov    0x18(%rsp),%edx
    2b0f:	48 8d 35 da 4a 00 00 	lea    0x4ada(%rip),%rsi        # 75f0 <_IO_stdin_used+0x5f0>
    2b16:	bf 01 00 00 00       	mov    $0x1,%edi
    2b1b:	31 c0                	xor    %eax,%eax
    2b1d:	e8 2e f9 ff ff       	call   2450 <__printf_chk@plt>
        } else {
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b22:	49 8b 56 28          	mov    0x28(%r14),%rdx
    2b26:	48 8d 05 83 31 00 00 	lea    0x3183(%rip),%rax        # 5cb0 <barriered_work_ingest>
    2b2d:	4a 89 84 22 18 01 00 00 	mov    %rax,0x118(%rdx,%r12,1)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b35:	83 fd 03             	cmp    $0x3,%ebp
    2b38:	74 22                	je     2b5c <main+0x56c>
    2b3a:	bb 01 00 00 00       	mov    $0x1,%ebx
    2b3f:	e9 1c fe ff ff       	jmp    2960 <main+0x370>
          thread_data[x].tasks[y].run = barriered_work; 
    2b44:	48 8d 05 65 2c 00 00 	lea    0x2c65(%rip),%rax        # 57b0 <barriered_work>
    2b4b:	bb 02 00 00 00       	mov    $0x2,%ebx
    2b50:	49 89 87 18 01 00 00 	mov    %rax,0x118(%r15)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b57:	e9 04 fe ff ff       	jmp    2960 <main+0x370>
            assigned = 1;
            // thread_data[x].tasks[y].run = barriered_work; 
        }
      }
			thread_data[x].buffers_count = buffers_per_thread;
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2b5c:	bf 02 00 00 00       	mov    $0x2,%edi
    2b61:	be 08 00 00 00       	mov    $0x8,%esi
			thread_data[x].buffers_count = buffers_per_thread;
    2b66:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
    2b6b:	41 c7 86 ac 00 00 00 02 00 00 00 	movl   $0x2,0xac(%r14)
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2b76:	e8 25 f8 ff ff       	call   23a0 <calloc@plt>
      for (int b = 0 ; b < buffers_per_thread; b++) {	
        thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2b7b:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
      }
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b80:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    2b85:	66 0f 6f 64 24 40    	movdqa 0x40(%rsp),%xmm4
  for (int x = 0 ; x < total_threads ; x++) {
    2b8b:	4c 8b 64 24 38       	mov    0x38(%rsp),%r12
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2b90:	49 89 46 40          	mov    %rax,0x40(%r14)
        thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2b94:	48 8d 4f 10          	lea    0x10(%rdi),%rcx
    2b98:	48 89 38             	mov    %rdi,(%rax)
  for (int x = 0 ; x < total_threads ; x++) {
    2b9b:	48 83 c7 20          	add    $0x20,%rdi
    2b9f:	83 7c 24 20 08       	cmpl   $0x8,0x20(%rsp)
        thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2ba4:	48 89 48 08          	mov    %rcx,0x8(%rax)
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2ba8:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2bb2:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2bbc:	c7 82 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%rdx)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2bc6:	48 89 82 34 05 00 00 	mov    %rax,0x534(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bcd:	41 8b 06             	mov    (%r14),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2bd0:	4c 89 b2 28 05 00 00 	mov    %r14,0x528(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2bd7:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bdc:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2be2:	c7 82 7c 05 00 00 02 00 00 00 	movl   $0x2,0x57c(%rdx)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2bec:	c7 82 3c 05 00 00 03 00 00 00 	movl   $0x3,0x53c(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2bf6:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2bfb:	0f 11 a2 18 05 00 00 	movups %xmm4,0x518(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2c02:	0f 85 e3 fb ff ff    	jne    27eb <main+0x1fb>
    2c08:	4c 8b 54 24 68       	mov    0x68(%rsp),%r10
    2c0d:	ba 03 00 00 00       	mov    $0x3,%edx
    2c12:	48 8d 35 ff 46 00 00 	lea    0x46ff(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2c19:	31 c0                	xor    %eax,%eax
    2c1b:	bf 01 00 00 00       	mov    $0x1,%edi
    2c20:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2c25:	e8 26 f8 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c2a:	be 08 00 00 00       	mov    $0x8,%esi
    2c2f:	bf 02 00 00 00       	mov    $0x2,%edi
    2c34:	e8 67 f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2c39:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c3e:	be 38 00 00 00       	mov    $0x38,%esi
    2c43:	bf 08 00 00 00       	mov    $0x8,%edi
    my_thread_data[0] = &thread_data[x]; 
    2c48:	49 8d aa 10 02 00 00 	lea    0x210(%r10),%rbp
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c4f:	4c 89 50 08          	mov    %r10,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c53:	4d 8d b2 b0 00 00 00 	lea    0xb0(%r10),%r14
    thread_data[x].threads = my_thread_data;
    2c5a:	49 89 82 20 02 00 00 	mov    %rax,0x220(%r10)
    my_thread_data[0] = &thread_data[x]; 
    2c61:	48 89 28             	mov    %rbp,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c64:	49 8b 42 28          	mov    0x28(%r10),%rax
    thread_data[x].thread_count = 2;
    2c68:	41 c7 82 28 02 00 00 02 00 00 00 	movl   $0x2,0x228(%r10)
    thread_data[x].thread_index = 0;
    2c73:	41 c7 82 10 02 00 00 00 00 00 00 	movl   $0x0,0x210(%r10)
    thread_data[x].task_count = total_barrier_count;
    2c7e:	41 c7 82 40 02 00 00 03 00 00 00 	movl   $0x3,0x240(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2c89:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2c93:	49 8b 82 d8 00 00 00 	mov    0xd8(%r10),%rax
    2c9a:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ca4:	e8 f7 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ca9:	be 38 00 00 00       	mov    $0x38,%esi
    2cae:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cb3:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cb6:	e8 e5 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cbb:	be 38 00 00 00       	mov    $0x38,%esi
    2cc0:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cc5:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cc8:	e8 d3 f6 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ccd:	be 38 00 00 00       	mov    $0x38,%esi
    2cd2:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cd7:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cdc:	e8 bf f6 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2ce1:	be 08 00 00 00       	mov    $0x8,%esi
    2ce6:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ceb:	49 89 c7             	mov    %rax,%r15
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2cee:	e8 ad f6 ff ff       	call   23a0 <calloc@plt>

  thread_data[thread_count].type = TIMER;
    2cf3:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2cf8:	be 08 00 00 00       	mov    $0x8,%esi
    2cfd:	bf 08 00 00 00       	mov    $0x8,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d02:	48 89 c3             	mov    %rax,%rbx
  thread_data[thread_count].task_count = total_barrier_count;
    2d05:	48 8b 05 9c 4d 00 00 	mov    0x4d9c(%rip),%rax        # 7aa8 <_IO_stdin_used+0xaa8>
  thread_data[thread_count].type = TIMER;
    2d0c:	41 c7 82 68 01 00 00 00 00 00 00 	movl   $0x0,0x168(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2d17:	49 89 82 90 01 00 00 	mov    %rax,0x190(%r10)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2d1e:	e8 7d f6 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2d23:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2d28:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    2d2d:	48 8d 35 f3 45 00 00 	lea    0x45f3(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2d34:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2d38:	bf 01 00 00 00       	mov    $0x1,%edi
    2d3d:	49 8d 92 70 03 00 00 	lea    0x370(%r10),%rdx
    2d44:	49 8d 8a 60 01 00 00 	lea    0x160(%r10),%rcx
    2d4b:	4c 89 10             	mov    %r10,(%rax)
    2d4e:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2d52:	49 8d 92 20 04 00 00 	lea    0x420(%r10),%rdx
    2d59:	4d 8d b2 c0 02 00 00 	lea    0x2c0(%r10),%r14
    2d60:	48 89 50 30          	mov    %rdx,0x30(%rax)
    2d64:	49 8d 92 d0 04 00 00 	lea    0x4d0(%r10),%rdx
  }
  thread_data[thread_count].threads = my_thread_data;
    2d6b:	49 89 82 70 01 00 00 	mov    %rax,0x170(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2d72:	48 89 48 10          	mov    %rcx,0x10(%rax)
    2d76:	48 89 68 18          	mov    %rbp,0x18(%rax)
    2d7a:	4c 89 70 20          	mov    %r14,0x20(%rax)
    2d7e:	48 89 50 38          	mov    %rdx,0x38(%rax)
    2d82:	ba 02 00 00 00       	mov    $0x2,%edx
    2d87:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2d89:	41 c7 82 78 01 00 00 02 00 00 00 	movl   $0x2,0x178(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2d94:	41 c7 82 80 01 00 00 02 00 00 00 	movl   $0x2,0x180(%r10)
  thread_data[thread_count].thread_index = 0;
    2d9f:	41 c7 82 60 01 00 00 00 00 00 00 	movl   $0x0,0x160(%r10)
    2daa:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    my_thread_data[n] = &thread_data[n]; 
    2daf:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    2db4:	e8 97 f6 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2db9:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    2dbe:	48 8d 7b 10          	lea    0x10(%rbx),%rdi
    2dc2:	49 8d 74 24 70       	lea    0x70(%r12),%rsi
    2dc7:	48 8d 15 b2 0d 00 00 	lea    0xdb2(%rip),%rdx        # 3b80 <timer_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    thread_data[x].type = WORKER;
    thread_data[x].running = 1;
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2dce:	4c 8d 25 fb 09 00 00 	lea    0x9fb(%rip),%r12        # 37d0 <barriered_thread>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2dd5:	e8 96 f6 ff ff       	call   2470 <pthread_create@plt>
    thread_data[x].type = WORKER;
    2dda:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    2ddf:	31 d2                	xor    %edx,%edx
    2de1:	31 c0                	xor    %eax,%eax
    2de3:	4c 8d 0d 26 48 00 00 	lea    0x4826(%rip),%r9        # 7610 <_IO_stdin_used+0x610>
    2dea:	bf 01 00 00 00       	mov    $0x1,%edi
    2def:	41 c7 42 08 01 00 00 00 	movl   $0x1,0x8(%r10)
    2df7:	4c 89 ce             	mov    %r9,%rsi
    thread_data[x].running = 1;
    2dfa:	41 c7 42 34 01 00 00 00 	movl   $0x1,0x34(%r10)
    2e02:	e8 49 f6 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2e07:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    2e0c:	4c 89 e2             	mov    %r12,%rdx
    2e0f:	4c 89 ee             	mov    %r13,%rsi
    2e12:	48 89 df             	mov    %rbx,%rdi
    2e15:	e8 56 f6 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2e1a:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    2e1f:	48 8b 3b             	mov    (%rbx),%rdi
    2e22:	be 08 00 00 00       	mov    $0x8,%esi
    2e27:	49 8b 92 a0 00 00 00 	mov    0xa0(%r10),%rdx
    2e2e:	e8 ad f4 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    thread_data[x].type = WORKER;
    2e33:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    2e38:	ba 01 00 00 00       	mov    $0x1,%edx
    2e3d:	31 c0                	xor    %eax,%eax
    2e3f:	4c 8d 0d ca 47 00 00 	lea    0x47ca(%rip),%r9        # 7610 <_IO_stdin_used+0x610>
    2e46:	bf 01 00 00 00       	mov    $0x1,%edi
    2e4b:	41 c7 82 b8 00 00 00 01 00 00 00 	movl   $0x1,0xb8(%r10)
    2e56:	4c 89 ce             	mov    %r9,%rsi
    thread_data[x].running = 1;
    2e59:	41 c7 82 e4 00 00 00 01 00 00 00 	movl   $0x1,0xe4(%r10)
    2e64:	e8 e7 f5 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2e69:	49 8d 75 38          	lea    0x38(%r13),%rsi
    2e6d:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    2e71:	4c 89 e2             	mov    %r12,%rdx
    2e74:	4c 8b 6c 24 08       	mov    0x8(%rsp),%r13
    2e79:	4c 8d 63 20          	lea    0x20(%rbx),%r12
    2e7d:	4c 89 e9             	mov    %r13,%rcx
    2e80:	e8 eb f5 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2e85:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    2e8a:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    2e8e:	be 08 00 00 00       	mov    $0x8,%esi
    2e93:	49 8b 92 50 01 00 00 	mov    0x150(%r10),%rdx
    2e9a:	e8 41 f4 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2e9f:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ea4:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].task_count = 0;
    2ea9:	48 8b 3d 00 4c 00 00 	mov    0x4c00(%rip),%rdi        # 7ab0 <_IO_stdin_used+0xab0>
    thread_data[x].type = IO;
    2eb0:	41 c7 82 18 02 00 00 02 00 00 00 	movl   $0x2,0x218(%r10)
    thread_data[x].task_count = 0;
    2ebb:	49 89 ba 40 02 00 00 	mov    %rdi,0x240(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ec2:	bf 01 00 00 00       	mov    $0x1,%edi
    2ec7:	e8 d4 f4 ff ff       	call   23a0 <calloc@plt>
    2ecc:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2ed1:	be 00 08 00 00       	mov    $0x800,%esi
    2ed6:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ed8:	49 89 82 58 02 00 00 	mov    %rax,0x258(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2edf:	e8 cc f5 ff ff       	call   24b0 <eventfd@plt>
    2ee4:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2ee9:	be 08 00 00 00       	mov    $0x8,%esi
    2eee:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2ef3:	41 89 82 60 02 00 00 	mov    %eax,0x260(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2efa:	e8 a1 f4 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    2eff:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    2f04:	ba 03 00 00 00       	mov    $0x3,%edx
    2f09:	48 8d 35 35 44 00 00 	lea    0x4435(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    2f10:	4c 89 68 08          	mov    %r13,0x8(%rax)
    2f14:	bf 01 00 00 00       	mov    $0x1,%edi
    2f19:	4d 89 f5             	mov    %r14,%r13
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2f1c:	41 be 04 00 00 00    	mov    $0x4,%r14d
      my_thread_data[n] = &thread_data[n]; 
    2f22:	4c 89 10             	mov    %r10,(%rax)
    thread_data[x].threads = my_thread_data;
    2f25:	49 89 82 20 02 00 00 	mov    %rax,0x220(%r10)
    2f2c:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_count = thread_count;
    2f2e:	41 c7 82 28 02 00 00 02 00 00 00 	movl   $0x2,0x228(%r10)
    thread_data[x].thread_index = x;
    2f39:	41 c7 82 10 02 00 00 03 00 00 00 	movl   $0x3,0x210(%r10)
    2f44:	e8 07 f5 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2f49:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    2f4e:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    2f52:	48 89 e9             	mov    %rbp,%rcx
    2f55:	48 8d 15 94 1e 00 00 	lea    0x1e94(%rip),%rdx        # 4df0 <io_thread>
    2f5c:	49 8d af e0 00 00 00 	lea    0xe0(%r15),%rbp
    2f63:	48 81 c6 a8 00 00 00 	add    $0xa8,%rsi
    2f6a:	4c 8d 3d 0f 0b 00 00 	lea    0xb0f(%rip),%r15        # 3a80 <external_thread>
    2f71:	e8 fa f4 ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2f76:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    2f7b:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    2f80:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
    2f85:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    2f8a:	44 89 f2             	mov    %r14d,%edx
    2f8d:	48 8d 35 c8 43 00 00 	lea    0x43c8(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    2f94:	bf 01 00 00 00       	mov    $0x1,%edi
    2f99:	31 c0                	xor    %eax,%eax
    2f9b:	e8 b0 f4 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    2fa0:	be 08 00 00 00       	mov    $0x8,%esi
    2fa5:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    2faa:	48 8b 05 ff 4a 00 00 	mov    0x4aff(%rip),%rax        # 7ab0 <_IO_stdin_used+0xab0>
    thread_data[x].type = EXTERNAL;
    2fb1:	41 c7 45 08 03 00 00 00 	movl   $0x3,0x8(%r13)
    thread_data[x].task_count = 0;
    2fb9:	49 89 45 30          	mov    %rax,0x30(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    2fbd:	e8 de f3 ff ff       	call   23a0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2fc2:	be 08 00 00 00       	mov    $0x8,%esi
    2fc7:	bf 02 00 00 00       	mov    $0x2,%edi
	  thread_data[x].buffers_count = 1;
    2fcc:	41 c7 85 ac 00 00 00 01 00 00 00 	movl   $0x1,0xac(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    2fd7:	49 89 45 40          	mov    %rax,0x40(%r13)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    2fdb:	48 89 18             	mov    %rbx,(%rax)
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2fde:	48 83 c3 10          	add    $0x10,%rbx
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2fe2:	e8 b9 f3 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    2fe7:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2fec:	4c 89 e9             	mov    %r13,%rcx
    2fef:	48 89 ee             	mov    %rbp,%rsi
    thread_data[x].threads = my_thread_data;
    2ff2:	49 89 45 10          	mov    %rax,0x10(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2ff6:	4c 89 fa             	mov    %r15,%rdx
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2ff9:	49 81 c5 b0 00 00 00 	add    $0xb0,%r13
    3000:	48 83 c5 38          	add    $0x38,%rbp
      my_thread_data[n] = &thread_data[n]; 
    3004:	48 89 38             	mov    %rdi,(%rax)
    3007:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    thread_data[x].thread_index = x;
    300c:	45 89 b5 50 ff ff ff 	mov    %r14d,-0xb0(%r13)
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3013:	41 83 c6 01          	add    $0x1,%r14d
      my_thread_data[n] = &thread_data[n]; 
    3017:	48 89 78 08          	mov    %rdi,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    301b:	48 8b 05 7e 4a 00 00 	mov    0x4a7e(%rip),%rax        # 7aa0 <_IO_stdin_used+0xaa0>
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3022:	4c 89 e7             	mov    %r12,%rdi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3025:	49 83 c4 08          	add    $0x8,%r12
    thread_data[x].thread_count = thread_count;
    3029:	49 89 85 68 ff ff ff 	mov    %rax,-0x98(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3030:	e8 3b f4 ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3035:	41 83 fe 08          	cmp    $0x8,%r14d
    3039:	0f 85 4b ff ff ff    	jne    2f8a <main+0x99a>
    303f:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    3044:	48 8d 3d 2e 43 00 00 	lea    0x432e(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    304b:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    3050:	31 ed                	xor    %ebp,%ebp
    3052:	4c 8d 6c 24 70       	lea    0x70(%rsp),%r13
    3057:	4c 8d 25 39 43 00 00 	lea    0x4339(%rip),%r12        # 7397 <_IO_stdin_used+0x397>
    305e:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    3063:	e8 88 f2 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3068:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    void * result; 
    pthread_join(thread[x], &result);
    306d:	48 8b 3c eb          	mov    (%rbx,%rbp,8),%rdi
    3071:	4c 89 ee             	mov    %r13,%rsi
    3074:	e8 77 f4 ff ff       	call   24f0 <pthread_join@plt>
    3079:	89 ea                	mov    %ebp,%edx
    307b:	4c 89 e6             	mov    %r12,%rsi
    307e:	bf 01 00 00 00       	mov    $0x1,%edi
    3083:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3085:	48 83 c5 01          	add    $0x1,%rbp
    3089:	e8 c2 f3 ff ff       	call   2450 <__printf_chk@plt>
    308e:	48 83 fd 08          	cmp    $0x8,%rbp
    3092:	75 d9                	jne    306d <main+0xa7d>
    3094:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
    3099:	45 31 c9             	xor    %r9d,%r9d
    309c:	4d 89 f2             	mov    %r14,%r10
  long received = 0;
    309f:	45 31 c0             	xor    %r8d,%r8d
  for (int x = 0 ; x < thread_count ; x++) {
    30a2:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
  long ingests = 0;
    30aa:	45 31 e4             	xor    %r12d,%r12d
  long total = 0;
    30ad:	31 ed                	xor    %ebp,%ebp
  long sends = 0;
    30af:	31 c9                	xor    %ecx,%ecx
    30b1:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    30b6:	4d 8d 76 28          	lea    0x28(%r14),%r14
    30ba:	49 89 ed             	mov    %rbp,%r13
    30bd:	4c 89 e3             	mov    %r12,%rbx
    30c0:	4c 89 4c 24 28       	mov    %r9,0x28(%rsp)
    30c5:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
    30ca:	4d 89 c2             	mov    %r8,%r10
    30cd:	bf 0a 00 00 00       	mov    $0xa,%edi
    30d2:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    30d7:	8b 6c 24 18          	mov    0x18(%rsp),%ebp
    30db:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    30e0:	e8 eb f1 ff ff       	call   22d0 <putchar@plt>
    30e5:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    30ea:	bf 01 00 00 00       	mov    $0x1,%edi
    30ef:	83 f5 01             	xor    $0x1,%ebp
    30f2:	48 8d 35 b2 42 00 00 	lea    0x42b2(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    30f9:	48 8b 10             	mov    (%rax),%rdx
    30fc:	31 c0                	xor    %eax,%eax
    30fe:	e8 4d f3 ff ff       	call   2450 <__printf_chk@plt>
      other = (x + 1) % total_threads;
    }
    printf("\n");
    printf("Total Protected %ld\n", protected_state[me].protected);

    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3103:	41 8b 56 08          	mov    0x8(%r14),%edx
    3107:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    310c:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    3111:	85 d2                	test   %edx,%edx
    3113:	0f 8e 05 05 00 00    	jle    361e <main+0x102e>
    3119:	48 63 f2             	movslq %edx,%rsi
    311c:	49 8b 06             	mov    (%r14),%rax
    long v = 0;
    311f:	31 d2                	xor    %edx,%edx
    3121:	48 c1 e6 09          	shl    $0x9,%rsi
    3125:	48 01 c6             	add    %rax,%rsi
    3128:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      v += thread_data[me].tasks[n].v;
    3130:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3137:	48 05 00 02 00 00    	add    $0x200,%rax
    313d:	48 39 f0             	cmp    %rsi,%rax
    3140:	75 ee                	jne    3130 <main+0xb40>
    }
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3142:	48 63 c5             	movslq %ebp,%rax
    3145:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    314a:	48 f7 d8             	neg    %rax
    314d:	25 b0 00 00 00       	and    $0xb0,%eax
    3152:	48 01 f8             	add    %rdi,%rax
    3155:	48 63 70 30          	movslq 0x30(%rax),%rsi
    3159:	85 f6                	test   %esi,%esi
    315b:	7e 25                	jle    3182 <main+0xb92>
    315d:	48 8b 40 28          	mov    0x28(%rax),%rax
    3161:	48 c1 e6 09          	shl    $0x9,%rsi
    3165:	48 01 c6             	add    %rax,%rsi
    3168:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      v += thread_data[other].tasks[n].v;
    3170:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3177:	48 05 00 02 00 00    	add    $0x200,%rax
    317d:	48 39 f0             	cmp    %rsi,%rax
    3180:	75 ee                	jne    3170 <main+0xb80>
    3182:	48 8d 35 37 42 00 00 	lea    0x4237(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    3189:	bf 01 00 00 00       	mov    $0x1,%edi
    318e:	31 c0                	xor    %eax,%eax
    3190:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    3195:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    319a:	e8 b1 f2 ff ff       	call   2450 <__printf_chk@plt>
    }
    printf("Total V %ld\n", v);
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    319f:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    31a4:	bf 01 00 00 00       	mov    $0x1,%edi
    31a9:	48 8b 30             	mov    (%rax),%rsi
    31ac:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    31b6:	48 f7 ee             	imul   %rsi
    31b9:	48 c1 fe 3f          	sar    $0x3f,%rsi
    31bd:	31 c0                	xor    %eax,%eax
    31bf:	48 d1 fa             	sar    %rdx
    31c2:	48 29 f2             	sub    %rsi,%rdx
    31c5:	48 8d 35 6c 44 00 00 	lea    0x446c(%rip),%rsi        # 7638 <_IO_stdin_used+0x638>
    31cc:	e8 7f f2 ff ff       	call   2450 <__printf_chk@plt>
    31d1:	bf 0a 00 00 00       	mov    $0xa,%edi
    31d6:	e8 f5 f0 ff ff       	call   22d0 <putchar@plt>
    printf("\n");
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    31db:	41 8b 56 08          	mov    0x8(%r14),%edx
    31df:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    31e4:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    31e9:	85 d2                	test   %edx,%edx
    31eb:	7e 4f                	jle    323c <main+0xc4c>
    31ed:	49 8b 06             	mov    (%r14),%rax
    31f0:	4c 63 c2             	movslq %edx,%r8
    31f3:	4c 8b 5c 24 28       	mov    0x28(%rsp),%r11
    31f8:	49 c1 e0 09          	shl    $0x9,%r8
    31fc:	49 01 c0             	add    %rax,%r8
    31ff:	90                   	nop
      total += thread_data[x].tasks[n].n;
      ingests += thread_data[x].tasks[n].ingest_count;
      sends += thread_data[x].tasks[n].sends;
      for (int k = 0 ; k < thread_count ; k++) {
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3200:	48 8b 90 68 01 00 00 	mov    0x168(%rax),%rdx
      total += thread_data[x].tasks[n].n;
    3207:	4c 03 a8 08 01 00 00 	add    0x108(%rax),%r13
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    320e:	48 05 00 02 00 00    	add    $0x200,%rax
      ingests += thread_data[x].tasks[n].ingest_count;
    3214:	48 03 98 60 ff ff ff 	add    -0xa0(%rax),%rbx
      sends += thread_data[x].tasks[n].sends;
    321b:	48 03 88 70 ff ff ff 	add    -0x90(%rax),%rcx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3222:	4c 03 5a 10          	add    0x10(%rdx),%r11
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3226:	4c 03 52 18          	add    0x18(%rdx),%r10
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    322a:	4c 03 5a 30          	add    0x30(%rdx),%r11
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    322e:	4c 03 52 38          	add    0x38(%rdx),%r10
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3232:	4c 39 c0             	cmp    %r8,%rax
    3235:	75 c9                	jne    3200 <main+0xc10>
    3237:	4c 89 5c 24 28       	mov    %r11,0x28(%rsp)
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      // printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
      // printf("%ld iterations\n", thread_data[x].iteration_count);
    }
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    323c:	45 31 ff             	xor    %r15d,%r15d
    323f:	49 83 7e 68 00       	cmpq   $0x0,0x68(%r14)
    3244:	4c 8d 25 0d 44 00 00 	lea    0x440d(%rip),%r12        # 7658 <_IO_stdin_used+0x658>
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    324b:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3255:	7e 7e                	jle    32d5 <main+0xce5>
    3257:	4c 89 6c 24 08       	mov    %r13,0x8(%rsp)
    325c:	4d 89 f5             	mov    %r14,%r13
    325f:	49 89 ce             	mov    %rcx,%r14
    3262:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    3267:	4c 89 fb             	mov    %r15,%rbx
    326a:	4d 89 d7             	mov    %r10,%r15
    326d:	0f 1f 00             	nopl   (%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3270:	49 8b 45 58          	mov    0x58(%r13),%rax
    3274:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    3278:	48 83 ec 08          	sub    $0x8,%rsp
    327c:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3281:	48 83 c3 01          	add    $0x1,%rbx
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3285:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3289:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    328d:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3291:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3294:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3298:	4c 2b 01             	sub    (%rcx),%r8
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    329b:	48 f7 e5             	mul    %rbp
    329e:	8b 49 20             	mov    0x20(%rcx),%ecx
    32a1:	56                   	push   %rsi
    32a2:	31 c0                	xor    %eax,%eax
    32a4:	4c 89 e6             	mov    %r12,%rsi
    32a7:	48 c1 ea 12          	shr    $0x12,%rdx
    32ab:	49 89 d1             	mov    %rdx,%r9
    32ae:	ba 02 00 00 00       	mov    $0x2,%edx
    32b3:	e8 98 f1 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    32b8:	41 5a                	pop    %r10
    32ba:	41 5b                	pop    %r11
    32bc:	49 39 5d 68          	cmp    %rbx,0x68(%r13)
    32c0:	7f ae                	jg     3270 <main+0xc80>
    32c2:	4c 89 f1             	mov    %r14,%rcx
    32c5:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    32ca:	4d 89 ee             	mov    %r13,%r14
    32cd:	4c 8b 6c 24 08       	mov    0x8(%rsp),%r13
    32d2:	4d 89 fa             	mov    %r15,%r10
      // printf("%ldns per thread\n", (seconds2 / 2));
    }
    // printf("cycles %ld\n", thread_data[x].cycles);

    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    32d5:	41 8b 86 84 00 00 00 	mov    0x84(%r14),%eax
    32dc:	85 c0                	test   %eax,%eax
    32de:	0f 8e 55 01 00 00    	jle    3439 <main+0xe49>
    32e4:	4c 89 6c 24 38       	mov    %r13,0x38(%rsp)
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    32e9:	31 ed                	xor    %ebp,%ebp
    32eb:	49 8b 76 18          	mov    0x18(%r14),%rsi
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
	  struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
	  const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
	  const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
	  printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32ef:	49 bf db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r15
    32f9:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
    32fe:	49 89 ec             	mov    %rbp,%r12
    3301:	4c 89 f5             	mov    %r14,%rbp
    3304:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    3309:	4c 89 54 24 60       	mov    %r10,0x60(%rsp)
    330e:	66 90                	xchg   %ax,%ax
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3310:	4a 8b 0c e6          	mov    (%rsi,%r12,8),%rcx
    3314:	4a 8d 1c e5 00 00 00 00 	lea    0x0(,%r12,8),%rbx
    331c:	31 d2                	xor    %edx,%edx
    331e:	8b 09                	mov    (%rcx),%ecx
    3320:	85 c9                	test   %ecx,%ecx
    3322:	0f 8e ed 00 00 00    	jle    3415 <main+0xe25>
    3328:	4c 89 64 24 10       	mov    %r12,0x10(%rsp)
    332d:	49 89 d0             	mov    %rdx,%r8
    3330:	49 89 ed             	mov    %rbp,%r13
    3333:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3338:	48 8d 3d 8e 40 00 00 	lea    0x408e(%rip),%rdi        # 73cd <_IO_stdin_used+0x3cd>
    333f:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    3344:	e8 a7 ef ff ff       	call   22f0 <puts@plt>
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3349:	49 8b 75 18          	mov    0x18(%r13),%rsi
    334d:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    3352:	48 8b 14 1e          	mov    (%rsi,%rbx,1),%rdx
    3356:	4d 89 c4             	mov    %r8,%r12
    3359:	49 c1 e4 05          	shl    $0x5,%r12
    335d:	48 8b 42 08          	mov    0x8(%rdx),%rax
    3361:	4c 01 e0             	add    %r12,%rax
    3364:	44 8b 48 1c          	mov    0x1c(%rax),%r9d
    3368:	45 85 c9             	test   %r9d,%r9d
    336b:	0f 8e 88 00 00 00    	jle    33f9 <main+0xe09>
    3371:	31 ed                	xor    %ebp,%ebp
    3373:	4c 89 ef             	mov    %r13,%rdi
    3376:	4f 8d 34 80          	lea    (%r8,%r8,4),%r14
    337a:	49 89 ed             	mov    %rbp,%r13
    337d:	49 c1 e6 03          	shl    $0x3,%r14
    3381:	48 89 fd             	mov    %rdi,%rbp
    3384:	0f 1f 40 00          	nopl   0x0(%rax)
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3388:	4c 89 e9             	mov    %r13,%rcx
    338b:	48 83 ec 08          	sub    $0x8,%rsp
    338f:	bf 01 00 00 00       	mov    $0x1,%edi
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3394:	49 83 c5 01          	add    $0x1,%r13
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3398:	48 c1 e1 05          	shl    $0x5,%rcx
    339c:	48 03 48 10          	add    0x10(%rax),%rcx
	  const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    33a0:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    33a4:	48 2b 71 08          	sub    0x8(%rcx),%rsi
	  printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    33a8:	48 89 f0             	mov    %rsi,%rax
	  const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    33ab:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    33af:	4c 2b 01             	sub    (%rcx),%r8
	  printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    33b2:	49 f7 e7             	mul    %r15
    33b5:	48 8b 45 58          	mov    0x58(%rbp),%rax
    33b9:	42 8b 4c 30 20       	mov    0x20(%rax,%r14,1),%ecx
    33be:	56                   	push   %rsi
    33bf:	31 c0                	xor    %eax,%eax
    33c1:	48 8d 35 e0 42 00 00 	lea    0x42e0(%rip),%rsi        # 76a8 <_IO_stdin_used+0x6a8>
    33c8:	48 c1 ea 12          	shr    $0x12,%rdx
    33cc:	49 89 d1             	mov    %rdx,%r9
    33cf:	ba 02 00 00 00       	mov    $0x2,%edx
    33d4:	e8 77 f0 ff ff       	call   2450 <__printf_chk@plt>
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    33d9:	48 8b 75 18          	mov    0x18(%rbp),%rsi
    33dd:	5f                   	pop    %rdi
    33de:	41 58                	pop    %r8
    33e0:	48 8b 14 1e          	mov    (%rsi,%rbx,1),%rdx
    33e4:	48 8b 42 08          	mov    0x8(%rdx),%rax
    33e8:	4c 01 e0             	add    %r12,%rax
    33eb:	44 39 68 1c          	cmp    %r13d,0x1c(%rax)
    33ef:	7f 97                	jg     3388 <main+0xd98>
    33f1:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    33f6:	49 89 ed             	mov    %rbp,%r13
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    33f9:	49 83 c0 01          	add    $0x1,%r8
    33fd:	44 39 02             	cmp    %r8d,(%rdx)
    3400:	0f 8f 32 ff ff ff    	jg     3338 <main+0xd48>
    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3406:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
    340b:	41 8b 85 84 00 00 00 	mov    0x84(%r13),%eax
    3412:	4c 89 ed             	mov    %r13,%rbp
    3415:	49 83 c4 01          	add    $0x1,%r12
    3419:	44 39 e0             	cmp    %r12d,%eax
    341c:	0f 8f ee fe ff ff    	jg     3310 <main+0xd20>
    3422:	4c 8b 6c 24 38       	mov    0x38(%rsp),%r13
    3427:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    342c:	49 89 ee             	mov    %rbp,%r14
    342f:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    3434:	4c 8b 54 24 60       	mov    0x60(%rsp),%r10
  for (int x = 0 ; x < thread_count ; x++) {
    3439:	8b 44 24 18          	mov    0x18(%rsp),%eax
    343d:	48 83 44 24 20 18    	addq   $0x18,0x20(%rsp)
    3443:	49 81 c6 b0 00 00 00 	add    $0xb0,%r14
    344a:	85 c0                	test   %eax,%eax
    344c:	0f 85 87 00 00 00    	jne    34d9 <main+0xee9>
    3452:	c7 44 24 18 01 00 00 00 	movl   $0x1,0x18(%rsp)
    345a:	e9 6e fc ff ff       	jmp    30cd <main+0xadd>
      my_thread_data[1] = &thread_data[other]; 
    345f:	49 8d 86 b0 00 00 00 	lea    0xb0(%r14),%rax
      my_thread_data[0] = &thread_data[x]; 
    3466:	4c 89 33             	mov    %r14,(%rbx)
    3469:	4c 89 f1             	mov    %r14,%rcx
    346c:	44 89 ea             	mov    %r13d,%edx
      my_thread_data[1] = &thread_data[other]; 
    346f:	48 89 43 08          	mov    %rax,0x8(%rbx)
    3473:	49 89 c0             	mov    %rax,%r8
    3476:	48 8d 35 8c 3e 00 00 	lea    0x3e8c(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
    347d:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].thread_index = 0;
    3482:	41 c7 06 00 00 00 00 	movl   $0x0,(%r14)
      my_thread_data[1] = &thread_data[other]; 
    3489:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    348e:	31 c0                	xor    %eax,%eax
    3490:	e8 bb ef ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    3495:	49 8d 44 24 18       	lea    0x18(%r12),%rax
      other = (x + 1) % total_threads;
    349a:	44 8b 7c 24 20       	mov    0x20(%rsp),%r15d
      thread_data[x].protected_state = &protected_state[x];
    349f:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    34a4:	49 89 c4             	mov    %rax,%r12
    34a7:	e9 c9 f3 ff ff       	jmp    2875 <main+0x285>
        CPU_SET(curcpu, sendercpu);
    34ac:	48 63 44 24 50       	movslq 0x50(%rsp),%rax
    34b1:	48 89 c7             	mov    %rax,%rdi
    34b4:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    34ba:	77 13                	ja     34cf <main+0xedf>
    34bc:	48 c1 e8 06          	shr    $0x6,%rax
    34c0:	ba 01 00 00 00       	mov    $0x1,%edx
    34c5:	89 f9                	mov    %edi,%ecx
    34c7:	48 d3 e2             	shl    %cl,%rdx
    34ca:	48 09 54 c5 00       	or     %rdx,0x0(%rbp,%rax,8)
        curcpu += 2;
    34cf:	83 44 24 50 02       	addl   $0x2,0x50(%rsp)
    34d4:	e9 ef f3 ff ff       	jmp    28c8 <main+0x2d8>
    34d9:	4c 8b 4c 24 28       	mov    0x28(%rsp),%r9
    34de:	4c 89 ea             	mov    %r13,%rdx
    34e1:	bf 01 00 00 00       	mov    $0x1,%edi
    34e6:	31 c0                	xor    %eax,%eax
    34e8:	48 8d 35 e6 3e 00 00 	lea    0x3ee6(%rip),%rsi        # 73d5 <_IO_stdin_used+0x3d5>
    34ef:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    34f4:	49 89 dc             	mov    %rbx,%r12
    34f7:	4c 89 ed             	mov    %r13,%rbp
    34fa:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    34ff:	4d 89 e7             	mov    %r12,%r15
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
  printf("Total Requests per second %ld\n", total / DURATION);
    3502:	48 c1 fd 3f          	sar    $0x3f,%rbp
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3506:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    3510:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    3515:	49 c1 ff 3f          	sar    $0x3f,%r15
    3519:	e8 32 ef ff ff       	call   2450 <__printf_chk@plt>
    351e:	bf 0a 00 00 00       	mov    $0xa,%edi
    3523:	e8 a8 ed ff ff       	call   22d0 <putchar@plt>
    3528:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    352d:	bf 01 00 00 00       	mov    $0x1,%edi
    3532:	48 8d 35 c7 41 00 00 	lea    0x41c7(%rip),%rsi        # 7700 <_IO_stdin_used+0x700>
    3539:	48 8b 50 08          	mov    0x8(%rax),%rdx
    353d:	31 c0                	xor    %eax,%eax
    353f:	e8 0c ef ff ff       	call   2450 <__printf_chk@plt>
    3544:	4c 89 e0             	mov    %r12,%rax
    3547:	bf 01 00 00 00       	mov    $0x1,%edi
    354c:	48 8d 35 d5 41 00 00 	lea    0x41d5(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    3553:	48 f7 eb             	imul   %rbx
    3556:	31 c0                	xor    %eax,%eax
    3558:	48 d1 fa             	sar    %rdx
    355b:	4c 29 fa             	sub    %r15,%rdx
    355e:	e8 ed ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3563:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3568:	bf 01 00 00 00       	mov    $0x1,%edi
    356d:	48 8d 35 e4 41 00 00 	lea    0x41e4(%rip),%rsi        # 7758 <_IO_stdin_used+0x758>
    3574:	48 89 c8             	mov    %rcx,%rax
    3577:	48 c1 f9 3f          	sar    $0x3f,%rcx
    357b:	48 f7 eb             	imul   %rbx
    357e:	31 c0                	xor    %eax,%eax
    3580:	48 d1 fa             	sar    %rdx
    3583:	48 29 ca             	sub    %rcx,%rdx
    3586:	e8 c5 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    358b:	4c 89 e8             	mov    %r13,%rax
    358e:	bf 01 00 00 00       	mov    $0x1,%edi
    3593:	48 8d 35 ee 41 00 00 	lea    0x41ee(%rip),%rsi        # 7788 <_IO_stdin_used+0x788>
    359a:	48 f7 eb             	imul   %rbx
    359d:	31 c0                	xor    %eax,%eax
    359f:	48 d1 fa             	sar    %rdx
    35a2:	48 29 ea             	sub    %rbp,%rdx
    35a5:	e8 a6 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    35aa:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    35af:	bf 01 00 00 00       	mov    $0x1,%edi
    35b4:	48 8d 35 2e 3e 00 00 	lea    0x3e2e(%rip),%rsi        # 73e9 <_IO_stdin_used+0x3e9>
    35bb:	4c 89 c8             	mov    %r9,%rax
    35be:	49 c1 f9 3f          	sar    $0x3f,%r9
    35c2:	48 f7 eb             	imul   %rbx
    35c5:	31 c0                	xor    %eax,%eax
    35c7:	48 d1 fa             	sar    %rdx
    35ca:	4c 29 ca             	sub    %r9,%rdx
    35cd:	e8 7e ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    35d2:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    35d7:	bf 01 00 00 00       	mov    $0x1,%edi
    35dc:	48 8d 35 17 3e 00 00 	lea    0x3e17(%rip),%rsi        # 73fa <_IO_stdin_used+0x3fa>
    35e3:	4c 89 c0             	mov    %r8,%rax
    35e6:	49 c1 f8 3f          	sar    $0x3f,%r8
    35ea:	48 f7 eb             	imul   %rbx
    35ed:	48 d1 fa             	sar    %rdx
    35f0:	4c 29 c2             	sub    %r8,%rdx
    35f3:	31 c0                	xor    %eax,%eax
    35f5:	e8 56 ee ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    35fa:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    35ff:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3608:	75 1b                	jne    3625 <main+0x1035>
    360a:	48 81 c4 88 00 00 00 	add    $0x88,%rsp
    3611:	31 c0                	xor    %eax,%eax
    3613:	5b                   	pop    %rbx
    3614:	5d                   	pop    %rbp
    3615:	41 5c                	pop    %r12
    3617:	41 5d                	pop    %r13
    3619:	41 5e                	pop    %r14
    361b:	41 5f                	pop    %r15
    361d:	c3                   	ret
    long v = 0;
    361e:	31 d2                	xor    %edx,%edx
    3620:	e9 1d fb ff ff       	jmp    3142 <main+0xb52>
}
    3625:	e8 06 ed ff ff       	call   2330 <__stack_chk_fail@plt>
    362a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000003630 <_start>:
    3630:	f3 0f 1e fa          	endbr64
    3634:	31 ed                	xor    %ebp,%ebp
    3636:	49 89 d1             	mov    %rdx,%r9
    3639:	5e                   	pop    %rsi
    363a:	48 89 e2             	mov    %rsp,%rdx
    363d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3641:	50                   	push   %rax
    3642:	54                   	push   %rsp
    3643:	45 31 c0             	xor    %r8d,%r8d
    3646:	31 c9                	xor    %ecx,%ecx
    3648:	48 8d 3d a1 ef ff ff 	lea    -0x105f(%rip),%rdi        # 25f0 <main>
    364f:	ff 15 83 69 00 00    	call   *0x6983(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3655:	f4                   	hlt
    3656:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003660 <deregister_tm_clones>:
    3660:	48 8d 3d b9 69 00 00 	lea    0x69b9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3667:	48 8d 05 b2 69 00 00 	lea    0x69b2(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    366e:	48 39 f8             	cmp    %rdi,%rax
    3671:	74 15                	je     3688 <deregister_tm_clones+0x28>
    3673:	48 8b 05 66 69 00 00 	mov    0x6966(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    367a:	48 85 c0             	test   %rax,%rax
    367d:	74 09                	je     3688 <deregister_tm_clones+0x28>
    367f:	ff e0                	jmp    *%rax
    3681:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3688:	c3                   	ret
    3689:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003690 <register_tm_clones>:
    3690:	48 8d 3d 89 69 00 00 	lea    0x6989(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3697:	48 8d 35 82 69 00 00 	lea    0x6982(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    369e:	48 29 fe             	sub    %rdi,%rsi
    36a1:	48 89 f0             	mov    %rsi,%rax
    36a4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    36a8:	48 c1 f8 03          	sar    $0x3,%rax
    36ac:	48 01 c6             	add    %rax,%rsi
    36af:	48 d1 fe             	sar    %rsi
    36b2:	74 14                	je     36c8 <register_tm_clones+0x38>
    36b4:	48 8b 05 35 69 00 00 	mov    0x6935(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    36bb:	48 85 c0             	test   %rax,%rax
    36be:	74 08                	je     36c8 <register_tm_clones+0x38>
    36c0:	ff e0                	jmp    *%rax
    36c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    36c8:	c3                   	ret
    36c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000036d0 <__do_global_dtors_aux>:
    36d0:	f3 0f 1e fa          	endbr64
    36d4:	80 3d 4d 69 00 00 00 	cmpb   $0x0,0x694d(%rip)        # a028 <completed.0>
    36db:	75 2b                	jne    3708 <__do_global_dtors_aux+0x38>
    36dd:	55                   	push   %rbp
    36de:	48 83 3d 12 69 00 00 00 	cmpq   $0x0,0x6912(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    36e6:	48 89 e5             	mov    %rsp,%rbp
    36e9:	74 0c                	je     36f7 <__do_global_dtors_aux+0x27>
    36eb:	48 8b 3d 16 69 00 00 	mov    0x6916(%rip),%rdi        # a008 <__dso_handle>
    36f2:	e8 b9 eb ff ff       	call   22b0 <__cxa_finalize@plt>
    36f7:	e8 64 ff ff ff       	call   3660 <deregister_tm_clones>
    36fc:	c6 05 25 69 00 00 01 	movb   $0x1,0x6925(%rip)        # a028 <completed.0>
    3703:	5d                   	pop    %rbp
    3704:	c3                   	ret
    3705:	0f 1f 00             	nopl   (%rax)
    3708:	c3                   	ret
    3709:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003710 <frame_dummy>:
    3710:	f3 0f 1e fa          	endbr64
    3714:	e9 77 ff ff ff       	jmp    3690 <register_tm_clones>
    3719:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003720 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3720:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3724:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    372b:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    372f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3737:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    373b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    373f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3746:	48 85 c9             	test   %rcx,%rcx
    3749:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3750:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3754:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3758:	31 c0                	xor    %eax,%eax
    375a:	c3                   	ret
    375b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003760 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3760:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3764:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    376b:	85 c9                	test   %ecx,%ecx
    376d:	7e 4f                	jle    37be <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    376f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3776:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    377d:	48 c1 e1 09          	shl    $0x9,%rcx
    3781:	48 8b 50 10          	mov    0x10(%rax),%rdx
    3785:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3789:	48 8b 70 28          	mov    0x28(%rax),%rsi
    378d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    378f:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    3793:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3798:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    37a0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    37a8:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    37b3:	48 05 00 02 00 00    	add    $0x200,%rax
    37b9:	48 39 c1             	cmp    %rax,%rcx
    37bc:	75 da                	jne    3798 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    37be:	0f ae f8             	sfence
}
    37c1:	31 c0                	xor    %eax,%eax
    37c3:	c3                   	ret
    37c4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    37cf:	90                   	nop

00000000000037d0 <barriered_thread>:
void* barriered_thread(void *arg) {
    37d0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    37d4:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    37d8:	0f 85 90 02 00 00    	jne    3a6e <barriered_thread+0x29e>
void* barriered_thread(void *arg) {
    37de:	41 56                	push   %r14
    37e0:	41 55                	push   %r13
    37e2:	49 89 fd             	mov    %rdi,%r13
    37e5:	41 54                	push   %r12
    37e7:	55                   	push   %rbp
    37e8:	31 ed                	xor    %ebp,%ebp
    37ea:	53                   	push   %rbx
    37eb:	31 db                	xor    %ebx,%ebx
    37ed:	0f 1f 00             	nopl   (%rax)
    if (t >= data->task_count) {
    37f0:	41 8b 55 30          	mov    0x30(%r13),%edx
    37f4:	39 da                	cmp    %ebx,%edx
    37f6:	7f 12                	jg     380a <barriered_thread+0x3a>
      data->cycles++;
    37f8:	49 83 85 98 00 00 00 01 	addq   $0x1,0x98(%r13)
    for (; t < data->task_count; t++) {
    3800:	31 db                	xor    %ebx,%ebx
    3802:	85 d2                	test   %edx,%edx
    3804:	0f 8e 56 01 00 00    	jle    3960 <barriered_thread+0x190>
    380a:	4c 63 e3             	movslq %ebx,%r12
    380d:	49 c1 e4 09          	shl    $0x9,%r12
    3811:	eb 17                	jmp    382a <barriered_thread+0x5a>
    3813:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3818:	83 c3 01             	add    $0x1,%ebx
    381b:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    3822:	39 d3                	cmp    %edx,%ebx
    3824:	0f 8d 36 01 00 00    	jge    3960 <barriered_thread+0x190>
      if (data->tasks[t].available == 1) {
    382a:	49 8b 45 28          	mov    0x28(%r13),%rax
    382e:	4a 8d 34 20          	lea    (%rax,%r12,1),%rsi
    3832:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    3839:	75 dd                	jne    3818 <barriered_thread+0x48>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    383b:	41 8b 7d 18          	mov    0x18(%r13),%edi
          previous = t - 1;
    383f:	83 ea 01             	sub    $0x1,%edx
    3842:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3845:	85 db                	test   %ebx,%ebx
    3847:	0f 4f d1             	cmovg  %ecx,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    384a:	85 ff                	test   %edi,%edi
    384c:	0f 8e 3e 01 00 00    	jle    3990 <barriered_thread+0x1c0>
    3852:	49 8b 45 10          	mov    0x10(%r13),%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3856:	48 63 ca             	movslq %edx,%rcx
    3859:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    385c:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    385f:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    3866:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    386d:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    3871:	45 31 f6             	xor    %r14d,%r14d
    3874:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3878:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3880:	48 8b 10             	mov    (%rax),%rdx
    3883:	4c 8b 5a 28          	mov    0x28(%rdx),%r11
    3887:	49 01 cb             	add    %rcx,%r11
    388a:	4c 89 da             	mov    %r11,%rdx
    388d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    3894:	75 04                	jne    389a <barriered_thread+0xca>
            arrived++;
    3896:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    389a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    38a1:	75 04                	jne    38a7 <barriered_thread+0xd7>
            prearrive++;
    38a3:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    38a7:	48 83 c0 08          	add    $0x8,%rax
    38ab:	48 39 f0             	cmp    %rsi,%rax
    38ae:	75 d0                	jne    3880 <barriered_thread+0xb0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    38b0:	44 39 d7             	cmp    %r10d,%edi
    38b3:	0f 84 c7 00 00 00    	je     3980 <barriered_thread+0x1b0>
    38b9:	45 85 d2             	test   %r10d,%r10d
    38bc:	0f 84 be 00 00 00    	je     3980 <barriered_thread+0x1b0>
        if (arrived == 0 || arrived == data->thread_count) {
    38c2:	45 85 f6             	test   %r14d,%r14d
    38c5:	74 0a                	je     38d1 <barriered_thread+0x101>
    38c7:	45 39 75 18          	cmp    %r14d,0x18(%r13)
    38cb:	0f 85 8f 00 00 00    	jne    3960 <barriered_thread+0x190>
    38d1:	49 8b 45 28          	mov    0x28(%r13),%rax
          data->tasks[t].prearrive++;
    38d5:	4c 01 e0             	add    %r12,%rax
    38d8:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    38df:	85 db                	test   %ebx,%ebx
    38e1:	75 0e                	jne    38f1 <barriered_thread+0x121>
    38e3:	49 8b 75 70          	mov    0x70(%r13),%rsi
    38e7:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    38eb:	0f 8c 5f 01 00 00    	jl     3a50 <barriered_thread+0x280>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    38f1:	49 63 4d 00          	movslq 0x0(%r13),%rcx
    38f5:	49 8b 55 10          	mov    0x10(%r13),%rdx
          data->tasks[t].available = 0;
    38f9:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3903:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    3907:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
    390b:	4c 01 e7             	add    %r12,%rdi
    390e:	ff 90 18 01 00 00    	call   *0x118(%rax)
          data->tasks[t].arrived++;
    3914:	49 8b 45 28          	mov    0x28(%r13),%rax
    3918:	4c 01 e0             	add    %r12,%rax
    391b:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3922:	41 8b 45 30          	mov    0x30(%r13),%eax
          data->iteration_count++;
    3926:	49 83 45 68 01       	addq   $0x1,0x68(%r13)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    392b:	83 e8 01             	sub    $0x1,%eax
    392e:	39 d8                	cmp    %ebx,%eax
    3930:	0f 84 b2 00 00 00    	je     39e8 <barriered_thread+0x218>
          asm volatile ("sfence" ::: "memory");
    3936:	0f ae f8             	sfence
          if (waiting == 0) {
    3939:	85 ed                	test   %ebp,%ebp
    393b:	0f 84 d7 00 00 00    	je     3a18 <barriered_thread+0x248>
    for (; t < data->task_count; t++) {
    3941:	41 8b 55 30          	mov    0x30(%r13),%edx
    3945:	83 c3 01             	add    $0x1,%ebx
    3948:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    394f:	39 d3                	cmp    %edx,%ebx
    3951:	0f 8c d3 fe ff ff    	jl     382a <barriered_thread+0x5a>
    3957:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  while (data->running == 1) {
    3960:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
    3965:	0f 84 85 fe ff ff    	je     37f0 <barriered_thread+0x20>
}
    396b:	5b                   	pop    %rbx
    396c:	31 c0                	xor    %eax,%eax
    396e:	5d                   	pop    %rbp
    396f:	41 5c                	pop    %r12
    3971:	41 5d                	pop    %r13
    3973:	41 5e                	pop    %r14
    3975:	c3                   	ret
    3976:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
    3980:	83 fd 01             	cmp    $0x1,%ebp
    3983:	74 1b                	je     39a0 <barriered_thread+0x1d0>
        int arrived = 0; 
    3985:	31 ed                	xor    %ebp,%ebp
    3987:	e9 36 ff ff ff       	jmp    38c2 <barriered_thread+0xf2>
    398c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    3990:	83 fd 01             	cmp    $0x1,%ebp
    3993:	0f 85 3c ff ff ff    	jne    38d5 <barriered_thread+0x105>
        int arrived = 0; 
    3999:	45 31 f6             	xor    %r14d,%r14d
    399c:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    39a0:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    39a7:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    39ac:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    39ae:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    39b2:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    39b9:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    39be:	e8 4d e9 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    39c3:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    39ca:	48 83 c0 01          	add    $0x1,%rax
    39ce:	48 99                	cqto
    39d0:	49 f7 bd 90 00 00 00 	idivq  0x90(%r13)
    39d7:	49 89 95 88 00 00 00 	mov    %rdx,0x88(%r13)
            waiting = 0; 
    39de:	e9 df fe ff ff       	jmp    38c2 <barriered_thread+0xf2>
    39e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    39e8:	49 8b 75 70          	mov    0x70(%r13),%rsi
    39ec:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    39f0:	0f 8d 40 ff ff ff    	jge    3936 <barriered_thread+0x166>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    39f6:	48 c1 e6 04          	shl    $0x4,%rsi
    39fa:	bf 04 00 00 00       	mov    $0x4,%edi
    39ff:	49 03 75 60          	add    0x60(%r13),%rsi
    3a03:	e8 08 e9 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3a08:	49 83 45 70 01       	addq   $0x1,0x70(%r13)
    3a0d:	e9 24 ff ff ff       	jmp    3936 <barriered_thread+0x166>
    3a12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    3a18:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3a1f:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3a24:	bd 01 00 00 00       	mov    $0x1,%ebp
            data->task_snapshot[data->task_timestamp_count].task = t;
    3a29:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3a2d:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    3a34:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3a38:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3a3b:	e8 d0 e8 ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3a40:	41 8b 55 30          	mov    0x30(%r13),%edx
    3a44:	e9 cf fd ff ff       	jmp    3818 <barriered_thread+0x48>
    3a49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3a50:	48 c1 e6 04          	shl    $0x4,%rsi
    3a54:	bf 04 00 00 00       	mov    $0x4,%edi
    3a59:	49 03 75 58          	add    0x58(%r13),%rsi
    3a5d:	e8 ae e8 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3a62:	49 8b 45 28          	mov    0x28(%r13),%rax
    3a66:	4c 01 e0             	add    %r12,%rax
    3a69:	e9 83 fe ff ff       	jmp    38f1 <barriered_thread+0x121>
}
    3a6e:	31 c0                	xor    %eax,%eax
    3a70:	c3                   	ret
    3a71:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3a7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003a80 <external_thread>:
void * external_thread(void *arg) {
    3a80:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3a84:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    3a88:	0f 85 ec 00 00 00    	jne    3b7a <external_thread+0xfa>
void * external_thread(void *arg) {
    3a8e:	41 57                	push   %r15
    3a90:	4c 8d 3d 6d 35 00 00 	lea    0x356d(%rip),%r15        # 7004 <_IO_stdin_used+0x4>
    3a97:	41 56                	push   %r14
    3a99:	49 89 fe             	mov    %rdi,%r14
    3a9c:	41 55                	push   %r13
    3a9e:	41 54                	push   %r12
    3aa0:	55                   	push   %rbp
    3aa1:	53                   	push   %rbx
    3aa2:	48 83 ec 08          	sub    $0x8,%rsp
    3aa6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int b = 0; b < data->buffers_count; b++) {
    3ab0:	41 8b 8e ac 00 00 00 	mov    0xac(%r14),%ecx
    3ab7:	85 c9                	test   %ecx,%ecx
    3ab9:	7e 54                	jle    3b0f <external_thread+0x8f>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3abb:	49 8b 7e 40          	mov    0x40(%r14),%rdi
    3abf:	45 31 ed             	xor    %r13d,%r13d
    3ac2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3ac8:	4e 8d 24 ed 00 00 00 00 	lea    0x0(,%r13,8),%r12
    3ad0:	31 db                	xor    %ebx,%ebx
    3ad2:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    3ad6:	48 8b 06             	mov    (%rsi),%rax
    3ad9:	8b 10                	mov    (%rax),%edx
    3adb:	85 d2                	test   %edx,%edx
    3add:	7e 27                	jle    3b06 <external_thread+0x86>
    3adf:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    3ae3:	48 89 dd             	mov    %rbx,%rbp
    3ae6:	48 c1 e5 05          	shl    $0x5,%rbp
    3aea:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    3aee:	44 8b 40 08          	mov    0x8(%rax),%r8d
    3af2:	45 85 c0             	test   %r8d,%r8d
    3af5:	74 39                	je     3b30 <external_thread+0xb0>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3af7:	48 83 c3 01          	add    $0x1,%rbx
    3afb:	39 da                	cmp    %ebx,%edx
    3afd:	7f e4                	jg     3ae3 <external_thread+0x63>
    for (int b = 0; b < data->buffers_count; b++) {
    3aff:	41 8b 8e ac 00 00 00 	mov    0xac(%r14),%ecx
    3b06:	49 83 c5 01          	add    $0x1,%r13
    3b0a:	44 39 e9             	cmp    %r13d,%ecx
    3b0d:	7f b9                	jg     3ac8 <external_thread+0x48>
    asm volatile ("mfence" ::: "memory");
    3b0f:	0f ae f0             	mfence
  while (data->running == 1) {
    3b12:	41 83 7e 34 01       	cmpl   $0x1,0x34(%r14)
    3b17:	74 97                	je     3ab0 <external_thread+0x30>
}
    3b19:	48 83 c4 08          	add    $0x8,%rsp
    3b1d:	31 c0                	xor    %eax,%eax
    3b1f:	5b                   	pop    %rbx
    3b20:	5d                   	pop    %rbp
    3b21:	41 5c                	pop    %r12
    3b23:	41 5d                	pop    %r13
    3b25:	41 5e                	pop    %r14
    3b27:	41 5f                	pop    %r15
    3b29:	c3                   	ret
    3b2a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
					data->buffers[b]->buffer[x].data = "Hello world";
    3b30:	4c 89 38             	mov    %r15,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    3b33:	48 8b 06             	mov    (%rsi),%rax
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3b36:	48 83 c3 01          	add    $0x1,%rbx
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    3b3a:	48 8b 78 08          	mov    0x8(%rax),%rdi
    3b3e:	48 01 ef             	add    %rbp,%rdi
    3b41:	48 63 77 1c          	movslq 0x1c(%rdi),%rsi
    3b45:	48 c1 e6 05          	shl    $0x5,%rsi
    3b49:	48 03 77 10          	add    0x10(%rdi),%rsi
    3b4d:	bf 04 00 00 00       	mov    $0x4,%edi
    3b52:	e8 b9 e7 ff ff       	call   2310 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    3b57:	49 8b 7e 40          	mov    0x40(%r14),%rdi
    3b5b:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    3b5f:	48 8b 06             	mov    (%rsi),%rax
    3b62:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3b66:	c7 44 2a 08 01 00 00 00 	movl   $0x1,0x8(%rdx,%rbp,1)
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3b6e:	8b 10                	mov    (%rax),%edx
    3b70:	39 da                	cmp    %ebx,%edx
    3b72:	0f 8f 67 ff ff ff    	jg     3adf <external_thread+0x5f>
    3b78:	eb 85                	jmp    3aff <external_thread+0x7f>
}
    3b7a:	31 c0                	xor    %eax,%eax
    3b7c:	c3                   	ret
    3b7d:	0f 1f 00             	nopl   (%rax)

0000000000003b80 <timer_thread>:
void* timer_thread(void *arg) {
    3b80:	f3 0f 1e fa          	endbr64
    3b84:	41 57                	push   %r15
    3b86:	48 8d 35 83 34 00 00 	lea    0x3483(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3b8d:	49 89 ff             	mov    %rdi,%r15
    3b90:	41 56                	push   %r14
    3b92:	41 55                	push   %r13
    3b94:	41 54                	push   %r12
    3b96:	55                   	push   %rbp
    3b97:	53                   	push   %rbx
    3b98:	48 83 ec 58          	sub    $0x58,%rsp
    3b9c:	8b 17                	mov    (%rdi),%edx
    3b9e:	bf 01 00 00 00       	mov    $0x1,%edi
    3ba3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3bac:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3bb1:	31 c0                	xor    %eax,%eax
    3bb3:	e8 98 e8 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3bb8:	66 0f 6f 05 e0 3d 00 00 	movdqa 0x3de0(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    3bc0:	ba 88 13 00 00       	mov    $0x1388,%edx
    3bc5:	31 c0                	xor    %eax,%eax
    3bc7:	48 8d 35 54 34 00 00 	lea    0x3454(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3bce:	bf 01 00 00 00       	mov    $0x1,%edi
    3bd3:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3bd8:	e8 73 e8 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3bdd:	45 8b 67 34          	mov    0x34(%r15),%r12d
    3be1:	45 85 e4             	test   %r12d,%r12d
    3be4:	0f 84 9b 00 00 00    	je     3c85 <timer_thread+0x105>
  int n = 0;
    3bea:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    3bed:	45 31 e4             	xor    %r12d,%r12d
    3bf0:	49 89 e5             	mov    %rsp,%r13
    y++;
    3bf3:	31 db                	xor    %ebx,%ebx
    3bf5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    3bfa:	48 89 ef             	mov    %rbp,%rdi
    3bfd:	4c 89 ee             	mov    %r13,%rsi
    n++;
    3c00:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3c04:	e8 47 e7 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c09:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3c0d:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c12:	85 c0                	test   %eax,%eax
    3c14:	7e 47                	jle    3c5d <timer_thread+0xdd>
    3c16:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3c1a:	49 c1 e4 09          	shl    $0x9,%r12
    3c1e:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3c22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3c28:	4c 8b 11             	mov    (%rcx),%r10
    3c2b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c2d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3c31:	99                   	cltd
    3c32:	41 f7 7a 30          	idivl  0x30(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3c36:	49 8b 72 28          	mov    0x28(%r10),%rsi
    3c3a:	48 63 d2             	movslq %edx,%rdx
    3c3d:	48 c1 e2 09          	shl    $0x9,%rdx
    3c41:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3c4c:	42 c7 84 26 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c58:	49 39 c8             	cmp    %rcx,%r8
    3c5b:	75 cb                	jne    3c28 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    3c5d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3c60:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3c64:	41 8b 57 34          	mov    0x34(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3c68:	48 8b 00             	mov    (%rax),%rax
    y++;
    3c6b:	39 78 30             	cmp    %edi,0x30(%rax)
    3c6e:	0f 4e fb             	cmovle %ebx,%edi
    3c71:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3c74:	85 d2                	test   %edx,%edx
    3c76:	74 0d                	je     3c85 <timer_thread+0x105>
    3c78:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3c7f:	0f 85 75 ff ff ff    	jne    3bfa <timer_thread+0x7a>
    3c85:	48 8d 3d ac 33 00 00 	lea    0x33ac(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3c8c:	e8 5f e6 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c91:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3c95:	85 d2                	test   %edx,%edx
    3c97:	7e 6b                	jle    3d04 <timer_thread+0x184>
    for (int y = 0 ; y < data->task_count ; y++) {
    3c99:	49 63 47 30          	movslq 0x30(%r15),%rax
    3c9d:	85 c0                	test   %eax,%eax
    3c9f:	7e 63                	jle    3d04 <timer_thread+0x184>
    3ca1:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3ca5:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3ca9:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3cb1:	31 ff                	xor    %edi,%edi
    3cb3:	48 89 c2             	mov    %rax,%rdx
    3cb6:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3cba:	48 8b 40 28          	mov    0x28(%rax),%rax
    3cbe:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3cc2:	f6 c6 02             	test   $0x2,%dh
    3cc5:	74 15                	je     3cdc <timer_thread+0x15c>
    3cc7:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3cd1:	48 05 00 02 00 00    	add    $0x200,%rax
    3cd7:	48 39 c6             	cmp    %rax,%rsi
    3cda:	74 1f                	je     3cfb <timer_thread+0x17b>
      data->threads[x]->tasks[y].sending = 0;
    3cdc:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3ce6:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3cec:	c7 80 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3cf6:	48 39 c6             	cmp    %rax,%rsi
    3cf9:	75 e1                	jne    3cdc <timer_thread+0x15c>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3cfb:	48 83 c7 08          	add    $0x8,%rdi
    3cff:	48 39 f9             	cmp    %rdi,%rcx
    3d02:	75 b2                	jne    3cb6 <timer_thread+0x136>
  asm volatile ("mfence" ::: "memory");
    3d04:	0f ae f0             	mfence
  struct timespec drain = {
    3d07:	66 0f 6f 05 a1 3c 00 00 	movdqa 0x3ca1(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    3d0f:	48 8d 2d 47 33 00 00 	lea    0x3347(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3d16:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d1b:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3d1f:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d24:	85 c0                	test   %eax,%eax
    3d26:	7e 4c                	jle    3d74 <timer_thread+0x1f4>
    3d28:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3d2c:	4d 63 c4             	movslq %r12d,%r8
    3d2f:	49 c1 e0 09          	shl    $0x9,%r8
    3d33:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3d37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3d40:	48 8b 19             	mov    (%rcx),%rbx
    3d43:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d45:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3d49:	99                   	cltd
    3d4a:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3d4d:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3d51:	48 63 d2             	movslq %edx,%rdx
    3d54:	48 c1 e2 09          	shl    $0x9,%rdx
    3d58:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3d63:	42 c7 84 06 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d6f:	4c 39 c9             	cmp    %r9,%rcx
    3d72:	75 cc                	jne    3d40 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    3d74:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3d77:	49 8b 47 10          	mov    0x10(%r15),%rax
    y++;
    3d7b:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3d7e:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3d81:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3d84:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3d88:	41 8b 7f 20          	mov    0x20(%r15),%edi
    3d8c:	85 ff                	test   %edi,%edi
    3d8e:	0f 8e bc 00 00 00    	jle    3e50 <timer_thread+0x2d0>
    3d94:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    3d97:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3d9d:	0f 1f 00             	nopl   (%rax)
    3da0:	4a 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbx
            all_empty = 0;
    3da8:	45 31 f6             	xor    %r14d,%r14d
    3dab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3db0:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3db4:	4c 89 f0             	mov    %r14,%rax
    3db7:	48 c1 e0 09          	shl    $0x9,%rax
    3dbb:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3dbf:	31 d2                	xor    %edx,%edx
    3dc1:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3dc8:	eb 16                	jmp    3de0 <timer_thread+0x260>
    3dca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3dd0:	4d 85 c0             	test   %r8,%r8
    3dd3:	7f 1f                	jg     3df4 <timer_thread+0x274>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3dd5:	83 c2 01             	add    $0x1,%edx
    3dd8:	48 83 c0 20          	add    $0x20,%rax
    3ddc:	39 fa                	cmp    %edi,%edx
    3dde:	74 2a                	je     3e0a <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3de0:	48 8b 08             	mov    (%rax),%rcx
    3de3:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3de7:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3deb:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3def:	48 85 c9             	test   %rcx,%rcx
    3df2:	7e dc                	jle    3dd0 <timer_thread+0x250>
    3df4:	bf 01 00 00 00       	mov    $0x1,%edi
    3df9:	48 89 ee             	mov    %rbp,%rsi
    3dfc:	31 c0                	xor    %eax,%eax
    3dfe:	e8 4d e6 ff ff       	call   2450 <__printf_chk@plt>
            break;
    3e03:	41 8b 7f 20          	mov    0x20(%r15),%edi
            all_empty = 0;
    3e07:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3e0a:	49 83 c6 01          	add    $0x1,%r14
    3e0e:	44 39 f7             	cmp    %r14d,%edi
    3e11:	7e 0d                	jle    3e20 <timer_thread+0x2a0>
    3e13:	49 8b 47 10          	mov    0x10(%r15),%rax
    3e17:	eb 97                	jmp    3db0 <timer_thread+0x230>
    3e19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3e20:	49 83 c5 01          	add    $0x1,%r13
    3e24:	44 39 ef             	cmp    %r13d,%edi
    3e27:	7e 0d                	jle    3e36 <timer_thread+0x2b6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3e29:	85 ff                	test   %edi,%edi
    3e2b:	7e 09                	jle    3e36 <timer_thread+0x2b6>
    3e2d:	49 8b 47 10          	mov    0x10(%r15),%rax
    3e31:	e9 6a ff ff ff       	jmp    3da0 <timer_thread+0x220>
    if (all_empty == 1) {
    3e36:	41 83 f9 01          	cmp    $0x1,%r9d
    3e3a:	74 14                	je     3e50 <timer_thread+0x2d0>
      nanosleep(&drain , &drainrem);
    3e3c:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3e41:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3e46:	e8 05 e5 ff ff       	call   2350 <nanosleep@plt>
    3e4b:	e9 cb fe ff ff       	jmp    3d1b <timer_thread+0x19b>
    3e50:	48 8d 3d fd 31 00 00 	lea    0x31fd(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3e57:	e8 94 e4 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3e5c:	41 8b 47 34          	mov    0x34(%r15),%eax
    3e60:	85 c0                	test   %eax,%eax
    3e62:	0f 84 cf 00 00 00    	je     3f37 <timer_thread+0x3b7>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3e68:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3e6c:	85 c9                	test   %ecx,%ecx
    3e6e:	7e 2d                	jle    3e9d <timer_thread+0x31d>
    3e70:	49 8b 47 10          	mov    0x10(%r15),%rax
    3e74:	31 db                	xor    %ebx,%ebx
    3e76:	48 8d 2d f1 31 00 00 	lea    0x31f1(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3e7d:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->running = 0;
    3e80:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3e84:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3e88:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3e8f:	0f 84 cf 00 00 00    	je     3f64 <timer_thread+0x3e4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3e95:	48 83 c3 01          	add    $0x1,%rbx
    3e99:	39 d9                	cmp    %ebx,%ecx
    3e9b:	7f e3                	jg     3e80 <timer_thread+0x300>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3e9d:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3ea1:	85 d2                	test   %edx,%edx
    3ea3:	7e 7b                	jle    3f20 <timer_thread+0x3a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3ea5:	49 63 47 30          	movslq 0x30(%r15),%rax
    3ea9:	85 c0                	test   %eax,%eax
    3eab:	7e 73                	jle    3f20 <timer_thread+0x3a0>
    3ead:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3eb1:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3eb5:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3ebd:	31 c9                	xor    %ecx,%ecx
    3ebf:	48 89 c6             	mov    %rax,%rsi
    3ec2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3ec8:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3ecc:	48 8b 40 28          	mov    0x28(%rax),%rax
    3ed0:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3ed4:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3eda:	74 1c                	je     3ef8 <timer_thread+0x378>
    3edc:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3ee6:	48 05 00 02 00 00    	add    $0x200,%rax
    3eec:	48 39 d0             	cmp    %rdx,%rax
    3eef:	74 26                	je     3f17 <timer_thread+0x397>
    3ef1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3ef8:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3f02:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3f08:	c7 80 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3f12:	48 39 d0             	cmp    %rdx,%rax
    3f15:	75 e1                	jne    3ef8 <timer_thread+0x378>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f17:	48 83 c1 08          	add    $0x8,%rcx
    3f1b:	48 39 f9             	cmp    %rdi,%rcx
    3f1e:	75 a8                	jne    3ec8 <timer_thread+0x348>
    asm volatile ("mfence" ::: "memory");
    3f20:	0f ae f0             	mfence
    3f23:	48 8d 3d 56 31 00 00 	lea    0x3156(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3f2a:	e8 c1 e3 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3f2f:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
    3f37:	48 8d 3d 49 31 00 00 	lea    0x3149(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3f3e:	e8 ad e3 ff ff       	call   22f0 <puts@plt>
}
    3f43:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3f48:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3f51:	75 47                	jne    3f9a <timer_thread+0x41a>
    3f53:	48 83 c4 58          	add    $0x58,%rsp
    3f57:	31 c0                	xor    %eax,%eax
    3f59:	5b                   	pop    %rbx
    3f5a:	5d                   	pop    %rbp
    3f5b:	41 5c                	pop    %r12
    3f5d:	41 5d                	pop    %r13
    3f5f:	41 5e                	pop    %r14
    3f61:	41 5f                	pop    %r15
    3f63:	c3                   	ret
    3f64:	48 89 ef             	mov    %rbp,%rdi
    3f67:	e8 84 e3 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3f6c:	49 8b 47 10          	mov    0x10(%r15),%rax
    3f70:	be 01 00 00 00       	mov    $0x1,%esi
    3f75:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3f79:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3f7d:	8b 78 50             	mov    0x50(%rax),%edi
    3f80:	e8 7b e4 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3f85:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3f89:	39 d9                	cmp    %ebx,%ecx
    3f8b:	0f 8e 0c ff ff ff    	jle    3e9d <timer_thread+0x31d>
    3f91:	49 8b 47 10          	mov    0x10(%r15),%rax
    3f95:	e9 e6 fe ff ff       	jmp    3e80 <timer_thread+0x300>
}
    3f9a:	e8 91 e3 ff ff       	call   2330 <__stack_chk_fail@plt>
    3f9f:	90                   	nop

0000000000003fa0 <strtolower>:
void strtolower(char *str) {
    3fa0:	f3 0f 1e fa          	endbr64
    3fa4:	55                   	push   %rbp
    3fa5:	53                   	push   %rbx
    3fa6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3faa:	48 0f be 1f          	movsbq (%rdi),%rbx
    3fae:	84 db                	test   %bl,%bl
    3fb0:	74 24                	je     3fd6 <strtolower+0x36>
    3fb2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3fb5:	e8 56 e5 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3fba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3fc0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3fc3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3fc7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3fca:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3fcd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3fd2:	84 db                	test   %bl,%bl
    3fd4:	75 ea                	jne    3fc0 <strtolower+0x20>
}
    3fd6:	48 83 c4 08          	add    $0x8,%rsp
    3fda:	5b                   	pop    %rbx
    3fdb:	5d                   	pop    %rbp
    3fdc:	c3                   	ret
    3fdd:	0f 1f 00             	nopl   (%rax)

0000000000003fe0 <zh_malloc>:
void *zh_malloc(size_t size) {
    3fe0:	f3 0f 1e fa          	endbr64
    3fe4:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3fe8:	e8 23 e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3fed:	48 85 c0             	test   %rax,%rax
    3ff0:	74 05                	je     3ff7 <zh_malloc+0x17>
}
    3ff2:	48 83 c4 08          	add    $0x8,%rsp
    3ff6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3ff7:	48 8b 0d 22 60 00 00 	mov    0x6022(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    3ffe:	ba 28 00 00 00       	mov    $0x28,%edx
    4003:	be 01 00 00 00       	mov    $0x1,%esi
    4008:	48 8d 3d 01 34 00 00 	lea    0x3401(%rip),%rdi        # 7410 <_IO_stdin_used+0x410>
    400f:	e8 ac e4 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4014:	bf 01 00 00 00       	mov    $0x1,%edi
    4019:	e8 82 e4 ff ff       	call   24a0 <exit@plt>
    401e:	66 90                	xchg   %ax,%ax

0000000000004020 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4020:	f3 0f 1e fa          	endbr64
    4024:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4025:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    402a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    402d:	e8 2e e3 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4032:	48 85 c0             	test   %rax,%rax
    4035:	74 11                	je     4048 <get_filename_ext+0x28>
    4037:	48 39 c3             	cmp    %rax,%rbx
    403a:	74 0c                	je     4048 <get_filename_ext+0x28>
    return dot + 1;
    403c:	48 83 c0 01          	add    $0x1,%rax
}
    4040:	5b                   	pop    %rbx
    4041:	c3                   	ret
    4042:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4048:	48 8d 05 80 30 00 00 	lea    0x3080(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    404f:	5b                   	pop    %rbx
    4050:	c3                   	ret
    4051:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    405c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004060 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4060:	f3 0f 1e fa          	endbr64
    4064:	41 55                	push   %r13
    4066:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4069:	48 89 fe             	mov    %rdi,%rsi
    406c:	41 54                	push   %r12
    406e:	55                   	push   %rbp
    406f:	48 89 d5             	mov    %rdx,%rbp
    4072:	ba 00 04 00 00       	mov    $0x400,%edx
    4077:	53                   	push   %rbx
    4078:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    407f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4088:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4090:	31 c0                	xor    %eax,%eax
    4092:	49 89 e4             	mov    %rsp,%r12
    4095:	4c 89 e7             	mov    %r12,%rdi
    4098:	e8 93 e3 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    409d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    40a2:	84 db                	test   %bl,%bl
    40a4:	74 24                	je     40ca <send_headers+0x6a>
        *str = (char)tolower(*str);
    40a6:	e8 65 e4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    40ab:	48 8b 08             	mov    (%rax),%rcx
    40ae:	4c 89 e0             	mov    %r12,%rax
    40b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    40b8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    40bb:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    40bf:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    40c2:	48 0f be 18          	movsbq (%rax),%rbx
    40c6:	84 db                	test   %bl,%bl
    40c8:	75 ee                	jne    40b8 <send_headers+0x58>
    void *buf = malloc(size);
    40ca:	bf 11 00 00 00       	mov    $0x11,%edi
    40cf:	e8 3c e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    40d4:	48 85 c0             	test   %rax,%rax
    40d7:	0f 84 7e 04 00 00    	je     455b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    40dd:	66 0f 6f 05 db 38 00 00 	movdqa 0x38db(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    iov[0].iov_base = zh_malloc(slen);
    40e5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    40e9:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    40ee:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    40f6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    40fa:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    40fd:	e8 0e e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4102:	48 85 c0             	test   %rax,%rax
    4105:	0f 84 50 04 00 00    	je     455b <send_headers+0x4fb>
    410b:	66 0f 6f 05 bd 38 00 00 	movdqa 0x38bd(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    iov[1].iov_base = zh_malloc(slen);
    4113:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4117:	4c 89 e7             	mov    %r12,%rdi
    411a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4124:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    412c:	0f 11 00             	movups %xmm0,(%rax)
    412f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4133:	be 2e 00 00 00       	mov    $0x2e,%esi
    4138:	e8 23 e2 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    413d:	48 85 c0             	test   %rax,%rax
    4140:	0f 84 ea 02 00 00    	je     4430 <send_headers+0x3d0>
    4146:	4c 39 e0             	cmp    %r12,%rax
    4149:	0f 84 e1 02 00 00    	je     4430 <send_headers+0x3d0>
    return dot + 1;
    414f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4153:	48 8d 3d 43 2f 00 00 	lea    0x2f43(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    415a:	48 89 de             	mov    %rbx,%rsi
    415d:	e8 4e e2 ff ff       	call   23b0 <strcmp@plt>
    4162:	85 c0                	test   %eax,%eax
    4164:	75 20                	jne    4186 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4166:	66 0f 6f 05 72 38 00 00 	movdqa 0x3872(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    416e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4176:	66 0f 6f 05 72 38 00 00 	movdqa 0x3872(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    417e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4186:	48 89 de             	mov    %rbx,%rsi
    4189:	48 8d 3d 11 2f 00 00 	lea    0x2f11(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    4190:	e8 1b e2 ff ff       	call   23b0 <strcmp@plt>
    4195:	85 c0                	test   %eax,%eax
    4197:	75 20                	jne    41b9 <send_headers+0x159>
    4199:	66 0f 6f 05 3f 38 00 00 	movdqa 0x383f(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    41a1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41a9:	66 0f 6f 05 3f 38 00 00 	movdqa 0x383f(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    41b1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    41b9:	48 89 de             	mov    %rbx,%rsi
    41bc:	48 8d 3d e3 2e 00 00 	lea    0x2ee3(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    41c3:	e8 e8 e1 ff ff       	call   23b0 <strcmp@plt>
    41c8:	85 c0                	test   %eax,%eax
    41ca:	0f 84 10 02 00 00    	je     43e0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    41d0:	48 89 de             	mov    %rbx,%rsi
    41d3:	48 8d 3d d0 2e 00 00 	lea    0x2ed0(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    41da:	e8 d1 e1 ff ff       	call   23b0 <strcmp@plt>
    41df:	85 c0                	test   %eax,%eax
    41e1:	0f 84 a9 02 00 00    	je     4490 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    41e7:	48 89 de             	mov    %rbx,%rsi
    41ea:	48 8d 3d bd 2e 00 00 	lea    0x2ebd(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    41f1:	e8 ba e1 ff ff       	call   23b0 <strcmp@plt>
    41f6:	85 c0                	test   %eax,%eax
    41f8:	0f 84 6a 02 00 00    	je     4468 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    41fe:	48 89 de             	mov    %rbx,%rsi
    4201:	48 8d 3d e9 2e 00 00 	lea    0x2ee9(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4208:	e8 a3 e1 ff ff       	call   23b0 <strcmp@plt>
    420d:	85 c0                	test   %eax,%eax
    420f:	0f 84 2b 02 00 00    	je     4440 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4215:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4218:	0f 84 52 01 00 00    	je     4370 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    421e:	48 89 de             	mov    %rbx,%rsi
    4221:	48 8d 3d 8a 2e 00 00 	lea    0x2e8a(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    4228:	e8 83 e1 ff ff       	call   23b0 <strcmp@plt>
    422d:	85 c0                	test   %eax,%eax
    422f:	0f 84 ab 02 00 00    	je     44e0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4235:	48 89 de             	mov    %rbx,%rsi
    4238:	48 8d 3d 77 2e 00 00 	lea    0x2e77(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    423f:	e8 6c e1 ff ff       	call   23b0 <strcmp@plt>
    4244:	85 c0                	test   %eax,%eax
    4246:	0f 84 6c 02 00 00    	je     44b8 <send_headers+0x458>
    slen = strlen(send_buffer);
    424c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4254:	4c 89 e7             	mov    %r12,%rdi
    4257:	e8 c4 e0 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    425c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    425f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4262:	e8 a9 e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4267:	48 85 c0             	test   %rax,%rax
    426a:	0f 84 eb 02 00 00    	je     455b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4270:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4274:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4278:	83 fb 08             	cmp    $0x8,%ebx
    427b:	0f 83 3f 01 00 00    	jae    43c0 <send_headers+0x360>
    4281:	f6 c3 04             	test   $0x4,%bl
    4284:	0f 85 7b 02 00 00    	jne    4505 <send_headers+0x4a5>
    428a:	85 db                	test   %ebx,%ebx
    428c:	74 13                	je     42a1 <send_headers+0x241>
    428e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4296:	88 10                	mov    %dl,(%rax)
    4298:	f6 c3 02             	test   $0x2,%bl
    429b:	0f 85 96 02 00 00    	jne    4537 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    42a1:	4d 89 e8             	mov    %r13,%r8
    42a4:	48 8d 0d 0f 2e 00 00 	lea    0x2e0f(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    42ab:	4c 89 e7             	mov    %r12,%rdi
    42ae:	31 c0                	xor    %eax,%eax
    42b0:	ba 00 04 00 00       	mov    $0x400,%edx
    42b5:	be 01 00 00 00       	mov    $0x1,%esi
    42ba:	e8 61 e2 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    42bf:	4c 89 e7             	mov    %r12,%rdi
    42c2:	e8 59 e0 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    42c7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    42ca:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    42cd:	e8 3e e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    42d2:	48 85 c0             	test   %rax,%rax
    42d5:	0f 84 80 02 00 00    	je     455b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    42db:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    42df:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    42e3:	83 fb 08             	cmp    $0x8,%ebx
    42e6:	0f 83 1c 01 00 00    	jae    4408 <send_headers+0x3a8>
    42ec:	f6 c3 04             	test   $0x4,%bl
    42ef:	0f 85 29 02 00 00    	jne    451e <send_headers+0x4be>
    42f5:	85 db                	test   %ebx,%ebx
    42f7:	74 13                	je     430c <send_headers+0x2ac>
    42f9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4301:	88 10                	mov    %dl,(%rax)
    4303:	f6 c3 02             	test   $0x2,%bl
    4306:	0f 85 3d 02 00 00    	jne    4549 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    430c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4311:	bf 02 00 00 00       	mov    $0x2,%edi
    4316:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    431e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4326:	e8 e5 e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    432b:	48 85 c0             	test   %rax,%rax
    432e:	0f 84 27 02 00 00    	je     455b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4334:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    433c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4340:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4348:	66 89 10             	mov    %dx,(%rax)
}
    434b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4353:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    435c:	0f 85 20 02 00 00    	jne    4582 <send_headers+0x522>
    4362:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4369:	5b                   	pop    %rbx
    436a:	5d                   	pop    %rbp
    436b:	41 5c                	pop    %r12
    436d:	41 5d                	pop    %r13
    436f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4370:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4374:	0f 85 a4 fe ff ff    	jne    421e <send_headers+0x1be>
    437a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    437e:	0f 85 9a fe ff ff    	jne    421e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4384:	66 0f 6f 05 b4 36 00 00 	movdqa 0x36b4(%rip),%xmm0        # 7a40 <_IO_stdin_used+0xa40>
    438c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4396:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    439e:	66 0f 6f 05 aa 36 00 00 	movdqa 0x36aa(%rip),%xmm0        # 7a50 <_IO_stdin_used+0xa50>
    43a6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    43ae:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    43b6:	e9 63 fe ff ff       	jmp    421e <send_headers+0x1be>
    43bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    43c0:	89 da                	mov    %ebx,%edx
    43c2:	48 89 c7             	mov    %rax,%rdi
    43c5:	4c 89 e6             	mov    %r12,%rsi
    43c8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    43cd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    43d2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    43d5:	c1 e9 03             	shr    $0x3,%ecx
    43d8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    43db:	e9 c1 fe ff ff       	jmp    42a1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    43e0:	66 0f 6f 05 f8 35 00 00 	movdqa 0x35f8(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    43e8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    43f0:	66 0f 6f 05 08 36 00 00 	movdqa 0x3608(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    43f8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4400:	e9 cb fd ff ff       	jmp    41d0 <send_headers+0x170>
    4405:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4408:	89 da                	mov    %ebx,%edx
    440a:	48 89 c7             	mov    %rax,%rdi
    440d:	4c 89 e6             	mov    %r12,%rsi
    4410:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4415:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    441a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    441d:	c1 e9 03             	shr    $0x3,%ecx
    4420:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4423:	e9 e4 fe ff ff       	jmp    430c <send_headers+0x2ac>
    4428:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4430:	48 8d 1d 98 2c 00 00 	lea    0x2c98(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4437:	e9 94 fd ff ff       	jmp    41d0 <send_headers+0x170>
    443c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4440:	66 0f 6f 05 d8 35 00 00 	movdqa 0x35d8(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    4448:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4450:	66 0f 6f 05 d8 35 00 00 	movdqa 0x35d8(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
    4458:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4460:	e9 b0 fd ff ff       	jmp    4215 <send_headers+0x1b5>
    4465:	0f 1f 00             	nopl   (%rax)
    4468:	66 0f 6f 05 b0 35 00 00 	movdqa 0x35b0(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    4470:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4478:	66 0f 6f 05 b0 35 00 00 	movdqa 0x35b0(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
    4480:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4488:	e9 71 fd ff ff       	jmp    41fe <send_headers+0x19e>
    448d:	0f 1f 00             	nopl   (%rax)
    4490:	66 0f 6f 05 48 35 00 00 	movdqa 0x3548(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    4498:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44a0:	66 0f 6f 05 68 35 00 00 	movdqa 0x3568(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    44a8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44b0:	e9 32 fd ff ff       	jmp    41e7 <send_headers+0x187>
    44b5:	0f 1f 00             	nopl   (%rax)
    44b8:	66 0f 6f 05 60 35 00 00 	movdqa 0x3560(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    44c0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44c8:	66 0f 6f 05 a0 35 00 00 	movdqa 0x35a0(%rip),%xmm0        # 7a70 <_IO_stdin_used+0xa70>
    44d0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    44d8:	e9 6f fd ff ff       	jmp    424c <send_headers+0x1ec>
    44dd:	0f 1f 00             	nopl   (%rax)
    44e0:	66 0f 6f 05 38 35 00 00 	movdqa 0x3538(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    44e8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44f0:	66 0f 6f 05 68 35 00 00 	movdqa 0x3568(%rip),%xmm0        # 7a60 <_IO_stdin_used+0xa60>
    44f8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4500:	e9 30 fd ff ff       	jmp    4235 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4505:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    450c:	89 db                	mov    %ebx,%ebx
    450e:	89 10                	mov    %edx,(%rax)
    4510:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4515:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4519:	e9 83 fd ff ff       	jmp    42a1 <send_headers+0x241>
    451e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4525:	89 db                	mov    %ebx,%ebx
    4527:	89 10                	mov    %edx,(%rax)
    4529:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    452e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4532:	e9 d5 fd ff ff       	jmp    430c <send_headers+0x2ac>
    4537:	89 db                	mov    %ebx,%ebx
    4539:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    453f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4544:	e9 58 fd ff ff       	jmp    42a1 <send_headers+0x241>
    4549:	89 db                	mov    %ebx,%ebx
    454b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4551:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4556:	e9 b1 fd ff ff       	jmp    430c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    455b:	48 8b 0d be 5a 00 00 	mov    0x5abe(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4562:	ba 28 00 00 00       	mov    $0x28,%edx
    4567:	be 01 00 00 00       	mov    $0x1,%esi
    456c:	48 8d 3d 9d 2e 00 00 	lea    0x2e9d(%rip),%rdi        # 7410 <_IO_stdin_used+0x410>
    4573:	e8 48 df ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4578:	bf 01 00 00 00       	mov    $0x1,%edi
    457d:	e8 1e df ff ff       	call   24a0 <exit@plt>
}
    4582:	e8 a9 dd ff ff       	call   2330 <__stack_chk_fail@plt>
    4587:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004590 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4590:	f3 0f 1e fa          	endbr64
    4594:	41 55                	push   %r13
    4596:	49 89 d5             	mov    %rdx,%r13
    4599:	41 54                	push   %r12
    459b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    459e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    45a1:	55                   	push   %rbp
    45a2:	53                   	push   %rbx
    45a3:	48 89 f3             	mov    %rsi,%rbx
    45a6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    45aa:	e8 61 de ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    45af:	48 85 c0             	test   %rax,%rax
    45b2:	74 6b                	je     461f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    45b4:	4c 89 e7             	mov    %r12,%rdi
    45b7:	48 89 c5             	mov    %rax,%rbp
    45ba:	31 f6                	xor    %esi,%esi
    45bc:	31 c0                	xor    %eax,%eax
    45be:	e8 bd de ff ff       	call   2480 <open@plt>
    45c3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    45c6:	85 c0                	test   %eax,%eax
    45c8:	0f 88 88 df ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    45ce:	48 89 da             	mov    %rbx,%rdx
    45d1:	48 89 ee             	mov    %rbp,%rsi
    45d4:	89 c7                	mov    %eax,%edi
    45d6:	e8 b5 dd ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    45db:	48 98                	cltq
    45dd:	48 39 d8             	cmp    %rbx,%rax
    45e0:	7c 1e                	jl     4600 <copy_file_contents+0x70>
    close(fd);
    45e2:	44 89 e7             	mov    %r12d,%edi
    45e5:	e8 86 dd ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    45ea:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    45ee:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    45f2:	48 83 c4 08          	add    $0x8,%rsp
    45f6:	5b                   	pop    %rbx
    45f7:	5d                   	pop    %rbp
    45f8:	41 5c                	pop    %r12
    45fa:	41 5d                	pop    %r13
    45fc:	c3                   	ret
    45fd:	0f 1f 00             	nopl   (%rax)
    4600:	48 8b 0d 19 5a 00 00 	mov    0x5a19(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4607:	ba 1a 00 00 00       	mov    $0x1a,%edx
    460c:	be 01 00 00 00       	mov    $0x1,%esi
    4611:	48 8d 3d b8 2a 00 00 	lea    0x2ab8(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    4618:	e8 a3 de ff ff       	call   24c0 <fwrite@plt>
    461d:	eb c3                	jmp    45e2 <copy_file_contents+0x52>
    461f:	48 8b 0d fa 59 00 00 	mov    0x59fa(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4626:	ba 28 00 00 00       	mov    $0x28,%edx
    462b:	be 01 00 00 00       	mov    $0x1,%esi
    4630:	48 8d 3d d9 2d 00 00 	lea    0x2dd9(%rip),%rdi        # 7410 <_IO_stdin_used+0x410>
    4637:	e8 84 de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    463c:	bf 01 00 00 00       	mov    $0x1,%edi
    4641:	e8 5a de ff ff       	call   24a0 <exit@plt>
    4646:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004650 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4650:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4654:	8b 46 44             	mov    0x44(%rsi),%eax
    4657:	48 89 fa             	mov    %rdi,%rdx
    465a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    465d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4663:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4666:	48 8b 07             	mov    (%rdi),%rax
    4669:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    466c:	f6 c1 02             	test   $0x2,%cl
    466f:	74 00                	je     4671 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4671:	89 f0                	mov    %esi,%eax
    4673:	44 29 c0             	sub    %r8d,%eax
    4676:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4679:	0f 82 e3 de ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    467f:	c1 e9 0a             	shr    $0xa,%ecx
    4682:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4686:	8b 47 44             	mov    0x44(%rdi),%eax
    4689:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    468c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    468f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4692:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4695:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4699:	d3 e0                	shl    %cl,%eax
    469b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    469e:	48 c1 e0 06          	shl    $0x6,%rax
    46a2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    46a6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    46ac:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    46af:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    46b3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    46b9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    46c1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    46c5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    46c8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    46cf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    46d7:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    46db:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    46df:	e8 5c dc ff ff       	call   2340 <io_uring_submit@plt>
}
    46e4:	31 c0                	xor    %eax,%eax
    46e6:	48 83 c4 08          	add    $0x8,%rsp
    46ea:	c3                   	ret
    46eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000046f0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    46f0:	f3 0f 1e fa          	endbr64
    46f4:	41 55                	push   %r13
    46f6:	41 89 fd             	mov    %edi,%r13d
    46f9:	41 54                	push   %r12
    46fb:	55                   	push   %rbp
    46fc:	53                   	push   %rbx
    46fd:	48 89 f3             	mov    %rsi,%rbx
    4700:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4704:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4707:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    470d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4710:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4713:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4715:	f6 c1 02             	test   $0x2,%cl
    4718:	74 00                	je     471a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    471a:	89 c2                	mov    %eax,%edx
    471c:	29 f2                	sub    %esi,%edx
    471e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4721:	0f 82 4b de ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4727:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    472a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    472d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4730:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4735:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4738:	23 6b 58             	and    0x58(%rbx),%ebp
    473b:	d3 e5                	shl    %cl,%ebp
    473d:	48 c1 e5 06          	shl    $0x6,%rbp
    4741:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4745:	e8 c6 dc ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    474a:	be 01 00 00 00       	mov    $0x1,%esi
    474f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4754:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4757:	e8 44 dc ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    475c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4761:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4765:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4768:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    476d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4772:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    477b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4783:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4787:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    478b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4792:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    479a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    479e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    47a6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    47ae:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    47b2:	e8 89 db ff ff       	call   2340 <io_uring_submit@plt>
}
    47b7:	48 83 c4 08          	add    $0x8,%rsp
    47bb:	31 c0                	xor    %eax,%eax
    47bd:	5b                   	pop    %rbx
    47be:	5d                   	pop    %rbp
    47bf:	41 5c                	pop    %r12
    47c1:	41 5d                	pop    %r13
    47c3:	c3                   	ret
    47c4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    47cf:	90                   	nop

00000000000047d0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    47d0:	f3 0f 1e fa          	endbr64
    47d4:	41 56                	push   %r14
    47d6:	41 89 f6             	mov    %esi,%r14d
    47d9:	41 55                	push   %r13
    47db:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    47de:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    47e3:	41 54                	push   %r12
    47e5:	55                   	push   %rbp
    47e6:	48 89 d5             	mov    %rdx,%rbp
    47e9:	53                   	push   %rbx
    void *buf = malloc(size);
    47ea:	e8 21 dc ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    47ef:	48 85 c0             	test   %rax,%rax
    47f2:	0f 84 dd 00 00 00    	je     48d5 <_send_static_string_content+0x105>
    47f8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    47fb:	4c 89 ef             	mov    %r13,%rdi
    47fe:	e8 1d db ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4803:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    480a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    480e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4811:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4814:	e8 f7 db ff ff       	call   2410 <malloc@plt>
    4819:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    481c:	48 85 c0             	test   %rax,%rax
    481f:	0f 84 b0 00 00 00    	je     48d5 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4825:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4829:	4c 89 e2             	mov    %r12,%rdx
    482c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    482f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4833:	e8 a8 db ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4838:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    483b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4841:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4844:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4848:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    484a:	f6 c1 02             	test   $0x2,%cl
    484d:	0f 85 7d 00 00 00    	jne    48d0 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4853:	89 d0                	mov    %edx,%eax
    4855:	29 f0                	sub    %esi,%eax
    4857:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    485a:	0f 82 1c dd ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4860:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4863:	8b 45 44             	mov    0x44(%rbp),%eax
    4866:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4869:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    486c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    486f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4872:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4878:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    487c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    487e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4881:	48 89 ef             	mov    %rbp,%rdi
    4884:	48 c1 e0 06          	shl    $0x6,%rax
    4888:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    488c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    488f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4893:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4899:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    48a1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    48a5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    48a8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    48af:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    48b7:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    48bb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    48bf:	5b                   	pop    %rbx
    48c0:	5d                   	pop    %rbp
    48c1:	41 5c                	pop    %r12
    48c3:	41 5d                	pop    %r13
    48c5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    48c7:	e9 74 da ff ff       	jmp    2340 <io_uring_submit@plt>
    48cc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    48d0:	e9 7e ff ff ff       	jmp    4853 <_send_static_string_content+0x83>
    48d5:	48 8b 0d 44 57 00 00 	mov    0x5744(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    48dc:	ba 28 00 00 00       	mov    $0x28,%edx
    48e1:	be 01 00 00 00       	mov    $0x1,%esi
    48e6:	48 8d 3d 23 2b 00 00 	lea    0x2b23(%rip),%rdi        # 7410 <_IO_stdin_used+0x410>
    48ed:	e8 ce db ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    48f2:	bf 01 00 00 00       	mov    $0x1,%edi
    48f7:	e8 a4 db ff ff       	call   24a0 <exit@plt>
    48fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004900 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4900:	f3 0f 1e fa          	endbr64
    4904:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4907:	89 fe                	mov    %edi,%esi
    4909:	48 8b 3d 08 57 00 00 	mov    0x5708(%rip),%rdi        # a018 <unimplemented_content>
    4910:	e9 bb fe ff ff       	jmp    47d0 <_send_static_string_content>
    4915:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004920 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4920:	f3 0f 1e fa          	endbr64
    4924:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4927:	89 fe                	mov    %edi,%esi
    4929:	48 8b 3d e0 56 00 00 	mov    0x56e0(%rip),%rdi        # a010 <http_404_content>
    4930:	e9 9b fe ff ff       	jmp    47d0 <_send_static_string_content>
    4935:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004940 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4940:	f3 0f 1e fa          	endbr64
    4944:	41 56                	push   %r14
    4946:	41 55                	push   %r13
    4948:	49 89 d5             	mov    %rdx,%r13
    494b:	41 54                	push   %r12
    494d:	41 89 f4             	mov    %esi,%r12d
    4950:	55                   	push   %rbp
    4951:	48 89 fd             	mov    %rdi,%rbp
    4954:	53                   	push   %rbx
    4955:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    495c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4965:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    496d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    496f:	e8 ac d9 ff ff       	call   2320 <strlen@plt>
    4974:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4979:	48 89 c3             	mov    %rax,%rbx
    497c:	0f 84 b6 00 00 00    	je     4a38 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4982:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4987:	48 89 ee             	mov    %rbp,%rsi
    498a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    498e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4993:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    499b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    49a3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    49ae:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    49b6:	e8 05 da ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    49bb:	48 89 e6             	mov    %rsp,%rsi
    49be:	4c 89 f7             	mov    %r14,%rdi
    49c1:	e8 0a da ff ff       	call   23d0 <stat@plt>
    49c6:	83 f8 ff             	cmp    $0xffffffff,%eax
    49c9:	0f 84 d3 00 00 00    	je     4aa2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    49cf:	8b 44 24 18          	mov    0x18(%rsp),%eax
    49d3:	25 00 f0 00 00       	and    $0xf000,%eax
    49d8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    49dd:	0f 84 f5 00 00 00    	je     4ad8 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    49e3:	48 8b 3d 26 56 00 00 	mov    0x5626(%rip),%rdi        # a010 <http_404_content>
    49ea:	4c 89 ea             	mov    %r13,%rdx
    49ed:	44 89 e6             	mov    %r12d,%esi
    49f0:	e8 db fd ff ff       	call   47d0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    49f5:	4c 89 f2             	mov    %r14,%rdx
    49f8:	bf 01 00 00 00       	mov    $0x1,%edi
    49fd:	31 c0                	xor    %eax,%eax
    49ff:	48 8d 35 1a 27 00 00 	lea    0x271a(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    4a06:	e8 45 da ff ff       	call   2450 <__printf_chk@plt>
}
    4a0b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4a13:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4a1c:	0f 85 20 01 00 00    	jne    4b42 <handle_get_method+0x202>
    4a22:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4a29:	5b                   	pop    %rbx
    4a2a:	5d                   	pop    %rbp
    4a2b:	41 5c                	pop    %r12
    4a2d:	41 5d                	pop    %r13
    4a2f:	41 5e                	pop    %r14
    4a31:	c3                   	ret
    4a32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a38:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a3d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4a45:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4a4a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a4d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a55:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a58:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4a60:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a6b:	e8 50 d9 ff ff       	call   23c0 <__memcpy_chk@plt>
    4a70:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4a75:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4a7a:	48 8d 35 6a 26 00 00 	lea    0x266a(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4a81:	48 29 d9             	sub    %rbx,%rcx
    4a84:	ba 0b 00 00 00       	mov    $0xb,%edx
    4a89:	e8 32 d9 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4a8e:	48 89 e6             	mov    %rsp,%rsi
    4a91:	4c 89 f7             	mov    %r14,%rdi
    4a94:	e8 37 d9 ff ff       	call   23d0 <stat@plt>
    4a99:	83 f8 ff             	cmp    $0xffffffff,%eax
    4a9c:	0f 85 2d ff ff ff    	jne    49cf <handle_get_method+0x8f>
    4aa2:	4c 89 f2             	mov    %r14,%rdx
    4aa5:	48 89 e9             	mov    %rbp,%rcx
    4aa8:	48 8d 35 47 26 00 00 	lea    0x2647(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    4aaf:	31 c0                	xor    %eax,%eax
    4ab1:	bf 01 00 00 00       	mov    $0x1,%edi
    4ab6:	e8 95 d9 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    4abb:	48 8b 3d 4e 55 00 00 	mov    0x554e(%rip),%rdi        # a010 <http_404_content>
    4ac2:	4c 89 ea             	mov    %r13,%rdx
    4ac5:	44 89 e6             	mov    %r12d,%esi
    4ac8:	e8 03 fd ff ff       	call   47d0 <_send_static_string_content>
}
    4acd:	e9 39 ff ff ff       	jmp    4a0b <handle_get_method+0xcb>
    4ad2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4ad8:	bf 70 00 00 00       	mov    $0x70,%edi
    4add:	e8 2e d9 ff ff       	call   2410 <malloc@plt>
    4ae2:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4ae5:	48 85 c0             	test   %rax,%rax
    4ae8:	74 5d                	je     4b47 <handle_get_method+0x207>
            req->client_socket = client_socket;
    4aea:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4aee:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4af3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4af7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    4afa:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4b01:	e8 5a f5 ff ff       	call   4060 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4b06:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4b0b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4b0f:	4c 89 f7             	mov    %r14,%rdi
    4b12:	e8 79 fa ff ff       	call   4590 <copy_file_contents>
    4b17:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4b1c:	4c 89 f2             	mov    %r14,%rdx
    4b1f:	31 c0                	xor    %eax,%eax
    4b21:	48 8d 35 e6 25 00 00 	lea    0x25e6(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4b28:	bf 01 00 00 00       	mov    $0x1,%edi
    4b2d:	e8 1e d9 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    4b32:	4c 89 ee             	mov    %r13,%rsi
    4b35:	48 89 df             	mov    %rbx,%rdi
    4b38:	e8 13 fb ff ff       	call   4650 <add_write_request>
    4b3d:	e9 c9 fe ff ff       	jmp    4a0b <handle_get_method+0xcb>
}
    4b42:	e8 e9 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4b47:	48 8b 0d d2 54 00 00 	mov    0x54d2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4b4e:	ba 28 00 00 00       	mov    $0x28,%edx
    4b53:	be 01 00 00 00       	mov    $0x1,%esi
    4b58:	48 8d 3d b1 28 00 00 	lea    0x28b1(%rip),%rdi        # 7410 <_IO_stdin_used+0x410>
    4b5f:	e8 5c d9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4b64:	bf 01 00 00 00       	mov    $0x1,%edi
    4b69:	e8 32 d9 ff ff       	call   24a0 <exit@plt>
    4b6e:	66 90                	xchg   %ax,%ax

0000000000004b70 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4b70:	f3 0f 1e fa          	endbr64
    4b74:	41 57                	push   %r15
    4b76:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4b78:	4c 8d 35 06 25 00 00 	lea    0x2506(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4b7f:	41 55                	push   %r13
    4b81:	49 89 d5             	mov    %rdx,%r13
    4b84:	41 54                	push   %r12
    4b86:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4b89:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4b8c:	55                   	push   %rbp
    4b8d:	53                   	push   %rbx
    4b8e:	48 83 ec 18          	sub    $0x18,%rsp
    4b92:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b9b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4ba0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4ba2:	49 89 e7             	mov    %rsp,%r15
    4ba5:	4c 89 fa             	mov    %r15,%rdx
    4ba8:	e8 d3 d7 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4bad:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4bb1:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4bb4:	84 db                	test   %bl,%bl
    4bb6:	74 1d                	je     4bd5 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4bb8:	e8 53 d9 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4bbd:	48 89 ea             	mov    %rbp,%rdx
    4bc0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4bc3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4bc7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4bca:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    4bcd:	48 0f be 1a          	movsbq (%rdx),%rbx
    4bd1:	84 db                	test   %bl,%bl
    4bd3:	75 eb                	jne    4bc0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4bd5:	4c 89 fa             	mov    %r15,%rdx
    4bd8:	4c 89 f6             	mov    %r14,%rsi
    4bdb:	31 ff                	xor    %edi,%edi
    4bdd:	e8 9e d7 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4be2:	48 8d 35 4a 25 00 00 	lea    0x254a(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4be9:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4bec:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    4bef:	e8 bc d7 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4bf4:	4c 89 ea             	mov    %r13,%rdx
    4bf7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4bfa:	85 c0                	test   %eax,%eax
    4bfc:	75 2a                	jne    4c28 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    4bfe:	48 89 df             	mov    %rbx,%rdi
    4c01:	e8 3a fd ff ff       	call   4940 <handle_get_method>
}
    4c06:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4c0b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4c14:	75 20                	jne    4c36 <handle_http_method+0xc6>
    4c16:	48 83 c4 18          	add    $0x18,%rsp
    4c1a:	5b                   	pop    %rbx
    4c1b:	5d                   	pop    %rbp
    4c1c:	41 5c                	pop    %r12
    4c1e:	41 5d                	pop    %r13
    4c20:	41 5e                	pop    %r14
    4c22:	41 5f                	pop    %r15
    4c24:	c3                   	ret
    4c25:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4c28:	48 8b 3d e9 53 00 00 	mov    0x53e9(%rip),%rdi        # a018 <unimplemented_content>
    4c2f:	e8 9c fb ff ff       	call   47d0 <_send_static_string_content>
}
    4c34:	eb d0                	jmp    4c06 <handle_http_method+0x96>
    4c36:	e8 f5 d6 ff ff       	call   2330 <__stack_chk_fail@plt>
    4c3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004c40 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4c40:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4c44:	85 d2                	test   %edx,%edx
    4c46:	7e 38                	jle    4c80 <get_line+0x40>
    4c48:	48 63 d2             	movslq %edx,%rdx
    4c4b:	48 83 c7 01          	add    $0x1,%rdi
    4c4f:	48 01 f2             	add    %rsi,%rdx
    4c52:	eb 11                	jmp    4c65 <get_line+0x25>
    4c54:	0f 1f 40 00          	nopl   0x0(%rax)
    4c58:	48 83 c6 01          	add    $0x1,%rsi
    4c5c:	48 83 c7 01          	add    $0x1,%rdi
    4c60:	48 39 d6             	cmp    %rdx,%rsi
    4c63:	74 1b                	je     4c80 <get_line+0x40>
        dest[i] = src[i];
    4c65:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4c69:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4c6b:	3c 0d                	cmp    $0xd,%al
    4c6d:	75 e9                	jne    4c58 <get_line+0x18>
    4c6f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4c72:	75 e4                	jne    4c58 <get_line+0x18>
            dest[i] = '\0';
    4c74:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4c77:	31 c0                	xor    %eax,%eax
    4c79:	c3                   	ret
    4c7a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4c80:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4c85:	c3                   	ret
    4c86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004c90 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4c90:	f3 0f 1e fa          	endbr64
    4c94:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4c9b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4c9f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4ca8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4cb0:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4cb2:	49 89 e2             	mov    %rsp,%r10
    4cb5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4cbd:	4c 89 d0             	mov    %r10,%rax
    4cc0:	eb 13                	jmp    4cd5 <handle_client_request+0x45>
    4cc2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4cc8:	48 83 c0 01          	add    $0x1,%rax
    4ccc:	48 83 c1 01          	add    $0x1,%rcx
    4cd0:	4c 39 c8             	cmp    %r9,%rax
    4cd3:	74 4b                	je     4d20 <handle_client_request+0x90>
        dest[i] = src[i];
    4cd5:	44 0f b6 01          	movzbl (%rcx),%r8d
    4cd9:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4cdc:	41 80 f8 0d          	cmp    $0xd,%r8b
    4ce0:	75 e6                	jne    4cc8 <handle_client_request+0x38>
    4ce2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4ce6:	75 e0                	jne    4cc8 <handle_client_request+0x38>
            dest[i] = '\0';
    4ce8:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4ceb:	8b 47 08             	mov    0x8(%rdi),%eax
    4cee:	48 89 f2             	mov    %rsi,%rdx
    4cf1:	4c 89 d7             	mov    %r10,%rdi
    4cf4:	89 c6                	mov    %eax,%esi
    4cf6:	e8 75 fe ff ff       	call   4b70 <handle_http_method>
}
    4cfb:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4d03:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d0c:	75 39                	jne    4d47 <handle_client_request+0xb7>
    4d0e:	31 c0                	xor    %eax,%eax
    4d10:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4d17:	c3                   	ret
    4d18:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4d20:	48 8b 0d f9 52 00 00 	mov    0x52f9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4d27:	ba 12 00 00 00       	mov    $0x12,%edx
    4d2c:	be 01 00 00 00       	mov    $0x1,%esi
    4d31:	48 8d 3d ff 23 00 00 	lea    0x23ff(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4d38:	e8 83 d7 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4d3d:	bf 01 00 00 00       	mov    $0x1,%edi
    4d42:	e8 59 d7 ff ff       	call   24a0 <exit@plt>
}
    4d47:	e8 e4 d5 ff ff       	call   2330 <__stack_chk_fail@plt>
    4d4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004d50 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4d50:	f3 0f 1e fa          	endbr64
    4d54:	55                   	push   %rbp
    4d55:	53                   	push   %rbx
    4d56:	48 89 cb             	mov    %rcx,%rbx
    4d59:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4d5d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4d60:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4d63:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4d69:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4d6c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4d6f:	f6 c1 02             	test   $0x2,%cl
    4d72:	74 00                	je     4d74 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4d74:	41 89 c0             	mov    %eax,%r8d
    4d77:	45 29 c8             	sub    %r9d,%r8d
    4d7a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4d7e:	0f 82 08 d8 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4d84:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d87:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4d8a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4d8d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4d90:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4d93:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d97:	d3 e5                	shl    %cl,%ebp
    4d99:	48 c1 e5 06          	shl    $0x6,%rbp
    4d9d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4da1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4da4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4da9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4db0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4db4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4db8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4dc0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4dc8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4dcc:	e8 3f d6 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4dd1:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4dd4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4dda:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4dde:	48 83 c4 08          	add    $0x8,%rsp
    4de2:	5b                   	pop    %rbx
    4de3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4de4:	e9 57 d5 ff ff       	jmp    2340 <io_uring_submit@plt>
    4de9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004df0 <io_thread>:
void* io_thread(void *arg) {
    4df0:	f3 0f 1e fa          	endbr64
    4df4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4df6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4df8:	41 56                	push   %r14
    4dfa:	41 55                	push   %r13
    4dfc:	41 54                	push   %r12
    4dfe:	55                   	push   %rbp
    4dff:	48 89 fd             	mov    %rdi,%rbp
    4e02:	53                   	push   %rbx
    4e03:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4e0a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4e13:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4e1b:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e1f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4e24:	bf 00 01 00 00       	mov    $0x100,%edi
    4e29:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4e2c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4e30:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4e35:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4e3a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4e3f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4e44:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4e4c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4e51:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4e59:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4e5e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4e66:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4e6b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4e73:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4e78:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4e80:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4e85:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4e8d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4e95:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4e9d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4ea5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4ead:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4eb5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4ebd:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4ec5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4ecd:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4ed5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4edd:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4ee4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4eec:	e8 ff d4 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4ef1:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
    4ef5:	31 f6                	xor    %esi,%esi
    4ef7:	e8 e4 d5 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4efc:	31 d2                	xor    %edx,%edx
    4efe:	be 01 00 00 00       	mov    $0x1,%esi
    4f03:	bf 02 00 00 00       	mov    $0x2,%edi
    4f08:	e8 23 d6 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4f0d:	83 f8 ff             	cmp    $0xffffffff,%eax
    4f10:	0f 84 b8 d6 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    4f16:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4f1b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4f21:	89 c7                	mov    %eax,%edi
    4f23:	41 89 c4             	mov    %eax,%r12d
    4f26:	ba 02 00 00 00       	mov    $0x2,%edx
    4f2b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4f30:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4f38:	e8 c3 d3 ff ff       	call   2300 <setsockopt@plt>
    4f3d:	85 c0                	test   %eax,%eax
    4f3f:	0f 88 5d d6 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4f45:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4f4a:	ba 10 00 00 00       	mov    $0x10,%edx
    4f4f:	44 89 e7             	mov    %r12d,%edi
    4f52:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4f5b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4f63:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4f6b:	e8 f0 d4 ff ff       	call   2460 <bind@plt>
    4f70:	85 c0                	test   %eax,%eax
    4f72:	0f 88 62 d6 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4f78:	be 0a 00 00 00       	mov    $0xa,%esi
    4f7d:	44 89 e7             	mov    %r12d,%edi
    4f80:	e8 9b d4 ff ff       	call   2420 <listen@plt>
    4f85:	85 c0                	test   %eax,%eax
    4f87:	0f 88 21 d6 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4f8d:	ba db 18 00 00       	mov    $0x18db,%edx
    4f92:	48 8d 35 e3 21 00 00 	lea    0x21e3(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4f99:	bf 01 00 00 00       	mov    $0x1,%edi
    4f9e:	31 c0                	xor    %eax,%eax
    4fa0:	e8 ab d4 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4fa5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4faa:	48 89 d9             	mov    %rbx,%rcx
    4fad:	44 89 e7             	mov    %r12d,%edi
    4fb0:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4fb5:	48 89 c6             	mov    %rax,%rsi
    4fb8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4fbd:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4fc2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4fca:	e8 81 fd ff ff       	call   4d50 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4fcf:	bf 01 00 00 00       	mov    $0x1,%edi
    4fd4:	be 10 00 00 00       	mov    $0x10,%esi
    4fd9:	e8 c2 d3 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    4fde:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4fe3:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4fe6:	e8 25 d4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4feb:	48 85 c0             	test   %rax,%rax
    4fee:	0f 84 ae 04 00 00    	je     54a2 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    4ff4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4ff8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4fff:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5006:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    500e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5011:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5016:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5018:	f6 c1 02             	test   $0x2,%cl
    501b:	0f 85 0f 04 00 00    	jne    5430 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5021:	89 d0                	mov    %edx,%eax
    5023:	29 f0                	sub    %esi,%eax
    5025:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    502c:	0f 82 92 d5 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5032:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5035:	48 8d 75 50          	lea    0x50(%rbp),%rsi
	sqe->addr3 = 0;
    5039:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    503d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5040:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5047:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    504a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5051:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5058:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    505a:	8b 55 50             	mov    0x50(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    505d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5062:	48 c1 e0 06          	shl    $0x6,%rax
    5066:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    506e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5074:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5077:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    507f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5083:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    508b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5093:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5097:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    509b:	e8 a0 d2 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    50a0:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    50a4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    50a9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    50b1:	0f 85 d7 01 00 00    	jne    528e <io_thread+0x49e>
    50b7:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    50bc:	4d 89 ce             	mov    %r9,%r14
    50bf:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    50c4:	0f 1f 40 00          	nopl   0x0(%rax)
    50c8:	48 8d 3d c3 20 00 00 	lea    0x20c3(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    50cf:	e8 1c d2 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    50d4:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    50db:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    50e2:	c1 e9 0b             	shr    $0xb,%ecx
    50e5:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    50e8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    50f0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    50f2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    50fa:	8b 16                	mov    (%rsi),%edx
		if (!available)
    50fc:	39 d0                	cmp    %edx,%eax
    50fe:	74 36                	je     5136 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5100:	89 f8                	mov    %edi,%eax
    5102:	21 d0                	and    %edx,%eax
    5104:	d3 e0                	shl    %cl,%eax
    5106:	48 c1 e0 04          	shl    $0x4,%rax
    510a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5112:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    511a:	0f 85 a8 01 00 00    	jne    52c8 <io_thread+0x4d8>
    5120:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5124:	0f 85 0e 03 00 00    	jne    5438 <io_thread+0x648>
			if (cqe->res < 0)
    512a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    512d:	83 c2 01             	add    $0x1,%edx
    5130:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5132:	85 c0                	test   %eax,%eax
    5134:	79 b2                	jns    50e8 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5136:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    513f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5140:	45 31 c0             	xor    %r8d,%r8d
    5143:	31 d2                	xor    %edx,%edx
    5145:	b9 01 00 00 00       	mov    $0x1,%ecx
    514a:	4c 89 f6             	mov    %r14,%rsi
    514d:	48 89 df             	mov    %rbx,%rdi
    5150:	e8 eb d2 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5155:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5158:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    515d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5161:	0f 84 e1 02 00 00    	je     5448 <io_thread+0x658>
    5167:	48 8d 3d 4a 20 00 00 	lea    0x204a(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    516e:	e8 7d d1 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5173:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5178:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    517b:	45 85 ff             	test   %r15d,%r15d
    517e:	0f 88 12 d4 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    5184:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5187:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    518b:	85 c0                	test   %eax,%eax
    518d:	0f 88 d5 02 00 00    	js     5468 <io_thread+0x678>
      switch (req->event_type) {
    5193:	41 83 f8 01          	cmp    $0x1,%r8d
    5197:	0f 84 7b 01 00 00    	je     5318 <io_thread+0x528>
    519d:	41 83 f8 02          	cmp    $0x2,%r8d
    51a1:	0f 84 a1 01 00 00    	je     5348 <io_thread+0x558>
    51a7:	45 85 c0             	test   %r8d,%r8d
    51aa:	0f 85 50 01 00 00    	jne    5300 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    51b0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    51b5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    51ba:	48 89 d9             	mov    %rbx,%rcx
    51bd:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    51c1:	e8 8a fb ff ff       	call   4d50 <add_accept_request>
              add_read_request(cqe->res, &ring);
    51c6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    51cb:	48 89 de             	mov    %rbx,%rsi
    51ce:	8b 78 08             	mov    0x8(%rax),%edi
    51d1:	e8 1a f5 ff ff       	call   46f0 <add_read_request>
              free(req);
    51d6:	4c 89 e7             	mov    %r12,%rdi
    51d9:	e8 e2 d0 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    51de:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    51e3:	48 85 c0             	test   %rax,%rax
    51e6:	0f 85 14 01 00 00    	jne    5300 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    51ec:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    51f3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    51fa:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    51fd:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5202:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5204:	f6 c1 02             	test   $0x2,%cl
    5207:	74 00                	je     5209 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5209:	89 d0                	mov    %edx,%eax
    520b:	29 f0                	sub    %esi,%eax
    520d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5214:	0f 82 a0 d3 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    521a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    521d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5222:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5226:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5229:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5230:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5233:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    523a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5241:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5243:	8b 55 50             	mov    0x50(%rbp),%edx
    5246:	48 c1 e0 06          	shl    $0x6,%rax
    524a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5252:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5258:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    525b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5263:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5267:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    526f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5277:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    527b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    527f:	e8 bc d0 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5284:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    5288:	0f 84 3a fe ff ff    	je     50c8 <io_thread+0x2d8>
    528e:	48 8d 3d 5c 1f 00 00 	lea    0x1f5c(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    5295:	e8 56 d0 ff ff       	call   22f0 <puts@plt>
}
    529a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    52a2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    52ab:	0f 85 18 02 00 00    	jne    54c9 <io_thread+0x6d9>
    52b1:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    52b8:	31 c0                	xor    %eax,%eax
    52ba:	5b                   	pop    %rbx
    52bb:	5d                   	pop    %rbp
    52bc:	41 5c                	pop    %r12
    52be:	41 5d                	pop    %r13
    52c0:	41 5e                	pop    %r14
    52c2:	41 5f                	pop    %r15
    52c4:	c3                   	ret
    52c5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    52c8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    52cd:	48 85 c0             	test   %rax,%rax
    52d0:	0f 84 6a fe ff ff    	je     5140 <io_thread+0x350>
      if (cqe->user_data == 1) {
    52d6:	48 83 38 01          	cmpq   $0x1,(%rax)
    52da:	0f 84 68 01 00 00    	je     5448 <io_thread+0x658>
    52e0:	48 8d 3d d1 1e 00 00 	lea    0x1ed1(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    52e7:	e8 04 d0 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    52ec:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    52f1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    52f4:	e9 8b fe ff ff       	jmp    5184 <io_thread+0x394>
    52f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5300:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5308:	8b 02                	mov    (%rdx),%eax
    530a:	83 c0 01             	add    $0x1,%eax
    530d:	89 02                	mov    %eax,(%rdx)
}
    530f:	e9 d8 fe ff ff       	jmp    51ec <io_thread+0x3fc>
    5314:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5318:	85 c0                	test   %eax,%eax
    531a:	75 74                	jne    5390 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    531c:	48 8b 0d fd 4c 00 00 	mov    0x4cfd(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5323:	ba 0f 00 00 00       	mov    $0xf,%edx
    5328:	be 01 00 00 00       	mov    $0x1,%esi
    532d:	48 8d 3d ad 1e 00 00 	lea    0x1ead(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    5334:	e8 87 d1 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5339:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    533e:	e9 a0 fe ff ff       	jmp    51e3 <io_thread+0x3f3>
    5343:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5348:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    534d:	45 31 ff             	xor    %r15d,%r15d
    5350:	85 c0                	test   %eax,%eax
    5352:	7e 20                	jle    5374 <io_thread+0x584>
    5354:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5358:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    535b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    535f:	48 c1 e0 04          	shl    $0x4,%rax
    5363:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5368:	e8 53 cf ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    536d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5372:	7f e4                	jg     5358 <io_thread+0x568>
              close(req->client_socket);
    5374:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5379:	e8 f2 cf ff ff       	call   2370 <close@plt>
              free(req);
    537e:	4c 89 e7             	mov    %r12,%rdi
    5381:	e8 3a cf ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5386:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    538b:	e9 53 fe ff ff       	jmp    51e3 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5390:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5395:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    539a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    53a2:	eb 11                	jmp    53b5 <io_thread+0x5c5>
    53a4:	0f 1f 40 00          	nopl   0x0(%rax)
    53a8:	48 83 c0 01          	add    $0x1,%rax
    53ac:	48 83 c2 01          	add    $0x1,%rdx
    53b0:	48 39 c6             	cmp    %rax,%rsi
    53b3:	74 4b                	je     5400 <io_thread+0x610>
        dest[i] = src[i];
    53b5:	0f b6 0a             	movzbl (%rdx),%ecx
    53b8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    53ba:	80 f9 0d             	cmp    $0xd,%cl
    53bd:	75 e9                	jne    53a8 <io_thread+0x5b8>
    53bf:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    53c3:	75 e3                	jne    53a8 <io_thread+0x5b8>
            dest[i] = '\0';
    53c5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    53c8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    53cd:	48 89 da             	mov    %rbx,%rdx
    53d0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    53d5:	e8 96 f7 ff ff       	call   4b70 <handle_http_method>
              free(req->iov[0].iov_base);
    53da:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    53df:	e8 dc ce ff ff       	call   22c0 <free@plt>
              free(req);
    53e4:	4c 89 e7             	mov    %r12,%rdi
    53e7:	e8 d4 ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    53ec:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    53f1:	e9 ed fd ff ff       	jmp    51e3 <io_thread+0x3f3>
    53f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5400:	48 8b 0d 19 4c 00 00 	mov    0x4c19(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5407:	ba 12 00 00 00       	mov    $0x12,%edx
    540c:	be 01 00 00 00       	mov    $0x1,%esi
    5411:	48 8d 3d 1f 1d 00 00 	lea    0x1d1f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5418:	e8 a3 d0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    541d:	bf 01 00 00 00       	mov    $0x1,%edi
    5422:	e8 79 d0 ff ff       	call   24a0 <exit@plt>
    5427:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5430:	e9 ec fb ff ff       	jmp    5021 <io_thread+0x231>
    5435:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5438:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    543d:	e9 94 fe ff ff       	jmp    52d6 <io_thread+0x4e6>
    5442:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5448:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5450:	48 8d 3d 4d 1d 00 00 	lea    0x1d4d(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    5457:	8b 02                	mov    (%rdx),%eax
    5459:	83 c0 01             	add    $0x1,%eax
    545c:	89 02                	mov    %eax,(%rdx)
    545e:	e8 8d ce ff ff       	call   22f0 <puts@plt>
    5463:	e9 26 fe ff ff       	jmp    528e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5468:	f7 d8                	neg    %eax
    546a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    546f:	89 c7                	mov    %eax,%edi
    5471:	e8 8a d0 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5476:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    547b:	be 01 00 00 00       	mov    $0x1,%esi
    5480:	48 8b 3d 99 4b 00 00 	mov    0x4b99(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5487:	48 89 c1             	mov    %rax,%rcx
    548a:	48 8d 15 af 1f 00 00 	lea    0x1faf(%rip),%rdx        # 7440 <_IO_stdin_used+0x440>
    5491:	31 c0                	xor    %eax,%eax
    5493:	e8 38 d0 ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5498:	bf 01 00 00 00       	mov    $0x1,%edi
    549d:	e8 fe cf ff ff       	call   24a0 <exit@plt>
    54a2:	48 8b 0d 77 4b 00 00 	mov    0x4b77(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    54a9:	ba 28 00 00 00       	mov    $0x28,%edx
    54ae:	be 01 00 00 00       	mov    $0x1,%esi
    54b3:	48 8d 3d 56 1f 00 00 	lea    0x1f56(%rip),%rdi        # 7410 <_IO_stdin_used+0x410>
    54ba:	e8 01 d0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    54bf:	bf 01 00 00 00       	mov    $0x1,%edi
    54c4:	e8 d7 cf ff ff       	call   24a0 <exit@plt>
}
    54c9:	e8 62 ce ff ff       	call   2330 <__stack_chk_fail@plt>
    54ce:	66 90                	xchg   %ax,%ax

00000000000054d0 <sendm>:
int sendm(struct BarrierTask *data) {
    54d0:	f3 0f 1e fa          	endbr64
    54d4:	41 57                	push   %r15
    54d6:	41 56                	push   %r14
    54d8:	41 55                	push   %r13
    54da:	41 54                	push   %r12
    54dc:	55                   	push   %rbp
    54dd:	53                   	push   %rbx
    54de:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    54e2:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
    54e9:	0f 85 99 01 00 00    	jne    5688 <sendm+0x1b8>
    54ef:	48 8d b7 80 01 00 00 	lea    0x180(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    54f6:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    54fc:	48 89 fa             	mov    %rdi,%rdx
    54ff:	31 c9                	xor    %ecx,%ecx
    5501:	48 89 34 24          	mov    %rsi,(%rsp)
    5505:	48 8d b7 88 01 00 00 	lea    0x188(%rdi),%rsi
    550c:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5511:	85 c0                	test   %eax,%eax
    5513:	0f 8e ce 00 00 00    	jle    55e7 <sendm+0x117>
    5519:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5520:	39 8a 30 01 00 00    	cmp    %ecx,0x130(%rdx)
    5526:	0f 84 af 00 00 00    	je     55db <sendm+0x10b>
        struct Data *them = data->mailboxes[n].higher;
    552c:	49 89 ca             	mov    %rcx,%r10
    552f:	49 c1 e2 05          	shl    $0x5,%r10
    5533:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
    553a:	4d 8b 5a 08          	mov    0x8(%r10),%r11
        for (; them->messages_count < min;) {
    553e:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    5542:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    5546:	4c 39 cb             	cmp    %r9,%rbx
    5549:	0f 8d 83 00 00 00    	jge    55d2 <sendm+0x102>
    554f:	4c 89 cf             	mov    %r9,%rdi
    5552:	48 8b aa 08 01 00 00 	mov    0x108(%rdx),%rbp
    5559:	4d 8b 72 10          	mov    0x10(%r10),%r14
    555d:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    5560:	49 8b 33             	mov    (%r11),%rsi
    5563:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    5567:	48 83 f8 02          	cmp    $0x2,%rax
    556b:	0f 86 ff 00 00 00    	jbe    5670 <sendm+0x1a0>
    5571:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5579:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5581:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    5585:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    5589:	4c 39 2c 24          	cmp    %r13,(%rsp)
    558d:	73 71                	jae    5600 <sendm+0x130>
    558f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5594:	4d 39 fc             	cmp    %r15,%r12
    5597:	73 67                	jae    5600 <sendm+0x130>
    5599:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    559d:	49 01 f0             	add    %rsi,%r8
    55a0:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    55a7:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    55ab:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    55af:	49 39 d8             	cmp    %rbx,%r8
    55b2:	75 ec                	jne    55a0 <sendm+0xd0>
    55b4:	0f 1f 40 00          	nopl   0x0(%rax)
    55b8:	48 01 fd             	add    %rdi,%rbp
    55bb:	4c 01 f7             	add    %r14,%rdi
    55be:	48 89 aa 08 01 00 00 	mov    %rbp,0x108(%rdx)
    55c5:	49 89 7a 10          	mov    %rdi,0x10(%r10)
    55c9:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    55cd:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    55d2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    55d5:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    55db:	48 83 c1 01          	add    $0x1,%rcx
    55df:	39 c8                	cmp    %ecx,%eax
    55e1:	0f 8f 39 ff ff ff    	jg     5520 <sendm+0x50>
}
    55e7:	48 83 c4 18          	add    $0x18,%rsp
    55eb:	31 c0                	xor    %eax,%eax
    55ed:	5b                   	pop    %rbx
    55ee:	5d                   	pop    %rbp
    55ef:	41 5c                	pop    %r12
    55f1:	41 5d                	pop    %r13
    55f3:	41 5e                	pop    %r14
    55f5:	41 5f                	pop    %r15
    55f7:	c3                   	ret
    55f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5600:	49 89 fd             	mov    %rdi,%r13
    5603:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    560a:	4d 89 e0             	mov    %r12,%r8
    560d:	49 d1 ed             	shr    %r13
    5610:	49 c1 e5 04          	shl    $0x4,%r13
    5614:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5619:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    561d:	41 83 e5 10          	and    $0x10,%r13d
    5621:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5625:	74 11                	je     5638 <sendm+0x168>
          them->messages[them->messages_count++] = data->message; 
    5627:	49 83 c0 10          	add    $0x10,%r8
    562b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5630:	4d 39 f8             	cmp    %r15,%r8
    5633:	74 15                	je     564a <sendm+0x17a>
    5635:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5638:	41 0f 11 00          	movups %xmm0,(%r8)
    563c:	49 83 c0 20          	add    $0x20,%r8
    5640:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    5645:	4d 39 f8             	cmp    %r15,%r8
    5648:	75 ee                	jne    5638 <sendm+0x168>
    564a:	49 89 f8             	mov    %rdi,%r8
    564d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    5651:	49 01 d8             	add    %rbx,%r8
    5654:	40 f6 c7 01          	test   $0x1,%dil
    5658:	0f 84 5a ff ff ff    	je     55b8 <sendm+0xe8>
          them->messages[them->messages_count++] = data->message; 
    565e:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    5665:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    5669:	e9 4a ff ff ff       	jmp    55b8 <sendm+0xe8>
    566e:	66 90                	xchg   %ax,%ax
    5670:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5678:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5680:	e9 14 ff ff ff       	jmp    5599 <sendm+0xc9>
    5685:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5688:	48 8d 3d 75 1b 00 00 	lea    0x1b75(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    568f:	e8 5c cc ff ff       	call   22f0 <puts@plt>
    5694:	e9 4e ff ff ff       	jmp    55e7 <sendm+0x117>
    5699:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000056a0 <receive>:
int receive(struct BarrierTask *data) {
    56a0:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    56a4:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    56aa:	85 c0                	test   %eax,%eax
    56ac:	0f 8e f1 00 00 00    	jle    57a3 <receive+0x103>
int receive(struct BarrierTask *data) {
    56b2:	41 54                	push   %r12
    56b4:	48 89 fa             	mov    %rdi,%rdx
    56b7:	55                   	push   %rbp
    56b8:	31 ed                	xor    %ebp,%ebp
    56ba:	53                   	push   %rbx
    56bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    56c0:	48 89 ee             	mov    %rbp,%rsi
    56c3:	48 c1 e6 05          	shl    $0x5,%rsi
    56c7:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    56ce:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    56d1:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    56d6:	48 85 ff             	test   %rdi,%rdi
    56d9:	0f 8e a1 00 00 00    	jle    5780 <receive+0xe0>
      data->sends++;
    56df:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    56e6:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    56ea:	4c 63 1a             	movslq (%rdx),%r11
    56ed:	49 89 c9             	mov    %rcx,%r9
    56f0:	48 8d 41 01          	lea    0x1(%rcx),%rax
    56f4:	49 f7 d9             	neg    %r9
    56f7:	48 01 c7             	add    %rax,%rdi
    56fa:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    56fe:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    5705:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    5709:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    570c:	49 29 c8             	sub    %rcx,%r8
    570f:	eb 10                	jmp    5721 <receive+0x81>
    5711:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5718:	48 83 c0 01          	add    $0x1,%rax
    571c:	48 39 c7             	cmp    %rax,%rdi
    571f:	74 5f                	je     5780 <receive+0xe0>
      data->n++;
    5721:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    5725:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
      data->n++;
    572c:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5733:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5737:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    573b:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5740:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5744:	75 d2                	jne    5718 <receive+0x78>
    5746:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    574d:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5751:	75 c5                	jne    5718 <receive+0x78>
    5753:	bf 01 00 00 00       	mov    $0x1,%edi
    5758:	b9 01 00 00 00       	mov    $0x1,%ecx
    575d:	ba 01 00 00 00       	mov    $0x1,%edx
    5762:	31 c0                	xor    %eax,%eax
    5764:	48 8d 35 fd 1c 00 00 	lea    0x1cfd(%rip),%rsi        # 7468 <_IO_stdin_used+0x468>
    576b:	e8 e0 cc ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5770:	bf 01 00 00 00       	mov    $0x1,%edi
    5775:	e8 26 cd ff ff       	call   24a0 <exit@plt>
    577a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5780:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    5789:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    578c:	48 83 c5 01          	add    $0x1,%rbp
    5790:	39 aa 34 01 00 00    	cmp    %ebp,0x134(%rdx)
    5796:	0f 8f 24 ff ff ff    	jg     56c0 <receive+0x20>
}
    579c:	5b                   	pop    %rbx
    579d:	31 c0                	xor    %eax,%eax
    579f:	5d                   	pop    %rbp
    57a0:	41 5c                	pop    %r12
    57a2:	c3                   	ret
    57a3:	31 c0                	xor    %eax,%eax
    57a5:	c3                   	ret
    57a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000057b0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    57b0:	f3 0f 1e fa          	endbr64
    57b4:	41 57                	push   %r15
    57b6:	41 56                	push   %r14
    57b8:	41 55                	push   %r13
    57ba:	41 54                	push   %r12
    57bc:	55                   	push   %rbp
    57bd:	53                   	push   %rbx
    57be:	48 89 fb             	mov    %rdi,%rbx
    57c1:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    57c5:	8b 07                	mov    (%rdi),%eax
    57c7:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    57cd:	0f 84 3d 01 00 00    	je     5910 <barriered_work+0x160>
    receive(data);
    57d3:	e8 c8 fe ff ff       	call   56a0 <receive>
    while (data->scheduled == 1) {
    57d8:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    57df:	75 1b                	jne    57fc <barriered_work+0x4c>
    57e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    57e8:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    57f0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    57f3:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    57fa:	74 ec                	je     57e8 <barriered_work+0x38>
  if (data->sending == 1) {
    57fc:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    5803:	0f 85 74 02 00 00    	jne    5a7d <barriered_work+0x2cd>
      for (int n = 0 ; n < data->thread_count; n++) {
    5809:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    580f:	85 c0                	test   %eax,%eax
    5811:	0f 8e 72 02 00 00    	jle    5a89 <barriered_work+0x2d9>
    5817:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    581e:	31 d2                	xor    %edx,%edx
    5820:	48 89 0c 24          	mov    %rcx,(%rsp)
    5824:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    582b:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    5830:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5836:	0f 84 bf 00 00 00    	je     58fb <barriered_work+0x14b>
        struct Data *them = data->mailboxes[n].higher;
    583c:	49 89 d1             	mov    %rdx,%r9
    583f:	49 c1 e1 05          	shl    $0x5,%r9
    5843:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    584a:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    584e:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5852:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5856:	4d 39 c3             	cmp    %r8,%r11
    5859:	0f 8d 93 00 00 00    	jge    58f2 <barriered_work+0x142>
    585f:	4c 89 c6             	mov    %r8,%rsi
    5862:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5869:	4d 8b 71 10          	mov    0x10(%r9),%r14
    586d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5870:	49 8b 0a             	mov    (%r10),%rcx
    5873:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5877:	48 83 f8 02          	cmp    $0x2,%rax
    587b:	0f 86 8f 02 00 00    	jbe    5b10 <barriered_work+0x360>
    5881:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5889:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5891:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5895:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5899:	4c 39 2c 24          	cmp    %r13,(%rsp)
    589d:	0f 83 fd 01 00 00    	jae    5aa0 <barriered_work+0x2f0>
    58a3:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    58a8:	4d 39 fc             	cmp    %r15,%r12
    58ab:	0f 83 ef 01 00 00    	jae    5aa0 <barriered_work+0x2f0>
    58b1:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    58b5:	48 01 cf             	add    %rcx,%rdi
    58b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    58c0:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    58c7:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    58cb:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    58cf:	49 39 fb             	cmp    %rdi,%r11
    58d2:	75 ec                	jne    58c0 <barriered_work+0x110>
    58d4:	0f 1f 40 00          	nopl   0x0(%rax)
    58d8:	48 01 f5             	add    %rsi,%rbp
    58db:	4c 01 f6             	add    %r14,%rsi
    58de:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    58e5:	49 89 71 10          	mov    %rsi,0x10(%r9)
    58e9:	4d 89 42 08          	mov    %r8,0x8(%r10)
    58ed:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    58f2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    58f5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    58fb:	48 83 c2 01          	add    $0x1,%rdx
    58ff:	39 d0                	cmp    %edx,%eax
    5901:	0f 8f 29 ff ff ff    	jg     5830 <barriered_work+0x80>
    5907:	e9 7d 01 00 00       	jmp    5a89 <barriered_work+0x2d9>
    590c:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    5910:	e8 8b fd ff ff       	call   56a0 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    5915:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    591c:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    591e:	45 85 c9             	test   %r9d,%r9d
    5921:	0f 8e 85 00 00 00    	jle    59ac <barriered_work+0x1fc>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5927:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    592e:	4c 63 d8             	movslq %eax,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    5931:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5934:	49 c1 e3 09          	shl    $0x9,%r11
    5938:	4c 8b 52 10          	mov    0x10(%rdx),%r10
              int next_task = abs((t + 1) % (data->thread_count));
    593c:	99                   	cltd
    593d:	41 f7 f9             	idiv   %r9d
    5940:	4c 89 d7             	mov    %r10,%rdi
    5943:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
    5947:	89 d0                	mov    %edx,%eax
    5949:	f7 d8                	neg    %eax
    594b:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    594e:	45 31 c0             	xor    %r8d,%r8d
              int next_task = abs((t + 1) % (data->thread_count));
    5951:	48 63 ea             	movslq %edx,%rbp
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5954:	48 c1 e5 09          	shl    $0x9,%rbp
    5958:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    5960:	31 c0                	xor    %eax,%eax
    5962:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5968:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    596c:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    5970:	48 8b 8c 2a 68 01 00 00 	mov    0x168(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5978:	48 8b 17             	mov    (%rdi),%rdx
    597b:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    597f:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5982:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5986:	48 c1 e2 05          	shl    $0x5,%rdx
    598a:	4a 03 94 1e 68 01 00 00 	add    0x168(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5992:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    5996:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    599a:	49 39 c1             	cmp    %rax,%r9
    599d:	75 c9                	jne    5968 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    599f:	48 83 c7 08          	add    $0x8,%rdi
    59a3:	49 83 c0 20          	add    $0x20,%r8
    59a7:	49 39 fc             	cmp    %rdi,%r12
    59aa:	75 b4                	jne    5960 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    59ac:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    59af:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    59b6:	31 ff                	xor    %edi,%edi
    59b8:	48 c1 e6 05          	shl    $0x5,%rsi
    59bc:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    59c3:	e8 48 c9 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    59c8:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    59cf:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    59d6:	48 8b 50 38          	mov    0x38(%rax),%rdx
    59da:	8b 4a 10             	mov    0x10(%rdx),%ecx
    59dd:	8d 69 01             	lea    0x1(%rcx),%ebp
    59e0:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    59e3:	75 53                	jne    5a38 <barriered_work+0x288>
    59e5:	0f 1f 00             	nopl   (%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    59e8:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    59ef:	48 8b 40 10          	mov    0x10(%rax),%rax
    59f3:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    59f6:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    59fe:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5a02:	48 c1 e7 09          	shl    $0x9,%rdi
    5a06:	48 03 78 28          	add    0x28(%rax),%rdi
    5a0a:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    5a10:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5a13:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    5a1a:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5a21:	74 c5                	je     59e8 <barriered_work+0x238>
    if (modcount != data->thread->protected_state->modcount) {
    5a23:	48 8b 40 38          	mov    0x38(%rax),%rax
    5a27:	3b 68 10             	cmp    0x10(%rax),%ebp
    5a2a:	74 0c                	je     5a38 <barriered_work+0x288>
    5a2c:	48 8d 3d dd 17 00 00 	lea    0x17dd(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    5a33:	e8 b8 c8 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5a38:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5a3f:	31 ff                	xor    %edi,%edi
    5a41:	48 c1 e6 05          	shl    $0x5,%rsi
    5a45:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5a4c:	48 83 c6 10          	add    $0x10,%rsi
    5a50:	e8 bb c8 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5a55:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    5a5c:	48 83 c0 01          	add    $0x1,%rax
    5a60:	48 99                	cqto
    5a62:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    5a69:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5a70:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    5a77:	0f 84 a8 00 00 00    	je     5b25 <barriered_work+0x375>
    5a7d:	48 8d 3d 80 17 00 00 	lea    0x1780(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5a84:	e8 67 c8 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5a89:	0f ae f8             	sfence
}
    5a8c:	48 83 c4 18          	add    $0x18,%rsp
    5a90:	31 c0                	xor    %eax,%eax
    5a92:	5b                   	pop    %rbx
    5a93:	5d                   	pop    %rbp
    5a94:	41 5c                	pop    %r12
    5a96:	41 5d                	pop    %r13
    5a98:	41 5e                	pop    %r14
    5a9a:	41 5f                	pop    %r15
    5a9c:	c3                   	ret
    5a9d:	0f 1f 00             	nopl   (%rax)
    5aa0:	49 89 f5             	mov    %rsi,%r13
    5aa3:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5aaa:	4c 89 e7             	mov    %r12,%rdi
    5aad:	49 d1 ed             	shr    %r13
    5ab0:	49 c1 e5 04          	shl    $0x4,%r13
    5ab4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5ab9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5abd:	41 83 e5 10          	and    $0x10,%r13d
    5ac1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5ac5:	74 11                	je     5ad8 <barriered_work+0x328>
          them->messages[them->messages_count++] = data->message; 
    5ac7:	48 83 c7 10          	add    $0x10,%rdi
    5acb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5ad0:	49 39 ff             	cmp    %rdi,%r15
    5ad3:	74 13                	je     5ae8 <barriered_work+0x338>
    5ad5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5ad8:	0f 11 07             	movups %xmm0,(%rdi)
    5adb:	48 83 c7 20          	add    $0x20,%rdi
    5adf:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5ae3:	49 39 ff             	cmp    %rdi,%r15
    5ae6:	75 f0                	jne    5ad8 <barriered_work+0x328>
    5ae8:	48 89 f7             	mov    %rsi,%rdi
    5aeb:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5aef:	4c 01 df             	add    %r11,%rdi
    5af2:	40 f6 c6 01          	test   $0x1,%sil
    5af6:	0f 84 dc fd ff ff    	je     58d8 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    5afc:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b03:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5b07:	e9 cc fd ff ff       	jmp    58d8 <barriered_work+0x128>
    5b0c:	0f 1f 40 00          	nopl   0x0(%rax)
    5b10:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5b18:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5b20:	e9 8c fd ff ff       	jmp    58b1 <barriered_work+0x101>
      for (int n = 0 ; n < data->thread_count; n++) {
    5b25:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    5b2c:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5b32:	31 d2                	xor    %edx,%edx
    5b34:	48 89 0c 24          	mov    %rcx,(%rsp)
    5b38:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    5b3f:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5b44:	85 c0                	test   %eax,%eax
    5b46:	0f 8e 3d ff ff ff    	jle    5a89 <barriered_work+0x2d9>
    5b4c:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5b50:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5b56:	0f 84 af 00 00 00    	je     5c0b <barriered_work+0x45b>
        struct Data *them = data->mailboxes[n].higher;
    5b5c:	49 89 d1             	mov    %rdx,%r9
    5b5f:	49 c1 e1 05          	shl    $0x5,%r9
    5b63:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    5b6a:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    5b6e:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5b72:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5b76:	4d 39 d8             	cmp    %r11,%r8
    5b79:	0f 8e 83 00 00 00    	jle    5c02 <barriered_work+0x452>
    5b7f:	4c 89 c6             	mov    %r8,%rsi
    5b82:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5b89:	4d 8b 71 10          	mov    0x10(%r9),%r14
    5b8d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5b90:	49 8b 0a             	mov    (%r10),%rcx
    5b93:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5b97:	48 83 f8 02          	cmp    $0x2,%rax
    5b9b:	0f 86 ef 00 00 00    	jbe    5c90 <barriered_work+0x4e0>
    5ba1:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5ba9:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5bb1:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5bb5:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5bb9:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5bbd:	73 61                	jae    5c20 <barriered_work+0x470>
    5bbf:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5bc4:	4d 39 fc             	cmp    %r15,%r12
    5bc7:	73 57                	jae    5c20 <barriered_work+0x470>
    5bc9:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5bcd:	48 01 cf             	add    %rcx,%rdi
    5bd0:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5bd7:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5bdb:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5bdf:	49 39 fb             	cmp    %rdi,%r11
    5be2:	75 ec                	jne    5bd0 <barriered_work+0x420>
    5be4:	0f 1f 40 00          	nopl   0x0(%rax)
    5be8:	48 01 f5             	add    %rsi,%rbp
    5beb:	4c 01 f6             	add    %r14,%rsi
    5bee:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5bf5:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5bf9:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5bfd:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5c02:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5c05:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5c0b:	48 83 c2 01          	add    $0x1,%rdx
    5c0f:	39 d0                	cmp    %edx,%eax
    5c11:	0f 8f 39 ff ff ff    	jg     5b50 <barriered_work+0x3a0>
    5c17:	e9 6d fe ff ff       	jmp    5a89 <barriered_work+0x2d9>
    5c1c:	0f 1f 40 00          	nopl   0x0(%rax)
    5c20:	49 89 f5             	mov    %rsi,%r13
    5c23:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5c2a:	4c 89 e7             	mov    %r12,%rdi
    5c2d:	49 d1 ed             	shr    %r13
    5c30:	49 c1 e5 04          	shl    $0x4,%r13
    5c34:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5c39:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5c3d:	41 83 e5 10          	and    $0x10,%r13d
    5c41:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5c45:	74 11                	je     5c58 <barriered_work+0x4a8>
          them->messages[them->messages_count++] = data->message; 
    5c47:	48 83 c7 10          	add    $0x10,%rdi
    5c4b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5c50:	4c 39 ff             	cmp    %r15,%rdi
    5c53:	74 13                	je     5c68 <barriered_work+0x4b8>
    5c55:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5c58:	0f 11 07             	movups %xmm0,(%rdi)
    5c5b:	48 83 c7 20          	add    $0x20,%rdi
    5c5f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5c63:	4c 39 ff             	cmp    %r15,%rdi
    5c66:	75 f0                	jne    5c58 <barriered_work+0x4a8>
    5c68:	48 89 f7             	mov    %rsi,%rdi
    5c6b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5c6f:	4c 01 df             	add    %r11,%rdi
    5c72:	40 f6 c6 01          	test   $0x1,%sil
    5c76:	0f 84 6c ff ff ff    	je     5be8 <barriered_work+0x438>
          them->messages[them->messages_count++] = data->message; 
    5c7c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5c83:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5c87:	e9 5c ff ff ff       	jmp    5be8 <barriered_work+0x438>
    5c8c:	0f 1f 40 00          	nopl   0x0(%rax)
    5c90:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5c98:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5ca0:	e9 24 ff ff ff       	jmp    5bc9 <barriered_work+0x419>
    5ca5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005cb0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5cb0:	f3 0f 1e fa          	endbr64
    5cb4:	41 56                	push   %r14
    5cb6:	41 55                	push   %r13
    5cb8:	49 89 fd             	mov    %rdi,%r13
    5cbb:	41 54                	push   %r12
    5cbd:	55                   	push   %rbp
    5cbe:	53                   	push   %rbx
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5cbf:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5cc6:	8b 86 ac 00 00 00    	mov    0xac(%rsi),%eax
    5ccc:	85 c0                	test   %eax,%eax
    5cce:	7e 50                	jle    5d20 <barriered_work_ingest+0x70>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5cd0:	48 8b 7e 40          	mov    0x40(%rsi),%rdi
    5cd4:	45 31 f6             	xor    %r14d,%r14d
    5cd7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5ce0:	4a 8b 0c f7          	mov    (%rdi,%r14,8),%rcx
    5ce4:	4e 8d 24 f5 00 00 00 00 	lea    0x0(,%r14,8),%r12
    5cec:	31 db                	xor    %ebx,%ebx
    5cee:	8b 11                	mov    (%rcx),%edx
    5cf0:	85 d2                	test   %edx,%edx
    5cf2:	7e 23                	jle    5d17 <barriered_work_ingest+0x67>
    5cf4:	48 8b 49 08          	mov    0x8(%rcx),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    5cf8:	48 89 dd             	mov    %rbx,%rbp
    5cfb:	48 c1 e5 05          	shl    $0x5,%rbp
    5cff:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    5d03:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5d07:	74 37                	je     5d40 <barriered_work_ingest+0x90>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5d09:	48 83 c3 01          	add    $0x1,%rbx
    5d0d:	39 da                	cmp    %ebx,%edx
    5d0f:	7f e7                	jg     5cf8 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5d11:	8b 86 ac 00 00 00    	mov    0xac(%rsi),%eax
    5d17:	49 83 c6 01          	add    $0x1,%r14
    5d1b:	44 39 f0             	cmp    %r14d,%eax
    5d1e:	7f c0                	jg     5ce0 <barriered_work_ingest+0x30>
  asm volatile ("sfence" ::: "memory");
    5d20:	0f ae f8             	sfence
  barriered_work(data);
    5d23:	4c 89 ef             	mov    %r13,%rdi
    5d26:	e8 85 fa ff ff       	call   57b0 <barriered_work>
}
    5d2b:	5b                   	pop    %rbx
    5d2c:	31 c0                	xor    %eax,%eax
    5d2e:	5d                   	pop    %rbp
    5d2f:	41 5c                	pop    %r12
    5d31:	41 5d                	pop    %r13
    5d33:	41 5e                	pop    %r14
    5d35:	c3                   	ret
    5d36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        data->ingest_count++;
    5d40:	49 83 85 60 01 00 00 01 	addq   $0x1,0x160(%r13)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5d48:	48 63 70 1c          	movslq 0x1c(%rax),%rsi
    5d4c:	bf 04 00 00 00       	mov    $0x4,%edi
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5d51:	48 83 c3 01          	add    $0x1,%rbx
        data->thread->buffers[b]->buffer[x].available = 0;
    5d55:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5d5c:	48 c1 e6 05          	shl    $0x5,%rsi
    5d60:	48 03 70 10          	add    0x10(%rax),%rsi
    5d64:	48 83 c6 10          	add    $0x10,%rsi
    5d68:	e8 a3 c5 ff ff       	call   2310 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5d6d:	49 8b b5 28 01 00 00 	mov    0x128(%r13),%rsi
    5d74:	48 8b 7e 40          	mov    0x40(%rsi),%rdi
    5d78:	4a 8b 0c 27          	mov    (%rdi,%r12,1),%rcx
    5d7c:	48 03 69 08          	add    0x8(%rcx),%rbp
    5d80:	8b 45 1c             	mov    0x1c(%rbp),%eax
    5d83:	83 c0 01             	add    $0x1,%eax
    5d86:	99                   	cltd
    5d87:	f7 7d 18             	idivl  0x18(%rbp)
    5d8a:	89 55 1c             	mov    %edx,0x1c(%rbp)
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5d8d:	8b 11                	mov    (%rcx),%edx
    5d8f:	39 da                	cmp    %ebx,%edx
    5d91:	0f 8f 5d ff ff ff    	jg     5cf4 <barriered_work_ingest+0x44>
    5d97:	e9 75 ff ff ff       	jmp    5d11 <barriered_work_ingest+0x61>
    5d9c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005da0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5da0:	f3 0f 1e fa          	endbr64
}
    5da4:	31 c0                	xor    %eax,%eax
    5da6:	c3                   	ret
    5da7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005db0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5db0:	f3 0f 1e fa          	endbr64
    5db4:	31 c0                	xor    %eax,%eax
    5db6:	c3                   	ret
    5db7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005dc0 <after>:
int after(struct timespec left, struct timespec right) {
    5dc0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5dc4:	31 c0                	xor    %eax,%eax
    5dc6:	48 39 d7             	cmp    %rdx,%rdi
    5dc9:	7e 08                	jle    5dd3 <after+0x13>
    5dcb:	31 c0                	xor    %eax,%eax
    5dcd:	48 39 ce             	cmp    %rcx,%rsi
    5dd0:	0f 9f c0             	setg   %al
}
    5dd3:	c3                   	ret
    5dd4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5ddf:	90                   	nop

0000000000005de0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5de0:	f3 0f 1e fa          	endbr64
    5de4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5de9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5dee:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5df0:	48 39 d7             	cmp    %rdx,%rdi
    5df3:	7f 18                	jg     5e0d <within+0x2d>
    5df5:	4d 39 d8             	cmp    %r11,%r8
    5df8:	0f 9e c2             	setle  %dl
    5dfb:	48 39 ce             	cmp    %rcx,%rsi
    5dfe:	0f 9e c0             	setle  %al
    5e01:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e03:	31 c0                	xor    %eax,%eax
    5e05:	4d 39 d1             	cmp    %r10,%r9
    5e08:	0f 9e c0             	setle  %al
    5e0b:	21 d0                	and    %edx,%eax
}
    5e0d:	c3                   	ret
    5e0e:	66 90                	xchg   %ax,%ax

0000000000005e10 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5e10:	f3 0f 1e fa          	endbr64
    5e14:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5e19:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5e1e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5e23:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5e28:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5e2d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5e32:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5e37:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5e3c:	48 39 fe             	cmp    %rdi,%rsi
    5e3f:	7d 2f                	jge    5e70 <overlap+0x60>
    5e41:	48 39 ca             	cmp    %rcx,%rdx
    5e44:	7d 62                	jge    5ea8 <overlap+0x98>
    5e46:	4d 39 da             	cmp    %r11,%r10
    5e49:	7d 0e                	jge    5e59 <overlap+0x49>
    return 1;
    5e4b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e50:	4d 39 c1             	cmp    %r8,%r9
    5e53:	0f 8c 7f 00 00 00    	jl     5ed8 <overlap+0xc8>
  return 0;
    5e59:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e5b:	4d 39 c1             	cmp    %r8,%r9
    5e5e:	7f 4c                	jg     5eac <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e60:	31 c0                	xor    %eax,%eax
    5e62:	4d 39 da             	cmp    %r11,%r10
    5e65:	0f 9e c0             	setle  %al
    5e68:	c3                   	ret
    5e69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5e70:	7e 4e                	jle    5ec0 <overlap+0xb0>
    5e72:	48 39 ca             	cmp    %rcx,%rdx
    5e75:	7f 39                	jg     5eb0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e77:	75 31                	jne    5eaa <overlap+0x9a>
    5e79:	4d 39 c1             	cmp    %r8,%r9
    5e7c:	7c 2c                	jl     5eaa <overlap+0x9a>
    return 1;
    5e7e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e83:	4d 39 da             	cmp    %r11,%r10
    5e86:	7d 24                	jge    5eac <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e88:	48 39 ca             	cmp    %rcx,%rdx
    5e8b:	0f 94 c2             	sete   %dl
    5e8e:	48 39 fe             	cmp    %rdi,%rsi
    5e91:	0f 94 c0             	sete   %al
    5e94:	21 c2                	and    %eax,%edx
    5e96:	31 c0                	xor    %eax,%eax
    5e98:	4d 39 c1             	cmp    %r8,%r9
    5e9b:	0f 94 c0             	sete   %al
    5e9e:	21 d0                	and    %edx,%eax
    5ea0:	c3                   	ret
    5ea1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5ea8:	74 af                	je     5e59 <overlap+0x49>
  return 0;
    5eaa:	31 c0                	xor    %eax,%eax
}
    5eac:	c3                   	ret
    5ead:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5eb0:	4d 39 da             	cmp    %r11,%r10
    5eb3:	7e c4                	jle    5e79 <overlap+0x69>
    return 1;
    5eb5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5eba:	4d 39 c1             	cmp    %r8,%r9
    5ebd:	7e ba                	jle    5e79 <overlap+0x69>
    5ebf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ec0:	48 39 ca             	cmp    %rcx,%rdx
    5ec3:	7c 94                	jl     5e59 <overlap+0x49>
    5ec5:	4d 39 c1             	cmp    %r8,%r9
    5ec8:	7d b4                	jge    5e7e <overlap+0x6e>
    5eca:	48 39 ca             	cmp    %rcx,%rdx
    5ecd:	74 91                	je     5e60 <overlap+0x50>
    5ecf:	eb d9                	jmp    5eaa <overlap+0x9a>
    5ed1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5ed8:	c3                   	ret
    5ed9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005ee0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5ee0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5ee4:	85 f6                	test   %esi,%esi
    5ee6:	0f 8e 44 03 00 00    	jle    6230 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    5eec:	41 57                	push   %r15
    5eee:	41 89 f7             	mov    %esi,%r15d
    5ef1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5ef3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5ef6:	41 55                	push   %r13
    5ef8:	41 54                	push   %r12
    5efa:	55                   	push   %rbp
    5efb:	53                   	push   %rbx
    5efc:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5f00:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5f04:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5f09:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5f0e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    5f11:	45 39 e6             	cmp    %r12d,%r14d
    5f14:	0f 84 4e 02 00 00    	je     6168 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5f1a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5f1f:	8b 50 08             	mov    0x8(%rax),%edx
    5f22:	85 d2                	test   %edx,%edx
    5f24:	0f 8e 3e 02 00 00    	jle    6168 <verify+0x288>
    5f2a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    5f2f:	31 c9                	xor    %ecx,%ecx
    5f31:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    5f36:	31 c0                	xor    %eax,%eax
    5f38:	44 89 f2             	mov    %r14d,%edx
    5f3b:	bf 01 00 00 00       	mov    $0x1,%edi
    5f40:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5f45:	48 8d 35 d4 12 00 00 	lea    0x12d4(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    5f4c:	e8 ff c4 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5f51:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5f56:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    5f5b:	8b 40 08             	mov    0x8(%rax),%eax
    5f5e:	85 c0                	test   %eax,%eax
    5f60:	0f 8e e6 01 00 00    	jle    614c <verify+0x26c>
    5f66:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5f69:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    5f6e:	31 db                	xor    %ebx,%ebx
    5f70:	48 c1 e0 09          	shl    $0x9,%rax
    5f74:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    5f79:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5f7e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5f83:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    5f88:	4c 8b 20             	mov    (%rax),%r12
    5f8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5f90:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    5f95:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5f9a:	49 89 de             	mov    %rbx,%r14
    5f9d:	48 8d 35 91 12 00 00 	lea    0x1291(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5fa4:	49 c1 e6 09          	shl    $0x9,%r14
    5fa8:	bf 01 00 00 00       	mov    $0x1,%edi
    5fad:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5fb1:	4b 8b 8c 3c 58 01 00 00 	mov    0x158(%r12,%r15,1),%rcx
    5fb9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    5fbe:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    5fc6:	31 c0                	xor    %eax,%eax
    5fc8:	e8 83 c4 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5fcd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5fd2:	4c 8b 20             	mov    (%rax),%r12
    5fd5:	4b 83 bc 3c 58 01 00 00 00 	cmpq   $0x0,0x158(%r12,%r15,1)
    5fde:	0f 8e 47 01 00 00    	jle    612b <verify+0x24b>
    5fe4:	4c 03 75 00          	add    0x0(%rbp),%r14
    5fe8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5fed:	ba 01 00 00 00       	mov    $0x1,%edx
    5ff2:	4d 89 f5             	mov    %r14,%r13
    5ff5:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    5ffc:	4d 85 f6             	test   %r14,%r14
    5fff:	0f 8e 21 01 00 00    	jle    6126 <verify+0x246>
    6005:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    6008:	48 89 d5             	mov    %rdx,%rbp
    600b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6010:	31 db                	xor    %ebx,%ebx
    6012:	4d 89 f2             	mov    %r14,%r10
    6015:	48 c1 e5 05          	shl    $0x5,%rbp
    6019:	48 83 ed 20          	sub    $0x20,%rbp
    601d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6021:	49 89 ee             	mov    %rbp,%r14
    6024:	48 89 dd             	mov    %rbx,%rbp
    6027:	48 89 d3             	mov    %rdx,%rbx
    602a:	eb 31                	jmp    605d <verify+0x17d>
    602c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6030:	4c 39 c2             	cmp    %r8,%rdx
    6033:	0f 8d 57 01 00 00    	jge    6190 <verify+0x2b0>
    6039:	4c 39 df             	cmp    %r11,%rdi
    603c:	7e 05                	jle    6043 <verify+0x163>
    603e:	49 39 c1             	cmp    %rax,%r9
    6041:	7c 75                	jl     60b8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6043:	4c 39 df             	cmp    %r11,%rdi
    6046:	0f 8d ab 01 00 00    	jge    61f7 <verify+0x317>
    604c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6050:	48 83 c5 01          	add    $0x1,%rbp
    6054:	49 39 ea             	cmp    %rbp,%r10
    6057:	0f 8e a9 00 00 00    	jle    6106 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    605d:	49 8b 97 48 01 00 00 	mov    0x148(%r15),%rdx
    6064:	48 89 e8             	mov    %rbp,%rax
    6067:	48 c1 e0 05          	shl    $0x5,%rax
    606b:	49 03 85 48 01 00 00 	add    0x148(%r13),%rax
    6072:	4c 01 f2             	add    %r14,%rdx
    6075:	48 8b 08             	mov    (%rax),%rcx
    6078:	48 8b 78 10          	mov    0x10(%rax),%rdi
    607c:	48 8b 32             	mov    (%rdx),%rsi
    607f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6083:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6087:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    608b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    608f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6093:	48 39 f1             	cmp    %rsi,%rcx
    6096:	7c 98                	jl     6030 <verify+0x150>
    6098:	0f 8e 42 01 00 00    	jle    61e0 <verify+0x300>
    609e:	4c 39 c2             	cmp    %r8,%rdx
    60a1:	0f 8f f9 00 00 00    	jg     61a0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    60a7:	75 a7                	jne    6050 <verify+0x170>
    60a9:	4c 39 df             	cmp    %r11,%rdi
    60ac:	7f a2                	jg     6050 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    60ae:	49 39 c1             	cmp    %rax,%r9
    60b1:	7c 9d                	jl     6050 <verify+0x170>
    60b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    60b8:	49 89 c1             	mov    %rax,%r9
    60bb:	48 89 f9             	mov    %rdi,%rcx
    60be:	48 89 f2             	mov    %rsi,%rdx
    60c1:	bf 01 00 00 00       	mov    $0x1,%edi
    60c6:	48 8d 35 c3 13 00 00 	lea    0x13c3(%rip),%rsi        # 7490 <_IO_stdin_used+0x490>
    60cd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60cf:	48 83 c5 01          	add    $0x1,%rbp
    60d3:	e8 78 c3 ff ff       	call   2450 <__printf_chk@plt>
    60d8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    60dd:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    60e2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60e5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60ea:	4d 8b 95 58 01 00 00 	mov    0x158(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60f1:	4c 8b 20             	mov    (%rax),%r12
    60f4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    60f9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60fd:	49 39 ea             	cmp    %rbp,%r10
    6100:	0f 8f 57 ff ff ff    	jg     605d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6106:	48 89 da             	mov    %rbx,%rdx
    6109:	49 3b 9f 58 01 00 00 	cmp    0x158(%r15),%rbx
    6110:	7d 14                	jge    6126 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6112:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    6119:	48 83 c2 01          	add    $0x1,%rdx
    611d:	4d 85 f6             	test   %r14,%r14
    6120:	0f 8f e2 fe ff ff    	jg     6008 <verify+0x128>
    6126:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    612b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6130:	48 83 c3 01          	add    $0x1,%rbx
    6134:	39 58 08             	cmp    %ebx,0x8(%rax)
    6137:	0f 8f 53 fe ff ff    	jg     5f90 <verify+0xb0>
    613d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6142:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6147:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    614c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6151:	48 83 c1 01          	add    $0x1,%rcx
    6155:	39 48 08             	cmp    %ecx,0x8(%rax)
    6158:	0f 8f d8 fd ff ff    	jg     5f36 <verify+0x56>
    615e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6163:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6168:	48 81 44 24 10 b0 00 00 00 	addq   $0xb0,0x10(%rsp)
    6171:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6176:	41 39 c7             	cmp    %eax,%r15d
    6179:	0f 84 86 00 00 00    	je     6205 <verify+0x325>
    617f:	41 89 c4             	mov    %eax,%r12d
    6182:	e9 8a fd ff ff       	jmp    5f11 <verify+0x31>
    6187:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6190:	0f 85 ba fe ff ff    	jne    6050 <verify+0x170>
    6196:	e9 a8 fe ff ff       	jmp    6043 <verify+0x163>
    619b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    61a0:	49 39 c1             	cmp    %rax,%r9
    61a3:	7e 09                	jle    61ae <verify+0x2ce>
    61a5:	4c 39 df             	cmp    %r11,%rdi
    61a8:	0f 8c 0a ff ff ff    	jl     60b8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    61ae:	4c 39 df             	cmp    %r11,%rdi
    61b1:	0f 8f 99 fe ff ff    	jg     6050 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    61b7:	49 39 c1             	cmp    %rax,%r9
    61ba:	0f 8d f8 fe ff ff    	jge    60b8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    61c0:	48 39 f1             	cmp    %rsi,%rcx
    61c3:	0f 85 87 fe ff ff    	jne    6050 <verify+0x170>
    61c9:	4c 39 c2             	cmp    %r8,%rdx
    61cc:	0f 85 7e fe ff ff    	jne    6050 <verify+0x170>
    61d2:	4c 39 df             	cmp    %r11,%rdi
    61d5:	0f 84 dd fe ff ff    	je     60b8 <verify+0x1d8>
    61db:	e9 70 fe ff ff       	jmp    6050 <verify+0x170>
    61e0:	4c 39 c2             	cmp    %r8,%rdx
    61e3:	0f 8c 5a fe ff ff    	jl     6043 <verify+0x163>
    61e9:	4c 39 df             	cmp    %r11,%rdi
    61ec:	7e c9                	jle    61b7 <verify+0x2d7>
    61ee:	4c 39 c2             	cmp    %r8,%rdx
    61f1:	0f 85 59 fe ff ff    	jne    6050 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    61f7:	49 39 c1             	cmp    %rax,%r9
    61fa:	0f 8f 50 fe ff ff    	jg     6050 <verify+0x170>
    6200:	e9 b3 fe ff ff       	jmp    60b8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    6205:	48 81 44 24 18 b0 00 00 00 	addq   $0xb0,0x18(%rsp)
    620e:	41 8d 46 01          	lea    0x1(%r14),%eax
    6212:	45 39 e6             	cmp    %r12d,%r14d
    6215:	74 08                	je     621f <verify+0x33f>
    6217:	41 89 c6             	mov    %eax,%r14d
    621a:	e9 ea fc ff ff       	jmp    5f09 <verify+0x29>
}
    621f:	48 83 c4 58          	add    $0x58,%rsp
    6223:	31 c0                	xor    %eax,%eax
    6225:	5b                   	pop    %rbx
    6226:	5d                   	pop    %rbp
    6227:	41 5c                	pop    %r12
    6229:	41 5d                	pop    %r13
    622b:	41 5e                	pop    %r14
    622d:	41 5f                	pop    %r15
    622f:	c3                   	ret
    6230:	31 c0                	xor    %eax,%eax
    6232:	c3                   	ret

Disassembly of section .fini:

0000000000006234 <_fini>:
    6234:	f3 0f 1e fa          	endbr64
    6238:	48 83 ec 08          	sub    $0x8,%rsp
    623c:	48 83 c4 08          	add    $0x8,%rsp
    6240:	c3                   	ret
