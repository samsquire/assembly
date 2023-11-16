
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
    2743:	be b0 00 00 00       	mov    $0xb0,%esi
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
    27f5:	0f 84 26 0e 00 00    	je     3621 <main+0x1031>
      my_thread_data[0] = &thread_data[other]; 
    27fb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    2800:	4d 89 e8             	mov    %r13,%r8
    2803:	89 ea                	mov    %ebp,%edx
    2805:	bf 01 00 00 00       	mov    $0x1,%edi
    280a:	49 8d 8d 50 ff ff ff 	lea    -0xb0(%r13),%rcx
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
    283c:	4d 89 65 38          	mov    %r12,0x38(%r13)
    2840:	45 8b 45 00          	mov    0x0(%r13),%r8d
    2844:	44 89 f1             	mov    %r14d,%ecx
    2847:	89 ea                	mov    %ebp,%edx
    2849:	48 8d 35 20 4d 00 00 	lea    0x4d20(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    2850:	bf 01 00 00 00       	mov    $0x1,%edi
    2855:	31 c0                	xor    %eax,%eax
      CPU_SET(j, sendercpu);
    2857:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    285d:	e8 ee fb ff ff       	call   2450 <__printf_chk@plt>
    thread_data[x].other = other;
    2862:	45 89 b5 a8 00 00 00 	mov    %r14d,0xa8(%r13)
    for (int j = 0 ; j < cores / 2 ; j++) {
    2869:	45 31 f6             	xor    %r14d,%r14d
    286c:	0f 1f 40 00          	nopl   0x0(%rax)
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
    28a3:	49 89 9d a0 00 00 00 	mov    %rbx,0xa0(%r13)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28aa:	31 db                	xor    %ebx,%ebx
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28ac:	be 10 00 00 00       	mov    $0x10,%esi
    thread_data[x].real_thread_index = x;
    28b1:	41 89 6d 04          	mov    %ebp,0x4(%r13)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28b5:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].threads = my_thread_data;
    28ba:	49 89 45 10          	mov    %rax,0x10(%r13)
    thread_data[x].thread_count = 2;
    28be:	48 8b 05 7b 51 00 00 	mov    0x517b(%rip),%rax        # 7a40 <_IO_stdin_used+0xa40>
    thread_data[x].task_count = total_barrier_count;
    28c5:	41 c7 45 30 03 00 00 00 	movl   $0x3,0x30(%r13)
    thread_data[x].thread_count = 2;
    28cd:	49 89 45 18          	mov    %rax,0x18(%r13)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28d1:	e8 ca fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28d6:	be 10 00 00 00       	mov    $0x10,%esi
    28db:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28e0:	49 89 45 58          	mov    %rax,0x58(%r13)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28e4:	e8 b7 fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28e9:	be 28 00 00 00       	mov    $0x28,%esi
    28ee:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    28f3:	66 0f 6f 15 25 51 00 00 	movdqa 0x5125(%rip),%xmm2        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28fb:	49 89 45 60          	mov    %rax,0x60(%r13)
    thread_data[x].timestamp_count = 0;
    28ff:	41 0f 11 55 70       	movups %xmm2,0x70(%r13)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2904:	e8 97 fa ff ff       	call   23a0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2909:	be 00 02 00 00       	mov    $0x200,%esi
    290e:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
    2913:	66 0f 6f 1d 05 51 00 00 	movdqa 0x5105(%rip),%xmm3        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    291b:	49 89 85 80 00 00 00 	mov    %rax,0x80(%r13)
    thread_data[x].task_timestamp_count = 0;
    2922:	41 0f 11 9d 88 00 00 00 	movups %xmm3,0x88(%r13)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    292a:	e8 71 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    292f:	44 89 7c 24 28       	mov    %r15d,0x28(%rsp)
      thread_data[x].tasks = barriers;
    2934:	49 89 45 28          	mov    %rax,0x28(%r13)
        thread_data[x].tasks[y].sending = 1;
    2938:	49 89 c4             	mov    %rax,%r12
    293b:	89 6c 24 08          	mov    %ebp,0x8(%rsp)
        thread_data[x].tasks[y].protected = do_protected_write; 
    293f:	48 63 eb             	movslq %ebx,%rbp
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2942:	be 20 00 00 00       	mov    $0x20,%esi
    2947:	bf 0c 00 00 00       	mov    $0xc,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    294c:	49 89 ef             	mov    %rbp,%r15
    294f:	48 8d 05 4a 0e 00 00 	lea    0xe4a(%rip),%rax        # 37a0 <do_protected_write>
    2956:	49 c1 e7 09          	shl    $0x9,%r15
    295a:	4d 01 fc             	add    %r15,%r12
    295d:	49 89 84 24 20 01 00 00 	mov    %rax,0x120(%r12)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2965:	e8 36 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    296a:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    296e:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    2973:	49 89 c6             	mov    %rax,%r14
    2976:	49 89 84 24 68 01 00 00 	mov    %rax,0x168(%r12)
        for (int b = 0 ; b < 2 ; b++) {
    297e:	4c 8d 60 40          	lea    0x40(%rax),%r12
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2982:	be 08 00 00 00       	mov    $0x8,%esi
    2987:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    298c:	49 83 c6 20          	add    $0x20,%r14
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2990:	e8 0b fa ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2995:	be 08 00 00 00       	mov    $0x8,%esi
    299a:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    299f:	48 89 c5             	mov    %rax,%rbp
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29a2:	e8 f9 f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29a7:	be 18 00 00 00       	mov    $0x18,%esi
    29ac:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29b1:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29b4:	e8 e7 f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    29b9:	66 0f 6f 05 6f 50 00 00 	movdqa 0x506f(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
          mailboxes[b].higher = &data[1];
    29c1:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29c5:	49 89 46 e0          	mov    %rax,-0x20(%r14)
          mailboxes[b].higher = &data[1];
    29c9:	49 89 76 e8          	mov    %rsi,-0x18(%r14)
          data[0].messages = messages;
    29cd:	48 89 28             	mov    %rbp,(%rax)
          data[1].messages = messages2;
    29d0:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    29d4:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    29d8:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    29dc:	4d 39 e6             	cmp    %r12,%r14
    29df:	75 a1                	jne    2982 <main+0x392>
        char *message = malloc(sizeof(char) * 256);
    29e1:	be 01 00 00 00       	mov    $0x1,%esi
    29e6:	bf 00 01 00 00       	mov    $0x100,%edi
    29eb:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    29ef:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    29f4:	e8 a7 f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    29f9:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    29fe:	49 89 c4             	mov    %rax,%r12
        struct Message *messaged = malloc(sizeof(struct Message));
    2a01:	e8 0a fa ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a06:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    2a0b:	4c 89 e7             	mov    %r12,%rdi
    2a0e:	41 89 d9             	mov    %ebx,%r9d
    2a11:	ba 00 01 00 00       	mov    $0x100,%edx
    2a16:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2a1b:	be 01 00 00 00       	mov    $0x1,%esi
    2a20:	31 c0                	xor    %eax,%eax
    2a22:	48 8d 0d 97 4b 00 00 	lea    0x4b97(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a29:	e8 f2 fa ff ff       	call   2520 <__sprintf_chk@plt>
        messaged->message = message;
    2a2e:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
        messaged->thread_index = thread_data[x].thread_index;
    2a33:	49 63 45 00          	movslq 0x0(%r13),%rax
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a37:	8d 4b 01             	lea    0x1(%rbx),%ecx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a3a:	be 20 00 00 00       	mov    $0x20,%esi
    2a3f:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a44:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
        messaged->message = message;
    2a48:	4d 89 22             	mov    %r12,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a4b:	4d 8b 65 28          	mov    0x28(%r13),%r12
        messaged->task_index = y;
    2a4f:	49 89 6a 10          	mov    %rbp,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a53:	4b 8d 2c 3c          	lea    (%r12,%r15,1),%rbp
        messaged->thread_index = thread_data[x].thread_index;
    2a57:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a5b:	89 8d 88 01 00 00    	mov    %ecx,0x188(%rbp)
        thread_data[x].tasks[y].message = messaged;
    2a61:	4c 89 95 80 01 00 00 	mov    %r10,0x180(%rbp)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a68:	48 c7 85 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%rbp)
        messaged->thread_index = thread_data[x].thread_index;
    2a73:	89 44 24 18          	mov    %eax,0x18(%rsp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a77:	e8 24 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a7c:	8b 54 24 18          	mov    0x18(%rsp),%edx
        if (y == barrier_count - 1) {
    2a80:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2a83:	89 5d 00             	mov    %ebx,0x0(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a86:	48 89 85 48 01 00 00 	mov    %rax,0x148(%rbp)
        if (y == barrier_count - 1) {
    2a8d:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
        thread_data[x].tasks[y].available = 1;
    2a91:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2a9b:	48 89 85 38 01 00 00 	mov    %rax,0x138(%rbp)
        thread_data[x].tasks[y].sending = 1;
    2aa2:	48 b8 01 00 00 00 0c 00 00 00 	movabs $0xc00000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2aac:	48 c7 85 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%rbp)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2ab7:	89 95 30 01 00 00    	mov    %edx,0x130(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2abd:	4c 89 ad 28 01 00 00 	mov    %r13,0x128(%rbp)
        thread_data[x].tasks[y].arrived = 0;
    2ac4:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        thread_data[x].tasks[y].thread_count = 2;
    2ace:	c7 85 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%rbp)
        thread_data[x].tasks[y].sending = 1;
    2ad8:	48 89 85 78 01 00 00 	mov    %rax,0x178(%rbp)
        if (y == barrier_count - 1) {
    2adf:	0f 84 24 0b 00 00    	je     3609 <main+0x1019>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2ae5:	8b 54 24 08          	mov    0x8(%rsp),%edx
    2ae9:	39 d3                	cmp    %edx,%ebx
    2aeb:	75 63                	jne    2b50 <main+0x560>
    2aed:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    2af1:	85 db                	test   %ebx,%ebx
    2af3:	7f 5b                	jg     2b50 <main+0x560>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2af5:	bf 01 00 00 00       	mov    $0x1,%edi
    2afa:	48 8d 35 e7 4a 00 00 	lea    0x4ae7(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2b01:	31 c0                	xor    %eax,%eax
    2b03:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
    2b07:	e8 44 f9 ff ff       	call   2450 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b0c:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    2b11:	48 63 c3             	movslq %ebx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b14:	4d 8b 65 28          	mov    0x28(%r13),%r12
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b18:	48 89 c7             	mov    %rax,%rdi
    2b1b:	48 c1 e0 04          	shl    $0x4,%rax
    2b1f:	48 01 c8             	add    %rcx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b22:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b26:	49 89 45 40          	mov    %rax,0x40(%r13)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b2a:	48 8d 05 bf 31 00 00 	lea    0x31bf(%rip),%rax        # 5cf0 <barriered_work_ingest>
    2b31:	4b 89 84 3c 18 01 00 00 	mov    %rax,0x118(%r12,%r15,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b39:	8d 47 01             	lea    0x1(%rdi),%eax
    2b3c:	89 44 24 20          	mov    %eax,0x20(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b40:	83 f9 03             	cmp    $0x3,%ecx
    2b43:	74 1e                	je     2b63 <main+0x573>
    2b45:	bb 01 00 00 00       	mov    $0x1,%ebx
    2b4a:	e9 f0 fd ff ff       	jmp    293f <main+0x34f>
    2b4f:	90                   	nop
            thread_data[x].tasks[y].run = barriered_work; 
    2b50:	48 8d 05 99 2c 00 00 	lea    0x2c99(%rip),%rax        # 57f0 <barriered_work>
    2b57:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b5e:	83 f9 03             	cmp    $0x3,%ecx
    2b61:	75 e2                	jne    2b45 <main+0x555>
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b63:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b6d:	66 0f 6f 64 24 30    	movdqa 0x30(%rsp),%xmm4
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2b73:	41 c7 84 24 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r12)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b7f:	49 89 84 24 34 05 00 00 	mov    %rax,0x534(%r12)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b87:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2b8c:	41 c7 84 24 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%r12)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2b98:	41 8b 45 00          	mov    0x0(%r13),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2b9c:	4d 89 ac 24 28 05 00 00 	mov    %r13,0x528(%r12)
  for (int x = 0 ; x < total_threads ; x++) {
    2ba4:	49 81 c5 b0 00 00 00 	add    $0xb0,%r13
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bab:	41 89 84 24 30 05 00 00 	mov    %eax,0x530(%r12)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2bb3:	41 c7 84 24 7c 05 00 00 0c 00 00 00 	movl   $0xc,0x57c(%r12)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2bbf:	41 c7 84 24 3c 05 00 00 03 00 00 00 	movl   $0x3,0x53c(%r12)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2bcb:	41 0f 11 a4 24 18 05 00 00 	movups %xmm4,0x518(%r12)
  for (int x = 0 ; x < total_threads ; x++) {
    2bd4:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    2bd9:	41 83 ff 0f          	cmp    $0xf,%r15d
    2bdd:	0f 85 dd fb ff ff    	jne    27c0 <main+0x1d0>
    2be3:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    2be8:	ba 0d 00 00 00       	mov    $0xd,%edx
    2bed:	48 8d 35 24 47 00 00 	lea    0x4724(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2bf4:	31 c0                	xor    %eax,%eax
    2bf6:	bf 01 00 00 00       	mov    $0x1,%edi
    2bfb:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    2c00:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2c05:	e8 46 f8 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c0a:	be 08 00 00 00       	mov    $0x8,%esi
    2c0f:	bf 02 00 00 00       	mov    $0x2,%edi
    2c14:	e8 87 f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2c19:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c1e:	bf 0f 00 00 00       	mov    $0xf,%edi
    my_thread_data[0] = &thread_data[x]; 
    2c23:	4d 8d ba f0 08 00 00 	lea    0x8f0(%r10),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c2a:	4d 8d b2 60 01 00 00 	lea    0x160(%r10),%r14
    thread_data[x].threads = my_thread_data;
    2c31:	49 89 82 00 09 00 00 	mov    %rax,0x900(%r10)
    my_thread_data[0] = &thread_data[x]; 
    2c38:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c3b:	49 8d 8a 10 02 00 00 	lea    0x210(%r10),%rcx
    2c42:	49 8d 92 70 03 00 00 	lea    0x370(%r10),%rdx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c49:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c4d:	49 8b 42 28          	mov    0x28(%r10),%rax
    2c51:	4d 8d 9a d0 04 00 00 	lea    0x4d0(%r10),%r11
    2c58:	4d 8d 8a 80 05 00 00 	lea    0x580(%r10),%r9
    2c5f:	49 8d b2 c0 02 00 00 	lea    0x2c0(%r10),%rsi
    2c66:	49 8d 9a 20 04 00 00 	lea    0x420(%r10),%rbx
    thread_data[x].thread_count = 2;
    2c6d:	41 c7 82 08 09 00 00 02 00 00 00 	movl   $0x2,0x908(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2c78:	48 89 4c 24 58       	mov    %rcx,0x58(%rsp)
    2c7d:	4d 8d 82 30 06 00 00 	lea    0x630(%r10),%r8
    2c84:	4d 8d aa e0 06 00 00 	lea    0x6e0(%r10),%r13
    2c8b:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    2c90:	4d 8d a2 90 07 00 00 	lea    0x790(%r10),%r12
    thread_data[x].thread_index = 0;
    2c97:	41 c7 82 f0 08 00 00 00 00 00 00 	movl   $0x0,0x8f0(%r10)
    thread_data[x].task_count = total_barrier_count;
    2ca2:	41 c7 82 20 09 00 00 03 00 00 00 	movl   $0x3,0x920(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2cad:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cb7:	49 8d 82 b0 00 00 00 	lea    0xb0(%r10),%rax
    2cbe:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2cc3:	49 8b 82 d8 00 00 00 	mov    0xd8(%r10),%rax
    2cca:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    2ccf:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cd9:	49 8b 82 88 01 00 00 	mov    0x188(%r10),%rax
    2ce0:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2ce5:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cef:	49 8b 82 38 02 00 00 	mov    0x238(%r10),%rax
    my_thread_data[0] = &thread_data[x]; 
    2cf6:	4c 89 7c 24 70       	mov    %r15,0x70(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2cfb:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d05:	49 8b 82 e8 02 00 00 	mov    0x2e8(%r10),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2d0c:	4c 89 74 24 78       	mov    %r14,0x78(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d11:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d1b:	49 8b 82 98 03 00 00 	mov    0x398(%r10),%rax
    2d22:	48 89 74 24 50       	mov    %rsi,0x50(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d27:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2d2c:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d36:	49 8b 82 48 04 00 00 	mov    0x448(%r10),%rax
    2d3d:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    2d42:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d4c:	49 8b 82 f8 04 00 00 	mov    0x4f8(%r10),%rax
    2d53:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d5d:	49 8b 82 a8 05 00 00 	mov    0x5a8(%r10),%rax
    2d64:	4c 89 44 24 30       	mov    %r8,0x30(%rsp)
    2d69:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d73:	49 8b 82 58 06 00 00 	mov    0x658(%r10),%rax
    2d7a:	4c 89 94 24 80 00 00 00 	mov    %r10,0x80(%rsp)
    2d82:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d8c:	49 8b 82 08 07 00 00 	mov    0x708(%r10),%rax
    2d93:	4c 89 6c 24 20       	mov    %r13,0x20(%rsp)
    2d98:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2da2:	49 8b 82 b8 07 00 00 	mov    0x7b8(%r10),%rax
    2da9:	4c 89 64 24 10       	mov    %r12,0x10(%rsp)
    2dae:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2db8:	e8 e3 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dbd:	be 38 00 00 00       	mov    $0x38,%esi
    2dc2:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dc7:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dca:	e8 d1 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dcf:	be 38 00 00 00       	mov    $0x38,%esi
    2dd4:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2dd9:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ddc:	e8 bf f5 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2de1:	be 38 00 00 00       	mov    $0x38,%esi
    2de6:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2deb:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2df3:	e8 a8 f5 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2df8:	be 08 00 00 00       	mov    $0x8,%esi
    2dfd:	bf 0f 00 00 00       	mov    $0xf,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2e02:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e0a:	e8 91 f5 ff ff       	call   23a0 <calloc@plt>
  thread_data[thread_count].type = TIMER;
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2e0f:	be 08 00 00 00       	mov    $0x8,%esi
    2e14:	bf 0f 00 00 00       	mov    $0xf,%edi
  thread_data[thread_count].type = TIMER;
    2e19:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2e21:	49 89 c5             	mov    %rax,%r13
  thread_data[thread_count].task_count = total_barrier_count;
    2e24:	48 8b 05 1d 4c 00 00 	mov    0x4c1d(%rip),%rax        # 7a48 <_IO_stdin_used+0xa48>
  thread_data[thread_count].type = TIMER;
    2e2b:	41 c7 82 48 08 00 00 00 00 00 00 	movl   $0x0,0x848(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2e36:	49 89 82 70 08 00 00 	mov    %rax,0x870(%r10)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2e3d:	e8 5e f5 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2e42:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    2e47:	48 8b 4c 24 58       	mov    0x58(%rsp),%rcx
    2e4c:	48 8b 74 24 50       	mov    0x50(%rsp),%rsi
    2e51:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    2e56:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2e5a:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    2e5f:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2e64:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2e68:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    2e6d:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
    2e75:	48 89 48 18          	mov    %rcx,0x18(%rax)
    2e79:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
    2e7e:	48 89 70 20          	mov    %rsi,0x20(%rax)
    2e82:	48 8d 35 9e 44 00 00 	lea    0x449e(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2e89:	48 89 78 30          	mov    %rdi,0x30(%rax)
    2e8d:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    2e92:	4d 8d b2 40 08 00 00 	lea    0x840(%r10),%r14
    2e99:	4c 89 10             	mov    %r10,(%rax)
    2e9c:	48 89 78 50          	mov    %rdi,0x50(%rax)
    2ea0:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    2ea5:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2ea9:	ba 0c 00 00 00       	mov    $0xc,%edx
    2eae:	48 89 78 58          	mov    %rdi,0x58(%rax)
    2eb2:	49 8d ba a0 09 00 00 	lea    0x9a0(%r10),%rdi
    2eb9:	4c 89 58 38          	mov    %r11,0x38(%rax)
    2ebd:	4c 89 48 40          	mov    %r9,0x40(%rax)
    2ec1:	4c 89 40 48          	mov    %r8,0x48(%rax)
    2ec5:	4c 89 70 60          	mov    %r14,0x60(%rax)
    2ec9:	4c 89 78 68          	mov    %r15,0x68(%rax)
    2ecd:	4c 8d 3d 7c 09 00 00 	lea    0x97c(%rip),%r15        # 3850 <barriered_thread>
    2ed4:	48 89 78 70          	mov    %rdi,0x70(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2ed8:	49 89 82 50 08 00 00 	mov    %rax,0x850(%r10)
    2edf:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2ee1:	41 c7 82 58 08 00 00 0c 00 00 00 	movl   $0xc,0x858(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2eec:	41 c7 82 60 08 00 00 02 00 00 00 	movl   $0x2,0x860(%r10)
  thread_data[thread_count].thread_index = 0;
    2ef7:	41 c7 82 40 08 00 00 00 00 00 00 	movl   $0x0,0x840(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2f02:	48 89 bc 24 80 00 00 00 	mov    %rdi,0x80(%rsp)
    2f0a:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].thread_index = 0;
    2f0f:	4c 89 94 24 98 00 00 00 	mov    %r10,0x98(%rsp)
    2f17:	e8 34 f5 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2f1c:	48 8d b3 a0 02 00 00 	lea    0x2a0(%rbx),%rsi
    2f23:	49 8d 7d 60          	lea    0x60(%r13),%rdi
    2f27:	4c 89 f1             	mov    %r14,%rcx
    2f2a:	48 8d 15 8f 0c 00 00 	lea    0xc8f(%rip),%rdx        # 3bc0 <timer_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    2f31:	45 31 f6             	xor    %r14d,%r14d
    2f34:	4c 89 eb             	mov    %r13,%rbx
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2f37:	e8 34 f5 ff ff       	call   2470 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2f3c:	44 89 f0             	mov    %r14d,%eax
    2f3f:	4d 89 ee             	mov    %r13,%r14
    2f42:	41 89 c5             	mov    %eax,%r13d
    thread_data[x].type = WORKER;
    2f45:	c7 45 08 01 00 00 00 	movl   $0x1,0x8(%rbp)
    2f4c:	44 89 ea             	mov    %r13d,%edx
    2f4f:	bf 01 00 00 00       	mov    $0x1,%edi
    2f54:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2f56:	c7 45 34 01 00 00 00 	movl   $0x1,0x34(%rbp)
    2f5d:	48 8d 35 a4 46 00 00 	lea    0x46a4(%rip),%rsi        # 7608 <_IO_stdin_used+0x608>
  for (int x = 0 ; x < thread_count ; x++) {
    2f64:	41 83 c5 01          	add    $0x1,%r13d
    2f68:	e8 e3 f4 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2f6d:	48 89 e9             	mov    %rbp,%rcx
    2f70:	4c 89 e6             	mov    %r12,%rsi
    2f73:	48 89 df             	mov    %rbx,%rdi
    2f76:	4c 89 fa             	mov    %r15,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2f79:	48 81 c5 b0 00 00 00 	add    $0xb0,%rbp
    2f80:	48 83 c3 08          	add    $0x8,%rbx
    2f84:	49 83 c4 38          	add    $0x38,%r12
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2f88:	e8 e3 f4 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2f8d:	48 8b 55 f0          	mov    -0x10(%rbp),%rdx
    2f91:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    2f95:	be 08 00 00 00       	mov    $0x8,%esi
    2f9a:	e8 41 f3 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2f9f:	41 83 fd 0c          	cmp    $0xc,%r13d
    2fa3:	75 a0                	jne    2f45 <main+0x955>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2fa5:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2fad:	48 8b 1d 9c 4a 00 00 	mov    0x4a9c(%rip),%rbx        # 7a50 <_IO_stdin_used+0xa50>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2fb4:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    2fb9:	4d 89 f5             	mov    %r14,%r13
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2fbc:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    2fc1:	49 89 9a 20 09 00 00 	mov    %rbx,0x920(%r10)
    thread_data[x].type = IO;
    2fc8:	41 c7 82 f8 08 00 00 02 00 00 00 	movl   $0x2,0x8f8(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2fd3:	e8 c8 f3 ff ff       	call   23a0 <calloc@plt>
    2fd8:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2fe0:	be 00 08 00 00       	mov    $0x800,%esi
    2fe5:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2fe7:	49 89 82 38 09 00 00 	mov    %rax,0x938(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2fee:	e8 bd f4 ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2ff3:	be 08 00 00 00       	mov    $0x8,%esi
    2ff8:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2ffd:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    3005:	41 89 82 40 09 00 00 	mov    %eax,0x940(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    300c:	e8 8f f3 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3011:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    3016:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    301b:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    3023:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    3028:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    302d:	4c 8b 74 24 78       	mov    0x78(%rsp),%r14
    3032:	4c 89 58 48          	mov    %r11,0x48(%rax)
    3036:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    303b:	4c 8b 7c 24 60       	mov    0x60(%rsp),%r15
    3040:	4c 89 48 50          	mov    %r9,0x50(%rax)
    3044:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    3049:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    304e:	4c 89 40 58          	mov    %r8,0x58(%rax)
    3052:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3057:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    305c:	4c 89 10             	mov    %r10,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    305f:	49 89 82 00 09 00 00 	mov    %rax,0x900(%r10)
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3066:	41 c7 82 08 09 00 00 0c 00 00 00 	movl   $0xc,0x908(%r10)
    thread_data[x].thread_index = x;
    3071:	41 c7 82 f0 08 00 00 0d 00 00 00 	movl   $0xd,0x8f0(%r10)
      my_thread_data[n] = &thread_data[n]; 
    307c:	4c 89 70 10          	mov    %r14,0x10(%rax)
    3080:	48 89 68 18          	mov    %rbp,0x18(%rax)
    3084:	4c 89 60 20          	mov    %r12,0x20(%rax)
    3088:	48 89 78 28          	mov    %rdi,0x28(%rax)
    308c:	bf 01 00 00 00       	mov    $0x1,%edi
    3091:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3095:	48 89 70 38          	mov    %rsi,0x38(%rax)
    3099:	48 8d 35 a5 42 00 00 	lea    0x42a5(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    30a0:	48 89 50 40          	mov    %rdx,0x40(%rax)
    30a4:	ba 0d 00 00 00       	mov    $0xd,%edx
    30a9:	4c 89 78 08          	mov    %r15,0x8(%rax)
    30ad:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    30af:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    30b4:	e8 97 f3 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    30b9:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    30be:	49 8d 7d 68          	lea    0x68(%r13),%rdi
    30c2:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    30ca:	48 8d 15 5f 1d 00 00 	lea    0x1d5f(%rip),%rdx        # 4e30 <io_thread>
    30d1:	48 05 d8 02 00 00    	add    $0x2d8,%rax
    30d7:	48 89 c6             	mov    %rax,%rsi
    30da:	e8 91 f3 ff ff       	call   2470 <pthread_create@plt>
    30df:	ba 0e 00 00 00       	mov    $0xe,%edx
    30e4:	48 8d 35 71 42 00 00 	lea    0x4271(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    30eb:	31 c0                	xor    %eax,%eax
    30ed:	bf 01 00 00 00       	mov    $0x1,%edi
    30f2:	e8 59 f3 ff ff       	call   2450 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    30f7:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    30fc:	48 8b 44 24 48       	mov    0x48(%rsp),%rax

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3101:	be 08 00 00 00       	mov    $0x8,%esi
    3106:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x].task_count = 0;
    310b:	49 89 9a d0 09 00 00 	mov    %rbx,0x9d0(%r10)
    3112:	31 db                	xor    %ebx,%ebx
    thread_data[x].type = EXTERNAL;
    3114:	41 c7 82 a8 09 00 00 03 00 00 00 	movl   $0x3,0x9a8(%r10)
    thread_data[x].buffers = &buffers[buffer_index];
    311f:	49 89 82 e0 09 00 00 	mov    %rax,0x9e0(%r10)
    3126:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    312b:	e8 70 f2 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3130:	4c 8b 54 24 48       	mov    0x48(%rsp),%r10
    3135:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    313a:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    313f:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3144:	4c 89 70 10          	mov    %r14,0x10(%rax)
    3148:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    314d:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    3152:	4c 89 10             	mov    %r10,(%rax)
    3155:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    315a:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    315f:	48 89 68 18          	mov    %rbp,0x18(%rax)
    3163:	48 8d 2d 2d 42 00 00 	lea    0x422d(%rip),%rbp        # 7397 <_IO_stdin_used+0x397>
    316a:	4c 89 60 20          	mov    %r12,0x20(%rax)
    316e:	4c 8d a4 24 a0 00 00 00 	lea    0xa0(%rsp),%r12
    3176:	48 89 78 28          	mov    %rdi,0x28(%rax)
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    317a:	49 8d 7d 70          	lea    0x70(%r13),%rdi
      my_thread_data[n] = &thread_data[n]; 
    317e:	48 89 48 30          	mov    %rcx,0x30(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3182:	48 8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%rcx
      my_thread_data[n] = &thread_data[n]; 
    318a:	48 89 70 38          	mov    %rsi,0x38(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    318e:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3196:	48 89 50 40          	mov    %rdx,0x40(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    319a:	48 8d 15 5f 09 00 00 	lea    0x95f(%rip),%rdx        # 3b00 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    31a1:	4c 89 58 48          	mov    %r11,0x48(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31a5:	48 81 c6 10 03 00 00 	add    $0x310,%rsi
      my_thread_data[n] = &thread_data[n]; 
    31ac:	4c 89 48 50          	mov    %r9,0x50(%rax)
    31b0:	4c 89 40 58          	mov    %r8,0x58(%rax)
    thread_data[x].threads = my_thread_data;
    31b4:	49 89 82 b0 09 00 00 	mov    %rax,0x9b0(%r10)
      my_thread_data[n] = &thread_data[n]; 
    31bb:	4c 89 78 08          	mov    %r15,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    31bf:	48 8b 05 92 48 00 00 	mov    0x4892(%rip),%rax        # 7a58 <_IO_stdin_used+0xa58>
    thread_data[x].thread_index = x;
    31c6:	41 c7 82 a0 09 00 00 0e 00 00 00 	movl   $0xe,0x9a0(%r10)
    thread_data[x].thread_count = thread_count;
    31d1:	49 89 82 b8 09 00 00 	mov    %rax,0x9b8(%r10)
    thread_data[x].thread_index = x;
    31d8:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31dd:	e8 8e f2 ff ff       	call   2470 <pthread_create@plt>
    31e2:	48 8d 3d 90 41 00 00 	lea    0x4190(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    31e9:	e8 02 f1 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    31ee:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    31f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    void * result; 
    pthread_join(thread[x], &result);
    31f8:	49 8b 7c dd 00       	mov    0x0(%r13,%rbx,8),%rdi
    31fd:	4c 89 e6             	mov    %r12,%rsi
    3200:	e8 eb f2 ff ff       	call   24f0 <pthread_join@plt>
    3205:	89 da                	mov    %ebx,%edx
    3207:	48 89 ee             	mov    %rbp,%rsi
    320a:	bf 01 00 00 00       	mov    $0x1,%edi
    320f:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3211:	48 83 c3 01          	add    $0x1,%rbx
    3215:	e8 36 f2 ff ff       	call   2450 <__printf_chk@plt>
    321a:	48 83 fb 0f          	cmp    $0xf,%rbx
    321e:	75 d8                	jne    31f8 <main+0xc08>
    3220:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    3225:	4d 89 f2             	mov    %r14,%r10
    3228:	4d 8d 6e 28          	lea    0x28(%r14),%r13
    printf("Finished thread %d\n", x);
  }
  long total = 0;
    322c:	45 31 f6             	xor    %r14d,%r14d
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    322f:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3237:	4d 89 ef             	mov    %r13,%r15
  long received = 0;
    323a:	31 db                	xor    %ebx,%ebx
  long sents = 0;
    323c:	31 ed                	xor    %ebp,%ebp
    323e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  long ingests = 0;
    3243:	45 31 c9             	xor    %r9d,%r9d
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3246:	4d 89 f5             	mov    %r14,%r13
    3249:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    if (x % 2 == 1) {
    324e:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    3252:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    3257:	89 f8                	mov    %edi,%eax
    3259:	41 89 fc             	mov    %edi,%r12d
      other = (x + 1) % total_threads;
    325c:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
    325f:	83 e0 01             	and    $0x1,%eax
      other = abs(x - 1) % total_threads;
    3262:	41 83 ec 01          	sub    $0x1,%r12d
      other = (x + 1) % total_threads;
    3266:	89 7c 24 10          	mov    %edi,0x10(%rsp)
      other = abs(x - 1) % total_threads;
    326a:	85 c0                	test   %eax,%eax
    326c:	44 0f 44 e7          	cmove  %edi,%r12d
    3270:	bf 0a 00 00 00       	mov    $0xa,%edi
    3275:	e8 56 f0 ff ff       	call   22d0 <putchar@plt>
    327a:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    327f:	bf 01 00 00 00       	mov    $0x1,%edi
    3284:	48 8d 35 20 41 00 00 	lea    0x4120(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    328b:	48 8b 10             	mov    (%rax),%rdx
    328e:	31 c0                	xor    %eax,%eax
    3290:	e8 bb f1 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3295:	49 63 57 08          	movslq 0x8(%r15),%rdx
    3299:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    329e:	85 d2                	test   %edx,%edx
    32a0:	0f 8e ef 03 00 00    	jle    3695 <main+0x10a5>
    32a6:	49 8b 07             	mov    (%r15),%rax
    32a9:	48 c1 e2 09          	shl    $0x9,%rdx
    32ad:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    long v = 0;
    32b1:	31 d2                	xor    %edx,%edx
    32b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      v += thread_data[me].tasks[n].v;
    32b8:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    32bf:	48 05 00 02 00 00    	add    $0x200,%rax
    32c5:	48 39 f0             	cmp    %rsi,%rax
    32c8:	75 ee                	jne    32b8 <main+0xcc8>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    32ca:	4d 63 e4             	movslq %r12d,%r12
    32cd:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    32d2:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    32d6:	49 8d 04 44          	lea    (%r12,%rax,2),%rax
    32da:	48 c1 e0 04          	shl    $0x4,%rax
    32de:	48 01 f8             	add    %rdi,%rax
    32e1:	48 63 70 30          	movslq 0x30(%rax),%rsi
    32e5:	85 f6                	test   %esi,%esi
    32e7:	7e 21                	jle    330a <main+0xd1a>
    32e9:	48 8b 40 28          	mov    0x28(%rax),%rax
    32ed:	48 c1 e6 09          	shl    $0x9,%rsi
    32f1:	48 01 c6             	add    %rax,%rsi
    32f4:	0f 1f 40 00          	nopl   0x0(%rax)
      v += thread_data[other].tasks[n].v;
    32f8:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    32ff:	48 05 00 02 00 00    	add    $0x200,%rax
    3305:	48 39 f0             	cmp    %rsi,%rax
    3308:	75 ee                	jne    32f8 <main+0xd08>
    330a:	48 8d 35 af 40 00 00 	lea    0x40af(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    3311:	bf 01 00 00 00       	mov    $0x1,%edi
    3316:	31 c0                	xor    %eax,%eax
    3318:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    331d:	e8 2e f1 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3322:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3327:	bf 01 00 00 00       	mov    $0x1,%edi
    332c:	48 8b 30             	mov    (%rax),%rsi
    332f:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3339:	48 f7 ee             	imul   %rsi
    333c:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3340:	31 c0                	xor    %eax,%eax
    3342:	48 d1 fa             	sar    %rdx
    3345:	48 29 f2             	sub    %rsi,%rdx
    3348:	48 8d 35 e1 42 00 00 	lea    0x42e1(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    334f:	e8 fc f0 ff ff       	call   2450 <__printf_chk@plt>
    3354:	bf 0a 00 00 00       	mov    $0xa,%edi
    3359:	e8 72 ef ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    335e:	49 63 47 08          	movslq 0x8(%r15),%rax
    3362:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3367:	85 c0                	test   %eax,%eax
    3369:	0f 8e cd 00 00 00    	jle    343c <main+0xe4c>
    336f:	49 8b 17             	mov    (%r15),%rdx
    3372:	48 c1 e0 09          	shl    $0x9,%rax
    3376:	48 8d 34 10          	lea    (%rax,%rdx,1),%rsi
    337a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3380:	48 8b 82 68 01 00 00 	mov    0x168(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    3387:	4c 03 aa 08 01 00 00 	add    0x108(%rdx),%r13
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    338e:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
      ingests += thread_data[x].tasks[n].ingest_count;
    3395:	4c 03 b2 60 ff ff ff 	add    -0xa0(%rdx),%r14
      sends += thread_data[x].tasks[n].sends;
    339c:	4c 03 8a 70 ff ff ff 	add    -0x90(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33a3:	48 03 68 10          	add    0x10(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33a7:	48 03 58 18          	add    0x18(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33ab:	48 03 68 30          	add    0x30(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33af:	48 03 58 38          	add    0x38(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33b3:	48 03 68 50          	add    0x50(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33b7:	48 03 58 58          	add    0x58(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33bb:	48 03 68 70          	add    0x70(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33bf:	48 03 58 78          	add    0x78(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33c3:	48 03 a8 90 00 00 00 	add    0x90(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33ca:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33d1:	48 03 a8 b0 00 00 00 	add    0xb0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33d8:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33df:	48 03 a8 d0 00 00 00 	add    0xd0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33e6:	48 03 98 d8 00 00 00 	add    0xd8(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33ed:	48 03 a8 f0 00 00 00 	add    0xf0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33f4:	48 03 98 f8 00 00 00 	add    0xf8(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33fb:	48 03 a8 10 01 00 00 	add    0x110(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3402:	48 03 98 18 01 00 00 	add    0x118(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3409:	48 03 a8 30 01 00 00 	add    0x130(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3410:	48 03 98 38 01 00 00 	add    0x138(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3417:	48 03 a8 50 01 00 00 	add    0x150(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    341e:	48 03 98 58 01 00 00 	add    0x158(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3425:	48 03 a8 70 01 00 00 	add    0x170(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    342c:	48 03 98 78 01 00 00 	add    0x178(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3433:	48 39 f2             	cmp    %rsi,%rdx
    3436:	0f 85 44 ff ff ff    	jne    3380 <main+0xd90>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    343c:	45 31 e4             	xor    %r12d,%r12d
    343f:	49 83 7f 68 00       	cmpq   $0x0,0x68(%r15)
    3444:	7e 78                	jle    34be <main+0xece>
    3446:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    344b:	4c 89 fb             	mov    %r15,%rbx
    344e:	4d 89 e7             	mov    %r12,%r15
    3451:	4d 89 cc             	mov    %r9,%r12
    3454:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3458:	48 8b 43 58          	mov    0x58(%rbx),%rax
    345c:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    3460:	48 83 ec 08          	sub    $0x8,%rsp
    3464:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3469:	49 83 c7 01          	add    $0x1,%r15
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    346d:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3471:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    347b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    347f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3483:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3486:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    348a:	4c 2b 01             	sub    (%rcx),%r8
    348d:	31 c0                	xor    %eax,%eax
    348f:	8b 49 20             	mov    0x20(%rcx),%ecx
    3492:	56                   	push   %rsi
    3493:	48 8d 35 b6 41 00 00 	lea    0x41b6(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    349a:	48 c1 ea 12          	shr    $0x12,%rdx
    349e:	49 89 d1             	mov    %rdx,%r9
    34a1:	ba 02 00 00 00       	mov    $0x2,%edx
    34a6:	e8 a5 ef ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    34ab:	58                   	pop    %rax
    34ac:	5a                   	pop    %rdx
    34ad:	4c 39 7b 68          	cmp    %r15,0x68(%rbx)
    34b1:	7f a5                	jg     3458 <main+0xe68>
    34b3:	49 89 df             	mov    %rbx,%r15
    34b6:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    34bb:	4d 89 e1             	mov    %r12,%r9
  for (int x = 0 ; x < thread_count ; x++) {
    34be:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    34c4:	49 81 c7 b0 00 00 00 	add    $0xb0,%r15
    34cb:	83 7c 24 10 0c       	cmpl   $0xc,0x10(%rsp)
    34d0:	0f 85 78 fd ff ff    	jne    324e <main+0xc5e>
    34d6:	4c 89 ea             	mov    %r13,%rdx
    34d9:	48 8d 35 ed 3e 00 00 	lea    0x3eed(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    34e0:	31 c0                	xor    %eax,%eax
    34e2:	4d 89 cf             	mov    %r9,%r15
    34e5:	bf 01 00 00 00       	mov    $0x1,%edi
    34ea:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    34ef:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    34f9:	e8 52 ef ff ff       	call   2450 <__printf_chk@plt>
    34fe:	bf 0a 00 00 00       	mov    $0xa,%edi
    3503:	e8 c8 ed ff ff       	call   22d0 <putchar@plt>
    3508:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    350d:	bf 01 00 00 00       	mov    $0x1,%edi
    3512:	48 8d 35 87 41 00 00 	lea    0x4187(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    3519:	48 8b 50 08          	mov    0x8(%rax),%rdx
    351d:	31 c0                	xor    %eax,%eax
    351f:	e8 2c ef ff ff       	call   2450 <__printf_chk@plt>
    3524:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3529:	bf 01 00 00 00       	mov    $0x1,%edi
    352e:	48 8d 35 93 41 00 00 	lea    0x4193(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    3535:	4c 89 c8             	mov    %r9,%rax
    3538:	49 c1 f9 3f          	sar    $0x3f,%r9
    353c:	49 f7 ec             	imul   %r12
    353f:	31 c0                	xor    %eax,%eax
    3541:	48 d1 fa             	sar    %rdx
    3544:	4c 29 ca             	sub    %r9,%rdx
    3547:	e8 04 ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    354c:	4c 89 f8             	mov    %r15,%rax
    354f:	4d 89 fb             	mov    %r15,%r11
    3552:	bf 01 00 00 00       	mov    $0x1,%edi
    3557:	49 f7 ec             	imul   %r12
    355a:	49 c1 fb 3f          	sar    $0x3f,%r11
    355e:	48 8d 35 93 41 00 00 	lea    0x4193(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    3565:	31 c0                	xor    %eax,%eax
    3567:	48 d1 fa             	sar    %rdx
    356a:	4c 29 da             	sub    %r11,%rdx
    356d:	e8 de ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3572:	4c 89 e8             	mov    %r13,%rax
    3575:	4c 89 e9             	mov    %r13,%rcx
    3578:	bf 01 00 00 00       	mov    $0x1,%edi
    357d:	49 f7 ec             	imul   %r12
    3580:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3584:	48 8d 35 9d 41 00 00 	lea    0x419d(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    358b:	31 c0                	xor    %eax,%eax
    358d:	48 d1 fa             	sar    %rdx
    3590:	48 29 ca             	sub    %rcx,%rdx
    3593:	e8 b8 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3598:	48 89 e8             	mov    %rbp,%rax
    359b:	48 c1 fd 3f          	sar    $0x3f,%rbp
    359f:	48 8d 35 3b 3e 00 00 	lea    0x3e3b(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    35a6:	49 f7 ec             	imul   %r12
    35a9:	bf 01 00 00 00       	mov    $0x1,%edi
    35ae:	31 c0                	xor    %eax,%eax
    35b0:	48 d1 fa             	sar    %rdx
    35b3:	48 29 ea             	sub    %rbp,%rdx
    35b6:	e8 95 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    35bb:	48 89 d8             	mov    %rbx,%rax
    35be:	48 c1 fb 3f          	sar    $0x3f,%rbx
    35c2:	48 8d 35 29 3e 00 00 	lea    0x3e29(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    35c9:	49 f7 ec             	imul   %r12
    35cc:	bf 01 00 00 00       	mov    $0x1,%edi
    35d1:	48 d1 fa             	sar    %rdx
    35d4:	48 29 da             	sub    %rbx,%rdx
    35d7:	31 c0                	xor    %eax,%eax
    35d9:	e8 72 ee ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    35de:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    35e6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    35ef:	0f 85 a7 00 00 00    	jne    369c <main+0x10ac>
    35f5:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    35fc:	31 c0                	xor    %eax,%eax
    35fe:	5b                   	pop    %rbx
    35ff:	5d                   	pop    %rbp
    3600:	41 5c                	pop    %r12
    3602:	41 5d                	pop    %r13
    3604:	41 5e                	pop    %r14
    3606:	41 5f                	pop    %r15
    3608:	c3                   	ret
          thread_data[x].tasks[y].run = barriered_work; 
    3609:	48 8d 05 e0 21 00 00 	lea    0x21e0(%rip),%rax        # 57f0 <barriered_work>
    3610:	bb 02 00 00 00       	mov    $0x2,%ebx
    3615:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    361c:	e9 1e f3 ff ff       	jmp    293f <main+0x34f>
      other = (x + 1) % total_threads;
    3621:	b8 89 88 88 88       	mov    $0x88888889,%eax
    3626:	45 89 fe             	mov    %r15d,%r14d
      my_thread_data[0] = &thread_data[x]; 
    3629:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    362e:	4c 89 e9             	mov    %r13,%rcx
      other = (x + 1) % total_threads;
    3631:	4c 0f af f0          	imul   %rax,%r14
      thread_data[x].thread_index = 0;
    3635:	41 c7 45 00 00 00 00 00 	movl   $0x0,0x0(%r13)
    363d:	48 8d 35 c5 3c 00 00 	lea    0x3cc5(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      my_thread_data[0] = &thread_data[x]; 
    3644:	4c 89 2f             	mov    %r13,(%rdi)
      other = (x + 1) % total_threads;
    3647:	49 c1 ee 23          	shr    $0x23,%r14
    364b:	44 89 f0             	mov    %r14d,%eax
    364e:	c1 e0 04             	shl    $0x4,%eax
    3651:	44 29 f0             	sub    %r14d,%eax
    3654:	45 89 fe             	mov    %r15d,%r14d
    3657:	41 29 c6             	sub    %eax,%r14d
      my_thread_data[1] = &thread_data[other]; 
    365a:	49 63 c6             	movslq %r14d,%rax
    365d:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3661:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    3665:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    366a:	89 ea                	mov    %ebp,%edx
    366c:	49 c1 e0 04          	shl    $0x4,%r8
    3670:	49 01 c0             	add    %rax,%r8
    3673:	31 c0                	xor    %eax,%eax
    3675:	4c 89 47 08          	mov    %r8,0x8(%rdi)
    3679:	bf 01 00 00 00       	mov    $0x1,%edi
    367e:	e8 cd ed ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    3683:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    3688:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    368d:	49 89 c4             	mov    %rax,%r12
    3690:	e9 a7 f1 ff ff       	jmp    283c <main+0x24c>
    long v = 0;
    3695:	31 d2                	xor    %edx,%edx
    3697:	e9 2e fc ff ff       	jmp    32ca <main+0xcda>
}
    369c:	e8 8f ec ff ff       	call   2330 <__stack_chk_fail@plt>
    36a1:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
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
    37ab:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    37af:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    37b7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    37bb:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    37bf:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    37c6:	48 85 c9             	test   %rcx,%rcx
    37c9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    37d0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    37d4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    37d8:	31 c0                	xor    %eax,%eax
    37da:	c3                   	ret
    37db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

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
    3801:	48 8b 50 10          	mov    0x10(%rax),%rdx
    3805:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3809:	48 8b 70 28          	mov    0x28(%rax),%rsi
    380d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    380f:	48 8b 52 28          	mov    0x28(%rdx),%rdx
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
    3854:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    3858:	0f 85 90 02 00 00    	jne    3aee <barriered_thread+0x29e>
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
    3870:	41 8b 55 30          	mov    0x30(%r13),%edx
    3874:	39 da                	cmp    %ebx,%edx
    3876:	7f 12                	jg     388a <barriered_thread+0x3a>
      data->cycles++;
    3878:	49 83 85 98 00 00 00 01 	addq   $0x1,0x98(%r13)
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
    38aa:	49 8b 45 28          	mov    0x28(%r13),%rax
    38ae:	4a 8d 34 20          	lea    (%rax,%r12,1),%rsi
    38b2:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    38b9:	75 dd                	jne    3898 <barriered_thread+0x48>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    38bb:	41 8b 7d 18          	mov    0x18(%r13),%edi
          previous = t - 1;
    38bf:	83 ea 01             	sub    $0x1,%edx
    38c2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    38c5:	85 db                	test   %ebx,%ebx
    38c7:	0f 4f d1             	cmovg  %ecx,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    38ca:	85 ff                	test   %edi,%edi
    38cc:	0f 8e 3e 01 00 00    	jle    3a10 <barriered_thread+0x1c0>
    38d2:	49 8b 45 10          	mov    0x10(%r13),%rax
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
    3903:	4c 8b 5a 28          	mov    0x28(%rdx),%r11
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
    3947:	45 39 75 18          	cmp    %r14d,0x18(%r13)
    394b:	0f 85 8f 00 00 00    	jne    39e0 <barriered_thread+0x190>
    3951:	49 8b 45 28          	mov    0x28(%r13),%rax
          data->tasks[t].prearrive++;
    3955:	4c 01 e0             	add    %r12,%rax
    3958:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    395f:	85 db                	test   %ebx,%ebx
    3961:	75 0e                	jne    3971 <barriered_thread+0x121>
    3963:	49 8b 75 70          	mov    0x70(%r13),%rsi
    3967:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    396b:	0f 8c 5f 01 00 00    	jl     3ad0 <barriered_thread+0x280>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3971:	49 63 4d 00          	movslq 0x0(%r13),%rcx
    3975:	49 8b 55 10          	mov    0x10(%r13),%rdx
          data->tasks[t].available = 0;
    3979:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3983:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    3987:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
    398b:	4c 01 e7             	add    %r12,%rdi
    398e:	ff 90 18 01 00 00    	call   *0x118(%rax)
          data->tasks[t].arrived++;
    3994:	49 8b 45 28          	mov    0x28(%r13),%rax
    3998:	4c 01 e0             	add    %r12,%rax
    399b:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    39a2:	41 8b 45 30          	mov    0x30(%r13),%eax
          data->iteration_count++;
    39a6:	49 83 45 68 01       	addq   $0x1,0x68(%r13)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    39ab:	83 e8 01             	sub    $0x1,%eax
    39ae:	39 d8                	cmp    %ebx,%eax
    39b0:	0f 84 b2 00 00 00    	je     3a68 <barriered_thread+0x218>
          asm volatile ("sfence" ::: "memory");
    39b6:	0f ae f8             	sfence
          if (waiting == 0) {
    39b9:	85 ed                	test   %ebp,%ebp
    39bb:	0f 84 d7 00 00 00    	je     3a98 <barriered_thread+0x248>
    for (; t < data->task_count; t++) {
    39c1:	41 8b 55 30          	mov    0x30(%r13),%edx
    39c5:	83 c3 01             	add    $0x1,%ebx
    39c8:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    39cf:	39 d3                	cmp    %edx,%ebx
    39d1:	0f 8c d3 fe ff ff    	jl     38aa <barriered_thread+0x5a>
    39d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  while (data->running == 1) {
    39e0:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
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
    3a20:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    3a27:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    3a2c:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3a2e:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3a32:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    3a39:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3a3e:	e8 cd e8 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3a43:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    3a4a:	48 83 c0 01          	add    $0x1,%rax
    3a4e:	48 99                	cqto
    3a50:	49 f7 bd 90 00 00 00 	idivq  0x90(%r13)
    3a57:	49 89 95 88 00 00 00 	mov    %rdx,0x88(%r13)
            waiting = 0; 
    3a5e:	e9 df fe ff ff       	jmp    3942 <barriered_thread+0xf2>
    3a63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3a68:	49 8b 75 70          	mov    0x70(%r13),%rsi
    3a6c:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    3a70:	0f 8d 40 ff ff ff    	jge    39b6 <barriered_thread+0x166>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    3a76:	48 c1 e6 04          	shl    $0x4,%rsi
    3a7a:	bf 04 00 00 00       	mov    $0x4,%edi
    3a7f:	49 03 75 60          	add    0x60(%r13),%rsi
    3a83:	e8 88 e8 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3a88:	49 83 45 70 01       	addq   $0x1,0x70(%r13)
    3a8d:	e9 24 ff ff ff       	jmp    39b6 <barriered_thread+0x166>
    3a92:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    3a98:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3a9f:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3aa4:	bd 01 00 00 00       	mov    $0x1,%ebp
            data->task_snapshot[data->task_timestamp_count].task = t;
    3aa9:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3aad:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    3ab4:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3ab8:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3abb:	e8 50 e8 ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3ac0:	41 8b 55 30          	mov    0x30(%r13),%edx
    3ac4:	e9 cf fd ff ff       	jmp    3898 <barriered_thread+0x48>
    3ac9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3ad0:	48 c1 e6 04          	shl    $0x4,%rsi
    3ad4:	bf 04 00 00 00       	mov    $0x4,%edi
    3ad9:	49 03 75 58          	add    0x58(%r13),%rsi
    3add:	e8 2e e8 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3ae2:	49 8b 45 28          	mov    0x28(%r13),%rax
    3ae6:	4c 01 e0             	add    %r12,%rax
    3ae9:	e9 83 fe ff ff       	jmp    3971 <barriered_thread+0x121>
}
    3aee:	31 c0                	xor    %eax,%eax
    3af0:	c3                   	ret
    3af1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
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
    3b26:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
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
    3b53:	49 8b 45 40          	mov    0x40(%r13),%rax
    3b57:	48 63 10             	movslq (%rax),%rdx
    3b5a:	85 d2                	test   %edx,%edx
    3b5c:	7e 2c                	jle    3b8a <external_thread+0x8a>
    3b5e:	48 8b 40 08          	mov    0x8(%rax),%rax
    3b62:	48 c1 e2 04          	shl    $0x4,%rdx
    3b66:	48 01 c2             	add    %rax,%rdx
    3b69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
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
    3b8d:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
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
    3c1d:	45 8b 67 34          	mov    0x34(%r15),%r12d
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
    3c49:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3c4d:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c52:	85 c0                	test   %eax,%eax
    3c54:	7e 47                	jle    3c9d <timer_thread+0xdd>
    3c56:	49 8b 4f 10          	mov    0x10(%r15),%rcx
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
    3c72:	41 f7 7a 30          	idivl  0x30(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3c76:	49 8b 72 28          	mov    0x28(%r10),%rsi
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
    3ca0:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3ca4:	41 8b 57 34          	mov    0x34(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3ca8:	48 8b 00             	mov    (%rax),%rax
    y++;
    3cab:	39 78 30             	cmp    %edi,0x30(%rax)
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
    3cd1:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3cd5:	85 d2                	test   %edx,%edx
    3cd7:	7e 6b                	jle    3d44 <timer_thread+0x184>
    for (int y = 0 ; y < data->task_count ; y++) {
    3cd9:	49 63 47 30          	movslq 0x30(%r15),%rax
    3cdd:	85 c0                	test   %eax,%eax
    3cdf:	7e 63                	jle    3d44 <timer_thread+0x184>
    3ce1:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3ce5:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3ce9:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3cf1:	31 ff                	xor    %edi,%edi
    3cf3:	48 89 c2             	mov    %rax,%rdx
    3cf6:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3cfa:	48 8b 40 28          	mov    0x28(%rax),%rax
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
    3d5b:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3d5f:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d64:	85 c0                	test   %eax,%eax
    3d66:	7e 4c                	jle    3db4 <timer_thread+0x1f4>
    3d68:	49 8b 4f 10          	mov    0x10(%r15),%rcx
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
    3d8a:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3d8d:	48 8b 73 28          	mov    0x28(%rbx),%rsi
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
    3db7:	49 8b 47 10          	mov    0x10(%r15),%rax
    y++;
    3dbb:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3dbe:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3dc1:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3dc4:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3dc8:	41 8b 7f 20          	mov    0x20(%r15),%edi
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
    3dfb:	48 03 42 28          	add    0x28(%rdx),%rax
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
    3e43:	41 8b 7f 20          	mov    0x20(%r15),%edi
            all_empty = 0;
    3e47:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3e4a:	49 83 c6 01          	add    $0x1,%r14
    3e4e:	44 39 f7             	cmp    %r14d,%edi
    3e51:	7e 0d                	jle    3e60 <timer_thread+0x2a0>
    3e53:	49 8b 47 10          	mov    0x10(%r15),%rax
    3e57:	eb 97                	jmp    3df0 <timer_thread+0x230>
    3e59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3e60:	49 83 c5 01          	add    $0x1,%r13
    3e64:	44 39 ef             	cmp    %r13d,%edi
    3e67:	7e 0d                	jle    3e76 <timer_thread+0x2b6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3e69:	85 ff                	test   %edi,%edi
    3e6b:	7e 09                	jle    3e76 <timer_thread+0x2b6>
    3e6d:	49 8b 47 10          	mov    0x10(%r15),%rax
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
    3e9c:	41 8b 47 34          	mov    0x34(%r15),%eax
    3ea0:	85 c0                	test   %eax,%eax
    3ea2:	0f 84 cf 00 00 00    	je     3f77 <timer_thread+0x3b7>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ea8:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3eac:	85 c9                	test   %ecx,%ecx
    3eae:	7e 2d                	jle    3edd <timer_thread+0x31d>
    3eb0:	49 8b 47 10          	mov    0x10(%r15),%rax
    3eb4:	31 db                	xor    %ebx,%ebx
    3eb6:	48 8d 2d b1 31 00 00 	lea    0x31b1(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3ebd:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->running = 0;
    3ec0:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3ec4:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3ec8:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3ecf:	0f 84 cf 00 00 00    	je     3fa4 <timer_thread+0x3e4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ed5:	48 83 c3 01          	add    $0x1,%rbx
    3ed9:	39 d9                	cmp    %ebx,%ecx
    3edb:	7f e3                	jg     3ec0 <timer_thread+0x300>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3edd:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3ee1:	85 d2                	test   %edx,%edx
    3ee3:	7e 7b                	jle    3f60 <timer_thread+0x3a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3ee5:	49 63 47 30          	movslq 0x30(%r15),%rax
    3ee9:	85 c0                	test   %eax,%eax
    3eeb:	7e 73                	jle    3f60 <timer_thread+0x3a0>
    3eed:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3ef1:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3ef5:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3efd:	31 c9                	xor    %ecx,%ecx
    3eff:	48 89 c6             	mov    %rax,%rsi
    3f02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3f08:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3f0c:	48 8b 40 28          	mov    0x28(%rax),%rax
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
    3f6f:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
    3f77:	48 8d 3d 09 31 00 00 	lea    0x3109(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3f7e:	e8 6d e3 ff ff       	call   22f0 <puts@plt>
}
    3f83:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3f88:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3f91:	75 47                	jne    3fda <timer_thread+0x41a>
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
    3fac:	49 8b 47 10          	mov    0x10(%r15),%rax
    3fb0:	be 01 00 00 00       	mov    $0x1,%esi
    3fb5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3fb9:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3fbd:	8b 78 50             	mov    0x50(%rax),%edi
    3fc0:	e8 3b e4 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3fc5:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3fc9:	39 d9                	cmp    %ebx,%ecx
    3fcb:	0f 8e 0c ff ff ff    	jle    3edd <timer_thread+0x31d>
    3fd1:	49 8b 47 10          	mov    0x10(%r15),%rax
    3fd5:	e9 e6 fe ff ff       	jmp    3ec0 <timer_thread+0x300>
}
    3fda:	e8 51 e3 ff ff       	call   2330 <__stack_chk_fail@plt>
    3fdf:	90                   	nop

0000000000003fe0 <strtolower>:
void strtolower(char *str) {
    3fe0:	f3 0f 1e fa          	endbr64
    3fe4:	55                   	push   %rbp
    3fe5:	53                   	push   %rbx
    3fe6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3fea:	48 0f be 1f          	movsbq (%rdi),%rbx
    3fee:	84 db                	test   %bl,%bl
    3ff0:	74 24                	je     4016 <strtolower+0x36>
    3ff2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3ff5:	e8 16 e5 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3ffa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4000:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4003:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4007:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    400a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    400d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4012:	84 db                	test   %bl,%bl
    4014:	75 ea                	jne    4000 <strtolower+0x20>
}
    4016:	48 83 c4 08          	add    $0x8,%rsp
    401a:	5b                   	pop    %rbx
    401b:	5d                   	pop    %rbp
    401c:	c3                   	ret
    401d:	0f 1f 00             	nopl   (%rax)

0000000000004020 <zh_malloc>:
void *zh_malloc(size_t size) {
    4020:	f3 0f 1e fa          	endbr64
    4024:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4028:	e8 e3 e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    402d:	48 85 c0             	test   %rax,%rax
    4030:	74 05                	je     4037 <zh_malloc+0x17>
}
    4032:	48 83 c4 08          	add    $0x8,%rsp
    4036:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4037:	48 8b 0d e2 5f 00 00 	mov    0x5fe2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    403e:	ba 28 00 00 00       	mov    $0x28,%edx
    4043:	be 01 00 00 00       	mov    $0x1,%esi
    4048:	48 8d 3d b9 33 00 00 	lea    0x33b9(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    404f:	e8 6c e4 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4054:	bf 01 00 00 00       	mov    $0x1,%edi
    4059:	e8 42 e4 ff ff       	call   24a0 <exit@plt>
    405e:	66 90                	xchg   %ax,%ax

0000000000004060 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4060:	f3 0f 1e fa          	endbr64
    4064:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4065:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    406a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    406d:	e8 ee e2 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4072:	48 85 c0             	test   %rax,%rax
    4075:	74 11                	je     4088 <get_filename_ext+0x28>
    4077:	48 39 c3             	cmp    %rax,%rbx
    407a:	74 0c                	je     4088 <get_filename_ext+0x28>
    return dot + 1;
    407c:	48 83 c0 01          	add    $0x1,%rax
}
    4080:	5b                   	pop    %rbx
    4081:	c3                   	ret
    4082:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4088:	48 8d 05 40 30 00 00 	lea    0x3040(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    408f:	5b                   	pop    %rbx
    4090:	c3                   	ret
    4091:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    409c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000040a0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    40a0:	f3 0f 1e fa          	endbr64
    40a4:	41 55                	push   %r13
    40a6:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40a9:	48 89 fe             	mov    %rdi,%rsi
    40ac:	41 54                	push   %r12
    40ae:	55                   	push   %rbp
    40af:	48 89 d5             	mov    %rdx,%rbp
    40b2:	ba 00 04 00 00       	mov    $0x400,%edx
    40b7:	53                   	push   %rbx
    40b8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    40bf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    40c8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    40d0:	31 c0                	xor    %eax,%eax
    40d2:	49 89 e4             	mov    %rsp,%r12
    40d5:	4c 89 e7             	mov    %r12,%rdi
    40d8:	e8 53 e3 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    40dd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    40e2:	84 db                	test   %bl,%bl
    40e4:	74 24                	je     410a <send_headers+0x6a>
        *str = (char)tolower(*str);
    40e6:	e8 25 e4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    40eb:	48 8b 08             	mov    (%rax),%rcx
    40ee:	4c 89 e0             	mov    %r12,%rax
    40f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    40f8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    40fb:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    40ff:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4102:	48 0f be 18          	movsbq (%rax),%rbx
    4106:	84 db                	test   %bl,%bl
    4108:	75 ee                	jne    40f8 <send_headers+0x58>
    void *buf = malloc(size);
    410a:	bf 11 00 00 00       	mov    $0x11,%edi
    410f:	e8 fc e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4114:	48 85 c0             	test   %rax,%rax
    4117:	0f 84 7e 04 00 00    	je     459b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    411d:	66 0f 6f 05 3b 38 00 00 	movdqa 0x383b(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    4125:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4129:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    412e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4136:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    413a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    413d:	e8 ce e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4142:	48 85 c0             	test   %rax,%rax
    4145:	0f 84 50 04 00 00    	je     459b <send_headers+0x4fb>
    414b:	66 0f 6f 05 1d 38 00 00 	movdqa 0x381d(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    4153:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4157:	4c 89 e7             	mov    %r12,%rdi
    415a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4164:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    416c:	0f 11 00             	movups %xmm0,(%rax)
    416f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4173:	be 2e 00 00 00       	mov    $0x2e,%esi
    4178:	e8 e3 e1 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    417d:	48 85 c0             	test   %rax,%rax
    4180:	0f 84 ea 02 00 00    	je     4470 <send_headers+0x3d0>
    4186:	4c 39 e0             	cmp    %r12,%rax
    4189:	0f 84 e1 02 00 00    	je     4470 <send_headers+0x3d0>
    return dot + 1;
    418f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4193:	48 8d 3d 03 2f 00 00 	lea    0x2f03(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    419a:	48 89 de             	mov    %rbx,%rsi
    419d:	e8 0e e2 ff ff       	call   23b0 <strcmp@plt>
    41a2:	85 c0                	test   %eax,%eax
    41a4:	75 20                	jne    41c6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    41a6:	66 0f 6f 05 d2 37 00 00 	movdqa 0x37d2(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    41ae:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41b6:	66 0f 6f 05 d2 37 00 00 	movdqa 0x37d2(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    41be:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    41c6:	48 89 de             	mov    %rbx,%rsi
    41c9:	48 8d 3d d1 2e 00 00 	lea    0x2ed1(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    41d0:	e8 db e1 ff ff       	call   23b0 <strcmp@plt>
    41d5:	85 c0                	test   %eax,%eax
    41d7:	75 20                	jne    41f9 <send_headers+0x159>
    41d9:	66 0f 6f 05 9f 37 00 00 	movdqa 0x379f(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    41e1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41e9:	66 0f 6f 05 9f 37 00 00 	movdqa 0x379f(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    41f1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    41f9:	48 89 de             	mov    %rbx,%rsi
    41fc:	48 8d 3d a3 2e 00 00 	lea    0x2ea3(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    4203:	e8 a8 e1 ff ff       	call   23b0 <strcmp@plt>
    4208:	85 c0                	test   %eax,%eax
    420a:	0f 84 10 02 00 00    	je     4420 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4210:	48 89 de             	mov    %rbx,%rsi
    4213:	48 8d 3d 90 2e 00 00 	lea    0x2e90(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    421a:	e8 91 e1 ff ff       	call   23b0 <strcmp@plt>
    421f:	85 c0                	test   %eax,%eax
    4221:	0f 84 a9 02 00 00    	je     44d0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4227:	48 89 de             	mov    %rbx,%rsi
    422a:	48 8d 3d 7d 2e 00 00 	lea    0x2e7d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4231:	e8 7a e1 ff ff       	call   23b0 <strcmp@plt>
    4236:	85 c0                	test   %eax,%eax
    4238:	0f 84 6a 02 00 00    	je     44a8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    423e:	48 89 de             	mov    %rbx,%rsi
    4241:	48 8d 3d a9 2e 00 00 	lea    0x2ea9(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4248:	e8 63 e1 ff ff       	call   23b0 <strcmp@plt>
    424d:	85 c0                	test   %eax,%eax
    424f:	0f 84 2b 02 00 00    	je     4480 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4255:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4258:	0f 84 52 01 00 00    	je     43b0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    425e:	48 89 de             	mov    %rbx,%rsi
    4261:	48 8d 3d 4a 2e 00 00 	lea    0x2e4a(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    4268:	e8 43 e1 ff ff       	call   23b0 <strcmp@plt>
    426d:	85 c0                	test   %eax,%eax
    426f:	0f 84 ab 02 00 00    	je     4520 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4275:	48 89 de             	mov    %rbx,%rsi
    4278:	48 8d 3d 37 2e 00 00 	lea    0x2e37(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    427f:	e8 2c e1 ff ff       	call   23b0 <strcmp@plt>
    4284:	85 c0                	test   %eax,%eax
    4286:	0f 84 6c 02 00 00    	je     44f8 <send_headers+0x458>
    slen = strlen(send_buffer);
    428c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4294:	4c 89 e7             	mov    %r12,%rdi
    4297:	e8 84 e0 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    429c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    429f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    42a2:	e8 69 e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    42a7:	48 85 c0             	test   %rax,%rax
    42aa:	0f 84 eb 02 00 00    	je     459b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    42b0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    42b4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    42b8:	83 fb 08             	cmp    $0x8,%ebx
    42bb:	0f 83 3f 01 00 00    	jae    4400 <send_headers+0x360>
    42c1:	f6 c3 04             	test   $0x4,%bl
    42c4:	0f 85 7b 02 00 00    	jne    4545 <send_headers+0x4a5>
    42ca:	85 db                	test   %ebx,%ebx
    42cc:	74 13                	je     42e1 <send_headers+0x241>
    42ce:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    42d6:	88 10                	mov    %dl,(%rax)
    42d8:	f6 c3 02             	test   $0x2,%bl
    42db:	0f 85 96 02 00 00    	jne    4577 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    42e1:	4d 89 e8             	mov    %r13,%r8
    42e4:	48 8d 0d cf 2d 00 00 	lea    0x2dcf(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    42eb:	4c 89 e7             	mov    %r12,%rdi
    42ee:	31 c0                	xor    %eax,%eax
    42f0:	ba 00 04 00 00       	mov    $0x400,%edx
    42f5:	be 01 00 00 00       	mov    $0x1,%esi
    42fa:	e8 21 e2 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    42ff:	4c 89 e7             	mov    %r12,%rdi
    4302:	e8 19 e0 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4307:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    430a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    430d:	e8 fe e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4312:	48 85 c0             	test   %rax,%rax
    4315:	0f 84 80 02 00 00    	je     459b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    431b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    431f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4323:	83 fb 08             	cmp    $0x8,%ebx
    4326:	0f 83 1c 01 00 00    	jae    4448 <send_headers+0x3a8>
    432c:	f6 c3 04             	test   $0x4,%bl
    432f:	0f 85 29 02 00 00    	jne    455e <send_headers+0x4be>
    4335:	85 db                	test   %ebx,%ebx
    4337:	74 13                	je     434c <send_headers+0x2ac>
    4339:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4341:	88 10                	mov    %dl,(%rax)
    4343:	f6 c3 02             	test   $0x2,%bl
    4346:	0f 85 3d 02 00 00    	jne    4589 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    434c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4351:	bf 02 00 00 00       	mov    $0x2,%edi
    4356:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    435e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4366:	e8 a5 e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    436b:	48 85 c0             	test   %rax,%rax
    436e:	0f 84 27 02 00 00    	je     459b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4374:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    437c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4380:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4388:	66 89 10             	mov    %dx,(%rax)
}
    438b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4393:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    439c:	0f 85 20 02 00 00    	jne    45c2 <send_headers+0x522>
    43a2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    43a9:	5b                   	pop    %rbx
    43aa:	5d                   	pop    %rbp
    43ab:	41 5c                	pop    %r12
    43ad:	41 5d                	pop    %r13
    43af:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    43b0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    43b4:	0f 85 a4 fe ff ff    	jne    425e <send_headers+0x1be>
    43ba:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    43be:	0f 85 9a fe ff ff    	jne    425e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    43c4:	66 0f 6f 05 14 36 00 00 	movdqa 0x3614(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    43cc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    43d6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    43de:	66 0f 6f 05 0a 36 00 00 	movdqa 0x360a(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    43e6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    43ee:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    43f6:	e9 63 fe ff ff       	jmp    425e <send_headers+0x1be>
    43fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4400:	89 da                	mov    %ebx,%edx
    4402:	48 89 c7             	mov    %rax,%rdi
    4405:	4c 89 e6             	mov    %r12,%rsi
    4408:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    440d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4412:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4415:	c1 e9 03             	shr    $0x3,%ecx
    4418:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    441b:	e9 c1 fe ff ff       	jmp    42e1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4420:	66 0f 6f 05 58 35 00 00 	movdqa 0x3558(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4428:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4430:	66 0f 6f 05 68 35 00 00 	movdqa 0x3568(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4438:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4440:	e9 cb fd ff ff       	jmp    4210 <send_headers+0x170>
    4445:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4448:	89 da                	mov    %ebx,%edx
    444a:	48 89 c7             	mov    %rax,%rdi
    444d:	4c 89 e6             	mov    %r12,%rsi
    4450:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4455:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    445a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    445d:	c1 e9 03             	shr    $0x3,%ecx
    4460:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4463:	e9 e4 fe ff ff       	jmp    434c <send_headers+0x2ac>
    4468:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4470:	48 8d 1d 58 2c 00 00 	lea    0x2c58(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4477:	e9 94 fd ff ff       	jmp    4210 <send_headers+0x170>
    447c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4480:	66 0f 6f 05 38 35 00 00 	movdqa 0x3538(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4488:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4490:	66 0f 6f 05 38 35 00 00 	movdqa 0x3538(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4498:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44a0:	e9 b0 fd ff ff       	jmp    4255 <send_headers+0x1b5>
    44a5:	0f 1f 00             	nopl   (%rax)
    44a8:	66 0f 6f 05 10 35 00 00 	movdqa 0x3510(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    44b0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44b8:	66 0f 6f 05 10 35 00 00 	movdqa 0x3510(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    44c0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44c8:	e9 71 fd ff ff       	jmp    423e <send_headers+0x19e>
    44cd:	0f 1f 00             	nopl   (%rax)
    44d0:	66 0f 6f 05 a8 34 00 00 	movdqa 0x34a8(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    44d8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44e0:	66 0f 6f 05 c8 34 00 00 	movdqa 0x34c8(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    44e8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44f0:	e9 32 fd ff ff       	jmp    4227 <send_headers+0x187>
    44f5:	0f 1f 00             	nopl   (%rax)
    44f8:	66 0f 6f 05 c0 34 00 00 	movdqa 0x34c0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4500:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4508:	66 0f 6f 05 00 35 00 00 	movdqa 0x3500(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4510:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4518:	e9 6f fd ff ff       	jmp    428c <send_headers+0x1ec>
    451d:	0f 1f 00             	nopl   (%rax)
    4520:	66 0f 6f 05 98 34 00 00 	movdqa 0x3498(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4528:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4530:	66 0f 6f 05 c8 34 00 00 	movdqa 0x34c8(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4538:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4540:	e9 30 fd ff ff       	jmp    4275 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4545:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    454c:	89 db                	mov    %ebx,%ebx
    454e:	89 10                	mov    %edx,(%rax)
    4550:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4555:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4559:	e9 83 fd ff ff       	jmp    42e1 <send_headers+0x241>
    455e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4565:	89 db                	mov    %ebx,%ebx
    4567:	89 10                	mov    %edx,(%rax)
    4569:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    456e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4572:	e9 d5 fd ff ff       	jmp    434c <send_headers+0x2ac>
    4577:	89 db                	mov    %ebx,%ebx
    4579:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    457f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4584:	e9 58 fd ff ff       	jmp    42e1 <send_headers+0x241>
    4589:	89 db                	mov    %ebx,%ebx
    458b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4591:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4596:	e9 b1 fd ff ff       	jmp    434c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    459b:	48 8b 0d 7e 5a 00 00 	mov    0x5a7e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    45a2:	ba 28 00 00 00       	mov    $0x28,%edx
    45a7:	be 01 00 00 00       	mov    $0x1,%esi
    45ac:	48 8d 3d 55 2e 00 00 	lea    0x2e55(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    45b3:	e8 08 df ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    45b8:	bf 01 00 00 00       	mov    $0x1,%edi
    45bd:	e8 de de ff ff       	call   24a0 <exit@plt>
}
    45c2:	e8 69 dd ff ff       	call   2330 <__stack_chk_fail@plt>
    45c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000045d0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    45d0:	f3 0f 1e fa          	endbr64
    45d4:	41 55                	push   %r13
    45d6:	49 89 d5             	mov    %rdx,%r13
    45d9:	41 54                	push   %r12
    45db:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    45de:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    45e1:	55                   	push   %rbp
    45e2:	53                   	push   %rbx
    45e3:	48 89 f3             	mov    %rsi,%rbx
    45e6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    45ea:	e8 21 de ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    45ef:	48 85 c0             	test   %rax,%rax
    45f2:	74 6b                	je     465f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    45f4:	4c 89 e7             	mov    %r12,%rdi
    45f7:	48 89 c5             	mov    %rax,%rbp
    45fa:	31 f6                	xor    %esi,%esi
    45fc:	31 c0                	xor    %eax,%eax
    45fe:	e8 7d de ff ff       	call   2480 <open@plt>
    4603:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4606:	85 c0                	test   %eax,%eax
    4608:	0f 88 48 df ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    460e:	48 89 da             	mov    %rbx,%rdx
    4611:	48 89 ee             	mov    %rbp,%rsi
    4614:	89 c7                	mov    %eax,%edi
    4616:	e8 75 dd ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    461b:	48 98                	cltq
    461d:	48 39 d8             	cmp    %rbx,%rax
    4620:	7c 1e                	jl     4640 <copy_file_contents+0x70>
    close(fd);
    4622:	44 89 e7             	mov    %r12d,%edi
    4625:	e8 46 dd ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    462a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    462e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4632:	48 83 c4 08          	add    $0x8,%rsp
    4636:	5b                   	pop    %rbx
    4637:	5d                   	pop    %rbp
    4638:	41 5c                	pop    %r12
    463a:	41 5d                	pop    %r13
    463c:	c3                   	ret
    463d:	0f 1f 00             	nopl   (%rax)
    4640:	48 8b 0d d9 59 00 00 	mov    0x59d9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4647:	ba 1a 00 00 00       	mov    $0x1a,%edx
    464c:	be 01 00 00 00       	mov    $0x1,%esi
    4651:	48 8d 3d 78 2a 00 00 	lea    0x2a78(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    4658:	e8 63 de ff ff       	call   24c0 <fwrite@plt>
    465d:	eb c3                	jmp    4622 <copy_file_contents+0x52>
    465f:	48 8b 0d ba 59 00 00 	mov    0x59ba(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4666:	ba 28 00 00 00       	mov    $0x28,%edx
    466b:	be 01 00 00 00       	mov    $0x1,%esi
    4670:	48 8d 3d 91 2d 00 00 	lea    0x2d91(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4677:	e8 44 de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    467c:	bf 01 00 00 00       	mov    $0x1,%edi
    4681:	e8 1a de ff ff       	call   24a0 <exit@plt>
    4686:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004690 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4690:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
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
    46b9:	0f 82 a3 de ff ff    	jb     2562 <add_write_request.cold>
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
    4761:	0f 82 0b de ff ff    	jb     2572 <add_read_request.cold>
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
    489a:	0f 82 dc dc ff ff    	jb     257c <_send_static_string_content.cold>
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
    4b41:	e8 5a f5 ff ff       	call   40a0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4b46:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4b4b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4b4f:	4c 89 f7             	mov    %r14,%rdi
    4b52:	e8 79 fa ff ff       	call   45d0 <copy_file_contents>
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
    4dbe:	0f 82 c8 d7 ff ff    	jb     258c <add_accept_request.cold>
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
    4e5b:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e5f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4e64:	bf 00 01 00 00       	mov    $0x100,%edi
    4e69:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4e6c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4e70:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4e75:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4e7a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4e7f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4e84:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4e8c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4e91:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4e99:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4e9e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4ea6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4eab:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4eb3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4eb8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4ec0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4ec5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4ecd:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4ed5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4edd:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4ee5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4eed:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4ef5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4efd:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4f05:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4f0d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4f15:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4f1d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4f24:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4f2c:	e8 bf d4 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4f31:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
    4f35:	31 f6                	xor    %esi,%esi
    4f37:	e8 a4 d5 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4f3c:	31 d2                	xor    %edx,%edx
    4f3e:	be 01 00 00 00       	mov    $0x1,%esi
    4f43:	bf 02 00 00 00       	mov    $0x2,%edi
    4f48:	e8 e3 d5 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4f4d:	83 f8 ff             	cmp    $0xffffffff,%eax
    4f50:	0f 84 78 d6 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    4f56:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4f5b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4f61:	89 c7                	mov    %eax,%edi
    4f63:	41 89 c4             	mov    %eax,%r12d
    4f66:	ba 02 00 00 00       	mov    $0x2,%edx
    4f6b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4f70:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4f78:	e8 83 d3 ff ff       	call   2300 <setsockopt@plt>
    4f7d:	85 c0                	test   %eax,%eax
    4f7f:	0f 88 1d d6 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4f85:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4f8a:	ba 10 00 00 00       	mov    $0x10,%edx
    4f8f:	44 89 e7             	mov    %r12d,%edi
    4f92:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4f9b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4fa3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4fab:	e8 b0 d4 ff ff       	call   2460 <bind@plt>
    4fb0:	85 c0                	test   %eax,%eax
    4fb2:	0f 88 22 d6 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4fb8:	be 0a 00 00 00       	mov    $0xa,%esi
    4fbd:	44 89 e7             	mov    %r12d,%edi
    4fc0:	e8 5b d4 ff ff       	call   2420 <listen@plt>
    4fc5:	85 c0                	test   %eax,%eax
    4fc7:	0f 88 e1 d5 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4fcd:	ba db 18 00 00       	mov    $0x18db,%edx
    4fd2:	48 8d 35 a3 21 00 00 	lea    0x21a3(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4fd9:	bf 01 00 00 00       	mov    $0x1,%edi
    4fde:	31 c0                	xor    %eax,%eax
    4fe0:	e8 6b d4 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4fe5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4fea:	48 89 d9             	mov    %rbx,%rcx
    4fed:	44 89 e7             	mov    %r12d,%edi
    4ff0:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4ff5:	48 89 c6             	mov    %rax,%rsi
    4ff8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4ffd:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5002:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    500a:	e8 81 fd ff ff       	call   4d90 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    500f:	bf 01 00 00 00       	mov    $0x1,%edi
    5014:	be 10 00 00 00       	mov    $0x10,%esi
    5019:	e8 82 d3 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    501e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5023:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5026:	e8 e5 d3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    502b:	48 85 c0             	test   %rax,%rax
    502e:	0f 84 ae 04 00 00    	je     54e2 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5034:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5038:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    503f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5046:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    504e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5051:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5056:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5058:	f6 c1 02             	test   $0x2,%cl
    505b:	0f 85 0f 04 00 00    	jne    5470 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5061:	89 d0                	mov    %edx,%eax
    5063:	29 f0                	sub    %esi,%eax
    5065:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    506c:	0f 82 52 d5 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5072:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5075:	48 8d 75 50          	lea    0x50(%rbp),%rsi
	sqe->addr3 = 0;
    5079:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    507d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5080:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5087:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    508a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5091:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5098:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    509a:	8b 55 50             	mov    0x50(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    509d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    50a2:	48 c1 e0 06          	shl    $0x6,%rax
    50a6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    50ae:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    50b4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    50b7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    50bf:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    50c3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    50cb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    50d3:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    50d7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    50db:	e8 60 d2 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    50e0:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    50e4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    50e9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    50f1:	0f 85 d7 01 00 00    	jne    52ce <io_thread+0x49e>
    50f7:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    50fc:	4d 89 ce             	mov    %r9,%r14
    50ff:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5104:	0f 1f 40 00          	nopl   0x0(%rax)
    5108:	48 8d 3d 83 20 00 00 	lea    0x2083(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    510f:	e8 dc d1 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5114:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    511b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5122:	c1 e9 0b             	shr    $0xb,%ecx
    5125:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5128:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5130:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5132:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    513a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    513c:	39 d0                	cmp    %edx,%eax
    513e:	74 36                	je     5176 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5140:	89 f8                	mov    %edi,%eax
    5142:	21 d0                	and    %edx,%eax
    5144:	d3 e0                	shl    %cl,%eax
    5146:	48 c1 e0 04          	shl    $0x4,%rax
    514a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5152:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    515a:	0f 85 a8 01 00 00    	jne    5308 <io_thread+0x4d8>
    5160:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5164:	0f 85 0e 03 00 00    	jne    5478 <io_thread+0x648>
			if (cqe->res < 0)
    516a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    516d:	83 c2 01             	add    $0x1,%edx
    5170:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5172:	85 c0                	test   %eax,%eax
    5174:	79 b2                	jns    5128 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5176:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    517f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5180:	45 31 c0             	xor    %r8d,%r8d
    5183:	31 d2                	xor    %edx,%edx
    5185:	b9 01 00 00 00       	mov    $0x1,%ecx
    518a:	4c 89 f6             	mov    %r14,%rsi
    518d:	48 89 df             	mov    %rbx,%rdi
    5190:	e8 ab d2 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5195:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5198:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    519d:	48 83 38 01          	cmpq   $0x1,(%rax)
    51a1:	0f 84 e1 02 00 00    	je     5488 <io_thread+0x658>
    51a7:	48 8d 3d 0a 20 00 00 	lea    0x200a(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    51ae:	e8 3d d1 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    51b3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    51b8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    51bb:	45 85 ff             	test   %r15d,%r15d
    51be:	0f 88 d2 d3 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    51c4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    51c7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    51cb:	85 c0                	test   %eax,%eax
    51cd:	0f 88 d5 02 00 00    	js     54a8 <io_thread+0x678>
      switch (req->event_type) {
    51d3:	41 83 f8 01          	cmp    $0x1,%r8d
    51d7:	0f 84 7b 01 00 00    	je     5358 <io_thread+0x528>
    51dd:	41 83 f8 02          	cmp    $0x2,%r8d
    51e1:	0f 84 a1 01 00 00    	je     5388 <io_thread+0x558>
    51e7:	45 85 c0             	test   %r8d,%r8d
    51ea:	0f 85 50 01 00 00    	jne    5340 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    51f0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    51f5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    51fa:	48 89 d9             	mov    %rbx,%rcx
    51fd:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5201:	e8 8a fb ff ff       	call   4d90 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5206:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    520b:	48 89 de             	mov    %rbx,%rsi
    520e:	8b 78 08             	mov    0x8(%rax),%edi
    5211:	e8 1a f5 ff ff       	call   4730 <add_read_request>
              free(req);
    5216:	4c 89 e7             	mov    %r12,%rdi
    5219:	e8 a2 d0 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    521e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5223:	48 85 c0             	test   %rax,%rax
    5226:	0f 85 14 01 00 00    	jne    5340 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    522c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5233:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    523a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    523d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5242:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5244:	f6 c1 02             	test   $0x2,%cl
    5247:	74 00                	je     5249 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5249:	89 d0                	mov    %edx,%eax
    524b:	29 f0                	sub    %esi,%eax
    524d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5254:	0f 82 60 d3 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    525a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    525d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5262:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5266:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5269:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5270:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5273:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    527a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5281:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5283:	8b 55 50             	mov    0x50(%rbp),%edx
    5286:	48 c1 e0 06          	shl    $0x6,%rax
    528a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5292:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5298:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    529b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    52a3:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    52a7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    52af:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    52b7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    52bb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    52bf:	e8 7c d0 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    52c4:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    52c8:	0f 84 3a fe ff ff    	je     5108 <io_thread+0x2d8>
    52ce:	48 8d 3d 1c 1f 00 00 	lea    0x1f1c(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    52d5:	e8 16 d0 ff ff       	call   22f0 <puts@plt>
}
    52da:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    52e2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    52eb:	0f 85 18 02 00 00    	jne    5509 <io_thread+0x6d9>
    52f1:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    52f8:	31 c0                	xor    %eax,%eax
    52fa:	5b                   	pop    %rbx
    52fb:	5d                   	pop    %rbp
    52fc:	41 5c                	pop    %r12
    52fe:	41 5d                	pop    %r13
    5300:	41 5e                	pop    %r14
    5302:	41 5f                	pop    %r15
    5304:	c3                   	ret
    5305:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5308:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    530d:	48 85 c0             	test   %rax,%rax
    5310:	0f 84 6a fe ff ff    	je     5180 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5316:	48 83 38 01          	cmpq   $0x1,(%rax)
    531a:	0f 84 68 01 00 00    	je     5488 <io_thread+0x658>
    5320:	48 8d 3d 91 1e 00 00 	lea    0x1e91(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    5327:	e8 c4 cf ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    532c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5331:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5334:	e9 8b fe ff ff       	jmp    51c4 <io_thread+0x394>
    5339:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5340:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5348:	8b 02                	mov    (%rdx),%eax
    534a:	83 c0 01             	add    $0x1,%eax
    534d:	89 02                	mov    %eax,(%rdx)
}
    534f:	e9 d8 fe ff ff       	jmp    522c <io_thread+0x3fc>
    5354:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5358:	85 c0                	test   %eax,%eax
    535a:	75 74                	jne    53d0 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    535c:	48 8b 0d bd 4c 00 00 	mov    0x4cbd(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5363:	ba 0f 00 00 00       	mov    $0xf,%edx
    5368:	be 01 00 00 00       	mov    $0x1,%esi
    536d:	48 8d 3d 6d 1e 00 00 	lea    0x1e6d(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    5374:	e8 47 d1 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5379:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    537e:	e9 a0 fe ff ff       	jmp    5223 <io_thread+0x3f3>
    5383:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5388:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    538d:	45 31 ff             	xor    %r15d,%r15d
    5390:	85 c0                	test   %eax,%eax
    5392:	7e 20                	jle    53b4 <io_thread+0x584>
    5394:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5398:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    539b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    539f:	48 c1 e0 04          	shl    $0x4,%rax
    53a3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    53a8:	e8 13 cf ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    53ad:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    53b2:	7f e4                	jg     5398 <io_thread+0x568>
              close(req->client_socket);
    53b4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    53b9:	e8 b2 cf ff ff       	call   2370 <close@plt>
              free(req);
    53be:	4c 89 e7             	mov    %r12,%rdi
    53c1:	e8 fa ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    53c6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    53cb:	e9 53 fe ff ff       	jmp    5223 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    53d0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    53d5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    53da:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    53e2:	eb 11                	jmp    53f5 <io_thread+0x5c5>
    53e4:	0f 1f 40 00          	nopl   0x0(%rax)
    53e8:	48 83 c0 01          	add    $0x1,%rax
    53ec:	48 83 c2 01          	add    $0x1,%rdx
    53f0:	48 39 c6             	cmp    %rax,%rsi
    53f3:	74 4b                	je     5440 <io_thread+0x610>
        dest[i] = src[i];
    53f5:	0f b6 0a             	movzbl (%rdx),%ecx
    53f8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    53fa:	80 f9 0d             	cmp    $0xd,%cl
    53fd:	75 e9                	jne    53e8 <io_thread+0x5b8>
    53ff:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5403:	75 e3                	jne    53e8 <io_thread+0x5b8>
            dest[i] = '\0';
    5405:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5408:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    540d:	48 89 da             	mov    %rbx,%rdx
    5410:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5415:	e8 96 f7 ff ff       	call   4bb0 <handle_http_method>
              free(req->iov[0].iov_base);
    541a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    541f:	e8 9c ce ff ff       	call   22c0 <free@plt>
              free(req);
    5424:	4c 89 e7             	mov    %r12,%rdi
    5427:	e8 94 ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    542c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5431:	e9 ed fd ff ff       	jmp    5223 <io_thread+0x3f3>
    5436:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5440:	48 8b 0d d9 4b 00 00 	mov    0x4bd9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5447:	ba 12 00 00 00       	mov    $0x12,%edx
    544c:	be 01 00 00 00       	mov    $0x1,%esi
    5451:	48 8d 3d df 1c 00 00 	lea    0x1cdf(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5458:	e8 63 d0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    545d:	bf 01 00 00 00       	mov    $0x1,%edi
    5462:	e8 39 d0 ff ff       	call   24a0 <exit@plt>
    5467:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5470:	e9 ec fb ff ff       	jmp    5061 <io_thread+0x231>
    5475:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5478:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    547d:	e9 94 fe ff ff       	jmp    5316 <io_thread+0x4e6>
    5482:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5488:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5490:	48 8d 3d 0d 1d 00 00 	lea    0x1d0d(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    5497:	8b 02                	mov    (%rdx),%eax
    5499:	83 c0 01             	add    $0x1,%eax
    549c:	89 02                	mov    %eax,(%rdx)
    549e:	e8 4d ce ff ff       	call   22f0 <puts@plt>
    54a3:	e9 26 fe ff ff       	jmp    52ce <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    54a8:	f7 d8                	neg    %eax
    54aa:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    54af:	89 c7                	mov    %eax,%edi
    54b1:	e8 4a d0 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    54b6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    54bb:	be 01 00 00 00       	mov    $0x1,%esi
    54c0:	48 8b 3d 59 4b 00 00 	mov    0x4b59(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    54c7:	48 89 c1             	mov    %rax,%rcx
    54ca:	48 8d 15 67 1f 00 00 	lea    0x1f67(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    54d1:	31 c0                	xor    %eax,%eax
    54d3:	e8 f8 cf ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    54d8:	bf 01 00 00 00       	mov    $0x1,%edi
    54dd:	e8 be cf ff ff       	call   24a0 <exit@plt>
    54e2:	48 8b 0d 37 4b 00 00 	mov    0x4b37(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    54e9:	ba 28 00 00 00       	mov    $0x28,%edx
    54ee:	be 01 00 00 00       	mov    $0x1,%esi
    54f3:	48 8d 3d 0e 1f 00 00 	lea    0x1f0e(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    54fa:	e8 c1 cf ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    54ff:	bf 01 00 00 00       	mov    $0x1,%edi
    5504:	e8 97 cf ff ff       	call   24a0 <exit@plt>
}
    5509:	e8 22 ce ff ff       	call   2330 <__stack_chk_fail@plt>
    550e:	66 90                	xchg   %ax,%ax

0000000000005510 <sendm>:
int sendm(struct BarrierTask *data) {
    5510:	f3 0f 1e fa          	endbr64
    5514:	41 57                	push   %r15
    5516:	41 56                	push   %r14
    5518:	41 55                	push   %r13
    551a:	41 54                	push   %r12
    551c:	55                   	push   %rbp
    551d:	53                   	push   %rbx
    551e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5522:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
    5529:	0f 85 99 01 00 00    	jne    56c8 <sendm+0x1b8>
    552f:	48 8d b7 80 01 00 00 	lea    0x180(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5536:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    553c:	48 89 fa             	mov    %rdi,%rdx
    553f:	31 c9                	xor    %ecx,%ecx
    5541:	48 89 34 24          	mov    %rsi,(%rsp)
    5545:	48 8d b7 88 01 00 00 	lea    0x188(%rdi),%rsi
    554c:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5551:	85 c0                	test   %eax,%eax
    5553:	0f 8e ce 00 00 00    	jle    5627 <sendm+0x117>
    5559:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5560:	39 8a 30 01 00 00    	cmp    %ecx,0x130(%rdx)
    5566:	0f 84 af 00 00 00    	je     561b <sendm+0x10b>
        struct Data *them = data->mailboxes[n].higher;
    556c:	49 89 ca             	mov    %rcx,%r10
    556f:	49 c1 e2 05          	shl    $0x5,%r10
    5573:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
    557a:	4d 8b 5a 08          	mov    0x8(%r10),%r11
        for (; them->messages_count < min;) {
    557e:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    5582:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    5586:	4c 39 cb             	cmp    %r9,%rbx
    5589:	0f 8d 83 00 00 00    	jge    5612 <sendm+0x102>
    558f:	4c 89 cf             	mov    %r9,%rdi
    5592:	48 8b aa 08 01 00 00 	mov    0x108(%rdx),%rbp
    5599:	4d 8b 72 10          	mov    0x10(%r10),%r14
    559d:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    55a0:	49 8b 33             	mov    (%r11),%rsi
    55a3:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    55a7:	48 83 f8 02          	cmp    $0x2,%rax
    55ab:	0f 86 ff 00 00 00    	jbe    56b0 <sendm+0x1a0>
    55b1:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    55b9:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    55c1:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    55c5:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    55c9:	4c 39 2c 24          	cmp    %r13,(%rsp)
    55cd:	73 71                	jae    5640 <sendm+0x130>
    55cf:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    55d4:	4d 39 fc             	cmp    %r15,%r12
    55d7:	73 67                	jae    5640 <sendm+0x130>
    55d9:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    55dd:	49 01 f0             	add    %rsi,%r8
    55e0:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    55e7:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    55eb:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    55ef:	49 39 d8             	cmp    %rbx,%r8
    55f2:	75 ec                	jne    55e0 <sendm+0xd0>
    55f4:	0f 1f 40 00          	nopl   0x0(%rax)
    55f8:	48 01 fd             	add    %rdi,%rbp
    55fb:	4c 01 f7             	add    %r14,%rdi
    55fe:	48 89 aa 08 01 00 00 	mov    %rbp,0x108(%rdx)
    5605:	49 89 7a 10          	mov    %rdi,0x10(%r10)
    5609:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    560d:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5612:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5615:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    561b:	48 83 c1 01          	add    $0x1,%rcx
    561f:	39 c8                	cmp    %ecx,%eax
    5621:	0f 8f 39 ff ff ff    	jg     5560 <sendm+0x50>
}
    5627:	48 83 c4 18          	add    $0x18,%rsp
    562b:	31 c0                	xor    %eax,%eax
    562d:	5b                   	pop    %rbx
    562e:	5d                   	pop    %rbp
    562f:	41 5c                	pop    %r12
    5631:	41 5d                	pop    %r13
    5633:	41 5e                	pop    %r14
    5635:	41 5f                	pop    %r15
    5637:	c3                   	ret
    5638:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5640:	49 89 fd             	mov    %rdi,%r13
    5643:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    564a:	4d 89 e0             	mov    %r12,%r8
    564d:	49 d1 ed             	shr    %r13
    5650:	49 c1 e5 04          	shl    $0x4,%r13
    5654:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5659:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    565d:	41 83 e5 10          	and    $0x10,%r13d
    5661:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5665:	74 11                	je     5678 <sendm+0x168>
          them->messages[them->messages_count++] = data->message; 
    5667:	49 83 c0 10          	add    $0x10,%r8
    566b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5670:	4d 39 f8             	cmp    %r15,%r8
    5673:	74 15                	je     568a <sendm+0x17a>
    5675:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5678:	41 0f 11 00          	movups %xmm0,(%r8)
    567c:	49 83 c0 20          	add    $0x20,%r8
    5680:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    5685:	4d 39 f8             	cmp    %r15,%r8
    5688:	75 ee                	jne    5678 <sendm+0x168>
    568a:	49 89 f8             	mov    %rdi,%r8
    568d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    5691:	49 01 d8             	add    %rbx,%r8
    5694:	40 f6 c7 01          	test   $0x1,%dil
    5698:	0f 84 5a ff ff ff    	je     55f8 <sendm+0xe8>
          them->messages[them->messages_count++] = data->message; 
    569e:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    56a5:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    56a9:	e9 4a ff ff ff       	jmp    55f8 <sendm+0xe8>
    56ae:	66 90                	xchg   %ax,%ax
    56b0:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    56b8:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    56c0:	e9 14 ff ff ff       	jmp    55d9 <sendm+0xc9>
    56c5:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    56c8:	48 8d 3d 35 1b 00 00 	lea    0x1b35(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    56cf:	e8 1c cc ff ff       	call   22f0 <puts@plt>
    56d4:	e9 4e ff ff ff       	jmp    5627 <sendm+0x117>
    56d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000056e0 <receive>:
int receive(struct BarrierTask *data) {
    56e0:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    56e4:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    56ea:	85 c0                	test   %eax,%eax
    56ec:	0f 8e f1 00 00 00    	jle    57e3 <receive+0x103>
int receive(struct BarrierTask *data) {
    56f2:	41 54                	push   %r12
    56f4:	48 89 fa             	mov    %rdi,%rdx
    56f7:	55                   	push   %rbp
    56f8:	31 ed                	xor    %ebp,%ebp
    56fa:	53                   	push   %rbx
    56fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5700:	48 89 ee             	mov    %rbp,%rsi
    5703:	48 c1 e6 05          	shl    $0x5,%rsi
    5707:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    570e:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5711:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    5716:	48 85 ff             	test   %rdi,%rdi
    5719:	0f 8e a1 00 00 00    	jle    57c0 <receive+0xe0>
      data->sends++;
    571f:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    5726:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    572a:	4c 63 1a             	movslq (%rdx),%r11
    572d:	49 89 c9             	mov    %rcx,%r9
    5730:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5734:	49 f7 d9             	neg    %r9
    5737:	48 01 c7             	add    %rax,%rdi
    573a:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    573e:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    5745:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    5749:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    574c:	49 29 c8             	sub    %rcx,%r8
    574f:	eb 10                	jmp    5761 <receive+0x81>
    5751:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5758:	48 83 c0 01          	add    $0x1,%rax
    575c:	48 39 c7             	cmp    %rax,%rdi
    575f:	74 5f                	je     57c0 <receive+0xe0>
      data->n++;
    5761:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    5765:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
      data->n++;
    576c:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5773:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5777:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    577b:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5780:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5784:	75 d2                	jne    5758 <receive+0x78>
    5786:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    578d:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5791:	75 c5                	jne    5758 <receive+0x78>
    5793:	bf 01 00 00 00       	mov    $0x1,%edi
    5798:	b9 01 00 00 00       	mov    $0x1,%ecx
    579d:	ba 01 00 00 00       	mov    $0x1,%edx
    57a2:	31 c0                	xor    %eax,%eax
    57a4:	48 8d 35 b5 1c 00 00 	lea    0x1cb5(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    57ab:	e8 a0 cc ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    57b0:	bf 01 00 00 00       	mov    $0x1,%edi
    57b5:	e8 e6 cc ff ff       	call   24a0 <exit@plt>
    57ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    57c0:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    57c9:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    57cc:	48 83 c5 01          	add    $0x1,%rbp
    57d0:	39 aa 34 01 00 00    	cmp    %ebp,0x134(%rdx)
    57d6:	0f 8f 24 ff ff ff    	jg     5700 <receive+0x20>
}
    57dc:	5b                   	pop    %rbx
    57dd:	31 c0                	xor    %eax,%eax
    57df:	5d                   	pop    %rbp
    57e0:	41 5c                	pop    %r12
    57e2:	c3                   	ret
    57e3:	31 c0                	xor    %eax,%eax
    57e5:	c3                   	ret
    57e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000057f0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    57f0:	f3 0f 1e fa          	endbr64
    57f4:	41 57                	push   %r15
    57f6:	41 56                	push   %r14
    57f8:	41 55                	push   %r13
    57fa:	41 54                	push   %r12
    57fc:	55                   	push   %rbp
    57fd:	53                   	push   %rbx
    57fe:	48 89 fb             	mov    %rdi,%rbx
    5801:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    5805:	8b 07                	mov    (%rdi),%eax
    5807:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    580d:	0f 84 3d 01 00 00    	je     5950 <barriered_work+0x160>
    receive(data);
    5813:	e8 c8 fe ff ff       	call   56e0 <receive>
    while (data->scheduled == 1) {
    5818:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    581f:	75 1b                	jne    583c <barriered_work+0x4c>
    5821:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    5828:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    5830:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5833:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    583a:	74 ec                	je     5828 <barriered_work+0x38>
  if (data->sending == 1) {
    583c:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    5843:	0f 85 74 02 00 00    	jne    5abd <barriered_work+0x2cd>
      for (int n = 0 ; n < data->thread_count; n++) {
    5849:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    584f:	85 c0                	test   %eax,%eax
    5851:	0f 8e 72 02 00 00    	jle    5ac9 <barriered_work+0x2d9>
    5857:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    585e:	31 d2                	xor    %edx,%edx
    5860:	48 89 0c 24          	mov    %rcx,(%rsp)
    5864:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    586b:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    5870:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5876:	0f 84 bf 00 00 00    	je     593b <barriered_work+0x14b>
        struct Data *them = data->mailboxes[n].higher;
    587c:	49 89 d1             	mov    %rdx,%r9
    587f:	49 c1 e1 05          	shl    $0x5,%r9
    5883:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    588a:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    588e:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5892:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5896:	4d 39 c3             	cmp    %r8,%r11
    5899:	0f 8d 93 00 00 00    	jge    5932 <barriered_work+0x142>
    589f:	4c 89 c6             	mov    %r8,%rsi
    58a2:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    58a9:	4d 8b 71 10          	mov    0x10(%r9),%r14
    58ad:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    58b0:	49 8b 0a             	mov    (%r10),%rcx
    58b3:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    58b7:	48 83 f8 02          	cmp    $0x2,%rax
    58bb:	0f 86 8f 02 00 00    	jbe    5b50 <barriered_work+0x360>
    58c1:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    58c9:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    58d1:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    58d5:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    58d9:	4c 39 2c 24          	cmp    %r13,(%rsp)
    58dd:	0f 83 fd 01 00 00    	jae    5ae0 <barriered_work+0x2f0>
    58e3:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    58e8:	4d 39 fc             	cmp    %r15,%r12
    58eb:	0f 83 ef 01 00 00    	jae    5ae0 <barriered_work+0x2f0>
    58f1:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    58f5:	48 01 cf             	add    %rcx,%rdi
    58f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5900:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5907:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    590b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    590f:	49 39 fb             	cmp    %rdi,%r11
    5912:	75 ec                	jne    5900 <barriered_work+0x110>
    5914:	0f 1f 40 00          	nopl   0x0(%rax)
    5918:	48 01 f5             	add    %rsi,%rbp
    591b:	4c 01 f6             	add    %r14,%rsi
    591e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5925:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5929:	4d 89 42 08          	mov    %r8,0x8(%r10)
    592d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5932:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5935:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    593b:	48 83 c2 01          	add    $0x1,%rdx
    593f:	39 d0                	cmp    %edx,%eax
    5941:	0f 8f 29 ff ff ff    	jg     5870 <barriered_work+0x80>
    5947:	e9 7d 01 00 00       	jmp    5ac9 <barriered_work+0x2d9>
    594c:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    5950:	e8 8b fd ff ff       	call   56e0 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    5955:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    595c:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    595e:	45 85 c9             	test   %r9d,%r9d
    5961:	0f 8e 85 00 00 00    	jle    59ec <barriered_work+0x1fc>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5967:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    596e:	4c 63 d8             	movslq %eax,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    5971:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5974:	49 c1 e3 09          	shl    $0x9,%r11
    5978:	4c 8b 52 10          	mov    0x10(%rdx),%r10
              int next_task = abs((t + 1) % (data->thread_count));
    597c:	99                   	cltd
    597d:	41 f7 f9             	idiv   %r9d
    5980:	4c 89 d7             	mov    %r10,%rdi
    5983:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
    5987:	89 d0                	mov    %edx,%eax
    5989:	f7 d8                	neg    %eax
    598b:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    598e:	45 31 c0             	xor    %r8d,%r8d
              int next_task = abs((t + 1) % (data->thread_count));
    5991:	48 63 ea             	movslq %edx,%rbp
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5994:	48 c1 e5 09          	shl    $0x9,%rbp
    5998:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    59a0:	31 c0                	xor    %eax,%eax
    59a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59a8:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    59ac:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    59b0:	48 8b 8c 2a 68 01 00 00 	mov    0x168(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59b8:	48 8b 17             	mov    (%rdi),%rdx
    59bb:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    59bf:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    59c2:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59c6:	48 c1 e2 05          	shl    $0x5,%rdx
    59ca:	4a 03 94 1e 68 01 00 00 	add    0x168(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    59d2:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    59d6:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    59da:	49 39 c1             	cmp    %rax,%r9
    59dd:	75 c9                	jne    59a8 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    59df:	48 83 c7 08          	add    $0x8,%rdi
    59e3:	49 83 c0 20          	add    $0x20,%r8
    59e7:	49 39 fc             	cmp    %rdi,%r12
    59ea:	75 b4                	jne    59a0 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    59ec:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    59ef:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    59f6:	31 ff                	xor    %edi,%edi
    59f8:	48 c1 e6 05          	shl    $0x5,%rsi
    59fc:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5a03:	e8 08 c9 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5a08:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5a0f:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5a16:	48 8b 50 38          	mov    0x38(%rax),%rdx
    5a1a:	8b 4a 10             	mov    0x10(%rdx),%ecx
    5a1d:	8d 69 01             	lea    0x1(%rcx),%ebp
    5a20:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5a23:	75 53                	jne    5a78 <barriered_work+0x288>
    5a25:	0f 1f 00             	nopl   (%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a28:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    5a2f:	48 8b 40 10          	mov    0x10(%rax),%rax
    5a33:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    5a36:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a3e:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5a42:	48 c1 e7 09          	shl    $0x9,%rdi
    5a46:	48 03 78 28          	add    0x28(%rax),%rdi
    5a4a:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    5a50:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5a53:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    5a5a:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5a61:	74 c5                	je     5a28 <barriered_work+0x238>
    if (modcount != data->thread->protected_state->modcount) {
    5a63:	48 8b 40 38          	mov    0x38(%rax),%rax
    5a67:	3b 68 10             	cmp    0x10(%rax),%ebp
    5a6a:	74 0c                	je     5a78 <barriered_work+0x288>
    5a6c:	48 8d 3d 9d 17 00 00 	lea    0x179d(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    5a73:	e8 78 c8 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5a78:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5a7f:	31 ff                	xor    %edi,%edi
    5a81:	48 c1 e6 05          	shl    $0x5,%rsi
    5a85:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5a8c:	48 83 c6 10          	add    $0x10,%rsi
    5a90:	e8 7b c8 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5a95:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    5a9c:	48 83 c0 01          	add    $0x1,%rax
    5aa0:	48 99                	cqto
    5aa2:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    5aa9:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5ab0:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    5ab7:	0f 84 a8 00 00 00    	je     5b65 <barriered_work+0x375>
    5abd:	48 8d 3d 40 17 00 00 	lea    0x1740(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5ac4:	e8 27 c8 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5ac9:	0f ae f8             	sfence
}
    5acc:	48 83 c4 18          	add    $0x18,%rsp
    5ad0:	31 c0                	xor    %eax,%eax
    5ad2:	5b                   	pop    %rbx
    5ad3:	5d                   	pop    %rbp
    5ad4:	41 5c                	pop    %r12
    5ad6:	41 5d                	pop    %r13
    5ad8:	41 5e                	pop    %r14
    5ada:	41 5f                	pop    %r15
    5adc:	c3                   	ret
    5add:	0f 1f 00             	nopl   (%rax)
    5ae0:	49 89 f5             	mov    %rsi,%r13
    5ae3:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5aea:	4c 89 e7             	mov    %r12,%rdi
    5aed:	49 d1 ed             	shr    %r13
    5af0:	49 c1 e5 04          	shl    $0x4,%r13
    5af4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5af9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5afd:	41 83 e5 10          	and    $0x10,%r13d
    5b01:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5b05:	74 11                	je     5b18 <barriered_work+0x328>
          them->messages[them->messages_count++] = data->message; 
    5b07:	48 83 c7 10          	add    $0x10,%rdi
    5b0b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5b10:	49 39 ff             	cmp    %rdi,%r15
    5b13:	74 13                	je     5b28 <barriered_work+0x338>
    5b15:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5b18:	0f 11 07             	movups %xmm0,(%rdi)
    5b1b:	48 83 c7 20          	add    $0x20,%rdi
    5b1f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5b23:	49 39 ff             	cmp    %rdi,%r15
    5b26:	75 f0                	jne    5b18 <barriered_work+0x328>
    5b28:	48 89 f7             	mov    %rsi,%rdi
    5b2b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5b2f:	4c 01 df             	add    %r11,%rdi
    5b32:	40 f6 c6 01          	test   $0x1,%sil
    5b36:	0f 84 dc fd ff ff    	je     5918 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    5b3c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b43:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5b47:	e9 cc fd ff ff       	jmp    5918 <barriered_work+0x128>
    5b4c:	0f 1f 40 00          	nopl   0x0(%rax)
    5b50:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5b58:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5b60:	e9 8c fd ff ff       	jmp    58f1 <barriered_work+0x101>
      for (int n = 0 ; n < data->thread_count; n++) {
    5b65:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    5b6c:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5b72:	31 d2                	xor    %edx,%edx
    5b74:	48 89 0c 24          	mov    %rcx,(%rsp)
    5b78:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    5b7f:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5b84:	85 c0                	test   %eax,%eax
    5b86:	0f 8e 3d ff ff ff    	jle    5ac9 <barriered_work+0x2d9>
    5b8c:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5b90:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5b96:	0f 84 af 00 00 00    	je     5c4b <barriered_work+0x45b>
        struct Data *them = data->mailboxes[n].higher;
    5b9c:	49 89 d1             	mov    %rdx,%r9
    5b9f:	49 c1 e1 05          	shl    $0x5,%r9
    5ba3:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    5baa:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    5bae:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5bb2:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5bb6:	4d 39 d8             	cmp    %r11,%r8
    5bb9:	0f 8e 83 00 00 00    	jle    5c42 <barriered_work+0x452>
    5bbf:	4c 89 c6             	mov    %r8,%rsi
    5bc2:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5bc9:	4d 8b 71 10          	mov    0x10(%r9),%r14
    5bcd:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5bd0:	49 8b 0a             	mov    (%r10),%rcx
    5bd3:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5bd7:	48 83 f8 02          	cmp    $0x2,%rax
    5bdb:	0f 86 ef 00 00 00    	jbe    5cd0 <barriered_work+0x4e0>
    5be1:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5be9:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5bf1:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5bf5:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5bf9:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5bfd:	73 61                	jae    5c60 <barriered_work+0x470>
    5bff:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5c04:	4d 39 fc             	cmp    %r15,%r12
    5c07:	73 57                	jae    5c60 <barriered_work+0x470>
    5c09:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5c0d:	48 01 cf             	add    %rcx,%rdi
    5c10:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5c17:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5c1b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5c1f:	49 39 fb             	cmp    %rdi,%r11
    5c22:	75 ec                	jne    5c10 <barriered_work+0x420>
    5c24:	0f 1f 40 00          	nopl   0x0(%rax)
    5c28:	48 01 f5             	add    %rsi,%rbp
    5c2b:	4c 01 f6             	add    %r14,%rsi
    5c2e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5c35:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5c39:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5c3d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5c42:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5c45:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5c4b:	48 83 c2 01          	add    $0x1,%rdx
    5c4f:	39 d0                	cmp    %edx,%eax
    5c51:	0f 8f 39 ff ff ff    	jg     5b90 <barriered_work+0x3a0>
    5c57:	e9 6d fe ff ff       	jmp    5ac9 <barriered_work+0x2d9>
    5c5c:	0f 1f 40 00          	nopl   0x0(%rax)
    5c60:	49 89 f5             	mov    %rsi,%r13
    5c63:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5c6a:	4c 89 e7             	mov    %r12,%rdi
    5c6d:	49 d1 ed             	shr    %r13
    5c70:	49 c1 e5 04          	shl    $0x4,%r13
    5c74:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5c79:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5c7d:	41 83 e5 10          	and    $0x10,%r13d
    5c81:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5c85:	74 11                	je     5c98 <barriered_work+0x4a8>
          them->messages[them->messages_count++] = data->message; 
    5c87:	48 83 c7 10          	add    $0x10,%rdi
    5c8b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5c90:	4c 39 ff             	cmp    %r15,%rdi
    5c93:	74 13                	je     5ca8 <barriered_work+0x4b8>
    5c95:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5c98:	0f 11 07             	movups %xmm0,(%rdi)
    5c9b:	48 83 c7 20          	add    $0x20,%rdi
    5c9f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5ca3:	4c 39 ff             	cmp    %r15,%rdi
    5ca6:	75 f0                	jne    5c98 <barriered_work+0x4a8>
    5ca8:	48 89 f7             	mov    %rsi,%rdi
    5cab:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5caf:	4c 01 df             	add    %r11,%rdi
    5cb2:	40 f6 c6 01          	test   $0x1,%sil
    5cb6:	0f 84 6c ff ff ff    	je     5c28 <barriered_work+0x438>
          them->messages[them->messages_count++] = data->message; 
    5cbc:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5cc3:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5cc7:	e9 5c ff ff ff       	jmp    5c28 <barriered_work+0x438>
    5ccc:	0f 1f 40 00          	nopl   0x0(%rax)
    5cd0:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5cd8:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5ce0:	e9 24 ff ff ff       	jmp    5c09 <barriered_work+0x419>
    5ce5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005cf0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5cf0:	f3 0f 1e fa          	endbr64
    5cf4:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5cf8:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5cff:	48 8b 40 40          	mov    0x40(%rax),%rax
    5d03:	48 63 10             	movslq (%rax),%rdx
    5d06:	85 d2                	test   %edx,%edx
    5d08:	7e 2c                	jle    5d36 <barriered_work_ingest+0x46>
    5d0a:	48 8b 40 08          	mov    0x8(%rax),%rax
    5d0e:	48 c1 e2 04          	shl    $0x4,%rdx
    5d12:	48 01 c2             	add    %rax,%rdx
    5d15:	0f 1f 00             	nopl   (%rax)
    if (data->thread->buffers->buffer[x].available == 1) {
    5d18:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5d1c:	75 0f                	jne    5d2d <barriered_work_ingest+0x3d>
      data->ingest_count++;
    5d1e:	48 83 87 60 01 00 00 01 	addq   $0x1,0x160(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5d26:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5d2d:	48 83 c0 10          	add    $0x10,%rax
    5d31:	48 39 d0             	cmp    %rdx,%rax
    5d34:	75 e2                	jne    5d18 <barriered_work_ingest+0x28>
  asm volatile ("sfence" ::: "memory");
    5d36:	0f ae f8             	sfence
  barriered_work(data);
    5d39:	e8 b2 fa ff ff       	call   57f0 <barriered_work>
}
    5d3e:	31 c0                	xor    %eax,%eax
    5d40:	48 83 c4 08          	add    $0x8,%rsp
    5d44:	c3                   	ret
    5d45:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005d50 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5d50:	f3 0f 1e fa          	endbr64
}
    5d54:	31 c0                	xor    %eax,%eax
    5d56:	c3                   	ret
    5d57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005d60 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5d60:	f3 0f 1e fa          	endbr64
    5d64:	31 c0                	xor    %eax,%eax
    5d66:	c3                   	ret
    5d67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005d70 <after>:
int after(struct timespec left, struct timespec right) {
    5d70:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5d74:	31 c0                	xor    %eax,%eax
    5d76:	48 39 d7             	cmp    %rdx,%rdi
    5d79:	7e 08                	jle    5d83 <after+0x13>
    5d7b:	31 c0                	xor    %eax,%eax
    5d7d:	48 39 ce             	cmp    %rcx,%rsi
    5d80:	0f 9f c0             	setg   %al
}
    5d83:	c3                   	ret
    5d84:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5d8f:	90                   	nop

0000000000005d90 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5d90:	f3 0f 1e fa          	endbr64
    5d94:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5d99:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5d9e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5da0:	48 39 d7             	cmp    %rdx,%rdi
    5da3:	7f 18                	jg     5dbd <within+0x2d>
    5da5:	4d 39 d8             	cmp    %r11,%r8
    5da8:	0f 9e c2             	setle  %dl
    5dab:	48 39 ce             	cmp    %rcx,%rsi
    5dae:	0f 9e c0             	setle  %al
    5db1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5db3:	31 c0                	xor    %eax,%eax
    5db5:	4d 39 d1             	cmp    %r10,%r9
    5db8:	0f 9e c0             	setle  %al
    5dbb:	21 d0                	and    %edx,%eax
}
    5dbd:	c3                   	ret
    5dbe:	66 90                	xchg   %ax,%ax

0000000000005dc0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5dc0:	f3 0f 1e fa          	endbr64
    5dc4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5dc9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5dce:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5dd3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5dd8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5ddd:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5de2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5de7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5dec:	48 39 fe             	cmp    %rdi,%rsi
    5def:	7d 2f                	jge    5e20 <overlap+0x60>
    5df1:	48 39 ca             	cmp    %rcx,%rdx
    5df4:	7d 62                	jge    5e58 <overlap+0x98>
    5df6:	4d 39 da             	cmp    %r11,%r10
    5df9:	7d 0e                	jge    5e09 <overlap+0x49>
    return 1;
    5dfb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e00:	4d 39 c1             	cmp    %r8,%r9
    5e03:	0f 8c 7f 00 00 00    	jl     5e88 <overlap+0xc8>
  return 0;
    5e09:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e0b:	4d 39 c1             	cmp    %r8,%r9
    5e0e:	7f 4c                	jg     5e5c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e10:	31 c0                	xor    %eax,%eax
    5e12:	4d 39 da             	cmp    %r11,%r10
    5e15:	0f 9e c0             	setle  %al
    5e18:	c3                   	ret
    5e19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5e20:	7e 4e                	jle    5e70 <overlap+0xb0>
    5e22:	48 39 ca             	cmp    %rcx,%rdx
    5e25:	7f 39                	jg     5e60 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e27:	75 31                	jne    5e5a <overlap+0x9a>
    5e29:	4d 39 c1             	cmp    %r8,%r9
    5e2c:	7c 2c                	jl     5e5a <overlap+0x9a>
    return 1;
    5e2e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e33:	4d 39 da             	cmp    %r11,%r10
    5e36:	7d 24                	jge    5e5c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e38:	48 39 ca             	cmp    %rcx,%rdx
    5e3b:	0f 94 c2             	sete   %dl
    5e3e:	48 39 fe             	cmp    %rdi,%rsi
    5e41:	0f 94 c0             	sete   %al
    5e44:	21 c2                	and    %eax,%edx
    5e46:	31 c0                	xor    %eax,%eax
    5e48:	4d 39 c1             	cmp    %r8,%r9
    5e4b:	0f 94 c0             	sete   %al
    5e4e:	21 d0                	and    %edx,%eax
    5e50:	c3                   	ret
    5e51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5e58:	74 af                	je     5e09 <overlap+0x49>
  return 0;
    5e5a:	31 c0                	xor    %eax,%eax
}
    5e5c:	c3                   	ret
    5e5d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5e60:	4d 39 da             	cmp    %r11,%r10
    5e63:	7e c4                	jle    5e29 <overlap+0x69>
    return 1;
    5e65:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e6a:	4d 39 c1             	cmp    %r8,%r9
    5e6d:	7e ba                	jle    5e29 <overlap+0x69>
    5e6f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e70:	48 39 ca             	cmp    %rcx,%rdx
    5e73:	7c 94                	jl     5e09 <overlap+0x49>
    5e75:	4d 39 c1             	cmp    %r8,%r9
    5e78:	7d b4                	jge    5e2e <overlap+0x6e>
    5e7a:	48 39 ca             	cmp    %rcx,%rdx
    5e7d:	74 91                	je     5e10 <overlap+0x50>
    5e7f:	eb d9                	jmp    5e5a <overlap+0x9a>
    5e81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5e88:	c3                   	ret
    5e89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005e90 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5e90:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5e94:	85 f6                	test   %esi,%esi
    5e96:	0f 8e 44 03 00 00    	jle    61e0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    5e9c:	41 57                	push   %r15
    5e9e:	41 89 f7             	mov    %esi,%r15d
    5ea1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5ea3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5ea6:	41 55                	push   %r13
    5ea8:	41 54                	push   %r12
    5eaa:	55                   	push   %rbp
    5eab:	53                   	push   %rbx
    5eac:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5eb0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5eb4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5eb9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5ebe:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    5ec1:	45 39 e6             	cmp    %r12d,%r14d
    5ec4:	0f 84 4e 02 00 00    	je     6118 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5eca:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5ecf:	8b 50 08             	mov    0x8(%rax),%edx
    5ed2:	85 d2                	test   %edx,%edx
    5ed4:	0f 8e 3e 02 00 00    	jle    6118 <verify+0x288>
    5eda:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    5edf:	31 c9                	xor    %ecx,%ecx
    5ee1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    5ee6:	31 c0                	xor    %eax,%eax
    5ee8:	44 89 f2             	mov    %r14d,%edx
    5eeb:	bf 01 00 00 00       	mov    $0x1,%edi
    5ef0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5ef5:	48 8d 35 24 13 00 00 	lea    0x1324(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    5efc:	e8 4f c5 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5f01:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5f06:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    5f0b:	8b 40 08             	mov    0x8(%rax),%eax
    5f0e:	85 c0                	test   %eax,%eax
    5f10:	0f 8e e6 01 00 00    	jle    60fc <verify+0x26c>
    5f16:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5f19:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    5f1e:	31 db                	xor    %ebx,%ebx
    5f20:	48 c1 e0 09          	shl    $0x9,%rax
    5f24:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    5f29:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5f2e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5f33:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    5f38:	4c 8b 20             	mov    (%rax),%r12
    5f3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5f40:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    5f45:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5f4a:	49 89 de             	mov    %rbx,%r14
    5f4d:	48 8d 35 e1 12 00 00 	lea    0x12e1(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5f54:	49 c1 e6 09          	shl    $0x9,%r14
    5f58:	bf 01 00 00 00       	mov    $0x1,%edi
    5f5d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5f61:	4b 8b 8c 3c 58 01 00 00 	mov    0x158(%r12,%r15,1),%rcx
    5f69:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    5f6e:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    5f76:	31 c0                	xor    %eax,%eax
    5f78:	e8 d3 c4 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5f7d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5f82:	4c 8b 20             	mov    (%rax),%r12
    5f85:	4b 83 bc 3c 58 01 00 00 00 	cmpq   $0x0,0x158(%r12,%r15,1)
    5f8e:	0f 8e 47 01 00 00    	jle    60db <verify+0x24b>
    5f94:	4c 03 75 00          	add    0x0(%rbp),%r14
    5f98:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5f9d:	ba 01 00 00 00       	mov    $0x1,%edx
    5fa2:	4d 89 f5             	mov    %r14,%r13
    5fa5:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    5fac:	4d 85 f6             	test   %r14,%r14
    5faf:	0f 8e 21 01 00 00    	jle    60d6 <verify+0x246>
    5fb5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5fb8:	48 89 d5             	mov    %rdx,%rbp
    5fbb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5fc0:	31 db                	xor    %ebx,%ebx
    5fc2:	4d 89 f2             	mov    %r14,%r10
    5fc5:	48 c1 e5 05          	shl    $0x5,%rbp
    5fc9:	48 83 ed 20          	sub    $0x20,%rbp
    5fcd:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    5fd1:	49 89 ee             	mov    %rbp,%r14
    5fd4:	48 89 dd             	mov    %rbx,%rbp
    5fd7:	48 89 d3             	mov    %rdx,%rbx
    5fda:	eb 31                	jmp    600d <verify+0x17d>
    5fdc:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5fe0:	4c 39 c2             	cmp    %r8,%rdx
    5fe3:	0f 8d 57 01 00 00    	jge    6140 <verify+0x2b0>
    5fe9:	4c 39 df             	cmp    %r11,%rdi
    5fec:	7e 05                	jle    5ff3 <verify+0x163>
    5fee:	49 39 c1             	cmp    %rax,%r9
    5ff1:	7c 75                	jl     6068 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ff3:	4c 39 df             	cmp    %r11,%rdi
    5ff6:	0f 8d ab 01 00 00    	jge    61a7 <verify+0x317>
    5ffc:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6000:	48 83 c5 01          	add    $0x1,%rbp
    6004:	49 39 ea             	cmp    %rbp,%r10
    6007:	0f 8e a9 00 00 00    	jle    60b6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    600d:	49 8b 97 48 01 00 00 	mov    0x148(%r15),%rdx
    6014:	48 89 e8             	mov    %rbp,%rax
    6017:	48 c1 e0 05          	shl    $0x5,%rax
    601b:	49 03 85 48 01 00 00 	add    0x148(%r13),%rax
    6022:	4c 01 f2             	add    %r14,%rdx
    6025:	48 8b 08             	mov    (%rax),%rcx
    6028:	48 8b 78 10          	mov    0x10(%rax),%rdi
    602c:	48 8b 32             	mov    (%rdx),%rsi
    602f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6033:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6037:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    603b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    603f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6043:	48 39 f1             	cmp    %rsi,%rcx
    6046:	7c 98                	jl     5fe0 <verify+0x150>
    6048:	0f 8e 42 01 00 00    	jle    6190 <verify+0x300>
    604e:	4c 39 c2             	cmp    %r8,%rdx
    6051:	0f 8f f9 00 00 00    	jg     6150 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6057:	75 a7                	jne    6000 <verify+0x170>
    6059:	4c 39 df             	cmp    %r11,%rdi
    605c:	7f a2                	jg     6000 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    605e:	49 39 c1             	cmp    %rax,%r9
    6061:	7c 9d                	jl     6000 <verify+0x170>
    6063:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6068:	49 89 c1             	mov    %rax,%r9
    606b:	48 89 f9             	mov    %rdi,%rcx
    606e:	48 89 f2             	mov    %rsi,%rdx
    6071:	bf 01 00 00 00       	mov    $0x1,%edi
    6076:	48 8d 35 0b 14 00 00 	lea    0x140b(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    607d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    607f:	48 83 c5 01          	add    $0x1,%rbp
    6083:	e8 c8 c3 ff ff       	call   2450 <__printf_chk@plt>
    6088:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    608d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    6092:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6095:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    609a:	4d 8b 95 58 01 00 00 	mov    0x158(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60a1:	4c 8b 20             	mov    (%rax),%r12
    60a4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    60a9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60ad:	49 39 ea             	cmp    %rbp,%r10
    60b0:	0f 8f 57 ff ff ff    	jg     600d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60b6:	48 89 da             	mov    %rbx,%rdx
    60b9:	49 3b 9f 58 01 00 00 	cmp    0x158(%r15),%rbx
    60c0:	7d 14                	jge    60d6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60c2:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    60c9:	48 83 c2 01          	add    $0x1,%rdx
    60cd:	4d 85 f6             	test   %r14,%r14
    60d0:	0f 8f e2 fe ff ff    	jg     5fb8 <verify+0x128>
    60d6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    60db:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    60e0:	48 83 c3 01          	add    $0x1,%rbx
    60e4:	39 58 08             	cmp    %ebx,0x8(%rax)
    60e7:	0f 8f 53 fe ff ff    	jg     5f40 <verify+0xb0>
    60ed:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    60f2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    60f7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    60fc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6101:	48 83 c1 01          	add    $0x1,%rcx
    6105:	39 48 08             	cmp    %ecx,0x8(%rax)
    6108:	0f 8f d8 fd ff ff    	jg     5ee6 <verify+0x56>
    610e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6113:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6118:	48 81 44 24 10 b0 00 00 00 	addq   $0xb0,0x10(%rsp)
    6121:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6126:	41 39 c7             	cmp    %eax,%r15d
    6129:	0f 84 86 00 00 00    	je     61b5 <verify+0x325>
    612f:	41 89 c4             	mov    %eax,%r12d
    6132:	e9 8a fd ff ff       	jmp    5ec1 <verify+0x31>
    6137:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6140:	0f 85 ba fe ff ff    	jne    6000 <verify+0x170>
    6146:	e9 a8 fe ff ff       	jmp    5ff3 <verify+0x163>
    614b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6150:	49 39 c1             	cmp    %rax,%r9
    6153:	7e 09                	jle    615e <verify+0x2ce>
    6155:	4c 39 df             	cmp    %r11,%rdi
    6158:	0f 8c 0a ff ff ff    	jl     6068 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    615e:	4c 39 df             	cmp    %r11,%rdi
    6161:	0f 8f 99 fe ff ff    	jg     6000 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6167:	49 39 c1             	cmp    %rax,%r9
    616a:	0f 8d f8 fe ff ff    	jge    6068 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6170:	48 39 f1             	cmp    %rsi,%rcx
    6173:	0f 85 87 fe ff ff    	jne    6000 <verify+0x170>
    6179:	4c 39 c2             	cmp    %r8,%rdx
    617c:	0f 85 7e fe ff ff    	jne    6000 <verify+0x170>
    6182:	4c 39 df             	cmp    %r11,%rdi
    6185:	0f 84 dd fe ff ff    	je     6068 <verify+0x1d8>
    618b:	e9 70 fe ff ff       	jmp    6000 <verify+0x170>
    6190:	4c 39 c2             	cmp    %r8,%rdx
    6193:	0f 8c 5a fe ff ff    	jl     5ff3 <verify+0x163>
    6199:	4c 39 df             	cmp    %r11,%rdi
    619c:	7e c9                	jle    6167 <verify+0x2d7>
    619e:	4c 39 c2             	cmp    %r8,%rdx
    61a1:	0f 85 59 fe ff ff    	jne    6000 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    61a7:	49 39 c1             	cmp    %rax,%r9
    61aa:	0f 8f 50 fe ff ff    	jg     6000 <verify+0x170>
    61b0:	e9 b3 fe ff ff       	jmp    6068 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    61b5:	48 81 44 24 18 b0 00 00 00 	addq   $0xb0,0x18(%rsp)
    61be:	41 8d 46 01          	lea    0x1(%r14),%eax
    61c2:	45 39 e6             	cmp    %r12d,%r14d
    61c5:	74 08                	je     61cf <verify+0x33f>
    61c7:	41 89 c6             	mov    %eax,%r14d
    61ca:	e9 ea fc ff ff       	jmp    5eb9 <verify+0x29>
}
    61cf:	48 83 c4 58          	add    $0x58,%rsp
    61d3:	31 c0                	xor    %eax,%eax
    61d5:	5b                   	pop    %rbx
    61d6:	5d                   	pop    %rbp
    61d7:	41 5c                	pop    %r12
    61d9:	41 5d                	pop    %r13
    61db:	41 5e                	pop    %r14
    61dd:	41 5f                	pop    %r15
    61df:	c3                   	ret
    61e0:	31 c0                	xor    %eax,%eax
    61e2:	c3                   	ret

Disassembly of section .fini:

00000000000061e4 <_fini>:
    61e4:	f3 0f 1e fa          	endbr64
    61e8:	48 83 ec 08          	sub    $0x8,%rsp
    61ec:	48 83 c4 08          	add    $0x8,%rsp
    61f0:	c3                   	ret
