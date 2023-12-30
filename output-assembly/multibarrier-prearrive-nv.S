
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
    2605:	48 83 ec 78          	sub    $0x78,%rsp
    2609:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2612:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    2617:	48 8d 05 b2 10 00 00 	lea    0x10b2(%rip),%rax        # 36d0 <barriered_reset>
    261e:	66 48 0f 6e e8       	movq   %rax,%xmm5
    2623:	0f 16 2d 4e 76 00 00 	movhps 0x764e(%rip),%xmm5        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    262a:	0f 29 6c 24 30       	movaps %xmm5,0x30(%rsp)
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
    26c7:	48 8d 35 4a 4e 00 00 	lea    0x4e4a(%rip),%rsi        # 7518 <_IO_stdin_used+0x518>
    26ce:	31 c0                	xor    %eax,%eax
    26d0:	bf 01 00 00 00       	mov    $0x1,%edi
    26d5:	e8 76 fd ff ff       	call   2450 <__printf_chk@plt>
    26da:	ba 01 00 00 00       	mov    $0x1,%edx
    26df:	48 8d 35 62 4e 00 00 	lea    0x4e62(%rip),%rsi        # 7548 <_IO_stdin_used+0x548>
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
    2747:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
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
    275b:	48 89 04 24          	mov    %rax,(%rsp)
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    275f:	e8 3c fc ff ff       	call   23a0 <calloc@plt>
    2764:	4c 8b 34 24          	mov    (%rsp),%r14
    2768:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    276d:	49 89 c5             	mov    %rax,%r13
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    2770:	48 8d 68 40          	lea    0x40(%rax),%rbp
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2774:	49 89 c4             	mov    %rax,%r12
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2777:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    277c:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2784:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2789:	49 83 c4 10          	add    $0x10,%r12
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    278d:	e8 0e fc ff ff       	call   23a0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2792:	be 20 00 00 00       	mov    $0x20,%esi
    2797:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    279c:	49 89 44 24 f8       	mov    %rax,-0x8(%r12)
    27a1:	48 89 c3             	mov    %rax,%rbx
      buffers[x].buffer[y].available = 0;
    27a4:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    27ae:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    27b8:	e8 e3 fb ff ff       	call   23a0 <calloc@plt>
    27bd:	48 89 83 88 00 00 00 	mov    %rax,0x88(%rbx)
  for (int x = 0 ; x < buffers_required; x++) {
    27c4:	4c 39 e5             	cmp    %r12,%rbp
    27c7:	75 ae                	jne    2777 <main+0x187>
    27c9:	4d 89 f2             	mov    %r14,%r10
    27cc:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    27d1:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
    }
  }
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
    27d6:	c7 44 24 40 00 00 00 00 	movl   $0x0,0x40(%rsp)
        thread_data[x].tasks[y].snapshot_count = 99;
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
        thread_data[x].tasks[y].current_snapshot = 0;
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
        thread_data[x].tasks[y].thread = &thread_data[x]; 
        thread_data[x].tasks[y].available = 1;
    27de:	4d 89 d5             	mov    %r10,%r13
    27e1:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    27e6:	4c 8d 70 e8          	lea    -0x18(%rax),%r14
  int cur_buffer = 0;
    27ea:	31 c0                	xor    %eax,%eax
        thread_data[x].tasks[y].available = 1;
    27ec:	4c 89 f5             	mov    %r14,%rbp
    27ef:	41 89 c6             	mov    %eax,%r14d
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27f2:	be 08 00 00 00       	mov    $0x8,%esi
    27f7:	bf 02 00 00 00       	mov    $0x2,%edi
    27fc:	e8 9f fb ff ff       	call   23a0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2801:	be 80 00 00 00       	mov    $0x80,%esi
    2806:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    280b:	48 89 c3             	mov    %rax,%rbx
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    280e:	e8 8d fb ff ff       	call   23a0 <calloc@plt>
    2813:	44 89 34 24          	mov    %r14d,(%rsp)
    2817:	44 89 f2             	mov    %r14d,%edx
    281a:	49 89 c4             	mov    %rax,%r12
    if (x % 2 == 1) {
    281d:	44 89 f0             	mov    %r14d,%eax
      other = (x + 1) % total_threads;
    2820:	41 83 c6 01          	add    $0x1,%r14d
    if (x % 2 == 1) {
    2824:	83 e0 01             	and    $0x1,%eax
    2827:	85 c0                	test   %eax,%eax
    2829:	0f 84 b3 07 00 00    	je     2fe2 <main+0x9f2>
      my_thread_data[0] = &thread_data[other]; 
    282f:	49 8d 8d 50 ff ff ff 	lea    -0xb0(%r13),%rcx
      my_thread_data[1] = &thread_data[x]; 
    2836:	4c 89 6b 08          	mov    %r13,0x8(%rbx)
    283a:	4d 89 e8             	mov    %r13,%r8
    283d:	31 c0                	xor    %eax,%eax
      my_thread_data[0] = &thread_data[other]; 
    283f:	48 89 0b             	mov    %rcx,(%rbx)
    2842:	48 8d 35 b2 4a 00 00 	lea    0x4ab2(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
    2849:	bf 01 00 00 00       	mov    $0x1,%edi
      other = abs(x - 1) % total_threads;
    284e:	44 8d 7a ff          	lea    -0x1(%rdx),%r15d
      thread_data[x].thread_index = 1;
    2852:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    285a:	e8 f1 fb ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    285f:	48 8d 45 18          	lea    0x18(%rbp),%rax
    2863:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2868:	49 89 6d 38          	mov    %rbp,0x38(%r13)
    286c:	8b 2c 24             	mov    (%rsp),%ebp
    286f:	44 89 f9             	mov    %r15d,%ecx
    2872:	bf 01 00 00 00       	mov    $0x1,%edi
    2877:	45 8b 45 00          	mov    0x0(%r13),%r8d
    287b:	48 8d 35 ee 4c 00 00 	lea    0x4cee(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    2882:	31 c0                	xor    %eax,%eax
    2884:	89 ea                	mov    %ebp,%edx
    2886:	e8 c5 fb ff ff       	call   2450 <__printf_chk@plt>
    thread_data[x].other = other;
    288b:	45 89 bd a8 00 00 00 	mov    %r15d,0xa8(%r13)
    2892:	31 c0                	xor    %eax,%eax
    2894:	89 ea                	mov    %ebp,%edx
    2896:	8b 4c 24 40          	mov    0x40(%rsp),%ecx
    289a:	48 8d 35 ff 4c 00 00 	lea    0x4cff(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    28a1:	bf 01 00 00 00       	mov    $0x1,%edi
    28a6:	e8 a5 fb ff ff       	call   2450 <__printf_chk@plt>
      if (x < thread_count) {
    28ab:	83 fd 01             	cmp    $0x1,%ebp
    28ae:	0f 86 9a 07 00 00    	jbe    304e <main+0xa5e>
          CPU_SET(j, sendercpu);
    28b4:	49 81 0c 24 ff 0f 00 00 	orq    $0xfff,(%r12)
    thread_data[x].real_thread_index = x;
    28bc:	8b 04 24             	mov    (%rsp),%eax
    thread_data[x].threads = my_thread_data;
    28bf:	49 89 5d 10          	mov    %rbx,0x10(%r13)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28c3:	be 10 00 00 00       	mov    $0x10,%esi
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28c8:	31 ed                	xor    %ebp,%ebp
    thread_data[x].cpu_set = sendercpu;
    28ca:	4d 89 a5 a0 00 00 00 	mov    %r12,0xa0(%r13)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28d1:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].real_thread_index = x;
    28d6:	41 89 45 04          	mov    %eax,0x4(%r13)
    thread_data[x].thread_count = 2;
    28da:	48 8b 05 9f 51 00 00 	mov    0x519f(%rip),%rax        # 7a80 <_IO_stdin_used+0xa80>
    thread_data[x].task_count = total_barrier_count;
    28e1:	41 c7 45 30 03 00 00 00 	movl   $0x3,0x30(%r13)
    thread_data[x].thread_count = 2;
    28e9:	49 89 45 18          	mov    %rax,0x18(%r13)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28ed:	e8 ae fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28f2:	be 10 00 00 00       	mov    $0x10,%esi
    28f7:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28fc:	49 89 45 58          	mov    %rax,0x58(%r13)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2900:	e8 9b fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2905:	be 28 00 00 00       	mov    $0x28,%esi
    290a:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    290f:	66 0f 6f 1d 49 51 00 00 	movdqa 0x5149(%rip),%xmm3        # 7a60 <_IO_stdin_used+0xa60>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2917:	49 89 45 60          	mov    %rax,0x60(%r13)
    thread_data[x].timestamp_count = 0;
    291b:	41 0f 11 5d 70       	movups %xmm3,0x70(%r13)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2920:	e8 7b fa ff ff       	call   23a0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2925:	be 00 02 00 00       	mov    $0x200,%esi
    292a:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
    292f:	66 0f 6f 25 29 51 00 00 	movdqa 0x5129(%rip),%xmm4        # 7a60 <_IO_stdin_used+0xa60>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2937:	49 89 85 80 00 00 00 	mov    %rax,0x80(%r13)
    thread_data[x].task_timestamp_count = 0;
    293e:	41 0f 11 a5 88 00 00 00 	movups %xmm4,0x88(%r13)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2946:	e8 55 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    294b:	44 89 74 24 20       	mov    %r14d,0x20(%rsp)
      thread_data[x].tasks = barriers;
    2950:	49 89 45 28          	mov    %rax,0x28(%r13)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2954:	49 89 c4             	mov    %rax,%r12
        thread_data[x].tasks[y].protected = do_protected_write; 
    2957:	4c 63 fd             	movslq %ebp,%r15
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    295a:	be 20 00 00 00       	mov    $0x20,%esi
    295f:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    2964:	4c 89 fb             	mov    %r15,%rbx
    2967:	48 8d 05 22 0d 00 00 	lea    0xd22(%rip),%rax        # 3690 <do_protected_write>
    296e:	48 c1 e3 09          	shl    $0x9,%rbx
    2972:	49 01 dc             	add    %rbx,%r12
    2975:	49 89 84 24 20 01 00 00 	mov    %rax,0x120(%r12)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    297d:	e8 1e fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    2982:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    2987:	89 6c 24 10          	mov    %ebp,0x10(%rsp)
    298b:	49 89 c6             	mov    %rax,%r14
    298e:	49 89 84 24 68 01 00 00 	mov    %rax,0x168(%r12)
        for (int b = 0 ; b < 2 ; b++) {
    2996:	4c 8d 60 40          	lea    0x40(%rax),%r12
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    299a:	be 08 00 00 00       	mov    $0x8,%esi
    299f:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    29a4:	49 83 c6 20          	add    $0x20,%r14
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29a8:	e8 f3 f9 ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29ad:	be 08 00 00 00       	mov    $0x8,%esi
    29b2:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29b7:	48 89 c5             	mov    %rax,%rbp
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29ba:	e8 e1 f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29bf:	be 18 00 00 00       	mov    $0x18,%esi
    29c4:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29c9:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29cc:	e8 cf f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    29d1:	66 0f 6f 05 97 50 00 00 	movdqa 0x5097(%rip),%xmm0        # 7a70 <_IO_stdin_used+0xa70>
          mailboxes[b].higher = &data[1];
    29d9:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29dd:	49 89 46 e0          	mov    %rax,-0x20(%r14)
          mailboxes[b].higher = &data[1];
    29e1:	49 89 76 e8          	mov    %rsi,-0x18(%r14)
          data[0].messages = messages;
    29e5:	48 89 28             	mov    %rbp,(%rax)
          data[1].messages = messages2;
    29e8:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    29ec:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    29f0:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    29f4:	4d 39 f4             	cmp    %r14,%r12
    29f7:	75 a1                	jne    299a <main+0x3aa>
        char *message = malloc(sizeof(char) * 256);
    29f9:	be 01 00 00 00       	mov    $0x1,%esi
    29fe:	bf 00 01 00 00       	mov    $0x100,%edi
    2a03:	8b 6c 24 10          	mov    0x10(%rsp),%ebp
    2a07:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    2a0c:	e8 8f f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a11:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a16:	49 89 c4             	mov    %rax,%r12
        struct Message *messaged = malloc(sizeof(struct Message));
    2a19:	e8 f2 f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a1e:	44 8b 04 24          	mov    (%rsp),%r8d
    2a22:	4c 89 e7             	mov    %r12,%rdi
    2a25:	41 89 e9             	mov    %ebp,%r9d
    2a28:	49 89 c6             	mov    %rax,%r14
    2a2b:	48 8d 0d 8e 4b 00 00 	lea    0x4b8e(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a32:	ba 00 01 00 00       	mov    $0x100,%edx
    2a37:	31 c0                	xor    %eax,%eax
    2a39:	be 01 00 00 00       	mov    $0x1,%esi
    2a3e:	e8 dd fa ff ff       	call   2520 <__sprintf_chk@plt>
        messaged->thread_index = thread_data[x].thread_index;
    2a43:	49 63 45 00          	movslq 0x0(%r13),%rax
        messaged->message = message;
    2a47:	4d 89 26             	mov    %r12,(%r14)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a4a:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a4f:	4d 8b 65 28          	mov    0x28(%r13),%r12
        messaged->task_index = y;
    2a53:	4d 89 7e 10          	mov    %r15,0x10(%r14)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a57:	be 20 00 00 00       	mov    $0x20,%esi
        messaged->thread_index = thread_data[x].thread_index;
    2a5c:	49 89 46 08          	mov    %rax,0x8(%r14)
    2a60:	49 89 c7             	mov    %rax,%r15
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a63:	8d 45 01             	lea    0x1(%rbp),%eax
    2a66:	4c 01 e3             	add    %r12,%rbx
    2a69:	83 e0 01             	and    $0x1,%eax
    2a6c:	89 83 88 01 00 00    	mov    %eax,0x188(%rbx)
        thread_data[x].tasks[y].message = messaged;
    2a72:	4c 89 b3 80 01 00 00 	mov    %r14,0x180(%rbx)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a79:	48 c7 83 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%rbx)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a84:	e8 17 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a89:	44 89 bb 30 01 00 00 	mov    %r15d,0x130(%rbx)
        thread_data[x].tasks[y].sending = 1;
    2a90:	48 bf 01 00 00 00 02 00 00 00 	movabs $0x200000001,%rdi
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a9a:	48 89 83 48 01 00 00 	mov    %rax,0x148(%rbx)
        thread_data[x].tasks[y].available = 1;
    2aa1:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2aab:	48 c7 83 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%rbx)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2ab6:	4c 89 ab 28 01 00 00 	mov    %r13,0x128(%rbx)
        thread_data[x].tasks[y].arrived = 0;
    2abd:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
        thread_data[x].tasks[y].thread_count = 2;
    2ac7:	c7 83 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%rbx)
        thread_data[x].tasks[y].available = 1;
    2ad1:	48 89 83 38 01 00 00 	mov    %rax,0x138(%rbx)
        thread_data[x].tasks[y].sending = 1;
    2ad8:	48 89 bb 78 01 00 00 	mov    %rdi,0x178(%rbx)
        thread_data[x].tasks[y].task_count = total_barrier_count;
        thread_data[x].tasks[y].worker_count = thread_count;
        thread_data[x].tasks[y].task_index = y;
    2adf:	89 2b                	mov    %ebp,(%rbx)
        if (y == barrier_count - 1) {
    2ae1:	83 fd 01             	cmp    $0x1,%ebp
    2ae4:	0f 84 ea 04 00 00    	je     2fd4 <main+0x9e4>
            thread_data[x].tasks[y].run = barriered_nulltask; 
          }
          */
          thread_data[x].tasks[y].run = barriered_work; 
        } else {
          if (y == 0) {
    2aea:	85 ed                	test   %ebp,%ebp
    2aec:	0f 84 ca 04 00 00    	je     2fbc <main+0x9cc>
            // printf("Thread %d is an ingest thread\n", x);
            thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
            assigned = 1;
           } else {
             thread_data[x].tasks[y].run = barriered_work; 
    2af2:	48 8d 3d 97 2b 00 00 	lea    0x2b97(%rip),%rdi        # 5690 <barriered_work>
           }
        }
      }
			thread_data[x].buffers_count = buffers_per_thread;
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2af9:	be 08 00 00 00       	mov    $0x8,%esi
             thread_data[x].tasks[y].run = barriered_work; 
    2afe:	44 8b 74 24 20       	mov    0x20(%rsp),%r14d
    2b03:	48 89 bb 18 01 00 00 	mov    %rdi,0x118(%rbx)
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2b0a:	bf 01 00 00 00       	mov    $0x1,%edi
			thread_data[x].buffers_count = buffers_per_thread;
    2b0f:	41 c7 85 ac 00 00 00 01 00 00 00 	movl   $0x1,0xac(%r13)
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2b1a:	e8 81 f8 ff ff       	call   23a0 <calloc@plt>
      for (int b = 0 ; b < buffers_per_thread; b++) {	
        thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2b1f:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
      }
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b24:	66 0f 6f 54 24 30    	movdqa 0x30(%rsp),%xmm2
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2b2a:	49 89 45 40          	mov    %rax,0x40(%r13)
  for (int x = 0 ; x < total_threads ; x++) {
    2b2e:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
        thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2b33:	48 89 38             	mov    %rdi,(%rax)
  for (int x = 0 ; x < total_threads ; x++) {
    2b36:	48 83 c7 10          	add    $0x10,%rdi
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
    2b3a:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2b44:	4d 89 ac 24 28 05 00 00 	mov    %r13,0x528(%r12)
  for (int x = 0 ; x < total_threads ; x++) {
    2b4c:	49 81 c5 b0 00 00 00 	add    $0xb0,%r13
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2b53:	41 c7 84 24 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r12)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2b5f:	41 c7 84 24 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%r12)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2b6b:	45 89 bc 24 30 05 00 00 	mov    %r15d,0x530(%r12)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2b73:	41 c7 84 24 7c 05 00 00 02 00 00 00 	movl   $0x2,0x57c(%r12)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b7f:	41 c7 84 24 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r12)
      thread_data[x].tasks[barrier_count].available = 1; 
    2b8b:	49 89 84 24 38 05 00 00 	mov    %rax,0x538(%r12)
  for (int x = 0 ; x < total_threads ; x++) {
    2b93:	48 89 7c 24 18       	mov    %rdi,0x18(%rsp)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b98:	41 0f 11 94 24 18 05 00 00 	movups %xmm2,0x518(%r12)
  for (int x = 0 ; x < total_threads ; x++) {
    2ba1:	41 83 fe 06          	cmp    $0x6,%r14d
    2ba5:	0f 85 47 fc ff ff    	jne    27f2 <main+0x202>
    2bab:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2bb0:	ba 03 00 00 00       	mov    $0x3,%edx
    2bb5:	48 8d 35 5c 47 00 00 	lea    0x475c(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2bbc:	31 c0                	xor    %eax,%eax
    2bbe:	bf 01 00 00 00       	mov    $0x1,%edi
    2bc3:	4c 89 14 24          	mov    %r10,(%rsp)
    2bc7:	e8 84 f8 ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2bcc:	be 08 00 00 00       	mov    $0x8,%esi
    2bd1:	bf 02 00 00 00       	mov    $0x2,%edi
    2bd6:	e8 c5 f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2bdb:	4c 8b 14 24          	mov    (%rsp),%r10
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bdf:	be 38 00 00 00       	mov    $0x38,%esi
    2be4:	bf 06 00 00 00       	mov    $0x6,%edi
    my_thread_data[0] = &thread_data[x]; 
    2be9:	49 8d aa 10 02 00 00 	lea    0x210(%r10),%rbp
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2bf0:	4c 89 50 08          	mov    %r10,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2bf4:	4d 8d a2 b0 00 00 00 	lea    0xb0(%r10),%r12
    thread_data[x].threads = my_thread_data;
    2bfb:	49 89 82 20 02 00 00 	mov    %rax,0x220(%r10)
    my_thread_data[0] = &thread_data[x]; 
    2c02:	48 89 28             	mov    %rbp,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c05:	49 8b 42 28          	mov    0x28(%r10),%rax
    thread_data[x].thread_count = 2;
    2c09:	41 c7 82 28 02 00 00 02 00 00 00 	movl   $0x2,0x228(%r10)
    thread_data[x].thread_index = 0;
    2c14:	41 c7 82 10 02 00 00 00 00 00 00 	movl   $0x0,0x210(%r10)
    thread_data[x].task_count = total_barrier_count;
    2c1f:	41 c7 82 40 02 00 00 03 00 00 00 	movl   $0x3,0x240(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2c2a:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2c34:	49 8b 82 d8 00 00 00 	mov    0xd8(%r10),%rax
    2c3b:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    2c40:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c4a:	e8 51 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c4f:	be 38 00 00 00       	mov    $0x38,%esi
    2c54:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c59:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c5c:	e8 3f f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c61:	be 38 00 00 00       	mov    $0x38,%esi
    2c66:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c6b:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c6e:	e8 2d f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c73:	be 38 00 00 00       	mov    $0x38,%esi
    2c78:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c7d:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c81:	e8 1a f7 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2c86:	be 08 00 00 00       	mov    $0x8,%esi
    2c8b:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c90:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2c95:	e8 06 f7 ff ff       	call   23a0 <calloc@plt>

  thread_data[thread_count].type = TIMER;
    2c9a:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2c9f:	be 08 00 00 00       	mov    $0x8,%esi
    2ca4:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2ca9:	48 89 c3             	mov    %rax,%rbx
  thread_data[thread_count].task_count = total_barrier_count;
    2cac:	48 8b 05 d5 4d 00 00 	mov    0x4dd5(%rip),%rax        # 7a88 <_IO_stdin_used+0xa88>
  thread_data[thread_count].type = TIMER;
    2cb3:	41 c7 82 68 01 00 00 00 00 00 00 	movl   $0x0,0x168(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2cbe:	49 89 82 90 01 00 00 	mov    %rax,0x190(%r10)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2cc5:	e8 d6 f6 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2cca:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2ccf:	bf 01 00 00 00       	mov    $0x1,%edi
    2cd4:	48 8d 35 4c 46 00 00 	lea    0x464c(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2cdb:	48 89 68 18          	mov    %rbp,0x18(%rax)
    2cdf:	49 8d 8a 60 01 00 00 	lea    0x160(%r10),%rcx
    2ce6:	4d 8d ba c0 02 00 00 	lea    0x2c0(%r10),%r15
    2ced:	4c 89 10             	mov    %r10,(%rax)
    2cf0:	49 8d 92 70 03 00 00 	lea    0x370(%r10),%rdx
  }
  thread_data[thread_count].threads = my_thread_data;
    2cf7:	49 89 82 70 01 00 00 	mov    %rax,0x170(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2cfe:	48 89 48 10          	mov    %rcx,0x10(%rax)
    2d02:	4c 89 78 20          	mov    %r15,0x20(%rax)
    2d06:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2d0a:	ba 02 00 00 00       	mov    $0x2,%edx
  thread_data[thread_count].thread_count = thread_count;
    2d0f:	41 c7 82 78 01 00 00 02 00 00 00 	movl   $0x2,0x178(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2d1a:	41 c7 82 80 01 00 00 02 00 00 00 	movl   $0x2,0x180(%r10)
  thread_data[thread_count].thread_index = 0;
    2d25:	41 c7 82 60 01 00 00 00 00 00 00 	movl   $0x0,0x160(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2d30:	4c 89 60 08          	mov    %r12,0x8(%rax)
    2d34:	31 c0                	xor    %eax,%eax
    2d36:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    2d3b:	e8 10 f7 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2d40:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    2d45:	49 8d 75 70          	lea    0x70(%r13),%rsi
    2d49:	48 8d 7b 10          	lea    0x10(%rbx),%rdi
    2d4d:	48 8d 15 fc 0a 00 00 	lea    0xafc(%rip),%rdx        # 3850 <timer_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    thread_data[x].type = WORKER;
    thread_data[x].running = 1;
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2d54:	4c 8d 2d 55 25 00 00 	lea    0x2555(%rip),%r13        # 52b0 <barriered_thread>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2d5b:	e8 10 f7 ff ff       	call   2470 <pthread_create@plt>
    thread_data[x].type = WORKER;
    2d60:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2d65:	31 d2                	xor    %edx,%edx
    2d67:	31 c0                	xor    %eax,%eax
    2d69:	4c 8d 0d 78 48 00 00 	lea    0x4878(%rip),%r9        # 75e8 <_IO_stdin_used+0x5e8>
    2d70:	bf 01 00 00 00       	mov    $0x1,%edi
    2d75:	41 c7 42 08 01 00 00 00 	movl   $0x1,0x8(%r10)
    2d7d:	4c 89 ce             	mov    %r9,%rsi
    thread_data[x].running = 1;
    2d80:	41 c7 42 34 01 00 00 00 	movl   $0x1,0x34(%r10)
    2d88:	e8 c3 f6 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2d8d:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2d92:	4c 89 ea             	mov    %r13,%rdx
    2d95:	4c 89 f6             	mov    %r14,%rsi
    2d98:	48 89 df             	mov    %rbx,%rdi
    2d9b:	e8 d0 f6 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2da0:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2da5:	48 8b 3b             	mov    (%rbx),%rdi
    2da8:	be 08 00 00 00       	mov    $0x8,%esi
    2dad:	49 8b 92 a0 00 00 00 	mov    0xa0(%r10),%rdx
    2db4:	e8 27 f5 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    thread_data[x].type = WORKER;
    2db9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2dbe:	ba 01 00 00 00       	mov    $0x1,%edx
    2dc3:	31 c0                	xor    %eax,%eax
    2dc5:	4c 8d 0d 1c 48 00 00 	lea    0x481c(%rip),%r9        # 75e8 <_IO_stdin_used+0x5e8>
    2dcc:	bf 01 00 00 00       	mov    $0x1,%edi
    2dd1:	41 c7 82 b8 00 00 00 01 00 00 00 	movl   $0x1,0xb8(%r10)
    2ddc:	4c 89 ce             	mov    %r9,%rsi
    thread_data[x].running = 1;
    2ddf:	41 c7 82 e4 00 00 00 01 00 00 00 	movl   $0x1,0xe4(%r10)
    2dea:	e8 61 f6 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2def:	4c 89 e1             	mov    %r12,%rcx
    2df2:	49 8d 76 38          	lea    0x38(%r14),%rsi
    2df6:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    2dfa:	4c 89 ea             	mov    %r13,%rdx
    2dfd:	4c 8d 6b 20          	lea    0x20(%rbx),%r13
    2e01:	4d 89 fe             	mov    %r15,%r14
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2e04:	41 bf 04 00 00 00    	mov    $0x4,%r15d
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2e0a:	e8 61 f6 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2e0f:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2e14:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    2e18:	be 08 00 00 00       	mov    $0x8,%esi
    2e1d:	49 8b 92 50 01 00 00 	mov    0x150(%r10),%rdx
    2e24:	e8 b7 f4 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    thread_data[x].type = IO;
    2e29:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e2e:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].task_count = 0;
    2e33:	48 8b 3d 56 4c 00 00 	mov    0x4c56(%rip),%rdi        # 7a90 <_IO_stdin_used+0xa90>
    thread_data[x].type = IO;
    2e3a:	41 c7 82 18 02 00 00 02 00 00 00 	movl   $0x2,0x218(%r10)
    thread_data[x].task_count = 0;
    2e45:	49 89 ba 40 02 00 00 	mov    %rdi,0x240(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e4c:	bf 01 00 00 00       	mov    $0x1,%edi
    2e51:	e8 4a f5 ff ff       	call   23a0 <calloc@plt>
    2e56:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e5b:	be 00 08 00 00       	mov    $0x800,%esi
    2e60:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e62:	49 89 82 58 02 00 00 	mov    %rax,0x258(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e69:	e8 42 f6 ff ff       	call   24b0 <eventfd@plt>
    2e6e:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2e73:	be 08 00 00 00       	mov    $0x8,%esi
    2e78:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e7d:	41 89 82 60 02 00 00 	mov    %eax,0x260(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2e84:	e8 17 f5 ff ff       	call   23a0 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
    2e89:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2e8e:	ba 03 00 00 00       	mov    $0x3,%edx
    2e93:	48 8d 35 ab 44 00 00 	lea    0x44ab(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    2e9a:	4c 89 60 08          	mov    %r12,0x8(%rax)
    2e9e:	bf 01 00 00 00       	mov    $0x1,%edi
    2ea3:	4c 89 10             	mov    %r10,(%rax)
    thread_data[x].threads = my_thread_data;
    2ea6:	49 89 82 20 02 00 00 	mov    %rax,0x220(%r10)
    2ead:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_count = thread_count;
    2eaf:	41 c7 82 28 02 00 00 02 00 00 00 	movl   $0x2,0x228(%r10)
    thread_data[x].thread_index = x;
    2eba:	41 c7 82 10 02 00 00 03 00 00 00 	movl   $0x3,0x210(%r10)
    2ec5:	e8 86 f5 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2eca:	48 8b 34 24          	mov    (%rsp),%rsi
    2ece:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    2ed2:	48 89 e9             	mov    %rbp,%rcx
    2ed5:	48 8d 15 e4 1b 00 00 	lea    0x1be4(%rip),%rdx        # 4ac0 <io_thread>
    2edc:	48 81 c6 a8 00 00 00 	add    $0xa8,%rsi
    2ee3:	e8 88 f5 ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2ee8:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    2eed:	48 89 1c 24          	mov    %rbx,(%rsp)
    2ef1:	4c 89 eb             	mov    %r13,%rbx
    2ef4:	48 81 c5 e0 00 00 00 	add    $0xe0,%rbp
    2efb:	49 89 ed             	mov    %rbp,%r13
    2efe:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    2f03:	44 89 fa             	mov    %r15d,%edx
    2f06:	48 8d 35 4f 44 00 00 	lea    0x444f(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    2f0d:	bf 01 00 00 00       	mov    $0x1,%edi
    2f12:	31 c0                	xor    %eax,%eax
    2f14:	e8 37 f5 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    2f19:	be 08 00 00 00       	mov    $0x8,%esi
    2f1e:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    2f23:	48 8b 05 66 4b 00 00 	mov    0x4b66(%rip),%rax        # 7a90 <_IO_stdin_used+0xa90>
    thread_data[x].type = EXTERNAL;
    2f2a:	41 c7 46 08 03 00 00 00 	movl   $0x3,0x8(%r14)
    thread_data[x].task_count = 0;
    2f32:	49 89 46 30          	mov    %rax,0x30(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    2f36:	e8 65 f4 ff ff       	call   23a0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    2f3b:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f40:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    2f45:	41 c7 86 ac 00 00 00 01 00 00 00 	movl   $0x1,0xac(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    2f50:	49 89 46 40          	mov    %rax,0x40(%r14)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    2f54:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f57:	bf 02 00 00 00       	mov    $0x2,%edi
    2f5c:	e8 3f f4 ff ff       	call   23a0 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    2f61:	45 89 3e             	mov    %r15d,(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f64:	4c 89 f1             	mov    %r14,%rcx
    2f67:	4c 89 ee             	mov    %r13,%rsi
    thread_data[x].threads = my_thread_data;
    2f6a:	49 89 46 10          	mov    %rax,0x10(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f6e:	48 89 df             	mov    %rbx,%rdi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2f71:	49 83 c5 38          	add    $0x38,%r13
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f75:	48 8d 15 c4 07 00 00 	lea    0x7c4(%rip),%rdx        # 3740 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    2f7c:	48 89 28             	mov    %rbp,(%rax)
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2f7f:	49 81 c6 b0 00 00 00 	add    $0xb0,%r14
    2f86:	48 83 c3 08          	add    $0x8,%rbx
      my_thread_data[n] = &thread_data[n]; 
    2f8a:	4c 89 60 08          	mov    %r12,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    2f8e:	48 8b 05 eb 4a 00 00 	mov    0x4aeb(%rip),%rax        # 7a80 <_IO_stdin_used+0xa80>
    2f95:	49 89 86 68 ff ff ff 	mov    %rax,-0x98(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f9c:	e8 cf f4 ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2fa1:	48 83 44 24 58 10    	addq   $0x10,0x58(%rsp)
    2fa7:	41 83 ff 04          	cmp    $0x4,%r15d
    2fab:	0f 85 c9 00 00 00    	jne    307a <main+0xa8a>
    2fb1:	41 bf 05 00 00 00    	mov    $0x5,%r15d
    2fb7:	e9 47 ff ff ff       	jmp    2f03 <main+0x913>
    2fbc:	48 8d 05 cd 2b 00 00 	lea    0x2bcd(%rip),%rax        # 5b90 <barriered_work_ingest_andwork>
    2fc3:	bd 01 00 00 00       	mov    $0x1,%ebp
          thread_data[x].tasks[y].run = barriered_work; 
    2fc8:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2fcf:	e9 83 f9 ff ff       	jmp    2957 <main+0x367>
    2fd4:	48 8d 05 b5 26 00 00 	lea    0x26b5(%rip),%rax        # 5690 <barriered_work>
    2fdb:	bd 02 00 00 00       	mov    $0x2,%ebp
    2fe0:	eb e6                	jmp    2fc8 <main+0x9d8>
      other = (x + 1) % total_threads;
    2fe2:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
    2fe7:	45 89 f7             	mov    %r14d,%r15d
      my_thread_data[0] = &thread_data[x]; 
    2fea:	4c 89 2b             	mov    %r13,(%rbx)
    2fed:	4c 89 e9             	mov    %r13,%rcx
      other = (x + 1) % total_threads;
    2ff0:	4c 0f af f8          	imul   %rax,%r15
      thread_data[x].thread_index = 0;
    2ff4:	41 c7 45 00 00 00 00 00 	movl   $0x0,0x0(%r13)
    2ffc:	bf 01 00 00 00       	mov    $0x1,%edi
    3001:	48 8d 35 01 43 00 00 	lea    0x4301(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      other = (x + 1) % total_threads;
    3008:	49 c1 ef 22          	shr    $0x22,%r15
    300c:	43 8d 04 7f          	lea    (%r15,%r15,2),%eax
    3010:	45 89 f7             	mov    %r14d,%r15d
    3013:	01 c0                	add    %eax,%eax
    3015:	41 29 c7             	sub    %eax,%r15d
      my_thread_data[1] = &thread_data[other]; 
    3018:	49 63 c7             	movslq %r15d,%rax
    301b:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    301f:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    3023:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    3028:	8b 14 24             	mov    (%rsp),%edx
    302b:	49 c1 e0 04          	shl    $0x4,%r8
    302f:	49 01 c0             	add    %rax,%r8
    3032:	31 c0                	xor    %eax,%eax
    3034:	4c 89 43 08          	mov    %r8,0x8(%rbx)
    3038:	e8 13 f4 ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    303d:	48 8d 45 18          	lea    0x18(%rbp),%rax
    3041:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3046:	48 89 c5             	mov    %rax,%rbp
    3049:	e9 1a f8 ff ff       	jmp    2868 <main+0x278>
        CPU_SET(curcpu, sendercpu);
    304e:	48 63 44 24 40       	movslq 0x40(%rsp),%rax
    3053:	48 89 c7             	mov    %rax,%rdi
    3056:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    305c:	77 12                	ja     3070 <main+0xa80>
    305e:	48 c1 e8 06          	shr    $0x6,%rax
    3062:	ba 01 00 00 00       	mov    $0x1,%edx
    3067:	89 f9                	mov    %edi,%ecx
    3069:	48 d3 e2             	shl    %cl,%rdx
    306c:	49 09 14 c4          	or     %rdx,(%r12,%rax,8)
        curcpu += 2;
    3070:	83 44 24 40 02       	addl   $0x2,0x40(%rsp)
    3075:	e9 42 f8 ff ff       	jmp    28bc <main+0x2cc>
    307a:	48 8d 3d f8 42 00 00 	lea    0x42f8(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    3081:	48 89 6c 24 08       	mov    %rbp,0x8(%rsp)
    3086:	48 8b 1c 24          	mov    (%rsp),%rbx
    308a:	31 ed                	xor    %ebp,%ebp
    308c:	e8 5f f2 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3091:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    3096:	4c 8d 6c 24 60       	lea    0x60(%rsp),%r13
    309b:	4c 8d 25 f5 42 00 00 	lea    0x42f5(%rip),%r12        # 7397 <_IO_stdin_used+0x397>
    void * result; 
    pthread_join(thread[x], &result);
    30a2:	48 8b 3c eb          	mov    (%rbx,%rbp,8),%rdi
    30a6:	4c 89 ee             	mov    %r13,%rsi
    30a9:	e8 42 f4 ff ff       	call   24f0 <pthread_join@plt>
    30ae:	89 ea                	mov    %ebp,%edx
    30b0:	4c 89 e6             	mov    %r12,%rsi
    30b3:	bf 01 00 00 00       	mov    $0x1,%edi
    30b8:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    30ba:	48 83 c5 01          	add    $0x1,%rbp
    30be:	e8 8d f3 ff ff       	call   2450 <__printf_chk@plt>
    30c3:	48 83 fd 06          	cmp    $0x6,%rbp
    30c7:	75 d9                	jne    30a2 <main+0xab2>
    30c9:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    30ce:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
    30d3:	31 c9                	xor    %ecx,%ecx
  long ingests = 0;
    30d5:	45 31 ff             	xor    %r15d,%r15d
  long received = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    30d8:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  long total = 0;
    30e0:	31 db                	xor    %ebx,%ebx
    30e2:	4d 89 fc             	mov    %r15,%r12
    30e5:	49 89 ca             	mov    %rcx,%r10
    30e8:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    30ed:	4d 8d 6e 28          	lea    0x28(%r14),%r13
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    30f1:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
    30fb:	bf 0a 00 00 00       	mov    $0xa,%edi
    3100:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    3105:	44 8b 74 24 10       	mov    0x10(%rsp),%r14d
    310a:	48 89 0c 24          	mov    %rcx,(%rsp)
    310e:	e8 bd f1 ff ff       	call   22d0 <putchar@plt>
    3113:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3118:	48 8d 35 8c 42 00 00 	lea    0x428c(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    311f:	bf 01 00 00 00       	mov    $0x1,%edi
    3124:	41 83 f6 01          	xor    $0x1,%r14d
    3128:	48 8b 10             	mov    (%rax),%rdx
    312b:	31 c0                	xor    %eax,%eax
    312d:	e8 1e f3 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3132:	41 8b 55 08          	mov    0x8(%r13),%edx
    3136:	48 8b 0c 24          	mov    (%rsp),%rcx
    313a:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    313f:	85 d2                	test   %edx,%edx
    3141:	0f 8e 40 04 00 00    	jle    3587 <main+0xf97>
    3147:	48 63 f2             	movslq %edx,%rsi
    314a:	49 8b 45 00          	mov    0x0(%r13),%rax
    long v = 0;
    314e:	31 d2                	xor    %edx,%edx
    3150:	48 c1 e6 09          	shl    $0x9,%rsi
    3154:	48 01 c6             	add    %rax,%rsi
    3157:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      v += thread_data[me].tasks[n].v;
    3160:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3167:	48 05 00 02 00 00    	add    $0x200,%rax
    316d:	48 39 f0             	cmp    %rsi,%rax
    3170:	75 ee                	jne    3160 <main+0xb70>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3172:	49 63 c6             	movslq %r14d,%rax
    3175:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    317a:	48 f7 d8             	neg    %rax
    317d:	25 b0 00 00 00       	and    $0xb0,%eax
    3182:	48 01 f8             	add    %rdi,%rax
    3185:	48 63 70 30          	movslq 0x30(%rax),%rsi
    3189:	85 f6                	test   %esi,%esi
    318b:	7e 25                	jle    31b2 <main+0xbc2>
    318d:	48 8b 40 28          	mov    0x28(%rax),%rax
    3191:	48 c1 e6 09          	shl    $0x9,%rsi
    3195:	48 01 c6             	add    %rax,%rsi
    3198:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      v += thread_data[other].tasks[n].v;
    31a0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    31a7:	48 05 00 02 00 00    	add    $0x200,%rax
    31ad:	48 39 f0             	cmp    %rsi,%rax
    31b0:	75 ee                	jne    31a0 <main+0xbb0>
    31b2:	48 8d 35 07 42 00 00 	lea    0x4207(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    31b9:	bf 01 00 00 00       	mov    $0x1,%edi
    31be:	31 c0                	xor    %eax,%eax
    31c0:	48 89 0c 24          	mov    %rcx,(%rsp)
    31c4:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    31c9:	e8 82 f2 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    31ce:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    31d3:	bf 01 00 00 00       	mov    $0x1,%edi
    31d8:	48 8b 30             	mov    (%rax),%rsi
    31db:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    31e5:	48 f7 ee             	imul   %rsi
    31e8:	48 c1 fe 3f          	sar    $0x3f,%rsi
    31ec:	31 c0                	xor    %eax,%eax
    31ee:	48 d1 fa             	sar    %rdx
    31f1:	48 29 f2             	sub    %rsi,%rdx
    31f4:	48 8d 35 15 44 00 00 	lea    0x4415(%rip),%rsi        # 7610 <_IO_stdin_used+0x610>
    31fb:	e8 50 f2 ff ff       	call   2450 <__printf_chk@plt>
    3200:	bf 0a 00 00 00       	mov    $0xa,%edi
    3205:	e8 c6 f0 ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    320a:	41 8b 55 08          	mov    0x8(%r13),%edx
    320e:	48 8b 0c 24          	mov    (%rsp),%rcx
    3212:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    3217:	85 d2                	test   %edx,%edx
    3219:	7e 4c                	jle    3267 <main+0xc77>
    321b:	49 8b 45 00          	mov    0x0(%r13),%rax
    321f:	4c 63 c2             	movslq %edx,%r8
    3222:	49 c1 e0 09          	shl    $0x9,%r8
    3226:	49 01 c0             	add    %rax,%r8
    3229:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3230:	48 8b 90 68 01 00 00 	mov    0x168(%rax),%rdx
      total += thread_data[x].tasks[n].n;
    3237:	48 03 98 08 01 00 00 	add    0x108(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    323e:	48 05 00 02 00 00    	add    $0x200,%rax
      ingests += thread_data[x].tasks[n].ingest_count;
    3244:	4c 03 a0 60 ff ff ff 	add    -0xa0(%rax),%r12
      sends += thread_data[x].tasks[n].sends;
    324b:	48 03 88 70 ff ff ff 	add    -0x90(%rax),%rcx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3252:	4c 03 52 10          	add    0x10(%rdx),%r10
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3256:	4c 03 7a 18          	add    0x18(%rdx),%r15
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    325a:	4c 03 52 30          	add    0x30(%rdx),%r10
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    325e:	4c 03 7a 38          	add    0x38(%rdx),%r15
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3262:	4c 39 c0             	cmp    %r8,%rax
    3265:	75 c9                	jne    3230 <main+0xc40>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3267:	45 31 f6             	xor    %r14d,%r14d
    326a:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    326f:	0f 8e 84 00 00 00    	jle    32f9 <main+0xd09>
    3275:	48 89 1c 24          	mov    %rbx,(%rsp)
    3279:	4c 89 f3             	mov    %r14,%rbx
    327c:	4d 89 d6             	mov    %r10,%r14
    327f:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
    3284:	4d 89 ec             	mov    %r13,%r12
    3287:	49 89 cd             	mov    %rcx,%r13
    328a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3290:	49 8b 44 24 58       	mov    0x58(%r12),%rax
    3295:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    3299:	48 83 ec 08          	sub    $0x8,%rsp
    329d:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    32a2:	48 83 c3 01          	add    $0x1,%rbx
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    32a6:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    32aa:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    32ae:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32b2:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    32b5:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    32b9:	4c 2b 01             	sub    (%rcx),%r8
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32bc:	48 f7 e5             	mul    %rbp
    32bf:	8b 49 20             	mov    0x20(%rcx),%ecx
    32c2:	56                   	push   %rsi
    32c3:	31 c0                	xor    %eax,%eax
    32c5:	48 8d 35 64 43 00 00 	lea    0x4364(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    32cc:	48 c1 ea 12          	shr    $0x12,%rdx
    32d0:	49 89 d1             	mov    %rdx,%r9
    32d3:	ba 02 00 00 00       	mov    $0x2,%edx
    32d8:	e8 73 f1 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    32dd:	41 5b                	pop    %r11
    32df:	58                   	pop    %rax
    32e0:	49 39 5c 24 68       	cmp    %rbx,0x68(%r12)
    32e5:	7f a9                	jg     3290 <main+0xca0>
    32e7:	4c 89 e9             	mov    %r13,%rcx
    32ea:	48 8b 1c 24          	mov    (%rsp),%rbx
    32ee:	4d 89 e5             	mov    %r12,%r13
    32f1:	4c 8b 64 24 08       	mov    0x8(%rsp),%r12
    32f6:	4d 89 f2             	mov    %r14,%r10
      // printf("%ldns per thread\n", (seconds2 / 2));
    }
    // printf("cycles %ld\n", thread_data[x].cycles);

    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    32f9:	41 8b b5 84 00 00 00 	mov    0x84(%r13),%esi
    3300:	85 f6                	test   %esi,%esi
    3302:	0f 8e 28 01 00 00    	jle    3430 <main+0xe40>
    3308:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    330d:	4d 8b 4d 18          	mov    0x18(%r13),%r9
    3311:	31 d2                	xor    %edx,%edx
    3313:	4c 89 64 24 40       	mov    %r12,0x40(%rsp)
    3318:	48 89 4c 24 30       	mov    %rcx,0x30(%rsp)
    331d:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    3322:	4c 89 7c 24 58       	mov    %r15,0x58(%rsp)
    3327:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3330:	49 8b 04 d1          	mov    (%r9,%rdx,8),%rax
    3334:	41 89 d7             	mov    %edx,%r15d
    3337:	48 8d 1c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rbx
    333f:	44 8b 00             	mov    (%rax),%r8d
    3342:	45 85 c0             	test   %r8d,%r8d
    3345:	0f 8e c0 00 00 00    	jle    340b <main+0xe1b>
    334b:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3350:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3354:	31 c0                	xor    %eax,%eax
    3356:	48 89 c6             	mov    %rax,%rsi
    3359:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3360:	49 89 f4             	mov    %rsi,%r12
    3363:	45 31 f6             	xor    %r14d,%r14d
    3366:	49 c1 e4 08          	shl    $0x8,%r12
    336a:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    336e:	8b ba 94 00 00 00    	mov    0x94(%rdx),%edi
    3374:	85 ff                	test   %edi,%edi
    3376:	7e 7a                	jle    33f2 <main+0xe02>
    3378:	48 89 34 24          	mov    %rsi,(%rsp)
    337c:	0f 1f 40 00          	nopl   0x0(%rax)
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3380:	4c 89 f1             	mov    %r14,%rcx
    3383:	48 83 ec 08          	sub    $0x8,%rsp
    3387:	bf 01 00 00 00       	mov    $0x1,%edi
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    338c:	49 83 c6 01          	add    $0x1,%r14
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3390:	48 c1 e1 05          	shl    $0x5,%rcx
    3394:	48 03 8a 88 00 00 00 	add    0x88(%rdx),%rcx
	  struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
	  const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
	  const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    339b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    339f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
	  printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    33a3:	48 89 f0             	mov    %rsi,%rax
	  const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    33a6:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    33aa:	4c 2b 01             	sub    (%rcx),%r8
    33ad:	56                   	push   %rsi
	  printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    33ae:	48 f7 e5             	mul    %rbp
    33b1:	44 89 f9             	mov    %r15d,%ecx
    33b4:	48 8d 35 c5 42 00 00 	lea    0x42c5(%rip),%rsi        # 7680 <_IO_stdin_used+0x680>
    33bb:	31 c0                	xor    %eax,%eax
    33bd:	48 c1 ea 12          	shr    $0x12,%rdx
    33c1:	49 89 d1             	mov    %rdx,%r9
    33c4:	ba 02 00 00 00       	mov    $0x2,%edx
    33c9:	e8 82 f0 ff ff       	call   2450 <__printf_chk@plt>
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    33ce:	4d 8b 4d 18          	mov    0x18(%r13),%r9
    33d2:	41 58                	pop    %r8
    33d4:	41 5a                	pop    %r10
    33d6:	49 8b 04 19          	mov    (%r9,%rbx,1),%rax
    33da:	48 8b 48 08          	mov    0x8(%rax),%rcx
    33de:	4a 8d 14 21          	lea    (%rcx,%r12,1),%rdx
    33e2:	44 39 b2 94 00 00 00 	cmp    %r14d,0x94(%rdx)
    33e9:	7f 95                	jg     3380 <main+0xd90>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    33eb:	48 8b 34 24          	mov    (%rsp),%rsi
    33ef:	44 8b 00             	mov    (%rax),%r8d
    33f2:	48 83 c6 01          	add    $0x1,%rsi
    33f6:	41 39 f0             	cmp    %esi,%r8d
    33f9:	0f 8f 61 ff ff ff    	jg     3360 <main+0xd70>
    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    33ff:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    3404:	41 8b b5 84 00 00 00 	mov    0x84(%r13),%esi
    340b:	48 83 c2 01          	add    $0x1,%rdx
    340f:	39 d6                	cmp    %edx,%esi
    3411:	0f 8f 19 ff ff ff    	jg     3330 <main+0xd40>
    3417:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    341c:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    3421:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    3426:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    342b:	4c 8b 7c 24 58       	mov    0x58(%rsp),%r15
  for (int x = 0 ; x < thread_count ; x++) {
    3430:	8b 44 24 10          	mov    0x10(%rsp),%eax
    3434:	48 83 44 24 18 18    	addq   $0x18,0x18(%rsp)
    343a:	49 81 c5 b0 00 00 00 	add    $0xb0,%r13
    3441:	85 c0                	test   %eax,%eax
    3443:	75 0d                	jne    3452 <main+0xe62>
    3445:	c7 44 24 10 01 00 00 00 	movl   $0x1,0x10(%rsp)
    344d:	e9 a9 fc ff ff       	jmp    30fb <main+0xb0b>
    3452:	48 89 da             	mov    %rbx,%rdx
    3455:	48 8d 35 71 3f 00 00 	lea    0x3f71(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    345c:	31 c0                	xor    %eax,%eax
    345e:	4c 89 3c 24          	mov    %r15,(%rsp)
    3462:	bf 01 00 00 00       	mov    $0x1,%edi
    3467:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    346c:	4d 89 e7             	mov    %r12,%r15
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    346f:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
    3479:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    347e:	49 c1 ff 3f          	sar    $0x3f,%r15
    3482:	e8 c9 ef ff ff       	call   2450 <__printf_chk@plt>
    3487:	bf 0a 00 00 00       	mov    $0xa,%edi
    348c:	e8 3f ee ff ff       	call   22d0 <putchar@plt>
    3491:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3496:	bf 01 00 00 00       	mov    $0x1,%edi
    349b:	48 8d 35 36 42 00 00 	lea    0x4236(%rip),%rsi        # 76d8 <_IO_stdin_used+0x6d8>
    34a2:	48 8b 50 08          	mov    0x8(%rax),%rdx
    34a6:	31 c0                	xor    %eax,%eax
    34a8:	e8 a3 ef ff ff       	call   2450 <__printf_chk@plt>
    34ad:	4c 89 e0             	mov    %r12,%rax
    34b0:	bf 01 00 00 00       	mov    $0x1,%edi
    34b5:	48 8d 35 44 42 00 00 	lea    0x4244(%rip),%rsi        # 7700 <_IO_stdin_used+0x700>
    34bc:	48 f7 ed             	imul   %rbp
    34bf:	31 c0                	xor    %eax,%eax
    34c1:	48 d1 fa             	sar    %rdx
    34c4:	4c 29 fa             	sub    %r15,%rdx
    34c7:	e8 84 ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    34cc:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    34d1:	bf 01 00 00 00       	mov    $0x1,%edi
    34d6:	48 8d 35 53 42 00 00 	lea    0x4253(%rip),%rsi        # 7730 <_IO_stdin_used+0x730>
    34dd:	4c 89 d8             	mov    %r11,%rax
    34e0:	49 c1 fb 3f          	sar    $0x3f,%r11
    34e4:	48 f7 ed             	imul   %rbp
    34e7:	31 c0                	xor    %eax,%eax
    34e9:	48 d1 fa             	sar    %rdx
    34ec:	4c 29 da             	sub    %r11,%rdx
    34ef:	e8 5c ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    34f4:	48 89 d8             	mov    %rbx,%rax
    34f7:	48 c1 fb 3f          	sar    $0x3f,%rbx
    34fb:	48 8d 35 5e 42 00 00 	lea    0x425e(%rip),%rsi        # 7760 <_IO_stdin_used+0x760>
    3502:	48 f7 ed             	imul   %rbp
    3505:	bf 01 00 00 00       	mov    $0x1,%edi
    350a:	31 c0                	xor    %eax,%eax
    350c:	48 d1 fa             	sar    %rdx
    350f:	48 29 da             	sub    %rbx,%rdx
    3512:	e8 39 ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3517:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    351c:	bf 01 00 00 00       	mov    $0x1,%edi
    3521:	48 8d 35 b9 3e 00 00 	lea    0x3eb9(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    3528:	48 89 c8             	mov    %rcx,%rax
    352b:	48 c1 f9 3f          	sar    $0x3f,%rcx
    352f:	48 f7 ed             	imul   %rbp
    3532:	31 c0                	xor    %eax,%eax
    3534:	48 d1 fa             	sar    %rdx
    3537:	48 29 ca             	sub    %rcx,%rdx
    353a:	e8 11 ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    353f:	4c 8b 0c 24          	mov    (%rsp),%r9
    3543:	bf 01 00 00 00       	mov    $0x1,%edi
    3548:	48 8d 35 a3 3e 00 00 	lea    0x3ea3(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    354f:	4c 89 c8             	mov    %r9,%rax
    3552:	49 c1 f9 3f          	sar    $0x3f,%r9
    3556:	48 f7 ed             	imul   %rbp
    3559:	48 d1 fa             	sar    %rdx
    355c:	4c 29 ca             	sub    %r9,%rdx
    355f:	31 c0                	xor    %eax,%eax
    3561:	e8 ea ee ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3566:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    356b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3574:	75 18                	jne    358e <main+0xf9e>
    3576:	48 83 c4 78          	add    $0x78,%rsp
    357a:	31 c0                	xor    %eax,%eax
    357c:	5b                   	pop    %rbx
    357d:	5d                   	pop    %rbp
    357e:	41 5c                	pop    %r12
    3580:	41 5d                	pop    %r13
    3582:	41 5e                	pop    %r14
    3584:	41 5f                	pop    %r15
    3586:	c3                   	ret
    long v = 0;
    3587:	31 d2                	xor    %edx,%edx
    3589:	e9 e4 fb ff ff       	jmp    3172 <main+0xb82>
}
    358e:	e8 9d ed ff ff       	call   2330 <__stack_chk_fail@plt>
    3593:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    359d:	0f 1f 00             	nopl   (%rax)

00000000000035a0 <_start>:
    35a0:	f3 0f 1e fa          	endbr64
    35a4:	31 ed                	xor    %ebp,%ebp
    35a6:	49 89 d1             	mov    %rdx,%r9
    35a9:	5e                   	pop    %rsi
    35aa:	48 89 e2             	mov    %rsp,%rdx
    35ad:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    35b1:	50                   	push   %rax
    35b2:	54                   	push   %rsp
    35b3:	45 31 c0             	xor    %r8d,%r8d
    35b6:	31 c9                	xor    %ecx,%ecx
    35b8:	48 8d 3d 31 f0 ff ff 	lea    -0xfcf(%rip),%rdi        # 25f0 <main>
    35bf:	ff 15 13 6a 00 00    	call   *0x6a13(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    35c5:	f4                   	hlt
    35c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000035d0 <deregister_tm_clones>:
    35d0:	48 8d 3d 49 6a 00 00 	lea    0x6a49(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    35d7:	48 8d 05 42 6a 00 00 	lea    0x6a42(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    35de:	48 39 f8             	cmp    %rdi,%rax
    35e1:	74 15                	je     35f8 <deregister_tm_clones+0x28>
    35e3:	48 8b 05 f6 69 00 00 	mov    0x69f6(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    35ea:	48 85 c0             	test   %rax,%rax
    35ed:	74 09                	je     35f8 <deregister_tm_clones+0x28>
    35ef:	ff e0                	jmp    *%rax
    35f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    35f8:	c3                   	ret
    35f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003600 <register_tm_clones>:
    3600:	48 8d 3d 19 6a 00 00 	lea    0x6a19(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3607:	48 8d 35 12 6a 00 00 	lea    0x6a12(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    360e:	48 29 fe             	sub    %rdi,%rsi
    3611:	48 89 f0             	mov    %rsi,%rax
    3614:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3618:	48 c1 f8 03          	sar    $0x3,%rax
    361c:	48 01 c6             	add    %rax,%rsi
    361f:	48 d1 fe             	sar    %rsi
    3622:	74 14                	je     3638 <register_tm_clones+0x38>
    3624:	48 8b 05 c5 69 00 00 	mov    0x69c5(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    362b:	48 85 c0             	test   %rax,%rax
    362e:	74 08                	je     3638 <register_tm_clones+0x38>
    3630:	ff e0                	jmp    *%rax
    3632:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3638:	c3                   	ret
    3639:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003640 <__do_global_dtors_aux>:
    3640:	f3 0f 1e fa          	endbr64
    3644:	80 3d dd 69 00 00 00 	cmpb   $0x0,0x69dd(%rip)        # a028 <completed.0>
    364b:	75 2b                	jne    3678 <__do_global_dtors_aux+0x38>
    364d:	55                   	push   %rbp
    364e:	48 83 3d a2 69 00 00 00 	cmpq   $0x0,0x69a2(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3656:	48 89 e5             	mov    %rsp,%rbp
    3659:	74 0c                	je     3667 <__do_global_dtors_aux+0x27>
    365b:	48 8b 3d a6 69 00 00 	mov    0x69a6(%rip),%rdi        # a008 <__dso_handle>
    3662:	e8 49 ec ff ff       	call   22b0 <__cxa_finalize@plt>
    3667:	e8 64 ff ff ff       	call   35d0 <deregister_tm_clones>
    366c:	c6 05 b5 69 00 00 01 	movb   $0x1,0x69b5(%rip)        # a028 <completed.0>
    3673:	5d                   	pop    %rbp
    3674:	c3                   	ret
    3675:	0f 1f 00             	nopl   (%rax)
    3678:	c3                   	ret
    3679:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003680 <frame_dummy>:
    3680:	f3 0f 1e fa          	endbr64
    3684:	e9 77 ff ff ff       	jmp    3600 <register_tm_clones>
    3689:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003690 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3690:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3694:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    369b:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    369f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    36a7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    36ab:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    36af:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    36b6:	48 85 c9             	test   %rcx,%rcx
    36b9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    36c0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    36c4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    36c8:	31 c0                	xor    %eax,%eax
    36ca:	c3                   	ret
    36cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000036d0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    36d0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    36d4:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    36db:	85 c9                	test   %ecx,%ecx
    36dd:	7e 4f                	jle    372e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    36df:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    36e6:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    36ed:	48 c1 e1 09          	shl    $0x9,%rcx
    36f1:	48 8b 50 10          	mov    0x10(%rax),%rdx
    36f5:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    36f9:	48 8b 70 28          	mov    0x28(%rax),%rsi
    36fd:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    36ff:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    3703:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3708:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3710:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3718:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3723:	48 05 00 02 00 00    	add    $0x200,%rax
    3729:	48 39 c1             	cmp    %rax,%rcx
    372c:	75 da                	jne    3708 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    372e:	0f ae f8             	sfence
}
    3731:	31 c0                	xor    %eax,%eax
    3733:	c3                   	ret
    3734:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    373f:	90                   	nop

0000000000003740 <external_thread>:
void * external_thread(void *arg) {
    3740:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3744:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    3748:	0f 85 fb 00 00 00    	jne    3849 <external_thread+0x109>
void * external_thread(void *arg) {
    374e:	41 57                	push   %r15
    3750:	49 89 ff             	mov    %rdi,%r15
    3753:	41 56                	push   %r14
    3755:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    3757:	4c 8d 2d a6 38 00 00 	lea    0x38a6(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    375e:	41 54                	push   %r12
    3760:	55                   	push   %rbp
    3761:	53                   	push   %rbx
    3762:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    3766:	8b 8f ac 00 00 00    	mov    0xac(%rdi),%ecx
    376c:	48 8b 7f 40          	mov    0x40(%rdi),%rdi
    3770:	85 c9                	test   %ecx,%ecx
    3772:	7e 6e                	jle    37e2 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3774:	45 31 e4             	xor    %r12d,%r12d
    3777:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3780:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    3788:	31 db                	xor    %ebx,%ebx
    378a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    378e:	48 8b 06             	mov    (%rsi),%rax
    3791:	8b 10                	mov    (%rax),%edx
    3793:	85 d2                	test   %edx,%edx
    3795:	7e 2a                	jle    37c1 <external_thread+0x81>
    3797:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    379b:	48 89 dd             	mov    %rbx,%rbp
    379e:	48 c1 e5 08          	shl    $0x8,%rbp
    37a2:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    37a6:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    37ad:	45 85 c0             	test   %r8d,%r8d
    37b0:	74 36                	je     37e8 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    37b2:	48 83 c3 01          	add    $0x1,%rbx
    37b6:	39 da                	cmp    %ebx,%edx
    37b8:	7f e1                	jg     379b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    37ba:	41 8b 8f ac 00 00 00 	mov    0xac(%r15),%ecx
    37c1:	49 83 c4 01          	add    $0x1,%r12
    37c5:	44 39 e1             	cmp    %r12d,%ecx
    37c8:	7f b6                	jg     3780 <external_thread+0x40>
  while (data->running == 1) {
    37ca:	41 83 7f 34 01       	cmpl   $0x1,0x34(%r15)
    37cf:	74 9f                	je     3770 <external_thread+0x30>
}
    37d1:	48 83 c4 08          	add    $0x8,%rsp
    37d5:	31 c0                	xor    %eax,%eax
    37d7:	5b                   	pop    %rbx
    37d8:	5d                   	pop    %rbp
    37d9:	41 5c                	pop    %r12
    37db:	41 5d                	pop    %r13
    37dd:	41 5e                	pop    %r14
    37df:	41 5f                	pop    %r15
    37e1:	c3                   	ret
  while (data->running == 1) {
    37e2:	eb fe                	jmp    37e2 <external_thread+0xa2>
    37e4:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    37e8:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    37eb:	48 8b 06             	mov    (%rsi),%rax
    37ee:	48 8b 78 08          	mov    0x8(%rax),%rdi
    37f2:	48 01 ef             	add    %rbp,%rdi
    37f5:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    37fc:	48 c1 e6 05          	shl    $0x5,%rsi
    3800:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    3807:	bf 04 00 00 00       	mov    $0x4,%edi
    380c:	e8 ff ea ff ff       	call   2310 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    3811:	49 8b 47 40          	mov    0x40(%r15),%rax
    3815:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    3819:	48 8b 40 08          	mov    0x8(%rax),%rax
    381d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    3828:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    382b:	49 8b 7f 40          	mov    0x40(%r15),%rdi
    382f:	48 83 c3 01          	add    $0x1,%rbx
    3833:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3837:	48 8b 06             	mov    (%rsi),%rax
    383a:	8b 10                	mov    (%rax),%edx
    383c:	39 da                	cmp    %ebx,%edx
    383e:	0f 8f 53 ff ff ff    	jg     3797 <external_thread+0x57>
    3844:	e9 71 ff ff ff       	jmp    37ba <external_thread+0x7a>
}
    3849:	31 c0                	xor    %eax,%eax
    384b:	c3                   	ret
    384c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003850 <timer_thread>:
void* timer_thread(void *arg) {
    3850:	f3 0f 1e fa          	endbr64
    3854:	41 57                	push   %r15
    3856:	48 8d 35 b3 37 00 00 	lea    0x37b3(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    385d:	49 89 ff             	mov    %rdi,%r15
    3860:	41 56                	push   %r14
    3862:	41 55                	push   %r13
    3864:	41 54                	push   %r12
    3866:	55                   	push   %rbp
    3867:	53                   	push   %rbx
    3868:	48 83 ec 58          	sub    $0x58,%rsp
    386c:	8b 17                	mov    (%rdi),%edx
    386e:	bf 01 00 00 00       	mov    $0x1,%edi
    3873:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    387c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3881:	31 c0                	xor    %eax,%eax
    3883:	e8 c8 eb ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3888:	66 0f 6f 05 f0 40 00 00 	movdqa 0x40f0(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    3890:	ba 88 13 00 00       	mov    $0x1388,%edx
    3895:	31 c0                	xor    %eax,%eax
    3897:	48 8d 35 84 37 00 00 	lea    0x3784(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    389e:	bf 01 00 00 00       	mov    $0x1,%edi
    38a3:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    38a8:	e8 a3 eb ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    38ad:	45 8b 67 34          	mov    0x34(%r15),%r12d
    38b1:	45 85 e4             	test   %r12d,%r12d
    38b4:	0f 84 9b 00 00 00    	je     3955 <timer_thread+0x105>
  int n = 0;
    38ba:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    38bd:	45 31 e4             	xor    %r12d,%r12d
    38c0:	49 89 e5             	mov    %rsp,%r13
    y++;
    38c3:	31 db                	xor    %ebx,%ebx
    38c5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    38ca:	48 89 ef             	mov    %rbp,%rdi
    38cd:	4c 89 ee             	mov    %r13,%rsi
    n++;
    38d0:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    38d4:	e8 77 ea ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    38d9:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    38dd:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    38e2:	85 c0                	test   %eax,%eax
    38e4:	7e 47                	jle    392d <timer_thread+0xdd>
    38e6:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    38ea:	49 c1 e4 09          	shl    $0x9,%r12
    38ee:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    38f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    38f8:	4c 8b 11             	mov    (%rcx),%r10
    38fb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    38fd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3901:	99                   	cltd
    3902:	41 f7 7a 30          	idivl  0x30(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3906:	49 8b 72 28          	mov    0x28(%r10),%rsi
    390a:	48 63 d2             	movslq %edx,%rdx
    390d:	48 c1 e2 09          	shl    $0x9,%rdx
    3911:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    391c:	42 c7 84 26 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3928:	49 39 c8             	cmp    %rcx,%r8
    392b:	75 cb                	jne    38f8 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    392d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3930:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3934:	41 8b 57 34          	mov    0x34(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3938:	48 8b 00             	mov    (%rax),%rax
    y++;
    393b:	39 78 30             	cmp    %edi,0x30(%rax)
    393e:	0f 4e fb             	cmovle %ebx,%edi
    3941:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3944:	85 d2                	test   %edx,%edx
    3946:	74 0d                	je     3955 <timer_thread+0x105>
    3948:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    394f:	0f 85 75 ff ff ff    	jne    38ca <timer_thread+0x7a>
    3955:	48 8d 3d dc 36 00 00 	lea    0x36dc(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    395c:	e8 8f e9 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3961:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3965:	85 d2                	test   %edx,%edx
    3967:	7e 6b                	jle    39d4 <timer_thread+0x184>
    for (int y = 0 ; y < data->task_count ; y++) {
    3969:	49 63 47 30          	movslq 0x30(%r15),%rax
    396d:	85 c0                	test   %eax,%eax
    396f:	7e 63                	jle    39d4 <timer_thread+0x184>
    3971:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3975:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3979:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3981:	31 ff                	xor    %edi,%edi
    3983:	48 89 c2             	mov    %rax,%rdx
    3986:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    398a:	48 8b 40 28          	mov    0x28(%rax),%rax
    398e:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3992:	f6 c6 02             	test   $0x2,%dh
    3995:	74 15                	je     39ac <timer_thread+0x15c>
    3997:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    39a1:	48 05 00 02 00 00    	add    $0x200,%rax
    39a7:	48 39 c6             	cmp    %rax,%rsi
    39aa:	74 1f                	je     39cb <timer_thread+0x17b>
      data->threads[x]->tasks[y].sending = 0;
    39ac:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    39b6:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    39bc:	c7 80 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    39c6:	48 39 c6             	cmp    %rax,%rsi
    39c9:	75 e1                	jne    39ac <timer_thread+0x15c>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    39cb:	48 83 c7 08          	add    $0x8,%rdi
    39cf:	48 39 f9             	cmp    %rdi,%rcx
    39d2:	75 b2                	jne    3986 <timer_thread+0x136>
  asm volatile ("mfence" ::: "memory");
    39d4:	0f ae f0             	mfence
  struct timespec drain = {
    39d7:	66 0f 6f 05 b1 3f 00 00 	movdqa 0x3fb1(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    39df:	48 8d 2d 77 36 00 00 	lea    0x3677(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    39e6:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    39eb:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    39ef:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    39f4:	85 c0                	test   %eax,%eax
    39f6:	7e 4c                	jle    3a44 <timer_thread+0x1f4>
    39f8:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    39fc:	4d 63 c4             	movslq %r12d,%r8
    39ff:	49 c1 e0 09          	shl    $0x9,%r8
    3a03:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3a07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3a10:	48 8b 19             	mov    (%rcx),%rbx
    3a13:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a15:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3a19:	99                   	cltd
    3a1a:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3a1d:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3a21:	48 63 d2             	movslq %edx,%rdx
    3a24:	48 c1 e2 09          	shl    $0x9,%rdx
    3a28:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3a33:	42 c7 84 06 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a3f:	4c 39 c9             	cmp    %r9,%rcx
    3a42:	75 cc                	jne    3a10 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    3a44:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3a47:	49 8b 47 10          	mov    0x10(%r15),%rax
    y++;
    3a4b:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3a4e:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3a51:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3a54:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3a58:	41 8b 7f 20          	mov    0x20(%r15),%edi
    3a5c:	85 ff                	test   %edi,%edi
    3a5e:	0f 8e bc 00 00 00    	jle    3b20 <timer_thread+0x2d0>
    3a64:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    3a67:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3a6d:	0f 1f 00             	nopl   (%rax)
    3a70:	4a 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbx
            all_empty = 0;
    3a78:	45 31 f6             	xor    %r14d,%r14d
    3a7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3a80:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3a84:	4c 89 f0             	mov    %r14,%rax
    3a87:	48 c1 e0 09          	shl    $0x9,%rax
    3a8b:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3a8f:	31 d2                	xor    %edx,%edx
    3a91:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3a98:	eb 16                	jmp    3ab0 <timer_thread+0x260>
    3a9a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3aa0:	4d 85 c0             	test   %r8,%r8
    3aa3:	7f 1f                	jg     3ac4 <timer_thread+0x274>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3aa5:	83 c2 01             	add    $0x1,%edx
    3aa8:	48 83 c0 20          	add    $0x20,%rax
    3aac:	39 fa                	cmp    %edi,%edx
    3aae:	74 2a                	je     3ada <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3ab0:	48 8b 08             	mov    (%rax),%rcx
    3ab3:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3ab7:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3abb:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3abf:	48 85 c9             	test   %rcx,%rcx
    3ac2:	7e dc                	jle    3aa0 <timer_thread+0x250>
    3ac4:	bf 01 00 00 00       	mov    $0x1,%edi
    3ac9:	48 89 ee             	mov    %rbp,%rsi
    3acc:	31 c0                	xor    %eax,%eax
    3ace:	e8 7d e9 ff ff       	call   2450 <__printf_chk@plt>
            break;
    3ad3:	41 8b 7f 20          	mov    0x20(%r15),%edi
            all_empty = 0;
    3ad7:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3ada:	49 83 c6 01          	add    $0x1,%r14
    3ade:	44 39 f7             	cmp    %r14d,%edi
    3ae1:	7e 0d                	jle    3af0 <timer_thread+0x2a0>
    3ae3:	49 8b 47 10          	mov    0x10(%r15),%rax
    3ae7:	eb 97                	jmp    3a80 <timer_thread+0x230>
    3ae9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3af0:	49 83 c5 01          	add    $0x1,%r13
    3af4:	44 39 ef             	cmp    %r13d,%edi
    3af7:	7e 0d                	jle    3b06 <timer_thread+0x2b6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3af9:	85 ff                	test   %edi,%edi
    3afb:	7e 09                	jle    3b06 <timer_thread+0x2b6>
    3afd:	49 8b 47 10          	mov    0x10(%r15),%rax
    3b01:	e9 6a ff ff ff       	jmp    3a70 <timer_thread+0x220>
    if (all_empty == 1) {
    3b06:	41 83 f9 01          	cmp    $0x1,%r9d
    3b0a:	74 14                	je     3b20 <timer_thread+0x2d0>
      nanosleep(&drain , &drainrem);
    3b0c:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3b11:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3b16:	e8 35 e8 ff ff       	call   2350 <nanosleep@plt>
    3b1b:	e9 cb fe ff ff       	jmp    39eb <timer_thread+0x19b>
    3b20:	48 8d 3d 2d 35 00 00 	lea    0x352d(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3b27:	e8 c4 e7 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3b2c:	41 8b 47 34          	mov    0x34(%r15),%eax
    3b30:	85 c0                	test   %eax,%eax
    3b32:	0f 84 cf 00 00 00    	je     3c07 <timer_thread+0x3b7>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b38:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3b3c:	85 c9                	test   %ecx,%ecx
    3b3e:	7e 2d                	jle    3b6d <timer_thread+0x31d>
    3b40:	49 8b 47 10          	mov    0x10(%r15),%rax
    3b44:	31 db                	xor    %ebx,%ebx
    3b46:	48 8d 2d 21 35 00 00 	lea    0x3521(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3b4d:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->running = 0;
    3b50:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3b54:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3b58:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3b5f:	0f 84 cf 00 00 00    	je     3c34 <timer_thread+0x3e4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b65:	48 83 c3 01          	add    $0x1,%rbx
    3b69:	39 d9                	cmp    %ebx,%ecx
    3b6b:	7f e3                	jg     3b50 <timer_thread+0x300>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b6d:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3b71:	85 d2                	test   %edx,%edx
    3b73:	7e 7b                	jle    3bf0 <timer_thread+0x3a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3b75:	49 63 47 30          	movslq 0x30(%r15),%rax
    3b79:	85 c0                	test   %eax,%eax
    3b7b:	7e 73                	jle    3bf0 <timer_thread+0x3a0>
    3b7d:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3b81:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3b85:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3b8d:	31 c9                	xor    %ecx,%ecx
    3b8f:	48 89 c6             	mov    %rax,%rsi
    3b92:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3b98:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3b9c:	48 8b 40 28          	mov    0x28(%rax),%rax
    3ba0:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3ba4:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3baa:	74 1c                	je     3bc8 <timer_thread+0x378>
    3bac:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3bb6:	48 05 00 02 00 00    	add    $0x200,%rax
    3bbc:	48 39 d0             	cmp    %rdx,%rax
    3bbf:	74 26                	je     3be7 <timer_thread+0x397>
    3bc1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3bc8:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3bd2:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3bd8:	c7 80 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3be2:	48 39 d0             	cmp    %rdx,%rax
    3be5:	75 e1                	jne    3bc8 <timer_thread+0x378>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3be7:	48 83 c1 08          	add    $0x8,%rcx
    3beb:	48 39 f9             	cmp    %rdi,%rcx
    3bee:	75 a8                	jne    3b98 <timer_thread+0x348>
    asm volatile ("mfence" ::: "memory");
    3bf0:	0f ae f0             	mfence
    3bf3:	48 8d 3d 86 34 00 00 	lea    0x3486(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3bfa:	e8 f1 e6 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3bff:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
    3c07:	48 8d 3d 79 34 00 00 	lea    0x3479(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3c0e:	e8 dd e6 ff ff       	call   22f0 <puts@plt>
}
    3c13:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3c18:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3c21:	75 47                	jne    3c6a <timer_thread+0x41a>
    3c23:	48 83 c4 58          	add    $0x58,%rsp
    3c27:	31 c0                	xor    %eax,%eax
    3c29:	5b                   	pop    %rbx
    3c2a:	5d                   	pop    %rbp
    3c2b:	41 5c                	pop    %r12
    3c2d:	41 5d                	pop    %r13
    3c2f:	41 5e                	pop    %r14
    3c31:	41 5f                	pop    %r15
    3c33:	c3                   	ret
    3c34:	48 89 ef             	mov    %rbp,%rdi
    3c37:	e8 b4 e6 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3c3c:	49 8b 47 10          	mov    0x10(%r15),%rax
    3c40:	be 01 00 00 00       	mov    $0x1,%esi
    3c45:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c49:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3c4d:	8b 78 50             	mov    0x50(%rax),%edi
    3c50:	e8 ab e7 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c55:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3c59:	39 d9                	cmp    %ebx,%ecx
    3c5b:	0f 8e 0c ff ff ff    	jle    3b6d <timer_thread+0x31d>
    3c61:	49 8b 47 10          	mov    0x10(%r15),%rax
    3c65:	e9 e6 fe ff ff       	jmp    3b50 <timer_thread+0x300>
}
    3c6a:	e8 c1 e6 ff ff       	call   2330 <__stack_chk_fail@plt>
    3c6f:	90                   	nop

0000000000003c70 <strtolower>:
void strtolower(char *str) {
    3c70:	f3 0f 1e fa          	endbr64
    3c74:	55                   	push   %rbp
    3c75:	53                   	push   %rbx
    3c76:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3c7a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3c7e:	84 db                	test   %bl,%bl
    3c80:	74 24                	je     3ca6 <strtolower+0x36>
    3c82:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3c85:	e8 86 e8 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3c8a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c90:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3c93:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3c97:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3c9a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3c9d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3ca2:	84 db                	test   %bl,%bl
    3ca4:	75 ea                	jne    3c90 <strtolower+0x20>
}
    3ca6:	48 83 c4 08          	add    $0x8,%rsp
    3caa:	5b                   	pop    %rbx
    3cab:	5d                   	pop    %rbp
    3cac:	c3                   	ret
    3cad:	0f 1f 00             	nopl   (%rax)

0000000000003cb0 <zh_malloc>:
void *zh_malloc(size_t size) {
    3cb0:	f3 0f 1e fa          	endbr64
    3cb4:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3cb8:	e8 53 e7 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3cbd:	48 85 c0             	test   %rax,%rax
    3cc0:	74 05                	je     3cc7 <zh_malloc+0x17>
}
    3cc2:	48 83 c4 08          	add    $0x8,%rsp
    3cc6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3cc7:	48 8b 0d 52 63 00 00 	mov    0x6352(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    3cce:	ba 28 00 00 00       	mov    $0x28,%edx
    3cd3:	be 01 00 00 00       	mov    $0x1,%esi
    3cd8:	48 8d 3d 29 37 00 00 	lea    0x3729(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    3cdf:	e8 dc e7 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    3ce4:	bf 01 00 00 00       	mov    $0x1,%edi
    3ce9:	e8 b2 e7 ff ff       	call   24a0 <exit@plt>
    3cee:	66 90                	xchg   %ax,%ax

0000000000003cf0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3cf0:	f3 0f 1e fa          	endbr64
    3cf4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    3cf5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3cfa:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3cfd:	e8 5e e6 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3d02:	48 85 c0             	test   %rax,%rax
    3d05:	74 11                	je     3d18 <get_filename_ext+0x28>
    3d07:	48 39 c3             	cmp    %rax,%rbx
    3d0a:	74 0c                	je     3d18 <get_filename_ext+0x28>
    return dot + 1;
    3d0c:	48 83 c0 01          	add    $0x1,%rax
}
    3d10:	5b                   	pop    %rbx
    3d11:	c3                   	ret
    3d12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    3d18:	48 8d 05 b0 33 00 00 	lea    0x33b0(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    3d1f:	5b                   	pop    %rbx
    3d20:	c3                   	ret
    3d21:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3d2c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003d30 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3d30:	f3 0f 1e fa          	endbr64
    3d34:	41 55                	push   %r13
    3d36:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3d39:	48 89 fe             	mov    %rdi,%rsi
    3d3c:	41 54                	push   %r12
    3d3e:	55                   	push   %rbp
    3d3f:	48 89 d5             	mov    %rdx,%rbp
    3d42:	ba 00 04 00 00       	mov    $0x400,%edx
    3d47:	53                   	push   %rbx
    3d48:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3d4f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3d58:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3d60:	31 c0                	xor    %eax,%eax
    3d62:	49 89 e4             	mov    %rsp,%r12
    3d65:	4c 89 e7             	mov    %r12,%rdi
    3d68:	e8 c3 e6 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    3d6d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3d72:	84 db                	test   %bl,%bl
    3d74:	74 24                	je     3d9a <send_headers+0x6a>
        *str = (char)tolower(*str);
    3d76:	e8 95 e7 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3d7b:	48 8b 08             	mov    (%rax),%rcx
    3d7e:	4c 89 e0             	mov    %r12,%rax
    3d81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3d88:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3d8b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3d8f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3d92:	48 0f be 18          	movsbq (%rax),%rbx
    3d96:	84 db                	test   %bl,%bl
    3d98:	75 ee                	jne    3d88 <send_headers+0x58>
    void *buf = malloc(size);
    3d9a:	bf 11 00 00 00       	mov    $0x11,%edi
    3d9f:	e8 6c e6 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3da4:	48 85 c0             	test   %rax,%rax
    3da7:	0f 84 7e 04 00 00    	je     422b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3dad:	66 0f 6f 05 eb 3b 00 00 	movdqa 0x3beb(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    iov[0].iov_base = zh_malloc(slen);
    3db5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    3db9:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3dbe:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3dc6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3dca:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3dcd:	e8 3e e6 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3dd2:	48 85 c0             	test   %rax,%rax
    3dd5:	0f 84 50 04 00 00    	je     422b <send_headers+0x4fb>
    3ddb:	66 0f 6f 05 cd 3b 00 00 	movdqa 0x3bcd(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    iov[1].iov_base = zh_malloc(slen);
    3de3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    3de7:	4c 89 e7             	mov    %r12,%rdi
    3dea:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3df4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3dfc:	0f 11 00             	movups %xmm0,(%rax)
    3dff:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3e03:	be 2e 00 00 00       	mov    $0x2e,%esi
    3e08:	e8 53 e5 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3e0d:	48 85 c0             	test   %rax,%rax
    3e10:	0f 84 ea 02 00 00    	je     4100 <send_headers+0x3d0>
    3e16:	4c 39 e0             	cmp    %r12,%rax
    3e19:	0f 84 e1 02 00 00    	je     4100 <send_headers+0x3d0>
    return dot + 1;
    3e1f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3e23:	48 8d 3d 73 32 00 00 	lea    0x3273(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    3e2a:	48 89 de             	mov    %rbx,%rsi
    3e2d:	e8 7e e5 ff ff       	call   23b0 <strcmp@plt>
    3e32:	85 c0                	test   %eax,%eax
    3e34:	75 20                	jne    3e56 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3e36:	66 0f 6f 05 82 3b 00 00 	movdqa 0x3b82(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    3e3e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3e46:	66 0f 6f 05 82 3b 00 00 	movdqa 0x3b82(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    3e4e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    3e56:	48 89 de             	mov    %rbx,%rsi
    3e59:	48 8d 3d 41 32 00 00 	lea    0x3241(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    3e60:	e8 4b e5 ff ff       	call   23b0 <strcmp@plt>
    3e65:	85 c0                	test   %eax,%eax
    3e67:	75 20                	jne    3e89 <send_headers+0x159>
    3e69:	66 0f 6f 05 4f 3b 00 00 	movdqa 0x3b4f(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    3e71:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3e79:	66 0f 6f 05 4f 3b 00 00 	movdqa 0x3b4f(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    3e81:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    3e89:	48 89 de             	mov    %rbx,%rsi
    3e8c:	48 8d 3d 13 32 00 00 	lea    0x3213(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    3e93:	e8 18 e5 ff ff       	call   23b0 <strcmp@plt>
    3e98:	85 c0                	test   %eax,%eax
    3e9a:	0f 84 10 02 00 00    	je     40b0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    3ea0:	48 89 de             	mov    %rbx,%rsi
    3ea3:	48 8d 3d 00 32 00 00 	lea    0x3200(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    3eaa:	e8 01 e5 ff ff       	call   23b0 <strcmp@plt>
    3eaf:	85 c0                	test   %eax,%eax
    3eb1:	0f 84 a9 02 00 00    	je     4160 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    3eb7:	48 89 de             	mov    %rbx,%rsi
    3eba:	48 8d 3d ed 31 00 00 	lea    0x31ed(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    3ec1:	e8 ea e4 ff ff       	call   23b0 <strcmp@plt>
    3ec6:	85 c0                	test   %eax,%eax
    3ec8:	0f 84 6a 02 00 00    	je     4138 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    3ece:	48 89 de             	mov    %rbx,%rsi
    3ed1:	48 8d 3d 19 32 00 00 	lea    0x3219(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    3ed8:	e8 d3 e4 ff ff       	call   23b0 <strcmp@plt>
    3edd:	85 c0                	test   %eax,%eax
    3edf:	0f 84 2b 02 00 00    	je     4110 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    3ee5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3ee8:	0f 84 52 01 00 00    	je     4040 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    3eee:	48 89 de             	mov    %rbx,%rsi
    3ef1:	48 8d 3d ba 31 00 00 	lea    0x31ba(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    3ef8:	e8 b3 e4 ff ff       	call   23b0 <strcmp@plt>
    3efd:	85 c0                	test   %eax,%eax
    3eff:	0f 84 ab 02 00 00    	je     41b0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    3f05:	48 89 de             	mov    %rbx,%rsi
    3f08:	48 8d 3d a7 31 00 00 	lea    0x31a7(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    3f0f:	e8 9c e4 ff ff       	call   23b0 <strcmp@plt>
    3f14:	85 c0                	test   %eax,%eax
    3f16:	0f 84 6c 02 00 00    	je     4188 <send_headers+0x458>
    slen = strlen(send_buffer);
    3f1c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3f24:	4c 89 e7             	mov    %r12,%rdi
    3f27:	e8 f4 e3 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    3f2c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3f2f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3f32:	e8 d9 e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3f37:	48 85 c0             	test   %rax,%rax
    3f3a:	0f 84 eb 02 00 00    	je     422b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    3f40:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    3f44:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    3f48:	83 fb 08             	cmp    $0x8,%ebx
    3f4b:	0f 83 3f 01 00 00    	jae    4090 <send_headers+0x360>
    3f51:	f6 c3 04             	test   $0x4,%bl
    3f54:	0f 85 7b 02 00 00    	jne    41d5 <send_headers+0x4a5>
    3f5a:	85 db                	test   %ebx,%ebx
    3f5c:	74 13                	je     3f71 <send_headers+0x241>
    3f5e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3f66:	88 10                	mov    %dl,(%rax)
    3f68:	f6 c3 02             	test   $0x2,%bl
    3f6b:	0f 85 96 02 00 00    	jne    4207 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3f71:	4d 89 e8             	mov    %r13,%r8
    3f74:	48 8d 0d 3f 31 00 00 	lea    0x313f(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    3f7b:	4c 89 e7             	mov    %r12,%rdi
    3f7e:	31 c0                	xor    %eax,%eax
    3f80:	ba 00 04 00 00       	mov    $0x400,%edx
    3f85:	be 01 00 00 00       	mov    $0x1,%esi
    3f8a:	e8 91 e5 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    3f8f:	4c 89 e7             	mov    %r12,%rdi
    3f92:	e8 89 e3 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    3f97:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3f9a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3f9d:	e8 6e e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3fa2:	48 85 c0             	test   %rax,%rax
    3fa5:	0f 84 80 02 00 00    	je     422b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    3fab:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    3faf:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    3fb3:	83 fb 08             	cmp    $0x8,%ebx
    3fb6:	0f 83 1c 01 00 00    	jae    40d8 <send_headers+0x3a8>
    3fbc:	f6 c3 04             	test   $0x4,%bl
    3fbf:	0f 85 29 02 00 00    	jne    41ee <send_headers+0x4be>
    3fc5:	85 db                	test   %ebx,%ebx
    3fc7:	74 13                	je     3fdc <send_headers+0x2ac>
    3fc9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3fd1:	88 10                	mov    %dl,(%rax)
    3fd3:	f6 c3 02             	test   $0x2,%bl
    3fd6:	0f 85 3d 02 00 00    	jne    4219 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3fdc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    3fe1:	bf 02 00 00 00       	mov    $0x2,%edi
    3fe6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    3fee:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    3ff6:	e8 15 e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3ffb:	48 85 c0             	test   %rax,%rax
    3ffe:	0f 84 27 02 00 00    	je     422b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4004:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    400c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4010:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4018:	66 89 10             	mov    %dx,(%rax)
}
    401b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4023:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    402c:	0f 85 20 02 00 00    	jne    4252 <send_headers+0x522>
    4032:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4039:	5b                   	pop    %rbx
    403a:	5d                   	pop    %rbp
    403b:	41 5c                	pop    %r12
    403d:	41 5d                	pop    %r13
    403f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4040:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4044:	0f 85 a4 fe ff ff    	jne    3eee <send_headers+0x1be>
    404a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    404e:	0f 85 9a fe ff ff    	jne    3eee <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4054:	66 0f 6f 05 c4 39 00 00 	movdqa 0x39c4(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    405c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4066:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    406e:	66 0f 6f 05 ba 39 00 00 	movdqa 0x39ba(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
    4076:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    407e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4086:	e9 63 fe ff ff       	jmp    3eee <send_headers+0x1be>
    408b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4090:	89 da                	mov    %ebx,%edx
    4092:	48 89 c7             	mov    %rax,%rdi
    4095:	4c 89 e6             	mov    %r12,%rsi
    4098:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    409d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    40a2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    40a5:	c1 e9 03             	shr    $0x3,%ecx
    40a8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    40ab:	e9 c1 fe ff ff       	jmp    3f71 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40b0:	66 0f 6f 05 08 39 00 00 	movdqa 0x3908(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    40b8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40c0:	66 0f 6f 05 18 39 00 00 	movdqa 0x3918(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    40c8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40d0:	e9 cb fd ff ff       	jmp    3ea0 <send_headers+0x170>
    40d5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    40d8:	89 da                	mov    %ebx,%edx
    40da:	48 89 c7             	mov    %rax,%rdi
    40dd:	4c 89 e6             	mov    %r12,%rsi
    40e0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    40e5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    40ea:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    40ed:	c1 e9 03             	shr    $0x3,%ecx
    40f0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    40f3:	e9 e4 fe ff ff       	jmp    3fdc <send_headers+0x2ac>
    40f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4100:	48 8d 1d c8 2f 00 00 	lea    0x2fc8(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4107:	e9 94 fd ff ff       	jmp    3ea0 <send_headers+0x170>
    410c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4110:	66 0f 6f 05 e8 38 00 00 	movdqa 0x38e8(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4118:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4120:	66 0f 6f 05 e8 38 00 00 	movdqa 0x38e8(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4128:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4130:	e9 b0 fd ff ff       	jmp    3ee5 <send_headers+0x1b5>
    4135:	0f 1f 00             	nopl   (%rax)
    4138:	66 0f 6f 05 c0 38 00 00 	movdqa 0x38c0(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4140:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4148:	66 0f 6f 05 c0 38 00 00 	movdqa 0x38c0(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4150:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4158:	e9 71 fd ff ff       	jmp    3ece <send_headers+0x19e>
    415d:	0f 1f 00             	nopl   (%rax)
    4160:	66 0f 6f 05 58 38 00 00 	movdqa 0x3858(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4168:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4170:	66 0f 6f 05 78 38 00 00 	movdqa 0x3878(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    4178:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4180:	e9 32 fd ff ff       	jmp    3eb7 <send_headers+0x187>
    4185:	0f 1f 00             	nopl   (%rax)
    4188:	66 0f 6f 05 70 38 00 00 	movdqa 0x3870(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4190:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4198:	66 0f 6f 05 b0 38 00 00 	movdqa 0x38b0(%rip),%xmm0        # 7a50 <_IO_stdin_used+0xa50>
    41a0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    41a8:	e9 6f fd ff ff       	jmp    3f1c <send_headers+0x1ec>
    41ad:	0f 1f 00             	nopl   (%rax)
    41b0:	66 0f 6f 05 48 38 00 00 	movdqa 0x3848(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    41b8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41c0:	66 0f 6f 05 78 38 00 00 	movdqa 0x3878(%rip),%xmm0        # 7a40 <_IO_stdin_used+0xa40>
    41c8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    41d0:	e9 30 fd ff ff       	jmp    3f05 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    41d5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    41dc:	89 db                	mov    %ebx,%ebx
    41de:	89 10                	mov    %edx,(%rax)
    41e0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    41e5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    41e9:	e9 83 fd ff ff       	jmp    3f71 <send_headers+0x241>
    41ee:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    41f5:	89 db                	mov    %ebx,%ebx
    41f7:	89 10                	mov    %edx,(%rax)
    41f9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    41fe:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4202:	e9 d5 fd ff ff       	jmp    3fdc <send_headers+0x2ac>
    4207:	89 db                	mov    %ebx,%ebx
    4209:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    420f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4214:	e9 58 fd ff ff       	jmp    3f71 <send_headers+0x241>
    4219:	89 db                	mov    %ebx,%ebx
    421b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4221:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4226:	e9 b1 fd ff ff       	jmp    3fdc <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    422b:	48 8b 0d ee 5d 00 00 	mov    0x5dee(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4232:	ba 28 00 00 00       	mov    $0x28,%edx
    4237:	be 01 00 00 00       	mov    $0x1,%esi
    423c:	48 8d 3d c5 31 00 00 	lea    0x31c5(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4243:	e8 78 e2 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4248:	bf 01 00 00 00       	mov    $0x1,%edi
    424d:	e8 4e e2 ff ff       	call   24a0 <exit@plt>
}
    4252:	e8 d9 e0 ff ff       	call   2330 <__stack_chk_fail@plt>
    4257:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004260 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4260:	f3 0f 1e fa          	endbr64
    4264:	41 55                	push   %r13
    4266:	49 89 d5             	mov    %rdx,%r13
    4269:	41 54                	push   %r12
    426b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    426e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4271:	55                   	push   %rbp
    4272:	53                   	push   %rbx
    4273:	48 89 f3             	mov    %rsi,%rbx
    4276:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    427a:	e8 91 e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    427f:	48 85 c0             	test   %rax,%rax
    4282:	74 6b                	je     42ef <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4284:	4c 89 e7             	mov    %r12,%rdi
    4287:	48 89 c5             	mov    %rax,%rbp
    428a:	31 f6                	xor    %esi,%esi
    428c:	31 c0                	xor    %eax,%eax
    428e:	e8 ed e1 ff ff       	call   2480 <open@plt>
    4293:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4296:	85 c0                	test   %eax,%eax
    4298:	0f 88 b8 e2 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    429e:	48 89 da             	mov    %rbx,%rdx
    42a1:	48 89 ee             	mov    %rbp,%rsi
    42a4:	89 c7                	mov    %eax,%edi
    42a6:	e8 e5 e0 ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    42ab:	48 98                	cltq
    42ad:	48 39 d8             	cmp    %rbx,%rax
    42b0:	7c 1e                	jl     42d0 <copy_file_contents+0x70>
    close(fd);
    42b2:	44 89 e7             	mov    %r12d,%edi
    42b5:	e8 b6 e0 ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    42ba:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    42be:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    42c2:	48 83 c4 08          	add    $0x8,%rsp
    42c6:	5b                   	pop    %rbx
    42c7:	5d                   	pop    %rbp
    42c8:	41 5c                	pop    %r12
    42ca:	41 5d                	pop    %r13
    42cc:	c3                   	ret
    42cd:	0f 1f 00             	nopl   (%rax)
    42d0:	48 8b 0d 49 5d 00 00 	mov    0x5d49(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    42d7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    42dc:	be 01 00 00 00       	mov    $0x1,%esi
    42e1:	48 8d 3d e8 2d 00 00 	lea    0x2de8(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    42e8:	e8 d3 e1 ff ff       	call   24c0 <fwrite@plt>
    42ed:	eb c3                	jmp    42b2 <copy_file_contents+0x52>
    42ef:	48 8b 0d 2a 5d 00 00 	mov    0x5d2a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    42f6:	ba 28 00 00 00       	mov    $0x28,%edx
    42fb:	be 01 00 00 00       	mov    $0x1,%esi
    4300:	48 8d 3d 01 31 00 00 	lea    0x3101(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4307:	e8 b4 e1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    430c:	bf 01 00 00 00       	mov    $0x1,%edi
    4311:	e8 8a e1 ff ff       	call   24a0 <exit@plt>
    4316:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004320 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4320:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4324:	8b 46 44             	mov    0x44(%rsi),%eax
    4327:	48 89 fa             	mov    %rdi,%rdx
    432a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    432d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4333:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4336:	48 8b 07             	mov    (%rdi),%rax
    4339:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    433c:	f6 c1 02             	test   $0x2,%cl
    433f:	74 00                	je     4341 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4341:	89 f0                	mov    %esi,%eax
    4343:	44 29 c0             	sub    %r8d,%eax
    4346:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4349:	0f 82 13 e2 ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    434f:	c1 e9 0a             	shr    $0xa,%ecx
    4352:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4356:	8b 47 44             	mov    0x44(%rdi),%eax
    4359:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    435c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    435f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4362:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4365:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4369:	d3 e0                	shl    %cl,%eax
    436b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    436e:	48 c1 e0 06          	shl    $0x6,%rax
    4372:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4376:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    437c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    437f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4383:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4389:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4391:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4395:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4398:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    439f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    43a7:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    43ab:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    43af:	e8 8c df ff ff       	call   2340 <io_uring_submit@plt>
}
    43b4:	31 c0                	xor    %eax,%eax
    43b6:	48 83 c4 08          	add    $0x8,%rsp
    43ba:	c3                   	ret
    43bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000043c0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    43c0:	f3 0f 1e fa          	endbr64
    43c4:	41 55                	push   %r13
    43c6:	41 89 fd             	mov    %edi,%r13d
    43c9:	41 54                	push   %r12
    43cb:	55                   	push   %rbp
    43cc:	53                   	push   %rbx
    43cd:	48 89 f3             	mov    %rsi,%rbx
    43d0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    43d4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    43d7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    43dd:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    43e0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    43e3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    43e5:	f6 c1 02             	test   $0x2,%cl
    43e8:	74 00                	je     43ea <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    43ea:	89 c2                	mov    %eax,%edx
    43ec:	29 f2                	sub    %esi,%edx
    43ee:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    43f1:	0f 82 7b e1 ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    43f7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    43fa:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    43fd:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4400:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4405:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4408:	23 6b 58             	and    0x58(%rbx),%ebp
    440b:	d3 e5                	shl    %cl,%ebp
    440d:	48 c1 e5 06          	shl    $0x6,%rbp
    4411:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4415:	e8 f6 df ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    441a:	be 01 00 00 00       	mov    $0x1,%esi
    441f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4424:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4427:	e8 74 df ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    442c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4431:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4435:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4438:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    443d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4442:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    444b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4453:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4457:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    445b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4462:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    446a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    446e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4476:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    447e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4482:	e8 b9 de ff ff       	call   2340 <io_uring_submit@plt>
}
    4487:	48 83 c4 08          	add    $0x8,%rsp
    448b:	31 c0                	xor    %eax,%eax
    448d:	5b                   	pop    %rbx
    448e:	5d                   	pop    %rbp
    448f:	41 5c                	pop    %r12
    4491:	41 5d                	pop    %r13
    4493:	c3                   	ret
    4494:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    449f:	90                   	nop

00000000000044a0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    44a0:	f3 0f 1e fa          	endbr64
    44a4:	41 56                	push   %r14
    44a6:	41 89 f6             	mov    %esi,%r14d
    44a9:	41 55                	push   %r13
    44ab:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    44ae:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    44b3:	41 54                	push   %r12
    44b5:	55                   	push   %rbp
    44b6:	48 89 d5             	mov    %rdx,%rbp
    44b9:	53                   	push   %rbx
    void *buf = malloc(size);
    44ba:	e8 51 df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    44bf:	48 85 c0             	test   %rax,%rax
    44c2:	0f 84 dd 00 00 00    	je     45a5 <_send_static_string_content+0x105>
    44c8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    44cb:	4c 89 ef             	mov    %r13,%rdi
    44ce:	e8 4d de ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    44d3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    44da:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    44de:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    44e1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    44e4:	e8 27 df ff ff       	call   2410 <malloc@plt>
    44e9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    44ec:	48 85 c0             	test   %rax,%rax
    44ef:	0f 84 b0 00 00 00    	je     45a5 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    44f5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    44f9:	4c 89 e2             	mov    %r12,%rdx
    44fc:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    44ff:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4503:	e8 d8 de ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4508:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    450b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4511:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4514:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4518:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    451a:	f6 c1 02             	test   $0x2,%cl
    451d:	0f 85 7d 00 00 00    	jne    45a0 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4523:	89 d0                	mov    %edx,%eax
    4525:	29 f0                	sub    %esi,%eax
    4527:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    452a:	0f 82 4c e0 ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4530:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4533:	8b 45 44             	mov    0x44(%rbp),%eax
    4536:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4539:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    453c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    453f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4542:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4548:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    454c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    454e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4551:	48 89 ef             	mov    %rbp,%rdi
    4554:	48 c1 e0 06          	shl    $0x6,%rax
    4558:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    455c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    455f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4563:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4569:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4571:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4575:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4578:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    457f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4587:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    458b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    458f:	5b                   	pop    %rbx
    4590:	5d                   	pop    %rbp
    4591:	41 5c                	pop    %r12
    4593:	41 5d                	pop    %r13
    4595:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4597:	e9 a4 dd ff ff       	jmp    2340 <io_uring_submit@plt>
    459c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    45a0:	e9 7e ff ff ff       	jmp    4523 <_send_static_string_content+0x83>
    45a5:	48 8b 0d 74 5a 00 00 	mov    0x5a74(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    45ac:	ba 28 00 00 00       	mov    $0x28,%edx
    45b1:	be 01 00 00 00       	mov    $0x1,%esi
    45b6:	48 8d 3d 4b 2e 00 00 	lea    0x2e4b(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    45bd:	e8 fe de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    45c2:	bf 01 00 00 00       	mov    $0x1,%edi
    45c7:	e8 d4 de ff ff       	call   24a0 <exit@plt>
    45cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000045d0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    45d0:	f3 0f 1e fa          	endbr64
    45d4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    45d7:	89 fe                	mov    %edi,%esi
    45d9:	48 8b 3d 38 5a 00 00 	mov    0x5a38(%rip),%rdi        # a018 <unimplemented_content>
    45e0:	e9 bb fe ff ff       	jmp    44a0 <_send_static_string_content>
    45e5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000045f0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    45f0:	f3 0f 1e fa          	endbr64
    45f4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    45f7:	89 fe                	mov    %edi,%esi
    45f9:	48 8b 3d 10 5a 00 00 	mov    0x5a10(%rip),%rdi        # a010 <http_404_content>
    4600:	e9 9b fe ff ff       	jmp    44a0 <_send_static_string_content>
    4605:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004610 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4610:	f3 0f 1e fa          	endbr64
    4614:	41 56                	push   %r14
    4616:	41 55                	push   %r13
    4618:	49 89 d5             	mov    %rdx,%r13
    461b:	41 54                	push   %r12
    461d:	41 89 f4             	mov    %esi,%r12d
    4620:	55                   	push   %rbp
    4621:	48 89 fd             	mov    %rdi,%rbp
    4624:	53                   	push   %rbx
    4625:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    462c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4635:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    463d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    463f:	e8 dc dc ff ff       	call   2320 <strlen@plt>
    4644:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4649:	48 89 c3             	mov    %rax,%rbx
    464c:	0f 84 b6 00 00 00    	je     4708 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4652:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4657:	48 89 ee             	mov    %rbp,%rsi
    465a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    465e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4663:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    466b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4673:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    467e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4686:	e8 35 dd ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    468b:	48 89 e6             	mov    %rsp,%rsi
    468e:	4c 89 f7             	mov    %r14,%rdi
    4691:	e8 3a dd ff ff       	call   23d0 <stat@plt>
    4696:	83 f8 ff             	cmp    $0xffffffff,%eax
    4699:	0f 84 d3 00 00 00    	je     4772 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    469f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    46a3:	25 00 f0 00 00       	and    $0xf000,%eax
    46a8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    46ad:	0f 84 f5 00 00 00    	je     47a8 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    46b3:	48 8b 3d 56 59 00 00 	mov    0x5956(%rip),%rdi        # a010 <http_404_content>
    46ba:	4c 89 ea             	mov    %r13,%rdx
    46bd:	44 89 e6             	mov    %r12d,%esi
    46c0:	e8 db fd ff ff       	call   44a0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    46c5:	4c 89 f2             	mov    %r14,%rdx
    46c8:	bf 01 00 00 00       	mov    $0x1,%edi
    46cd:	31 c0                	xor    %eax,%eax
    46cf:	48 8d 35 4a 2a 00 00 	lea    0x2a4a(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    46d6:	e8 75 dd ff ff       	call   2450 <__printf_chk@plt>
}
    46db:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    46e3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    46ec:	0f 85 20 01 00 00    	jne    4812 <handle_get_method+0x202>
    46f2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    46f9:	5b                   	pop    %rbx
    46fa:	5d                   	pop    %rbp
    46fb:	41 5c                	pop    %r12
    46fd:	41 5d                	pop    %r13
    46ff:	41 5e                	pop    %r14
    4701:	c3                   	ret
    4702:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4708:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    470d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4715:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    471a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    471d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4725:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4728:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4730:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    473b:	e8 80 dc ff ff       	call   23c0 <__memcpy_chk@plt>
    4740:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4745:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    474a:	48 8d 35 9a 29 00 00 	lea    0x299a(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4751:	48 29 d9             	sub    %rbx,%rcx
    4754:	ba 0b 00 00 00       	mov    $0xb,%edx
    4759:	e8 62 dc ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    475e:	48 89 e6             	mov    %rsp,%rsi
    4761:	4c 89 f7             	mov    %r14,%rdi
    4764:	e8 67 dc ff ff       	call   23d0 <stat@plt>
    4769:	83 f8 ff             	cmp    $0xffffffff,%eax
    476c:	0f 85 2d ff ff ff    	jne    469f <handle_get_method+0x8f>
    4772:	4c 89 f2             	mov    %r14,%rdx
    4775:	48 89 e9             	mov    %rbp,%rcx
    4778:	48 8d 35 77 29 00 00 	lea    0x2977(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    477f:	31 c0                	xor    %eax,%eax
    4781:	bf 01 00 00 00       	mov    $0x1,%edi
    4786:	e8 c5 dc ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    478b:	48 8b 3d 7e 58 00 00 	mov    0x587e(%rip),%rdi        # a010 <http_404_content>
    4792:	4c 89 ea             	mov    %r13,%rdx
    4795:	44 89 e6             	mov    %r12d,%esi
    4798:	e8 03 fd ff ff       	call   44a0 <_send_static_string_content>
}
    479d:	e9 39 ff ff ff       	jmp    46db <handle_get_method+0xcb>
    47a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    47a8:	bf 70 00 00 00       	mov    $0x70,%edi
    47ad:	e8 5e dc ff ff       	call   2410 <malloc@plt>
    47b2:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    47b5:	48 85 c0             	test   %rax,%rax
    47b8:	74 5d                	je     4817 <handle_get_method+0x207>
            req->client_socket = client_socket;
    47ba:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    47be:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    47c3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    47c7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    47ca:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    47d1:	e8 5a f5 ff ff       	call   3d30 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    47d6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    47db:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    47df:	4c 89 f7             	mov    %r14,%rdi
    47e2:	e8 79 fa ff ff       	call   4260 <copy_file_contents>
    47e7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    47ec:	4c 89 f2             	mov    %r14,%rdx
    47ef:	31 c0                	xor    %eax,%eax
    47f1:	48 8d 35 16 29 00 00 	lea    0x2916(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    47f8:	bf 01 00 00 00       	mov    $0x1,%edi
    47fd:	e8 4e dc ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    4802:	4c 89 ee             	mov    %r13,%rsi
    4805:	48 89 df             	mov    %rbx,%rdi
    4808:	e8 13 fb ff ff       	call   4320 <add_write_request>
    480d:	e9 c9 fe ff ff       	jmp    46db <handle_get_method+0xcb>
}
    4812:	e8 19 db ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4817:	48 8b 0d 02 58 00 00 	mov    0x5802(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    481e:	ba 28 00 00 00       	mov    $0x28,%edx
    4823:	be 01 00 00 00       	mov    $0x1,%esi
    4828:	48 8d 3d d9 2b 00 00 	lea    0x2bd9(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    482f:	e8 8c dc ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4834:	bf 01 00 00 00       	mov    $0x1,%edi
    4839:	e8 62 dc ff ff       	call   24a0 <exit@plt>
    483e:	66 90                	xchg   %ax,%ax

0000000000004840 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4840:	f3 0f 1e fa          	endbr64
    4844:	41 57                	push   %r15
    4846:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4848:	4c 8d 35 36 28 00 00 	lea    0x2836(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    484f:	41 55                	push   %r13
    4851:	49 89 d5             	mov    %rdx,%r13
    4854:	41 54                	push   %r12
    4856:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4859:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    485c:	55                   	push   %rbp
    485d:	53                   	push   %rbx
    485e:	48 83 ec 18          	sub    $0x18,%rsp
    4862:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    486b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4870:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4872:	49 89 e7             	mov    %rsp,%r15
    4875:	4c 89 fa             	mov    %r15,%rdx
    4878:	e8 03 db ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    487d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4881:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4884:	84 db                	test   %bl,%bl
    4886:	74 1d                	je     48a5 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4888:	e8 83 dc ff ff       	call   2510 <__ctype_tolower_loc@plt>
    488d:	48 89 ea             	mov    %rbp,%rdx
    4890:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4893:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4897:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    489a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    489d:	48 0f be 1a          	movsbq (%rdx),%rbx
    48a1:	84 db                	test   %bl,%bl
    48a3:	75 eb                	jne    4890 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    48a5:	4c 89 fa             	mov    %r15,%rdx
    48a8:	4c 89 f6             	mov    %r14,%rsi
    48ab:	31 ff                	xor    %edi,%edi
    48ad:	e8 ce da ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    48b2:	48 8d 35 7a 28 00 00 	lea    0x287a(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    48b9:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    48bc:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    48bf:	e8 ec da ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    48c4:	4c 89 ea             	mov    %r13,%rdx
    48c7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    48ca:	85 c0                	test   %eax,%eax
    48cc:	75 2a                	jne    48f8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    48ce:	48 89 df             	mov    %rbx,%rdi
    48d1:	e8 3a fd ff ff       	call   4610 <handle_get_method>
}
    48d6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    48db:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    48e4:	75 20                	jne    4906 <handle_http_method+0xc6>
    48e6:	48 83 c4 18          	add    $0x18,%rsp
    48ea:	5b                   	pop    %rbx
    48eb:	5d                   	pop    %rbp
    48ec:	41 5c                	pop    %r12
    48ee:	41 5d                	pop    %r13
    48f0:	41 5e                	pop    %r14
    48f2:	41 5f                	pop    %r15
    48f4:	c3                   	ret
    48f5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    48f8:	48 8b 3d 19 57 00 00 	mov    0x5719(%rip),%rdi        # a018 <unimplemented_content>
    48ff:	e8 9c fb ff ff       	call   44a0 <_send_static_string_content>
}
    4904:	eb d0                	jmp    48d6 <handle_http_method+0x96>
    4906:	e8 25 da ff ff       	call   2330 <__stack_chk_fail@plt>
    490b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004910 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4910:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4914:	85 d2                	test   %edx,%edx
    4916:	7e 38                	jle    4950 <get_line+0x40>
    4918:	48 63 d2             	movslq %edx,%rdx
    491b:	48 83 c7 01          	add    $0x1,%rdi
    491f:	48 01 f2             	add    %rsi,%rdx
    4922:	eb 11                	jmp    4935 <get_line+0x25>
    4924:	0f 1f 40 00          	nopl   0x0(%rax)
    4928:	48 83 c6 01          	add    $0x1,%rsi
    492c:	48 83 c7 01          	add    $0x1,%rdi
    4930:	48 39 d6             	cmp    %rdx,%rsi
    4933:	74 1b                	je     4950 <get_line+0x40>
        dest[i] = src[i];
    4935:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4939:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    493b:	3c 0d                	cmp    $0xd,%al
    493d:	75 e9                	jne    4928 <get_line+0x18>
    493f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4942:	75 e4                	jne    4928 <get_line+0x18>
            dest[i] = '\0';
    4944:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4947:	31 c0                	xor    %eax,%eax
    4949:	c3                   	ret
    494a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4950:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4955:	c3                   	ret
    4956:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004960 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4960:	f3 0f 1e fa          	endbr64
    4964:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    496b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    496f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4978:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4980:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4982:	49 89 e2             	mov    %rsp,%r10
    4985:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    498d:	4c 89 d0             	mov    %r10,%rax
    4990:	eb 13                	jmp    49a5 <handle_client_request+0x45>
    4992:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4998:	48 83 c0 01          	add    $0x1,%rax
    499c:	48 83 c1 01          	add    $0x1,%rcx
    49a0:	4c 39 c8             	cmp    %r9,%rax
    49a3:	74 4b                	je     49f0 <handle_client_request+0x90>
        dest[i] = src[i];
    49a5:	44 0f b6 01          	movzbl (%rcx),%r8d
    49a9:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    49ac:	41 80 f8 0d          	cmp    $0xd,%r8b
    49b0:	75 e6                	jne    4998 <handle_client_request+0x38>
    49b2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    49b6:	75 e0                	jne    4998 <handle_client_request+0x38>
            dest[i] = '\0';
    49b8:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    49bb:	8b 47 08             	mov    0x8(%rdi),%eax
    49be:	48 89 f2             	mov    %rsi,%rdx
    49c1:	4c 89 d7             	mov    %r10,%rdi
    49c4:	89 c6                	mov    %eax,%esi
    49c6:	e8 75 fe ff ff       	call   4840 <handle_http_method>
}
    49cb:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    49d3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    49dc:	75 39                	jne    4a17 <handle_client_request+0xb7>
    49de:	31 c0                	xor    %eax,%eax
    49e0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    49e7:	c3                   	ret
    49e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    49f0:	48 8b 0d 29 56 00 00 	mov    0x5629(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    49f7:	ba 12 00 00 00       	mov    $0x12,%edx
    49fc:	be 01 00 00 00       	mov    $0x1,%esi
    4a01:	48 8d 3d 2f 27 00 00 	lea    0x272f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4a08:	e8 b3 da ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4a0d:	bf 01 00 00 00       	mov    $0x1,%edi
    4a12:	e8 89 da ff ff       	call   24a0 <exit@plt>
}
    4a17:	e8 14 d9 ff ff       	call   2330 <__stack_chk_fail@plt>
    4a1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a20 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4a20:	f3 0f 1e fa          	endbr64
    4a24:	55                   	push   %rbp
    4a25:	53                   	push   %rbx
    4a26:	48 89 cb             	mov    %rcx,%rbx
    4a29:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4a2d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4a30:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4a33:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4a39:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4a3c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4a3f:	f6 c1 02             	test   $0x2,%cl
    4a42:	74 00                	je     4a44 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4a44:	41 89 c0             	mov    %eax,%r8d
    4a47:	45 29 c8             	sub    %r9d,%r8d
    4a4a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4a4e:	0f 82 38 db ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4a54:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4a57:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4a5a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4a5d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4a60:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4a63:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4a67:	d3 e5                	shl    %cl,%ebp
    4a69:	48 c1 e5 06          	shl    $0x6,%rbp
    4a6d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4a71:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4a74:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4a79:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4a80:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4a84:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4a88:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4a90:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4a98:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4a9c:	e8 6f d9 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4aa1:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4aa4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4aaa:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4aae:	48 83 c4 08          	add    $0x8,%rsp
    4ab2:	5b                   	pop    %rbx
    4ab3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4ab4:	e9 87 d8 ff ff       	jmp    2340 <io_uring_submit@plt>
    4ab9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004ac0 <io_thread>:
void* io_thread(void *arg) {
    4ac0:	f3 0f 1e fa          	endbr64
    4ac4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4ac6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4ac8:	41 56                	push   %r14
    4aca:	41 55                	push   %r13
    4acc:	41 54                	push   %r12
    4ace:	55                   	push   %rbp
    4acf:	48 89 fd             	mov    %rdi,%rbp
    4ad2:	53                   	push   %rbx
    4ad3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4ada:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4ae3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4aeb:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4aef:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4af4:	bf 00 01 00 00       	mov    $0x100,%edi
    4af9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4afc:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4b00:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4b05:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4b0a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4b0f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4b14:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4b1c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4b21:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4b29:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4b2e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4b36:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4b3b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4b43:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4b48:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4b50:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4b55:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4b5d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4b65:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4b6d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4b75:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4b7d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4b85:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4b8d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4b95:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4b9d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4ba5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4bad:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4bb4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4bbc:	e8 2f d8 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4bc1:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
    4bc5:	31 f6                	xor    %esi,%esi
    4bc7:	e8 14 d9 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4bcc:	31 d2                	xor    %edx,%edx
    4bce:	be 01 00 00 00       	mov    $0x1,%esi
    4bd3:	bf 02 00 00 00       	mov    $0x2,%edi
    4bd8:	e8 53 d9 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4bdd:	83 f8 ff             	cmp    $0xffffffff,%eax
    4be0:	0f 84 e8 d9 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    4be6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4beb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4bf1:	89 c7                	mov    %eax,%edi
    4bf3:	41 89 c4             	mov    %eax,%r12d
    4bf6:	ba 02 00 00 00       	mov    $0x2,%edx
    4bfb:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4c00:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4c08:	e8 f3 d6 ff ff       	call   2300 <setsockopt@plt>
    4c0d:	85 c0                	test   %eax,%eax
    4c0f:	0f 88 8d d9 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4c15:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4c1a:	ba 10 00 00 00       	mov    $0x10,%edx
    4c1f:	44 89 e7             	mov    %r12d,%edi
    4c22:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4c2b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4c33:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4c3b:	e8 20 d8 ff ff       	call   2460 <bind@plt>
    4c40:	85 c0                	test   %eax,%eax
    4c42:	0f 88 92 d9 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4c48:	be 0a 00 00 00       	mov    $0xa,%esi
    4c4d:	44 89 e7             	mov    %r12d,%edi
    4c50:	e8 cb d7 ff ff       	call   2420 <listen@plt>
    4c55:	85 c0                	test   %eax,%eax
    4c57:	0f 88 51 d9 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4c5d:	ba db 18 00 00       	mov    $0x18db,%edx
    4c62:	48 8d 35 13 25 00 00 	lea    0x2513(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4c69:	bf 01 00 00 00       	mov    $0x1,%edi
    4c6e:	31 c0                	xor    %eax,%eax
    4c70:	e8 db d7 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4c75:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4c7a:	48 89 d9             	mov    %rbx,%rcx
    4c7d:	44 89 e7             	mov    %r12d,%edi
    4c80:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4c85:	48 89 c6             	mov    %rax,%rsi
    4c88:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4c8d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4c92:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4c9a:	e8 81 fd ff ff       	call   4a20 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4c9f:	bf 01 00 00 00       	mov    $0x1,%edi
    4ca4:	be 10 00 00 00       	mov    $0x10,%esi
    4ca9:	e8 f2 d6 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    4cae:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4cb3:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4cb6:	e8 55 d7 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4cbb:	48 85 c0             	test   %rax,%rax
    4cbe:	0f 84 ae 04 00 00    	je     5172 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    4cc4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4cc8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4ccf:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    4cd6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4cde:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4ce1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4ce6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4ce8:	f6 c1 02             	test   $0x2,%cl
    4ceb:	0f 85 0f 04 00 00    	jne    5100 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    4cf1:	89 d0                	mov    %edx,%eax
    4cf3:	29 f0                	sub    %esi,%eax
    4cf5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4cfc:	0f 82 c2 d8 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4d02:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4d05:	48 8d 75 50          	lea    0x50(%rbp),%rsi
	sqe->addr3 = 0;
    4d09:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4d0d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d10:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4d17:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d1a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4d21:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d28:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4d2a:	8b 55 50             	mov    0x50(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4d2d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4d32:	48 c1 e0 06          	shl    $0x6,%rax
    4d36:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4d3e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4d44:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4d47:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4d4f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4d53:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4d5b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4d63:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4d67:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4d6b:	e8 d0 d5 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4d70:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4d74:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4d79:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4d81:	0f 85 d7 01 00 00    	jne    4f5e <io_thread+0x49e>
    4d87:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4d8c:	4d 89 ce             	mov    %r9,%r14
    4d8f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4d94:	0f 1f 40 00          	nopl   0x0(%rax)
    4d98:	48 8d 3d f3 23 00 00 	lea    0x23f3(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    4d9f:	e8 4c d5 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4da4:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4dab:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4db2:	c1 e9 0b             	shr    $0xb,%ecx
    4db5:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4db8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4dc0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4dc2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4dca:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4dcc:	39 d0                	cmp    %edx,%eax
    4dce:	74 36                	je     4e06 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4dd0:	89 f8                	mov    %edi,%eax
    4dd2:	21 d0                	and    %edx,%eax
    4dd4:	d3 e0                	shl    %cl,%eax
    4dd6:	48 c1 e0 04          	shl    $0x4,%rax
    4dda:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4de2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4dea:	0f 85 a8 01 00 00    	jne    4f98 <io_thread+0x4d8>
    4df0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4df4:	0f 85 0e 03 00 00    	jne    5108 <io_thread+0x648>
			if (cqe->res < 0)
    4dfa:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4dfd:	83 c2 01             	add    $0x1,%edx
    4e00:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4e02:	85 c0                	test   %eax,%eax
    4e04:	79 b2                	jns    4db8 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    4e06:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    4e0f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4e10:	45 31 c0             	xor    %r8d,%r8d
    4e13:	31 d2                	xor    %edx,%edx
    4e15:	b9 01 00 00 00       	mov    $0x1,%ecx
    4e1a:	4c 89 f6             	mov    %r14,%rsi
    4e1d:	48 89 df             	mov    %rbx,%rdi
    4e20:	e8 1b d6 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    4e25:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    4e28:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4e2d:	48 83 38 01          	cmpq   $0x1,(%rax)
    4e31:	0f 84 e1 02 00 00    	je     5118 <io_thread+0x658>
    4e37:	48 8d 3d 7a 23 00 00 	lea    0x237a(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    4e3e:	e8 ad d4 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4e43:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4e48:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4e4b:	45 85 ff             	test   %r15d,%r15d
    4e4e:	0f 88 42 d7 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    4e54:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    4e57:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    4e5b:	85 c0                	test   %eax,%eax
    4e5d:	0f 88 d5 02 00 00    	js     5138 <io_thread+0x678>
      switch (req->event_type) {
    4e63:	41 83 f8 01          	cmp    $0x1,%r8d
    4e67:	0f 84 7b 01 00 00    	je     4fe8 <io_thread+0x528>
    4e6d:	41 83 f8 02          	cmp    $0x2,%r8d
    4e71:	0f 84 a1 01 00 00    	je     5018 <io_thread+0x558>
    4e77:	45 85 c0             	test   %r8d,%r8d
    4e7a:	0f 85 50 01 00 00    	jne    4fd0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4e80:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    4e85:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    4e8a:	48 89 d9             	mov    %rbx,%rcx
    4e8d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4e91:	e8 8a fb ff ff       	call   4a20 <add_accept_request>
              add_read_request(cqe->res, &ring);
    4e96:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4e9b:	48 89 de             	mov    %rbx,%rsi
    4e9e:	8b 78 08             	mov    0x8(%rax),%edi
    4ea1:	e8 1a f5 ff ff       	call   43c0 <add_read_request>
              free(req);
    4ea6:	4c 89 e7             	mov    %r12,%rdi
    4ea9:	e8 12 d4 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4eae:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    4eb3:	48 85 c0             	test   %rax,%rax
    4eb6:	0f 85 14 01 00 00    	jne    4fd0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    4ebc:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4ec3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4eca:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4ecd:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4ed2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4ed4:	f6 c1 02             	test   $0x2,%cl
    4ed7:	74 00                	je     4ed9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    4ed9:	89 d0                	mov    %edx,%eax
    4edb:	29 f0                	sub    %esi,%eax
    4edd:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4ee4:	0f 82 d0 d6 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    4eea:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    4eed:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    4ef2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    4ef6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ef9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4f00:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4f03:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4f0a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4f11:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4f13:	8b 55 50             	mov    0x50(%rbp),%edx
    4f16:	48 c1 e0 06          	shl    $0x6,%rax
    4f1a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4f22:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4f28:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4f2b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4f33:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4f37:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4f3f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4f47:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4f4b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    4f4f:	e8 ec d3 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4f54:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    4f58:	0f 84 3a fe ff ff    	je     4d98 <io_thread+0x2d8>
    4f5e:	48 8d 3d 8c 22 00 00 	lea    0x228c(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    4f65:	e8 86 d3 ff ff       	call   22f0 <puts@plt>
}
    4f6a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    4f72:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4f7b:	0f 85 18 02 00 00    	jne    5199 <io_thread+0x6d9>
    4f81:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    4f88:	31 c0                	xor    %eax,%eax
    4f8a:	5b                   	pop    %rbx
    4f8b:	5d                   	pop    %rbp
    4f8c:	41 5c                	pop    %r12
    4f8e:	41 5d                	pop    %r13
    4f90:	41 5e                	pop    %r14
    4f92:	41 5f                	pop    %r15
    4f94:	c3                   	ret
    4f95:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    4f98:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    4f9d:	48 85 c0             	test   %rax,%rax
    4fa0:	0f 84 6a fe ff ff    	je     4e10 <io_thread+0x350>
      if (cqe->user_data == 1) {
    4fa6:	48 83 38 01          	cmpq   $0x1,(%rax)
    4faa:	0f 84 68 01 00 00    	je     5118 <io_thread+0x658>
    4fb0:	48 8d 3d 01 22 00 00 	lea    0x2201(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    4fb7:	e8 34 d3 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4fbc:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4fc1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4fc4:	e9 8b fe ff ff       	jmp    4e54 <io_thread+0x394>
    4fc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4fd0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4fd8:	8b 02                	mov    (%rdx),%eax
    4fda:	83 c0 01             	add    $0x1,%eax
    4fdd:	89 02                	mov    %eax,(%rdx)
}
    4fdf:	e9 d8 fe ff ff       	jmp    4ebc <io_thread+0x3fc>
    4fe4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    4fe8:	85 c0                	test   %eax,%eax
    4fea:	75 74                	jne    5060 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4fec:	48 8b 0d 2d 50 00 00 	mov    0x502d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4ff3:	ba 0f 00 00 00       	mov    $0xf,%edx
    4ff8:	be 01 00 00 00       	mov    $0x1,%esi
    4ffd:	48 8d 3d dd 21 00 00 	lea    0x21dd(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    5004:	e8 b7 d4 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5009:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    500e:	e9 a0 fe ff ff       	jmp    4eb3 <io_thread+0x3f3>
    5013:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5018:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    501d:	45 31 ff             	xor    %r15d,%r15d
    5020:	85 c0                	test   %eax,%eax
    5022:	7e 20                	jle    5044 <io_thread+0x584>
    5024:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5028:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    502b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    502f:	48 c1 e0 04          	shl    $0x4,%rax
    5033:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5038:	e8 83 d2 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    503d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5042:	7f e4                	jg     5028 <io_thread+0x568>
              close(req->client_socket);
    5044:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5049:	e8 22 d3 ff ff       	call   2370 <close@plt>
              free(req);
    504e:	4c 89 e7             	mov    %r12,%rdi
    5051:	e8 6a d2 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5056:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    505b:	e9 53 fe ff ff       	jmp    4eb3 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5060:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5065:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    506a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5072:	eb 11                	jmp    5085 <io_thread+0x5c5>
    5074:	0f 1f 40 00          	nopl   0x0(%rax)
    5078:	48 83 c0 01          	add    $0x1,%rax
    507c:	48 83 c2 01          	add    $0x1,%rdx
    5080:	48 39 c6             	cmp    %rax,%rsi
    5083:	74 4b                	je     50d0 <io_thread+0x610>
        dest[i] = src[i];
    5085:	0f b6 0a             	movzbl (%rdx),%ecx
    5088:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    508a:	80 f9 0d             	cmp    $0xd,%cl
    508d:	75 e9                	jne    5078 <io_thread+0x5b8>
    508f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5093:	75 e3                	jne    5078 <io_thread+0x5b8>
            dest[i] = '\0';
    5095:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5098:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    509d:	48 89 da             	mov    %rbx,%rdx
    50a0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    50a5:	e8 96 f7 ff ff       	call   4840 <handle_http_method>
              free(req->iov[0].iov_base);
    50aa:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    50af:	e8 0c d2 ff ff       	call   22c0 <free@plt>
              free(req);
    50b4:	4c 89 e7             	mov    %r12,%rdi
    50b7:	e8 04 d2 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    50bc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    50c1:	e9 ed fd ff ff       	jmp    4eb3 <io_thread+0x3f3>
    50c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    50d0:	48 8b 0d 49 4f 00 00 	mov    0x4f49(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    50d7:	ba 12 00 00 00       	mov    $0x12,%edx
    50dc:	be 01 00 00 00       	mov    $0x1,%esi
    50e1:	48 8d 3d 4f 20 00 00 	lea    0x204f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    50e8:	e8 d3 d3 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    50ed:	bf 01 00 00 00       	mov    $0x1,%edi
    50f2:	e8 a9 d3 ff ff       	call   24a0 <exit@plt>
    50f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5100:	e9 ec fb ff ff       	jmp    4cf1 <io_thread+0x231>
    5105:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5108:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    510d:	e9 94 fe ff ff       	jmp    4fa6 <io_thread+0x4e6>
    5112:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5118:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5120:	48 8d 3d 7d 20 00 00 	lea    0x207d(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    5127:	8b 02                	mov    (%rdx),%eax
    5129:	83 c0 01             	add    $0x1,%eax
    512c:	89 02                	mov    %eax,(%rdx)
    512e:	e8 bd d1 ff ff       	call   22f0 <puts@plt>
    5133:	e9 26 fe ff ff       	jmp    4f5e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5138:	f7 d8                	neg    %eax
    513a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    513f:	89 c7                	mov    %eax,%edi
    5141:	e8 ba d3 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5146:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    514b:	be 01 00 00 00       	mov    $0x1,%esi
    5150:	48 8b 3d c9 4e 00 00 	mov    0x4ec9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5157:	48 89 c1             	mov    %rax,%rcx
    515a:	48 8d 15 d7 22 00 00 	lea    0x22d7(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    5161:	31 c0                	xor    %eax,%eax
    5163:	e8 68 d3 ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5168:	bf 01 00 00 00       	mov    $0x1,%edi
    516d:	e8 2e d3 ff ff       	call   24a0 <exit@plt>
    5172:	48 8b 0d a7 4e 00 00 	mov    0x4ea7(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5179:	ba 28 00 00 00       	mov    $0x28,%edx
    517e:	be 01 00 00 00       	mov    $0x1,%esi
    5183:	48 8d 3d 7e 22 00 00 	lea    0x227e(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    518a:	e8 31 d3 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    518f:	bf 01 00 00 00       	mov    $0x1,%edi
    5194:	e8 07 d3 ff ff       	call   24a0 <exit@plt>
}
    5199:	e8 92 d1 ff ff       	call   2330 <__stack_chk_fail@plt>
    519e:	66 90                	xchg   %ax,%ax

00000000000051a0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    51a0:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    51a4:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    51ab:	8b 8e ac 00 00 00    	mov    0xac(%rsi),%ecx
    51b1:	85 c9                	test   %ecx,%ecx
    51b3:	0f 8e ea 00 00 00    	jle    52a3 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    51b9:	41 56                	push   %r14
    51bb:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    51bd:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    51c0:	41 54                	push   %r12
    51c2:	49 89 fc             	mov    %rdi,%r12
    51c5:	55                   	push   %rbp
    51c6:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    51c7:	48 8b 7e 40          	mov    0x40(%rsi),%rdi
    51cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    51d0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    51d4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    51dc:	31 db                	xor    %ebx,%ebx
    51de:	8b 10                	mov    (%rax),%edx
    51e0:	85 d2                	test   %edx,%edx
    51e2:	7e 26                	jle    520a <barriered_work_ingest+0x6a>
    51e4:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    51e8:	48 89 dd             	mov    %rbx,%rbp
    51eb:	48 c1 e5 08          	shl    $0x8,%rbp
    51ef:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    51f3:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    51fa:	74 24                	je     5220 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    51fc:	48 83 c3 01          	add    $0x1,%rbx
    5200:	39 da                	cmp    %ebx,%edx
    5202:	7f e4                	jg     51e8 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5204:	8b 8e ac 00 00 00    	mov    0xac(%rsi),%ecx
    520a:	49 83 c5 01          	add    $0x1,%r13
    520e:	44 39 e9             	cmp    %r13d,%ecx
    5211:	7f bd                	jg     51d0 <barriered_work_ingest+0x30>
}
    5213:	5b                   	pop    %rbx
    5214:	31 c0                	xor    %eax,%eax
    5216:	5d                   	pop    %rbp
    5217:	41 5c                	pop    %r12
    5219:	41 5d                	pop    %r13
    521b:	41 5e                	pop    %r14
    521d:	c3                   	ret
    521e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    5220:	49 83 84 24 60 01 00 00 01 	addq   $0x1,0x160(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    5229:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5230:	bf 04 00 00 00       	mov    $0x4,%edi
    5235:	48 c1 e6 05          	shl    $0x5,%rsi
    5239:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5240:	48 83 c6 10          	add    $0x10,%rsi
    5244:	e8 c7 d0 ff ff       	call   2310 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5249:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5251:	48 8b 40 40          	mov    0x40(%rax),%rax
    5255:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5259:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    525d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5267:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    526d:	83 c0 01             	add    $0x1,%eax
    5270:	99                   	cltd
    5271:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5277:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    527d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5280:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5288:	48 83 c3 01          	add    $0x1,%rbx
    528c:	48 8b 7e 40          	mov    0x40(%rsi),%rdi
    5290:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5294:	8b 10                	mov    (%rax),%edx
    5296:	39 da                	cmp    %ebx,%edx
    5298:	0f 8f 46 ff ff ff    	jg     51e4 <barriered_work_ingest+0x44>
    529e:	e9 61 ff ff ff       	jmp    5204 <barriered_work_ingest+0x64>
}
    52a3:	31 c0                	xor    %eax,%eax
    52a5:	c3                   	ret
    52a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000052b0 <barriered_thread>:
void* barriered_thread(void *arg) {
    52b0:	f3 0f 1e fa          	endbr64
    52b4:	41 56                	push   %r14
    52b6:	41 55                	push   %r13
    52b8:	41 54                	push   %r12
  int t = 0;
    52ba:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    52bd:	55                   	push   %rbp
  int waiting = 0;
    52be:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    52c0:	53                   	push   %rbx
    52c1:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    52c4:	83 7b 34 01          	cmpl   $0x1,0x34(%rbx)
    52c8:	0f 85 64 02 00 00    	jne    5532 <barriered_thread+0x282>
    if (t >= data->task_count) {
    52ce:	8b 43 30             	mov    0x30(%rbx),%eax
    52d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    52d8:	41 39 c4             	cmp    %eax,%r12d
    52db:	0f 8d 67 01 00 00    	jge    5448 <barriered_thread+0x198>
    52e1:	49 63 fc             	movslq %r12d,%rdi
    52e4:	48 c1 e7 09          	shl    $0x9,%rdi
    52e8:	49 89 fd             	mov    %rdi,%r13
    52eb:	eb 31                	jmp    531e <barriered_thread+0x6e>
    52ed:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    52f0:	48 63 13             	movslq (%rbx),%rdx
    52f3:	48 8b 43 10          	mov    0x10(%rbx),%rax
    52f7:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    52fb:	48 8b 78 28          	mov    0x28(%rax),%rdi
    52ff:	4c 01 ef             	add    %r13,%rdi
    5302:	e8 99 fe ff ff       	call   51a0 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    5307:	8b 43 30             	mov    0x30(%rbx),%eax
    530a:	41 83 c4 01          	add    $0x1,%r12d
    530e:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    5315:	44 39 e0             	cmp    %r12d,%eax
    5318:	0f 8e 0a 02 00 00    	jle    5528 <barriered_thread+0x278>
      if (data->tasks[t].available == 1) {
    531e:	48 8b 53 28          	mov    0x28(%rbx),%rdx
    5322:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    5326:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    532d:	75 c1                	jne    52f0 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    532f:	44 8b 43 18          	mov    0x18(%rbx),%r8d
          previous = t - 1;
    5333:	83 e8 01             	sub    $0x1,%eax
    5336:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    533b:	45 85 e4             	test   %r12d,%r12d
    533e:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5341:	45 85 c0             	test   %r8d,%r8d
    5344:	0f 8e 26 01 00 00    	jle    5470 <barriered_thread+0x1c0>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    534a:	48 63 c8             	movslq %eax,%rcx
    534d:	48 8b 43 10          	mov    0x10(%rbx),%rax
    5351:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5354:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    535a:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    5361:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    5365:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    5368:	45 31 f6             	xor    %r14d,%r14d
    536b:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    536f:	90                   	nop
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5370:	48 8b 10             	mov    (%rax),%rdx
    5373:	4c 8b 5a 28          	mov    0x28(%rdx),%r11
    5377:	49 01 cb             	add    %rcx,%r11
    537a:	4c 89 da             	mov    %r11,%rdx
    537d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    5384:	75 04                	jne    538a <barriered_thread+0xda>
            arrived++;
    5386:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    538a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    5390:	75 04                	jne    5396 <barriered_thread+0xe6>
            prearrive++;
    5392:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    5396:	48 83 c0 08          	add    $0x8,%rax
    539a:	48 39 c6             	cmp    %rax,%rsi
    539d:	75 d1                	jne    5370 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    539f:	45 85 d2             	test   %r10d,%r10d
    53a2:	0f 84 b8 00 00 00    	je     5460 <barriered_thread+0x1b0>
    53a8:	45 39 d0             	cmp    %r10d,%r8d
    53ab:	0f 84 af 00 00 00    	je     5460 <barriered_thread+0x1b0>
        if (arrived == 0 || arrived == data->thread_count) {
    53b1:	45 85 f6             	test   %r14d,%r14d
    53b4:	74 0a                	je     53c0 <barriered_thread+0x110>
    53b6:	44 39 73 18          	cmp    %r14d,0x18(%rbx)
    53ba:	0f 85 9e 01 00 00    	jne    555e <barriered_thread+0x2ae>
    53c0:	48 8b 53 28          	mov    0x28(%rbx),%rdx
          data->tasks[t].prearrive++;
    53c4:	4c 01 ea             	add    %r13,%rdx
    53c7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    53ce:	45 85 e4             	test   %r12d,%r12d
    53d1:	75 0e                	jne    53e1 <barriered_thread+0x131>
    53d3:	48 8b 73 70          	mov    0x70(%rbx),%rsi
    53d7:	48 3b 73 78          	cmp    0x78(%rbx),%rsi
    53db:	0f 8c 5f 01 00 00    	jl     5540 <barriered_thread+0x290>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    53e1:	48 63 0b             	movslq (%rbx),%rcx
    53e4:	48 8b 43 10          	mov    0x10(%rbx),%rax
          data->tasks[t].available = 0;
    53e8:	c7 82 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    53f2:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    53f6:	48 8b 78 28          	mov    0x28(%rax),%rdi
    53fa:	4c 01 ef             	add    %r13,%rdi
    53fd:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    5403:	48 8b 43 28          	mov    0x28(%rbx),%rax
    5407:	4c 01 e8             	add    %r13,%rax
    540a:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5411:	8b 43 30             	mov    0x30(%rbx),%eax
          data->iteration_count++;
    5414:	48 83 43 68 01       	addq   $0x1,0x68(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    5419:	83 e8 01             	sub    $0x1,%eax
    541c:	44 39 e0             	cmp    %r12d,%eax
    541f:	0f 84 a3 00 00 00    	je     54c8 <barriered_thread+0x218>
          asm volatile ("sfence" ::: "memory");
    5425:	0f ae f8             	sfence
          if (waiting == 0) {
    5428:	85 ed                	test   %ebp,%ebp
    542a:	0f 84 c8 00 00 00    	je     54f8 <barriered_thread+0x248>
        int arrived = 0; 
    5430:	bd 01 00 00 00       	mov    $0x1,%ebp
    5435:	e9 cd fe ff ff       	jmp    5307 <barriered_thread+0x57>
  while (data->running == 1) {
    543a:	83 7b 34 01          	cmpl   $0x1,0x34(%rbx)
    543e:	0f 85 ee 00 00 00    	jne    5532 <barriered_thread+0x282>
    5444:	0f 1f 40 00          	nopl   0x0(%rax)
      data->cycles++;
    5448:	48 83 83 98 00 00 00 01 	addq   $0x1,0x98(%rbx)
    for (; t < data->task_count; t++) {
    5450:	85 c0                	test   %eax,%eax
    5452:	7e e6                	jle    543a <barriered_thread+0x18a>
    5454:	45 31 e4             	xor    %r12d,%r12d
    5457:	e9 85 fe ff ff       	jmp    52e1 <barriered_thread+0x31>
    545c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5460:	83 fd 01             	cmp    $0x1,%ebp
    5463:	74 1b                	je     5480 <barriered_thread+0x1d0>
        int arrived = 0; 
    5465:	31 ed                	xor    %ebp,%ebp
    5467:	e9 45 ff ff ff       	jmp    53b1 <barriered_thread+0x101>
    546c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5470:	83 fd 01             	cmp    $0x1,%ebp
    5473:	0f 85 4b ff ff ff    	jne    53c4 <barriered_thread+0x114>
        int arrived = 0; 
    5479:	45 31 f6             	xor    %r14d,%r14d
    547c:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5480:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
    5487:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    548c:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    548e:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5492:	48 8b 83 80 00 00 00 	mov    0x80(%rbx),%rax
    5499:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    549e:	e8 6d ce ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    54a3:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
    54aa:	48 83 c0 01          	add    $0x1,%rax
    54ae:	48 99                	cqto
    54b0:	48 f7 bb 90 00 00 00 	idivq  0x90(%rbx)
    54b7:	48 89 93 88 00 00 00 	mov    %rdx,0x88(%rbx)
            waiting = 0; 
    54be:	e9 ee fe ff ff       	jmp    53b1 <barriered_thread+0x101>
    54c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    54c8:	48 8b 73 70          	mov    0x70(%rbx),%rsi
    54cc:	48 3b 73 78          	cmp    0x78(%rbx),%rsi
    54d0:	0f 8d 4f ff ff ff    	jge    5425 <barriered_thread+0x175>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    54d6:	48 c1 e6 04          	shl    $0x4,%rsi
    54da:	bf 04 00 00 00       	mov    $0x4,%edi
    54df:	48 03 73 60          	add    0x60(%rbx),%rsi
    54e3:	e8 28 ce ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    54e8:	48 83 43 70 01       	addq   $0x1,0x70(%rbx)
    54ed:	e9 33 ff ff ff       	jmp    5425 <barriered_thread+0x175>
    54f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    54f8:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    54ff:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    5504:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5508:	48 8b 83 80 00 00 00 	mov    0x80(%rbx),%rax
    550f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5513:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5517:	e8 f4 cd ff ff       	call   2310 <clock_gettime@plt>
            waiting = 1;
    551c:	e9 0f ff ff ff       	jmp    5430 <barriered_thread+0x180>
    5521:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    5528:	83 7b 34 01          	cmpl   $0x1,0x34(%rbx)
    552c:	0f 84 a6 fd ff ff    	je     52d8 <barriered_thread+0x28>
}
    5532:	5b                   	pop    %rbx
    5533:	31 c0                	xor    %eax,%eax
    5535:	5d                   	pop    %rbp
    5536:	41 5c                	pop    %r12
    5538:	41 5d                	pop    %r13
    553a:	41 5e                	pop    %r14
    553c:	c3                   	ret
    553d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    5540:	48 c1 e6 04          	shl    $0x4,%rsi
    5544:	bf 04 00 00 00       	mov    $0x4,%edi
    5549:	48 03 73 58          	add    0x58(%rbx),%rsi
    554d:	e8 be cd ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    5552:	48 8b 53 28          	mov    0x28(%rbx),%rdx
    5556:	4c 01 ea             	add    %r13,%rdx
    5559:	e9 83 fe ff ff       	jmp    53e1 <barriered_thread+0x131>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    555e:	48 63 13             	movslq (%rbx),%rdx
    5561:	48 8b 43 10          	mov    0x10(%rbx),%rax
    5565:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5569:	48 8b 78 28          	mov    0x28(%rax),%rdi
    556d:	4c 01 ef             	add    %r13,%rdi
    5570:	e8 2b fc ff ff       	call   51a0 <barriered_work_ingest>
          break;
    5575:	e9 4a fd ff ff       	jmp    52c4 <barriered_thread+0x14>
    557a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005580 <receive>:
int receive(struct BarrierTask *data) {
    5580:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5584:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    558a:	85 c0                	test   %eax,%eax
    558c:	0f 8e f1 00 00 00    	jle    5683 <receive+0x103>
int receive(struct BarrierTask *data) {
    5592:	41 54                	push   %r12
    5594:	48 89 fa             	mov    %rdi,%rdx
    5597:	55                   	push   %rbp
    5598:	31 ed                	xor    %ebp,%ebp
    559a:	53                   	push   %rbx
    559b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    55a0:	48 89 ee             	mov    %rbp,%rsi
    55a3:	48 c1 e6 05          	shl    $0x5,%rsi
    55a7:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    55ae:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    55b1:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    55b6:	48 85 ff             	test   %rdi,%rdi
    55b9:	0f 8e a1 00 00 00    	jle    5660 <receive+0xe0>
      data->sends++;
    55bf:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    55c6:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    55ca:	4c 63 1a             	movslq (%rdx),%r11
    55cd:	49 89 c9             	mov    %rcx,%r9
    55d0:	48 8d 41 01          	lea    0x1(%rcx),%rax
    55d4:	49 f7 d9             	neg    %r9
    55d7:	48 01 c7             	add    %rax,%rdi
    55da:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    55de:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    55e5:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    55e9:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    55ec:	49 29 c8             	sub    %rcx,%r8
    55ef:	eb 10                	jmp    5601 <receive+0x81>
    55f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    55f8:	48 83 c0 01          	add    $0x1,%rax
    55fc:	48 39 c7             	cmp    %rax,%rdi
    55ff:	74 5f                	je     5660 <receive+0xe0>
      data->n++;
    5601:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    5605:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
      data->n++;
    560c:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5613:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5617:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    561b:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5620:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5624:	75 d2                	jne    55f8 <receive+0x78>
    5626:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    562d:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5631:	75 c5                	jne    55f8 <receive+0x78>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5633:	bf 01 00 00 00       	mov    $0x1,%edi
    5638:	b9 01 00 00 00       	mov    $0x1,%ecx
    563d:	ba 01 00 00 00       	mov    $0x1,%edx
    5642:	31 c0                	xor    %eax,%eax
    5644:	48 8d 35 15 1e 00 00 	lea    0x1e15(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    564b:	e8 00 ce ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5650:	bf 01 00 00 00       	mov    $0x1,%edi
    5655:	e8 46 ce ff ff       	call   24a0 <exit@plt>
    565a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5660:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    5669:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    566c:	48 83 c5 01          	add    $0x1,%rbp
    5670:	39 aa 34 01 00 00    	cmp    %ebp,0x134(%rdx)
    5676:	0f 8f 24 ff ff ff    	jg     55a0 <receive+0x20>
}
    567c:	5b                   	pop    %rbx
    567d:	31 c0                	xor    %eax,%eax
    567f:	5d                   	pop    %rbp
    5680:	41 5c                	pop    %r12
    5682:	c3                   	ret
    5683:	31 c0                	xor    %eax,%eax
    5685:	c3                   	ret
    5686:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005690 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5690:	f3 0f 1e fa          	endbr64
    5694:	41 57                	push   %r15
    5696:	41 56                	push   %r14
    5698:	41 55                	push   %r13
    569a:	41 54                	push   %r12
    569c:	55                   	push   %rbp
    569d:	53                   	push   %rbx
    569e:	48 89 fb             	mov    %rdi,%rbx
    56a1:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    56a5:	8b 07                	mov    (%rdi),%eax
    56a7:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    56ad:	0f 84 3d 01 00 00    	je     57f0 <barriered_work+0x160>
    receive(data);
    56b3:	e8 c8 fe ff ff       	call   5580 <receive>
    while (data->scheduled == 1) {
    56b8:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    56bf:	75 1b                	jne    56dc <barriered_work+0x4c>
    56c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    56c8:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    56d0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    56d3:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    56da:	74 ec                	je     56c8 <barriered_work+0x38>
  if (data->sending == 1) {
    56dc:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    56e3:	0f 85 74 02 00 00    	jne    595d <barriered_work+0x2cd>
      for (int n = 0 ; n < data->thread_count; n++) {
    56e9:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    56ef:	85 c0                	test   %eax,%eax
    56f1:	0f 8e 72 02 00 00    	jle    5969 <barriered_work+0x2d9>
    56f7:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    56fe:	31 d2                	xor    %edx,%edx
    5700:	48 89 0c 24          	mov    %rcx,(%rsp)
    5704:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    570b:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    5710:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5716:	0f 84 bf 00 00 00    	je     57db <barriered_work+0x14b>
        struct Data *them = data->mailboxes[n].higher;
    571c:	49 89 d1             	mov    %rdx,%r9
    571f:	49 c1 e1 05          	shl    $0x5,%r9
    5723:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    572a:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    572e:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5732:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5736:	4d 39 c3             	cmp    %r8,%r11
    5739:	0f 8d 93 00 00 00    	jge    57d2 <barriered_work+0x142>
    573f:	4c 89 c6             	mov    %r8,%rsi
    5742:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5749:	4d 8b 71 10          	mov    0x10(%r9),%r14
    574d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5750:	49 8b 0a             	mov    (%r10),%rcx
    5753:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5757:	48 83 f8 02          	cmp    $0x2,%rax
    575b:	0f 86 8f 02 00 00    	jbe    59f0 <barriered_work+0x360>
    5761:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5769:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5771:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5775:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5779:	4c 39 2c 24          	cmp    %r13,(%rsp)
    577d:	0f 83 fd 01 00 00    	jae    5980 <barriered_work+0x2f0>
    5783:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5788:	4d 39 fc             	cmp    %r15,%r12
    578b:	0f 83 ef 01 00 00    	jae    5980 <barriered_work+0x2f0>
    5791:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5795:	48 01 cf             	add    %rcx,%rdi
    5798:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    57a0:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    57a7:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    57ab:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    57af:	49 39 fb             	cmp    %rdi,%r11
    57b2:	75 ec                	jne    57a0 <barriered_work+0x110>
    57b4:	0f 1f 40 00          	nopl   0x0(%rax)
    57b8:	48 01 f5             	add    %rsi,%rbp
    57bb:	4c 01 f6             	add    %r14,%rsi
    57be:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    57c5:	49 89 71 10          	mov    %rsi,0x10(%r9)
    57c9:	4d 89 42 08          	mov    %r8,0x8(%r10)
    57cd:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    57d2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    57d5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    57db:	48 83 c2 01          	add    $0x1,%rdx
    57df:	39 d0                	cmp    %edx,%eax
    57e1:	0f 8f 29 ff ff ff    	jg     5710 <barriered_work+0x80>
    57e7:	e9 7d 01 00 00       	jmp    5969 <barriered_work+0x2d9>
    57ec:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    57f0:	e8 8b fd ff ff       	call   5580 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    57f5:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    57fc:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    57fe:	45 85 c9             	test   %r9d,%r9d
    5801:	0f 8e 85 00 00 00    	jle    588c <barriered_work+0x1fc>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5807:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    580e:	4c 63 d8             	movslq %eax,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    5811:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5814:	49 c1 e3 09          	shl    $0x9,%r11
    5818:	4c 8b 52 10          	mov    0x10(%rdx),%r10
              int next_task = abs((t + 1) % (data->thread_count));
    581c:	99                   	cltd
    581d:	41 f7 f9             	idiv   %r9d
    5820:	4c 89 d7             	mov    %r10,%rdi
    5823:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
    5827:	89 d0                	mov    %edx,%eax
    5829:	f7 d8                	neg    %eax
    582b:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    582e:	45 31 c0             	xor    %r8d,%r8d
              int next_task = abs((t + 1) % (data->thread_count));
    5831:	48 63 ea             	movslq %edx,%rbp
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5834:	48 c1 e5 09          	shl    $0x9,%rbp
    5838:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    5840:	31 c0                	xor    %eax,%eax
    5842:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5848:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    584c:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    5850:	48 8b 8c 2a 68 01 00 00 	mov    0x168(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5858:	48 8b 17             	mov    (%rdi),%rdx
    585b:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    585f:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5862:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5866:	48 c1 e2 05          	shl    $0x5,%rdx
    586a:	4a 03 94 1e 68 01 00 00 	add    0x168(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5872:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    5876:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    587a:	49 39 c1             	cmp    %rax,%r9
    587d:	75 c9                	jne    5848 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    587f:	48 83 c7 08          	add    $0x8,%rdi
    5883:	49 83 c0 20          	add    $0x20,%r8
    5887:	49 39 fc             	cmp    %rdi,%r12
    588a:	75 b4                	jne    5840 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    588c:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    588f:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5896:	31 ff                	xor    %edi,%edi
    5898:	48 c1 e6 05          	shl    $0x5,%rsi
    589c:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    58a3:	e8 68 ca ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    58a8:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    58af:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    58b6:	48 8b 50 38          	mov    0x38(%rax),%rdx
    58ba:	8b 4a 10             	mov    0x10(%rdx),%ecx
    58bd:	8d 69 01             	lea    0x1(%rcx),%ebp
    58c0:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    58c3:	75 53                	jne    5918 <barriered_work+0x288>
    58c5:	0f 1f 00             	nopl   (%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    58c8:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    58cf:	48 8b 40 10          	mov    0x10(%rax),%rax
    58d3:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    58d6:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    58de:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    58e2:	48 c1 e7 09          	shl    $0x9,%rdi
    58e6:	48 03 78 28          	add    0x28(%rax),%rdi
    58ea:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    58f0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    58f3:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    58fa:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5901:	74 c5                	je     58c8 <barriered_work+0x238>
    if (modcount != data->thread->protected_state->modcount) {
    5903:	48 8b 40 38          	mov    0x38(%rax),%rax
    5907:	3b 68 10             	cmp    0x10(%rax),%ebp
    590a:	74 0c                	je     5918 <barriered_work+0x288>
    590c:	48 8d 3d f1 18 00 00 	lea    0x18f1(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5913:	e8 d8 c9 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5918:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    591f:	31 ff                	xor    %edi,%edi
    5921:	48 c1 e6 05          	shl    $0x5,%rsi
    5925:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    592c:	48 83 c6 10          	add    $0x10,%rsi
    5930:	e8 db c9 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5935:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    593c:	48 83 c0 01          	add    $0x1,%rax
    5940:	48 99                	cqto
    5942:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    5949:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5950:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    5957:	0f 84 a8 00 00 00    	je     5a05 <barriered_work+0x375>
    595d:	48 8d 3d b0 18 00 00 	lea    0x18b0(%rip),%rdi        # 7214 <_IO_stdin_used+0x214>
    5964:	e8 87 c9 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5969:	0f ae f8             	sfence
}
    596c:	48 83 c4 18          	add    $0x18,%rsp
    5970:	31 c0                	xor    %eax,%eax
    5972:	5b                   	pop    %rbx
    5973:	5d                   	pop    %rbp
    5974:	41 5c                	pop    %r12
    5976:	41 5d                	pop    %r13
    5978:	41 5e                	pop    %r14
    597a:	41 5f                	pop    %r15
    597c:	c3                   	ret
    597d:	0f 1f 00             	nopl   (%rax)
    5980:	49 89 f5             	mov    %rsi,%r13
    5983:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    598a:	4c 89 e7             	mov    %r12,%rdi
    598d:	49 d1 ed             	shr    %r13
    5990:	49 c1 e5 04          	shl    $0x4,%r13
    5994:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5999:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    599d:	41 83 e5 10          	and    $0x10,%r13d
    59a1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    59a5:	74 11                	je     59b8 <barriered_work+0x328>
          them->messages[them->messages_count++] = data->message; 
    59a7:	48 83 c7 10          	add    $0x10,%rdi
    59ab:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    59b0:	49 39 ff             	cmp    %rdi,%r15
    59b3:	74 13                	je     59c8 <barriered_work+0x338>
    59b5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    59b8:	0f 11 07             	movups %xmm0,(%rdi)
    59bb:	48 83 c7 20          	add    $0x20,%rdi
    59bf:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    59c3:	49 39 ff             	cmp    %rdi,%r15
    59c6:	75 f0                	jne    59b8 <barriered_work+0x328>
    59c8:	48 89 f7             	mov    %rsi,%rdi
    59cb:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    59cf:	4c 01 df             	add    %r11,%rdi
    59d2:	40 f6 c6 01          	test   $0x1,%sil
    59d6:	0f 84 dc fd ff ff    	je     57b8 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    59dc:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    59e3:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    59e7:	e9 cc fd ff ff       	jmp    57b8 <barriered_work+0x128>
    59ec:	0f 1f 40 00          	nopl   0x0(%rax)
    59f0:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    59f8:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5a00:	e9 8c fd ff ff       	jmp    5791 <barriered_work+0x101>
      for (int n = 0 ; n < data->thread_count; n++) {
    5a05:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    5a0c:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5a12:	31 d2                	xor    %edx,%edx
    5a14:	48 89 0c 24          	mov    %rcx,(%rsp)
    5a18:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    5a1f:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5a24:	85 c0                	test   %eax,%eax
    5a26:	0f 8e 3d ff ff ff    	jle    5969 <barriered_work+0x2d9>
    5a2c:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5a30:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5a36:	0f 84 af 00 00 00    	je     5aeb <barriered_work+0x45b>
        struct Data *them = data->mailboxes[n].higher;
    5a3c:	49 89 d1             	mov    %rdx,%r9
    5a3f:	49 c1 e1 05          	shl    $0x5,%r9
    5a43:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    5a4a:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    5a4e:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5a52:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5a56:	4d 39 d8             	cmp    %r11,%r8
    5a59:	0f 8e 83 00 00 00    	jle    5ae2 <barriered_work+0x452>
    5a5f:	4c 89 c6             	mov    %r8,%rsi
    5a62:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5a69:	4d 8b 71 10          	mov    0x10(%r9),%r14
    5a6d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5a70:	49 8b 0a             	mov    (%r10),%rcx
    5a73:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5a77:	48 83 f8 02          	cmp    $0x2,%rax
    5a7b:	0f 86 ef 00 00 00    	jbe    5b70 <barriered_work+0x4e0>
    5a81:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5a89:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5a91:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5a95:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5a99:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5a9d:	73 61                	jae    5b00 <barriered_work+0x470>
    5a9f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5aa4:	4d 39 fc             	cmp    %r15,%r12
    5aa7:	73 57                	jae    5b00 <barriered_work+0x470>
    5aa9:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5aad:	48 01 cf             	add    %rcx,%rdi
    5ab0:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5ab7:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5abb:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5abf:	49 39 fb             	cmp    %rdi,%r11
    5ac2:	75 ec                	jne    5ab0 <barriered_work+0x420>
    5ac4:	0f 1f 40 00          	nopl   0x0(%rax)
    5ac8:	48 01 f5             	add    %rsi,%rbp
    5acb:	4c 01 f6             	add    %r14,%rsi
    5ace:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5ad5:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5ad9:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5add:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5ae2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5ae5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5aeb:	48 83 c2 01          	add    $0x1,%rdx
    5aef:	39 d0                	cmp    %edx,%eax
    5af1:	0f 8f 39 ff ff ff    	jg     5a30 <barriered_work+0x3a0>
    5af7:	e9 6d fe ff ff       	jmp    5969 <barriered_work+0x2d9>
    5afc:	0f 1f 40 00          	nopl   0x0(%rax)
    5b00:	49 89 f5             	mov    %rsi,%r13
    5b03:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b0a:	4c 89 e7             	mov    %r12,%rdi
    5b0d:	49 d1 ed             	shr    %r13
    5b10:	49 c1 e5 04          	shl    $0x4,%r13
    5b14:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5b19:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5b1d:	41 83 e5 10          	and    $0x10,%r13d
    5b21:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5b25:	74 11                	je     5b38 <barriered_work+0x4a8>
          them->messages[them->messages_count++] = data->message; 
    5b27:	48 83 c7 10          	add    $0x10,%rdi
    5b2b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5b30:	4c 39 ff             	cmp    %r15,%rdi
    5b33:	74 13                	je     5b48 <barriered_work+0x4b8>
    5b35:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5b38:	0f 11 07             	movups %xmm0,(%rdi)
    5b3b:	48 83 c7 20          	add    $0x20,%rdi
    5b3f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5b43:	4c 39 ff             	cmp    %r15,%rdi
    5b46:	75 f0                	jne    5b38 <barriered_work+0x4a8>
    5b48:	48 89 f7             	mov    %rsi,%rdi
    5b4b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5b4f:	4c 01 df             	add    %r11,%rdi
    5b52:	40 f6 c6 01          	test   $0x1,%sil
    5b56:	0f 84 6c ff ff ff    	je     5ac8 <barriered_work+0x438>
          them->messages[them->messages_count++] = data->message; 
    5b5c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b63:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5b67:	e9 5c ff ff ff       	jmp    5ac8 <barriered_work+0x438>
    5b6c:	0f 1f 40 00          	nopl   0x0(%rax)
    5b70:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5b78:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5b80:	e9 24 ff ff ff       	jmp    5aa9 <barriered_work+0x419>
    5b85:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005b90 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    5b90:	f3 0f 1e fa          	endbr64
    5b94:	53                   	push   %rbx
    5b95:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    5b98:	e8 03 f6 ff ff       	call   51a0 <barriered_work_ingest>
  barriered_work(data);
    5b9d:	48 89 df             	mov    %rbx,%rdi
}
    5ba0:	5b                   	pop    %rbx
  barriered_work(data);
    5ba1:	e9 ea fa ff ff       	jmp    5690 <barriered_work>
    5ba6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005bb0 <sendm>:
int sendm(struct BarrierTask *data) {
    5bb0:	f3 0f 1e fa          	endbr64
    5bb4:	41 57                	push   %r15
    5bb6:	41 56                	push   %r14
    5bb8:	41 55                	push   %r13
    5bba:	41 54                	push   %r12
    5bbc:	55                   	push   %rbp
    5bbd:	53                   	push   %rbx
    5bbe:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5bc2:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
    5bc9:	0f 85 99 01 00 00    	jne    5d68 <sendm+0x1b8>
    5bcf:	48 8d b7 80 01 00 00 	lea    0x180(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5bd6:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    5bdc:	48 89 fa             	mov    %rdi,%rdx
    5bdf:	31 c9                	xor    %ecx,%ecx
    5be1:	48 89 34 24          	mov    %rsi,(%rsp)
    5be5:	48 8d b7 88 01 00 00 	lea    0x188(%rdi),%rsi
    5bec:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5bf1:	85 c0                	test   %eax,%eax
    5bf3:	0f 8e ce 00 00 00    	jle    5cc7 <sendm+0x117>
    5bf9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5c00:	39 8a 30 01 00 00    	cmp    %ecx,0x130(%rdx)
    5c06:	0f 84 af 00 00 00    	je     5cbb <sendm+0x10b>
        struct Data *them = data->mailboxes[n].higher;
    5c0c:	49 89 ca             	mov    %rcx,%r10
    5c0f:	49 c1 e2 05          	shl    $0x5,%r10
    5c13:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
    5c1a:	4d 8b 5a 08          	mov    0x8(%r10),%r11
        for (; them->messages_count < min;) {
    5c1e:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    5c22:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    5c26:	4c 39 cb             	cmp    %r9,%rbx
    5c29:	0f 8d 83 00 00 00    	jge    5cb2 <sendm+0x102>
    5c2f:	4c 89 cf             	mov    %r9,%rdi
    5c32:	48 8b aa 08 01 00 00 	mov    0x108(%rdx),%rbp
    5c39:	4d 8b 72 10          	mov    0x10(%r10),%r14
    5c3d:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    5c40:	49 8b 33             	mov    (%r11),%rsi
    5c43:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    5c47:	48 83 f8 02          	cmp    $0x2,%rax
    5c4b:	0f 86 ff 00 00 00    	jbe    5d50 <sendm+0x1a0>
    5c51:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5c59:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5c61:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    5c65:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    5c69:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5c6d:	73 71                	jae    5ce0 <sendm+0x130>
    5c6f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5c74:	4d 39 fc             	cmp    %r15,%r12
    5c77:	73 67                	jae    5ce0 <sendm+0x130>
    5c79:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    5c7d:	49 01 f0             	add    %rsi,%r8
    5c80:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    5c87:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    5c8b:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    5c8f:	49 39 d8             	cmp    %rbx,%r8
    5c92:	75 ec                	jne    5c80 <sendm+0xd0>
    5c94:	0f 1f 40 00          	nopl   0x0(%rax)
    5c98:	48 01 fd             	add    %rdi,%rbp
    5c9b:	4c 01 f7             	add    %r14,%rdi
    5c9e:	48 89 aa 08 01 00 00 	mov    %rbp,0x108(%rdx)
    5ca5:	49 89 7a 10          	mov    %rdi,0x10(%r10)
    5ca9:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    5cad:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5cb2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5cb5:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    5cbb:	48 83 c1 01          	add    $0x1,%rcx
    5cbf:	39 c8                	cmp    %ecx,%eax
    5cc1:	0f 8f 39 ff ff ff    	jg     5c00 <sendm+0x50>
}
    5cc7:	48 83 c4 18          	add    $0x18,%rsp
    5ccb:	31 c0                	xor    %eax,%eax
    5ccd:	5b                   	pop    %rbx
    5cce:	5d                   	pop    %rbp
    5ccf:	41 5c                	pop    %r12
    5cd1:	41 5d                	pop    %r13
    5cd3:	41 5e                	pop    %r14
    5cd5:	41 5f                	pop    %r15
    5cd7:	c3                   	ret
    5cd8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5ce0:	49 89 fd             	mov    %rdi,%r13
    5ce3:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    5cea:	4d 89 e0             	mov    %r12,%r8
    5ced:	49 d1 ed             	shr    %r13
    5cf0:	49 c1 e5 04          	shl    $0x4,%r13
    5cf4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5cf9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5cfd:	41 83 e5 10          	and    $0x10,%r13d
    5d01:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5d05:	74 11                	je     5d18 <sendm+0x168>
          them->messages[them->messages_count++] = data->message; 
    5d07:	49 83 c0 10          	add    $0x10,%r8
    5d0b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5d10:	4d 39 f8             	cmp    %r15,%r8
    5d13:	74 15                	je     5d2a <sendm+0x17a>
    5d15:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5d18:	41 0f 11 00          	movups %xmm0,(%r8)
    5d1c:	49 83 c0 20          	add    $0x20,%r8
    5d20:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    5d25:	4d 39 f8             	cmp    %r15,%r8
    5d28:	75 ee                	jne    5d18 <sendm+0x168>
    5d2a:	49 89 f8             	mov    %rdi,%r8
    5d2d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    5d31:	49 01 d8             	add    %rbx,%r8
    5d34:	40 f6 c7 01          	test   $0x1,%dil
    5d38:	0f 84 5a ff ff ff    	je     5c98 <sendm+0xe8>
          them->messages[them->messages_count++] = data->message; 
    5d3e:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    5d45:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    5d49:	e9 4a ff ff ff       	jmp    5c98 <sendm+0xe8>
    5d4e:	66 90                	xchg   %ax,%ax
    5d50:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5d58:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5d60:	e9 14 ff ff ff       	jmp    5c79 <sendm+0xc9>
    5d65:	0f 1f 00             	nopl   (%rax)
    5d68:	48 8d 3d a5 14 00 00 	lea    0x14a5(%rip),%rdi        # 7214 <_IO_stdin_used+0x214>
    5d6f:	e8 7c c5 ff ff       	call   22f0 <puts@plt>
    5d74:	e9 4e ff ff ff       	jmp    5cc7 <sendm+0x117>
    5d79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005d80 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5d80:	f3 0f 1e fa          	endbr64
}
    5d84:	31 c0                	xor    %eax,%eax
    5d86:	c3                   	ret
    5d87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005d90 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5d90:	f3 0f 1e fa          	endbr64
    5d94:	31 c0                	xor    %eax,%eax
    5d96:	c3                   	ret
    5d97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005da0 <after>:
int after(struct timespec left, struct timespec right) {
    5da0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5da4:	31 c0                	xor    %eax,%eax
    5da6:	48 39 d7             	cmp    %rdx,%rdi
    5da9:	7e 08                	jle    5db3 <after+0x13>
    5dab:	31 c0                	xor    %eax,%eax
    5dad:	48 39 ce             	cmp    %rcx,%rsi
    5db0:	0f 9f c0             	setg   %al
}
    5db3:	c3                   	ret
    5db4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5dbf:	90                   	nop

0000000000005dc0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5dc0:	f3 0f 1e fa          	endbr64
    5dc4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5dc9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5dce:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5dd0:	48 39 d7             	cmp    %rdx,%rdi
    5dd3:	7f 18                	jg     5ded <within+0x2d>
    5dd5:	4d 39 d8             	cmp    %r11,%r8
    5dd8:	0f 9e c2             	setle  %dl
    5ddb:	48 39 ce             	cmp    %rcx,%rsi
    5dde:	0f 9e c0             	setle  %al
    5de1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5de3:	31 c0                	xor    %eax,%eax
    5de5:	4d 39 d1             	cmp    %r10,%r9
    5de8:	0f 9e c0             	setle  %al
    5deb:	21 d0                	and    %edx,%eax
}
    5ded:	c3                   	ret
    5dee:	66 90                	xchg   %ax,%ax

0000000000005df0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5df0:	f3 0f 1e fa          	endbr64
    5df4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5df9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5dfe:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5e03:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5e08:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5e0d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5e12:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5e17:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5e1c:	48 39 fe             	cmp    %rdi,%rsi
    5e1f:	7d 2f                	jge    5e50 <overlap+0x60>
    5e21:	48 39 ca             	cmp    %rcx,%rdx
    5e24:	7d 62                	jge    5e88 <overlap+0x98>
    5e26:	4d 39 da             	cmp    %r11,%r10
    5e29:	7d 0e                	jge    5e39 <overlap+0x49>
    return 1;
    5e2b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e30:	4d 39 c1             	cmp    %r8,%r9
    5e33:	0f 8c 7f 00 00 00    	jl     5eb8 <overlap+0xc8>
  return 0;
    5e39:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e3b:	4d 39 c1             	cmp    %r8,%r9
    5e3e:	7f 4c                	jg     5e8c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e40:	31 c0                	xor    %eax,%eax
    5e42:	4d 39 da             	cmp    %r11,%r10
    5e45:	0f 9e c0             	setle  %al
    5e48:	c3                   	ret
    5e49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5e50:	7e 4e                	jle    5ea0 <overlap+0xb0>
    5e52:	48 39 ca             	cmp    %rcx,%rdx
    5e55:	7f 39                	jg     5e90 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e57:	75 31                	jne    5e8a <overlap+0x9a>
    5e59:	4d 39 c1             	cmp    %r8,%r9
    5e5c:	7c 2c                	jl     5e8a <overlap+0x9a>
    return 1;
    5e5e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e63:	4d 39 da             	cmp    %r11,%r10
    5e66:	7d 24                	jge    5e8c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e68:	48 39 ca             	cmp    %rcx,%rdx
    5e6b:	0f 94 c2             	sete   %dl
    5e6e:	48 39 fe             	cmp    %rdi,%rsi
    5e71:	0f 94 c0             	sete   %al
    5e74:	21 c2                	and    %eax,%edx
    5e76:	31 c0                	xor    %eax,%eax
    5e78:	4d 39 c1             	cmp    %r8,%r9
    5e7b:	0f 94 c0             	sete   %al
    5e7e:	21 d0                	and    %edx,%eax
    5e80:	c3                   	ret
    5e81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5e88:	74 af                	je     5e39 <overlap+0x49>
  return 0;
    5e8a:	31 c0                	xor    %eax,%eax
}
    5e8c:	c3                   	ret
    5e8d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5e90:	4d 39 da             	cmp    %r11,%r10
    5e93:	7e c4                	jle    5e59 <overlap+0x69>
    return 1;
    5e95:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e9a:	4d 39 c1             	cmp    %r8,%r9
    5e9d:	7e ba                	jle    5e59 <overlap+0x69>
    5e9f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ea0:	48 39 ca             	cmp    %rcx,%rdx
    5ea3:	7c 94                	jl     5e39 <overlap+0x49>
    5ea5:	4d 39 c1             	cmp    %r8,%r9
    5ea8:	7d b4                	jge    5e5e <overlap+0x6e>
    5eaa:	48 39 ca             	cmp    %rcx,%rdx
    5ead:	74 91                	je     5e40 <overlap+0x50>
    5eaf:	eb d9                	jmp    5e8a <overlap+0x9a>
    5eb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5eb8:	c3                   	ret
    5eb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005ec0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5ec0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5ec4:	85 f6                	test   %esi,%esi
    5ec6:	0f 8e 44 03 00 00    	jle    6210 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    5ecc:	41 57                	push   %r15
    5ece:	41 89 f7             	mov    %esi,%r15d
    5ed1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5ed3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5ed6:	41 55                	push   %r13
    5ed8:	41 54                	push   %r12
    5eda:	55                   	push   %rbp
    5edb:	53                   	push   %rbx
    5edc:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5ee0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5ee4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5ee9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5eee:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    5ef1:	45 39 e6             	cmp    %r12d,%r14d
    5ef4:	0f 84 4e 02 00 00    	je     6148 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5efa:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5eff:	8b 50 08             	mov    0x8(%rax),%edx
    5f02:	85 d2                	test   %edx,%edx
    5f04:	0f 8e 3e 02 00 00    	jle    6148 <verify+0x288>
    5f0a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    5f0f:	31 c9                	xor    %ecx,%ecx
    5f11:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    5f16:	31 c0                	xor    %eax,%eax
    5f18:	44 89 f2             	mov    %r14d,%edx
    5f1b:	bf 01 00 00 00       	mov    $0x1,%edi
    5f20:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5f25:	48 8d 35 f4 12 00 00 	lea    0x12f4(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    5f2c:	e8 1f c5 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5f31:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5f36:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    5f3b:	8b 40 08             	mov    0x8(%rax),%eax
    5f3e:	85 c0                	test   %eax,%eax
    5f40:	0f 8e e6 01 00 00    	jle    612c <verify+0x26c>
    5f46:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5f49:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    5f4e:	31 db                	xor    %ebx,%ebx
    5f50:	48 c1 e0 09          	shl    $0x9,%rax
    5f54:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    5f59:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5f5e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5f63:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    5f68:	4c 8b 20             	mov    (%rax),%r12
    5f6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5f70:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    5f75:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5f7a:	49 89 de             	mov    %rbx,%r14
    5f7d:	48 8d 35 b1 12 00 00 	lea    0x12b1(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5f84:	49 c1 e6 09          	shl    $0x9,%r14
    5f88:	bf 01 00 00 00       	mov    $0x1,%edi
    5f8d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5f91:	4b 8b 8c 3c 58 01 00 00 	mov    0x158(%r12,%r15,1),%rcx
    5f99:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    5f9e:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    5fa6:	31 c0                	xor    %eax,%eax
    5fa8:	e8 a3 c4 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5fad:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5fb2:	4c 8b 20             	mov    (%rax),%r12
    5fb5:	4b 83 bc 3c 58 01 00 00 00 	cmpq   $0x0,0x158(%r12,%r15,1)
    5fbe:	0f 8e 47 01 00 00    	jle    610b <verify+0x24b>
    5fc4:	4c 03 75 00          	add    0x0(%rbp),%r14
    5fc8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5fcd:	ba 01 00 00 00       	mov    $0x1,%edx
    5fd2:	4d 89 f5             	mov    %r14,%r13
    5fd5:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    5fdc:	4d 85 f6             	test   %r14,%r14
    5fdf:	0f 8e 21 01 00 00    	jle    6106 <verify+0x246>
    5fe5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5fe8:	48 89 d5             	mov    %rdx,%rbp
    5feb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5ff0:	31 db                	xor    %ebx,%ebx
    5ff2:	4d 89 f2             	mov    %r14,%r10
    5ff5:	48 c1 e5 05          	shl    $0x5,%rbp
    5ff9:	48 83 ed 20          	sub    $0x20,%rbp
    5ffd:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    6001:	49 89 ee             	mov    %rbp,%r14
    6004:	48 89 dd             	mov    %rbx,%rbp
    6007:	48 89 d3             	mov    %rdx,%rbx
    600a:	eb 31                	jmp    603d <verify+0x17d>
    600c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6010:	4c 39 c2             	cmp    %r8,%rdx
    6013:	0f 8d 57 01 00 00    	jge    6170 <verify+0x2b0>
    6019:	4c 39 df             	cmp    %r11,%rdi
    601c:	7e 05                	jle    6023 <verify+0x163>
    601e:	49 39 c1             	cmp    %rax,%r9
    6021:	7c 75                	jl     6098 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6023:	4c 39 df             	cmp    %r11,%rdi
    6026:	0f 8d ab 01 00 00    	jge    61d7 <verify+0x317>
    602c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6030:	48 83 c5 01          	add    $0x1,%rbp
    6034:	49 39 ea             	cmp    %rbp,%r10
    6037:	0f 8e a9 00 00 00    	jle    60e6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    603d:	49 8b 97 48 01 00 00 	mov    0x148(%r15),%rdx
    6044:	48 89 e8             	mov    %rbp,%rax
    6047:	48 c1 e0 05          	shl    $0x5,%rax
    604b:	49 03 85 48 01 00 00 	add    0x148(%r13),%rax
    6052:	4c 01 f2             	add    %r14,%rdx
    6055:	48 8b 08             	mov    (%rax),%rcx
    6058:	48 8b 78 10          	mov    0x10(%rax),%rdi
    605c:	48 8b 32             	mov    (%rdx),%rsi
    605f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6063:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6067:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    606b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    606f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6073:	48 39 f1             	cmp    %rsi,%rcx
    6076:	7c 98                	jl     6010 <verify+0x150>
    6078:	0f 8e 42 01 00 00    	jle    61c0 <verify+0x300>
    607e:	4c 39 c2             	cmp    %r8,%rdx
    6081:	0f 8f f9 00 00 00    	jg     6180 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6087:	75 a7                	jne    6030 <verify+0x170>
    6089:	4c 39 df             	cmp    %r11,%rdi
    608c:	7f a2                	jg     6030 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    608e:	49 39 c1             	cmp    %rax,%r9
    6091:	7c 9d                	jl     6030 <verify+0x170>
    6093:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6098:	49 89 c1             	mov    %rax,%r9
    609b:	48 89 f9             	mov    %rdi,%rcx
    609e:	48 89 f2             	mov    %rsi,%rdx
    60a1:	bf 01 00 00 00       	mov    $0x1,%edi
    60a6:	48 8d 35 db 13 00 00 	lea    0x13db(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    60ad:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60af:	48 83 c5 01          	add    $0x1,%rbp
    60b3:	e8 98 c3 ff ff       	call   2450 <__printf_chk@plt>
    60b8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    60bd:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    60c2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60c5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60ca:	4d 8b 95 58 01 00 00 	mov    0x158(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60d1:	4c 8b 20             	mov    (%rax),%r12
    60d4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    60d9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60dd:	49 39 ea             	cmp    %rbp,%r10
    60e0:	0f 8f 57 ff ff ff    	jg     603d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60e6:	48 89 da             	mov    %rbx,%rdx
    60e9:	49 3b 9f 58 01 00 00 	cmp    0x158(%r15),%rbx
    60f0:	7d 14                	jge    6106 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60f2:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    60f9:	48 83 c2 01          	add    $0x1,%rdx
    60fd:	4d 85 f6             	test   %r14,%r14
    6100:	0f 8f e2 fe ff ff    	jg     5fe8 <verify+0x128>
    6106:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    610b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6110:	48 83 c3 01          	add    $0x1,%rbx
    6114:	39 58 08             	cmp    %ebx,0x8(%rax)
    6117:	0f 8f 53 fe ff ff    	jg     5f70 <verify+0xb0>
    611d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6122:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6127:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    612c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6131:	48 83 c1 01          	add    $0x1,%rcx
    6135:	39 48 08             	cmp    %ecx,0x8(%rax)
    6138:	0f 8f d8 fd ff ff    	jg     5f16 <verify+0x56>
    613e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6143:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6148:	48 81 44 24 10 b0 00 00 00 	addq   $0xb0,0x10(%rsp)
    6151:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6156:	41 39 c7             	cmp    %eax,%r15d
    6159:	0f 84 86 00 00 00    	je     61e5 <verify+0x325>
    615f:	41 89 c4             	mov    %eax,%r12d
    6162:	e9 8a fd ff ff       	jmp    5ef1 <verify+0x31>
    6167:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6170:	0f 85 ba fe ff ff    	jne    6030 <verify+0x170>
    6176:	e9 a8 fe ff ff       	jmp    6023 <verify+0x163>
    617b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6180:	49 39 c1             	cmp    %rax,%r9
    6183:	7e 09                	jle    618e <verify+0x2ce>
    6185:	4c 39 df             	cmp    %r11,%rdi
    6188:	0f 8c 0a ff ff ff    	jl     6098 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    618e:	4c 39 df             	cmp    %r11,%rdi
    6191:	0f 8f 99 fe ff ff    	jg     6030 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6197:	49 39 c1             	cmp    %rax,%r9
    619a:	0f 8d f8 fe ff ff    	jge    6098 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    61a0:	48 39 f1             	cmp    %rsi,%rcx
    61a3:	0f 85 87 fe ff ff    	jne    6030 <verify+0x170>
    61a9:	4c 39 c2             	cmp    %r8,%rdx
    61ac:	0f 85 7e fe ff ff    	jne    6030 <verify+0x170>
    61b2:	4c 39 df             	cmp    %r11,%rdi
    61b5:	0f 84 dd fe ff ff    	je     6098 <verify+0x1d8>
    61bb:	e9 70 fe ff ff       	jmp    6030 <verify+0x170>
    61c0:	4c 39 c2             	cmp    %r8,%rdx
    61c3:	0f 8c 5a fe ff ff    	jl     6023 <verify+0x163>
    61c9:	4c 39 df             	cmp    %r11,%rdi
    61cc:	7e c9                	jle    6197 <verify+0x2d7>
    61ce:	4c 39 c2             	cmp    %r8,%rdx
    61d1:	0f 85 59 fe ff ff    	jne    6030 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    61d7:	49 39 c1             	cmp    %rax,%r9
    61da:	0f 8f 50 fe ff ff    	jg     6030 <verify+0x170>
    61e0:	e9 b3 fe ff ff       	jmp    6098 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    61e5:	48 81 44 24 18 b0 00 00 00 	addq   $0xb0,0x18(%rsp)
    61ee:	41 8d 46 01          	lea    0x1(%r14),%eax
    61f2:	45 39 e6             	cmp    %r12d,%r14d
    61f5:	74 08                	je     61ff <verify+0x33f>
    61f7:	41 89 c6             	mov    %eax,%r14d
    61fa:	e9 ea fc ff ff       	jmp    5ee9 <verify+0x29>
}
    61ff:	48 83 c4 58          	add    $0x58,%rsp
    6203:	31 c0                	xor    %eax,%eax
    6205:	5b                   	pop    %rbx
    6206:	5d                   	pop    %rbp
    6207:	41 5c                	pop    %r12
    6209:	41 5d                	pop    %r13
    620b:	41 5e                	pop    %r14
    620d:	41 5f                	pop    %r15
    620f:	c3                   	ret
    6210:	31 c0                	xor    %eax,%eax
    6212:	c3                   	ret

Disassembly of section .fini:

0000000000006214 <_fini>:
    6214:	f3 0f 1e fa          	endbr64
    6218:	48 83 ec 08          	sub    $0x8,%rsp
    621c:	48 83 c4 08          	add    $0x8,%rsp
    6220:	c3                   	ret
