
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
    261f:	48 8d 05 1a 10 00 00 	lea    0x101a(%rip),%rax        # 3640 <barriered_reset>
    2626:	66 48 0f 6e e8       	movq   %rax,%xmm5
    262b:	0f 16 2d 46 76 00 00 	movhps 0x7646(%rip),%xmm5        # 9c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    2632:	0f 29 6c 24 40       	movaps %xmm5,0x40(%rsp)
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
    2752:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
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
    276f:	4d 89 f5             	mov    %r14,%r13
    2772:	41 89 ee             	mov    %ebp,%r14d
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2775:	e8 26 fc ff ff       	call   23a0 <calloc@plt>
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    277a:	be 10 00 00 00       	mov    $0x10,%esi
    277f:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    2784:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    278a:	48 89 c3             	mov    %rax,%rbx
    278d:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2792:	e8 09 fc ff ff       	call   23a0 <calloc@plt>
    2797:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
  int curcpu = 0;
    279c:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    27a4:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
    27a8:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    27af:	4d 89 df             	mov    %r11,%r15
  int external_thread_index = 0;
    27b2:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
            thread_data[x].tasks[y].run = barriered_work; 
    27ba:	4c 89 5c 24 58       	mov    %r11,0x58(%rsp)
    27bf:	4c 89 5c 24 68       	mov    %r11,0x68(%rsp)
    27c4:	0f 1f 40 00          	nopl   0x0(%rax)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27c8:	be 08 00 00 00       	mov    $0x8,%esi
    27cd:	bf 02 00 00 00       	mov    $0x2,%edi
    27d2:	45 89 f4             	mov    %r14d,%r12d
    27d5:	e8 c6 fb ff ff       	call   23a0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27da:	be 80 00 00 00       	mov    $0x80,%esi
    27df:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27e4:	48 89 c3             	mov    %rax,%rbx
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27e7:	e8 b4 fb ff ff       	call   23a0 <calloc@plt>
    27ec:	44 89 74 24 10       	mov    %r14d,0x10(%rsp)
    27f1:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    if (x % 2 == 1) {
    27f6:	44 89 f0             	mov    %r14d,%eax
    27f9:	41 83 c6 01          	add    $0x1,%r14d
    27fd:	83 e0 01             	and    $0x1,%eax
    2800:	85 c0                	test   %eax,%eax
    2802:	0f 84 78 0c 00 00    	je     3480 <main+0xe90>
      my_thread_data[0] = &thread_data[other]; 
    2808:	49 8d 8f 50 ff ff ff 	lea    -0xb0(%r15),%rcx
      my_thread_data[1] = &thread_data[x]; 
    280f:	4c 89 7b 08          	mov    %r15,0x8(%rbx)
    2813:	4d 89 f8             	mov    %r15,%r8
    2816:	31 c0                	xor    %eax,%eax
      my_thread_data[0] = &thread_data[other]; 
    2818:	48 89 0b             	mov    %rcx,(%rbx)
    281b:	44 89 e2             	mov    %r12d,%edx
    281e:	bf 01 00 00 00       	mov    $0x1,%edi
      other = abs(x - 1) % total_threads;
    2823:	41 8d 6c 24 ff       	lea    -0x1(%r12),%ebp
      thread_data[x].thread_index = 1;
    2828:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
    282f:	48 8d 35 c5 4a 00 00 	lea    0x4ac5(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
    2836:	e8 15 fc ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    283b:	49 8d 45 18          	lea    0x18(%r13),%rax
    283f:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2844:	4d 89 6f 38          	mov    %r13,0x38(%r15)
    2848:	45 8b 07             	mov    (%r15),%r8d
    284b:	89 e9                	mov    %ebp,%ecx
    284d:	44 89 e2             	mov    %r12d,%edx
    2850:	48 8d 35 19 4d 00 00 	lea    0x4d19(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    2857:	bf 01 00 00 00       	mov    $0x1,%edi
    285c:	31 c0                	xor    %eax,%eax
    285e:	e8 ed fb ff ff       	call   2450 <__printf_chk@plt>
    2863:	8b 4c 24 28          	mov    0x28(%rsp),%ecx
    2867:	31 c0                	xor    %eax,%eax
    2869:	44 89 e2             	mov    %r12d,%edx
    thread_data[x].other = other;
    286c:	41 89 af a8 00 00 00 	mov    %ebp,0xa8(%r15)
    2873:	48 8d 35 26 4d 00 00 	lea    0x4d26(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    287a:	bf 01 00 00 00       	mov    $0x1,%edi
    287f:	e8 cc fb ff ff       	call   2450 <__printf_chk@plt>
      if (x < thread_count) {
    2884:	83 7c 24 10 05       	cmpl   $0x5,0x10(%rsp)
    2889:	0f 87 57 0c 00 00    	ja     34e6 <main+0xef6>
        CPU_SET(curcpu, sendercpu);
    288f:	48 63 44 24 28       	movslq 0x28(%rsp),%rax
    2894:	48 89 c7             	mov    %rax,%rdi
    2897:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    289d:	77 17                	ja     28b6 <main+0x2c6>
    289f:	89 f9                	mov    %edi,%ecx
    28a1:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    28a6:	48 c1 e8 06          	shr    $0x6,%rax
    28aa:	ba 01 00 00 00       	mov    $0x1,%edx
    28af:	48 d3 e2             	shl    %cl,%rdx
    28b2:	48 09 14 c7          	or     %rdx,(%rdi,%rax,8)
        curcpu += 2;
    28b6:	83 44 24 28 02       	addl   $0x2,0x28(%rsp)
    thread_data[x].cpu_set = sendercpu;
    28bb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    thread_data[x].threads = my_thread_data;
    28c0:	49 89 5f 10          	mov    %rbx,0x10(%r15)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28c4:	31 db                	xor    %ebx,%ebx
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28c6:	be 10 00 00 00       	mov    $0x10,%esi
    thread_data[x].real_thread_index = x;
    28cb:	45 89 67 04          	mov    %r12d,0x4(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28cf:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].cpu_set = sendercpu;
    28d4:	49 89 87 a0 00 00 00 	mov    %rax,0xa0(%r15)
    thread_data[x].thread_count = 2;
    28db:	48 8b 05 5e 51 00 00 	mov    0x515e(%rip),%rax        # 7a40 <_IO_stdin_used+0xa40>
    thread_data[x].task_count = total_barrier_count;
    28e2:	41 c7 47 30 03 00 00 00 	movl   $0x3,0x30(%r15)
    thread_data[x].thread_count = 2;
    28ea:	49 89 47 18          	mov    %rax,0x18(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28ee:	e8 ad fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28f3:	be 10 00 00 00       	mov    $0x10,%esi
    28f8:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28fd:	49 89 47 58          	mov    %rax,0x58(%r15)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2901:	e8 9a fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2906:	be 28 00 00 00       	mov    $0x28,%esi
    290b:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    2910:	66 0f 6f 15 08 51 00 00 	movdqa 0x5108(%rip),%xmm2        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2918:	49 89 47 60          	mov    %rax,0x60(%r15)
    thread_data[x].timestamp_count = 0;
    291c:	41 0f 11 57 70       	movups %xmm2,0x70(%r15)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2921:	e8 7a fa ff ff       	call   23a0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2926:	be 00 02 00 00       	mov    $0x200,%esi
    292b:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
    2930:	66 0f 6f 1d e8 50 00 00 	movdqa 0x50e8(%rip),%xmm3        # 7a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2938:	49 89 87 80 00 00 00 	mov    %rax,0x80(%r15)
    thread_data[x].task_timestamp_count = 0;
    293f:	41 0f 11 9f 88 00 00 00 	movups %xmm3,0x88(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2947:	e8 54 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    294c:	44 89 74 24 38       	mov    %r14d,0x38(%rsp)
      thread_data[x].tasks = barriers;
    2951:	49 89 47 28          	mov    %rax,0x28(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2955:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks[y].protected = do_protected_write; 
    2958:	4c 63 f3             	movslq %ebx,%r14
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    295b:	be 20 00 00 00       	mov    $0x20,%esi
    2960:	bf 06 00 00 00       	mov    $0x6,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    2965:	4d 89 f5             	mov    %r14,%r13
    2968:	48 8d 05 91 0c 00 00 	lea    0xc91(%rip),%rax        # 3600 <do_protected_write>
    296f:	49 c1 e5 09          	shl    $0x9,%r13
    2973:	4a 8d 2c 2a          	lea    (%rdx,%r13,1),%rbp
    2977:	48 89 85 20 01 00 00 	mov    %rax,0x120(%rbp)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    297e:	e8 1d fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    2983:	44 89 64 24 10       	mov    %r12d,0x10(%rsp)
    2988:	48 89 85 68 01 00 00 	mov    %rax,0x168(%rbp)
        for (int b = 0 ; b < 2 ; b++) {
    298f:	48 89 c5             	mov    %rax,%rbp
    2992:	48 8d 40 40          	lea    0x40(%rax),%rax
    2996:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    299b:	89 5c 24 18          	mov    %ebx,0x18(%rsp)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    299f:	be 08 00 00 00       	mov    $0x8,%esi
    29a4:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    29a9:	48 83 c5 20          	add    $0x20,%rbp
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29ad:	e8 ee f9 ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29b2:	be 08 00 00 00       	mov    $0x8,%esi
    29b7:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29bc:	49 89 c4             	mov    %rax,%r12
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29bf:	e8 dc f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29c4:	be 18 00 00 00       	mov    $0x18,%esi
    29c9:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29ce:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29d1:	e8 ca f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    29d6:	66 0f 6f 05 52 50 00 00 	movdqa 0x5052(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
          mailboxes[b].higher = &data[1];
    29de:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29e2:	48 89 45 e0          	mov    %rax,-0x20(%rbp)
          mailboxes[b].higher = &data[1];
    29e6:	48 89 75 e8          	mov    %rsi,-0x18(%rbp)
          data[0].messages = messages;
    29ea:	4c 89 20             	mov    %r12,(%rax)
          data[1].messages = messages2;
    29ed:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    29f1:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    29f5:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    29f9:	48 39 6c 24 08       	cmp    %rbp,0x8(%rsp)
    29fe:	75 9f                	jne    299f <main+0x3af>
        char *message = malloc(sizeof(char) * 256);
    2a00:	be 01 00 00 00       	mov    $0x1,%esi
    2a05:	bf 00 01 00 00       	mov    $0x100,%edi
    2a0a:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
    2a0e:	44 8b 64 24 10       	mov    0x10(%rsp),%r12d
    2a13:	e8 88 f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a18:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a1d:	48 89 c5             	mov    %rax,%rbp
        struct Message *messaged = malloc(sizeof(struct Message));
    2a20:	e8 eb f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a25:	48 89 ef             	mov    %rbp,%rdi
    2a28:	41 89 d9             	mov    %ebx,%r9d
    2a2b:	45 89 e0             	mov    %r12d,%r8d
    2a2e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2a33:	48 8d 0d 86 4b 00 00 	lea    0x4b86(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a3a:	ba 00 01 00 00       	mov    $0x100,%edx
    2a3f:	31 c0                	xor    %eax,%eax
    2a41:	be 01 00 00 00       	mov    $0x1,%esi
    2a46:	e8 d5 fa ff ff       	call   2520 <__sprintf_chk@plt>
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a4b:	49 8b 57 28          	mov    0x28(%r15),%rdx
        messaged->thread_index = thread_data[x].thread_index;
    2a4f:	49 63 07             	movslq (%r15),%rax
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a52:	8d 4b 01             	lea    0x1(%rbx),%ecx
        messaged->message = message;
    2a55:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a5a:	be 20 00 00 00       	mov    $0x20,%esi
    2a5f:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a64:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2a68:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
        messaged->message = message;
    2a6d:	49 89 2a             	mov    %rbp,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a70:	4a 8d 2c 2a          	lea    (%rdx,%r13,1),%rbp
        messaged->task_index = y;
    2a74:	4d 89 72 10          	mov    %r14,0x10(%r10)
        messaged->thread_index = thread_data[x].thread_index;
    2a78:	49 89 c6             	mov    %rax,%r14
    2a7b:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a7f:	89 8d 88 01 00 00    	mov    %ecx,0x188(%rbp)
        thread_data[x].tasks[y].message = messaged;
    2a85:	4c 89 95 80 01 00 00 	mov    %r10,0x180(%rbp)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a8c:	48 c7 85 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a97:	e8 04 f9 ff ff       	call   23a0 <calloc@plt>
        if (y == barrier_count - 1) {
    2a9c:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2a9f:	89 5d 00             	mov    %ebx,0x0(%rbp)
        if (y == barrier_count - 1) {
    2aa2:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2aa6:	48 89 85 48 01 00 00 	mov    %rax,0x148(%rbp)
        if (y == barrier_count - 1) {
    2aad:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
        thread_data[x].tasks[y].available = 1;
    2ab2:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2abc:	48 89 85 38 01 00 00 	mov    %rax,0x138(%rbp)
        thread_data[x].tasks[y].sending = 1;
    2ac3:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2acd:	48 c7 85 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%rbp)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2ad8:	44 89 b5 30 01 00 00 	mov    %r14d,0x130(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2adf:	4c 89 bd 28 01 00 00 	mov    %r15,0x128(%rbp)
        thread_data[x].tasks[y].arrived = 0;
    2ae6:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        thread_data[x].tasks[y].thread_count = 2;
    2af0:	c7 85 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%rbp)
        thread_data[x].tasks[y].sending = 1;
    2afa:	48 89 85 78 01 00 00 	mov    %rax,0x178(%rbp)
        if (y == barrier_count - 1) {
    2b01:	0f 84 61 09 00 00    	je     3468 <main+0xe78>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2b07:	41 39 dc             	cmp    %ebx,%r12d
    2b0a:	75 6c                	jne    2b78 <main+0x588>
    2b0c:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    2b10:	85 db                	test   %ebx,%ebx
    2b12:	7f 64                	jg     2b78 <main+0x588>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2b14:	44 89 e2             	mov    %r12d,%edx
    2b17:	bf 01 00 00 00       	mov    $0x1,%edi
    2b1c:	31 c0                	xor    %eax,%eax
    2b1e:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2b22:	48 8d 35 bf 4a 00 00 	lea    0x4abf(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2b29:	e8 22 f9 ff ff       	call   2450 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b2e:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    2b33:	48 63 c3             	movslq %ebx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b36:	49 8b 57 28          	mov    0x28(%r15),%rdx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b3a:	48 89 c7             	mov    %rax,%rdi
    2b3d:	48 c1 e0 04          	shl    $0x4,%rax
    2b41:	48 01 c8             	add    %rcx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b44:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b48:	49 89 47 40          	mov    %rax,0x40(%r15)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b4c:	48 8d 05 fd 2f 00 00 	lea    0x2ffd(%rip),%rax        # 5b50 <barriered_work_ingest>
    2b53:	4a 89 84 2a 18 01 00 00 	mov    %rax,0x118(%rdx,%r13,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b5b:	8d 47 01             	lea    0x1(%rdi),%eax
    2b5e:	89 44 24 20          	mov    %eax,0x20(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b62:	83 f9 03             	cmp    $0x3,%ecx
    2b65:	74 24                	je     2b8b <main+0x59b>
    2b67:	bb 01 00 00 00       	mov    $0x1,%ebx
    2b6c:	e9 e7 fd ff ff       	jmp    2958 <main+0x368>
    2b71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            thread_data[x].tasks[y].run = barriered_work; 
    2b78:	48 8d 05 d1 2a 00 00 	lea    0x2ad1(%rip),%rax        # 5650 <barriered_work>
    2b7f:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b86:	83 f9 03             	cmp    $0x3,%ecx
    2b89:	75 dc                	jne    2b67 <main+0x577>
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b8b:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b95:	44 8b 74 24 38       	mov    0x38(%rsp),%r14d
  for (int x = 0 ; x < total_threads ; x++) {
    2b9a:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2b9f:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2ba9:	c7 82 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2bb3:	66 0f 6f 64 24 40    	movdqa 0x40(%rsp),%xmm4
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2bb9:	48 89 82 34 05 00 00 	mov    %rax,0x534(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bc0:	41 8b 07             	mov    (%r15),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2bc3:	4c 89 ba 28 05 00 00 	mov    %r15,0x528(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2bca:	49 81 c7 b0 00 00 00 	add    $0xb0,%r15
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2bd1:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2bd7:	c7 82 7c 05 00 00 06 00 00 00 	movl   $0x6,0x57c(%rdx)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2be1:	c7 82 3c 05 00 00 03 00 00 00 	movl   $0x3,0x53c(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2beb:	0f 11 a2 18 05 00 00 	movups %xmm4,0x518(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2bf2:	41 83 fe 09          	cmp    $0x9,%r14d
    2bf6:	0f 85 cc fb ff ff    	jne    27c8 <main+0x1d8>
    2bfc:	4c 8b 44 24 68       	mov    0x68(%rsp),%r8
    2c01:	4c 8b 5c 24 58       	mov    0x58(%rsp),%r11
    2c06:	31 c0                	xor    %eax,%eax
    2c08:	ba 07 00 00 00       	mov    $0x7,%edx
    2c0d:	48 8d 35 04 47 00 00 	lea    0x4704(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2c14:	bf 01 00 00 00       	mov    $0x1,%edi
    2c19:	4c 89 44 24 78       	mov    %r8,0x78(%rsp)
    2c1e:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    2c23:	e8 28 f8 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c28:	be 08 00 00 00       	mov    $0x8,%esi
    2c2d:	bf 02 00 00 00       	mov    $0x2,%edi
    2c32:	e8 69 f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2c37:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c3c:	bf 09 00 00 00       	mov    $0x9,%edi
    my_thread_data[0] = &thread_data[x]; 
    2c41:	4d 8d bb d0 04 00 00 	lea    0x4d0(%r11),%r15
    thread_data[n].tasks[0].scheduled = 1;
    2c48:	4c 89 5c 24 30       	mov    %r11,0x30(%rsp)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c4d:	4d 8d b3 60 01 00 00 	lea    0x160(%r11),%r14
    thread_data[x].threads = my_thread_data;
    2c54:	49 89 83 e0 04 00 00 	mov    %rax,0x4e0(%r11)
    thread_data[n].tasks[0].scheduled = 1;
    2c5b:	49 8d b3 70 03 00 00 	lea    0x370(%r11),%rsi
    2c62:	4d 8d a3 b0 00 00 00 	lea    0xb0(%r11),%r12
    my_thread_data[0] = &thread_data[x]; 
    2c69:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c6c:	49 8d 8b c0 02 00 00 	lea    0x2c0(%r11),%rcx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c73:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c77:	49 8b 43 28          	mov    0x28(%r11),%rax
    thread_data[x].thread_count = 2;
    2c7b:	41 c7 83 e8 04 00 00 02 00 00 00 	movl   $0x2,0x4e8(%r11)
    thread_data[x].thread_index = 0;
    2c86:	41 c7 83 d0 04 00 00 00 00 00 00 	movl   $0x0,0x4d0(%r11)
    thread_data[x].task_count = total_barrier_count;
    2c91:	41 c7 83 00 05 00 00 03 00 00 00 	movl   $0x3,0x500(%r11)
    thread_data[n].tasks[0].scheduled = 1;
    2c9c:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2ca6:	49 8b 83 d8 00 00 00 	mov    0xd8(%r11),%rax
    2cad:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2cb2:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2cb7:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cc1:	49 8b 83 88 01 00 00 	mov    0x188(%r11),%rax
    2cc8:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    2ccd:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cd7:	49 8d 83 10 02 00 00 	lea    0x210(%r11),%rax
    2cde:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2ce3:	49 8b 83 38 02 00 00 	mov    0x238(%r11),%rax
    my_thread_data[0] = &thread_data[x]; 
    2cea:	4c 89 7c 24 20       	mov    %r15,0x20(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2cef:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cf9:	49 8b 83 e8 02 00 00 	mov    0x2e8(%r11),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2d00:	4c 89 74 24 28       	mov    %r14,0x28(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d05:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d0f:	49 8b 83 98 03 00 00 	mov    0x398(%r11),%rax
    2d16:	4c 89 64 24 38       	mov    %r12,0x38(%rsp)
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
    2d58:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d5d:	e8 3e f6 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d62:	be 08 00 00 00       	mov    $0x8,%esi
    2d67:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d6c:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2d71:	e8 2a f6 ff ff       	call   23a0 <calloc@plt>

  thread_data[thread_count].type = TIMER;
    2d76:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
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
    2d8f:	41 c7 83 28 04 00 00 00 00 00 00 	movl   $0x0,0x428(%r11)
  thread_data[thread_count].task_count = total_barrier_count;
    2d9a:	49 89 83 50 04 00 00 	mov    %rax,0x450(%r11)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2da1:	e8 fa f5 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2da6:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    2dab:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    2db0:	ba 06 00 00 00       	mov    $0x6,%edx
    2db5:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2dba:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2dbf:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2dc3:	48 89 78 18          	mov    %rdi,0x18(%rax)
    2dc7:	4d 8d b3 20 04 00 00 	lea    0x420(%r11),%r14
    2dce:	49 8d bb 80 05 00 00 	lea    0x580(%r11),%rdi
    2dd5:	4c 89 18             	mov    %r11,(%rax)
    2dd8:	4c 89 60 08          	mov    %r12,0x8(%rax)
    2ddc:	4c 8d 25 cd 08 00 00 	lea    0x8cd(%rip),%r12        # 36b0 <barriered_thread>
    2de3:	48 89 48 20          	mov    %rcx,0x20(%rax)
    2de7:	48 89 70 28          	mov    %rsi,0x28(%rax)
    2deb:	48 8d 35 35 45 00 00 	lea    0x4535(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2df2:	4c 89 70 30          	mov    %r14,0x30(%rax)
    2df6:	4c 89 78 38          	mov    %r15,0x38(%rax)
    2dfa:	4c 8d 3d 07 48 00 00 	lea    0x4807(%rip),%r15        # 7608 <_IO_stdin_used+0x608>
    2e01:	48 89 78 40          	mov    %rdi,0x40(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2e05:	49 89 83 30 04 00 00 	mov    %rax,0x430(%r11)
    2e0c:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2e0e:	41 c7 83 38 04 00 00 06 00 00 00 	movl   $0x6,0x438(%r11)
  thread_data[thread_count].my_thread_count = 2;
    2e19:	41 c7 83 40 04 00 00 02 00 00 00 	movl   $0x2,0x440(%r11)
  thread_data[thread_count].thread_index = 0;
    2e24:	41 c7 83 20 04 00 00 00 00 00 00 	movl   $0x0,0x420(%r11)
    my_thread_data[n] = &thread_data[n]; 
    2e2f:	48 89 7c 24 30       	mov    %rdi,0x30(%rsp)
    2e34:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].thread_index = 0;
    2e39:	4c 89 5c 24 68       	mov    %r11,0x68(%rsp)
    2e3e:	e8 0d f6 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2e43:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2e4a:	49 8d 7d 30          	lea    0x30(%r13),%rdi
    2e4e:	4c 89 f1             	mov    %r14,%rcx
    2e51:	48 8d 15 c8 0b 00 00 	lea    0xbc8(%rip),%rdx        # 3a20 <timer_thread>
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
    2ece:	4c 8b 5c 24 68       	mov    0x68(%rsp),%r11
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
    2ee9:	49 89 9b 00 05 00 00 	mov    %rbx,0x500(%r11)
    thread_data[x].type = IO;
    2ef0:	41 c7 83 d8 04 00 00 02 00 00 00 	movl   $0x2,0x4d8(%r11)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2efb:	e8 a0 f4 ff ff       	call   23a0 <calloc@plt>
    2f00:	4c 8b 5c 24 68       	mov    0x68(%rsp),%r11
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f05:	be 00 08 00 00       	mov    $0x800,%esi
    2f0a:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2f0c:	49 89 83 18 05 00 00 	mov    %rax,0x518(%r11)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f13:	e8 98 f5 ff ff       	call   24b0 <eventfd@plt>
    2f18:	4c 8b 5c 24 68       	mov    0x68(%rsp),%r11
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f1d:	be 08 00 00 00       	mov    $0x8,%esi
    2f22:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2f27:	41 89 83 20 05 00 00 	mov    %eax,0x520(%r11)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f2e:	e8 6d f4 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    2f33:	4c 8b 5c 24 68       	mov    0x68(%rsp),%r11
    2f38:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
    2f3d:	ba 07 00 00 00       	mov    $0x7,%edx
    2f42:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    2f47:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    2f4c:	48 8d 35 f2 43 00 00 	lea    0x43f2(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    2f53:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    2f58:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    2f5d:	4c 89 18             	mov    %r11,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    2f60:	49 89 83 e0 04 00 00 	mov    %rax,0x4e0(%r11)
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    2f67:	41 c7 83 e8 04 00 00 06 00 00 00 	movl   $0x6,0x4e8(%r11)
    thread_data[x].thread_index = x;
    2f72:	41 c7 83 d0 04 00 00 07 00 00 00 	movl   $0x7,0x4d0(%r11)
      my_thread_data[n] = &thread_data[n]; 
    2f7d:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2f81:	48 89 68 18          	mov    %rbp,0x18(%rax)
    2f85:	4c 89 60 20          	mov    %r12,0x20(%rax)
    2f89:	48 89 78 28          	mov    %rdi,0x28(%rax)
    2f8d:	bf 01 00 00 00       	mov    $0x1,%edi
    2f92:	4c 89 78 10          	mov    %r15,0x10(%rax)
    2f96:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    2f98:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    2f9d:	e8 ae f4 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2fa2:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    2fa7:	49 8d 7d 38          	lea    0x38(%r13),%rdi
    2fab:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    2fb0:	48 8d 15 d9 1c 00 00 	lea    0x1cd9(%rip),%rdx        # 4c90 <io_thread>
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
    2fdb:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    2fe0:	48 8b 44 24 50       	mov    0x50(%rsp),%rax

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2fe5:	be 08 00 00 00       	mov    $0x8,%esi
    2fea:	bf 06 00 00 00       	mov    $0x6,%edi
    thread_data[x].task_count = 0;
    2fef:	49 89 9b b0 05 00 00 	mov    %rbx,0x5b0(%r11)
    2ff6:	31 db                	xor    %ebx,%ebx
    thread_data[x].type = EXTERNAL;
    2ff8:	41 c7 83 88 05 00 00 03 00 00 00 	movl   $0x3,0x588(%r11)
    thread_data[x].buffers = &buffers[buffer_index];
    3003:	49 89 83 c0 05 00 00 	mov    %rax,0x5c0(%r11)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    300a:	e8 91 f3 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    300f:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    3014:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3019:	48 8d 15 40 09 00 00 	lea    0x940(%rip),%rdx        # 3960 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    3020:	4c 89 70 08          	mov    %r14,0x8(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3024:	48 8b 74 24 58       	mov    0x58(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3029:	4c 89 18             	mov    %r11,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    302c:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
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
    3057:	49 89 83 90 05 00 00 	mov    %rax,0x590(%r11)
      my_thread_data[n] = &thread_data[n]; 
    305e:	4c 89 78 10          	mov    %r15,0x10(%rax)
    thread_data[x].thread_count = thread_count;
    3062:	48 8b 05 ef 49 00 00 	mov    0x49ef(%rip),%rax        # 7a58 <_IO_stdin_used+0xa58>
    thread_data[x].thread_index = x;
    3069:	41 c7 83 80 05 00 00 08 00 00 00 	movl   $0x8,0x580(%r11)
    thread_data[x].thread_count = thread_count;
    3074:	49 89 83 98 05 00 00 	mov    %rax,0x598(%r11)
    thread_data[x].thread_index = x;
    307b:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
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
    30c8:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    30cd:	4d 89 f3             	mov    %r14,%r11
    30d0:	4d 8d 6e 28          	lea    0x28(%r14),%r13
    printf("Finished thread %d\n", x);
  }
  long total = 0;
    30d4:	45 31 f6             	xor    %r14d,%r14d
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    30d7:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    30df:	4d 89 ef             	mov    %r13,%r15
  long received = 0;
    30e2:	31 db                	xor    %ebx,%ebx
  long sents = 0;
    30e4:	31 ed                	xor    %ebp,%ebp
    30e6:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  long ingests = 0;
    30eb:	45 31 c9             	xor    %r9d,%r9d
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    30ee:	4d 89 f5             	mov    %r14,%r13
    30f1:	4c 89 5c 24 20       	mov    %r11,0x20(%rsp)
    30f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    if (x % 2 == 1) {
    3100:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    3104:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    3109:	89 f8                	mov    %edi,%eax
    310b:	41 89 fc             	mov    %edi,%r12d
      other = (x + 1) % total_threads;
    310e:	83 c7 01             	add    $0x1,%edi
    if (x % 2 == 1) {
    3111:	83 e0 01             	and    $0x1,%eax
      other = abs(x - 1) % total_threads;
    3114:	41 83 ec 01          	sub    $0x1,%r12d
      other = (x + 1) % total_threads;
    3118:	89 7c 24 10          	mov    %edi,0x10(%rsp)
      other = abs(x - 1) % total_threads;
    311c:	85 c0                	test   %eax,%eax
    311e:	44 0f 44 e7          	cmove  %edi,%r12d
    3122:	bf 0a 00 00 00       	mov    $0xa,%edi
    3127:	e8 a4 f1 ff ff       	call   22d0 <putchar@plt>
    312c:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3131:	bf 01 00 00 00       	mov    $0x1,%edi
    3136:	48 8d 35 6e 42 00 00 	lea    0x426e(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    313d:	48 8b 10             	mov    (%rax),%rdx
    3140:	31 c0                	xor    %eax,%eax
    3142:	e8 09 f3 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3147:	49 63 57 08          	movslq 0x8(%r15),%rdx
    314b:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3150:	85 d2                	test   %edx,%edx
    3152:	0f 8e 9f 03 00 00    	jle    34f7 <main+0xf07>
    3158:	49 8b 07             	mov    (%r15),%rax
    315b:	48 c1 e2 09          	shl    $0x9,%rdx
    315f:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    long v = 0;
    3163:	31 d2                	xor    %edx,%edx
    3165:	0f 1f 00             	nopl   (%rax)
      v += thread_data[me].tasks[n].v;
    3168:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    316f:	48 05 00 02 00 00    	add    $0x200,%rax
    3175:	48 39 f0             	cmp    %rsi,%rax
    3178:	75 ee                	jne    3168 <main+0xb78>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    317a:	4d 63 e4             	movslq %r12d,%r12
    317d:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3182:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    3186:	49 8d 04 44          	lea    (%r12,%rax,2),%rax
    318a:	48 c1 e0 04          	shl    $0x4,%rax
    318e:	48 01 f8             	add    %rdi,%rax
    3191:	48 63 70 30          	movslq 0x30(%rax),%rsi
    3195:	85 f6                	test   %esi,%esi
    3197:	7e 21                	jle    31ba <main+0xbca>
    3199:	48 8b 40 28          	mov    0x28(%rax),%rax
    319d:	48 c1 e6 09          	shl    $0x9,%rsi
    31a1:	48 01 c6             	add    %rax,%rsi
    31a4:	0f 1f 40 00          	nopl   0x0(%rax)
      v += thread_data[other].tasks[n].v;
    31a8:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    31af:	48 05 00 02 00 00    	add    $0x200,%rax
    31b5:	48 39 c6             	cmp    %rax,%rsi
    31b8:	75 ee                	jne    31a8 <main+0xbb8>
    31ba:	48 8d 35 ff 41 00 00 	lea    0x41ff(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    31c1:	bf 01 00 00 00       	mov    $0x1,%edi
    31c6:	31 c0                	xor    %eax,%eax
    31c8:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    31cd:	e8 7e f2 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    31d2:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    31d7:	bf 01 00 00 00       	mov    $0x1,%edi
    31dc:	48 8b 30             	mov    (%rax),%rsi
    31df:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    31e9:	48 f7 ee             	imul   %rsi
    31ec:	48 c1 fe 3f          	sar    $0x3f,%rsi
    31f0:	31 c0                	xor    %eax,%eax
    31f2:	48 d1 fa             	sar    %rdx
    31f5:	48 29 f2             	sub    %rsi,%rdx
    31f8:	48 8d 35 31 44 00 00 	lea    0x4431(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    31ff:	e8 4c f2 ff ff       	call   2450 <__printf_chk@plt>
    3204:	bf 0a 00 00 00       	mov    $0xa,%edi
    3209:	e8 c2 f0 ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    320e:	49 63 47 08          	movslq 0x8(%r15),%rax
    3212:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3217:	85 c0                	test   %eax,%eax
    3219:	7e 79                	jle    3294 <main+0xca4>
    321b:	49 8b 17             	mov    (%r15),%rdx
    321e:	48 c1 e0 09          	shl    $0x9,%rax
    3222:	48 8d 34 10          	lea    (%rax,%rdx,1),%rsi
    3226:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3230:	48 8b 82 68 01 00 00 	mov    0x168(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    3237:	4c 03 aa 08 01 00 00 	add    0x108(%rdx),%r13
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    323e:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
      ingests += thread_data[x].tasks[n].ingest_count;
    3245:	4c 03 b2 60 ff ff ff 	add    -0xa0(%rdx),%r14
      sends += thread_data[x].tasks[n].sends;
    324c:	4c 03 8a 70 ff ff ff 	add    -0x90(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3253:	48 03 68 10          	add    0x10(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3257:	48 03 58 18          	add    0x18(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    325b:	48 03 68 30          	add    0x30(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    325f:	48 03 58 38          	add    0x38(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3263:	48 03 68 50          	add    0x50(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3267:	48 03 58 58          	add    0x58(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    326b:	48 03 68 70          	add    0x70(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    326f:	48 03 58 78          	add    0x78(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3273:	48 03 a8 90 00 00 00 	add    0x90(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    327a:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3281:	48 03 a8 b0 00 00 00 	add    0xb0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3288:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    328f:	48 39 f2             	cmp    %rsi,%rdx
    3292:	75 9c                	jne    3230 <main+0xc40>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3294:	45 31 e4             	xor    %r12d,%r12d
    3297:	49 83 7f 68 00       	cmpq   $0x0,0x68(%r15)
    329c:	7e 78                	jle    3316 <main+0xd26>
    329e:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    32a3:	4c 89 fb             	mov    %r15,%rbx
    32a6:	4d 89 e7             	mov    %r12,%r15
    32a9:	4d 89 cc             	mov    %r9,%r12
    32ac:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    32b0:	48 8b 43 58          	mov    0x58(%rbx),%rax
    32b4:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    32b8:	48 83 ec 08          	sub    $0x8,%rsp
    32bc:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    32c1:	49 83 c7 01          	add    $0x1,%r15
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    32c5:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32c9:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    32d3:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    32d7:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    32db:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    32de:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    32e2:	4c 2b 01             	sub    (%rcx),%r8
    32e5:	31 c0                	xor    %eax,%eax
    32e7:	8b 49 20             	mov    0x20(%rcx),%ecx
    32ea:	56                   	push   %rsi
    32eb:	48 8d 35 5e 43 00 00 	lea    0x435e(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    32f2:	48 c1 ea 12          	shr    $0x12,%rdx
    32f6:	49 89 d1             	mov    %rdx,%r9
    32f9:	ba 02 00 00 00       	mov    $0x2,%edx
    32fe:	e8 4d f1 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3303:	58                   	pop    %rax
    3304:	5a                   	pop    %rdx
    3305:	4c 39 7b 68          	cmp    %r15,0x68(%rbx)
    3309:	7f a5                	jg     32b0 <main+0xcc0>
    330b:	49 89 df             	mov    %rbx,%r15
    330e:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    3313:	4d 89 e1             	mov    %r12,%r9
  for (int x = 0 ; x < thread_count ; x++) {
    3316:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    331c:	49 81 c7 b0 00 00 00 	add    $0xb0,%r15
    3323:	83 7c 24 10 06       	cmpl   $0x6,0x10(%rsp)
    3328:	0f 85 d2 fd ff ff    	jne    3100 <main+0xb10>
    332e:	4c 89 ea             	mov    %r13,%rdx
    3331:	48 8d 35 95 40 00 00 	lea    0x4095(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    3338:	31 c0                	xor    %eax,%eax
    333a:	4d 89 cf             	mov    %r9,%r15
    333d:	bf 01 00 00 00       	mov    $0x1,%edi
    3342:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3347:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    3351:	e8 fa f0 ff ff       	call   2450 <__printf_chk@plt>
    3356:	bf 0a 00 00 00       	mov    $0xa,%edi
    335b:	e8 70 ef ff ff       	call   22d0 <putchar@plt>
    3360:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    3365:	bf 01 00 00 00       	mov    $0x1,%edi
    336a:	48 8d 35 2f 43 00 00 	lea    0x432f(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    3371:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3375:	31 c0                	xor    %eax,%eax
    3377:	e8 d4 f0 ff ff       	call   2450 <__printf_chk@plt>
    337c:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3381:	bf 01 00 00 00       	mov    $0x1,%edi
    3386:	48 8d 35 3b 43 00 00 	lea    0x433b(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    338d:	4c 89 c8             	mov    %r9,%rax
    3390:	49 c1 f9 3f          	sar    $0x3f,%r9
    3394:	49 f7 ec             	imul   %r12
    3397:	31 c0                	xor    %eax,%eax
    3399:	48 d1 fa             	sar    %rdx
    339c:	4c 29 ca             	sub    %r9,%rdx
    339f:	e8 ac f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    33a4:	4c 89 f8             	mov    %r15,%rax
    33a7:	4d 89 fb             	mov    %r15,%r11
    33aa:	bf 01 00 00 00       	mov    $0x1,%edi
    33af:	49 f7 ec             	imul   %r12
    33b2:	49 c1 fb 3f          	sar    $0x3f,%r11
    33b6:	48 8d 35 3b 43 00 00 	lea    0x433b(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    33bd:	31 c0                	xor    %eax,%eax
    33bf:	48 d1 fa             	sar    %rdx
    33c2:	4c 29 da             	sub    %r11,%rdx
    33c5:	e8 86 f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    33ca:	4c 89 e8             	mov    %r13,%rax
    33cd:	4c 89 e9             	mov    %r13,%rcx
    33d0:	bf 01 00 00 00       	mov    $0x1,%edi
    33d5:	49 f7 ec             	imul   %r12
    33d8:	48 c1 f9 3f          	sar    $0x3f,%rcx
    33dc:	48 8d 35 45 43 00 00 	lea    0x4345(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    33e3:	31 c0                	xor    %eax,%eax
    33e5:	48 d1 fa             	sar    %rdx
    33e8:	48 29 ca             	sub    %rcx,%rdx
    33eb:	e8 60 f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    33f0:	48 89 e8             	mov    %rbp,%rax
    33f3:	48 c1 fd 3f          	sar    $0x3f,%rbp
    33f7:	48 8d 35 e3 3f 00 00 	lea    0x3fe3(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    33fe:	49 f7 ec             	imul   %r12
    3401:	bf 01 00 00 00       	mov    $0x1,%edi
    3406:	31 c0                	xor    %eax,%eax
    3408:	48 d1 fa             	sar    %rdx
    340b:	48 29 ea             	sub    %rbp,%rdx
    340e:	e8 3d f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3413:	48 89 d8             	mov    %rbx,%rax
    3416:	48 c1 fb 3f          	sar    $0x3f,%rbx
    341a:	48 8d 35 d1 3f 00 00 	lea    0x3fd1(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    3421:	49 f7 ec             	imul   %r12
    3424:	bf 01 00 00 00       	mov    $0x1,%edi
    3429:	48 d1 fa             	sar    %rdx
    342c:	48 29 da             	sub    %rbx,%rdx
    342f:	31 c0                	xor    %eax,%eax
    3431:	e8 1a f0 ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3436:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    343e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3447:	0f 85 b1 00 00 00    	jne    34fe <main+0xf0e>
    344d:	48 81 c4 98 00 00 00 	add    $0x98,%rsp
    3454:	31 c0                	xor    %eax,%eax
    3456:	5b                   	pop    %rbx
    3457:	5d                   	pop    %rbp
    3458:	41 5c                	pop    %r12
    345a:	41 5d                	pop    %r13
    345c:	41 5e                	pop    %r14
    345e:	41 5f                	pop    %r15
    3460:	c3                   	ret
    3461:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          thread_data[x].tasks[y].run = barriered_work; 
    3468:	48 8d 05 e1 21 00 00 	lea    0x21e1(%rip),%rax        # 5650 <barriered_work>
    346f:	bb 02 00 00 00       	mov    $0x2,%ebx
    3474:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    347b:	e9 d8 f4 ff ff       	jmp    2958 <main+0x368>
      other = (x + 1) % total_threads;
    3480:	45 89 f2             	mov    %r14d,%r10d
    3483:	44 89 f5             	mov    %r14d,%ebp
      thread_data[x].thread_index = 0;
    3486:	41 c7 07 00 00 00 00 	movl   $0x0,(%r15)
    348d:	4c 89 f9             	mov    %r15,%rcx
      other = (x + 1) % total_threads;
    3490:	4d 69 d2 39 8e e3 38 	imul   $0x38e38e39,%r10,%r10
      my_thread_data[0] = &thread_data[x]; 
    3497:	4c 89 3b             	mov    %r15,(%rbx)
    349a:	bf 01 00 00 00       	mov    $0x1,%edi
    349f:	48 8d 35 63 3e 00 00 	lea    0x3e63(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      other = (x + 1) % total_threads;
    34a6:	49 c1 ea 21          	shr    $0x21,%r10
    34aa:	43 8d 04 d2          	lea    (%r10,%r10,8),%eax
    34ae:	29 c5                	sub    %eax,%ebp
      my_thread_data[1] = &thread_data[other]; 
    34b0:	48 63 c5             	movslq %ebp,%rax
    34b3:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    34b7:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    34bb:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    34c0:	44 89 e2             	mov    %r12d,%edx
    34c3:	49 c1 e0 04          	shl    $0x4,%r8
    34c7:	49 01 c0             	add    %rax,%r8
    34ca:	31 c0                	xor    %eax,%eax
    34cc:	4c 89 43 08          	mov    %r8,0x8(%rbx)
    34d0:	e8 7b ef ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    34d5:	49 8d 45 18          	lea    0x18(%r13),%rax
    34d9:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    34de:	49 89 c5             	mov    %rax,%r13
    34e1:	e9 5e f3 ff ff       	jmp    2844 <main+0x254>
          CPU_SET(j, sendercpu);
    34e6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    34eb:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
        for (int j = 0 ; j < cores ; j++) {
    34f2:	e9 c4 f3 ff ff       	jmp    28bb <main+0x2cb>
    long v = 0;
    34f7:	31 d2                	xor    %edx,%edx
    34f9:	e9 7c fc ff ff       	jmp    317a <main+0xb8a>
}
    34fe:	e8 2d ee ff ff       	call   2330 <__stack_chk_fail@plt>
    3503:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    350d:	0f 1f 00             	nopl   (%rax)

0000000000003510 <_start>:
    3510:	f3 0f 1e fa          	endbr64
    3514:	31 ed                	xor    %ebp,%ebp
    3516:	49 89 d1             	mov    %rdx,%r9
    3519:	5e                   	pop    %rsi
    351a:	48 89 e2             	mov    %rsp,%rdx
    351d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3521:	50                   	push   %rax
    3522:	54                   	push   %rsp
    3523:	45 31 c0             	xor    %r8d,%r8d
    3526:	31 c9                	xor    %ecx,%ecx
    3528:	48 8d 3d c1 f0 ff ff 	lea    -0xf3f(%rip),%rdi        # 25f0 <main>
    352f:	ff 15 a3 6a 00 00    	call   *0x6aa3(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3535:	f4                   	hlt
    3536:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003540 <deregister_tm_clones>:
    3540:	48 8d 3d d9 6a 00 00 	lea    0x6ad9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3547:	48 8d 05 d2 6a 00 00 	lea    0x6ad2(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    354e:	48 39 f8             	cmp    %rdi,%rax
    3551:	74 15                	je     3568 <deregister_tm_clones+0x28>
    3553:	48 8b 05 86 6a 00 00 	mov    0x6a86(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    355a:	48 85 c0             	test   %rax,%rax
    355d:	74 09                	je     3568 <deregister_tm_clones+0x28>
    355f:	ff e0                	jmp    *%rax
    3561:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3568:	c3                   	ret
    3569:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003570 <register_tm_clones>:
    3570:	48 8d 3d a9 6a 00 00 	lea    0x6aa9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3577:	48 8d 35 a2 6a 00 00 	lea    0x6aa2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    357e:	48 29 fe             	sub    %rdi,%rsi
    3581:	48 89 f0             	mov    %rsi,%rax
    3584:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3588:	48 c1 f8 03          	sar    $0x3,%rax
    358c:	48 01 c6             	add    %rax,%rsi
    358f:	48 d1 fe             	sar    %rsi
    3592:	74 14                	je     35a8 <register_tm_clones+0x38>
    3594:	48 8b 05 55 6a 00 00 	mov    0x6a55(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    359b:	48 85 c0             	test   %rax,%rax
    359e:	74 08                	je     35a8 <register_tm_clones+0x38>
    35a0:	ff e0                	jmp    *%rax
    35a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    35a8:	c3                   	ret
    35a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000035b0 <__do_global_dtors_aux>:
    35b0:	f3 0f 1e fa          	endbr64
    35b4:	80 3d 6d 6a 00 00 00 	cmpb   $0x0,0x6a6d(%rip)        # a028 <completed.0>
    35bb:	75 2b                	jne    35e8 <__do_global_dtors_aux+0x38>
    35bd:	55                   	push   %rbp
    35be:	48 83 3d 32 6a 00 00 00 	cmpq   $0x0,0x6a32(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    35c6:	48 89 e5             	mov    %rsp,%rbp
    35c9:	74 0c                	je     35d7 <__do_global_dtors_aux+0x27>
    35cb:	48 8b 3d 36 6a 00 00 	mov    0x6a36(%rip),%rdi        # a008 <__dso_handle>
    35d2:	e8 d9 ec ff ff       	call   22b0 <__cxa_finalize@plt>
    35d7:	e8 64 ff ff ff       	call   3540 <deregister_tm_clones>
    35dc:	c6 05 45 6a 00 00 01 	movb   $0x1,0x6a45(%rip)        # a028 <completed.0>
    35e3:	5d                   	pop    %rbp
    35e4:	c3                   	ret
    35e5:	0f 1f 00             	nopl   (%rax)
    35e8:	c3                   	ret
    35e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000035f0 <frame_dummy>:
    35f0:	f3 0f 1e fa          	endbr64
    35f4:	e9 77 ff ff ff       	jmp    3570 <register_tm_clones>
    35f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003600 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3600:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3604:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    360b:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    360f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3617:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    361b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    361f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3626:	48 85 c9             	test   %rcx,%rcx
    3629:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3630:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3634:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3638:	31 c0                	xor    %eax,%eax
    363a:	c3                   	ret
    363b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003640 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3640:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3644:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    364b:	85 c9                	test   %ecx,%ecx
    364d:	7e 4f                	jle    369e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    364f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3656:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    365d:	48 c1 e1 09          	shl    $0x9,%rcx
    3661:	48 8b 50 10          	mov    0x10(%rax),%rdx
    3665:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3669:	48 8b 70 28          	mov    0x28(%rax),%rsi
    366d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    366f:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    3673:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3678:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3680:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3688:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3693:	48 05 00 02 00 00    	add    $0x200,%rax
    3699:	48 39 c1             	cmp    %rax,%rcx
    369c:	75 da                	jne    3678 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    369e:	0f ae f8             	sfence
}
    36a1:	31 c0                	xor    %eax,%eax
    36a3:	c3                   	ret
    36a4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    36af:	90                   	nop

00000000000036b0 <barriered_thread>:
void* barriered_thread(void *arg) {
    36b0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    36b4:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    36b8:	0f 85 90 02 00 00    	jne    394e <barriered_thread+0x29e>
void* barriered_thread(void *arg) {
    36be:	41 56                	push   %r14
    36c0:	41 55                	push   %r13
    36c2:	49 89 fd             	mov    %rdi,%r13
    36c5:	41 54                	push   %r12
    36c7:	55                   	push   %rbp
    36c8:	31 ed                	xor    %ebp,%ebp
    36ca:	53                   	push   %rbx
    36cb:	31 db                	xor    %ebx,%ebx
    36cd:	0f 1f 00             	nopl   (%rax)
    if (t >= data->task_count) {
    36d0:	41 8b 55 30          	mov    0x30(%r13),%edx
    36d4:	39 da                	cmp    %ebx,%edx
    36d6:	7f 12                	jg     36ea <barriered_thread+0x3a>
      data->cycles++;
    36d8:	49 83 85 98 00 00 00 01 	addq   $0x1,0x98(%r13)
    for (; t < data->task_count; t++) {
    36e0:	31 db                	xor    %ebx,%ebx
    36e2:	85 d2                	test   %edx,%edx
    36e4:	0f 8e 56 01 00 00    	jle    3840 <barriered_thread+0x190>
    36ea:	4c 63 e3             	movslq %ebx,%r12
    36ed:	49 c1 e4 09          	shl    $0x9,%r12
    36f1:	eb 17                	jmp    370a <barriered_thread+0x5a>
    36f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    36f8:	83 c3 01             	add    $0x1,%ebx
    36fb:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    3702:	39 d3                	cmp    %edx,%ebx
    3704:	0f 8d 36 01 00 00    	jge    3840 <barriered_thread+0x190>
      if (data->tasks[t].available == 1) {
    370a:	49 8b 45 28          	mov    0x28(%r13),%rax
    370e:	4a 8d 34 20          	lea    (%rax,%r12,1),%rsi
    3712:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    3719:	75 dd                	jne    36f8 <barriered_thread+0x48>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    371b:	41 8b 7d 18          	mov    0x18(%r13),%edi
          previous = t - 1;
    371f:	83 ea 01             	sub    $0x1,%edx
    3722:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3725:	85 db                	test   %ebx,%ebx
    3727:	0f 4f d1             	cmovg  %ecx,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    372a:	85 ff                	test   %edi,%edi
    372c:	0f 8e 3e 01 00 00    	jle    3870 <barriered_thread+0x1c0>
    3732:	49 8b 45 10          	mov    0x10(%r13),%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3736:	48 63 ca             	movslq %edx,%rcx
    3739:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    373c:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    373f:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    3746:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    374d:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    3751:	45 31 f6             	xor    %r14d,%r14d
    3754:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3758:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3760:	48 8b 10             	mov    (%rax),%rdx
    3763:	4c 8b 5a 28          	mov    0x28(%rdx),%r11
    3767:	49 01 cb             	add    %rcx,%r11
    376a:	4c 89 da             	mov    %r11,%rdx
    376d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    3774:	75 04                	jne    377a <barriered_thread+0xca>
            arrived++;
    3776:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    377a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    3781:	75 04                	jne    3787 <barriered_thread+0xd7>
            prearrive++;
    3783:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3787:	48 83 c0 08          	add    $0x8,%rax
    378b:	48 39 f0             	cmp    %rsi,%rax
    378e:	75 d0                	jne    3760 <barriered_thread+0xb0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    3790:	44 39 d7             	cmp    %r10d,%edi
    3793:	0f 84 c7 00 00 00    	je     3860 <barriered_thread+0x1b0>
    3799:	45 85 d2             	test   %r10d,%r10d
    379c:	0f 84 be 00 00 00    	je     3860 <barriered_thread+0x1b0>
        if (arrived == 0 || arrived == data->thread_count) {
    37a2:	45 85 f6             	test   %r14d,%r14d
    37a5:	74 0a                	je     37b1 <barriered_thread+0x101>
    37a7:	45 39 75 18          	cmp    %r14d,0x18(%r13)
    37ab:	0f 85 8f 00 00 00    	jne    3840 <barriered_thread+0x190>
    37b1:	49 8b 45 28          	mov    0x28(%r13),%rax
          data->tasks[t].prearrive++;
    37b5:	4c 01 e0             	add    %r12,%rax
    37b8:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    37bf:	85 db                	test   %ebx,%ebx
    37c1:	75 0e                	jne    37d1 <barriered_thread+0x121>
    37c3:	49 8b 75 70          	mov    0x70(%r13),%rsi
    37c7:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    37cb:	0f 8c 5f 01 00 00    	jl     3930 <barriered_thread+0x280>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    37d1:	49 63 4d 00          	movslq 0x0(%r13),%rcx
    37d5:	49 8b 55 10          	mov    0x10(%r13),%rdx
          data->tasks[t].available = 0;
    37d9:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    37e3:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    37e7:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
    37eb:	4c 01 e7             	add    %r12,%rdi
    37ee:	ff 90 18 01 00 00    	call   *0x118(%rax)
          data->tasks[t].arrived++;
    37f4:	49 8b 45 28          	mov    0x28(%r13),%rax
    37f8:	4c 01 e0             	add    %r12,%rax
    37fb:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3802:	41 8b 45 30          	mov    0x30(%r13),%eax
          data->iteration_count++;
    3806:	49 83 45 68 01       	addq   $0x1,0x68(%r13)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    380b:	83 e8 01             	sub    $0x1,%eax
    380e:	39 d8                	cmp    %ebx,%eax
    3810:	0f 84 b2 00 00 00    	je     38c8 <barriered_thread+0x218>
          asm volatile ("sfence" ::: "memory");
    3816:	0f ae f8             	sfence
          if (waiting == 0) {
    3819:	85 ed                	test   %ebp,%ebp
    381b:	0f 84 d7 00 00 00    	je     38f8 <barriered_thread+0x248>
    for (; t < data->task_count; t++) {
    3821:	41 8b 55 30          	mov    0x30(%r13),%edx
    3825:	83 c3 01             	add    $0x1,%ebx
    3828:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    382f:	39 d3                	cmp    %edx,%ebx
    3831:	0f 8c d3 fe ff ff    	jl     370a <barriered_thread+0x5a>
    3837:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  while (data->running == 1) {
    3840:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
    3845:	0f 84 85 fe ff ff    	je     36d0 <barriered_thread+0x20>
}
    384b:	5b                   	pop    %rbx
    384c:	31 c0                	xor    %eax,%eax
    384e:	5d                   	pop    %rbp
    384f:	41 5c                	pop    %r12
    3851:	41 5d                	pop    %r13
    3853:	41 5e                	pop    %r14
    3855:	c3                   	ret
    3856:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
    3860:	83 fd 01             	cmp    $0x1,%ebp
    3863:	74 1b                	je     3880 <barriered_thread+0x1d0>
        int arrived = 0; 
    3865:	31 ed                	xor    %ebp,%ebp
    3867:	e9 36 ff ff ff       	jmp    37a2 <barriered_thread+0xf2>
    386c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    3870:	83 fd 01             	cmp    $0x1,%ebp
    3873:	0f 85 3c ff ff ff    	jne    37b5 <barriered_thread+0x105>
        int arrived = 0; 
    3879:	45 31 f6             	xor    %r14d,%r14d
    387c:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3880:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    3887:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    388c:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    388e:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3892:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    3899:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    389e:	e8 6d ea ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    38a3:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    38aa:	48 83 c0 01          	add    $0x1,%rax
    38ae:	48 99                	cqto
    38b0:	49 f7 bd 90 00 00 00 	idivq  0x90(%r13)
    38b7:	49 89 95 88 00 00 00 	mov    %rdx,0x88(%r13)
            waiting = 0; 
    38be:	e9 df fe ff ff       	jmp    37a2 <barriered_thread+0xf2>
    38c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    38c8:	49 8b 75 70          	mov    0x70(%r13),%rsi
    38cc:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    38d0:	0f 8d 40 ff ff ff    	jge    3816 <barriered_thread+0x166>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    38d6:	48 c1 e6 04          	shl    $0x4,%rsi
    38da:	bf 04 00 00 00       	mov    $0x4,%edi
    38df:	49 03 75 60          	add    0x60(%r13),%rsi
    38e3:	e8 28 ea ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    38e8:	49 83 45 70 01       	addq   $0x1,0x70(%r13)
    38ed:	e9 24 ff ff ff       	jmp    3816 <barriered_thread+0x166>
    38f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    38f8:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    38ff:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3904:	bd 01 00 00 00       	mov    $0x1,%ebp
            data->task_snapshot[data->task_timestamp_count].task = t;
    3909:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    390d:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    3914:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3918:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    391b:	e8 f0 e9 ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3920:	41 8b 55 30          	mov    0x30(%r13),%edx
    3924:	e9 cf fd ff ff       	jmp    36f8 <barriered_thread+0x48>
    3929:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3930:	48 c1 e6 04          	shl    $0x4,%rsi
    3934:	bf 04 00 00 00       	mov    $0x4,%edi
    3939:	49 03 75 58          	add    0x58(%r13),%rsi
    393d:	e8 ce e9 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3942:	49 8b 45 28          	mov    0x28(%r13),%rax
    3946:	4c 01 e0             	add    %r12,%rax
    3949:	e9 83 fe ff ff       	jmp    37d1 <barriered_thread+0x121>
}
    394e:	31 c0                	xor    %eax,%eax
    3950:	c3                   	ret
    3951:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    395c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003960 <external_thread>:
void * external_thread(void *arg) {
    3960:	f3 0f 1e fa          	endbr64
    3964:	41 55                	push   %r13
    3966:	41 54                	push   %r12
    3968:	55                   	push   %rbp
    3969:	53                   	push   %rbx
    396a:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    396e:	66 0f 6f 05 ca 3f 00 00 	movdqa 0x3fca(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
void * external_thread(void *arg) {
    3976:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    397f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3984:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3986:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
  struct timespec req = {
    398a:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    398e:	75 64                	jne    39f4 <external_thread+0x94>
    3990:	49 89 fd             	mov    %rdi,%r13
    3993:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3998:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    399b:	4c 8d 25 62 36 00 00 	lea    0x3662(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    39a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    nanosleep(&req , &rem);
    39a8:	48 89 ee             	mov    %rbp,%rsi
    39ab:	48 89 df             	mov    %rbx,%rdi
    39ae:	e8 9d e9 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    39b3:	49 8b 45 40          	mov    0x40(%r13),%rax
    39b7:	48 63 10             	movslq (%rax),%rdx
    39ba:	85 d2                	test   %edx,%edx
    39bc:	7e 2c                	jle    39ea <external_thread+0x8a>
    39be:	48 8b 40 08          	mov    0x8(%rax),%rax
    39c2:	48 c1 e2 04          	shl    $0x4,%rdx
    39c6:	48 01 c2             	add    %rax,%rdx
    39c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    39d0:	8b 48 08             	mov    0x8(%rax),%ecx
    39d3:	85 c9                	test   %ecx,%ecx
    39d5:	75 0a                	jne    39e1 <external_thread+0x81>
        data->buffers->buffer[x].data = "Hello world";
    39d7:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    39da:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    39e1:	48 83 c0 10          	add    $0x10,%rax
    39e5:	48 39 c2             	cmp    %rax,%rdx
    39e8:	75 e6                	jne    39d0 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    39ea:	0f ae f0             	mfence
  while (data->running == 1) {
    39ed:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
    39f2:	74 b4                	je     39a8 <external_thread+0x48>
}
    39f4:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    39f9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3a02:	75 0d                	jne    3a11 <external_thread+0xb1>
    3a04:	48 83 c4 38          	add    $0x38,%rsp
    3a08:	31 c0                	xor    %eax,%eax
    3a0a:	5b                   	pop    %rbx
    3a0b:	5d                   	pop    %rbp
    3a0c:	41 5c                	pop    %r12
    3a0e:	41 5d                	pop    %r13
    3a10:	c3                   	ret
    3a11:	e8 1a e9 ff ff       	call   2330 <__stack_chk_fail@plt>
    3a16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003a20 <timer_thread>:
void* timer_thread(void *arg) {
    3a20:	f3 0f 1e fa          	endbr64
    3a24:	41 57                	push   %r15
    3a26:	48 8d 35 e3 35 00 00 	lea    0x35e3(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3a2d:	49 89 ff             	mov    %rdi,%r15
    3a30:	41 56                	push   %r14
    3a32:	41 55                	push   %r13
    3a34:	41 54                	push   %r12
    3a36:	55                   	push   %rbp
    3a37:	53                   	push   %rbx
    3a38:	48 83 ec 58          	sub    $0x58,%rsp
    3a3c:	8b 17                	mov    (%rdi),%edx
    3a3e:	bf 01 00 00 00       	mov    $0x1,%edi
    3a43:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3a4c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3a51:	31 c0                	xor    %eax,%eax
    3a53:	e8 f8 e9 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3a58:	66 0f 6f 05 e0 3e 00 00 	movdqa 0x3ee0(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3a60:	ba 88 13 00 00       	mov    $0x1388,%edx
    3a65:	31 c0                	xor    %eax,%eax
    3a67:	48 8d 35 b4 35 00 00 	lea    0x35b4(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3a6e:	bf 01 00 00 00       	mov    $0x1,%edi
    3a73:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3a78:	e8 d3 e9 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3a7d:	45 8b 67 34          	mov    0x34(%r15),%r12d
    3a81:	45 85 e4             	test   %r12d,%r12d
    3a84:	0f 84 9b 00 00 00    	je     3b25 <timer_thread+0x105>
  int n = 0;
    3a8a:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    3a8d:	45 31 e4             	xor    %r12d,%r12d
    3a90:	49 89 e5             	mov    %rsp,%r13
    y++;
    3a93:	31 db                	xor    %ebx,%ebx
    3a95:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    3a9a:	48 89 ef             	mov    %rbp,%rdi
    3a9d:	4c 89 ee             	mov    %r13,%rsi
    n++;
    3aa0:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3aa4:	e8 a7 e8 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3aa9:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3aad:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ab2:	85 c0                	test   %eax,%eax
    3ab4:	7e 47                	jle    3afd <timer_thread+0xdd>
    3ab6:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3aba:	49 c1 e4 09          	shl    $0x9,%r12
    3abe:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3ac2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3ac8:	4c 8b 11             	mov    (%rcx),%r10
    3acb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3acd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3ad1:	99                   	cltd
    3ad2:	41 f7 7a 30          	idivl  0x30(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3ad6:	49 8b 72 28          	mov    0x28(%r10),%rsi
    3ada:	48 63 d2             	movslq %edx,%rdx
    3add:	48 c1 e2 09          	shl    $0x9,%rdx
    3ae1:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3aec:	42 c7 84 26 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3af8:	49 39 c8             	cmp    %rcx,%r8
    3afb:	75 cb                	jne    3ac8 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    3afd:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3b00:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3b04:	41 8b 57 34          	mov    0x34(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3b08:	48 8b 00             	mov    (%rax),%rax
    y++;
    3b0b:	39 78 30             	cmp    %edi,0x30(%rax)
    3b0e:	0f 4e fb             	cmovle %ebx,%edi
    3b11:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3b14:	85 d2                	test   %edx,%edx
    3b16:	74 0d                	je     3b25 <timer_thread+0x105>
    3b18:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3b1f:	0f 85 75 ff ff ff    	jne    3a9a <timer_thread+0x7a>
    3b25:	48 8d 3d 0c 35 00 00 	lea    0x350c(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3b2c:	e8 bf e7 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b31:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3b35:	85 d2                	test   %edx,%edx
    3b37:	7e 6b                	jle    3ba4 <timer_thread+0x184>
    for (int y = 0 ; y < data->task_count ; y++) {
    3b39:	49 63 47 30          	movslq 0x30(%r15),%rax
    3b3d:	85 c0                	test   %eax,%eax
    3b3f:	7e 63                	jle    3ba4 <timer_thread+0x184>
    3b41:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3b45:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3b49:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3b51:	31 ff                	xor    %edi,%edi
    3b53:	48 89 c2             	mov    %rax,%rdx
    3b56:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3b5a:	48 8b 40 28          	mov    0x28(%rax),%rax
    3b5e:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3b62:	f6 c6 02             	test   $0x2,%dh
    3b65:	74 15                	je     3b7c <timer_thread+0x15c>
    3b67:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3b71:	48 05 00 02 00 00    	add    $0x200,%rax
    3b77:	48 39 c6             	cmp    %rax,%rsi
    3b7a:	74 1f                	je     3b9b <timer_thread+0x17b>
      data->threads[x]->tasks[y].sending = 0;
    3b7c:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3b86:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3b8c:	c7 80 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3b96:	48 39 c6             	cmp    %rax,%rsi
    3b99:	75 e1                	jne    3b7c <timer_thread+0x15c>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b9b:	48 83 c7 08          	add    $0x8,%rdi
    3b9f:	48 39 f9             	cmp    %rdi,%rcx
    3ba2:	75 b2                	jne    3b56 <timer_thread+0x136>
  asm volatile ("mfence" ::: "memory");
    3ba4:	0f ae f0             	mfence
  struct timespec drain = {
    3ba7:	66 0f 6f 05 a1 3d 00 00 	movdqa 0x3da1(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3baf:	48 8d 2d a7 34 00 00 	lea    0x34a7(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3bb6:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bbb:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3bbf:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bc4:	85 c0                	test   %eax,%eax
    3bc6:	7e 4c                	jle    3c14 <timer_thread+0x1f4>
    3bc8:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3bcc:	4d 63 c4             	movslq %r12d,%r8
    3bcf:	49 c1 e0 09          	shl    $0x9,%r8
    3bd3:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3bd7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3be0:	48 8b 19             	mov    (%rcx),%rbx
    3be3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3be5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3be9:	99                   	cltd
    3bea:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3bed:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3bf1:	48 63 d2             	movslq %edx,%rdx
    3bf4:	48 c1 e2 09          	shl    $0x9,%rdx
    3bf8:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3c03:	42 c7 84 06 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c0f:	4c 39 c9             	cmp    %r9,%rcx
    3c12:	75 cc                	jne    3be0 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    3c14:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3c17:	49 8b 47 10          	mov    0x10(%r15),%rax
    y++;
    3c1b:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3c1e:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3c21:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3c24:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3c28:	41 8b 7f 20          	mov    0x20(%r15),%edi
    3c2c:	85 ff                	test   %edi,%edi
    3c2e:	0f 8e bc 00 00 00    	jle    3cf0 <timer_thread+0x2d0>
    3c34:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    3c37:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3c3d:	0f 1f 00             	nopl   (%rax)
    3c40:	4a 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbx
            all_empty = 0;
    3c48:	45 31 f6             	xor    %r14d,%r14d
    3c4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3c50:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3c54:	4c 89 f0             	mov    %r14,%rax
    3c57:	48 c1 e0 09          	shl    $0x9,%rax
    3c5b:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3c5f:	31 d2                	xor    %edx,%edx
    3c61:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3c68:	eb 16                	jmp    3c80 <timer_thread+0x260>
    3c6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3c70:	4d 85 c0             	test   %r8,%r8
    3c73:	7f 1f                	jg     3c94 <timer_thread+0x274>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3c75:	83 c2 01             	add    $0x1,%edx
    3c78:	48 83 c0 20          	add    $0x20,%rax
    3c7c:	39 fa                	cmp    %edi,%edx
    3c7e:	74 2a                	je     3caa <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3c80:	48 8b 08             	mov    (%rax),%rcx
    3c83:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3c87:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3c8b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3c8f:	48 85 c9             	test   %rcx,%rcx
    3c92:	7e dc                	jle    3c70 <timer_thread+0x250>
    3c94:	bf 01 00 00 00       	mov    $0x1,%edi
    3c99:	48 89 ee             	mov    %rbp,%rsi
    3c9c:	31 c0                	xor    %eax,%eax
    3c9e:	e8 ad e7 ff ff       	call   2450 <__printf_chk@plt>
            break;
    3ca3:	41 8b 7f 20          	mov    0x20(%r15),%edi
            all_empty = 0;
    3ca7:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3caa:	49 83 c6 01          	add    $0x1,%r14
    3cae:	44 39 f7             	cmp    %r14d,%edi
    3cb1:	7e 0d                	jle    3cc0 <timer_thread+0x2a0>
    3cb3:	49 8b 47 10          	mov    0x10(%r15),%rax
    3cb7:	eb 97                	jmp    3c50 <timer_thread+0x230>
    3cb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3cc0:	49 83 c5 01          	add    $0x1,%r13
    3cc4:	44 39 ef             	cmp    %r13d,%edi
    3cc7:	7e 0d                	jle    3cd6 <timer_thread+0x2b6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3cc9:	85 ff                	test   %edi,%edi
    3ccb:	7e 09                	jle    3cd6 <timer_thread+0x2b6>
    3ccd:	49 8b 47 10          	mov    0x10(%r15),%rax
    3cd1:	e9 6a ff ff ff       	jmp    3c40 <timer_thread+0x220>
    if (all_empty == 1) {
    3cd6:	41 83 f9 01          	cmp    $0x1,%r9d
    3cda:	74 14                	je     3cf0 <timer_thread+0x2d0>
      nanosleep(&drain , &drainrem);
    3cdc:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3ce1:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3ce6:	e8 65 e6 ff ff       	call   2350 <nanosleep@plt>
    3ceb:	e9 cb fe ff ff       	jmp    3bbb <timer_thread+0x19b>
    3cf0:	48 8d 3d 5d 33 00 00 	lea    0x335d(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3cf7:	e8 f4 e5 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3cfc:	41 8b 47 34          	mov    0x34(%r15),%eax
    3d00:	85 c0                	test   %eax,%eax
    3d02:	0f 84 cf 00 00 00    	je     3dd7 <timer_thread+0x3b7>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d08:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3d0c:	85 c9                	test   %ecx,%ecx
    3d0e:	7e 2d                	jle    3d3d <timer_thread+0x31d>
    3d10:	49 8b 47 10          	mov    0x10(%r15),%rax
    3d14:	31 db                	xor    %ebx,%ebx
    3d16:	48 8d 2d 51 33 00 00 	lea    0x3351(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3d1d:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->running = 0;
    3d20:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3d24:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3d28:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3d2f:	0f 84 cf 00 00 00    	je     3e04 <timer_thread+0x3e4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d35:	48 83 c3 01          	add    $0x1,%rbx
    3d39:	39 d9                	cmp    %ebx,%ecx
    3d3b:	7f e3                	jg     3d20 <timer_thread+0x300>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d3d:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3d41:	85 d2                	test   %edx,%edx
    3d43:	7e 7b                	jle    3dc0 <timer_thread+0x3a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3d45:	49 63 47 30          	movslq 0x30(%r15),%rax
    3d49:	85 c0                	test   %eax,%eax
    3d4b:	7e 73                	jle    3dc0 <timer_thread+0x3a0>
    3d4d:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3d51:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3d55:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3d5d:	31 c9                	xor    %ecx,%ecx
    3d5f:	48 89 c6             	mov    %rax,%rsi
    3d62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3d68:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3d6c:	48 8b 40 28          	mov    0x28(%rax),%rax
    3d70:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3d74:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3d7a:	74 1c                	je     3d98 <timer_thread+0x378>
    3d7c:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3d86:	48 05 00 02 00 00    	add    $0x200,%rax
    3d8c:	48 39 d0             	cmp    %rdx,%rax
    3d8f:	74 26                	je     3db7 <timer_thread+0x397>
    3d91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3d98:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3da2:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3da8:	c7 80 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3db2:	48 39 d0             	cmp    %rdx,%rax
    3db5:	75 e1                	jne    3d98 <timer_thread+0x378>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3db7:	48 83 c1 08          	add    $0x8,%rcx
    3dbb:	48 39 f9             	cmp    %rdi,%rcx
    3dbe:	75 a8                	jne    3d68 <timer_thread+0x348>
    asm volatile ("mfence" ::: "memory");
    3dc0:	0f ae f0             	mfence
    3dc3:	48 8d 3d b6 32 00 00 	lea    0x32b6(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3dca:	e8 21 e5 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3dcf:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
    3dd7:	48 8d 3d a9 32 00 00 	lea    0x32a9(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3dde:	e8 0d e5 ff ff       	call   22f0 <puts@plt>
}
    3de3:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3de8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3df1:	75 47                	jne    3e3a <timer_thread+0x41a>
    3df3:	48 83 c4 58          	add    $0x58,%rsp
    3df7:	31 c0                	xor    %eax,%eax
    3df9:	5b                   	pop    %rbx
    3dfa:	5d                   	pop    %rbp
    3dfb:	41 5c                	pop    %r12
    3dfd:	41 5d                	pop    %r13
    3dff:	41 5e                	pop    %r14
    3e01:	41 5f                	pop    %r15
    3e03:	c3                   	ret
    3e04:	48 89 ef             	mov    %rbp,%rdi
    3e07:	e8 e4 e4 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3e0c:	49 8b 47 10          	mov    0x10(%r15),%rax
    3e10:	be 01 00 00 00       	mov    $0x1,%esi
    3e15:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3e19:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3e1d:	8b 78 50             	mov    0x50(%rax),%edi
    3e20:	e8 db e5 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3e25:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3e29:	39 d9                	cmp    %ebx,%ecx
    3e2b:	0f 8e 0c ff ff ff    	jle    3d3d <timer_thread+0x31d>
    3e31:	49 8b 47 10          	mov    0x10(%r15),%rax
    3e35:	e9 e6 fe ff ff       	jmp    3d20 <timer_thread+0x300>
}
    3e3a:	e8 f1 e4 ff ff       	call   2330 <__stack_chk_fail@plt>
    3e3f:	90                   	nop

0000000000003e40 <strtolower>:
void strtolower(char *str) {
    3e40:	f3 0f 1e fa          	endbr64
    3e44:	55                   	push   %rbp
    3e45:	53                   	push   %rbx
    3e46:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3e4a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3e4e:	84 db                	test   %bl,%bl
    3e50:	74 24                	je     3e76 <strtolower+0x36>
    3e52:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3e55:	e8 b6 e6 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3e5a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3e60:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3e63:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3e67:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3e6a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3e6d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3e72:	84 db                	test   %bl,%bl
    3e74:	75 ea                	jne    3e60 <strtolower+0x20>
}
    3e76:	48 83 c4 08          	add    $0x8,%rsp
    3e7a:	5b                   	pop    %rbx
    3e7b:	5d                   	pop    %rbp
    3e7c:	c3                   	ret
    3e7d:	0f 1f 00             	nopl   (%rax)

0000000000003e80 <zh_malloc>:
void *zh_malloc(size_t size) {
    3e80:	f3 0f 1e fa          	endbr64
    3e84:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3e88:	e8 83 e5 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3e8d:	48 85 c0             	test   %rax,%rax
    3e90:	74 05                	je     3e97 <zh_malloc+0x17>
}
    3e92:	48 83 c4 08          	add    $0x8,%rsp
    3e96:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3e97:	48 8b 0d 82 61 00 00 	mov    0x6182(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    3e9e:	ba 28 00 00 00       	mov    $0x28,%edx
    3ea3:	be 01 00 00 00       	mov    $0x1,%esi
    3ea8:	48 8d 3d 59 35 00 00 	lea    0x3559(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    3eaf:	e8 0c e6 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    3eb4:	bf 01 00 00 00       	mov    $0x1,%edi
    3eb9:	e8 e2 e5 ff ff       	call   24a0 <exit@plt>
    3ebe:	66 90                	xchg   %ax,%ax

0000000000003ec0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3ec0:	f3 0f 1e fa          	endbr64
    3ec4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    3ec5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3eca:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3ecd:	e8 8e e4 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3ed2:	48 85 c0             	test   %rax,%rax
    3ed5:	74 11                	je     3ee8 <get_filename_ext+0x28>
    3ed7:	48 39 c3             	cmp    %rax,%rbx
    3eda:	74 0c                	je     3ee8 <get_filename_ext+0x28>
    return dot + 1;
    3edc:	48 83 c0 01          	add    $0x1,%rax
}
    3ee0:	5b                   	pop    %rbx
    3ee1:	c3                   	ret
    3ee2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    3ee8:	48 8d 05 e0 31 00 00 	lea    0x31e0(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    3eef:	5b                   	pop    %rbx
    3ef0:	c3                   	ret
    3ef1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3efc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003f00 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3f00:	f3 0f 1e fa          	endbr64
    3f04:	41 55                	push   %r13
    3f06:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3f09:	48 89 fe             	mov    %rdi,%rsi
    3f0c:	41 54                	push   %r12
    3f0e:	55                   	push   %rbp
    3f0f:	48 89 d5             	mov    %rdx,%rbp
    3f12:	ba 00 04 00 00       	mov    $0x400,%edx
    3f17:	53                   	push   %rbx
    3f18:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3f1f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3f28:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3f30:	31 c0                	xor    %eax,%eax
    3f32:	49 89 e4             	mov    %rsp,%r12
    3f35:	4c 89 e7             	mov    %r12,%rdi
    3f38:	e8 f3 e4 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    3f3d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3f42:	84 db                	test   %bl,%bl
    3f44:	74 24                	je     3f6a <send_headers+0x6a>
        *str = (char)tolower(*str);
    3f46:	e8 c5 e5 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3f4b:	48 8b 08             	mov    (%rax),%rcx
    3f4e:	4c 89 e0             	mov    %r12,%rax
    3f51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3f58:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3f5b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3f5f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3f62:	48 0f be 18          	movsbq (%rax),%rbx
    3f66:	84 db                	test   %bl,%bl
    3f68:	75 ee                	jne    3f58 <send_headers+0x58>
    void *buf = malloc(size);
    3f6a:	bf 11 00 00 00       	mov    $0x11,%edi
    3f6f:	e8 9c e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3f74:	48 85 c0             	test   %rax,%rax
    3f77:	0f 84 7e 04 00 00    	je     43fb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3f7d:	66 0f 6f 05 db 39 00 00 	movdqa 0x39db(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    3f85:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    3f89:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3f8e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3f96:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3f9a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3f9d:	e8 6e e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3fa2:	48 85 c0             	test   %rax,%rax
    3fa5:	0f 84 50 04 00 00    	je     43fb <send_headers+0x4fb>
    3fab:	66 0f 6f 05 bd 39 00 00 	movdqa 0x39bd(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    3fb3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    3fb7:	4c 89 e7             	mov    %r12,%rdi
    3fba:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3fc4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3fcc:	0f 11 00             	movups %xmm0,(%rax)
    3fcf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3fd3:	be 2e 00 00 00       	mov    $0x2e,%esi
    3fd8:	e8 83 e3 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3fdd:	48 85 c0             	test   %rax,%rax
    3fe0:	0f 84 ea 02 00 00    	je     42d0 <send_headers+0x3d0>
    3fe6:	4c 39 e0             	cmp    %r12,%rax
    3fe9:	0f 84 e1 02 00 00    	je     42d0 <send_headers+0x3d0>
    return dot + 1;
    3fef:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3ff3:	48 8d 3d a3 30 00 00 	lea    0x30a3(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    3ffa:	48 89 de             	mov    %rbx,%rsi
    3ffd:	e8 ae e3 ff ff       	call   23b0 <strcmp@plt>
    4002:	85 c0                	test   %eax,%eax
    4004:	75 20                	jne    4026 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4006:	66 0f 6f 05 72 39 00 00 	movdqa 0x3972(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    400e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4016:	66 0f 6f 05 72 39 00 00 	movdqa 0x3972(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    401e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4026:	48 89 de             	mov    %rbx,%rsi
    4029:	48 8d 3d 71 30 00 00 	lea    0x3071(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    4030:	e8 7b e3 ff ff       	call   23b0 <strcmp@plt>
    4035:	85 c0                	test   %eax,%eax
    4037:	75 20                	jne    4059 <send_headers+0x159>
    4039:	66 0f 6f 05 3f 39 00 00 	movdqa 0x393f(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4041:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4049:	66 0f 6f 05 3f 39 00 00 	movdqa 0x393f(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    4051:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4059:	48 89 de             	mov    %rbx,%rsi
    405c:	48 8d 3d 43 30 00 00 	lea    0x3043(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    4063:	e8 48 e3 ff ff       	call   23b0 <strcmp@plt>
    4068:	85 c0                	test   %eax,%eax
    406a:	0f 84 10 02 00 00    	je     4280 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4070:	48 89 de             	mov    %rbx,%rsi
    4073:	48 8d 3d 30 30 00 00 	lea    0x3030(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    407a:	e8 31 e3 ff ff       	call   23b0 <strcmp@plt>
    407f:	85 c0                	test   %eax,%eax
    4081:	0f 84 a9 02 00 00    	je     4330 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4087:	48 89 de             	mov    %rbx,%rsi
    408a:	48 8d 3d 1d 30 00 00 	lea    0x301d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4091:	e8 1a e3 ff ff       	call   23b0 <strcmp@plt>
    4096:	85 c0                	test   %eax,%eax
    4098:	0f 84 6a 02 00 00    	je     4308 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    409e:	48 89 de             	mov    %rbx,%rsi
    40a1:	48 8d 3d 49 30 00 00 	lea    0x3049(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    40a8:	e8 03 e3 ff ff       	call   23b0 <strcmp@plt>
    40ad:	85 c0                	test   %eax,%eax
    40af:	0f 84 2b 02 00 00    	je     42e0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    40b5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    40b8:	0f 84 52 01 00 00    	je     4210 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    40be:	48 89 de             	mov    %rbx,%rsi
    40c1:	48 8d 3d ea 2f 00 00 	lea    0x2fea(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    40c8:	e8 e3 e2 ff ff       	call   23b0 <strcmp@plt>
    40cd:	85 c0                	test   %eax,%eax
    40cf:	0f 84 ab 02 00 00    	je     4380 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    40d5:	48 89 de             	mov    %rbx,%rsi
    40d8:	48 8d 3d d7 2f 00 00 	lea    0x2fd7(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    40df:	e8 cc e2 ff ff       	call   23b0 <strcmp@plt>
    40e4:	85 c0                	test   %eax,%eax
    40e6:	0f 84 6c 02 00 00    	je     4358 <send_headers+0x458>
    slen = strlen(send_buffer);
    40ec:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    40f4:	4c 89 e7             	mov    %r12,%rdi
    40f7:	e8 24 e2 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    40fc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    40ff:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4102:	e8 09 e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4107:	48 85 c0             	test   %rax,%rax
    410a:	0f 84 eb 02 00 00    	je     43fb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4110:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4114:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4118:	83 fb 08             	cmp    $0x8,%ebx
    411b:	0f 83 3f 01 00 00    	jae    4260 <send_headers+0x360>
    4121:	f6 c3 04             	test   $0x4,%bl
    4124:	0f 85 7b 02 00 00    	jne    43a5 <send_headers+0x4a5>
    412a:	85 db                	test   %ebx,%ebx
    412c:	74 13                	je     4141 <send_headers+0x241>
    412e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4136:	88 10                	mov    %dl,(%rax)
    4138:	f6 c3 02             	test   $0x2,%bl
    413b:	0f 85 96 02 00 00    	jne    43d7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4141:	4d 89 e8             	mov    %r13,%r8
    4144:	48 8d 0d 6f 2f 00 00 	lea    0x2f6f(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    414b:	4c 89 e7             	mov    %r12,%rdi
    414e:	31 c0                	xor    %eax,%eax
    4150:	ba 00 04 00 00       	mov    $0x400,%edx
    4155:	be 01 00 00 00       	mov    $0x1,%esi
    415a:	e8 c1 e3 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    415f:	4c 89 e7             	mov    %r12,%rdi
    4162:	e8 b9 e1 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4167:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    416a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    416d:	e8 9e e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4172:	48 85 c0             	test   %rax,%rax
    4175:	0f 84 80 02 00 00    	je     43fb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    417b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    417f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4183:	83 fb 08             	cmp    $0x8,%ebx
    4186:	0f 83 1c 01 00 00    	jae    42a8 <send_headers+0x3a8>
    418c:	f6 c3 04             	test   $0x4,%bl
    418f:	0f 85 29 02 00 00    	jne    43be <send_headers+0x4be>
    4195:	85 db                	test   %ebx,%ebx
    4197:	74 13                	je     41ac <send_headers+0x2ac>
    4199:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    41a1:	88 10                	mov    %dl,(%rax)
    41a3:	f6 c3 02             	test   $0x2,%bl
    41a6:	0f 85 3d 02 00 00    	jne    43e9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    41ac:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    41b1:	bf 02 00 00 00       	mov    $0x2,%edi
    41b6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    41be:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    41c6:	e8 45 e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    41cb:	48 85 c0             	test   %rax,%rax
    41ce:	0f 84 27 02 00 00    	je     43fb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    41d4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    41dc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    41e0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    41e8:	66 89 10             	mov    %dx,(%rax)
}
    41eb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    41f3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    41fc:	0f 85 20 02 00 00    	jne    4422 <send_headers+0x522>
    4202:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4209:	5b                   	pop    %rbx
    420a:	5d                   	pop    %rbp
    420b:	41 5c                	pop    %r12
    420d:	41 5d                	pop    %r13
    420f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4210:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4214:	0f 85 a4 fe ff ff    	jne    40be <send_headers+0x1be>
    421a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    421e:	0f 85 9a fe ff ff    	jne    40be <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4224:	66 0f 6f 05 b4 37 00 00 	movdqa 0x37b4(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    422c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4236:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    423e:	66 0f 6f 05 aa 37 00 00 	movdqa 0x37aa(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    4246:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    424e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4256:	e9 63 fe ff ff       	jmp    40be <send_headers+0x1be>
    425b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4260:	89 da                	mov    %ebx,%edx
    4262:	48 89 c7             	mov    %rax,%rdi
    4265:	4c 89 e6             	mov    %r12,%rsi
    4268:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    426d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4272:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4275:	c1 e9 03             	shr    $0x3,%ecx
    4278:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    427b:	e9 c1 fe ff ff       	jmp    4141 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4280:	66 0f 6f 05 f8 36 00 00 	movdqa 0x36f8(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4288:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4290:	66 0f 6f 05 08 37 00 00 	movdqa 0x3708(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4298:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    42a0:	e9 cb fd ff ff       	jmp    4070 <send_headers+0x170>
    42a5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    42a8:	89 da                	mov    %ebx,%edx
    42aa:	48 89 c7             	mov    %rax,%rdi
    42ad:	4c 89 e6             	mov    %r12,%rsi
    42b0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    42b5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    42ba:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    42bd:	c1 e9 03             	shr    $0x3,%ecx
    42c0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    42c3:	e9 e4 fe ff ff       	jmp    41ac <send_headers+0x2ac>
    42c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    42d0:	48 8d 1d f8 2d 00 00 	lea    0x2df8(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    42d7:	e9 94 fd ff ff       	jmp    4070 <send_headers+0x170>
    42dc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    42e0:	66 0f 6f 05 d8 36 00 00 	movdqa 0x36d8(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    42e8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    42f0:	66 0f 6f 05 d8 36 00 00 	movdqa 0x36d8(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    42f8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4300:	e9 b0 fd ff ff       	jmp    40b5 <send_headers+0x1b5>
    4305:	0f 1f 00             	nopl   (%rax)
    4308:	66 0f 6f 05 b0 36 00 00 	movdqa 0x36b0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4310:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4318:	66 0f 6f 05 b0 36 00 00 	movdqa 0x36b0(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4320:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4328:	e9 71 fd ff ff       	jmp    409e <send_headers+0x19e>
    432d:	0f 1f 00             	nopl   (%rax)
    4330:	66 0f 6f 05 48 36 00 00 	movdqa 0x3648(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4338:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4340:	66 0f 6f 05 68 36 00 00 	movdqa 0x3668(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    4348:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4350:	e9 32 fd ff ff       	jmp    4087 <send_headers+0x187>
    4355:	0f 1f 00             	nopl   (%rax)
    4358:	66 0f 6f 05 60 36 00 00 	movdqa 0x3660(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4360:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4368:	66 0f 6f 05 a0 36 00 00 	movdqa 0x36a0(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4370:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4378:	e9 6f fd ff ff       	jmp    40ec <send_headers+0x1ec>
    437d:	0f 1f 00             	nopl   (%rax)
    4380:	66 0f 6f 05 38 36 00 00 	movdqa 0x3638(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4388:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4390:	66 0f 6f 05 68 36 00 00 	movdqa 0x3668(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4398:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    43a0:	e9 30 fd ff ff       	jmp    40d5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    43a5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    43ac:	89 db                	mov    %ebx,%ebx
    43ae:	89 10                	mov    %edx,(%rax)
    43b0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    43b5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    43b9:	e9 83 fd ff ff       	jmp    4141 <send_headers+0x241>
    43be:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    43c5:	89 db                	mov    %ebx,%ebx
    43c7:	89 10                	mov    %edx,(%rax)
    43c9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    43ce:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    43d2:	e9 d5 fd ff ff       	jmp    41ac <send_headers+0x2ac>
    43d7:	89 db                	mov    %ebx,%ebx
    43d9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    43df:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    43e4:	e9 58 fd ff ff       	jmp    4141 <send_headers+0x241>
    43e9:	89 db                	mov    %ebx,%ebx
    43eb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    43f1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    43f6:	e9 b1 fd ff ff       	jmp    41ac <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    43fb:	48 8b 0d 1e 5c 00 00 	mov    0x5c1e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4402:	ba 28 00 00 00       	mov    $0x28,%edx
    4407:	be 01 00 00 00       	mov    $0x1,%esi
    440c:	48 8d 3d f5 2f 00 00 	lea    0x2ff5(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4413:	e8 a8 e0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4418:	bf 01 00 00 00       	mov    $0x1,%edi
    441d:	e8 7e e0 ff ff       	call   24a0 <exit@plt>
}
    4422:	e8 09 df ff ff       	call   2330 <__stack_chk_fail@plt>
    4427:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004430 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4430:	f3 0f 1e fa          	endbr64
    4434:	41 55                	push   %r13
    4436:	49 89 d5             	mov    %rdx,%r13
    4439:	41 54                	push   %r12
    443b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    443e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4441:	55                   	push   %rbp
    4442:	53                   	push   %rbx
    4443:	48 89 f3             	mov    %rsi,%rbx
    4446:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    444a:	e8 c1 df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    444f:	48 85 c0             	test   %rax,%rax
    4452:	74 6b                	je     44bf <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4454:	4c 89 e7             	mov    %r12,%rdi
    4457:	48 89 c5             	mov    %rax,%rbp
    445a:	31 f6                	xor    %esi,%esi
    445c:	31 c0                	xor    %eax,%eax
    445e:	e8 1d e0 ff ff       	call   2480 <open@plt>
    4463:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4466:	85 c0                	test   %eax,%eax
    4468:	0f 88 e8 e0 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    446e:	48 89 da             	mov    %rbx,%rdx
    4471:	48 89 ee             	mov    %rbp,%rsi
    4474:	89 c7                	mov    %eax,%edi
    4476:	e8 15 df ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    447b:	48 98                	cltq
    447d:	48 39 d8             	cmp    %rbx,%rax
    4480:	7c 1e                	jl     44a0 <copy_file_contents+0x70>
    close(fd);
    4482:	44 89 e7             	mov    %r12d,%edi
    4485:	e8 e6 de ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    448a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    448e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4492:	48 83 c4 08          	add    $0x8,%rsp
    4496:	5b                   	pop    %rbx
    4497:	5d                   	pop    %rbp
    4498:	41 5c                	pop    %r12
    449a:	41 5d                	pop    %r13
    449c:	c3                   	ret
    449d:	0f 1f 00             	nopl   (%rax)
    44a0:	48 8b 0d 79 5b 00 00 	mov    0x5b79(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    44a7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    44ac:	be 01 00 00 00       	mov    $0x1,%esi
    44b1:	48 8d 3d 18 2c 00 00 	lea    0x2c18(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    44b8:	e8 03 e0 ff ff       	call   24c0 <fwrite@plt>
    44bd:	eb c3                	jmp    4482 <copy_file_contents+0x52>
    44bf:	48 8b 0d 5a 5b 00 00 	mov    0x5b5a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    44c6:	ba 28 00 00 00       	mov    $0x28,%edx
    44cb:	be 01 00 00 00       	mov    $0x1,%esi
    44d0:	48 8d 3d 31 2f 00 00 	lea    0x2f31(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    44d7:	e8 e4 df ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    44dc:	bf 01 00 00 00       	mov    $0x1,%edi
    44e1:	e8 ba df ff ff       	call   24a0 <exit@plt>
    44e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000044f0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    44f0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    44f4:	8b 46 44             	mov    0x44(%rsi),%eax
    44f7:	48 89 fa             	mov    %rdi,%rdx
    44fa:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    44fd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4503:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4506:	48 8b 07             	mov    (%rdi),%rax
    4509:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    450c:	f6 c1 02             	test   $0x2,%cl
    450f:	74 00                	je     4511 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4511:	89 f0                	mov    %esi,%eax
    4513:	44 29 c0             	sub    %r8d,%eax
    4516:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4519:	0f 82 43 e0 ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    451f:	c1 e9 0a             	shr    $0xa,%ecx
    4522:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4526:	8b 47 44             	mov    0x44(%rdi),%eax
    4529:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    452c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    452f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4532:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4535:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4539:	d3 e0                	shl    %cl,%eax
    453b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    453e:	48 c1 e0 06          	shl    $0x6,%rax
    4542:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4546:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    454c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    454f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4553:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4559:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4561:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4565:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4568:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    456f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4577:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    457b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    457f:	e8 bc dd ff ff       	call   2340 <io_uring_submit@plt>
}
    4584:	31 c0                	xor    %eax,%eax
    4586:	48 83 c4 08          	add    $0x8,%rsp
    458a:	c3                   	ret
    458b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004590 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4590:	f3 0f 1e fa          	endbr64
    4594:	41 55                	push   %r13
    4596:	41 89 fd             	mov    %edi,%r13d
    4599:	41 54                	push   %r12
    459b:	55                   	push   %rbp
    459c:	53                   	push   %rbx
    459d:	48 89 f3             	mov    %rsi,%rbx
    45a0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    45a4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    45a7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    45ad:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    45b0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    45b3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    45b5:	f6 c1 02             	test   $0x2,%cl
    45b8:	74 00                	je     45ba <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    45ba:	89 c2                	mov    %eax,%edx
    45bc:	29 f2                	sub    %esi,%edx
    45be:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    45c1:	0f 82 ab df ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    45c7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    45ca:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    45cd:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    45d0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    45d5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    45d8:	23 6b 58             	and    0x58(%rbx),%ebp
    45db:	d3 e5                	shl    %cl,%ebp
    45dd:	48 c1 e5 06          	shl    $0x6,%rbp
    45e1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    45e5:	e8 26 de ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    45ea:	be 01 00 00 00       	mov    $0x1,%esi
    45ef:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    45f4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    45f7:	e8 a4 dd ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    45fc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4601:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4605:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4608:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    460d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4612:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    461b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4623:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4627:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    462b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4632:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    463a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    463e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4646:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    464e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4652:	e8 e9 dc ff ff       	call   2340 <io_uring_submit@plt>
}
    4657:	48 83 c4 08          	add    $0x8,%rsp
    465b:	31 c0                	xor    %eax,%eax
    465d:	5b                   	pop    %rbx
    465e:	5d                   	pop    %rbp
    465f:	41 5c                	pop    %r12
    4661:	41 5d                	pop    %r13
    4663:	c3                   	ret
    4664:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    466f:	90                   	nop

0000000000004670 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4670:	f3 0f 1e fa          	endbr64
    4674:	41 56                	push   %r14
    4676:	41 89 f6             	mov    %esi,%r14d
    4679:	41 55                	push   %r13
    467b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    467e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4683:	41 54                	push   %r12
    4685:	55                   	push   %rbp
    4686:	48 89 d5             	mov    %rdx,%rbp
    4689:	53                   	push   %rbx
    void *buf = malloc(size);
    468a:	e8 81 dd ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    468f:	48 85 c0             	test   %rax,%rax
    4692:	0f 84 dd 00 00 00    	je     4775 <_send_static_string_content+0x105>
    4698:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    469b:	4c 89 ef             	mov    %r13,%rdi
    469e:	e8 7d dc ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    46a3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    46aa:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    46ae:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    46b1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    46b4:	e8 57 dd ff ff       	call   2410 <malloc@plt>
    46b9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    46bc:	48 85 c0             	test   %rax,%rax
    46bf:	0f 84 b0 00 00 00    	je     4775 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    46c5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    46c9:	4c 89 e2             	mov    %r12,%rdx
    46cc:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    46cf:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    46d3:	e8 08 dd ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    46d8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    46db:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    46e1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    46e4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    46e8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    46ea:	f6 c1 02             	test   $0x2,%cl
    46ed:	0f 85 7d 00 00 00    	jne    4770 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    46f3:	89 d0                	mov    %edx,%eax
    46f5:	29 f0                	sub    %esi,%eax
    46f7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    46fa:	0f 82 7c de ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4700:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4703:	8b 45 44             	mov    0x44(%rbp),%eax
    4706:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4709:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    470c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    470f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4712:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4718:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    471c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    471e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4721:	48 89 ef             	mov    %rbp,%rdi
    4724:	48 c1 e0 06          	shl    $0x6,%rax
    4728:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    472c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    472f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4733:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4739:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4741:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4745:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4748:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    474f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4757:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    475b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    475f:	5b                   	pop    %rbx
    4760:	5d                   	pop    %rbp
    4761:	41 5c                	pop    %r12
    4763:	41 5d                	pop    %r13
    4765:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4767:	e9 d4 db ff ff       	jmp    2340 <io_uring_submit@plt>
    476c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4770:	e9 7e ff ff ff       	jmp    46f3 <_send_static_string_content+0x83>
    4775:	48 8b 0d a4 58 00 00 	mov    0x58a4(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    477c:	ba 28 00 00 00       	mov    $0x28,%edx
    4781:	be 01 00 00 00       	mov    $0x1,%esi
    4786:	48 8d 3d 7b 2c 00 00 	lea    0x2c7b(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    478d:	e8 2e dd ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4792:	bf 01 00 00 00       	mov    $0x1,%edi
    4797:	e8 04 dd ff ff       	call   24a0 <exit@plt>
    479c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000047a0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    47a0:	f3 0f 1e fa          	endbr64
    47a4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    47a7:	89 fe                	mov    %edi,%esi
    47a9:	48 8b 3d 68 58 00 00 	mov    0x5868(%rip),%rdi        # a018 <unimplemented_content>
    47b0:	e9 bb fe ff ff       	jmp    4670 <_send_static_string_content>
    47b5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000047c0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    47c0:	f3 0f 1e fa          	endbr64
    47c4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    47c7:	89 fe                	mov    %edi,%esi
    47c9:	48 8b 3d 40 58 00 00 	mov    0x5840(%rip),%rdi        # a010 <http_404_content>
    47d0:	e9 9b fe ff ff       	jmp    4670 <_send_static_string_content>
    47d5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000047e0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    47e0:	f3 0f 1e fa          	endbr64
    47e4:	41 56                	push   %r14
    47e6:	41 55                	push   %r13
    47e8:	49 89 d5             	mov    %rdx,%r13
    47eb:	41 54                	push   %r12
    47ed:	41 89 f4             	mov    %esi,%r12d
    47f0:	55                   	push   %rbp
    47f1:	48 89 fd             	mov    %rdi,%rbp
    47f4:	53                   	push   %rbx
    47f5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    47fc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4805:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    480d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    480f:	e8 0c db ff ff       	call   2320 <strlen@plt>
    4814:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4819:	48 89 c3             	mov    %rax,%rbx
    481c:	0f 84 b6 00 00 00    	je     48d8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4822:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4827:	48 89 ee             	mov    %rbp,%rsi
    482a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    482e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4833:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    483b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4843:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    484e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4856:	e8 65 db ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    485b:	48 89 e6             	mov    %rsp,%rsi
    485e:	4c 89 f7             	mov    %r14,%rdi
    4861:	e8 6a db ff ff       	call   23d0 <stat@plt>
    4866:	83 f8 ff             	cmp    $0xffffffff,%eax
    4869:	0f 84 d3 00 00 00    	je     4942 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    486f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4873:	25 00 f0 00 00       	and    $0xf000,%eax
    4878:	3d 00 80 00 00       	cmp    $0x8000,%eax
    487d:	0f 84 f5 00 00 00    	je     4978 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4883:	48 8b 3d 86 57 00 00 	mov    0x5786(%rip),%rdi        # a010 <http_404_content>
    488a:	4c 89 ea             	mov    %r13,%rdx
    488d:	44 89 e6             	mov    %r12d,%esi
    4890:	e8 db fd ff ff       	call   4670 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4895:	4c 89 f2             	mov    %r14,%rdx
    4898:	bf 01 00 00 00       	mov    $0x1,%edi
    489d:	31 c0                	xor    %eax,%eax
    489f:	48 8d 35 7a 28 00 00 	lea    0x287a(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    48a6:	e8 a5 db ff ff       	call   2450 <__printf_chk@plt>
}
    48ab:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    48b3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    48bc:	0f 85 20 01 00 00    	jne    49e2 <handle_get_method+0x202>
    48c2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    48c9:	5b                   	pop    %rbx
    48ca:	5d                   	pop    %rbp
    48cb:	41 5c                	pop    %r12
    48cd:	41 5d                	pop    %r13
    48cf:	41 5e                	pop    %r14
    48d1:	c3                   	ret
    48d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    48d8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    48dd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    48e5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    48ea:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    48ed:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    48f5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    48f8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4900:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    490b:	e8 b0 da ff ff       	call   23c0 <__memcpy_chk@plt>
    4910:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4915:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    491a:	48 8d 35 ca 27 00 00 	lea    0x27ca(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4921:	48 29 d9             	sub    %rbx,%rcx
    4924:	ba 0b 00 00 00       	mov    $0xb,%edx
    4929:	e8 92 da ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    492e:	48 89 e6             	mov    %rsp,%rsi
    4931:	4c 89 f7             	mov    %r14,%rdi
    4934:	e8 97 da ff ff       	call   23d0 <stat@plt>
    4939:	83 f8 ff             	cmp    $0xffffffff,%eax
    493c:	0f 85 2d ff ff ff    	jne    486f <handle_get_method+0x8f>
    4942:	4c 89 f2             	mov    %r14,%rdx
    4945:	48 89 e9             	mov    %rbp,%rcx
    4948:	48 8d 35 a7 27 00 00 	lea    0x27a7(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    494f:	31 c0                	xor    %eax,%eax
    4951:	bf 01 00 00 00       	mov    $0x1,%edi
    4956:	e8 f5 da ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    495b:	48 8b 3d ae 56 00 00 	mov    0x56ae(%rip),%rdi        # a010 <http_404_content>
    4962:	4c 89 ea             	mov    %r13,%rdx
    4965:	44 89 e6             	mov    %r12d,%esi
    4968:	e8 03 fd ff ff       	call   4670 <_send_static_string_content>
}
    496d:	e9 39 ff ff ff       	jmp    48ab <handle_get_method+0xcb>
    4972:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4978:	bf 70 00 00 00       	mov    $0x70,%edi
    497d:	e8 8e da ff ff       	call   2410 <malloc@plt>
    4982:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4985:	48 85 c0             	test   %rax,%rax
    4988:	74 5d                	je     49e7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    498a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    498e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4993:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4997:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    499a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    49a1:	e8 5a f5 ff ff       	call   3f00 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    49a6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    49ab:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    49af:	4c 89 f7             	mov    %r14,%rdi
    49b2:	e8 79 fa ff ff       	call   4430 <copy_file_contents>
    49b7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    49bc:	4c 89 f2             	mov    %r14,%rdx
    49bf:	31 c0                	xor    %eax,%eax
    49c1:	48 8d 35 46 27 00 00 	lea    0x2746(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    49c8:	bf 01 00 00 00       	mov    $0x1,%edi
    49cd:	e8 7e da ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    49d2:	4c 89 ee             	mov    %r13,%rsi
    49d5:	48 89 df             	mov    %rbx,%rdi
    49d8:	e8 13 fb ff ff       	call   44f0 <add_write_request>
    49dd:	e9 c9 fe ff ff       	jmp    48ab <handle_get_method+0xcb>
}
    49e2:	e8 49 d9 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    49e7:	48 8b 0d 32 56 00 00 	mov    0x5632(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    49ee:	ba 28 00 00 00       	mov    $0x28,%edx
    49f3:	be 01 00 00 00       	mov    $0x1,%esi
    49f8:	48 8d 3d 09 2a 00 00 	lea    0x2a09(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    49ff:	e8 bc da ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4a04:	bf 01 00 00 00       	mov    $0x1,%edi
    4a09:	e8 92 da ff ff       	call   24a0 <exit@plt>
    4a0e:	66 90                	xchg   %ax,%ax

0000000000004a10 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4a10:	f3 0f 1e fa          	endbr64
    4a14:	41 57                	push   %r15
    4a16:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4a18:	4c 8d 35 66 26 00 00 	lea    0x2666(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4a1f:	41 55                	push   %r13
    4a21:	49 89 d5             	mov    %rdx,%r13
    4a24:	41 54                	push   %r12
    4a26:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4a29:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4a2c:	55                   	push   %rbp
    4a2d:	53                   	push   %rbx
    4a2e:	48 83 ec 18          	sub    $0x18,%rsp
    4a32:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a3b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4a40:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4a42:	49 89 e7             	mov    %rsp,%r15
    4a45:	4c 89 fa             	mov    %r15,%rdx
    4a48:	e8 33 d9 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4a4d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4a51:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4a54:	84 db                	test   %bl,%bl
    4a56:	74 1d                	je     4a75 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4a58:	e8 b3 da ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4a5d:	48 89 ea             	mov    %rbp,%rdx
    4a60:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4a63:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4a67:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4a6a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    4a6d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4a71:	84 db                	test   %bl,%bl
    4a73:	75 eb                	jne    4a60 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4a75:	4c 89 fa             	mov    %r15,%rdx
    4a78:	4c 89 f6             	mov    %r14,%rsi
    4a7b:	31 ff                	xor    %edi,%edi
    4a7d:	e8 fe d8 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4a82:	48 8d 35 aa 26 00 00 	lea    0x26aa(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4a89:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4a8c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    4a8f:	e8 1c d9 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4a94:	4c 89 ea             	mov    %r13,%rdx
    4a97:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4a9a:	85 c0                	test   %eax,%eax
    4a9c:	75 2a                	jne    4ac8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    4a9e:	48 89 df             	mov    %rbx,%rdi
    4aa1:	e8 3a fd ff ff       	call   47e0 <handle_get_method>
}
    4aa6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4aab:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4ab4:	75 20                	jne    4ad6 <handle_http_method+0xc6>
    4ab6:	48 83 c4 18          	add    $0x18,%rsp
    4aba:	5b                   	pop    %rbx
    4abb:	5d                   	pop    %rbp
    4abc:	41 5c                	pop    %r12
    4abe:	41 5d                	pop    %r13
    4ac0:	41 5e                	pop    %r14
    4ac2:	41 5f                	pop    %r15
    4ac4:	c3                   	ret
    4ac5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4ac8:	48 8b 3d 49 55 00 00 	mov    0x5549(%rip),%rdi        # a018 <unimplemented_content>
    4acf:	e8 9c fb ff ff       	call   4670 <_send_static_string_content>
}
    4ad4:	eb d0                	jmp    4aa6 <handle_http_method+0x96>
    4ad6:	e8 55 d8 ff ff       	call   2330 <__stack_chk_fail@plt>
    4adb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004ae0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4ae0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4ae4:	85 d2                	test   %edx,%edx
    4ae6:	7e 38                	jle    4b20 <get_line+0x40>
    4ae8:	48 63 d2             	movslq %edx,%rdx
    4aeb:	48 83 c7 01          	add    $0x1,%rdi
    4aef:	48 01 f2             	add    %rsi,%rdx
    4af2:	eb 11                	jmp    4b05 <get_line+0x25>
    4af4:	0f 1f 40 00          	nopl   0x0(%rax)
    4af8:	48 83 c6 01          	add    $0x1,%rsi
    4afc:	48 83 c7 01          	add    $0x1,%rdi
    4b00:	48 39 d6             	cmp    %rdx,%rsi
    4b03:	74 1b                	je     4b20 <get_line+0x40>
        dest[i] = src[i];
    4b05:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4b09:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4b0b:	3c 0d                	cmp    $0xd,%al
    4b0d:	75 e9                	jne    4af8 <get_line+0x18>
    4b0f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4b12:	75 e4                	jne    4af8 <get_line+0x18>
            dest[i] = '\0';
    4b14:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4b17:	31 c0                	xor    %eax,%eax
    4b19:	c3                   	ret
    4b1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4b20:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4b25:	c3                   	ret
    4b26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004b30 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4b30:	f3 0f 1e fa          	endbr64
    4b34:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4b3b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4b3f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b48:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4b50:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4b52:	49 89 e2             	mov    %rsp,%r10
    4b55:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4b5d:	4c 89 d0             	mov    %r10,%rax
    4b60:	eb 13                	jmp    4b75 <handle_client_request+0x45>
    4b62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b68:	48 83 c0 01          	add    $0x1,%rax
    4b6c:	48 83 c1 01          	add    $0x1,%rcx
    4b70:	4c 39 c8             	cmp    %r9,%rax
    4b73:	74 4b                	je     4bc0 <handle_client_request+0x90>
        dest[i] = src[i];
    4b75:	44 0f b6 01          	movzbl (%rcx),%r8d
    4b79:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4b7c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4b80:	75 e6                	jne    4b68 <handle_client_request+0x38>
    4b82:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4b86:	75 e0                	jne    4b68 <handle_client_request+0x38>
            dest[i] = '\0';
    4b88:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4b8b:	8b 47 08             	mov    0x8(%rdi),%eax
    4b8e:	48 89 f2             	mov    %rsi,%rdx
    4b91:	4c 89 d7             	mov    %r10,%rdi
    4b94:	89 c6                	mov    %eax,%esi
    4b96:	e8 75 fe ff ff       	call   4a10 <handle_http_method>
}
    4b9b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4ba3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4bac:	75 39                	jne    4be7 <handle_client_request+0xb7>
    4bae:	31 c0                	xor    %eax,%eax
    4bb0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4bb7:	c3                   	ret
    4bb8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4bc0:	48 8b 0d 59 54 00 00 	mov    0x5459(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4bc7:	ba 12 00 00 00       	mov    $0x12,%edx
    4bcc:	be 01 00 00 00       	mov    $0x1,%esi
    4bd1:	48 8d 3d 5f 25 00 00 	lea    0x255f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4bd8:	e8 e3 d8 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4bdd:	bf 01 00 00 00       	mov    $0x1,%edi
    4be2:	e8 b9 d8 ff ff       	call   24a0 <exit@plt>
}
    4be7:	e8 44 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
    4bec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004bf0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4bf0:	f3 0f 1e fa          	endbr64
    4bf4:	55                   	push   %rbp
    4bf5:	53                   	push   %rbx
    4bf6:	48 89 cb             	mov    %rcx,%rbx
    4bf9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4bfd:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4c00:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4c03:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4c09:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4c0c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4c0f:	f6 c1 02             	test   $0x2,%cl
    4c12:	74 00                	je     4c14 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4c14:	41 89 c0             	mov    %eax,%r8d
    4c17:	45 29 c8             	sub    %r9d,%r8d
    4c1a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4c1e:	0f 82 68 d9 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4c24:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c27:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4c2a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4c2d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4c30:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4c33:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c37:	d3 e5                	shl    %cl,%ebp
    4c39:	48 c1 e5 06          	shl    $0x6,%rbp
    4c3d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4c41:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4c44:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4c49:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4c50:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4c54:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4c58:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4c60:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4c68:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4c6c:	e8 9f d7 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4c71:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4c74:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4c7a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4c7e:	48 83 c4 08          	add    $0x8,%rsp
    4c82:	5b                   	pop    %rbx
    4c83:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4c84:	e9 b7 d6 ff ff       	jmp    2340 <io_uring_submit@plt>
    4c89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004c90 <io_thread>:
void* io_thread(void *arg) {
    4c90:	f3 0f 1e fa          	endbr64
    4c94:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4c96:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4c98:	41 56                	push   %r14
    4c9a:	41 55                	push   %r13
    4c9c:	41 54                	push   %r12
    4c9e:	55                   	push   %rbp
    4c9f:	48 89 fd             	mov    %rdi,%rbp
    4ca2:	53                   	push   %rbx
    4ca3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4caa:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4cb3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4cbb:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4cbf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4cc4:	bf 00 01 00 00       	mov    $0x100,%edi
    4cc9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4ccc:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4cd0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4cd5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4cda:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4cdf:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4ce4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4cec:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4cf1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4cf9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4cfe:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4d06:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4d0b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4d13:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4d18:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4d20:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4d25:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4d2d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4d35:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4d3d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4d45:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4d4d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4d55:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4d5d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4d65:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4d6d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4d75:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4d7d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4d84:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4d8c:	e8 5f d6 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4d91:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
    4d95:	31 f6                	xor    %esi,%esi
    4d97:	e8 44 d7 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4d9c:	31 d2                	xor    %edx,%edx
    4d9e:	be 01 00 00 00       	mov    $0x1,%esi
    4da3:	bf 02 00 00 00       	mov    $0x2,%edi
    4da8:	e8 83 d7 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4dad:	83 f8 ff             	cmp    $0xffffffff,%eax
    4db0:	0f 84 18 d8 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    4db6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4dbb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4dc1:	89 c7                	mov    %eax,%edi
    4dc3:	41 89 c4             	mov    %eax,%r12d
    4dc6:	ba 02 00 00 00       	mov    $0x2,%edx
    4dcb:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4dd0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4dd8:	e8 23 d5 ff ff       	call   2300 <setsockopt@plt>
    4ddd:	85 c0                	test   %eax,%eax
    4ddf:	0f 88 bd d7 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4de5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4dea:	ba 10 00 00 00       	mov    $0x10,%edx
    4def:	44 89 e7             	mov    %r12d,%edi
    4df2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4dfb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4e03:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4e0b:	e8 50 d6 ff ff       	call   2460 <bind@plt>
    4e10:	85 c0                	test   %eax,%eax
    4e12:	0f 88 c2 d7 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4e18:	be 0a 00 00 00       	mov    $0xa,%esi
    4e1d:	44 89 e7             	mov    %r12d,%edi
    4e20:	e8 fb d5 ff ff       	call   2420 <listen@plt>
    4e25:	85 c0                	test   %eax,%eax
    4e27:	0f 88 81 d7 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4e2d:	ba db 18 00 00       	mov    $0x18db,%edx
    4e32:	48 8d 35 43 23 00 00 	lea    0x2343(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4e39:	bf 01 00 00 00       	mov    $0x1,%edi
    4e3e:	31 c0                	xor    %eax,%eax
    4e40:	e8 0b d6 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4e45:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4e4a:	48 89 d9             	mov    %rbx,%rcx
    4e4d:	44 89 e7             	mov    %r12d,%edi
    4e50:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4e55:	48 89 c6             	mov    %rax,%rsi
    4e58:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4e5d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4e62:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4e6a:	e8 81 fd ff ff       	call   4bf0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4e6f:	bf 01 00 00 00       	mov    $0x1,%edi
    4e74:	be 10 00 00 00       	mov    $0x10,%esi
    4e79:	e8 22 d5 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    4e7e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4e83:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4e86:	e8 85 d5 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4e8b:	48 85 c0             	test   %rax,%rax
    4e8e:	0f 84 ae 04 00 00    	je     5342 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    4e94:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4e98:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e9f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    4ea6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4eae:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4eb1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4eb6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4eb8:	f6 c1 02             	test   $0x2,%cl
    4ebb:	0f 85 0f 04 00 00    	jne    52d0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    4ec1:	89 d0                	mov    %edx,%eax
    4ec3:	29 f0                	sub    %esi,%eax
    4ec5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4ecc:	0f 82 f2 d6 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4ed2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4ed5:	48 8d 75 50          	lea    0x50(%rbp),%rsi
	sqe->addr3 = 0;
    4ed9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4edd:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ee0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4ee7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4eea:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4ef1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ef8:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4efa:	8b 55 50             	mov    0x50(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4efd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4f02:	48 c1 e0 06          	shl    $0x6,%rax
    4f06:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4f0e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4f14:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4f17:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4f1f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4f23:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4f2b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4f33:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4f37:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4f3b:	e8 00 d4 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4f40:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4f44:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4f49:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4f51:	0f 85 d7 01 00 00    	jne    512e <io_thread+0x49e>
    4f57:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4f5c:	4d 89 ce             	mov    %r9,%r14
    4f5f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4f64:	0f 1f 40 00          	nopl   0x0(%rax)
    4f68:	48 8d 3d 23 22 00 00 	lea    0x2223(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    4f6f:	e8 7c d3 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4f74:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4f7b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4f82:	c1 e9 0b             	shr    $0xb,%ecx
    4f85:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4f88:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4f90:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4f92:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4f9a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4f9c:	39 d0                	cmp    %edx,%eax
    4f9e:	74 36                	je     4fd6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4fa0:	89 f8                	mov    %edi,%eax
    4fa2:	21 d0                	and    %edx,%eax
    4fa4:	d3 e0                	shl    %cl,%eax
    4fa6:	48 c1 e0 04          	shl    $0x4,%rax
    4faa:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4fb2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4fba:	0f 85 a8 01 00 00    	jne    5168 <io_thread+0x4d8>
    4fc0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4fc4:	0f 85 0e 03 00 00    	jne    52d8 <io_thread+0x648>
			if (cqe->res < 0)
    4fca:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4fcd:	83 c2 01             	add    $0x1,%edx
    4fd0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4fd2:	85 c0                	test   %eax,%eax
    4fd4:	79 b2                	jns    4f88 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    4fd6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    4fdf:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4fe0:	45 31 c0             	xor    %r8d,%r8d
    4fe3:	31 d2                	xor    %edx,%edx
    4fe5:	b9 01 00 00 00       	mov    $0x1,%ecx
    4fea:	4c 89 f6             	mov    %r14,%rsi
    4fed:	48 89 df             	mov    %rbx,%rdi
    4ff0:	e8 4b d4 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    4ff5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    4ff8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4ffd:	48 83 38 01          	cmpq   $0x1,(%rax)
    5001:	0f 84 e1 02 00 00    	je     52e8 <io_thread+0x658>
    5007:	48 8d 3d aa 21 00 00 	lea    0x21aa(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    500e:	e8 dd d2 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5013:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5018:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    501b:	45 85 ff             	test   %r15d,%r15d
    501e:	0f 88 72 d5 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    5024:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5027:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    502b:	85 c0                	test   %eax,%eax
    502d:	0f 88 d5 02 00 00    	js     5308 <io_thread+0x678>
      switch (req->event_type) {
    5033:	41 83 f8 01          	cmp    $0x1,%r8d
    5037:	0f 84 7b 01 00 00    	je     51b8 <io_thread+0x528>
    503d:	41 83 f8 02          	cmp    $0x2,%r8d
    5041:	0f 84 a1 01 00 00    	je     51e8 <io_thread+0x558>
    5047:	45 85 c0             	test   %r8d,%r8d
    504a:	0f 85 50 01 00 00    	jne    51a0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5050:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5055:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    505a:	48 89 d9             	mov    %rbx,%rcx
    505d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5061:	e8 8a fb ff ff       	call   4bf0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5066:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    506b:	48 89 de             	mov    %rbx,%rsi
    506e:	8b 78 08             	mov    0x8(%rax),%edi
    5071:	e8 1a f5 ff ff       	call   4590 <add_read_request>
              free(req);
    5076:	4c 89 e7             	mov    %r12,%rdi
    5079:	e8 42 d2 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    507e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5083:	48 85 c0             	test   %rax,%rax
    5086:	0f 85 14 01 00 00    	jne    51a0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    508c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5093:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    509a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    509d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    50a2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    50a4:	f6 c1 02             	test   $0x2,%cl
    50a7:	74 00                	je     50a9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    50a9:	89 d0                	mov    %edx,%eax
    50ab:	29 f0                	sub    %esi,%eax
    50ad:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    50b4:	0f 82 00 d5 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    50ba:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    50bd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    50c2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    50c6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50c9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    50d0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50d3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    50da:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50e1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    50e3:	8b 55 50             	mov    0x50(%rbp),%edx
    50e6:	48 c1 e0 06          	shl    $0x6,%rax
    50ea:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    50f2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    50f8:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    50fb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5103:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5107:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    510f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5117:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    511b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    511f:	e8 1c d2 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5124:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    5128:	0f 84 3a fe ff ff    	je     4f68 <io_thread+0x2d8>
    512e:	48 8d 3d bc 20 00 00 	lea    0x20bc(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    5135:	e8 b6 d1 ff ff       	call   22f0 <puts@plt>
}
    513a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5142:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    514b:	0f 85 18 02 00 00    	jne    5369 <io_thread+0x6d9>
    5151:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5158:	31 c0                	xor    %eax,%eax
    515a:	5b                   	pop    %rbx
    515b:	5d                   	pop    %rbp
    515c:	41 5c                	pop    %r12
    515e:	41 5d                	pop    %r13
    5160:	41 5e                	pop    %r14
    5162:	41 5f                	pop    %r15
    5164:	c3                   	ret
    5165:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5168:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    516d:	48 85 c0             	test   %rax,%rax
    5170:	0f 84 6a fe ff ff    	je     4fe0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5176:	48 83 38 01          	cmpq   $0x1,(%rax)
    517a:	0f 84 68 01 00 00    	je     52e8 <io_thread+0x658>
    5180:	48 8d 3d 31 20 00 00 	lea    0x2031(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    5187:	e8 64 d1 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    518c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5191:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5194:	e9 8b fe ff ff       	jmp    5024 <io_thread+0x394>
    5199:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    51a0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    51a8:	8b 02                	mov    (%rdx),%eax
    51aa:	83 c0 01             	add    $0x1,%eax
    51ad:	89 02                	mov    %eax,(%rdx)
}
    51af:	e9 d8 fe ff ff       	jmp    508c <io_thread+0x3fc>
    51b4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    51b8:	85 c0                	test   %eax,%eax
    51ba:	75 74                	jne    5230 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    51bc:	48 8b 0d 5d 4e 00 00 	mov    0x4e5d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    51c3:	ba 0f 00 00 00       	mov    $0xf,%edx
    51c8:	be 01 00 00 00       	mov    $0x1,%esi
    51cd:	48 8d 3d 0d 20 00 00 	lea    0x200d(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    51d4:	e8 e7 d2 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    51d9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    51de:	e9 a0 fe ff ff       	jmp    5083 <io_thread+0x3f3>
    51e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    51e8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    51ed:	45 31 ff             	xor    %r15d,%r15d
    51f0:	85 c0                	test   %eax,%eax
    51f2:	7e 20                	jle    5214 <io_thread+0x584>
    51f4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    51f8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    51fb:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    51ff:	48 c1 e0 04          	shl    $0x4,%rax
    5203:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5208:	e8 b3 d0 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    520d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5212:	7f e4                	jg     51f8 <io_thread+0x568>
              close(req->client_socket);
    5214:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5219:	e8 52 d1 ff ff       	call   2370 <close@plt>
              free(req);
    521e:	4c 89 e7             	mov    %r12,%rdi
    5221:	e8 9a d0 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5226:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    522b:	e9 53 fe ff ff       	jmp    5083 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5230:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5235:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    523a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5242:	eb 11                	jmp    5255 <io_thread+0x5c5>
    5244:	0f 1f 40 00          	nopl   0x0(%rax)
    5248:	48 83 c0 01          	add    $0x1,%rax
    524c:	48 83 c2 01          	add    $0x1,%rdx
    5250:	48 39 c6             	cmp    %rax,%rsi
    5253:	74 4b                	je     52a0 <io_thread+0x610>
        dest[i] = src[i];
    5255:	0f b6 0a             	movzbl (%rdx),%ecx
    5258:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    525a:	80 f9 0d             	cmp    $0xd,%cl
    525d:	75 e9                	jne    5248 <io_thread+0x5b8>
    525f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5263:	75 e3                	jne    5248 <io_thread+0x5b8>
            dest[i] = '\0';
    5265:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5268:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    526d:	48 89 da             	mov    %rbx,%rdx
    5270:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5275:	e8 96 f7 ff ff       	call   4a10 <handle_http_method>
              free(req->iov[0].iov_base);
    527a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    527f:	e8 3c d0 ff ff       	call   22c0 <free@plt>
              free(req);
    5284:	4c 89 e7             	mov    %r12,%rdi
    5287:	e8 34 d0 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    528c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5291:	e9 ed fd ff ff       	jmp    5083 <io_thread+0x3f3>
    5296:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    52a0:	48 8b 0d 79 4d 00 00 	mov    0x4d79(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    52a7:	ba 12 00 00 00       	mov    $0x12,%edx
    52ac:	be 01 00 00 00       	mov    $0x1,%esi
    52b1:	48 8d 3d 7f 1e 00 00 	lea    0x1e7f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    52b8:	e8 03 d2 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    52bd:	bf 01 00 00 00       	mov    $0x1,%edi
    52c2:	e8 d9 d1 ff ff       	call   24a0 <exit@plt>
    52c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    52d0:	e9 ec fb ff ff       	jmp    4ec1 <io_thread+0x231>
    52d5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    52d8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    52dd:	e9 94 fe ff ff       	jmp    5176 <io_thread+0x4e6>
    52e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    52e8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    52f0:	48 8d 3d ad 1e 00 00 	lea    0x1ead(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    52f7:	8b 02                	mov    (%rdx),%eax
    52f9:	83 c0 01             	add    $0x1,%eax
    52fc:	89 02                	mov    %eax,(%rdx)
    52fe:	e8 ed cf ff ff       	call   22f0 <puts@plt>
    5303:	e9 26 fe ff ff       	jmp    512e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5308:	f7 d8                	neg    %eax
    530a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    530f:	89 c7                	mov    %eax,%edi
    5311:	e8 ea d1 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5316:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    531b:	be 01 00 00 00       	mov    $0x1,%esi
    5320:	48 8b 3d f9 4c 00 00 	mov    0x4cf9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5327:	48 89 c1             	mov    %rax,%rcx
    532a:	48 8d 15 07 21 00 00 	lea    0x2107(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    5331:	31 c0                	xor    %eax,%eax
    5333:	e8 98 d1 ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5338:	bf 01 00 00 00       	mov    $0x1,%edi
    533d:	e8 5e d1 ff ff       	call   24a0 <exit@plt>
    5342:	48 8b 0d d7 4c 00 00 	mov    0x4cd7(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5349:	ba 28 00 00 00       	mov    $0x28,%edx
    534e:	be 01 00 00 00       	mov    $0x1,%esi
    5353:	48 8d 3d ae 20 00 00 	lea    0x20ae(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    535a:	e8 61 d1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    535f:	bf 01 00 00 00       	mov    $0x1,%edi
    5364:	e8 37 d1 ff ff       	call   24a0 <exit@plt>
}
    5369:	e8 c2 cf ff ff       	call   2330 <__stack_chk_fail@plt>
    536e:	66 90                	xchg   %ax,%ax

0000000000005370 <sendm>:
int sendm(struct BarrierTask *data) {
    5370:	f3 0f 1e fa          	endbr64
    5374:	41 57                	push   %r15
    5376:	41 56                	push   %r14
    5378:	41 55                	push   %r13
    537a:	41 54                	push   %r12
    537c:	55                   	push   %rbp
    537d:	53                   	push   %rbx
    537e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5382:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
    5389:	0f 85 99 01 00 00    	jne    5528 <sendm+0x1b8>
    538f:	48 8d b7 80 01 00 00 	lea    0x180(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5396:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    539c:	48 89 fa             	mov    %rdi,%rdx
    539f:	31 c9                	xor    %ecx,%ecx
    53a1:	48 89 34 24          	mov    %rsi,(%rsp)
    53a5:	48 8d b7 88 01 00 00 	lea    0x188(%rdi),%rsi
    53ac:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    53b1:	85 c0                	test   %eax,%eax
    53b3:	0f 8e ce 00 00 00    	jle    5487 <sendm+0x117>
    53b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    53c0:	39 8a 30 01 00 00    	cmp    %ecx,0x130(%rdx)
    53c6:	0f 84 af 00 00 00    	je     547b <sendm+0x10b>
        struct Data *them = data->mailboxes[n].higher;
    53cc:	49 89 ca             	mov    %rcx,%r10
    53cf:	49 c1 e2 05          	shl    $0x5,%r10
    53d3:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
    53da:	4d 8b 5a 08          	mov    0x8(%r10),%r11
        for (; them->messages_count < min;) {
    53de:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    53e2:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    53e6:	4c 39 cb             	cmp    %r9,%rbx
    53e9:	0f 8d 83 00 00 00    	jge    5472 <sendm+0x102>
    53ef:	4c 89 cf             	mov    %r9,%rdi
    53f2:	48 8b aa 08 01 00 00 	mov    0x108(%rdx),%rbp
    53f9:	4d 8b 72 10          	mov    0x10(%r10),%r14
    53fd:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    5400:	49 8b 33             	mov    (%r11),%rsi
    5403:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    5407:	48 83 f8 02          	cmp    $0x2,%rax
    540b:	0f 86 ff 00 00 00    	jbe    5510 <sendm+0x1a0>
    5411:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5419:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5421:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    5425:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    5429:	4c 39 2c 24          	cmp    %r13,(%rsp)
    542d:	73 71                	jae    54a0 <sendm+0x130>
    542f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5434:	4d 39 fc             	cmp    %r15,%r12
    5437:	73 67                	jae    54a0 <sendm+0x130>
    5439:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    543d:	49 01 f0             	add    %rsi,%r8
    5440:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    5447:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    544b:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    544f:	49 39 d8             	cmp    %rbx,%r8
    5452:	75 ec                	jne    5440 <sendm+0xd0>
    5454:	0f 1f 40 00          	nopl   0x0(%rax)
    5458:	48 01 fd             	add    %rdi,%rbp
    545b:	4c 01 f7             	add    %r14,%rdi
    545e:	48 89 aa 08 01 00 00 	mov    %rbp,0x108(%rdx)
    5465:	49 89 7a 10          	mov    %rdi,0x10(%r10)
    5469:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    546d:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5472:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5475:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    547b:	48 83 c1 01          	add    $0x1,%rcx
    547f:	39 c8                	cmp    %ecx,%eax
    5481:	0f 8f 39 ff ff ff    	jg     53c0 <sendm+0x50>
}
    5487:	48 83 c4 18          	add    $0x18,%rsp
    548b:	31 c0                	xor    %eax,%eax
    548d:	5b                   	pop    %rbx
    548e:	5d                   	pop    %rbp
    548f:	41 5c                	pop    %r12
    5491:	41 5d                	pop    %r13
    5493:	41 5e                	pop    %r14
    5495:	41 5f                	pop    %r15
    5497:	c3                   	ret
    5498:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    54a0:	49 89 fd             	mov    %rdi,%r13
    54a3:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    54aa:	4d 89 e0             	mov    %r12,%r8
    54ad:	49 d1 ed             	shr    %r13
    54b0:	49 c1 e5 04          	shl    $0x4,%r13
    54b4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    54b9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    54bd:	41 83 e5 10          	and    $0x10,%r13d
    54c1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    54c5:	74 11                	je     54d8 <sendm+0x168>
          them->messages[them->messages_count++] = data->message; 
    54c7:	49 83 c0 10          	add    $0x10,%r8
    54cb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    54d0:	4d 39 f8             	cmp    %r15,%r8
    54d3:	74 15                	je     54ea <sendm+0x17a>
    54d5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    54d8:	41 0f 11 00          	movups %xmm0,(%r8)
    54dc:	49 83 c0 20          	add    $0x20,%r8
    54e0:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    54e5:	4d 39 f8             	cmp    %r15,%r8
    54e8:	75 ee                	jne    54d8 <sendm+0x168>
    54ea:	49 89 f8             	mov    %rdi,%r8
    54ed:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    54f1:	49 01 d8             	add    %rbx,%r8
    54f4:	40 f6 c7 01          	test   $0x1,%dil
    54f8:	0f 84 5a ff ff ff    	je     5458 <sendm+0xe8>
          them->messages[them->messages_count++] = data->message; 
    54fe:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    5505:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    5509:	e9 4a ff ff ff       	jmp    5458 <sendm+0xe8>
    550e:	66 90                	xchg   %ax,%ax
    5510:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5518:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5520:	e9 14 ff ff ff       	jmp    5439 <sendm+0xc9>
    5525:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5528:	48 8d 3d d5 1c 00 00 	lea    0x1cd5(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    552f:	e8 bc cd ff ff       	call   22f0 <puts@plt>
    5534:	e9 4e ff ff ff       	jmp    5487 <sendm+0x117>
    5539:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005540 <receive>:
int receive(struct BarrierTask *data) {
    5540:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5544:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    554a:	85 c0                	test   %eax,%eax
    554c:	0f 8e f1 00 00 00    	jle    5643 <receive+0x103>
int receive(struct BarrierTask *data) {
    5552:	41 54                	push   %r12
    5554:	48 89 fa             	mov    %rdi,%rdx
    5557:	55                   	push   %rbp
    5558:	31 ed                	xor    %ebp,%ebp
    555a:	53                   	push   %rbx
    555b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5560:	48 89 ee             	mov    %rbp,%rsi
    5563:	48 c1 e6 05          	shl    $0x5,%rsi
    5567:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    556e:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5571:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    5576:	48 85 ff             	test   %rdi,%rdi
    5579:	0f 8e a1 00 00 00    	jle    5620 <receive+0xe0>
      data->sends++;
    557f:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    5586:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    558a:	4c 63 1a             	movslq (%rdx),%r11
    558d:	49 89 c9             	mov    %rcx,%r9
    5590:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5594:	49 f7 d9             	neg    %r9
    5597:	48 01 c7             	add    %rax,%rdi
    559a:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    559e:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    55a5:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    55a9:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    55ac:	49 29 c8             	sub    %rcx,%r8
    55af:	eb 10                	jmp    55c1 <receive+0x81>
    55b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    55b8:	48 83 c0 01          	add    $0x1,%rax
    55bc:	48 39 c7             	cmp    %rax,%rdi
    55bf:	74 5f                	je     5620 <receive+0xe0>
      data->n++;
    55c1:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    55c5:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
      data->n++;
    55cc:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    55d3:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    55d7:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    55db:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    55e0:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    55e4:	75 d2                	jne    55b8 <receive+0x78>
    55e6:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    55ed:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    55f1:	75 c5                	jne    55b8 <receive+0x78>
    55f3:	bf 01 00 00 00       	mov    $0x1,%edi
    55f8:	b9 01 00 00 00       	mov    $0x1,%ecx
    55fd:	ba 01 00 00 00       	mov    $0x1,%edx
    5602:	31 c0                	xor    %eax,%eax
    5604:	48 8d 35 55 1e 00 00 	lea    0x1e55(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    560b:	e8 40 ce ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5610:	bf 01 00 00 00       	mov    $0x1,%edi
    5615:	e8 86 ce ff ff       	call   24a0 <exit@plt>
    561a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5620:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    5629:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    562c:	48 83 c5 01          	add    $0x1,%rbp
    5630:	39 aa 34 01 00 00    	cmp    %ebp,0x134(%rdx)
    5636:	0f 8f 24 ff ff ff    	jg     5560 <receive+0x20>
}
    563c:	5b                   	pop    %rbx
    563d:	31 c0                	xor    %eax,%eax
    563f:	5d                   	pop    %rbp
    5640:	41 5c                	pop    %r12
    5642:	c3                   	ret
    5643:	31 c0                	xor    %eax,%eax
    5645:	c3                   	ret
    5646:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005650 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5650:	f3 0f 1e fa          	endbr64
    5654:	41 57                	push   %r15
    5656:	41 56                	push   %r14
    5658:	41 55                	push   %r13
    565a:	41 54                	push   %r12
    565c:	55                   	push   %rbp
    565d:	53                   	push   %rbx
    565e:	48 89 fb             	mov    %rdi,%rbx
    5661:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    5665:	8b 07                	mov    (%rdi),%eax
    5667:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    566d:	0f 84 3d 01 00 00    	je     57b0 <barriered_work+0x160>
    receive(data);
    5673:	e8 c8 fe ff ff       	call   5540 <receive>
    while (data->scheduled == 1) {
    5678:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    567f:	75 1b                	jne    569c <barriered_work+0x4c>
    5681:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    5688:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    5690:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5693:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    569a:	74 ec                	je     5688 <barriered_work+0x38>
  if (data->sending == 1) {
    569c:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    56a3:	0f 85 74 02 00 00    	jne    591d <barriered_work+0x2cd>
      for (int n = 0 ; n < data->thread_count; n++) {
    56a9:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    56af:	85 c0                	test   %eax,%eax
    56b1:	0f 8e 72 02 00 00    	jle    5929 <barriered_work+0x2d9>
    56b7:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    56be:	31 d2                	xor    %edx,%edx
    56c0:	48 89 0c 24          	mov    %rcx,(%rsp)
    56c4:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    56cb:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    56d0:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    56d6:	0f 84 bf 00 00 00    	je     579b <barriered_work+0x14b>
        struct Data *them = data->mailboxes[n].higher;
    56dc:	49 89 d1             	mov    %rdx,%r9
    56df:	49 c1 e1 05          	shl    $0x5,%r9
    56e3:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    56ea:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    56ee:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    56f2:	4d 63 42 10          	movslq 0x10(%r10),%r8
    56f6:	4d 39 c3             	cmp    %r8,%r11
    56f9:	0f 8d 93 00 00 00    	jge    5792 <barriered_work+0x142>
    56ff:	4c 89 c6             	mov    %r8,%rsi
    5702:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5709:	4d 8b 71 10          	mov    0x10(%r9),%r14
    570d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5710:	49 8b 0a             	mov    (%r10),%rcx
    5713:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5717:	48 83 f8 02          	cmp    $0x2,%rax
    571b:	0f 86 8f 02 00 00    	jbe    59b0 <barriered_work+0x360>
    5721:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5729:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5731:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5735:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5739:	4c 39 2c 24          	cmp    %r13,(%rsp)
    573d:	0f 83 fd 01 00 00    	jae    5940 <barriered_work+0x2f0>
    5743:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5748:	4d 39 fc             	cmp    %r15,%r12
    574b:	0f 83 ef 01 00 00    	jae    5940 <barriered_work+0x2f0>
    5751:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5755:	48 01 cf             	add    %rcx,%rdi
    5758:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5760:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5767:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    576b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    576f:	49 39 fb             	cmp    %rdi,%r11
    5772:	75 ec                	jne    5760 <barriered_work+0x110>
    5774:	0f 1f 40 00          	nopl   0x0(%rax)
    5778:	48 01 f5             	add    %rsi,%rbp
    577b:	4c 01 f6             	add    %r14,%rsi
    577e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5785:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5789:	4d 89 42 08          	mov    %r8,0x8(%r10)
    578d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5792:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5795:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    579b:	48 83 c2 01          	add    $0x1,%rdx
    579f:	39 d0                	cmp    %edx,%eax
    57a1:	0f 8f 29 ff ff ff    	jg     56d0 <barriered_work+0x80>
    57a7:	e9 7d 01 00 00       	jmp    5929 <barriered_work+0x2d9>
    57ac:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    57b0:	e8 8b fd ff ff       	call   5540 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    57b5:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    57bc:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    57be:	45 85 c9             	test   %r9d,%r9d
    57c1:	0f 8e 85 00 00 00    	jle    584c <barriered_work+0x1fc>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    57c7:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    57ce:	4c 63 d8             	movslq %eax,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    57d1:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    57d4:	49 c1 e3 09          	shl    $0x9,%r11
    57d8:	4c 8b 52 10          	mov    0x10(%rdx),%r10
              int next_task = abs((t + 1) % (data->thread_count));
    57dc:	99                   	cltd
    57dd:	41 f7 f9             	idiv   %r9d
    57e0:	4c 89 d7             	mov    %r10,%rdi
    57e3:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
    57e7:	89 d0                	mov    %edx,%eax
    57e9:	f7 d8                	neg    %eax
    57eb:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    57ee:	45 31 c0             	xor    %r8d,%r8d
              int next_task = abs((t + 1) % (data->thread_count));
    57f1:	48 63 ea             	movslq %edx,%rbp
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    57f4:	48 c1 e5 09          	shl    $0x9,%rbp
    57f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    5800:	31 c0                	xor    %eax,%eax
    5802:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5808:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    580c:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    5810:	48 8b 8c 2a 68 01 00 00 	mov    0x168(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5818:	48 8b 17             	mov    (%rdi),%rdx
    581b:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    581f:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5822:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5826:	48 c1 e2 05          	shl    $0x5,%rdx
    582a:	4a 03 94 1e 68 01 00 00 	add    0x168(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5832:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    5836:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    583a:	49 39 c1             	cmp    %rax,%r9
    583d:	75 c9                	jne    5808 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    583f:	48 83 c7 08          	add    $0x8,%rdi
    5843:	49 83 c0 20          	add    $0x20,%r8
    5847:	49 39 fc             	cmp    %rdi,%r12
    584a:	75 b4                	jne    5800 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    584c:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    584f:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5856:	31 ff                	xor    %edi,%edi
    5858:	48 c1 e6 05          	shl    $0x5,%rsi
    585c:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5863:	e8 a8 ca ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5868:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    586f:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5876:	48 8b 50 38          	mov    0x38(%rax),%rdx
    587a:	8b 4a 10             	mov    0x10(%rdx),%ecx
    587d:	8d 69 01             	lea    0x1(%rcx),%ebp
    5880:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5883:	75 53                	jne    58d8 <barriered_work+0x288>
    5885:	0f 1f 00             	nopl   (%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5888:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    588f:	48 8b 40 10          	mov    0x10(%rax),%rax
    5893:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    5896:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    589e:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    58a2:	48 c1 e7 09          	shl    $0x9,%rdi
    58a6:	48 03 78 28          	add    0x28(%rax),%rdi
    58aa:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    58b0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    58b3:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    58ba:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    58c1:	74 c5                	je     5888 <barriered_work+0x238>
    if (modcount != data->thread->protected_state->modcount) {
    58c3:	48 8b 40 38          	mov    0x38(%rax),%rax
    58c7:	3b 68 10             	cmp    0x10(%rax),%ebp
    58ca:	74 0c                	je     58d8 <barriered_work+0x288>
    58cc:	48 8d 3d 3d 19 00 00 	lea    0x193d(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    58d3:	e8 18 ca ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    58d8:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    58df:	31 ff                	xor    %edi,%edi
    58e1:	48 c1 e6 05          	shl    $0x5,%rsi
    58e5:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    58ec:	48 83 c6 10          	add    $0x10,%rsi
    58f0:	e8 1b ca ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    58f5:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    58fc:	48 83 c0 01          	add    $0x1,%rax
    5900:	48 99                	cqto
    5902:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    5909:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5910:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    5917:	0f 84 a8 00 00 00    	je     59c5 <barriered_work+0x375>
    591d:	48 8d 3d e0 18 00 00 	lea    0x18e0(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5924:	e8 c7 c9 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5929:	0f ae f8             	sfence
}
    592c:	48 83 c4 18          	add    $0x18,%rsp
    5930:	31 c0                	xor    %eax,%eax
    5932:	5b                   	pop    %rbx
    5933:	5d                   	pop    %rbp
    5934:	41 5c                	pop    %r12
    5936:	41 5d                	pop    %r13
    5938:	41 5e                	pop    %r14
    593a:	41 5f                	pop    %r15
    593c:	c3                   	ret
    593d:	0f 1f 00             	nopl   (%rax)
    5940:	49 89 f5             	mov    %rsi,%r13
    5943:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    594a:	4c 89 e7             	mov    %r12,%rdi
    594d:	49 d1 ed             	shr    %r13
    5950:	49 c1 e5 04          	shl    $0x4,%r13
    5954:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5959:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    595d:	41 83 e5 10          	and    $0x10,%r13d
    5961:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5965:	74 11                	je     5978 <barriered_work+0x328>
          them->messages[them->messages_count++] = data->message; 
    5967:	48 83 c7 10          	add    $0x10,%rdi
    596b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5970:	49 39 ff             	cmp    %rdi,%r15
    5973:	74 13                	je     5988 <barriered_work+0x338>
    5975:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5978:	0f 11 07             	movups %xmm0,(%rdi)
    597b:	48 83 c7 20          	add    $0x20,%rdi
    597f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5983:	49 39 ff             	cmp    %rdi,%r15
    5986:	75 f0                	jne    5978 <barriered_work+0x328>
    5988:	48 89 f7             	mov    %rsi,%rdi
    598b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    598f:	4c 01 df             	add    %r11,%rdi
    5992:	40 f6 c6 01          	test   $0x1,%sil
    5996:	0f 84 dc fd ff ff    	je     5778 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    599c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    59a3:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    59a7:	e9 cc fd ff ff       	jmp    5778 <barriered_work+0x128>
    59ac:	0f 1f 40 00          	nopl   0x0(%rax)
    59b0:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    59b8:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    59c0:	e9 8c fd ff ff       	jmp    5751 <barriered_work+0x101>
      for (int n = 0 ; n < data->thread_count; n++) {
    59c5:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    59cc:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    59d2:	31 d2                	xor    %edx,%edx
    59d4:	48 89 0c 24          	mov    %rcx,(%rsp)
    59d8:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    59df:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    59e4:	85 c0                	test   %eax,%eax
    59e6:	0f 8e 3d ff ff ff    	jle    5929 <barriered_work+0x2d9>
    59ec:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    59f0:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    59f6:	0f 84 af 00 00 00    	je     5aab <barriered_work+0x45b>
        struct Data *them = data->mailboxes[n].higher;
    59fc:	49 89 d1             	mov    %rdx,%r9
    59ff:	49 c1 e1 05          	shl    $0x5,%r9
    5a03:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    5a0a:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    5a0e:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5a12:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5a16:	4d 39 d8             	cmp    %r11,%r8
    5a19:	0f 8e 83 00 00 00    	jle    5aa2 <barriered_work+0x452>
    5a1f:	4c 89 c6             	mov    %r8,%rsi
    5a22:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5a29:	4d 8b 71 10          	mov    0x10(%r9),%r14
    5a2d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5a30:	49 8b 0a             	mov    (%r10),%rcx
    5a33:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5a37:	48 83 f8 02          	cmp    $0x2,%rax
    5a3b:	0f 86 ef 00 00 00    	jbe    5b30 <barriered_work+0x4e0>
    5a41:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5a49:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5a51:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5a55:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5a59:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5a5d:	73 61                	jae    5ac0 <barriered_work+0x470>
    5a5f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5a64:	4d 39 fc             	cmp    %r15,%r12
    5a67:	73 57                	jae    5ac0 <barriered_work+0x470>
    5a69:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5a6d:	48 01 cf             	add    %rcx,%rdi
    5a70:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5a77:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5a7b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5a7f:	49 39 fb             	cmp    %rdi,%r11
    5a82:	75 ec                	jne    5a70 <barriered_work+0x420>
    5a84:	0f 1f 40 00          	nopl   0x0(%rax)
    5a88:	48 01 f5             	add    %rsi,%rbp
    5a8b:	4c 01 f6             	add    %r14,%rsi
    5a8e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5a95:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5a99:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5a9d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5aa2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5aa5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5aab:	48 83 c2 01          	add    $0x1,%rdx
    5aaf:	39 d0                	cmp    %edx,%eax
    5ab1:	0f 8f 39 ff ff ff    	jg     59f0 <barriered_work+0x3a0>
    5ab7:	e9 6d fe ff ff       	jmp    5929 <barriered_work+0x2d9>
    5abc:	0f 1f 40 00          	nopl   0x0(%rax)
    5ac0:	49 89 f5             	mov    %rsi,%r13
    5ac3:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5aca:	4c 89 e7             	mov    %r12,%rdi
    5acd:	49 d1 ed             	shr    %r13
    5ad0:	49 c1 e5 04          	shl    $0x4,%r13
    5ad4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5ad9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5add:	41 83 e5 10          	and    $0x10,%r13d
    5ae1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5ae5:	74 11                	je     5af8 <barriered_work+0x4a8>
          them->messages[them->messages_count++] = data->message; 
    5ae7:	48 83 c7 10          	add    $0x10,%rdi
    5aeb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5af0:	4c 39 ff             	cmp    %r15,%rdi
    5af3:	74 13                	je     5b08 <barriered_work+0x4b8>
    5af5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5af8:	0f 11 07             	movups %xmm0,(%rdi)
    5afb:	48 83 c7 20          	add    $0x20,%rdi
    5aff:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5b03:	4c 39 ff             	cmp    %r15,%rdi
    5b06:	75 f0                	jne    5af8 <barriered_work+0x4a8>
    5b08:	48 89 f7             	mov    %rsi,%rdi
    5b0b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5b0f:	4c 01 df             	add    %r11,%rdi
    5b12:	40 f6 c6 01          	test   $0x1,%sil
    5b16:	0f 84 6c ff ff ff    	je     5a88 <barriered_work+0x438>
          them->messages[them->messages_count++] = data->message; 
    5b1c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b23:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5b27:	e9 5c ff ff ff       	jmp    5a88 <barriered_work+0x438>
    5b2c:	0f 1f 40 00          	nopl   0x0(%rax)
    5b30:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5b38:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5b40:	e9 24 ff ff ff       	jmp    5a69 <barriered_work+0x419>
    5b45:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005b50 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5b50:	f3 0f 1e fa          	endbr64
    5b54:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5b58:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5b5f:	48 8b 40 40          	mov    0x40(%rax),%rax
    5b63:	48 63 10             	movslq (%rax),%rdx
    5b66:	85 d2                	test   %edx,%edx
    5b68:	7e 2c                	jle    5b96 <barriered_work_ingest+0x46>
    5b6a:	48 8b 40 08          	mov    0x8(%rax),%rax
    5b6e:	48 c1 e2 04          	shl    $0x4,%rdx
    5b72:	48 01 c2             	add    %rax,%rdx
    5b75:	0f 1f 00             	nopl   (%rax)
    if (data->thread->buffers->buffer[x].available == 1) {
    5b78:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5b7c:	75 0f                	jne    5b8d <barriered_work_ingest+0x3d>
      data->ingest_count++;
    5b7e:	48 83 87 60 01 00 00 01 	addq   $0x1,0x160(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5b86:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5b8d:	48 83 c0 10          	add    $0x10,%rax
    5b91:	48 39 d0             	cmp    %rdx,%rax
    5b94:	75 e2                	jne    5b78 <barriered_work_ingest+0x28>
  asm volatile ("sfence" ::: "memory");
    5b96:	0f ae f8             	sfence
  barriered_work(data);
    5b99:	e8 b2 fa ff ff       	call   5650 <barriered_work>
}
    5b9e:	31 c0                	xor    %eax,%eax
    5ba0:	48 83 c4 08          	add    $0x8,%rsp
    5ba4:	c3                   	ret
    5ba5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005bb0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5bb0:	f3 0f 1e fa          	endbr64
}
    5bb4:	31 c0                	xor    %eax,%eax
    5bb6:	c3                   	ret
    5bb7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005bc0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5bc0:	f3 0f 1e fa          	endbr64
    5bc4:	31 c0                	xor    %eax,%eax
    5bc6:	c3                   	ret
    5bc7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005bd0 <after>:
int after(struct timespec left, struct timespec right) {
    5bd0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5bd4:	31 c0                	xor    %eax,%eax
    5bd6:	48 39 d7             	cmp    %rdx,%rdi
    5bd9:	7e 08                	jle    5be3 <after+0x13>
    5bdb:	31 c0                	xor    %eax,%eax
    5bdd:	48 39 ce             	cmp    %rcx,%rsi
    5be0:	0f 9f c0             	setg   %al
}
    5be3:	c3                   	ret
    5be4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5bef:	90                   	nop

0000000000005bf0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5bf0:	f3 0f 1e fa          	endbr64
    5bf4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5bf9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5bfe:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5c00:	48 39 d7             	cmp    %rdx,%rdi
    5c03:	7f 18                	jg     5c1d <within+0x2d>
    5c05:	4d 39 d8             	cmp    %r11,%r8
    5c08:	0f 9e c2             	setle  %dl
    5c0b:	48 39 ce             	cmp    %rcx,%rsi
    5c0e:	0f 9e c0             	setle  %al
    5c11:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5c13:	31 c0                	xor    %eax,%eax
    5c15:	4d 39 d1             	cmp    %r10,%r9
    5c18:	0f 9e c0             	setle  %al
    5c1b:	21 d0                	and    %edx,%eax
}
    5c1d:	c3                   	ret
    5c1e:	66 90                	xchg   %ax,%ax

0000000000005c20 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5c20:	f3 0f 1e fa          	endbr64
    5c24:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5c29:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5c2e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5c33:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5c38:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5c3d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5c42:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5c47:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5c4c:	48 39 fe             	cmp    %rdi,%rsi
    5c4f:	7d 2f                	jge    5c80 <overlap+0x60>
    5c51:	48 39 ca             	cmp    %rcx,%rdx
    5c54:	7d 62                	jge    5cb8 <overlap+0x98>
    5c56:	4d 39 da             	cmp    %r11,%r10
    5c59:	7d 0e                	jge    5c69 <overlap+0x49>
    return 1;
    5c5b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5c60:	4d 39 c1             	cmp    %r8,%r9
    5c63:	0f 8c 7f 00 00 00    	jl     5ce8 <overlap+0xc8>
  return 0;
    5c69:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5c6b:	4d 39 c1             	cmp    %r8,%r9
    5c6e:	7f 4c                	jg     5cbc <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5c70:	31 c0                	xor    %eax,%eax
    5c72:	4d 39 da             	cmp    %r11,%r10
    5c75:	0f 9e c0             	setle  %al
    5c78:	c3                   	ret
    5c79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5c80:	7e 4e                	jle    5cd0 <overlap+0xb0>
    5c82:	48 39 ca             	cmp    %rcx,%rdx
    5c85:	7f 39                	jg     5cc0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5c87:	75 31                	jne    5cba <overlap+0x9a>
    5c89:	4d 39 c1             	cmp    %r8,%r9
    5c8c:	7c 2c                	jl     5cba <overlap+0x9a>
    return 1;
    5c8e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5c93:	4d 39 da             	cmp    %r11,%r10
    5c96:	7d 24                	jge    5cbc <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5c98:	48 39 ca             	cmp    %rcx,%rdx
    5c9b:	0f 94 c2             	sete   %dl
    5c9e:	48 39 fe             	cmp    %rdi,%rsi
    5ca1:	0f 94 c0             	sete   %al
    5ca4:	21 c2                	and    %eax,%edx
    5ca6:	31 c0                	xor    %eax,%eax
    5ca8:	4d 39 c1             	cmp    %r8,%r9
    5cab:	0f 94 c0             	sete   %al
    5cae:	21 d0                	and    %edx,%eax
    5cb0:	c3                   	ret
    5cb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5cb8:	74 af                	je     5c69 <overlap+0x49>
  return 0;
    5cba:	31 c0                	xor    %eax,%eax
}
    5cbc:	c3                   	ret
    5cbd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5cc0:	4d 39 da             	cmp    %r11,%r10
    5cc3:	7e c4                	jle    5c89 <overlap+0x69>
    return 1;
    5cc5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5cca:	4d 39 c1             	cmp    %r8,%r9
    5ccd:	7e ba                	jle    5c89 <overlap+0x69>
    5ccf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5cd0:	48 39 ca             	cmp    %rcx,%rdx
    5cd3:	7c 94                	jl     5c69 <overlap+0x49>
    5cd5:	4d 39 c1             	cmp    %r8,%r9
    5cd8:	7d b4                	jge    5c8e <overlap+0x6e>
    5cda:	48 39 ca             	cmp    %rcx,%rdx
    5cdd:	74 91                	je     5c70 <overlap+0x50>
    5cdf:	eb d9                	jmp    5cba <overlap+0x9a>
    5ce1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5ce8:	c3                   	ret
    5ce9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005cf0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5cf0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5cf4:	85 f6                	test   %esi,%esi
    5cf6:	0f 8e 44 03 00 00    	jle    6040 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    5cfc:	41 57                	push   %r15
    5cfe:	41 89 f7             	mov    %esi,%r15d
    5d01:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5d03:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5d06:	41 55                	push   %r13
    5d08:	41 54                	push   %r12
    5d0a:	55                   	push   %rbp
    5d0b:	53                   	push   %rbx
    5d0c:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5d10:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5d14:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5d19:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5d1e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    5d21:	45 39 e6             	cmp    %r12d,%r14d
    5d24:	0f 84 4e 02 00 00    	je     5f78 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5d2a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5d2f:	8b 50 08             	mov    0x8(%rax),%edx
    5d32:	85 d2                	test   %edx,%edx
    5d34:	0f 8e 3e 02 00 00    	jle    5f78 <verify+0x288>
    5d3a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    5d3f:	31 c9                	xor    %ecx,%ecx
    5d41:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    5d46:	31 c0                	xor    %eax,%eax
    5d48:	44 89 f2             	mov    %r14d,%edx
    5d4b:	bf 01 00 00 00       	mov    $0x1,%edi
    5d50:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5d55:	48 8d 35 c4 14 00 00 	lea    0x14c4(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    5d5c:	e8 ef c6 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5d61:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5d66:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    5d6b:	8b 40 08             	mov    0x8(%rax),%eax
    5d6e:	85 c0                	test   %eax,%eax
    5d70:	0f 8e e6 01 00 00    	jle    5f5c <verify+0x26c>
    5d76:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5d79:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    5d7e:	31 db                	xor    %ebx,%ebx
    5d80:	48 c1 e0 09          	shl    $0x9,%rax
    5d84:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    5d89:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5d8e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5d93:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    5d98:	4c 8b 20             	mov    (%rax),%r12
    5d9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5da0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    5da5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5daa:	49 89 de             	mov    %rbx,%r14
    5dad:	48 8d 35 81 14 00 00 	lea    0x1481(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5db4:	49 c1 e6 09          	shl    $0x9,%r14
    5db8:	bf 01 00 00 00       	mov    $0x1,%edi
    5dbd:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5dc1:	4b 8b 8c 3c 58 01 00 00 	mov    0x158(%r12,%r15,1),%rcx
    5dc9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    5dce:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    5dd6:	31 c0                	xor    %eax,%eax
    5dd8:	e8 73 c6 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5ddd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5de2:	4c 8b 20             	mov    (%rax),%r12
    5de5:	4b 83 bc 3c 58 01 00 00 00 	cmpq   $0x0,0x158(%r12,%r15,1)
    5dee:	0f 8e 47 01 00 00    	jle    5f3b <verify+0x24b>
    5df4:	4c 03 75 00          	add    0x0(%rbp),%r14
    5df8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5dfd:	ba 01 00 00 00       	mov    $0x1,%edx
    5e02:	4d 89 f5             	mov    %r14,%r13
    5e05:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    5e0c:	4d 85 f6             	test   %r14,%r14
    5e0f:	0f 8e 21 01 00 00    	jle    5f36 <verify+0x246>
    5e15:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5e18:	48 89 d5             	mov    %rdx,%rbp
    5e1b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5e20:	31 db                	xor    %ebx,%ebx
    5e22:	4d 89 f2             	mov    %r14,%r10
    5e25:	48 c1 e5 05          	shl    $0x5,%rbp
    5e29:	48 83 ed 20          	sub    $0x20,%rbp
    5e2d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    5e31:	49 89 ee             	mov    %rbp,%r14
    5e34:	48 89 dd             	mov    %rbx,%rbp
    5e37:	48 89 d3             	mov    %rdx,%rbx
    5e3a:	eb 31                	jmp    5e6d <verify+0x17d>
    5e3c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5e40:	4c 39 c2             	cmp    %r8,%rdx
    5e43:	0f 8d 57 01 00 00    	jge    5fa0 <verify+0x2b0>
    5e49:	4c 39 df             	cmp    %r11,%rdi
    5e4c:	7e 05                	jle    5e53 <verify+0x163>
    5e4e:	49 39 c1             	cmp    %rax,%r9
    5e51:	7c 75                	jl     5ec8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e53:	4c 39 df             	cmp    %r11,%rdi
    5e56:	0f 8d ab 01 00 00    	jge    6007 <verify+0x317>
    5e5c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5e60:	48 83 c5 01          	add    $0x1,%rbp
    5e64:	49 39 ea             	cmp    %rbp,%r10
    5e67:	0f 8e a9 00 00 00    	jle    5f16 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5e6d:	49 8b 97 48 01 00 00 	mov    0x148(%r15),%rdx
    5e74:	48 89 e8             	mov    %rbp,%rax
    5e77:	48 c1 e0 05          	shl    $0x5,%rax
    5e7b:	49 03 85 48 01 00 00 	add    0x148(%r13),%rax
    5e82:	4c 01 f2             	add    %r14,%rdx
    5e85:	48 8b 08             	mov    (%rax),%rcx
    5e88:	48 8b 78 10          	mov    0x10(%rax),%rdi
    5e8c:	48 8b 32             	mov    (%rdx),%rsi
    5e8f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    5e93:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    5e97:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    5e9b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    5e9f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    5ea3:	48 39 f1             	cmp    %rsi,%rcx
    5ea6:	7c 98                	jl     5e40 <verify+0x150>
    5ea8:	0f 8e 42 01 00 00    	jle    5ff0 <verify+0x300>
    5eae:	4c 39 c2             	cmp    %r8,%rdx
    5eb1:	0f 8f f9 00 00 00    	jg     5fb0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5eb7:	75 a7                	jne    5e60 <verify+0x170>
    5eb9:	4c 39 df             	cmp    %r11,%rdi
    5ebc:	7f a2                	jg     5e60 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5ebe:	49 39 c1             	cmp    %rax,%r9
    5ec1:	7c 9d                	jl     5e60 <verify+0x170>
    5ec3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5ec8:	49 89 c1             	mov    %rax,%r9
    5ecb:	48 89 f9             	mov    %rdi,%rcx
    5ece:	48 89 f2             	mov    %rsi,%rdx
    5ed1:	bf 01 00 00 00       	mov    $0x1,%edi
    5ed6:	48 8d 35 ab 15 00 00 	lea    0x15ab(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    5edd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5edf:	48 83 c5 01          	add    $0x1,%rbp
    5ee3:	e8 68 c5 ff ff       	call   2450 <__printf_chk@plt>
    5ee8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5eed:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    5ef2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5ef5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5efa:	4d 8b 95 58 01 00 00 	mov    0x158(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5f01:	4c 8b 20             	mov    (%rax),%r12
    5f04:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5f09:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5f0d:	49 39 ea             	cmp    %rbp,%r10
    5f10:	0f 8f 57 ff ff ff    	jg     5e6d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5f16:	48 89 da             	mov    %rbx,%rdx
    5f19:	49 3b 9f 58 01 00 00 	cmp    0x158(%r15),%rbx
    5f20:	7d 14                	jge    5f36 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5f22:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    5f29:	48 83 c2 01          	add    $0x1,%rdx
    5f2d:	4d 85 f6             	test   %r14,%r14
    5f30:	0f 8f e2 fe ff ff    	jg     5e18 <verify+0x128>
    5f36:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5f3b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5f40:	48 83 c3 01          	add    $0x1,%rbx
    5f44:	39 58 08             	cmp    %ebx,0x8(%rax)
    5f47:	0f 8f 53 fe ff ff    	jg     5da0 <verify+0xb0>
    5f4d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    5f52:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    5f57:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5f5c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5f61:	48 83 c1 01          	add    $0x1,%rcx
    5f65:	39 48 08             	cmp    %ecx,0x8(%rax)
    5f68:	0f 8f d8 fd ff ff    	jg     5d46 <verify+0x56>
    5f6e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    5f73:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    5f78:	48 81 44 24 10 b0 00 00 00 	addq   $0xb0,0x10(%rsp)
    5f81:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    5f86:	41 39 c7             	cmp    %eax,%r15d
    5f89:	0f 84 86 00 00 00    	je     6015 <verify+0x325>
    5f8f:	41 89 c4             	mov    %eax,%r12d
    5f92:	e9 8a fd ff ff       	jmp    5d21 <verify+0x31>
    5f97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5fa0:	0f 85 ba fe ff ff    	jne    5e60 <verify+0x170>
    5fa6:	e9 a8 fe ff ff       	jmp    5e53 <verify+0x163>
    5fab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5fb0:	49 39 c1             	cmp    %rax,%r9
    5fb3:	7e 09                	jle    5fbe <verify+0x2ce>
    5fb5:	4c 39 df             	cmp    %r11,%rdi
    5fb8:	0f 8c 0a ff ff ff    	jl     5ec8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5fbe:	4c 39 df             	cmp    %r11,%rdi
    5fc1:	0f 8f 99 fe ff ff    	jg     5e60 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5fc7:	49 39 c1             	cmp    %rax,%r9
    5fca:	0f 8d f8 fe ff ff    	jge    5ec8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5fd0:	48 39 f1             	cmp    %rsi,%rcx
    5fd3:	0f 85 87 fe ff ff    	jne    5e60 <verify+0x170>
    5fd9:	4c 39 c2             	cmp    %r8,%rdx
    5fdc:	0f 85 7e fe ff ff    	jne    5e60 <verify+0x170>
    5fe2:	4c 39 df             	cmp    %r11,%rdi
    5fe5:	0f 84 dd fe ff ff    	je     5ec8 <verify+0x1d8>
    5feb:	e9 70 fe ff ff       	jmp    5e60 <verify+0x170>
    5ff0:	4c 39 c2             	cmp    %r8,%rdx
    5ff3:	0f 8c 5a fe ff ff    	jl     5e53 <verify+0x163>
    5ff9:	4c 39 df             	cmp    %r11,%rdi
    5ffc:	7e c9                	jle    5fc7 <verify+0x2d7>
    5ffe:	4c 39 c2             	cmp    %r8,%rdx
    6001:	0f 85 59 fe ff ff    	jne    5e60 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6007:	49 39 c1             	cmp    %rax,%r9
    600a:	0f 8f 50 fe ff ff    	jg     5e60 <verify+0x170>
    6010:	e9 b3 fe ff ff       	jmp    5ec8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    6015:	48 81 44 24 18 b0 00 00 00 	addq   $0xb0,0x18(%rsp)
    601e:	41 8d 46 01          	lea    0x1(%r14),%eax
    6022:	45 39 e6             	cmp    %r12d,%r14d
    6025:	74 08                	je     602f <verify+0x33f>
    6027:	41 89 c6             	mov    %eax,%r14d
    602a:	e9 ea fc ff ff       	jmp    5d19 <verify+0x29>
}
    602f:	48 83 c4 58          	add    $0x58,%rsp
    6033:	31 c0                	xor    %eax,%eax
    6035:	5b                   	pop    %rbx
    6036:	5d                   	pop    %rbp
    6037:	41 5c                	pop    %r12
    6039:	41 5d                	pop    %r13
    603b:	41 5e                	pop    %r14
    603d:	41 5f                	pop    %r15
    603f:	c3                   	ret
    6040:	31 c0                	xor    %eax,%eax
    6042:	c3                   	ret

Disassembly of section .fini:

0000000000006044 <_fini>:
    6044:	f3 0f 1e fa          	endbr64
    6048:	48 83 ec 08          	sub    $0x8,%rsp
    604c:	48 83 c4 08          	add    $0x8,%rsp
    6050:	c3                   	ret
