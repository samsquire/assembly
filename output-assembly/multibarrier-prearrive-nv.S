
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
    2540:	f3 0f 1e fa          	endbr64
    2544:	50                   	push   %rax
    2545:	58                   	pop    %rax
    2546:	50                   	push   %rax
    2547:	e8 44 ff ff ff       	call   2490 <perror@plt>
    254c:	bf 01 00 00 00       	mov    $0x1,%edi
    2551:	e8 4a ff ff ff       	call   24a0 <exit@plt>

0000000000002556 <copy_file_contents.cold>:
    2556:	48 8d 3d a2 4c 00 00 	lea    0x4ca2(%rip),%rdi        # 71ff <_IO_stdin_used+0x1ff>
    255d:	e8 de ff ff ff       	call   2540 <fatal_error>

0000000000002562 <add_write_request.cold>:
    2562:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
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
    2596:	48 8d 3d 32 4c 00 00 	lea    0x4c32(%rip),%rdi        # 71cf <_IO_stdin_used+0x1cf>
    259d:	e8 9e ff ff ff       	call   2540 <fatal_error>
    25a2:	48 8d 3d aa 4b 00 00 	lea    0x4baa(%rip),%rdi        # 7153 <_IO_stdin_used+0x153>
    25a9:	e8 92 ff ff ff       	call   2540 <fatal_error>
    25ae:	48 8d 3d be 4b 00 00 	lea    0x4bbe(%rip),%rdi        # 7173 <_IO_stdin_used+0x173>
    25b5:	e8 86 ff ff ff       	call   2540 <fatal_error>
    25ba:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25c2:	0f 0b                	ud2
    25c4:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25cc:	0f 0b                	ud2
    25ce:	48 8d 3d 75 4b 00 00 	lea    0x4b75(%rip),%rdi        # 714a <_IO_stdin_used+0x14a>
    25d5:	e8 66 ff ff ff       	call   2540 <fatal_error>
    25da:	48 8d 3d 8b 4b 00 00 	lea    0x4b8b(%rip),%rdi        # 716c <_IO_stdin_used+0x16c>
    25e1:	e8 5a ff ff ff       	call   2540 <fatal_error>
    25e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000025f0 <main>:
    25f0:	f3 0f 1e fa          	endbr64
    25f4:	41 57                	push   %r15
    25f6:	48 8d 3d b3 4e 00 00 	lea    0x4eb3(%rip),%rdi        # 74b0 <_IO_stdin_used+0x4b0>
    25fd:	41 56                	push   %r14
    25ff:	41 55                	push   %r13
    2601:	41 54                	push   %r12
    2603:	55                   	push   %rbp
    2604:	53                   	push   %rbx
    2605:	48 81 ec b8 00 00 00 	sub    $0xb8,%rsp
    260c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2615:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
    261d:	48 8d 05 1c 12 00 00 	lea    0x121c(%rip),%rax        # 3840 <barriered_reset>
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
    2734:	be 18 00 00 00       	mov    $0x18,%esi
    2739:	bf 0c 00 00 00       	mov    $0xc,%edi
    273e:	e8 5d fc ff ff       	call   23a0 <calloc@plt>
    2743:	be b0 00 00 00       	mov    $0xb0,%esi
    2748:	bf 0f 00 00 00       	mov    $0xf,%edi
    274d:	49 89 c7             	mov    %rax,%r15
    2750:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    2755:	e8 46 fc ff ff       	call   23a0 <calloc@plt>
    275a:	be 10 00 00 00       	mov    $0x10,%esi
    275f:	bf 01 00 00 00       	mov    $0x1,%edi
    2764:	4d 8d 67 e8          	lea    -0x18(%r15),%r12
    2768:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    276d:	45 31 ff             	xor    %r15d,%r15d
    2770:	e8 2b fc ff ff       	call   23a0 <calloc@plt>
    2775:	be 10 00 00 00       	mov    $0x10,%esi
    277a:	bf 01 00 00 00       	mov    $0x1,%edi
    277f:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    2785:	48 89 c3             	mov    %rax,%rbx
    2788:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    278d:	e8 0e fc ff ff       	call   23a0 <calloc@plt>
    2792:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2797:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    279f:	48 89 43 08          	mov    %rax,0x8(%rbx)
    27a3:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    27aa:	4d 89 d1             	mov    %r10,%r9
    27ad:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    27b2:	4c 89 54 24 58       	mov    %r10,0x58(%rsp)
    27b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    27c0:	be 08 00 00 00       	mov    $0x8,%esi
    27c5:	bf 02 00 00 00       	mov    $0x2,%edi
    27ca:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    27cf:	44 89 fd             	mov    %r15d,%ebp
    27d2:	e8 c9 fb ff ff       	call   23a0 <calloc@plt>
    27d7:	be 80 00 00 00       	mov    $0x80,%esi
    27dc:	bf 01 00 00 00       	mov    $0x1,%edi
    27e1:	49 89 c5             	mov    %rax,%r13
    27e4:	e8 b7 fb ff ff       	call   23a0 <calloc@plt>
    27e9:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    27ee:	48 89 c3             	mov    %rax,%rbx
    27f1:	44 89 f8             	mov    %r15d,%eax
    27f4:	41 83 c7 01          	add    $0x1,%r15d
    27f8:	83 e0 01             	and    $0x1,%eax
    27fb:	85 c0                	test   %eax,%eax
    27fd:	0f 84 86 0e 00 00    	je     3689 <main+0x1099>
    2803:	49 8d 89 50 ff ff ff 	lea    -0xb0(%r9),%rcx
    280a:	4d 89 4d 08          	mov    %r9,0x8(%r13)
    280e:	4d 89 c8             	mov    %r9,%r8
    2811:	89 ea                	mov    %ebp,%edx
    2813:	49 89 4d 00          	mov    %rcx,0x0(%r13)
    2817:	bf 01 00 00 00       	mov    $0x1,%edi
    281c:	31 c0                	xor    %eax,%eax
    281e:	44 8d 75 ff          	lea    -0x1(%rbp),%r14d
    2822:	41 c7 01 01 00 00 00 	movl   $0x1,(%r9)
    2829:	48 8d 35 cb 4a 00 00 	lea    0x4acb(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
    2830:	e8 1b fc ff ff       	call   2450 <__printf_chk@plt>
    2835:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    283a:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    283f:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2844:	4d 89 61 38          	mov    %r12,0x38(%r9)
    2848:	45 8b 01             	mov    (%r9),%r8d
    284b:	44 89 f1             	mov    %r14d,%ecx
    284e:	89 ea                	mov    %ebp,%edx
    2850:	48 8d 35 19 4d 00 00 	lea    0x4d19(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    2857:	bf 01 00 00 00       	mov    $0x1,%edi
    285c:	31 c0                	xor    %eax,%eax
    285e:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2863:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    2869:	e8 e2 fb ff ff       	call   2450 <__printf_chk@plt>
    286e:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2873:	45 89 b1 a8 00 00 00 	mov    %r14d,0xa8(%r9)
    287a:	45 31 f6             	xor    %r14d,%r14d
    287d:	0f 1f 00             	nopl   (%rax)
    2880:	44 89 f1             	mov    %r14d,%ecx
    2883:	89 ea                	mov    %ebp,%edx
    2885:	48 8d 35 14 4d 00 00 	lea    0x4d14(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    288c:	31 c0                	xor    %eax,%eax
    288e:	bf 01 00 00 00       	mov    $0x1,%edi
    2893:	e8 b8 fb ff ff       	call   2450 <__printf_chk@plt>
    2898:	44 89 f1             	mov    %r14d,%ecx
    289b:	4c 89 e0             	mov    %r12,%rax
    289e:	41 83 c6 01          	add    $0x1,%r14d
    28a2:	48 d3 e0             	shl    %cl,%rax
    28a5:	48 09 03             	or     %rax,(%rbx)
    28a8:	41 83 fe 06          	cmp    $0x6,%r14d
    28ac:	75 d2                	jne    2880 <main+0x290>
    28ae:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    28b3:	48 8b 05 86 51 00 00 	mov    0x5186(%rip),%rax        # 7a40 <_IO_stdin_used+0xa40>
    28ba:	be 10 00 00 00       	mov    $0x10,%esi
    28bf:	41 89 ee             	mov    %ebp,%r14d
    28c2:	bf 64 00 00 00       	mov    $0x64,%edi
    28c7:	49 89 99 a0 00 00 00 	mov    %rbx,0xa0(%r9)
    28ce:	31 db                	xor    %ebx,%ebx
    28d0:	41 89 69 04          	mov    %ebp,0x4(%r9)
    28d4:	4d 89 69 10          	mov    %r13,0x10(%r9)
    28d8:	49 89 41 18          	mov    %rax,0x18(%r9)
    28dc:	41 c7 41 30 03 00 00 00 	movl   $0x3,0x30(%r9)
    28e4:	e8 b7 fa ff ff       	call   23a0 <calloc@plt>
    28e9:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    28ee:	be 10 00 00 00       	mov    $0x10,%esi
    28f3:	bf 64 00 00 00       	mov    $0x64,%edi
    28f8:	49 89 41 58          	mov    %rax,0x58(%r9)
    28fc:	e8 9f fa ff ff       	call   23a0 <calloc@plt>
    2901:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2906:	be 28 00 00 00       	mov    $0x28,%esi
    290b:	66 0f 6f 15 0d 51 00 00 	movdqa 0x510d(%rip),%xmm2        # 7a20 <_IO_stdin_used+0xa20>
    2913:	bf 64 00 00 00       	mov    $0x64,%edi
    2918:	49 89 41 60          	mov    %rax,0x60(%r9)
    291c:	41 0f 11 51 70       	movups %xmm2,0x70(%r9)
    2921:	e8 7a fa ff ff       	call   23a0 <calloc@plt>
    2926:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    292b:	be 80 02 00 00       	mov    $0x280,%esi
    2930:	66 0f 6f 1d e8 50 00 00 	movdqa 0x50e8(%rip),%xmm3        # 7a20 <_IO_stdin_used+0xa20>
    2938:	bf 03 00 00 00       	mov    $0x3,%edi
    293d:	49 89 81 80 00 00 00 	mov    %rax,0x80(%r9)
    2944:	41 0f 11 99 88 00 00 00 	movups %xmm3,0x88(%r9)
    294c:	e8 4f fa ff ff       	call   23a0 <calloc@plt>
    2951:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2956:	44 89 7c 24 28       	mov    %r15d,0x28(%rsp)
    295b:	48 89 c2             	mov    %rax,%rdx
    295e:	49 89 41 28          	mov    %rax,0x28(%r9)
    2962:	4c 89 cd             	mov    %r9,%rbp
    2965:	4c 63 fb             	movslq %ebx,%r15
    2968:	be 00 02 00 00       	mov    $0x200,%esi
    296d:	bf 0c 00 00 00       	mov    $0xc,%edi
    2972:	4f 8d 24 bf          	lea    (%r15,%r15,4),%r12
    2976:	48 8d 05 83 0e 00 00 	lea    0xe83(%rip),%rax        # 3800 <do_protected_write>
    297d:	49 c1 e4 07          	shl    $0x7,%r12
    2981:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
    2985:	49 89 85 10 02 00 00 	mov    %rax,0x210(%r13)
    298c:	e8 0f fa ff ff       	call   23a0 <calloc@plt>
    2991:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    2995:	49 89 85 58 02 00 00 	mov    %rax,0x258(%r13)
    299c:	49 89 c5             	mov    %rax,%r13
    299f:	48 8d 80 00 04 00 00 	lea    0x400(%rax),%rax
    29a6:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    29ab:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    29b0:	be 08 00 00 00       	mov    $0x8,%esi
    29b5:	bf 01 00 00 00       	mov    $0x1,%edi
    29ba:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    29c1:	e8 da f9 ff ff       	call   23a0 <calloc@plt>
    29c6:	be 08 00 00 00       	mov    $0x8,%esi
    29cb:	bf 01 00 00 00       	mov    $0x1,%edi
    29d0:	48 89 c5             	mov    %rax,%rbp
    29d3:	e8 c8 f9 ff ff       	call   23a0 <calloc@plt>
    29d8:	be 18 00 00 00       	mov    $0x18,%esi
    29dd:	bf 02 00 00 00       	mov    $0x2,%edi
    29e2:	48 89 c3             	mov    %rax,%rbx
    29e5:	e8 b6 f9 ff ff       	call   23a0 <calloc@plt>
    29ea:	66 0f 6f 05 3e 50 00 00 	movdqa 0x503e(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
    29f2:	48 8d 70 18          	lea    0x18(%rax),%rsi
    29f6:	49 89 85 00 fe ff ff 	mov    %rax,-0x200(%r13)
    29fd:	49 89 b5 80 fe ff ff 	mov    %rsi,-0x180(%r13)
    2a04:	48 89 28             	mov    %rbp,(%rax)
    2a07:	48 89 58 18          	mov    %rbx,0x18(%rax)
    2a0b:	0f 11 40 08          	movups %xmm0,0x8(%rax)
    2a0f:	0f 11 40 20          	movups %xmm0,0x20(%rax)
    2a13:	4c 39 6c 24 08       	cmp    %r13,0x8(%rsp)
    2a18:	75 96                	jne    29b0 <main+0x3c0>
    2a1a:	be 01 00 00 00       	mov    $0x1,%esi
    2a1f:	bf 00 01 00 00       	mov    $0x100,%edi
    2a24:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    2a28:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    2a2d:	e8 6e f9 ff ff       	call   23a0 <calloc@plt>
    2a32:	bf 18 00 00 00       	mov    $0x18,%edi
    2a37:	49 89 c5             	mov    %rax,%r13
    2a3a:	e8 d1 f9 ff ff       	call   2410 <malloc@plt>
    2a3f:	4c 89 ef             	mov    %r13,%rdi
    2a42:	41 89 d9             	mov    %ebx,%r9d
    2a45:	45 89 f0             	mov    %r14d,%r8d
    2a48:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2a4d:	48 8d 0d 6c 4b 00 00 	lea    0x4b6c(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a54:	ba 00 01 00 00       	mov    $0x100,%edx
    2a59:	31 c0                	xor    %eax,%eax
    2a5b:	be 01 00 00 00       	mov    $0x1,%esi
    2a60:	e8 bb fa ff ff       	call   2520 <__sprintf_chk@plt>
    2a65:	48 8b 55 28          	mov    0x28(%rbp),%rdx
    2a69:	48 63 45 00          	movslq 0x0(%rbp),%rax
    2a6d:	8d 4b 01             	lea    0x1(%rbx),%ecx
    2a70:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2a75:	be 20 00 00 00       	mov    $0x20,%esi
    2a7a:	bf 63 00 00 00       	mov    $0x63,%edi
    2a7f:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2a83:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    2a88:	4d 89 2a             	mov    %r13,(%r10)
    2a8b:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
    2a8f:	4d 89 7a 10          	mov    %r15,0x10(%r10)
    2a93:	49 89 c7             	mov    %rax,%r15
    2a96:	49 89 42 08          	mov    %rax,0x8(%r10)
    2a9a:	41 89 8d 78 02 00 00 	mov    %ecx,0x278(%r13)
    2aa1:	4d 89 95 70 02 00 00 	mov    %r10,0x270(%r13)
    2aa8:	49 c7 85 40 02 00 00 63 00 00 00 	movq   $0x63,0x240(%r13)
    2ab3:	e8 e8 f8 ff ff       	call   23a0 <calloc@plt>
    2ab8:	83 fb 01             	cmp    $0x1,%ebx
    2abb:	41 89 5d 00          	mov    %ebx,0x0(%r13)
    2abf:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2ac3:	49 89 85 38 02 00 00 	mov    %rax,0x238(%r13)
    2aca:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    2acf:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2ad9:	49 89 85 28 02 00 00 	mov    %rax,0x228(%r13)
    2ae0:	48 b8 01 00 00 00 0c 00 00 00 	movabs $0xc00000001,%rax
    2aea:	49 c7 85 48 02 00 00 00 00 00 00 	movq   $0x0,0x248(%r13)
    2af5:	45 89 bd 20 02 00 00 	mov    %r15d,0x220(%r13)
    2afc:	49 89 ad 18 02 00 00 	mov    %rbp,0x218(%r13)
    2b03:	41 c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r13)
    2b0e:	41 c7 85 24 02 00 00 02 00 00 00 	movl   $0x2,0x224(%r13)
    2b19:	49 89 85 68 02 00 00 	mov    %rax,0x268(%r13)
    2b20:	0f 84 4b 0b 00 00    	je     3671 <main+0x1081>
    2b26:	44 39 f3             	cmp    %r14d,%ebx
    2b29:	75 65                	jne    2b90 <main+0x5a0>
    2b2b:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    2b2f:	85 db                	test   %ebx,%ebx
    2b31:	7f 5d                	jg     2b90 <main+0x5a0>
    2b33:	44 89 f2             	mov    %r14d,%edx
    2b36:	bf 01 00 00 00       	mov    $0x1,%edi
    2b3b:	31 c0                	xor    %eax,%eax
    2b3d:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2b41:	48 8d 35 a0 4a 00 00 	lea    0x4aa0(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2b48:	e8 03 f9 ff ff       	call   2450 <__printf_chk@plt>
    2b4d:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    2b52:	48 63 c3             	movslq %ebx,%rax
    2b55:	48 8b 55 28          	mov    0x28(%rbp),%rdx
    2b59:	48 89 c7             	mov    %rax,%rdi
    2b5c:	48 c1 e0 04          	shl    $0x4,%rax
    2b60:	48 01 c8             	add    %rcx,%rax
    2b63:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2b67:	48 89 45 40          	mov    %rax,0x40(%rbp)
    2b6b:	48 8d 05 7e 32 00 00 	lea    0x327e(%rip),%rax        # 5df0 <barriered_work_ingest>
    2b72:	4a 89 84 22 08 02 00 00 	mov    %rax,0x208(%rdx,%r12,1)
    2b7a:	8d 47 01             	lea    0x1(%rdi),%eax
    2b7d:	89 44 24 20          	mov    %eax,0x20(%rsp)
    2b81:	83 f9 03             	cmp    $0x3,%ecx
    2b84:	74 1d                	je     2ba3 <main+0x5b3>
    2b86:	bb 01 00 00 00       	mov    $0x1,%ebx
    2b8b:	e9 d5 fd ff ff       	jmp    2965 <main+0x375>
    2b90:	48 8d 05 39 2d 00 00 	lea    0x2d39(%rip),%rax        # 58d0 <barriered_work>
    2b97:	49 89 85 08 02 00 00 	mov    %rax,0x208(%r13)
    2b9e:	83 f9 03             	cmp    $0x3,%ecx
    2ba1:	75 e3                	jne    2b86 <main+0x596>
    2ba3:	66 0f 6f 64 24 30    	movdqa 0x30(%rsp),%xmm4
    2ba9:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
    2bae:	49 89 e9             	mov    %rbp,%r9
    2bb1:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
    2bbb:	c7 82 80 05 00 00 00 00 00 00 	movl   $0x0,0x580(%rdx)
    2bc5:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    2bca:	49 81 c1 b0 00 00 00 	add    $0xb0,%r9
    2bd1:	c7 82 00 05 00 00 02 00 00 00 	movl   $0x2,0x500(%rdx)
    2bdb:	48 89 82 24 07 00 00 	mov    %rax,0x724(%rdx)
    2be2:	8b 45 00             	mov    0x0(%rbp),%eax
    2be5:	48 89 aa 18 07 00 00 	mov    %rbp,0x718(%rdx)
    2bec:	89 82 20 07 00 00    	mov    %eax,0x720(%rdx)
    2bf2:	c7 82 6c 07 00 00 0c 00 00 00 	movl   $0xc,0x76c(%rdx)
    2bfc:	c7 82 2c 07 00 00 03 00 00 00 	movl   $0x3,0x72c(%rdx)
    2c06:	0f 11 a2 08 07 00 00 	movups %xmm4,0x708(%rdx)
    2c0d:	41 83 ff 0f          	cmp    $0xf,%r15d
    2c11:	0f 85 a9 fb ff ff    	jne    27c0 <main+0x1d0>
    2c17:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    2c1c:	ba 0d 00 00 00       	mov    $0xd,%edx
    2c21:	48 8d 35 f0 46 00 00 	lea    0x46f0(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2c28:	31 c0                	xor    %eax,%eax
    2c2a:	bf 01 00 00 00       	mov    $0x1,%edi
    2c2f:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    2c34:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2c39:	e8 12 f8 ff ff       	call   2450 <__printf_chk@plt>
    2c3e:	be 08 00 00 00       	mov    $0x8,%esi
    2c43:	bf 02 00 00 00       	mov    $0x2,%edi
    2c48:	e8 53 f7 ff ff       	call   23a0 <calloc@plt>
    2c4d:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2c52:	bf 0f 00 00 00       	mov    $0xf,%edi
    2c57:	4d 8d ba f0 08 00 00 	lea    0x8f0(%r10),%r15
    2c5e:	4d 8d b2 60 01 00 00 	lea    0x160(%r10),%r14
    2c65:	49 89 82 00 09 00 00 	mov    %rax,0x900(%r10)
    2c6c:	4c 89 38             	mov    %r15,(%rax)
    2c6f:	49 8d 8a 10 02 00 00 	lea    0x210(%r10),%rcx
    2c76:	49 8d 92 70 03 00 00 	lea    0x370(%r10),%rdx
    2c7d:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2c81:	49 8b 42 28          	mov    0x28(%r10),%rax
    2c85:	4d 8d 9a d0 04 00 00 	lea    0x4d0(%r10),%r11
    2c8c:	4d 8d 82 80 05 00 00 	lea    0x580(%r10),%r8
    2c93:	49 8d b2 c0 02 00 00 	lea    0x2c0(%r10),%rsi
    2c9a:	49 8d 9a 20 04 00 00 	lea    0x420(%r10),%rbx
    2ca1:	41 c7 82 08 09 00 00 02 00 00 00 	movl   $0x2,0x908(%r10)
    2cac:	48 89 4c 24 58       	mov    %rcx,0x58(%rsp)
    2cb1:	4d 8d 8a 30 06 00 00 	lea    0x630(%r10),%r9
    2cb8:	4d 8d a2 e0 06 00 00 	lea    0x6e0(%r10),%r12
    2cbf:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    2cc4:	4d 8d aa 90 07 00 00 	lea    0x790(%r10),%r13
    2ccb:	41 c7 82 f0 08 00 00 00 00 00 00 	movl   $0x0,0x8f0(%r10)
    2cd6:	41 c7 82 20 09 00 00 03 00 00 00 	movl   $0x3,0x920(%r10)
    2ce1:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2ceb:	49 8d 82 b0 00 00 00 	lea    0xb0(%r10),%rax
    2cf2:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2cf7:	49 8b 82 d8 00 00 00 	mov    0xd8(%r10),%rax
    2cfe:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    2d03:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2d0d:	49 8b 82 88 01 00 00 	mov    0x188(%r10),%rax
    2d14:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    2d19:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2d23:	49 8b 82 38 02 00 00 	mov    0x238(%r10),%rax
    2d2a:	4c 89 7c 24 70       	mov    %r15,0x70(%rsp)
    2d2f:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2d39:	49 8b 82 e8 02 00 00 	mov    0x2e8(%r10),%rax
    2d40:	4c 89 74 24 78       	mov    %r14,0x78(%rsp)
    2d45:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2d4f:	49 8b 82 98 03 00 00 	mov    0x398(%r10),%rax
    2d56:	48 89 74 24 50       	mov    %rsi,0x50(%rsp)
    2d5b:	be 38 00 00 00       	mov    $0x38,%esi
    2d60:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2d6a:	49 8b 82 48 04 00 00 	mov    0x448(%r10),%rax
    2d71:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    2d76:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2d80:	49 8b 82 f8 04 00 00 	mov    0x4f8(%r10),%rax
    2d87:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2d91:	49 8b 82 a8 05 00 00 	mov    0x5a8(%r10),%rax
    2d98:	4c 89 4c 24 30       	mov    %r9,0x30(%rsp)
    2d9d:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2da7:	49 8b 82 58 06 00 00 	mov    0x658(%r10),%rax
    2dae:	4c 89 94 24 80 00 00 00 	mov    %r10,0x80(%rsp)
    2db6:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2dc0:	49 8b 82 08 07 00 00 	mov    0x708(%r10),%rax
    2dc7:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    2dcc:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2dd6:	49 8b 82 b8 07 00 00 	mov    0x7b8(%r10),%rax
    2ddd:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    2de2:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2dec:	e8 af f5 ff ff       	call   23a0 <calloc@plt>
    2df1:	be 38 00 00 00       	mov    $0x38,%esi
    2df6:	bf 0f 00 00 00       	mov    $0xf,%edi
    2dfb:	49 89 c4             	mov    %rax,%r12
    2dfe:	e8 9d f5 ff ff       	call   23a0 <calloc@plt>
    2e03:	be 38 00 00 00       	mov    $0x38,%esi
    2e08:	bf 0f 00 00 00       	mov    $0xf,%edi
    2e0d:	48 89 c3             	mov    %rax,%rbx
    2e10:	e8 8b f5 ff ff       	call   23a0 <calloc@plt>
    2e15:	be 38 00 00 00       	mov    $0x38,%esi
    2e1a:	bf 0f 00 00 00       	mov    $0xf,%edi
    2e1f:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    2e27:	e8 74 f5 ff ff       	call   23a0 <calloc@plt>
    2e2c:	be 08 00 00 00       	mov    $0x8,%esi
    2e31:	bf 0f 00 00 00       	mov    $0xf,%edi
    2e36:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
    2e3e:	e8 5d f5 ff ff       	call   23a0 <calloc@plt>
    2e43:	be 08 00 00 00       	mov    $0x8,%esi
    2e48:	bf 0f 00 00 00       	mov    $0xf,%edi
    2e4d:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
    2e55:	49 89 c5             	mov    %rax,%r13
    2e58:	48 8b 05 e9 4b 00 00 	mov    0x4be9(%rip),%rax        # 7a48 <_IO_stdin_used+0xa48>
    2e5f:	41 c7 82 48 08 00 00 00 00 00 00 	movl   $0x0,0x848(%r10)
    2e6a:	49 89 82 70 08 00 00 	mov    %rax,0x870(%r10)
    2e71:	e8 2a f5 ff ff       	call   23a0 <calloc@plt>
    2e76:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    2e7b:	48 8b 4c 24 58       	mov    0x58(%rsp),%rcx
    2e80:	48 8b 74 24 50       	mov    0x50(%rsp),%rsi
    2e85:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    2e8a:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2e8e:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    2e93:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    2e98:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2e9c:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    2ea1:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
    2ea9:	48 89 48 18          	mov    %rcx,0x18(%rax)
    2ead:	4c 8b 4c 24 30       	mov    0x30(%rsp),%r9
    2eb2:	48 89 70 20          	mov    %rsi,0x20(%rax)
    2eb6:	48 8d 35 6a 44 00 00 	lea    0x446a(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2ebd:	48 89 78 30          	mov    %rdi,0x30(%rax)
    2ec1:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    2ec6:	4d 8d b2 40 08 00 00 	lea    0x840(%r10),%r14
    2ecd:	4c 89 10             	mov    %r10,(%rax)
    2ed0:	48 89 78 50          	mov    %rdi,0x50(%rax)
    2ed4:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    2ed9:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2edd:	ba 0c 00 00 00       	mov    $0xc,%edx
    2ee2:	48 89 78 58          	mov    %rdi,0x58(%rax)
    2ee6:	49 8d ba a0 09 00 00 	lea    0x9a0(%r10),%rdi
    2eed:	4c 89 58 38          	mov    %r11,0x38(%rax)
    2ef1:	4c 89 40 40          	mov    %r8,0x40(%rax)
    2ef5:	4c 89 48 48          	mov    %r9,0x48(%rax)
    2ef9:	4c 89 70 60          	mov    %r14,0x60(%rax)
    2efd:	4c 89 78 68          	mov    %r15,0x68(%rax)
    2f01:	4c 8d 3d b8 09 00 00 	lea    0x9b8(%rip),%r15        # 38c0 <barriered_thread>
    2f08:	48 89 78 70          	mov    %rdi,0x70(%rax)
    2f0c:	49 89 82 50 08 00 00 	mov    %rax,0x850(%r10)
    2f13:	31 c0                	xor    %eax,%eax
    2f15:	41 c7 82 58 08 00 00 0c 00 00 00 	movl   $0xc,0x858(%r10)
    2f20:	41 c7 82 60 08 00 00 02 00 00 00 	movl   $0x2,0x860(%r10)
    2f2b:	41 c7 82 40 08 00 00 00 00 00 00 	movl   $0x0,0x840(%r10)
    2f36:	48 89 bc 24 80 00 00 00 	mov    %rdi,0x80(%rsp)
    2f3e:	bf 01 00 00 00       	mov    $0x1,%edi
    2f43:	4c 89 94 24 98 00 00 00 	mov    %r10,0x98(%rsp)
    2f4b:	e8 00 f5 ff ff       	call   2450 <__printf_chk@plt>
    2f50:	48 8d b3 a0 02 00 00 	lea    0x2a0(%rbx),%rsi
    2f57:	49 8d 7d 60          	lea    0x60(%r13),%rdi
    2f5b:	4c 89 f1             	mov    %r14,%rcx
    2f5e:	48 8d 15 db 0c 00 00 	lea    0xcdb(%rip),%rdx        # 3c40 <timer_thread>
    2f65:	45 31 f6             	xor    %r14d,%r14d
    2f68:	4c 89 eb             	mov    %r13,%rbx
    2f6b:	e8 00 f5 ff ff       	call   2470 <pthread_create@plt>
    2f70:	44 89 f0             	mov    %r14d,%eax
    2f73:	4d 89 ee             	mov    %r13,%r14
    2f76:	41 89 c5             	mov    %eax,%r13d
    2f79:	c7 45 08 01 00 00 00 	movl   $0x1,0x8(%rbp)
    2f80:	44 89 ea             	mov    %r13d,%edx
    2f83:	bf 01 00 00 00       	mov    $0x1,%edi
    2f88:	31 c0                	xor    %eax,%eax
    2f8a:	c7 45 34 01 00 00 00 	movl   $0x1,0x34(%rbp)
    2f91:	48 8d 35 70 46 00 00 	lea    0x4670(%rip),%rsi        # 7608 <_IO_stdin_used+0x608>
    2f98:	41 83 c5 01          	add    $0x1,%r13d
    2f9c:	e8 af f4 ff ff       	call   2450 <__printf_chk@plt>
    2fa1:	48 89 e9             	mov    %rbp,%rcx
    2fa4:	4c 89 e6             	mov    %r12,%rsi
    2fa7:	48 89 df             	mov    %rbx,%rdi
    2faa:	4c 89 fa             	mov    %r15,%rdx
    2fad:	48 81 c5 b0 00 00 00 	add    $0xb0,%rbp
    2fb4:	48 83 c3 08          	add    $0x8,%rbx
    2fb8:	49 83 c4 38          	add    $0x38,%r12
    2fbc:	e8 af f4 ff ff       	call   2470 <pthread_create@plt>
    2fc1:	48 8b 55 f0          	mov    -0x10(%rbp),%rdx
    2fc5:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    2fc9:	be 08 00 00 00       	mov    $0x8,%esi
    2fce:	e8 0d f3 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    2fd3:	41 83 fd 0c          	cmp    $0xc,%r13d
    2fd7:	75 a0                	jne    2f79 <main+0x989>
    2fd9:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    2fe1:	48 8b 1d 68 4a 00 00 	mov    0x4a68(%rip),%rbx        # 7a50 <_IO_stdin_used+0xa50>
    2fe8:	be d8 00 00 00       	mov    $0xd8,%esi
    2fed:	4d 89 f5             	mov    %r14,%r13
    2ff0:	bf 01 00 00 00       	mov    $0x1,%edi
    2ff5:	49 89 9a 20 09 00 00 	mov    %rbx,0x920(%r10)
    2ffc:	41 c7 82 f8 08 00 00 02 00 00 00 	movl   $0x2,0x8f8(%r10)
    3007:	e8 94 f3 ff ff       	call   23a0 <calloc@plt>
    300c:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    3014:	be 00 08 00 00       	mov    $0x800,%esi
    3019:	31 ff                	xor    %edi,%edi
    301b:	49 89 82 38 09 00 00 	mov    %rax,0x938(%r10)
    3022:	e8 89 f4 ff ff       	call   24b0 <eventfd@plt>
    3027:	be 08 00 00 00       	mov    $0x8,%esi
    302c:	bf 0c 00 00 00       	mov    $0xc,%edi
    3031:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    3039:	41 89 82 40 09 00 00 	mov    %eax,0x940(%r10)
    3040:	e8 5b f3 ff ff       	call   23a0 <calloc@plt>
    3045:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    304a:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    304f:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    3057:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    305c:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    3061:	4c 8b 74 24 78       	mov    0x78(%rsp),%r14
    3066:	4c 89 58 48          	mov    %r11,0x48(%rax)
    306a:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    306f:	4c 8b 7c 24 60       	mov    0x60(%rsp),%r15
    3074:	4c 89 40 50          	mov    %r8,0x50(%rax)
    3078:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    307d:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3082:	4c 89 48 58          	mov    %r9,0x58(%rax)
    3086:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    308b:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    3090:	4c 89 10             	mov    %r10,(%rax)
    3093:	49 89 82 00 09 00 00 	mov    %rax,0x900(%r10)
    309a:	41 c7 82 08 09 00 00 0c 00 00 00 	movl   $0xc,0x908(%r10)
    30a5:	41 c7 82 f0 08 00 00 0d 00 00 00 	movl   $0xd,0x8f0(%r10)
    30b0:	4c 89 70 10          	mov    %r14,0x10(%rax)
    30b4:	48 89 68 18          	mov    %rbp,0x18(%rax)
    30b8:	4c 89 60 20          	mov    %r12,0x20(%rax)
    30bc:	48 89 78 28          	mov    %rdi,0x28(%rax)
    30c0:	bf 01 00 00 00       	mov    $0x1,%edi
    30c5:	48 89 48 30          	mov    %rcx,0x30(%rax)
    30c9:	48 89 70 38          	mov    %rsi,0x38(%rax)
    30cd:	48 8d 35 71 42 00 00 	lea    0x4271(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    30d4:	48 89 50 40          	mov    %rdx,0x40(%rax)
    30d8:	ba 0d 00 00 00       	mov    $0xd,%edx
    30dd:	4c 89 78 08          	mov    %r15,0x8(%rax)
    30e1:	31 c0                	xor    %eax,%eax
    30e3:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    30e8:	e8 63 f3 ff ff       	call   2450 <__printf_chk@plt>
    30ed:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    30f2:	49 8d 7d 68          	lea    0x68(%r13),%rdi
    30f6:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    30fe:	48 8d 15 fb 1d 00 00 	lea    0x1dfb(%rip),%rdx        # 4f00 <io_thread>
    3105:	48 05 d8 02 00 00    	add    $0x2d8,%rax
    310b:	48 89 c6             	mov    %rax,%rsi
    310e:	e8 5d f3 ff ff       	call   2470 <pthread_create@plt>
    3113:	ba 0e 00 00 00       	mov    $0xe,%edx
    3118:	48 8d 35 3d 42 00 00 	lea    0x423d(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    311f:	31 c0                	xor    %eax,%eax
    3121:	bf 01 00 00 00       	mov    $0x1,%edi
    3126:	e8 25 f3 ff ff       	call   2450 <__printf_chk@plt>
    312b:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    3130:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3135:	be 08 00 00 00       	mov    $0x8,%esi
    313a:	bf 0c 00 00 00       	mov    $0xc,%edi
    313f:	49 89 9a d0 09 00 00 	mov    %rbx,0x9d0(%r10)
    3146:	31 db                	xor    %ebx,%ebx
    3148:	41 c7 82 a8 09 00 00 03 00 00 00 	movl   $0x3,0x9a8(%r10)
    3153:	49 89 82 e0 09 00 00 	mov    %rax,0x9e0(%r10)
    315a:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    315f:	e8 3c f2 ff ff       	call   23a0 <calloc@plt>
    3164:	4c 8b 54 24 48       	mov    0x48(%rsp),%r10
    3169:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    316e:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    3173:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    3178:	4c 89 70 10          	mov    %r14,0x10(%rax)
    317c:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3181:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    3186:	4c 89 10             	mov    %r10,(%rax)
    3189:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    318e:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3193:	48 89 68 18          	mov    %rbp,0x18(%rax)
    3197:	48 8d 2d f9 41 00 00 	lea    0x41f9(%rip),%rbp        # 7397 <_IO_stdin_used+0x397>
    319e:	4c 89 60 20          	mov    %r12,0x20(%rax)
    31a2:	4c 8d a4 24 a0 00 00 00 	lea    0xa0(%rsp),%r12
    31aa:	48 89 78 28          	mov    %rdi,0x28(%rax)
    31ae:	49 8d 7d 70          	lea    0x70(%r13),%rdi
    31b2:	48 89 48 30          	mov    %rcx,0x30(%rax)
    31b6:	48 8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%rcx
    31be:	48 89 70 38          	mov    %rsi,0x38(%rax)
    31c2:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
    31ca:	48 89 50 40          	mov    %rdx,0x40(%rax)
    31ce:	48 8d 15 ab 09 00 00 	lea    0x9ab(%rip),%rdx        # 3b80 <external_thread>
    31d5:	4c 89 58 48          	mov    %r11,0x48(%rax)
    31d9:	48 81 c6 10 03 00 00 	add    $0x310,%rsi
    31e0:	4c 89 40 50          	mov    %r8,0x50(%rax)
    31e4:	4c 89 48 58          	mov    %r9,0x58(%rax)
    31e8:	49 89 82 b0 09 00 00 	mov    %rax,0x9b0(%r10)
    31ef:	4c 89 78 08          	mov    %r15,0x8(%rax)
    31f3:	48 8b 05 5e 48 00 00 	mov    0x485e(%rip),%rax        # 7a58 <_IO_stdin_used+0xa58>
    31fa:	41 c7 82 a0 09 00 00 0e 00 00 00 	movl   $0xe,0x9a0(%r10)
    3205:	49 89 82 b8 09 00 00 	mov    %rax,0x9b8(%r10)
    320c:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    3211:	e8 5a f2 ff ff       	call   2470 <pthread_create@plt>
    3216:	48 8d 3d 5c 41 00 00 	lea    0x415c(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    321d:	e8 ce f0 ff ff       	call   22f0 <puts@plt>
    3222:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    3227:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3230:	49 8b 7c dd 00       	mov    0x0(%r13,%rbx,8),%rdi
    3235:	4c 89 e6             	mov    %r12,%rsi
    3238:	e8 b3 f2 ff ff       	call   24f0 <pthread_join@plt>
    323d:	89 da                	mov    %ebx,%edx
    323f:	48 89 ee             	mov    %rbp,%rsi
    3242:	bf 01 00 00 00       	mov    $0x1,%edi
    3247:	31 c0                	xor    %eax,%eax
    3249:	48 83 c3 01          	add    $0x1,%rbx
    324d:	e8 fe f1 ff ff       	call   2450 <__printf_chk@plt>
    3252:	48 83 fb 0f          	cmp    $0xf,%rbx
    3256:	75 d8                	jne    3230 <main+0xc40>
    3258:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    325d:	4d 89 f2             	mov    %r14,%r10
    3260:	4d 8d 6e 28          	lea    0x28(%r14),%r13
    3264:	45 31 f6             	xor    %r14d,%r14d
    3267:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    326f:	4d 89 ef             	mov    %r13,%r15
    3272:	31 db                	xor    %ebx,%ebx
    3274:	31 ed                	xor    %ebp,%ebp
    3276:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    327b:	45 31 c9             	xor    %r9d,%r9d
    327e:	4d 89 f5             	mov    %r14,%r13
    3281:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    3286:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    328a:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    328f:	89 f8                	mov    %edi,%eax
    3291:	41 89 fc             	mov    %edi,%r12d
    3294:	83 c7 01             	add    $0x1,%edi
    3297:	83 e0 01             	and    $0x1,%eax
    329a:	41 83 ec 01          	sub    $0x1,%r12d
    329e:	89 7c 24 10          	mov    %edi,0x10(%rsp)
    32a2:	85 c0                	test   %eax,%eax
    32a4:	44 0f 44 e7          	cmove  %edi,%r12d
    32a8:	bf 0a 00 00 00       	mov    $0xa,%edi
    32ad:	e8 1e f0 ff ff       	call   22d0 <putchar@plt>
    32b2:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    32b7:	bf 01 00 00 00       	mov    $0x1,%edi
    32bc:	48 8d 35 e8 40 00 00 	lea    0x40e8(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    32c3:	48 8b 10             	mov    (%rax),%rdx
    32c6:	31 c0                	xor    %eax,%eax
    32c8:	e8 83 f1 ff ff       	call   2450 <__printf_chk@plt>
    32cd:	49 63 57 08          	movslq 0x8(%r15),%rdx
    32d1:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    32d6:	85 d2                	test   %edx,%edx
    32d8:	0f 8e 24 04 00 00    	jle    3702 <main+0x1112>
    32de:	49 8b 07             	mov    (%r15),%rax
    32e1:	48 8d 34 92          	lea    (%rdx,%rdx,4),%rsi
    32e5:	31 d2                	xor    %edx,%edx
    32e7:	48 c1 e6 07          	shl    $0x7,%rsi
    32eb:	48 05 00 02 00 00    	add    $0x200,%rax
    32f1:	48 01 c6             	add    %rax,%rsi
    32f4:	0f 1f 40 00          	nopl   0x0(%rax)
    32f8:	48 03 10             	add    (%rax),%rdx
    32fb:	48 05 80 02 00 00    	add    $0x280,%rax
    3301:	48 39 f0             	cmp    %rsi,%rax
    3304:	75 f2                	jne    32f8 <main+0xd08>
    3306:	4d 63 e4             	movslq %r12d,%r12
    3309:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    330e:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    3312:	49 8d 04 44          	lea    (%r12,%rax,2),%rax
    3316:	48 c1 e0 04          	shl    $0x4,%rax
    331a:	48 01 f8             	add    %rdi,%rax
    331d:	48 63 70 30          	movslq 0x30(%rax),%rsi
    3321:	85 f6                	test   %esi,%esi
    3323:	7e 29                	jle    334e <main+0xd5e>
    3325:	48 8b 40 28          	mov    0x28(%rax),%rax
    3329:	48 8d 34 b6          	lea    (%rsi,%rsi,4),%rsi
    332d:	48 c1 e6 07          	shl    $0x7,%rsi
    3331:	48 05 00 02 00 00    	add    $0x200,%rax
    3337:	48 01 c6             	add    %rax,%rsi
    333a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3340:	48 03 10             	add    (%rax),%rdx
    3343:	48 05 80 02 00 00    	add    $0x280,%rax
    3349:	48 39 f0             	cmp    %rsi,%rax
    334c:	75 f2                	jne    3340 <main+0xd50>
    334e:	48 8d 35 6b 40 00 00 	lea    0x406b(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    3355:	bf 01 00 00 00       	mov    $0x1,%edi
    335a:	31 c0                	xor    %eax,%eax
    335c:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    3361:	e8 ea f0 ff ff       	call   2450 <__printf_chk@plt>
    3366:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    336b:	bf 01 00 00 00       	mov    $0x1,%edi
    3370:	48 8b 30             	mov    (%rax),%rsi
    3373:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    337d:	48 f7 ee             	imul   %rsi
    3380:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3384:	31 c0                	xor    %eax,%eax
    3386:	48 d1 fa             	sar    %rdx
    3389:	48 29 f2             	sub    %rsi,%rdx
    338c:	48 8d 35 9d 42 00 00 	lea    0x429d(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    3393:	e8 b8 f0 ff ff       	call   2450 <__printf_chk@plt>
    3398:	bf 0a 00 00 00       	mov    $0xa,%edi
    339d:	e8 2e ef ff ff       	call   22d0 <putchar@plt>
    33a2:	49 63 47 08          	movslq 0x8(%r15),%rax
    33a6:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    33ab:	85 c0                	test   %eax,%eax
    33ad:	0f 8e ed 00 00 00    	jle    34a0 <main+0xeb0>
    33b3:	49 8b 3f             	mov    (%r15),%rdi
    33b6:	48 8d 34 80          	lea    (%rax,%rax,4),%rsi
    33ba:	48 c1 e6 07          	shl    $0x7,%rsi
    33be:	48 8d 97 80 01 00 00 	lea    0x180(%rdi),%rdx
    33c5:	48 01 d6             	add    %rdx,%rsi
    33c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    33d0:	48 8b 82 d8 00 00 00 	mov    0xd8(%rdx),%rax
    33d7:	4c 03 2a             	add    (%rdx),%r13
    33da:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
    33e1:	4c 03 b2 50 fe ff ff 	add    -0x1b0(%rdx),%r14
    33e8:	4c 03 8a 60 fe ff ff 	add    -0x1a0(%rdx),%r9
    33ef:	48 03 a8 00 01 00 00 	add    0x100(%rax),%rbp
    33f6:	48 03 98 80 01 00 00 	add    0x180(%rax),%rbx
    33fd:	48 03 a8 00 03 00 00 	add    0x300(%rax),%rbp
    3404:	48 03 98 80 03 00 00 	add    0x380(%rax),%rbx
    340b:	48 03 a8 00 05 00 00 	add    0x500(%rax),%rbp
    3412:	48 03 98 80 05 00 00 	add    0x580(%rax),%rbx
    3419:	48 03 a8 00 07 00 00 	add    0x700(%rax),%rbp
    3420:	48 03 98 80 07 00 00 	add    0x780(%rax),%rbx
    3427:	48 03 a8 00 09 00 00 	add    0x900(%rax),%rbp
    342e:	48 03 98 80 09 00 00 	add    0x980(%rax),%rbx
    3435:	48 03 a8 00 0b 00 00 	add    0xb00(%rax),%rbp
    343c:	48 03 98 80 0b 00 00 	add    0xb80(%rax),%rbx
    3443:	48 03 a8 00 0d 00 00 	add    0xd00(%rax),%rbp
    344a:	48 03 98 80 0d 00 00 	add    0xd80(%rax),%rbx
    3451:	48 03 a8 00 0f 00 00 	add    0xf00(%rax),%rbp
    3458:	48 03 98 80 0f 00 00 	add    0xf80(%rax),%rbx
    345f:	48 03 a8 00 11 00 00 	add    0x1100(%rax),%rbp
    3466:	48 03 98 80 11 00 00 	add    0x1180(%rax),%rbx
    346d:	48 03 a8 00 13 00 00 	add    0x1300(%rax),%rbp
    3474:	48 03 98 80 13 00 00 	add    0x1380(%rax),%rbx
    347b:	48 03 a8 00 15 00 00 	add    0x1500(%rax),%rbp
    3482:	48 03 98 80 15 00 00 	add    0x1580(%rax),%rbx
    3489:	48 03 a8 00 17 00 00 	add    0x1700(%rax),%rbp
    3490:	48 03 98 80 17 00 00 	add    0x1780(%rax),%rbx
    3497:	48 39 f2             	cmp    %rsi,%rdx
    349a:	0f 85 30 ff ff ff    	jne    33d0 <main+0xde0>
    34a0:	45 31 e4             	xor    %r12d,%r12d
    34a3:	49 83 7f 68 00       	cmpq   $0x0,0x68(%r15)
    34a8:	7e 7c                	jle    3526 <main+0xf36>
    34aa:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    34af:	4c 89 fb             	mov    %r15,%rbx
    34b2:	4d 89 e7             	mov    %r12,%r15
    34b5:	4d 89 cc             	mov    %r9,%r12
    34b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    34c0:	48 8b 43 58          	mov    0x58(%rbx),%rax
    34c4:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    34c8:	48 83 ec 08          	sub    $0x8,%rsp
    34cc:	bf 01 00 00 00       	mov    $0x1,%edi
    34d1:	49 83 c7 01          	add    $0x1,%r15
    34d5:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    34d9:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
    34e3:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    34e7:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    34eb:	48 f7 e6             	mul    %rsi
    34ee:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    34f2:	4c 2b 01             	sub    (%rcx),%r8
    34f5:	31 c0                	xor    %eax,%eax
    34f7:	8b 49 20             	mov    0x20(%rcx),%ecx
    34fa:	56                   	push   %rsi
    34fb:	48 8d 35 4e 41 00 00 	lea    0x414e(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    3502:	48 c1 ea 12          	shr    $0x12,%rdx
    3506:	49 89 d1             	mov    %rdx,%r9
    3509:	ba 02 00 00 00       	mov    $0x2,%edx
    350e:	e8 3d ef ff ff       	call   2450 <__printf_chk@plt>
    3513:	58                   	pop    %rax
    3514:	5a                   	pop    %rdx
    3515:	4c 39 7b 68          	cmp    %r15,0x68(%rbx)
    3519:	7f a5                	jg     34c0 <main+0xed0>
    351b:	49 89 df             	mov    %rbx,%r15
    351e:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    3523:	4d 89 e1             	mov    %r12,%r9
    3526:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    352c:	49 81 c7 b0 00 00 00 	add    $0xb0,%r15
    3533:	83 7c 24 10 0c       	cmpl   $0xc,0x10(%rsp)
    3538:	0f 85 48 fd ff ff    	jne    3286 <main+0xc96>
    353e:	4c 89 ea             	mov    %r13,%rdx
    3541:	48 8d 35 85 3e 00 00 	lea    0x3e85(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    3548:	31 c0                	xor    %eax,%eax
    354a:	4d 89 cf             	mov    %r9,%r15
    354d:	bf 01 00 00 00       	mov    $0x1,%edi
    3552:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    3557:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    3561:	e8 ea ee ff ff       	call   2450 <__printf_chk@plt>
    3566:	bf 0a 00 00 00       	mov    $0xa,%edi
    356b:	e8 60 ed ff ff       	call   22d0 <putchar@plt>
    3570:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    3575:	bf 01 00 00 00       	mov    $0x1,%edi
    357a:	48 8d 35 1f 41 00 00 	lea    0x411f(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    3581:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3585:	31 c0                	xor    %eax,%eax
    3587:	e8 c4 ee ff ff       	call   2450 <__printf_chk@plt>
    358c:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3591:	bf 01 00 00 00       	mov    $0x1,%edi
    3596:	48 8d 35 2b 41 00 00 	lea    0x412b(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    359d:	4c 89 c8             	mov    %r9,%rax
    35a0:	49 c1 f9 3f          	sar    $0x3f,%r9
    35a4:	49 f7 ec             	imul   %r12
    35a7:	31 c0                	xor    %eax,%eax
    35a9:	48 d1 fa             	sar    %rdx
    35ac:	4c 29 ca             	sub    %r9,%rdx
    35af:	e8 9c ee ff ff       	call   2450 <__printf_chk@plt>
    35b4:	4c 89 f8             	mov    %r15,%rax
    35b7:	4d 89 fb             	mov    %r15,%r11
    35ba:	bf 01 00 00 00       	mov    $0x1,%edi
    35bf:	49 f7 ec             	imul   %r12
    35c2:	49 c1 fb 3f          	sar    $0x3f,%r11
    35c6:	48 8d 35 2b 41 00 00 	lea    0x412b(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    35cd:	31 c0                	xor    %eax,%eax
    35cf:	48 d1 fa             	sar    %rdx
    35d2:	4c 29 da             	sub    %r11,%rdx
    35d5:	e8 76 ee ff ff       	call   2450 <__printf_chk@plt>
    35da:	4c 89 e8             	mov    %r13,%rax
    35dd:	4c 89 e9             	mov    %r13,%rcx
    35e0:	bf 01 00 00 00       	mov    $0x1,%edi
    35e5:	49 f7 ec             	imul   %r12
    35e8:	48 c1 f9 3f          	sar    $0x3f,%rcx
    35ec:	48 8d 35 35 41 00 00 	lea    0x4135(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    35f3:	31 c0                	xor    %eax,%eax
    35f5:	48 d1 fa             	sar    %rdx
    35f8:	48 29 ca             	sub    %rcx,%rdx
    35fb:	e8 50 ee ff ff       	call   2450 <__printf_chk@plt>
    3600:	48 89 e8             	mov    %rbp,%rax
    3603:	48 c1 fd 3f          	sar    $0x3f,%rbp
    3607:	48 8d 35 d3 3d 00 00 	lea    0x3dd3(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    360e:	49 f7 ec             	imul   %r12
    3611:	bf 01 00 00 00       	mov    $0x1,%edi
    3616:	31 c0                	xor    %eax,%eax
    3618:	48 d1 fa             	sar    %rdx
    361b:	48 29 ea             	sub    %rbp,%rdx
    361e:	e8 2d ee ff ff       	call   2450 <__printf_chk@plt>
    3623:	48 89 d8             	mov    %rbx,%rax
    3626:	48 c1 fb 3f          	sar    $0x3f,%rbx
    362a:	48 8d 35 c1 3d 00 00 	lea    0x3dc1(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    3631:	49 f7 ec             	imul   %r12
    3634:	bf 01 00 00 00       	mov    $0x1,%edi
    3639:	48 d1 fa             	sar    %rdx
    363c:	48 29 da             	sub    %rbx,%rdx
    363f:	31 c0                	xor    %eax,%eax
    3641:	e8 0a ee ff ff       	call   2450 <__printf_chk@plt>
    3646:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    364e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3657:	0f 85 ac 00 00 00    	jne    3709 <main+0x1119>
    365d:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    3664:	31 c0                	xor    %eax,%eax
    3666:	5b                   	pop    %rbx
    3667:	5d                   	pop    %rbp
    3668:	41 5c                	pop    %r12
    366a:	41 5d                	pop    %r13
    366c:	41 5e                	pop    %r14
    366e:	41 5f                	pop    %r15
    3670:	c3                   	ret
    3671:	48 8d 05 58 22 00 00 	lea    0x2258(%rip),%rax        # 58d0 <barriered_work>
    3678:	bb 02 00 00 00       	mov    $0x2,%ebx
    367d:	49 89 85 08 02 00 00 	mov    %rax,0x208(%r13)
    3684:	e9 dc f2 ff ff       	jmp    2965 <main+0x375>
    3689:	b8 89 88 88 88       	mov    $0x88888889,%eax
    368e:	45 89 fe             	mov    %r15d,%r14d
    3691:	4d 89 4d 00          	mov    %r9,0x0(%r13)
    3695:	4c 89 c9             	mov    %r9,%rcx
    3698:	4c 0f af f0          	imul   %rax,%r14
    369c:	bf 01 00 00 00       	mov    $0x1,%edi
    36a1:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    36a6:	48 8d 35 5c 3c 00 00 	lea    0x3c5c(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
    36ad:	41 c7 01 00 00 00 00 	movl   $0x0,(%r9)
    36b4:	49 c1 ee 23          	shr    $0x23,%r14
    36b8:	44 89 f0             	mov    %r14d,%eax
    36bb:	c1 e0 04             	shl    $0x4,%eax
    36be:	44 29 f0             	sub    %r14d,%eax
    36c1:	45 89 fe             	mov    %r15d,%r14d
    36c4:	41 29 c6             	sub    %eax,%r14d
    36c7:	49 63 c6             	movslq %r14d,%rax
    36ca:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    36ce:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    36d2:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    36d7:	89 ea                	mov    %ebp,%edx
    36d9:	49 c1 e0 04          	shl    $0x4,%r8
    36dd:	49 01 c0             	add    %rax,%r8
    36e0:	31 c0                	xor    %eax,%eax
    36e2:	4d 89 45 08          	mov    %r8,0x8(%r13)
    36e6:	e8 65 ed ff ff       	call   2450 <__printf_chk@plt>
    36eb:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    36f0:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    36f5:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    36fa:	49 89 c4             	mov    %rax,%r12
    36fd:	e9 42 f1 ff ff       	jmp    2844 <main+0x254>
    3702:	31 d2                	xor    %edx,%edx
    3704:	e9 fd fb ff ff       	jmp    3306 <main+0xd16>
    3709:	e8 22 ec ff ff       	call   2330 <__stack_chk_fail@plt>
    370e:	66 90                	xchg   %ax,%ax

0000000000003710 <_start>:
    3710:	f3 0f 1e fa          	endbr64
    3714:	31 ed                	xor    %ebp,%ebp
    3716:	49 89 d1             	mov    %rdx,%r9
    3719:	5e                   	pop    %rsi
    371a:	48 89 e2             	mov    %rsp,%rdx
    371d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3721:	50                   	push   %rax
    3722:	54                   	push   %rsp
    3723:	45 31 c0             	xor    %r8d,%r8d
    3726:	31 c9                	xor    %ecx,%ecx
    3728:	48 8d 3d c1 ee ff ff 	lea    -0x113f(%rip),%rdi        # 25f0 <main>
    372f:	ff 15 a3 68 00 00    	call   *0x68a3(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3735:	f4                   	hlt
    3736:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003740 <deregister_tm_clones>:
    3740:	48 8d 3d d9 68 00 00 	lea    0x68d9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3747:	48 8d 05 d2 68 00 00 	lea    0x68d2(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    374e:	48 39 f8             	cmp    %rdi,%rax
    3751:	74 15                	je     3768 <deregister_tm_clones+0x28>
    3753:	48 8b 05 86 68 00 00 	mov    0x6886(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    375a:	48 85 c0             	test   %rax,%rax
    375d:	74 09                	je     3768 <deregister_tm_clones+0x28>
    375f:	ff e0                	jmp    *%rax
    3761:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3768:	c3                   	ret
    3769:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003770 <register_tm_clones>:
    3770:	48 8d 3d a9 68 00 00 	lea    0x68a9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3777:	48 8d 35 a2 68 00 00 	lea    0x68a2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    377e:	48 29 fe             	sub    %rdi,%rsi
    3781:	48 89 f0             	mov    %rsi,%rax
    3784:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3788:	48 c1 f8 03          	sar    $0x3,%rax
    378c:	48 01 c6             	add    %rax,%rsi
    378f:	48 d1 fe             	sar    %rsi
    3792:	74 14                	je     37a8 <register_tm_clones+0x38>
    3794:	48 8b 05 55 68 00 00 	mov    0x6855(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    379b:	48 85 c0             	test   %rax,%rax
    379e:	74 08                	je     37a8 <register_tm_clones+0x38>
    37a0:	ff e0                	jmp    *%rax
    37a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    37a8:	c3                   	ret
    37a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037b0 <__do_global_dtors_aux>:
    37b0:	f3 0f 1e fa          	endbr64
    37b4:	80 3d 6d 68 00 00 00 	cmpb   $0x0,0x686d(%rip)        # a028 <completed.0>
    37bb:	75 2b                	jne    37e8 <__do_global_dtors_aux+0x38>
    37bd:	55                   	push   %rbp
    37be:	48 83 3d 32 68 00 00 00 	cmpq   $0x0,0x6832(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    37c6:	48 89 e5             	mov    %rsp,%rbp
    37c9:	74 0c                	je     37d7 <__do_global_dtors_aux+0x27>
    37cb:	48 8b 3d 36 68 00 00 	mov    0x6836(%rip),%rdi        # a008 <__dso_handle>
    37d2:	e8 d9 ea ff ff       	call   22b0 <__cxa_finalize@plt>
    37d7:	e8 64 ff ff ff       	call   3740 <deregister_tm_clones>
    37dc:	c6 05 45 68 00 00 01 	movb   $0x1,0x6845(%rip)        # a028 <completed.0>
    37e3:	5d                   	pop    %rbp
    37e4:	c3                   	ret
    37e5:	0f 1f 00             	nopl   (%rax)
    37e8:	c3                   	ret
    37e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037f0 <frame_dummy>:
    37f0:	f3 0f 1e fa          	endbr64
    37f4:	e9 77 ff ff ff       	jmp    3770 <register_tm_clones>
    37f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003800 <do_protected_write>:
    3800:	f3 0f 1e fa          	endbr64
    3804:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    380b:	48 8b 40 38          	mov    0x38(%rax),%rax
    380f:	48 83 87 00 02 00 00 01 	addq   $0x1,0x200(%rdi)
    3817:	48 8b 48 08          	mov    0x8(%rax),%rcx
    381b:	48 83 00 01          	addq   $0x1,(%rax)
    381f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3826:	48 85 c9             	test   %rcx,%rcx
    3829:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3830:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3834:	48 89 50 08          	mov    %rdx,0x8(%rax)
    3838:	31 c0                	xor    %eax,%eax
    383a:	c3                   	ret
    383b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003840 <barriered_reset>:
    3840:	f3 0f 1e fa          	endbr64
    3844:	48 63 8f 2c 02 00 00 	movslq 0x22c(%rdi),%rcx
    384b:	85 c9                	test   %ecx,%ecx
    384d:	7e 64                	jle    38b3 <barriered_reset+0x73>
    384f:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    3856:	48 63 bf 20 02 00 00 	movslq 0x220(%rdi),%rdi
    385d:	48 8d 0c 89          	lea    (%rcx,%rcx,4),%rcx
    3861:	48 c1 e1 07          	shl    $0x7,%rcx
    3865:	48 8b 70 28          	mov    0x28(%rax),%rsi
    3869:	48 8b 40 10          	mov    0x10(%rax),%rax
    386d:	48 8b 04 f8          	mov    (%rax,%rdi,8),%rax
    3871:	48 8d 96 28 02 00 00 	lea    0x228(%rsi),%rdx
    3878:	48 8d 8c 0e 28 02 00 00 	lea    0x228(%rsi,%rcx,1),%rcx
    3880:	48 8b 40 28          	mov    0x28(%rax),%rax
    3884:	48 05 00 01 00 00    	add    $0x100,%rax
    388a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3890:	83 40 80 01          	addl   $0x1,-0x80(%rax)
    3894:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
    389b:	83 00 01             	addl   $0x1,(%rax)
    389e:	48 05 80 02 00 00    	add    $0x280,%rax
    38a4:	c7 82 80 fd ff ff 01 00 00 00 	movl   $0x1,-0x280(%rdx)
    38ae:	48 39 ca             	cmp    %rcx,%rdx
    38b1:	75 dd                	jne    3890 <barriered_reset+0x50>
    38b3:	0f ae f8             	sfence
    38b6:	31 c0                	xor    %eax,%eax
    38b8:	c3                   	ret
    38b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000038c0 <barriered_thread>:
    38c0:	f3 0f 1e fa          	endbr64
    38c4:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    38c8:	0f 85 a8 02 00 00    	jne    3b76 <barriered_thread+0x2b6>
    38ce:	41 56                	push   %r14
    38d0:	41 55                	push   %r13
    38d2:	45 31 ed             	xor    %r13d,%r13d
    38d5:	41 54                	push   %r12
    38d7:	49 89 fc             	mov    %rdi,%r12
    38da:	55                   	push   %rbp
    38db:	53                   	push   %rbx
    38dc:	31 db                	xor    %ebx,%ebx
    38de:	66 90                	xchg   %ax,%ax
    38e0:	41 8b 54 24 30       	mov    0x30(%r12),%edx
    38e5:	39 da                	cmp    %ebx,%edx
    38e7:	7f 13                	jg     38fc <barriered_thread+0x3c>
    38e9:	49 83 84 24 98 00 00 00 01 	addq   $0x1,0x98(%r12)
    38f2:	31 db                	xor    %ebx,%ebx
    38f4:	85 d2                	test   %edx,%edx
    38f6:	0f 8e 64 01 00 00    	jle    3a60 <barriered_thread+0x1a0>
    38fc:	48 63 c3             	movslq %ebx,%rax
    38ff:	48 8d 2c 80          	lea    (%rax,%rax,4),%rbp
    3903:	48 c1 e5 07          	shl    $0x7,%rbp
    3907:	eb 19                	jmp    3922 <barriered_thread+0x62>
    3909:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3910:	83 c3 01             	add    $0x1,%ebx
    3913:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    391a:	39 d3                	cmp    %edx,%ebx
    391c:	0f 8d 3e 01 00 00    	jge    3a60 <barriered_thread+0x1a0>
    3922:	49 8b 44 24 28       	mov    0x28(%r12),%rax
    3927:	48 8d 0c 28          	lea    (%rax,%rbp,1),%rcx
    392b:	83 b9 28 02 00 00 01 	cmpl   $0x1,0x228(%rcx)
    3932:	75 dc                	jne    3910 <barriered_thread+0x50>
    3934:	41 8b 7c 24 18       	mov    0x18(%r12),%edi
    3939:	83 ea 01             	sub    $0x1,%edx
    393c:	8d 73 ff             	lea    -0x1(%rbx),%esi
    393f:	85 db                	test   %ebx,%ebx
    3941:	0f 4f d6             	cmovg  %esi,%edx
    3944:	85 ff                	test   %edi,%edi
    3946:	0f 8e d4 01 00 00    	jle    3b20 <barriered_thread+0x260>
    394c:	48 63 d2             	movslq %edx,%rdx
    394f:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    3954:	45 31 d2             	xor    %r10d,%r10d
    3957:	45 31 f6             	xor    %r14d,%r14d
    395a:	48 8d 34 92          	lea    (%rdx,%rdx,4),%rsi
    395e:	48 63 d7             	movslq %edi,%rdx
    3961:	44 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9d
    3968:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    396f:	48 c1 e6 07          	shl    $0x7,%rsi
    3973:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    3977:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3980:	48 8b 10             	mov    (%rax),%rdx
    3983:	4c 8b 5a 28          	mov    0x28(%rdx),%r11
    3987:	49 01 f3             	add    %rsi,%r11
    398a:	4c 89 da             	mov    %r11,%rdx
    398d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    3994:	75 04                	jne    399a <barriered_thread+0xda>
    3996:	41 83 c6 01          	add    $0x1,%r14d
    399a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    39a1:	75 04                	jne    39a7 <barriered_thread+0xe7>
    39a3:	41 83 c2 01          	add    $0x1,%r10d
    39a7:	48 83 c0 08          	add    $0x8,%rax
    39ab:	48 39 c8             	cmp    %rcx,%rax
    39ae:	75 d0                	jne    3980 <barriered_thread+0xc0>
    39b0:	44 39 d7             	cmp    %r10d,%edi
    39b3:	0f 84 c7 00 00 00    	je     3a80 <barriered_thread+0x1c0>
    39b9:	45 85 d2             	test   %r10d,%r10d
    39bc:	0f 84 be 00 00 00    	je     3a80 <barriered_thread+0x1c0>
    39c2:	45 85 f6             	test   %r14d,%r14d
    39c5:	74 0b                	je     39d2 <barriered_thread+0x112>
    39c7:	45 39 74 24 18       	cmp    %r14d,0x18(%r12)
    39cc:	0f 85 8e 00 00 00    	jne    3a60 <barriered_thread+0x1a0>
    39d2:	49 8b 44 24 28       	mov    0x28(%r12),%rax
    39d7:	48 01 e8             	add    %rbp,%rax
    39da:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
    39e1:	85 db                	test   %ebx,%ebx
    39e3:	75 10                	jne    39f5 <barriered_thread+0x135>
    39e5:	49 8b 74 24 70       	mov    0x70(%r12),%rsi
    39ea:	49 3b 74 24 78       	cmp    0x78(%r12),%rsi
    39ef:	0f 8c 0b 01 00 00    	jl     3b00 <barriered_thread+0x240>
    39f5:	49 63 0c 24          	movslq (%r12),%rcx
    39f9:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    39fe:	c7 80 28 02 00 00 00 00 00 00 	movl   $0x0,0x228(%rax)
    3a08:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    3a0c:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
    3a10:	48 01 ef             	add    %rbp,%rdi
    3a13:	ff 90 08 02 00 00    	call   *0x208(%rax)
    3a19:	49 8b 44 24 28       	mov    0x28(%r12),%rax
    3a1e:	48 01 e8             	add    %rbp,%rax
    3a21:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
    3a28:	41 8b 44 24 30       	mov    0x30(%r12),%eax
    3a2d:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
    3a33:	83 e8 01             	sub    $0x1,%eax
    3a36:	39 d8                	cmp    %ebx,%eax
    3a38:	74 5e                	je     3a98 <barriered_thread+0x1d8>
    3a3a:	0f ae f8             	sfence
    3a3d:	45 85 ed             	test   %r13d,%r13d
    3a40:	0f 84 82 00 00 00    	je     3ac8 <barriered_thread+0x208>
    3a46:	41 8b 54 24 30       	mov    0x30(%r12),%edx
    3a4b:	83 c3 01             	add    $0x1,%ebx
    3a4e:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    3a55:	39 d3                	cmp    %edx,%ebx
    3a57:	0f 8c c5 fe ff ff    	jl     3922 <barriered_thread+0x62>
    3a5d:	0f 1f 00             	nopl   (%rax)
    3a60:	41 83 7c 24 34 01    	cmpl   $0x1,0x34(%r12)
    3a66:	0f 84 74 fe ff ff    	je     38e0 <barriered_thread+0x20>
    3a6c:	5b                   	pop    %rbx
    3a6d:	31 c0                	xor    %eax,%eax
    3a6f:	5d                   	pop    %rbp
    3a70:	41 5c                	pop    %r12
    3a72:	41 5d                	pop    %r13
    3a74:	41 5e                	pop    %r14
    3a76:	c3                   	ret
    3a77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3a80:	41 83 fd 01          	cmp    $0x1,%r13d
    3a84:	0f 84 a6 00 00 00    	je     3b30 <barriered_thread+0x270>
    3a8a:	45 31 ed             	xor    %r13d,%r13d
    3a8d:	e9 30 ff ff ff       	jmp    39c2 <barriered_thread+0x102>
    3a92:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3a98:	49 8b 74 24 70       	mov    0x70(%r12),%rsi
    3a9d:	49 3b 74 24 78       	cmp    0x78(%r12),%rsi
    3aa2:	7d 96                	jge    3a3a <barriered_thread+0x17a>
    3aa4:	48 c1 e6 04          	shl    $0x4,%rsi
    3aa8:	bf 04 00 00 00       	mov    $0x4,%edi
    3aad:	49 03 74 24 60       	add    0x60(%r12),%rsi
    3ab2:	e8 59 e8 ff ff       	call   2310 <clock_gettime@plt>
    3ab7:	49 83 44 24 70 01    	addq   $0x1,0x70(%r12)
    3abd:	e9 78 ff ff ff       	jmp    3a3a <barriered_thread+0x17a>
    3ac2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3ac8:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
    3ad0:	bf 04 00 00 00       	mov    $0x4,%edi
    3ad5:	41 bd 01 00 00 00    	mov    $0x1,%r13d
    3adb:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3adf:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3ae7:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3aeb:	89 5e 20             	mov    %ebx,0x20(%rsi)
    3aee:	e8 1d e8 ff ff       	call   2310 <clock_gettime@plt>
    3af3:	41 8b 54 24 30       	mov    0x30(%r12),%edx
    3af8:	e9 13 fe ff ff       	jmp    3910 <barriered_thread+0x50>
    3afd:	0f 1f 00             	nopl   (%rax)
    3b00:	48 c1 e6 04          	shl    $0x4,%rsi
    3b04:	bf 04 00 00 00       	mov    $0x4,%edi
    3b09:	49 03 74 24 58       	add    0x58(%r12),%rsi
    3b0e:	e8 fd e7 ff ff       	call   2310 <clock_gettime@plt>
    3b13:	49 8b 44 24 28       	mov    0x28(%r12),%rax
    3b18:	48 01 e8             	add    %rbp,%rax
    3b1b:	e9 d5 fe ff ff       	jmp    39f5 <barriered_thread+0x135>
    3b20:	41 83 fd 01          	cmp    $0x1,%r13d
    3b24:	0f 85 ad fe ff ff    	jne    39d7 <barriered_thread+0x117>
    3b2a:	45 31 f6             	xor    %r14d,%r14d
    3b2d:	0f 1f 00             	nopl   (%rax)
    3b30:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
    3b38:	bf 04 00 00 00       	mov    $0x4,%edi
    3b3d:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3b41:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3b49:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3b4e:	e8 bd e7 ff ff       	call   2310 <clock_gettime@plt>
    3b53:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
    3b5b:	48 83 c0 01          	add    $0x1,%rax
    3b5f:	48 99                	cqto
    3b61:	49 f7 bc 24 90 00 00 00 	idivq  0x90(%r12)
    3b69:	49 89 94 24 88 00 00 00 	mov    %rdx,0x88(%r12)
    3b71:	e9 14 ff ff ff       	jmp    3a8a <barriered_thread+0x1ca>
    3b76:	31 c0                	xor    %eax,%eax
    3b78:	c3                   	ret
    3b79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003b80 <external_thread>:
    3b80:	f3 0f 1e fa          	endbr64
    3b84:	41 55                	push   %r13
    3b86:	41 54                	push   %r12
    3b88:	55                   	push   %rbp
    3b89:	53                   	push   %rbx
    3b8a:	48 83 ec 38          	sub    $0x38,%rsp
    3b8e:	66 0f 6f 05 aa 3d 00 00 	movdqa 0x3daa(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3b96:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3b9f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3ba4:	31 c0                	xor    %eax,%eax
    3ba6:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    3baa:	0f 29 04 24          	movaps %xmm0,(%rsp)
    3bae:	75 64                	jne    3c14 <external_thread+0x94>
    3bb0:	49 89 fd             	mov    %rdi,%r13
    3bb3:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3bb8:	48 89 e3             	mov    %rsp,%rbx
    3bbb:	4c 8d 25 42 34 00 00 	lea    0x3442(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    3bc2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3bc8:	48 89 ee             	mov    %rbp,%rsi
    3bcb:	48 89 df             	mov    %rbx,%rdi
    3bce:	e8 7d e7 ff ff       	call   2350 <nanosleep@plt>
    3bd3:	49 8b 45 40          	mov    0x40(%r13),%rax
    3bd7:	48 63 10             	movslq (%rax),%rdx
    3bda:	85 d2                	test   %edx,%edx
    3bdc:	7e 2c                	jle    3c0a <external_thread+0x8a>
    3bde:	48 8b 40 08          	mov    0x8(%rax),%rax
    3be2:	48 c1 e2 04          	shl    $0x4,%rdx
    3be6:	48 01 c2             	add    %rax,%rdx
    3be9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3bf0:	8b 48 08             	mov    0x8(%rax),%ecx
    3bf3:	85 c9                	test   %ecx,%ecx
    3bf5:	75 0a                	jne    3c01 <external_thread+0x81>
    3bf7:	4c 89 20             	mov    %r12,(%rax)
    3bfa:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    3c01:	48 83 c0 10          	add    $0x10,%rax
    3c05:	48 39 c2             	cmp    %rax,%rdx
    3c08:	75 e6                	jne    3bf0 <external_thread+0x70>
    3c0a:	0f ae f0             	mfence
    3c0d:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
    3c12:	74 b4                	je     3bc8 <external_thread+0x48>
    3c14:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3c19:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3c22:	75 0d                	jne    3c31 <external_thread+0xb1>
    3c24:	48 83 c4 38          	add    $0x38,%rsp
    3c28:	31 c0                	xor    %eax,%eax
    3c2a:	5b                   	pop    %rbx
    3c2b:	5d                   	pop    %rbp
    3c2c:	41 5c                	pop    %r12
    3c2e:	41 5d                	pop    %r13
    3c30:	c3                   	ret
    3c31:	e8 fa e6 ff ff       	call   2330 <__stack_chk_fail@plt>
    3c36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003c40 <timer_thread>:
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
    3c78:	66 0f 6f 05 c0 3c 00 00 	movdqa 0x3cc0(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3c80:	ba 88 13 00 00       	mov    $0x1388,%edx
    3c85:	31 c0                	xor    %eax,%eax
    3c87:	48 8d 35 94 33 00 00 	lea    0x3394(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3c8e:	bf 01 00 00 00       	mov    $0x1,%edi
    3c93:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3c98:	e8 b3 e7 ff ff       	call   2450 <__printf_chk@plt>
    3c9d:	45 8b 6f 34          	mov    0x34(%r15),%r13d
    3ca1:	45 85 ed             	test   %r13d,%r13d
    3ca4:	0f 84 a7 00 00 00    	je     3d51 <timer_thread+0x111>
    3caa:	45 31 f6             	xor    %r14d,%r14d
    3cad:	45 31 ed             	xor    %r13d,%r13d
    3cb0:	49 89 e4             	mov    %rsp,%r12
    3cb3:	31 db                	xor    %ebx,%ebx
    3cb5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3cba:	48 89 ef             	mov    %rbp,%rdi
    3cbd:	4c 89 e6             	mov    %r12,%rsi
    3cc0:	41 83 c6 01          	add    $0x1,%r14d
    3cc4:	e8 87 e6 ff ff       	call   2350 <nanosleep@plt>
    3cc9:	49 63 47 18          	movslq 0x18(%r15),%rax
    3ccd:	41 8d 7d 01          	lea    0x1(%r13),%edi
    3cd1:	85 c0                	test   %eax,%eax
    3cd3:	7e 54                	jle    3d29 <timer_thread+0xe9>
    3cd5:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3cd9:	4f 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%r8
    3cde:	49 c1 e0 07          	shl    $0x7,%r8
    3ce2:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3ce6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3cf0:	4c 8b 19             	mov    (%rcx),%r11
    3cf3:	89 f8                	mov    %edi,%eax
    3cf5:	48 83 c1 08          	add    $0x8,%rcx
    3cf9:	99                   	cltd
    3cfa:	41 f7 7b 30          	idivl  0x30(%r11)
    3cfe:	49 8b 73 28          	mov    0x28(%r11),%rsi
    3d02:	48 63 d2             	movslq %edx,%rdx
    3d05:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    3d09:	48 c1 e0 07          	shl    $0x7,%rax
    3d0d:	c7 84 06 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rsi,%rax,1)
    3d18:	42 c7 84 06 30 02 00 00 00 00 00 00 	movl   $0x0,0x230(%rsi,%r8,1)
    3d24:	49 39 c9             	cmp    %rcx,%r9
    3d27:	75 c7                	jne    3cf0 <timer_thread+0xb0>
    3d29:	0f ae f0             	mfence
    3d2c:	49 8b 47 10          	mov    0x10(%r15),%rax
    3d30:	41 8b 57 34          	mov    0x34(%r15),%edx
    3d34:	48 8b 00             	mov    (%rax),%rax
    3d37:	39 78 30             	cmp    %edi,0x30(%rax)
    3d3a:	0f 4e fb             	cmovle %ebx,%edi
    3d3d:	4c 63 ef             	movslq %edi,%r13
    3d40:	85 d2                	test   %edx,%edx
    3d42:	74 0d                	je     3d51 <timer_thread+0x111>
    3d44:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3d4b:	0f 85 69 ff ff ff    	jne    3cba <timer_thread+0x7a>
    3d51:	48 8d 3d e0 32 00 00 	lea    0x32e0(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3d58:	e8 93 e5 ff ff       	call   22f0 <puts@plt>
    3d5d:	49 63 47 1c          	movslq 0x1c(%r15),%rax
    3d61:	85 c0                	test   %eax,%eax
    3d63:	0f 8e 84 00 00 00    	jle    3ded <timer_thread+0x1ad>
    3d69:	41 8b 57 30          	mov    0x30(%r15),%edx
    3d6d:	85 d2                	test   %edx,%edx
    3d6f:	7e 7c                	jle    3ded <timer_thread+0x1ad>
    3d71:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    3d79:	48 63 c2             	movslq %edx,%rax
    3d7c:	4d 8b 4f 10          	mov    0x10(%r15),%r9
    3d80:	31 f6                	xor    %esi,%esi
    3d82:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3d86:	48 c1 e0 07          	shl    $0x7,%rax
    3d8a:	4c 8d 80 68 02 00 00 	lea    0x268(%rax),%r8
    3d91:	49 8b 04 31          	mov    (%r9,%rsi,1),%rax
    3d95:	48 8b 78 28          	mov    0x28(%rax),%rdi
    3d99:	4a 8d 14 07          	lea    (%rdi,%r8,1),%rdx
    3d9d:	48 8d 87 68 02 00 00 	lea    0x268(%rdi),%rax
    3da4:	49 89 d2             	mov    %rdx,%r10
    3da7:	49 29 c2             	sub    %rax,%r10
    3daa:	41 81 e2 80 00 00 00 	and    $0x80,%r10d
    3db1:	74 16                	je     3dc9 <timer_thread+0x189>
    3db3:	48 8d 87 e8 04 00 00 	lea    0x4e8(%rdi),%rax
    3dba:	c7 87 68 02 00 00 00 00 00 00 	movl   $0x0,0x268(%rdi)
    3dc4:	48 39 c2             	cmp    %rax,%rdx
    3dc7:	74 1b                	je     3de4 <timer_thread+0x1a4>
    3dc9:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    3dcf:	48 05 00 05 00 00    	add    $0x500,%rax
    3dd5:	c7 80 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%rax)
    3ddf:	48 39 c2             	cmp    %rax,%rdx
    3de2:	75 e5                	jne    3dc9 <timer_thread+0x189>
    3de4:	48 83 c6 08          	add    $0x8,%rsi
    3de8:	48 39 f1             	cmp    %rsi,%rcx
    3deb:	75 a4                	jne    3d91 <timer_thread+0x151>
    3ded:	0f ae f0             	mfence
    3df0:	66 0f 6f 05 58 3b 00 00 	movdqa 0x3b58(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3df8:	48 8d 2d 5e 32 00 00 	lea    0x325e(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3dff:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    3e04:	49 63 47 18          	movslq 0x18(%r15),%rax
    3e08:	41 8d 7d 01          	lea    0x1(%r13),%edi
    3e0c:	85 c0                	test   %eax,%eax
    3e0e:	7e 50                	jle    3e60 <timer_thread+0x220>
    3e10:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3e14:	4d 63 ed             	movslq %r13d,%r13
    3e17:	4f 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%r8
    3e1c:	49 c1 e0 07          	shl    $0x7,%r8
    3e20:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3e24:	0f 1f 40 00          	nopl   0x0(%rax)
    3e28:	48 8b 19             	mov    (%rcx),%rbx
    3e2b:	89 f8                	mov    %edi,%eax
    3e2d:	48 83 c1 08          	add    $0x8,%rcx
    3e31:	99                   	cltd
    3e32:	f7 7b 30             	idivl  0x30(%rbx)
    3e35:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3e39:	48 63 c2             	movslq %edx,%rax
    3e3c:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3e40:	48 c1 e0 07          	shl    $0x7,%rax
    3e44:	c7 84 06 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rsi,%rax,1)
    3e4f:	42 c7 84 06 30 02 00 00 00 00 00 00 	movl   $0x0,0x230(%rsi,%r8,1)
    3e5b:	49 39 c9             	cmp    %rcx,%r9
    3e5e:	75 c8                	jne    3e28 <timer_thread+0x1e8>
    3e60:	0f ae f0             	mfence
    3e63:	49 8b 47 10          	mov    0x10(%r15),%rax
    3e67:	45 31 ed             	xor    %r13d,%r13d
    3e6a:	48 8b 10             	mov    (%rax),%rdx
    3e6d:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3e70:	44 0f 4f ef          	cmovg  %edi,%r13d
    3e74:	41 8b 7f 20          	mov    0x20(%r15),%edi
    3e78:	85 ff                	test   %edi,%edi
    3e7a:	0f 8e c0 00 00 00    	jle    3f40 <timer_thread+0x300>
    3e80:	45 31 e4             	xor    %r12d,%r12d
    3e83:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3e89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3e90:	4a 8d 1c e5 00 00 00 00 	lea    0x0(,%r12,8),%rbx
    3e98:	45 31 f6             	xor    %r14d,%r14d
    3e9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3ea0:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3ea4:	4b 8d 04 b6          	lea    (%r14,%r14,4),%rax
    3ea8:	48 c1 e0 07          	shl    $0x7,%rax
    3eac:	48 03 42 28          	add    0x28(%rdx),%rax
    3eb0:	31 d2                	xor    %edx,%edx
    3eb2:	48 8b 80 58 02 00 00 	mov    0x258(%rax),%rax
    3eb9:	eb 17                	jmp    3ed2 <timer_thread+0x292>
    3ebb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3ec0:	4d 85 c0             	test   %r8,%r8
    3ec3:	7f 24                	jg     3ee9 <timer_thread+0x2a9>
    3ec5:	83 c2 01             	add    $0x1,%edx
    3ec8:	48 05 00 02 00 00    	add    $0x200,%rax
    3ece:	39 fa                	cmp    %edi,%edx
    3ed0:	74 2d                	je     3eff <timer_thread+0x2bf>
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
    3ef8:	41 8b 7f 20          	mov    0x20(%r15),%edi
    3efc:	45 31 c9             	xor    %r9d,%r9d
    3eff:	49 83 c6 01          	add    $0x1,%r14
    3f03:	44 39 f7             	cmp    %r14d,%edi
    3f06:	7e 08                	jle    3f10 <timer_thread+0x2d0>
    3f08:	49 8b 47 10          	mov    0x10(%r15),%rax
    3f0c:	eb 92                	jmp    3ea0 <timer_thread+0x260>
    3f0e:	66 90                	xchg   %ax,%ax
    3f10:	49 83 c4 01          	add    $0x1,%r12
    3f14:	44 39 e7             	cmp    %r12d,%edi
    3f17:	7e 0d                	jle    3f26 <timer_thread+0x2e6>
    3f19:	85 ff                	test   %edi,%edi
    3f1b:	7e 09                	jle    3f26 <timer_thread+0x2e6>
    3f1d:	49 8b 47 10          	mov    0x10(%r15),%rax
    3f21:	e9 6a ff ff ff       	jmp    3e90 <timer_thread+0x250>
    3f26:	41 83 f9 01          	cmp    $0x1,%r9d
    3f2a:	74 14                	je     3f40 <timer_thread+0x300>
    3f2c:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3f31:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3f36:	e8 15 e4 ff ff       	call   2350 <nanosleep@plt>
    3f3b:	e9 c4 fe ff ff       	jmp    3e04 <timer_thread+0x1c4>
    3f40:	48 8d 3d 0d 31 00 00 	lea    0x310d(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3f47:	e8 a4 e3 ff ff       	call   22f0 <puts@plt>
    3f4c:	41 8b 47 34          	mov    0x34(%r15),%eax
    3f50:	85 c0                	test   %eax,%eax
    3f52:	0f 84 e3 00 00 00    	je     403b <timer_thread+0x3fb>
    3f58:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3f5c:	85 c9                	test   %ecx,%ecx
    3f5e:	7e 2d                	jle    3f8d <timer_thread+0x34d>
    3f60:	49 8b 47 10          	mov    0x10(%r15),%rax
    3f64:	31 db                	xor    %ebx,%ebx
    3f66:	48 8d 2d 01 31 00 00 	lea    0x3101(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3f6d:	0f 1f 00             	nopl   (%rax)
    3f70:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
    3f74:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
    3f78:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
    3f7f:	0f 84 e3 00 00 00    	je     4068 <timer_thread+0x428>
    3f85:	48 83 c3 01          	add    $0x1,%rbx
    3f89:	39 d9                	cmp    %ebx,%ecx
    3f8b:	7f e3                	jg     3f70 <timer_thread+0x330>
    3f8d:	49 63 47 18          	movslq 0x18(%r15),%rax
    3f91:	85 c0                	test   %eax,%eax
    3f93:	0f 8e 8b 00 00 00    	jle    4024 <timer_thread+0x3e4>
    3f99:	41 8b 57 30          	mov    0x30(%r15),%edx
    3f9d:	85 d2                	test   %edx,%edx
    3f9f:	0f 8e 7f 00 00 00    	jle    4024 <timer_thread+0x3e4>
    3fa5:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
    3fad:	48 63 c2             	movslq %edx,%rax
    3fb0:	4d 8b 57 10          	mov    0x10(%r15),%r10
    3fb4:	31 c9                	xor    %ecx,%ecx
    3fb6:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3fba:	48 c1 e0 07          	shl    $0x7,%rax
    3fbe:	4c 8d 88 30 02 00 00 	lea    0x230(%rax),%r9
    3fc5:	0f 1f 00             	nopl   (%rax)
    3fc8:	49 8b 04 0a          	mov    (%r10,%rcx,1),%rax
    3fcc:	48 8b 70 28          	mov    0x28(%rax),%rsi
    3fd0:	4a 8d 14 0e          	lea    (%rsi,%r9,1),%rdx
    3fd4:	48 8d 86 30 02 00 00 	lea    0x230(%rsi),%rax
    3fdb:	48 89 d7             	mov    %rdx,%rdi
    3fde:	48 29 c7             	sub    %rax,%rdi
    3fe1:	81 e7 80 00 00 00    	and    $0x80,%edi
    3fe7:	74 17                	je     4000 <timer_thread+0x3c0>
    3fe9:	48 8d 86 b0 04 00 00 	lea    0x4b0(%rsi),%rax
    3ff0:	c7 86 30 02 00 00 00 00 00 00 	movl   $0x0,0x230(%rsi)
    3ffa:	48 39 d0             	cmp    %rdx,%rax
    3ffd:	74 1c                	je     401b <timer_thread+0x3db>
    3fff:	90                   	nop
    4000:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    4006:	48 05 00 05 00 00    	add    $0x500,%rax
    400c:	c7 80 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%rax)
    4016:	48 39 d0             	cmp    %rdx,%rax
    4019:	75 e5                	jne    4000 <timer_thread+0x3c0>
    401b:	48 83 c1 08          	add    $0x8,%rcx
    401f:	4c 39 c1             	cmp    %r8,%rcx
    4022:	75 a4                	jne    3fc8 <timer_thread+0x388>
    4024:	0f ae f0             	mfence
    4027:	48 8d 3d 52 30 00 00 	lea    0x3052(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    402e:	e8 bd e2 ff ff       	call   22f0 <puts@plt>
    4033:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
    403b:	48 8d 3d 45 30 00 00 	lea    0x3045(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    4042:	e8 a9 e2 ff ff       	call   22f0 <puts@plt>
    4047:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    404c:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4055:	75 47                	jne    409e <timer_thread+0x45e>
    4057:	48 83 c4 58          	add    $0x58,%rsp
    405b:	31 c0                	xor    %eax,%eax
    405d:	5b                   	pop    %rbx
    405e:	5d                   	pop    %rbp
    405f:	41 5c                	pop    %r12
    4061:	41 5d                	pop    %r13
    4063:	41 5e                	pop    %r14
    4065:	41 5f                	pop    %r15
    4067:	c3                   	ret
    4068:	48 89 ef             	mov    %rbp,%rdi
    406b:	e8 80 e2 ff ff       	call   22f0 <puts@plt>
    4070:	49 8b 47 10          	mov    0x10(%r15),%rax
    4074:	be 01 00 00 00       	mov    $0x1,%esi
    4079:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    407d:	48 83 c3 01          	add    $0x1,%rbx
    4081:	8b 78 50             	mov    0x50(%rax),%edi
    4084:	e8 77 e3 ff ff       	call   2400 <eventfd_write@plt>
    4089:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    408d:	39 d9                	cmp    %ebx,%ecx
    408f:	0f 8e f8 fe ff ff    	jle    3f8d <timer_thread+0x34d>
    4095:	49 8b 47 10          	mov    0x10(%r15),%rax
    4099:	e9 d2 fe ff ff       	jmp    3f70 <timer_thread+0x330>
    409e:	e8 8d e2 ff ff       	call   2330 <__stack_chk_fail@plt>
    40a3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    40ae:	66 90                	xchg   %ax,%ax

00000000000040b0 <strtolower>:
    40b0:	f3 0f 1e fa          	endbr64
    40b4:	55                   	push   %rbp
    40b5:	53                   	push   %rbx
    40b6:	48 83 ec 08          	sub    $0x8,%rsp
    40ba:	48 0f be 1f          	movsbq (%rdi),%rbx
    40be:	84 db                	test   %bl,%bl
    40c0:	74 24                	je     40e6 <strtolower+0x36>
    40c2:	48 89 fd             	mov    %rdi,%rbp
    40c5:	e8 46 e4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    40ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    40d0:	48 8b 10             	mov    (%rax),%rdx
    40d3:	48 83 c5 01          	add    $0x1,%rbp
    40d7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    40da:	88 55 ff             	mov    %dl,-0x1(%rbp)
    40dd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    40e2:	84 db                	test   %bl,%bl
    40e4:	75 ea                	jne    40d0 <strtolower+0x20>
    40e6:	48 83 c4 08          	add    $0x8,%rsp
    40ea:	5b                   	pop    %rbx
    40eb:	5d                   	pop    %rbp
    40ec:	c3                   	ret
    40ed:	0f 1f 00             	nopl   (%rax)

00000000000040f0 <zh_malloc>:
    40f0:	f3 0f 1e fa          	endbr64
    40f4:	48 83 ec 08          	sub    $0x8,%rsp
    40f8:	e8 13 e3 ff ff       	call   2410 <malloc@plt>
    40fd:	48 85 c0             	test   %rax,%rax
    4100:	74 05                	je     4107 <zh_malloc+0x17>
    4102:	48 83 c4 08          	add    $0x8,%rsp
    4106:	c3                   	ret
    4107:	48 8b 0d 12 5f 00 00 	mov    0x5f12(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    410e:	ba 28 00 00 00       	mov    $0x28,%edx
    4113:	be 01 00 00 00       	mov    $0x1,%esi
    4118:	48 8d 3d e9 32 00 00 	lea    0x32e9(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    411f:	e8 9c e3 ff ff       	call   24c0 <fwrite@plt>
    4124:	bf 01 00 00 00       	mov    $0x1,%edi
    4129:	e8 72 e3 ff ff       	call   24a0 <exit@plt>
    412e:	66 90                	xchg   %ax,%ax

0000000000004130 <get_filename_ext>:
    4130:	f3 0f 1e fa          	endbr64
    4134:	53                   	push   %rbx
    4135:	be 2e 00 00 00       	mov    $0x2e,%esi
    413a:	48 89 fb             	mov    %rdi,%rbx
    413d:	e8 1e e2 ff ff       	call   2360 <strrchr@plt>
    4142:	48 85 c0             	test   %rax,%rax
    4145:	74 11                	je     4158 <get_filename_ext+0x28>
    4147:	48 39 c3             	cmp    %rax,%rbx
    414a:	74 0c                	je     4158 <get_filename_ext+0x28>
    414c:	48 83 c0 01          	add    $0x1,%rax
    4150:	5b                   	pop    %rbx
    4151:	c3                   	ret
    4152:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4158:	48 8d 05 70 2f 00 00 	lea    0x2f70(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
    415f:	5b                   	pop    %rbx
    4160:	c3                   	ret
    4161:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    416c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004170 <send_headers>:
    4170:	f3 0f 1e fa          	endbr64
    4174:	41 55                	push   %r13
    4176:	49 89 f5             	mov    %rsi,%r13
    4179:	48 89 fe             	mov    %rdi,%rsi
    417c:	41 54                	push   %r12
    417e:	55                   	push   %rbp
    417f:	48 89 d5             	mov    %rdx,%rbp
    4182:	ba 00 04 00 00       	mov    $0x400,%edx
    4187:	53                   	push   %rbx
    4188:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    418f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4198:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    41a0:	31 c0                	xor    %eax,%eax
    41a2:	49 89 e4             	mov    %rsp,%r12
    41a5:	4c 89 e7             	mov    %r12,%rdi
    41a8:	e8 83 e2 ff ff       	call   2430 <__strcpy_chk@plt>
    41ad:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    41b2:	84 db                	test   %bl,%bl
    41b4:	74 24                	je     41da <send_headers+0x6a>
    41b6:	e8 55 e3 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    41bb:	48 8b 08             	mov    (%rax),%rcx
    41be:	4c 89 e0             	mov    %r12,%rax
    41c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    41c8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    41cb:	48 83 c0 01          	add    $0x1,%rax
    41cf:	88 50 ff             	mov    %dl,-0x1(%rax)
    41d2:	48 0f be 18          	movsbq (%rax),%rbx
    41d6:	84 db                	test   %bl,%bl
    41d8:	75 ee                	jne    41c8 <send_headers+0x58>
    41da:	bf 11 00 00 00       	mov    $0x11,%edi
    41df:	e8 2c e2 ff ff       	call   2410 <malloc@plt>
    41e4:	48 85 c0             	test   %rax,%rax
    41e7:	0f 84 7e 04 00 00    	je     466b <send_headers+0x4fb>
    41ed:	66 0f 6f 05 6b 37 00 00 	movdqa 0x376b(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    41f5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    41f9:	bf 17 00 00 00       	mov    $0x17,%edi
    41fe:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4206:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    420a:	0f 11 00             	movups %xmm0,(%rax)
    420d:	e8 fe e1 ff ff       	call   2410 <malloc@plt>
    4212:	48 85 c0             	test   %rax,%rax
    4215:	0f 84 50 04 00 00    	je     466b <send_headers+0x4fb>
    421b:	66 0f 6f 05 4d 37 00 00 	movdqa 0x374d(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    4223:	48 89 45 10          	mov    %rax,0x10(%rbp)
    4227:	4c 89 e7             	mov    %r12,%rdi
    422a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    4234:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    423c:	0f 11 00             	movups %xmm0,(%rax)
    423f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    4243:	be 2e 00 00 00       	mov    $0x2e,%esi
    4248:	e8 13 e1 ff ff       	call   2360 <strrchr@plt>
    424d:	48 85 c0             	test   %rax,%rax
    4250:	0f 84 ea 02 00 00    	je     4540 <send_headers+0x3d0>
    4256:	4c 39 e0             	cmp    %r12,%rax
    4259:	0f 84 e1 02 00 00    	je     4540 <send_headers+0x3d0>
    425f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    4263:	48 8d 3d 33 2e 00 00 	lea    0x2e33(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    426a:	48 89 de             	mov    %rbx,%rsi
    426d:	e8 3e e1 ff ff       	call   23b0 <strcmp@plt>
    4272:	85 c0                	test   %eax,%eax
    4274:	75 20                	jne    4296 <send_headers+0x126>
    4276:	66 0f 6f 05 02 37 00 00 	movdqa 0x3702(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    427e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4286:	66 0f 6f 05 02 37 00 00 	movdqa 0x3702(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    428e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4296:	48 89 de             	mov    %rbx,%rsi
    4299:	48 8d 3d 01 2e 00 00 	lea    0x2e01(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    42a0:	e8 0b e1 ff ff       	call   23b0 <strcmp@plt>
    42a5:	85 c0                	test   %eax,%eax
    42a7:	75 20                	jne    42c9 <send_headers+0x159>
    42a9:	66 0f 6f 05 cf 36 00 00 	movdqa 0x36cf(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    42b1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    42b9:	66 0f 6f 05 cf 36 00 00 	movdqa 0x36cf(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    42c1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    42c9:	48 89 de             	mov    %rbx,%rsi
    42cc:	48 8d 3d d3 2d 00 00 	lea    0x2dd3(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    42d3:	e8 d8 e0 ff ff       	call   23b0 <strcmp@plt>
    42d8:	85 c0                	test   %eax,%eax
    42da:	0f 84 10 02 00 00    	je     44f0 <send_headers+0x380>
    42e0:	48 89 de             	mov    %rbx,%rsi
    42e3:	48 8d 3d c0 2d 00 00 	lea    0x2dc0(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    42ea:	e8 c1 e0 ff ff       	call   23b0 <strcmp@plt>
    42ef:	85 c0                	test   %eax,%eax
    42f1:	0f 84 a9 02 00 00    	je     45a0 <send_headers+0x430>
    42f7:	48 89 de             	mov    %rbx,%rsi
    42fa:	48 8d 3d ad 2d 00 00 	lea    0x2dad(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4301:	e8 aa e0 ff ff       	call   23b0 <strcmp@plt>
    4306:	85 c0                	test   %eax,%eax
    4308:	0f 84 6a 02 00 00    	je     4578 <send_headers+0x408>
    430e:	48 89 de             	mov    %rbx,%rsi
    4311:	48 8d 3d d9 2d 00 00 	lea    0x2dd9(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4318:	e8 93 e0 ff ff       	call   23b0 <strcmp@plt>
    431d:	85 c0                	test   %eax,%eax
    431f:	0f 84 2b 02 00 00    	je     4550 <send_headers+0x3e0>
    4325:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4328:	0f 84 52 01 00 00    	je     4480 <send_headers+0x310>
    432e:	48 89 de             	mov    %rbx,%rsi
    4331:	48 8d 3d 7a 2d 00 00 	lea    0x2d7a(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    4338:	e8 73 e0 ff ff       	call   23b0 <strcmp@plt>
    433d:	85 c0                	test   %eax,%eax
    433f:	0f 84 ab 02 00 00    	je     45f0 <send_headers+0x480>
    4345:	48 89 de             	mov    %rbx,%rsi
    4348:	48 8d 3d 67 2d 00 00 	lea    0x2d67(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    434f:	e8 5c e0 ff ff       	call   23b0 <strcmp@plt>
    4354:	85 c0                	test   %eax,%eax
    4356:	0f 84 6c 02 00 00    	je     45c8 <send_headers+0x458>
    435c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4364:	4c 89 e7             	mov    %r12,%rdi
    4367:	e8 b4 df ff ff       	call   2320 <strlen@plt>
    436c:	48 89 c7             	mov    %rax,%rdi
    436f:	48 89 c3             	mov    %rax,%rbx
    4372:	e8 99 e0 ff ff       	call   2410 <malloc@plt>
    4377:	48 85 c0             	test   %rax,%rax
    437a:	0f 84 eb 02 00 00    	je     466b <send_headers+0x4fb>
    4380:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4384:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    4388:	83 fb 08             	cmp    $0x8,%ebx
    438b:	0f 83 3f 01 00 00    	jae    44d0 <send_headers+0x360>
    4391:	f6 c3 04             	test   $0x4,%bl
    4394:	0f 85 7b 02 00 00    	jne    4615 <send_headers+0x4a5>
    439a:	85 db                	test   %ebx,%ebx
    439c:	74 13                	je     43b1 <send_headers+0x241>
    439e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    43a6:	88 10                	mov    %dl,(%rax)
    43a8:	f6 c3 02             	test   $0x2,%bl
    43ab:	0f 85 96 02 00 00    	jne    4647 <send_headers+0x4d7>
    43b1:	4d 89 e8             	mov    %r13,%r8
    43b4:	48 8d 0d ff 2c 00 00 	lea    0x2cff(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    43bb:	4c 89 e7             	mov    %r12,%rdi
    43be:	31 c0                	xor    %eax,%eax
    43c0:	ba 00 04 00 00       	mov    $0x400,%edx
    43c5:	be 01 00 00 00       	mov    $0x1,%esi
    43ca:	e8 51 e1 ff ff       	call   2520 <__sprintf_chk@plt>
    43cf:	4c 89 e7             	mov    %r12,%rdi
    43d2:	e8 49 df ff ff       	call   2320 <strlen@plt>
    43d7:	48 89 c7             	mov    %rax,%rdi
    43da:	48 89 c3             	mov    %rax,%rbx
    43dd:	e8 2e e0 ff ff       	call   2410 <malloc@plt>
    43e2:	48 85 c0             	test   %rax,%rax
    43e5:	0f 84 80 02 00 00    	je     466b <send_headers+0x4fb>
    43eb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    43ef:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    43f3:	83 fb 08             	cmp    $0x8,%ebx
    43f6:	0f 83 1c 01 00 00    	jae    4518 <send_headers+0x3a8>
    43fc:	f6 c3 04             	test   $0x4,%bl
    43ff:	0f 85 29 02 00 00    	jne    462e <send_headers+0x4be>
    4405:	85 db                	test   %ebx,%ebx
    4407:	74 13                	je     441c <send_headers+0x2ac>
    4409:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4411:	88 10                	mov    %dl,(%rax)
    4413:	f6 c3 02             	test   $0x2,%bl
    4416:	0f 85 3d 02 00 00    	jne    4659 <send_headers+0x4e9>
    441c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    4421:	bf 02 00 00 00       	mov    $0x2,%edi
    4426:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    442e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4436:	e8 d5 df ff ff       	call   2410 <malloc@plt>
    443b:	48 85 c0             	test   %rax,%rax
    443e:	0f 84 27 02 00 00    	je     466b <send_headers+0x4fb>
    4444:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    444c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    4450:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4458:	66 89 10             	mov    %dx,(%rax)
    445b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4463:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    446c:	0f 85 20 02 00 00    	jne    4692 <send_headers+0x522>
    4472:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4479:	5b                   	pop    %rbx
    447a:	5d                   	pop    %rbp
    447b:	41 5c                	pop    %r12
    447d:	41 5d                	pop    %r13
    447f:	c3                   	ret
    4480:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4484:	0f 85 a4 fe ff ff    	jne    432e <send_headers+0x1be>
    448a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    448e:	0f 85 9a fe ff ff    	jne    432e <send_headers+0x1be>
    4494:	66 0f 6f 05 44 35 00 00 	movdqa 0x3544(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    449c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    44a6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44ae:	66 0f 6f 05 3a 35 00 00 	movdqa 0x353a(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    44b6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    44be:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    44c6:	e9 63 fe ff ff       	jmp    432e <send_headers+0x1be>
    44cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    44d0:	89 da                	mov    %ebx,%edx
    44d2:	48 89 c7             	mov    %rax,%rdi
    44d5:	4c 89 e6             	mov    %r12,%rsi
    44d8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    44dd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    44e2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    44e5:	c1 e9 03             	shr    $0x3,%ecx
    44e8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    44eb:	e9 c1 fe ff ff       	jmp    43b1 <send_headers+0x241>
    44f0:	66 0f 6f 05 88 34 00 00 	movdqa 0x3488(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    44f8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4500:	66 0f 6f 05 98 34 00 00 	movdqa 0x3498(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4508:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4510:	e9 cb fd ff ff       	jmp    42e0 <send_headers+0x170>
    4515:	0f 1f 00             	nopl   (%rax)
    4518:	89 da                	mov    %ebx,%edx
    451a:	48 89 c7             	mov    %rax,%rdi
    451d:	4c 89 e6             	mov    %r12,%rsi
    4520:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4525:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    452a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    452d:	c1 e9 03             	shr    $0x3,%ecx
    4530:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4533:	e9 e4 fe ff ff       	jmp    441c <send_headers+0x2ac>
    4538:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4540:	48 8d 1d 88 2b 00 00 	lea    0x2b88(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4547:	e9 94 fd ff ff       	jmp    42e0 <send_headers+0x170>
    454c:	0f 1f 40 00          	nopl   0x0(%rax)
    4550:	66 0f 6f 05 68 34 00 00 	movdqa 0x3468(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4558:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4560:	66 0f 6f 05 68 34 00 00 	movdqa 0x3468(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4568:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4570:	e9 b0 fd ff ff       	jmp    4325 <send_headers+0x1b5>
    4575:	0f 1f 00             	nopl   (%rax)
    4578:	66 0f 6f 05 40 34 00 00 	movdqa 0x3440(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4580:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4588:	66 0f 6f 05 40 34 00 00 	movdqa 0x3440(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4590:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4598:	e9 71 fd ff ff       	jmp    430e <send_headers+0x19e>
    459d:	0f 1f 00             	nopl   (%rax)
    45a0:	66 0f 6f 05 d8 33 00 00 	movdqa 0x33d8(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    45a8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    45b0:	66 0f 6f 05 f8 33 00 00 	movdqa 0x33f8(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    45b8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    45c0:	e9 32 fd ff ff       	jmp    42f7 <send_headers+0x187>
    45c5:	0f 1f 00             	nopl   (%rax)
    45c8:	66 0f 6f 05 f0 33 00 00 	movdqa 0x33f0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    45d0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    45d8:	66 0f 6f 05 30 34 00 00 	movdqa 0x3430(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    45e0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    45e8:	e9 6f fd ff ff       	jmp    435c <send_headers+0x1ec>
    45ed:	0f 1f 00             	nopl   (%rax)
    45f0:	66 0f 6f 05 c8 33 00 00 	movdqa 0x33c8(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    45f8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4600:	66 0f 6f 05 f8 33 00 00 	movdqa 0x33f8(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4608:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4610:	e9 30 fd ff ff       	jmp    4345 <send_headers+0x1d5>
    4615:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    461c:	89 db                	mov    %ebx,%ebx
    461e:	89 10                	mov    %edx,(%rax)
    4620:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4625:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4629:	e9 83 fd ff ff       	jmp    43b1 <send_headers+0x241>
    462e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4635:	89 db                	mov    %ebx,%ebx
    4637:	89 10                	mov    %edx,(%rax)
    4639:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    463e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4642:	e9 d5 fd ff ff       	jmp    441c <send_headers+0x2ac>
    4647:	89 db                	mov    %ebx,%ebx
    4649:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    464f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4654:	e9 58 fd ff ff       	jmp    43b1 <send_headers+0x241>
    4659:	89 db                	mov    %ebx,%ebx
    465b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4661:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4666:	e9 b1 fd ff ff       	jmp    441c <send_headers+0x2ac>
    466b:	48 8b 0d ae 59 00 00 	mov    0x59ae(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4672:	ba 28 00 00 00       	mov    $0x28,%edx
    4677:	be 01 00 00 00       	mov    $0x1,%esi
    467c:	48 8d 3d 85 2d 00 00 	lea    0x2d85(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4683:	e8 38 de ff ff       	call   24c0 <fwrite@plt>
    4688:	bf 01 00 00 00       	mov    $0x1,%edi
    468d:	e8 0e de ff ff       	call   24a0 <exit@plt>
    4692:	e8 99 dc ff ff       	call   2330 <__stack_chk_fail@plt>
    4697:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000046a0 <copy_file_contents>:
    46a0:	f3 0f 1e fa          	endbr64
    46a4:	41 55                	push   %r13
    46a6:	49 89 d5             	mov    %rdx,%r13
    46a9:	41 54                	push   %r12
    46ab:	49 89 fc             	mov    %rdi,%r12
    46ae:	48 89 f7             	mov    %rsi,%rdi
    46b1:	55                   	push   %rbp
    46b2:	53                   	push   %rbx
    46b3:	48 89 f3             	mov    %rsi,%rbx
    46b6:	48 83 ec 08          	sub    $0x8,%rsp
    46ba:	e8 51 dd ff ff       	call   2410 <malloc@plt>
    46bf:	48 85 c0             	test   %rax,%rax
    46c2:	74 6b                	je     472f <copy_file_contents+0x8f>
    46c4:	4c 89 e7             	mov    %r12,%rdi
    46c7:	48 89 c5             	mov    %rax,%rbp
    46ca:	31 f6                	xor    %esi,%esi
    46cc:	31 c0                	xor    %eax,%eax
    46ce:	e8 ad dd ff ff       	call   2480 <open@plt>
    46d3:	41 89 c4             	mov    %eax,%r12d
    46d6:	85 c0                	test   %eax,%eax
    46d8:	0f 88 78 de ff ff    	js     2556 <copy_file_contents.cold>
    46de:	48 89 da             	mov    %rbx,%rdx
    46e1:	48 89 ee             	mov    %rbp,%rsi
    46e4:	89 c7                	mov    %eax,%edi
    46e6:	e8 a5 dc ff ff       	call   2390 <read@plt>
    46eb:	48 98                	cltq
    46ed:	48 39 d8             	cmp    %rbx,%rax
    46f0:	7c 1e                	jl     4710 <copy_file_contents+0x70>
    46f2:	44 89 e7             	mov    %r12d,%edi
    46f5:	e8 76 dc ff ff       	call   2370 <close@plt>
    46fa:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    46fe:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    4702:	48 83 c4 08          	add    $0x8,%rsp
    4706:	5b                   	pop    %rbx
    4707:	5d                   	pop    %rbp
    4708:	41 5c                	pop    %r12
    470a:	41 5d                	pop    %r13
    470c:	c3                   	ret
    470d:	0f 1f 00             	nopl   (%rax)
    4710:	48 8b 0d 09 59 00 00 	mov    0x5909(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4717:	ba 1a 00 00 00       	mov    $0x1a,%edx
    471c:	be 01 00 00 00       	mov    $0x1,%esi
    4721:	48 8d 3d a8 29 00 00 	lea    0x29a8(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    4728:	e8 93 dd ff ff       	call   24c0 <fwrite@plt>
    472d:	eb c3                	jmp    46f2 <copy_file_contents+0x52>
    472f:	48 8b 0d ea 58 00 00 	mov    0x58ea(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4736:	ba 28 00 00 00       	mov    $0x28,%edx
    473b:	be 01 00 00 00       	mov    $0x1,%esi
    4740:	48 8d 3d c1 2c 00 00 	lea    0x2cc1(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4747:	e8 74 dd ff ff       	call   24c0 <fwrite@plt>
    474c:	bf 01 00 00 00       	mov    $0x1,%edi
    4751:	e8 4a dd ff ff       	call   24a0 <exit@plt>
    4756:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004760 <add_write_request>:
    4760:	f3 0f 1e fa          	endbr64
    4764:	8b 46 44             	mov    0x44(%rsi),%eax
    4767:	48 89 fa             	mov    %rdi,%rdx
    476a:	48 89 f7             	mov    %rsi,%rdi
    476d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    4773:	8d 70 01             	lea    0x1(%rax),%esi
    4776:	48 8b 07             	mov    (%rdi),%rax
    4779:	44 8b 00             	mov    (%rax),%r8d
    477c:	f6 c1 02             	test   $0x2,%cl
    477f:	74 00                	je     4781 <add_write_request+0x21>
    4781:	89 f0                	mov    %esi,%eax
    4783:	44 29 c0             	sub    %r8d,%eax
    4786:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4789:	0f 82 d3 dd ff ff    	jb     2562 <add_write_request.cold>
    478f:	c1 e9 0a             	shr    $0xa,%ecx
    4792:	48 83 ec 08          	sub    $0x8,%rsp
    4796:	8b 47 44             	mov    0x44(%rdi),%eax
    4799:	23 47 58             	and    0x58(%rdi),%eax
    479c:	83 e1 01             	and    $0x1,%ecx
    479f:	89 77 44             	mov    %esi,0x44(%rdi)
    47a2:	8b 72 08             	mov    0x8(%rdx),%esi
    47a5:	66 0f ef c0          	pxor   %xmm0,%xmm0
    47a9:	d3 e0                	shl    %cl,%eax
    47ab:	8b 4a 04             	mov    0x4(%rdx),%ecx
    47ae:	48 c1 e0 06          	shl    $0x6,%rax
    47b2:	48 03 47 38          	add    0x38(%rdi),%rax
    47b6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    47bc:	89 70 04             	mov    %esi,0x4(%rax)
    47bf:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    47c3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    47c9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    47d1:	48 89 70 10          	mov    %rsi,0x10(%rax)
    47d5:	89 48 18             	mov    %ecx,0x18(%rax)
    47d8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    47df:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    47e7:	48 89 50 20          	mov    %rdx,0x20(%rax)
    47eb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    47ef:	e8 4c db ff ff       	call   2340 <io_uring_submit@plt>
    47f4:	31 c0                	xor    %eax,%eax
    47f6:	48 83 c4 08          	add    $0x8,%rsp
    47fa:	c3                   	ret
    47fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004800 <add_read_request>:
    4800:	f3 0f 1e fa          	endbr64
    4804:	41 55                	push   %r13
    4806:	41 89 fd             	mov    %edi,%r13d
    4809:	41 54                	push   %r12
    480b:	55                   	push   %rbp
    480c:	53                   	push   %rbx
    480d:	48 89 f3             	mov    %rsi,%rbx
    4810:	48 83 ec 08          	sub    $0x8,%rsp
    4814:	8b 46 44             	mov    0x44(%rsi),%eax
    4817:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    481d:	48 8b 16             	mov    (%rsi),%rdx
    4820:	83 c0 01             	add    $0x1,%eax
    4823:	8b 32                	mov    (%rdx),%esi
    4825:	f6 c1 02             	test   $0x2,%cl
    4828:	74 00                	je     482a <add_read_request+0x2a>
    482a:	89 c2                	mov    %eax,%edx
    482c:	29 f2                	sub    %esi,%edx
    482e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4831:	0f 82 3b dd ff ff    	jb     2572 <add_read_request.cold>
    4837:	8b 6b 44             	mov    0x44(%rbx),%ebp
    483a:	c1 e9 0a             	shr    $0xa,%ecx
    483d:	89 43 44             	mov    %eax,0x44(%rbx)
    4840:	bf 20 00 00 00       	mov    $0x20,%edi
    4845:	83 e1 01             	and    $0x1,%ecx
    4848:	23 6b 58             	and    0x58(%rbx),%ebp
    484b:	d3 e5                	shl    %cl,%ebp
    484d:	48 c1 e5 06          	shl    $0x6,%rbp
    4851:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4855:	e8 b6 db ff ff       	call   2410 <malloc@plt>
    485a:	be 01 00 00 00       	mov    $0x1,%esi
    485f:	bf 00 20 00 00       	mov    $0x2000,%edi
    4864:	49 89 c4             	mov    %rax,%r12
    4867:	e8 34 db ff ff       	call   23a0 <calloc@plt>
    486c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    4871:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4875:	48 89 df             	mov    %rbx,%rdi
    4878:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    487d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    4882:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    488b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    4893:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    4897:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    489b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    48a2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    48aa:	48 89 45 10          	mov    %rax,0x10(%rbp)
    48ae:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    48b6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    48be:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    48c2:	e8 79 da ff ff       	call   2340 <io_uring_submit@plt>
    48c7:	48 83 c4 08          	add    $0x8,%rsp
    48cb:	31 c0                	xor    %eax,%eax
    48cd:	5b                   	pop    %rbx
    48ce:	5d                   	pop    %rbp
    48cf:	41 5c                	pop    %r12
    48d1:	41 5d                	pop    %r13
    48d3:	c3                   	ret
    48d4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    48df:	90                   	nop

00000000000048e0 <_send_static_string_content>:
    48e0:	f3 0f 1e fa          	endbr64
    48e4:	41 56                	push   %r14
    48e6:	41 89 f6             	mov    %esi,%r14d
    48e9:	41 55                	push   %r13
    48eb:	49 89 fd             	mov    %rdi,%r13
    48ee:	bf 20 00 00 00       	mov    $0x20,%edi
    48f3:	41 54                	push   %r12
    48f5:	55                   	push   %rbp
    48f6:	48 89 d5             	mov    %rdx,%rbp
    48f9:	53                   	push   %rbx
    48fa:	e8 11 db ff ff       	call   2410 <malloc@plt>
    48ff:	48 85 c0             	test   %rax,%rax
    4902:	0f 84 dd 00 00 00    	je     49e5 <_send_static_string_content+0x105>
    4908:	48 89 c3             	mov    %rax,%rbx
    490b:	4c 89 ef             	mov    %r13,%rdi
    490e:	e8 0d da ff ff       	call   2320 <strlen@plt>
    4913:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    491a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    491e:	48 89 c7             	mov    %rax,%rdi
    4921:	49 89 c4             	mov    %rax,%r12
    4924:	e8 e7 da ff ff       	call   2410 <malloc@plt>
    4929:	48 89 c7             	mov    %rax,%rdi
    492c:	48 85 c0             	test   %rax,%rax
    492f:	0f 84 b0 00 00 00    	je     49e5 <_send_static_string_content+0x105>
    4935:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4939:	4c 89 e2             	mov    %r12,%rdx
    493c:	4c 89 ee             	mov    %r13,%rsi
    493f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4943:	e8 98 da ff ff       	call   23e0 <memcpy@plt>
    4948:	8b 45 44             	mov    0x44(%rbp),%eax
    494b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    4951:	8d 50 01             	lea    0x1(%rax),%edx
    4954:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4958:	8b 30                	mov    (%rax),%esi
    495a:	f6 c1 02             	test   $0x2,%cl
    495d:	0f 85 7d 00 00 00    	jne    49e0 <_send_static_string_content+0x100>
    4963:	89 d0                	mov    %edx,%eax
    4965:	29 f0                	sub    %esi,%eax
    4967:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    496a:	0f 82 0c dc ff ff    	jb     257c <_send_static_string_content.cold>
    4970:	c1 e9 0a             	shr    $0xa,%ecx
    4973:	8b 45 44             	mov    0x44(%rbp),%eax
    4976:	23 45 58             	and    0x58(%rbp),%eax
    4979:	89 55 44             	mov    %edx,0x44(%rbp)
    497c:	83 e1 01             	and    $0x1,%ecx
    497f:	8b 53 04             	mov    0x4(%rbx),%edx
    4982:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    4988:	66 0f ef c0          	pxor   %xmm0,%xmm0
    498c:	d3 e0                	shl    %cl,%eax
    498e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    4991:	48 89 ef             	mov    %rbp,%rdi
    4994:	48 c1 e0 06          	shl    $0x6,%rax
    4998:	48 03 45 38          	add    0x38(%rbp),%rax
    499c:	89 48 04             	mov    %ecx,0x4(%rax)
    499f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    49a3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    49a9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    49b1:	48 89 48 10          	mov    %rcx,0x10(%rax)
    49b5:	89 50 18             	mov    %edx,0x18(%rax)
    49b8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    49bf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    49c7:	48 89 58 20          	mov    %rbx,0x20(%rax)
    49cb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    49cf:	5b                   	pop    %rbx
    49d0:	5d                   	pop    %rbp
    49d1:	41 5c                	pop    %r12
    49d3:	41 5d                	pop    %r13
    49d5:	41 5e                	pop    %r14
    49d7:	e9 64 d9 ff ff       	jmp    2340 <io_uring_submit@plt>
    49dc:	0f 1f 40 00          	nopl   0x0(%rax)
    49e0:	e9 7e ff ff ff       	jmp    4963 <_send_static_string_content+0x83>
    49e5:	48 8b 0d 34 56 00 00 	mov    0x5634(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    49ec:	ba 28 00 00 00       	mov    $0x28,%edx
    49f1:	be 01 00 00 00       	mov    $0x1,%esi
    49f6:	48 8d 3d 0b 2a 00 00 	lea    0x2a0b(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    49fd:	e8 be da ff ff       	call   24c0 <fwrite@plt>
    4a02:	bf 01 00 00 00       	mov    $0x1,%edi
    4a07:	e8 94 da ff ff       	call   24a0 <exit@plt>
    4a0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a10 <handle_unimplemented_method>:
    4a10:	f3 0f 1e fa          	endbr64
    4a14:	48 89 f2             	mov    %rsi,%rdx
    4a17:	89 fe                	mov    %edi,%esi
    4a19:	48 8b 3d f8 55 00 00 	mov    0x55f8(%rip),%rdi        # a018 <unimplemented_content>
    4a20:	e9 bb fe ff ff       	jmp    48e0 <_send_static_string_content>
    4a25:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004a30 <handle_http_404>:
    4a30:	f3 0f 1e fa          	endbr64
    4a34:	48 89 f2             	mov    %rsi,%rdx
    4a37:	89 fe                	mov    %edi,%esi
    4a39:	48 8b 3d d0 55 00 00 	mov    0x55d0(%rip),%rdi        # a010 <http_404_content>
    4a40:	e9 9b fe ff ff       	jmp    48e0 <_send_static_string_content>
    4a45:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004a50 <handle_get_method>:
    4a50:	f3 0f 1e fa          	endbr64
    4a54:	41 56                	push   %r14
    4a56:	41 55                	push   %r13
    4a58:	49 89 d5             	mov    %rdx,%r13
    4a5b:	41 54                	push   %r12
    4a5d:	41 89 f4             	mov    %esi,%r12d
    4a60:	55                   	push   %rbp
    4a61:	48 89 fd             	mov    %rdi,%rbp
    4a64:	53                   	push   %rbx
    4a65:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    4a6c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a75:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    4a7d:	31 c0                	xor    %eax,%eax
    4a7f:	e8 9c d8 ff ff       	call   2320 <strlen@plt>
    4a84:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4a89:	48 89 c3             	mov    %rax,%rbx
    4a8c:	0f 84 b6 00 00 00    	je     4b48 <handle_get_method+0xf8>
    4a92:	b8 69 63 00 00       	mov    $0x6369,%eax
    4a97:	48 89 ee             	mov    %rbp,%rsi
    4a9a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    4a9e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4aa3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4aab:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4ab3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4abe:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    4ac6:	e8 f5 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    4acb:	48 89 e6             	mov    %rsp,%rsi
    4ace:	4c 89 f7             	mov    %r14,%rdi
    4ad1:	e8 fa d8 ff ff       	call   23d0 <stat@plt>
    4ad6:	83 f8 ff             	cmp    $0xffffffff,%eax
    4ad9:	0f 84 d3 00 00 00    	je     4bb2 <handle_get_method+0x162>
    4adf:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4ae3:	25 00 f0 00 00       	and    $0xf000,%eax
    4ae8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4aed:	0f 84 f5 00 00 00    	je     4be8 <handle_get_method+0x198>
    4af3:	48 8b 3d 16 55 00 00 	mov    0x5516(%rip),%rdi        # a010 <http_404_content>
    4afa:	4c 89 ea             	mov    %r13,%rdx
    4afd:	44 89 e6             	mov    %r12d,%esi
    4b00:	e8 db fd ff ff       	call   48e0 <_send_static_string_content>
    4b05:	4c 89 f2             	mov    %r14,%rdx
    4b08:	bf 01 00 00 00       	mov    $0x1,%edi
    4b0d:	31 c0                	xor    %eax,%eax
    4b0f:	48 8d 35 0a 26 00 00 	lea    0x260a(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    4b16:	e8 35 d9 ff ff       	call   2450 <__printf_chk@plt>
    4b1b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4b23:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b2c:	0f 85 20 01 00 00    	jne    4c52 <handle_get_method+0x202>
    4b32:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4b39:	5b                   	pop    %rbx
    4b3a:	5d                   	pop    %rbp
    4b3b:	41 5c                	pop    %r12
    4b3d:	41 5d                	pop    %r13
    4b3f:	41 5e                	pop    %r14
    4b41:	c3                   	ret
    4b42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b48:	ba 69 63 00 00       	mov    $0x6369,%edx
    4b4d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4b55:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4b5a:	48 89 ee             	mov    %rbp,%rsi
    4b5d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    4b65:	48 89 c2             	mov    %rax,%rdx
    4b68:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4b70:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4b7b:	e8 40 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    4b80:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4b85:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4b8a:	48 8d 35 5a 25 00 00 	lea    0x255a(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4b91:	48 29 d9             	sub    %rbx,%rcx
    4b94:	ba 0b 00 00 00       	mov    $0xb,%edx
    4b99:	e8 22 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    4b9e:	48 89 e6             	mov    %rsp,%rsi
    4ba1:	4c 89 f7             	mov    %r14,%rdi
    4ba4:	e8 27 d8 ff ff       	call   23d0 <stat@plt>
    4ba9:	83 f8 ff             	cmp    $0xffffffff,%eax
    4bac:	0f 85 2d ff ff ff    	jne    4adf <handle_get_method+0x8f>
    4bb2:	4c 89 f2             	mov    %r14,%rdx
    4bb5:	48 89 e9             	mov    %rbp,%rcx
    4bb8:	48 8d 35 37 25 00 00 	lea    0x2537(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    4bbf:	31 c0                	xor    %eax,%eax
    4bc1:	bf 01 00 00 00       	mov    $0x1,%edi
    4bc6:	e8 85 d8 ff ff       	call   2450 <__printf_chk@plt>
    4bcb:	48 8b 3d 3e 54 00 00 	mov    0x543e(%rip),%rdi        # a010 <http_404_content>
    4bd2:	4c 89 ea             	mov    %r13,%rdx
    4bd5:	44 89 e6             	mov    %r12d,%esi
    4bd8:	e8 03 fd ff ff       	call   48e0 <_send_static_string_content>
    4bdd:	e9 39 ff ff ff       	jmp    4b1b <handle_get_method+0xcb>
    4be2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4be8:	bf 70 00 00 00       	mov    $0x70,%edi
    4bed:	e8 1e d8 ff ff       	call   2410 <malloc@plt>
    4bf2:	48 89 c3             	mov    %rax,%rbx
    4bf5:	48 85 c0             	test   %rax,%rax
    4bf8:	74 5d                	je     4c57 <handle_get_method+0x207>
    4bfa:	44 89 60 08          	mov    %r12d,0x8(%rax)
    4bfe:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4c03:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4c07:	4c 89 f7             	mov    %r14,%rdi
    4c0a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    4c11:	e8 5a f5 ff ff       	call   4170 <send_headers>
    4c16:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4c1b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4c1f:	4c 89 f7             	mov    %r14,%rdi
    4c22:	e8 79 fa ff ff       	call   46a0 <copy_file_contents>
    4c27:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4c2c:	4c 89 f2             	mov    %r14,%rdx
    4c2f:	31 c0                	xor    %eax,%eax
    4c31:	48 8d 35 d6 24 00 00 	lea    0x24d6(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4c38:	bf 01 00 00 00       	mov    $0x1,%edi
    4c3d:	e8 0e d8 ff ff       	call   2450 <__printf_chk@plt>
    4c42:	4c 89 ee             	mov    %r13,%rsi
    4c45:	48 89 df             	mov    %rbx,%rdi
    4c48:	e8 13 fb ff ff       	call   4760 <add_write_request>
    4c4d:	e9 c9 fe ff ff       	jmp    4b1b <handle_get_method+0xcb>
    4c52:	e8 d9 d6 ff ff       	call   2330 <__stack_chk_fail@plt>
    4c57:	48 8b 0d c2 53 00 00 	mov    0x53c2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4c5e:	ba 28 00 00 00       	mov    $0x28,%edx
    4c63:	be 01 00 00 00       	mov    $0x1,%esi
    4c68:	48 8d 3d 99 27 00 00 	lea    0x2799(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4c6f:	e8 4c d8 ff ff       	call   24c0 <fwrite@plt>
    4c74:	bf 01 00 00 00       	mov    $0x1,%edi
    4c79:	e8 22 d8 ff ff       	call   24a0 <exit@plt>
    4c7e:	66 90                	xchg   %ax,%ax

0000000000004c80 <handle_http_method>:
    4c80:	f3 0f 1e fa          	endbr64
    4c84:	41 57                	push   %r15
    4c86:	41 56                	push   %r14
    4c88:	4c 8d 35 f6 23 00 00 	lea    0x23f6(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
    4c8f:	41 55                	push   %r13
    4c91:	49 89 d5             	mov    %rdx,%r13
    4c94:	41 54                	push   %r12
    4c96:	41 89 f4             	mov    %esi,%r12d
    4c99:	4c 89 f6             	mov    %r14,%rsi
    4c9c:	55                   	push   %rbp
    4c9d:	53                   	push   %rbx
    4c9e:	48 83 ec 18          	sub    $0x18,%rsp
    4ca2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4cab:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4cb0:	31 c0                	xor    %eax,%eax
    4cb2:	49 89 e7             	mov    %rsp,%r15
    4cb5:	4c 89 fa             	mov    %r15,%rdx
    4cb8:	e8 c3 d6 ff ff       	call   2380 <strtok_r@plt>
    4cbd:	48 0f be 18          	movsbq (%rax),%rbx
    4cc1:	48 89 c5             	mov    %rax,%rbp
    4cc4:	84 db                	test   %bl,%bl
    4cc6:	74 1d                	je     4ce5 <handle_http_method+0x65>
    4cc8:	e8 43 d8 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4ccd:	48 89 ea             	mov    %rbp,%rdx
    4cd0:	48 8b 08             	mov    (%rax),%rcx
    4cd3:	48 83 c2 01          	add    $0x1,%rdx
    4cd7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4cda:	88 4a ff             	mov    %cl,-0x1(%rdx)
    4cdd:	48 0f be 1a          	movsbq (%rdx),%rbx
    4ce1:	84 db                	test   %bl,%bl
    4ce3:	75 eb                	jne    4cd0 <handle_http_method+0x50>
    4ce5:	4c 89 fa             	mov    %r15,%rdx
    4ce8:	4c 89 f6             	mov    %r14,%rsi
    4ceb:	31 ff                	xor    %edi,%edi
    4ced:	e8 8e d6 ff ff       	call   2380 <strtok_r@plt>
    4cf2:	48 8d 35 3a 24 00 00 	lea    0x243a(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4cf9:	48 89 ef             	mov    %rbp,%rdi
    4cfc:	48 89 c3             	mov    %rax,%rbx
    4cff:	e8 ac d6 ff ff       	call   23b0 <strcmp@plt>
    4d04:	4c 89 ea             	mov    %r13,%rdx
    4d07:	44 89 e6             	mov    %r12d,%esi
    4d0a:	85 c0                	test   %eax,%eax
    4d0c:	75 2a                	jne    4d38 <handle_http_method+0xb8>
    4d0e:	48 89 df             	mov    %rbx,%rdi
    4d11:	e8 3a fd ff ff       	call   4a50 <handle_get_method>
    4d16:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4d1b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d24:	75 20                	jne    4d46 <handle_http_method+0xc6>
    4d26:	48 83 c4 18          	add    $0x18,%rsp
    4d2a:	5b                   	pop    %rbx
    4d2b:	5d                   	pop    %rbp
    4d2c:	41 5c                	pop    %r12
    4d2e:	41 5d                	pop    %r13
    4d30:	41 5e                	pop    %r14
    4d32:	41 5f                	pop    %r15
    4d34:	c3                   	ret
    4d35:	0f 1f 00             	nopl   (%rax)
    4d38:	48 8b 3d d9 52 00 00 	mov    0x52d9(%rip),%rdi        # a018 <unimplemented_content>
    4d3f:	e8 9c fb ff ff       	call   48e0 <_send_static_string_content>
    4d44:	eb d0                	jmp    4d16 <handle_http_method+0x96>
    4d46:	e8 e5 d5 ff ff       	call   2330 <__stack_chk_fail@plt>
    4d4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004d50 <get_line>:
    4d50:	f3 0f 1e fa          	endbr64
    4d54:	85 d2                	test   %edx,%edx
    4d56:	7e 38                	jle    4d90 <get_line+0x40>
    4d58:	48 63 d2             	movslq %edx,%rdx
    4d5b:	48 83 c7 01          	add    $0x1,%rdi
    4d5f:	48 01 f2             	add    %rsi,%rdx
    4d62:	eb 11                	jmp    4d75 <get_line+0x25>
    4d64:	0f 1f 40 00          	nopl   0x0(%rax)
    4d68:	48 83 c6 01          	add    $0x1,%rsi
    4d6c:	48 83 c7 01          	add    $0x1,%rdi
    4d70:	48 39 d6             	cmp    %rdx,%rsi
    4d73:	74 1b                	je     4d90 <get_line+0x40>
    4d75:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4d79:	88 06                	mov    %al,(%rsi)
    4d7b:	3c 0d                	cmp    $0xd,%al
    4d7d:	75 e9                	jne    4d68 <get_line+0x18>
    4d7f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4d82:	75 e4                	jne    4d68 <get_line+0x18>
    4d84:	c6 06 00             	movb   $0x0,(%rsi)
    4d87:	31 c0                	xor    %eax,%eax
    4d89:	c3                   	ret
    4d8a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4d90:	b8 01 00 00 00       	mov    $0x1,%eax
    4d95:	c3                   	ret
    4d96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004da0 <handle_client_request>:
    4da0:	f3 0f 1e fa          	endbr64
    4da4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4dab:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4daf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4db8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4dc0:	31 c0                	xor    %eax,%eax
    4dc2:	49 89 e2             	mov    %rsp,%r10
    4dc5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4dcd:	4c 89 d0             	mov    %r10,%rax
    4dd0:	eb 13                	jmp    4de5 <handle_client_request+0x45>
    4dd2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4dd8:	48 83 c0 01          	add    $0x1,%rax
    4ddc:	48 83 c1 01          	add    $0x1,%rcx
    4de0:	4c 39 c8             	cmp    %r9,%rax
    4de3:	74 4b                	je     4e30 <handle_client_request+0x90>
    4de5:	44 0f b6 01          	movzbl (%rcx),%r8d
    4de9:	44 88 00             	mov    %r8b,(%rax)
    4dec:	41 80 f8 0d          	cmp    $0xd,%r8b
    4df0:	75 e6                	jne    4dd8 <handle_client_request+0x38>
    4df2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4df6:	75 e0                	jne    4dd8 <handle_client_request+0x38>
    4df8:	c6 00 00             	movb   $0x0,(%rax)
    4dfb:	8b 47 08             	mov    0x8(%rdi),%eax
    4dfe:	48 89 f2             	mov    %rsi,%rdx
    4e01:	4c 89 d7             	mov    %r10,%rdi
    4e04:	89 c6                	mov    %eax,%esi
    4e06:	e8 75 fe ff ff       	call   4c80 <handle_http_method>
    4e0b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4e13:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4e1c:	75 39                	jne    4e57 <handle_client_request+0xb7>
    4e1e:	31 c0                	xor    %eax,%eax
    4e20:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4e27:	c3                   	ret
    4e28:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4e30:	48 8b 0d e9 51 00 00 	mov    0x51e9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4e37:	ba 12 00 00 00       	mov    $0x12,%edx
    4e3c:	be 01 00 00 00       	mov    $0x1,%esi
    4e41:	48 8d 3d ef 22 00 00 	lea    0x22ef(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4e48:	e8 73 d6 ff ff       	call   24c0 <fwrite@plt>
    4e4d:	bf 01 00 00 00       	mov    $0x1,%edi
    4e52:	e8 49 d6 ff ff       	call   24a0 <exit@plt>
    4e57:	e8 d4 d4 ff ff       	call   2330 <__stack_chk_fail@plt>
    4e5c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004e60 <add_accept_request>:
    4e60:	f3 0f 1e fa          	endbr64
    4e64:	55                   	push   %rbp
    4e65:	53                   	push   %rbx
    4e66:	48 89 cb             	mov    %rcx,%rbx
    4e69:	48 83 ec 08          	sub    $0x8,%rsp
    4e6d:	8b 41 44             	mov    0x44(%rcx),%eax
    4e70:	4c 8b 03             	mov    (%rbx),%r8
    4e73:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    4e79:	83 c0 01             	add    $0x1,%eax
    4e7c:	45 8b 08             	mov    (%r8),%r9d
    4e7f:	f6 c1 02             	test   $0x2,%cl
    4e82:	74 00                	je     4e84 <add_accept_request+0x24>
    4e84:	41 89 c0             	mov    %eax,%r8d
    4e87:	45 29 c8             	sub    %r9d,%r8d
    4e8a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4e8e:	0f 82 f8 d6 ff ff    	jb     258c <add_accept_request.cold>
    4e94:	c1 e9 0a             	shr    $0xa,%ecx
    4e97:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4e9a:	23 6b 58             	and    0x58(%rbx),%ebp
    4e9d:	89 43 44             	mov    %eax,0x44(%rbx)
    4ea0:	83 e1 01             	and    $0x1,%ecx
    4ea3:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4ea7:	d3 e5                	shl    %cl,%ebp
    4ea9:	48 c1 e5 06          	shl    $0x6,%rbp
    4ead:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4eb1:	89 7d 04             	mov    %edi,0x4(%rbp)
    4eb4:	bf 10 00 00 00       	mov    $0x10,%edi
    4eb9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    4ec0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    4ec4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    4ec8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    4ed0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    4ed8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4edc:	e8 2f d5 ff ff       	call   2410 <malloc@plt>
    4ee1:	48 89 df             	mov    %rbx,%rdi
    4ee4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    4eea:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4eee:	48 83 c4 08          	add    $0x8,%rsp
    4ef2:	5b                   	pop    %rbx
    4ef3:	5d                   	pop    %rbp
    4ef4:	e9 47 d4 ff ff       	jmp    2340 <io_uring_submit@plt>
    4ef9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004f00 <io_thread>:
    4f00:	f3 0f 1e fa          	endbr64
    4f04:	41 57                	push   %r15
    4f06:	31 d2                	xor    %edx,%edx
    4f08:	41 56                	push   %r14
    4f0a:	41 55                	push   %r13
    4f0c:	41 54                	push   %r12
    4f0e:	55                   	push   %rbp
    4f0f:	48 89 fd             	mov    %rdi,%rbp
    4f12:	53                   	push   %rbx
    4f13:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4f1a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4f23:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4f2b:	48 8b 47 48          	mov    0x48(%rdi),%rax
    4f2f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4f34:	bf 00 01 00 00       	mov    $0x100,%edi
    4f39:	48 89 de             	mov    %rbx,%rsi
    4f3c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4f40:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4f45:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4f4a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4f4f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4f54:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4f5c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4f61:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4f69:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4f6e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4f76:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4f7b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4f83:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4f88:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4f90:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4f95:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4f9d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4fa5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4fad:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4fb5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4fbd:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4fc5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4fcd:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4fd5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4fdd:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4fe5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4fed:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4ff4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    4ffc:	e8 ef d3 ff ff       	call   23f0 <io_uring_queue_init@plt>
    5001:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
    5005:	31 f6                	xor    %esi,%esi
    5007:	e8 d4 d4 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
    500c:	31 d2                	xor    %edx,%edx
    500e:	be 01 00 00 00       	mov    $0x1,%esi
    5013:	bf 02 00 00 00       	mov    $0x2,%edi
    5018:	e8 13 d5 ff ff       	call   2530 <socket@plt>
    501d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5020:	0f 84 a8 d5 ff ff    	je     25ce <io_thread.cold+0x38>
    5026:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    502b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5031:	89 c7                	mov    %eax,%edi
    5033:	41 89 c4             	mov    %eax,%r12d
    5036:	ba 02 00 00 00       	mov    $0x2,%edx
    503b:	be 01 00 00 00       	mov    $0x1,%esi
    5040:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    5048:	e8 b3 d2 ff ff       	call   2300 <setsockopt@plt>
    504d:	85 c0                	test   %eax,%eax
    504f:	0f 88 4d d5 ff ff    	js     25a2 <io_thread.cold+0xc>
    5055:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    505a:	ba 10 00 00 00       	mov    $0x10,%edx
    505f:	44 89 e7             	mov    %r12d,%edi
    5062:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    506b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    5073:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
    507b:	e8 e0 d3 ff ff       	call   2460 <bind@plt>
    5080:	85 c0                	test   %eax,%eax
    5082:	0f 88 52 d5 ff ff    	js     25da <io_thread.cold+0x44>
    5088:	be 0a 00 00 00       	mov    $0xa,%esi
    508d:	44 89 e7             	mov    %r12d,%edi
    5090:	e8 8b d3 ff ff       	call   2420 <listen@plt>
    5095:	85 c0                	test   %eax,%eax
    5097:	0f 88 11 d5 ff ff    	js     25ae <io_thread.cold+0x18>
    509d:	ba db 18 00 00       	mov    $0x18db,%edx
    50a2:	48 8d 35 d3 20 00 00 	lea    0x20d3(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    50a9:	bf 01 00 00 00       	mov    $0x1,%edi
    50ae:	31 c0                	xor    %eax,%eax
    50b0:	e8 9b d3 ff ff       	call   2450 <__printf_chk@plt>
    50b5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    50ba:	48 89 d9             	mov    %rbx,%rcx
    50bd:	44 89 e7             	mov    %r12d,%edi
    50c0:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    50c5:	48 89 c6             	mov    %rax,%rsi
    50c8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    50cd:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    50d2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    50da:	e8 81 fd ff ff       	call   4e60 <add_accept_request>
    50df:	bf 01 00 00 00       	mov    $0x1,%edi
    50e4:	be 10 00 00 00       	mov    $0x10,%esi
    50e9:	e8 b2 d2 ff ff       	call   23a0 <calloc@plt>
    50ee:	bf 0a 00 00 00       	mov    $0xa,%edi
    50f3:	49 89 c5             	mov    %rax,%r13
    50f6:	e8 15 d3 ff ff       	call   2410 <malloc@plt>
    50fb:	48 85 c0             	test   %rax,%rax
    50fe:	0f 84 ae 04 00 00    	je     55b2 <io_thread+0x6b2>
    5104:	49 89 45 00          	mov    %rax,0x0(%r13)
    5108:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    510f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5116:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    511e:	8d 50 01             	lea    0x1(%rax),%edx
    5121:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5126:	8b 30                	mov    (%rax),%esi
    5128:	f6 c1 02             	test   $0x2,%cl
    512b:	0f 85 0f 04 00 00    	jne    5540 <io_thread+0x640>
    5131:	89 d0                	mov    %edx,%eax
    5133:	29 f0                	sub    %esi,%eax
    5135:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    513c:	0f 82 82 d4 ff ff    	jb     25c4 <io_thread.cold+0x2e>
    5142:	c1 e9 0a             	shr    $0xa,%ecx
    5145:	48 8d 75 50          	lea    0x50(%rbp),%rsi
    5149:	66 0f ef c0          	pxor   %xmm0,%xmm0
    514d:	48 89 df             	mov    %rbx,%rdi
    5150:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5157:	83 e1 01             	and    $0x1,%ecx
    515a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5161:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5168:	d3 e0                	shl    %cl,%eax
    516a:	8b 55 50             	mov    0x50(%rbp),%edx
    516d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5172:	48 c1 e0 06          	shl    $0x6,%rax
    5176:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    517e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5184:	89 50 04             	mov    %edx,0x4(%rax)
    5187:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    518f:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5193:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    519b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    51a3:	48 89 70 20          	mov    %rsi,0x20(%rax)
    51a7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    51ab:	e8 90 d1 ff ff       	call   2340 <io_uring_submit@plt>
    51b0:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    51b4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    51b9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    51c1:	0f 85 d7 01 00 00    	jne    539e <io_thread+0x49e>
    51c7:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    51cc:	4d 89 ce             	mov    %r9,%r14
    51cf:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    51d4:	0f 1f 40 00          	nopl   0x0(%rax)
    51d8:	48 8d 3d b3 1f 00 00 	lea    0x1fb3(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    51df:	e8 0c d1 ff ff       	call   22f0 <puts@plt>
    51e4:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    51eb:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    51f2:	c1 e9 0b             	shr    $0xb,%ecx
    51f5:	83 e1 01             	and    $0x1,%ecx
    51f8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5200:	8b 00                	mov    (%rax),%eax
    5202:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    520a:	8b 16                	mov    (%rsi),%edx
    520c:	39 d0                	cmp    %edx,%eax
    520e:	74 36                	je     5246 <io_thread+0x346>
    5210:	89 f8                	mov    %edi,%eax
    5212:	21 d0                	and    %edx,%eax
    5214:	d3 e0                	shl    %cl,%eax
    5216:	48 c1 e0 04          	shl    $0x4,%rax
    521a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    5222:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    522a:	0f 85 a8 01 00 00    	jne    53d8 <io_thread+0x4d8>
    5230:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5234:	0f 85 0e 03 00 00    	jne    5548 <io_thread+0x648>
    523a:	8b 40 08             	mov    0x8(%rax),%eax
    523d:	83 c2 01             	add    $0x1,%edx
    5240:	89 16                	mov    %edx,(%rsi)
    5242:	85 c0                	test   %eax,%eax
    5244:	79 b2                	jns    51f8 <io_thread+0x2f8>
    5246:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    524f:	90                   	nop
    5250:	45 31 c0             	xor    %r8d,%r8d
    5253:	31 d2                	xor    %edx,%edx
    5255:	b9 01 00 00 00       	mov    $0x1,%ecx
    525a:	4c 89 f6             	mov    %r14,%rsi
    525d:	48 89 df             	mov    %rbx,%rdi
    5260:	e8 db d1 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5265:	41 89 c7             	mov    %eax,%r15d
    5268:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    526d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5271:	0f 84 e1 02 00 00    	je     5558 <io_thread+0x658>
    5277:	48 8d 3d 3a 1f 00 00 	lea    0x1f3a(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    527e:	e8 6d d0 ff ff       	call   22f0 <puts@plt>
    5283:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5288:	4c 8b 22             	mov    (%rdx),%r12
    528b:	45 85 ff             	test   %r15d,%r15d
    528e:	0f 88 02 d3 ff ff    	js     2596 <io_thread.cold>
    5294:	8b 42 08             	mov    0x8(%rdx),%eax
    5297:	45 8b 04 24          	mov    (%r12),%r8d
    529b:	85 c0                	test   %eax,%eax
    529d:	0f 88 d5 02 00 00    	js     5578 <io_thread+0x678>
    52a3:	41 83 f8 01          	cmp    $0x1,%r8d
    52a7:	0f 84 7b 01 00 00    	je     5428 <io_thread+0x528>
    52ad:	41 83 f8 02          	cmp    $0x2,%r8d
    52b1:	0f 84 a1 01 00 00    	je     5458 <io_thread+0x558>
    52b7:	45 85 c0             	test   %r8d,%r8d
    52ba:	0f 85 50 01 00 00    	jne    5410 <io_thread+0x510>
    52c0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    52c5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    52ca:	48 89 d9             	mov    %rbx,%rcx
    52cd:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    52d1:	e8 8a fb ff ff       	call   4e60 <add_accept_request>
    52d6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    52db:	48 89 de             	mov    %rbx,%rsi
    52de:	8b 78 08             	mov    0x8(%rax),%edi
    52e1:	e8 1a f5 ff ff       	call   4800 <add_read_request>
    52e6:	4c 89 e7             	mov    %r12,%rdi
    52e9:	e8 d2 cf ff ff       	call   22c0 <free@plt>
    52ee:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    52f3:	48 85 c0             	test   %rax,%rax
    52f6:	0f 85 14 01 00 00    	jne    5410 <io_thread+0x510>
    52fc:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5303:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    530a:	8d 50 01             	lea    0x1(%rax),%edx
    530d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5312:	8b 30                	mov    (%rax),%esi
    5314:	f6 c1 02             	test   $0x2,%cl
    5317:	74 00                	je     5319 <io_thread+0x419>
    5319:	89 d0                	mov    %edx,%eax
    531b:	29 f0                	sub    %esi,%eax
    531d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5324:	0f 82 90 d2 ff ff    	jb     25ba <io_thread.cold+0x24>
    532a:	c1 e9 0a             	shr    $0xa,%ecx
    532d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    5332:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5336:	48 89 df             	mov    %rbx,%rdi
    5339:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5340:	83 e1 01             	and    $0x1,%ecx
    5343:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    534a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5351:	d3 e0                	shl    %cl,%eax
    5353:	8b 55 50             	mov    0x50(%rbp),%edx
    5356:	48 c1 e0 06          	shl    $0x6,%rax
    535a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5362:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5368:	89 50 04             	mov    %edx,0x4(%rax)
    536b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5373:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5377:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    537f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5387:	48 89 70 20          	mov    %rsi,0x20(%rax)
    538b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    538f:	e8 ac cf ff ff       	call   2340 <io_uring_submit@plt>
    5394:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    5398:	0f 84 3a fe ff ff    	je     51d8 <io_thread+0x2d8>
    539e:	48 8d 3d 4c 1e 00 00 	lea    0x1e4c(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    53a5:	e8 46 cf ff ff       	call   22f0 <puts@plt>
    53aa:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    53b2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    53bb:	0f 85 18 02 00 00    	jne    55d9 <io_thread+0x6d9>
    53c1:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    53c8:	31 c0                	xor    %eax,%eax
    53ca:	5b                   	pop    %rbx
    53cb:	5d                   	pop    %rbp
    53cc:	41 5c                	pop    %r12
    53ce:	41 5d                	pop    %r13
    53d0:	41 5e                	pop    %r14
    53d2:	41 5f                	pop    %r15
    53d4:	c3                   	ret
    53d5:	0f 1f 00             	nopl   (%rax)
    53d8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    53dd:	48 85 c0             	test   %rax,%rax
    53e0:	0f 84 6a fe ff ff    	je     5250 <io_thread+0x350>
    53e6:	48 83 38 01          	cmpq   $0x1,(%rax)
    53ea:	0f 84 68 01 00 00    	je     5558 <io_thread+0x658>
    53f0:	48 8d 3d c1 1d 00 00 	lea    0x1dc1(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    53f7:	e8 f4 ce ff ff       	call   22f0 <puts@plt>
    53fc:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5401:	4c 8b 22             	mov    (%rdx),%r12
    5404:	e9 8b fe ff ff       	jmp    5294 <io_thread+0x394>
    5409:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5410:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5418:	8b 02                	mov    (%rdx),%eax
    541a:	83 c0 01             	add    $0x1,%eax
    541d:	89 02                	mov    %eax,(%rdx)
    541f:	e9 d8 fe ff ff       	jmp    52fc <io_thread+0x3fc>
    5424:	0f 1f 40 00          	nopl   0x0(%rax)
    5428:	85 c0                	test   %eax,%eax
    542a:	75 74                	jne    54a0 <io_thread+0x5a0>
    542c:	48 8b 0d ed 4b 00 00 	mov    0x4bed(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5433:	ba 0f 00 00 00       	mov    $0xf,%edx
    5438:	be 01 00 00 00       	mov    $0x1,%esi
    543d:	48 8d 3d 9d 1d 00 00 	lea    0x1d9d(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    5444:	e8 77 d0 ff ff       	call   24c0 <fwrite@plt>
    5449:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    544e:	e9 a0 fe ff ff       	jmp    52f3 <io_thread+0x3f3>
    5453:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5458:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    545d:	45 31 ff             	xor    %r15d,%r15d
    5460:	85 c0                	test   %eax,%eax
    5462:	7e 20                	jle    5484 <io_thread+0x584>
    5464:	0f 1f 40 00          	nopl   0x0(%rax)
    5468:	4c 89 f8             	mov    %r15,%rax
    546b:	49 83 c7 01          	add    $0x1,%r15
    546f:	48 c1 e0 04          	shl    $0x4,%rax
    5473:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5478:	e8 43 ce ff ff       	call   22c0 <free@plt>
    547d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5482:	7f e4                	jg     5468 <io_thread+0x568>
    5484:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5489:	e8 e2 ce ff ff       	call   2370 <close@plt>
    548e:	4c 89 e7             	mov    %r12,%rdi
    5491:	e8 2a ce ff ff       	call   22c0 <free@plt>
    5496:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    549b:	e9 53 fe ff ff       	jmp    52f3 <io_thread+0x3f3>
    54a0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    54a5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    54aa:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    54b2:	eb 11                	jmp    54c5 <io_thread+0x5c5>
    54b4:	0f 1f 40 00          	nopl   0x0(%rax)
    54b8:	48 83 c0 01          	add    $0x1,%rax
    54bc:	48 83 c2 01          	add    $0x1,%rdx
    54c0:	48 39 c6             	cmp    %rax,%rsi
    54c3:	74 4b                	je     5510 <io_thread+0x610>
    54c5:	0f b6 0a             	movzbl (%rdx),%ecx
    54c8:	88 08                	mov    %cl,(%rax)
    54ca:	80 f9 0d             	cmp    $0xd,%cl
    54cd:	75 e9                	jne    54b8 <io_thread+0x5b8>
    54cf:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    54d3:	75 e3                	jne    54b8 <io_thread+0x5b8>
    54d5:	c6 00 00             	movb   $0x0,(%rax)
    54d8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    54dd:	48 89 da             	mov    %rbx,%rdx
    54e0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    54e5:	e8 96 f7 ff ff       	call   4c80 <handle_http_method>
    54ea:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    54ef:	e8 cc cd ff ff       	call   22c0 <free@plt>
    54f4:	4c 89 e7             	mov    %r12,%rdi
    54f7:	e8 c4 cd ff ff       	call   22c0 <free@plt>
    54fc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5501:	e9 ed fd ff ff       	jmp    52f3 <io_thread+0x3f3>
    5506:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5510:	48 8b 0d 09 4b 00 00 	mov    0x4b09(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5517:	ba 12 00 00 00       	mov    $0x12,%edx
    551c:	be 01 00 00 00       	mov    $0x1,%esi
    5521:	48 8d 3d 0f 1c 00 00 	lea    0x1c0f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    5528:	e8 93 cf ff ff       	call   24c0 <fwrite@plt>
    552d:	bf 01 00 00 00       	mov    $0x1,%edi
    5532:	e8 69 cf ff ff       	call   24a0 <exit@plt>
    5537:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5540:	e9 ec fb ff ff       	jmp    5131 <io_thread+0x231>
    5545:	0f 1f 00             	nopl   (%rax)
    5548:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    554d:	e9 94 fe ff ff       	jmp    53e6 <io_thread+0x4e6>
    5552:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5558:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5560:	48 8d 3d 3d 1c 00 00 	lea    0x1c3d(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    5567:	8b 02                	mov    (%rdx),%eax
    5569:	83 c0 01             	add    $0x1,%eax
    556c:	89 02                	mov    %eax,(%rdx)
    556e:	e8 7d cd ff ff       	call   22f0 <puts@plt>
    5573:	e9 26 fe ff ff       	jmp    539e <io_thread+0x49e>
    5578:	f7 d8                	neg    %eax
    557a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    557f:	89 c7                	mov    %eax,%edi
    5581:	e8 7a cf ff ff       	call   2500 <strerror@plt>
    5586:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    558b:	be 01 00 00 00       	mov    $0x1,%esi
    5590:	48 8b 3d 89 4a 00 00 	mov    0x4a89(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5597:	48 89 c1             	mov    %rax,%rcx
    559a:	48 8d 15 97 1e 00 00 	lea    0x1e97(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    55a1:	31 c0                	xor    %eax,%eax
    55a3:	e8 28 cf ff ff       	call   24d0 <__fprintf_chk@plt>
    55a8:	bf 01 00 00 00       	mov    $0x1,%edi
    55ad:	e8 ee ce ff ff       	call   24a0 <exit@plt>
    55b2:	48 8b 0d 67 4a 00 00 	mov    0x4a67(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    55b9:	ba 28 00 00 00       	mov    $0x28,%edx
    55be:	be 01 00 00 00       	mov    $0x1,%esi
    55c3:	48 8d 3d 3e 1e 00 00 	lea    0x1e3e(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    55ca:	e8 f1 ce ff ff       	call   24c0 <fwrite@plt>
    55cf:	bf 01 00 00 00       	mov    $0x1,%edi
    55d4:	e8 c7 ce ff ff       	call   24a0 <exit@plt>
    55d9:	e8 52 cd ff ff       	call   2330 <__stack_chk_fail@plt>
    55de:	66 90                	xchg   %ax,%ax

00000000000055e0 <sendm>:
    55e0:	f3 0f 1e fa          	endbr64
    55e4:	41 57                	push   %r15
    55e6:	41 56                	push   %r14
    55e8:	41 55                	push   %r13
    55ea:	41 54                	push   %r12
    55ec:	55                   	push   %rbp
    55ed:	53                   	push   %rbx
    55ee:	48 83 ec 18          	sub    $0x18,%rsp
    55f2:	83 bf 68 02 00 00 01 	cmpl   $0x1,0x268(%rdi)
    55f9:	0f 85 a9 01 00 00    	jne    57a8 <sendm+0x1c8>
    55ff:	48 8d b7 70 02 00 00 	lea    0x270(%rdi),%rsi
    5606:	8b 87 24 02 00 00    	mov    0x224(%rdi),%eax
    560c:	48 89 fa             	mov    %rdi,%rdx
    560f:	31 c9                	xor    %ecx,%ecx
    5611:	48 89 34 24          	mov    %rsi,(%rsp)
    5615:	48 8d b7 78 02 00 00 	lea    0x278(%rdi),%rsi
    561c:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5621:	85 c0                	test   %eax,%eax
    5623:	0f 8e e1 00 00 00    	jle    570a <sendm+0x12a>
    5629:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5630:	39 8a 20 02 00 00    	cmp    %ecx,0x220(%rdx)
    5636:	0f 84 c2 00 00 00    	je     56fe <sendm+0x11e>
    563c:	49 89 ca             	mov    %rcx,%r10
    563f:	49 c1 e2 09          	shl    $0x9,%r10
    5643:	4c 03 92 58 02 00 00 	add    0x258(%rdx),%r10
    564a:	4d 8b 9a 80 00 00 00 	mov    0x80(%r10),%r11
    5651:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    5655:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    5659:	4c 39 cb             	cmp    %r9,%rbx
    565c:	0f 8d 93 00 00 00    	jge    56f5 <sendm+0x115>
    5662:	4c 89 cf             	mov    %r9,%rdi
    5665:	48 8b aa 80 01 00 00 	mov    0x180(%rdx),%rbp
    566c:	4d 8b b2 00 01 00 00 	mov    0x100(%r10),%r14
    5673:	48 29 df             	sub    %rbx,%rdi
    5676:	49 8b 33             	mov    (%r11),%rsi
    5679:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    567d:	48 83 f8 02          	cmp    $0x2,%rax
    5681:	0f 86 09 01 00 00    	jbe    5790 <sendm+0x1b0>
    5687:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    568f:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5697:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    569b:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    569f:	4c 39 2c 24          	cmp    %r13,(%rsp)
    56a3:	73 7b                	jae    5720 <sendm+0x140>
    56a5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    56aa:	4d 39 fc             	cmp    %r15,%r12
    56ad:	73 71                	jae    5720 <sendm+0x140>
    56af:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    56b3:	49 01 f0             	add    %rsi,%r8
    56b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    56c0:	48 8b 82 70 02 00 00 	mov    0x270(%rdx),%rax
    56c7:	48 83 c3 08          	add    $0x8,%rbx
    56cb:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
    56cf:	49 39 d8             	cmp    %rbx,%r8
    56d2:	75 ec                	jne    56c0 <sendm+0xe0>
    56d4:	0f 1f 40 00          	nopl   0x0(%rax)
    56d8:	48 01 fd             	add    %rdi,%rbp
    56db:	4c 01 f7             	add    %r14,%rdi
    56de:	48 89 aa 80 01 00 00 	mov    %rbp,0x180(%rdx)
    56e5:	49 89 ba 00 01 00 00 	mov    %rdi,0x100(%r10)
    56ec:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    56f0:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
    56f5:	0f ae f8             	sfence
    56f8:	8b 82 24 02 00 00    	mov    0x224(%rdx),%eax
    56fe:	48 83 c1 01          	add    $0x1,%rcx
    5702:	39 c8                	cmp    %ecx,%eax
    5704:	0f 8f 26 ff ff ff    	jg     5630 <sendm+0x50>
    570a:	48 83 c4 18          	add    $0x18,%rsp
    570e:	31 c0                	xor    %eax,%eax
    5710:	5b                   	pop    %rbx
    5711:	5d                   	pop    %rbp
    5712:	41 5c                	pop    %r12
    5714:	41 5d                	pop    %r13
    5716:	41 5e                	pop    %r14
    5718:	41 5f                	pop    %r15
    571a:	c3                   	ret
    571b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5720:	49 89 fd             	mov    %rdi,%r13
    5723:	48 8b 82 70 02 00 00 	mov    0x270(%rdx),%rax
    572a:	4d 89 e0             	mov    %r12,%r8
    572d:	49 d1 ed             	shr    %r13
    5730:	49 c1 e5 04          	shl    $0x4,%r13
    5734:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5739:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    573d:	41 83 e5 10          	and    $0x10,%r13d
    5741:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5745:	74 11                	je     5758 <sendm+0x178>
    5747:	49 83 c0 10          	add    $0x10,%r8
    574b:	41 0f 11 04 24       	movups %xmm0,(%r12)
    5750:	4d 39 f8             	cmp    %r15,%r8
    5753:	74 15                	je     576a <sendm+0x18a>
    5755:	0f 1f 00             	nopl   (%rax)
    5758:	41 0f 11 00          	movups %xmm0,(%r8)
    575c:	49 83 c0 20          	add    $0x20,%r8
    5760:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
    5765:	4d 39 f8             	cmp    %r15,%r8
    5768:	75 ee                	jne    5758 <sendm+0x178>
    576a:	49 89 f8             	mov    %rdi,%r8
    576d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    5771:	49 01 d8             	add    %rbx,%r8
    5774:	40 f6 c7 01          	test   $0x1,%dil
    5778:	0f 84 5a ff ff ff    	je     56d8 <sendm+0xf8>
    577e:	48 8b 82 70 02 00 00 	mov    0x270(%rdx),%rax
    5785:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
    5789:	e9 4a ff ff ff       	jmp    56d8 <sendm+0xf8>
    578e:	66 90                	xchg   %ax,%ax
    5790:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5798:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    57a0:	e9 0a ff ff ff       	jmp    56af <sendm+0xcf>
    57a5:	0f 1f 00             	nopl   (%rax)
    57a8:	48 8d 3d 55 1a 00 00 	lea    0x1a55(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    57af:	e8 3c cb ff ff       	call   22f0 <puts@plt>
    57b4:	e9 51 ff ff ff       	jmp    570a <sendm+0x12a>
    57b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000057c0 <receive>:
    57c0:	f3 0f 1e fa          	endbr64
    57c4:	8b 87 24 02 00 00    	mov    0x224(%rdi),%eax
    57ca:	85 c0                	test   %eax,%eax
    57cc:	0f 8e f1 00 00 00    	jle    58c3 <receive+0x103>
    57d2:	41 54                	push   %r12
    57d4:	48 89 fa             	mov    %rdi,%rdx
    57d7:	55                   	push   %rbp
    57d8:	31 ed                	xor    %ebp,%ebp
    57da:	53                   	push   %rbx
    57db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    57e0:	48 89 ee             	mov    %rbp,%rsi
    57e3:	48 c1 e6 09          	shl    $0x9,%rsi
    57e7:	48 03 b2 58 02 00 00 	add    0x258(%rdx),%rsi
    57ee:	4c 8b 26             	mov    (%rsi),%r12
    57f1:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    57f6:	48 85 ff             	test   %rdi,%rdi
    57f9:	0f 8e a1 00 00 00    	jle    58a0 <receive+0xe0>
    57ff:	48 8b 8a 60 02 00 00 	mov    0x260(%rdx),%rcx
    5806:	4d 8b 04 24          	mov    (%r12),%r8
    580a:	4c 63 1a             	movslq (%rdx),%r11
    580d:	49 89 c9             	mov    %rcx,%r9
    5810:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5814:	49 f7 d9             	neg    %r9
    5817:	48 01 c7             	add    %rax,%rdi
    581a:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
    581e:	4c 8b 8a 80 01 00 00 	mov    0x180(%rdx),%r9
    5825:	4c 8b 86 80 01 00 00 	mov    0x180(%rsi),%r8
    582c:	49 29 c9             	sub    %rcx,%r9
    582f:	49 29 c8             	sub    %rcx,%r8
    5832:	eb 0d                	jmp    5841 <receive+0x81>
    5834:	0f 1f 40 00          	nopl   0x0(%rax)
    5838:	48 83 c0 01          	add    $0x1,%rax
    583c:	48 39 c7             	cmp    %rax,%rdi
    583f:	74 5f                	je     58a0 <receive+0xe0>
    5841:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    5845:	48 89 82 60 02 00 00 	mov    %rax,0x260(%rdx)
    584c:	48 89 8a 80 01 00 00 	mov    %rcx,0x180(%rdx)
    5853:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5857:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
    585e:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5863:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5867:	75 cf                	jne    5838 <receive+0x78>
    5869:	48 63 9a 20 02 00 00 	movslq 0x220(%rdx),%rbx
    5870:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5874:	75 c2                	jne    5838 <receive+0x78>
    5876:	bf 01 00 00 00       	mov    $0x1,%edi
    587b:	b9 01 00 00 00       	mov    $0x1,%ecx
    5880:	ba 01 00 00 00       	mov    $0x1,%edx
    5885:	31 c0                	xor    %eax,%eax
    5887:	48 8d 35 d2 1b 00 00 	lea    0x1bd2(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    588e:	e8 bd cb ff ff       	call   2450 <__printf_chk@plt>
    5893:	bf 01 00 00 00       	mov    $0x1,%edi
    5898:	e8 03 cc ff ff       	call   24a0 <exit@plt>
    589d:	0f 1f 00             	nopl   (%rax)
    58a0:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    58a9:	0f ae f8             	sfence
    58ac:	48 83 c5 01          	add    $0x1,%rbp
    58b0:	39 aa 24 02 00 00    	cmp    %ebp,0x224(%rdx)
    58b6:	0f 8f 24 ff ff ff    	jg     57e0 <receive+0x20>
    58bc:	5b                   	pop    %rbx
    58bd:	31 c0                	xor    %eax,%eax
    58bf:	5d                   	pop    %rbp
    58c0:	41 5c                	pop    %r12
    58c2:	c3                   	ret
    58c3:	31 c0                	xor    %eax,%eax
    58c5:	c3                   	ret
    58c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000058d0 <barriered_work>:
    58d0:	f3 0f 1e fa          	endbr64
    58d4:	41 57                	push   %r15
    58d6:	41 56                	push   %r14
    58d8:	41 55                	push   %r13
    58da:	41 54                	push   %r12
    58dc:	55                   	push   %rbp
    58dd:	53                   	push   %rbx
    58de:	48 89 fb             	mov    %rdi,%rbx
    58e1:	48 83 ec 18          	sub    $0x18,%rsp
    58e5:	8b 07                	mov    (%rdi),%eax
    58e7:	39 87 20 02 00 00    	cmp    %eax,0x220(%rdi)
    58ed:	0f 84 3d 01 00 00    	je     5a30 <barriered_work+0x160>
    58f3:	e8 c8 fe ff ff       	call   57c0 <receive>
    58f8:	83 bb 30 02 00 00 01 	cmpl   $0x1,0x230(%rbx)
    58ff:	75 1b                	jne    591c <barriered_work+0x4c>
    5901:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5908:	48 83 83 80 01 00 00 01 	addq   $0x1,0x180(%rbx)
    5910:	0f ae f8             	sfence
    5913:	83 bb 30 02 00 00 01 	cmpl   $0x1,0x230(%rbx)
    591a:	74 ec                	je     5908 <barriered_work+0x38>
    591c:	83 bb 68 02 00 00 01 	cmpl   $0x1,0x268(%rbx)
    5923:	0f 85 80 02 00 00    	jne    5ba9 <barriered_work+0x2d9>
    5929:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    592f:	85 c0                	test   %eax,%eax
    5931:	0f 8e 7e 02 00 00    	jle    5bb5 <barriered_work+0x2e5>
    5937:	48 8d 8b 70 02 00 00 	lea    0x270(%rbx),%rcx
    593e:	31 d2                	xor    %edx,%edx
    5940:	48 89 0c 24          	mov    %rcx,(%rsp)
    5944:	48 8d 8b 78 02 00 00 	lea    0x278(%rbx),%rcx
    594b:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5950:	39 93 20 02 00 00    	cmp    %edx,0x220(%rbx)
    5956:	0f 84 c2 00 00 00    	je     5a1e <barriered_work+0x14e>
    595c:	49 89 d1             	mov    %rdx,%r9
    595f:	49 c1 e1 09          	shl    $0x9,%r9
    5963:	4c 03 8b 58 02 00 00 	add    0x258(%rbx),%r9
    596a:	4d 8b 91 80 00 00 00 	mov    0x80(%r9),%r10
    5971:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5975:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5979:	4d 39 c3             	cmp    %r8,%r11
    597c:	0f 8d 93 00 00 00    	jge    5a15 <barriered_work+0x145>
    5982:	4c 89 c6             	mov    %r8,%rsi
    5985:	48 8b ab 80 01 00 00 	mov    0x180(%rbx),%rbp
    598c:	4d 8b b1 00 01 00 00 	mov    0x100(%r9),%r14
    5993:	4c 29 de             	sub    %r11,%rsi
    5996:	49 8b 0a             	mov    (%r10),%rcx
    5999:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    599d:	48 83 f8 02          	cmp    $0x2,%rax
    59a1:	0f 86 99 02 00 00    	jbe    5c40 <barriered_work+0x370>
    59a7:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    59af:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    59b7:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    59bb:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    59bf:	4c 39 2c 24          	cmp    %r13,(%rsp)
    59c3:	0f 83 07 02 00 00    	jae    5bd0 <barriered_work+0x300>
    59c9:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    59ce:	4d 39 fc             	cmp    %r15,%r12
    59d1:	0f 83 f9 01 00 00    	jae    5bd0 <barriered_work+0x300>
    59d7:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    59db:	48 01 cf             	add    %rcx,%rdi
    59de:	66 90                	xchg   %ax,%ax
    59e0:	48 8b 83 70 02 00 00 	mov    0x270(%rbx),%rax
    59e7:	49 83 c3 08          	add    $0x8,%r11
    59eb:	49 89 43 f8          	mov    %rax,-0x8(%r11)
    59ef:	49 39 fb             	cmp    %rdi,%r11
    59f2:	75 ec                	jne    59e0 <barriered_work+0x110>
    59f4:	0f 1f 40 00          	nopl   0x0(%rax)
    59f8:	48 01 f5             	add    %rsi,%rbp
    59fb:	4c 01 f6             	add    %r14,%rsi
    59fe:	48 89 ab 80 01 00 00 	mov    %rbp,0x180(%rbx)
    5a05:	49 89 b1 00 01 00 00 	mov    %rsi,0x100(%r9)
    5a0c:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5a10:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
    5a15:	0f ae f8             	sfence
    5a18:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    5a1e:	48 83 c2 01          	add    $0x1,%rdx
    5a22:	39 d0                	cmp    %edx,%eax
    5a24:	0f 8f 26 ff ff ff    	jg     5950 <barriered_work+0x80>
    5a2a:	e9 86 01 00 00       	jmp    5bb5 <barriered_work+0x2e5>
    5a2f:	90                   	nop
    5a30:	e8 8b fd ff ff       	call   57c0 <receive>
    5a35:	4c 63 8b 24 02 00 00 	movslq 0x224(%rbx),%r9
    5a3c:	8b 03                	mov    (%rbx),%eax
    5a3e:	45 85 c9             	test   %r9d,%r9d
    5a41:	0f 8e 8b 00 00 00    	jle    5ad2 <barriered_work+0x202>
    5a47:	48 8b 93 18 02 00 00 	mov    0x218(%rbx),%rdx
    5a4e:	4c 8b 52 10          	mov    0x10(%rdx),%r10
    5a52:	48 63 d0             	movslq %eax,%rdx
    5a55:	83 c0 01             	add    $0x1,%eax
    5a58:	4c 8d 1c 92          	lea    (%rdx,%rdx,4),%r11
    5a5c:	99                   	cltd
    5a5d:	41 f7 f9             	idiv   %r9d
    5a60:	49 c1 e3 07          	shl    $0x7,%r11
    5a64:	4c 89 d7             	mov    %r10,%rdi
    5a67:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
    5a6b:	89 d0                	mov    %edx,%eax
    5a6d:	f7 d8                	neg    %eax
    5a6f:	0f 48 c2             	cmovs  %edx,%eax
    5a72:	45 31 c0             	xor    %r8d,%r8d
    5a75:	48 98                	cltq
    5a77:	48 8d 2c 80          	lea    (%rax,%rax,4),%rbp
    5a7b:	48 c1 e5 07          	shl    $0x7,%rbp
    5a7f:	90                   	nop
    5a80:	31 c0                	xor    %eax,%eax
    5a82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5a88:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    5a8c:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    5a90:	48 8b 8c 2a 58 02 00 00 	mov    0x258(%rdx,%rbp,1),%rcx
    5a98:	48 8b 17             	mov    (%rdi),%rdx
    5a9b:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    5a9f:	48 89 c2             	mov    %rax,%rdx
    5aa2:	48 83 c0 01          	add    $0x1,%rax
    5aa6:	48 c1 e2 09          	shl    $0x9,%rdx
    5aaa:	4a 03 94 1e 58 02 00 00 	add    0x258(%rsi,%r11,1),%rdx
    5ab2:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    5ab9:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
    5abd:	49 39 c1             	cmp    %rax,%r9
    5ac0:	75 c6                	jne    5a88 <barriered_work+0x1b8>
    5ac2:	48 83 c7 08          	add    $0x8,%rdi
    5ac6:	49 81 c0 00 02 00 00 	add    $0x200,%r8
    5acd:	49 39 fc             	cmp    %rdi,%r12
    5ad0:	75 ae                	jne    5a80 <barriered_work+0x1b0>
    5ad2:	0f ae f8             	sfence
    5ad5:	48 8b b3 48 02 00 00 	mov    0x248(%rbx),%rsi
    5adc:	31 ff                	xor    %edi,%edi
    5ade:	48 c1 e6 05          	shl    $0x5,%rsi
    5ae2:	48 03 b3 38 02 00 00 	add    0x238(%rbx),%rsi
    5ae9:	e8 22 c8 ff ff       	call   2310 <clock_gettime@plt>
    5aee:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    5af5:	83 bb 30 02 00 00 01 	cmpl   $0x1,0x230(%rbx)
    5afc:	48 8b 50 38          	mov    0x38(%rax),%rdx
    5b00:	8b 4a 10             	mov    0x10(%rdx),%ecx
    5b03:	8d 69 01             	lea    0x1(%rcx),%ebp
    5b06:	89 6a 10             	mov    %ebp,0x10(%rdx)
    5b09:	75 59                	jne    5b64 <barriered_work+0x294>
    5b0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5b10:	48 63 93 20 02 00 00 	movslq 0x220(%rbx),%rdx
    5b17:	48 8b 40 10          	mov    0x10(%rax),%rax
    5b1b:	48 83 83 80 01 00 00 01 	addq   $0x1,0x180(%rbx)
    5b23:	48 8b 14 d0          	mov    (%rax,%rdx,8),%rdx
    5b27:	48 63 03             	movslq (%rbx),%rax
    5b2a:	48 8d 3c 80          	lea    (%rax,%rax,4),%rdi
    5b2e:	48 c1 e7 07          	shl    $0x7,%rdi
    5b32:	48 03 7a 28          	add    0x28(%rdx),%rdi
    5b36:	ff 93 10 02 00 00    	call   *0x210(%rbx)
    5b3c:	0f ae f8             	sfence
    5b3f:	83 bb 30 02 00 00 01 	cmpl   $0x1,0x230(%rbx)
    5b46:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    5b4d:	74 c1                	je     5b10 <barriered_work+0x240>
    5b4f:	48 8b 40 38          	mov    0x38(%rax),%rax
    5b53:	3b 68 10             	cmp    0x10(%rax),%ebp
    5b56:	74 0c                	je     5b64 <barriered_work+0x294>
    5b58:	48 8d 3d b1 16 00 00 	lea    0x16b1(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    5b5f:	e8 8c c7 ff ff       	call   22f0 <puts@plt>
    5b64:	48 8b b3 48 02 00 00 	mov    0x248(%rbx),%rsi
    5b6b:	31 ff                	xor    %edi,%edi
    5b6d:	48 c1 e6 05          	shl    $0x5,%rsi
    5b71:	48 03 b3 38 02 00 00 	add    0x238(%rbx),%rsi
    5b78:	48 83 c6 10          	add    $0x10,%rsi
    5b7c:	e8 8f c7 ff ff       	call   2310 <clock_gettime@plt>
    5b81:	48 8b 83 48 02 00 00 	mov    0x248(%rbx),%rax
    5b88:	48 83 c0 01          	add    $0x1,%rax
    5b8c:	48 99                	cqto
    5b8e:	48 f7 bb 40 02 00 00 	idivq  0x240(%rbx)
    5b95:	83 bb 68 02 00 00 01 	cmpl   $0x1,0x268(%rbx)
    5b9c:	48 89 93 48 02 00 00 	mov    %rdx,0x248(%rbx)
    5ba3:	0f 84 ac 00 00 00    	je     5c55 <barriered_work+0x385>
    5ba9:	48 8d 3d 54 16 00 00 	lea    0x1654(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5bb0:	e8 3b c7 ff ff       	call   22f0 <puts@plt>
    5bb5:	0f ae f8             	sfence
    5bb8:	48 83 c4 18          	add    $0x18,%rsp
    5bbc:	31 c0                	xor    %eax,%eax
    5bbe:	5b                   	pop    %rbx
    5bbf:	5d                   	pop    %rbp
    5bc0:	41 5c                	pop    %r12
    5bc2:	41 5d                	pop    %r13
    5bc4:	41 5e                	pop    %r14
    5bc6:	41 5f                	pop    %r15
    5bc8:	c3                   	ret
    5bc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5bd0:	49 89 f5             	mov    %rsi,%r13
    5bd3:	48 8b 83 70 02 00 00 	mov    0x270(%rbx),%rax
    5bda:	4c 89 e7             	mov    %r12,%rdi
    5bdd:	49 d1 ed             	shr    %r13
    5be0:	49 c1 e5 04          	shl    $0x4,%r13
    5be4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5be9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5bed:	41 83 e5 10          	and    $0x10,%r13d
    5bf1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5bf5:	74 11                	je     5c08 <barriered_work+0x338>
    5bf7:	48 83 c7 10          	add    $0x10,%rdi
    5bfb:	41 0f 11 04 24       	movups %xmm0,(%r12)
    5c00:	49 39 ff             	cmp    %rdi,%r15
    5c03:	74 13                	je     5c18 <barriered_work+0x348>
    5c05:	0f 1f 00             	nopl   (%rax)
    5c08:	0f 11 07             	movups %xmm0,(%rdi)
    5c0b:	48 83 c7 20          	add    $0x20,%rdi
    5c0f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
    5c13:	49 39 ff             	cmp    %rdi,%r15
    5c16:	75 f0                	jne    5c08 <barriered_work+0x338>
    5c18:	48 89 f7             	mov    %rsi,%rdi
    5c1b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5c1f:	4c 01 df             	add    %r11,%rdi
    5c22:	40 f6 c6 01          	test   $0x1,%sil
    5c26:	0f 84 cc fd ff ff    	je     59f8 <barriered_work+0x128>
    5c2c:	48 8b 83 70 02 00 00 	mov    0x270(%rbx),%rax
    5c33:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
    5c37:	e9 bc fd ff ff       	jmp    59f8 <barriered_work+0x128>
    5c3c:	0f 1f 40 00          	nopl   0x0(%rax)
    5c40:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5c48:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5c50:	e9 82 fd ff ff       	jmp    59d7 <barriered_work+0x107>
    5c55:	48 8d 8b 70 02 00 00 	lea    0x270(%rbx),%rcx
    5c5c:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    5c62:	31 d2                	xor    %edx,%edx
    5c64:	48 89 0c 24          	mov    %rcx,(%rsp)
    5c68:	48 8d 8b 78 02 00 00 	lea    0x278(%rbx),%rcx
    5c6f:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5c74:	85 c0                	test   %eax,%eax
    5c76:	0f 8e 39 ff ff ff    	jle    5bb5 <barriered_work+0x2e5>
    5c7c:	0f 1f 40 00          	nopl   0x0(%rax)
    5c80:	39 93 20 02 00 00    	cmp    %edx,0x220(%rbx)
    5c86:	0f 84 c2 00 00 00    	je     5d4e <barriered_work+0x47e>
    5c8c:	49 89 d1             	mov    %rdx,%r9
    5c8f:	49 c1 e1 09          	shl    $0x9,%r9
    5c93:	4c 03 8b 58 02 00 00 	add    0x258(%rbx),%r9
    5c9a:	4d 8b 91 80 00 00 00 	mov    0x80(%r9),%r10
    5ca1:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5ca5:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5ca9:	4d 39 d8             	cmp    %r11,%r8
    5cac:	0f 8e 93 00 00 00    	jle    5d45 <barriered_work+0x475>
    5cb2:	4c 89 c6             	mov    %r8,%rsi
    5cb5:	48 8b ab 80 01 00 00 	mov    0x180(%rbx),%rbp
    5cbc:	4d 8b b1 00 01 00 00 	mov    0x100(%r9),%r14
    5cc3:	4c 29 de             	sub    %r11,%rsi
    5cc6:	49 8b 0a             	mov    (%r10),%rcx
    5cc9:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5ccd:	48 83 f8 02          	cmp    $0x2,%rax
    5cd1:	0f 86 f9 00 00 00    	jbe    5dd0 <barriered_work+0x500>
    5cd7:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5cdf:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5ce7:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5ceb:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5cef:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5cf3:	73 6b                	jae    5d60 <barriered_work+0x490>
    5cf5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5cfa:	4d 39 fc             	cmp    %r15,%r12
    5cfd:	73 61                	jae    5d60 <barriered_work+0x490>
    5cff:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5d03:	48 01 cf             	add    %rcx,%rdi
    5d06:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5d10:	48 8b 83 70 02 00 00 	mov    0x270(%rbx),%rax
    5d17:	49 83 c3 08          	add    $0x8,%r11
    5d1b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
    5d1f:	49 39 fb             	cmp    %rdi,%r11
    5d22:	75 ec                	jne    5d10 <barriered_work+0x440>
    5d24:	0f 1f 40 00          	nopl   0x0(%rax)
    5d28:	48 01 f5             	add    %rsi,%rbp
    5d2b:	4c 01 f6             	add    %r14,%rsi
    5d2e:	48 89 ab 80 01 00 00 	mov    %rbp,0x180(%rbx)
    5d35:	49 89 b1 00 01 00 00 	mov    %rsi,0x100(%r9)
    5d3c:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5d40:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
    5d45:	0f ae f8             	sfence
    5d48:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    5d4e:	48 83 c2 01          	add    $0x1,%rdx
    5d52:	39 d0                	cmp    %edx,%eax
    5d54:	0f 8f 26 ff ff ff    	jg     5c80 <barriered_work+0x3b0>
    5d5a:	e9 56 fe ff ff       	jmp    5bb5 <barriered_work+0x2e5>
    5d5f:	90                   	nop
    5d60:	49 89 f5             	mov    %rsi,%r13
    5d63:	48 8b 83 70 02 00 00 	mov    0x270(%rbx),%rax
    5d6a:	4c 89 e7             	mov    %r12,%rdi
    5d6d:	49 d1 ed             	shr    %r13
    5d70:	49 c1 e5 04          	shl    $0x4,%r13
    5d74:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5d79:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5d7d:	41 83 e5 10          	and    $0x10,%r13d
    5d81:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5d85:	74 11                	je     5d98 <barriered_work+0x4c8>
    5d87:	48 83 c7 10          	add    $0x10,%rdi
    5d8b:	41 0f 11 04 24       	movups %xmm0,(%r12)
    5d90:	4c 39 ff             	cmp    %r15,%rdi
    5d93:	74 13                	je     5da8 <barriered_work+0x4d8>
    5d95:	0f 1f 00             	nopl   (%rax)
    5d98:	0f 11 07             	movups %xmm0,(%rdi)
    5d9b:	48 83 c7 20          	add    $0x20,%rdi
    5d9f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
    5da3:	4c 39 ff             	cmp    %r15,%rdi
    5da6:	75 f0                	jne    5d98 <barriered_work+0x4c8>
    5da8:	48 89 f7             	mov    %rsi,%rdi
    5dab:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5daf:	4c 01 df             	add    %r11,%rdi
    5db2:	40 f6 c6 01          	test   $0x1,%sil
    5db6:	0f 84 6c ff ff ff    	je     5d28 <barriered_work+0x458>
    5dbc:	48 8b 83 70 02 00 00 	mov    0x270(%rbx),%rax
    5dc3:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
    5dc7:	e9 5c ff ff ff       	jmp    5d28 <barriered_work+0x458>
    5dcc:	0f 1f 40 00          	nopl   0x0(%rax)
    5dd0:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5dd8:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5de0:	e9 1a ff ff ff       	jmp    5cff <barriered_work+0x42f>
    5de5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005df0 <barriered_work_ingest>:
    5df0:	f3 0f 1e fa          	endbr64
    5df4:	48 83 ec 08          	sub    $0x8,%rsp
    5df8:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    5dff:	48 8b 40 40          	mov    0x40(%rax),%rax
    5e03:	48 63 10             	movslq (%rax),%rdx
    5e06:	85 d2                	test   %edx,%edx
    5e08:	7e 2c                	jle    5e36 <barriered_work_ingest+0x46>
    5e0a:	48 8b 40 08          	mov    0x8(%rax),%rax
    5e0e:	48 c1 e2 04          	shl    $0x4,%rdx
    5e12:	48 01 c2             	add    %rax,%rdx
    5e15:	0f 1f 00             	nopl   (%rax)
    5e18:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5e1c:	75 0f                	jne    5e2d <barriered_work_ingest+0x3d>
    5e1e:	48 83 87 50 02 00 00 01 	addq   $0x1,0x250(%rdi)
    5e26:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    5e2d:	48 83 c0 10          	add    $0x10,%rax
    5e31:	48 39 d0             	cmp    %rdx,%rax
    5e34:	75 e2                	jne    5e18 <barriered_work_ingest+0x28>
    5e36:	0f ae f8             	sfence
    5e39:	e8 92 fa ff ff       	call   58d0 <barriered_work>
    5e3e:	31 c0                	xor    %eax,%eax
    5e40:	48 83 c4 08          	add    $0x8,%rsp
    5e44:	c3                   	ret
    5e45:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005e50 <barriered_nulltask>:
    5e50:	f3 0f 1e fa          	endbr64
    5e54:	31 c0                	xor    %eax,%eax
    5e56:	c3                   	ret
    5e57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005e60 <barriered_steal>:
    5e60:	f3 0f 1e fa          	endbr64
    5e64:	31 c0                	xor    %eax,%eax
    5e66:	c3                   	ret
    5e67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005e70 <after>:
    5e70:	f3 0f 1e fa          	endbr64
    5e74:	31 c0                	xor    %eax,%eax
    5e76:	48 39 d7             	cmp    %rdx,%rdi
    5e79:	7e 08                	jle    5e83 <after+0x13>
    5e7b:	31 c0                	xor    %eax,%eax
    5e7d:	48 39 ce             	cmp    %rcx,%rsi
    5e80:	0f 9f c0             	setg   %al
    5e83:	c3                   	ret
    5e84:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5e8f:	90                   	nop

0000000000005e90 <within>:
    5e90:	f3 0f 1e fa          	endbr64
    5e94:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5e99:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    5e9e:	31 c0                	xor    %eax,%eax
    5ea0:	48 39 d7             	cmp    %rdx,%rdi
    5ea3:	7f 18                	jg     5ebd <within+0x2d>
    5ea5:	4d 39 d8             	cmp    %r11,%r8
    5ea8:	0f 9e c2             	setle  %dl
    5eab:	48 39 ce             	cmp    %rcx,%rsi
    5eae:	0f 9e c0             	setle  %al
    5eb1:	21 c2                	and    %eax,%edx
    5eb3:	31 c0                	xor    %eax,%eax
    5eb5:	4d 39 d1             	cmp    %r10,%r9
    5eb8:	0f 9e c0             	setle  %al
    5ebb:	21 d0                	and    %edx,%eax
    5ebd:	c3                   	ret
    5ebe:	66 90                	xchg   %ax,%ax

0000000000005ec0 <overlap>:
    5ec0:	f3 0f 1e fa          	endbr64
    5ec4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5ec9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5ece:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5ed3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5ed8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5edd:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
    5ee2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5ee7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    5eec:	48 39 fe             	cmp    %rdi,%rsi
    5eef:	7d 2f                	jge    5f20 <overlap+0x60>
    5ef1:	48 39 ca             	cmp    %rcx,%rdx
    5ef4:	7d 62                	jge    5f58 <overlap+0x98>
    5ef6:	4d 39 da             	cmp    %r11,%r10
    5ef9:	7d 0e                	jge    5f09 <overlap+0x49>
    5efb:	b8 01 00 00 00       	mov    $0x1,%eax
    5f00:	4d 39 c1             	cmp    %r8,%r9
    5f03:	0f 8c 7f 00 00 00    	jl     5f88 <overlap+0xc8>
    5f09:	31 c0                	xor    %eax,%eax
    5f0b:	4d 39 c1             	cmp    %r8,%r9
    5f0e:	7f 4c                	jg     5f5c <overlap+0x9c>
    5f10:	31 c0                	xor    %eax,%eax
    5f12:	4d 39 da             	cmp    %r11,%r10
    5f15:	0f 9e c0             	setle  %al
    5f18:	c3                   	ret
    5f19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5f20:	7e 4e                	jle    5f70 <overlap+0xb0>
    5f22:	48 39 ca             	cmp    %rcx,%rdx
    5f25:	7f 39                	jg     5f60 <overlap+0xa0>
    5f27:	75 31                	jne    5f5a <overlap+0x9a>
    5f29:	4d 39 c1             	cmp    %r8,%r9
    5f2c:	7c 2c                	jl     5f5a <overlap+0x9a>
    5f2e:	b8 01 00 00 00       	mov    $0x1,%eax
    5f33:	4d 39 da             	cmp    %r11,%r10
    5f36:	7d 24                	jge    5f5c <overlap+0x9c>
    5f38:	48 39 ca             	cmp    %rcx,%rdx
    5f3b:	0f 94 c2             	sete   %dl
    5f3e:	48 39 fe             	cmp    %rdi,%rsi
    5f41:	0f 94 c0             	sete   %al
    5f44:	21 c2                	and    %eax,%edx
    5f46:	31 c0                	xor    %eax,%eax
    5f48:	4d 39 c1             	cmp    %r8,%r9
    5f4b:	0f 94 c0             	sete   %al
    5f4e:	21 d0                	and    %edx,%eax
    5f50:	c3                   	ret
    5f51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5f58:	74 af                	je     5f09 <overlap+0x49>
    5f5a:	31 c0                	xor    %eax,%eax
    5f5c:	c3                   	ret
    5f5d:	0f 1f 00             	nopl   (%rax)
    5f60:	4d 39 da             	cmp    %r11,%r10
    5f63:	7e c4                	jle    5f29 <overlap+0x69>
    5f65:	b8 01 00 00 00       	mov    $0x1,%eax
    5f6a:	4d 39 c1             	cmp    %r8,%r9
    5f6d:	7e ba                	jle    5f29 <overlap+0x69>
    5f6f:	c3                   	ret
    5f70:	48 39 ca             	cmp    %rcx,%rdx
    5f73:	7c 94                	jl     5f09 <overlap+0x49>
    5f75:	4d 39 c1             	cmp    %r8,%r9
    5f78:	7d b4                	jge    5f2e <overlap+0x6e>
    5f7a:	48 39 ca             	cmp    %rcx,%rdx
    5f7d:	74 91                	je     5f10 <overlap+0x50>
    5f7f:	eb d9                	jmp    5f5a <overlap+0x9a>
    5f81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5f88:	c3                   	ret
    5f89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005f90 <verify>:
    5f90:	f3 0f 1e fa          	endbr64
    5f94:	85 f6                	test   %esi,%esi
    5f96:	0f 8e 49 03 00 00    	jle    62e5 <verify+0x355>
    5f9c:	41 57                	push   %r15
    5f9e:	41 89 f7             	mov    %esi,%r15d
    5fa1:	41 56                	push   %r14
    5fa3:	45 31 f6             	xor    %r14d,%r14d
    5fa6:	41 55                	push   %r13
    5fa8:	41 54                	push   %r12
    5faa:	55                   	push   %rbp
    5fab:	53                   	push   %rbx
    5fac:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5fb0:	48 83 ec 48          	sub    $0x48,%rsp
    5fb4:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5fb9:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    5fbe:	45 31 e4             	xor    %r12d,%r12d
    5fc1:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    5fc6:	45 39 e6             	cmp    %r12d,%r14d
    5fc9:	0f 84 47 02 00 00    	je     6216 <verify+0x286>
    5fcf:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5fd4:	8b 50 08             	mov    0x8(%rax),%edx
    5fd7:	85 d2                	test   %edx,%edx
    5fd9:	0f 8e 37 02 00 00    	jle    6216 <verify+0x286>
    5fdf:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    5fe7:	31 ed                	xor    %ebp,%ebp
    5fe9:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    5fee:	44 89 7c 24 34       	mov    %r15d,0x34(%rsp)
    5ff3:	45 89 f7             	mov    %r14d,%r15d
    5ff6:	41 89 ee             	mov    %ebp,%r14d
    5ff9:	44 89 fa             	mov    %r15d,%edx
    5ffc:	48 8d 35 1d 12 00 00 	lea    0x121d(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    6003:	bf 01 00 00 00       	mov    $0x1,%edi
    6008:	31 c0                	xor    %eax,%eax
    600a:	e8 41 c4 ff ff       	call   2450 <__printf_chk@plt>
    600f:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6014:	8b 40 08             	mov    0x8(%rax),%eax
    6017:	85 c0                	test   %eax,%eax
    6019:	0f 8e cf 01 00 00    	jle    61ee <verify+0x25e>
    601f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6024:	44 89 74 24 38       	mov    %r14d,0x38(%rsp)
    6029:	31 db                	xor    %ebx,%ebx
    602b:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    6030:	4c 8b 20             	mov    (%rax),%r12
    6033:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6038:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    603d:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    6041:	4c 8b 3c 24          	mov    (%rsp),%r15
    6045:	48 8d 35 e9 11 00 00 	lea    0x11e9(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    604c:	49 89 c6             	mov    %rax,%r14
    604f:	bf 01 00 00 00       	mov    $0x1,%edi
    6054:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6058:	49 c1 e6 07          	shl    $0x7,%r14
    605c:	4b 8b 8c 3c 48 02 00 00 	mov    0x248(%r12,%r15,1),%rcx
    6064:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    6069:	4a 8b 94 30 48 02 00 00 	mov    0x248(%rax,%r14,1),%rdx
    6071:	31 c0                	xor    %eax,%eax
    6073:	e8 d8 c3 ff ff       	call   2450 <__printf_chk@plt>
    6078:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    607d:	4c 8b 20             	mov    (%rax),%r12
    6080:	4b 83 bc 3c 48 02 00 00 00 	cmpq   $0x0,0x248(%r12,%r15,1)
    6089:	0f 8e 43 01 00 00    	jle    61d2 <verify+0x242>
    608f:	4c 03 75 00          	add    0x0(%rbp),%r14
    6093:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    6098:	ba 01 00 00 00       	mov    $0x1,%edx
    609d:	4d 89 f5             	mov    %r14,%r13
    60a0:	4d 8b b5 48 02 00 00 	mov    0x248(%r13),%r14
    60a7:	4d 85 f6             	test   %r14,%r14
    60aa:	0f 8e 1d 01 00 00    	jle    61cd <verify+0x23d>
    60b0:	48 89 d5             	mov    %rdx,%rbp
    60b3:	48 8b 04 24          	mov    (%rsp),%rax
    60b7:	31 db                	xor    %ebx,%ebx
    60b9:	4d 89 f2             	mov    %r14,%r10
    60bc:	48 c1 e5 05          	shl    $0x5,%rbp
    60c0:	48 83 ed 20          	sub    $0x20,%rbp
    60c4:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    60c8:	49 89 ee             	mov    %rbp,%r14
    60cb:	48 89 dd             	mov    %rbx,%rbp
    60ce:	48 89 d3             	mov    %rdx,%rbx
    60d1:	eb 32                	jmp    6105 <verify+0x175>
    60d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    60d8:	4c 39 c2             	cmp    %r8,%rdx
    60db:	0f 8d 57 01 00 00    	jge    6238 <verify+0x2a8>
    60e1:	4c 39 df             	cmp    %r11,%rdi
    60e4:	7e 05                	jle    60eb <verify+0x15b>
    60e6:	49 39 c1             	cmp    %rax,%r9
    60e9:	7c 75                	jl     6160 <verify+0x1d0>
    60eb:	4c 39 df             	cmp    %r11,%rdi
    60ee:	0f 8d b3 01 00 00    	jge    62a7 <verify+0x317>
    60f4:	0f 1f 40 00          	nopl   0x0(%rax)
    60f8:	48 83 c5 01          	add    $0x1,%rbp
    60fc:	49 39 ea             	cmp    %rbp,%r10
    60ff:	0f 8e a8 00 00 00    	jle    61ad <verify+0x21d>
    6105:	49 8b 97 38 02 00 00 	mov    0x238(%r15),%rdx
    610c:	48 89 e8             	mov    %rbp,%rax
    610f:	48 c1 e0 05          	shl    $0x5,%rax
    6113:	49 03 85 38 02 00 00 	add    0x238(%r13),%rax
    611a:	4c 01 f2             	add    %r14,%rdx
    611d:	48 8b 08             	mov    (%rax),%rcx
    6120:	48 8b 78 10          	mov    0x10(%rax),%rdi
    6124:	48 8b 32             	mov    (%rdx),%rsi
    6127:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    612b:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    612f:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    6133:	48 8b 50 08          	mov    0x8(%rax),%rdx
    6137:	48 8b 40 18          	mov    0x18(%rax),%rax
    613b:	48 39 f1             	cmp    %rsi,%rcx
    613e:	7c 98                	jl     60d8 <verify+0x148>
    6140:	0f 8e 4a 01 00 00    	jle    6290 <verify+0x300>
    6146:	4c 39 c2             	cmp    %r8,%rdx
    6149:	0f 8f f9 00 00 00    	jg     6248 <verify+0x2b8>
    614f:	75 a7                	jne    60f8 <verify+0x168>
    6151:	4c 39 df             	cmp    %r11,%rdi
    6154:	7f a2                	jg     60f8 <verify+0x168>
    6156:	49 39 c1             	cmp    %rax,%r9
    6159:	7c 9d                	jl     60f8 <verify+0x168>
    615b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6160:	49 89 c1             	mov    %rax,%r9
    6163:	48 89 f9             	mov    %rdi,%rcx
    6166:	48 89 f2             	mov    %rsi,%rdx
    6169:	bf 01 00 00 00       	mov    $0x1,%edi
    616e:	48 8d 35 13 13 00 00 	lea    0x1313(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    6175:	31 c0                	xor    %eax,%eax
    6177:	48 83 c5 01          	add    $0x1,%rbp
    617b:	e8 d0 c2 ff ff       	call   2450 <__printf_chk@plt>
    6180:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6185:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    618a:	4c 03 28             	add    (%rax),%r13
    618d:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6192:	4d 8b 95 48 02 00 00 	mov    0x248(%r13),%r10
    6199:	4c 8b 20             	mov    (%rax),%r12
    619c:	48 8b 04 24          	mov    (%rsp),%rax
    61a0:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    61a4:	49 39 ea             	cmp    %rbp,%r10
    61a7:	0f 8f 58 ff ff ff    	jg     6105 <verify+0x175>
    61ad:	48 89 da             	mov    %rbx,%rdx
    61b0:	49 3b 9f 48 02 00 00 	cmp    0x248(%r15),%rbx
    61b7:	7d 14                	jge    61cd <verify+0x23d>
    61b9:	4d 8b b5 48 02 00 00 	mov    0x248(%r13),%r14
    61c0:	48 83 c2 01          	add    $0x1,%rdx
    61c4:	4d 85 f6             	test   %r14,%r14
    61c7:	0f 8f e3 fe ff ff    	jg     60b0 <verify+0x120>
    61cd:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    61d2:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    61d7:	48 83 c3 01          	add    $0x1,%rbx
    61db:	39 58 08             	cmp    %ebx,0x8(%rax)
    61de:	0f 8f 54 fe ff ff    	jg     6038 <verify+0xa8>
    61e4:	44 8b 74 24 38       	mov    0x38(%rsp),%r14d
    61e9:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
    61ee:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    61f3:	48 81 04 24 80 02 00 00 	addq   $0x280,(%rsp)
    61fb:	41 83 c6 01          	add    $0x1,%r14d
    61ff:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    6203:	0f 8f f0 fd ff ff    	jg     5ff9 <verify+0x69>
    6209:	45 89 fe             	mov    %r15d,%r14d
    620c:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    6211:	44 8b 7c 24 34       	mov    0x34(%rsp),%r15d
    6216:	48 81 44 24 08 b0 00 00 00 	addq   $0xb0,0x8(%rsp)
    621f:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6224:	41 39 c7             	cmp    %eax,%r15d
    6227:	0f 84 88 00 00 00    	je     62b5 <verify+0x325>
    622d:	41 89 c4             	mov    %eax,%r12d
    6230:	e9 91 fd ff ff       	jmp    5fc6 <verify+0x36>
    6235:	0f 1f 00             	nopl   (%rax)
    6238:	0f 85 ba fe ff ff    	jne    60f8 <verify+0x168>
    623e:	e9 a8 fe ff ff       	jmp    60eb <verify+0x15b>
    6243:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6248:	49 39 c1             	cmp    %rax,%r9
    624b:	7e 09                	jle    6256 <verify+0x2c6>
    624d:	4c 39 df             	cmp    %r11,%rdi
    6250:	0f 8c 0a ff ff ff    	jl     6160 <verify+0x1d0>
    6256:	4c 39 df             	cmp    %r11,%rdi
    6259:	0f 8f 99 fe ff ff    	jg     60f8 <verify+0x168>
    625f:	49 39 c1             	cmp    %rax,%r9
    6262:	0f 8d f8 fe ff ff    	jge    6160 <verify+0x1d0>
    6268:	48 39 f1             	cmp    %rsi,%rcx
    626b:	0f 85 87 fe ff ff    	jne    60f8 <verify+0x168>
    6271:	4c 39 c2             	cmp    %r8,%rdx
    6274:	0f 85 7e fe ff ff    	jne    60f8 <verify+0x168>
    627a:	4c 39 df             	cmp    %r11,%rdi
    627d:	0f 84 dd fe ff ff    	je     6160 <verify+0x1d0>
    6283:	e9 70 fe ff ff       	jmp    60f8 <verify+0x168>
    6288:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6290:	4c 39 c2             	cmp    %r8,%rdx
    6293:	0f 8c 52 fe ff ff    	jl     60eb <verify+0x15b>
    6299:	4c 39 df             	cmp    %r11,%rdi
    629c:	7e c1                	jle    625f <verify+0x2cf>
    629e:	4c 39 c2             	cmp    %r8,%rdx
    62a1:	0f 85 51 fe ff ff    	jne    60f8 <verify+0x168>
    62a7:	49 39 c1             	cmp    %rax,%r9
    62aa:	0f 8f 48 fe ff ff    	jg     60f8 <verify+0x168>
    62b0:	e9 ab fe ff ff       	jmp    6160 <verify+0x1d0>
    62b5:	48 81 44 24 10 b0 00 00 00 	addq   $0xb0,0x10(%rsp)
    62be:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    62c3:	41 8d 46 01          	lea    0x1(%r14),%eax
    62c7:	45 39 e6             	cmp    %r12d,%r14d
    62ca:	74 08                	je     62d4 <verify+0x344>
    62cc:	41 89 c6             	mov    %eax,%r14d
    62cf:	e9 e5 fc ff ff       	jmp    5fb9 <verify+0x29>
    62d4:	48 83 c4 48          	add    $0x48,%rsp
    62d8:	31 c0                	xor    %eax,%eax
    62da:	5b                   	pop    %rbx
    62db:	5d                   	pop    %rbp
    62dc:	41 5c                	pop    %r12
    62de:	41 5d                	pop    %r13
    62e0:	41 5e                	pop    %r14
    62e2:	41 5f                	pop    %r15
    62e4:	c3                   	ret
    62e5:	31 c0                	xor    %eax,%eax
    62e7:	c3                   	ret

Disassembly of section .fini:

00000000000062e8 <_fini>:
    62e8:	f3 0f 1e fa          	endbr64
    62ec:	48 83 ec 08          	sub    $0x8,%rsp
    62f0:	48 83 c4 08          	add    $0x8,%rsp
    62f4:	c3                   	ret
