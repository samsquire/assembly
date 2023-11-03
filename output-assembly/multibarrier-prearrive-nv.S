
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
    2540:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
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
    2580:	f3 0f 1e fa          	endbr64
    2584:	41 57                	push   %r15
    2586:	48 8d 3d 23 4f 00 00 	lea    0x4f23(%rip),%rdi        # 74b0 <_IO_stdin_used+0x4b0>
    258d:	41 56                	push   %r14
    258f:	41 55                	push   %r13
    2591:	41 54                	push   %r12
    2593:	55                   	push   %rbp
    2594:	53                   	push   %rbx
    2595:	48 81 ec b8 00 00 00 	sub    $0xb8,%rsp
    259c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    25a5:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
    25ad:	48 8d 05 ac 11 00 00 	lea    0x11ac(%rip),%rax        # 3760 <barriered_reset>
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
    26c4:	be 18 00 00 00       	mov    $0x18,%esi
    26c9:	bf 0c 00 00 00       	mov    $0xc,%edi
    26ce:	e8 cd fc ff ff       	call   23a0 <calloc@plt>
    26d3:	be 40 01 00 00       	mov    $0x140,%esi
    26d8:	bf 0f 00 00 00       	mov    $0xf,%edi
    26dd:	49 89 c7             	mov    %rax,%r15
    26e0:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    26e5:	e8 b6 fc ff ff       	call   23a0 <calloc@plt>
    26ea:	be 10 00 00 00       	mov    $0x10,%esi
    26ef:	bf 01 00 00 00       	mov    $0x1,%edi
    26f4:	4d 8d 67 e8          	lea    -0x18(%r15),%r12
    26f8:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    26fd:	45 31 ff             	xor    %r15d,%r15d
    2700:	e8 9b fc ff ff       	call   23a0 <calloc@plt>
    2705:	be 10 00 00 00       	mov    $0x10,%esi
    270a:	bf 01 00 00 00       	mov    $0x1,%edi
    270f:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    2715:	48 89 c3             	mov    %rax,%rbx
    2718:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    271d:	e8 7e fc ff ff       	call   23a0 <calloc@plt>
    2722:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2727:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    272f:	48 89 43 08          	mov    %rax,0x8(%rbx)
    2733:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    273a:	4d 89 d5             	mov    %r10,%r13
    273d:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    2742:	4c 89 54 24 58       	mov    %r10,0x58(%rsp)
    2747:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    2750:	be 08 00 00 00       	mov    $0x8,%esi
    2755:	bf 02 00 00 00       	mov    $0x2,%edi
    275a:	44 89 fd             	mov    %r15d,%ebp
    275d:	e8 3e fc ff ff       	call   23a0 <calloc@plt>
    2762:	be 80 00 00 00       	mov    $0x80,%esi
    2767:	bf 01 00 00 00       	mov    $0x1,%edi
    276c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2771:	e8 2a fc ff ff       	call   23a0 <calloc@plt>
    2776:	48 89 c3             	mov    %rax,%rbx
    2779:	44 89 f8             	mov    %r15d,%eax
    277c:	41 83 c7 01          	add    $0x1,%r15d
    2780:	83 e0 01             	and    $0x1,%eax
    2783:	85 c0                	test   %eax,%eax
    2785:	0f 84 24 0e 00 00    	je     35af <main+0x102f>
    278b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    2790:	4d 89 e8             	mov    %r13,%r8
    2793:	89 ea                	mov    %ebp,%edx
    2795:	bf 01 00 00 00       	mov    $0x1,%edi
    279a:	49 8d 8d c0 fe ff ff 	lea    -0x140(%r13),%rcx
    27a1:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    27a9:	48 8d 35 4b 4b 00 00 	lea    0x4b4b(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
    27b0:	48 89 08             	mov    %rcx,(%rax)
    27b3:	44 8d 75 ff          	lea    -0x1(%rbp),%r14d
    27b7:	4c 89 68 08          	mov    %r13,0x8(%rax)
    27bb:	31 c0                	xor    %eax,%eax
    27bd:	e8 8e fc ff ff       	call   2450 <__printf_chk@plt>
    27c2:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    27c7:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    27cc:	4d 89 a5 80 00 00 00 	mov    %r12,0x80(%r13)
    27d3:	45 8b 45 00          	mov    0x0(%r13),%r8d
    27d7:	44 89 f1             	mov    %r14d,%ecx
    27da:	89 ea                	mov    %ebp,%edx
    27dc:	48 8d 35 8d 4d 00 00 	lea    0x4d8d(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    27e3:	bf 01 00 00 00       	mov    $0x1,%edi
    27e8:	31 c0                	xor    %eax,%eax
    27ea:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    27f0:	e8 5b fc ff ff       	call   2450 <__printf_chk@plt>
    27f5:	45 89 b5 28 01 00 00 	mov    %r14d,0x128(%r13)
    27fc:	45 31 f6             	xor    %r14d,%r14d
    27ff:	90                   	nop
    2800:	44 89 f1             	mov    %r14d,%ecx
    2803:	89 ea                	mov    %ebp,%edx
    2805:	48 8d 35 94 4d 00 00 	lea    0x4d94(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    280c:	31 c0                	xor    %eax,%eax
    280e:	bf 01 00 00 00       	mov    $0x1,%edi
    2813:	e8 38 fc ff ff       	call   2450 <__printf_chk@plt>
    2818:	44 89 f1             	mov    %r14d,%ecx
    281b:	4c 89 e0             	mov    %r12,%rax
    281e:	41 83 c6 01          	add    $0x1,%r14d
    2822:	48 d3 e0             	shl    %cl,%rax
    2825:	48 09 03             	or     %rax,(%rbx)
    2828:	41 83 fe 06          	cmp    $0x6,%r14d
    282c:	75 d2                	jne    2800 <main+0x280>
    282e:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    2833:	49 89 9d 20 01 00 00 	mov    %rbx,0x120(%r13)
    283a:	31 db                	xor    %ebx,%ebx
    283c:	be 10 00 00 00       	mov    $0x10,%esi
    2841:	41 89 6d 04          	mov    %ebp,0x4(%r13)
    2845:	bf 64 00 00 00       	mov    $0x64,%edi
    284a:	49 89 45 40          	mov    %rax,0x40(%r13)
    284e:	48 8b 05 f3 51 00 00 	mov    0x51f3(%rip),%rax        # 7a48 <_IO_stdin_used+0xa48>
    2855:	41 c7 45 60 03 00 00 00 	movl   $0x3,0x60(%r13)
    285d:	49 89 45 48          	mov    %rax,0x48(%r13)
    2861:	e8 3a fb ff ff       	call   23a0 <calloc@plt>
    2866:	be 10 00 00 00       	mov    $0x10,%esi
    286b:	bf 64 00 00 00       	mov    $0x64,%edi
    2870:	49 89 85 d8 00 00 00 	mov    %rax,0xd8(%r13)
    2877:	e8 24 fb ff ff       	call   23a0 <calloc@plt>
    287c:	be 28 00 00 00       	mov    $0x28,%esi
    2881:	bf 64 00 00 00       	mov    $0x64,%edi
    2886:	66 0f 6f 15 92 51 00 00 	movdqa 0x5192(%rip),%xmm2        # 7a20 <_IO_stdin_used+0xa20>
    288e:	49 89 85 e0 00 00 00 	mov    %rax,0xe0(%r13)
    2895:	41 0f 29 95 f0 00 00 00 	movaps %xmm2,0xf0(%r13)
    289d:	e8 fe fa ff ff       	call   23a0 <calloc@plt>
    28a2:	be 00 02 00 00       	mov    $0x200,%esi
    28a7:	bf 03 00 00 00       	mov    $0x3,%edi
    28ac:	66 0f 6f 1d 6c 51 00 00 	movdqa 0x516c(%rip),%xmm3        # 7a20 <_IO_stdin_used+0xa20>
    28b4:	49 89 85 00 01 00 00 	mov    %rax,0x100(%r13)
    28bb:	41 0f 11 9d 08 01 00 00 	movups %xmm3,0x108(%r13)
    28c3:	e8 d8 fa ff ff       	call   23a0 <calloc@plt>
    28c8:	89 6c 24 08          	mov    %ebp,0x8(%rsp)
    28cc:	49 89 45 58          	mov    %rax,0x58(%r13)
    28d0:	49 89 c4             	mov    %rax,%r12
    28d3:	44 89 7c 24 28       	mov    %r15d,0x28(%rsp)
    28d8:	48 63 eb             	movslq %ebx,%rbp
    28db:	be 20 00 00 00       	mov    $0x20,%esi
    28e0:	bf 0c 00 00 00       	mov    $0xc,%edi
    28e5:	49 89 ef             	mov    %rbp,%r15
    28e8:	48 8d 05 31 0e 00 00 	lea    0xe31(%rip),%rax        # 3720 <do_protected_write>
    28ef:	49 c1 e7 09          	shl    $0x9,%r15
    28f3:	4d 01 fc             	add    %r15,%r12
    28f6:	49 89 84 24 20 01 00 00 	mov    %rax,0x120(%r12)
    28fe:	e8 9d fa ff ff       	call   23a0 <calloc@plt>
    2903:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    2907:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    290c:	49 89 c6             	mov    %rax,%r14
    290f:	49 89 84 24 68 01 00 00 	mov    %rax,0x168(%r12)
    2917:	4c 8d 60 40          	lea    0x40(%rax),%r12
    291b:	be 08 00 00 00       	mov    $0x8,%esi
    2920:	bf 01 00 00 00       	mov    $0x1,%edi
    2925:	49 83 c6 20          	add    $0x20,%r14
    2929:	e8 72 fa ff ff       	call   23a0 <calloc@plt>
    292e:	be 08 00 00 00       	mov    $0x8,%esi
    2933:	bf 01 00 00 00       	mov    $0x1,%edi
    2938:	48 89 c5             	mov    %rax,%rbp
    293b:	e8 60 fa ff ff       	call   23a0 <calloc@plt>
    2940:	be 18 00 00 00       	mov    $0x18,%esi
    2945:	bf 02 00 00 00       	mov    $0x2,%edi
    294a:	48 89 c3             	mov    %rax,%rbx
    294d:	e8 4e fa ff ff       	call   23a0 <calloc@plt>
    2952:	66 0f 6f 05 d6 50 00 00 	movdqa 0x50d6(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
    295a:	48 8d 70 18          	lea    0x18(%rax),%rsi
    295e:	49 89 46 e0          	mov    %rax,-0x20(%r14)
    2962:	49 89 76 e8          	mov    %rsi,-0x18(%r14)
    2966:	48 89 28             	mov    %rbp,(%rax)
    2969:	48 89 58 18          	mov    %rbx,0x18(%rax)
    296d:	0f 11 40 08          	movups %xmm0,0x8(%rax)
    2971:	0f 11 40 20          	movups %xmm0,0x20(%rax)
    2975:	4d 39 f4             	cmp    %r14,%r12
    2978:	75 a1                	jne    291b <main+0x39b>
    297a:	be 01 00 00 00       	mov    $0x1,%esi
    297f:	bf 00 01 00 00       	mov    $0x100,%edi
    2984:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    2988:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    298d:	e8 0e fa ff ff       	call   23a0 <calloc@plt>
    2992:	bf 18 00 00 00       	mov    $0x18,%edi
    2997:	49 89 c4             	mov    %rax,%r12
    299a:	e8 71 fa ff ff       	call   2410 <malloc@plt>
    299f:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    29a4:	4c 89 e7             	mov    %r12,%rdi
    29a7:	41 89 d9             	mov    %ebx,%r9d
    29aa:	ba 00 01 00 00       	mov    $0x100,%edx
    29af:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    29b4:	be 01 00 00 00       	mov    $0x1,%esi
    29b9:	31 c0                	xor    %eax,%eax
    29bb:	48 8d 0d fe 4b 00 00 	lea    0x4bfe(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    29c2:	e8 59 fb ff ff       	call   2520 <__sprintf_chk@plt>
    29c7:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    29cc:	49 63 45 00          	movslq 0x0(%r13),%rax
    29d0:	8d 4b 01             	lea    0x1(%rbx),%ecx
    29d3:	be 20 00 00 00       	mov    $0x20,%esi
    29d8:	bf 63 00 00 00       	mov    $0x63,%edi
    29dd:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
    29e1:	4d 89 22             	mov    %r12,(%r10)
    29e4:	4d 8b 65 58          	mov    0x58(%r13),%r12
    29e8:	49 89 6a 10          	mov    %rbp,0x10(%r10)
    29ec:	4b 8d 2c 3c          	lea    (%r12,%r15,1),%rbp
    29f0:	49 89 42 08          	mov    %rax,0x8(%r10)
    29f4:	89 8d 88 01 00 00    	mov    %ecx,0x188(%rbp)
    29fa:	4c 89 95 80 01 00 00 	mov    %r10,0x180(%rbp)
    2a01:	48 c7 85 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%rbp)
    2a0c:	89 44 24 18          	mov    %eax,0x18(%rsp)
    2a10:	e8 8b f9 ff ff       	call   23a0 <calloc@plt>
    2a15:	8b 54 24 18          	mov    0x18(%rsp),%edx
    2a19:	83 fb 01             	cmp    $0x1,%ebx
    2a1c:	89 5d 00             	mov    %ebx,0x0(%rbp)
    2a1f:	48 89 85 48 01 00 00 	mov    %rax,0x148(%rbp)
    2a26:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
    2a2a:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2a34:	48 89 85 38 01 00 00 	mov    %rax,0x138(%rbp)
    2a3b:	48 b8 01 00 00 00 0c 00 00 00 	movabs $0xc00000001,%rax
    2a45:	48 c7 85 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%rbp)
    2a50:	89 95 30 01 00 00    	mov    %edx,0x130(%rbp)
    2a56:	4c 89 ad 28 01 00 00 	mov    %r13,0x128(%rbp)
    2a5d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
    2a67:	c7 85 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%rbp)
    2a71:	48 89 85 78 01 00 00 	mov    %rax,0x178(%rbp)
    2a78:	0f 84 19 0b 00 00    	je     3597 <main+0x1017>
    2a7e:	8b 54 24 08          	mov    0x8(%rsp),%edx
    2a82:	39 da                	cmp    %ebx,%edx
    2a84:	75 5a                	jne    2ae0 <main+0x560>
    2a86:	8b 74 24 20          	mov    0x20(%rsp),%esi
    2a8a:	85 f6                	test   %esi,%esi
    2a8c:	75 52                	jne    2ae0 <main+0x560>
    2a8e:	48 8d 35 53 4b 00 00 	lea    0x4b53(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2a95:	bf 01 00 00 00       	mov    $0x1,%edi
    2a9a:	31 c0                	xor    %eax,%eax
    2a9c:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
    2aa0:	e8 ab f9 ff ff       	call   2450 <__printf_chk@plt>
    2aa5:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    2aaa:	4d 8b 65 58          	mov    0x58(%r13),%r12
    2aae:	c7 44 24 20 01 00 00 00 	movl   $0x1,0x20(%rsp)
    2ab6:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
    2aba:	49 89 85 c0 00 00 00 	mov    %rax,0xc0(%r13)
    2ac1:	48 8d 05 98 31 00 00 	lea    0x3198(%rip),%rax        # 5c60 <barriered_work_ingest>
    2ac8:	4b 89 84 3c 18 01 00 00 	mov    %rax,0x118(%r12,%r15,1)
    2ad0:	83 f9 03             	cmp    $0x3,%ecx
    2ad3:	74 1e                	je     2af3 <main+0x573>
    2ad5:	bb 01 00 00 00       	mov    $0x1,%ebx
    2ada:	e9 f9 fd ff ff       	jmp    28d8 <main+0x358>
    2adf:	90                   	nop
    2ae0:	48 8d 05 a9 2c 00 00 	lea    0x2ca9(%rip),%rax        # 5790 <barriered_work>
    2ae7:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
    2aee:	83 f9 03             	cmp    $0x3,%ecx
    2af1:	75 e2                	jne    2ad5 <main+0x555>
    2af3:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
    2afd:	66 0f 6f 64 24 30    	movdqa 0x30(%rsp),%xmm4
    2b03:	41 c7 84 24 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r12)
    2b0f:	49 89 84 24 34 05 00 00 	mov    %rax,0x534(%r12)
    2b17:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
    2b1c:	41 c7 84 24 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%r12)
    2b28:	41 8b 45 00          	mov    0x0(%r13),%eax
    2b2c:	4d 89 ac 24 28 05 00 00 	mov    %r13,0x528(%r12)
    2b34:	49 81 c5 40 01 00 00 	add    $0x140,%r13
    2b3b:	41 89 84 24 30 05 00 00 	mov    %eax,0x530(%r12)
    2b43:	41 c7 84 24 7c 05 00 00 0c 00 00 00 	movl   $0xc,0x57c(%r12)
    2b4f:	41 c7 84 24 3c 05 00 00 03 00 00 00 	movl   $0x3,0x53c(%r12)
    2b5b:	41 0f 11 a4 24 18 05 00 00 	movups %xmm4,0x518(%r12)
    2b64:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    2b69:	41 83 ff 0f          	cmp    $0xf,%r15d
    2b6d:	0f 85 dd fb ff ff    	jne    2750 <main+0x1d0>
    2b73:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    2b78:	ba 0d 00 00 00       	mov    $0xd,%edx
    2b7d:	48 8d 35 94 47 00 00 	lea    0x4794(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2b84:	31 c0                	xor    %eax,%eax
    2b86:	bf 01 00 00 00       	mov    $0x1,%edi
    2b8b:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    2b90:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2b95:	e8 b6 f8 ff ff       	call   2450 <__printf_chk@plt>
    2b9a:	be 08 00 00 00       	mov    $0x8,%esi
    2b9f:	bf 02 00 00 00       	mov    $0x2,%edi
    2ba4:	e8 f7 f7 ff ff       	call   23a0 <calloc@plt>
    2ba9:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2bae:	bf 0f 00 00 00       	mov    $0xf,%edi
    2bb3:	4d 8d ba 40 10 00 00 	lea    0x1040(%r10),%r15
    2bba:	4d 8d b2 80 02 00 00 	lea    0x280(%r10),%r14
    2bc1:	49 89 82 80 10 00 00 	mov    %rax,0x1080(%r10)
    2bc8:	4c 89 38             	mov    %r15,(%rax)
    2bcb:	49 8d 8a c0 03 00 00 	lea    0x3c0(%r10),%rcx
    2bd2:	49 8d 92 40 06 00 00 	lea    0x640(%r10),%rdx
    2bd9:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2bdd:	49 8b 42 58          	mov    0x58(%r10),%rax
    2be1:	4d 8d 9a c0 08 00 00 	lea    0x8c0(%r10),%r11
    2be8:	4d 8d 8a 00 0a 00 00 	lea    0xa00(%r10),%r9
    2bef:	49 8d b2 00 05 00 00 	lea    0x500(%r10),%rsi
    2bf6:	49 8d 9a 80 07 00 00 	lea    0x780(%r10),%rbx
    2bfd:	41 c7 82 88 10 00 00 02 00 00 00 	movl   $0x2,0x1088(%r10)
    2c08:	48 89 4c 24 58       	mov    %rcx,0x58(%rsp)
    2c0d:	4d 8d 82 40 0b 00 00 	lea    0xb40(%r10),%r8
    2c14:	4d 8d aa 80 0c 00 00 	lea    0xc80(%r10),%r13
    2c1b:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    2c20:	4d 8d a2 c0 0d 00 00 	lea    0xdc0(%r10),%r12
    2c27:	41 c7 82 40 10 00 00 00 00 00 00 	movl   $0x0,0x1040(%r10)
    2c32:	41 c7 82 a0 10 00 00 03 00 00 00 	movl   $0x3,0x10a0(%r10)
    2c3d:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2c47:	49 8d 82 40 01 00 00 	lea    0x140(%r10),%rax
    2c4e:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2c53:	49 8b 82 98 01 00 00 	mov    0x198(%r10),%rax
    2c5a:	4c 89 5c 24 20       	mov    %r11,0x20(%rsp)
    2c5f:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2c69:	49 8b 82 d8 02 00 00 	mov    0x2d8(%r10),%rax
    2c70:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    2c75:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2c7f:	49 8b 82 18 04 00 00 	mov    0x418(%r10),%rax
    2c86:	4c 89 7c 24 70       	mov    %r15,0x70(%rsp)
    2c8b:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2c95:	49 8b 82 58 05 00 00 	mov    0x558(%r10),%rax
    2c9c:	4c 89 74 24 78       	mov    %r14,0x78(%rsp)
    2ca1:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cab:	49 8b 82 98 06 00 00 	mov    0x698(%r10),%rax
    2cb2:	48 89 74 24 50       	mov    %rsi,0x50(%rsp)
    2cb7:	be 38 00 00 00       	mov    $0x38,%esi
    2cbc:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cc6:	49 8b 82 d8 07 00 00 	mov    0x7d8(%r10),%rax
    2ccd:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    2cd2:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cdc:	49 8b 82 18 09 00 00 	mov    0x918(%r10),%rax
    2ce3:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2ced:	49 8b 82 58 0a 00 00 	mov    0xa58(%r10),%rax
    2cf4:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    2cf9:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d03:	49 8b 82 98 0b 00 00 	mov    0xb98(%r10),%rax
    2d0a:	4c 89 94 24 80 00 00 00 	mov    %r10,0x80(%rsp)
    2d12:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d1c:	49 8b 82 d8 0c 00 00 	mov    0xcd8(%r10),%rax
    2d23:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    2d28:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d32:	49 8b 82 18 0e 00 00 	mov    0xe18(%r10),%rax
    2d39:	4c 89 64 24 10       	mov    %r12,0x10(%rsp)
    2d3e:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d48:	e8 53 f6 ff ff       	call   23a0 <calloc@plt>
    2d4d:	be 38 00 00 00       	mov    $0x38,%esi
    2d52:	bf 0f 00 00 00       	mov    $0xf,%edi
    2d57:	49 89 c4             	mov    %rax,%r12
    2d5a:	e8 41 f6 ff ff       	call   23a0 <calloc@plt>
    2d5f:	be 38 00 00 00       	mov    $0x38,%esi
    2d64:	bf 0f 00 00 00       	mov    $0xf,%edi
    2d69:	48 89 c3             	mov    %rax,%rbx
    2d6c:	e8 2f f6 ff ff       	call   23a0 <calloc@plt>
    2d71:	be 38 00 00 00       	mov    $0x38,%esi
    2d76:	bf 0f 00 00 00       	mov    $0xf,%edi
    2d7b:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    2d83:	e8 18 f6 ff ff       	call   23a0 <calloc@plt>
    2d88:	be 08 00 00 00       	mov    $0x8,%esi
    2d8d:	bf 0f 00 00 00       	mov    $0xf,%edi
    2d92:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
    2d9a:	e8 01 f6 ff ff       	call   23a0 <calloc@plt>
    2d9f:	be 08 00 00 00       	mov    $0x8,%esi
    2da4:	bf 0f 00 00 00       	mov    $0xf,%edi
    2da9:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
    2db1:	49 89 c5             	mov    %rax,%r13
    2db4:	48 8b 05 95 4c 00 00 	mov    0x4c95(%rip),%rax        # 7a50 <_IO_stdin_used+0xa50>
    2dbb:	41 c7 82 08 0f 00 00 00 00 00 00 	movl   $0x0,0xf08(%r10)
    2dc6:	49 89 82 60 0f 00 00 	mov    %rax,0xf60(%r10)
    2dcd:	e8 ce f5 ff ff       	call   23a0 <calloc@plt>
    2dd2:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    2dd7:	48 8b 4c 24 58       	mov    0x58(%rsp),%rcx
    2ddc:	48 8b 74 24 50       	mov    0x50(%rsp),%rsi
    2de1:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    2de6:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2dea:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    2def:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    2df4:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2df8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    2dfd:	4c 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%r10
    2e05:	48 89 48 18          	mov    %rcx,0x18(%rax)
    2e09:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    2e0e:	48 89 70 20          	mov    %rsi,0x20(%rax)
    2e12:	48 8d 35 0e 45 00 00 	lea    0x450e(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2e19:	48 89 78 30          	mov    %rdi,0x30(%rax)
    2e1d:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    2e22:	4d 8d b2 00 0f 00 00 	lea    0xf00(%r10),%r14
    2e29:	4c 89 10             	mov    %r10,(%rax)
    2e2c:	48 89 78 50          	mov    %rdi,0x50(%rax)
    2e30:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    2e35:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2e39:	ba 0c 00 00 00       	mov    $0xc,%edx
    2e3e:	48 89 78 58          	mov    %rdi,0x58(%rax)
    2e42:	49 8d ba 80 11 00 00 	lea    0x1180(%r10),%rdi
    2e49:	4c 89 58 38          	mov    %r11,0x38(%rax)
    2e4d:	4c 89 48 40          	mov    %r9,0x40(%rax)
    2e51:	4c 89 40 48          	mov    %r8,0x48(%rax)
    2e55:	4c 89 70 60          	mov    %r14,0x60(%rax)
    2e59:	4c 89 78 68          	mov    %r15,0x68(%rax)
    2e5d:	4c 8d 3d 6c 09 00 00 	lea    0x96c(%rip),%r15        # 37d0 <barriered_thread>
    2e64:	48 89 78 70          	mov    %rdi,0x70(%rax)
    2e68:	49 89 82 40 0f 00 00 	mov    %rax,0xf40(%r10)
    2e6f:	31 c0                	xor    %eax,%eax
    2e71:	41 c7 82 48 0f 00 00 0c 00 00 00 	movl   $0xc,0xf48(%r10)
    2e7c:	41 c7 82 50 0f 00 00 02 00 00 00 	movl   $0x2,0xf50(%r10)
    2e87:	41 c7 82 00 0f 00 00 00 00 00 00 	movl   $0x0,0xf00(%r10)
    2e92:	48 89 bc 24 80 00 00 00 	mov    %rdi,0x80(%rsp)
    2e9a:	bf 01 00 00 00       	mov    $0x1,%edi
    2e9f:	4c 89 94 24 98 00 00 00 	mov    %r10,0x98(%rsp)
    2ea7:	e8 a4 f5 ff ff       	call   2450 <__printf_chk@plt>
    2eac:	48 8d b3 a0 02 00 00 	lea    0x2a0(%rbx),%rsi
    2eb3:	49 8d 7d 60          	lea    0x60(%r13),%rdi
    2eb7:	4c 89 f1             	mov    %r14,%rcx
    2eba:	4c 89 eb             	mov    %r13,%rbx
    2ebd:	45 31 f6             	xor    %r14d,%r14d
    2ec0:	48 8d 15 79 0c 00 00 	lea    0xc79(%rip),%rdx        # 3b40 <timer_thread>
    2ec7:	e8 a4 f5 ff ff       	call   2470 <pthread_create@plt>
    2ecc:	45 89 f5             	mov    %r14d,%r13d
    2ecf:	49 89 de             	mov    %rbx,%r14
    2ed2:	c7 45 08 01 00 00 00 	movl   $0x1,0x8(%rbp)
    2ed9:	44 89 ea             	mov    %r13d,%edx
    2edc:	bf 01 00 00 00       	mov    $0x1,%edi
    2ee1:	31 c0                	xor    %eax,%eax
    2ee3:	c7 45 64 01 00 00 00 	movl   $0x1,0x64(%rbp)
    2eea:	48 8d 35 17 47 00 00 	lea    0x4717(%rip),%rsi        # 7608 <_IO_stdin_used+0x608>
    2ef1:	41 83 c5 01          	add    $0x1,%r13d
    2ef5:	e8 56 f5 ff ff       	call   2450 <__printf_chk@plt>
    2efa:	48 89 e9             	mov    %rbp,%rcx
    2efd:	4c 89 e6             	mov    %r12,%rsi
    2f00:	48 89 df             	mov    %rbx,%rdi
    2f03:	4c 89 fa             	mov    %r15,%rdx
    2f06:	48 81 c5 40 01 00 00 	add    $0x140,%rbp
    2f0d:	48 83 c3 08          	add    $0x8,%rbx
    2f11:	49 83 c4 38          	add    $0x38,%r12
    2f15:	e8 56 f5 ff ff       	call   2470 <pthread_create@plt>
    2f1a:	48 8b 55 e0          	mov    -0x20(%rbp),%rdx
    2f1e:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    2f22:	be 08 00 00 00       	mov    $0x8,%esi
    2f27:	e8 b4 f3 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    2f2c:	41 83 fd 0c          	cmp    $0xc,%r13d
    2f30:	75 a0                	jne    2ed2 <main+0x952>
    2f32:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    2f3a:	48 8b 1d 17 4b 00 00 	mov    0x4b17(%rip),%rbx        # 7a58 <_IO_stdin_used+0xa58>
    2f41:	be d8 00 00 00       	mov    $0xd8,%esi
    2f46:	4d 89 f5             	mov    %r14,%r13
    2f49:	bf 01 00 00 00       	mov    $0x1,%edi
    2f4e:	49 89 9a a0 10 00 00 	mov    %rbx,0x10a0(%r10)
    2f55:	41 c7 82 48 10 00 00 02 00 00 00 	movl   $0x2,0x1048(%r10)
    2f60:	e8 3b f4 ff ff       	call   23a0 <calloc@plt>
    2f65:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    2f6d:	be 00 08 00 00       	mov    $0x800,%esi
    2f72:	31 ff                	xor    %edi,%edi
    2f74:	49 89 82 08 11 00 00 	mov    %rax,0x1108(%r10)
    2f7b:	e8 30 f5 ff ff       	call   24b0 <eventfd@plt>
    2f80:	be 08 00 00 00       	mov    $0x8,%esi
    2f85:	bf 0c 00 00 00       	mov    $0xc,%edi
    2f8a:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    2f92:	41 89 82 10 11 00 00 	mov    %eax,0x1110(%r10)
    2f99:	e8 02 f4 ff ff       	call   23a0 <calloc@plt>
    2f9e:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    2fa3:	4c 8b 4c 24 30       	mov    0x30(%rsp),%r9
    2fa8:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    2fb0:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    2fb5:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    2fba:	4c 8b 74 24 78       	mov    0x78(%rsp),%r14
    2fbf:	4c 89 58 48          	mov    %r11,0x48(%rax)
    2fc3:	48 8b 6c 24 58       	mov    0x58(%rsp),%rbp
    2fc8:	4c 8b 7c 24 60       	mov    0x60(%rsp),%r15
    2fcd:	4c 89 48 50          	mov    %r9,0x50(%rax)
    2fd1:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    2fd6:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    2fdb:	4c 89 40 58          	mov    %r8,0x58(%rax)
    2fdf:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    2fe4:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    2fe9:	4c 89 10             	mov    %r10,(%rax)
    2fec:	49 89 82 80 10 00 00 	mov    %rax,0x1080(%r10)
    2ff3:	41 c7 82 88 10 00 00 0c 00 00 00 	movl   $0xc,0x1088(%r10)
    2ffe:	41 c7 82 40 10 00 00 0d 00 00 00 	movl   $0xd,0x1040(%r10)
    3009:	4c 89 70 10          	mov    %r14,0x10(%rax)
    300d:	48 89 68 18          	mov    %rbp,0x18(%rax)
    3011:	4c 89 60 20          	mov    %r12,0x20(%rax)
    3015:	48 89 78 28          	mov    %rdi,0x28(%rax)
    3019:	bf 01 00 00 00       	mov    $0x1,%edi
    301e:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3022:	48 89 70 38          	mov    %rsi,0x38(%rax)
    3026:	48 8d 35 18 43 00 00 	lea    0x4318(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    302d:	48 89 50 40          	mov    %rdx,0x40(%rax)
    3031:	ba 0d 00 00 00       	mov    $0xd,%edx
    3036:	4c 89 78 08          	mov    %r15,0x8(%rax)
    303a:	31 c0                	xor    %eax,%eax
    303c:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    3041:	e8 0a f4 ff ff       	call   2450 <__printf_chk@plt>
    3046:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    304b:	49 8d 7d 68          	lea    0x68(%r13),%rdi
    304f:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    3057:	48 8d 15 32 1d 00 00 	lea    0x1d32(%rip),%rdx        # 4d90 <io_thread>
    305e:	48 05 d8 02 00 00    	add    $0x2d8,%rax
    3064:	48 89 c6             	mov    %rax,%rsi
    3067:	e8 04 f4 ff ff       	call   2470 <pthread_create@plt>
    306c:	ba 0e 00 00 00       	mov    $0xe,%edx
    3071:	48 8d 35 e4 42 00 00 	lea    0x42e4(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    3078:	31 c0                	xor    %eax,%eax
    307a:	bf 01 00 00 00       	mov    $0x1,%edi
    307f:	e8 cc f3 ff ff       	call   2450 <__printf_chk@plt>
    3084:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    3089:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    308e:	be 08 00 00 00       	mov    $0x8,%esi
    3093:	bf 0c 00 00 00       	mov    $0xc,%edi
    3098:	49 89 9a e0 11 00 00 	mov    %rbx,0x11e0(%r10)
    309f:	31 db                	xor    %ebx,%ebx
    30a1:	41 c7 82 88 11 00 00 03 00 00 00 	movl   $0x3,0x1188(%r10)
    30ac:	49 89 82 40 12 00 00 	mov    %rax,0x1240(%r10)
    30b3:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    30b8:	e8 e3 f2 ff ff       	call   23a0 <calloc@plt>
    30bd:	4c 8b 54 24 48       	mov    0x48(%rsp),%r10
    30c2:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    30c7:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    30cc:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    30d1:	4c 89 70 10          	mov    %r14,0x10(%rax)
    30d5:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    30da:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    30df:	4c 89 10             	mov    %r10,(%rax)
    30e2:	4c 8b 4c 24 30       	mov    0x30(%rsp),%r9
    30e7:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    30ec:	48 89 68 18          	mov    %rbp,0x18(%rax)
    30f0:	48 8d 2d a0 42 00 00 	lea    0x42a0(%rip),%rbp        # 7397 <_IO_stdin_used+0x397>
    30f7:	4c 89 60 20          	mov    %r12,0x20(%rax)
    30fb:	4c 8d a4 24 a0 00 00 00 	lea    0xa0(%rsp),%r12
    3103:	48 89 78 28          	mov    %rdi,0x28(%rax)
    3107:	49 8d 7d 70          	lea    0x70(%r13),%rdi
    310b:	48 89 48 30          	mov    %rcx,0x30(%rax)
    310f:	48 8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%rcx
    3117:	48 89 70 38          	mov    %rsi,0x38(%rax)
    311b:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
    3123:	48 89 50 40          	mov    %rdx,0x40(%rax)
    3127:	48 8d 15 52 09 00 00 	lea    0x952(%rip),%rdx        # 3a80 <external_thread>
    312e:	4c 89 58 48          	mov    %r11,0x48(%rax)
    3132:	48 81 c6 10 03 00 00 	add    $0x310,%rsi
    3139:	4c 89 48 50          	mov    %r9,0x50(%rax)
    313d:	4c 89 40 58          	mov    %r8,0x58(%rax)
    3141:	49 89 82 c0 11 00 00 	mov    %rax,0x11c0(%r10)
    3148:	4c 89 78 08          	mov    %r15,0x8(%rax)
    314c:	48 8b 05 0d 49 00 00 	mov    0x490d(%rip),%rax        # 7a60 <_IO_stdin_used+0xa60>
    3153:	41 c7 82 80 11 00 00 0e 00 00 00 	movl   $0xe,0x1180(%r10)
    315e:	49 89 82 c8 11 00 00 	mov    %rax,0x11c8(%r10)
    3165:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    316a:	e8 01 f3 ff ff       	call   2470 <pthread_create@plt>
    316f:	48 8d 3d 03 42 00 00 	lea    0x4203(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    3176:	e8 75 f1 ff ff       	call   22f0 <puts@plt>
    317b:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    3180:	49 8b 7c dd 00       	mov    0x0(%r13,%rbx,8),%rdi
    3185:	4c 89 e6             	mov    %r12,%rsi
    3188:	e8 63 f3 ff ff       	call   24f0 <pthread_join@plt>
    318d:	89 da                	mov    %ebx,%edx
    318f:	48 89 ee             	mov    %rbp,%rsi
    3192:	bf 01 00 00 00       	mov    $0x1,%edi
    3197:	31 c0                	xor    %eax,%eax
    3199:	48 83 c3 01          	add    $0x1,%rbx
    319d:	e8 ae f2 ff ff       	call   2450 <__printf_chk@plt>
    31a2:	48 83 fb 0f          	cmp    $0xf,%rbx
    31a6:	75 d8                	jne    3180 <main+0xc00>
    31a8:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    31ad:	4d 8d 6e 58          	lea    0x58(%r14),%r13
    31b1:	45 31 ff             	xor    %r15d,%r15d
    31b4:	31 db                	xor    %ebx,%ebx
    31b6:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    31be:	31 ed                	xor    %ebp,%ebp
    31c0:	45 31 c9             	xor    %r9d,%r9d
    31c3:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    31c8:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    31cd:	4d 89 ee             	mov    %r13,%r14
    31d0:	4d 89 fd             	mov    %r15,%r13
    31d3:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    31d7:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    31dc:	89 f8                	mov    %edi,%eax
    31de:	41 89 fc             	mov    %edi,%r12d
    31e1:	83 c7 01             	add    $0x1,%edi
    31e4:	83 e0 01             	and    $0x1,%eax
    31e7:	41 83 ec 01          	sub    $0x1,%r12d
    31eb:	89 7c 24 10          	mov    %edi,0x10(%rsp)
    31ef:	85 c0                	test   %eax,%eax
    31f1:	44 0f 44 e7          	cmove  %edi,%r12d
    31f5:	bf 0a 00 00 00       	mov    $0xa,%edi
    31fa:	e8 d1 f0 ff ff       	call   22d0 <putchar@plt>
    31ff:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3204:	bf 01 00 00 00       	mov    $0x1,%edi
    3209:	48 8d 35 9b 41 00 00 	lea    0x419b(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    3210:	48 8b 10             	mov    (%rax),%rdx
    3213:	31 c0                	xor    %eax,%eax
    3215:	e8 36 f2 ff ff       	call   2450 <__printf_chk@plt>
    321a:	49 63 56 08          	movslq 0x8(%r14),%rdx
    321e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3223:	85 d2                	test   %edx,%edx
    3225:	0f 8e f4 03 00 00    	jle    361f <main+0x109f>
    322b:	49 8b 06             	mov    (%r14),%rax
    322e:	48 c1 e2 09          	shl    $0x9,%rdx
    3232:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3236:	31 d2                	xor    %edx,%edx
    3238:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3240:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    3247:	48 05 00 02 00 00    	add    $0x200,%rax
    324d:	48 39 f0             	cmp    %rsi,%rax
    3250:	75 ee                	jne    3240 <main+0xcc0>
    3252:	4d 63 e4             	movslq %r12d,%r12
    3255:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    325a:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    325e:	48 c1 e0 06          	shl    $0x6,%rax
    3262:	48 01 f8             	add    %rdi,%rax
    3265:	48 63 70 60          	movslq 0x60(%rax),%rsi
    3269:	85 f6                	test   %esi,%esi
    326b:	7e 25                	jle    3292 <main+0xd12>
    326d:	48 8b 40 58          	mov    0x58(%rax),%rax
    3271:	48 c1 e6 09          	shl    $0x9,%rsi
    3275:	48 01 c6             	add    %rax,%rsi
    3278:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3280:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    3287:	48 05 00 02 00 00    	add    $0x200,%rax
    328d:	48 39 f0             	cmp    %rsi,%rax
    3290:	75 ee                	jne    3280 <main+0xd00>
    3292:	48 8d 35 27 41 00 00 	lea    0x4127(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    3299:	bf 01 00 00 00       	mov    $0x1,%edi
    329e:	31 c0                	xor    %eax,%eax
    32a0:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    32a5:	e8 a6 f1 ff ff       	call   2450 <__printf_chk@plt>
    32aa:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    32af:	bf 01 00 00 00       	mov    $0x1,%edi
    32b4:	48 8b 30             	mov    (%rax),%rsi
    32b7:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    32c1:	48 f7 ee             	imul   %rsi
    32c4:	48 c1 fe 3f          	sar    $0x3f,%rsi
    32c8:	31 c0                	xor    %eax,%eax
    32ca:	48 d1 fa             	sar    %rdx
    32cd:	48 29 f2             	sub    %rsi,%rdx
    32d0:	48 8d 35 59 43 00 00 	lea    0x4359(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    32d7:	e8 74 f1 ff ff       	call   2450 <__printf_chk@plt>
    32dc:	bf 0a 00 00 00       	mov    $0xa,%edi
    32e1:	e8 ea ef ff ff       	call   22d0 <putchar@plt>
    32e6:	49 63 46 08          	movslq 0x8(%r14),%rax
    32ea:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    32ef:	85 c0                	test   %eax,%eax
    32f1:	0f 8e cd 00 00 00    	jle    33c4 <main+0xe44>
    32f7:	49 8b 16             	mov    (%r14),%rdx
    32fa:	48 c1 e0 09          	shl    $0x9,%rax
    32fe:	48 8d 34 10          	lea    (%rax,%rdx,1),%rsi
    3302:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3308:	48 8b 82 68 01 00 00 	mov    0x168(%rdx),%rax
    330f:	4c 03 8a 08 01 00 00 	add    0x108(%rdx),%r9
    3316:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    331d:	4c 03 ba 60 ff ff ff 	add    -0xa0(%rdx),%r15
    3324:	4c 03 aa 70 ff ff ff 	add    -0x90(%rdx),%r13
    332b:	48 03 68 10          	add    0x10(%rax),%rbp
    332f:	48 03 58 18          	add    0x18(%rax),%rbx
    3333:	48 03 68 30          	add    0x30(%rax),%rbp
    3337:	48 03 58 38          	add    0x38(%rax),%rbx
    333b:	48 03 68 50          	add    0x50(%rax),%rbp
    333f:	48 03 58 58          	add    0x58(%rax),%rbx
    3343:	48 03 68 70          	add    0x70(%rax),%rbp
    3347:	48 03 58 78          	add    0x78(%rax),%rbx
    334b:	48 03 a8 90 00 00 00 	add    0x90(%rax),%rbp
    3352:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
    3359:	48 03 a8 b0 00 00 00 	add    0xb0(%rax),%rbp
    3360:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
    3367:	48 03 a8 d0 00 00 00 	add    0xd0(%rax),%rbp
    336e:	48 03 98 d8 00 00 00 	add    0xd8(%rax),%rbx
    3375:	48 03 a8 f0 00 00 00 	add    0xf0(%rax),%rbp
    337c:	48 03 98 f8 00 00 00 	add    0xf8(%rax),%rbx
    3383:	48 03 a8 10 01 00 00 	add    0x110(%rax),%rbp
    338a:	48 03 98 18 01 00 00 	add    0x118(%rax),%rbx
    3391:	48 03 a8 30 01 00 00 	add    0x130(%rax),%rbp
    3398:	48 03 98 38 01 00 00 	add    0x138(%rax),%rbx
    339f:	48 03 a8 50 01 00 00 	add    0x150(%rax),%rbp
    33a6:	48 03 98 58 01 00 00 	add    0x158(%rax),%rbx
    33ad:	48 03 a8 70 01 00 00 	add    0x170(%rax),%rbp
    33b4:	48 03 98 78 01 00 00 	add    0x178(%rax),%rbx
    33bb:	48 39 f2             	cmp    %rsi,%rdx
    33be:	0f 85 44 ff ff ff    	jne    3308 <main+0xd88>
    33c4:	45 31 e4             	xor    %r12d,%r12d
    33c7:	49 83 be b8 00 00 00 00 	cmpq   $0x0,0xb8(%r14)
    33cf:	7e 7b                	jle    344c <main+0xecc>
    33d1:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    33d6:	4c 89 f3             	mov    %r14,%rbx
    33d9:	4d 89 e6             	mov    %r12,%r14
    33dc:	4d 89 cc             	mov    %r9,%r12
    33df:	90                   	nop
    33e0:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    33e7:	4b 8d 14 b6          	lea    (%r14,%r14,4),%rdx
    33eb:	48 83 ec 08          	sub    $0x8,%rsp
    33ef:	bf 01 00 00 00       	mov    $0x1,%edi
    33f4:	49 83 c6 01          	add    $0x1,%r14
    33f8:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    33fc:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
    3406:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    340a:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    340e:	48 f7 e6             	mul    %rsi
    3411:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3415:	4c 2b 01             	sub    (%rcx),%r8
    3418:	31 c0                	xor    %eax,%eax
    341a:	8b 49 20             	mov    0x20(%rcx),%ecx
    341d:	56                   	push   %rsi
    341e:	48 8d 35 2b 42 00 00 	lea    0x422b(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    3425:	48 c1 ea 12          	shr    $0x12,%rdx
    3429:	49 89 d1             	mov    %rdx,%r9
    342c:	ba 02 00 00 00       	mov    $0x2,%edx
    3431:	e8 1a f0 ff ff       	call   2450 <__printf_chk@plt>
    3436:	58                   	pop    %rax
    3437:	5a                   	pop    %rdx
    3438:	4c 3b b3 b8 00 00 00 	cmp    0xb8(%rbx),%r14
    343f:	7c 9f                	jl     33e0 <main+0xe60>
    3441:	49 89 de             	mov    %rbx,%r14
    3444:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    3449:	4d 89 e1             	mov    %r12,%r9
    344c:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    3452:	49 81 c6 40 01 00 00 	add    $0x140,%r14
    3459:	83 7c 24 10 0c       	cmpl   $0xc,0x10(%rsp)
    345e:	0f 85 6f fd ff ff    	jne    31d3 <main+0xc53>
    3464:	4d 89 ce             	mov    %r9,%r14
    3467:	bf 01 00 00 00       	mov    $0x1,%edi
    346c:	31 c0                	xor    %eax,%eax
    346e:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    3473:	4c 89 f2             	mov    %r14,%rdx
    3476:	48 8d 35 50 3f 00 00 	lea    0x3f50(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    347d:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    3487:	e8 c4 ef ff ff       	call   2450 <__printf_chk@plt>
    348c:	bf 0a 00 00 00       	mov    $0xa,%edi
    3491:	e8 3a ee ff ff       	call   22d0 <putchar@plt>
    3496:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    349b:	bf 01 00 00 00       	mov    $0x1,%edi
    34a0:	48 8d 35 f9 41 00 00 	lea    0x41f9(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    34a7:	48 8b 50 08          	mov    0x8(%rax),%rdx
    34ab:	31 c0                	xor    %eax,%eax
    34ad:	e8 9e ef ff ff       	call   2450 <__printf_chk@plt>
    34b2:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    34b7:	bf 01 00 00 00       	mov    $0x1,%edi
    34bc:	48 8d 35 05 42 00 00 	lea    0x4205(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    34c3:	4c 89 c8             	mov    %r9,%rax
    34c6:	49 c1 f9 3f          	sar    $0x3f,%r9
    34ca:	49 f7 ec             	imul   %r12
    34cd:	31 c0                	xor    %eax,%eax
    34cf:	48 d1 fa             	sar    %rdx
    34d2:	4c 29 ca             	sub    %r9,%rdx
    34d5:	e8 76 ef ff ff       	call   2450 <__printf_chk@plt>
    34da:	4c 89 e8             	mov    %r13,%rax
    34dd:	4d 89 eb             	mov    %r13,%r11
    34e0:	bf 01 00 00 00       	mov    $0x1,%edi
    34e5:	49 f7 ec             	imul   %r12
    34e8:	49 c1 fb 3f          	sar    $0x3f,%r11
    34ec:	48 8d 35 05 42 00 00 	lea    0x4205(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    34f3:	31 c0                	xor    %eax,%eax
    34f5:	48 d1 fa             	sar    %rdx
    34f8:	4c 29 da             	sub    %r11,%rdx
    34fb:	e8 50 ef ff ff       	call   2450 <__printf_chk@plt>
    3500:	4c 89 f0             	mov    %r14,%rax
    3503:	4c 89 f1             	mov    %r14,%rcx
    3506:	bf 01 00 00 00       	mov    $0x1,%edi
    350b:	49 f7 ec             	imul   %r12
    350e:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3512:	48 8d 35 0f 42 00 00 	lea    0x420f(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    3519:	31 c0                	xor    %eax,%eax
    351b:	48 d1 fa             	sar    %rdx
    351e:	48 29 ca             	sub    %rcx,%rdx
    3521:	e8 2a ef ff ff       	call   2450 <__printf_chk@plt>
    3526:	48 89 e8             	mov    %rbp,%rax
    3529:	48 c1 fd 3f          	sar    $0x3f,%rbp
    352d:	48 8d 35 ad 3e 00 00 	lea    0x3ead(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    3534:	49 f7 ec             	imul   %r12
    3537:	bf 01 00 00 00       	mov    $0x1,%edi
    353c:	31 c0                	xor    %eax,%eax
    353e:	48 d1 fa             	sar    %rdx
    3541:	48 29 ea             	sub    %rbp,%rdx
    3544:	e8 07 ef ff ff       	call   2450 <__printf_chk@plt>
    3549:	48 89 d8             	mov    %rbx,%rax
    354c:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3550:	48 8d 35 9b 3e 00 00 	lea    0x3e9b(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    3557:	49 f7 ec             	imul   %r12
    355a:	bf 01 00 00 00       	mov    $0x1,%edi
    355f:	48 d1 fa             	sar    %rdx
    3562:	48 29 da             	sub    %rbx,%rdx
    3565:	31 c0                	xor    %eax,%eax
    3567:	e8 e4 ee ff ff       	call   2450 <__printf_chk@plt>
    356c:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    3574:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    357d:	0f 85 a3 00 00 00    	jne    3626 <main+0x10a6>
    3583:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    358a:	31 c0                	xor    %eax,%eax
    358c:	5b                   	pop    %rbx
    358d:	5d                   	pop    %rbp
    358e:	41 5c                	pop    %r12
    3590:	41 5d                	pop    %r13
    3592:	41 5e                	pop    %r14
    3594:	41 5f                	pop    %r15
    3596:	c3                   	ret
    3597:	48 8d 05 f2 21 00 00 	lea    0x21f2(%rip),%rax        # 5790 <barriered_work>
    359e:	bb 02 00 00 00       	mov    $0x2,%ebx
    35a3:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
    35aa:	e9 29 f3 ff ff       	jmp    28d8 <main+0x358>
    35af:	b8 89 88 88 88       	mov    $0x88888889,%eax
    35b4:	45 89 fe             	mov    %r15d,%r14d
    35b7:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    35bc:	4c 89 e9             	mov    %r13,%rcx
    35bf:	4c 0f af f0          	imul   %rax,%r14
    35c3:	89 ea                	mov    %ebp,%edx
    35c5:	41 c7 45 00 00 00 00 00 	movl   $0x0,0x0(%r13)
    35cd:	48 8d 35 35 3d 00 00 	lea    0x3d35(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
    35d4:	4c 89 2f             	mov    %r13,(%rdi)
    35d7:	49 c1 ee 23          	shr    $0x23,%r14
    35db:	44 89 f0             	mov    %r14d,%eax
    35de:	c1 e0 04             	shl    $0x4,%eax
    35e1:	44 29 f0             	sub    %r14d,%eax
    35e4:	45 89 fe             	mov    %r15d,%r14d
    35e7:	41 29 c6             	sub    %eax,%r14d
    35ea:	49 63 c6             	movslq %r14d,%rax
    35ed:	4c 8d 04 80          	lea    (%rax,%rax,4),%r8
    35f1:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    35f6:	49 c1 e0 06          	shl    $0x6,%r8
    35fa:	49 01 c0             	add    %rax,%r8
    35fd:	31 c0                	xor    %eax,%eax
    35ff:	4c 89 47 08          	mov    %r8,0x8(%rdi)
    3603:	bf 01 00 00 00       	mov    $0x1,%edi
    3608:	e8 43 ee ff ff       	call   2450 <__printf_chk@plt>
    360d:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    3612:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    3617:	49 89 c4             	mov    %rax,%r12
    361a:	e9 ad f1 ff ff       	jmp    27cc <main+0x24c>
    361f:	31 d2                	xor    %edx,%edx
    3621:	e9 2c fc ff ff       	jmp    3252 <main+0xcd2>
    3626:	e8 05 ed ff ff       	call   2330 <__stack_chk_fail@plt>
    362b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

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
    3648:	48 8d 3d 31 ef ff ff 	lea    -0x10cf(%rip),%rdi        # 2580 <main>
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
    3720:	f3 0f 1e fa          	endbr64
    3724:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    372b:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    3732:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
    373a:	48 8b 48 08          	mov    0x8(%rax),%rcx
    373e:	48 83 00 01          	addq   $0x1,(%rax)
    3742:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3749:	48 85 c9             	test   %rcx,%rcx
    374c:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3753:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3757:	48 89 50 08          	mov    %rdx,0x8(%rax)
    375b:	31 c0                	xor    %eax,%eax
    375d:	c3                   	ret
    375e:	66 90                	xchg   %ax,%ax

0000000000003760 <barriered_reset>:
    3760:	f3 0f 1e fa          	endbr64
    3764:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    376b:	85 c9                	test   %ecx,%ecx
    376d:	7e 4f                	jle    37be <barriered_reset+0x5e>
    376f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3776:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    377d:	48 c1 e1 09          	shl    $0x9,%rcx
    3781:	48 8b 50 40          	mov    0x40(%rax),%rdx
    3785:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
    3789:	48 8b 70 58          	mov    0x58(%rax),%rsi
    378d:	31 c0                	xor    %eax,%eax
    378f:	48 8b 52 58          	mov    0x58(%rdx),%rdx
    3793:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3798:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
    37a0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
    37a8:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    37b3:	48 05 00 02 00 00    	add    $0x200,%rax
    37b9:	48 39 c8             	cmp    %rcx,%rax
    37bc:	75 da                	jne    3798 <barriered_reset+0x38>
    37be:	0f ae f8             	sfence
    37c1:	31 c0                	xor    %eax,%eax
    37c3:	c3                   	ret
    37c4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    37cf:	90                   	nop

00000000000037d0 <barriered_thread>:
    37d0:	f3 0f 1e fa          	endbr64
    37d4:	83 7f 64 01          	cmpl   $0x1,0x64(%rdi)
    37d8:	0f 85 9b 02 00 00    	jne    3a79 <barriered_thread+0x2a9>
    37de:	41 56                	push   %r14
    37e0:	41 55                	push   %r13
    37e2:	49 89 fd             	mov    %rdi,%r13
    37e5:	41 54                	push   %r12
    37e7:	55                   	push   %rbp
    37e8:	31 ed                	xor    %ebp,%ebp
    37ea:	53                   	push   %rbx
    37eb:	31 db                	xor    %ebx,%ebx
    37ed:	0f 1f 00             	nopl   (%rax)
    37f0:	41 8b 55 60          	mov    0x60(%r13),%edx
    37f4:	39 da                	cmp    %ebx,%edx
    37f6:	7f 12                	jg     380a <barriered_thread+0x3a>
    37f8:	49 83 85 18 01 00 00 01 	addq   $0x1,0x118(%r13)
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
    382a:	49 8b 45 58          	mov    0x58(%r13),%rax
    382e:	4a 8d 34 20          	lea    (%rax,%r12,1),%rsi
    3832:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    3839:	75 dd                	jne    3818 <barriered_thread+0x48>
    383b:	41 8b 7d 48          	mov    0x48(%r13),%edi
    383f:	83 ea 01             	sub    $0x1,%edx
    3842:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3845:	85 db                	test   %ebx,%ebx
    3847:	0f 4f d1             	cmovg  %ecx,%edx
    384a:	85 ff                	test   %edi,%edi
    384c:	0f 8e 3e 01 00 00    	jle    3990 <barriered_thread+0x1c0>
    3852:	49 8b 45 40          	mov    0x40(%r13),%rax
    3856:	48 63 ca             	movslq %edx,%rcx
    3859:	48 63 d7             	movslq %edi,%rdx
    385c:	45 31 d2             	xor    %r10d,%r10d
    385f:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    3866:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
    386d:	48 c1 e1 09          	shl    $0x9,%rcx
    3871:	45 31 f6             	xor    %r14d,%r14d
    3874:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3878:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3880:	48 8b 10             	mov    (%rax),%rdx
    3883:	4c 8b 5a 58          	mov    0x58(%rdx),%r11
    3887:	49 01 cb             	add    %rcx,%r11
    388a:	4c 89 da             	mov    %r11,%rdx
    388d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    3894:	75 04                	jne    389a <barriered_thread+0xca>
    3896:	41 83 c6 01          	add    $0x1,%r14d
    389a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    38a1:	75 04                	jne    38a7 <barriered_thread+0xd7>
    38a3:	41 83 c2 01          	add    $0x1,%r10d
    38a7:	48 83 c0 08          	add    $0x8,%rax
    38ab:	48 39 f0             	cmp    %rsi,%rax
    38ae:	75 d0                	jne    3880 <barriered_thread+0xb0>
    38b0:	44 39 d7             	cmp    %r10d,%edi
    38b3:	0f 84 c7 00 00 00    	je     3980 <barriered_thread+0x1b0>
    38b9:	45 85 d2             	test   %r10d,%r10d
    38bc:	0f 84 be 00 00 00    	je     3980 <barriered_thread+0x1b0>
    38c2:	45 85 f6             	test   %r14d,%r14d
    38c5:	74 0a                	je     38d1 <barriered_thread+0x101>
    38c7:	45 39 75 48          	cmp    %r14d,0x48(%r13)
    38cb:	0f 85 8f 00 00 00    	jne    3960 <barriered_thread+0x190>
    38d1:	49 8b 45 58          	mov    0x58(%r13),%rax
    38d5:	4c 01 e0             	add    %r12,%rax
    38d8:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
    38df:	85 db                	test   %ebx,%ebx
    38e1:	75 14                	jne    38f7 <barriered_thread+0x127>
    38e3:	49 8b b5 f0 00 00 00 	mov    0xf0(%r13),%rsi
    38ea:	49 3b b5 f8 00 00 00 	cmp    0xf8(%r13),%rsi
    38f1:	0f 8c 61 01 00 00    	jl     3a58 <barriered_thread+0x288>
    38f7:	49 63 4d 00          	movslq 0x0(%r13),%rcx
    38fb:	49 8b 55 40          	mov    0x40(%r13),%rdx
    38ff:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
    3909:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    390d:	48 8b 7a 58          	mov    0x58(%rdx),%rdi
    3911:	4c 01 e7             	add    %r12,%rdi
    3914:	ff 90 18 01 00 00    	call   *0x118(%rax)
    391a:	49 8b 45 58          	mov    0x58(%r13),%rax
    391e:	4c 01 e0             	add    %r12,%rax
    3921:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
    3928:	41 8b 45 60          	mov    0x60(%r13),%eax
    392c:	49 83 85 e8 00 00 00 01 	addq   $0x1,0xe8(%r13)
    3934:	83 e8 01             	sub    $0x1,%eax
    3937:	39 d8                	cmp    %ebx,%eax
    3939:	0f 84 a9 00 00 00    	je     39e8 <barriered_thread+0x218>
    393f:	0f ae f8             	sfence
    3942:	85 ed                	test   %ebp,%ebp
    3944:	0f 84 d6 00 00 00    	je     3a20 <barriered_thread+0x250>
    394a:	41 8b 55 60          	mov    0x60(%r13),%edx
    394e:	83 c3 01             	add    $0x1,%ebx
    3951:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    3958:	39 d3                	cmp    %edx,%ebx
    395a:	0f 8c ca fe ff ff    	jl     382a <barriered_thread+0x5a>
    3960:	41 83 7d 64 01       	cmpl   $0x1,0x64(%r13)
    3965:	0f 84 85 fe ff ff    	je     37f0 <barriered_thread+0x20>
    396b:	5b                   	pop    %rbx
    396c:	31 c0                	xor    %eax,%eax
    396e:	5d                   	pop    %rbp
    396f:	41 5c                	pop    %r12
    3971:	41 5d                	pop    %r13
    3973:	41 5e                	pop    %r14
    3975:	c3                   	ret
    3976:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3980:	83 fd 01             	cmp    $0x1,%ebp
    3983:	74 1b                	je     39a0 <barriered_thread+0x1d0>
    3985:	31 ed                	xor    %ebp,%ebp
    3987:	e9 36 ff ff ff       	jmp    38c2 <barriered_thread+0xf2>
    398c:	0f 1f 40 00          	nopl   0x0(%rax)
    3990:	83 fd 01             	cmp    $0x1,%ebp
    3993:	0f 85 3c ff ff ff    	jne    38d5 <barriered_thread+0x105>
    3999:	45 31 f6             	xor    %r14d,%r14d
    399c:	0f 1f 40 00          	nopl   0x0(%rax)
    39a0:	49 8b 85 08 01 00 00 	mov    0x108(%r13),%rax
    39a7:	bf 04 00 00 00       	mov    $0x4,%edi
    39ac:	31 ed                	xor    %ebp,%ebp
    39ae:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    39b2:	49 8b 85 00 01 00 00 	mov    0x100(%r13),%rax
    39b9:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    39be:	e8 4d e9 ff ff       	call   2310 <clock_gettime@plt>
    39c3:	49 8b 85 08 01 00 00 	mov    0x108(%r13),%rax
    39ca:	48 83 c0 01          	add    $0x1,%rax
    39ce:	48 99                	cqto
    39d0:	49 f7 bd 10 01 00 00 	idivq  0x110(%r13)
    39d7:	49 89 95 08 01 00 00 	mov    %rdx,0x108(%r13)
    39de:	e9 df fe ff ff       	jmp    38c2 <barriered_thread+0xf2>
    39e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    39e8:	49 8b b5 f0 00 00 00 	mov    0xf0(%r13),%rsi
    39ef:	49 3b b5 f8 00 00 00 	cmp    0xf8(%r13),%rsi
    39f6:	0f 8d 43 ff ff ff    	jge    393f <barriered_thread+0x16f>
    39fc:	48 c1 e6 04          	shl    $0x4,%rsi
    3a00:	bf 04 00 00 00       	mov    $0x4,%edi
    3a05:	49 03 b5 e0 00 00 00 	add    0xe0(%r13),%rsi
    3a0c:	e8 ff e8 ff ff       	call   2310 <clock_gettime@plt>
    3a11:	49 83 85 f0 00 00 00 01 	addq   $0x1,0xf0(%r13)
    3a19:	e9 21 ff ff ff       	jmp    393f <barriered_thread+0x16f>
    3a1e:	66 90                	xchg   %ax,%ax
    3a20:	49 8b 85 08 01 00 00 	mov    0x108(%r13),%rax
    3a27:	bf 04 00 00 00       	mov    $0x4,%edi
    3a2c:	bd 01 00 00 00       	mov    $0x1,%ebp
    3a31:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3a35:	49 8b 85 00 01 00 00 	mov    0x100(%r13),%rax
    3a3c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3a40:	89 5e 20             	mov    %ebx,0x20(%rsi)
    3a43:	e8 c8 e8 ff ff       	call   2310 <clock_gettime@plt>
    3a48:	41 8b 55 60          	mov    0x60(%r13),%edx
    3a4c:	e9 c7 fd ff ff       	jmp    3818 <barriered_thread+0x48>
    3a51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3a58:	48 c1 e6 04          	shl    $0x4,%rsi
    3a5c:	bf 04 00 00 00       	mov    $0x4,%edi
    3a61:	49 03 b5 d8 00 00 00 	add    0xd8(%r13),%rsi
    3a68:	e8 a3 e8 ff ff       	call   2310 <clock_gettime@plt>
    3a6d:	49 8b 45 58          	mov    0x58(%r13),%rax
    3a71:	4c 01 e0             	add    %r12,%rax
    3a74:	e9 7e fe ff ff       	jmp    38f7 <barriered_thread+0x127>
    3a79:	31 c0                	xor    %eax,%eax
    3a7b:	c3                   	ret
    3a7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003a80 <external_thread>:
    3a80:	f3 0f 1e fa          	endbr64
    3a84:	41 55                	push   %r13
    3a86:	41 54                	push   %r12
    3a88:	55                   	push   %rbp
    3a89:	53                   	push   %rbx
    3a8a:	48 83 ec 38          	sub    $0x38,%rsp
    3a8e:	66 0f 6f 05 aa 3e 00 00 	movdqa 0x3eaa(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3a96:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3a9f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3aa4:	31 c0                	xor    %eax,%eax
    3aa6:	83 7f 64 01          	cmpl   $0x1,0x64(%rdi)
    3aaa:	0f 29 04 24          	movaps %xmm0,(%rsp)
    3aae:	75 64                	jne    3b14 <external_thread+0x94>
    3ab0:	49 89 fd             	mov    %rdi,%r13
    3ab3:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3ab8:	48 89 e3             	mov    %rsp,%rbx
    3abb:	4c 8d 25 42 35 00 00 	lea    0x3542(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    3ac2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3ac8:	48 89 ee             	mov    %rbp,%rsi
    3acb:	48 89 df             	mov    %rbx,%rdi
    3ace:	e8 7d e8 ff ff       	call   2350 <nanosleep@plt>
    3ad3:	49 8b 85 c0 00 00 00 	mov    0xc0(%r13),%rax
    3ada:	48 63 10             	movslq (%rax),%rdx
    3add:	85 d2                	test   %edx,%edx
    3adf:	7e 29                	jle    3b0a <external_thread+0x8a>
    3ae1:	48 8b 40 08          	mov    0x8(%rax),%rax
    3ae5:	48 c1 e2 04          	shl    $0x4,%rdx
    3ae9:	48 01 c2             	add    %rax,%rdx
    3aec:	0f 1f 40 00          	nopl   0x0(%rax)
    3af0:	8b 48 08             	mov    0x8(%rax),%ecx
    3af3:	85 c9                	test   %ecx,%ecx
    3af5:	75 0a                	jne    3b01 <external_thread+0x81>
    3af7:	4c 89 20             	mov    %r12,(%rax)
    3afa:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    3b01:	48 83 c0 10          	add    $0x10,%rax
    3b05:	48 39 c2             	cmp    %rax,%rdx
    3b08:	75 e6                	jne    3af0 <external_thread+0x70>
    3b0a:	0f ae f0             	mfence
    3b0d:	41 83 7d 64 01       	cmpl   $0x1,0x64(%r13)
    3b12:	74 b4                	je     3ac8 <external_thread+0x48>
    3b14:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3b19:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3b22:	75 0d                	jne    3b31 <external_thread+0xb1>
    3b24:	48 83 c4 38          	add    $0x38,%rsp
    3b28:	31 c0                	xor    %eax,%eax
    3b2a:	5b                   	pop    %rbx
    3b2b:	5d                   	pop    %rbp
    3b2c:	41 5c                	pop    %r12
    3b2e:	41 5d                	pop    %r13
    3b30:	c3                   	ret
    3b31:	e8 fa e7 ff ff       	call   2330 <__stack_chk_fail@plt>
    3b36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003b40 <timer_thread>:
    3b40:	f3 0f 1e fa          	endbr64
    3b44:	41 57                	push   %r15
    3b46:	48 8d 35 c3 34 00 00 	lea    0x34c3(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3b4d:	49 89 ff             	mov    %rdi,%r15
    3b50:	41 56                	push   %r14
    3b52:	41 55                	push   %r13
    3b54:	41 54                	push   %r12
    3b56:	55                   	push   %rbp
    3b57:	53                   	push   %rbx
    3b58:	48 83 ec 58          	sub    $0x58,%rsp
    3b5c:	8b 17                	mov    (%rdi),%edx
    3b5e:	bf 01 00 00 00       	mov    $0x1,%edi
    3b63:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3b6c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3b71:	31 c0                	xor    %eax,%eax
    3b73:	e8 d8 e8 ff ff       	call   2450 <__printf_chk@plt>
    3b78:	66 0f 6f 05 c0 3d 00 00 	movdqa 0x3dc0(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3b80:	ba 88 13 00 00       	mov    $0x1388,%edx
    3b85:	31 c0                	xor    %eax,%eax
    3b87:	48 8d 35 94 34 00 00 	lea    0x3494(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3b8e:	bf 01 00 00 00       	mov    $0x1,%edi
    3b93:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3b98:	e8 b3 e8 ff ff       	call   2450 <__printf_chk@plt>
    3b9d:	45 8b 77 64          	mov    0x64(%r15),%r14d
    3ba1:	45 85 f6             	test   %r14d,%r14d
    3ba4:	0f 84 9d 00 00 00    	je     3c47 <timer_thread+0x107>
    3baa:	45 31 ed             	xor    %r13d,%r13d
    3bad:	45 31 f6             	xor    %r14d,%r14d
    3bb0:	49 89 e4             	mov    %rsp,%r12
    3bb3:	31 db                	xor    %ebx,%ebx
    3bb5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3bba:	4c 89 e6             	mov    %r12,%rsi
    3bbd:	48 89 ef             	mov    %rbp,%rdi
    3bc0:	41 83 c5 01          	add    $0x1,%r13d
    3bc4:	e8 87 e7 ff ff       	call   2350 <nanosleep@plt>
    3bc9:	49 63 47 48          	movslq 0x48(%r15),%rax
    3bcd:	45 8d 46 01          	lea    0x1(%r14),%r8d
    3bd1:	85 c0                	test   %eax,%eax
    3bd3:	7e 48                	jle    3c1d <timer_thread+0xdd>
    3bd5:	49 8b 4f 40          	mov    0x40(%r15),%rcx
    3bd9:	49 63 fe             	movslq %r14d,%rdi
    3bdc:	48 c1 e7 09          	shl    $0x9,%rdi
    3be0:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3be4:	0f 1f 40 00          	nopl   0x0(%rax)
    3be8:	4c 8b 11             	mov    (%rcx),%r10
    3beb:	44 89 c0             	mov    %r8d,%eax
    3bee:	48 83 c1 08          	add    $0x8,%rcx
    3bf2:	99                   	cltd
    3bf3:	41 f7 7a 60          	idivl  0x60(%r10)
    3bf7:	49 8b 72 58          	mov    0x58(%r10),%rsi
    3bfb:	48 63 d2             	movslq %edx,%rdx
    3bfe:	48 c1 e2 09          	shl    $0x9,%rdx
    3c02:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
    3c0d:	c7 84 3e 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%rdi,1)
    3c18:	4c 39 c9             	cmp    %r9,%rcx
    3c1b:	75 cb                	jne    3be8 <timer_thread+0xa8>
    3c1d:	0f ae f0             	mfence
    3c20:	49 8b 47 40          	mov    0x40(%r15),%rax
    3c24:	41 8b 57 64          	mov    0x64(%r15),%edx
    3c28:	45 89 c6             	mov    %r8d,%r14d
    3c2b:	48 8b 00             	mov    (%rax),%rax
    3c2e:	44 39 40 60          	cmp    %r8d,0x60(%rax)
    3c32:	44 0f 4e f3          	cmovle %ebx,%r14d
    3c36:	85 d2                	test   %edx,%edx
    3c38:	74 0d                	je     3c47 <timer_thread+0x107>
    3c3a:	41 81 fd 88 13 00 00 	cmp    $0x1388,%r13d
    3c41:	0f 85 73 ff ff ff    	jne    3bba <timer_thread+0x7a>
    3c47:	48 8d 3d ea 33 00 00 	lea    0x33ea(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3c4e:	e8 9d e6 ff ff       	call   22f0 <puts@plt>
    3c53:	49 63 57 4c          	movslq 0x4c(%r15),%rdx
    3c57:	85 d2                	test   %edx,%edx
    3c59:	7e 4b                	jle    3ca6 <timer_thread+0x166>
    3c5b:	49 63 47 60          	movslq 0x60(%r15),%rax
    3c5f:	85 c0                	test   %eax,%eax
    3c61:	7e 43                	jle    3ca6 <timer_thread+0x166>
    3c63:	48 c1 e0 09          	shl    $0x9,%rax
    3c67:	4d 8b 47 40          	mov    0x40(%r15),%r8
    3c6b:	48 8d 34 d5 00 00 00 00 	lea    0x0(,%rdx,8),%rsi
    3c73:	31 ff                	xor    %edi,%edi
    3c75:	48 89 c1             	mov    %rax,%rcx
    3c78:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3c7c:	48 8b 40 58          	mov    0x58(%rax),%rax
    3c80:	48 8d 14 01          	lea    (%rcx,%rax,1),%rdx
    3c84:	0f 1f 40 00          	nopl   0x0(%rax)
    3c88:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    3c92:	48 05 00 02 00 00    	add    $0x200,%rax
    3c98:	48 39 d0             	cmp    %rdx,%rax
    3c9b:	75 eb                	jne    3c88 <timer_thread+0x148>
    3c9d:	48 83 c7 08          	add    $0x8,%rdi
    3ca1:	48 39 f7             	cmp    %rsi,%rdi
    3ca4:	75 d2                	jne    3c78 <timer_thread+0x138>
    3ca6:	0f ae f0             	mfence
    3ca9:	66 0f 6f 05 9f 3c 00 00 	movdqa 0x3c9f(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3cb1:	48 8d 2d a5 33 00 00 	lea    0x33a5(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3cb8:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    3cbd:	49 63 47 48          	movslq 0x48(%r15),%rax
    3cc1:	45 8d 6e 01          	lea    0x1(%r14),%r13d
    3cc5:	85 c0                	test   %eax,%eax
    3cc7:	7e 4b                	jle    3d14 <timer_thread+0x1d4>
    3cc9:	49 8b 4f 40          	mov    0x40(%r15),%rcx
    3ccd:	49 63 fe             	movslq %r14d,%rdi
    3cd0:	48 c1 e7 09          	shl    $0x9,%rdi
    3cd4:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3cd8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3ce0:	48 8b 19             	mov    (%rcx),%rbx
    3ce3:	44 89 e8             	mov    %r13d,%eax
    3ce6:	48 83 c1 08          	add    $0x8,%rcx
    3cea:	99                   	cltd
    3ceb:	f7 7b 60             	idivl  0x60(%rbx)
    3cee:	48 8b 73 58          	mov    0x58(%rbx),%rsi
    3cf2:	48 63 d2             	movslq %edx,%rdx
    3cf5:	48 c1 e2 09          	shl    $0x9,%rdx
    3cf9:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
    3d04:	c7 84 3e 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%rdi,1)
    3d0f:	4c 39 c1             	cmp    %r8,%rcx
    3d12:	75 cc                	jne    3ce0 <timer_thread+0x1a0>
    3d14:	0f ae f0             	mfence
    3d17:	49 8b 47 40          	mov    0x40(%r15),%rax
    3d1b:	48 8b 00             	mov    (%rax),%rax
    3d1e:	44 39 68 60          	cmp    %r13d,0x60(%rax)
    3d22:	7f 03                	jg     3d27 <timer_thread+0x1e7>
    3d24:	45 31 ed             	xor    %r13d,%r13d
    3d27:	41 8b 7f 50          	mov    0x50(%r15),%edi
    3d2b:	85 ff                	test   %edi,%edi
    3d2d:	0f 8e af 00 00 00    	jle    3de2 <timer_thread+0x2a2>
    3d33:	45 31 e4             	xor    %r12d,%r12d
    3d36:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3d3c:	31 db                	xor    %ebx,%ebx
    3d3e:	66 90                	xchg   %ax,%ax
    3d40:	45 31 f6             	xor    %r14d,%r14d
    3d43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3d48:	85 ff                	test   %edi,%edi
    3d4a:	7e 5e                	jle    3daa <timer_thread+0x26a>
    3d4c:	49 8b 47 40          	mov    0x40(%r15),%rax
    3d50:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3d54:	4c 89 f0             	mov    %r14,%rax
    3d57:	48 c1 e0 09          	shl    $0x9,%rax
    3d5b:	48 03 42 58          	add    0x58(%rdx),%rax
    3d5f:	31 d2                	xor    %edx,%edx
    3d61:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3d68:	eb 16                	jmp    3d80 <timer_thread+0x240>
    3d6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3d70:	4d 85 c0             	test   %r8,%r8
    3d73:	7f 1f                	jg     3d94 <timer_thread+0x254>
    3d75:	83 c2 01             	add    $0x1,%edx
    3d78:	48 83 c0 20          	add    $0x20,%rax
    3d7c:	39 fa                	cmp    %edi,%edx
    3d7e:	74 2a                	je     3daa <timer_thread+0x26a>
    3d80:	48 8b 08             	mov    (%rax),%rcx
    3d83:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3d87:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3d8b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3d8f:	48 85 c9             	test   %rcx,%rcx
    3d92:	7e dc                	jle    3d70 <timer_thread+0x230>
    3d94:	bf 01 00 00 00       	mov    $0x1,%edi
    3d99:	48 89 ee             	mov    %rbp,%rsi
    3d9c:	31 c0                	xor    %eax,%eax
    3d9e:	e8 ad e6 ff ff       	call   2450 <__printf_chk@plt>
    3da3:	41 8b 7f 50          	mov    0x50(%r15),%edi
    3da7:	45 31 c9             	xor    %r9d,%r9d
    3daa:	49 83 c6 01          	add    $0x1,%r14
    3dae:	44 39 f7             	cmp    %r14d,%edi
    3db1:	7f 95                	jg     3d48 <timer_thread+0x208>
    3db3:	41 83 c4 01          	add    $0x1,%r12d
    3db7:	41 39 fc             	cmp    %edi,%r12d
    3dba:	7d 09                	jge    3dc5 <timer_thread+0x285>
    3dbc:	48 83 c3 08          	add    $0x8,%rbx
    3dc0:	e9 7b ff ff ff       	jmp    3d40 <timer_thread+0x200>
    3dc5:	41 83 f9 01          	cmp    $0x1,%r9d
    3dc9:	74 17                	je     3de2 <timer_thread+0x2a2>
    3dcb:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3dd0:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3dd5:	45 89 ee             	mov    %r13d,%r14d
    3dd8:	e8 73 e5 ff ff       	call   2350 <nanosleep@plt>
    3ddd:	e9 db fe ff ff       	jmp    3cbd <timer_thread+0x17d>
    3de2:	48 8d 3d 6b 32 00 00 	lea    0x326b(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3de9:	e8 02 e5 ff ff       	call   22f0 <puts@plt>
    3dee:	41 8b 47 64          	mov    0x64(%r15),%eax
    3df2:	85 c0                	test   %eax,%eax
    3df4:	0f 84 a3 00 00 00    	je     3e9d <timer_thread+0x35d>
    3dfa:	41 8b 57 4c          	mov    0x4c(%r15),%edx
    3dfe:	85 d2                	test   %edx,%edx
    3e00:	7e 2b                	jle    3e2d <timer_thread+0x2ed>
    3e02:	49 8b 4f 40          	mov    0x40(%r15),%rcx
    3e06:	31 db                	xor    %ebx,%ebx
    3e08:	48 8d 2d 5f 32 00 00 	lea    0x325f(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3e0f:	90                   	nop
    3e10:	48 8b 04 d9          	mov    (%rcx,%rbx,8),%rax
    3e14:	83 78 08 02          	cmpl   $0x2,0x8(%rax)
    3e18:	c7 40 64 00 00 00 00 	movl   $0x0,0x64(%rax)
    3e1f:	0f 84 a5 00 00 00    	je     3eca <timer_thread+0x38a>
    3e25:	48 83 c3 01          	add    $0x1,%rbx
    3e29:	39 da                	cmp    %ebx,%edx
    3e2b:	7f e3                	jg     3e10 <timer_thread+0x2d0>
    3e2d:	49 63 57 48          	movslq 0x48(%r15),%rdx
    3e31:	85 d2                	test   %edx,%edx
    3e33:	7e 51                	jle    3e86 <timer_thread+0x346>
    3e35:	49 63 47 60          	movslq 0x60(%r15),%rax
    3e39:	85 c0                	test   %eax,%eax
    3e3b:	7e 49                	jle    3e86 <timer_thread+0x346>
    3e3d:	48 c1 e0 09          	shl    $0x9,%rax
    3e41:	4d 8b 47 40          	mov    0x40(%r15),%r8
    3e45:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3e4d:	31 c9                	xor    %ecx,%ecx
    3e4f:	48 89 c6             	mov    %rax,%rsi
    3e52:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3e58:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3e5c:	48 8b 40 58          	mov    0x58(%rax),%rax
    3e60:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    3e64:	0f 1f 40 00          	nopl   0x0(%rax)
    3e68:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
    3e72:	48 05 00 02 00 00    	add    $0x200,%rax
    3e78:	48 39 c2             	cmp    %rax,%rdx
    3e7b:	75 eb                	jne    3e68 <timer_thread+0x328>
    3e7d:	48 83 c1 08          	add    $0x8,%rcx
    3e81:	48 39 cf             	cmp    %rcx,%rdi
    3e84:	75 d2                	jne    3e58 <timer_thread+0x318>
    3e86:	0f ae f0             	mfence
    3e89:	48 8d 3d f0 31 00 00 	lea    0x31f0(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3e90:	e8 5b e4 ff ff       	call   22f0 <puts@plt>
    3e95:	41 c7 47 64 00 00 00 00 	movl   $0x0,0x64(%r15)
    3e9d:	48 8d 3d e3 31 00 00 	lea    0x31e3(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3ea4:	e8 47 e4 ff ff       	call   22f0 <puts@plt>
    3ea9:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3eae:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3eb7:	75 4a                	jne    3f03 <timer_thread+0x3c3>
    3eb9:	48 83 c4 58          	add    $0x58,%rsp
    3ebd:	31 c0                	xor    %eax,%eax
    3ebf:	5b                   	pop    %rbx
    3ec0:	5d                   	pop    %rbp
    3ec1:	41 5c                	pop    %r12
    3ec3:	41 5d                	pop    %r13
    3ec5:	41 5e                	pop    %r14
    3ec7:	41 5f                	pop    %r15
    3ec9:	c3                   	ret
    3eca:	48 89 ef             	mov    %rbp,%rdi
    3ecd:	e8 1e e4 ff ff       	call   22f0 <puts@plt>
    3ed2:	49 8b 47 40          	mov    0x40(%r15),%rax
    3ed6:	be 01 00 00 00       	mov    $0x1,%esi
    3edb:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    3edf:	48 83 c3 01          	add    $0x1,%rbx
    3ee3:	8b b8 d0 00 00 00    	mov    0xd0(%rax),%edi
    3ee9:	e8 12 e5 ff ff       	call   2400 <eventfd_write@plt>
    3eee:	41 8b 57 4c          	mov    0x4c(%r15),%edx
    3ef2:	39 da                	cmp    %ebx,%edx
    3ef4:	0f 8e 33 ff ff ff    	jle    3e2d <timer_thread+0x2ed>
    3efa:	49 8b 4f 40          	mov    0x40(%r15),%rcx
    3efe:	e9 0d ff ff ff       	jmp    3e10 <timer_thread+0x2d0>
    3f03:	e8 28 e4 ff ff       	call   2330 <__stack_chk_fail@plt>
    3f08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000003f10 <fatal_error>:
    3f10:	f3 0f 1e fa          	endbr64
    3f14:	50                   	push   %rax
    3f15:	58                   	pop    %rax
    3f16:	48 83 ec 08          	sub    $0x8,%rsp
    3f1a:	e8 71 e5 ff ff       	call   2490 <perror@plt>
    3f1f:	bf 01 00 00 00       	mov    $0x1,%edi
    3f24:	e8 77 e5 ff ff       	call   24a0 <exit@plt>
    3f29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003f30 <strtolower>:
    3f30:	f3 0f 1e fa          	endbr64
    3f34:	55                   	push   %rbp
    3f35:	53                   	push   %rbx
    3f36:	48 83 ec 08          	sub    $0x8,%rsp
    3f3a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3f3e:	84 db                	test   %bl,%bl
    3f40:	74 24                	je     3f66 <strtolower+0x36>
    3f42:	48 89 fd             	mov    %rdi,%rbp
    3f45:	e8 c6 e5 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3f4a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3f50:	48 8b 10             	mov    (%rax),%rdx
    3f53:	48 83 c5 01          	add    $0x1,%rbp
    3f57:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3f5a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    3f5d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3f62:	84 db                	test   %bl,%bl
    3f64:	75 ea                	jne    3f50 <strtolower+0x20>
    3f66:	48 83 c4 08          	add    $0x8,%rsp
    3f6a:	5b                   	pop    %rbx
    3f6b:	5d                   	pop    %rbp
    3f6c:	c3                   	ret
    3f6d:	0f 1f 00             	nopl   (%rax)

0000000000003f70 <zh_malloc>:
    3f70:	f3 0f 1e fa          	endbr64
    3f74:	48 83 ec 08          	sub    $0x8,%rsp
    3f78:	e8 93 e4 ff ff       	call   2410 <malloc@plt>
    3f7d:	48 85 c0             	test   %rax,%rax
    3f80:	74 05                	je     3f87 <zh_malloc+0x17>
    3f82:	48 83 c4 08          	add    $0x8,%rsp
    3f86:	c3                   	ret
    3f87:	48 8b 0d 92 60 00 00 	mov    0x6092(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    3f8e:	ba 28 00 00 00       	mov    $0x28,%edx
    3f93:	be 01 00 00 00       	mov    $0x1,%esi
    3f98:	48 8d 3d 69 34 00 00 	lea    0x3469(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    3f9f:	e8 1c e5 ff ff       	call   24c0 <fwrite@plt>
    3fa4:	bf 01 00 00 00       	mov    $0x1,%edi
    3fa9:	e8 f2 e4 ff ff       	call   24a0 <exit@plt>
    3fae:	66 90                	xchg   %ax,%ax

0000000000003fb0 <get_filename_ext>:
    3fb0:	f3 0f 1e fa          	endbr64
    3fb4:	53                   	push   %rbx
    3fb5:	be 2e 00 00 00       	mov    $0x2e,%esi
    3fba:	48 89 fb             	mov    %rdi,%rbx
    3fbd:	e8 9e e3 ff ff       	call   2360 <strrchr@plt>
    3fc2:	48 85 c0             	test   %rax,%rax
    3fc5:	74 11                	je     3fd8 <get_filename_ext+0x28>
    3fc7:	48 39 c3             	cmp    %rax,%rbx
    3fca:	74 0c                	je     3fd8 <get_filename_ext+0x28>
    3fcc:	48 83 c0 01          	add    $0x1,%rax
    3fd0:	5b                   	pop    %rbx
    3fd1:	c3                   	ret
    3fd2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3fd8:	48 8d 05 f0 30 00 00 	lea    0x30f0(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
    3fdf:	5b                   	pop    %rbx
    3fe0:	c3                   	ret
    3fe1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3fec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003ff0 <send_headers>:
    3ff0:	f3 0f 1e fa          	endbr64
    3ff4:	41 55                	push   %r13
    3ff6:	49 89 f5             	mov    %rsi,%r13
    3ff9:	48 89 fe             	mov    %rdi,%rsi
    3ffc:	41 54                	push   %r12
    3ffe:	55                   	push   %rbp
    3fff:	48 89 d5             	mov    %rdx,%rbp
    4002:	ba 00 04 00 00       	mov    $0x400,%edx
    4007:	53                   	push   %rbx
    4008:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    400f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4018:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4020:	31 c0                	xor    %eax,%eax
    4022:	49 89 e4             	mov    %rsp,%r12
    4025:	4c 89 e7             	mov    %r12,%rdi
    4028:	e8 03 e4 ff ff       	call   2430 <__strcpy_chk@plt>
    402d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4032:	84 db                	test   %bl,%bl
    4034:	74 24                	je     405a <send_headers+0x6a>
    4036:	e8 d5 e4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    403b:	48 8b 08             	mov    (%rax),%rcx
    403e:	4c 89 e0             	mov    %r12,%rax
    4041:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4048:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    404b:	48 83 c0 01          	add    $0x1,%rax
    404f:	88 50 ff             	mov    %dl,-0x1(%rax)
    4052:	48 0f be 18          	movsbq (%rax),%rbx
    4056:	84 db                	test   %bl,%bl
    4058:	75 ee                	jne    4048 <send_headers+0x58>
    405a:	bf 11 00 00 00       	mov    $0x11,%edi
    405f:	e8 ac e3 ff ff       	call   2410 <malloc@plt>
    4064:	48 85 c0             	test   %rax,%rax
    4067:	0f 84 7e 04 00 00    	je     44eb <send_headers+0x4fb>
    406d:	66 0f 6f 05 eb 38 00 00 	movdqa 0x38eb(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    4075:	48 89 45 00          	mov    %rax,0x0(%rbp)
    4079:	bf 17 00 00 00       	mov    $0x17,%edi
    407e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4086:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    408a:	0f 11 00             	movups %xmm0,(%rax)
    408d:	e8 7e e3 ff ff       	call   2410 <malloc@plt>
    4092:	48 85 c0             	test   %rax,%rax
    4095:	0f 84 50 04 00 00    	je     44eb <send_headers+0x4fb>
    409b:	66 0f 6f 05 cd 38 00 00 	movdqa 0x38cd(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    40a3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    40a7:	4c 89 e7             	mov    %r12,%rdi
    40aa:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    40b4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    40bc:	0f 11 00             	movups %xmm0,(%rax)
    40bf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    40c3:	be 2e 00 00 00       	mov    $0x2e,%esi
    40c8:	e8 93 e2 ff ff       	call   2360 <strrchr@plt>
    40cd:	48 85 c0             	test   %rax,%rax
    40d0:	0f 84 ea 02 00 00    	je     43c0 <send_headers+0x3d0>
    40d6:	4c 39 e0             	cmp    %r12,%rax
    40d9:	0f 84 e1 02 00 00    	je     43c0 <send_headers+0x3d0>
    40df:	48 8d 58 01          	lea    0x1(%rax),%rbx
    40e3:	48 8d 3d b3 2f 00 00 	lea    0x2fb3(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    40ea:	48 89 de             	mov    %rbx,%rsi
    40ed:	e8 be e2 ff ff       	call   23b0 <strcmp@plt>
    40f2:	85 c0                	test   %eax,%eax
    40f4:	75 20                	jne    4116 <send_headers+0x126>
    40f6:	66 0f 6f 05 82 38 00 00 	movdqa 0x3882(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    40fe:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4106:	66 0f 6f 05 82 38 00 00 	movdqa 0x3882(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    410e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4116:	48 89 de             	mov    %rbx,%rsi
    4119:	48 8d 3d 81 2f 00 00 	lea    0x2f81(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    4120:	e8 8b e2 ff ff       	call   23b0 <strcmp@plt>
    4125:	85 c0                	test   %eax,%eax
    4127:	75 20                	jne    4149 <send_headers+0x159>
    4129:	66 0f 6f 05 4f 38 00 00 	movdqa 0x384f(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4131:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4139:	66 0f 6f 05 4f 38 00 00 	movdqa 0x384f(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    4141:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4149:	48 89 de             	mov    %rbx,%rsi
    414c:	48 8d 3d 53 2f 00 00 	lea    0x2f53(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    4153:	e8 58 e2 ff ff       	call   23b0 <strcmp@plt>
    4158:	85 c0                	test   %eax,%eax
    415a:	0f 84 10 02 00 00    	je     4370 <send_headers+0x380>
    4160:	48 89 de             	mov    %rbx,%rsi
    4163:	48 8d 3d 40 2f 00 00 	lea    0x2f40(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    416a:	e8 41 e2 ff ff       	call   23b0 <strcmp@plt>
    416f:	85 c0                	test   %eax,%eax
    4171:	0f 84 a9 02 00 00    	je     4420 <send_headers+0x430>
    4177:	48 89 de             	mov    %rbx,%rsi
    417a:	48 8d 3d 2d 2f 00 00 	lea    0x2f2d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4181:	e8 2a e2 ff ff       	call   23b0 <strcmp@plt>
    4186:	85 c0                	test   %eax,%eax
    4188:	0f 84 6a 02 00 00    	je     43f8 <send_headers+0x408>
    418e:	48 89 de             	mov    %rbx,%rsi
    4191:	48 8d 3d 59 2f 00 00 	lea    0x2f59(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4198:	e8 13 e2 ff ff       	call   23b0 <strcmp@plt>
    419d:	85 c0                	test   %eax,%eax
    419f:	0f 84 2b 02 00 00    	je     43d0 <send_headers+0x3e0>
    41a5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    41a8:	0f 84 52 01 00 00    	je     4300 <send_headers+0x310>
    41ae:	48 89 de             	mov    %rbx,%rsi
    41b1:	48 8d 3d fa 2e 00 00 	lea    0x2efa(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    41b8:	e8 f3 e1 ff ff       	call   23b0 <strcmp@plt>
    41bd:	85 c0                	test   %eax,%eax
    41bf:	0f 84 ab 02 00 00    	je     4470 <send_headers+0x480>
    41c5:	48 89 de             	mov    %rbx,%rsi
    41c8:	48 8d 3d e7 2e 00 00 	lea    0x2ee7(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    41cf:	e8 dc e1 ff ff       	call   23b0 <strcmp@plt>
    41d4:	85 c0                	test   %eax,%eax
    41d6:	0f 84 6c 02 00 00    	je     4448 <send_headers+0x458>
    41dc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    41e4:	4c 89 e7             	mov    %r12,%rdi
    41e7:	e8 34 e1 ff ff       	call   2320 <strlen@plt>
    41ec:	48 89 c7             	mov    %rax,%rdi
    41ef:	48 89 c3             	mov    %rax,%rbx
    41f2:	e8 19 e2 ff ff       	call   2410 <malloc@plt>
    41f7:	48 85 c0             	test   %rax,%rax
    41fa:	0f 84 eb 02 00 00    	je     44eb <send_headers+0x4fb>
    4200:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4204:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    4208:	83 fb 08             	cmp    $0x8,%ebx
    420b:	0f 83 3f 01 00 00    	jae    4350 <send_headers+0x360>
    4211:	f6 c3 04             	test   $0x4,%bl
    4214:	0f 85 7b 02 00 00    	jne    4495 <send_headers+0x4a5>
    421a:	85 db                	test   %ebx,%ebx
    421c:	74 13                	je     4231 <send_headers+0x241>
    421e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4226:	88 10                	mov    %dl,(%rax)
    4228:	f6 c3 02             	test   $0x2,%bl
    422b:	0f 85 96 02 00 00    	jne    44c7 <send_headers+0x4d7>
    4231:	4d 89 e8             	mov    %r13,%r8
    4234:	48 8d 0d 7f 2e 00 00 	lea    0x2e7f(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    423b:	4c 89 e7             	mov    %r12,%rdi
    423e:	31 c0                	xor    %eax,%eax
    4240:	ba 00 04 00 00       	mov    $0x400,%edx
    4245:	be 01 00 00 00       	mov    $0x1,%esi
    424a:	e8 d1 e2 ff ff       	call   2520 <__sprintf_chk@plt>
    424f:	4c 89 e7             	mov    %r12,%rdi
    4252:	e8 c9 e0 ff ff       	call   2320 <strlen@plt>
    4257:	48 89 c7             	mov    %rax,%rdi
    425a:	48 89 c3             	mov    %rax,%rbx
    425d:	e8 ae e1 ff ff       	call   2410 <malloc@plt>
    4262:	48 85 c0             	test   %rax,%rax
    4265:	0f 84 80 02 00 00    	je     44eb <send_headers+0x4fb>
    426b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    426f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4273:	83 fb 08             	cmp    $0x8,%ebx
    4276:	0f 83 1c 01 00 00    	jae    4398 <send_headers+0x3a8>
    427c:	f6 c3 04             	test   $0x4,%bl
    427f:	0f 85 29 02 00 00    	jne    44ae <send_headers+0x4be>
    4285:	85 db                	test   %ebx,%ebx
    4287:	74 13                	je     429c <send_headers+0x2ac>
    4289:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4291:	88 10                	mov    %dl,(%rax)
    4293:	f6 c3 02             	test   $0x2,%bl
    4296:	0f 85 3d 02 00 00    	jne    44d9 <send_headers+0x4e9>
    429c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    42a1:	bf 02 00 00 00       	mov    $0x2,%edi
    42a6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    42ae:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    42b6:	e8 55 e1 ff ff       	call   2410 <malloc@plt>
    42bb:	48 85 c0             	test   %rax,%rax
    42be:	0f 84 27 02 00 00    	je     44eb <send_headers+0x4fb>
    42c4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    42cc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    42d0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    42d8:	66 89 10             	mov    %dx,(%rax)
    42db:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    42e3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    42ec:	0f 85 20 02 00 00    	jne    4512 <send_headers+0x522>
    42f2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    42f9:	5b                   	pop    %rbx
    42fa:	5d                   	pop    %rbp
    42fb:	41 5c                	pop    %r12
    42fd:	41 5d                	pop    %r13
    42ff:	c3                   	ret
    4300:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4304:	0f 85 a4 fe ff ff    	jne    41ae <send_headers+0x1be>
    430a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    430e:	0f 85 9a fe ff ff    	jne    41ae <send_headers+0x1be>
    4314:	66 0f 6f 05 c4 36 00 00 	movdqa 0x36c4(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    431c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4326:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    432e:	66 0f 6f 05 ba 36 00 00 	movdqa 0x36ba(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    4336:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    433e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4346:	e9 63 fe ff ff       	jmp    41ae <send_headers+0x1be>
    434b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4350:	89 da                	mov    %ebx,%edx
    4352:	48 89 c7             	mov    %rax,%rdi
    4355:	4c 89 e6             	mov    %r12,%rsi
    4358:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    435d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4362:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4365:	c1 e9 03             	shr    $0x3,%ecx
    4368:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    436b:	e9 c1 fe ff ff       	jmp    4231 <send_headers+0x241>
    4370:	66 0f 6f 05 08 36 00 00 	movdqa 0x3608(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4378:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4380:	66 0f 6f 05 18 36 00 00 	movdqa 0x3618(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4388:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4390:	e9 cb fd ff ff       	jmp    4160 <send_headers+0x170>
    4395:	0f 1f 00             	nopl   (%rax)
    4398:	89 da                	mov    %ebx,%edx
    439a:	48 89 c7             	mov    %rax,%rdi
    439d:	4c 89 e6             	mov    %r12,%rsi
    43a0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    43a5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    43aa:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    43ad:	c1 e9 03             	shr    $0x3,%ecx
    43b0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    43b3:	e9 e4 fe ff ff       	jmp    429c <send_headers+0x2ac>
    43b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    43c0:	48 8d 1d 08 2d 00 00 	lea    0x2d08(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    43c7:	e9 94 fd ff ff       	jmp    4160 <send_headers+0x170>
    43cc:	0f 1f 40 00          	nopl   0x0(%rax)
    43d0:	66 0f 6f 05 e8 35 00 00 	movdqa 0x35e8(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    43d8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    43e0:	66 0f 6f 05 e8 35 00 00 	movdqa 0x35e8(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    43e8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    43f0:	e9 b0 fd ff ff       	jmp    41a5 <send_headers+0x1b5>
    43f5:	0f 1f 00             	nopl   (%rax)
    43f8:	66 0f 6f 05 c0 35 00 00 	movdqa 0x35c0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4400:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4408:	66 0f 6f 05 c0 35 00 00 	movdqa 0x35c0(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    4410:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4418:	e9 71 fd ff ff       	jmp    418e <send_headers+0x19e>
    441d:	0f 1f 00             	nopl   (%rax)
    4420:	66 0f 6f 05 58 35 00 00 	movdqa 0x3558(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4428:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4430:	66 0f 6f 05 78 35 00 00 	movdqa 0x3578(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    4438:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4440:	e9 32 fd ff ff       	jmp    4177 <send_headers+0x187>
    4445:	0f 1f 00             	nopl   (%rax)
    4448:	66 0f 6f 05 70 35 00 00 	movdqa 0x3570(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4450:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4458:	66 0f 6f 05 b0 35 00 00 	movdqa 0x35b0(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4460:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4468:	e9 6f fd ff ff       	jmp    41dc <send_headers+0x1ec>
    446d:	0f 1f 00             	nopl   (%rax)
    4470:	66 0f 6f 05 48 35 00 00 	movdqa 0x3548(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4478:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4480:	66 0f 6f 05 78 35 00 00 	movdqa 0x3578(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4488:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4490:	e9 30 fd ff ff       	jmp    41c5 <send_headers+0x1d5>
    4495:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    449c:	89 db                	mov    %ebx,%ebx
    449e:	89 10                	mov    %edx,(%rax)
    44a0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    44a5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    44a9:	e9 83 fd ff ff       	jmp    4231 <send_headers+0x241>
    44ae:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    44b5:	89 db                	mov    %ebx,%ebx
    44b7:	89 10                	mov    %edx,(%rax)
    44b9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    44be:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    44c2:	e9 d5 fd ff ff       	jmp    429c <send_headers+0x2ac>
    44c7:	89 db                	mov    %ebx,%ebx
    44c9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    44cf:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    44d4:	e9 58 fd ff ff       	jmp    4231 <send_headers+0x241>
    44d9:	89 db                	mov    %ebx,%ebx
    44db:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    44e1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    44e6:	e9 b1 fd ff ff       	jmp    429c <send_headers+0x2ac>
    44eb:	48 8b 0d 2e 5b 00 00 	mov    0x5b2e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    44f2:	ba 28 00 00 00       	mov    $0x28,%edx
    44f7:	be 01 00 00 00       	mov    $0x1,%esi
    44fc:	48 8d 3d 05 2f 00 00 	lea    0x2f05(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4503:	e8 b8 df ff ff       	call   24c0 <fwrite@plt>
    4508:	bf 01 00 00 00       	mov    $0x1,%edi
    450d:	e8 8e df ff ff       	call   24a0 <exit@plt>
    4512:	e8 19 de ff ff       	call   2330 <__stack_chk_fail@plt>
    4517:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004520 <copy_file_contents>:
    4520:	f3 0f 1e fa          	endbr64
    4524:	41 55                	push   %r13
    4526:	49 89 d5             	mov    %rdx,%r13
    4529:	41 54                	push   %r12
    452b:	49 89 fc             	mov    %rdi,%r12
    452e:	48 89 f7             	mov    %rsi,%rdi
    4531:	55                   	push   %rbp
    4532:	53                   	push   %rbx
    4533:	48 89 f3             	mov    %rsi,%rbx
    4536:	48 83 ec 08          	sub    $0x8,%rsp
    453a:	e8 d1 de ff ff       	call   2410 <malloc@plt>
    453f:	48 85 c0             	test   %rax,%rax
    4542:	74 77                	je     45bb <copy_file_contents+0x9b>
    4544:	4c 89 e7             	mov    %r12,%rdi
    4547:	48 89 c5             	mov    %rax,%rbp
    454a:	31 f6                	xor    %esi,%esi
    454c:	31 c0                	xor    %eax,%eax
    454e:	e8 2d df ff ff       	call   2480 <open@plt>
    4553:	41 89 c4             	mov    %eax,%r12d
    4556:	85 c0                	test   %eax,%eax
    4558:	78 55                	js     45af <copy_file_contents+0x8f>
    455a:	48 89 da             	mov    %rbx,%rdx
    455d:	48 89 ee             	mov    %rbp,%rsi
    4560:	89 c7                	mov    %eax,%edi
    4562:	e8 29 de ff ff       	call   2390 <read@plt>
    4567:	48 98                	cltq
    4569:	48 39 d8             	cmp    %rbx,%rax
    456c:	7c 22                	jl     4590 <copy_file_contents+0x70>
    456e:	44 89 e7             	mov    %r12d,%edi
    4571:	e8 fa dd ff ff       	call   2370 <close@plt>
    4576:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    457a:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    457e:	48 83 c4 08          	add    $0x8,%rsp
    4582:	5b                   	pop    %rbx
    4583:	5d                   	pop    %rbp
    4584:	41 5c                	pop    %r12
    4586:	41 5d                	pop    %r13
    4588:	c3                   	ret
    4589:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4590:	48 8b 0d 89 5a 00 00 	mov    0x5a89(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4597:	ba 1a 00 00 00       	mov    $0x1a,%edx
    459c:	be 01 00 00 00       	mov    $0x1,%esi
    45a1:	48 8d 3d 28 2b 00 00 	lea    0x2b28(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    45a8:	e8 13 df ff ff       	call   24c0 <fwrite@plt>
    45ad:	eb bf                	jmp    456e <copy_file_contents+0x4e>
    45af:	48 8d 3d 49 2c 00 00 	lea    0x2c49(%rip),%rdi        # 71ff <_IO_stdin_used+0x1ff>
    45b6:	e8 55 f9 ff ff       	call   3f10 <fatal_error>
    45bb:	48 8b 0d 5e 5a 00 00 	mov    0x5a5e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    45c2:	ba 28 00 00 00       	mov    $0x28,%edx
    45c7:	be 01 00 00 00       	mov    $0x1,%esi
    45cc:	48 8d 3d 35 2e 00 00 	lea    0x2e35(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    45d3:	e8 e8 de ff ff       	call   24c0 <fwrite@plt>
    45d8:	bf 01 00 00 00       	mov    $0x1,%edi
    45dd:	e8 be de ff ff       	call   24a0 <exit@plt>
    45e2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    45ed:	0f 1f 00             	nopl   (%rax)

00000000000045f0 <add_write_request>:
    45f0:	f3 0f 1e fa          	endbr64
    45f4:	8b 46 44             	mov    0x44(%rsi),%eax
    45f7:	48 89 fa             	mov    %rdi,%rdx
    45fa:	48 89 f7             	mov    %rsi,%rdi
    45fd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    4603:	8d 70 01             	lea    0x1(%rax),%esi
    4606:	48 8b 07             	mov    (%rdi),%rax
    4609:	44 8b 00             	mov    (%rax),%r8d
    460c:	f6 c1 02             	test   $0x2,%cl
    460f:	74 00                	je     4611 <add_write_request+0x21>
    4611:	89 f0                	mov    %esi,%eax
    4613:	44 29 c0             	sub    %r8d,%eax
    4616:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4619:	0f 82 21 df ff ff    	jb     2540 <add_write_request.cold>
    461f:	c1 e9 0a             	shr    $0xa,%ecx
    4622:	48 83 ec 08          	sub    $0x8,%rsp
    4626:	8b 47 44             	mov    0x44(%rdi),%eax
    4629:	23 47 58             	and    0x58(%rdi),%eax
    462c:	83 e1 01             	and    $0x1,%ecx
    462f:	89 77 44             	mov    %esi,0x44(%rdi)
    4632:	8b 72 08             	mov    0x8(%rdx),%esi
    4635:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4639:	d3 e0                	shl    %cl,%eax
    463b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    463e:	48 c1 e0 06          	shl    $0x6,%rax
    4642:	48 03 47 38          	add    0x38(%rdi),%rax
    4646:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    464c:	89 70 04             	mov    %esi,0x4(%rax)
    464f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    4653:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4659:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4661:	48 89 70 10          	mov    %rsi,0x10(%rax)
    4665:	89 48 18             	mov    %ecx,0x18(%rax)
    4668:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    466f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4677:	48 89 50 20          	mov    %rdx,0x20(%rax)
    467b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    467f:	e8 bc dc ff ff       	call   2340 <io_uring_submit@plt>
    4684:	31 c0                	xor    %eax,%eax
    4686:	48 83 c4 08          	add    $0x8,%rsp
    468a:	c3                   	ret
    468b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004690 <add_read_request>:
    4690:	f3 0f 1e fa          	endbr64
    4694:	41 55                	push   %r13
    4696:	41 89 fd             	mov    %edi,%r13d
    4699:	41 54                	push   %r12
    469b:	55                   	push   %rbp
    469c:	53                   	push   %rbx
    469d:	48 89 f3             	mov    %rsi,%rbx
    46a0:	48 83 ec 08          	sub    $0x8,%rsp
    46a4:	8b 46 44             	mov    0x44(%rsi),%eax
    46a7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    46ad:	48 8b 16             	mov    (%rsi),%rdx
    46b0:	83 c0 01             	add    $0x1,%eax
    46b3:	8b 32                	mov    (%rdx),%esi
    46b5:	f6 c1 02             	test   $0x2,%cl
    46b8:	74 00                	je     46ba <add_read_request+0x2a>
    46ba:	89 c2                	mov    %eax,%edx
    46bc:	29 f2                	sub    %esi,%edx
    46be:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    46c1:	0f 82 89 de ff ff    	jb     2550 <add_read_request.cold>
    46c7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    46ca:	c1 e9 0a             	shr    $0xa,%ecx
    46cd:	89 43 44             	mov    %eax,0x44(%rbx)
    46d0:	bf 20 00 00 00       	mov    $0x20,%edi
    46d5:	83 e1 01             	and    $0x1,%ecx
    46d8:	23 6b 58             	and    0x58(%rbx),%ebp
    46db:	d3 e5                	shl    %cl,%ebp
    46dd:	48 c1 e5 06          	shl    $0x6,%rbp
    46e1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    46e5:	e8 26 dd ff ff       	call   2410 <malloc@plt>
    46ea:	be 01 00 00 00       	mov    $0x1,%esi
    46ef:	bf 00 20 00 00       	mov    $0x2000,%edi
    46f4:	49 89 c4             	mov    %rax,%r12
    46f7:	e8 a4 dc ff ff       	call   23a0 <calloc@plt>
    46fc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    4701:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4705:	48 89 df             	mov    %rbx,%rdi
    4708:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    470d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    4712:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    471b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    4723:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    4727:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    472b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    4732:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    473a:	48 89 45 10          	mov    %rax,0x10(%rbp)
    473e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    4746:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    474e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4752:	e8 e9 db ff ff       	call   2340 <io_uring_submit@plt>
    4757:	48 83 c4 08          	add    $0x8,%rsp
    475b:	31 c0                	xor    %eax,%eax
    475d:	5b                   	pop    %rbx
    475e:	5d                   	pop    %rbp
    475f:	41 5c                	pop    %r12
    4761:	41 5d                	pop    %r13
    4763:	c3                   	ret
    4764:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    476f:	90                   	nop

0000000000004770 <_send_static_string_content>:
    4770:	f3 0f 1e fa          	endbr64
    4774:	41 56                	push   %r14
    4776:	41 89 f6             	mov    %esi,%r14d
    4779:	41 55                	push   %r13
    477b:	49 89 fd             	mov    %rdi,%r13
    477e:	bf 20 00 00 00       	mov    $0x20,%edi
    4783:	41 54                	push   %r12
    4785:	55                   	push   %rbp
    4786:	48 89 d5             	mov    %rdx,%rbp
    4789:	53                   	push   %rbx
    478a:	e8 81 dc ff ff       	call   2410 <malloc@plt>
    478f:	48 85 c0             	test   %rax,%rax
    4792:	0f 84 dd 00 00 00    	je     4875 <_send_static_string_content+0x105>
    4798:	48 89 c3             	mov    %rax,%rbx
    479b:	4c 89 ef             	mov    %r13,%rdi
    479e:	e8 7d db ff ff       	call   2320 <strlen@plt>
    47a3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    47aa:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    47ae:	48 89 c7             	mov    %rax,%rdi
    47b1:	49 89 c4             	mov    %rax,%r12
    47b4:	e8 57 dc ff ff       	call   2410 <malloc@plt>
    47b9:	48 89 c7             	mov    %rax,%rdi
    47bc:	48 85 c0             	test   %rax,%rax
    47bf:	0f 84 b0 00 00 00    	je     4875 <_send_static_string_content+0x105>
    47c5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    47c9:	4c 89 e2             	mov    %r12,%rdx
    47cc:	4c 89 ee             	mov    %r13,%rsi
    47cf:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    47d3:	e8 08 dc ff ff       	call   23e0 <memcpy@plt>
    47d8:	8b 45 44             	mov    0x44(%rbp),%eax
    47db:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    47e1:	8d 50 01             	lea    0x1(%rax),%edx
    47e4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    47e8:	8b 30                	mov    (%rax),%esi
    47ea:	f6 c1 02             	test   $0x2,%cl
    47ed:	0f 85 7d 00 00 00    	jne    4870 <_send_static_string_content+0x100>
    47f3:	89 d0                	mov    %edx,%eax
    47f5:	29 f0                	sub    %esi,%eax
    47f7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    47fa:	0f 82 5a dd ff ff    	jb     255a <_send_static_string_content.cold>
    4800:	c1 e9 0a             	shr    $0xa,%ecx
    4803:	8b 45 44             	mov    0x44(%rbp),%eax
    4806:	23 45 58             	and    0x58(%rbp),%eax
    4809:	89 55 44             	mov    %edx,0x44(%rbp)
    480c:	83 e1 01             	and    $0x1,%ecx
    480f:	8b 53 04             	mov    0x4(%rbx),%edx
    4812:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    4818:	66 0f ef c0          	pxor   %xmm0,%xmm0
    481c:	d3 e0                	shl    %cl,%eax
    481e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    4821:	48 89 ef             	mov    %rbp,%rdi
    4824:	48 c1 e0 06          	shl    $0x6,%rax
    4828:	48 03 45 38          	add    0x38(%rbp),%rax
    482c:	89 48 04             	mov    %ecx,0x4(%rax)
    482f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    4833:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4839:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4841:	48 89 48 10          	mov    %rcx,0x10(%rax)
    4845:	89 50 18             	mov    %edx,0x18(%rax)
    4848:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    484f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4857:	48 89 58 20          	mov    %rbx,0x20(%rax)
    485b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    485f:	5b                   	pop    %rbx
    4860:	5d                   	pop    %rbp
    4861:	41 5c                	pop    %r12
    4863:	41 5d                	pop    %r13
    4865:	41 5e                	pop    %r14
    4867:	e9 d4 da ff ff       	jmp    2340 <io_uring_submit@plt>
    486c:	0f 1f 40 00          	nopl   0x0(%rax)
    4870:	e9 7e ff ff ff       	jmp    47f3 <_send_static_string_content+0x83>
    4875:	48 8b 0d a4 57 00 00 	mov    0x57a4(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    487c:	ba 28 00 00 00       	mov    $0x28,%edx
    4881:	be 01 00 00 00       	mov    $0x1,%esi
    4886:	48 8d 3d 7b 2b 00 00 	lea    0x2b7b(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    488d:	e8 2e dc ff ff       	call   24c0 <fwrite@plt>
    4892:	bf 01 00 00 00       	mov    $0x1,%edi
    4897:	e8 04 dc ff ff       	call   24a0 <exit@plt>
    489c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000048a0 <handle_unimplemented_method>:
    48a0:	f3 0f 1e fa          	endbr64
    48a4:	48 89 f2             	mov    %rsi,%rdx
    48a7:	89 fe                	mov    %edi,%esi
    48a9:	48 8b 3d 68 57 00 00 	mov    0x5768(%rip),%rdi        # a018 <unimplemented_content>
    48b0:	e9 bb fe ff ff       	jmp    4770 <_send_static_string_content>
    48b5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000048c0 <handle_http_404>:
    48c0:	f3 0f 1e fa          	endbr64
    48c4:	48 89 f2             	mov    %rsi,%rdx
    48c7:	89 fe                	mov    %edi,%esi
    48c9:	48 8b 3d 40 57 00 00 	mov    0x5740(%rip),%rdi        # a010 <http_404_content>
    48d0:	e9 9b fe ff ff       	jmp    4770 <_send_static_string_content>
    48d5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000048e0 <handle_get_method>:
    48e0:	f3 0f 1e fa          	endbr64
    48e4:	41 56                	push   %r14
    48e6:	41 55                	push   %r13
    48e8:	49 89 d5             	mov    %rdx,%r13
    48eb:	41 54                	push   %r12
    48ed:	41 89 f4             	mov    %esi,%r12d
    48f0:	55                   	push   %rbp
    48f1:	48 89 fd             	mov    %rdi,%rbp
    48f4:	53                   	push   %rbx
    48f5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    48fc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4905:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    490d:	31 c0                	xor    %eax,%eax
    490f:	e8 0c da ff ff       	call   2320 <strlen@plt>
    4914:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4919:	48 89 c3             	mov    %rax,%rbx
    491c:	0f 84 b6 00 00 00    	je     49d8 <handle_get_method+0xf8>
    4922:	b8 69 63 00 00       	mov    $0x6369,%eax
    4927:	48 89 ee             	mov    %rbp,%rsi
    492a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    492e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4933:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    493b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4943:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    494e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    4956:	e8 65 da ff ff       	call   23c0 <__memcpy_chk@plt>
    495b:	48 89 e6             	mov    %rsp,%rsi
    495e:	4c 89 f7             	mov    %r14,%rdi
    4961:	e8 6a da ff ff       	call   23d0 <stat@plt>
    4966:	83 f8 ff             	cmp    $0xffffffff,%eax
    4969:	0f 84 d3 00 00 00    	je     4a42 <handle_get_method+0x162>
    496f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4973:	25 00 f0 00 00       	and    $0xf000,%eax
    4978:	3d 00 80 00 00       	cmp    $0x8000,%eax
    497d:	0f 84 f5 00 00 00    	je     4a78 <handle_get_method+0x198>
    4983:	48 8b 3d 86 56 00 00 	mov    0x5686(%rip),%rdi        # a010 <http_404_content>
    498a:	4c 89 ea             	mov    %r13,%rdx
    498d:	44 89 e6             	mov    %r12d,%esi
    4990:	e8 db fd ff ff       	call   4770 <_send_static_string_content>
    4995:	4c 89 f2             	mov    %r14,%rdx
    4998:	bf 01 00 00 00       	mov    $0x1,%edi
    499d:	31 c0                	xor    %eax,%eax
    499f:	48 8d 35 7a 27 00 00 	lea    0x277a(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    49a6:	e8 a5 da ff ff       	call   2450 <__printf_chk@plt>
    49ab:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    49b3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    49bc:	0f 85 20 01 00 00    	jne    4ae2 <handle_get_method+0x202>
    49c2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    49c9:	5b                   	pop    %rbx
    49ca:	5d                   	pop    %rbp
    49cb:	41 5c                	pop    %r12
    49cd:	41 5d                	pop    %r13
    49cf:	41 5e                	pop    %r14
    49d1:	c3                   	ret
    49d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    49d8:	ba 69 63 00 00       	mov    $0x6369,%edx
    49dd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    49e5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    49ea:	48 89 ee             	mov    %rbp,%rsi
    49ed:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    49f5:	48 89 c2             	mov    %rax,%rdx
    49f8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4a00:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4a0b:	e8 b0 d9 ff ff       	call   23c0 <__memcpy_chk@plt>
    4a10:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4a15:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4a1a:	48 8d 35 ca 26 00 00 	lea    0x26ca(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4a21:	48 29 d9             	sub    %rbx,%rcx
    4a24:	ba 0b 00 00 00       	mov    $0xb,%edx
    4a29:	e8 92 d9 ff ff       	call   23c0 <__memcpy_chk@plt>
    4a2e:	48 89 e6             	mov    %rsp,%rsi
    4a31:	4c 89 f7             	mov    %r14,%rdi
    4a34:	e8 97 d9 ff ff       	call   23d0 <stat@plt>
    4a39:	83 f8 ff             	cmp    $0xffffffff,%eax
    4a3c:	0f 85 2d ff ff ff    	jne    496f <handle_get_method+0x8f>
    4a42:	4c 89 f2             	mov    %r14,%rdx
    4a45:	48 89 e9             	mov    %rbp,%rcx
    4a48:	48 8d 35 a7 26 00 00 	lea    0x26a7(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    4a4f:	31 c0                	xor    %eax,%eax
    4a51:	bf 01 00 00 00       	mov    $0x1,%edi
    4a56:	e8 f5 d9 ff ff       	call   2450 <__printf_chk@plt>
    4a5b:	48 8b 3d ae 55 00 00 	mov    0x55ae(%rip),%rdi        # a010 <http_404_content>
    4a62:	4c 89 ea             	mov    %r13,%rdx
    4a65:	44 89 e6             	mov    %r12d,%esi
    4a68:	e8 03 fd ff ff       	call   4770 <_send_static_string_content>
    4a6d:	e9 39 ff ff ff       	jmp    49ab <handle_get_method+0xcb>
    4a72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4a78:	bf 70 00 00 00       	mov    $0x70,%edi
    4a7d:	e8 8e d9 ff ff       	call   2410 <malloc@plt>
    4a82:	48 89 c3             	mov    %rax,%rbx
    4a85:	48 85 c0             	test   %rax,%rax
    4a88:	74 5d                	je     4ae7 <handle_get_method+0x207>
    4a8a:	44 89 60 08          	mov    %r12d,0x8(%rax)
    4a8e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4a93:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4a97:	4c 89 f7             	mov    %r14,%rdi
    4a9a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    4aa1:	e8 4a f5 ff ff       	call   3ff0 <send_headers>
    4aa6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4aab:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4aaf:	4c 89 f7             	mov    %r14,%rdi
    4ab2:	e8 69 fa ff ff       	call   4520 <copy_file_contents>
    4ab7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4abc:	4c 89 f2             	mov    %r14,%rdx
    4abf:	31 c0                	xor    %eax,%eax
    4ac1:	48 8d 35 46 26 00 00 	lea    0x2646(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4ac8:	bf 01 00 00 00       	mov    $0x1,%edi
    4acd:	e8 7e d9 ff ff       	call   2450 <__printf_chk@plt>
    4ad2:	4c 89 ee             	mov    %r13,%rsi
    4ad5:	48 89 df             	mov    %rbx,%rdi
    4ad8:	e8 13 fb ff ff       	call   45f0 <add_write_request>
    4add:	e9 c9 fe ff ff       	jmp    49ab <handle_get_method+0xcb>
    4ae2:	e8 49 d8 ff ff       	call   2330 <__stack_chk_fail@plt>
    4ae7:	48 8b 0d 32 55 00 00 	mov    0x5532(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4aee:	ba 28 00 00 00       	mov    $0x28,%edx
    4af3:	be 01 00 00 00       	mov    $0x1,%esi
    4af8:	48 8d 3d 09 29 00 00 	lea    0x2909(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4aff:	e8 bc d9 ff ff       	call   24c0 <fwrite@plt>
    4b04:	bf 01 00 00 00       	mov    $0x1,%edi
    4b09:	e8 92 d9 ff ff       	call   24a0 <exit@plt>
    4b0e:	66 90                	xchg   %ax,%ax

0000000000004b10 <handle_http_method>:
    4b10:	f3 0f 1e fa          	endbr64
    4b14:	41 57                	push   %r15
    4b16:	41 56                	push   %r14
    4b18:	4c 8d 35 66 25 00 00 	lea    0x2566(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
    4b1f:	41 55                	push   %r13
    4b21:	49 89 d5             	mov    %rdx,%r13
    4b24:	41 54                	push   %r12
    4b26:	41 89 f4             	mov    %esi,%r12d
    4b29:	4c 89 f6             	mov    %r14,%rsi
    4b2c:	55                   	push   %rbp
    4b2d:	53                   	push   %rbx
    4b2e:	48 83 ec 18          	sub    $0x18,%rsp
    4b32:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b3b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4b40:	31 c0                	xor    %eax,%eax
    4b42:	49 89 e7             	mov    %rsp,%r15
    4b45:	4c 89 fa             	mov    %r15,%rdx
    4b48:	e8 33 d8 ff ff       	call   2380 <strtok_r@plt>
    4b4d:	48 0f be 18          	movsbq (%rax),%rbx
    4b51:	48 89 c5             	mov    %rax,%rbp
    4b54:	84 db                	test   %bl,%bl
    4b56:	74 1d                	je     4b75 <handle_http_method+0x65>
    4b58:	e8 b3 d9 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4b5d:	48 89 ea             	mov    %rbp,%rdx
    4b60:	48 8b 08             	mov    (%rax),%rcx
    4b63:	48 83 c2 01          	add    $0x1,%rdx
    4b67:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4b6a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    4b6d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4b71:	84 db                	test   %bl,%bl
    4b73:	75 eb                	jne    4b60 <handle_http_method+0x50>
    4b75:	4c 89 fa             	mov    %r15,%rdx
    4b78:	4c 89 f6             	mov    %r14,%rsi
    4b7b:	31 ff                	xor    %edi,%edi
    4b7d:	e8 fe d7 ff ff       	call   2380 <strtok_r@plt>
    4b82:	48 8d 35 aa 25 00 00 	lea    0x25aa(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4b89:	48 89 ef             	mov    %rbp,%rdi
    4b8c:	48 89 c3             	mov    %rax,%rbx
    4b8f:	e8 1c d8 ff ff       	call   23b0 <strcmp@plt>
    4b94:	4c 89 ea             	mov    %r13,%rdx
    4b97:	44 89 e6             	mov    %r12d,%esi
    4b9a:	85 c0                	test   %eax,%eax
    4b9c:	75 2a                	jne    4bc8 <handle_http_method+0xb8>
    4b9e:	48 89 df             	mov    %rbx,%rdi
    4ba1:	e8 3a fd ff ff       	call   48e0 <handle_get_method>
    4ba6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4bab:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4bb4:	75 20                	jne    4bd6 <handle_http_method+0xc6>
    4bb6:	48 83 c4 18          	add    $0x18,%rsp
    4bba:	5b                   	pop    %rbx
    4bbb:	5d                   	pop    %rbp
    4bbc:	41 5c                	pop    %r12
    4bbe:	41 5d                	pop    %r13
    4bc0:	41 5e                	pop    %r14
    4bc2:	41 5f                	pop    %r15
    4bc4:	c3                   	ret
    4bc5:	0f 1f 00             	nopl   (%rax)
    4bc8:	48 8b 3d 49 54 00 00 	mov    0x5449(%rip),%rdi        # a018 <unimplemented_content>
    4bcf:	e8 9c fb ff ff       	call   4770 <_send_static_string_content>
    4bd4:	eb d0                	jmp    4ba6 <handle_http_method+0x96>
    4bd6:	e8 55 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
    4bdb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004be0 <get_line>:
    4be0:	f3 0f 1e fa          	endbr64
    4be4:	85 d2                	test   %edx,%edx
    4be6:	7e 38                	jle    4c20 <get_line+0x40>
    4be8:	48 63 d2             	movslq %edx,%rdx
    4beb:	48 83 c7 01          	add    $0x1,%rdi
    4bef:	48 01 f2             	add    %rsi,%rdx
    4bf2:	eb 11                	jmp    4c05 <get_line+0x25>
    4bf4:	0f 1f 40 00          	nopl   0x0(%rax)
    4bf8:	48 83 c6 01          	add    $0x1,%rsi
    4bfc:	48 83 c7 01          	add    $0x1,%rdi
    4c00:	48 39 d6             	cmp    %rdx,%rsi
    4c03:	74 1b                	je     4c20 <get_line+0x40>
    4c05:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4c09:	88 06                	mov    %al,(%rsi)
    4c0b:	3c 0d                	cmp    $0xd,%al
    4c0d:	75 e9                	jne    4bf8 <get_line+0x18>
    4c0f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4c12:	75 e4                	jne    4bf8 <get_line+0x18>
    4c14:	c6 06 00             	movb   $0x0,(%rsi)
    4c17:	31 c0                	xor    %eax,%eax
    4c19:	c3                   	ret
    4c1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4c20:	b8 01 00 00 00       	mov    $0x1,%eax
    4c25:	c3                   	ret
    4c26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004c30 <handle_client_request>:
    4c30:	f3 0f 1e fa          	endbr64
    4c34:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4c3b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4c3f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4c48:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4c50:	31 c0                	xor    %eax,%eax
    4c52:	49 89 e2             	mov    %rsp,%r10
    4c55:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4c5d:	4c 89 d0             	mov    %r10,%rax
    4c60:	eb 13                	jmp    4c75 <handle_client_request+0x45>
    4c62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4c68:	48 83 c0 01          	add    $0x1,%rax
    4c6c:	48 83 c1 01          	add    $0x1,%rcx
    4c70:	4c 39 c8             	cmp    %r9,%rax
    4c73:	74 4b                	je     4cc0 <handle_client_request+0x90>
    4c75:	44 0f b6 01          	movzbl (%rcx),%r8d
    4c79:	44 88 00             	mov    %r8b,(%rax)
    4c7c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4c80:	75 e6                	jne    4c68 <handle_client_request+0x38>
    4c82:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4c86:	75 e0                	jne    4c68 <handle_client_request+0x38>
    4c88:	c6 00 00             	movb   $0x0,(%rax)
    4c8b:	8b 47 08             	mov    0x8(%rdi),%eax
    4c8e:	48 89 f2             	mov    %rsi,%rdx
    4c91:	4c 89 d7             	mov    %r10,%rdi
    4c94:	89 c6                	mov    %eax,%esi
    4c96:	e8 75 fe ff ff       	call   4b10 <handle_http_method>
    4c9b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4ca3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4cac:	75 39                	jne    4ce7 <handle_client_request+0xb7>
    4cae:	31 c0                	xor    %eax,%eax
    4cb0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4cb7:	c3                   	ret
    4cb8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4cc0:	48 8b 0d 59 53 00 00 	mov    0x5359(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4cc7:	ba 12 00 00 00       	mov    $0x12,%edx
    4ccc:	be 01 00 00 00       	mov    $0x1,%esi
    4cd1:	48 8d 3d 5f 24 00 00 	lea    0x245f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4cd8:	e8 e3 d7 ff ff       	call   24c0 <fwrite@plt>
    4cdd:	bf 01 00 00 00       	mov    $0x1,%edi
    4ce2:	e8 b9 d7 ff ff       	call   24a0 <exit@plt>
    4ce7:	e8 44 d6 ff ff       	call   2330 <__stack_chk_fail@plt>
    4cec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004cf0 <add_accept_request>:
    4cf0:	f3 0f 1e fa          	endbr64
    4cf4:	55                   	push   %rbp
    4cf5:	53                   	push   %rbx
    4cf6:	48 89 cb             	mov    %rcx,%rbx
    4cf9:	48 83 ec 08          	sub    $0x8,%rsp
    4cfd:	8b 41 44             	mov    0x44(%rcx),%eax
    4d00:	4c 8b 03             	mov    (%rbx),%r8
    4d03:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    4d09:	83 c0 01             	add    $0x1,%eax
    4d0c:	45 8b 08             	mov    (%r8),%r9d
    4d0f:	f6 c1 02             	test   $0x2,%cl
    4d12:	74 00                	je     4d14 <add_accept_request+0x24>
    4d14:	41 89 c0             	mov    %eax,%r8d
    4d17:	45 29 c8             	sub    %r9d,%r8d
    4d1a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4d1e:	0f 82 46 d8 ff ff    	jb     256a <add_accept_request.cold>
    4d24:	c1 e9 0a             	shr    $0xa,%ecx
    4d27:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4d2a:	23 6b 58             	and    0x58(%rbx),%ebp
    4d2d:	89 43 44             	mov    %eax,0x44(%rbx)
    4d30:	83 e1 01             	and    $0x1,%ecx
    4d33:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4d37:	d3 e5                	shl    %cl,%ebp
    4d39:	48 c1 e5 06          	shl    $0x6,%rbp
    4d3d:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4d41:	89 7d 04             	mov    %edi,0x4(%rbp)
    4d44:	bf 10 00 00 00       	mov    $0x10,%edi
    4d49:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    4d50:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    4d54:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    4d58:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    4d60:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    4d68:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4d6c:	e8 9f d6 ff ff       	call   2410 <malloc@plt>
    4d71:	48 89 df             	mov    %rbx,%rdi
    4d74:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    4d7a:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4d7e:	48 83 c4 08          	add    $0x8,%rsp
    4d82:	5b                   	pop    %rbx
    4d83:	5d                   	pop    %rbp
    4d84:	e9 b7 d5 ff ff       	jmp    2340 <io_uring_submit@plt>
    4d89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004d90 <io_thread>:
    4d90:	f3 0f 1e fa          	endbr64
    4d94:	41 57                	push   %r15
    4d96:	31 d2                	xor    %edx,%edx
    4d98:	41 56                	push   %r14
    4d9a:	41 55                	push   %r13
    4d9c:	41 54                	push   %r12
    4d9e:	55                   	push   %rbp
    4d9f:	48 89 fd             	mov    %rdi,%rbp
    4da2:	53                   	push   %rbx
    4da3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4daa:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4db3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4dbb:	48 8b 87 c8 00 00 00 	mov    0xc8(%rdi),%rax
    4dc2:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4dc7:	bf 00 01 00 00       	mov    $0x100,%edi
    4dcc:	48 89 de             	mov    %rbx,%rsi
    4dcf:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4dd3:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4dd8:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4ddd:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4de2:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4de7:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4def:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4df4:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4dfc:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4e01:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4e09:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4e0e:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4e16:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4e1b:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4e23:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4e28:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4e30:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4e38:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4e40:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4e48:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4e50:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4e58:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4e60:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4e68:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4e70:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4e78:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4e80:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4e87:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    4e8f:	e8 5c d5 ff ff       	call   23f0 <io_uring_queue_init@plt>
    4e94:	48 8b bd c8 00 00 00 	mov    0xc8(%rbp),%rdi
    4e9b:	31 f6                	xor    %esi,%esi
    4e9d:	e8 3e d6 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
    4ea2:	31 d2                	xor    %edx,%edx
    4ea4:	be 01 00 00 00       	mov    $0x1,%esi
    4ea9:	bf 02 00 00 00       	mov    $0x2,%edi
    4eae:	e8 7d d6 ff ff       	call   2530 <socket@plt>
    4eb3:	83 f8 ff             	cmp    $0xffffffff,%eax
    4eb6:	0f 84 02 06 00 00    	je     54be <io_thread+0x72e>
    4ebc:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4ec1:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4ec7:	89 c7                	mov    %eax,%edi
    4ec9:	41 89 c4             	mov    %eax,%r12d
    4ecc:	ba 02 00 00 00       	mov    $0x2,%edx
    4ed1:	be 01 00 00 00       	mov    $0x1,%esi
    4ed6:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    4ede:	e8 1d d4 ff ff       	call   2300 <setsockopt@plt>
    4ee3:	85 c0                	test   %eax,%eax
    4ee5:	0f 88 c7 05 00 00    	js     54b2 <io_thread+0x722>
    4eeb:	8b 05 4f 2b 00 00    	mov    0x2b4f(%rip),%eax        # 7a40 <_IO_stdin_used+0xa40>
    4ef1:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    4ef6:	ba 10 00 00 00       	mov    $0x10,%edx
    4efb:	44 89 e7             	mov    %r12d,%edi
    4efe:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4f07:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    4f0f:	89 44 24 40          	mov    %eax,0x40(%rsp)
    4f13:	e8 48 d5 ff ff       	call   2460 <bind@plt>
    4f18:	85 c0                	test   %eax,%eax
    4f1a:	0f 88 86 05 00 00    	js     54a6 <io_thread+0x716>
    4f20:	be 0a 00 00 00       	mov    $0xa,%esi
    4f25:	44 89 e7             	mov    %r12d,%edi
    4f28:	e8 f3 d4 ff ff       	call   2420 <listen@plt>
    4f2d:	85 c0                	test   %eax,%eax
    4f2f:	0f 88 65 05 00 00    	js     549a <io_thread+0x70a>
    4f35:	ba db 18 00 00       	mov    $0x18db,%edx
    4f3a:	48 8d 35 3b 22 00 00 	lea    0x223b(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4f41:	bf 01 00 00 00       	mov    $0x1,%edi
    4f46:	31 c0                	xor    %eax,%eax
    4f48:	e8 03 d5 ff ff       	call   2450 <__printf_chk@plt>
    4f4d:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4f52:	48 89 d9             	mov    %rbx,%rcx
    4f55:	44 89 e7             	mov    %r12d,%edi
    4f58:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4f5d:	48 89 c6             	mov    %rax,%rsi
    4f60:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4f65:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    4f6a:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    4f72:	e8 79 fd ff ff       	call   4cf0 <add_accept_request>
    4f77:	bf 01 00 00 00       	mov    $0x1,%edi
    4f7c:	be 10 00 00 00       	mov    $0x10,%esi
    4f81:	e8 1a d4 ff ff       	call   23a0 <calloc@plt>
    4f86:	bf 0a 00 00 00       	mov    $0xa,%edi
    4f8b:	49 89 c5             	mov    %rax,%r13
    4f8e:	e8 7d d4 ff ff       	call   2410 <malloc@plt>
    4f93:	48 85 c0             	test   %rax,%rax
    4f96:	0f 84 d7 04 00 00    	je     5473 <io_thread+0x6e3>
    4f9c:	49 89 45 00          	mov    %rax,0x0(%r13)
    4fa0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4fa7:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4fae:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    4fb6:	8d 50 01             	lea    0x1(%rax),%edx
    4fb9:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4fbe:	8b 30                	mov    (%rax),%esi
    4fc0:	f6 c1 02             	test   $0x2,%cl
    4fc3:	0f 85 27 04 00 00    	jne    53f0 <io_thread+0x660>
    4fc9:	89 d0                	mov    %edx,%eax
    4fcb:	29 f0                	sub    %esi,%eax
    4fcd:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4fd4:	0f 82 9a d5 ff ff    	jb     2574 <io_thread.cold>
    4fda:	c1 e9 0a             	shr    $0xa,%ecx
    4fdd:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4fe4:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4fe8:	48 89 df             	mov    %rbx,%rdi
    4feb:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4ff2:	83 e1 01             	and    $0x1,%ecx
    4ff5:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4ffc:	48 8d b5 d0 00 00 00 	lea    0xd0(%rbp),%rsi
    5003:	8b 95 d0 00 00 00    	mov    0xd0(%rbp),%edx
    5009:	d3 e0                	shl    %cl,%eax
    500b:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5010:	48 c1 e0 06          	shl    $0x6,%rax
    5014:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    501c:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5022:	89 50 04             	mov    %edx,0x4(%rax)
    5025:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    502d:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5031:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5039:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5041:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5045:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5049:	e8 f2 d2 ff ff       	call   2340 <io_uring_submit@plt>
    504e:	83 7d 64 01          	cmpl   $0x1,0x64(%rbp)
    5052:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5057:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    505f:	0f 85 af 01 00 00    	jne    5214 <io_thread+0x484>
    5065:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    506a:	4d 89 ce             	mov    %r9,%r14
    506d:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5072:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5078:	48 8d 3d 13 21 00 00 	lea    0x2113(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    507f:	e8 6c d2 ff ff       	call   22f0 <puts@plt>
    5084:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    508b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    5092:	c1 e9 0b             	shr    $0xb,%ecx
    5095:	83 e1 01             	and    $0x1,%ecx
    5098:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    50a0:	8b 00                	mov    (%rax),%eax
    50a2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    50aa:	8b 16                	mov    (%rsi),%edx
    50ac:	39 d0                	cmp    %edx,%eax
    50ae:	74 36                	je     50e6 <io_thread+0x356>
    50b0:	89 f8                	mov    %edi,%eax
    50b2:	21 d0                	and    %edx,%eax
    50b4:	d3 e0                	shl    %cl,%eax
    50b6:	48 c1 e0 04          	shl    $0x4,%rax
    50ba:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    50c2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    50ca:	0f 85 80 01 00 00    	jne    5250 <io_thread+0x4c0>
    50d0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    50d4:	0f 85 1e 03 00 00    	jne    53f8 <io_thread+0x668>
    50da:	8b 40 08             	mov    0x8(%rax),%eax
    50dd:	83 c2 01             	add    $0x1,%edx
    50e0:	89 16                	mov    %edx,(%rsi)
    50e2:	85 c0                	test   %eax,%eax
    50e4:	79 b2                	jns    5098 <io_thread+0x308>
    50e6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    50ef:	90                   	nop
    50f0:	45 31 c0             	xor    %r8d,%r8d
    50f3:	31 d2                	xor    %edx,%edx
    50f5:	b9 01 00 00 00       	mov    $0x1,%ecx
    50fa:	4c 89 f6             	mov    %r14,%rsi
    50fd:	48 89 df             	mov    %rbx,%rdi
    5100:	e8 3b d3 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    5105:	41 89 c7             	mov    %eax,%r15d
    5108:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    510d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5111:	0f 84 f1 02 00 00    	je     5408 <io_thread+0x678>
    5117:	48 8d 3d 9a 20 00 00 	lea    0x209a(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    511e:	e8 cd d1 ff ff       	call   22f0 <puts@plt>
    5123:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5128:	4c 8b 22             	mov    (%rdx),%r12
    512b:	45 85 ff             	test   %r15d,%r15d
    512e:	0f 88 2e 03 00 00    	js     5462 <io_thread+0x6d2>
    5134:	8b 42 08             	mov    0x8(%rdx),%eax
    5137:	45 8b 04 24          	mov    (%r12),%r8d
    513b:	85 c0                	test   %eax,%eax
    513d:	0f 88 e5 02 00 00    	js     5428 <io_thread+0x698>
    5143:	41 83 f8 01          	cmp    $0x1,%r8d
    5147:	0f 84 3b 01 00 00    	je     5288 <io_thread+0x4f8>
    514d:	41 83 f8 02          	cmp    $0x2,%r8d
    5151:	0f 84 b1 01 00 00    	je     5308 <io_thread+0x578>
    5157:	45 85 c0             	test   %r8d,%r8d
    515a:	0f 84 70 01 00 00    	je     52d0 <io_thread+0x540>
    5160:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5168:	8b 02                	mov    (%rdx),%eax
    516a:	83 c0 01             	add    $0x1,%eax
    516d:	89 02                	mov    %eax,(%rdx)
    516f:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5176:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    517d:	8d 50 01             	lea    0x1(%rax),%edx
    5180:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5185:	8b 30                	mov    (%rax),%esi
    5187:	f6 c1 02             	test   $0x2,%cl
    518a:	74 00                	je     518c <io_thread+0x3fc>
    518c:	89 d0                	mov    %edx,%eax
    518e:	29 f0                	sub    %esi,%eax
    5190:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5197:	0f 82 d7 d3 ff ff    	jb     2574 <io_thread.cold>
    519d:	c1 e9 0a             	shr    $0xa,%ecx
    51a0:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    51a5:	66 0f ef c0          	pxor   %xmm0,%xmm0
    51a9:	48 89 df             	mov    %rbx,%rdi
    51ac:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    51b3:	83 e1 01             	and    $0x1,%ecx
    51b6:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    51bd:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    51c4:	d3 e0                	shl    %cl,%eax
    51c6:	8b 95 d0 00 00 00    	mov    0xd0(%rbp),%edx
    51cc:	48 c1 e0 06          	shl    $0x6,%rax
    51d0:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    51d8:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    51de:	89 50 04             	mov    %edx,0x4(%rax)
    51e1:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    51e9:	4c 89 68 10          	mov    %r13,0x10(%rax)
    51ed:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    51f5:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    51fd:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5201:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5205:	e8 36 d1 ff ff       	call   2340 <io_uring_submit@plt>
    520a:	83 7d 64 01          	cmpl   $0x1,0x64(%rbp)
    520e:	0f 84 64 fe ff ff    	je     5078 <io_thread+0x2e8>
    5214:	48 8d 3d d6 1f 00 00 	lea    0x1fd6(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    521b:	e8 d0 d0 ff ff       	call   22f0 <puts@plt>
    5220:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5228:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5231:	0f 85 37 02 00 00    	jne    546e <io_thread+0x6de>
    5237:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    523e:	31 c0                	xor    %eax,%eax
    5240:	5b                   	pop    %rbx
    5241:	5d                   	pop    %rbp
    5242:	41 5c                	pop    %r12
    5244:	41 5d                	pop    %r13
    5246:	41 5e                	pop    %r14
    5248:	41 5f                	pop    %r15
    524a:	c3                   	ret
    524b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5250:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    5255:	48 85 c0             	test   %rax,%rax
    5258:	0f 84 92 fe ff ff    	je     50f0 <io_thread+0x360>
    525e:	48 83 38 01          	cmpq   $0x1,(%rax)
    5262:	0f 84 a0 01 00 00    	je     5408 <io_thread+0x678>
    5268:	48 8d 3d 49 1f 00 00 	lea    0x1f49(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    526f:	e8 7c d0 ff ff       	call   22f0 <puts@plt>
    5274:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5279:	4c 8b 22             	mov    (%rdx),%r12
    527c:	e9 b3 fe ff ff       	jmp    5134 <io_thread+0x3a4>
    5281:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5288:	85 c0                	test   %eax,%eax
    528a:	0f 85 c0 00 00 00    	jne    5350 <io_thread+0x5c0>
    5290:	48 8b 0d 89 4d 00 00 	mov    0x4d89(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5297:	ba 0f 00 00 00       	mov    $0xf,%edx
    529c:	be 01 00 00 00       	mov    $0x1,%esi
    52a1:	48 8d 3d 39 1f 00 00 	lea    0x1f39(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    52a8:	e8 13 d2 ff ff       	call   24c0 <fwrite@plt>
    52ad:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    52b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    52b8:	48 85 c0             	test   %rax,%rax
    52bb:	0f 84 ae fe ff ff    	je     516f <io_thread+0x3df>
    52c1:	e9 9a fe ff ff       	jmp    5160 <io_thread+0x3d0>
    52c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    52d0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    52d5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    52da:	48 89 d9             	mov    %rbx,%rcx
    52dd:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    52e1:	e8 0a fa ff ff       	call   4cf0 <add_accept_request>
    52e6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    52eb:	48 89 de             	mov    %rbx,%rsi
    52ee:	8b 78 08             	mov    0x8(%rax),%edi
    52f1:	e8 9a f3 ff ff       	call   4690 <add_read_request>
    52f6:	4c 89 e7             	mov    %r12,%rdi
    52f9:	e8 c2 cf ff ff       	call   22c0 <free@plt>
    52fe:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5303:	eb b3                	jmp    52b8 <io_thread+0x528>
    5305:	0f 1f 00             	nopl   (%rax)
    5308:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    530d:	45 31 ff             	xor    %r15d,%r15d
    5310:	85 c0                	test   %eax,%eax
    5312:	7e 20                	jle    5334 <io_thread+0x5a4>
    5314:	0f 1f 40 00          	nopl   0x0(%rax)
    5318:	4c 89 f8             	mov    %r15,%rax
    531b:	49 83 c7 01          	add    $0x1,%r15
    531f:	48 c1 e0 04          	shl    $0x4,%rax
    5323:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5328:	e8 93 cf ff ff       	call   22c0 <free@plt>
    532d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5332:	7f e4                	jg     5318 <io_thread+0x588>
    5334:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5339:	e8 32 d0 ff ff       	call   2370 <close@plt>
    533e:	4c 89 e7             	mov    %r12,%rdi
    5341:	e8 7a cf ff ff       	call   22c0 <free@plt>
    5346:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    534b:	e9 68 ff ff ff       	jmp    52b8 <io_thread+0x528>
    5350:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5355:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    535a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5362:	eb 11                	jmp    5375 <io_thread+0x5e5>
    5364:	0f 1f 40 00          	nopl   0x0(%rax)
    5368:	48 83 c0 01          	add    $0x1,%rax
    536c:	48 83 c2 01          	add    $0x1,%rdx
    5370:	48 39 c6             	cmp    %rax,%rsi
    5373:	74 4b                	je     53c0 <io_thread+0x630>
    5375:	0f b6 0a             	movzbl (%rdx),%ecx
    5378:	88 08                	mov    %cl,(%rax)
    537a:	80 f9 0d             	cmp    $0xd,%cl
    537d:	75 e9                	jne    5368 <io_thread+0x5d8>
    537f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5383:	75 e3                	jne    5368 <io_thread+0x5d8>
    5385:	c6 00 00             	movb   $0x0,(%rax)
    5388:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    538d:	48 89 da             	mov    %rbx,%rdx
    5390:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5395:	e8 76 f7 ff ff       	call   4b10 <handle_http_method>
    539a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    539f:	e8 1c cf ff ff       	call   22c0 <free@plt>
    53a4:	4c 89 e7             	mov    %r12,%rdi
    53a7:	e8 14 cf ff ff       	call   22c0 <free@plt>
    53ac:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    53b1:	e9 02 ff ff ff       	jmp    52b8 <io_thread+0x528>
    53b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    53c0:	48 8b 0d 59 4c 00 00 	mov    0x4c59(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    53c7:	ba 12 00 00 00       	mov    $0x12,%edx
    53cc:	be 01 00 00 00       	mov    $0x1,%esi
    53d1:	48 8d 3d 5f 1d 00 00 	lea    0x1d5f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    53d8:	e8 e3 d0 ff ff       	call   24c0 <fwrite@plt>
    53dd:	bf 01 00 00 00       	mov    $0x1,%edi
    53e2:	e8 b9 d0 ff ff       	call   24a0 <exit@plt>
    53e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    53f0:	e9 d4 fb ff ff       	jmp    4fc9 <io_thread+0x239>
    53f5:	0f 1f 00             	nopl   (%rax)
    53f8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    53fd:	e9 5c fe ff ff       	jmp    525e <io_thread+0x4ce>
    5402:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5408:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5410:	48 8d 3d 8d 1d 00 00 	lea    0x1d8d(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    5417:	8b 02                	mov    (%rdx),%eax
    5419:	83 c0 01             	add    $0x1,%eax
    541c:	89 02                	mov    %eax,(%rdx)
    541e:	e8 cd ce ff ff       	call   22f0 <puts@plt>
    5423:	e9 ec fd ff ff       	jmp    5214 <io_thread+0x484>
    5428:	f7 d8                	neg    %eax
    542a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    542f:	89 c7                	mov    %eax,%edi
    5431:	e8 ca d0 ff ff       	call   2500 <strerror@plt>
    5436:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    543b:	be 01 00 00 00       	mov    $0x1,%esi
    5440:	48 8b 3d d9 4b 00 00 	mov    0x4bd9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5447:	48 89 c1             	mov    %rax,%rcx
    544a:	48 8d 15 e7 1f 00 00 	lea    0x1fe7(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    5451:	31 c0                	xor    %eax,%eax
    5453:	e8 78 d0 ff ff       	call   24d0 <__fprintf_chk@plt>
    5458:	bf 01 00 00 00       	mov    $0x1,%edi
    545d:	e8 3e d0 ff ff       	call   24a0 <exit@plt>
    5462:	48 8d 3d 66 1d 00 00 	lea    0x1d66(%rip),%rdi        # 71cf <_IO_stdin_used+0x1cf>
    5469:	e8 a2 ea ff ff       	call   3f10 <fatal_error>
    546e:	e8 bd ce ff ff       	call   2330 <__stack_chk_fail@plt>
    5473:	48 8b 0d a6 4b 00 00 	mov    0x4ba6(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    547a:	ba 28 00 00 00       	mov    $0x28,%edx
    547f:	be 01 00 00 00       	mov    $0x1,%esi
    5484:	48 8d 3d 7d 1f 00 00 	lea    0x1f7d(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    548b:	e8 30 d0 ff ff       	call   24c0 <fwrite@plt>
    5490:	bf 01 00 00 00       	mov    $0x1,%edi
    5495:	e8 06 d0 ff ff       	call   24a0 <exit@plt>
    549a:	48 8d 3d d2 1c 00 00 	lea    0x1cd2(%rip),%rdi        # 7173 <_IO_stdin_used+0x173>
    54a1:	e8 6a ea ff ff       	call   3f10 <fatal_error>
    54a6:	48 8d 3d bf 1c 00 00 	lea    0x1cbf(%rip),%rdi        # 716c <_IO_stdin_used+0x16c>
    54ad:	e8 5e ea ff ff       	call   3f10 <fatal_error>
    54b2:	48 8d 3d 9a 1c 00 00 	lea    0x1c9a(%rip),%rdi        # 7153 <_IO_stdin_used+0x153>
    54b9:	e8 52 ea ff ff       	call   3f10 <fatal_error>
    54be:	48 8d 3d 85 1c 00 00 	lea    0x1c85(%rip),%rdi        # 714a <_IO_stdin_used+0x14a>
    54c5:	e8 46 ea ff ff       	call   3f10 <fatal_error>
    54ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000054d0 <sendm>:
    54d0:	f3 0f 1e fa          	endbr64
    54d4:	41 57                	push   %r15
    54d6:	41 56                	push   %r14
    54d8:	41 55                	push   %r13
    54da:	41 54                	push   %r12
    54dc:	55                   	push   %rbp
    54dd:	53                   	push   %rbx
    54de:	48 83 ec 18          	sub    $0x18,%rsp
    54e2:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
    54e9:	0f 85 79 01 00 00    	jne    5668 <sendm+0x198>
    54ef:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    54f5:	48 89 fa             	mov    %rdi,%rdx
    54f8:	4c 8d bf 80 01 00 00 	lea    0x180(%rdi),%r15
    54ff:	31 f6                	xor    %esi,%esi
    5501:	48 8d bf 88 01 00 00 	lea    0x188(%rdi),%rdi
    5508:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    550d:	85 c0                	test   %eax,%eax
    550f:	0f 8e d2 00 00 00    	jle    55e7 <sendm+0x117>
    5515:	0f 1f 00             	nopl   (%rax)
    5518:	39 b2 30 01 00 00    	cmp    %esi,0x130(%rdx)
    551e:	0f 84 b7 00 00 00    	je     55db <sendm+0x10b>
    5524:	49 89 f2             	mov    %rsi,%r10
    5527:	49 c1 e2 05          	shl    $0x5,%r10
    552b:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
    5532:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5536:	49 8b 6b 08          	mov    0x8(%r11),%rbp
    553a:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    553e:	49 39 e9             	cmp    %rbp,%r9
    5541:	0f 8e 8b 00 00 00    	jle    55d2 <sendm+0x102>
    5547:	4c 89 cb             	mov    %r9,%rbx
    554a:	4c 8b aa 08 01 00 00 	mov    0x108(%rdx),%r13
    5551:	4d 8b 62 10          	mov    0x10(%r10),%r12
    5555:	48 29 eb             	sub    %rbp,%rbx
    5558:	4d 8b 03             	mov    (%r11),%r8
    555b:	48 8d 43 ff          	lea    -0x1(%rbx),%rax
    555f:	48 83 f8 02          	cmp    $0x2,%rax
    5563:	0f 86 e7 00 00 00    	jbe    5650 <sendm+0x180>
    5569:	4a 8d 3c cd 00 00 00 00 	lea    0x0(,%r9,8),%rdi
    5571:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    5579:	4d 8d 34 38          	lea    (%r8,%rdi,1),%r14
    557d:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5581:	4d 39 f7             	cmp    %r14,%r15
    5584:	73 7a                	jae    5600 <sendm+0x130>
    5586:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    558b:	4c 39 f1             	cmp    %r14,%rcx
    558e:	73 70                	jae    5600 <sendm+0x130>
    5590:	4c 01 c0             	add    %r8,%rax
    5593:	4c 01 c7             	add    %r8,%rdi
    5596:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    55a0:	4c 8b b2 80 01 00 00 	mov    0x180(%rdx),%r14
    55a7:	48 83 c0 08          	add    $0x8,%rax
    55ab:	4c 89 70 f8          	mov    %r14,-0x8(%rax)
    55af:	48 39 c7             	cmp    %rax,%rdi
    55b2:	75 ec                	jne    55a0 <sendm+0xd0>
    55b4:	0f 1f 40 00          	nopl   0x0(%rax)
    55b8:	49 01 dd             	add    %rbx,%r13
    55bb:	49 01 dc             	add    %rbx,%r12
    55be:	4c 89 aa 08 01 00 00 	mov    %r13,0x108(%rdx)
    55c5:	4d 89 62 10          	mov    %r12,0x10(%r10)
    55c9:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    55cd:	4f 89 74 c8 f8       	mov    %r14,-0x8(%r8,%r9,8)
    55d2:	0f ae f8             	sfence
    55d5:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    55db:	48 83 c6 01          	add    $0x1,%rsi
    55df:	39 f0                	cmp    %esi,%eax
    55e1:	0f 8f 31 ff ff ff    	jg     5518 <sendm+0x48>
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
    5600:	4c 8b b2 80 01 00 00 	mov    0x180(%rdx),%r14
    5607:	48 89 d8             	mov    %rbx,%rax
    560a:	48 d1 e8             	shr    %rax
    560d:	66 49 0f 6e c6       	movq   %r14,%xmm0
    5612:	48 c1 e0 04          	shl    $0x4,%rax
    5616:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    561a:	48 01 c8             	add    %rcx,%rax
    561d:	0f 1f 00             	nopl   (%rax)
    5620:	0f 11 01             	movups %xmm0,(%rcx)
    5623:	48 83 c1 10          	add    $0x10,%rcx
    5627:	48 39 c8             	cmp    %rcx,%rax
    562a:	75 f4                	jne    5620 <sendm+0x150>
    562c:	48 89 d8             	mov    %rbx,%rax
    562f:	48 83 e0 fe          	and    $0xfffffffffffffffe,%rax
    5633:	48 01 e8             	add    %rbp,%rax
    5636:	f6 c3 01             	test   $0x1,%bl
    5639:	0f 84 79 ff ff ff    	je     55b8 <sendm+0xe8>
    563f:	4c 8b b2 80 01 00 00 	mov    0x180(%rdx),%r14
    5646:	4d 89 34 c0          	mov    %r14,(%r8,%rax,8)
    564a:	e9 69 ff ff ff       	jmp    55b8 <sendm+0xe8>
    564f:	90                   	nop
    5650:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    5658:	4a 8d 3c cd 00 00 00 00 	lea    0x0(,%r9,8),%rdi
    5660:	e9 2b ff ff ff       	jmp    5590 <sendm+0xc0>
    5665:	0f 1f 00             	nopl   (%rax)
    5668:	48 8d 3d 95 1b 00 00 	lea    0x1b95(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    566f:	e8 7c cc ff ff       	call   22f0 <puts@plt>
    5674:	e9 6e ff ff ff       	jmp    55e7 <sendm+0x117>
    5679:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005680 <receive>:
    5680:	f3 0f 1e fa          	endbr64
    5684:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    568a:	85 c0                	test   %eax,%eax
    568c:	0f 8e f1 00 00 00    	jle    5783 <receive+0x103>
    5692:	41 54                	push   %r12
    5694:	48 89 fa             	mov    %rdi,%rdx
    5697:	55                   	push   %rbp
    5698:	31 ed                	xor    %ebp,%ebp
    569a:	53                   	push   %rbx
    569b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    56a0:	48 89 ee             	mov    %rbp,%rsi
    56a3:	48 c1 e6 05          	shl    $0x5,%rsi
    56a7:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    56ae:	4c 8b 26             	mov    (%rsi),%r12
    56b1:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    56b6:	48 85 ff             	test   %rdi,%rdi
    56b9:	0f 8e a1 00 00 00    	jle    5760 <receive+0xe0>
    56bf:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    56c6:	4d 8b 04 24          	mov    (%r12),%r8
    56ca:	4c 63 1a             	movslq (%rdx),%r11
    56cd:	49 89 c9             	mov    %rcx,%r9
    56d0:	48 8d 41 01          	lea    0x1(%rcx),%rax
    56d4:	49 f7 d9             	neg    %r9
    56d7:	48 01 c7             	add    %rax,%rdi
    56da:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
    56de:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
    56e5:	4c 8b 46 18          	mov    0x18(%rsi),%r8
    56e9:	49 29 c9             	sub    %rcx,%r9
    56ec:	49 29 c8             	sub    %rcx,%r8
    56ef:	eb 10                	jmp    5701 <receive+0x81>
    56f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    56f8:	48 83 c0 01          	add    $0x1,%rax
    56fc:	48 39 f8             	cmp    %rdi,%rax
    56ff:	74 5f                	je     5760 <receive+0xe0>
    5701:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    5705:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
    570c:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
    5713:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5717:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
    571b:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5720:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5724:	75 d2                	jne    56f8 <receive+0x78>
    5726:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    572d:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5731:	75 c5                	jne    56f8 <receive+0x78>
    5733:	bf 01 00 00 00       	mov    $0x1,%edi
    5738:	b9 01 00 00 00       	mov    $0x1,%ecx
    573d:	ba 01 00 00 00       	mov    $0x1,%edx
    5742:	31 c0                	xor    %eax,%eax
    5744:	48 8d 35 15 1d 00 00 	lea    0x1d15(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    574b:	e8 00 cd ff ff       	call   2450 <__printf_chk@plt>
    5750:	bf 01 00 00 00       	mov    $0x1,%edi
    5755:	e8 46 cd ff ff       	call   24a0 <exit@plt>
    575a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5760:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    5769:	0f ae f8             	sfence
    576c:	48 83 c5 01          	add    $0x1,%rbp
    5770:	39 aa 34 01 00 00    	cmp    %ebp,0x134(%rdx)
    5776:	0f 8f 24 ff ff ff    	jg     56a0 <receive+0x20>
    577c:	5b                   	pop    %rbx
    577d:	31 c0                	xor    %eax,%eax
    577f:	5d                   	pop    %rbp
    5780:	41 5c                	pop    %r12
    5782:	c3                   	ret
    5783:	31 c0                	xor    %eax,%eax
    5785:	c3                   	ret
    5786:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005790 <barriered_work>:
    5790:	f3 0f 1e fa          	endbr64
    5794:	41 57                	push   %r15
    5796:	41 56                	push   %r14
    5798:	41 55                	push   %r13
    579a:	41 54                	push   %r12
    579c:	55                   	push   %rbp
    579d:	53                   	push   %rbx
    579e:	48 89 fb             	mov    %rdi,%rbx
    57a1:	48 83 ec 18          	sub    $0x18,%rsp
    57a5:	8b 07                	mov    (%rdi),%eax
    57a7:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    57ad:	0f 84 3d 01 00 00    	je     58f0 <barriered_work+0x160>
    57b3:	e8 c8 fe ff ff       	call   5680 <receive>
    57b8:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    57bf:	75 1b                	jne    57dc <barriered_work+0x4c>
    57c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    57c8:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    57d0:	0f ae f8             	sfence
    57d3:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    57da:	74 ec                	je     57c8 <barriered_work+0x38>
    57dc:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    57e3:	0f 85 7f 02 00 00    	jne    5a68 <barriered_work+0x2d8>
    57e9:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    57ef:	85 c0                	test   %eax,%eax
    57f1:	0f 8e 7d 02 00 00    	jle    5a74 <barriered_work+0x2e4>
    57f7:	48 8d b3 88 01 00 00 	lea    0x188(%rbx),%rsi
    57fe:	31 c9                	xor    %ecx,%ecx
    5800:	4c 8d bb 80 01 00 00 	lea    0x180(%rbx),%r15
    5807:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    580c:	0f 1f 40 00          	nopl   0x0(%rax)
    5810:	39 8b 30 01 00 00    	cmp    %ecx,0x130(%rbx)
    5816:	0f 84 bf 00 00 00    	je     58db <barriered_work+0x14b>
    581c:	49 89 c9             	mov    %rcx,%r9
    581f:	49 c1 e1 05          	shl    $0x5,%r9
    5823:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    582a:	4d 8b 51 08          	mov    0x8(%r9),%r10
    582e:	49 8b 6a 08          	mov    0x8(%r10),%rbp
    5832:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5836:	4c 39 c5             	cmp    %r8,%rbp
    5839:	0f 8d 93 00 00 00    	jge    58d2 <barriered_work+0x142>
    583f:	4d 89 c3             	mov    %r8,%r11
    5842:	4c 8b ab 08 01 00 00 	mov    0x108(%rbx),%r13
    5849:	4d 8b 61 10          	mov    0x10(%r9),%r12
    584d:	49 29 eb             	sub    %rbp,%r11
    5850:	49 8b 3a             	mov    (%r10),%rdi
    5853:	49 8d 43 ff          	lea    -0x1(%r11),%rax
    5857:	48 83 f8 02          	cmp    $0x2,%rax
    585b:	0f 86 7f 02 00 00    	jbe    5ae0 <barriered_work+0x350>
    5861:	4a 8d 34 c5 00 00 00 00 	lea    0x0(,%r8,8),%rsi
    5869:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    5871:	4c 8d 34 37          	lea    (%rdi,%rsi,1),%r14
    5875:	48 8d 14 07          	lea    (%rdi,%rax,1),%rdx
    5879:	4d 39 f7             	cmp    %r14,%r15
    587c:	0f 83 0e 02 00 00    	jae    5a90 <barriered_work+0x300>
    5882:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    5887:	4c 39 f2             	cmp    %r14,%rdx
    588a:	0f 83 00 02 00 00    	jae    5a90 <barriered_work+0x300>
    5890:	48 01 f8             	add    %rdi,%rax
    5893:	48 01 fe             	add    %rdi,%rsi
    5896:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    58a0:	4c 8b b3 80 01 00 00 	mov    0x180(%rbx),%r14
    58a7:	48 83 c0 08          	add    $0x8,%rax
    58ab:	4c 89 70 f8          	mov    %r14,-0x8(%rax)
    58af:	48 39 f0             	cmp    %rsi,%rax
    58b2:	75 ec                	jne    58a0 <barriered_work+0x110>
    58b4:	0f 1f 40 00          	nopl   0x0(%rax)
    58b8:	4d 01 dd             	add    %r11,%r13
    58bb:	4d 01 dc             	add    %r11,%r12
    58be:	4c 89 ab 08 01 00 00 	mov    %r13,0x108(%rbx)
    58c5:	4d 89 61 10          	mov    %r12,0x10(%r9)
    58c9:	4d 89 42 08          	mov    %r8,0x8(%r10)
    58cd:	4e 89 74 c7 f8       	mov    %r14,-0x8(%rdi,%r8,8)
    58d2:	0f ae f8             	sfence
    58d5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    58db:	48 83 c1 01          	add    $0x1,%rcx
    58df:	39 c8                	cmp    %ecx,%eax
    58e1:	0f 8f 29 ff ff ff    	jg     5810 <barriered_work+0x80>
    58e7:	e9 88 01 00 00       	jmp    5a74 <barriered_work+0x2e4>
    58ec:	0f 1f 40 00          	nopl   0x0(%rax)
    58f0:	e8 8b fd ff ff       	call   5680 <receive>
    58f5:	8b 8b 34 01 00 00    	mov    0x134(%rbx),%ecx
    58fb:	8b 03                	mov    (%rbx),%eax
    58fd:	85 c9                	test   %ecx,%ecx
    58ff:	0f 8e 8b 00 00 00    	jle    5990 <barriered_work+0x200>
    5905:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    590c:	4c 63 d0             	movslq %eax,%r10
    590f:	83 c0 01             	add    $0x1,%eax
    5912:	4c 63 d9             	movslq %ecx,%r11
    5915:	49 c1 e2 09          	shl    $0x9,%r10
    5919:	4a 8d 2c dd 00 00 00 00 	lea    0x0(,%r11,8),%rbp
    5921:	48 8b 7a 40          	mov    0x40(%rdx),%rdi
    5925:	99                   	cltd
    5926:	f7 f9                	idiv   %ecx
    5928:	89 d0                	mov    %edx,%eax
    592a:	f7 d8                	neg    %eax
    592c:	0f 49 d0             	cmovns %eax,%edx
    592f:	45 31 ed             	xor    %r13d,%r13d
    5932:	4c 63 e2             	movslq %edx,%r12
    5935:	49 c1 e4 09          	shl    $0x9,%r12
    5939:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5940:	4e 8d 0c 2f          	lea    (%rdi,%r13,1),%r9
    5944:	4e 8d 04 ad 00 00 00 00 	lea    0x0(,%r13,4),%r8
    594c:	31 c0                	xor    %eax,%eax
    594e:	66 90                	xchg   %ax,%ax
    5950:	48 8b 14 c7          	mov    (%rdi,%rax,8),%rdx
    5954:	48 8b 52 58          	mov    0x58(%rdx),%rdx
    5958:	4a 8b 8c 22 68 01 00 00 	mov    0x168(%rdx,%r12,1),%rcx
    5960:	49 8b 11             	mov    (%r9),%rdx
    5963:	48 8b 72 58          	mov    0x58(%rdx),%rsi
    5967:	48 89 c2             	mov    %rax,%rdx
    596a:	48 83 c0 01          	add    $0x1,%rax
    596e:	48 c1 e2 05          	shl    $0x5,%rdx
    5972:	4a 03 94 16 68 01 00 00 	add    0x168(%rsi,%r10,1),%rdx
    597a:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    597e:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
    5982:	49 39 c3             	cmp    %rax,%r11
    5985:	75 c9                	jne    5950 <barriered_work+0x1c0>
    5987:	49 83 c5 08          	add    $0x8,%r13
    598b:	4c 39 ed             	cmp    %r13,%rbp
    598e:	75 b0                	jne    5940 <barriered_work+0x1b0>
    5990:	0f ae f8             	sfence
    5993:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    599a:	31 ff                	xor    %edi,%edi
    599c:	48 c1 e6 05          	shl    $0x5,%rsi
    59a0:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    59a7:	e8 64 c9 ff ff       	call   2310 <clock_gettime@plt>
    59ac:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    59b3:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    59ba:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    59c1:	8b 4a 10             	mov    0x10(%rdx),%ecx
    59c4:	8d 69 01             	lea    0x1(%rcx),%ebp
    59c7:	89 6a 10             	mov    %ebp,0x10(%rdx)
    59ca:	75 57                	jne    5a23 <barriered_work+0x293>
    59cc:	0f 1f 40 00          	nopl   0x0(%rax)
    59d0:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    59d7:	48 8b 40 40          	mov    0x40(%rax),%rax
    59db:	48 63 3b             	movslq (%rbx),%rdi
    59de:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    59e6:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    59ea:	48 c1 e7 09          	shl    $0x9,%rdi
    59ee:	48 03 78 58          	add    0x58(%rax),%rdi
    59f2:	ff 93 20 01 00 00    	call   *0x120(%rbx)
    59f8:	0f ae f8             	sfence
    59fb:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    5a02:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    5a09:	74 c5                	je     59d0 <barriered_work+0x240>
    5a0b:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    5a12:	3b 68 10             	cmp    0x10(%rax),%ebp
    5a15:	74 0c                	je     5a23 <barriered_work+0x293>
    5a17:	48 8d 3d f2 17 00 00 	lea    0x17f2(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    5a1e:	e8 cd c8 ff ff       	call   22f0 <puts@plt>
    5a23:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5a2a:	31 ff                	xor    %edi,%edi
    5a2c:	48 c1 e6 05          	shl    $0x5,%rsi
    5a30:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5a37:	48 83 c6 10          	add    $0x10,%rsi
    5a3b:	e8 d0 c8 ff ff       	call   2310 <clock_gettime@plt>
    5a40:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    5a47:	48 83 c0 01          	add    $0x1,%rax
    5a4b:	48 99                	cqto
    5a4d:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
    5a54:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    5a5b:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
    5a62:	0f 84 8d 00 00 00    	je     5af5 <barriered_work+0x365>
    5a68:	48 8d 3d 95 17 00 00 	lea    0x1795(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5a6f:	e8 7c c8 ff ff       	call   22f0 <puts@plt>
    5a74:	0f ae f8             	sfence
    5a77:	48 83 c4 18          	add    $0x18,%rsp
    5a7b:	31 c0                	xor    %eax,%eax
    5a7d:	5b                   	pop    %rbx
    5a7e:	5d                   	pop    %rbp
    5a7f:	41 5c                	pop    %r12
    5a81:	41 5d                	pop    %r13
    5a83:	41 5e                	pop    %r14
    5a85:	41 5f                	pop    %r15
    5a87:	c3                   	ret
    5a88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5a90:	4c 8b b3 80 01 00 00 	mov    0x180(%rbx),%r14
    5a97:	4c 89 d8             	mov    %r11,%rax
    5a9a:	48 d1 e8             	shr    %rax
    5a9d:	66 49 0f 6e c6       	movq   %r14,%xmm0
    5aa2:	48 c1 e0 04          	shl    $0x4,%rax
    5aa6:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5aaa:	48 01 d0             	add    %rdx,%rax
    5aad:	0f 1f 00             	nopl   (%rax)
    5ab0:	0f 11 02             	movups %xmm0,(%rdx)
    5ab3:	48 83 c2 10          	add    $0x10,%rdx
    5ab7:	48 39 d0             	cmp    %rdx,%rax
    5aba:	75 f4                	jne    5ab0 <barriered_work+0x320>
    5abc:	4c 89 d8             	mov    %r11,%rax
    5abf:	48 83 e0 fe          	and    $0xfffffffffffffffe,%rax
    5ac3:	48 01 e8             	add    %rbp,%rax
    5ac6:	41 f6 c3 01          	test   $0x1,%r11b
    5aca:	0f 84 e8 fd ff ff    	je     58b8 <barriered_work+0x128>
    5ad0:	4c 8b b3 80 01 00 00 	mov    0x180(%rbx),%r14
    5ad7:	4c 89 34 c7          	mov    %r14,(%rdi,%rax,8)
    5adb:	e9 d8 fd ff ff       	jmp    58b8 <barriered_work+0x128>
    5ae0:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    5ae8:	4a 8d 34 c5 00 00 00 00 	lea    0x0(,%r8,8),%rsi
    5af0:	e9 9b fd ff ff       	jmp    5890 <barriered_work+0x100>
    5af5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5afb:	48 8d b3 88 01 00 00 	lea    0x188(%rbx),%rsi
    5b02:	31 c9                	xor    %ecx,%ecx
    5b04:	4c 8d bb 80 01 00 00 	lea    0x180(%rbx),%r15
    5b0b:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5b10:	85 c0                	test   %eax,%eax
    5b12:	0f 8e 5c ff ff ff    	jle    5a74 <barriered_work+0x2e4>
    5b18:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5b20:	39 8b 30 01 00 00    	cmp    %ecx,0x130(%rbx)
    5b26:	0f 84 af 00 00 00    	je     5bdb <barriered_work+0x44b>
    5b2c:	49 89 c9             	mov    %rcx,%r9
    5b2f:	49 c1 e1 05          	shl    $0x5,%r9
    5b33:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    5b3a:	4d 8b 51 08          	mov    0x8(%r9),%r10
    5b3e:	49 8b 6a 08          	mov    0x8(%r10),%rbp
    5b42:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5b46:	49 39 e8             	cmp    %rbp,%r8
    5b49:	0f 8e 83 00 00 00    	jle    5bd2 <barriered_work+0x442>
    5b4f:	4d 89 c3             	mov    %r8,%r11
    5b52:	4c 8b ab 08 01 00 00 	mov    0x108(%rbx),%r13
    5b59:	4d 8b 61 10          	mov    0x10(%r9),%r12
    5b5d:	49 29 eb             	sub    %rbp,%r11
    5b60:	49 8b 3a             	mov    (%r10),%rdi
    5b63:	49 8d 43 ff          	lea    -0x1(%r11),%rax
    5b67:	48 83 f8 02          	cmp    $0x2,%rax
    5b6b:	0f 86 cf 00 00 00    	jbe    5c40 <barriered_work+0x4b0>
    5b71:	4a 8d 34 c5 00 00 00 00 	lea    0x0(,%r8,8),%rsi
    5b79:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    5b81:	4c 8d 34 37          	lea    (%rdi,%rsi,1),%r14
    5b85:	48 8d 14 07          	lea    (%rdi,%rax,1),%rdx
    5b89:	4d 39 f7             	cmp    %r14,%r15
    5b8c:	73 62                	jae    5bf0 <barriered_work+0x460>
    5b8e:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    5b93:	4c 39 f2             	cmp    %r14,%rdx
    5b96:	73 58                	jae    5bf0 <barriered_work+0x460>
    5b98:	48 01 f8             	add    %rdi,%rax
    5b9b:	48 01 fe             	add    %rdi,%rsi
    5b9e:	66 90                	xchg   %ax,%ax
    5ba0:	4c 8b b3 80 01 00 00 	mov    0x180(%rbx),%r14
    5ba7:	48 83 c0 08          	add    $0x8,%rax
    5bab:	4c 89 70 f8          	mov    %r14,-0x8(%rax)
    5baf:	48 39 f0             	cmp    %rsi,%rax
    5bb2:	75 ec                	jne    5ba0 <barriered_work+0x410>
    5bb4:	0f 1f 40 00          	nopl   0x0(%rax)
    5bb8:	4d 01 dd             	add    %r11,%r13
    5bbb:	4d 01 dc             	add    %r11,%r12
    5bbe:	4c 89 ab 08 01 00 00 	mov    %r13,0x108(%rbx)
    5bc5:	4d 89 61 10          	mov    %r12,0x10(%r9)
    5bc9:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5bcd:	4e 89 74 c7 f8       	mov    %r14,-0x8(%rdi,%r8,8)
    5bd2:	0f ae f8             	sfence
    5bd5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5bdb:	48 83 c1 01          	add    $0x1,%rcx
    5bdf:	39 c8                	cmp    %ecx,%eax
    5be1:	0f 8f 39 ff ff ff    	jg     5b20 <barriered_work+0x390>
    5be7:	e9 88 fe ff ff       	jmp    5a74 <barriered_work+0x2e4>
    5bec:	0f 1f 40 00          	nopl   0x0(%rax)
    5bf0:	4c 8b b3 80 01 00 00 	mov    0x180(%rbx),%r14
    5bf7:	4c 89 d8             	mov    %r11,%rax
    5bfa:	48 d1 e8             	shr    %rax
    5bfd:	66 49 0f 6e c6       	movq   %r14,%xmm0
    5c02:	48 c1 e0 04          	shl    $0x4,%rax
    5c06:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5c0a:	48 01 d0             	add    %rdx,%rax
    5c0d:	0f 1f 00             	nopl   (%rax)
    5c10:	0f 11 02             	movups %xmm0,(%rdx)
    5c13:	48 83 c2 10          	add    $0x10,%rdx
    5c17:	48 39 c2             	cmp    %rax,%rdx
    5c1a:	75 f4                	jne    5c10 <barriered_work+0x480>
    5c1c:	4c 89 d8             	mov    %r11,%rax
    5c1f:	48 83 e0 fe          	and    $0xfffffffffffffffe,%rax
    5c23:	48 01 e8             	add    %rbp,%rax
    5c26:	41 f6 c3 01          	test   $0x1,%r11b
    5c2a:	74 8c                	je     5bb8 <barriered_work+0x428>
    5c2c:	4c 8b b3 80 01 00 00 	mov    0x180(%rbx),%r14
    5c33:	4c 89 34 c7          	mov    %r14,(%rdi,%rax,8)
    5c37:	e9 7c ff ff ff       	jmp    5bb8 <barriered_work+0x428>
    5c3c:	0f 1f 40 00          	nopl   0x0(%rax)
    5c40:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    5c48:	4a 8d 34 c5 00 00 00 00 	lea    0x0(,%r8,8),%rsi
    5c50:	e9 43 ff ff ff       	jmp    5b98 <barriered_work+0x408>
    5c55:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005c60 <barriered_work_ingest>:
    5c60:	f3 0f 1e fa          	endbr64
    5c64:	48 83 ec 08          	sub    $0x8,%rsp
    5c68:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5c6f:	48 8b 80 c0 00 00 00 	mov    0xc0(%rax),%rax
    5c76:	48 63 10             	movslq (%rax),%rdx
    5c79:	85 d2                	test   %edx,%edx
    5c7b:	7e 31                	jle    5cae <barriered_work_ingest+0x4e>
    5c7d:	48 8b 40 08          	mov    0x8(%rax),%rax
    5c81:	48 c1 e2 04          	shl    $0x4,%rdx
    5c85:	48 01 c2             	add    %rax,%rdx
    5c88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5c90:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5c94:	75 0f                	jne    5ca5 <barriered_work_ingest+0x45>
    5c96:	48 83 87 60 01 00 00 01 	addq   $0x1,0x160(%rdi)
    5c9e:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    5ca5:	48 83 c0 10          	add    $0x10,%rax
    5ca9:	48 39 d0             	cmp    %rdx,%rax
    5cac:	75 e2                	jne    5c90 <barriered_work_ingest+0x30>
    5cae:	0f ae f8             	sfence
    5cb1:	e8 da fa ff ff       	call   5790 <barriered_work>
    5cb6:	31 c0                	xor    %eax,%eax
    5cb8:	48 83 c4 08          	add    $0x8,%rsp
    5cbc:	c3                   	ret
    5cbd:	0f 1f 00             	nopl   (%rax)

0000000000005cc0 <barriered_nulltask>:
    5cc0:	f3 0f 1e fa          	endbr64
    5cc4:	31 c0                	xor    %eax,%eax
    5cc6:	c3                   	ret
    5cc7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005cd0 <barriered_steal>:
    5cd0:	f3 0f 1e fa          	endbr64
    5cd4:	31 c0                	xor    %eax,%eax
    5cd6:	c3                   	ret
    5cd7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005ce0 <after>:
    5ce0:	f3 0f 1e fa          	endbr64
    5ce4:	31 c0                	xor    %eax,%eax
    5ce6:	48 39 d7             	cmp    %rdx,%rdi
    5ce9:	7e 08                	jle    5cf3 <after+0x13>
    5ceb:	31 c0                	xor    %eax,%eax
    5ced:	48 39 ce             	cmp    %rcx,%rsi
    5cf0:	0f 9f c0             	setg   %al
    5cf3:	c3                   	ret
    5cf4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5cff:	90                   	nop

0000000000005d00 <within>:
    5d00:	f3 0f 1e fa          	endbr64
    5d04:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5d09:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    5d0e:	31 c0                	xor    %eax,%eax
    5d10:	48 39 d7             	cmp    %rdx,%rdi
    5d13:	7f 18                	jg     5d2d <within+0x2d>
    5d15:	4d 39 d8             	cmp    %r11,%r8
    5d18:	0f 9e c2             	setle  %dl
    5d1b:	48 39 ce             	cmp    %rcx,%rsi
    5d1e:	0f 9e c0             	setle  %al
    5d21:	21 c2                	and    %eax,%edx
    5d23:	31 c0                	xor    %eax,%eax
    5d25:	4d 39 d1             	cmp    %r10,%r9
    5d28:	0f 9e c0             	setle  %al
    5d2b:	21 d0                	and    %edx,%eax
    5d2d:	c3                   	ret
    5d2e:	66 90                	xchg   %ax,%ax

0000000000005d30 <overlap>:
    5d30:	f3 0f 1e fa          	endbr64
    5d34:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5d39:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5d3e:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    5d43:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    5d48:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
    5d4d:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    5d52:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5d57:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    5d5c:	48 39 fe             	cmp    %rdi,%rsi
    5d5f:	7d 2f                	jge    5d90 <overlap+0x60>
    5d61:	48 39 ca             	cmp    %rcx,%rdx
    5d64:	7d 62                	jge    5dc8 <overlap+0x98>
    5d66:	4d 39 da             	cmp    %r11,%r10
    5d69:	7e 0e                	jle    5d79 <overlap+0x49>
    5d6b:	b8 01 00 00 00       	mov    $0x1,%eax
    5d70:	4d 39 c1             	cmp    %r8,%r9
    5d73:	0f 8f 7f 00 00 00    	jg     5df8 <overlap+0xc8>
    5d79:	31 c0                	xor    %eax,%eax
    5d7b:	4d 39 c1             	cmp    %r8,%r9
    5d7e:	7c 4c                	jl     5dcc <overlap+0x9c>
    5d80:	31 c0                	xor    %eax,%eax
    5d82:	4d 39 da             	cmp    %r11,%r10
    5d85:	0f 9d c0             	setge  %al
    5d88:	c3                   	ret
    5d89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5d90:	7e 4e                	jle    5de0 <overlap+0xb0>
    5d92:	48 39 ca             	cmp    %rcx,%rdx
    5d95:	7f 39                	jg     5dd0 <overlap+0xa0>
    5d97:	75 31                	jne    5dca <overlap+0x9a>
    5d99:	4d 39 c1             	cmp    %r8,%r9
    5d9c:	7f 2c                	jg     5dca <overlap+0x9a>
    5d9e:	b8 01 00 00 00       	mov    $0x1,%eax
    5da3:	4d 39 da             	cmp    %r11,%r10
    5da6:	7e 24                	jle    5dcc <overlap+0x9c>
    5da8:	48 39 ca             	cmp    %rcx,%rdx
    5dab:	0f 94 c2             	sete   %dl
    5dae:	48 39 fe             	cmp    %rdi,%rsi
    5db1:	0f 94 c0             	sete   %al
    5db4:	21 c2                	and    %eax,%edx
    5db6:	31 c0                	xor    %eax,%eax
    5db8:	4d 39 c1             	cmp    %r8,%r9
    5dbb:	0f 94 c0             	sete   %al
    5dbe:	21 d0                	and    %edx,%eax
    5dc0:	c3                   	ret
    5dc1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5dc8:	74 af                	je     5d79 <overlap+0x49>
    5dca:	31 c0                	xor    %eax,%eax
    5dcc:	c3                   	ret
    5dcd:	0f 1f 00             	nopl   (%rax)
    5dd0:	4d 39 c1             	cmp    %r8,%r9
    5dd3:	7d c4                	jge    5d99 <overlap+0x69>
    5dd5:	b8 01 00 00 00       	mov    $0x1,%eax
    5dda:	4d 39 da             	cmp    %r11,%r10
    5ddd:	7d ba                	jge    5d99 <overlap+0x69>
    5ddf:	c3                   	ret
    5de0:	48 39 ca             	cmp    %rcx,%rdx
    5de3:	7c 94                	jl     5d79 <overlap+0x49>
    5de5:	4d 39 c1             	cmp    %r8,%r9
    5de8:	7e b4                	jle    5d9e <overlap+0x6e>
    5dea:	48 39 ca             	cmp    %rcx,%rdx
    5ded:	74 91                	je     5d80 <overlap+0x50>
    5def:	eb d9                	jmp    5dca <overlap+0x9a>
    5df1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5df8:	c3                   	ret
    5df9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005e00 <verify>:
    5e00:	f3 0f 1e fa          	endbr64
    5e04:	85 f6                	test   %esi,%esi
    5e06:	0f 8e 18 03 00 00    	jle    6124 <verify+0x324>
    5e0c:	41 57                	push   %r15
    5e0e:	41 89 f7             	mov    %esi,%r15d
    5e11:	41 56                	push   %r14
    5e13:	45 31 f6             	xor    %r14d,%r14d
    5e16:	41 55                	push   %r13
    5e18:	41 54                	push   %r12
    5e1a:	55                   	push   %rbp
    5e1b:	53                   	push   %rbx
    5e1c:	48 8d 5f 58          	lea    0x58(%rdi),%rbx
    5e20:	48 83 ec 58          	sub    $0x58,%rsp
    5e24:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    5e29:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5e2e:	45 31 e4             	xor    %r12d,%r12d
    5e31:	45 39 f4             	cmp    %r14d,%r12d
    5e34:	0f 84 4f 02 00 00    	je     6089 <verify+0x289>
    5e3a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5e3f:	8b 50 08             	mov    0x8(%rax),%edx
    5e42:	85 d2                	test   %edx,%edx
    5e44:	0f 8e 3f 02 00 00    	jle    6089 <verify+0x289>
    5e4a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    5e4f:	45 31 ed             	xor    %r13d,%r13d
    5e52:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    5e57:	44 89 f2             	mov    %r14d,%edx
    5e5a:	48 8d 35 bf 13 00 00 	lea    0x13bf(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    5e61:	bf 01 00 00 00       	mov    $0x1,%edi
    5e66:	31 c0                	xor    %eax,%eax
    5e68:	e8 e3 c5 ff ff       	call   2450 <__printf_chk@plt>
    5e6d:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5e72:	8b 40 08             	mov    0x8(%rax),%eax
    5e75:	85 c0                	test   %eax,%eax
    5e77:	0f 8e ef 01 00 00    	jle    606c <verify+0x26c>
    5e7d:	4c 89 e8             	mov    %r13,%rax
    5e80:	4c 89 6c 24 40       	mov    %r13,0x40(%rsp)
    5e85:	31 db                	xor    %ebx,%ebx
    5e87:	48 c1 e0 09          	shl    $0x9,%rax
    5e8b:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    5e90:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5e95:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5e9a:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    5e9f:	4c 8b 20             	mov    (%rax),%r12
    5ea2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5ea8:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    5ead:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5eb2:	49 89 de             	mov    %rbx,%r14
    5eb5:	48 8d 35 79 13 00 00 	lea    0x1379(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5ebc:	49 c1 e6 09          	shl    $0x9,%r14
    5ec0:	bf 01 00 00 00       	mov    $0x1,%edi
    5ec5:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5ec9:	4b 8b 8c 3c 58 01 00 00 	mov    0x158(%r12,%r15,1),%rcx
    5ed1:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    5ed6:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    5ede:	31 c0                	xor    %eax,%eax
    5ee0:	e8 6b c5 ff ff       	call   2450 <__printf_chk@plt>
    5ee5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5eea:	4c 8b 20             	mov    (%rax),%r12
    5eed:	4b 83 bc 3c 58 01 00 00 00 	cmpq   $0x0,0x158(%r12,%r15,1)
    5ef6:	0f 8e 4f 01 00 00    	jle    604b <verify+0x24b>
    5efc:	4c 03 75 00          	add    0x0(%rbp),%r14
    5f00:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    5f05:	ba 01 00 00 00       	mov    $0x1,%edx
    5f0a:	4d 89 f3             	mov    %r14,%r11
    5f0d:	4d 8b b3 58 01 00 00 	mov    0x158(%r11),%r14
    5f14:	4d 85 f6             	test   %r14,%r14
    5f17:	0f 8e 29 01 00 00    	jle    6046 <verify+0x246>
    5f1d:	0f 1f 00             	nopl   (%rax)
    5f20:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5f25:	48 89 d5             	mov    %rdx,%rbp
    5f28:	31 db                	xor    %ebx,%ebx
    5f2a:	49 89 d5             	mov    %rdx,%r13
    5f2d:	48 c1 e5 05          	shl    $0x5,%rbp
    5f31:	48 83 ed 20          	sub    $0x20,%rbp
    5f35:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    5f39:	eb 32                	jmp    5f6d <verify+0x16d>
    5f3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5f40:	4c 39 c2             	cmp    %r8,%rdx
    5f43:	0f 8d 5f 01 00 00    	jge    60a8 <verify+0x2a8>
    5f49:	4c 39 d7             	cmp    %r10,%rdi
    5f4c:	7e 09                	jle    5f57 <verify+0x157>
    5f4e:	49 39 c1             	cmp    %rax,%r9
    5f51:	0f 8c 81 00 00 00    	jl     5fd8 <verify+0x1d8>
    5f57:	4c 39 d7             	cmp    %r10,%rdi
    5f5a:	0f 8d 8b 01 00 00    	jge    60eb <verify+0x2eb>
    5f60:	48 83 c3 01          	add    $0x1,%rbx
    5f64:	49 39 de             	cmp    %rbx,%r14
    5f67:	0f 8e b9 00 00 00    	jle    6026 <verify+0x226>
    5f6d:	49 8b 97 48 01 00 00 	mov    0x148(%r15),%rdx
    5f74:	48 89 d8             	mov    %rbx,%rax
    5f77:	48 c1 e0 05          	shl    $0x5,%rax
    5f7b:	49 03 83 48 01 00 00 	add    0x148(%r11),%rax
    5f82:	48 01 ea             	add    %rbp,%rdx
    5f85:	48 8b 08             	mov    (%rax),%rcx
    5f88:	48 8b 78 10          	mov    0x10(%rax),%rdi
    5f8c:	48 8b 32             	mov    (%rdx),%rsi
    5f8f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    5f93:	4c 8b 52 10          	mov    0x10(%rdx),%r10
    5f97:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    5f9b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    5f9f:	48 8b 40 18          	mov    0x18(%rax),%rax
    5fa3:	48 39 f1             	cmp    %rsi,%rcx
    5fa6:	7c 98                	jl     5f40 <verify+0x140>
    5fa8:	0f 8e 22 01 00 00    	jle    60d0 <verify+0x2d0>
    5fae:	4c 39 c2             	cmp    %r8,%rdx
    5fb1:	0f 8f 01 01 00 00    	jg     60b8 <verify+0x2b8>
    5fb7:	75 a7                	jne    5f60 <verify+0x160>
    5fb9:	4c 39 d7             	cmp    %r10,%rdi
    5fbc:	7f a2                	jg     5f60 <verify+0x160>
    5fbe:	49 39 c1             	cmp    %rax,%r9
    5fc1:	7d 15                	jge    5fd8 <verify+0x1d8>
    5fc3:	48 39 f1             	cmp    %rsi,%rcx
    5fc6:	75 98                	jne    5f60 <verify+0x160>
    5fc8:	4c 39 c2             	cmp    %r8,%rdx
    5fcb:	75 93                	jne    5f60 <verify+0x160>
    5fcd:	4c 39 d7             	cmp    %r10,%rdi
    5fd0:	75 8e                	jne    5f60 <verify+0x160>
    5fd2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5fd8:	49 89 c1             	mov    %rax,%r9
    5fdb:	48 89 f9             	mov    %rdi,%rcx
    5fde:	48 89 f2             	mov    %rsi,%rdx
    5fe1:	bf 01 00 00 00       	mov    $0x1,%edi
    5fe6:	48 8d 35 9b 14 00 00 	lea    0x149b(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    5fed:	31 c0                	xor    %eax,%eax
    5fef:	48 83 c3 01          	add    $0x1,%rbx
    5ff3:	e8 58 c4 ff ff       	call   2450 <__printf_chk@plt>
    5ff8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5ffd:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    6002:	4c 03 18             	add    (%rax),%r11
    6005:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    600a:	4d 8b b3 58 01 00 00 	mov    0x158(%r11),%r14
    6011:	4c 8b 20             	mov    (%rax),%r12
    6014:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6019:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    601d:	49 39 de             	cmp    %rbx,%r14
    6020:	0f 8f 47 ff ff ff    	jg     5f6d <verify+0x16d>
    6026:	4c 89 ea             	mov    %r13,%rdx
    6029:	4d 3b af 58 01 00 00 	cmp    0x158(%r15),%r13
    6030:	7d 14                	jge    6046 <verify+0x246>
    6032:	4d 8b b3 58 01 00 00 	mov    0x158(%r11),%r14
    6039:	48 83 c2 01          	add    $0x1,%rdx
    603d:	4d 85 f6             	test   %r14,%r14
    6040:	0f 8f da fe ff ff    	jg     5f20 <verify+0x120>
    6046:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    604b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6050:	48 83 c3 01          	add    $0x1,%rbx
    6054:	39 58 08             	cmp    %ebx,0x8(%rax)
    6057:	0f 8f 4b fe ff ff    	jg     5ea8 <verify+0xa8>
    605d:	4c 8b 6c 24 40       	mov    0x40(%rsp),%r13
    6062:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6067:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
    606c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6071:	49 83 c5 01          	add    $0x1,%r13
    6075:	44 39 68 08          	cmp    %r13d,0x8(%rax)
    6079:	0f 8f d8 fd ff ff    	jg     5e57 <verify+0x57>
    607f:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6084:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    6089:	48 81 44 24 10 40 01 00 00 	addq   $0x140,0x10(%rsp)
    6092:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6097:	41 39 c7             	cmp    %eax,%r15d
    609a:	74 5d                	je     60f9 <verify+0x2f9>
    609c:	41 89 c4             	mov    %eax,%r12d
    609f:	e9 8d fd ff ff       	jmp    5e31 <verify+0x31>
    60a4:	0f 1f 40 00          	nopl   0x0(%rax)
    60a8:	0f 85 b2 fe ff ff    	jne    5f60 <verify+0x160>
    60ae:	e9 a4 fe ff ff       	jmp    5f57 <verify+0x157>
    60b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    60b8:	4c 39 d7             	cmp    %r10,%rdi
    60bb:	0f 8d f8 fe ff ff    	jge    5fb9 <verify+0x1b9>
    60c1:	49 39 c1             	cmp    %rax,%r9
    60c4:	0f 8e ef fe ff ff    	jle    5fb9 <verify+0x1b9>
    60ca:	e9 09 ff ff ff       	jmp    5fd8 <verify+0x1d8>
    60cf:	90                   	nop
    60d0:	4c 39 c2             	cmp    %r8,%rdx
    60d3:	0f 8c 7e fe ff ff    	jl     5f57 <verify+0x157>
    60d9:	4c 39 d7             	cmp    %r10,%rdi
    60dc:	0f 8e dc fe ff ff    	jle    5fbe <verify+0x1be>
    60e2:	4c 39 c2             	cmp    %r8,%rdx
    60e5:	0f 85 75 fe ff ff    	jne    5f60 <verify+0x160>
    60eb:	49 39 c1             	cmp    %rax,%r9
    60ee:	0f 8f 6c fe ff ff    	jg     5f60 <verify+0x160>
    60f4:	e9 df fe ff ff       	jmp    5fd8 <verify+0x1d8>
    60f9:	48 81 44 24 18 40 01 00 00 	addq   $0x140,0x18(%rsp)
    6102:	41 8d 46 01          	lea    0x1(%r14),%eax
    6106:	45 39 f4             	cmp    %r14d,%r12d
    6109:	74 08                	je     6113 <verify+0x313>
    610b:	41 89 c6             	mov    %eax,%r14d
    610e:	e9 16 fd ff ff       	jmp    5e29 <verify+0x29>
    6113:	48 83 c4 58          	add    $0x58,%rsp
    6117:	31 c0                	xor    %eax,%eax
    6119:	5b                   	pop    %rbx
    611a:	5d                   	pop    %rbp
    611b:	41 5c                	pop    %r12
    611d:	41 5d                	pop    %r13
    611f:	41 5e                	pop    %r14
    6121:	41 5f                	pop    %r15
    6123:	c3                   	ret
    6124:	31 c0                	xor    %eax,%eax
    6126:	c3                   	ret

Disassembly of section .fini:

0000000000006128 <_fini>:
    6128:	f3 0f 1e fa          	endbr64
    612c:	48 83 ec 08          	sub    $0x8,%rsp
    6130:	48 83 c4 08          	add    $0x8,%rsp
    6134:	c3                   	ret
