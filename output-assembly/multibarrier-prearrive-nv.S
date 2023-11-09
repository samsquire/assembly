
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
    261d:	48 8d 05 dc 11 00 00 	lea    0x11dc(%rip),%rax        # 3800 <barriered_reset>
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
    27f5:	0f 84 4e 0e 00 00    	je     3649 <main+0x1059>
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
    2942:	be 00 02 00 00       	mov    $0x200,%esi
    2947:	bf 0c 00 00 00       	mov    $0xc,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    294c:	49 89 ef             	mov    %rbp,%r15
    294f:	48 8d 05 6a 0e 00 00 	lea    0xe6a(%rip),%rax        # 37c0 <do_protected_write>
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
    297e:	4c 8d a0 00 04 00 00 	lea    0x400(%rax),%r12
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2985:	be 08 00 00 00       	mov    $0x8,%esi
    298a:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    298f:	49 81 c6 00 02 00 00 	add    $0x200,%r14
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2996:	e8 05 fa ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    299b:	be 08 00 00 00       	mov    $0x8,%esi
    29a0:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29a5:	48 89 c5             	mov    %rax,%rbp
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29a8:	e8 f3 f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29ad:	be 18 00 00 00       	mov    $0x18,%esi
    29b2:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29b7:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29ba:	e8 e1 f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    29bf:	66 0f 6f 05 69 50 00 00 	movdqa 0x5069(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
          mailboxes[b].higher = &data[1];
    29c7:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29cb:	49 89 86 00 fe ff ff 	mov    %rax,-0x200(%r14)
          mailboxes[b].higher = &data[1];
    29d2:	49 89 b6 80 fe ff ff 	mov    %rsi,-0x180(%r14)
          data[0].messages = messages;
    29d9:	48 89 28             	mov    %rbp,(%rax)
          data[1].messages = messages2;
    29dc:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    29e0:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    29e4:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    29e8:	4d 39 e6             	cmp    %r12,%r14
    29eb:	75 98                	jne    2985 <main+0x395>
        char *message = malloc(sizeof(char) * 256);
    29ed:	be 01 00 00 00       	mov    $0x1,%esi
    29f2:	bf 00 01 00 00       	mov    $0x100,%edi
    29f7:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    29fb:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    2a00:	e8 9b f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a05:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a0a:	49 89 c4             	mov    %rax,%r12
        struct Message *messaged = malloc(sizeof(struct Message));
    2a0d:	e8 fe f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a12:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    2a17:	4c 89 e7             	mov    %r12,%rdi
    2a1a:	41 89 d9             	mov    %ebx,%r9d
    2a1d:	ba 00 01 00 00       	mov    $0x100,%edx
    2a22:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2a27:	be 01 00 00 00       	mov    $0x1,%esi
    2a2c:	31 c0                	xor    %eax,%eax
    2a2e:	48 8d 0d 8b 4b 00 00 	lea    0x4b8b(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a35:	e8 e6 fa ff ff       	call   2520 <__sprintf_chk@plt>
        messaged->message = message;
    2a3a:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
        messaged->thread_index = thread_data[x].thread_index;
    2a3f:	49 63 45 00          	movslq 0x0(%r13),%rax
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a43:	8d 4b 01             	lea    0x1(%rbx),%ecx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a46:	be 20 00 00 00       	mov    $0x20,%esi
    2a4b:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a50:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
        messaged->message = message;
    2a54:	4d 89 22             	mov    %r12,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a57:	4d 8b 65 28          	mov    0x28(%r13),%r12
        messaged->task_index = y;
    2a5b:	49 89 6a 10          	mov    %rbp,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a5f:	4b 8d 2c 3c          	lea    (%r12,%r15,1),%rbp
        messaged->thread_index = thread_data[x].thread_index;
    2a63:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a67:	89 8d 88 01 00 00    	mov    %ecx,0x188(%rbp)
        thread_data[x].tasks[y].message = messaged;
    2a6d:	4c 89 95 80 01 00 00 	mov    %r10,0x180(%rbp)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a74:	48 c7 85 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%rbp)
        messaged->thread_index = thread_data[x].thread_index;
    2a7f:	89 44 24 18          	mov    %eax,0x18(%rsp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a83:	e8 18 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a88:	8b 54 24 18          	mov    0x18(%rsp),%edx
        if (y == barrier_count - 1) {
    2a8c:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2a8f:	89 5d 00             	mov    %ebx,0x0(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a92:	48 89 85 48 01 00 00 	mov    %rax,0x148(%rbp)
        if (y == barrier_count - 1) {
    2a99:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
        thread_data[x].tasks[y].available = 1;
    2a9d:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2aa7:	48 89 85 38 01 00 00 	mov    %rax,0x138(%rbp)
        thread_data[x].tasks[y].sending = 1;
    2aae:	48 b8 01 00 00 00 0c 00 00 00 	movabs $0xc00000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2ab8:	48 c7 85 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%rbp)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2ac3:	89 95 30 01 00 00    	mov    %edx,0x130(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2ac9:	4c 89 ad 28 01 00 00 	mov    %r13,0x128(%rbp)
        thread_data[x].tasks[y].arrived = 0;
    2ad0:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        thread_data[x].tasks[y].thread_count = 2;
    2ada:	c7 85 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%rbp)
        thread_data[x].tasks[y].sending = 1;
    2ae4:	48 89 85 78 01 00 00 	mov    %rax,0x178(%rbp)
        if (y == barrier_count - 1) {
    2aeb:	0f 84 40 0b 00 00    	je     3631 <main+0x1041>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2af1:	8b 54 24 08          	mov    0x8(%rsp),%edx
    2af5:	39 d3                	cmp    %edx,%ebx
    2af7:	75 67                	jne    2b60 <main+0x570>
    2af9:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    2afd:	85 db                	test   %ebx,%ebx
    2aff:	7f 5f                	jg     2b60 <main+0x570>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2b01:	bf 01 00 00 00       	mov    $0x1,%edi
    2b06:	48 8d 35 db 4a 00 00 	lea    0x4adb(%rip),%rsi        # 75e8 <_IO_stdin_used+0x5e8>
    2b0d:	31 c0                	xor    %eax,%eax
    2b0f:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
    2b13:	e8 38 f9 ff ff       	call   2450 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b18:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    2b1d:	48 63 c3             	movslq %ebx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b20:	4d 8b 65 28          	mov    0x28(%r13),%r12
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b24:	48 89 c7             	mov    %rax,%rdi
    2b27:	48 c1 e0 04          	shl    $0x4,%rax
    2b2b:	48 01 c8             	add    %rcx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b2e:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b32:	49 89 45 40          	mov    %rax,0x40(%r13)
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
    2b56:	e9 e4 fd ff ff       	jmp    293f <main+0x34f>
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
    2bb4:	49 81 c5 b0 00 00 00 	add    $0xb0,%r13
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
    2c33:	4d 8d ba f0 08 00 00 	lea    0x8f0(%r10),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c3a:	4d 8d b2 60 01 00 00 	lea    0x160(%r10),%r14
    thread_data[x].threads = my_thread_data;
    2c41:	49 89 82 00 09 00 00 	mov    %rax,0x900(%r10)
    my_thread_data[0] = &thread_data[x]; 
    2c48:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c4b:	49 8d 8a 10 02 00 00 	lea    0x210(%r10),%rcx
    2c52:	49 8d 92 70 03 00 00 	lea    0x370(%r10),%rdx
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c59:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c5d:	49 8b 42 28          	mov    0x28(%r10),%rax
    2c61:	4d 8d 9a d0 04 00 00 	lea    0x4d0(%r10),%r11
    2c68:	4d 8d 8a 80 05 00 00 	lea    0x580(%r10),%r9
    2c6f:	49 8d b2 c0 02 00 00 	lea    0x2c0(%r10),%rsi
    2c76:	49 8d 9a 20 04 00 00 	lea    0x420(%r10),%rbx
    thread_data[x].thread_count = 2;
    2c7d:	41 c7 82 08 09 00 00 02 00 00 00 	movl   $0x2,0x908(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2c88:	48 89 4c 24 58       	mov    %rcx,0x58(%rsp)
    2c8d:	4d 8d 82 30 06 00 00 	lea    0x630(%r10),%r8
    2c94:	4d 8d aa e0 06 00 00 	lea    0x6e0(%r10),%r13
    2c9b:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    2ca0:	4d 8d a2 90 07 00 00 	lea    0x790(%r10),%r12
    thread_data[x].thread_index = 0;
    2ca7:	41 c7 82 f0 08 00 00 00 00 00 00 	movl   $0x0,0x8f0(%r10)
    thread_data[x].task_count = total_barrier_count;
    2cb2:	41 c7 82 20 09 00 00 03 00 00 00 	movl   $0x3,0x920(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2cbd:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cc7:	49 8d 82 b0 00 00 00 	lea    0xb0(%r10),%rax
    2cce:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2cd3:	49 8b 82 d8 00 00 00 	mov    0xd8(%r10),%rax
    2cda:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    2cdf:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2ce9:	49 8b 82 88 01 00 00 	mov    0x188(%r10),%rax
    2cf0:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2cf5:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2cff:	49 8b 82 38 02 00 00 	mov    0x238(%r10),%rax
    my_thread_data[0] = &thread_data[x]; 
    2d06:	4c 89 7c 24 70       	mov    %r15,0x70(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d0b:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d15:	49 8b 82 e8 02 00 00 	mov    0x2e8(%r10),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2d1c:	4c 89 74 24 78       	mov    %r14,0x78(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2d21:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d2b:	49 8b 82 98 03 00 00 	mov    0x398(%r10),%rax
    2d32:	48 89 74 24 50       	mov    %rsi,0x50(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2d37:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    2d3c:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d46:	49 8b 82 48 04 00 00 	mov    0x448(%r10),%rax
    2d4d:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    2d52:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d5c:	49 8b 82 f8 04 00 00 	mov    0x4f8(%r10),%rax
    2d63:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d6d:	49 8b 82 a8 05 00 00 	mov    0x5a8(%r10),%rax
    2d74:	4c 89 44 24 30       	mov    %r8,0x30(%rsp)
    2d79:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d83:	49 8b 82 58 06 00 00 	mov    0x658(%r10),%rax
    2d8a:	4c 89 94 24 80 00 00 00 	mov    %r10,0x80(%rsp)
    2d92:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2d9c:	49 8b 82 08 07 00 00 	mov    0x708(%r10),%rax
    2da3:	4c 89 6c 24 20       	mov    %r13,0x20(%rsp)
    2da8:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2db2:	49 8b 82 b8 07 00 00 	mov    0x7b8(%r10),%rax
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
    2e3b:	41 c7 82 48 08 00 00 00 00 00 00 	movl   $0x0,0x848(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2e46:	49 89 82 70 08 00 00 	mov    %rax,0x870(%r10)
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
    2ea2:	4d 8d b2 40 08 00 00 	lea    0x840(%r10),%r14
    2ea9:	4c 89 10             	mov    %r10,(%rax)
    2eac:	48 89 78 50          	mov    %rdi,0x50(%rax)
    2eb0:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    2eb5:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2eb9:	ba 0c 00 00 00       	mov    $0xc,%edx
    2ebe:	48 89 78 58          	mov    %rdi,0x58(%rax)
    2ec2:	49 8d ba a0 09 00 00 	lea    0x9a0(%r10),%rdi
    2ec9:	4c 89 58 38          	mov    %r11,0x38(%rax)
    2ecd:	4c 89 48 40          	mov    %r9,0x40(%rax)
    2ed1:	4c 89 40 48          	mov    %r8,0x48(%rax)
    2ed5:	4c 89 70 60          	mov    %r14,0x60(%rax)
    2ed9:	4c 89 78 68          	mov    %r15,0x68(%rax)
    2edd:	4c 8d 3d 8c 09 00 00 	lea    0x98c(%rip),%r15        # 3870 <barriered_thread>
    2ee4:	48 89 78 70          	mov    %rdi,0x70(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2ee8:	49 89 82 50 08 00 00 	mov    %rax,0x850(%r10)
    2eef:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2ef1:	41 c7 82 58 08 00 00 0c 00 00 00 	movl   $0xc,0x858(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2efc:	41 c7 82 60 08 00 00 02 00 00 00 	movl   $0x2,0x860(%r10)
  thread_data[thread_count].thread_index = 0;
    2f07:	41 c7 82 40 08 00 00 00 00 00 00 	movl   $0x0,0x840(%r10)
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
    2f3a:	48 8d 15 9f 0c 00 00 	lea    0xc9f(%rip),%rdx        # 3be0 <timer_thread>
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
    2f66:	c7 45 34 01 00 00 00 	movl   $0x1,0x34(%rbp)
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
    2f89:	48 81 c5 b0 00 00 00 	add    $0xb0,%rbp
    2f90:	48 83 c3 08          	add    $0x8,%rbx
    2f94:	49 83 c4 38          	add    $0x38,%r12
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2f98:	e8 d3 f4 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2f9d:	48 8b 55 f0          	mov    -0x10(%rbp),%rdx
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
    2fd1:	49 89 9a 20 09 00 00 	mov    %rbx,0x920(%r10)
    thread_data[x].type = IO;
    2fd8:	41 c7 82 f8 08 00 00 02 00 00 00 	movl   $0x2,0x8f8(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2fe3:	e8 b8 f3 ff ff       	call   23a0 <calloc@plt>
    2fe8:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2ff0:	be 00 08 00 00       	mov    $0x800,%esi
    2ff5:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ff7:	49 89 82 38 09 00 00 	mov    %rax,0x938(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2ffe:	e8 ad f4 ff ff       	call   24b0 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3003:	be 08 00 00 00       	mov    $0x8,%esi
    3008:	bf 0c 00 00 00       	mov    $0xc,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    300d:	4c 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%r10
    3015:	41 89 82 40 09 00 00 	mov    %eax,0x940(%r10)
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
    306f:	49 89 82 00 09 00 00 	mov    %rax,0x900(%r10)
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3076:	41 c7 82 08 09 00 00 0c 00 00 00 	movl   $0xc,0x908(%r10)
    thread_data[x].thread_index = x;
    3081:	41 c7 82 f0 08 00 00 0d 00 00 00 	movl   $0xd,0x8f0(%r10)
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
    30da:	48 8d 15 6f 1d 00 00 	lea    0x1d6f(%rip),%rdx        # 4e50 <io_thread>
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
    311b:	49 89 9a d0 09 00 00 	mov    %rbx,0x9d0(%r10)
    3122:	31 db                	xor    %ebx,%ebx
    thread_data[x].type = EXTERNAL;
    3124:	41 c7 82 a8 09 00 00 03 00 00 00 	movl   $0x3,0x9a8(%r10)
    thread_data[x].buffers = &buffers[buffer_index];
    312f:	49 89 82 e0 09 00 00 	mov    %rax,0x9e0(%r10)
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
    31aa:	48 8d 15 6f 09 00 00 	lea    0x96f(%rip),%rdx        # 3b20 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    31b1:	4c 89 58 48          	mov    %r11,0x48(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    31b5:	48 81 c6 10 03 00 00 	add    $0x310,%rsi
      my_thread_data[n] = &thread_data[n]; 
    31bc:	4c 89 48 50          	mov    %r9,0x50(%rax)
    31c0:	4c 89 40 58          	mov    %r8,0x58(%rax)
    thread_data[x].threads = my_thread_data;
    31c4:	49 89 82 b0 09 00 00 	mov    %rax,0x9b0(%r10)
      my_thread_data[n] = &thread_data[n]; 
    31cb:	4c 89 78 08          	mov    %r15,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    31cf:	48 8b 05 82 48 00 00 	mov    0x4882(%rip),%rax        # 7a58 <_IO_stdin_used+0xa58>
    thread_data[x].thread_index = x;
    31d6:	41 c7 82 a0 09 00 00 0e 00 00 00 	movl   $0xe,0x9a0(%r10)
    thread_data[x].thread_count = thread_count;
    31e1:	49 89 82 b8 09 00 00 	mov    %rax,0x9b8(%r10)
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
    3238:	4d 8d 6e 28          	lea    0x28(%r14),%r13
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
    32b0:	0f 8e 07 04 00 00    	jle    36bd <main+0x10cd>
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
    32e6:	49 8d 04 44          	lea    (%r12,%rax,2),%rax
    32ea:	48 c1 e0 04          	shl    $0x4,%rax
    32ee:	48 01 f8             	add    %rdi,%rax
    32f1:	48 63 70 30          	movslq 0x30(%rax),%rsi
    32f5:	85 f6                	test   %esi,%esi
    32f7:	7e 21                	jle    331a <main+0xd2a>
    32f9:	48 8b 40 28          	mov    0x28(%rax),%rax
    32fd:	48 c1 e6 09          	shl    $0x9,%rsi
    3301:	48 01 c6             	add    %rax,%rsi
    3304:	0f 1f 40 00          	nopl   0x0(%rax)
      v += thread_data[other].tasks[n].v;
    3308:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    330f:	48 05 00 02 00 00    	add    $0x200,%rax
    3315:	48 39 f0             	cmp    %rsi,%rax
    3318:	75 ee                	jne    3308 <main+0xd18>
    331a:	48 8d 35 9f 40 00 00 	lea    0x409f(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    3321:	bf 01 00 00 00       	mov    $0x1,%edi
    3326:	31 c0                	xor    %eax,%eax
    3328:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    332d:	e8 1e f1 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3332:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3337:	bf 01 00 00 00       	mov    $0x1,%edi
    333c:	48 8b 30             	mov    (%rax),%rsi
    333f:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3349:	48 f7 ee             	imul   %rsi
    334c:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3350:	31 c0                	xor    %eax,%eax
    3352:	48 d1 fa             	sar    %rdx
    3355:	48 29 f2             	sub    %rsi,%rdx
    3358:	48 8d 35 d1 42 00 00 	lea    0x42d1(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    335f:	e8 ec f0 ff ff       	call   2450 <__printf_chk@plt>
    3364:	bf 0a 00 00 00       	mov    $0xa,%edi
    3369:	e8 62 ef ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    336e:	49 63 47 08          	movslq 0x8(%r15),%rax
    3372:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3377:	85 c0                	test   %eax,%eax
    3379:	0f 8e e5 00 00 00    	jle    3464 <main+0xe74>
    337f:	49 8b 17             	mov    (%r15),%rdx
    3382:	48 c1 e0 09          	shl    $0x9,%rax
    3386:	48 8d 34 10          	lea    (%rax,%rdx,1),%rsi
    338a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3390:	48 8b 82 68 01 00 00 	mov    0x168(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    3397:	4c 03 aa 08 01 00 00 	add    0x108(%rdx),%r13
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    339e:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
      ingests += thread_data[x].tasks[n].ingest_count;
    33a5:	4c 03 b2 60 ff ff ff 	add    -0xa0(%rdx),%r14
      sends += thread_data[x].tasks[n].sends;
    33ac:	4c 03 8a 70 ff ff ff 	add    -0x90(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33b3:	48 03 a8 00 01 00 00 	add    0x100(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33ba:	48 03 98 80 01 00 00 	add    0x180(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33c1:	48 03 a8 00 03 00 00 	add    0x300(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33c8:	48 03 98 80 03 00 00 	add    0x380(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33cf:	48 03 a8 00 05 00 00 	add    0x500(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33d6:	48 03 98 80 05 00 00 	add    0x580(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33dd:	48 03 a8 00 07 00 00 	add    0x700(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33e4:	48 03 98 80 07 00 00 	add    0x780(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33eb:	48 03 a8 00 09 00 00 	add    0x900(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    33f2:	48 03 98 80 09 00 00 	add    0x980(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    33f9:	48 03 a8 00 0b 00 00 	add    0xb00(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3400:	48 03 98 80 0b 00 00 	add    0xb80(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3407:	48 03 a8 00 0d 00 00 	add    0xd00(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    340e:	48 03 98 80 0d 00 00 	add    0xd80(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3415:	48 03 a8 00 0f 00 00 	add    0xf00(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    341c:	48 03 98 80 0f 00 00 	add    0xf80(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3423:	48 03 a8 00 11 00 00 	add    0x1100(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    342a:	48 03 98 80 11 00 00 	add    0x1180(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3431:	48 03 a8 00 13 00 00 	add    0x1300(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3438:	48 03 98 80 13 00 00 	add    0x1380(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    343f:	48 03 a8 00 15 00 00 	add    0x1500(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3446:	48 03 98 80 15 00 00 	add    0x1580(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    344d:	48 03 a8 00 17 00 00 	add    0x1700(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3454:	48 03 98 80 17 00 00 	add    0x1780(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    345b:	48 39 f2             	cmp    %rsi,%rdx
    345e:	0f 85 2c ff ff ff    	jne    3390 <main+0xda0>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3464:	45 31 e4             	xor    %r12d,%r12d
    3467:	49 83 7f 68 00       	cmpq   $0x0,0x68(%r15)
    346c:	7e 78                	jle    34e6 <main+0xef6>
    346e:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    3473:	4c 89 fb             	mov    %r15,%rbx
    3476:	4d 89 e7             	mov    %r12,%r15
    3479:	4d 89 cc             	mov    %r9,%r12
    347c:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3480:	48 8b 43 58          	mov    0x58(%rbx),%rax
    3484:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    3488:	48 83 ec 08          	sub    $0x8,%rsp
    348c:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3491:	49 83 c7 01          	add    $0x1,%r15
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3495:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3499:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    34a3:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    34a7:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    34ab:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    34ae:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    34b2:	4c 2b 01             	sub    (%rcx),%r8
    34b5:	31 c0                	xor    %eax,%eax
    34b7:	8b 49 20             	mov    0x20(%rcx),%ecx
    34ba:	56                   	push   %rsi
    34bb:	48 8d 35 8e 41 00 00 	lea    0x418e(%rip),%rsi        # 7650 <_IO_stdin_used+0x650>
    34c2:	48 c1 ea 12          	shr    $0x12,%rdx
    34c6:	49 89 d1             	mov    %rdx,%r9
    34c9:	ba 02 00 00 00       	mov    $0x2,%edx
    34ce:	e8 7d ef ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    34d3:	58                   	pop    %rax
    34d4:	5a                   	pop    %rdx
    34d5:	4c 39 7b 68          	cmp    %r15,0x68(%rbx)
    34d9:	7f a5                	jg     3480 <main+0xe90>
    34db:	49 89 df             	mov    %rbx,%r15
    34de:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    34e3:	4d 89 e1             	mov    %r12,%r9
  for (int x = 0 ; x < thread_count ; x++) {
    34e6:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    34ec:	49 81 c7 b0 00 00 00 	add    $0xb0,%r15
    34f3:	83 7c 24 10 0c       	cmpl   $0xc,0x10(%rsp)
    34f8:	0f 85 60 fd ff ff    	jne    325e <main+0xc6e>
    34fe:	4c 89 ea             	mov    %r13,%rdx
    3501:	48 8d 35 c5 3e 00 00 	lea    0x3ec5(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    3508:	31 c0                	xor    %eax,%eax
    350a:	4d 89 cf             	mov    %r9,%r15
    350d:	bf 01 00 00 00       	mov    $0x1,%edi
    3512:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3517:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    3521:	e8 2a ef ff ff       	call   2450 <__printf_chk@plt>
    3526:	bf 0a 00 00 00       	mov    $0xa,%edi
    352b:	e8 a0 ed ff ff       	call   22d0 <putchar@plt>
    3530:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    3535:	bf 01 00 00 00       	mov    $0x1,%edi
    353a:	48 8d 35 5f 41 00 00 	lea    0x415f(%rip),%rsi        # 76a0 <_IO_stdin_used+0x6a0>
    3541:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3545:	31 c0                	xor    %eax,%eax
    3547:	e8 04 ef ff ff       	call   2450 <__printf_chk@plt>
    354c:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3551:	bf 01 00 00 00       	mov    $0x1,%edi
    3556:	48 8d 35 6b 41 00 00 	lea    0x416b(%rip),%rsi        # 76c8 <_IO_stdin_used+0x6c8>
    355d:	4c 89 c8             	mov    %r9,%rax
    3560:	49 c1 f9 3f          	sar    $0x3f,%r9
    3564:	49 f7 ec             	imul   %r12
    3567:	31 c0                	xor    %eax,%eax
    3569:	48 d1 fa             	sar    %rdx
    356c:	4c 29 ca             	sub    %r9,%rdx
    356f:	e8 dc ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3574:	4c 89 f8             	mov    %r15,%rax
    3577:	4d 89 fb             	mov    %r15,%r11
    357a:	bf 01 00 00 00       	mov    $0x1,%edi
    357f:	49 f7 ec             	imul   %r12
    3582:	49 c1 fb 3f          	sar    $0x3f,%r11
    3586:	48 8d 35 6b 41 00 00 	lea    0x416b(%rip),%rsi        # 76f8 <_IO_stdin_used+0x6f8>
    358d:	31 c0                	xor    %eax,%eax
    358f:	48 d1 fa             	sar    %rdx
    3592:	4c 29 da             	sub    %r11,%rdx
    3595:	e8 b6 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    359a:	4c 89 e8             	mov    %r13,%rax
    359d:	4c 89 e9             	mov    %r13,%rcx
    35a0:	bf 01 00 00 00       	mov    $0x1,%edi
    35a5:	49 f7 ec             	imul   %r12
    35a8:	48 c1 f9 3f          	sar    $0x3f,%rcx
    35ac:	48 8d 35 75 41 00 00 	lea    0x4175(%rip),%rsi        # 7728 <_IO_stdin_used+0x728>
    35b3:	31 c0                	xor    %eax,%eax
    35b5:	48 d1 fa             	sar    %rdx
    35b8:	48 29 ca             	sub    %rcx,%rdx
    35bb:	e8 90 ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    35c0:	48 89 e8             	mov    %rbp,%rax
    35c3:	48 c1 fd 3f          	sar    $0x3f,%rbp
    35c7:	48 8d 35 13 3e 00 00 	lea    0x3e13(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    35ce:	49 f7 ec             	imul   %r12
    35d1:	bf 01 00 00 00       	mov    $0x1,%edi
    35d6:	31 c0                	xor    %eax,%eax
    35d8:	48 d1 fa             	sar    %rdx
    35db:	48 29 ea             	sub    %rbp,%rdx
    35de:	e8 6d ee ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    35e3:	48 89 d8             	mov    %rbx,%rax
    35e6:	48 c1 fb 3f          	sar    $0x3f,%rbx
    35ea:	48 8d 35 01 3e 00 00 	lea    0x3e01(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    35f1:	49 f7 ec             	imul   %r12
    35f4:	bf 01 00 00 00       	mov    $0x1,%edi
    35f9:	48 d1 fa             	sar    %rdx
    35fc:	48 29 da             	sub    %rbx,%rdx
    35ff:	31 c0                	xor    %eax,%eax
    3601:	e8 4a ee ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3606:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    360e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3617:	0f 85 a7 00 00 00    	jne    36c4 <main+0x10d4>
    361d:	48 81 c4 b8 00 00 00 	add    $0xb8,%rsp
    3624:	31 c0                	xor    %eax,%eax
    3626:	5b                   	pop    %rbx
    3627:	5d                   	pop    %rbp
    3628:	41 5c                	pop    %r12
    362a:	41 5d                	pop    %r13
    362c:	41 5e                	pop    %r14
    362e:	41 5f                	pop    %r15
    3630:	c3                   	ret
          thread_data[x].tasks[y].run = barriered_work; 
    3631:	48 8d 05 e8 21 00 00 	lea    0x21e8(%rip),%rax        # 5820 <barriered_work>
    3638:	bb 02 00 00 00       	mov    $0x2,%ebx
    363d:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3644:	e9 f6 f2 ff ff       	jmp    293f <main+0x34f>
      other = (x + 1) % total_threads;
    3649:	b8 89 88 88 88       	mov    $0x88888889,%eax
    364e:	45 89 fe             	mov    %r15d,%r14d
      my_thread_data[0] = &thread_data[x]; 
    3651:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    3656:	4c 89 e9             	mov    %r13,%rcx
      other = (x + 1) % total_threads;
    3659:	4c 0f af f0          	imul   %rax,%r14
      thread_data[x].thread_index = 0;
    365d:	41 c7 45 00 00 00 00 00 	movl   $0x0,0x0(%r13)
    3665:	48 8d 35 9d 3c 00 00 	lea    0x3c9d(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
      my_thread_data[0] = &thread_data[x]; 
    366c:	4c 89 2f             	mov    %r13,(%rdi)
      other = (x + 1) % total_threads;
    366f:	49 c1 ee 23          	shr    $0x23,%r14
    3673:	44 89 f0             	mov    %r14d,%eax
    3676:	c1 e0 04             	shl    $0x4,%eax
    3679:	44 29 f0             	sub    %r14d,%eax
    367c:	45 89 fe             	mov    %r15d,%r14d
    367f:	41 29 c6             	sub    %eax,%r14d
      my_thread_data[1] = &thread_data[other]; 
    3682:	49 63 c6             	movslq %r14d,%rax
    3685:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3689:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    368d:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    3692:	89 ea                	mov    %ebp,%edx
    3694:	49 c1 e0 04          	shl    $0x4,%r8
    3698:	49 01 c0             	add    %rax,%r8
    369b:	31 c0                	xor    %eax,%eax
    369d:	4c 89 47 08          	mov    %r8,0x8(%rdi)
    36a1:	bf 01 00 00 00       	mov    $0x1,%edi
    36a6:	e8 a5 ed ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    36ab:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    36b0:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    36b5:	49 89 c4             	mov    %rax,%r12
    36b8:	e9 7f f1 ff ff       	jmp    283c <main+0x24c>
    long v = 0;
    36bd:	31 d2                	xor    %edx,%edx
    36bf:	e9 16 fc ff ff       	jmp    32da <main+0xcea>
}
    36c4:	e8 67 ec ff ff       	call   2330 <__stack_chk_fail@plt>
    36c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000036d0 <_start>:
    36d0:	f3 0f 1e fa          	endbr64
    36d4:	31 ed                	xor    %ebp,%ebp
    36d6:	49 89 d1             	mov    %rdx,%r9
    36d9:	5e                   	pop    %rsi
    36da:	48 89 e2             	mov    %rsp,%rdx
    36dd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    36e1:	50                   	push   %rax
    36e2:	54                   	push   %rsp
    36e3:	45 31 c0             	xor    %r8d,%r8d
    36e6:	31 c9                	xor    %ecx,%ecx
    36e8:	48 8d 3d 01 ef ff ff 	lea    -0x10ff(%rip),%rdi        # 25f0 <main>
    36ef:	ff 15 e3 68 00 00    	call   *0x68e3(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    36f5:	f4                   	hlt
    36f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003700 <deregister_tm_clones>:
    3700:	48 8d 3d 19 69 00 00 	lea    0x6919(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3707:	48 8d 05 12 69 00 00 	lea    0x6912(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    370e:	48 39 f8             	cmp    %rdi,%rax
    3711:	74 15                	je     3728 <deregister_tm_clones+0x28>
    3713:	48 8b 05 c6 68 00 00 	mov    0x68c6(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    371a:	48 85 c0             	test   %rax,%rax
    371d:	74 09                	je     3728 <deregister_tm_clones+0x28>
    371f:	ff e0                	jmp    *%rax
    3721:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3728:	c3                   	ret
    3729:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003730 <register_tm_clones>:
    3730:	48 8d 3d e9 68 00 00 	lea    0x68e9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    3737:	48 8d 35 e2 68 00 00 	lea    0x68e2(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    373e:	48 29 fe             	sub    %rdi,%rsi
    3741:	48 89 f0             	mov    %rsi,%rax
    3744:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3748:	48 c1 f8 03          	sar    $0x3,%rax
    374c:	48 01 c6             	add    %rax,%rsi
    374f:	48 d1 fe             	sar    %rsi
    3752:	74 14                	je     3768 <register_tm_clones+0x38>
    3754:	48 8b 05 95 68 00 00 	mov    0x6895(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    375b:	48 85 c0             	test   %rax,%rax
    375e:	74 08                	je     3768 <register_tm_clones+0x38>
    3760:	ff e0                	jmp    *%rax
    3762:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3768:	c3                   	ret
    3769:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003770 <__do_global_dtors_aux>:
    3770:	f3 0f 1e fa          	endbr64
    3774:	80 3d ad 68 00 00 00 	cmpb   $0x0,0x68ad(%rip)        # a028 <completed.0>
    377b:	75 2b                	jne    37a8 <__do_global_dtors_aux+0x38>
    377d:	55                   	push   %rbp
    377e:	48 83 3d 72 68 00 00 00 	cmpq   $0x0,0x6872(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3786:	48 89 e5             	mov    %rsp,%rbp
    3789:	74 0c                	je     3797 <__do_global_dtors_aux+0x27>
    378b:	48 8b 3d 76 68 00 00 	mov    0x6876(%rip),%rdi        # a008 <__dso_handle>
    3792:	e8 19 eb ff ff       	call   22b0 <__cxa_finalize@plt>
    3797:	e8 64 ff ff ff       	call   3700 <deregister_tm_clones>
    379c:	c6 05 85 68 00 00 01 	movb   $0x1,0x6885(%rip)        # a028 <completed.0>
    37a3:	5d                   	pop    %rbp
    37a4:	c3                   	ret
    37a5:	0f 1f 00             	nopl   (%rax)
    37a8:	c3                   	ret
    37a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037b0 <frame_dummy>:
    37b0:	f3 0f 1e fa          	endbr64
    37b4:	e9 77 ff ff ff       	jmp    3730 <register_tm_clones>
    37b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000037c0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    37c0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    37c4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    37cb:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    37cf:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    37d7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    37db:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    37df:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    37e6:	48 85 c9             	test   %rcx,%rcx
    37e9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    37f0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    37f4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    37f8:	31 c0                	xor    %eax,%eax
    37fa:	c3                   	ret
    37fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003800 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3800:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3804:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    380b:	85 c9                	test   %ecx,%ecx
    380d:	7e 4f                	jle    385e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    380f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3816:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    381d:	48 c1 e1 09          	shl    $0x9,%rcx
    3821:	48 8b 50 10          	mov    0x10(%rax),%rdx
    3825:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3829:	48 8b 70 28          	mov    0x28(%rax),%rsi
    382d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    382f:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    3833:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3838:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3840:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3848:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3853:	48 05 00 02 00 00    	add    $0x200,%rax
    3859:	48 39 c1             	cmp    %rax,%rcx
    385c:	75 da                	jne    3838 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    385e:	0f ae f8             	sfence
}
    3861:	31 c0                	xor    %eax,%eax
    3863:	c3                   	ret
    3864:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    386f:	90                   	nop

0000000000003870 <barriered_thread>:
void* barriered_thread(void *arg) {
    3870:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3874:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    3878:	0f 85 90 02 00 00    	jne    3b0e <barriered_thread+0x29e>
void* barriered_thread(void *arg) {
    387e:	41 56                	push   %r14
    3880:	41 55                	push   %r13
    3882:	49 89 fd             	mov    %rdi,%r13
    3885:	41 54                	push   %r12
    3887:	55                   	push   %rbp
    3888:	31 ed                	xor    %ebp,%ebp
    388a:	53                   	push   %rbx
    388b:	31 db                	xor    %ebx,%ebx
    388d:	0f 1f 00             	nopl   (%rax)
    if (t >= data->task_count) {
    3890:	41 8b 55 30          	mov    0x30(%r13),%edx
    3894:	39 da                	cmp    %ebx,%edx
    3896:	7f 12                	jg     38aa <barriered_thread+0x3a>
      data->cycles++;
    3898:	49 83 85 98 00 00 00 01 	addq   $0x1,0x98(%r13)
    for (; t < data->task_count; t++) {
    38a0:	31 db                	xor    %ebx,%ebx
    38a2:	85 d2                	test   %edx,%edx
    38a4:	0f 8e 56 01 00 00    	jle    3a00 <barriered_thread+0x190>
    38aa:	4c 63 e3             	movslq %ebx,%r12
    38ad:	49 c1 e4 09          	shl    $0x9,%r12
    38b1:	eb 17                	jmp    38ca <barriered_thread+0x5a>
    38b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    38b8:	83 c3 01             	add    $0x1,%ebx
    38bb:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    38c2:	39 d3                	cmp    %edx,%ebx
    38c4:	0f 8d 36 01 00 00    	jge    3a00 <barriered_thread+0x190>
      if (data->tasks[t].available == 1) {
    38ca:	49 8b 45 28          	mov    0x28(%r13),%rax
    38ce:	4a 8d 34 20          	lea    (%rax,%r12,1),%rsi
    38d2:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    38d9:	75 dd                	jne    38b8 <barriered_thread+0x48>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    38db:	41 8b 7d 18          	mov    0x18(%r13),%edi
          previous = t - 1;
    38df:	83 ea 01             	sub    $0x1,%edx
    38e2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    38e5:	85 db                	test   %ebx,%ebx
    38e7:	0f 4f d1             	cmovg  %ecx,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    38ea:	85 ff                	test   %edi,%edi
    38ec:	0f 8e 3e 01 00 00    	jle    3a30 <barriered_thread+0x1c0>
    38f2:	49 8b 45 10          	mov    0x10(%r13),%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    38f6:	48 63 ca             	movslq %edx,%rcx
    38f9:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    38fc:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    38ff:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    3906:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    390d:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    3911:	45 31 f6             	xor    %r14d,%r14d
    3914:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3918:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3920:	48 8b 10             	mov    (%rax),%rdx
    3923:	4c 8b 5a 28          	mov    0x28(%rdx),%r11
    3927:	49 01 cb             	add    %rcx,%r11
    392a:	4c 89 da             	mov    %r11,%rdx
    392d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    3934:	75 04                	jne    393a <barriered_thread+0xca>
            arrived++;
    3936:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    393a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    3941:	75 04                	jne    3947 <barriered_thread+0xd7>
            prearrive++;
    3943:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3947:	48 83 c0 08          	add    $0x8,%rax
    394b:	48 39 f0             	cmp    %rsi,%rax
    394e:	75 d0                	jne    3920 <barriered_thread+0xb0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    3950:	44 39 d7             	cmp    %r10d,%edi
    3953:	0f 84 c7 00 00 00    	je     3a20 <barriered_thread+0x1b0>
    3959:	45 85 d2             	test   %r10d,%r10d
    395c:	0f 84 be 00 00 00    	je     3a20 <barriered_thread+0x1b0>
        if (arrived == 0 || arrived == data->thread_count) {
    3962:	45 85 f6             	test   %r14d,%r14d
    3965:	74 0a                	je     3971 <barriered_thread+0x101>
    3967:	45 39 75 18          	cmp    %r14d,0x18(%r13)
    396b:	0f 85 8f 00 00 00    	jne    3a00 <barriered_thread+0x190>
    3971:	49 8b 45 28          	mov    0x28(%r13),%rax
          data->tasks[t].prearrive++;
    3975:	4c 01 e0             	add    %r12,%rax
    3978:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    397f:	85 db                	test   %ebx,%ebx
    3981:	75 0e                	jne    3991 <barriered_thread+0x121>
    3983:	49 8b 75 70          	mov    0x70(%r13),%rsi
    3987:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    398b:	0f 8c 5f 01 00 00    	jl     3af0 <barriered_thread+0x280>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    3991:	49 63 4d 00          	movslq 0x0(%r13),%rcx
    3995:	49 8b 55 10          	mov    0x10(%r13),%rdx
          data->tasks[t].available = 0;
    3999:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    39a3:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    39a7:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
    39ab:	4c 01 e7             	add    %r12,%rdi
    39ae:	ff 90 18 01 00 00    	call   *0x118(%rax)
          data->tasks[t].arrived++;
    39b4:	49 8b 45 28          	mov    0x28(%r13),%rax
    39b8:	4c 01 e0             	add    %r12,%rax
    39bb:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    39c2:	41 8b 45 30          	mov    0x30(%r13),%eax
          data->iteration_count++;
    39c6:	49 83 45 68 01       	addq   $0x1,0x68(%r13)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    39cb:	83 e8 01             	sub    $0x1,%eax
    39ce:	39 d8                	cmp    %ebx,%eax
    39d0:	0f 84 b2 00 00 00    	je     3a88 <barriered_thread+0x218>
          asm volatile ("sfence" ::: "memory");
    39d6:	0f ae f8             	sfence
          if (waiting == 0) {
    39d9:	85 ed                	test   %ebp,%ebp
    39db:	0f 84 d7 00 00 00    	je     3ab8 <barriered_thread+0x248>
    for (; t < data->task_count; t++) {
    39e1:	41 8b 55 30          	mov    0x30(%r13),%edx
    39e5:	83 c3 01             	add    $0x1,%ebx
    39e8:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    39ef:	39 d3                	cmp    %edx,%ebx
    39f1:	0f 8c d3 fe ff ff    	jl     38ca <barriered_thread+0x5a>
    39f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  while (data->running == 1) {
    3a00:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
    3a05:	0f 84 85 fe ff ff    	je     3890 <barriered_thread+0x20>
}
    3a0b:	5b                   	pop    %rbx
    3a0c:	31 c0                	xor    %eax,%eax
    3a0e:	5d                   	pop    %rbp
    3a0f:	41 5c                	pop    %r12
    3a11:	41 5d                	pop    %r13
    3a13:	41 5e                	pop    %r14
    3a15:	c3                   	ret
    3a16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
    3a20:	83 fd 01             	cmp    $0x1,%ebp
    3a23:	74 1b                	je     3a40 <barriered_thread+0x1d0>
        int arrived = 0; 
    3a25:	31 ed                	xor    %ebp,%ebp
    3a27:	e9 36 ff ff ff       	jmp    3962 <barriered_thread+0xf2>
    3a2c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    3a30:	83 fd 01             	cmp    $0x1,%ebp
    3a33:	0f 85 3c ff ff ff    	jne    3975 <barriered_thread+0x105>
        int arrived = 0; 
    3a39:	45 31 f6             	xor    %r14d,%r14d
    3a3c:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3a40:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    3a47:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    3a4c:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3a4e:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3a52:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    3a59:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3a5e:	e8 ad e8 ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3a63:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    3a6a:	48 83 c0 01          	add    $0x1,%rax
    3a6e:	48 99                	cqto
    3a70:	49 f7 bd 90 00 00 00 	idivq  0x90(%r13)
    3a77:	49 89 95 88 00 00 00 	mov    %rdx,0x88(%r13)
            waiting = 0; 
    3a7e:	e9 df fe ff ff       	jmp    3962 <barriered_thread+0xf2>
    3a83:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3a88:	49 8b 75 70          	mov    0x70(%r13),%rsi
    3a8c:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    3a90:	0f 8d 40 ff ff ff    	jge    39d6 <barriered_thread+0x166>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    3a96:	48 c1 e6 04          	shl    $0x4,%rsi
    3a9a:	bf 04 00 00 00       	mov    $0x4,%edi
    3a9f:	49 03 75 60          	add    0x60(%r13),%rsi
    3aa3:	e8 68 e8 ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3aa8:	49 83 45 70 01       	addq   $0x1,0x70(%r13)
    3aad:	e9 24 ff ff ff       	jmp    39d6 <barriered_thread+0x166>
    3ab2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    3ab8:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3abf:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3ac4:	bd 01 00 00 00       	mov    $0x1,%ebp
            data->task_snapshot[data->task_timestamp_count].task = t;
    3ac9:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3acd:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    3ad4:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3ad8:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3adb:	e8 30 e8 ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3ae0:	41 8b 55 30          	mov    0x30(%r13),%edx
    3ae4:	e9 cf fd ff ff       	jmp    38b8 <barriered_thread+0x48>
    3ae9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3af0:	48 c1 e6 04          	shl    $0x4,%rsi
    3af4:	bf 04 00 00 00       	mov    $0x4,%edi
    3af9:	49 03 75 58          	add    0x58(%r13),%rsi
    3afd:	e8 0e e8 ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3b02:	49 8b 45 28          	mov    0x28(%r13),%rax
    3b06:	4c 01 e0             	add    %r12,%rax
    3b09:	e9 83 fe ff ff       	jmp    3991 <barriered_thread+0x121>
}
    3b0e:	31 c0                	xor    %eax,%eax
    3b10:	c3                   	ret
    3b11:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3b1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003b20 <external_thread>:
void * external_thread(void *arg) {
    3b20:	f3 0f 1e fa          	endbr64
    3b24:	41 55                	push   %r13
    3b26:	41 54                	push   %r12
    3b28:	55                   	push   %rbp
    3b29:	53                   	push   %rbx
    3b2a:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    3b2e:	66 0f 6f 05 0a 3e 00 00 	movdqa 0x3e0a(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
void * external_thread(void *arg) {
    3b36:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3b3f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3b44:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3b46:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
  struct timespec req = {
    3b4a:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    3b4e:	75 64                	jne    3bb4 <external_thread+0x94>
    3b50:	49 89 fd             	mov    %rdi,%r13
    3b53:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3b58:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    3b5b:	4c 8d 25 a2 34 00 00 	lea    0x34a2(%rip),%r12        # 7004 <_IO_stdin_used+0x4>
    3b62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    nanosleep(&req , &rem);
    3b68:	48 89 ee             	mov    %rbp,%rsi
    3b6b:	48 89 df             	mov    %rbx,%rdi
    3b6e:	e8 dd e7 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3b73:	49 8b 45 40          	mov    0x40(%r13),%rax
    3b77:	48 63 10             	movslq (%rax),%rdx
    3b7a:	85 d2                	test   %edx,%edx
    3b7c:	7e 2c                	jle    3baa <external_thread+0x8a>
    3b7e:	48 8b 40 08          	mov    0x8(%rax),%rax
    3b82:	48 c1 e2 04          	shl    $0x4,%rdx
    3b86:	48 01 c2             	add    %rax,%rdx
    3b89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    3b90:	8b 48 08             	mov    0x8(%rax),%ecx
    3b93:	85 c9                	test   %ecx,%ecx
    3b95:	75 0a                	jne    3ba1 <external_thread+0x81>
        data->buffers->buffer[x].data = "Hello world";
    3b97:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    3b9a:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3ba1:	48 83 c0 10          	add    $0x10,%rax
    3ba5:	48 39 c2             	cmp    %rax,%rdx
    3ba8:	75 e6                	jne    3b90 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    3baa:	0f ae f0             	mfence
  while (data->running == 1) {
    3bad:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
    3bb2:	74 b4                	je     3b68 <external_thread+0x48>
}
    3bb4:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3bb9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3bc2:	75 0d                	jne    3bd1 <external_thread+0xb1>
    3bc4:	48 83 c4 38          	add    $0x38,%rsp
    3bc8:	31 c0                	xor    %eax,%eax
    3bca:	5b                   	pop    %rbx
    3bcb:	5d                   	pop    %rbp
    3bcc:	41 5c                	pop    %r12
    3bce:	41 5d                	pop    %r13
    3bd0:	c3                   	ret
    3bd1:	e8 5a e7 ff ff       	call   2330 <__stack_chk_fail@plt>
    3bd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003be0 <timer_thread>:
void* timer_thread(void *arg) {
    3be0:	f3 0f 1e fa          	endbr64
    3be4:	41 57                	push   %r15
    3be6:	48 8d 35 23 34 00 00 	lea    0x3423(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    3bed:	49 89 ff             	mov    %rdi,%r15
    3bf0:	41 56                	push   %r14
    3bf2:	41 55                	push   %r13
    3bf4:	41 54                	push   %r12
    3bf6:	55                   	push   %rbp
    3bf7:	53                   	push   %rbx
    3bf8:	48 83 ec 58          	sub    $0x58,%rsp
    3bfc:	8b 17                	mov    (%rdi),%edx
    3bfe:	bf 01 00 00 00       	mov    $0x1,%edi
    3c03:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3c0c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3c11:	31 c0                	xor    %eax,%eax
    3c13:	e8 38 e8 ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3c18:	66 0f 6f 05 20 3d 00 00 	movdqa 0x3d20(%rip),%xmm0        # 7940 <_IO_stdin_used+0x940>
    3c20:	ba 88 13 00 00       	mov    $0x1388,%edx
    3c25:	31 c0                	xor    %eax,%eax
    3c27:	48 8d 35 f4 33 00 00 	lea    0x33f4(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    3c2e:	bf 01 00 00 00       	mov    $0x1,%edi
    3c33:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3c38:	e8 13 e8 ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    3c3d:	45 8b 67 34          	mov    0x34(%r15),%r12d
    3c41:	45 85 e4             	test   %r12d,%r12d
    3c44:	0f 84 9b 00 00 00    	je     3ce5 <timer_thread+0x105>
  int n = 0;
    3c4a:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    3c4d:	45 31 e4             	xor    %r12d,%r12d
    3c50:	49 89 e5             	mov    %rsp,%r13
    y++;
    3c53:	31 db                	xor    %ebx,%ebx
    3c55:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    3c5a:	48 89 ef             	mov    %rbp,%rdi
    3c5d:	4c 89 ee             	mov    %r13,%rsi
    n++;
    3c60:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3c64:	e8 e7 e6 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c69:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3c6d:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c72:	85 c0                	test   %eax,%eax
    3c74:	7e 47                	jle    3cbd <timer_thread+0xdd>
    3c76:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3c7a:	49 c1 e4 09          	shl    $0x9,%r12
    3c7e:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3c82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3c88:	4c 8b 11             	mov    (%rcx),%r10
    3c8b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c8d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3c91:	99                   	cltd
    3c92:	41 f7 7a 30          	idivl  0x30(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    3c96:	49 8b 72 28          	mov    0x28(%r10),%rsi
    3c9a:	48 63 d2             	movslq %edx,%rdx
    3c9d:	48 c1 e2 09          	shl    $0x9,%rdx
    3ca1:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3cac:	42 c7 84 26 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3cb8:	49 39 c8             	cmp    %rcx,%r8
    3cbb:	75 cb                	jne    3c88 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    3cbd:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3cc0:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3cc4:	41 8b 57 34          	mov    0x34(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3cc8:	48 8b 00             	mov    (%rax),%rax
    y++;
    3ccb:	39 78 30             	cmp    %edi,0x30(%rax)
    3cce:	0f 4e fb             	cmovle %ebx,%edi
    3cd1:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3cd4:	85 d2                	test   %edx,%edx
    3cd6:	74 0d                	je     3ce5 <timer_thread+0x105>
    3cd8:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3cdf:	0f 85 75 ff ff ff    	jne    3c5a <timer_thread+0x7a>
    3ce5:	48 8d 3d 4c 33 00 00 	lea    0x334c(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    3cec:	e8 ff e5 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3cf1:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3cf5:	85 d2                	test   %edx,%edx
    3cf7:	7e 6b                	jle    3d64 <timer_thread+0x184>
    for (int y = 0 ; y < data->task_count ; y++) {
    3cf9:	49 63 47 30          	movslq 0x30(%r15),%rax
    3cfd:	85 c0                	test   %eax,%eax
    3cff:	7e 63                	jle    3d64 <timer_thread+0x184>
    3d01:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3d05:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3d09:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3d11:	31 ff                	xor    %edi,%edi
    3d13:	48 89 c2             	mov    %rax,%rdx
    3d16:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3d1a:	48 8b 40 28          	mov    0x28(%rax),%rax
    3d1e:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3d22:	f6 c6 02             	test   $0x2,%dh
    3d25:	74 15                	je     3d3c <timer_thread+0x15c>
    3d27:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3d31:	48 05 00 02 00 00    	add    $0x200,%rax
    3d37:	48 39 c6             	cmp    %rax,%rsi
    3d3a:	74 1f                	je     3d5b <timer_thread+0x17b>
      data->threads[x]->tasks[y].sending = 0;
    3d3c:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3d46:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3d4c:	c7 80 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3d56:	48 39 c6             	cmp    %rax,%rsi
    3d59:	75 e1                	jne    3d3c <timer_thread+0x15c>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d5b:	48 83 c7 08          	add    $0x8,%rdi
    3d5f:	48 39 f9             	cmp    %rdi,%rcx
    3d62:	75 b2                	jne    3d16 <timer_thread+0x136>
  asm volatile ("mfence" ::: "memory");
    3d64:	0f ae f0             	mfence
  struct timespec drain = {
    3d67:	66 0f 6f 05 e1 3b 00 00 	movdqa 0x3be1(%rip),%xmm0        # 7950 <_IO_stdin_used+0x950>
    3d6f:	48 8d 2d e7 32 00 00 	lea    0x32e7(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    3d76:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d7b:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3d7f:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3d84:	85 c0                	test   %eax,%eax
    3d86:	7e 4c                	jle    3dd4 <timer_thread+0x1f4>
    3d88:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3d8c:	4d 63 c4             	movslq %r12d,%r8
    3d8f:	49 c1 e0 09          	shl    $0x9,%r8
    3d93:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3d97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3da0:	48 8b 19             	mov    (%rcx),%rbx
    3da3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3da5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3da9:	99                   	cltd
    3daa:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3dad:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3db1:	48 63 d2             	movslq %edx,%rdx
    3db4:	48 c1 e2 09          	shl    $0x9,%rdx
    3db8:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3dc3:	42 c7 84 06 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3dcf:	4c 39 c9             	cmp    %r9,%rcx
    3dd2:	75 cc                	jne    3da0 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    3dd4:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3dd7:	49 8b 47 10          	mov    0x10(%r15),%rax
    y++;
    3ddb:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3dde:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3de1:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3de4:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3de8:	41 8b 7f 20          	mov    0x20(%r15),%edi
    3dec:	85 ff                	test   %edi,%edi
    3dee:	0f 8e bc 00 00 00    	jle    3eb0 <timer_thread+0x2d0>
    3df4:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    3df7:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3dfd:	0f 1f 00             	nopl   (%rax)
    3e00:	4a 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbx
            all_empty = 0;
    3e08:	45 31 f6             	xor    %r14d,%r14d
    3e0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3e10:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3e14:	4c 89 f0             	mov    %r14,%rax
    3e17:	48 c1 e0 09          	shl    $0x9,%rax
    3e1b:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3e1f:	31 d2                	xor    %edx,%edx
    3e21:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3e28:	eb 18                	jmp    3e42 <timer_thread+0x262>
    3e2a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3e30:	4d 85 c0             	test   %r8,%r8
    3e33:	7f 24                	jg     3e59 <timer_thread+0x279>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3e35:	83 c2 01             	add    $0x1,%edx
    3e38:	48 05 00 02 00 00    	add    $0x200,%rax
    3e3e:	39 fa                	cmp    %edi,%edx
    3e40:	74 2d                	je     3e6f <timer_thread+0x28f>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3e42:	48 8b 08             	mov    (%rax),%rcx
    3e45:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    3e4c:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3e50:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3e54:	48 85 c9             	test   %rcx,%rcx
    3e57:	7e d7                	jle    3e30 <timer_thread+0x250>
    3e59:	bf 01 00 00 00       	mov    $0x1,%edi
    3e5e:	48 89 ee             	mov    %rbp,%rsi
    3e61:	31 c0                	xor    %eax,%eax
    3e63:	e8 e8 e5 ff ff       	call   2450 <__printf_chk@plt>
            break;
    3e68:	41 8b 7f 20          	mov    0x20(%r15),%edi
            all_empty = 0;
    3e6c:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3e6f:	49 83 c6 01          	add    $0x1,%r14
    3e73:	44 39 f7             	cmp    %r14d,%edi
    3e76:	7e 08                	jle    3e80 <timer_thread+0x2a0>
    3e78:	49 8b 47 10          	mov    0x10(%r15),%rax
    3e7c:	eb 92                	jmp    3e10 <timer_thread+0x230>
    3e7e:	66 90                	xchg   %ax,%ax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3e80:	49 83 c5 01          	add    $0x1,%r13
    3e84:	44 39 ef             	cmp    %r13d,%edi
    3e87:	7e 0d                	jle    3e96 <timer_thread+0x2b6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3e89:	85 ff                	test   %edi,%edi
    3e8b:	7e 09                	jle    3e96 <timer_thread+0x2b6>
    3e8d:	49 8b 47 10          	mov    0x10(%r15),%rax
    3e91:	e9 6a ff ff ff       	jmp    3e00 <timer_thread+0x220>
    if (all_empty == 1) {
    3e96:	41 83 f9 01          	cmp    $0x1,%r9d
    3e9a:	74 14                	je     3eb0 <timer_thread+0x2d0>
      nanosleep(&drain , &drainrem);
    3e9c:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3ea1:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3ea6:	e8 a5 e4 ff ff       	call   2350 <nanosleep@plt>
    3eab:	e9 cb fe ff ff       	jmp    3d7b <timer_thread+0x19b>
    3eb0:	48 8d 3d 9d 31 00 00 	lea    0x319d(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3eb7:	e8 34 e4 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3ebc:	41 8b 47 34          	mov    0x34(%r15),%eax
    3ec0:	85 c0                	test   %eax,%eax
    3ec2:	0f 84 cf 00 00 00    	je     3f97 <timer_thread+0x3b7>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ec8:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3ecc:	85 c9                	test   %ecx,%ecx
    3ece:	7e 2d                	jle    3efd <timer_thread+0x31d>
    3ed0:	49 8b 47 10          	mov    0x10(%r15),%rax
    3ed4:	31 db                	xor    %ebx,%ebx
    3ed6:	48 8d 2d 91 31 00 00 	lea    0x3191(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3edd:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->running = 0;
    3ee0:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3ee4:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3ee8:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3eef:	0f 84 cf 00 00 00    	je     3fc4 <timer_thread+0x3e4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3ef5:	48 83 c3 01          	add    $0x1,%rbx
    3ef9:	39 d9                	cmp    %ebx,%ecx
    3efb:	7f e3                	jg     3ee0 <timer_thread+0x300>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3efd:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3f01:	85 d2                	test   %edx,%edx
    3f03:	7e 7b                	jle    3f80 <timer_thread+0x3a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3f05:	49 63 47 30          	movslq 0x30(%r15),%rax
    3f09:	85 c0                	test   %eax,%eax
    3f0b:	7e 73                	jle    3f80 <timer_thread+0x3a0>
    3f0d:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3f11:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3f15:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3f1d:	31 c9                	xor    %ecx,%ecx
    3f1f:	48 89 c6             	mov    %rax,%rsi
    3f22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3f28:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3f2c:	48 8b 40 28          	mov    0x28(%rax),%rax
    3f30:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3f34:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3f3a:	74 1c                	je     3f58 <timer_thread+0x378>
    3f3c:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3f46:	48 05 00 02 00 00    	add    $0x200,%rax
    3f4c:	48 39 d0             	cmp    %rdx,%rax
    3f4f:	74 26                	je     3f77 <timer_thread+0x397>
    3f51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3f58:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3f62:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3f68:	c7 80 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3f72:	48 39 d0             	cmp    %rdx,%rax
    3f75:	75 e1                	jne    3f58 <timer_thread+0x378>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3f77:	48 83 c1 08          	add    $0x8,%rcx
    3f7b:	48 39 f9             	cmp    %rdi,%rcx
    3f7e:	75 a8                	jne    3f28 <timer_thread+0x348>
    asm volatile ("mfence" ::: "memory");
    3f80:	0f ae f0             	mfence
    3f83:	48 8d 3d f6 30 00 00 	lea    0x30f6(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3f8a:	e8 61 e3 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3f8f:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
    3f97:	48 8d 3d e9 30 00 00 	lea    0x30e9(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3f9e:	e8 4d e3 ff ff       	call   22f0 <puts@plt>
}
    3fa3:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3fa8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3fb1:	75 47                	jne    3ffa <timer_thread+0x41a>
    3fb3:	48 83 c4 58          	add    $0x58,%rsp
    3fb7:	31 c0                	xor    %eax,%eax
    3fb9:	5b                   	pop    %rbx
    3fba:	5d                   	pop    %rbp
    3fbb:	41 5c                	pop    %r12
    3fbd:	41 5d                	pop    %r13
    3fbf:	41 5e                	pop    %r14
    3fc1:	41 5f                	pop    %r15
    3fc3:	c3                   	ret
    3fc4:	48 89 ef             	mov    %rbp,%rdi
    3fc7:	e8 24 e3 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3fcc:	49 8b 47 10          	mov    0x10(%r15),%rax
    3fd0:	be 01 00 00 00       	mov    $0x1,%esi
    3fd5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3fd9:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3fdd:	8b 78 50             	mov    0x50(%rax),%edi
    3fe0:	e8 1b e4 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3fe5:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3fe9:	39 d9                	cmp    %ebx,%ecx
    3feb:	0f 8e 0c ff ff ff    	jle    3efd <timer_thread+0x31d>
    3ff1:	49 8b 47 10          	mov    0x10(%r15),%rax
    3ff5:	e9 e6 fe ff ff       	jmp    3ee0 <timer_thread+0x300>
}
    3ffa:	e8 31 e3 ff ff       	call   2330 <__stack_chk_fail@plt>
    3fff:	90                   	nop

0000000000004000 <strtolower>:
void strtolower(char *str) {
    4000:	f3 0f 1e fa          	endbr64
    4004:	55                   	push   %rbp
    4005:	53                   	push   %rbx
    4006:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    400a:	48 0f be 1f          	movsbq (%rdi),%rbx
    400e:	84 db                	test   %bl,%bl
    4010:	74 24                	je     4036 <strtolower+0x36>
    4012:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4015:	e8 f6 e4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    401a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4020:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4023:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4027:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    402a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    402d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4032:	84 db                	test   %bl,%bl
    4034:	75 ea                	jne    4020 <strtolower+0x20>
}
    4036:	48 83 c4 08          	add    $0x8,%rsp
    403a:	5b                   	pop    %rbx
    403b:	5d                   	pop    %rbp
    403c:	c3                   	ret
    403d:	0f 1f 00             	nopl   (%rax)

0000000000004040 <zh_malloc>:
void *zh_malloc(size_t size) {
    4040:	f3 0f 1e fa          	endbr64
    4044:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4048:	e8 c3 e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    404d:	48 85 c0             	test   %rax,%rax
    4050:	74 05                	je     4057 <zh_malloc+0x17>
}
    4052:	48 83 c4 08          	add    $0x8,%rsp
    4056:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4057:	48 8b 0d c2 5f 00 00 	mov    0x5fc2(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    405e:	ba 28 00 00 00       	mov    $0x28,%edx
    4063:	be 01 00 00 00       	mov    $0x1,%esi
    4068:	48 8d 3d 99 33 00 00 	lea    0x3399(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    406f:	e8 4c e4 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4074:	bf 01 00 00 00       	mov    $0x1,%edi
    4079:	e8 22 e4 ff ff       	call   24a0 <exit@plt>
    407e:	66 90                	xchg   %ax,%ax

0000000000004080 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4080:	f3 0f 1e fa          	endbr64
    4084:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4085:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    408a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    408d:	e8 ce e2 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    4092:	48 85 c0             	test   %rax,%rax
    4095:	74 11                	je     40a8 <get_filename_ext+0x28>
    4097:	48 39 c3             	cmp    %rax,%rbx
    409a:	74 0c                	je     40a8 <get_filename_ext+0x28>
    return dot + 1;
    409c:	48 83 c0 01          	add    $0x1,%rax
}
    40a0:	5b                   	pop    %rbx
    40a1:	c3                   	ret
    40a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    40a8:	48 8d 05 20 30 00 00 	lea    0x3020(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    40af:	5b                   	pop    %rbx
    40b0:	c3                   	ret
    40b1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    40bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000040c0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    40c0:	f3 0f 1e fa          	endbr64
    40c4:	41 55                	push   %r13
    40c6:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40c9:	48 89 fe             	mov    %rdi,%rsi
    40cc:	41 54                	push   %r12
    40ce:	55                   	push   %rbp
    40cf:	48 89 d5             	mov    %rdx,%rbp
    40d2:	ba 00 04 00 00       	mov    $0x400,%edx
    40d7:	53                   	push   %rbx
    40d8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    40df:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    40e8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    40f0:	31 c0                	xor    %eax,%eax
    40f2:	49 89 e4             	mov    %rsp,%r12
    40f5:	4c 89 e7             	mov    %r12,%rdi
    40f8:	e8 33 e3 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    40fd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4102:	84 db                	test   %bl,%bl
    4104:	74 24                	je     412a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4106:	e8 05 e4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    410b:	48 8b 08             	mov    (%rax),%rcx
    410e:	4c 89 e0             	mov    %r12,%rax
    4111:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4118:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    411b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    411f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4122:	48 0f be 18          	movsbq (%rax),%rbx
    4126:	84 db                	test   %bl,%bl
    4128:	75 ee                	jne    4118 <send_headers+0x58>
    void *buf = malloc(size);
    412a:	bf 11 00 00 00       	mov    $0x11,%edi
    412f:	e8 dc e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4134:	48 85 c0             	test   %rax,%rax
    4137:	0f 84 7e 04 00 00    	je     45bb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    413d:	66 0f 6f 05 1b 38 00 00 	movdqa 0x381b(%rip),%xmm0        # 7960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    4145:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4149:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    414e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4156:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    415a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    415d:	e8 ae e2 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4162:	48 85 c0             	test   %rax,%rax
    4165:	0f 84 50 04 00 00    	je     45bb <send_headers+0x4fb>
    416b:	66 0f 6f 05 fd 37 00 00 	movdqa 0x37fd(%rip),%xmm0        # 7970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    4173:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4177:	4c 89 e7             	mov    %r12,%rdi
    417a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4184:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    418c:	0f 11 00             	movups %xmm0,(%rax)
    418f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4193:	be 2e 00 00 00       	mov    $0x2e,%esi
    4198:	e8 c3 e1 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    419d:	48 85 c0             	test   %rax,%rax
    41a0:	0f 84 ea 02 00 00    	je     4490 <send_headers+0x3d0>
    41a6:	4c 39 e0             	cmp    %r12,%rax
    41a9:	0f 84 e1 02 00 00    	je     4490 <send_headers+0x3d0>
    return dot + 1;
    41af:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    41b3:	48 8d 3d e3 2e 00 00 	lea    0x2ee3(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    41ba:	48 89 de             	mov    %rbx,%rsi
    41bd:	e8 ee e1 ff ff       	call   23b0 <strcmp@plt>
    41c2:	85 c0                	test   %eax,%eax
    41c4:	75 20                	jne    41e6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    41c6:	66 0f 6f 05 b2 37 00 00 	movdqa 0x37b2(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    41ce:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41d6:	66 0f 6f 05 b2 37 00 00 	movdqa 0x37b2(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    41de:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    41e6:	48 89 de             	mov    %rbx,%rsi
    41e9:	48 8d 3d b1 2e 00 00 	lea    0x2eb1(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    41f0:	e8 bb e1 ff ff       	call   23b0 <strcmp@plt>
    41f5:	85 c0                	test   %eax,%eax
    41f7:	75 20                	jne    4219 <send_headers+0x159>
    41f9:	66 0f 6f 05 7f 37 00 00 	movdqa 0x377f(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4201:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4209:	66 0f 6f 05 7f 37 00 00 	movdqa 0x377f(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    4211:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4219:	48 89 de             	mov    %rbx,%rsi
    421c:	48 8d 3d 83 2e 00 00 	lea    0x2e83(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    4223:	e8 88 e1 ff ff       	call   23b0 <strcmp@plt>
    4228:	85 c0                	test   %eax,%eax
    422a:	0f 84 10 02 00 00    	je     4440 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4230:	48 89 de             	mov    %rbx,%rsi
    4233:	48 8d 3d 70 2e 00 00 	lea    0x2e70(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    423a:	e8 71 e1 ff ff       	call   23b0 <strcmp@plt>
    423f:	85 c0                	test   %eax,%eax
    4241:	0f 84 a9 02 00 00    	je     44f0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4247:	48 89 de             	mov    %rbx,%rsi
    424a:	48 8d 3d 5d 2e 00 00 	lea    0x2e5d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    4251:	e8 5a e1 ff ff       	call   23b0 <strcmp@plt>
    4256:	85 c0                	test   %eax,%eax
    4258:	0f 84 6a 02 00 00    	je     44c8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    425e:	48 89 de             	mov    %rbx,%rsi
    4261:	48 8d 3d 89 2e 00 00 	lea    0x2e89(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    4268:	e8 43 e1 ff ff       	call   23b0 <strcmp@plt>
    426d:	85 c0                	test   %eax,%eax
    426f:	0f 84 2b 02 00 00    	je     44a0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4275:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4278:	0f 84 52 01 00 00    	je     43d0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    427e:	48 89 de             	mov    %rbx,%rsi
    4281:	48 8d 3d 2a 2e 00 00 	lea    0x2e2a(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    4288:	e8 23 e1 ff ff       	call   23b0 <strcmp@plt>
    428d:	85 c0                	test   %eax,%eax
    428f:	0f 84 ab 02 00 00    	je     4540 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4295:	48 89 de             	mov    %rbx,%rsi
    4298:	48 8d 3d 17 2e 00 00 	lea    0x2e17(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    429f:	e8 0c e1 ff ff       	call   23b0 <strcmp@plt>
    42a4:	85 c0                	test   %eax,%eax
    42a6:	0f 84 6c 02 00 00    	je     4518 <send_headers+0x458>
    slen = strlen(send_buffer);
    42ac:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    42b4:	4c 89 e7             	mov    %r12,%rdi
    42b7:	e8 64 e0 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    42bc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    42bf:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    42c2:	e8 49 e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    42c7:	48 85 c0             	test   %rax,%rax
    42ca:	0f 84 eb 02 00 00    	je     45bb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    42d0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    42d4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    42d8:	83 fb 08             	cmp    $0x8,%ebx
    42db:	0f 83 3f 01 00 00    	jae    4420 <send_headers+0x360>
    42e1:	f6 c3 04             	test   $0x4,%bl
    42e4:	0f 85 7b 02 00 00    	jne    4565 <send_headers+0x4a5>
    42ea:	85 db                	test   %ebx,%ebx
    42ec:	74 13                	je     4301 <send_headers+0x241>
    42ee:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    42f6:	88 10                	mov    %dl,(%rax)
    42f8:	f6 c3 02             	test   $0x2,%bl
    42fb:	0f 85 96 02 00 00    	jne    4597 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4301:	4d 89 e8             	mov    %r13,%r8
    4304:	48 8d 0d af 2d 00 00 	lea    0x2daf(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    430b:	4c 89 e7             	mov    %r12,%rdi
    430e:	31 c0                	xor    %eax,%eax
    4310:	ba 00 04 00 00       	mov    $0x400,%edx
    4315:	be 01 00 00 00       	mov    $0x1,%esi
    431a:	e8 01 e2 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    431f:	4c 89 e7             	mov    %r12,%rdi
    4322:	e8 f9 df ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4327:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    432a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    432d:	e8 de e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4332:	48 85 c0             	test   %rax,%rax
    4335:	0f 84 80 02 00 00    	je     45bb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    433b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    433f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4343:	83 fb 08             	cmp    $0x8,%ebx
    4346:	0f 83 1c 01 00 00    	jae    4468 <send_headers+0x3a8>
    434c:	f6 c3 04             	test   $0x4,%bl
    434f:	0f 85 29 02 00 00    	jne    457e <send_headers+0x4be>
    4355:	85 db                	test   %ebx,%ebx
    4357:	74 13                	je     436c <send_headers+0x2ac>
    4359:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4361:	88 10                	mov    %dl,(%rax)
    4363:	f6 c3 02             	test   $0x2,%bl
    4366:	0f 85 3d 02 00 00    	jne    45a9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    436c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4371:	bf 02 00 00 00       	mov    $0x2,%edi
    4376:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    437e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4386:	e8 85 e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    438b:	48 85 c0             	test   %rax,%rax
    438e:	0f 84 27 02 00 00    	je     45bb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4394:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    439c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    43a0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    43a8:	66 89 10             	mov    %dx,(%rax)
}
    43ab:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    43b3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    43bc:	0f 85 20 02 00 00    	jne    45e2 <send_headers+0x522>
    43c2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    43c9:	5b                   	pop    %rbx
    43ca:	5d                   	pop    %rbp
    43cb:	41 5c                	pop    %r12
    43cd:	41 5d                	pop    %r13
    43cf:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    43d0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    43d4:	0f 85 a4 fe ff ff    	jne    427e <send_headers+0x1be>
    43da:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    43de:	0f 85 9a fe ff ff    	jne    427e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    43e4:	66 0f 6f 05 f4 35 00 00 	movdqa 0x35f4(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    43ec:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    43f6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    43fe:	66 0f 6f 05 ea 35 00 00 	movdqa 0x35ea(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    4406:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    440e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4416:	e9 63 fe ff ff       	jmp    427e <send_headers+0x1be>
    441b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4420:	89 da                	mov    %ebx,%edx
    4422:	48 89 c7             	mov    %rax,%rdi
    4425:	4c 89 e6             	mov    %r12,%rsi
    4428:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    442d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4432:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4435:	c1 e9 03             	shr    $0x3,%ecx
    4438:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    443b:	e9 c1 fe ff ff       	jmp    4301 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4440:	66 0f 6f 05 38 35 00 00 	movdqa 0x3538(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    4448:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4450:	66 0f 6f 05 48 35 00 00 	movdqa 0x3548(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    4458:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4460:	e9 cb fd ff ff       	jmp    4230 <send_headers+0x170>
    4465:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4468:	89 da                	mov    %ebx,%edx
    446a:	48 89 c7             	mov    %rax,%rdi
    446d:	4c 89 e6             	mov    %r12,%rsi
    4470:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4475:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    447a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    447d:	c1 e9 03             	shr    $0x3,%ecx
    4480:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4483:	e9 e4 fe ff ff       	jmp    436c <send_headers+0x2ac>
    4488:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4490:	48 8d 1d 38 2c 00 00 	lea    0x2c38(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    4497:	e9 94 fd ff ff       	jmp    4230 <send_headers+0x170>
    449c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    44a0:	66 0f 6f 05 18 35 00 00 	movdqa 0x3518(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    44a8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44b0:	66 0f 6f 05 18 35 00 00 	movdqa 0x3518(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    44b8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44c0:	e9 b0 fd ff ff       	jmp    4275 <send_headers+0x1b5>
    44c5:	0f 1f 00             	nopl   (%rax)
    44c8:	66 0f 6f 05 f0 34 00 00 	movdqa 0x34f0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    44d0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44d8:	66 0f 6f 05 f0 34 00 00 	movdqa 0x34f0(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    44e0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44e8:	e9 71 fd ff ff       	jmp    425e <send_headers+0x19e>
    44ed:	0f 1f 00             	nopl   (%rax)
    44f0:	66 0f 6f 05 88 34 00 00 	movdqa 0x3488(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    44f8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4500:	66 0f 6f 05 a8 34 00 00 	movdqa 0x34a8(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    4508:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4510:	e9 32 fd ff ff       	jmp    4247 <send_headers+0x187>
    4515:	0f 1f 00             	nopl   (%rax)
    4518:	66 0f 6f 05 a0 34 00 00 	movdqa 0x34a0(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4520:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4528:	66 0f 6f 05 e0 34 00 00 	movdqa 0x34e0(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4530:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4538:	e9 6f fd ff ff       	jmp    42ac <send_headers+0x1ec>
    453d:	0f 1f 00             	nopl   (%rax)
    4540:	66 0f 6f 05 78 34 00 00 	movdqa 0x3478(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4548:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4550:	66 0f 6f 05 a8 34 00 00 	movdqa 0x34a8(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4558:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4560:	e9 30 fd ff ff       	jmp    4295 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4565:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    456c:	89 db                	mov    %ebx,%ebx
    456e:	89 10                	mov    %edx,(%rax)
    4570:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4575:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4579:	e9 83 fd ff ff       	jmp    4301 <send_headers+0x241>
    457e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4585:	89 db                	mov    %ebx,%ebx
    4587:	89 10                	mov    %edx,(%rax)
    4589:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    458e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4592:	e9 d5 fd ff ff       	jmp    436c <send_headers+0x2ac>
    4597:	89 db                	mov    %ebx,%ebx
    4599:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    459f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    45a4:	e9 58 fd ff ff       	jmp    4301 <send_headers+0x241>
    45a9:	89 db                	mov    %ebx,%ebx
    45ab:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    45b1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    45b6:	e9 b1 fd ff ff       	jmp    436c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    45bb:	48 8b 0d 5e 5a 00 00 	mov    0x5a5e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    45c2:	ba 28 00 00 00       	mov    $0x28,%edx
    45c7:	be 01 00 00 00       	mov    $0x1,%esi
    45cc:	48 8d 3d 35 2e 00 00 	lea    0x2e35(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    45d3:	e8 e8 de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    45d8:	bf 01 00 00 00       	mov    $0x1,%edi
    45dd:	e8 be de ff ff       	call   24a0 <exit@plt>
}
    45e2:	e8 49 dd ff ff       	call   2330 <__stack_chk_fail@plt>
    45e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000045f0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    45f0:	f3 0f 1e fa          	endbr64
    45f4:	41 55                	push   %r13
    45f6:	49 89 d5             	mov    %rdx,%r13
    45f9:	41 54                	push   %r12
    45fb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    45fe:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4601:	55                   	push   %rbp
    4602:	53                   	push   %rbx
    4603:	48 89 f3             	mov    %rsi,%rbx
    4606:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    460a:	e8 01 de ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    460f:	48 85 c0             	test   %rax,%rax
    4612:	74 6b                	je     467f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4614:	4c 89 e7             	mov    %r12,%rdi
    4617:	48 89 c5             	mov    %rax,%rbp
    461a:	31 f6                	xor    %esi,%esi
    461c:	31 c0                	xor    %eax,%eax
    461e:	e8 5d de ff ff       	call   2480 <open@plt>
    4623:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4626:	85 c0                	test   %eax,%eax
    4628:	0f 88 28 df ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    462e:	48 89 da             	mov    %rbx,%rdx
    4631:	48 89 ee             	mov    %rbp,%rsi
    4634:	89 c7                	mov    %eax,%edi
    4636:	e8 55 dd ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    463b:	48 98                	cltq
    463d:	48 39 d8             	cmp    %rbx,%rax
    4640:	7c 1e                	jl     4660 <copy_file_contents+0x70>
    close(fd);
    4642:	44 89 e7             	mov    %r12d,%edi
    4645:	e8 26 dd ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    464a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    464e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4652:	48 83 c4 08          	add    $0x8,%rsp
    4656:	5b                   	pop    %rbx
    4657:	5d                   	pop    %rbp
    4658:	41 5c                	pop    %r12
    465a:	41 5d                	pop    %r13
    465c:	c3                   	ret
    465d:	0f 1f 00             	nopl   (%rax)
    4660:	48 8b 0d b9 59 00 00 	mov    0x59b9(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4667:	ba 1a 00 00 00       	mov    $0x1a,%edx
    466c:	be 01 00 00 00       	mov    $0x1,%esi
    4671:	48 8d 3d 58 2a 00 00 	lea    0x2a58(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    4678:	e8 43 de ff ff       	call   24c0 <fwrite@plt>
    467d:	eb c3                	jmp    4642 <copy_file_contents+0x52>
    467f:	48 8b 0d 9a 59 00 00 	mov    0x599a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4686:	ba 28 00 00 00       	mov    $0x28,%edx
    468b:	be 01 00 00 00       	mov    $0x1,%esi
    4690:	48 8d 3d 71 2d 00 00 	lea    0x2d71(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4697:	e8 24 de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    469c:	bf 01 00 00 00       	mov    $0x1,%edi
    46a1:	e8 fa dd ff ff       	call   24a0 <exit@plt>
    46a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000046b0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    46b0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    46b4:	8b 46 44             	mov    0x44(%rsi),%eax
    46b7:	48 89 fa             	mov    %rdi,%rdx
    46ba:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    46bd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    46c3:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    46c6:	48 8b 07             	mov    (%rdi),%rax
    46c9:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    46cc:	f6 c1 02             	test   $0x2,%cl
    46cf:	74 00                	je     46d1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    46d1:	89 f0                	mov    %esi,%eax
    46d3:	44 29 c0             	sub    %r8d,%eax
    46d6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    46d9:	0f 82 83 de ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    46df:	c1 e9 0a             	shr    $0xa,%ecx
    46e2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    46e6:	8b 47 44             	mov    0x44(%rdi),%eax
    46e9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    46ec:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    46ef:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    46f2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    46f5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    46f9:	d3 e0                	shl    %cl,%eax
    46fb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    46fe:	48 c1 e0 06          	shl    $0x6,%rax
    4702:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4706:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    470c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    470f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4713:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4719:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4721:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4725:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4728:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    472f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4737:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    473b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    473f:	e8 fc db ff ff       	call   2340 <io_uring_submit@plt>
}
    4744:	31 c0                	xor    %eax,%eax
    4746:	48 83 c4 08          	add    $0x8,%rsp
    474a:	c3                   	ret
    474b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004750 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4750:	f3 0f 1e fa          	endbr64
    4754:	41 55                	push   %r13
    4756:	41 89 fd             	mov    %edi,%r13d
    4759:	41 54                	push   %r12
    475b:	55                   	push   %rbp
    475c:	53                   	push   %rbx
    475d:	48 89 f3             	mov    %rsi,%rbx
    4760:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4764:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4767:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    476d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4770:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4773:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4775:	f6 c1 02             	test   $0x2,%cl
    4778:	74 00                	je     477a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    477a:	89 c2                	mov    %eax,%edx
    477c:	29 f2                	sub    %esi,%edx
    477e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4781:	0f 82 eb dd ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4787:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    478a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    478d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4790:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4795:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4798:	23 6b 58             	and    0x58(%rbx),%ebp
    479b:	d3 e5                	shl    %cl,%ebp
    479d:	48 c1 e5 06          	shl    $0x6,%rbp
    47a1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    47a5:	e8 66 dc ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    47aa:	be 01 00 00 00       	mov    $0x1,%esi
    47af:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    47b4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    47b7:	e8 e4 db ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    47bc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    47c1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    47c5:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    47c8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    47cd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    47d2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    47db:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    47e3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    47e7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    47eb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    47f2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    47fa:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    47fe:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4806:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    480e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4812:	e8 29 db ff ff       	call   2340 <io_uring_submit@plt>
}
    4817:	48 83 c4 08          	add    $0x8,%rsp
    481b:	31 c0                	xor    %eax,%eax
    481d:	5b                   	pop    %rbx
    481e:	5d                   	pop    %rbp
    481f:	41 5c                	pop    %r12
    4821:	41 5d                	pop    %r13
    4823:	c3                   	ret
    4824:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    482f:	90                   	nop

0000000000004830 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4830:	f3 0f 1e fa          	endbr64
    4834:	41 56                	push   %r14
    4836:	41 89 f6             	mov    %esi,%r14d
    4839:	41 55                	push   %r13
    483b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    483e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4843:	41 54                	push   %r12
    4845:	55                   	push   %rbp
    4846:	48 89 d5             	mov    %rdx,%rbp
    4849:	53                   	push   %rbx
    void *buf = malloc(size);
    484a:	e8 c1 db ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    484f:	48 85 c0             	test   %rax,%rax
    4852:	0f 84 dd 00 00 00    	je     4935 <_send_static_string_content+0x105>
    4858:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    485b:	4c 89 ef             	mov    %r13,%rdi
    485e:	e8 bd da ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    4863:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    486a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    486e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4871:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4874:	e8 97 db ff ff       	call   2410 <malloc@plt>
    4879:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    487c:	48 85 c0             	test   %rax,%rax
    487f:	0f 84 b0 00 00 00    	je     4935 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4885:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4889:	4c 89 e2             	mov    %r12,%rdx
    488c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    488f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4893:	e8 48 db ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4898:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    489b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    48a1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    48a4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    48a8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    48aa:	f6 c1 02             	test   $0x2,%cl
    48ad:	0f 85 7d 00 00 00    	jne    4930 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    48b3:	89 d0                	mov    %edx,%eax
    48b5:	29 f0                	sub    %esi,%eax
    48b7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    48ba:	0f 82 bc dc ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    48c0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    48c3:	8b 45 44             	mov    0x44(%rbp),%eax
    48c6:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    48c9:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    48cc:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    48cf:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    48d2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    48d8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    48dc:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    48de:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    48e1:	48 89 ef             	mov    %rbp,%rdi
    48e4:	48 c1 e0 06          	shl    $0x6,%rax
    48e8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    48ec:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    48ef:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    48f3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    48f9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4901:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4905:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4908:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    490f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4917:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    491b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    491f:	5b                   	pop    %rbx
    4920:	5d                   	pop    %rbp
    4921:	41 5c                	pop    %r12
    4923:	41 5d                	pop    %r13
    4925:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4927:	e9 14 da ff ff       	jmp    2340 <io_uring_submit@plt>
    492c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4930:	e9 7e ff ff ff       	jmp    48b3 <_send_static_string_content+0x83>
    4935:	48 8b 0d e4 56 00 00 	mov    0x56e4(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    493c:	ba 28 00 00 00       	mov    $0x28,%edx
    4941:	be 01 00 00 00       	mov    $0x1,%esi
    4946:	48 8d 3d bb 2a 00 00 	lea    0x2abb(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    494d:	e8 6e db ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4952:	bf 01 00 00 00       	mov    $0x1,%edi
    4957:	e8 44 db ff ff       	call   24a0 <exit@plt>
    495c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004960 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4960:	f3 0f 1e fa          	endbr64
    4964:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4967:	89 fe                	mov    %edi,%esi
    4969:	48 8b 3d a8 56 00 00 	mov    0x56a8(%rip),%rdi        # a018 <unimplemented_content>
    4970:	e9 bb fe ff ff       	jmp    4830 <_send_static_string_content>
    4975:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004980 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4980:	f3 0f 1e fa          	endbr64
    4984:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4987:	89 fe                	mov    %edi,%esi
    4989:	48 8b 3d 80 56 00 00 	mov    0x5680(%rip),%rdi        # a010 <http_404_content>
    4990:	e9 9b fe ff ff       	jmp    4830 <_send_static_string_content>
    4995:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000049a0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    49a0:	f3 0f 1e fa          	endbr64
    49a4:	41 56                	push   %r14
    49a6:	41 55                	push   %r13
    49a8:	49 89 d5             	mov    %rdx,%r13
    49ab:	41 54                	push   %r12
    49ad:	41 89 f4             	mov    %esi,%r12d
    49b0:	55                   	push   %rbp
    49b1:	48 89 fd             	mov    %rdi,%rbp
    49b4:	53                   	push   %rbx
    49b5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    49bc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    49c5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    49cd:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    49cf:	e8 4c d9 ff ff       	call   2320 <strlen@plt>
    49d4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    49d9:	48 89 c3             	mov    %rax,%rbx
    49dc:	0f 84 b6 00 00 00    	je     4a98 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    49e2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    49e7:	48 89 ee             	mov    %rbp,%rsi
    49ea:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    49ee:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    49f3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    49fb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a03:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4a0e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a16:	e8 a5 d9 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4a1b:	48 89 e6             	mov    %rsp,%rsi
    4a1e:	4c 89 f7             	mov    %r14,%rdi
    4a21:	e8 aa d9 ff ff       	call   23d0 <stat@plt>
    4a26:	83 f8 ff             	cmp    $0xffffffff,%eax
    4a29:	0f 84 d3 00 00 00    	je     4b02 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    4a2f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4a33:	25 00 f0 00 00       	and    $0xf000,%eax
    4a38:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4a3d:	0f 84 f5 00 00 00    	je     4b38 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4a43:	48 8b 3d c6 55 00 00 	mov    0x55c6(%rip),%rdi        # a010 <http_404_content>
    4a4a:	4c 89 ea             	mov    %r13,%rdx
    4a4d:	44 89 e6             	mov    %r12d,%esi
    4a50:	e8 db fd ff ff       	call   4830 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4a55:	4c 89 f2             	mov    %r14,%rdx
    4a58:	bf 01 00 00 00       	mov    $0x1,%edi
    4a5d:	31 c0                	xor    %eax,%eax
    4a5f:	48 8d 35 ba 26 00 00 	lea    0x26ba(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    4a66:	e8 e5 d9 ff ff       	call   2450 <__printf_chk@plt>
}
    4a6b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4a73:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4a7c:	0f 85 20 01 00 00    	jne    4ba2 <handle_get_method+0x202>
    4a82:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4a89:	5b                   	pop    %rbx
    4a8a:	5d                   	pop    %rbp
    4a8b:	41 5c                	pop    %r12
    4a8d:	41 5d                	pop    %r13
    4a8f:	41 5e                	pop    %r14
    4a91:	c3                   	ret
    4a92:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a98:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4a9d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4aa5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4aaa:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4aad:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4ab5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ab8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4ac0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4acb:	e8 f0 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    4ad0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4ad5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4ada:	48 8d 35 0a 26 00 00 	lea    0x260a(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4ae1:	48 29 d9             	sub    %rbx,%rcx
    4ae4:	ba 0b 00 00 00       	mov    $0xb,%edx
    4ae9:	e8 d2 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    4aee:	48 89 e6             	mov    %rsp,%rsi
    4af1:	4c 89 f7             	mov    %r14,%rdi
    4af4:	e8 d7 d8 ff ff       	call   23d0 <stat@plt>
    4af9:	83 f8 ff             	cmp    $0xffffffff,%eax
    4afc:	0f 85 2d ff ff ff    	jne    4a2f <handle_get_method+0x8f>
    4b02:	4c 89 f2             	mov    %r14,%rdx
    4b05:	48 89 e9             	mov    %rbp,%rcx
    4b08:	48 8d 35 e7 25 00 00 	lea    0x25e7(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    4b0f:	31 c0                	xor    %eax,%eax
    4b11:	bf 01 00 00 00       	mov    $0x1,%edi
    4b16:	e8 35 d9 ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    4b1b:	48 8b 3d ee 54 00 00 	mov    0x54ee(%rip),%rdi        # a010 <http_404_content>
    4b22:	4c 89 ea             	mov    %r13,%rdx
    4b25:	44 89 e6             	mov    %r12d,%esi
    4b28:	e8 03 fd ff ff       	call   4830 <_send_static_string_content>
}
    4b2d:	e9 39 ff ff ff       	jmp    4a6b <handle_get_method+0xcb>
    4b32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4b38:	bf 70 00 00 00       	mov    $0x70,%edi
    4b3d:	e8 ce d8 ff ff       	call   2410 <malloc@plt>
    4b42:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4b45:	48 85 c0             	test   %rax,%rax
    4b48:	74 5d                	je     4ba7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    4b4a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4b4e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4b53:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4b57:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    4b5a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4b61:	e8 5a f5 ff ff       	call   40c0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4b66:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4b6b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4b6f:	4c 89 f7             	mov    %r14,%rdi
    4b72:	e8 79 fa ff ff       	call   45f0 <copy_file_contents>
    4b77:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4b7c:	4c 89 f2             	mov    %r14,%rdx
    4b7f:	31 c0                	xor    %eax,%eax
    4b81:	48 8d 35 86 25 00 00 	lea    0x2586(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    4b88:	bf 01 00 00 00       	mov    $0x1,%edi
    4b8d:	e8 be d8 ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    4b92:	4c 89 ee             	mov    %r13,%rsi
    4b95:	48 89 df             	mov    %rbx,%rdi
    4b98:	e8 13 fb ff ff       	call   46b0 <add_write_request>
    4b9d:	e9 c9 fe ff ff       	jmp    4a6b <handle_get_method+0xcb>
}
    4ba2:	e8 89 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4ba7:	48 8b 0d 72 54 00 00 	mov    0x5472(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4bae:	ba 28 00 00 00       	mov    $0x28,%edx
    4bb3:	be 01 00 00 00       	mov    $0x1,%esi
    4bb8:	48 8d 3d 49 28 00 00 	lea    0x2849(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4bbf:	e8 fc d8 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4bc4:	bf 01 00 00 00       	mov    $0x1,%edi
    4bc9:	e8 d2 d8 ff ff       	call   24a0 <exit@plt>
    4bce:	66 90                	xchg   %ax,%ax

0000000000004bd0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4bd0:	f3 0f 1e fa          	endbr64
    4bd4:	41 57                	push   %r15
    4bd6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4bd8:	4c 8d 35 a6 24 00 00 	lea    0x24a6(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4bdf:	41 55                	push   %r13
    4be1:	49 89 d5             	mov    %rdx,%r13
    4be4:	41 54                	push   %r12
    4be6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4be9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4bec:	55                   	push   %rbp
    4bed:	53                   	push   %rbx
    4bee:	48 83 ec 18          	sub    $0x18,%rsp
    4bf2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4bfb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4c00:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4c02:	49 89 e7             	mov    %rsp,%r15
    4c05:	4c 89 fa             	mov    %r15,%rdx
    4c08:	e8 73 d7 ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    4c0d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4c11:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4c14:	84 db                	test   %bl,%bl
    4c16:	74 1d                	je     4c35 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4c18:	e8 f3 d8 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4c1d:	48 89 ea             	mov    %rbp,%rdx
    4c20:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4c23:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4c27:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4c2a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    4c2d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4c31:	84 db                	test   %bl,%bl
    4c33:	75 eb                	jne    4c20 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4c35:	4c 89 fa             	mov    %r15,%rdx
    4c38:	4c 89 f6             	mov    %r14,%rsi
    4c3b:	31 ff                	xor    %edi,%edi
    4c3d:	e8 3e d7 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4c42:	48 8d 35 ea 24 00 00 	lea    0x24ea(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4c49:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    4c4c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    4c4f:	e8 5c d7 ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4c54:	4c 89 ea             	mov    %r13,%rdx
    4c57:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    4c5a:	85 c0                	test   %eax,%eax
    4c5c:	75 2a                	jne    4c88 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    4c5e:	48 89 df             	mov    %rbx,%rdi
    4c61:	e8 3a fd ff ff       	call   49a0 <handle_get_method>
}
    4c66:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4c6b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4c74:	75 20                	jne    4c96 <handle_http_method+0xc6>
    4c76:	48 83 c4 18          	add    $0x18,%rsp
    4c7a:	5b                   	pop    %rbx
    4c7b:	5d                   	pop    %rbp
    4c7c:	41 5c                	pop    %r12
    4c7e:	41 5d                	pop    %r13
    4c80:	41 5e                	pop    %r14
    4c82:	41 5f                	pop    %r15
    4c84:	c3                   	ret
    4c85:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4c88:	48 8b 3d 89 53 00 00 	mov    0x5389(%rip),%rdi        # a018 <unimplemented_content>
    4c8f:	e8 9c fb ff ff       	call   4830 <_send_static_string_content>
}
    4c94:	eb d0                	jmp    4c66 <handle_http_method+0x96>
    4c96:	e8 95 d6 ff ff       	call   2330 <__stack_chk_fail@plt>
    4c9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004ca0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4ca0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4ca4:	85 d2                	test   %edx,%edx
    4ca6:	7e 38                	jle    4ce0 <get_line+0x40>
    4ca8:	48 63 d2             	movslq %edx,%rdx
    4cab:	48 83 c7 01          	add    $0x1,%rdi
    4caf:	48 01 f2             	add    %rsi,%rdx
    4cb2:	eb 11                	jmp    4cc5 <get_line+0x25>
    4cb4:	0f 1f 40 00          	nopl   0x0(%rax)
    4cb8:	48 83 c6 01          	add    $0x1,%rsi
    4cbc:	48 83 c7 01          	add    $0x1,%rdi
    4cc0:	48 39 d6             	cmp    %rdx,%rsi
    4cc3:	74 1b                	je     4ce0 <get_line+0x40>
        dest[i] = src[i];
    4cc5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4cc9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4ccb:	3c 0d                	cmp    $0xd,%al
    4ccd:	75 e9                	jne    4cb8 <get_line+0x18>
    4ccf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4cd2:	75 e4                	jne    4cb8 <get_line+0x18>
            dest[i] = '\0';
    4cd4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4cd7:	31 c0                	xor    %eax,%eax
    4cd9:	c3                   	ret
    4cda:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4ce0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4ce5:	c3                   	ret
    4ce6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004cf0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4cf0:	f3 0f 1e fa          	endbr64
    4cf4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4cfb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4cff:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4d08:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4d10:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4d12:	49 89 e2             	mov    %rsp,%r10
    4d15:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4d1d:	4c 89 d0             	mov    %r10,%rax
    4d20:	eb 13                	jmp    4d35 <handle_client_request+0x45>
    4d22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4d28:	48 83 c0 01          	add    $0x1,%rax
    4d2c:	48 83 c1 01          	add    $0x1,%rcx
    4d30:	4c 39 c8             	cmp    %r9,%rax
    4d33:	74 4b                	je     4d80 <handle_client_request+0x90>
        dest[i] = src[i];
    4d35:	44 0f b6 01          	movzbl (%rcx),%r8d
    4d39:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4d3c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4d40:	75 e6                	jne    4d28 <handle_client_request+0x38>
    4d42:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4d46:	75 e0                	jne    4d28 <handle_client_request+0x38>
            dest[i] = '\0';
    4d48:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4d4b:	8b 47 08             	mov    0x8(%rdi),%eax
    4d4e:	48 89 f2             	mov    %rsi,%rdx
    4d51:	4c 89 d7             	mov    %r10,%rdi
    4d54:	89 c6                	mov    %eax,%esi
    4d56:	e8 75 fe ff ff       	call   4bd0 <handle_http_method>
}
    4d5b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4d63:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d6c:	75 39                	jne    4da7 <handle_client_request+0xb7>
    4d6e:	31 c0                	xor    %eax,%eax
    4d70:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4d77:	c3                   	ret
    4d78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4d80:	48 8b 0d 99 52 00 00 	mov    0x5299(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4d87:	ba 12 00 00 00       	mov    $0x12,%edx
    4d8c:	be 01 00 00 00       	mov    $0x1,%esi
    4d91:	48 8d 3d 9f 23 00 00 	lea    0x239f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    4d98:	e8 23 d7 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4d9d:	bf 01 00 00 00       	mov    $0x1,%edi
    4da2:	e8 f9 d6 ff ff       	call   24a0 <exit@plt>
}
    4da7:	e8 84 d5 ff ff       	call   2330 <__stack_chk_fail@plt>
    4dac:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004db0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4db0:	f3 0f 1e fa          	endbr64
    4db4:	55                   	push   %rbp
    4db5:	53                   	push   %rbx
    4db6:	48 89 cb             	mov    %rcx,%rbx
    4db9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4dbd:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4dc0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4dc3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4dc9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4dcc:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4dcf:	f6 c1 02             	test   $0x2,%cl
    4dd2:	74 00                	je     4dd4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4dd4:	41 89 c0             	mov    %eax,%r8d
    4dd7:	45 29 c8             	sub    %r9d,%r8d
    4dda:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4dde:	0f 82 a8 d7 ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4de4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4de7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4dea:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4ded:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4df0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4df3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4df7:	d3 e5                	shl    %cl,%ebp
    4df9:	48 c1 e5 06          	shl    $0x6,%rbp
    4dfd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4e01:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4e04:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4e09:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4e10:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4e14:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4e18:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4e20:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4e28:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4e2c:	e8 df d5 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4e31:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4e34:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4e3a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4e3e:	48 83 c4 08          	add    $0x8,%rsp
    4e42:	5b                   	pop    %rbx
    4e43:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4e44:	e9 f7 d4 ff ff       	jmp    2340 <io_uring_submit@plt>
    4e49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004e50 <io_thread>:
void* io_thread(void *arg) {
    4e50:	f3 0f 1e fa          	endbr64
    4e54:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e56:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4e58:	41 56                	push   %r14
    4e5a:	41 55                	push   %r13
    4e5c:	41 54                	push   %r12
    4e5e:	55                   	push   %rbp
    4e5f:	48 89 fd             	mov    %rdi,%rbp
    4e62:	53                   	push   %rbx
    4e63:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4e6a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4e73:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4e7b:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4e7f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4e84:	bf 00 01 00 00       	mov    $0x100,%edi
    4e89:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4e8c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4e90:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4e95:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4e9a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4e9f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4ea4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4eac:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4eb1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4eb9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4ebe:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4ec6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4ecb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4ed3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4ed8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4ee0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4ee5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4eed:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4ef5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4efd:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4f05:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4f0d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4f15:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4f1d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4f25:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4f2d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4f35:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4f3d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4f44:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4f4c:	e8 9f d4 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4f51:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
    4f55:	31 f6                	xor    %esi,%esi
    4f57:	e8 84 d5 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4f5c:	31 d2                	xor    %edx,%edx
    4f5e:	be 01 00 00 00       	mov    $0x1,%esi
    4f63:	bf 02 00 00 00       	mov    $0x2,%edi
    4f68:	e8 c3 d5 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4f6d:	83 f8 ff             	cmp    $0xffffffff,%eax
    4f70:	0f 84 58 d6 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    4f76:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4f7b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4f81:	89 c7                	mov    %eax,%edi
    4f83:	41 89 c4             	mov    %eax,%r12d
    4f86:	ba 02 00 00 00       	mov    $0x2,%edx
    4f8b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4f90:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4f98:	e8 63 d3 ff ff       	call   2300 <setsockopt@plt>
    4f9d:	85 c0                	test   %eax,%eax
    4f9f:	0f 88 fd d5 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4fa5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4faa:	ba 10 00 00 00       	mov    $0x10,%edx
    4faf:	44 89 e7             	mov    %r12d,%edi
    4fb2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4fbb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4fc3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4fcb:	e8 90 d4 ff ff       	call   2460 <bind@plt>
    4fd0:	85 c0                	test   %eax,%eax
    4fd2:	0f 88 02 d6 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4fd8:	be 0a 00 00 00       	mov    $0xa,%esi
    4fdd:	44 89 e7             	mov    %r12d,%edi
    4fe0:	e8 3b d4 ff ff       	call   2420 <listen@plt>
    4fe5:	85 c0                	test   %eax,%eax
    4fe7:	0f 88 c1 d5 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4fed:	ba db 18 00 00       	mov    $0x18db,%edx
    4ff2:	48 8d 35 83 21 00 00 	lea    0x2183(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4ff9:	bf 01 00 00 00       	mov    $0x1,%edi
    4ffe:	31 c0                	xor    %eax,%eax
    5000:	e8 4b d4 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5005:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    500a:	48 89 d9             	mov    %rbx,%rcx
    500d:	44 89 e7             	mov    %r12d,%edi
    5010:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5015:	48 89 c6             	mov    %rax,%rsi
    5018:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    501d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5022:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    502a:	e8 81 fd ff ff       	call   4db0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    502f:	bf 01 00 00 00       	mov    $0x1,%edi
    5034:	be 10 00 00 00       	mov    $0x10,%esi
    5039:	e8 62 d3 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    503e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5043:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5046:	e8 c5 d3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    504b:	48 85 c0             	test   %rax,%rax
    504e:	0f 84 ae 04 00 00    	je     5502 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5054:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5058:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    505f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5066:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    506e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5071:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5076:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5078:	f6 c1 02             	test   $0x2,%cl
    507b:	0f 85 0f 04 00 00    	jne    5490 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5081:	89 d0                	mov    %edx,%eax
    5083:	29 f0                	sub    %esi,%eax
    5085:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    508c:	0f 82 32 d5 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5092:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5095:	48 8d 75 50          	lea    0x50(%rbp),%rsi
	sqe->addr3 = 0;
    5099:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    509d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50a0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    50a7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50aa:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    50b1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50b8:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    50ba:	8b 55 50             	mov    0x50(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    50bd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    50c2:	48 c1 e0 06          	shl    $0x6,%rax
    50c6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    50ce:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    50d4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    50d7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    50df:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    50e3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    50eb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    50f3:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    50f7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    50fb:	e8 40 d2 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5100:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5104:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5109:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5111:	0f 85 d7 01 00 00    	jne    52ee <io_thread+0x49e>
    5117:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    511c:	4d 89 ce             	mov    %r9,%r14
    511f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5124:	0f 1f 40 00          	nopl   0x0(%rax)
    5128:	48 8d 3d 63 20 00 00 	lea    0x2063(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    512f:	e8 bc d1 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5134:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    513b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5142:	c1 e9 0b             	shr    $0xb,%ecx
    5145:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5148:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5150:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5152:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    515a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    515c:	39 d0                	cmp    %edx,%eax
    515e:	74 36                	je     5196 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5160:	89 f8                	mov    %edi,%eax
    5162:	21 d0                	and    %edx,%eax
    5164:	d3 e0                	shl    %cl,%eax
    5166:	48 c1 e0 04          	shl    $0x4,%rax
    516a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5172:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    517a:	0f 85 a8 01 00 00    	jne    5328 <io_thread+0x4d8>
    5180:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5184:	0f 85 0e 03 00 00    	jne    5498 <io_thread+0x648>
			if (cqe->res < 0)
    518a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    518d:	83 c2 01             	add    $0x1,%edx
    5190:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5192:	85 c0                	test   %eax,%eax
    5194:	79 b2                	jns    5148 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5196:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    519f:	90                   	nop
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
    51c1:	0f 84 e1 02 00 00    	je     54a8 <io_thread+0x658>
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
    51ed:	0f 88 d5 02 00 00    	js     54c8 <io_thread+0x678>
      switch (req->event_type) {
    51f3:	41 83 f8 01          	cmp    $0x1,%r8d
    51f7:	0f 84 7b 01 00 00    	je     5378 <io_thread+0x528>
    51fd:	41 83 f8 02          	cmp    $0x2,%r8d
    5201:	0f 84 a1 01 00 00    	je     53a8 <io_thread+0x558>
    5207:	45 85 c0             	test   %r8d,%r8d
    520a:	0f 85 50 01 00 00    	jne    5360 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5210:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5215:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    521a:	48 89 d9             	mov    %rbx,%rcx
    521d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5221:	e8 8a fb ff ff       	call   4db0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5226:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    522b:	48 89 de             	mov    %rbx,%rsi
    522e:	8b 78 08             	mov    0x8(%rax),%edi
    5231:	e8 1a f5 ff ff       	call   4750 <add_read_request>
              free(req);
    5236:	4c 89 e7             	mov    %r12,%rdi
    5239:	e8 82 d0 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    523e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5243:	48 85 c0             	test   %rax,%rax
    5246:	0f 85 14 01 00 00    	jne    5360 <io_thread+0x510>
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
    5267:	74 00                	je     5269 <io_thread+0x419>
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
    52a3:	8b 55 50             	mov    0x50(%rbp),%edx
    52a6:	48 c1 e0 06          	shl    $0x6,%rax
    52aa:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    52b2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    52b8:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    52bb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    52c3:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    52c7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    52cf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    52d7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    52db:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    52df:	e8 5c d0 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    52e4:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    52e8:	0f 84 3a fe ff ff    	je     5128 <io_thread+0x2d8>
    52ee:	48 8d 3d fc 1e 00 00 	lea    0x1efc(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    52f5:	e8 f6 cf ff ff       	call   22f0 <puts@plt>
}
    52fa:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5302:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    530b:	0f 85 18 02 00 00    	jne    5529 <io_thread+0x6d9>
    5311:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5318:	31 c0                	xor    %eax,%eax
    531a:	5b                   	pop    %rbx
    531b:	5d                   	pop    %rbp
    531c:	41 5c                	pop    %r12
    531e:	41 5d                	pop    %r13
    5320:	41 5e                	pop    %r14
    5322:	41 5f                	pop    %r15
    5324:	c3                   	ret
    5325:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5328:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    532d:	48 85 c0             	test   %rax,%rax
    5330:	0f 84 6a fe ff ff    	je     51a0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5336:	48 83 38 01          	cmpq   $0x1,(%rax)
    533a:	0f 84 68 01 00 00    	je     54a8 <io_thread+0x658>
    5340:	48 8d 3d 71 1e 00 00 	lea    0x1e71(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    5347:	e8 a4 cf ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    534c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5351:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5354:	e9 8b fe ff ff       	jmp    51e4 <io_thread+0x394>
    5359:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5360:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5368:	8b 02                	mov    (%rdx),%eax
    536a:	83 c0 01             	add    $0x1,%eax
    536d:	89 02                	mov    %eax,(%rdx)
}
    536f:	e9 d8 fe ff ff       	jmp    524c <io_thread+0x3fc>
    5374:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5378:	85 c0                	test   %eax,%eax
    537a:	75 74                	jne    53f0 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    537c:	48 8b 0d 9d 4c 00 00 	mov    0x4c9d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5383:	ba 0f 00 00 00       	mov    $0xf,%edx
    5388:	be 01 00 00 00       	mov    $0x1,%esi
    538d:	48 8d 3d 4d 1e 00 00 	lea    0x1e4d(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    5394:	e8 27 d1 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5399:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    539e:	e9 a0 fe ff ff       	jmp    5243 <io_thread+0x3f3>
    53a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    53a8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    53ad:	45 31 ff             	xor    %r15d,%r15d
    53b0:	85 c0                	test   %eax,%eax
    53b2:	7e 20                	jle    53d4 <io_thread+0x584>
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
    53d2:	7f e4                	jg     53b8 <io_thread+0x568>
              close(req->client_socket);
    53d4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    53d9:	e8 92 cf ff ff       	call   2370 <close@plt>
              free(req);
    53de:	4c 89 e7             	mov    %r12,%rdi
    53e1:	e8 da ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    53e6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    53eb:	e9 53 fe ff ff       	jmp    5243 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    53f0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    53f5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    53fa:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5402:	eb 11                	jmp    5415 <io_thread+0x5c5>
    5404:	0f 1f 40 00          	nopl   0x0(%rax)
    5408:	48 83 c0 01          	add    $0x1,%rax
    540c:	48 83 c2 01          	add    $0x1,%rdx
    5410:	48 39 c6             	cmp    %rax,%rsi
    5413:	74 4b                	je     5460 <io_thread+0x610>
        dest[i] = src[i];
    5415:	0f b6 0a             	movzbl (%rdx),%ecx
    5418:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    541a:	80 f9 0d             	cmp    $0xd,%cl
    541d:	75 e9                	jne    5408 <io_thread+0x5b8>
    541f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5423:	75 e3                	jne    5408 <io_thread+0x5b8>
            dest[i] = '\0';
    5425:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5428:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    542d:	48 89 da             	mov    %rbx,%rdx
    5430:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5435:	e8 96 f7 ff ff       	call   4bd0 <handle_http_method>
              free(req->iov[0].iov_base);
    543a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    543f:	e8 7c ce ff ff       	call   22c0 <free@plt>
              free(req);
    5444:	4c 89 e7             	mov    %r12,%rdi
    5447:	e8 74 ce ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    544c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5451:	e9 ed fd ff ff       	jmp    5243 <io_thread+0x3f3>
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
    5490:	e9 ec fb ff ff       	jmp    5081 <io_thread+0x231>
    5495:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5498:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    549d:	e9 94 fe ff ff       	jmp    5336 <io_thread+0x4e6>
    54a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    54a8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    54b0:	48 8d 3d ed 1c 00 00 	lea    0x1ced(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    54b7:	8b 02                	mov    (%rdx),%eax
    54b9:	83 c0 01             	add    $0x1,%eax
    54bc:	89 02                	mov    %eax,(%rdx)
    54be:	e8 2d ce ff ff       	call   22f0 <puts@plt>
    54c3:	e9 26 fe ff ff       	jmp    52ee <io_thread+0x49e>
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
    5502:	48 8b 0d 17 4b 00 00 	mov    0x4b17(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5509:	ba 28 00 00 00       	mov    $0x28,%edx
    550e:	be 01 00 00 00       	mov    $0x1,%esi
    5513:	48 8d 3d ee 1e 00 00 	lea    0x1eee(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    551a:	e8 a1 cf ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    551f:	bf 01 00 00 00       	mov    $0x1,%edi
    5524:	e8 77 cf ff ff       	call   24a0 <exit@plt>
}
    5529:	e8 02 ce ff ff       	call   2330 <__stack_chk_fail@plt>
    552e:	66 90                	xchg   %ax,%ax

0000000000005530 <sendm>:
int sendm(struct BarrierTask *data) {
    5530:	f3 0f 1e fa          	endbr64
    5534:	41 57                	push   %r15
    5536:	41 56                	push   %r14
    5538:	41 55                	push   %r13
    553a:	41 54                	push   %r12
    553c:	55                   	push   %rbp
    553d:	53                   	push   %rbx
    553e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5542:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
    5549:	0f 85 a9 01 00 00    	jne    56f8 <sendm+0x1c8>
    554f:	48 8d b7 80 01 00 00 	lea    0x180(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5556:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    555c:	48 89 fa             	mov    %rdi,%rdx
    555f:	31 c9                	xor    %ecx,%ecx
    5561:	48 89 34 24          	mov    %rsi,(%rsp)
    5565:	48 8d b7 88 01 00 00 	lea    0x188(%rdi),%rsi
    556c:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5571:	85 c0                	test   %eax,%eax
    5573:	0f 8e e1 00 00 00    	jle    565a <sendm+0x12a>
    5579:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5580:	39 8a 30 01 00 00    	cmp    %ecx,0x130(%rdx)
    5586:	0f 84 c2 00 00 00    	je     564e <sendm+0x11e>
        struct Data *them = data->mailboxes[n].higher;
    558c:	49 89 ca             	mov    %rcx,%r10
    558f:	49 c1 e2 09          	shl    $0x9,%r10
    5593:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
    559a:	4d 8b 9a 80 00 00 00 	mov    0x80(%r10),%r11
        for (; them->messages_count < min;) {
    55a1:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    55a5:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    55a9:	4c 39 cb             	cmp    %r9,%rbx
    55ac:	0f 8d 93 00 00 00    	jge    5645 <sendm+0x115>
    55b2:	4c 89 cf             	mov    %r9,%rdi
    55b5:	48 8b aa 08 01 00 00 	mov    0x108(%rdx),%rbp
    55bc:	4d 8b b2 00 01 00 00 	mov    0x100(%r10),%r14
    55c3:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    55c6:	49 8b 33             	mov    (%r11),%rsi
    55c9:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    55cd:	48 83 f8 02          	cmp    $0x2,%rax
    55d1:	0f 86 09 01 00 00    	jbe    56e0 <sendm+0x1b0>
    55d7:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    55df:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    55e7:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    55eb:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    55ef:	4c 39 2c 24          	cmp    %r13,(%rsp)
    55f3:	73 7b                	jae    5670 <sendm+0x140>
    55f5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    55fa:	4d 39 fc             	cmp    %r15,%r12
    55fd:	73 71                	jae    5670 <sendm+0x140>
    55ff:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    5603:	49 01 f0             	add    %rsi,%r8
    5606:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5610:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    5617:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    561b:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    561f:	49 39 d8             	cmp    %rbx,%r8
    5622:	75 ec                	jne    5610 <sendm+0xe0>
    5624:	0f 1f 40 00          	nopl   0x0(%rax)
    5628:	48 01 fd             	add    %rdi,%rbp
    562b:	4c 01 f7             	add    %r14,%rdi
    562e:	48 89 aa 08 01 00 00 	mov    %rbp,0x108(%rdx)
    5635:	49 89 ba 00 01 00 00 	mov    %rdi,0x100(%r10)
    563c:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    5640:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5645:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5648:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    564e:	48 83 c1 01          	add    $0x1,%rcx
    5652:	39 c8                	cmp    %ecx,%eax
    5654:	0f 8f 26 ff ff ff    	jg     5580 <sendm+0x50>
}
    565a:	48 83 c4 18          	add    $0x18,%rsp
    565e:	31 c0                	xor    %eax,%eax
    5660:	5b                   	pop    %rbx
    5661:	5d                   	pop    %rbp
    5662:	41 5c                	pop    %r12
    5664:	41 5d                	pop    %r13
    5666:	41 5e                	pop    %r14
    5668:	41 5f                	pop    %r15
    566a:	c3                   	ret
    566b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5670:	49 89 fd             	mov    %rdi,%r13
    5673:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    567a:	4d 89 e0             	mov    %r12,%r8
    567d:	49 d1 ed             	shr    %r13
    5680:	49 c1 e5 04          	shl    $0x4,%r13
    5684:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5689:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    568d:	41 83 e5 10          	and    $0x10,%r13d
    5691:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5695:	74 11                	je     56a8 <sendm+0x178>
          them->messages[them->messages_count++] = data->message; 
    5697:	49 83 c0 10          	add    $0x10,%r8
    569b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    56a0:	4d 39 f8             	cmp    %r15,%r8
    56a3:	74 15                	je     56ba <sendm+0x18a>
    56a5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    56a8:	41 0f 11 00          	movups %xmm0,(%r8)
    56ac:	49 83 c0 20          	add    $0x20,%r8
    56b0:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    56b5:	4d 39 f8             	cmp    %r15,%r8
    56b8:	75 ee                	jne    56a8 <sendm+0x178>
    56ba:	49 89 f8             	mov    %rdi,%r8
    56bd:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    56c1:	49 01 d8             	add    %rbx,%r8
    56c4:	40 f6 c7 01          	test   $0x1,%dil
    56c8:	0f 84 5a ff ff ff    	je     5628 <sendm+0xf8>
          them->messages[them->messages_count++] = data->message; 
    56ce:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    56d5:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    56d9:	e9 4a ff ff ff       	jmp    5628 <sendm+0xf8>
    56de:	66 90                	xchg   %ax,%ax
    56e0:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    56e8:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    56f0:	e9 0a ff ff ff       	jmp    55ff <sendm+0xcf>
    56f5:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    56f8:	48 8d 3d 05 1b 00 00 	lea    0x1b05(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    56ff:	e8 ec cb ff ff       	call   22f0 <puts@plt>
    5704:	e9 51 ff ff ff       	jmp    565a <sendm+0x12a>
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
    5733:	48 c1 e6 09          	shl    $0x9,%rsi
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
    5775:	4c 8b 86 80 01 00 00 	mov    0x180(%rsi),%r8
      data->n++;
    577c:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    577f:	49 29 c8             	sub    %rcx,%r8
    5782:	eb 0d                	jmp    5791 <receive+0x81>
    5784:	0f 1f 40 00          	nopl   0x0(%rax)
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
    57a7:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    57ae:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    57b3:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    57b7:	75 cf                	jne    5788 <receive+0x78>
    57b9:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    57c0:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    57c4:	75 c2                	jne    5788 <receive+0x78>
    57c6:	bf 01 00 00 00       	mov    $0x1,%edi
    57cb:	b9 01 00 00 00       	mov    $0x1,%ecx
    57d0:	ba 01 00 00 00       	mov    $0x1,%edx
    57d5:	31 c0                	xor    %eax,%eax
    57d7:	48 8d 35 82 1c 00 00 	lea    0x1c82(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    57de:	e8 6d cc ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    57e3:	bf 01 00 00 00       	mov    $0x1,%edi
    57e8:	e8 b3 cc ff ff       	call   24a0 <exit@plt>
    57ed:	0f 1f 00             	nopl   (%rax)
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
    5873:	0f 85 7c 02 00 00    	jne    5af5 <barriered_work+0x2d5>
      for (int n = 0 ; n < data->thread_count; n++) {
    5879:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    587f:	85 c0                	test   %eax,%eax
    5881:	0f 8e 7a 02 00 00    	jle    5b01 <barriered_work+0x2e1>
    5887:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    588e:	31 d2                	xor    %edx,%edx
    5890:	48 89 0c 24          	mov    %rcx,(%rsp)
    5894:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    589b:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    58a0:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    58a6:	0f 84 c2 00 00 00    	je     596e <barriered_work+0x14e>
        struct Data *them = data->mailboxes[n].higher;
    58ac:	49 89 d1             	mov    %rdx,%r9
    58af:	49 c1 e1 09          	shl    $0x9,%r9
    58b3:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    58ba:	4d 8b 91 80 00 00 00 	mov    0x80(%r9),%r10
        for (; them->messages_count < min;) {
    58c1:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    58c5:	4d 63 42 10          	movslq 0x10(%r10),%r8
    58c9:	4d 39 c3             	cmp    %r8,%r11
    58cc:	0f 8d 93 00 00 00    	jge    5965 <barriered_work+0x145>
    58d2:	4c 89 c6             	mov    %r8,%rsi
    58d5:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    58dc:	4d 8b b1 00 01 00 00 	mov    0x100(%r9),%r14
    58e3:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    58e6:	49 8b 0a             	mov    (%r10),%rcx
    58e9:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    58ed:	48 83 f8 02          	cmp    $0x2,%rax
    58f1:	0f 86 91 02 00 00    	jbe    5b88 <barriered_work+0x368>
    58f7:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    58ff:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5907:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    590b:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    590f:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5913:	0f 83 ff 01 00 00    	jae    5b18 <barriered_work+0x2f8>
    5919:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    591e:	4d 39 fc             	cmp    %r15,%r12
    5921:	0f 83 f1 01 00 00    	jae    5b18 <barriered_work+0x2f8>
    5927:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    592b:	48 01 cf             	add    %rcx,%rdi
    592e:	66 90                	xchg   %ax,%ax
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
    5955:	49 89 b1 00 01 00 00 	mov    %rsi,0x100(%r9)
    595c:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5960:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5965:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5968:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    596e:	48 83 c2 01          	add    $0x1,%rdx
    5972:	39 d0                	cmp    %edx,%eax
    5974:	0f 8f 26 ff ff ff    	jg     58a0 <barriered_work+0x80>
    597a:	e9 82 01 00 00       	jmp    5b01 <barriered_work+0x2e1>
    597f:	90                   	nop
      receive(data);
    5980:	e8 8b fd ff ff       	call   5710 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    5985:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    598c:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    598e:	45 85 c9             	test   %r9d,%r9d
    5991:	0f 8e 8b 00 00 00    	jle    5a22 <barriered_work+0x202>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5997:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    599e:	4c 63 d8             	movslq %eax,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    59a1:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59a4:	49 c1 e3 09          	shl    $0x9,%r11
    59a8:	4c 8b 52 10          	mov    0x10(%rdx),%r10
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
    59dc:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    59e0:	48 8b 8c 2a 68 01 00 00 	mov    0x168(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59e8:	48 8b 17             	mov    (%rdi),%rdx
    59eb:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    59ef:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    59f2:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    59f6:	48 c1 e2 09          	shl    $0x9,%rdx
    59fa:	4a 03 94 1e 68 01 00 00 	add    0x168(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5a02:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    5a09:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    5a0d:	49 39 c1             	cmp    %rax,%r9
    5a10:	75 c6                	jne    59d8 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    5a12:	48 83 c7 08          	add    $0x8,%rdi
    5a16:	49 81 c0 00 02 00 00 	add    $0x200,%r8
    5a1d:	49 39 fc             	cmp    %rdi,%r12
    5a20:	75 ae                	jne    59d0 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    5a22:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5a25:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5a2c:	31 ff                	xor    %edi,%edi
    5a2e:	48 c1 e6 05          	shl    $0x5,%rsi
    5a32:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5a39:	e8 d2 c8 ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5a3e:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    5a45:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5a4c:	48 8b 50 38          	mov    0x38(%rax),%rdx
    5a50:	8b 4a 10             	mov    0x10(%rdx),%ecx
    5a53:	8d 69 01             	lea    0x1(%rcx),%ebp
    5a56:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5a59:	75 55                	jne    5ab0 <barriered_work+0x290>
    5a5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a60:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    5a67:	48 8b 40 10          	mov    0x10(%rax),%rax
    5a6b:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    5a6e:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5a76:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5a7a:	48 c1 e7 09          	shl    $0x9,%rdi
    5a7e:	48 03 78 28          	add    0x28(%rax),%rdi
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
    5a9b:	48 8b 40 38          	mov    0x38(%rax),%rax
    5a9f:	3b 68 10             	cmp    0x10(%rax),%ebp
    5aa2:	74 0c                	je     5ab0 <barriered_work+0x290>
    5aa4:	48 8d 3d 65 17 00 00 	lea    0x1765(%rip),%rdi        # 7210 <_IO_stdin_used+0x210>
    5aab:	e8 40 c8 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5ab0:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5ab7:	31 ff                	xor    %edi,%edi
    5ab9:	48 c1 e6 05          	shl    $0x5,%rsi
    5abd:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5ac4:	48 83 c6 10          	add    $0x10,%rsi
    5ac8:	e8 43 c8 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5acd:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    5ad4:	48 83 c0 01          	add    $0x1,%rax
    5ad8:	48 99                	cqto
    5ada:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    5ae1:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5ae8:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    5aef:	0f 84 a8 00 00 00    	je     5b9d <barriered_work+0x37d>
    5af5:	48 8d 3d 08 17 00 00 	lea    0x1708(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    5afc:	e8 ef c7 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5b01:	0f ae f8             	sfence
}
    5b04:	48 83 c4 18          	add    $0x18,%rsp
    5b08:	31 c0                	xor    %eax,%eax
    5b0a:	5b                   	pop    %rbx
    5b0b:	5d                   	pop    %rbp
    5b0c:	41 5c                	pop    %r12
    5b0e:	41 5d                	pop    %r13
    5b10:	41 5e                	pop    %r14
    5b12:	41 5f                	pop    %r15
    5b14:	c3                   	ret
    5b15:	0f 1f 00             	nopl   (%rax)
    5b18:	49 89 f5             	mov    %rsi,%r13
    5b1b:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b22:	4c 89 e7             	mov    %r12,%rdi
    5b25:	49 d1 ed             	shr    %r13
    5b28:	49 c1 e5 04          	shl    $0x4,%r13
    5b2c:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5b31:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5b35:	41 83 e5 10          	and    $0x10,%r13d
    5b39:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5b3d:	74 11                	je     5b50 <barriered_work+0x330>
          them->messages[them->messages_count++] = data->message; 
    5b3f:	48 83 c7 10          	add    $0x10,%rdi
    5b43:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5b48:	49 39 ff             	cmp    %rdi,%r15
    5b4b:	74 13                	je     5b60 <barriered_work+0x340>
    5b4d:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5b50:	0f 11 07             	movups %xmm0,(%rdi)
    5b53:	48 83 c7 20          	add    $0x20,%rdi
    5b57:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5b5b:	49 39 ff             	cmp    %rdi,%r15
    5b5e:	75 f0                	jne    5b50 <barriered_work+0x330>
    5b60:	48 89 f7             	mov    %rsi,%rdi
    5b63:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5b67:	4c 01 df             	add    %r11,%rdi
    5b6a:	40 f6 c6 01          	test   $0x1,%sil
    5b6e:	0f 84 d4 fd ff ff    	je     5948 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    5b74:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b7b:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5b7f:	e9 c4 fd ff ff       	jmp    5948 <barriered_work+0x128>
    5b84:	0f 1f 40 00          	nopl   0x0(%rax)
    5b88:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5b90:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5b98:	e9 8a fd ff ff       	jmp    5927 <barriered_work+0x107>
      for (int n = 0 ; n < data->thread_count; n++) {
    5b9d:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    5ba4:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5baa:	31 d2                	xor    %edx,%edx
    5bac:	48 89 0c 24          	mov    %rcx,(%rsp)
    5bb0:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    5bb7:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5bbc:	85 c0                	test   %eax,%eax
    5bbe:	0f 8e 3d ff ff ff    	jle    5b01 <barriered_work+0x2e1>
    5bc4:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5bc8:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5bce:	0f 84 ba 00 00 00    	je     5c8e <barriered_work+0x46e>
        struct Data *them = data->mailboxes[n].higher;
    5bd4:	49 89 d1             	mov    %rdx,%r9
    5bd7:	49 c1 e1 09          	shl    $0x9,%r9
    5bdb:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    5be2:	4d 8b 91 80 00 00 00 	mov    0x80(%r9),%r10
        for (; them->messages_count < min;) {
    5be9:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5bed:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5bf1:	4d 39 d8             	cmp    %r11,%r8
    5bf4:	0f 8e 8b 00 00 00    	jle    5c85 <barriered_work+0x465>
    5bfa:	4c 89 c6             	mov    %r8,%rsi
    5bfd:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5c04:	4d 8b b1 00 01 00 00 	mov    0x100(%r9),%r14
    5c0b:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5c0e:	49 8b 0a             	mov    (%r10),%rcx
    5c11:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5c15:	48 83 f8 02          	cmp    $0x2,%rax
    5c19:	0f 86 f1 00 00 00    	jbe    5d10 <barriered_work+0x4f0>
    5c1f:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5c27:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5c2f:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5c33:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5c37:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5c3b:	73 63                	jae    5ca0 <barriered_work+0x480>
    5c3d:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5c42:	4d 39 fc             	cmp    %r15,%r12
    5c45:	73 59                	jae    5ca0 <barriered_work+0x480>
    5c47:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5c4b:	48 01 cf             	add    %rcx,%rdi
    5c4e:	66 90                	xchg   %ax,%ax
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
    5c75:	49 89 b1 00 01 00 00 	mov    %rsi,0x100(%r9)
    5c7c:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5c80:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5c85:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5c88:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5c8e:	48 83 c2 01          	add    $0x1,%rdx
    5c92:	39 d0                	cmp    %edx,%eax
    5c94:	0f 8f 2e ff ff ff    	jg     5bc8 <barriered_work+0x3a8>
    5c9a:	e9 62 fe ff ff       	jmp    5b01 <barriered_work+0x2e1>
    5c9f:	90                   	nop
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
    5d20:	e9 22 ff ff ff       	jmp    5c47 <barriered_work+0x427>
    5d25:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005d30 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5d30:	f3 0f 1e fa          	endbr64
    5d34:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5d38:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5d3f:	48 8b 40 40          	mov    0x40(%rax),%rax
    5d43:	48 63 10             	movslq (%rax),%rdx
    5d46:	85 d2                	test   %edx,%edx
    5d48:	7e 2c                	jle    5d76 <barriered_work_ingest+0x46>
    5d4a:	48 8b 40 08          	mov    0x8(%rax),%rax
    5d4e:	48 c1 e2 04          	shl    $0x4,%rdx
    5d52:	48 01 c2             	add    %rax,%rdx
    5d55:	0f 1f 00             	nopl   (%rax)
    if (data->thread->buffers->buffer[x].available == 1) {
    5d58:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5d5c:	75 0f                	jne    5d6d <barriered_work_ingest+0x3d>
      data->ingest_count++;
    5d5e:	48 83 87 60 01 00 00 01 	addq   $0x1,0x160(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5d66:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5d6d:	48 83 c0 10          	add    $0x10,%rax
    5d71:	48 39 d0             	cmp    %rdx,%rax
    5d74:	75 e2                	jne    5d58 <barriered_work_ingest+0x28>
  asm volatile ("sfence" ::: "memory");
    5d76:	0f ae f8             	sfence
  barriered_work(data);
    5d79:	e8 a2 fa ff ff       	call   5820 <barriered_work>
}
    5d7e:	31 c0                	xor    %eax,%eax
    5d80:	48 83 c4 08          	add    $0x8,%rsp
    5d84:	c3                   	ret
    5d85:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

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
    5eec:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
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
    6158:	48 81 44 24 10 b0 00 00 00 	addq   $0xb0,0x10(%rsp)
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
    61f5:	48 81 44 24 18 b0 00 00 00 	addq   $0xb0,0x18(%rsp)
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
