
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
    2617:	48 8d 05 82 10 00 00 	lea    0x1082(%rip),%rax        # 36a0 <barriered_reset>
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
    2764:	4c 8b 2c 24          	mov    (%rsp),%r13
    2768:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    276d:	49 89 c7             	mov    %rax,%r15
  int snapshot_limit = 10;
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
    2797:	bf 0a 00 00 00       	mov    $0xa,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    279c:	49 89 44 24 f8       	mov    %rax,-0x8(%r12)
    27a1:	48 89 c3             	mov    %rax,%rbx
      buffers[x].buffer[y].available = 0;
    27a4:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    27ae:	c7 80 90 00 00 00 0a 00 00 00 	movl   $0xa,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    27b8:	e8 e3 fb ff ff       	call   23a0 <calloc@plt>
    27bd:	48 89 83 88 00 00 00 	mov    %rax,0x88(%rbx)
  for (int x = 0 ; x < buffers_required; x++) {
    27c4:	4c 39 e5             	cmp    %r12,%rbp
    27c7:	75 ae                	jne    2777 <main+0x187>
    27c9:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    }
  }
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
    27ce:	c7 44 24 40 00 00 00 00 	movl   $0x0,0x40(%rsp)
  int my_buffers = 0;
  int cur_buffer = 0;
    27d6:	45 31 e4             	xor    %r12d,%r12d
        thread_data[x].tasks[y].snapshot_count = 99;
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
        thread_data[x].tasks[y].current_snapshot = 0;
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
        thread_data[x].tasks[y].thread = &thread_data[x]; 
        thread_data[x].tasks[y].available = 1;
    27d9:	4c 89 6c 24 50       	mov    %r13,0x50(%rsp)
    27de:	4c 8d 70 e8          	lea    -0x18(%rax),%r14
  for (int x = 0 ; x < buffers_required; x++) {
    27e2:	4c 89 7c 24 18       	mov    %r15,0x18(%rsp)
        thread_data[x].tasks[y].available = 1;
    27e7:	4d 89 ef             	mov    %r13,%r15
    27ea:	4c 89 f3             	mov    %r14,%rbx
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27ed:	be 08 00 00 00       	mov    $0x8,%esi
    27f2:	bf 02 00 00 00       	mov    $0x2,%edi
    27f7:	e8 a4 fb ff ff       	call   23a0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27fc:	be 80 00 00 00       	mov    $0x80,%esi
    2801:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2806:	48 89 c5             	mov    %rax,%rbp
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2809:	e8 92 fb ff ff       	call   23a0 <calloc@plt>
    280e:	44 89 24 24          	mov    %r12d,(%rsp)
    2812:	44 89 e2             	mov    %r12d,%edx
    2815:	49 89 c5             	mov    %rax,%r13
    if (x % 2 == 1) {
    2818:	44 89 e0             	mov    %r12d,%eax
      other = (x + 1) % total_threads;
    281b:	41 83 c4 01          	add    $0x1,%r12d
    if (x % 2 == 1) {
    281f:	83 e0 01             	and    $0x1,%eax
    2822:	85 c0                	test   %eax,%eax
    2824:	0f 84 b1 07 00 00    	je     2fdb <main+0x9eb>
      my_thread_data[0] = &thread_data[other]; 
    282a:	49 8d 8f 50 ff ff ff 	lea    -0xb0(%r15),%rcx
      my_thread_data[1] = &thread_data[x]; 
    2831:	4c 89 7d 08          	mov    %r15,0x8(%rbp)
    2835:	4d 89 f8             	mov    %r15,%r8
    2838:	31 c0                	xor    %eax,%eax
      thread_data[x].thread_index = 1;
    283a:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
    2841:	bf 01 00 00 00       	mov    $0x1,%edi
      other = abs(x - 1) % total_threads;
    2846:	44 8d 72 ff          	lea    -0x1(%rdx),%r14d
    284a:	48 8d 35 aa 4a 00 00 	lea    0x4aaa(%rip),%rsi        # 72fb <_IO_stdin_used+0x2fb>
      my_thread_data[0] = &thread_data[other]; 
    2851:	48 89 4d 00          	mov    %rcx,0x0(%rbp)
    2855:	e8 f6 fb ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    285a:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    285e:	48 89 d8             	mov    %rbx,%rax
    2861:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
    2866:	8b 1c 24             	mov    (%rsp),%ebx
    2869:	49 89 47 38          	mov    %rax,0x38(%r15)
    286d:	44 89 f1             	mov    %r14d,%ecx
    2870:	bf 01 00 00 00       	mov    $0x1,%edi
    2875:	45 8b 07             	mov    (%r15),%r8d
    2878:	48 8d 35 f1 4c 00 00 	lea    0x4cf1(%rip),%rsi        # 7570 <_IO_stdin_used+0x570>
    287f:	31 c0                	xor    %eax,%eax
    2881:	89 da                	mov    %ebx,%edx
    2883:	e8 c8 fb ff ff       	call   2450 <__printf_chk@plt>
    thread_data[x].other = other;
    2888:	45 89 b7 a8 00 00 00 	mov    %r14d,0xa8(%r15)
    288f:	31 c0                	xor    %eax,%eax
    2891:	89 da                	mov    %ebx,%edx
    2893:	8b 4c 24 40          	mov    0x40(%rsp),%ecx
    2897:	48 8d 35 02 4d 00 00 	lea    0x4d02(%rip),%rsi        # 75a0 <_IO_stdin_used+0x5a0>
    289e:	bf 01 00 00 00       	mov    $0x1,%edi
    28a3:	e8 a8 fb ff ff       	call   2450 <__printf_chk@plt>
      if (x < thread_count) {
    28a8:	83 fb 01             	cmp    $0x1,%ebx
    28ab:	0f 86 93 07 00 00    	jbe    3044 <main+0xa54>
          CPU_SET(j, sendercpu);
    28b1:	49 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%r13)
    thread_data[x].real_thread_index = x;
    28b9:	8b 04 24             	mov    (%rsp),%eax
    thread_data[x].threads = my_thread_data;
    28bc:	49 89 6f 10          	mov    %rbp,0x10(%r15)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    28c0:	31 ed                	xor    %ebp,%ebp
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28c2:	be 10 00 00 00       	mov    $0x10,%esi
    thread_data[x].cpu_set = sendercpu;
    28c7:	4d 89 af a0 00 00 00 	mov    %r13,0xa0(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28ce:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].real_thread_index = x;
    28d3:	41 89 47 04          	mov    %eax,0x4(%r15)
    thread_data[x].thread_count = 2;
    28d7:	48 8b 05 a2 51 00 00 	mov    0x51a2(%rip),%rax        # 7a80 <_IO_stdin_used+0xa80>
    thread_data[x].task_count = total_barrier_count;
    28de:	41 c7 47 30 03 00 00 00 	movl   $0x3,0x30(%r15)
    thread_data[x].thread_count = 2;
    28e6:	49 89 47 18          	mov    %rax,0x18(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28ea:	e8 b1 fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28ef:	be 10 00 00 00       	mov    $0x10,%esi
    28f4:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28f9:	49 89 47 58          	mov    %rax,0x58(%r15)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28fd:	e8 9e fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2902:	be 28 00 00 00       	mov    $0x28,%esi
    2907:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    290c:	66 0f 6f 1d 4c 51 00 00 	movdqa 0x514c(%rip),%xmm3        # 7a60 <_IO_stdin_used+0xa60>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2914:	49 89 47 60          	mov    %rax,0x60(%r15)
    thread_data[x].timestamp_count = 0;
    2918:	41 0f 11 5f 70       	movups %xmm3,0x70(%r15)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    291d:	e8 7e fa ff ff       	call   23a0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2922:	be 00 02 00 00       	mov    $0x200,%esi
    2927:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
    292c:	66 0f 6f 25 2c 51 00 00 	movdqa 0x512c(%rip),%xmm4        # 7a60 <_IO_stdin_used+0xa60>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2934:	49 89 87 80 00 00 00 	mov    %rax,0x80(%r15)
    thread_data[x].task_timestamp_count = 0;
    293b:	41 0f 11 a7 88 00 00 00 	movups %xmm4,0x88(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2943:	e8 58 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    2948:	44 89 64 24 28       	mov    %r12d,0x28(%rsp)
      thread_data[x].tasks = barriers;
    294d:	49 89 47 28          	mov    %rax,0x28(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2951:	49 89 c6             	mov    %rax,%r14
        thread_data[x].tasks[y].protected = do_protected_write; 
    2954:	4c 63 e5             	movslq %ebp,%r12
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2957:	be 20 00 00 00       	mov    $0x20,%esi
    295c:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    2961:	4c 89 e3             	mov    %r12,%rbx
    2964:	48 8d 05 f5 0c 00 00 	lea    0xcf5(%rip),%rax        # 3660 <do_protected_write>
    296b:	48 c1 e3 09          	shl    $0x9,%rbx
    296f:	49 01 de             	add    %rbx,%r14
    2972:	49 89 86 20 01 00 00 	mov    %rax,0x120(%r14)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2979:	e8 22 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    297e:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    2983:	89 6c 24 10          	mov    %ebp,0x10(%rsp)
    2987:	4c 8d 68 40          	lea    0x40(%rax),%r13
    298b:	49 89 86 68 01 00 00 	mov    %rax,0x168(%r14)
        for (int b = 0 ; b < 2 ; b++) {
    2992:	49 89 c6             	mov    %rax,%r14
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2995:	be 08 00 00 00       	mov    $0x8,%esi
    299a:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    299f:	49 83 c6 20          	add    $0x20,%r14
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29a3:	e8 f8 f9 ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29a8:	be 08 00 00 00       	mov    $0x8,%esi
    29ad:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    29b2:	48 89 c5             	mov    %rax,%rbp
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29b5:	e8 e6 f9 ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    29ba:	be 18 00 00 00       	mov    $0x18,%esi
    29bf:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29c4:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29c7:	e8 d4 f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    29cc:	66 0f 6f 05 9c 50 00 00 	movdqa 0x509c(%rip),%xmm0        # 7a70 <_IO_stdin_used+0xa70>
          mailboxes[b].higher = &data[1];
    29d4:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29d8:	49 89 46 e0          	mov    %rax,-0x20(%r14)
          mailboxes[b].higher = &data[1];
    29dc:	49 89 76 e8          	mov    %rsi,-0x18(%r14)
          data[0].messages = messages;
    29e0:	48 89 28             	mov    %rbp,(%rax)
          data[1].messages = messages2;
    29e3:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    29e7:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    29eb:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    29ef:	4d 39 f5             	cmp    %r14,%r13
    29f2:	75 a1                	jne    2995 <main+0x3a5>
        char *message = malloc(sizeof(char) * 256);
    29f4:	be 01 00 00 00       	mov    $0x1,%esi
    29f9:	bf 00 01 00 00       	mov    $0x100,%edi
    29fe:	8b 6c 24 10          	mov    0x10(%rsp),%ebp
    2a02:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    2a07:	e8 94 f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2a0c:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2a11:	49 89 c5             	mov    %rax,%r13
        struct Message *messaged = malloc(sizeof(struct Message));
    2a14:	e8 f7 f9 ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2a19:	44 8b 04 24          	mov    (%rsp),%r8d
    2a1d:	4c 89 ef             	mov    %r13,%rdi
    2a20:	41 89 e9             	mov    %ebp,%r9d
    2a23:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2a28:	48 8d 0d 91 4b 00 00 	lea    0x4b91(%rip),%rcx        # 75c0 <_IO_stdin_used+0x5c0>
    2a2f:	ba 00 01 00 00       	mov    $0x100,%edx
    2a34:	31 c0                	xor    %eax,%eax
    2a36:	be 01 00 00 00       	mov    $0x1,%esi
    2a3b:	e8 e0 fa ff ff       	call   2520 <__sprintf_chk@plt>
        messaged->thread_index = thread_data[x].thread_index;
    2a40:	49 63 07             	movslq (%r15),%rax
        messaged->message = message;
    2a43:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a48:	bf 63 00 00 00       	mov    $0x63,%edi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a4d:	4d 8b 77 28          	mov    0x28(%r15),%r14
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a51:	be 20 00 00 00       	mov    $0x20,%esi
        messaged->message = message;
    2a56:	4d 89 2a             	mov    %r13,(%r10)
        messaged->thread_index = thread_data[x].thread_index;
    2a59:	49 89 c5             	mov    %rax,%r13
    2a5c:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a60:	8d 45 01             	lea    0x1(%rbp),%eax
    2a63:	4c 01 f3             	add    %r14,%rbx
    2a66:	83 e0 01             	and    $0x1,%eax
        messaged->task_index = y;
    2a69:	4d 89 62 10          	mov    %r12,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a6d:	89 83 88 01 00 00    	mov    %eax,0x188(%rbx)
        thread_data[x].tasks[y].message = messaged;
    2a73:	4c 89 93 80 01 00 00 	mov    %r10,0x180(%rbx)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a7a:	48 c7 83 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%rbx)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a85:	e8 16 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a8a:	44 89 ab 30 01 00 00 	mov    %r13d,0x130(%rbx)
        thread_data[x].tasks[y].sending = 1;
    2a91:	48 bf 01 00 00 00 02 00 00 00 	movabs $0x200000001,%rdi
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a9b:	48 89 83 48 01 00 00 	mov    %rax,0x148(%rbx)
        thread_data[x].tasks[y].available = 1;
    2aa2:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2aac:	48 c7 83 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%rbx)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2ab7:	4c 89 bb 28 01 00 00 	mov    %r15,0x128(%rbx)
        thread_data[x].tasks[y].arrived = 0;
    2abe:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
        thread_data[x].tasks[y].thread_count = 2;
    2ac8:	c7 83 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%rbx)
        thread_data[x].tasks[y].available = 1;
    2ad2:	48 89 83 38 01 00 00 	mov    %rax,0x138(%rbx)
        thread_data[x].tasks[y].sending = 1;
    2ad9:	48 89 bb 78 01 00 00 	mov    %rdi,0x178(%rbx)
        thread_data[x].tasks[y].task_count = total_barrier_count;
        thread_data[x].tasks[y].worker_count = thread_count;
        thread_data[x].tasks[y].task_index = y;
    2ae0:	89 2b                	mov    %ebp,(%rbx)
        if (y == barrier_count - 1) {
    2ae2:	83 fd 01             	cmp    $0x1,%ebp
    2ae5:	0f 84 e2 04 00 00    	je     2fcd <main+0x9dd>
            thread_data[x].tasks[y].run = barriered_nulltask; 
          }
          */
          thread_data[x].tasks[y].run = barriered_work; 
        } else {
          if (y == 0) {
    2aeb:	85 ed                	test   %ebp,%ebp
    2aed:	0f 84 c2 04 00 00    	je     2fb5 <main+0x9c5>
            // printf("Thread %d is an ingest thread\n", x);
            thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
            assigned = 1;
           } else {
             thread_data[x].tasks[y].run = barriered_work; 
    2af3:	48 8d 3d 76 2b 00 00 	lea    0x2b76(%rip),%rdi        # 5670 <barriered_work>
           }
        }
      }
			thread_data[x].buffers_count = buffers_per_thread;
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2afa:	be 08 00 00 00       	mov    $0x8,%esi
             thread_data[x].tasks[y].run = barriered_work; 
    2aff:	44 8b 64 24 28       	mov    0x28(%rsp),%r12d
    2b04:	48 89 bb 18 01 00 00 	mov    %rdi,0x118(%rbx)
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2b0b:	bf 01 00 00 00       	mov    $0x1,%edi
			thread_data[x].buffers_count = buffers_per_thread;
    2b10:	41 c7 87 ac 00 00 00 01 00 00 00 	movl   $0x1,0xac(%r15)
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2b1b:	e8 80 f8 ff ff       	call   23a0 <calloc@plt>
      for (int b = 0 ; b < buffers_per_thread; b++) {	
        thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2b20:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
      }
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b25:	66 0f 6f 54 24 30    	movdqa 0x30(%rsp),%xmm2
      thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2b2b:	49 89 47 40          	mov    %rax,0x40(%r15)
  for (int x = 0 ; x < total_threads ; x++) {
    2b2f:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
        thread_data[x].buffers[b] = &buffers[cur_buffer++];
    2b34:	48 89 38             	mov    %rdi,(%rax)
  for (int x = 0 ; x < total_threads ; x++) {
    2b37:	48 83 c7 10          	add    $0x10,%rdi
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
    2b3b:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2b45:	4d 89 be 28 05 00 00 	mov    %r15,0x528(%r14)
  for (int x = 0 ; x < total_threads ; x++) {
    2b4c:	49 81 c7 b0 00 00 00 	add    $0xb0,%r15
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2b53:	41 c7 86 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r14)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2b5e:	41 c7 86 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%r14)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2b69:	45 89 ae 30 05 00 00 	mov    %r13d,0x530(%r14)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2b70:	41 c7 86 7c 05 00 00 02 00 00 00 	movl   $0x2,0x57c(%r14)
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b7b:	41 c7 86 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r14)
      thread_data[x].tasks[barrier_count].available = 1; 
    2b86:	49 89 86 38 05 00 00 	mov    %rax,0x538(%r14)
  for (int x = 0 ; x < total_threads ; x++) {
    2b8d:	48 89 7c 24 18       	mov    %rdi,0x18(%rsp)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b92:	41 0f 11 96 18 05 00 00 	movups %xmm2,0x518(%r14)
  for (int x = 0 ; x < total_threads ; x++) {
    2b9a:	41 83 fc 06          	cmp    $0x6,%r12d
    2b9e:	0f 85 49 fc ff ff    	jne    27ed <main+0x1fd>
    2ba4:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2ba9:	ba 03 00 00 00       	mov    $0x3,%edx
    2bae:	48 8d 35 63 47 00 00 	lea    0x4763(%rip),%rsi        # 7318 <_IO_stdin_used+0x318>
    2bb5:	31 c0                	xor    %eax,%eax
    2bb7:	bf 01 00 00 00       	mov    $0x1,%edi
    2bbc:	4c 89 14 24          	mov    %r10,(%rsp)
    2bc0:	e8 8b f8 ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2bc5:	be 08 00 00 00       	mov    $0x8,%esi
    2bca:	bf 02 00 00 00       	mov    $0x2,%edi
    2bcf:	e8 cc f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2bd4:	4c 8b 14 24          	mov    (%rsp),%r10
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bd8:	be 38 00 00 00       	mov    $0x38,%esi
    2bdd:	bf 06 00 00 00       	mov    $0x6,%edi
    my_thread_data[0] = &thread_data[x]; 
    2be2:	49 8d aa 10 02 00 00 	lea    0x210(%r10),%rbp
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2be9:	4c 89 50 08          	mov    %r10,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2bed:	4d 8d a2 b0 00 00 00 	lea    0xb0(%r10),%r12
    thread_data[x].threads = my_thread_data;
    2bf4:	49 89 82 20 02 00 00 	mov    %rax,0x220(%r10)
    my_thread_data[0] = &thread_data[x]; 
    2bfb:	48 89 28             	mov    %rbp,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2bfe:	49 8b 42 28          	mov    0x28(%r10),%rax
    thread_data[x].thread_count = 2;
    2c02:	41 c7 82 28 02 00 00 02 00 00 00 	movl   $0x2,0x228(%r10)
    thread_data[x].thread_index = 0;
    2c0d:	41 c7 82 10 02 00 00 00 00 00 00 	movl   $0x0,0x210(%r10)
    thread_data[x].task_count = total_barrier_count;
    2c18:	41 c7 82 40 02 00 00 03 00 00 00 	movl   $0x3,0x240(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2c23:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2c2d:	49 8b 82 d8 00 00 00 	mov    0xd8(%r10),%rax
    2c34:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    2c39:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c43:	e8 58 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c48:	be 38 00 00 00       	mov    $0x38,%esi
    2c4d:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c52:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c55:	e8 46 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c5a:	be 38 00 00 00       	mov    $0x38,%esi
    2c5f:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c64:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c67:	e8 34 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c6c:	be 38 00 00 00       	mov    $0x38,%esi
    2c71:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c76:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c7a:	e8 21 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2c7f:	be 08 00 00 00       	mov    $0x8,%esi
    2c84:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c89:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2c8e:	e8 0d f7 ff ff       	call   23a0 <calloc@plt>

  thread_data[thread_count].type = TIMER;
    2c93:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2c98:	be 08 00 00 00       	mov    $0x8,%esi
    2c9d:	bf 06 00 00 00       	mov    $0x6,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2ca2:	48 89 c3             	mov    %rax,%rbx
  thread_data[thread_count].task_count = total_barrier_count;
    2ca5:	48 8b 05 dc 4d 00 00 	mov    0x4ddc(%rip),%rax        # 7a88 <_IO_stdin_used+0xa88>
  thread_data[thread_count].type = TIMER;
    2cac:	41 c7 82 68 01 00 00 00 00 00 00 	movl   $0x0,0x168(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2cb7:	49 89 82 90 01 00 00 	mov    %rax,0x190(%r10)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2cbe:	e8 dd f6 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2cc3:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2cc8:	bf 01 00 00 00       	mov    $0x1,%edi
    2ccd:	48 8d 35 53 46 00 00 	lea    0x4653(%rip),%rsi        # 7327 <_IO_stdin_used+0x327>
    2cd4:	48 89 68 18          	mov    %rbp,0x18(%rax)
    2cd8:	49 8d 8a 60 01 00 00 	lea    0x160(%r10),%rcx
    2cdf:	4d 8d ba c0 02 00 00 	lea    0x2c0(%r10),%r15
    2ce6:	4c 89 10             	mov    %r10,(%rax)
    2ce9:	49 8d 92 70 03 00 00 	lea    0x370(%r10),%rdx
  }
  thread_data[thread_count].threads = my_thread_data;
    2cf0:	49 89 82 70 01 00 00 	mov    %rax,0x170(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2cf7:	48 89 48 10          	mov    %rcx,0x10(%rax)
    2cfb:	4c 89 78 20          	mov    %r15,0x20(%rax)
    2cff:	48 89 50 28          	mov    %rdx,0x28(%rax)
    2d03:	ba 02 00 00 00       	mov    $0x2,%edx
  thread_data[thread_count].thread_count = thread_count;
    2d08:	41 c7 82 78 01 00 00 02 00 00 00 	movl   $0x2,0x178(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2d13:	41 c7 82 80 01 00 00 02 00 00 00 	movl   $0x2,0x180(%r10)
  thread_data[thread_count].thread_index = 0;
    2d1e:	41 c7 82 60 01 00 00 00 00 00 00 	movl   $0x0,0x160(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2d29:	4c 89 60 08          	mov    %r12,0x8(%rax)
    2d2d:	31 c0                	xor    %eax,%eax
    2d2f:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    2d34:	e8 17 f7 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2d39:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    2d3e:	49 8d 75 70          	lea    0x70(%r13),%rsi
    2d42:	48 8d 7b 10          	lea    0x10(%rbx),%rdi
    2d46:	48 8d 15 d3 0a 00 00 	lea    0xad3(%rip),%rdx        # 3820 <timer_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    thread_data[x].type = WORKER;
    thread_data[x].running = 1;
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2d4d:	4c 8d 2d 2c 25 00 00 	lea    0x252c(%rip),%r13        # 5280 <barriered_thread>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2d54:	e8 17 f7 ff ff       	call   2470 <pthread_create@plt>
    thread_data[x].type = WORKER;
    2d59:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2d5e:	31 d2                	xor    %edx,%edx
    2d60:	31 c0                	xor    %eax,%eax
    2d62:	4c 8d 0d 7f 48 00 00 	lea    0x487f(%rip),%r9        # 75e8 <_IO_stdin_used+0x5e8>
    2d69:	bf 01 00 00 00       	mov    $0x1,%edi
    2d6e:	41 c7 42 08 01 00 00 00 	movl   $0x1,0x8(%r10)
    2d76:	4c 89 ce             	mov    %r9,%rsi
    thread_data[x].running = 1;
    2d79:	41 c7 42 34 01 00 00 00 	movl   $0x1,0x34(%r10)
    2d81:	e8 ca f6 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2d86:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2d8b:	4c 89 ea             	mov    %r13,%rdx
    2d8e:	4c 89 f6             	mov    %r14,%rsi
    2d91:	48 89 df             	mov    %rbx,%rdi
    2d94:	e8 d7 f6 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2d99:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2d9e:	48 8b 3b             	mov    (%rbx),%rdi
    2da1:	be 08 00 00 00       	mov    $0x8,%esi
    2da6:	49 8b 92 a0 00 00 00 	mov    0xa0(%r10),%rdx
    2dad:	e8 2e f5 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    thread_data[x].type = WORKER;
    2db2:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2db7:	ba 01 00 00 00       	mov    $0x1,%edx
    2dbc:	31 c0                	xor    %eax,%eax
    2dbe:	4c 8d 0d 23 48 00 00 	lea    0x4823(%rip),%r9        # 75e8 <_IO_stdin_used+0x5e8>
    2dc5:	bf 01 00 00 00       	mov    $0x1,%edi
    2dca:	41 c7 82 b8 00 00 00 01 00 00 00 	movl   $0x1,0xb8(%r10)
    2dd5:	4c 89 ce             	mov    %r9,%rsi
    thread_data[x].running = 1;
    2dd8:	41 c7 82 e4 00 00 00 01 00 00 00 	movl   $0x1,0xe4(%r10)
    2de3:	e8 68 f6 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2de8:	4c 89 e1             	mov    %r12,%rcx
    2deb:	49 8d 76 38          	lea    0x38(%r14),%rsi
    2def:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    2df3:	4c 89 ea             	mov    %r13,%rdx
    2df6:	4c 8d 6b 20          	lea    0x20(%rbx),%r13
    2dfa:	4d 89 fe             	mov    %r15,%r14
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2dfd:	41 bf 04 00 00 00    	mov    $0x4,%r15d
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2e03:	e8 68 f6 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2e08:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2e0d:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    2e11:	be 08 00 00 00       	mov    $0x8,%esi
    2e16:	49 8b 92 50 01 00 00 	mov    0x150(%r10),%rdx
    2e1d:	e8 be f4 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    thread_data[x].type = IO;
    2e22:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e27:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].task_count = 0;
    2e2c:	48 8b 3d 5d 4c 00 00 	mov    0x4c5d(%rip),%rdi        # 7a90 <_IO_stdin_used+0xa90>
    thread_data[x].type = IO;
    2e33:	41 c7 82 18 02 00 00 02 00 00 00 	movl   $0x2,0x218(%r10)
    thread_data[x].task_count = 0;
    2e3e:	49 89 ba 40 02 00 00 	mov    %rdi,0x240(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e45:	bf 01 00 00 00       	mov    $0x1,%edi
    2e4a:	e8 51 f5 ff ff       	call   23a0 <calloc@plt>
    2e4f:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e54:	be 00 08 00 00       	mov    $0x800,%esi
    2e59:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e5b:	49 89 82 58 02 00 00 	mov    %rax,0x258(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e62:	e8 49 f6 ff ff       	call   24b0 <eventfd@plt>
    2e67:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2e6c:	be 08 00 00 00       	mov    $0x8,%esi
    2e71:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e76:	41 89 82 60 02 00 00 	mov    %eax,0x260(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2e7d:	e8 1e f5 ff ff       	call   23a0 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
    2e82:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2e87:	ba 03 00 00 00       	mov    $0x3,%edx
    2e8c:	48 8d 35 b2 44 00 00 	lea    0x44b2(%rip),%rsi        # 7345 <_IO_stdin_used+0x345>
    2e93:	4c 89 60 08          	mov    %r12,0x8(%rax)
    2e97:	bf 01 00 00 00       	mov    $0x1,%edi
    2e9c:	4c 89 10             	mov    %r10,(%rax)
    thread_data[x].threads = my_thread_data;
    2e9f:	49 89 82 20 02 00 00 	mov    %rax,0x220(%r10)
    2ea6:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_count = thread_count;
    2ea8:	41 c7 82 28 02 00 00 02 00 00 00 	movl   $0x2,0x228(%r10)
    thread_data[x].thread_index = x;
    2eb3:	41 c7 82 10 02 00 00 03 00 00 00 	movl   $0x3,0x210(%r10)
    2ebe:	e8 8d f5 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2ec3:	48 8b 34 24          	mov    (%rsp),%rsi
    2ec7:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    2ecb:	48 89 e9             	mov    %rbp,%rcx
    2ece:	48 8d 15 bb 1b 00 00 	lea    0x1bbb(%rip),%rdx        # 4a90 <io_thread>
    2ed5:	48 81 c6 a8 00 00 00 	add    $0xa8,%rsi
    2edc:	e8 8f f5 ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2ee1:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    2ee6:	48 89 1c 24          	mov    %rbx,(%rsp)
    2eea:	4c 89 eb             	mov    %r13,%rbx
    2eed:	48 81 c5 e0 00 00 00 	add    $0xe0,%rbp
    2ef4:	49 89 ed             	mov    %rbp,%r13
    2ef7:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    2efc:	44 89 fa             	mov    %r15d,%edx
    2eff:	48 8d 35 56 44 00 00 	lea    0x4456(%rip),%rsi        # 735c <_IO_stdin_used+0x35c>
    2f06:	bf 01 00 00 00       	mov    $0x1,%edi
    2f0b:	31 c0                	xor    %eax,%eax
    2f0d:	e8 3e f5 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    2f12:	be 08 00 00 00       	mov    $0x8,%esi
    2f17:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    2f1c:	48 8b 05 6d 4b 00 00 	mov    0x4b6d(%rip),%rax        # 7a90 <_IO_stdin_used+0xa90>
    thread_data[x].type = EXTERNAL;
    2f23:	41 c7 46 08 03 00 00 00 	movl   $0x3,0x8(%r14)
    thread_data[x].task_count = 0;
    2f2b:	49 89 46 30          	mov    %rax,0x30(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    2f2f:	e8 6c f4 ff ff       	call   23a0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    2f34:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f39:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    2f3e:	41 c7 86 ac 00 00 00 01 00 00 00 	movl   $0x1,0xac(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    2f49:	49 89 46 40          	mov    %rax,0x40(%r14)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    2f4d:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f50:	bf 02 00 00 00       	mov    $0x2,%edi
    2f55:	e8 46 f4 ff ff       	call   23a0 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    2f5a:	45 89 3e             	mov    %r15d,(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f5d:	4c 89 f1             	mov    %r14,%rcx
    2f60:	4c 89 ee             	mov    %r13,%rsi
    thread_data[x].threads = my_thread_data;
    2f63:	49 89 46 10          	mov    %rax,0x10(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f67:	48 89 df             	mov    %rbx,%rdi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2f6a:	49 83 c5 38          	add    $0x38,%r13
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f6e:	48 8d 15 9b 07 00 00 	lea    0x79b(%rip),%rdx        # 3710 <external_thread>
      my_thread_data[n] = &thread_data[n]; 
    2f75:	48 89 28             	mov    %rbp,(%rax)
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2f78:	49 81 c6 b0 00 00 00 	add    $0xb0,%r14
    2f7f:	48 83 c3 08          	add    $0x8,%rbx
      my_thread_data[n] = &thread_data[n]; 
    2f83:	4c 89 60 08          	mov    %r12,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    2f87:	48 8b 05 f2 4a 00 00 	mov    0x4af2(%rip),%rax        # 7a80 <_IO_stdin_used+0xa80>
    2f8e:	49 89 86 68 ff ff ff 	mov    %rax,-0x98(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f95:	e8 d6 f4 ff ff       	call   2470 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    2f9a:	48 83 44 24 58 10    	addq   $0x10,0x58(%rsp)
    2fa0:	41 83 ff 04          	cmp    $0x4,%r15d
    2fa4:	0f 85 c7 00 00 00    	jne    3071 <main+0xa81>
    2faa:	41 bf 05 00 00 00    	mov    $0x5,%r15d
    2fb0:	e9 47 ff ff ff       	jmp    2efc <main+0x90c>
    2fb5:	48 8d 05 b4 2b 00 00 	lea    0x2bb4(%rip),%rax        # 5b70 <barriered_work_ingest_andwork>
    2fbc:	bd 01 00 00 00       	mov    $0x1,%ebp
          thread_data[x].tasks[y].run = barriered_work; 
    2fc1:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2fc8:	e9 87 f9 ff ff       	jmp    2954 <main+0x364>
    2fcd:	48 8d 05 9c 26 00 00 	lea    0x269c(%rip),%rax        # 5670 <barriered_work>
    2fd4:	bd 02 00 00 00       	mov    $0x2,%ebp
    2fd9:	eb e6                	jmp    2fc1 <main+0x9d1>
      other = (x + 1) % total_threads;
    2fdb:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
    2fe0:	45 89 e2             	mov    %r12d,%r10d
    2fe3:	45 89 e6             	mov    %r12d,%r14d
      my_thread_data[0] = &thread_data[x]; 
    2fe6:	4c 89 7d 00          	mov    %r15,0x0(%rbp)
      other = (x + 1) % total_threads;
    2fea:	4c 0f af d0          	imul   %rax,%r10
    2fee:	4c 89 f9             	mov    %r15,%rcx
      thread_data[x].thread_index = 0;
    2ff1:	41 c7 07 00 00 00 00 	movl   $0x0,(%r15)
    2ff8:	48 8d 35 0a 43 00 00 	lea    0x430a(%rip),%rsi        # 7309 <_IO_stdin_used+0x309>
    2fff:	bf 01 00 00 00       	mov    $0x1,%edi
      other = (x + 1) % total_threads;
    3004:	49 c1 ea 22          	shr    $0x22,%r10
    3008:	43 8d 04 52          	lea    (%r10,%r10,2),%eax
    300c:	01 c0                	add    %eax,%eax
    300e:	41 29 c6             	sub    %eax,%r14d
      my_thread_data[1] = &thread_data[other]; 
    3011:	49 63 c6             	movslq %r14d,%rax
    3014:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3018:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    301c:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    3021:	8b 14 24             	mov    (%rsp),%edx
    3024:	49 c1 e0 04          	shl    $0x4,%r8
    3028:	49 01 c0             	add    %rax,%r8
    302b:	31 c0                	xor    %eax,%eax
    302d:	4c 89 45 08          	mov    %r8,0x8(%rbp)
    3031:	e8 1a f4 ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    3036:	48 8d 43 18          	lea    0x18(%rbx),%rax
    303a:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    303f:	e9 22 f8 ff ff       	jmp    2866 <main+0x276>
        CPU_SET(curcpu, sendercpu);
    3044:	48 63 44 24 40       	movslq 0x40(%rsp),%rax
    3049:	48 89 c7             	mov    %rax,%rdi
    304c:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    3052:	77 13                	ja     3067 <main+0xa77>
    3054:	48 c1 e8 06          	shr    $0x6,%rax
    3058:	ba 01 00 00 00       	mov    $0x1,%edx
    305d:	89 f9                	mov    %edi,%ecx
    305f:	48 d3 e2             	shl    %cl,%rdx
    3062:	49 09 54 c5 00       	or     %rdx,0x0(%r13,%rax,8)
        curcpu += 2;
    3067:	83 44 24 40 02       	addl   $0x2,0x40(%rsp)
    306c:	e9 48 f8 ff ff       	jmp    28b9 <main+0x2c9>
    3071:	48 8d 3d 01 43 00 00 	lea    0x4301(%rip),%rdi        # 7379 <_IO_stdin_used+0x379>
    3078:	48 89 6c 24 08       	mov    %rbp,0x8(%rsp)
    307d:	48 8b 1c 24          	mov    (%rsp),%rbx
    3081:	31 ed                	xor    %ebp,%ebp
    3083:	e8 68 f2 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3088:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    308d:	4c 8d 6c 24 60       	lea    0x60(%rsp),%r13
    3092:	4c 8d 25 fe 42 00 00 	lea    0x42fe(%rip),%r12        # 7397 <_IO_stdin_used+0x397>
    void * result; 
    pthread_join(thread[x], &result);
    3099:	48 8b 3c eb          	mov    (%rbx,%rbp,8),%rdi
    309d:	4c 89 ee             	mov    %r13,%rsi
    30a0:	e8 4b f4 ff ff       	call   24f0 <pthread_join@plt>
    30a5:	89 ea                	mov    %ebp,%edx
    30a7:	4c 89 e6             	mov    %r12,%rsi
    30aa:	bf 01 00 00 00       	mov    $0x1,%edi
    30af:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    30b1:	48 83 c5 01          	add    $0x1,%rbp
    30b5:	e8 96 f3 ff ff       	call   2450 <__printf_chk@plt>
    30ba:	48 83 fd 06          	cmp    $0x6,%rbp
    30be:	75 d9                	jne    3099 <main+0xaa9>
    30c0:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    30c5:	4d 89 f2             	mov    %r14,%r10
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
    30c8:	45 31 ff             	xor    %r15d,%r15d
  long total = 0;
    30cb:	31 db                	xor    %ebx,%ebx
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    30cd:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  long sents = 0;
    30d5:	45 31 db             	xor    %r11d,%r11d
  long sends = 0;
    30d8:	31 c9                	xor    %ecx,%ecx
    30da:	48 89 dd             	mov    %rbx,%rbp
    30dd:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    30e2:	4d 8d 76 28          	lea    0x28(%r14),%r14
    30e6:	4d 89 fd             	mov    %r15,%r13
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    30e9:	49 bc db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r12
    30f3:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    30f8:	bf 0a 00 00 00       	mov    $0xa,%edi
    30fd:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    3102:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    3106:	48 89 0c 24          	mov    %rcx,(%rsp)
    310a:	e8 c1 f1 ff ff       	call   22d0 <putchar@plt>
    310f:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3114:	bf 01 00 00 00       	mov    $0x1,%edi
    3119:	83 f3 01             	xor    $0x1,%ebx
    311c:	48 8d 35 88 42 00 00 	lea    0x4288(%rip),%rsi        # 73ab <_IO_stdin_used+0x3ab>
    3123:	48 8b 10             	mov    (%rax),%rdx
    3126:	31 c0                	xor    %eax,%eax
    3128:	e8 23 f3 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    312d:	41 8b 56 08          	mov    0x8(%r14),%edx
    3131:	48 8b 0c 24          	mov    (%rsp),%rcx
    3135:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    313a:	85 d2                	test   %edx,%edx
    313c:	0f 8e 17 04 00 00    	jle    3559 <main+0xf69>
    3142:	48 63 f2             	movslq %edx,%rsi
    3145:	49 8b 06             	mov    (%r14),%rax
    long v = 0;
    3148:	31 d2                	xor    %edx,%edx
    314a:	48 c1 e6 09          	shl    $0x9,%rsi
    314e:	48 01 c6             	add    %rax,%rsi
    3151:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      v += thread_data[me].tasks[n].v;
    3158:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    315f:	48 05 00 02 00 00    	add    $0x200,%rax
    3165:	48 39 f0             	cmp    %rsi,%rax
    3168:	75 ee                	jne    3158 <main+0xb68>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    316a:	48 63 c3             	movslq %ebx,%rax
    316d:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3172:	48 f7 d8             	neg    %rax
    3175:	25 b0 00 00 00       	and    $0xb0,%eax
    317a:	48 01 f8             	add    %rdi,%rax
    317d:	48 63 70 30          	movslq 0x30(%rax),%rsi
    3181:	85 f6                	test   %esi,%esi
    3183:	7e 1d                	jle    31a2 <main+0xbb2>
    3185:	48 8b 40 28          	mov    0x28(%rax),%rax
    3189:	48 c1 e6 09          	shl    $0x9,%rsi
    318d:	48 01 c6             	add    %rax,%rsi
      v += thread_data[other].tasks[n].v;
    3190:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3197:	48 05 00 02 00 00    	add    $0x200,%rax
    319d:	48 39 f0             	cmp    %rsi,%rax
    31a0:	75 ee                	jne    3190 <main+0xba0>
    31a2:	48 8d 35 17 42 00 00 	lea    0x4217(%rip),%rsi        # 73c0 <_IO_stdin_used+0x3c0>
    31a9:	bf 01 00 00 00       	mov    $0x1,%edi
    31ae:	31 c0                	xor    %eax,%eax
    31b0:	48 89 0c 24          	mov    %rcx,(%rsp)
    31b4:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    31b9:	e8 92 f2 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    31be:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    31c3:	bf 01 00 00 00       	mov    $0x1,%edi
    31c8:	48 8b 30             	mov    (%rax),%rsi
    31cb:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    31d5:	48 f7 ee             	imul   %rsi
    31d8:	48 c1 fe 3f          	sar    $0x3f,%rsi
    31dc:	31 c0                	xor    %eax,%eax
    31de:	48 d1 fa             	sar    %rdx
    31e1:	48 29 f2             	sub    %rsi,%rdx
    31e4:	48 8d 35 25 44 00 00 	lea    0x4425(%rip),%rsi        # 7610 <_IO_stdin_used+0x610>
    31eb:	e8 60 f2 ff ff       	call   2450 <__printf_chk@plt>
    31f0:	bf 0a 00 00 00       	mov    $0xa,%edi
    31f5:	e8 d6 f0 ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    31fa:	41 8b 56 08          	mov    0x8(%r14),%edx
    31fe:	48 8b 0c 24          	mov    (%rsp),%rcx
    3202:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    3207:	85 d2                	test   %edx,%edx
    3209:	7e 4c                	jle    3257 <main+0xc67>
    320b:	49 8b 06             	mov    (%r14),%rax
    320e:	4c 63 c2             	movslq %edx,%r8
    3211:	49 c1 e0 09          	shl    $0x9,%r8
    3215:	49 01 c0             	add    %rax,%r8
    3218:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3220:	48 8b 90 68 01 00 00 	mov    0x168(%rax),%rdx
      total += thread_data[x].tasks[n].n;
    3227:	48 03 a8 08 01 00 00 	add    0x108(%rax),%rbp
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    322e:	48 05 00 02 00 00    	add    $0x200,%rax
      ingests += thread_data[x].tasks[n].ingest_count;
    3234:	4c 03 a8 60 ff ff ff 	add    -0xa0(%rax),%r13
      sends += thread_data[x].tasks[n].sends;
    323b:	48 03 88 70 ff ff ff 	add    -0x90(%rax),%rcx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3242:	4c 03 5a 10          	add    0x10(%rdx),%r11
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3246:	4c 03 7a 18          	add    0x18(%rdx),%r15
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    324a:	4c 03 5a 30          	add    0x30(%rdx),%r11
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    324e:	4c 03 7a 38          	add    0x38(%rdx),%r15
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3252:	49 39 c0             	cmp    %rax,%r8
    3255:	75 c9                	jne    3220 <main+0xc30>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3257:	31 db                	xor    %ebx,%ebx
    3259:	49 83 7e 68 00       	cmpq   $0x0,0x68(%r14)
    325e:	7e 75                	jle    32d5 <main+0xce5>
    3260:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    3265:	48 89 2c 24          	mov    %rbp,(%rsp)
    3269:	4c 89 f5             	mov    %r14,%rbp
    326c:	4d 89 de             	mov    %r11,%r14
    326f:	90                   	nop
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3270:	48 8b 45 58          	mov    0x58(%rbp),%rax
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
    329b:	49 f7 e4             	mul    %r12
    329e:	8b 49 20             	mov    0x20(%rcx),%ecx
    32a1:	56                   	push   %rsi
    32a2:	31 c0                	xor    %eax,%eax
    32a4:	48 8d 35 85 43 00 00 	lea    0x4385(%rip),%rsi        # 7630 <_IO_stdin_used+0x630>
    32ab:	48 c1 ea 12          	shr    $0x12,%rdx
    32af:	49 89 d1             	mov    %rdx,%r9
    32b2:	ba 02 00 00 00       	mov    $0x2,%edx
    32b7:	e8 94 f1 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    32bc:	41 58                	pop    %r8
    32be:	41 59                	pop    %r9
    32c0:	48 39 5d 68          	cmp    %rbx,0x68(%rbp)
    32c4:	7f aa                	jg     3270 <main+0xc80>
    32c6:	4d 89 f3             	mov    %r14,%r11
    32c9:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    32ce:	49 89 ee             	mov    %rbp,%r14
    32d1:	48 8b 2c 24          	mov    (%rsp),%rbp
      // printf("%ldns per thread\n", (seconds2 / 2));
    }
    // printf("cycles %ld\n", thread_data[x].cycles);

    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    32d5:	45 8b 8e 84 00 00 00 	mov    0x84(%r14),%r9d
    32dc:	45 85 c9             	test   %r9d,%r9d
    32df:	0f 8e 1a 01 00 00    	jle    33ff <main+0xe0f>
    32e5:	48 89 6c 24 28       	mov    %rbp,0x28(%rsp)
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    32ea:	31 d2                	xor    %edx,%edx
    32ec:	4d 8b 46 18          	mov    0x18(%r14),%r8
    32f0:	4c 89 6c 24 40       	mov    %r13,0x40(%rsp)
    32f5:	48 89 d3             	mov    %rdx,%rbx
    32f8:	48 89 4c 24 30       	mov    %rcx,0x30(%rsp)
    32fd:	4c 89 5c 24 50       	mov    %r11,0x50(%rsp)
    3302:	4c 89 7c 24 58       	mov    %r15,0x58(%rsp)
    3307:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3310:	49 8b 14 d8          	mov    (%r8,%rbx,8),%rdx
    3314:	41 89 dd             	mov    %ebx,%r13d
    3317:	4c 8d 3c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r15
    331f:	31 c0                	xor    %eax,%eax
    3321:	8b 0a                	mov    (%rdx),%ecx
    3323:	85 c9                	test   %ecx,%ecx
    3325:	0f 8e ae 00 00 00    	jle    33d9 <main+0xde9>
    332b:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    3330:	48 89 c1             	mov    %rax,%rcx
    3333:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3338:	31 db                	xor    %ebx,%ebx
    333a:	4c 89 f0             	mov    %r14,%rax
    333d:	48 89 cd             	mov    %rcx,%rbp
    3340:	48 89 0c 24          	mov    %rcx,(%rsp)
    3344:	49 89 de             	mov    %rbx,%r14
    3347:	48 c1 e5 08          	shl    $0x8,%rbp
    334b:	48 89 c3             	mov    %rax,%rbx
    334e:	eb 08                	jmp    3358 <main+0xd68>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3350:	48 8b 43 18          	mov    0x18(%rbx),%rax
    3354:	4a 8b 14 38          	mov    (%rax,%r15,1),%rdx
	for (int k = 0 ; k < snapshot_limit ; k++) {
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3358:	48 8b 42 08          	mov    0x8(%rdx),%rax
    335c:	48 83 ec 08          	sub    $0x8,%rsp
    3360:	bf 01 00 00 00       	mov    $0x1,%edi
    3365:	48 8b b4 28 88 00 00 00 	mov    0x88(%rax,%rbp,1),%rsi
    336d:	4c 01 f6             	add    %r14,%rsi
	for (int k = 0 ; k < snapshot_limit ; k++) {
    3370:	49 83 c6 20          	add    $0x20,%r14
	  struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
	  const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
	  const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3374:	48 8b 4e 18          	mov    0x18(%rsi),%rcx
    3378:	48 2b 4e 08          	sub    0x8(%rsi),%rcx
	  printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    337c:	48 89 c8             	mov    %rcx,%rax
	  const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    337f:	4c 8b 46 10          	mov    0x10(%rsi),%r8
    3383:	4c 2b 06             	sub    (%rsi),%r8
    3386:	51                   	push   %rcx
	  printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3387:	49 f7 e4             	mul    %r12
    338a:	48 8d 35 ef 42 00 00 	lea    0x42ef(%rip),%rsi        # 7680 <_IO_stdin_used+0x680>
    3391:	44 89 e9             	mov    %r13d,%ecx
    3394:	31 c0                	xor    %eax,%eax
    3396:	48 c1 ea 12          	shr    $0x12,%rdx
    339a:	49 89 d1             	mov    %rdx,%r9
    339d:	ba 02 00 00 00       	mov    $0x2,%edx
    33a2:	e8 a9 f0 ff ff       	call   2450 <__printf_chk@plt>
	for (int k = 0 ; k < snapshot_limit ; k++) {
    33a7:	5e                   	pop    %rsi
    33a8:	5f                   	pop    %rdi
    33a9:	49 81 fe 40 01 00 00 	cmp    $0x140,%r14
    33b0:	75 9e                	jne    3350 <main+0xd60>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    33b2:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    33b6:	48 8b 0c 24          	mov    (%rsp),%rcx
    33ba:	49 89 de             	mov    %rbx,%r14
    33bd:	4b 8b 14 38          	mov    (%r8,%r15,1),%rdx
    33c1:	48 83 c1 01          	add    $0x1,%rcx
    33c5:	39 0a                	cmp    %ecx,(%rdx)
    33c7:	0f 8f 6b ff ff ff    	jg     3338 <main+0xd48>
    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    33cd:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    33d2:	45 8b 8e 84 00 00 00 	mov    0x84(%r14),%r9d
    33d9:	48 83 c3 01          	add    $0x1,%rbx
    33dd:	41 39 d9             	cmp    %ebx,%r9d
    33e0:	0f 8f 2a ff ff ff    	jg     3310 <main+0xd20>
    33e6:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
    33eb:	4c 8b 6c 24 40       	mov    0x40(%rsp),%r13
    33f0:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    33f5:	4c 8b 5c 24 50       	mov    0x50(%rsp),%r11
    33fa:	4c 8b 7c 24 58       	mov    0x58(%rsp),%r15
  for (int x = 0 ; x < thread_count ; x++) {
    33ff:	8b 44 24 10          	mov    0x10(%rsp),%eax
    3403:	48 83 44 24 18 18    	addq   $0x18,0x18(%rsp)
    3409:	49 81 c6 b0 00 00 00 	add    $0xb0,%r14
    3410:	85 c0                	test   %eax,%eax
    3412:	75 0d                	jne    3421 <main+0xe31>
    3414:	c7 44 24 10 01 00 00 00 	movl   $0x1,0x10(%rsp)
    341c:	e9 d7 fc ff ff       	jmp    30f8 <main+0xb08>
    3421:	48 89 ea             	mov    %rbp,%rdx
    3424:	48 8d 35 a2 3f 00 00 	lea    0x3fa2(%rip),%rsi        # 73cd <_IO_stdin_used+0x3cd>
    342b:	31 c0                	xor    %eax,%eax
    342d:	4c 89 3c 24          	mov    %r15,(%rsp)
    3431:	bf 01 00 00 00       	mov    $0x1,%edi
    3436:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    343b:	48 89 eb             	mov    %rbp,%rbx
    343e:	4d 89 ef             	mov    %r13,%r15
    3441:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3446:	49 c1 ff 3f          	sar    $0x3f,%r15
    344a:	48 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbp
    3454:	e8 f7 ef ff ff       	call   2450 <__printf_chk@plt>
    3459:	bf 0a 00 00 00       	mov    $0xa,%edi
    345e:	e8 6d ee ff ff       	call   22d0 <putchar@plt>
    3463:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3468:	bf 01 00 00 00       	mov    $0x1,%edi
    346d:	48 8d 35 64 42 00 00 	lea    0x4264(%rip),%rsi        # 76d8 <_IO_stdin_used+0x6d8>
    3474:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3478:	31 c0                	xor    %eax,%eax
    347a:	e8 d1 ef ff ff       	call   2450 <__printf_chk@plt>
    347f:	4c 89 e8             	mov    %r13,%rax
    3482:	bf 01 00 00 00       	mov    $0x1,%edi
    3487:	48 8d 35 72 42 00 00 	lea    0x4272(%rip),%rsi        # 7700 <_IO_stdin_used+0x700>
    348e:	48 f7 ed             	imul   %rbp
    3491:	31 c0                	xor    %eax,%eax
    3493:	48 d1 fa             	sar    %rdx
    3496:	4c 29 fa             	sub    %r15,%rdx
    3499:	e8 b2 ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    349e:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    34a3:	bf 01 00 00 00       	mov    $0x1,%edi
    34a8:	48 8d 35 81 42 00 00 	lea    0x4281(%rip),%rsi        # 7730 <_IO_stdin_used+0x730>
    34af:	48 89 c8             	mov    %rcx,%rax
    34b2:	48 c1 f9 3f          	sar    $0x3f,%rcx
    34b6:	48 f7 ed             	imul   %rbp
    34b9:	31 c0                	xor    %eax,%eax
    34bb:	48 d1 fa             	sar    %rdx
    34be:	48 29 ca             	sub    %rcx,%rdx
    34c1:	e8 8a ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    34c6:	48 89 d8             	mov    %rbx,%rax
    34c9:	48 c1 fb 3f          	sar    $0x3f,%rbx
    34cd:	48 8d 35 8c 42 00 00 	lea    0x428c(%rip),%rsi        # 7760 <_IO_stdin_used+0x760>
    34d4:	48 f7 ed             	imul   %rbp
    34d7:	bf 01 00 00 00       	mov    $0x1,%edi
    34dc:	31 c0                	xor    %eax,%eax
    34de:	48 d1 fa             	sar    %rdx
    34e1:	48 29 da             	sub    %rbx,%rdx
    34e4:	e8 67 ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    34e9:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    34ee:	bf 01 00 00 00       	mov    $0x1,%edi
    34f3:	48 8d 35 e7 3e 00 00 	lea    0x3ee7(%rip),%rsi        # 73e1 <_IO_stdin_used+0x3e1>
    34fa:	4c 89 d8             	mov    %r11,%rax
    34fd:	49 c1 fb 3f          	sar    $0x3f,%r11
    3501:	48 f7 ed             	imul   %rbp
    3504:	31 c0                	xor    %eax,%eax
    3506:	48 d1 fa             	sar    %rdx
    3509:	4c 29 da             	sub    %r11,%rdx
    350c:	e8 3f ef ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3511:	4c 8b 0c 24          	mov    (%rsp),%r9
    3515:	bf 01 00 00 00       	mov    $0x1,%edi
    351a:	48 8d 35 d1 3e 00 00 	lea    0x3ed1(%rip),%rsi        # 73f2 <_IO_stdin_used+0x3f2>
    3521:	4c 89 c8             	mov    %r9,%rax
    3524:	49 c1 f9 3f          	sar    $0x3f,%r9
    3528:	48 f7 ed             	imul   %rbp
    352b:	48 d1 fa             	sar    %rdx
    352e:	4c 29 ca             	sub    %r9,%rdx
    3531:	31 c0                	xor    %eax,%eax
    3533:	e8 18 ef ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3538:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    353d:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3546:	75 18                	jne    3560 <main+0xf70>
    3548:	48 83 c4 78          	add    $0x78,%rsp
    354c:	31 c0                	xor    %eax,%eax
    354e:	5b                   	pop    %rbx
    354f:	5d                   	pop    %rbp
    3550:	41 5c                	pop    %r12
    3552:	41 5d                	pop    %r13
    3554:	41 5e                	pop    %r14
    3556:	41 5f                	pop    %r15
    3558:	c3                   	ret
    long v = 0;
    3559:	31 d2                	xor    %edx,%edx
    355b:	e9 0a fc ff ff       	jmp    316a <main+0xb7a>
}
    3560:	e8 cb ed ff ff       	call   2330 <__stack_chk_fail@plt>
    3565:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    356f:	90                   	nop

0000000000003570 <_start>:
    3570:	f3 0f 1e fa          	endbr64
    3574:	31 ed                	xor    %ebp,%ebp
    3576:	49 89 d1             	mov    %rdx,%r9
    3579:	5e                   	pop    %rsi
    357a:	48 89 e2             	mov    %rsp,%rdx
    357d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3581:	50                   	push   %rax
    3582:	54                   	push   %rsp
    3583:	45 31 c0             	xor    %r8d,%r8d
    3586:	31 c9                	xor    %ecx,%ecx
    3588:	48 8d 3d 61 f0 ff ff 	lea    -0xf9f(%rip),%rdi        # 25f0 <main>
    358f:	ff 15 43 6a 00 00    	call   *0x6a43(%rip)        # 9fd8 <__libc_start_main@GLIBC_2.34>
    3595:	f4                   	hlt
    3596:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000035a0 <deregister_tm_clones>:
    35a0:	48 8d 3d 79 6a 00 00 	lea    0x6a79(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    35a7:	48 8d 05 72 6a 00 00 	lea    0x6a72(%rip),%rax        # a020 <stderr@GLIBC_2.2.5>
    35ae:	48 39 f8             	cmp    %rdi,%rax
    35b1:	74 15                	je     35c8 <deregister_tm_clones+0x28>
    35b3:	48 8b 05 26 6a 00 00 	mov    0x6a26(%rip),%rax        # 9fe0 <_ITM_deregisterTMCloneTable@Base>
    35ba:	48 85 c0             	test   %rax,%rax
    35bd:	74 09                	je     35c8 <deregister_tm_clones+0x28>
    35bf:	ff e0                	jmp    *%rax
    35c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    35c8:	c3                   	ret
    35c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000035d0 <register_tm_clones>:
    35d0:	48 8d 3d 49 6a 00 00 	lea    0x6a49(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    35d7:	48 8d 35 42 6a 00 00 	lea    0x6a42(%rip),%rsi        # a020 <stderr@GLIBC_2.2.5>
    35de:	48 29 fe             	sub    %rdi,%rsi
    35e1:	48 89 f0             	mov    %rsi,%rax
    35e4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    35e8:	48 c1 f8 03          	sar    $0x3,%rax
    35ec:	48 01 c6             	add    %rax,%rsi
    35ef:	48 d1 fe             	sar    %rsi
    35f2:	74 14                	je     3608 <register_tm_clones+0x38>
    35f4:	48 8b 05 f5 69 00 00 	mov    0x69f5(%rip),%rax        # 9ff0 <_ITM_registerTMCloneTable@Base>
    35fb:	48 85 c0             	test   %rax,%rax
    35fe:	74 08                	je     3608 <register_tm_clones+0x38>
    3600:	ff e0                	jmp    *%rax
    3602:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3608:	c3                   	ret
    3609:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003610 <__do_global_dtors_aux>:
    3610:	f3 0f 1e fa          	endbr64
    3614:	80 3d 0d 6a 00 00 00 	cmpb   $0x0,0x6a0d(%rip)        # a028 <completed.0>
    361b:	75 2b                	jne    3648 <__do_global_dtors_aux+0x38>
    361d:	55                   	push   %rbp
    361e:	48 83 3d d2 69 00 00 00 	cmpq   $0x0,0x69d2(%rip)        # 9ff8 <__cxa_finalize@GLIBC_2.2.5>
    3626:	48 89 e5             	mov    %rsp,%rbp
    3629:	74 0c                	je     3637 <__do_global_dtors_aux+0x27>
    362b:	48 8b 3d d6 69 00 00 	mov    0x69d6(%rip),%rdi        # a008 <__dso_handle>
    3632:	e8 79 ec ff ff       	call   22b0 <__cxa_finalize@plt>
    3637:	e8 64 ff ff ff       	call   35a0 <deregister_tm_clones>
    363c:	c6 05 e5 69 00 00 01 	movb   $0x1,0x69e5(%rip)        # a028 <completed.0>
    3643:	5d                   	pop    %rbp
    3644:	c3                   	ret
    3645:	0f 1f 00             	nopl   (%rax)
    3648:	c3                   	ret
    3649:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003650 <frame_dummy>:
    3650:	f3 0f 1e fa          	endbr64
    3654:	e9 77 ff ff ff       	jmp    35d0 <register_tm_clones>
    3659:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003660 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3660:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3664:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    366b:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    366f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3677:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    367b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    367f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3686:	48 85 c9             	test   %rcx,%rcx
    3689:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3690:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3694:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3698:	31 c0                	xor    %eax,%eax
    369a:	c3                   	ret
    369b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000036a0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    36a0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    36a4:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    36ab:	85 c9                	test   %ecx,%ecx
    36ad:	7e 4f                	jle    36fe <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    36af:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    36b6:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    36bd:	48 c1 e1 09          	shl    $0x9,%rcx
    36c1:	48 8b 50 10          	mov    0x10(%rax),%rdx
    36c5:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    36c9:	48 8b 70 28          	mov    0x28(%rax),%rsi
    36cd:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    36cf:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    36d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    36d8:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    36e0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    36e8:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    36f3:	48 05 00 02 00 00    	add    $0x200,%rax
    36f9:	48 39 c1             	cmp    %rax,%rcx
    36fc:	75 da                	jne    36d8 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    36fe:	0f ae f8             	sfence
}
    3701:	31 c0                	xor    %eax,%eax
    3703:	c3                   	ret
    3704:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    370f:	90                   	nop

0000000000003710 <external_thread>:
void * external_thread(void *arg) {
    3710:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3714:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    3718:	0f 85 fb 00 00 00    	jne    3819 <external_thread+0x109>
void * external_thread(void *arg) {
    371e:	41 57                	push   %r15
    3720:	49 89 ff             	mov    %rdi,%r15
    3723:	41 56                	push   %r14
    3725:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    3727:	4c 8d 2d d6 38 00 00 	lea    0x38d6(%rip),%r13        # 7004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    372e:	41 54                	push   %r12
    3730:	55                   	push   %rbp
    3731:	53                   	push   %rbx
    3732:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    3736:	8b 8f ac 00 00 00    	mov    0xac(%rdi),%ecx
    373c:	48 8b 7f 40          	mov    0x40(%rdi),%rdi
    3740:	85 c9                	test   %ecx,%ecx
    3742:	7e 6e                	jle    37b2 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3744:	45 31 e4             	xor    %r12d,%r12d
    3747:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3750:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    3758:	31 db                	xor    %ebx,%ebx
    375a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    375e:	48 8b 06             	mov    (%rsi),%rax
    3761:	8b 10                	mov    (%rax),%edx
    3763:	85 d2                	test   %edx,%edx
    3765:	7e 2a                	jle    3791 <external_thread+0x81>
    3767:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    376b:	48 89 dd             	mov    %rbx,%rbp
    376e:	48 c1 e5 08          	shl    $0x8,%rbp
    3772:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    3776:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    377d:	45 85 c0             	test   %r8d,%r8d
    3780:	74 36                	je     37b8 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    3782:	48 83 c3 01          	add    $0x1,%rbx
    3786:	39 da                	cmp    %ebx,%edx
    3788:	7f e1                	jg     376b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    378a:	41 8b 8f ac 00 00 00 	mov    0xac(%r15),%ecx
    3791:	49 83 c4 01          	add    $0x1,%r12
    3795:	44 39 e1             	cmp    %r12d,%ecx
    3798:	7f b6                	jg     3750 <external_thread+0x40>
  while (data->running == 1) {
    379a:	41 83 7f 34 01       	cmpl   $0x1,0x34(%r15)
    379f:	74 9f                	je     3740 <external_thread+0x30>
}
    37a1:	48 83 c4 08          	add    $0x8,%rsp
    37a5:	31 c0                	xor    %eax,%eax
    37a7:	5b                   	pop    %rbx
    37a8:	5d                   	pop    %rbp
    37a9:	41 5c                	pop    %r12
    37ab:	41 5d                	pop    %r13
    37ad:	41 5e                	pop    %r14
    37af:	41 5f                	pop    %r15
    37b1:	c3                   	ret
  while (data->running == 1) {
    37b2:	eb fe                	jmp    37b2 <external_thread+0xa2>
    37b4:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    37b8:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    37bb:	48 8b 06             	mov    (%rsi),%rax
    37be:	48 8b 78 08          	mov    0x8(%rax),%rdi
    37c2:	48 01 ef             	add    %rbp,%rdi
    37c5:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    37cc:	48 c1 e6 05          	shl    $0x5,%rsi
    37d0:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    37d7:	bf 04 00 00 00       	mov    $0x4,%edi
    37dc:	e8 2f eb ff ff       	call   2310 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    37e1:	49 8b 47 40          	mov    0x40(%r15),%rax
    37e5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    37e9:	48 8b 40 08          	mov    0x8(%rax),%rax
    37ed:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    37f8:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    37fb:	49 8b 7f 40          	mov    0x40(%r15),%rdi
    37ff:	48 83 c3 01          	add    $0x1,%rbx
    3803:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    3807:	48 8b 06             	mov    (%rsi),%rax
    380a:	8b 10                	mov    (%rax),%edx
    380c:	39 da                	cmp    %ebx,%edx
    380e:	0f 8f 53 ff ff ff    	jg     3767 <external_thread+0x57>
    3814:	e9 71 ff ff ff       	jmp    378a <external_thread+0x7a>
}
    3819:	31 c0                	xor    %eax,%eax
    381b:	c3                   	ret
    381c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003820 <timer_thread>:
void* timer_thread(void *arg) {
    3820:	f3 0f 1e fa          	endbr64
    3824:	41 57                	push   %r15
    3826:	48 8d 35 e3 37 00 00 	lea    0x37e3(%rip),%rsi        # 7010 <_IO_stdin_used+0x10>
    382d:	49 89 ff             	mov    %rdi,%r15
    3830:	41 56                	push   %r14
    3832:	41 55                	push   %r13
    3834:	41 54                	push   %r12
    3836:	55                   	push   %rbp
    3837:	53                   	push   %rbx
    3838:	48 83 ec 58          	sub    $0x58,%rsp
    383c:	8b 17                	mov    (%rdi),%edx
    383e:	bf 01 00 00 00       	mov    $0x1,%edi
    3843:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    384c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3851:	31 c0                	xor    %eax,%eax
    3853:	e8 f8 eb ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3858:	66 0f 6f 05 20 41 00 00 	movdqa 0x4120(%rip),%xmm0        # 7980 <_IO_stdin_used+0x980>
    3860:	ba 88 13 00 00       	mov    $0x1388,%edx
    3865:	31 c0                	xor    %eax,%eax
    3867:	48 8d 35 b4 37 00 00 	lea    0x37b4(%rip),%rsi        # 7022 <_IO_stdin_used+0x22>
    386e:	bf 01 00 00 00       	mov    $0x1,%edi
    3873:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3878:	e8 d3 eb ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    387d:	45 8b 67 34          	mov    0x34(%r15),%r12d
    3881:	45 85 e4             	test   %r12d,%r12d
    3884:	0f 84 9b 00 00 00    	je     3925 <timer_thread+0x105>
  int n = 0;
    388a:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    388d:	45 31 e4             	xor    %r12d,%r12d
    3890:	49 89 e5             	mov    %rsp,%r13
    y++;
    3893:	31 db                	xor    %ebx,%ebx
    3895:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    389a:	48 89 ef             	mov    %rbp,%rdi
    389d:	4c 89 ee             	mov    %r13,%rsi
    n++;
    38a0:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    38a4:	e8 a7 ea ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    38a9:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    38ad:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    38b2:	85 c0                	test   %eax,%eax
    38b4:	7e 47                	jle    38fd <timer_thread+0xdd>
    38b6:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    38ba:	49 c1 e4 09          	shl    $0x9,%r12
    38be:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    38c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    38c8:	4c 8b 11             	mov    (%rcx),%r10
    38cb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    38cd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    38d1:	99                   	cltd
    38d2:	41 f7 7a 30          	idivl  0x30(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    38d6:	49 8b 72 28          	mov    0x28(%r10),%rsi
    38da:	48 63 d2             	movslq %edx,%rdx
    38dd:	48 c1 e2 09          	shl    $0x9,%rdx
    38e1:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    38ec:	42 c7 84 26 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    38f8:	49 39 c8             	cmp    %rcx,%r8
    38fb:	75 cb                	jne    38c8 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    38fd:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3900:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3904:	41 8b 57 34          	mov    0x34(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3908:	48 8b 00             	mov    (%rax),%rax
    y++;
    390b:	39 78 30             	cmp    %edi,0x30(%rax)
    390e:	0f 4e fb             	cmovle %ebx,%edi
    3911:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3914:	85 d2                	test   %edx,%edx
    3916:	74 0d                	je     3925 <timer_thread+0x105>
    3918:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    391f:	0f 85 75 ff ff ff    	jne    389a <timer_thread+0x7a>
    3925:	48 8d 3d 0c 37 00 00 	lea    0x370c(%rip),%rdi        # 7038 <_IO_stdin_used+0x38>
    392c:	e8 bf e9 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3931:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3935:	85 d2                	test   %edx,%edx
    3937:	7e 6b                	jle    39a4 <timer_thread+0x184>
    for (int y = 0 ; y < data->task_count ; y++) {
    3939:	49 63 47 30          	movslq 0x30(%r15),%rax
    393d:	85 c0                	test   %eax,%eax
    393f:	7e 63                	jle    39a4 <timer_thread+0x184>
    3941:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3945:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3949:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3951:	31 ff                	xor    %edi,%edi
    3953:	48 89 c2             	mov    %rax,%rdx
    3956:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    395a:	48 8b 40 28          	mov    0x28(%rax),%rax
    395e:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3962:	f6 c6 02             	test   $0x2,%dh
    3965:	74 15                	je     397c <timer_thread+0x15c>
    3967:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3971:	48 05 00 02 00 00    	add    $0x200,%rax
    3977:	48 39 c6             	cmp    %rax,%rsi
    397a:	74 1f                	je     399b <timer_thread+0x17b>
      data->threads[x]->tasks[y].sending = 0;
    397c:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3986:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    398c:	c7 80 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3996:	48 39 c6             	cmp    %rax,%rsi
    3999:	75 e1                	jne    397c <timer_thread+0x15c>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    399b:	48 83 c7 08          	add    $0x8,%rdi
    399f:	48 39 f9             	cmp    %rdi,%rcx
    39a2:	75 b2                	jne    3956 <timer_thread+0x136>
  asm volatile ("mfence" ::: "memory");
    39a4:	0f ae f0             	mfence
  struct timespec drain = {
    39a7:	66 0f 6f 05 e1 3f 00 00 	movdqa 0x3fe1(%rip),%xmm0        # 7990 <_IO_stdin_used+0x990>
    39af:	48 8d 2d a7 36 00 00 	lea    0x36a7(%rip),%rbp        # 705d <_IO_stdin_used+0x5d>
    39b6:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    39bb:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    39bf:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    39c4:	85 c0                	test   %eax,%eax
    39c6:	7e 4c                	jle    3a14 <timer_thread+0x1f4>
    39c8:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    39cc:	4d 63 c4             	movslq %r12d,%r8
    39cf:	49 c1 e0 09          	shl    $0x9,%r8
    39d3:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    39d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    39e0:	48 8b 19             	mov    (%rcx),%rbx
    39e3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    39e5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    39e9:	99                   	cltd
    39ea:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    39ed:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    39f1:	48 63 d2             	movslq %edx,%rdx
    39f4:	48 c1 e2 09          	shl    $0x9,%rdx
    39f8:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3a03:	42 c7 84 06 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a0f:	4c 39 c9             	cmp    %r9,%rcx
    3a12:	75 cc                	jne    39e0 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    3a14:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3a17:	49 8b 47 10          	mov    0x10(%r15),%rax
    y++;
    3a1b:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3a1e:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3a21:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3a24:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3a28:	41 8b 7f 20          	mov    0x20(%r15),%edi
    3a2c:	85 ff                	test   %edi,%edi
    3a2e:	0f 8e bc 00 00 00    	jle    3af0 <timer_thread+0x2d0>
    3a34:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    3a37:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3a3d:	0f 1f 00             	nopl   (%rax)
    3a40:	4a 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbx
            all_empty = 0;
    3a48:	45 31 f6             	xor    %r14d,%r14d
    3a4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3a50:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3a54:	4c 89 f0             	mov    %r14,%rax
    3a57:	48 c1 e0 09          	shl    $0x9,%rax
    3a5b:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3a5f:	31 d2                	xor    %edx,%edx
    3a61:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3a68:	eb 16                	jmp    3a80 <timer_thread+0x260>
    3a6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3a70:	4d 85 c0             	test   %r8,%r8
    3a73:	7f 1f                	jg     3a94 <timer_thread+0x274>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3a75:	83 c2 01             	add    $0x1,%edx
    3a78:	48 83 c0 20          	add    $0x20,%rax
    3a7c:	39 fa                	cmp    %edi,%edx
    3a7e:	74 2a                	je     3aaa <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3a80:	48 8b 08             	mov    (%rax),%rcx
    3a83:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3a87:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3a8b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3a8f:	48 85 c9             	test   %rcx,%rcx
    3a92:	7e dc                	jle    3a70 <timer_thread+0x250>
    3a94:	bf 01 00 00 00       	mov    $0x1,%edi
    3a99:	48 89 ee             	mov    %rbp,%rsi
    3a9c:	31 c0                	xor    %eax,%eax
    3a9e:	e8 ad e9 ff ff       	call   2450 <__printf_chk@plt>
            break;
    3aa3:	41 8b 7f 20          	mov    0x20(%r15),%edi
            all_empty = 0;
    3aa7:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3aaa:	49 83 c6 01          	add    $0x1,%r14
    3aae:	44 39 f7             	cmp    %r14d,%edi
    3ab1:	7e 0d                	jle    3ac0 <timer_thread+0x2a0>
    3ab3:	49 8b 47 10          	mov    0x10(%r15),%rax
    3ab7:	eb 97                	jmp    3a50 <timer_thread+0x230>
    3ab9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3ac0:	49 83 c5 01          	add    $0x1,%r13
    3ac4:	44 39 ef             	cmp    %r13d,%edi
    3ac7:	7e 0d                	jle    3ad6 <timer_thread+0x2b6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3ac9:	85 ff                	test   %edi,%edi
    3acb:	7e 09                	jle    3ad6 <timer_thread+0x2b6>
    3acd:	49 8b 47 10          	mov    0x10(%r15),%rax
    3ad1:	e9 6a ff ff ff       	jmp    3a40 <timer_thread+0x220>
    if (all_empty == 1) {
    3ad6:	41 83 f9 01          	cmp    $0x1,%r9d
    3ada:	74 14                	je     3af0 <timer_thread+0x2d0>
      nanosleep(&drain , &drainrem);
    3adc:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3ae1:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3ae6:	e8 65 e8 ff ff       	call   2350 <nanosleep@plt>
    3aeb:	e9 cb fe ff ff       	jmp    39bb <timer_thread+0x19b>
    3af0:	48 8d 3d 5d 35 00 00 	lea    0x355d(%rip),%rdi        # 7054 <_IO_stdin_used+0x54>
    3af7:	e8 f4 e7 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3afc:	41 8b 47 34          	mov    0x34(%r15),%eax
    3b00:	85 c0                	test   %eax,%eax
    3b02:	0f 84 cf 00 00 00    	je     3bd7 <timer_thread+0x3b7>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b08:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3b0c:	85 c9                	test   %ecx,%ecx
    3b0e:	7e 2d                	jle    3b3d <timer_thread+0x31d>
    3b10:	49 8b 47 10          	mov    0x10(%r15),%rax
    3b14:	31 db                	xor    %ebx,%ebx
    3b16:	48 8d 2d 51 35 00 00 	lea    0x3551(%rip),%rbp        # 706e <_IO_stdin_used+0x6e>
    3b1d:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->running = 0;
    3b20:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3b24:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3b28:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3b2f:	0f 84 cf 00 00 00    	je     3c04 <timer_thread+0x3e4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b35:	48 83 c3 01          	add    $0x1,%rbx
    3b39:	39 d9                	cmp    %ebx,%ecx
    3b3b:	7f e3                	jg     3b20 <timer_thread+0x300>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b3d:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3b41:	85 d2                	test   %edx,%edx
    3b43:	7e 7b                	jle    3bc0 <timer_thread+0x3a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3b45:	49 63 47 30          	movslq 0x30(%r15),%rax
    3b49:	85 c0                	test   %eax,%eax
    3b4b:	7e 73                	jle    3bc0 <timer_thread+0x3a0>
    3b4d:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3b51:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3b55:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3b5d:	31 c9                	xor    %ecx,%ecx
    3b5f:	48 89 c6             	mov    %rax,%rsi
    3b62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3b68:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3b6c:	48 8b 40 28          	mov    0x28(%rax),%rax
    3b70:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3b74:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3b7a:	74 1c                	je     3b98 <timer_thread+0x378>
    3b7c:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3b86:	48 05 00 02 00 00    	add    $0x200,%rax
    3b8c:	48 39 d0             	cmp    %rdx,%rax
    3b8f:	74 26                	je     3bb7 <timer_thread+0x397>
    3b91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3b98:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3ba2:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3ba8:	c7 80 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3bb2:	48 39 d0             	cmp    %rdx,%rax
    3bb5:	75 e1                	jne    3b98 <timer_thread+0x378>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bb7:	48 83 c1 08          	add    $0x8,%rcx
    3bbb:	48 39 f9             	cmp    %rdi,%rcx
    3bbe:	75 a8                	jne    3b68 <timer_thread+0x348>
    asm volatile ("mfence" ::: "memory");
    3bc0:	0f ae f0             	mfence
    3bc3:	48 8d 3d b6 34 00 00 	lea    0x34b6(%rip),%rdi        # 7080 <_IO_stdin_used+0x80>
    3bca:	e8 21 e7 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3bcf:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
    3bd7:	48 8d 3d a9 34 00 00 	lea    0x34a9(%rip),%rdi        # 7087 <_IO_stdin_used+0x87>
    3bde:	e8 0d e7 ff ff       	call   22f0 <puts@plt>
}
    3be3:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3be8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3bf1:	75 47                	jne    3c3a <timer_thread+0x41a>
    3bf3:	48 83 c4 58          	add    $0x58,%rsp
    3bf7:	31 c0                	xor    %eax,%eax
    3bf9:	5b                   	pop    %rbx
    3bfa:	5d                   	pop    %rbp
    3bfb:	41 5c                	pop    %r12
    3bfd:	41 5d                	pop    %r13
    3bff:	41 5e                	pop    %r14
    3c01:	41 5f                	pop    %r15
    3c03:	c3                   	ret
    3c04:	48 89 ef             	mov    %rbp,%rdi
    3c07:	e8 e4 e6 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3c0c:	49 8b 47 10          	mov    0x10(%r15),%rax
    3c10:	be 01 00 00 00       	mov    $0x1,%esi
    3c15:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c19:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3c1d:	8b 78 50             	mov    0x50(%rax),%edi
    3c20:	e8 db e7 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c25:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3c29:	39 d9                	cmp    %ebx,%ecx
    3c2b:	0f 8e 0c ff ff ff    	jle    3b3d <timer_thread+0x31d>
    3c31:	49 8b 47 10          	mov    0x10(%r15),%rax
    3c35:	e9 e6 fe ff ff       	jmp    3b20 <timer_thread+0x300>
}
    3c3a:	e8 f1 e6 ff ff       	call   2330 <__stack_chk_fail@plt>
    3c3f:	90                   	nop

0000000000003c40 <strtolower>:
void strtolower(char *str) {
    3c40:	f3 0f 1e fa          	endbr64
    3c44:	55                   	push   %rbp
    3c45:	53                   	push   %rbx
    3c46:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3c4a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3c4e:	84 db                	test   %bl,%bl
    3c50:	74 24                	je     3c76 <strtolower+0x36>
    3c52:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3c55:	e8 b6 e8 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3c5a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c60:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3c63:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3c67:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3c6a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3c6d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3c72:	84 db                	test   %bl,%bl
    3c74:	75 ea                	jne    3c60 <strtolower+0x20>
}
    3c76:	48 83 c4 08          	add    $0x8,%rsp
    3c7a:	5b                   	pop    %rbx
    3c7b:	5d                   	pop    %rbp
    3c7c:	c3                   	ret
    3c7d:	0f 1f 00             	nopl   (%rax)

0000000000003c80 <zh_malloc>:
void *zh_malloc(size_t size) {
    3c80:	f3 0f 1e fa          	endbr64
    3c84:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3c88:	e8 83 e7 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3c8d:	48 85 c0             	test   %rax,%rax
    3c90:	74 05                	je     3c97 <zh_malloc+0x17>
}
    3c92:	48 83 c4 08          	add    $0x8,%rsp
    3c96:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3c97:	48 8b 0d 82 63 00 00 	mov    0x6382(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    3c9e:	ba 28 00 00 00       	mov    $0x28,%edx
    3ca3:	be 01 00 00 00       	mov    $0x1,%esi
    3ca8:	48 8d 3d 59 37 00 00 	lea    0x3759(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    3caf:	e8 0c e8 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    3cb4:	bf 01 00 00 00       	mov    $0x1,%edi
    3cb9:	e8 e2 e7 ff ff       	call   24a0 <exit@plt>
    3cbe:	66 90                	xchg   %ax,%ax

0000000000003cc0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3cc0:	f3 0f 1e fa          	endbr64
    3cc4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    3cc5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3cca:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3ccd:	e8 8e e6 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3cd2:	48 85 c0             	test   %rax,%rax
    3cd5:	74 11                	je     3ce8 <get_filename_ext+0x28>
    3cd7:	48 39 c3             	cmp    %rax,%rbx
    3cda:	74 0c                	je     3ce8 <get_filename_ext+0x28>
    return dot + 1;
    3cdc:	48 83 c0 01          	add    $0x1,%rax
}
    3ce0:	5b                   	pop    %rbx
    3ce1:	c3                   	ret
    3ce2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    3ce8:	48 8d 05 e0 33 00 00 	lea    0x33e0(%rip),%rax        # 70cf <_IO_stdin_used+0xcf>
}
    3cef:	5b                   	pop    %rbx
    3cf0:	c3                   	ret
    3cf1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3cfc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003d00 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3d00:	f3 0f 1e fa          	endbr64
    3d04:	41 55                	push   %r13
    3d06:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3d09:	48 89 fe             	mov    %rdi,%rsi
    3d0c:	41 54                	push   %r12
    3d0e:	55                   	push   %rbp
    3d0f:	48 89 d5             	mov    %rdx,%rbp
    3d12:	ba 00 04 00 00       	mov    $0x400,%edx
    3d17:	53                   	push   %rbx
    3d18:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3d1f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3d28:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3d30:	31 c0                	xor    %eax,%eax
    3d32:	49 89 e4             	mov    %rsp,%r12
    3d35:	4c 89 e7             	mov    %r12,%rdi
    3d38:	e8 f3 e6 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    3d3d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3d42:	84 db                	test   %bl,%bl
    3d44:	74 24                	je     3d6a <send_headers+0x6a>
        *str = (char)tolower(*str);
    3d46:	e8 c5 e7 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3d4b:	48 8b 08             	mov    (%rax),%rcx
    3d4e:	4c 89 e0             	mov    %r12,%rax
    3d51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3d58:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3d5b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3d5f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3d62:	48 0f be 18          	movsbq (%rax),%rbx
    3d66:	84 db                	test   %bl,%bl
    3d68:	75 ee                	jne    3d58 <send_headers+0x58>
    void *buf = malloc(size);
    3d6a:	bf 11 00 00 00       	mov    $0x11,%edi
    3d6f:	e8 9c e6 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3d74:	48 85 c0             	test   %rax,%rax
    3d77:	0f 84 7e 04 00 00    	je     41fb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3d7d:	66 0f 6f 05 1b 3c 00 00 	movdqa 0x3c1b(%rip),%xmm0        # 79a0 <_IO_stdin_used+0x9a0>
    iov[0].iov_base = zh_malloc(slen);
    3d85:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    3d89:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3d8e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3d96:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3d9a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3d9d:	e8 6e e6 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3da2:	48 85 c0             	test   %rax,%rax
    3da5:	0f 84 50 04 00 00    	je     41fb <send_headers+0x4fb>
    3dab:	66 0f 6f 05 fd 3b 00 00 	movdqa 0x3bfd(%rip),%xmm0        # 79b0 <_IO_stdin_used+0x9b0>
    iov[1].iov_base = zh_malloc(slen);
    3db3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    3db7:	4c 89 e7             	mov    %r12,%rdi
    3dba:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3dc4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3dcc:	0f 11 00             	movups %xmm0,(%rax)
    3dcf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3dd3:	be 2e 00 00 00       	mov    $0x2e,%esi
    3dd8:	e8 83 e5 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3ddd:	48 85 c0             	test   %rax,%rax
    3de0:	0f 84 ea 02 00 00    	je     40d0 <send_headers+0x3d0>
    3de6:	4c 39 e0             	cmp    %r12,%rax
    3de9:	0f 84 e1 02 00 00    	je     40d0 <send_headers+0x3d0>
    return dot + 1;
    3def:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3df3:	48 8d 3d a3 32 00 00 	lea    0x32a3(%rip),%rdi        # 709d <_IO_stdin_used+0x9d>
    3dfa:	48 89 de             	mov    %rbx,%rsi
    3dfd:	e8 ae e5 ff ff       	call   23b0 <strcmp@plt>
    3e02:	85 c0                	test   %eax,%eax
    3e04:	75 20                	jne    3e26 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3e06:	66 0f 6f 05 b2 3b 00 00 	movdqa 0x3bb2(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    3e0e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3e16:	66 0f 6f 05 b2 3b 00 00 	movdqa 0x3bb2(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    3e1e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    3e26:	48 89 de             	mov    %rbx,%rsi
    3e29:	48 8d 3d 71 32 00 00 	lea    0x3271(%rip),%rdi        # 70a1 <_IO_stdin_used+0xa1>
    3e30:	e8 7b e5 ff ff       	call   23b0 <strcmp@plt>
    3e35:	85 c0                	test   %eax,%eax
    3e37:	75 20                	jne    3e59 <send_headers+0x159>
    3e39:	66 0f 6f 05 7f 3b 00 00 	movdqa 0x3b7f(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    3e41:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3e49:	66 0f 6f 05 7f 3b 00 00 	movdqa 0x3b7f(%rip),%xmm0        # 79d0 <_IO_stdin_used+0x9d0>
    3e51:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    3e59:	48 89 de             	mov    %rbx,%rsi
    3e5c:	48 8d 3d 43 32 00 00 	lea    0x3243(%rip),%rdi        # 70a6 <_IO_stdin_used+0xa6>
    3e63:	e8 48 e5 ff ff       	call   23b0 <strcmp@plt>
    3e68:	85 c0                	test   %eax,%eax
    3e6a:	0f 84 10 02 00 00    	je     4080 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    3e70:	48 89 de             	mov    %rbx,%rsi
    3e73:	48 8d 3d 30 32 00 00 	lea    0x3230(%rip),%rdi        # 70aa <_IO_stdin_used+0xaa>
    3e7a:	e8 31 e5 ff ff       	call   23b0 <strcmp@plt>
    3e7f:	85 c0                	test   %eax,%eax
    3e81:	0f 84 a9 02 00 00    	je     4130 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    3e87:	48 89 de             	mov    %rbx,%rsi
    3e8a:	48 8d 3d 1d 32 00 00 	lea    0x321d(%rip),%rdi        # 70ae <_IO_stdin_used+0xae>
    3e91:	e8 1a e5 ff ff       	call   23b0 <strcmp@plt>
    3e96:	85 c0                	test   %eax,%eax
    3e98:	0f 84 6a 02 00 00    	je     4108 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    3e9e:	48 89 de             	mov    %rbx,%rsi
    3ea1:	48 8d 3d 49 32 00 00 	lea    0x3249(%rip),%rdi        # 70f1 <_IO_stdin_used+0xf1>
    3ea8:	e8 03 e5 ff ff       	call   23b0 <strcmp@plt>
    3ead:	85 c0                	test   %eax,%eax
    3eaf:	0f 84 2b 02 00 00    	je     40e0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    3eb5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3eb8:	0f 84 52 01 00 00    	je     4010 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    3ebe:	48 89 de             	mov    %rbx,%rsi
    3ec1:	48 8d 3d ea 31 00 00 	lea    0x31ea(%rip),%rdi        # 70b2 <_IO_stdin_used+0xb2>
    3ec8:	e8 e3 e4 ff ff       	call   23b0 <strcmp@plt>
    3ecd:	85 c0                	test   %eax,%eax
    3ecf:	0f 84 ab 02 00 00    	je     4180 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    3ed5:	48 89 de             	mov    %rbx,%rsi
    3ed8:	48 8d 3d d7 31 00 00 	lea    0x31d7(%rip),%rdi        # 70b6 <_IO_stdin_used+0xb6>
    3edf:	e8 cc e4 ff ff       	call   23b0 <strcmp@plt>
    3ee4:	85 c0                	test   %eax,%eax
    3ee6:	0f 84 6c 02 00 00    	je     4158 <send_headers+0x458>
    slen = strlen(send_buffer);
    3eec:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3ef4:	4c 89 e7             	mov    %r12,%rdi
    3ef7:	e8 24 e4 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    3efc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3eff:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3f02:	e8 09 e5 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3f07:	48 85 c0             	test   %rax,%rax
    3f0a:	0f 84 eb 02 00 00    	je     41fb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    3f10:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    3f14:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    3f18:	83 fb 08             	cmp    $0x8,%ebx
    3f1b:	0f 83 3f 01 00 00    	jae    4060 <send_headers+0x360>
    3f21:	f6 c3 04             	test   $0x4,%bl
    3f24:	0f 85 7b 02 00 00    	jne    41a5 <send_headers+0x4a5>
    3f2a:	85 db                	test   %ebx,%ebx
    3f2c:	74 13                	je     3f41 <send_headers+0x241>
    3f2e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3f36:	88 10                	mov    %dl,(%rax)
    3f38:	f6 c3 02             	test   $0x2,%bl
    3f3b:	0f 85 96 02 00 00    	jne    41d7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3f41:	4d 89 e8             	mov    %r13,%r8
    3f44:	48 8d 0d 6f 31 00 00 	lea    0x316f(%rip),%rcx        # 70ba <_IO_stdin_used+0xba>
    3f4b:	4c 89 e7             	mov    %r12,%rdi
    3f4e:	31 c0                	xor    %eax,%eax
    3f50:	ba 00 04 00 00       	mov    $0x400,%edx
    3f55:	be 01 00 00 00       	mov    $0x1,%esi
    3f5a:	e8 c1 e5 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    3f5f:	4c 89 e7             	mov    %r12,%rdi
    3f62:	e8 b9 e3 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    3f67:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3f6a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3f6d:	e8 9e e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3f72:	48 85 c0             	test   %rax,%rax
    3f75:	0f 84 80 02 00 00    	je     41fb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    3f7b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    3f7f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    3f83:	83 fb 08             	cmp    $0x8,%ebx
    3f86:	0f 83 1c 01 00 00    	jae    40a8 <send_headers+0x3a8>
    3f8c:	f6 c3 04             	test   $0x4,%bl
    3f8f:	0f 85 29 02 00 00    	jne    41be <send_headers+0x4be>
    3f95:	85 db                	test   %ebx,%ebx
    3f97:	74 13                	je     3fac <send_headers+0x2ac>
    3f99:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3fa1:	88 10                	mov    %dl,(%rax)
    3fa3:	f6 c3 02             	test   $0x2,%bl
    3fa6:	0f 85 3d 02 00 00    	jne    41e9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3fac:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    3fb1:	bf 02 00 00 00       	mov    $0x2,%edi
    3fb6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    3fbe:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    3fc6:	e8 45 e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3fcb:	48 85 c0             	test   %rax,%rax
    3fce:	0f 84 27 02 00 00    	je     41fb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3fd4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    3fdc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    3fe0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    3fe8:	66 89 10             	mov    %dx,(%rax)
}
    3feb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    3ff3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3ffc:	0f 85 20 02 00 00    	jne    4222 <send_headers+0x522>
    4002:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4009:	5b                   	pop    %rbx
    400a:	5d                   	pop    %rbp
    400b:	41 5c                	pop    %r12
    400d:	41 5d                	pop    %r13
    400f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4010:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4014:	0f 85 a4 fe ff ff    	jne    3ebe <send_headers+0x1be>
    401a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    401e:	0f 85 9a fe ff ff    	jne    3ebe <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4024:	66 0f 6f 05 f4 39 00 00 	movdqa 0x39f4(%rip),%xmm0        # 7a20 <_IO_stdin_used+0xa20>
    402c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4036:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    403e:	66 0f 6f 05 ea 39 00 00 	movdqa 0x39ea(%rip),%xmm0        # 7a30 <_IO_stdin_used+0xa30>
    4046:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    404e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4056:	e9 63 fe ff ff       	jmp    3ebe <send_headers+0x1be>
    405b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4060:	89 da                	mov    %ebx,%edx
    4062:	48 89 c7             	mov    %rax,%rdi
    4065:	4c 89 e6             	mov    %r12,%rsi
    4068:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    406d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4072:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4075:	c1 e9 03             	shr    $0x3,%ecx
    4078:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    407b:	e9 c1 fe ff ff       	jmp    3f41 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4080:	66 0f 6f 05 38 39 00 00 	movdqa 0x3938(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4088:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4090:	66 0f 6f 05 48 39 00 00 	movdqa 0x3948(%rip),%xmm0        # 79e0 <_IO_stdin_used+0x9e0>
    4098:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40a0:	e9 cb fd ff ff       	jmp    3e70 <send_headers+0x170>
    40a5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    40a8:	89 da                	mov    %ebx,%edx
    40aa:	48 89 c7             	mov    %rax,%rdi
    40ad:	4c 89 e6             	mov    %r12,%rsi
    40b0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    40b5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    40ba:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    40bd:	c1 e9 03             	shr    $0x3,%ecx
    40c0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    40c3:	e9 e4 fe ff ff       	jmp    3fac <send_headers+0x2ac>
    40c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    40d0:	48 8d 1d f8 2f 00 00 	lea    0x2ff8(%rip),%rbx        # 70cf <_IO_stdin_used+0xcf>
    40d7:	e9 94 fd ff ff       	jmp    3e70 <send_headers+0x170>
    40dc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40e0:	66 0f 6f 05 18 39 00 00 	movdqa 0x3918(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    40e8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40f0:	66 0f 6f 05 18 39 00 00 	movdqa 0x3918(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    40f8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4100:	e9 b0 fd ff ff       	jmp    3eb5 <send_headers+0x1b5>
    4105:	0f 1f 00             	nopl   (%rax)
    4108:	66 0f 6f 05 f0 38 00 00 	movdqa 0x38f0(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4110:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4118:	66 0f 6f 05 f0 38 00 00 	movdqa 0x38f0(%rip),%xmm0        # 7a10 <_IO_stdin_used+0xa10>
    4120:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4128:	e9 71 fd ff ff       	jmp    3e9e <send_headers+0x19e>
    412d:	0f 1f 00             	nopl   (%rax)
    4130:	66 0f 6f 05 88 38 00 00 	movdqa 0x3888(%rip),%xmm0        # 79c0 <_IO_stdin_used+0x9c0>
    4138:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4140:	66 0f 6f 05 a8 38 00 00 	movdqa 0x38a8(%rip),%xmm0        # 79f0 <_IO_stdin_used+0x9f0>
    4148:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4150:	e9 32 fd ff ff       	jmp    3e87 <send_headers+0x187>
    4155:	0f 1f 00             	nopl   (%rax)
    4158:	66 0f 6f 05 a0 38 00 00 	movdqa 0x38a0(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4160:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4168:	66 0f 6f 05 e0 38 00 00 	movdqa 0x38e0(%rip),%xmm0        # 7a50 <_IO_stdin_used+0xa50>
    4170:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4178:	e9 6f fd ff ff       	jmp    3eec <send_headers+0x1ec>
    417d:	0f 1f 00             	nopl   (%rax)
    4180:	66 0f 6f 05 78 38 00 00 	movdqa 0x3878(%rip),%xmm0        # 7a00 <_IO_stdin_used+0xa00>
    4188:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4190:	66 0f 6f 05 a8 38 00 00 	movdqa 0x38a8(%rip),%xmm0        # 7a40 <_IO_stdin_used+0xa40>
    4198:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    41a0:	e9 30 fd ff ff       	jmp    3ed5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    41a5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    41ac:	89 db                	mov    %ebx,%ebx
    41ae:	89 10                	mov    %edx,(%rax)
    41b0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    41b5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    41b9:	e9 83 fd ff ff       	jmp    3f41 <send_headers+0x241>
    41be:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    41c5:	89 db                	mov    %ebx,%ebx
    41c7:	89 10                	mov    %edx,(%rax)
    41c9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    41ce:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    41d2:	e9 d5 fd ff ff       	jmp    3fac <send_headers+0x2ac>
    41d7:	89 db                	mov    %ebx,%ebx
    41d9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    41df:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    41e4:	e9 58 fd ff ff       	jmp    3f41 <send_headers+0x241>
    41e9:	89 db                	mov    %ebx,%ebx
    41eb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    41f1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    41f6:	e9 b1 fd ff ff       	jmp    3fac <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    41fb:	48 8b 0d 1e 5e 00 00 	mov    0x5e1e(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4202:	ba 28 00 00 00       	mov    $0x28,%edx
    4207:	be 01 00 00 00       	mov    $0x1,%esi
    420c:	48 8d 3d f5 31 00 00 	lea    0x31f5(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    4213:	e8 a8 e2 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4218:	bf 01 00 00 00       	mov    $0x1,%edi
    421d:	e8 7e e2 ff ff       	call   24a0 <exit@plt>
}
    4222:	e8 09 e1 ff ff       	call   2330 <__stack_chk_fail@plt>
    4227:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004230 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4230:	f3 0f 1e fa          	endbr64
    4234:	41 55                	push   %r13
    4236:	49 89 d5             	mov    %rdx,%r13
    4239:	41 54                	push   %r12
    423b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    423e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4241:	55                   	push   %rbp
    4242:	53                   	push   %rbx
    4243:	48 89 f3             	mov    %rsi,%rbx
    4246:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    424a:	e8 c1 e1 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    424f:	48 85 c0             	test   %rax,%rax
    4252:	74 6b                	je     42bf <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4254:	4c 89 e7             	mov    %r12,%rdi
    4257:	48 89 c5             	mov    %rax,%rbp
    425a:	31 f6                	xor    %esi,%esi
    425c:	31 c0                	xor    %eax,%eax
    425e:	e8 1d e2 ff ff       	call   2480 <open@plt>
    4263:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4266:	85 c0                	test   %eax,%eax
    4268:	0f 88 e8 e2 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    426e:	48 89 da             	mov    %rbx,%rdx
    4271:	48 89 ee             	mov    %rbp,%rsi
    4274:	89 c7                	mov    %eax,%edi
    4276:	e8 15 e1 ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    427b:	48 98                	cltq
    427d:	48 39 d8             	cmp    %rbx,%rax
    4280:	7c 1e                	jl     42a0 <copy_file_contents+0x70>
    close(fd);
    4282:	44 89 e7             	mov    %r12d,%edi
    4285:	e8 e6 e0 ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    428a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    428e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4292:	48 83 c4 08          	add    $0x8,%rsp
    4296:	5b                   	pop    %rbx
    4297:	5d                   	pop    %rbp
    4298:	41 5c                	pop    %r12
    429a:	41 5d                	pop    %r13
    429c:	c3                   	ret
    429d:	0f 1f 00             	nopl   (%rax)
    42a0:	48 8b 0d 79 5d 00 00 	mov    0x5d79(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    42a7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    42ac:	be 01 00 00 00       	mov    $0x1,%esi
    42b1:	48 8d 3d 18 2e 00 00 	lea    0x2e18(%rip),%rdi        # 70d0 <_IO_stdin_used+0xd0>
    42b8:	e8 03 e2 ff ff       	call   24c0 <fwrite@plt>
    42bd:	eb c3                	jmp    4282 <copy_file_contents+0x52>
    42bf:	48 8b 0d 5a 5d 00 00 	mov    0x5d5a(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    42c6:	ba 28 00 00 00       	mov    $0x28,%edx
    42cb:	be 01 00 00 00       	mov    $0x1,%esi
    42d0:	48 8d 3d 31 31 00 00 	lea    0x3131(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    42d7:	e8 e4 e1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    42dc:	bf 01 00 00 00       	mov    $0x1,%edi
    42e1:	e8 ba e1 ff ff       	call   24a0 <exit@plt>
    42e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000042f0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    42f0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    42f4:	8b 46 44             	mov    0x44(%rsi),%eax
    42f7:	48 89 fa             	mov    %rdi,%rdx
    42fa:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    42fd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4303:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4306:	48 8b 07             	mov    (%rdi),%rax
    4309:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    430c:	f6 c1 02             	test   $0x2,%cl
    430f:	74 00                	je     4311 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4311:	89 f0                	mov    %esi,%eax
    4313:	44 29 c0             	sub    %r8d,%eax
    4316:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4319:	0f 82 43 e2 ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    431f:	c1 e9 0a             	shr    $0xa,%ecx
    4322:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4326:	8b 47 44             	mov    0x44(%rdi),%eax
    4329:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    432c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    432f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4332:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4335:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4339:	d3 e0                	shl    %cl,%eax
    433b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    433e:	48 c1 e0 06          	shl    $0x6,%rax
    4342:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4346:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    434c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    434f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4353:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4359:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4361:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4365:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4368:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    436f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4377:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    437b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    437f:	e8 bc df ff ff       	call   2340 <io_uring_submit@plt>
}
    4384:	31 c0                	xor    %eax,%eax
    4386:	48 83 c4 08          	add    $0x8,%rsp
    438a:	c3                   	ret
    438b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004390 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4390:	f3 0f 1e fa          	endbr64
    4394:	41 55                	push   %r13
    4396:	41 89 fd             	mov    %edi,%r13d
    4399:	41 54                	push   %r12
    439b:	55                   	push   %rbp
    439c:	53                   	push   %rbx
    439d:	48 89 f3             	mov    %rsi,%rbx
    43a0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    43a4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    43a7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    43ad:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    43b0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    43b3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    43b5:	f6 c1 02             	test   $0x2,%cl
    43b8:	74 00                	je     43ba <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    43ba:	89 c2                	mov    %eax,%edx
    43bc:	29 f2                	sub    %esi,%edx
    43be:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    43c1:	0f 82 ab e1 ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    43c7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    43ca:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    43cd:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    43d0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    43d5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    43d8:	23 6b 58             	and    0x58(%rbx),%ebp
    43db:	d3 e5                	shl    %cl,%ebp
    43dd:	48 c1 e5 06          	shl    $0x6,%rbp
    43e1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    43e5:	e8 26 e0 ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    43ea:	be 01 00 00 00       	mov    $0x1,%esi
    43ef:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    43f4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    43f7:	e8 a4 df ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    43fc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4401:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4405:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4408:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    440d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4412:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    441b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4423:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4427:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    442b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4432:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    443a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    443e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4446:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    444e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4452:	e8 e9 de ff ff       	call   2340 <io_uring_submit@plt>
}
    4457:	48 83 c4 08          	add    $0x8,%rsp
    445b:	31 c0                	xor    %eax,%eax
    445d:	5b                   	pop    %rbx
    445e:	5d                   	pop    %rbp
    445f:	41 5c                	pop    %r12
    4461:	41 5d                	pop    %r13
    4463:	c3                   	ret
    4464:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    446f:	90                   	nop

0000000000004470 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4470:	f3 0f 1e fa          	endbr64
    4474:	41 56                	push   %r14
    4476:	41 89 f6             	mov    %esi,%r14d
    4479:	41 55                	push   %r13
    447b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    447e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4483:	41 54                	push   %r12
    4485:	55                   	push   %rbp
    4486:	48 89 d5             	mov    %rdx,%rbp
    4489:	53                   	push   %rbx
    void *buf = malloc(size);
    448a:	e8 81 df ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    448f:	48 85 c0             	test   %rax,%rax
    4492:	0f 84 dd 00 00 00    	je     4575 <_send_static_string_content+0x105>
    4498:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    449b:	4c 89 ef             	mov    %r13,%rdi
    449e:	e8 7d de ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    44a3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    44aa:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    44ae:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    44b1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    44b4:	e8 57 df ff ff       	call   2410 <malloc@plt>
    44b9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    44bc:	48 85 c0             	test   %rax,%rax
    44bf:	0f 84 b0 00 00 00    	je     4575 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    44c5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    44c9:	4c 89 e2             	mov    %r12,%rdx
    44cc:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    44cf:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    44d3:	e8 08 df ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    44d8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    44db:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    44e1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    44e4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    44e8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    44ea:	f6 c1 02             	test   $0x2,%cl
    44ed:	0f 85 7d 00 00 00    	jne    4570 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    44f3:	89 d0                	mov    %edx,%eax
    44f5:	29 f0                	sub    %esi,%eax
    44f7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    44fa:	0f 82 7c e0 ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4500:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4503:	8b 45 44             	mov    0x44(%rbp),%eax
    4506:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4509:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    450c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    450f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4512:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4518:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    451c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    451e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4521:	48 89 ef             	mov    %rbp,%rdi
    4524:	48 c1 e0 06          	shl    $0x6,%rax
    4528:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    452c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    452f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4533:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4539:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4541:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4545:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4548:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    454f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4557:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    455b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    455f:	5b                   	pop    %rbx
    4560:	5d                   	pop    %rbp
    4561:	41 5c                	pop    %r12
    4563:	41 5d                	pop    %r13
    4565:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4567:	e9 d4 dd ff ff       	jmp    2340 <io_uring_submit@plt>
    456c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4570:	e9 7e ff ff ff       	jmp    44f3 <_send_static_string_content+0x83>
    4575:	48 8b 0d a4 5a 00 00 	mov    0x5aa4(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    457c:	ba 28 00 00 00       	mov    $0x28,%edx
    4581:	be 01 00 00 00       	mov    $0x1,%esi
    4586:	48 8d 3d 7b 2e 00 00 	lea    0x2e7b(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    458d:	e8 2e df ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4592:	bf 01 00 00 00       	mov    $0x1,%edi
    4597:	e8 04 df ff ff       	call   24a0 <exit@plt>
    459c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000045a0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    45a0:	f3 0f 1e fa          	endbr64
    45a4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    45a7:	89 fe                	mov    %edi,%esi
    45a9:	48 8b 3d 68 5a 00 00 	mov    0x5a68(%rip),%rdi        # a018 <unimplemented_content>
    45b0:	e9 bb fe ff ff       	jmp    4470 <_send_static_string_content>
    45b5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000045c0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    45c0:	f3 0f 1e fa          	endbr64
    45c4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    45c7:	89 fe                	mov    %edi,%esi
    45c9:	48 8b 3d 40 5a 00 00 	mov    0x5a40(%rip),%rdi        # a010 <http_404_content>
    45d0:	e9 9b fe ff ff       	jmp    4470 <_send_static_string_content>
    45d5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000045e0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    45e0:	f3 0f 1e fa          	endbr64
    45e4:	41 56                	push   %r14
    45e6:	41 55                	push   %r13
    45e8:	49 89 d5             	mov    %rdx,%r13
    45eb:	41 54                	push   %r12
    45ed:	41 89 f4             	mov    %esi,%r12d
    45f0:	55                   	push   %rbp
    45f1:	48 89 fd             	mov    %rdi,%rbp
    45f4:	53                   	push   %rbx
    45f5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    45fc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4605:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    460d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    460f:	e8 0c dd ff ff       	call   2320 <strlen@plt>
    4614:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4619:	48 89 c3             	mov    %rax,%rbx
    461c:	0f 84 b6 00 00 00    	je     46d8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4622:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4627:	48 89 ee             	mov    %rbp,%rsi
    462a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    462e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4633:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    463b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4643:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    464e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4656:	e8 65 dd ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    465b:	48 89 e6             	mov    %rsp,%rsi
    465e:	4c 89 f7             	mov    %r14,%rdi
    4661:	e8 6a dd ff ff       	call   23d0 <stat@plt>
    4666:	83 f8 ff             	cmp    $0xffffffff,%eax
    4669:	0f 84 d3 00 00 00    	je     4742 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    466f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4673:	25 00 f0 00 00       	and    $0xf000,%eax
    4678:	3d 00 80 00 00       	cmp    $0x8000,%eax
    467d:	0f 84 f5 00 00 00    	je     4778 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4683:	48 8b 3d 86 59 00 00 	mov    0x5986(%rip),%rdi        # a010 <http_404_content>
    468a:	4c 89 ea             	mov    %r13,%rdx
    468d:	44 89 e6             	mov    %r12d,%esi
    4690:	e8 db fd ff ff       	call   4470 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4695:	4c 89 f2             	mov    %r14,%rdx
    4698:	bf 01 00 00 00       	mov    $0x1,%edi
    469d:	31 c0                	xor    %eax,%eax
    469f:	48 8d 35 7a 2a 00 00 	lea    0x2a7a(%rip),%rsi        # 7120 <_IO_stdin_used+0x120>
    46a6:	e8 a5 dd ff ff       	call   2450 <__printf_chk@plt>
}
    46ab:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    46b3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    46bc:	0f 85 20 01 00 00    	jne    47e2 <handle_get_method+0x202>
    46c2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    46c9:	5b                   	pop    %rbx
    46ca:	5d                   	pop    %rbp
    46cb:	41 5c                	pop    %r12
    46cd:	41 5d                	pop    %r13
    46cf:	41 5e                	pop    %r14
    46d1:	c3                   	ret
    46d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    46d8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    46dd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    46e5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    46ea:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    46ed:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    46f5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    46f8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4700:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    470b:	e8 b0 dc ff ff       	call   23c0 <__memcpy_chk@plt>
    4710:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4715:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    471a:	48 8d 35 ca 29 00 00 	lea    0x29ca(%rip),%rsi        # 70eb <_IO_stdin_used+0xeb>
    4721:	48 29 d9             	sub    %rbx,%rcx
    4724:	ba 0b 00 00 00       	mov    $0xb,%edx
    4729:	e8 92 dc ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    472e:	48 89 e6             	mov    %rsp,%rsi
    4731:	4c 89 f7             	mov    %r14,%rdi
    4734:	e8 97 dc ff ff       	call   23d0 <stat@plt>
    4739:	83 f8 ff             	cmp    $0xffffffff,%eax
    473c:	0f 85 2d ff ff ff    	jne    466f <handle_get_method+0x8f>
    4742:	4c 89 f2             	mov    %r14,%rdx
    4745:	48 89 e9             	mov    %rbp,%rcx
    4748:	48 8d 35 a7 29 00 00 	lea    0x29a7(%rip),%rsi        # 70f6 <_IO_stdin_used+0xf6>
    474f:	31 c0                	xor    %eax,%eax
    4751:	bf 01 00 00 00       	mov    $0x1,%edi
    4756:	e8 f5 dc ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    475b:	48 8b 3d ae 58 00 00 	mov    0x58ae(%rip),%rdi        # a010 <http_404_content>
    4762:	4c 89 ea             	mov    %r13,%rdx
    4765:	44 89 e6             	mov    %r12d,%esi
    4768:	e8 03 fd ff ff       	call   4470 <_send_static_string_content>
}
    476d:	e9 39 ff ff ff       	jmp    46ab <handle_get_method+0xcb>
    4772:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4778:	bf 70 00 00 00       	mov    $0x70,%edi
    477d:	e8 8e dc ff ff       	call   2410 <malloc@plt>
    4782:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4785:	48 85 c0             	test   %rax,%rax
    4788:	74 5d                	je     47e7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    478a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    478e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4793:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4797:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    479a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    47a1:	e8 5a f5 ff ff       	call   3d00 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    47a6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    47ab:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    47af:	4c 89 f7             	mov    %r14,%rdi
    47b2:	e8 79 fa ff ff       	call   4230 <copy_file_contents>
    47b7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    47bc:	4c 89 f2             	mov    %r14,%rdx
    47bf:	31 c0                	xor    %eax,%eax
    47c1:	48 8d 35 46 29 00 00 	lea    0x2946(%rip),%rsi        # 710e <_IO_stdin_used+0x10e>
    47c8:	bf 01 00 00 00       	mov    $0x1,%edi
    47cd:	e8 7e dc ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    47d2:	4c 89 ee             	mov    %r13,%rsi
    47d5:	48 89 df             	mov    %rbx,%rdi
    47d8:	e8 13 fb ff ff       	call   42f0 <add_write_request>
    47dd:	e9 c9 fe ff ff       	jmp    46ab <handle_get_method+0xcb>
}
    47e2:	e8 49 db ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    47e7:	48 8b 0d 32 58 00 00 	mov    0x5832(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    47ee:	ba 28 00 00 00       	mov    $0x28,%edx
    47f3:	be 01 00 00 00       	mov    $0x1,%esi
    47f8:	48 8d 3d 09 2c 00 00 	lea    0x2c09(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    47ff:	e8 bc dc ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4804:	bf 01 00 00 00       	mov    $0x1,%edi
    4809:	e8 92 dc ff ff       	call   24a0 <exit@plt>
    480e:	66 90                	xchg   %ax,%ax

0000000000004810 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4810:	f3 0f 1e fa          	endbr64
    4814:	41 57                	push   %r15
    4816:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4818:	4c 8d 35 66 28 00 00 	lea    0x2866(%rip),%r14        # 7085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    481f:	41 55                	push   %r13
    4821:	49 89 d5             	mov    %rdx,%r13
    4824:	41 54                	push   %r12
    4826:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4829:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    482c:	55                   	push   %rbp
    482d:	53                   	push   %rbx
    482e:	48 83 ec 18          	sub    $0x18,%rsp
    4832:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    483b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4840:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4842:	49 89 e7             	mov    %rsp,%r15
    4845:	4c 89 fa             	mov    %r15,%rdx
    4848:	e8 33 db ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    484d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4851:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4854:	84 db                	test   %bl,%bl
    4856:	74 1d                	je     4875 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4858:	e8 b3 dc ff ff       	call   2510 <__ctype_tolower_loc@plt>
    485d:	48 89 ea             	mov    %rbp,%rdx
    4860:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4863:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4867:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    486a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    486d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4871:	84 db                	test   %bl,%bl
    4873:	75 eb                	jne    4860 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4875:	4c 89 fa             	mov    %r15,%rdx
    4878:	4c 89 f6             	mov    %r14,%rsi
    487b:	31 ff                	xor    %edi,%edi
    487d:	e8 fe da ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4882:	48 8d 35 aa 28 00 00 	lea    0x28aa(%rip),%rsi        # 7133 <_IO_stdin_used+0x133>
    4889:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    488c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    488f:	e8 1c db ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4894:	4c 89 ea             	mov    %r13,%rdx
    4897:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    489a:	85 c0                	test   %eax,%eax
    489c:	75 2a                	jne    48c8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    489e:	48 89 df             	mov    %rbx,%rdi
    48a1:	e8 3a fd ff ff       	call   45e0 <handle_get_method>
}
    48a6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    48ab:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    48b4:	75 20                	jne    48d6 <handle_http_method+0xc6>
    48b6:	48 83 c4 18          	add    $0x18,%rsp
    48ba:	5b                   	pop    %rbx
    48bb:	5d                   	pop    %rbp
    48bc:	41 5c                	pop    %r12
    48be:	41 5d                	pop    %r13
    48c0:	41 5e                	pop    %r14
    48c2:	41 5f                	pop    %r15
    48c4:	c3                   	ret
    48c5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    48c8:	48 8b 3d 49 57 00 00 	mov    0x5749(%rip),%rdi        # a018 <unimplemented_content>
    48cf:	e8 9c fb ff ff       	call   4470 <_send_static_string_content>
}
    48d4:	eb d0                	jmp    48a6 <handle_http_method+0x96>
    48d6:	e8 55 da ff ff       	call   2330 <__stack_chk_fail@plt>
    48db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000048e0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    48e0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    48e4:	85 d2                	test   %edx,%edx
    48e6:	7e 38                	jle    4920 <get_line+0x40>
    48e8:	48 63 d2             	movslq %edx,%rdx
    48eb:	48 83 c7 01          	add    $0x1,%rdi
    48ef:	48 01 f2             	add    %rsi,%rdx
    48f2:	eb 11                	jmp    4905 <get_line+0x25>
    48f4:	0f 1f 40 00          	nopl   0x0(%rax)
    48f8:	48 83 c6 01          	add    $0x1,%rsi
    48fc:	48 83 c7 01          	add    $0x1,%rdi
    4900:	48 39 d6             	cmp    %rdx,%rsi
    4903:	74 1b                	je     4920 <get_line+0x40>
        dest[i] = src[i];
    4905:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4909:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    490b:	3c 0d                	cmp    $0xd,%al
    490d:	75 e9                	jne    48f8 <get_line+0x18>
    490f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4912:	75 e4                	jne    48f8 <get_line+0x18>
            dest[i] = '\0';
    4914:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4917:	31 c0                	xor    %eax,%eax
    4919:	c3                   	ret
    491a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4920:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4925:	c3                   	ret
    4926:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004930 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4930:	f3 0f 1e fa          	endbr64
    4934:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    493b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    493f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4948:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4950:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4952:	49 89 e2             	mov    %rsp,%r10
    4955:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    495d:	4c 89 d0             	mov    %r10,%rax
    4960:	eb 13                	jmp    4975 <handle_client_request+0x45>
    4962:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4968:	48 83 c0 01          	add    $0x1,%rax
    496c:	48 83 c1 01          	add    $0x1,%rcx
    4970:	4c 39 c8             	cmp    %r9,%rax
    4973:	74 4b                	je     49c0 <handle_client_request+0x90>
        dest[i] = src[i];
    4975:	44 0f b6 01          	movzbl (%rcx),%r8d
    4979:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    497c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4980:	75 e6                	jne    4968 <handle_client_request+0x38>
    4982:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4986:	75 e0                	jne    4968 <handle_client_request+0x38>
            dest[i] = '\0';
    4988:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    498b:	8b 47 08             	mov    0x8(%rdi),%eax
    498e:	48 89 f2             	mov    %rsi,%rdx
    4991:	4c 89 d7             	mov    %r10,%rdi
    4994:	89 c6                	mov    %eax,%esi
    4996:	e8 75 fe ff ff       	call   4810 <handle_http_method>
}
    499b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    49a3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    49ac:	75 39                	jne    49e7 <handle_client_request+0xb7>
    49ae:	31 c0                	xor    %eax,%eax
    49b0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    49b7:	c3                   	ret
    49b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    49c0:	48 8b 0d 59 56 00 00 	mov    0x5659(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    49c7:	ba 12 00 00 00       	mov    $0x12,%edx
    49cc:	be 01 00 00 00       	mov    $0x1,%esi
    49d1:	48 8d 3d 5f 27 00 00 	lea    0x275f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    49d8:	e8 e3 da ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    49dd:	bf 01 00 00 00       	mov    $0x1,%edi
    49e2:	e8 b9 da ff ff       	call   24a0 <exit@plt>
}
    49e7:	e8 44 d9 ff ff       	call   2330 <__stack_chk_fail@plt>
    49ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000049f0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    49f0:	f3 0f 1e fa          	endbr64
    49f4:	55                   	push   %rbp
    49f5:	53                   	push   %rbx
    49f6:	48 89 cb             	mov    %rcx,%rbx
    49f9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    49fd:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4a00:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4a03:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4a09:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4a0c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4a0f:	f6 c1 02             	test   $0x2,%cl
    4a12:	74 00                	je     4a14 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4a14:	41 89 c0             	mov    %eax,%r8d
    4a17:	45 29 c8             	sub    %r9d,%r8d
    4a1a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4a1e:	0f 82 68 db ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4a24:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4a27:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4a2a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4a2d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4a30:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4a33:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4a37:	d3 e5                	shl    %cl,%ebp
    4a39:	48 c1 e5 06          	shl    $0x6,%rbp
    4a3d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4a41:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4a44:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4a49:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4a50:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4a54:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4a58:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4a60:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4a68:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4a6c:	e8 9f d9 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4a71:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4a74:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4a7a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4a7e:	48 83 c4 08          	add    $0x8,%rsp
    4a82:	5b                   	pop    %rbx
    4a83:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4a84:	e9 b7 d8 ff ff       	jmp    2340 <io_uring_submit@plt>
    4a89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004a90 <io_thread>:
void* io_thread(void *arg) {
    4a90:	f3 0f 1e fa          	endbr64
    4a94:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4a96:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4a98:	41 56                	push   %r14
    4a9a:	41 55                	push   %r13
    4a9c:	41 54                	push   %r12
    4a9e:	55                   	push   %rbp
    4a9f:	48 89 fd             	mov    %rdi,%rbp
    4aa2:	53                   	push   %rbx
    4aa3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4aaa:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4ab3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4abb:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4abf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4ac4:	bf 00 01 00 00       	mov    $0x100,%edi
    4ac9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4acc:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4ad0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4ad5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4ada:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4adf:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4ae4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4aec:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4af1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4af9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4afe:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4b06:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4b0b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4b13:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4b18:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4b20:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4b25:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4b2d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4b35:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4b3d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4b45:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4b4d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4b55:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4b5d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4b65:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4b6d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4b75:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4b7d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4b84:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4b8c:	e8 5f d8 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4b91:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
    4b95:	31 f6                	xor    %esi,%esi
    4b97:	e8 44 d9 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4b9c:	31 d2                	xor    %edx,%edx
    4b9e:	be 01 00 00 00       	mov    $0x1,%esi
    4ba3:	bf 02 00 00 00       	mov    $0x2,%edi
    4ba8:	e8 83 d9 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4bad:	83 f8 ff             	cmp    $0xffffffff,%eax
    4bb0:	0f 84 18 da ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    4bb6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4bbb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4bc1:	89 c7                	mov    %eax,%edi
    4bc3:	41 89 c4             	mov    %eax,%r12d
    4bc6:	ba 02 00 00 00       	mov    $0x2,%edx
    4bcb:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4bd0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4bd8:	e8 23 d7 ff ff       	call   2300 <setsockopt@plt>
    4bdd:	85 c0                	test   %eax,%eax
    4bdf:	0f 88 bd d9 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4be5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4bea:	ba 10 00 00 00       	mov    $0x10,%edx
    4bef:	44 89 e7             	mov    %r12d,%edi
    4bf2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4bfb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4c03:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4c0b:	e8 50 d8 ff ff       	call   2460 <bind@plt>
    4c10:	85 c0                	test   %eax,%eax
    4c12:	0f 88 c2 d9 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4c18:	be 0a 00 00 00       	mov    $0xa,%esi
    4c1d:	44 89 e7             	mov    %r12d,%edi
    4c20:	e8 fb d7 ff ff       	call   2420 <listen@plt>
    4c25:	85 c0                	test   %eax,%eax
    4c27:	0f 88 81 d9 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4c2d:	ba db 18 00 00       	mov    $0x18db,%edx
    4c32:	48 8d 35 43 25 00 00 	lea    0x2543(%rip),%rsi        # 717c <_IO_stdin_used+0x17c>
    4c39:	bf 01 00 00 00       	mov    $0x1,%edi
    4c3e:	31 c0                	xor    %eax,%eax
    4c40:	e8 0b d8 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4c45:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4c4a:	48 89 d9             	mov    %rbx,%rcx
    4c4d:	44 89 e7             	mov    %r12d,%edi
    4c50:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4c55:	48 89 c6             	mov    %rax,%rsi
    4c58:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4c5d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4c62:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4c6a:	e8 81 fd ff ff       	call   49f0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4c6f:	bf 01 00 00 00       	mov    $0x1,%edi
    4c74:	be 10 00 00 00       	mov    $0x10,%esi
    4c79:	e8 22 d7 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    4c7e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4c83:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4c86:	e8 85 d7 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4c8b:	48 85 c0             	test   %rax,%rax
    4c8e:	0f 84 ae 04 00 00    	je     5142 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    4c94:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4c98:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4c9f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    4ca6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4cae:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4cb1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4cb6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4cb8:	f6 c1 02             	test   $0x2,%cl
    4cbb:	0f 85 0f 04 00 00    	jne    50d0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    4cc1:	89 d0                	mov    %edx,%eax
    4cc3:	29 f0                	sub    %esi,%eax
    4cc5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4ccc:	0f 82 f2 d8 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4cd2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4cd5:	48 8d 75 50          	lea    0x50(%rbp),%rsi
	sqe->addr3 = 0;
    4cd9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4cdd:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ce0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4ce7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4cea:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4cf1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4cf8:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4cfa:	8b 55 50             	mov    0x50(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4cfd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4d02:	48 c1 e0 06          	shl    $0x6,%rax
    4d06:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4d0e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4d14:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4d17:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4d1f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4d23:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4d2b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4d33:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4d37:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4d3b:	e8 00 d6 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4d40:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4d44:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4d49:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4d51:	0f 85 d7 01 00 00    	jne    4f2e <io_thread+0x49e>
    4d57:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4d5c:	4d 89 ce             	mov    %r9,%r14
    4d5f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4d64:	0f 1f 40 00          	nopl   0x0(%rax)
    4d68:	48 8d 3d 23 24 00 00 	lea    0x2423(%rip),%rdi        # 7192 <_IO_stdin_used+0x192>
    4d6f:	e8 7c d5 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4d74:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4d7b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4d82:	c1 e9 0b             	shr    $0xb,%ecx
    4d85:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4d88:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4d90:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4d92:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4d9a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4d9c:	39 d0                	cmp    %edx,%eax
    4d9e:	74 36                	je     4dd6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4da0:	89 f8                	mov    %edi,%eax
    4da2:	21 d0                	and    %edx,%eax
    4da4:	d3 e0                	shl    %cl,%eax
    4da6:	48 c1 e0 04          	shl    $0x4,%rax
    4daa:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4db2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4dba:	0f 85 a8 01 00 00    	jne    4f68 <io_thread+0x4d8>
    4dc0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4dc4:	0f 85 0e 03 00 00    	jne    50d8 <io_thread+0x648>
			if (cqe->res < 0)
    4dca:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4dcd:	83 c2 01             	add    $0x1,%edx
    4dd0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4dd2:	85 c0                	test   %eax,%eax
    4dd4:	79 b2                	jns    4d88 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    4dd6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    4ddf:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4de0:	45 31 c0             	xor    %r8d,%r8d
    4de3:	31 d2                	xor    %edx,%edx
    4de5:	b9 01 00 00 00       	mov    $0x1,%ecx
    4dea:	4c 89 f6             	mov    %r14,%rsi
    4ded:	48 89 df             	mov    %rbx,%rdi
    4df0:	e8 4b d6 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    4df5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    4df8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4dfd:	48 83 38 01          	cmpq   $0x1,(%rax)
    4e01:	0f 84 e1 02 00 00    	je     50e8 <io_thread+0x658>
    4e07:	48 8d 3d aa 23 00 00 	lea    0x23aa(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    4e0e:	e8 dd d4 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4e13:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4e18:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4e1b:	45 85 ff             	test   %r15d,%r15d
    4e1e:	0f 88 72 d7 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    4e24:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    4e27:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    4e2b:	85 c0                	test   %eax,%eax
    4e2d:	0f 88 d5 02 00 00    	js     5108 <io_thread+0x678>
      switch (req->event_type) {
    4e33:	41 83 f8 01          	cmp    $0x1,%r8d
    4e37:	0f 84 7b 01 00 00    	je     4fb8 <io_thread+0x528>
    4e3d:	41 83 f8 02          	cmp    $0x2,%r8d
    4e41:	0f 84 a1 01 00 00    	je     4fe8 <io_thread+0x558>
    4e47:	45 85 c0             	test   %r8d,%r8d
    4e4a:	0f 85 50 01 00 00    	jne    4fa0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4e50:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    4e55:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    4e5a:	48 89 d9             	mov    %rbx,%rcx
    4e5d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4e61:	e8 8a fb ff ff       	call   49f0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    4e66:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4e6b:	48 89 de             	mov    %rbx,%rsi
    4e6e:	8b 78 08             	mov    0x8(%rax),%edi
    4e71:	e8 1a f5 ff ff       	call   4390 <add_read_request>
              free(req);
    4e76:	4c 89 e7             	mov    %r12,%rdi
    4e79:	e8 42 d4 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4e7e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    4e83:	48 85 c0             	test   %rax,%rax
    4e86:	0f 85 14 01 00 00    	jne    4fa0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    4e8c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e93:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4e9a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4e9d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4ea2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4ea4:	f6 c1 02             	test   $0x2,%cl
    4ea7:	74 00                	je     4ea9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    4ea9:	89 d0                	mov    %edx,%eax
    4eab:	29 f0                	sub    %esi,%eax
    4ead:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4eb4:	0f 82 00 d7 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    4eba:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    4ebd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    4ec2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    4ec6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ec9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4ed0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ed3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4eda:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ee1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4ee3:	8b 55 50             	mov    0x50(%rbp),%edx
    4ee6:	48 c1 e0 06          	shl    $0x6,%rax
    4eea:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4ef2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4ef8:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4efb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4f03:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4f07:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4f0f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4f17:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4f1b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    4f1f:	e8 1c d4 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4f24:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    4f28:	0f 84 3a fe ff ff    	je     4d68 <io_thread+0x2d8>
    4f2e:	48 8d 3d bc 22 00 00 	lea    0x22bc(%rip),%rdi        # 71f1 <_IO_stdin_used+0x1f1>
    4f35:	e8 b6 d3 ff ff       	call   22f0 <puts@plt>
}
    4f3a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    4f42:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4f4b:	0f 85 18 02 00 00    	jne    5169 <io_thread+0x6d9>
    4f51:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    4f58:	31 c0                	xor    %eax,%eax
    4f5a:	5b                   	pop    %rbx
    4f5b:	5d                   	pop    %rbp
    4f5c:	41 5c                	pop    %r12
    4f5e:	41 5d                	pop    %r13
    4f60:	41 5e                	pop    %r14
    4f62:	41 5f                	pop    %r15
    4f64:	c3                   	ret
    4f65:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    4f68:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    4f6d:	48 85 c0             	test   %rax,%rax
    4f70:	0f 84 6a fe ff ff    	je     4de0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    4f76:	48 83 38 01          	cmpq   $0x1,(%rax)
    4f7a:	0f 84 68 01 00 00    	je     50e8 <io_thread+0x658>
    4f80:	48 8d 3d 31 22 00 00 	lea    0x2231(%rip),%rdi        # 71b8 <_IO_stdin_used+0x1b8>
    4f87:	e8 64 d3 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4f8c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4f91:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4f94:	e9 8b fe ff ff       	jmp    4e24 <io_thread+0x394>
    4f99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4fa0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4fa8:	8b 02                	mov    (%rdx),%eax
    4faa:	83 c0 01             	add    $0x1,%eax
    4fad:	89 02                	mov    %eax,(%rdx)
}
    4faf:	e9 d8 fe ff ff       	jmp    4e8c <io_thread+0x3fc>
    4fb4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    4fb8:	85 c0                	test   %eax,%eax
    4fba:	75 74                	jne    5030 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4fbc:	48 8b 0d 5d 50 00 00 	mov    0x505d(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    4fc3:	ba 0f 00 00 00       	mov    $0xf,%edx
    4fc8:	be 01 00 00 00       	mov    $0x1,%esi
    4fcd:	48 8d 3d 0d 22 00 00 	lea    0x220d(%rip),%rdi        # 71e1 <_IO_stdin_used+0x1e1>
    4fd4:	e8 e7 d4 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    4fd9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4fde:	e9 a0 fe ff ff       	jmp    4e83 <io_thread+0x3f3>
    4fe3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    4fe8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    4fed:	45 31 ff             	xor    %r15d,%r15d
    4ff0:	85 c0                	test   %eax,%eax
    4ff2:	7e 20                	jle    5014 <io_thread+0x584>
    4ff4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    4ff8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    4ffb:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    4fff:	48 c1 e0 04          	shl    $0x4,%rax
    5003:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5008:	e8 b3 d2 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    500d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5012:	7f e4                	jg     4ff8 <io_thread+0x568>
              close(req->client_socket);
    5014:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5019:	e8 52 d3 ff ff       	call   2370 <close@plt>
              free(req);
    501e:	4c 89 e7             	mov    %r12,%rdi
    5021:	e8 9a d2 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5026:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    502b:	e9 53 fe ff ff       	jmp    4e83 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5030:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5035:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    503a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5042:	eb 11                	jmp    5055 <io_thread+0x5c5>
    5044:	0f 1f 40 00          	nopl   0x0(%rax)
    5048:	48 83 c0 01          	add    $0x1,%rax
    504c:	48 83 c2 01          	add    $0x1,%rdx
    5050:	48 39 c6             	cmp    %rax,%rsi
    5053:	74 4b                	je     50a0 <io_thread+0x610>
        dest[i] = src[i];
    5055:	0f b6 0a             	movzbl (%rdx),%ecx
    5058:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    505a:	80 f9 0d             	cmp    $0xd,%cl
    505d:	75 e9                	jne    5048 <io_thread+0x5b8>
    505f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5063:	75 e3                	jne    5048 <io_thread+0x5b8>
            dest[i] = '\0';
    5065:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5068:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    506d:	48 89 da             	mov    %rbx,%rdx
    5070:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5075:	e8 96 f7 ff ff       	call   4810 <handle_http_method>
              free(req->iov[0].iov_base);
    507a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    507f:	e8 3c d2 ff ff       	call   22c0 <free@plt>
              free(req);
    5084:	4c 89 e7             	mov    %r12,%rdi
    5087:	e8 34 d2 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    508c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5091:	e9 ed fd ff ff       	jmp    4e83 <io_thread+0x3f3>
    5096:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    50a0:	48 8b 0d 79 4f 00 00 	mov    0x4f79(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    50a7:	ba 12 00 00 00       	mov    $0x12,%edx
    50ac:	be 01 00 00 00       	mov    $0x1,%esi
    50b1:	48 8d 3d 7f 20 00 00 	lea    0x207f(%rip),%rdi        # 7137 <_IO_stdin_used+0x137>
    50b8:	e8 03 d4 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    50bd:	bf 01 00 00 00       	mov    $0x1,%edi
    50c2:	e8 d9 d3 ff ff       	call   24a0 <exit@plt>
    50c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    50d0:	e9 ec fb ff ff       	jmp    4cc1 <io_thread+0x231>
    50d5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    50d8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    50dd:	e9 94 fe ff ff       	jmp    4f76 <io_thread+0x4e6>
    50e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    50e8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    50f0:	48 8d 3d ad 20 00 00 	lea    0x20ad(%rip),%rdi        # 71a4 <_IO_stdin_used+0x1a4>
    50f7:	8b 02                	mov    (%rdx),%eax
    50f9:	83 c0 01             	add    $0x1,%eax
    50fc:	89 02                	mov    %eax,(%rdx)
    50fe:	e8 ed d1 ff ff       	call   22f0 <puts@plt>
    5103:	e9 26 fe ff ff       	jmp    4f2e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5108:	f7 d8                	neg    %eax
    510a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    510f:	89 c7                	mov    %eax,%edi
    5111:	e8 ea d3 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5116:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    511b:	be 01 00 00 00       	mov    $0x1,%esi
    5120:	48 8b 3d f9 4e 00 00 	mov    0x4ef9(%rip),%rdi        # a020 <stderr@GLIBC_2.2.5>
    5127:	48 89 c1             	mov    %rax,%rcx
    512a:	48 8d 15 07 23 00 00 	lea    0x2307(%rip),%rdx        # 7438 <_IO_stdin_used+0x438>
    5131:	31 c0                	xor    %eax,%eax
    5133:	e8 98 d3 ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5138:	bf 01 00 00 00       	mov    $0x1,%edi
    513d:	e8 5e d3 ff ff       	call   24a0 <exit@plt>
    5142:	48 8b 0d d7 4e 00 00 	mov    0x4ed7(%rip),%rcx        # a020 <stderr@GLIBC_2.2.5>
    5149:	ba 28 00 00 00       	mov    $0x28,%edx
    514e:	be 01 00 00 00       	mov    $0x1,%esi
    5153:	48 8d 3d ae 22 00 00 	lea    0x22ae(%rip),%rdi        # 7408 <_IO_stdin_used+0x408>
    515a:	e8 61 d3 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    515f:	bf 01 00 00 00       	mov    $0x1,%edi
    5164:	e8 37 d3 ff ff       	call   24a0 <exit@plt>
}
    5169:	e8 c2 d1 ff ff       	call   2330 <__stack_chk_fail@plt>
    516e:	66 90                	xchg   %ax,%ax

0000000000005170 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5170:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5174:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    517b:	8b 8e ac 00 00 00    	mov    0xac(%rsi),%ecx
    5181:	85 c9                	test   %ecx,%ecx
    5183:	0f 8e ea 00 00 00    	jle    5273 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    5189:	41 56                	push   %r14
    518b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    518d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    5190:	41 54                	push   %r12
    5192:	49 89 fc             	mov    %rdi,%r12
    5195:	55                   	push   %rbp
    5196:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5197:	48 8b 7e 40          	mov    0x40(%rsi),%rdi
    519b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    51a0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    51a4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    51ac:	31 db                	xor    %ebx,%ebx
    51ae:	8b 10                	mov    (%rax),%edx
    51b0:	85 d2                	test   %edx,%edx
    51b2:	7e 26                	jle    51da <barriered_work_ingest+0x6a>
    51b4:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    51b8:	48 89 dd             	mov    %rbx,%rbp
    51bb:	48 c1 e5 08          	shl    $0x8,%rbp
    51bf:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    51c3:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    51ca:	74 24                	je     51f0 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    51cc:	48 83 c3 01          	add    $0x1,%rbx
    51d0:	39 da                	cmp    %ebx,%edx
    51d2:	7f e4                	jg     51b8 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    51d4:	8b 8e ac 00 00 00    	mov    0xac(%rsi),%ecx
    51da:	49 83 c5 01          	add    $0x1,%r13
    51de:	44 39 e9             	cmp    %r13d,%ecx
    51e1:	7f bd                	jg     51a0 <barriered_work_ingest+0x30>
}
    51e3:	5b                   	pop    %rbx
    51e4:	31 c0                	xor    %eax,%eax
    51e6:	5d                   	pop    %rbp
    51e7:	41 5c                	pop    %r12
    51e9:	41 5d                	pop    %r13
    51eb:	41 5e                	pop    %r14
    51ed:	c3                   	ret
    51ee:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    51f0:	49 83 84 24 60 01 00 00 01 	addq   $0x1,0x160(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    51f9:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    5200:	bf 04 00 00 00       	mov    $0x4,%edi
    5205:	48 c1 e6 05          	shl    $0x5,%rsi
    5209:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    5210:	48 83 c6 10          	add    $0x10,%rsi
    5214:	e8 f7 d0 ff ff       	call   2310 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5219:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    5221:	48 8b 40 40          	mov    0x40(%rax),%rax
    5225:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    5229:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    522d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    5237:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    523d:	83 c0 01             	add    $0x1,%eax
    5240:	99                   	cltd
    5241:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    5247:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    524d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5250:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    5258:	48 83 c3 01          	add    $0x1,%rbx
    525c:	48 8b 7e 40          	mov    0x40(%rsi),%rdi
    5260:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    5264:	8b 10                	mov    (%rax),%edx
    5266:	39 da                	cmp    %ebx,%edx
    5268:	0f 8f 46 ff ff ff    	jg     51b4 <barriered_work_ingest+0x44>
    526e:	e9 61 ff ff ff       	jmp    51d4 <barriered_work_ingest+0x64>
}
    5273:	31 c0                	xor    %eax,%eax
    5275:	c3                   	ret
    5276:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005280 <barriered_thread>:
void* barriered_thread(void *arg) {
    5280:	f3 0f 1e fa          	endbr64
    5284:	41 56                	push   %r14
    5286:	41 55                	push   %r13
    5288:	41 54                	push   %r12
    528a:	49 89 fc             	mov    %rdi,%r12
    528d:	55                   	push   %rbp
  int waiting = 0;
    528e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    5290:	53                   	push   %rbx
  int t = 0;
    5291:	31 db                	xor    %ebx,%ebx
  while (data->running == 1) {
    5293:	41 83 7c 24 34 01    	cmpl   $0x1,0x34(%r12)
    5299:	0f 85 7d 01 00 00    	jne    541c <barriered_thread+0x19c>
    if (t >= data->task_count) {
    529f:	41 8b 54 24 30       	mov    0x30(%r12),%edx
    52a4:	0f 1f 40 00          	nopl   0x0(%rax)
    52a8:	39 d3                	cmp    %edx,%ebx
    52aa:	0f 8d 80 01 00 00    	jge    5430 <barriered_thread+0x1b0>
    52b0:	48 63 fb             	movslq %ebx,%rdi
    52b3:	48 c1 e7 09          	shl    $0x9,%rdi
    52b7:	49 89 fd             	mov    %rdi,%r13
    52ba:	eb 16                	jmp    52d2 <barriered_thread+0x52>
    52bc:	0f 1f 40 00          	nopl   0x0(%rax)
    for (; t < data->task_count; t++) {
    52c0:	83 c3 01             	add    $0x1,%ebx
    52c3:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    52ca:	39 d3                	cmp    %edx,%ebx
    52cc:	0f 8d 3e 01 00 00    	jge    5410 <barriered_thread+0x190>
      if (data->tasks[t].available == 1) {
    52d2:	49 8b 44 24 28       	mov    0x28(%r12),%rax
    52d7:	4a 8d 34 28          	lea    (%rax,%r13,1),%rsi
    52db:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    52e2:	75 dc                	jne    52c0 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    52e4:	41 8b 7c 24 18       	mov    0x18(%r12),%edi
          previous = t - 1;
    52e9:	83 ea 01             	sub    $0x1,%edx
    52ec:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    52ef:	85 db                	test   %ebx,%ebx
    52f1:	0f 4f d1             	cmovg  %ecx,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    52f4:	85 ff                	test   %edi,%edi
    52f6:	0f 8e 5c 01 00 00    	jle    5458 <barriered_thread+0x1d8>
    52fc:	49 8b 44 24 10       	mov    0x10(%r12),%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5301:	48 63 ca             	movslq %edx,%rcx
    5304:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    5307:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    530a:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5311:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5318:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    531c:	45 31 f6             	xor    %r14d,%r14d
    531f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5323:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    5328:	48 8b 10             	mov    (%rax),%rdx
    532b:	4c 8b 5a 28          	mov    0x28(%rdx),%r11
    532f:	49 01 cb             	add    %rcx,%r11
    5332:	4c 89 da             	mov    %r11,%rdx
    5335:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    533c:	75 04                	jne    5342 <barriered_thread+0xc2>
            arrived++;
    533e:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    5342:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    5349:	75 04                	jne    534f <barriered_thread+0xcf>
            prearrive++;
    534b:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    534f:	48 83 c0 08          	add    $0x8,%rax
    5353:	48 39 f0             	cmp    %rsi,%rax
    5356:	75 d0                	jne    5328 <barriered_thread+0xa8>
        if (prearrive == 0 || prearrive == data->thread_count) {
    5358:	45 85 d2             	test   %r10d,%r10d
    535b:	0f 84 e7 00 00 00    	je     5448 <barriered_thread+0x1c8>
    5361:	44 39 d7             	cmp    %r10d,%edi
    5364:	0f 84 de 00 00 00    	je     5448 <barriered_thread+0x1c8>
        if (arrived == 0 || arrived == data->thread_count) {
    536a:	45 85 f6             	test   %r14d,%r14d
    536d:	74 0b                	je     537a <barriered_thread+0xfa>
    536f:	45 39 74 24 18       	cmp    %r14d,0x18(%r12)
    5374:	0f 85 be 01 00 00    	jne    5538 <barriered_thread+0x2b8>
    537a:	49 8b 44 24 28       	mov    0x28(%r12),%rax
          data->tasks[t].prearrive++;
    537f:	4c 01 e8             	add    %r13,%rax
    5382:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    5389:	85 db                	test   %ebx,%ebx
    538b:	75 10                	jne    539d <barriered_thread+0x11d>
    538d:	49 8b 74 24 70       	mov    0x70(%r12),%rsi
    5392:	49 3b 74 24 78       	cmp    0x78(%r12),%rsi
    5397:	0f 8c 7b 01 00 00    	jl     5518 <barriered_thread+0x298>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    539d:	49 63 0c 24          	movslq (%r12),%rcx
    53a1:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
          data->tasks[t].available = 0;
    53a6:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    53b0:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    53b4:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
    53b8:	4c 01 ef             	add    %r13,%rdi
    53bb:	ff 90 18 01 00 00    	call   *0x118(%rax)
          data->tasks[t].arrived++;
    53c1:	49 8b 44 24 28       	mov    0x28(%r12),%rax
    53c6:	4c 01 e8             	add    %r13,%rax
    53c9:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    53d0:	41 8b 44 24 30       	mov    0x30(%r12),%eax
          data->iteration_count++;
    53d5:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    53db:	83 e8 01             	sub    $0x1,%eax
    53de:	39 d8                	cmp    %ebx,%eax
    53e0:	0f 84 ca 00 00 00    	je     54b0 <barriered_thread+0x230>
          asm volatile ("sfence" ::: "memory");
    53e6:	0f ae f8             	sfence
          if (waiting == 0) {
    53e9:	85 ed                	test   %ebp,%ebp
    53eb:	0f 84 ef 00 00 00    	je     54e0 <barriered_thread+0x260>
    for (; t < data->task_count; t++) {
    53f1:	41 8b 54 24 30       	mov    0x30(%r12),%edx
    53f6:	83 c3 01             	add    $0x1,%ebx
    53f9:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    5400:	39 d3                	cmp    %edx,%ebx
    5402:	0f 8c ca fe ff ff    	jl     52d2 <barriered_thread+0x52>
    5408:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  while (data->running == 1) {
    5410:	41 83 7c 24 34 01    	cmpl   $0x1,0x34(%r12)
    5416:	0f 84 8c fe ff ff    	je     52a8 <barriered_thread+0x28>
}
    541c:	5b                   	pop    %rbx
    541d:	31 c0                	xor    %eax,%eax
    541f:	5d                   	pop    %rbp
    5420:	41 5c                	pop    %r12
    5422:	41 5d                	pop    %r13
    5424:	41 5e                	pop    %r14
    5426:	c3                   	ret
    5427:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      data->cycles++;
    5430:	49 83 84 24 98 00 00 00 01 	addq   $0x1,0x98(%r12)
    for (; t < data->task_count; t++) {
    5439:	85 d2                	test   %edx,%edx
    543b:	7e f3                	jle    5430 <barriered_thread+0x1b0>
    543d:	31 db                	xor    %ebx,%ebx
    543f:	e9 6c fe ff ff       	jmp    52b0 <barriered_thread+0x30>
    5444:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5448:	83 fd 01             	cmp    $0x1,%ebp
    544b:	74 1b                	je     5468 <barriered_thread+0x1e8>
        int arrived = 0; 
    544d:	31 ed                	xor    %ebp,%ebp
    544f:	e9 16 ff ff ff       	jmp    536a <barriered_thread+0xea>
    5454:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    5458:	83 fd 01             	cmp    $0x1,%ebp
    545b:	0f 85 1e ff ff ff    	jne    537f <barriered_thread+0xff>
        int arrived = 0; 
    5461:	45 31 f6             	xor    %r14d,%r14d
    5464:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5468:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
    5470:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    5475:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    5477:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    547b:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    5483:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    5488:	e8 83 ce ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    548d:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
    5495:	48 83 c0 01          	add    $0x1,%rax
    5499:	48 99                	cqto
    549b:	49 f7 bc 24 90 00 00 00 	idivq  0x90(%r12)
    54a3:	49 89 94 24 88 00 00 00 	mov    %rdx,0x88(%r12)
            waiting = 0; 
    54ab:	e9 ba fe ff ff       	jmp    536a <barriered_thread+0xea>
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    54b0:	49 8b 74 24 70       	mov    0x70(%r12),%rsi
    54b5:	49 3b 74 24 78       	cmp    0x78(%r12),%rsi
    54ba:	0f 8d 26 ff ff ff    	jge    53e6 <barriered_thread+0x166>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    54c0:	48 c1 e6 04          	shl    $0x4,%rsi
    54c4:	bf 04 00 00 00       	mov    $0x4,%edi
    54c9:	49 03 74 24 60       	add    0x60(%r12),%rsi
    54ce:	e8 3d ce ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    54d3:	49 83 44 24 70 01    	addq   $0x1,0x70(%r12)
    54d9:	e9 08 ff ff ff       	jmp    53e6 <barriered_thread+0x166>
    54de:	66 90                	xchg   %ax,%ax
            data->task_snapshot[data->task_timestamp_count].task = t;
    54e0:	49 8b 84 24 88 00 00 00 	mov    0x88(%r12),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    54e8:	bf 04 00 00 00       	mov    $0x4,%edi
    for (; t < data->task_count; t++) {
    54ed:	bd 01 00 00 00       	mov    $0x1,%ebp
            data->task_snapshot[data->task_timestamp_count].task = t;
    54f2:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    54f6:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    54fe:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    5502:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    5505:	e8 06 ce ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    550a:	41 8b 54 24 30       	mov    0x30(%r12),%edx
    550f:	e9 ac fd ff ff       	jmp    52c0 <barriered_thread+0x40>
    5514:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    5518:	48 c1 e6 04          	shl    $0x4,%rsi
    551c:	bf 04 00 00 00       	mov    $0x4,%edi
    5521:	49 03 74 24 58       	add    0x58(%r12),%rsi
    5526:	e8 e5 cd ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    552b:	49 8b 44 24 28       	mov    0x28(%r12),%rax
    5530:	4c 01 e8             	add    %r13,%rax
    5533:	e9 65 fe ff ff       	jmp    539d <barriered_thread+0x11d>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    5538:	49 63 14 24          	movslq (%r12),%rdx
    553c:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    5541:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    5545:	48 8b 78 28          	mov    0x28(%rax),%rdi
    5549:	4c 01 ef             	add    %r13,%rdi
    554c:	e8 1f fc ff ff       	call   5170 <barriered_work_ingest>
          break;
    5551:	e9 3d fd ff ff       	jmp    5293 <barriered_thread+0x13>
    5556:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005560 <receive>:
int receive(struct BarrierTask *data) {
    5560:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5564:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    556a:	85 c0                	test   %eax,%eax
    556c:	0f 8e f1 00 00 00    	jle    5663 <receive+0x103>
int receive(struct BarrierTask *data) {
    5572:	41 54                	push   %r12
    5574:	48 89 fa             	mov    %rdi,%rdx
    5577:	55                   	push   %rbp
    5578:	31 ed                	xor    %ebp,%ebp
    557a:	53                   	push   %rbx
    557b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5580:	48 89 ee             	mov    %rbp,%rsi
    5583:	48 c1 e6 05          	shl    $0x5,%rsi
    5587:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    558e:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5591:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    5596:	48 85 ff             	test   %rdi,%rdi
    5599:	0f 8e a1 00 00 00    	jle    5640 <receive+0xe0>
      data->sends++;
    559f:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    55a6:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    55aa:	4c 63 1a             	movslq (%rdx),%r11
    55ad:	49 89 c9             	mov    %rcx,%r9
    55b0:	48 8d 41 01          	lea    0x1(%rcx),%rax
    55b4:	49 f7 d9             	neg    %r9
    55b7:	48 01 c7             	add    %rax,%rdi
    55ba:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    55be:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    55c5:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    55c9:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    55cc:	49 29 c8             	sub    %rcx,%r8
    55cf:	eb 10                	jmp    55e1 <receive+0x81>
    55d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    55d8:	48 83 c0 01          	add    $0x1,%rax
    55dc:	48 39 c7             	cmp    %rax,%rdi
    55df:	74 5f                	je     5640 <receive+0xe0>
      data->n++;
    55e1:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    55e5:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
      data->n++;
    55ec:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    55f3:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    55f7:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    55fb:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5600:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5604:	75 d2                	jne    55d8 <receive+0x78>
    5606:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    560d:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5611:	75 c5                	jne    55d8 <receive+0x78>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5613:	bf 01 00 00 00       	mov    $0x1,%edi
    5618:	b9 01 00 00 00       	mov    $0x1,%ecx
    561d:	ba 01 00 00 00       	mov    $0x1,%edx
    5622:	31 c0                	xor    %eax,%eax
    5624:	48 8d 35 35 1e 00 00 	lea    0x1e35(%rip),%rsi        # 7460 <_IO_stdin_used+0x460>
    562b:	e8 20 ce ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5630:	bf 01 00 00 00       	mov    $0x1,%edi
    5635:	e8 66 ce ff ff       	call   24a0 <exit@plt>
    563a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5640:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    5649:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    564c:	48 83 c5 01          	add    $0x1,%rbp
    5650:	39 aa 34 01 00 00    	cmp    %ebp,0x134(%rdx)
    5656:	0f 8f 24 ff ff ff    	jg     5580 <receive+0x20>
}
    565c:	5b                   	pop    %rbx
    565d:	31 c0                	xor    %eax,%eax
    565f:	5d                   	pop    %rbp
    5660:	41 5c                	pop    %r12
    5662:	c3                   	ret
    5663:	31 c0                	xor    %eax,%eax
    5665:	c3                   	ret
    5666:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005670 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5670:	f3 0f 1e fa          	endbr64
    5674:	41 57                	push   %r15
    5676:	41 56                	push   %r14
    5678:	41 55                	push   %r13
    567a:	41 54                	push   %r12
    567c:	55                   	push   %rbp
    567d:	53                   	push   %rbx
    567e:	48 89 fb             	mov    %rdi,%rbx
    5681:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    5685:	8b 07                	mov    (%rdi),%eax
    5687:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    568d:	0f 84 3d 01 00 00    	je     57d0 <barriered_work+0x160>
    receive(data);
    5693:	e8 c8 fe ff ff       	call   5560 <receive>
    while (data->scheduled == 1) {
    5698:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    569f:	75 1b                	jne    56bc <barriered_work+0x4c>
    56a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    56a8:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    56b0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    56b3:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    56ba:	74 ec                	je     56a8 <barriered_work+0x38>
  if (data->sending == 1) {
    56bc:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    56c3:	0f 85 74 02 00 00    	jne    593d <barriered_work+0x2cd>
      for (int n = 0 ; n < data->thread_count; n++) {
    56c9:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    56cf:	85 c0                	test   %eax,%eax
    56d1:	0f 8e 72 02 00 00    	jle    5949 <barriered_work+0x2d9>
    56d7:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    56de:	31 d2                	xor    %edx,%edx
    56e0:	48 89 0c 24          	mov    %rcx,(%rsp)
    56e4:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    56eb:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    56f0:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    56f6:	0f 84 bf 00 00 00    	je     57bb <barriered_work+0x14b>
        struct Data *them = data->mailboxes[n].higher;
    56fc:	49 89 d1             	mov    %rdx,%r9
    56ff:	49 c1 e1 05          	shl    $0x5,%r9
    5703:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    570a:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    570e:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5712:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5716:	4d 39 c3             	cmp    %r8,%r11
    5719:	0f 8d 93 00 00 00    	jge    57b2 <barriered_work+0x142>
    571f:	4c 89 c6             	mov    %r8,%rsi
    5722:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5729:	4d 8b 71 10          	mov    0x10(%r9),%r14
    572d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5730:	49 8b 0a             	mov    (%r10),%rcx
    5733:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5737:	48 83 f8 02          	cmp    $0x2,%rax
    573b:	0f 86 8f 02 00 00    	jbe    59d0 <barriered_work+0x360>
    5741:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5749:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5751:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5755:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5759:	4c 39 2c 24          	cmp    %r13,(%rsp)
    575d:	0f 83 fd 01 00 00    	jae    5960 <barriered_work+0x2f0>
    5763:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5768:	4d 39 fc             	cmp    %r15,%r12
    576b:	0f 83 ef 01 00 00    	jae    5960 <barriered_work+0x2f0>
    5771:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5775:	48 01 cf             	add    %rcx,%rdi
    5778:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5780:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5787:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    578b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    578f:	49 39 fb             	cmp    %rdi,%r11
    5792:	75 ec                	jne    5780 <barriered_work+0x110>
    5794:	0f 1f 40 00          	nopl   0x0(%rax)
    5798:	48 01 f5             	add    %rsi,%rbp
    579b:	4c 01 f6             	add    %r14,%rsi
    579e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    57a5:	49 89 71 10          	mov    %rsi,0x10(%r9)
    57a9:	4d 89 42 08          	mov    %r8,0x8(%r10)
    57ad:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    57b2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    57b5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    57bb:	48 83 c2 01          	add    $0x1,%rdx
    57bf:	39 d0                	cmp    %edx,%eax
    57c1:	0f 8f 29 ff ff ff    	jg     56f0 <barriered_work+0x80>
    57c7:	e9 7d 01 00 00       	jmp    5949 <barriered_work+0x2d9>
    57cc:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    57d0:	e8 8b fd ff ff       	call   5560 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    57d5:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    57dc:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    57de:	45 85 c9             	test   %r9d,%r9d
    57e1:	0f 8e 85 00 00 00    	jle    586c <barriered_work+0x1fc>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    57e7:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    57ee:	4c 63 d8             	movslq %eax,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    57f1:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    57f4:	49 c1 e3 09          	shl    $0x9,%r11
    57f8:	4c 8b 52 10          	mov    0x10(%rdx),%r10
              int next_task = abs((t + 1) % (data->thread_count));
    57fc:	99                   	cltd
    57fd:	41 f7 f9             	idiv   %r9d
    5800:	4c 89 d7             	mov    %r10,%rdi
    5803:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
    5807:	89 d0                	mov    %edx,%eax
    5809:	f7 d8                	neg    %eax
    580b:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    580e:	45 31 c0             	xor    %r8d,%r8d
              int next_task = abs((t + 1) % (data->thread_count));
    5811:	48 63 ea             	movslq %edx,%rbp
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5814:	48 c1 e5 09          	shl    $0x9,%rbp
    5818:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    5820:	31 c0                	xor    %eax,%eax
    5822:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5828:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    582c:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    5830:	48 8b 8c 2a 68 01 00 00 	mov    0x168(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5838:	48 8b 17             	mov    (%rdi),%rdx
    583b:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    583f:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5842:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5846:	48 c1 e2 05          	shl    $0x5,%rdx
    584a:	4a 03 94 1e 68 01 00 00 	add    0x168(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5852:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    5856:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    585a:	49 39 c1             	cmp    %rax,%r9
    585d:	75 c9                	jne    5828 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    585f:	48 83 c7 08          	add    $0x8,%rdi
    5863:	49 83 c0 20          	add    $0x20,%r8
    5867:	49 39 fc             	cmp    %rdi,%r12
    586a:	75 b4                	jne    5820 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    586c:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    586f:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5876:	31 ff                	xor    %edi,%edi
    5878:	48 c1 e6 05          	shl    $0x5,%rsi
    587c:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5883:	e8 88 ca ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5888:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    588f:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5896:	48 8b 50 38          	mov    0x38(%rax),%rdx
    589a:	8b 4a 10             	mov    0x10(%rdx),%ecx
    589d:	8d 69 01             	lea    0x1(%rcx),%ebp
    58a0:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    58a3:	75 53                	jne    58f8 <barriered_work+0x288>
    58a5:	0f 1f 00             	nopl   (%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    58a8:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    58af:	48 8b 40 10          	mov    0x10(%rax),%rax
    58b3:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    58b6:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    58be:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    58c2:	48 c1 e7 09          	shl    $0x9,%rdi
    58c6:	48 03 78 28          	add    0x28(%rax),%rdi
    58ca:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    58d0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    58d3:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    58da:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    58e1:	74 c5                	je     58a8 <barriered_work+0x238>
    if (modcount != data->thread->protected_state->modcount) {
    58e3:	48 8b 40 38          	mov    0x38(%rax),%rax
    58e7:	3b 68 10             	cmp    0x10(%rax),%ebp
    58ea:	74 0c                	je     58f8 <barriered_work+0x288>
    58ec:	48 8d 3d 11 19 00 00 	lea    0x1911(%rip),%rdi        # 7204 <_IO_stdin_used+0x204>
    58f3:	e8 f8 c9 ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    58f8:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    58ff:	31 ff                	xor    %edi,%edi
    5901:	48 c1 e6 05          	shl    $0x5,%rsi
    5905:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    590c:	48 83 c6 10          	add    $0x10,%rsi
    5910:	e8 fb c9 ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5915:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    591c:	48 83 c0 01          	add    $0x1,%rax
    5920:	48 99                	cqto
    5922:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    5929:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5930:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    5937:	0f 84 a8 00 00 00    	je     59e5 <barriered_work+0x375>
    593d:	48 8d 3d d0 18 00 00 	lea    0x18d0(%rip),%rdi        # 7214 <_IO_stdin_used+0x214>
    5944:	e8 a7 c9 ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5949:	0f ae f8             	sfence
}
    594c:	48 83 c4 18          	add    $0x18,%rsp
    5950:	31 c0                	xor    %eax,%eax
    5952:	5b                   	pop    %rbx
    5953:	5d                   	pop    %rbp
    5954:	41 5c                	pop    %r12
    5956:	41 5d                	pop    %r13
    5958:	41 5e                	pop    %r14
    595a:	41 5f                	pop    %r15
    595c:	c3                   	ret
    595d:	0f 1f 00             	nopl   (%rax)
    5960:	49 89 f5             	mov    %rsi,%r13
    5963:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    596a:	4c 89 e7             	mov    %r12,%rdi
    596d:	49 d1 ed             	shr    %r13
    5970:	49 c1 e5 04          	shl    $0x4,%r13
    5974:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5979:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    597d:	41 83 e5 10          	and    $0x10,%r13d
    5981:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5985:	74 11                	je     5998 <barriered_work+0x328>
          them->messages[them->messages_count++] = data->message; 
    5987:	48 83 c7 10          	add    $0x10,%rdi
    598b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5990:	49 39 ff             	cmp    %rdi,%r15
    5993:	74 13                	je     59a8 <barriered_work+0x338>
    5995:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5998:	0f 11 07             	movups %xmm0,(%rdi)
    599b:	48 83 c7 20          	add    $0x20,%rdi
    599f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    59a3:	49 39 ff             	cmp    %rdi,%r15
    59a6:	75 f0                	jne    5998 <barriered_work+0x328>
    59a8:	48 89 f7             	mov    %rsi,%rdi
    59ab:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    59af:	4c 01 df             	add    %r11,%rdi
    59b2:	40 f6 c6 01          	test   $0x1,%sil
    59b6:	0f 84 dc fd ff ff    	je     5798 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    59bc:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    59c3:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    59c7:	e9 cc fd ff ff       	jmp    5798 <barriered_work+0x128>
    59cc:	0f 1f 40 00          	nopl   0x0(%rax)
    59d0:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    59d8:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    59e0:	e9 8c fd ff ff       	jmp    5771 <barriered_work+0x101>
      for (int n = 0 ; n < data->thread_count; n++) {
    59e5:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    59ec:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    59f2:	31 d2                	xor    %edx,%edx
    59f4:	48 89 0c 24          	mov    %rcx,(%rsp)
    59f8:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    59ff:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5a04:	85 c0                	test   %eax,%eax
    5a06:	0f 8e 3d ff ff ff    	jle    5949 <barriered_work+0x2d9>
    5a0c:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5a10:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    5a16:	0f 84 af 00 00 00    	je     5acb <barriered_work+0x45b>
        struct Data *them = data->mailboxes[n].higher;
    5a1c:	49 89 d1             	mov    %rdx,%r9
    5a1f:	49 c1 e1 05          	shl    $0x5,%r9
    5a23:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    5a2a:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    5a2e:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5a32:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5a36:	4d 39 d8             	cmp    %r11,%r8
    5a39:	0f 8e 83 00 00 00    	jle    5ac2 <barriered_work+0x452>
    5a3f:	4c 89 c6             	mov    %r8,%rsi
    5a42:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5a49:	4d 8b 71 10          	mov    0x10(%r9),%r14
    5a4d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5a50:	49 8b 0a             	mov    (%r10),%rcx
    5a53:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5a57:	48 83 f8 02          	cmp    $0x2,%rax
    5a5b:	0f 86 ef 00 00 00    	jbe    5b50 <barriered_work+0x4e0>
    5a61:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5a69:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5a71:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5a75:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5a79:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5a7d:	73 61                	jae    5ae0 <barriered_work+0x470>
    5a7f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5a84:	4d 39 fc             	cmp    %r15,%r12
    5a87:	73 57                	jae    5ae0 <barriered_work+0x470>
    5a89:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5a8d:	48 01 cf             	add    %rcx,%rdi
    5a90:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5a97:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    5a9b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    5a9f:	49 39 fb             	cmp    %rdi,%r11
    5aa2:	75 ec                	jne    5a90 <barriered_work+0x420>
    5aa4:	0f 1f 40 00          	nopl   0x0(%rax)
    5aa8:	48 01 f5             	add    %rsi,%rbp
    5aab:	4c 01 f6             	add    %r14,%rsi
    5aae:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5ab5:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5ab9:	4d 89 42 08          	mov    %r8,0x8(%r10)
    5abd:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5ac2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5ac5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    5acb:	48 83 c2 01          	add    $0x1,%rdx
    5acf:	39 d0                	cmp    %edx,%eax
    5ad1:	0f 8f 39 ff ff ff    	jg     5a10 <barriered_work+0x3a0>
    5ad7:	e9 6d fe ff ff       	jmp    5949 <barriered_work+0x2d9>
    5adc:	0f 1f 40 00          	nopl   0x0(%rax)
    5ae0:	49 89 f5             	mov    %rsi,%r13
    5ae3:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5aea:	4c 89 e7             	mov    %r12,%rdi
    5aed:	49 d1 ed             	shr    %r13
    5af0:	49 c1 e5 04          	shl    $0x4,%r13
    5af4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5af9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5afd:	41 83 e5 10          	and    $0x10,%r13d
    5b01:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5b05:	74 11                	je     5b18 <barriered_work+0x4a8>
          them->messages[them->messages_count++] = data->message; 
    5b07:	48 83 c7 10          	add    $0x10,%rdi
    5b0b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5b10:	4c 39 ff             	cmp    %r15,%rdi
    5b13:	74 13                	je     5b28 <barriered_work+0x4b8>
    5b15:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5b18:	0f 11 07             	movups %xmm0,(%rdi)
    5b1b:	48 83 c7 20          	add    $0x20,%rdi
    5b1f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5b23:	4c 39 ff             	cmp    %r15,%rdi
    5b26:	75 f0                	jne    5b18 <barriered_work+0x4a8>
    5b28:	48 89 f7             	mov    %rsi,%rdi
    5b2b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5b2f:	4c 01 df             	add    %r11,%rdi
    5b32:	40 f6 c6 01          	test   $0x1,%sil
    5b36:	0f 84 6c ff ff ff    	je     5aa8 <barriered_work+0x438>
          them->messages[them->messages_count++] = data->message; 
    5b3c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5b43:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5b47:	e9 5c ff ff ff       	jmp    5aa8 <barriered_work+0x438>
    5b4c:	0f 1f 40 00          	nopl   0x0(%rax)
    5b50:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5b58:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5b60:	e9 24 ff ff ff       	jmp    5a89 <barriered_work+0x419>
    5b65:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005b70 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    5b70:	f3 0f 1e fa          	endbr64
    5b74:	53                   	push   %rbx
    5b75:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    5b78:	e8 f3 f5 ff ff       	call   5170 <barriered_work_ingest>
  barriered_work(data);
    5b7d:	48 89 df             	mov    %rbx,%rdi
}
    5b80:	5b                   	pop    %rbx
  barriered_work(data);
    5b81:	e9 ea fa ff ff       	jmp    5670 <barriered_work>
    5b86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005b90 <sendm>:
int sendm(struct BarrierTask *data) {
    5b90:	f3 0f 1e fa          	endbr64
    5b94:	41 57                	push   %r15
    5b96:	41 56                	push   %r14
    5b98:	41 55                	push   %r13
    5b9a:	41 54                	push   %r12
    5b9c:	55                   	push   %rbp
    5b9d:	53                   	push   %rbx
    5b9e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5ba2:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
    5ba9:	0f 85 99 01 00 00    	jne    5d48 <sendm+0x1b8>
    5baf:	48 8d b7 80 01 00 00 	lea    0x180(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5bb6:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    5bbc:	48 89 fa             	mov    %rdi,%rdx
    5bbf:	31 c9                	xor    %ecx,%ecx
    5bc1:	48 89 34 24          	mov    %rsi,(%rsp)
    5bc5:	48 8d b7 88 01 00 00 	lea    0x188(%rdi),%rsi
    5bcc:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5bd1:	85 c0                	test   %eax,%eax
    5bd3:	0f 8e ce 00 00 00    	jle    5ca7 <sendm+0x117>
    5bd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    5be0:	39 8a 30 01 00 00    	cmp    %ecx,0x130(%rdx)
    5be6:	0f 84 af 00 00 00    	je     5c9b <sendm+0x10b>
        struct Data *them = data->mailboxes[n].higher;
    5bec:	49 89 ca             	mov    %rcx,%r10
    5bef:	49 c1 e2 05          	shl    $0x5,%r10
    5bf3:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
    5bfa:	4d 8b 5a 08          	mov    0x8(%r10),%r11
        for (; them->messages_count < min;) {
    5bfe:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    5c02:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    5c06:	4c 39 cb             	cmp    %r9,%rbx
    5c09:	0f 8d 83 00 00 00    	jge    5c92 <sendm+0x102>
    5c0f:	4c 89 cf             	mov    %r9,%rdi
    5c12:	48 8b aa 08 01 00 00 	mov    0x108(%rdx),%rbp
    5c19:	4d 8b 72 10          	mov    0x10(%r10),%r14
    5c1d:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    5c20:	49 8b 33             	mov    (%r11),%rsi
    5c23:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    5c27:	48 83 f8 02          	cmp    $0x2,%rax
    5c2b:	0f 86 ff 00 00 00    	jbe    5d30 <sendm+0x1a0>
    5c31:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5c39:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5c41:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    5c45:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    5c49:	4c 39 2c 24          	cmp    %r13,(%rsp)
    5c4d:	73 71                	jae    5cc0 <sendm+0x130>
    5c4f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5c54:	4d 39 fc             	cmp    %r15,%r12
    5c57:	73 67                	jae    5cc0 <sendm+0x130>
    5c59:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    5c5d:	49 01 f0             	add    %rsi,%r8
    5c60:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    5c67:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    5c6b:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    5c6f:	49 39 d8             	cmp    %rbx,%r8
    5c72:	75 ec                	jne    5c60 <sendm+0xd0>
    5c74:	0f 1f 40 00          	nopl   0x0(%rax)
    5c78:	48 01 fd             	add    %rdi,%rbp
    5c7b:	4c 01 f7             	add    %r14,%rdi
    5c7e:	48 89 aa 08 01 00 00 	mov    %rbp,0x108(%rdx)
    5c85:	49 89 7a 10          	mov    %rdi,0x10(%r10)
    5c89:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    5c8d:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5c92:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5c95:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    5c9b:	48 83 c1 01          	add    $0x1,%rcx
    5c9f:	39 c8                	cmp    %ecx,%eax
    5ca1:	0f 8f 39 ff ff ff    	jg     5be0 <sendm+0x50>
}
    5ca7:	48 83 c4 18          	add    $0x18,%rsp
    5cab:	31 c0                	xor    %eax,%eax
    5cad:	5b                   	pop    %rbx
    5cae:	5d                   	pop    %rbp
    5caf:	41 5c                	pop    %r12
    5cb1:	41 5d                	pop    %r13
    5cb3:	41 5e                	pop    %r14
    5cb5:	41 5f                	pop    %r15
    5cb7:	c3                   	ret
    5cb8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5cc0:	49 89 fd             	mov    %rdi,%r13
    5cc3:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    5cca:	4d 89 e0             	mov    %r12,%r8
    5ccd:	49 d1 ed             	shr    %r13
    5cd0:	49 c1 e5 04          	shl    $0x4,%r13
    5cd4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5cd9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    5cdd:	41 83 e5 10          	and    $0x10,%r13d
    5ce1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5ce5:	74 11                	je     5cf8 <sendm+0x168>
          them->messages[them->messages_count++] = data->message; 
    5ce7:	49 83 c0 10          	add    $0x10,%r8
    5ceb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5cf0:	4d 39 f8             	cmp    %r15,%r8
    5cf3:	74 15                	je     5d0a <sendm+0x17a>
    5cf5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5cf8:	41 0f 11 00          	movups %xmm0,(%r8)
    5cfc:	49 83 c0 20          	add    $0x20,%r8
    5d00:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    5d05:	4d 39 f8             	cmp    %r15,%r8
    5d08:	75 ee                	jne    5cf8 <sendm+0x168>
    5d0a:	49 89 f8             	mov    %rdi,%r8
    5d0d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    5d11:	49 01 d8             	add    %rbx,%r8
    5d14:	40 f6 c7 01          	test   $0x1,%dil
    5d18:	0f 84 5a ff ff ff    	je     5c78 <sendm+0xe8>
          them->messages[them->messages_count++] = data->message; 
    5d1e:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    5d25:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    5d29:	e9 4a ff ff ff       	jmp    5c78 <sendm+0xe8>
    5d2e:	66 90                	xchg   %ax,%ax
    5d30:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5d38:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5d40:	e9 14 ff ff ff       	jmp    5c59 <sendm+0xc9>
    5d45:	0f 1f 00             	nopl   (%rax)
    5d48:	48 8d 3d c5 14 00 00 	lea    0x14c5(%rip),%rdi        # 7214 <_IO_stdin_used+0x214>
    5d4f:	e8 9c c5 ff ff       	call   22f0 <puts@plt>
    5d54:	e9 4e ff ff ff       	jmp    5ca7 <sendm+0x117>
    5d59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005d60 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5d60:	f3 0f 1e fa          	endbr64
}
    5d64:	31 c0                	xor    %eax,%eax
    5d66:	c3                   	ret
    5d67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005d70 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5d70:	f3 0f 1e fa          	endbr64
    5d74:	31 c0                	xor    %eax,%eax
    5d76:	c3                   	ret
    5d77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005d80 <after>:
int after(struct timespec left, struct timespec right) {
    5d80:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5d84:	31 c0                	xor    %eax,%eax
    5d86:	48 39 d7             	cmp    %rdx,%rdi
    5d89:	7e 08                	jle    5d93 <after+0x13>
    5d8b:	31 c0                	xor    %eax,%eax
    5d8d:	48 39 ce             	cmp    %rcx,%rsi
    5d90:	0f 9f c0             	setg   %al
}
    5d93:	c3                   	ret
    5d94:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5d9f:	90                   	nop

0000000000005da0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5da0:	f3 0f 1e fa          	endbr64
    5da4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5da9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5dae:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5db0:	48 39 d7             	cmp    %rdx,%rdi
    5db3:	7f 18                	jg     5dcd <within+0x2d>
    5db5:	4d 39 d8             	cmp    %r11,%r8
    5db8:	0f 9e c2             	setle  %dl
    5dbb:	48 39 ce             	cmp    %rcx,%rsi
    5dbe:	0f 9e c0             	setle  %al
    5dc1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5dc3:	31 c0                	xor    %eax,%eax
    5dc5:	4d 39 d1             	cmp    %r10,%r9
    5dc8:	0f 9e c0             	setle  %al
    5dcb:	21 d0                	and    %edx,%eax
}
    5dcd:	c3                   	ret
    5dce:	66 90                	xchg   %ax,%ax

0000000000005dd0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5dd0:	f3 0f 1e fa          	endbr64
    5dd4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5dd9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5dde:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5de3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5de8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5ded:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5df2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5df7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5dfc:	48 39 fe             	cmp    %rdi,%rsi
    5dff:	7d 2f                	jge    5e30 <overlap+0x60>
    5e01:	48 39 ca             	cmp    %rcx,%rdx
    5e04:	7d 62                	jge    5e68 <overlap+0x98>
    5e06:	4d 39 da             	cmp    %r11,%r10
    5e09:	7d 0e                	jge    5e19 <overlap+0x49>
    return 1;
    5e0b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e10:	4d 39 c1             	cmp    %r8,%r9
    5e13:	0f 8c 7f 00 00 00    	jl     5e98 <overlap+0xc8>
  return 0;
    5e19:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e1b:	4d 39 c1             	cmp    %r8,%r9
    5e1e:	7f 4c                	jg     5e6c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e20:	31 c0                	xor    %eax,%eax
    5e22:	4d 39 da             	cmp    %r11,%r10
    5e25:	0f 9e c0             	setle  %al
    5e28:	c3                   	ret
    5e29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5e30:	7e 4e                	jle    5e80 <overlap+0xb0>
    5e32:	48 39 ca             	cmp    %rcx,%rdx
    5e35:	7f 39                	jg     5e70 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e37:	75 31                	jne    5e6a <overlap+0x9a>
    5e39:	4d 39 c1             	cmp    %r8,%r9
    5e3c:	7c 2c                	jl     5e6a <overlap+0x9a>
    return 1;
    5e3e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5e43:	4d 39 da             	cmp    %r11,%r10
    5e46:	7d 24                	jge    5e6c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e48:	48 39 ca             	cmp    %rcx,%rdx
    5e4b:	0f 94 c2             	sete   %dl
    5e4e:	48 39 fe             	cmp    %rdi,%rsi
    5e51:	0f 94 c0             	sete   %al
    5e54:	21 c2                	and    %eax,%edx
    5e56:	31 c0                	xor    %eax,%eax
    5e58:	4d 39 c1             	cmp    %r8,%r9
    5e5b:	0f 94 c0             	sete   %al
    5e5e:	21 d0                	and    %edx,%eax
    5e60:	c3                   	ret
    5e61:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5e68:	74 af                	je     5e19 <overlap+0x49>
  return 0;
    5e6a:	31 c0                	xor    %eax,%eax
}
    5e6c:	c3                   	ret
    5e6d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5e70:	4d 39 da             	cmp    %r11,%r10
    5e73:	7e c4                	jle    5e39 <overlap+0x69>
    return 1;
    5e75:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5e7a:	4d 39 c1             	cmp    %r8,%r9
    5e7d:	7e ba                	jle    5e39 <overlap+0x69>
    5e7f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5e80:	48 39 ca             	cmp    %rcx,%rdx
    5e83:	7c 94                	jl     5e19 <overlap+0x49>
    5e85:	4d 39 c1             	cmp    %r8,%r9
    5e88:	7d b4                	jge    5e3e <overlap+0x6e>
    5e8a:	48 39 ca             	cmp    %rcx,%rdx
    5e8d:	74 91                	je     5e20 <overlap+0x50>
    5e8f:	eb d9                	jmp    5e6a <overlap+0x9a>
    5e91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5e98:	c3                   	ret
    5e99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005ea0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5ea0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5ea4:	85 f6                	test   %esi,%esi
    5ea6:	0f 8e 44 03 00 00    	jle    61f0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    5eac:	41 57                	push   %r15
    5eae:	41 89 f7             	mov    %esi,%r15d
    5eb1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5eb3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5eb6:	41 55                	push   %r13
    5eb8:	41 54                	push   %r12
    5eba:	55                   	push   %rbp
    5ebb:	53                   	push   %rbx
    5ebc:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5ec0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5ec4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5ec9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5ece:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    5ed1:	45 39 e6             	cmp    %r12d,%r14d
    5ed4:	0f 84 4e 02 00 00    	je     6128 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5eda:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5edf:	8b 50 08             	mov    0x8(%rax),%edx
    5ee2:	85 d2                	test   %edx,%edx
    5ee4:	0f 8e 3e 02 00 00    	jle    6128 <verify+0x288>
    5eea:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    5eef:	31 c9                	xor    %ecx,%ecx
    5ef1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    5ef6:	31 c0                	xor    %eax,%eax
    5ef8:	44 89 f2             	mov    %r14d,%edx
    5efb:	bf 01 00 00 00       	mov    $0x1,%edi
    5f00:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5f05:	48 8d 35 14 13 00 00 	lea    0x1314(%rip),%rsi        # 7220 <_IO_stdin_used+0x220>
    5f0c:	e8 3f c5 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5f11:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5f16:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    5f1b:	8b 40 08             	mov    0x8(%rax),%eax
    5f1e:	85 c0                	test   %eax,%eax
    5f20:	0f 8e e6 01 00 00    	jle    610c <verify+0x26c>
    5f26:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5f29:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    5f2e:	31 db                	xor    %ebx,%ebx
    5f30:	48 c1 e0 09          	shl    $0x9,%rax
    5f34:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    5f39:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5f3e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5f43:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    5f48:	4c 8b 20             	mov    (%rax),%r12
    5f4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5f50:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    5f55:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5f5a:	49 89 de             	mov    %rbx,%r14
    5f5d:	48 8d 35 d1 12 00 00 	lea    0x12d1(%rip),%rsi        # 7235 <_IO_stdin_used+0x235>
    5f64:	49 c1 e6 09          	shl    $0x9,%r14
    5f68:	bf 01 00 00 00       	mov    $0x1,%edi
    5f6d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5f71:	4b 8b 8c 3c 58 01 00 00 	mov    0x158(%r12,%r15,1),%rcx
    5f79:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    5f7e:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    5f86:	31 c0                	xor    %eax,%eax
    5f88:	e8 c3 c4 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5f8d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5f92:	4c 8b 20             	mov    (%rax),%r12
    5f95:	4b 83 bc 3c 58 01 00 00 00 	cmpq   $0x0,0x158(%r12,%r15,1)
    5f9e:	0f 8e 47 01 00 00    	jle    60eb <verify+0x24b>
    5fa4:	4c 03 75 00          	add    0x0(%rbp),%r14
    5fa8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5fad:	ba 01 00 00 00       	mov    $0x1,%edx
    5fb2:	4d 89 f5             	mov    %r14,%r13
    5fb5:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    5fbc:	4d 85 f6             	test   %r14,%r14
    5fbf:	0f 8e 21 01 00 00    	jle    60e6 <verify+0x246>
    5fc5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5fc8:	48 89 d5             	mov    %rdx,%rbp
    5fcb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5fd0:	31 db                	xor    %ebx,%ebx
    5fd2:	4d 89 f2             	mov    %r14,%r10
    5fd5:	48 c1 e5 05          	shl    $0x5,%rbp
    5fd9:	48 83 ed 20          	sub    $0x20,%rbp
    5fdd:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    5fe1:	49 89 ee             	mov    %rbp,%r14
    5fe4:	48 89 dd             	mov    %rbx,%rbp
    5fe7:	48 89 d3             	mov    %rdx,%rbx
    5fea:	eb 31                	jmp    601d <verify+0x17d>
    5fec:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5ff0:	4c 39 c2             	cmp    %r8,%rdx
    5ff3:	0f 8d 57 01 00 00    	jge    6150 <verify+0x2b0>
    5ff9:	4c 39 df             	cmp    %r11,%rdi
    5ffc:	7e 05                	jle    6003 <verify+0x163>
    5ffe:	49 39 c1             	cmp    %rax,%r9
    6001:	7c 75                	jl     6078 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6003:	4c 39 df             	cmp    %r11,%rdi
    6006:	0f 8d ab 01 00 00    	jge    61b7 <verify+0x317>
    600c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6010:	48 83 c5 01          	add    $0x1,%rbp
    6014:	49 39 ea             	cmp    %rbp,%r10
    6017:	0f 8e a9 00 00 00    	jle    60c6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    601d:	49 8b 97 48 01 00 00 	mov    0x148(%r15),%rdx
    6024:	48 89 e8             	mov    %rbp,%rax
    6027:	48 c1 e0 05          	shl    $0x5,%rax
    602b:	49 03 85 48 01 00 00 	add    0x148(%r13),%rax
    6032:	4c 01 f2             	add    %r14,%rdx
    6035:	48 8b 08             	mov    (%rax),%rcx
    6038:	48 8b 78 10          	mov    0x10(%rax),%rdi
    603c:	48 8b 32             	mov    (%rdx),%rsi
    603f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    6043:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    6047:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    604b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    604f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    6053:	48 39 f1             	cmp    %rsi,%rcx
    6056:	7c 98                	jl     5ff0 <verify+0x150>
    6058:	0f 8e 42 01 00 00    	jle    61a0 <verify+0x300>
    605e:	4c 39 c2             	cmp    %r8,%rdx
    6061:	0f 8f f9 00 00 00    	jg     6160 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6067:	75 a7                	jne    6010 <verify+0x170>
    6069:	4c 39 df             	cmp    %r11,%rdi
    606c:	7f a2                	jg     6010 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    606e:	49 39 c1             	cmp    %rax,%r9
    6071:	7c 9d                	jl     6010 <verify+0x170>
    6073:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6078:	49 89 c1             	mov    %rax,%r9
    607b:	48 89 f9             	mov    %rdi,%rcx
    607e:	48 89 f2             	mov    %rsi,%rdx
    6081:	bf 01 00 00 00       	mov    $0x1,%edi
    6086:	48 8d 35 fb 13 00 00 	lea    0x13fb(%rip),%rsi        # 7488 <_IO_stdin_used+0x488>
    608d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    608f:	48 83 c5 01          	add    $0x1,%rbp
    6093:	e8 b8 c3 ff ff       	call   2450 <__printf_chk@plt>
    6098:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    609d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    60a2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60a5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60aa:	4d 8b 95 58 01 00 00 	mov    0x158(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60b1:	4c 8b 20             	mov    (%rax),%r12
    60b4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    60b9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60bd:	49 39 ea             	cmp    %rbp,%r10
    60c0:	0f 8f 57 ff ff ff    	jg     601d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    60c6:	48 89 da             	mov    %rbx,%rdx
    60c9:	49 3b 9f 58 01 00 00 	cmp    0x158(%r15),%rbx
    60d0:	7d 14                	jge    60e6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    60d2:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    60d9:	48 83 c2 01          	add    $0x1,%rdx
    60dd:	4d 85 f6             	test   %r14,%r14
    60e0:	0f 8f e2 fe ff ff    	jg     5fc8 <verify+0x128>
    60e6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    60eb:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    60f0:	48 83 c3 01          	add    $0x1,%rbx
    60f4:	39 58 08             	cmp    %ebx,0x8(%rax)
    60f7:	0f 8f 53 fe ff ff    	jg     5f50 <verify+0xb0>
    60fd:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    6102:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    6107:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    610c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6111:	48 83 c1 01          	add    $0x1,%rcx
    6115:	39 48 08             	cmp    %ecx,0x8(%rax)
    6118:	0f 8f d8 fd ff ff    	jg     5ef6 <verify+0x56>
    611e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    6123:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    6128:	48 81 44 24 10 b0 00 00 00 	addq   $0xb0,0x10(%rsp)
    6131:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    6136:	41 39 c7             	cmp    %eax,%r15d
    6139:	0f 84 86 00 00 00    	je     61c5 <verify+0x325>
    613f:	41 89 c4             	mov    %eax,%r12d
    6142:	e9 8a fd ff ff       	jmp    5ed1 <verify+0x31>
    6147:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6150:	0f 85 ba fe ff ff    	jne    6010 <verify+0x170>
    6156:	e9 a8 fe ff ff       	jmp    6003 <verify+0x163>
    615b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    6160:	49 39 c1             	cmp    %rax,%r9
    6163:	7e 09                	jle    616e <verify+0x2ce>
    6165:	4c 39 df             	cmp    %r11,%rdi
    6168:	0f 8c 0a ff ff ff    	jl     6078 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    616e:	4c 39 df             	cmp    %r11,%rdi
    6171:	0f 8f 99 fe ff ff    	jg     6010 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6177:	49 39 c1             	cmp    %rax,%r9
    617a:	0f 8d f8 fe ff ff    	jge    6078 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6180:	48 39 f1             	cmp    %rsi,%rcx
    6183:	0f 85 87 fe ff ff    	jne    6010 <verify+0x170>
    6189:	4c 39 c2             	cmp    %r8,%rdx
    618c:	0f 85 7e fe ff ff    	jne    6010 <verify+0x170>
    6192:	4c 39 df             	cmp    %r11,%rdi
    6195:	0f 84 dd fe ff ff    	je     6078 <verify+0x1d8>
    619b:	e9 70 fe ff ff       	jmp    6010 <verify+0x170>
    61a0:	4c 39 c2             	cmp    %r8,%rdx
    61a3:	0f 8c 5a fe ff ff    	jl     6003 <verify+0x163>
    61a9:	4c 39 df             	cmp    %r11,%rdi
    61ac:	7e c9                	jle    6177 <verify+0x2d7>
    61ae:	4c 39 c2             	cmp    %r8,%rdx
    61b1:	0f 85 59 fe ff ff    	jne    6010 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    61b7:	49 39 c1             	cmp    %rax,%r9
    61ba:	0f 8f 50 fe ff ff    	jg     6010 <verify+0x170>
    61c0:	e9 b3 fe ff ff       	jmp    6078 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    61c5:	48 81 44 24 18 b0 00 00 00 	addq   $0xb0,0x18(%rsp)
    61ce:	41 8d 46 01          	lea    0x1(%r14),%eax
    61d2:	45 39 e6             	cmp    %r12d,%r14d
    61d5:	74 08                	je     61df <verify+0x33f>
    61d7:	41 89 c6             	mov    %eax,%r14d
    61da:	e9 ea fc ff ff       	jmp    5ec9 <verify+0x29>
}
    61df:	48 83 c4 58          	add    $0x58,%rsp
    61e3:	31 c0                	xor    %eax,%eax
    61e5:	5b                   	pop    %rbx
    61e6:	5d                   	pop    %rbp
    61e7:	41 5c                	pop    %r12
    61e9:	41 5d                	pop    %r13
    61eb:	41 5e                	pop    %r14
    61ed:	41 5f                	pop    %r15
    61ef:	c3                   	ret
    61f0:	31 c0                	xor    %eax,%eax
    61f2:	c3                   	ret

Disassembly of section .fini:

00000000000061f4 <_fini>:
    61f4:	f3 0f 1e fa          	endbr64
    61f8:	48 83 ec 08          	sub    $0x8,%rsp
    61fc:	48 83 c4 08          	add    $0x8,%rsp
    6200:	c3                   	ret
