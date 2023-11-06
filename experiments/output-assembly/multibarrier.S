
multibarrier:     file format elf64-x86-64


Disassembly of section .init:

0000000000002000 <_init>:
    2000:	f3 0f 1e fa          	endbr64
    2004:	48 83 ec 08          	sub    $0x8,%rsp
    2008:	48 8b 05 d9 6f 00 00 	mov    0x6fd9(%rip),%rax        # 8fe8 <__gmon_start__@Base>
    200f:	48 85 c0             	test   %rax,%rax
    2012:	74 02                	je     2016 <_init+0x16>
    2014:	ff d0                	call   *%rax
    2016:	48 83 c4 08          	add    $0x8,%rsp
    201a:	c3                   	ret

Disassembly of section .plt:

0000000000002020 <.plt>:
    2020:	ff 35 62 6e 00 00    	push   0x6e62(%rip)        # 8e88 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 64 6e 00 00    	jmp    *0x6e64(%rip)        # 8e90 <_GLOBAL_OFFSET_TABLE_+0x10>
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
    22b4:	ff 25 3e 6d 00 00    	jmp    *0x6d3e(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    22ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

00000000000022c0 <free@plt>:
    22c0:	f3 0f 1e fa          	endbr64
    22c4:	ff 25 ce 6b 00 00    	jmp    *0x6bce(%rip)        # 8e98 <free@GLIBC_2.2.5>
    22ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000022d0 <putchar@plt>:
    22d0:	f3 0f 1e fa          	endbr64
    22d4:	ff 25 c6 6b 00 00    	jmp    *0x6bc6(%rip)        # 8ea0 <putchar@GLIBC_2.2.5>
    22da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000022e0 <pthread_setaffinity_np@plt>:
    22e0:	f3 0f 1e fa          	endbr64
    22e4:	ff 25 be 6b 00 00    	jmp    *0x6bbe(%rip)        # 8ea8 <pthread_setaffinity_np@GLIBC_2.34>
    22ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000022f0 <puts@plt>:
    22f0:	f3 0f 1e fa          	endbr64
    22f4:	ff 25 b6 6b 00 00    	jmp    *0x6bb6(%rip)        # 8eb0 <puts@GLIBC_2.2.5>
    22fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002300 <setsockopt@plt>:
    2300:	f3 0f 1e fa          	endbr64
    2304:	ff 25 ae 6b 00 00    	jmp    *0x6bae(%rip)        # 8eb8 <setsockopt@GLIBC_2.2.5>
    230a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002310 <clock_gettime@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 a6 6b 00 00    	jmp    *0x6ba6(%rip)        # 8ec0 <clock_gettime@GLIBC_2.17>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002320 <strlen@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 9e 6b 00 00    	jmp    *0x6b9e(%rip)        # 8ec8 <strlen@GLIBC_2.2.5>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <__stack_chk_fail@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 96 6b 00 00    	jmp    *0x6b96(%rip)        # 8ed0 <__stack_chk_fail@GLIBC_2.4>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <io_uring_submit@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 8e 6b 00 00    	jmp    *0x6b8e(%rip)        # 8ed8 <io_uring_submit@LIBURING_2.0>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <nanosleep@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 86 6b 00 00    	jmp    *0x6b86(%rip)        # 8ee0 <nanosleep@GLIBC_2.2.5>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <strrchr@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 7e 6b 00 00    	jmp    *0x6b7e(%rip)        # 8ee8 <strrchr@GLIBC_2.2.5>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <close@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 76 6b 00 00    	jmp    *0x6b76(%rip)        # 8ef0 <close@GLIBC_2.2.5>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <strtok_r@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 6e 6b 00 00    	jmp    *0x6b6e(%rip)        # 8ef8 <strtok_r@GLIBC_2.2.5>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <read@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 66 6b 00 00    	jmp    *0x6b66(%rip)        # 8f00 <read@GLIBC_2.2.5>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <calloc@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 5e 6b 00 00    	jmp    *0x6b5e(%rip)        # 8f08 <calloc@GLIBC_2.2.5>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <strcmp@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 56 6b 00 00    	jmp    *0x6b56(%rip)        # 8f10 <strcmp@GLIBC_2.2.5>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <__memcpy_chk@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 4e 6b 00 00    	jmp    *0x6b4e(%rip)        # 8f18 <__memcpy_chk@GLIBC_2.3.4>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <stat@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 46 6b 00 00    	jmp    *0x6b46(%rip)        # 8f20 <stat@GLIBC_2.33>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <memcpy@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 3e 6b 00 00    	jmp    *0x6b3e(%rip)        # 8f28 <memcpy@GLIBC_2.14>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <io_uring_queue_init@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 36 6b 00 00    	jmp    *0x6b36(%rip)        # 8f30 <io_uring_queue_init@LIBURING_2.0>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <eventfd_write@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 2e 6b 00 00    	jmp    *0x6b2e(%rip)        # 8f38 <eventfd_write@GLIBC_2.7>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <malloc@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 26 6b 00 00    	jmp    *0x6b26(%rip)        # 8f40 <malloc@GLIBC_2.2.5>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <listen@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 1e 6b 00 00    	jmp    *0x6b1e(%rip)        # 8f48 <listen@GLIBC_2.2.5>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <__strcpy_chk@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 16 6b 00 00    	jmp    *0x6b16(%rip)        # 8f50 <__strcpy_chk@GLIBC_2.3.4>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <__io_uring_get_cqe@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 0e 6b 00 00    	jmp    *0x6b0e(%rip)        # 8f58 <__io_uring_get_cqe@LIBURING_2.0>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <__printf_chk@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 06 6b 00 00    	jmp    *0x6b06(%rip)        # 8f60 <__printf_chk@GLIBC_2.3.4>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <bind@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 fe 6a 00 00    	jmp    *0x6afe(%rip)        # 8f68 <bind@GLIBC_2.2.5>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <pthread_create@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 f6 6a 00 00    	jmp    *0x6af6(%rip)        # 8f70 <pthread_create@GLIBC_2.34>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <open@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 ee 6a 00 00    	jmp    *0x6aee(%rip)        # 8f78 <open@GLIBC_2.2.5>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <perror@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 e6 6a 00 00    	jmp    *0x6ae6(%rip)        # 8f80 <perror@GLIBC_2.2.5>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <exit@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 de 6a 00 00    	jmp    *0x6ade(%rip)        # 8f88 <exit@GLIBC_2.2.5>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <eventfd@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 d6 6a 00 00    	jmp    *0x6ad6(%rip)        # 8f90 <eventfd@GLIBC_2.7>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <fwrite@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 ce 6a 00 00    	jmp    *0x6ace(%rip)        # 8f98 <fwrite@GLIBC_2.2.5>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <__fprintf_chk@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 c6 6a 00 00    	jmp    *0x6ac6(%rip)        # 8fa0 <__fprintf_chk@GLIBC_2.3.4>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <io_uring_register_eventfd@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 be 6a 00 00    	jmp    *0x6abe(%rip)        # 8fa8 <io_uring_register_eventfd@LIBURING_2.0>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <pthread_join@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 b6 6a 00 00    	jmp    *0x6ab6(%rip)        # 8fb0 <pthread_join@GLIBC_2.34>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <strerror@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 ae 6a 00 00    	jmp    *0x6aae(%rip)        # 8fb8 <strerror@GLIBC_2.2.5>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <__ctype_tolower_loc@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 a6 6a 00 00    	jmp    *0x6aa6(%rip)        # 8fc0 <__ctype_tolower_loc@GLIBC_2.3>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <__sprintf_chk@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 9e 6a 00 00    	jmp    *0x6a9e(%rip)        # 8fc8 <__sprintf_chk@GLIBC_2.3.4>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <socket@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 96 6a 00 00    	jmp    *0x6a96(%rip)        # 8fd0 <socket@GLIBC_2.2.5>
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
    2586:	48 8d 3d 1b 3f 00 00 	lea    0x3f1b(%rip),%rdi        # 64a8 <_IO_stdin_used+0x4a8>
    258d:	41 56                	push   %r14
    258f:	41 55                	push   %r13
    2591:	41 54                	push   %r12
    2593:	55                   	push   %rbp
    2594:	53                   	push   %rbx
    2595:	48 81 ec a8 00 00 00 	sub    $0xa8,%rsp
    259c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    25a5:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
    25ad:	31 c0                	xor    %eax,%eax
    25af:	e8 3c fd ff ff       	call   22f0 <puts@plt>
    25b4:	bf 0a 00 00 00       	mov    $0xa,%edi
    25b9:	e8 12 fd ff ff       	call   22d0 <putchar@plt>
    25be:	48 8d 3d 6d 3c 00 00 	lea    0x3c6d(%rip),%rdi        # 6232 <_IO_stdin_used+0x232>
    25c5:	e8 26 fd ff ff       	call   22f0 <puts@plt>
    25ca:	ba 0c 00 00 00       	mov    $0xc,%edx
    25cf:	48 8d 35 78 3c 00 00 	lea    0x3c78(%rip),%rsi        # 624e <_IO_stdin_used+0x24e>
    25d6:	31 c0                	xor    %eax,%eax
    25d8:	bf 01 00 00 00       	mov    $0x1,%edi
    25dd:	e8 6e fe ff ff       	call   2450 <__printf_chk@plt>
    25e2:	ba 0f 00 00 00       	mov    $0xf,%edx
    25e7:	48 8d 35 7a 3c 00 00 	lea    0x3c7a(%rip),%rsi        # 6268 <_IO_stdin_used+0x268>
    25ee:	31 c0                	xor    %eax,%eax
    25f0:	bf 01 00 00 00       	mov    $0x1,%edi
    25f5:	e8 56 fe ff ff       	call   2450 <__printf_chk@plt>
    25fa:	ba 01 00 00 00       	mov    $0x1,%edx
    25ff:	48 8d 35 76 3c 00 00 	lea    0x3c76(%rip),%rsi        # 627c <_IO_stdin_used+0x27c>
    2606:	31 c0                	xor    %eax,%eax
    2608:	bf 01 00 00 00       	mov    $0x1,%edi
    260d:	e8 3e fe ff ff       	call   2450 <__printf_chk@plt>
    2612:	ba 01 00 00 00       	mov    $0x1,%edx
    2617:	48 8d 35 6f 3c 00 00 	lea    0x3c6f(%rip),%rsi        # 628d <_IO_stdin_used+0x28d>
    261e:	31 c0                	xor    %eax,%eax
    2620:	bf 01 00 00 00       	mov    $0x1,%edi
    2625:	e8 26 fe ff ff       	call   2450 <__printf_chk@plt>
    262a:	ba 01 00 00 00       	mov    $0x1,%edx
    262f:	48 8d 35 6f 3c 00 00 	lea    0x3c6f(%rip),%rsi        # 62a5 <_IO_stdin_used+0x2a5>
    2636:	31 c0                	xor    %eax,%eax
    2638:	bf 01 00 00 00       	mov    $0x1,%edi
    263d:	e8 0e fe ff ff       	call   2450 <__printf_chk@plt>
    2642:	ba 01 00 00 00       	mov    $0x1,%edx
    2647:	48 8d 35 c2 3e 00 00 	lea    0x3ec2(%rip),%rsi        # 6510 <_IO_stdin_used+0x510>
    264e:	31 c0                	xor    %eax,%eax
    2650:	bf 01 00 00 00       	mov    $0x1,%edi
    2655:	e8 f6 fd ff ff       	call   2450 <__printf_chk@plt>
    265a:	ba 01 00 00 00       	mov    $0x1,%edx
    265f:	48 8d 35 da 3e 00 00 	lea    0x3eda(%rip),%rsi        # 6540 <_IO_stdin_used+0x540>
    2666:	31 c0                	xor    %eax,%eax
    2668:	bf 01 00 00 00       	mov    $0x1,%edi
    266d:	e8 de fd ff ff       	call   2450 <__printf_chk@plt>
    2672:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2677:	48 8d 35 43 3c 00 00 	lea    0x3c43(%rip),%rsi        # 62c1 <_IO_stdin_used+0x2c1>
    267e:	31 c0                	xor    %eax,%eax
    2680:	bf 01 00 00 00       	mov    $0x1,%edi
    2685:	e8 c6 fd ff ff       	call   2450 <__printf_chk@plt>
    268a:	ba 05 00 00 00       	mov    $0x5,%edx
    268f:	48 8d 35 45 3c 00 00 	lea    0x3c45(%rip),%rsi        # 62db <_IO_stdin_used+0x2db>
    2696:	31 c0                	xor    %eax,%eax
    2698:	bf 01 00 00 00       	mov    $0x1,%edi
    269d:	e8 ae fd ff ff       	call   2450 <__printf_chk@plt>
    26a2:	48 8d 3d 25 3a 00 00 	lea    0x3a25(%rip),%rdi        # 60ce <_IO_stdin_used+0xce>
    26a9:	e8 42 fc ff ff       	call   22f0 <puts@plt>
    26ae:	be 18 00 00 00       	mov    $0x18,%esi
    26b3:	bf 0c 00 00 00       	mov    $0xc,%edi
    26b8:	e8 e3 fc ff ff       	call   23a0 <calloc@plt>
    26bd:	be 40 01 00 00       	mov    $0x140,%esi
    26c2:	bf 0f 00 00 00       	mov    $0xf,%edi
    26c7:	49 89 c6             	mov    %rax,%r14
    26ca:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    26cf:	e8 cc fc ff ff       	call   23a0 <calloc@plt>
    26d4:	be 10 00 00 00       	mov    $0x10,%esi
    26d9:	bf 01 00 00 00       	mov    $0x1,%edi
    26de:	4d 8d 66 e8          	lea    -0x18(%r14),%r12
    26e2:	48 89 04 24          	mov    %rax,(%rsp)
    26e6:	45 31 f6             	xor    %r14d,%r14d
    26e9:	e8 b2 fc ff ff       	call   23a0 <calloc@plt>
    26ee:	be 10 00 00 00       	mov    $0x10,%esi
    26f3:	bf 01 00 00 00       	mov    $0x1,%edi
    26f8:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    26fe:	48 89 c3             	mov    %rax,%rbx
    2701:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2706:	e8 95 fc ff ff       	call   23a0 <calloc@plt>
    270b:	4c 8b 1c 24          	mov    (%rsp),%r11
    270f:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
    2717:	48 89 43 08          	mov    %rax,0x8(%rbx)
    271b:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    2722:	4d 89 df             	mov    %r11,%r15
    2725:	4c 89 5c 24 38       	mov    %r11,0x38(%rsp)
    272a:	4c 89 5c 24 48       	mov    %r11,0x48(%rsp)
    272f:	90                   	nop
    2730:	be 08 00 00 00       	mov    $0x8,%esi
    2735:	bf 02 00 00 00       	mov    $0x2,%edi
    273a:	44 89 f5             	mov    %r14d,%ebp
    273d:	e8 5e fc ff ff       	call   23a0 <calloc@plt>
    2742:	be 80 00 00 00       	mov    $0x80,%esi
    2747:	bf 01 00 00 00       	mov    $0x1,%edi
    274c:	48 89 04 24          	mov    %rax,(%rsp)
    2750:	e8 4b fc ff ff       	call   23a0 <calloc@plt>
    2755:	48 89 c3             	mov    %rax,%rbx
    2758:	44 89 f0             	mov    %r14d,%eax
    275b:	41 83 c6 01          	add    $0x1,%r14d
    275f:	83 e0 01             	and    $0x1,%eax
    2762:	85 c0                	test   %eax,%eax
    2764:	0f 84 c9 0e 00 00    	je     3633 <main+0x10b3>
    276a:	48 8b 04 24          	mov    (%rsp),%rax
    276e:	49 8d 8f c0 fe ff ff 	lea    -0x140(%r15),%rcx
    2775:	4d 89 f8             	mov    %r15,%r8
    2778:	89 ea                	mov    %ebp,%edx
    277a:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
    2781:	48 8d 35 67 3b 00 00 	lea    0x3b67(%rip),%rsi        # 62ef <_IO_stdin_used+0x2ef>
    2788:	bf 01 00 00 00       	mov    $0x1,%edi
    278d:	44 8d 6d ff          	lea    -0x1(%rbp),%r13d
    2791:	48 89 08             	mov    %rcx,(%rax)
    2794:	4c 89 78 08          	mov    %r15,0x8(%rax)
    2798:	31 c0                	xor    %eax,%eax
    279a:	e8 b1 fc ff ff       	call   2450 <__printf_chk@plt>
    279f:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    27a4:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    27a9:	4d 89 a7 80 00 00 00 	mov    %r12,0x80(%r15)
    27b0:	45 8b 07             	mov    (%r15),%r8d
    27b3:	44 89 e9             	mov    %r13d,%ecx
    27b6:	89 ea                	mov    %ebp,%edx
    27b8:	48 8d 35 a9 3d 00 00 	lea    0x3da9(%rip),%rsi        # 6568 <_IO_stdin_used+0x568>
    27bf:	bf 01 00 00 00       	mov    $0x1,%edi
    27c4:	31 c0                	xor    %eax,%eax
    27c6:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    27cc:	e8 7f fc ff ff       	call   2450 <__printf_chk@plt>
    27d1:	45 89 af 28 01 00 00 	mov    %r13d,0x128(%r15)
    27d8:	45 31 ed             	xor    %r13d,%r13d
    27db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    27e0:	44 89 e9             	mov    %r13d,%ecx
    27e3:	89 ea                	mov    %ebp,%edx
    27e5:	48 8d 35 ac 3d 00 00 	lea    0x3dac(%rip),%rsi        # 6598 <_IO_stdin_used+0x598>
    27ec:	31 c0                	xor    %eax,%eax
    27ee:	bf 01 00 00 00       	mov    $0x1,%edi
    27f3:	e8 58 fc ff ff       	call   2450 <__printf_chk@plt>
    27f8:	44 89 e9             	mov    %r13d,%ecx
    27fb:	4c 89 e0             	mov    %r12,%rax
    27fe:	41 83 c5 01          	add    $0x1,%r13d
    2802:	48 d3 e0             	shl    %cl,%rax
    2805:	48 09 03             	or     %rax,(%rbx)
    2808:	41 83 fd 06          	cmp    $0x6,%r13d
    280c:	75 d2                	jne    27e0 <main+0x260>
    280e:	48 8b 04 24          	mov    (%rsp),%rax
    2812:	49 89 9f 20 01 00 00 	mov    %rbx,0x120(%r15)
    2819:	31 db                	xor    %ebx,%ebx
    281b:	be 10 00 00 00       	mov    $0x10,%esi
    2820:	41 89 6f 04          	mov    %ebp,0x4(%r15)
    2824:	bf 64 00 00 00       	mov    $0x64,%edi
    2829:	49 89 47 40          	mov    %rax,0x40(%r15)
    282d:	48 8b 05 04 42 00 00 	mov    0x4204(%rip),%rax        # 6a38 <_IO_stdin_used+0xa38>
    2834:	41 c7 47 60 03 00 00 00 	movl   $0x3,0x60(%r15)
    283c:	49 89 47 48          	mov    %rax,0x48(%r15)
    2840:	e8 5b fb ff ff       	call   23a0 <calloc@plt>
    2845:	be 10 00 00 00       	mov    $0x10,%esi
    284a:	bf 64 00 00 00       	mov    $0x64,%edi
    284f:	49 89 87 d8 00 00 00 	mov    %rax,0xd8(%r15)
    2856:	e8 45 fb ff ff       	call   23a0 <calloc@plt>
    285b:	be 28 00 00 00       	mov    $0x28,%esi
    2860:	bf 64 00 00 00       	mov    $0x64,%edi
    2865:	66 0f 6f 05 b3 41 00 00 	movdqa 0x41b3(%rip),%xmm0        # 6a20 <_IO_stdin_used+0xa20>
    286d:	49 89 87 e0 00 00 00 	mov    %rax,0xe0(%r15)
    2874:	41 0f 29 87 f0 00 00 00 	movaps %xmm0,0xf0(%r15)
    287c:	e8 1f fb ff ff       	call   23a0 <calloc@plt>
    2881:	be 00 01 00 00       	mov    $0x100,%esi
    2886:	bf 03 00 00 00       	mov    $0x3,%edi
    288b:	66 0f 6f 0d 8d 41 00 00 	movdqa 0x418d(%rip),%xmm1        # 6a20 <_IO_stdin_used+0xa20>
    2893:	49 89 87 00 01 00 00 	mov    %rax,0x100(%r15)
    289a:	41 0f 11 8f 08 01 00 00 	movups %xmm1,0x108(%r15)
    28a2:	e8 f9 fa ff ff       	call   23a0 <calloc@plt>
    28a7:	44 89 74 24 20       	mov    %r14d,0x20(%rsp)
    28ac:	49 89 47 58          	mov    %rax,0x58(%r15)
    28b0:	48 89 c2             	mov    %rax,%rdx
    28b3:	4c 63 f3             	movslq %ebx,%r14
    28b6:	be 20 00 00 00       	mov    $0x20,%esi
    28bb:	bf 0c 00 00 00       	mov    $0xc,%edi
    28c0:	4d 89 f5             	mov    %r14,%r13
    28c3:	48 8d 05 d6 0e 00 00 	lea    0xed6(%rip),%rax        # 37a0 <do_protected_write>
    28ca:	49 c1 e5 08          	shl    $0x8,%r13
    28ce:	4e 8d 24 2a          	lea    (%rdx,%r13,1),%r12
    28d2:	49 89 44 24 60       	mov    %rax,0x60(%r12)
    28d7:	e8 c4 fa ff ff       	call   23a0 <calloc@plt>
    28dc:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    28e0:	49 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%r12)
    28e8:	49 89 c4             	mov    %rax,%r12
    28eb:	48 8d 40 40          	lea    0x40(%rax),%rax
    28ef:	48 89 04 24          	mov    %rax,(%rsp)
    28f3:	89 6c 24 10          	mov    %ebp,0x10(%rsp)
    28f7:	be 08 00 00 00       	mov    $0x8,%esi
    28fc:	bf 01 00 00 00       	mov    $0x1,%edi
    2901:	49 83 c4 20          	add    $0x20,%r12
    2905:	e8 96 fa ff ff       	call   23a0 <calloc@plt>
    290a:	be 08 00 00 00       	mov    $0x8,%esi
    290f:	bf 01 00 00 00       	mov    $0x1,%edi
    2914:	48 89 c5             	mov    %rax,%rbp
    2917:	e8 84 fa ff ff       	call   23a0 <calloc@plt>
    291c:	be 18 00 00 00       	mov    $0x18,%esi
    2921:	bf 02 00 00 00       	mov    $0x2,%edi
    2926:	48 89 c3             	mov    %rax,%rbx
    2929:	e8 72 fa ff ff       	call   23a0 <calloc@plt>
    292e:	48 8d 70 18          	lea    0x18(%rax),%rsi
    2932:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    293a:	49 89 44 24 e0       	mov    %rax,-0x20(%r12)
    293f:	49 89 74 24 e8       	mov    %rsi,-0x18(%r12)
    2944:	48 89 28             	mov    %rbp,(%rax)
    2947:	48 89 58 18          	mov    %rbx,0x18(%rax)
    294b:	48 c7 40 10 01 00 00 00 	movq   $0x1,0x10(%rax)
    2953:	48 c7 40 20 00 00 00 00 	movq   $0x0,0x20(%rax)
    295b:	48 c7 40 28 01 00 00 00 	movq   $0x1,0x28(%rax)
    2963:	4c 39 24 24          	cmp    %r12,(%rsp)
    2967:	75 8e                	jne    28f7 <main+0x377>
    2969:	be 01 00 00 00       	mov    $0x1,%esi
    296e:	bf 00 01 00 00       	mov    $0x100,%edi
    2973:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2977:	8b 6c 24 10          	mov    0x10(%rsp),%ebp
    297b:	e8 20 fa ff ff       	call   23a0 <calloc@plt>
    2980:	bf 18 00 00 00       	mov    $0x18,%edi
    2985:	49 89 c4             	mov    %rax,%r12
    2988:	e8 83 fa ff ff       	call   2410 <malloc@plt>
    298d:	4c 89 e7             	mov    %r12,%rdi
    2990:	41 89 d9             	mov    %ebx,%r9d
    2993:	41 89 e8             	mov    %ebp,%r8d
    2996:	48 8d 0d 1b 3c 00 00 	lea    0x3c1b(%rip),%rcx        # 65b8 <_IO_stdin_used+0x5b8>
    299d:	48 89 04 24          	mov    %rax,(%rsp)
    29a1:	ba 00 01 00 00       	mov    $0x100,%edx
    29a6:	31 c0                	xor    %eax,%eax
    29a8:	be 01 00 00 00       	mov    $0x1,%esi
    29ad:	e8 6e fb ff ff       	call   2520 <__sprintf_chk@plt>
    29b2:	49 8b 57 58          	mov    0x58(%r15),%rdx
    29b6:	4c 8b 14 24          	mov    (%rsp),%r10
    29ba:	be 20 00 00 00       	mov    $0x20,%esi
    29bf:	49 63 07             	movslq (%r15),%rax
    29c2:	4d 89 22             	mov    %r12,(%r10)
    29c5:	4e 8d 24 2a          	lea    (%rdx,%r13,1),%r12
    29c9:	4d 89 72 10          	mov    %r14,0x10(%r10)
    29cd:	44 8d 73 01          	lea    0x1(%rbx),%r14d
    29d1:	49 89 42 08          	mov    %rax,0x8(%r10)
    29d5:	45 89 b4 24 c8 00 00 00 	mov    %r14d,0xc8(%r12)
    29dd:	4d 89 94 24 c0 00 00 00 	mov    %r10,0xc0(%r12)
    29e5:	41 c7 84 24 b8 00 00 00 01 00 00 00 	movl   $0x1,0xb8(%r12)
    29f1:	49 c7 84 24 90 00 00 00 63 00 00 00 	movq   $0x63,0x90(%r12)
    29fd:	49 8b bc 24 90 00 00 00 	mov    0x90(%r12),%rdi
    2a05:	48 89 14 24          	mov    %rdx,(%rsp)
    2a09:	89 44 24 08          	mov    %eax,0x8(%rsp)
    2a0d:	e8 8e f9 ff ff       	call   23a0 <calloc@plt>
    2a12:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2a16:	83 fb 01             	cmp    $0x1,%ebx
    2a19:	48 8b 14 24          	mov    (%rsp),%rdx
    2a1d:	49 89 84 24 88 00 00 00 	mov    %rax,0x88(%r12)
    2a25:	49 c7 84 24 98 00 00 00 00 00 00 00 	movq   $0x0,0x98(%r12)
    2a31:	41 89 4c 24 70       	mov    %ecx,0x70(%r12)
    2a36:	4d 89 7c 24 68       	mov    %r15,0x68(%r12)
    2a3b:	41 c7 44 24 78 01 00 00 00 	movl   $0x1,0x78(%r12)
    2a44:	41 c7 44 24 40 00 00 00 00 	movl   $0x0,0x40(%r12)
    2a4d:	41 c7 44 24 74 02 00 00 00 	movl   $0x2,0x74(%r12)
    2a56:	41 c7 44 24 7c 03 00 00 00 	movl   $0x3,0x7c(%r12)
    2a5f:	41 c7 84 24 bc 00 00 00 0c 00 00 00 	movl   $0xc,0xbc(%r12)
    2a6b:	41 89 1c 24          	mov    %ebx,(%r12)
    2a6f:	0f 84 a8 0b 00 00    	je     361d <main+0x109d>
    2a75:	39 dd                	cmp    %ebx,%ebp
    2a77:	75 57                	jne    2ad0 <main+0x550>
    2a79:	8b 4c 24 18          	mov    0x18(%rsp),%ecx
    2a7d:	85 c9                	test   %ecx,%ecx
    2a7f:	75 4f                	jne    2ad0 <main+0x550>
    2a81:	89 ea                	mov    %ebp,%edx
    2a83:	48 8d 35 56 3b 00 00 	lea    0x3b56(%rip),%rsi        # 65e0 <_IO_stdin_used+0x5e0>
    2a8a:	bf 01 00 00 00       	mov    $0x1,%edi
    2a8f:	31 c0                	xor    %eax,%eax
    2a91:	e8 ba f9 ff ff       	call   2450 <__printf_chk@plt>
    2a96:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    2a9b:	49 8b 57 58          	mov    0x58(%r15),%rdx
    2a9f:	c7 44 24 18 01 00 00 00 	movl   $0x1,0x18(%rsp)
    2aa7:	49 89 87 c0 00 00 00 	mov    %rax,0xc0(%r15)
    2aae:	49 01 d5             	add    %rdx,%r13
    2ab1:	48 8d 05 88 2f 00 00 	lea    0x2f88(%rip),%rax        # 5a40 <barriered_work_ingest>
    2ab8:	49 89 45 58          	mov    %rax,0x58(%r13)
    2abc:	41 83 fe 03          	cmp    $0x3,%r14d
    2ac0:	74 20                	je     2ae2 <main+0x562>
    2ac2:	bb 01 00 00 00       	mov    $0x1,%ebx
    2ac7:	e9 e7 fd ff ff       	jmp    28b3 <main+0x333>
    2acc:	0f 1f 40 00          	nopl   0x0(%rax)
    2ad0:	48 8d 05 49 2c 00 00 	lea    0x2c49(%rip),%rax        # 5720 <barriered_work>
    2ad7:	49 89 44 24 58       	mov    %rax,0x58(%r12)
    2adc:	41 83 fe 03          	cmp    $0x3,%r14d
    2ae0:	75 e0                	jne    2ac2 <main+0x542>
    2ae2:	48 8d 05 b7 0c 00 00 	lea    0xcb7(%rip),%rax        # 37a0 <do_protected_write>
    2ae9:	44 8b 74 24 20       	mov    0x20(%rsp),%r14d
    2aee:	4c 8b 64 24 28       	mov    0x28(%rsp),%r12
    2af3:	48 89 82 60 02 00 00 	mov    %rax,0x260(%rdx)
    2afa:	48 8d 05 df 0c 00 00 	lea    0xcdf(%rip),%rax        # 37e0 <barriered_reset>
    2b01:	48 89 82 58 02 00 00 	mov    %rax,0x258(%rdx)
    2b08:	4c 89 ba 68 02 00 00 	mov    %r15,0x268(%rdx)
    2b0f:	49 81 c7 40 01 00 00 	add    $0x140,%r15
    2b16:	c7 82 78 02 00 00 01 00 00 00 	movl   $0x1,0x278(%rdx)
    2b20:	c7 82 40 02 00 00 00 00 00 00 	movl   $0x0,0x240(%rdx)
    2b2a:	c7 82 00 02 00 00 02 00 00 00 	movl   $0x2,0x200(%rdx)
    2b34:	c7 82 74 02 00 00 02 00 00 00 	movl   $0x2,0x274(%rdx)
    2b3e:	41 8b 87 c0 fe ff ff 	mov    -0x140(%r15),%eax
    2b45:	89 82 70 02 00 00    	mov    %eax,0x270(%rdx)
    2b4b:	c7 82 bc 02 00 00 0c 00 00 00 	movl   $0xc,0x2bc(%rdx)
    2b55:	c7 82 7c 02 00 00 03 00 00 00 	movl   $0x3,0x27c(%rdx)
    2b5f:	41 83 fe 0f          	cmp    $0xf,%r14d
    2b63:	0f 85 c7 fb ff ff    	jne    2730 <main+0x1b0>
    2b69:	4c 8b 5c 24 38       	mov    0x38(%rsp),%r11
    2b6e:	ba 0d 00 00 00       	mov    $0xd,%edx
    2b73:	48 8d 35 92 37 00 00 	lea    0x3792(%rip),%rsi        # 630c <_IO_stdin_used+0x30c>
    2b7a:	31 c0                	xor    %eax,%eax
    2b7c:	bf 01 00 00 00       	mov    $0x1,%edi
    2b81:	48 8b 6c 24 48       	mov    0x48(%rsp),%rbp
    2b86:	4c 89 1c 24          	mov    %r11,(%rsp)
    2b8a:	e8 c1 f8 ff ff       	call   2450 <__printf_chk@plt>
    2b8f:	be 08 00 00 00       	mov    $0x8,%esi
    2b94:	bf 02 00 00 00       	mov    $0x2,%edi
    2b99:	e8 02 f8 ff ff       	call   23a0 <calloc@plt>
    2b9e:	4c 8b 1c 24          	mov    (%rsp),%r11
    2ba2:	bf 0f 00 00 00       	mov    $0xf,%edi
    2ba7:	4d 8d bb 40 10 00 00 	lea    0x1040(%r11),%r15
    2bae:	4d 8d b3 80 02 00 00 	lea    0x280(%r11),%r14
    2bb5:	49 89 83 80 10 00 00 	mov    %rax,0x1080(%r11)
    2bbc:	4c 89 38             	mov    %r15,(%rax)
    2bbf:	49 8d 93 00 05 00 00 	lea    0x500(%r11),%rdx
    2bc6:	49 8d 8b 80 07 00 00 	lea    0x780(%r11),%rcx
    2bcd:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2bd1:	49 8b 43 58          	mov    0x58(%r11),%rax
    2bd5:	4d 8d 8b c0 08 00 00 	lea    0x8c0(%r11),%r9
    2bdc:	4d 8d 93 00 0a 00 00 	lea    0xa00(%r11),%r10
    2be3:	49 8d b3 c0 03 00 00 	lea    0x3c0(%r11),%rsi
    2bea:	49 8d 9b 40 06 00 00 	lea    0x640(%r11),%rbx
    2bf1:	41 c7 83 88 10 00 00 02 00 00 00 	movl   $0x2,0x1088(%r11)
    2bfc:	48 89 54 24 50       	mov    %rdx,0x50(%rsp)
    2c01:	4d 8d 83 40 0b 00 00 	lea    0xb40(%r11),%r8
    2c08:	4d 8d ab 80 0c 00 00 	lea    0xc80(%r11),%r13
    2c0f:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    2c14:	4d 8d a3 c0 0d 00 00 	lea    0xdc0(%r11),%r12
    2c1b:	41 c7 83 40 10 00 00 00 00 00 00 	movl   $0x0,0x1040(%r11)
    2c26:	41 c7 83 a0 10 00 00 03 00 00 00 	movl   $0x3,0x10a0(%r11)
    2c31:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    2c3b:	49 8d 83 40 01 00 00 	lea    0x140(%r11),%rax
    2c42:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2c47:	49 8b 83 98 01 00 00 	mov    0x198(%r11),%rax
    2c4e:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2c53:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    2c5d:	49 8b 83 d8 02 00 00 	mov    0x2d8(%r11),%rax
    2c64:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    2c69:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    2c73:	49 8b 83 18 04 00 00 	mov    0x418(%r11),%rax
    2c7a:	4c 89 7c 24 60       	mov    %r15,0x60(%rsp)
    2c7f:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    2c89:	49 8b 83 58 05 00 00 	mov    0x558(%r11),%rax
    2c90:	4c 89 74 24 68       	mov    %r14,0x68(%rsp)
    2c95:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    2c9f:	49 8b 83 98 06 00 00 	mov    0x698(%r11),%rax
    2ca6:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
    2cab:	be 38 00 00 00       	mov    $0x38,%esi
    2cb0:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    2cba:	49 8b 83 d8 07 00 00 	mov    0x7d8(%r11),%rax
    2cc1:	48 89 5c 24 58       	mov    %rbx,0x58(%rsp)
    2cc6:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    2cd0:	49 8b 83 18 09 00 00 	mov    0x918(%r11),%rax
    2cd7:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    2ce1:	49 8b 83 58 0a 00 00 	mov    0xa58(%r11),%rax
    2ce8:	4c 89 44 24 20       	mov    %r8,0x20(%rsp)
    2ced:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    2cf7:	49 8b 83 98 0b 00 00 	mov    0xb98(%r11),%rax
    2cfe:	4c 89 5c 24 70       	mov    %r11,0x70(%rsp)
    2d03:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    2d0d:	49 8b 83 d8 0c 00 00 	mov    0xcd8(%r11),%rax
    2d14:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    2d19:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    2d23:	49 8b 83 18 0e 00 00 	mov    0xe18(%r11),%rax
    2d2a:	4c 89 24 24          	mov    %r12,(%rsp)
    2d2e:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    2d38:	e8 63 f6 ff ff       	call   23a0 <calloc@plt>
    2d3d:	be 38 00 00 00       	mov    $0x38,%esi
    2d42:	bf 0f 00 00 00       	mov    $0xf,%edi
    2d47:	49 89 c4             	mov    %rax,%r12
    2d4a:	e8 51 f6 ff ff       	call   23a0 <calloc@plt>
    2d4f:	be 38 00 00 00       	mov    $0x38,%esi
    2d54:	bf 0f 00 00 00       	mov    $0xf,%edi
    2d59:	48 89 c3             	mov    %rax,%rbx
    2d5c:	e8 3f f6 ff ff       	call   23a0 <calloc@plt>
    2d61:	be 38 00 00 00       	mov    $0x38,%esi
    2d66:	bf 0f 00 00 00       	mov    $0xf,%edi
    2d6b:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    2d70:	e8 2b f6 ff ff       	call   23a0 <calloc@plt>
    2d75:	be 08 00 00 00       	mov    $0x8,%esi
    2d7a:	bf 0f 00 00 00       	mov    $0xf,%edi
    2d7f:	48 89 84 24 80 00 00 00 	mov    %rax,0x80(%rsp)
    2d87:	e8 14 f6 ff ff       	call   23a0 <calloc@plt>
    2d8c:	4c 8b 5c 24 70       	mov    0x70(%rsp),%r11
    2d91:	be 08 00 00 00       	mov    $0x8,%esi
    2d96:	bf 0f 00 00 00       	mov    $0xf,%edi
    2d9b:	49 89 c5             	mov    %rax,%r13
    2d9e:	41 c7 83 08 0f 00 00 00 00 00 00 	movl   $0x0,0xf08(%r11)
    2da9:	41 c7 83 64 0f 00 00 01 00 00 00 	movl   $0x1,0xf64(%r11)
    2db4:	41 c7 83 60 0f 00 00 03 00 00 00 	movl   $0x3,0xf60(%r11)
    2dbf:	e8 dc f5 ff ff       	call   23a0 <calloc@plt>
    2dc4:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    2dc9:	4c 8b 5c 24 70       	mov    0x70(%rsp),%r11
    2dce:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    2dd3:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
    2dd8:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2ddc:	48 89 78 08          	mov    %rdi,0x8(%rax)
    2de0:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
    2de5:	4d 8d b3 00 0f 00 00 	lea    0xf00(%r11),%r14
    2dec:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    2df1:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2df6:	4c 89 18             	mov    %r11,(%rax)
    2df9:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    2dfe:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    2e03:	48 89 78 28          	mov    %rdi,0x28(%rax)
    2e07:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    2e0c:	48 89 70 18          	mov    %rsi,0x18(%rax)
    2e10:	48 8d 35 04 35 00 00 	lea    0x3504(%rip),%rsi        # 631b <_IO_stdin_used+0x31b>
    2e17:	48 89 50 20          	mov    %rdx,0x20(%rax)
    2e1b:	ba 0c 00 00 00       	mov    $0xc,%edx
    2e20:	48 89 78 50          	mov    %rdi,0x50(%rax)
    2e24:	48 8b 3c 24          	mov    (%rsp),%rdi
    2e28:	48 89 48 30          	mov    %rcx,0x30(%rax)
    2e2c:	48 89 78 58          	mov    %rdi,0x58(%rax)
    2e30:	49 8d bb 80 11 00 00 	lea    0x1180(%r11),%rdi
    2e37:	4c 89 48 38          	mov    %r9,0x38(%rax)
    2e3b:	4c 89 50 40          	mov    %r10,0x40(%rax)
    2e3f:	4c 89 40 48          	mov    %r8,0x48(%rax)
    2e43:	4c 89 70 60          	mov    %r14,0x60(%rax)
    2e47:	4c 89 78 68          	mov    %r15,0x68(%rax)
    2e4b:	4c 8d 3d ee 09 00 00 	lea    0x9ee(%rip),%r15        # 3840 <barriered_thread>
    2e52:	48 89 78 70          	mov    %rdi,0x70(%rax)
    2e56:	49 89 83 40 0f 00 00 	mov    %rax,0xf40(%r11)
    2e5d:	31 c0                	xor    %eax,%eax
    2e5f:	41 c7 83 48 0f 00 00 0c 00 00 00 	movl   $0xc,0xf48(%r11)
    2e6a:	41 c7 83 50 0f 00 00 02 00 00 00 	movl   $0x2,0xf50(%r11)
    2e75:	41 c7 83 00 0f 00 00 00 00 00 00 	movl   $0x0,0xf00(%r11)
    2e80:	48 89 7c 24 70       	mov    %rdi,0x70(%rsp)
    2e85:	bf 01 00 00 00       	mov    $0x1,%edi
    2e8a:	4c 89 9c 24 88 00 00 00 	mov    %r11,0x88(%rsp)
    2e92:	e8 b9 f5 ff ff       	call   2450 <__printf_chk@plt>
    2e97:	48 8d b3 a0 02 00 00 	lea    0x2a0(%rbx),%rsi
    2e9e:	49 8d 7d 60          	lea    0x60(%r13),%rdi
    2ea2:	4c 89 f1             	mov    %r14,%rcx
    2ea5:	4c 89 eb             	mov    %r13,%rbx
    2ea8:	45 31 f6             	xor    %r14d,%r14d
    2eab:	48 8d 15 ee 0c 00 00 	lea    0xcee(%rip),%rdx        # 3ba0 <timer_thread>
    2eb2:	e8 b9 f5 ff ff       	call   2470 <pthread_create@plt>
    2eb7:	45 89 f5             	mov    %r14d,%r13d
    2eba:	49 89 de             	mov    %rbx,%r14
    2ebd:	c7 45 08 01 00 00 00 	movl   $0x1,0x8(%rbp)
    2ec4:	44 89 ea             	mov    %r13d,%edx
    2ec7:	bf 01 00 00 00       	mov    $0x1,%edi
    2ecc:	31 c0                	xor    %eax,%eax
    2ece:	c7 45 64 01 00 00 00 	movl   $0x1,0x64(%rbp)
    2ed5:	48 8d 35 24 37 00 00 	lea    0x3724(%rip),%rsi        # 6600 <_IO_stdin_used+0x600>
    2edc:	41 83 c5 01          	add    $0x1,%r13d
    2ee0:	e8 6b f5 ff ff       	call   2450 <__printf_chk@plt>
    2ee5:	48 89 e9             	mov    %rbp,%rcx
    2ee8:	4c 89 e6             	mov    %r12,%rsi
    2eeb:	48 89 df             	mov    %rbx,%rdi
    2eee:	4c 89 fa             	mov    %r15,%rdx
    2ef1:	48 81 c5 40 01 00 00 	add    $0x140,%rbp
    2ef8:	48 83 c3 08          	add    $0x8,%rbx
    2efc:	49 83 c4 38          	add    $0x38,%r12
    2f00:	e8 6b f5 ff ff       	call   2470 <pthread_create@plt>
    2f05:	48 8b 55 e0          	mov    -0x20(%rbp),%rdx
    2f09:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    2f0d:	be 08 00 00 00       	mov    $0x8,%esi
    2f12:	e8 c9 f3 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    2f17:	41 83 fd 0c          	cmp    $0xc,%r13d
    2f1b:	75 a0                	jne    2ebd <main+0x93d>
    2f1d:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    2f25:	be d8 00 00 00       	mov    $0xd8,%esi
    2f2a:	bf 01 00 00 00       	mov    $0x1,%edi
    2f2f:	4d 89 f5             	mov    %r14,%r13
    2f32:	41 c7 83 48 10 00 00 02 00 00 00 	movl   $0x2,0x1048(%r11)
    2f3d:	41 c7 83 a4 10 00 00 01 00 00 00 	movl   $0x1,0x10a4(%r11)
    2f48:	41 c7 83 a0 10 00 00 00 00 00 00 	movl   $0x0,0x10a0(%r11)
    2f53:	e8 48 f4 ff ff       	call   23a0 <calloc@plt>
    2f58:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    2f60:	be 00 08 00 00       	mov    $0x800,%esi
    2f65:	31 ff                	xor    %edi,%edi
    2f67:	49 89 83 08 11 00 00 	mov    %rax,0x1108(%r11)
    2f6e:	e8 3d f5 ff ff       	call   24b0 <eventfd@plt>
    2f73:	be 08 00 00 00       	mov    $0x8,%esi
    2f78:	bf 0c 00 00 00       	mov    $0xc,%edi
    2f7d:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    2f85:	41 89 83 10 11 00 00 	mov    %eax,0x1110(%r11)
    2f8c:	e8 0f f4 ff ff       	call   23a0 <calloc@plt>
    2f91:	4c 8b 4c 24 28       	mov    0x28(%rsp),%r9
    2f96:	4c 8b 14 24          	mov    (%rsp),%r10
    2f9a:	4c 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%r11
    2fa2:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    2fa7:	4c 8b 74 24 68       	mov    0x68(%rsp),%r14
    2fac:	48 8b 6c 24 50       	mov    0x50(%rsp),%rbp
    2fb1:	4c 89 48 50          	mov    %r9,0x50(%rax)
    2fb5:	4c 8b 64 24 58       	mov    0x58(%rsp),%r12
    2fba:	4c 8b 7c 24 48       	mov    0x48(%rsp),%r15
    2fbf:	4c 89 50 58          	mov    %r10,0x58(%rax)
    2fc3:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    2fc8:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    2fcd:	4c 89 18             	mov    %r11,(%rax)
    2fd0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    2fd5:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    2fda:	49 89 83 80 10 00 00 	mov    %rax,0x1080(%r11)
    2fe1:	41 c7 83 88 10 00 00 0c 00 00 00 	movl   $0xc,0x1088(%r11)
    2fec:	41 c7 83 40 10 00 00 0d 00 00 00 	movl   $0xd,0x1040(%r11)
    2ff7:	48 89 58 08          	mov    %rbx,0x8(%rax)
    2ffb:	4c 89 70 10          	mov    %r14,0x10(%rax)
    2fff:	48 89 68 20          	mov    %rbp,0x20(%rax)
    3003:	4c 89 60 28          	mov    %r12,0x28(%rax)
    3007:	48 89 78 30          	mov    %rdi,0x30(%rax)
    300b:	bf 01 00 00 00       	mov    $0x1,%edi
    3010:	48 89 70 38          	mov    %rsi,0x38(%rax)
    3014:	48 8d 35 1e 33 00 00 	lea    0x331e(%rip),%rsi        # 6339 <_IO_stdin_used+0x339>
    301b:	48 89 50 40          	mov    %rdx,0x40(%rax)
    301f:	ba 0d 00 00 00       	mov    $0xd,%edx
    3024:	48 89 48 48          	mov    %rcx,0x48(%rax)
    3028:	4c 89 78 18          	mov    %r15,0x18(%rax)
    302c:	31 c0                	xor    %eax,%eax
    302e:	4c 89 5c 24 38       	mov    %r11,0x38(%rsp)
    3033:	e8 18 f4 ff ff       	call   2450 <__printf_chk@plt>
    3038:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    303d:	49 8d 7d 68          	lea    0x68(%r13),%rdi
    3041:	48 8b 4c 24 60       	mov    0x60(%rsp),%rcx
    3046:	48 8d 15 f3 1d 00 00 	lea    0x1df3(%rip),%rdx        # 4e40 <io_thread>
    304d:	48 05 d8 02 00 00    	add    $0x2d8,%rax
    3053:	48 89 c6             	mov    %rax,%rsi
    3056:	e8 15 f4 ff ff       	call   2470 <pthread_create@plt>
    305b:	ba 0e 00 00 00       	mov    $0xe,%edx
    3060:	48 8d 35 e9 32 00 00 	lea    0x32e9(%rip),%rsi        # 6350 <_IO_stdin_used+0x350>
    3067:	31 c0                	xor    %eax,%eax
    3069:	bf 01 00 00 00       	mov    $0x1,%edi
    306e:	e8 dd f3 ff ff       	call   2450 <__printf_chk@plt>
    3073:	4c 8b 5c 24 38       	mov    0x38(%rsp),%r11
    3078:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    307d:	be 08 00 00 00       	mov    $0x8,%esi
    3082:	bf 0c 00 00 00       	mov    $0xc,%edi
    3087:	41 c7 83 88 11 00 00 03 00 00 00 	movl   $0x3,0x1188(%r11)
    3092:	41 c7 83 e4 11 00 00 01 00 00 00 	movl   $0x1,0x11e4(%r11)
    309d:	41 c7 83 e0 11 00 00 00 00 00 00 	movl   $0x0,0x11e0(%r11)
    30a8:	49 89 83 40 12 00 00 	mov    %rax,0x1240(%r11)
    30af:	4c 89 5c 24 30       	mov    %r11,0x30(%rsp)
    30b4:	e8 e7 f2 ff ff       	call   23a0 <calloc@plt>
    30b9:	4c 8b 5c 24 30       	mov    0x30(%rsp),%r11
    30be:	4c 8b 14 24          	mov    (%rsp),%r10
    30c2:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    30c7:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    30cc:	48 89 58 08          	mov    %rbx,0x8(%rax)
    30d0:	31 db                	xor    %ebx,%ebx
    30d2:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    30d7:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    30dc:	4c 89 18             	mov    %r11,(%rax)
    30df:	4c 8b 4c 24 28       	mov    0x28(%rsp),%r9
    30e4:	4c 89 70 10          	mov    %r14,0x10(%rax)
    30e8:	48 89 68 20          	mov    %rbp,0x20(%rax)
    30ec:	48 8d 2d 98 32 00 00 	lea    0x3298(%rip),%rbp        # 638b <_IO_stdin_used+0x38b>
    30f3:	4c 89 60 28          	mov    %r12,0x28(%rax)
    30f7:	4c 8d a4 24 90 00 00 00 	lea    0x90(%rsp),%r12
    30ff:	48 89 78 30          	mov    %rdi,0x30(%rax)
    3103:	49 8d 7d 70          	lea    0x70(%r13),%rdi
    3107:	48 89 70 38          	mov    %rsi,0x38(%rax)
    310b:	48 8b b4 24 80 00 00 00 	mov    0x80(%rsp),%rsi
    3113:	48 89 50 40          	mov    %rdx,0x40(%rax)
    3117:	48 8d 15 c2 09 00 00 	lea    0x9c2(%rip),%rdx        # 3ae0 <external_thread>
    311e:	48 89 48 48          	mov    %rcx,0x48(%rax)
    3122:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    3127:	48 81 c6 10 03 00 00 	add    $0x310,%rsi
    312e:	4c 89 48 50          	mov    %r9,0x50(%rax)
    3132:	4c 89 50 58          	mov    %r10,0x58(%rax)
    3136:	49 89 83 c0 11 00 00 	mov    %rax,0x11c0(%r11)
    313d:	4c 89 78 18          	mov    %r15,0x18(%rax)
    3141:	48 8b 05 f8 38 00 00 	mov    0x38f8(%rip),%rax        # 6a40 <_IO_stdin_used+0xa40>
    3148:	41 c7 83 80 11 00 00 0e 00 00 00 	movl   $0xe,0x1180(%r11)
    3153:	49 89 83 c8 11 00 00 	mov    %rax,0x11c8(%r11)
    315a:	4c 89 1c 24          	mov    %r11,(%rsp)
    315e:	e8 0d f3 ff ff       	call   2470 <pthread_create@plt>
    3163:	48 8d 3d 03 32 00 00 	lea    0x3203(%rip),%rdi        # 636d <_IO_stdin_used+0x36d>
    316a:	e8 81 f1 ff ff       	call   22f0 <puts@plt>
    316f:	4c 8b 34 24          	mov    (%rsp),%r14
    3173:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3178:	49 8b 7c dd 00       	mov    0x0(%r13,%rbx,8),%rdi
    317d:	4c 89 e6             	mov    %r12,%rsi
    3180:	e8 6b f3 ff ff       	call   24f0 <pthread_join@plt>
    3185:	89 da                	mov    %ebx,%edx
    3187:	48 89 ee             	mov    %rbp,%rsi
    318a:	bf 01 00 00 00       	mov    $0x1,%edi
    318f:	31 c0                	xor    %eax,%eax
    3191:	48 83 c3 01          	add    $0x1,%rbx
    3195:	e8 b6 f2 ff ff       	call   2450 <__printf_chk@plt>
    319a:	48 83 fb 0f          	cmp    $0xf,%rbx
    319e:	75 d8                	jne    3178 <main+0xbf8>
    31a0:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    31a5:	4d 89 f3             	mov    %r14,%r11
    31a8:	45 31 d2             	xor    %r10d,%r10d
    31ab:	4d 8d 7e 58          	lea    0x58(%r14),%r15
    31af:	c7 04 24 00 00 00 00 	movl   $0x0,(%rsp)
    31b6:	45 31 f6             	xor    %r14d,%r14d
    31b9:	45 31 c9             	xor    %r9d,%r9d
    31bc:	31 db                	xor    %ebx,%ebx
    31be:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    31c3:	31 ed                	xor    %ebp,%ebp
    31c5:	4d 89 c8             	mov    %r9,%r8
    31c8:	49 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r13
    31d2:	4c 89 5c 24 20       	mov    %r11,0x20(%rsp)
    31d7:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    31dc:	4c 89 f8             	mov    %r15,%rax
    31df:	4d 89 f7             	mov    %r14,%r15
    31e2:	49 89 c6             	mov    %rax,%r14
    31e5:	8b 3c 24             	mov    (%rsp),%edi
    31e8:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    31ed:	89 f8                	mov    %edi,%eax
    31ef:	41 89 fc             	mov    %edi,%r12d
    31f2:	83 c7 01             	add    $0x1,%edi
    31f5:	83 e0 01             	and    $0x1,%eax
    31f8:	41 83 ec 01          	sub    $0x1,%r12d
    31fc:	89 3c 24             	mov    %edi,(%rsp)
    31ff:	85 c0                	test   %eax,%eax
    3201:	44 0f 44 e7          	cmove  %edi,%r12d
    3205:	bf 0a 00 00 00       	mov    $0xa,%edi
    320a:	e8 c1 f0 ff ff       	call   22d0 <putchar@plt>
    320f:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3214:	bf 01 00 00 00       	mov    $0x1,%edi
    3219:	48 8d 35 7f 31 00 00 	lea    0x317f(%rip),%rsi        # 639f <_IO_stdin_used+0x39f>
    3220:	48 8b 10             	mov    (%rax),%rdx
    3223:	31 c0                	xor    %eax,%eax
    3225:	e8 26 f2 ff ff       	call   2450 <__printf_chk@plt>
    322a:	49 63 56 08          	movslq 0x8(%r14),%rdx
    322e:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    3233:	85 d2                	test   %edx,%edx
    3235:	0f 8e 66 04 00 00    	jle    36a1 <main+0x1121>
    323b:	49 8b 06             	mov    (%r14),%rax
    323e:	48 c1 e2 08          	shl    $0x8,%rdx
    3242:	48 8d 3c 02          	lea    (%rdx,%rax,1),%rdi
    3246:	31 d2                	xor    %edx,%edx
    3248:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3250:	48 8b 48 50          	mov    0x50(%rax),%rcx
    3254:	48 05 00 01 00 00    	add    $0x100,%rax
    325a:	48 01 ca             	add    %rcx,%rdx
    325d:	48 39 c7             	cmp    %rax,%rdi
    3260:	75 ee                	jne    3250 <main+0xcd0>
    3262:	4d 63 e4             	movslq %r12d,%r12
    3265:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    326a:	4b 8d 04 a4          	lea    (%r12,%r12,4),%rax
    326e:	48 c1 e0 06          	shl    $0x6,%rax
    3272:	48 01 f8             	add    %rdi,%rax
    3275:	48 63 70 60          	movslq 0x60(%rax),%rsi
    3279:	85 f6                	test   %esi,%esi
    327b:	7e 25                	jle    32a2 <main+0xd22>
    327d:	48 8b 40 58          	mov    0x58(%rax),%rax
    3281:	48 c1 e6 08          	shl    $0x8,%rsi
    3285:	48 8d 3c 06          	lea    (%rsi,%rax,1),%rdi
    3289:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3290:	48 8b 48 50          	mov    0x50(%rax),%rcx
    3294:	48 05 00 01 00 00    	add    $0x100,%rax
    329a:	48 01 ca             	add    %rcx,%rdx
    329d:	48 39 c7             	cmp    %rax,%rdi
    32a0:	75 ee                	jne    3290 <main+0xd10>
    32a2:	48 8d 35 0b 31 00 00 	lea    0x310b(%rip),%rsi        # 63b4 <_IO_stdin_used+0x3b4>
    32a9:	bf 01 00 00 00       	mov    $0x1,%edi
    32ae:	31 c0                	xor    %eax,%eax
    32b0:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    32b5:	e8 96 f1 ff ff       	call   2450 <__printf_chk@plt>
    32ba:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    32bf:	bf 01 00 00 00       	mov    $0x1,%edi
    32c4:	48 8b 30             	mov    (%rax),%rsi
    32c7:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    32d1:	48 f7 ee             	imul   %rsi
    32d4:	48 c1 fe 3f          	sar    $0x3f,%rsi
    32d8:	31 c0                	xor    %eax,%eax
    32da:	48 d1 fa             	sar    %rdx
    32dd:	48 29 f2             	sub    %rsi,%rdx
    32e0:	48 8d 35 41 33 00 00 	lea    0x3341(%rip),%rsi        # 6628 <_IO_stdin_used+0x628>
    32e7:	e8 64 f1 ff ff       	call   2450 <__printf_chk@plt>
    32ec:	bf 0a 00 00 00       	mov    $0xa,%edi
    32f1:	e8 da ef ff ff       	call   22d0 <putchar@plt>
    32f6:	49 63 56 08          	movslq 0x8(%r14),%rdx
    32fa:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    32ff:	85 d2                	test   %edx,%edx
    3301:	0f 8e 32 01 00 00    	jle    3439 <main+0xeb9>
    3307:	49 8b 06             	mov    (%r14),%rax
    330a:	48 c1 e2 08          	shl    $0x8,%rdx
    330e:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3313:	48 01 c2             	add    %rax,%rdx
    3316:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3320:	48 8b 48 48          	mov    0x48(%rax),%rcx
    3324:	48 05 00 01 00 00    	add    $0x100,%rax
    332a:	49 01 cf             	add    %rcx,%r15
    332d:	48 8b 48 a0          	mov    -0x60(%rax),%rcx
    3331:	49 01 c8             	add    %rcx,%r8
    3334:	48 8b 48 b0          	mov    -0x50(%rax),%rcx
    3338:	49 01 c9             	add    %rcx,%r9
    333b:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    333f:	48 03 69 10          	add    0x10(%rcx),%rbp
    3343:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3347:	48 03 59 18          	add    0x18(%rcx),%rbx
    334b:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    334f:	48 03 69 30          	add    0x30(%rcx),%rbp
    3353:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3357:	48 03 59 38          	add    0x38(%rcx),%rbx
    335b:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    335f:	48 03 69 50          	add    0x50(%rcx),%rbp
    3363:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3367:	48 03 59 58          	add    0x58(%rcx),%rbx
    336b:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    336f:	48 03 69 70          	add    0x70(%rcx),%rbp
    3373:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3377:	48 03 59 78          	add    0x78(%rcx),%rbx
    337b:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    337f:	48 03 a9 90 00 00 00 	add    0x90(%rcx),%rbp
    3386:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    338a:	48 03 99 98 00 00 00 	add    0x98(%rcx),%rbx
    3391:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3395:	48 03 a9 b0 00 00 00 	add    0xb0(%rcx),%rbp
    339c:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33a0:	48 03 99 b8 00 00 00 	add    0xb8(%rcx),%rbx
    33a7:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33ab:	48 03 a9 d0 00 00 00 	add    0xd0(%rcx),%rbp
    33b2:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33b6:	48 03 99 d8 00 00 00 	add    0xd8(%rcx),%rbx
    33bd:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33c1:	48 03 a9 f0 00 00 00 	add    0xf0(%rcx),%rbp
    33c8:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33cc:	48 03 99 f8 00 00 00 	add    0xf8(%rcx),%rbx
    33d3:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33d7:	48 03 a9 10 01 00 00 	add    0x110(%rcx),%rbp
    33de:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33e2:	48 03 99 18 01 00 00 	add    0x118(%rcx),%rbx
    33e9:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33ed:	48 03 a9 30 01 00 00 	add    0x130(%rcx),%rbp
    33f4:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    33f8:	48 03 99 38 01 00 00 	add    0x138(%rcx),%rbx
    33ff:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3403:	48 03 a9 50 01 00 00 	add    0x150(%rcx),%rbp
    340a:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    340e:	48 03 99 58 01 00 00 	add    0x158(%rcx),%rbx
    3415:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3419:	48 03 a9 70 01 00 00 	add    0x170(%rcx),%rbp
    3420:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
    3424:	48 03 99 78 01 00 00 	add    0x178(%rcx),%rbx
    342b:	48 39 c2             	cmp    %rax,%rdx
    342e:	0f 85 ec fe ff ff    	jne    3320 <main+0xda0>
    3434:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    3439:	45 31 e4             	xor    %r12d,%r12d
    343c:	49 83 be b8 00 00 00 00 	cmpq   $0x0,0xb8(%r14)
    3444:	0f 8e 82 00 00 00    	jle    34cc <main+0xf4c>
    344a:	4c 89 f0             	mov    %r14,%rax
    344d:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    3452:	49 89 de             	mov    %rbx,%r14
    3455:	4c 89 e5             	mov    %r12,%rbp
    3458:	48 89 c3             	mov    %rax,%rbx
    345b:	4d 89 c4             	mov    %r8,%r12
    345e:	66 90                	xchg   %ax,%ax
    3460:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    3467:	48 8d 54 ad 00       	lea    0x0(%rbp,%rbp,4),%rdx
    346c:	48 83 ec 08          	sub    $0x8,%rsp
    3470:	bf 01 00 00 00       	mov    $0x1,%edi
    3475:	48 83 c5 01          	add    $0x1,%rbp
    3479:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    347d:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3481:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    3485:	48 89 f0             	mov    %rsi,%rax
    3488:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    348c:	4c 2b 01             	sub    (%rcx),%r8
    348f:	49 f7 e5             	mul    %r13
    3492:	8b 49 20             	mov    0x20(%rcx),%ecx
    3495:	56                   	push   %rsi
    3496:	31 c0                	xor    %eax,%eax
    3498:	48 8d 35 a9 31 00 00 	lea    0x31a9(%rip),%rsi        # 6648 <_IO_stdin_used+0x648>
    349f:	48 c1 ea 12          	shr    $0x12,%rdx
    34a3:	49 89 d1             	mov    %rdx,%r9
    34a6:	ba 02 00 00 00       	mov    $0x2,%edx
    34ab:	e8 a0 ef ff ff       	call   2450 <__printf_chk@plt>
    34b0:	58                   	pop    %rax
    34b1:	5a                   	pop    %rdx
    34b2:	48 39 ab b8 00 00 00 	cmp    %rbp,0xb8(%rbx)
    34b9:	7f a5                	jg     3460 <main+0xee0>
    34bb:	48 89 d8             	mov    %rbx,%rax
    34be:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    34c3:	4c 89 f3             	mov    %r14,%rbx
    34c6:	4d 89 e0             	mov    %r12,%r8
    34c9:	49 89 c6             	mov    %rax,%r14
    34cc:	48 83 44 24 08 18    	addq   $0x18,0x8(%rsp)
    34d2:	49 81 c6 40 01 00 00 	add    $0x140,%r14
    34d9:	83 3c 24 0c          	cmpl   $0xc,(%rsp)
    34dd:	0f 85 02 fd ff ff    	jne    31e5 <main+0xc65>
    34e3:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    34e8:	4c 89 fa             	mov    %r15,%rdx
    34eb:	bf 01 00 00 00       	mov    $0x1,%edi
    34f0:	31 c0                	xor    %eax,%eax
    34f2:	48 8d 35 c8 2e 00 00 	lea    0x2ec8(%rip),%rsi        # 63c1 <_IO_stdin_used+0x3c1>
    34f9:	4c 89 04 24          	mov    %r8,(%rsp)
    34fd:	49 bc 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r12
    3507:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    350c:	e8 3f ef ff ff       	call   2450 <__printf_chk@plt>
    3511:	bf 0a 00 00 00       	mov    $0xa,%edi
    3516:	e8 b5 ed ff ff       	call   22d0 <putchar@plt>
    351b:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3520:	bf 01 00 00 00       	mov    $0x1,%edi
    3525:	48 8d 35 6c 31 00 00 	lea    0x316c(%rip),%rsi        # 6698 <_IO_stdin_used+0x698>
    352c:	48 8b 50 08          	mov    0x8(%rax),%rdx
    3530:	31 c0                	xor    %eax,%eax
    3532:	e8 19 ef ff ff       	call   2450 <__printf_chk@plt>
    3537:	4c 8b 0c 24          	mov    (%rsp),%r9
    353b:	bf 01 00 00 00       	mov    $0x1,%edi
    3540:	48 8d 35 79 31 00 00 	lea    0x3179(%rip),%rsi        # 66c0 <_IO_stdin_used+0x6c0>
    3547:	4c 89 c8             	mov    %r9,%rax
    354a:	49 c1 f9 3f          	sar    $0x3f,%r9
    354e:	49 f7 ec             	imul   %r12
    3551:	31 c0                	xor    %eax,%eax
    3553:	48 d1 fa             	sar    %rdx
    3556:	4c 29 ca             	sub    %r9,%rdx
    3559:	e8 f2 ee ff ff       	call   2450 <__printf_chk@plt>
    355e:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    3563:	bf 01 00 00 00       	mov    $0x1,%edi
    3568:	48 8d 35 81 31 00 00 	lea    0x3181(%rip),%rsi        # 66f0 <_IO_stdin_used+0x6f0>
    356f:	4c 89 d0             	mov    %r10,%rax
    3572:	49 c1 fa 3f          	sar    $0x3f,%r10
    3576:	49 f7 ec             	imul   %r12
    3579:	31 c0                	xor    %eax,%eax
    357b:	48 d1 fa             	sar    %rdx
    357e:	4c 29 d2             	sub    %r10,%rdx
    3581:	e8 ca ee ff ff       	call   2450 <__printf_chk@plt>
    3586:	4c 89 f8             	mov    %r15,%rax
    3589:	4c 89 f9             	mov    %r15,%rcx
    358c:	bf 01 00 00 00       	mov    $0x1,%edi
    3591:	49 f7 ec             	imul   %r12
    3594:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3598:	48 8d 35 81 31 00 00 	lea    0x3181(%rip),%rsi        # 6720 <_IO_stdin_used+0x720>
    359f:	31 c0                	xor    %eax,%eax
    35a1:	48 d1 fa             	sar    %rdx
    35a4:	48 29 ca             	sub    %rcx,%rdx
    35a7:	e8 a4 ee ff ff       	call   2450 <__printf_chk@plt>
    35ac:	48 89 e8             	mov    %rbp,%rax
    35af:	48 c1 fd 3f          	sar    $0x3f,%rbp
    35b3:	48 8d 35 1b 2e 00 00 	lea    0x2e1b(%rip),%rsi        # 63d5 <_IO_stdin_used+0x3d5>
    35ba:	49 f7 ec             	imul   %r12
    35bd:	bf 01 00 00 00       	mov    $0x1,%edi
    35c2:	31 c0                	xor    %eax,%eax
    35c4:	48 d1 fa             	sar    %rdx
    35c7:	48 29 ea             	sub    %rbp,%rdx
    35ca:	e8 81 ee ff ff       	call   2450 <__printf_chk@plt>
    35cf:	48 89 d8             	mov    %rbx,%rax
    35d2:	48 c1 fb 3f          	sar    $0x3f,%rbx
    35d6:	48 8d 35 09 2e 00 00 	lea    0x2e09(%rip),%rsi        # 63e6 <_IO_stdin_used+0x3e6>
    35dd:	49 f7 ec             	imul   %r12
    35e0:	bf 01 00 00 00       	mov    $0x1,%edi
    35e5:	48 d1 fa             	sar    %rdx
    35e8:	48 29 da             	sub    %rbx,%rdx
    35eb:	31 c0                	xor    %eax,%eax
    35ed:	e8 5e ee ff ff       	call   2450 <__printf_chk@plt>
    35f2:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    35fa:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3603:	0f 85 9f 00 00 00    	jne    36a8 <main+0x1128>
    3609:	48 81 c4 a8 00 00 00 	add    $0xa8,%rsp
    3610:	31 c0                	xor    %eax,%eax
    3612:	5b                   	pop    %rbx
    3613:	5d                   	pop    %rbp
    3614:	41 5c                	pop    %r12
    3616:	41 5d                	pop    %r13
    3618:	41 5e                	pop    %r14
    361a:	41 5f                	pop    %r15
    361c:	c3                   	ret
    361d:	48 8d 05 fc 20 00 00 	lea    0x20fc(%rip),%rax        # 5720 <barriered_work>
    3624:	bb 02 00 00 00       	mov    $0x2,%ebx
    3629:	49 89 44 24 58       	mov    %rax,0x58(%r12)
    362e:	e9 80 f2 ff ff       	jmp    28b3 <main+0x333>
    3633:	b8 89 88 88 88       	mov    $0x88888889,%eax
    3638:	45 89 f2             	mov    %r14d,%r10d
    363b:	45 89 f5             	mov    %r14d,%r13d
    363e:	48 8b 3c 24          	mov    (%rsp),%rdi
    3642:	4c 0f af d0          	imul   %rax,%r10
    3646:	41 c7 07 00 00 00 00 	movl   $0x0,(%r15)
    364d:	4c 89 f9             	mov    %r15,%rcx
    3650:	89 ea                	mov    %ebp,%edx
    3652:	4c 89 3f             	mov    %r15,(%rdi)
    3655:	48 8d 35 a1 2c 00 00 	lea    0x2ca1(%rip),%rsi        # 62fd <_IO_stdin_used+0x2fd>
    365c:	49 c1 ea 23          	shr    $0x23,%r10
    3660:	44 89 d0             	mov    %r10d,%eax
    3663:	c1 e0 04             	shl    $0x4,%eax
    3666:	44 29 d0             	sub    %r10d,%eax
    3669:	41 29 c5             	sub    %eax,%r13d
    366c:	49 63 c5             	movslq %r13d,%rax
    366f:	4c 8d 04 80          	lea    (%rax,%rax,4),%r8
    3673:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3678:	49 c1 e0 06          	shl    $0x6,%r8
    367c:	49 01 c0             	add    %rax,%r8
    367f:	31 c0                	xor    %eax,%eax
    3681:	4c 89 47 08          	mov    %r8,0x8(%rdi)
    3685:	bf 01 00 00 00       	mov    $0x1,%edi
    368a:	e8 c1 ed ff ff       	call   2450 <__printf_chk@plt>
    368f:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    3694:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3699:	49 89 c4             	mov    %rax,%r12
    369c:	e9 08 f1 ff ff       	jmp    27a9 <main+0x229>
    36a1:	31 d2                	xor    %edx,%edx
    36a3:	e9 ba fb ff ff       	jmp    3262 <main+0xce2>
    36a8:	e8 83 ec ff ff       	call   2330 <__stack_chk_fail@plt>
    36ad:	0f 1f 00             	nopl   (%rax)

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
    36c8:	48 8d 3d b1 ee ff ff 	lea    -0x114f(%rip),%rdi        # 2580 <main>
    36cf:	ff 15 03 59 00 00    	call   *0x5903(%rip)        # 8fd8 <__libc_start_main@GLIBC_2.34>
    36d5:	f4                   	hlt
    36d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000036e0 <deregister_tm_clones>:
    36e0:	48 8d 3d 39 59 00 00 	lea    0x5939(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    36e7:	48 8d 05 32 59 00 00 	lea    0x5932(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    36ee:	48 39 f8             	cmp    %rdi,%rax
    36f1:	74 15                	je     3708 <deregister_tm_clones+0x28>
    36f3:	48 8b 05 e6 58 00 00 	mov    0x58e6(%rip),%rax        # 8fe0 <_ITM_deregisterTMCloneTable@Base>
    36fa:	48 85 c0             	test   %rax,%rax
    36fd:	74 09                	je     3708 <deregister_tm_clones+0x28>
    36ff:	ff e0                	jmp    *%rax
    3701:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3708:	c3                   	ret
    3709:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003710 <register_tm_clones>:
    3710:	48 8d 3d 09 59 00 00 	lea    0x5909(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3717:	48 8d 35 02 59 00 00 	lea    0x5902(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    371e:	48 29 fe             	sub    %rdi,%rsi
    3721:	48 89 f0             	mov    %rsi,%rax
    3724:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3728:	48 c1 f8 03          	sar    $0x3,%rax
    372c:	48 01 c6             	add    %rax,%rsi
    372f:	48 d1 fe             	sar    %rsi
    3732:	74 14                	je     3748 <register_tm_clones+0x38>
    3734:	48 8b 05 b5 58 00 00 	mov    0x58b5(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    373b:	48 85 c0             	test   %rax,%rax
    373e:	74 08                	je     3748 <register_tm_clones+0x38>
    3740:	ff e0                	jmp    *%rax
    3742:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3748:	c3                   	ret
    3749:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003750 <__do_global_dtors_aux>:
    3750:	f3 0f 1e fa          	endbr64
    3754:	80 3d cd 58 00 00 00 	cmpb   $0x0,0x58cd(%rip)        # 9028 <completed.0>
    375b:	75 2b                	jne    3788 <__do_global_dtors_aux+0x38>
    375d:	55                   	push   %rbp
    375e:	48 83 3d 92 58 00 00 00 	cmpq   $0x0,0x5892(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    3766:	48 89 e5             	mov    %rsp,%rbp
    3769:	74 0c                	je     3777 <__do_global_dtors_aux+0x27>
    376b:	48 8b 3d 96 58 00 00 	mov    0x5896(%rip),%rdi        # 9008 <__dso_handle>
    3772:	e8 39 eb ff ff       	call   22b0 <__cxa_finalize@plt>
    3777:	e8 64 ff ff ff       	call   36e0 <deregister_tm_clones>
    377c:	c6 05 a5 58 00 00 01 	movb   $0x1,0x58a5(%rip)        # 9028 <completed.0>
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
    37a0:	f3 0f 1e fa          	endbr64
    37a4:	48 8b 47 68          	mov    0x68(%rdi),%rax
    37a8:	48 8b 57 50          	mov    0x50(%rdi),%rdx
    37ac:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    37b3:	48 83 c2 01          	add    $0x1,%rdx
    37b7:	48 89 57 50          	mov    %rdx,0x50(%rdi)
    37bb:	48 8b 48 08          	mov    0x8(%rax),%rcx
    37bf:	48 83 00 01          	addq   $0x1,(%rax)
    37c3:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    37ca:	48 85 c9             	test   %rcx,%rcx
    37cd:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    37d4:	48 0f 4f d6          	cmovg  %rsi,%rdx
    37d8:	48 89 50 08          	mov    %rdx,0x8(%rax)
    37dc:	31 c0                	xor    %eax,%eax
    37de:	c3                   	ret
    37df:	90                   	nop

00000000000037e0 <barriered_reset>:
    37e0:	f3 0f 1e fa          	endbr64
    37e4:	8b 47 7c             	mov    0x7c(%rdi),%eax
    37e7:	85 c0                	test   %eax,%eax
    37e9:	7e 46                	jle    3831 <barriered_reset+0x51>
    37eb:	31 d2                	xor    %edx,%edx
    37ed:	0f 1f 00             	nopl   (%rax)
    37f0:	48 8b 77 68          	mov    0x68(%rdi),%rsi
    37f4:	48 63 4f 70          	movslq 0x70(%rdi),%rcx
    37f8:	48 89 d0             	mov    %rdx,%rax
    37fb:	48 83 c2 01          	add    $0x1,%rdx
    37ff:	48 c1 e0 08          	shl    $0x8,%rax
    3803:	48 8b 76 40          	mov    0x40(%rsi),%rsi
    3807:	48 8b 0c ce          	mov    (%rsi,%rcx,8),%rcx
    380b:	48 8b 71 58          	mov    0x58(%rcx),%rsi
    380f:	48 01 c6             	add    %rax,%rsi
    3812:	8b 4e 40             	mov    0x40(%rsi),%ecx
    3815:	83 c1 01             	add    $0x1,%ecx
    3818:	89 4e 40             	mov    %ecx,0x40(%rsi)
    381b:	48 8b 4f 68          	mov    0x68(%rdi),%rcx
    381f:	48 03 41 58          	add    0x58(%rcx),%rax
    3823:	c7 40 78 01 00 00 00 	movl   $0x1,0x78(%rax)
    382a:	8b 47 7c             	mov    0x7c(%rdi),%eax
    382d:	39 d0                	cmp    %edx,%eax
    382f:	7f bf                	jg     37f0 <barriered_reset+0x10>
    3831:	0f ae f8             	sfence
    3834:	31 c0                	xor    %eax,%eax
    3836:	c3                   	ret
    3837:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000003840 <barriered_thread>:
    3840:	f3 0f 1e fa          	endbr64
    3844:	8b 47 64             	mov    0x64(%rdi),%eax
    3847:	83 f8 01             	cmp    $0x1,%eax
    384a:	0f 85 8a 02 00 00    	jne    3ada <barriered_thread+0x29a>
    3850:	41 55                	push   %r13
    3852:	45 31 db             	xor    %r11d,%r11d
    3855:	41 54                	push   %r12
    3857:	49 89 fc             	mov    %rdi,%r12
    385a:	55                   	push   %rbp
    385b:	53                   	push   %rbx
    385c:	31 db                	xor    %ebx,%ebx
    385e:	48 83 ec 08          	sub    $0x8,%rsp
    3862:	44 8b 4f 60          	mov    0x60(%rdi),%r9d
    3866:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3870:	44 39 cb             	cmp    %r9d,%ebx
    3873:	7c 14                	jl     3889 <barriered_thread+0x49>
    3875:	49 83 84 24 18 01 00 00 01 	addq   $0x1,0x118(%r12)
    387e:	31 db                	xor    %ebx,%ebx
    3880:	45 85 c9             	test   %r9d,%r9d
    3883:	0f 8e 57 01 00 00    	jle    39e0 <barriered_thread+0x1a0>
    3889:	48 63 eb             	movslq %ebx,%rbp
    388c:	48 c1 e5 08          	shl    $0x8,%rbp
    3890:	eb 19                	jmp    38ab <barriered_thread+0x6b>
    3892:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3898:	83 c3 01             	add    $0x1,%ebx
    389b:	48 81 c5 00 01 00 00 	add    $0x100,%rbp
    38a2:	44 39 cb             	cmp    %r9d,%ebx
    38a5:	0f 8d 35 01 00 00    	jge    39e0 <barriered_thread+0x1a0>
    38ab:	49 8b 44 24 58       	mov    0x58(%r12),%rax
    38b0:	48 8d 14 28          	lea    (%rax,%rbp,1),%rdx
    38b4:	8b 4a 78             	mov    0x78(%rdx),%ecx
    38b7:	83 f9 01             	cmp    $0x1,%ecx
    38ba:	75 dc                	jne    3898 <barriered_thread+0x58>
    38bc:	85 db                	test   %ebx,%ebx
    38be:	0f 8e 3c 01 00 00    	jle    3a00 <barriered_thread+0x1c0>
    38c4:	45 8b 54 24 48       	mov    0x48(%r12),%r10d
    38c9:	44 8d 43 ff          	lea    -0x1(%rbx),%r8d
    38cd:	45 85 d2             	test   %r10d,%r10d
    38d0:	0f 8e f5 01 00 00    	jle    3acb <barriered_thread+0x28b>
    38d6:	49 8b 44 24 40       	mov    0x40(%r12),%rax
    38db:	49 63 ca             	movslq %r10d,%rcx
    38de:	4d 63 c0             	movslq %r8d,%r8
    38e1:	49 c1 e0 08          	shl    $0x8,%r8
    38e5:	4c 8d 2c c8          	lea    (%rax,%rcx,8),%r13
    38e9:	31 c9                	xor    %ecx,%ecx
    38eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    38f0:	48 8b 30             	mov    (%rax),%rsi
    38f3:	48 8b 7e 58          	mov    0x58(%rsi),%rdi
    38f7:	4c 01 c7             	add    %r8,%rdi
    38fa:	8b 77 40             	mov    0x40(%rdi),%esi
    38fd:	8b 7a 40             	mov    0x40(%rdx),%edi
    3900:	39 f7                	cmp    %esi,%edi
    3902:	40 0f 94 c6          	sete   %sil
    3906:	48 83 c0 08          	add    $0x8,%rax
    390a:	40 0f b6 f6          	movzbl %sil,%esi
    390e:	01 f1                	add    %esi,%ecx
    3910:	4c 39 e8             	cmp    %r13,%rax
    3913:	75 db                	jne    38f0 <barriered_thread+0xb0>
    3915:	85 c9                	test   %ecx,%ecx
    3917:	74 09                	je     3922 <barriered_thread+0xe2>
    3919:	44 39 d1             	cmp    %r10d,%ecx
    391c:	0f 85 be 00 00 00    	jne    39e0 <barriered_thread+0x1a0>
    3922:	41 83 fb 01          	cmp    $0x1,%r11d
    3926:	0f 84 f4 00 00 00    	je     3a20 <barriered_thread+0x1e0>
    392c:	85 db                	test   %ebx,%ebx
    392e:	75 16                	jne    3946 <barriered_thread+0x106>
    3930:	49 8b b4 24 f0 00 00 00 	mov    0xf0(%r12),%rsi
    3938:	49 3b b4 24 f8 00 00 00 	cmp    0xf8(%r12),%rsi
    3940:	0f 8c 6a 01 00 00    	jl     3ab0 <barriered_thread+0x270>
    3946:	49 8b 44 24 58       	mov    0x58(%r12),%rax
    394b:	49 63 0c 24          	movslq (%r12),%rcx
    394f:	49 8b 54 24 40       	mov    0x40(%r12),%rdx
    3954:	48 01 e8             	add    %rbp,%rax
    3957:	c7 40 78 00 00 00 00 	movl   $0x0,0x78(%rax)
    395e:	48 8b 40 58          	mov    0x58(%rax),%rax
    3962:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    3966:	48 8b 7a 58          	mov    0x58(%rdx),%rdi
    396a:	48 01 ef             	add    %rbp,%rdi
    396d:	ff d0                	call   *%rax
    396f:	49 8b 54 24 58       	mov    0x58(%r12),%rdx
    3974:	48 01 ea             	add    %rbp,%rdx
    3977:	8b 42 40             	mov    0x40(%rdx),%eax
    397a:	83 c0 01             	add    $0x1,%eax
    397d:	89 42 40             	mov    %eax,0x40(%rdx)
    3980:	41 8b 44 24 60       	mov    0x60(%r12),%eax
    3985:	49 83 84 24 e8 00 00 00 01 	addq   $0x1,0xe8(%r12)
    398e:	83 e8 01             	sub    $0x1,%eax
    3991:	39 d8                	cmp    %ebx,%eax
    3993:	0f 84 d7 00 00 00    	je     3a70 <barriered_thread+0x230>
    3999:	0f ae f8             	sfence
    399c:	49 8b 84 24 08 01 00 00 	mov    0x108(%r12),%rax
    39a4:	bf 04 00 00 00       	mov    $0x4,%edi
    39a9:	48 81 c5 00 01 00 00 	add    $0x100,%rbp
    39b0:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    39b4:	49 8b 84 24 00 01 00 00 	mov    0x100(%r12),%rax
    39bc:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    39c0:	89 5e 20             	mov    %ebx,0x20(%rsi)
    39c3:	83 c3 01             	add    $0x1,%ebx
    39c6:	e8 45 e9 ff ff       	call   2310 <clock_gettime@plt>
    39cb:	45 8b 4c 24 60       	mov    0x60(%r12),%r9d
    39d0:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    39d6:	44 39 cb             	cmp    %r9d,%ebx
    39d9:	0f 8c cc fe ff ff    	jl     38ab <barriered_thread+0x6b>
    39df:	90                   	nop
    39e0:	41 8b 44 24 64       	mov    0x64(%r12),%eax
    39e5:	83 f8 01             	cmp    $0x1,%eax
    39e8:	0f 84 82 fe ff ff    	je     3870 <barriered_thread+0x30>
    39ee:	48 83 c4 08          	add    $0x8,%rsp
    39f2:	31 c0                	xor    %eax,%eax
    39f4:	5b                   	pop    %rbx
    39f5:	5d                   	pop    %rbp
    39f6:	41 5c                	pop    %r12
    39f8:	41 5d                	pop    %r13
    39fa:	c3                   	ret
    39fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3a00:	45 8b 54 24 48       	mov    0x48(%r12),%r10d
    3a05:	45 8d 41 ff          	lea    -0x1(%r9),%r8d
    3a09:	45 85 d2             	test   %r10d,%r10d
    3a0c:	0f 8f c4 fe ff ff    	jg     38d6 <barriered_thread+0x96>
    3a12:	41 83 fb 01          	cmp    $0x1,%r11d
    3a16:	0f 85 10 ff ff ff    	jne    392c <barriered_thread+0xec>
    3a1c:	0f 1f 40 00          	nopl   0x0(%rax)
    3a20:	49 8b 84 24 08 01 00 00 	mov    0x108(%r12),%rax
    3a28:	bf 04 00 00 00       	mov    $0x4,%edi
    3a2d:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3a31:	49 8b 84 24 00 01 00 00 	mov    0x100(%r12),%rax
    3a39:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3a3e:	e8 cd e8 ff ff       	call   2310 <clock_gettime@plt>
    3a43:	49 8b 84 24 08 01 00 00 	mov    0x108(%r12),%rax
    3a4b:	48 83 c0 01          	add    $0x1,%rax
    3a4f:	48 99                	cqto
    3a51:	49 f7 bc 24 10 01 00 00 	idivq  0x110(%r12)
    3a59:	49 89 94 24 08 01 00 00 	mov    %rdx,0x108(%r12)
    3a61:	e9 c6 fe ff ff       	jmp    392c <barriered_thread+0xec>
    3a66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3a70:	49 8b b4 24 f0 00 00 00 	mov    0xf0(%r12),%rsi
    3a78:	49 3b b4 24 f8 00 00 00 	cmp    0xf8(%r12),%rsi
    3a80:	0f 8d 13 ff ff ff    	jge    3999 <barriered_thread+0x159>
    3a86:	48 c1 e6 04          	shl    $0x4,%rsi
    3a8a:	bf 04 00 00 00       	mov    $0x4,%edi
    3a8f:	49 03 b4 24 e0 00 00 00 	add    0xe0(%r12),%rsi
    3a97:	e8 74 e8 ff ff       	call   2310 <clock_gettime@plt>
    3a9c:	49 83 84 24 f0 00 00 00 01 	addq   $0x1,0xf0(%r12)
    3aa5:	e9 ef fe ff ff       	jmp    3999 <barriered_thread+0x159>
    3aaa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3ab0:	48 c1 e6 04          	shl    $0x4,%rsi
    3ab4:	bf 04 00 00 00       	mov    $0x4,%edi
    3ab9:	49 03 b4 24 d8 00 00 00 	add    0xd8(%r12),%rsi
    3ac1:	e8 4a e8 ff ff       	call   2310 <clock_gettime@plt>
    3ac6:	e9 7b fe ff ff       	jmp    3946 <barriered_thread+0x106>
    3acb:	41 83 fb 01          	cmp    $0x1,%r11d
    3acf:	0f 85 76 fe ff ff    	jne    394b <barriered_thread+0x10b>
    3ad5:	e9 46 ff ff ff       	jmp    3a20 <barriered_thread+0x1e0>
    3ada:	31 c0                	xor    %eax,%eax
    3adc:	c3                   	ret
    3add:	0f 1f 00             	nopl   (%rax)

0000000000003ae0 <external_thread>:
    3ae0:	f3 0f 1e fa          	endbr64
    3ae4:	41 55                	push   %r13
    3ae6:	41 54                	push   %r12
    3ae8:	55                   	push   %rbp
    3ae9:	53                   	push   %rbx
    3aea:	48 83 ec 38          	sub    $0x38,%rsp
    3aee:	66 0f 6f 05 4a 2e 00 00 	movdqa 0x2e4a(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3af6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3aff:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3b04:	31 c0                	xor    %eax,%eax
    3b06:	0f 29 04 24          	movaps %xmm0,(%rsp)
    3b0a:	8b 47 64             	mov    0x64(%rdi),%eax
    3b0d:	83 f8 01             	cmp    $0x1,%eax
    3b10:	75 64                	jne    3b76 <external_thread+0x96>
    3b12:	49 89 fd             	mov    %rdi,%r13
    3b15:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3b1a:	48 89 e3             	mov    %rsp,%rbx
    3b1d:	4c 8d 25 e0 24 00 00 	lea    0x24e0(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    3b24:	0f 1f 40 00          	nopl   0x0(%rax)
    3b28:	48 89 ee             	mov    %rbp,%rsi
    3b2b:	48 89 df             	mov    %rbx,%rdi
    3b2e:	e8 1d e8 ff ff       	call   2350 <nanosleep@plt>
    3b33:	49 8b 85 c0 00 00 00 	mov    0xc0(%r13),%rax
    3b3a:	48 63 08             	movslq (%rax),%rcx
    3b3d:	85 c9                	test   %ecx,%ecx
    3b3f:	7e 29                	jle    3b6a <external_thread+0x8a>
    3b41:	48 8b 40 08          	mov    0x8(%rax),%rax
    3b45:	48 c1 e1 04          	shl    $0x4,%rcx
    3b49:	48 01 c1             	add    %rax,%rcx
    3b4c:	0f 1f 40 00          	nopl   0x0(%rax)
    3b50:	8b 50 08             	mov    0x8(%rax),%edx
    3b53:	85 d2                	test   %edx,%edx
    3b55:	75 0a                	jne    3b61 <external_thread+0x81>
    3b57:	4c 89 20             	mov    %r12,(%rax)
    3b5a:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    3b61:	48 83 c0 10          	add    $0x10,%rax
    3b65:	48 39 c1             	cmp    %rax,%rcx
    3b68:	75 e6                	jne    3b50 <external_thread+0x70>
    3b6a:	0f ae f0             	mfence
    3b6d:	41 8b 45 64          	mov    0x64(%r13),%eax
    3b71:	83 f8 01             	cmp    $0x1,%eax
    3b74:	74 b2                	je     3b28 <external_thread+0x48>
    3b76:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3b7b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3b84:	75 0d                	jne    3b93 <external_thread+0xb3>
    3b86:	48 83 c4 38          	add    $0x38,%rsp
    3b8a:	31 c0                	xor    %eax,%eax
    3b8c:	5b                   	pop    %rbx
    3b8d:	5d                   	pop    %rbp
    3b8e:	41 5c                	pop    %r12
    3b90:	41 5d                	pop    %r13
    3b92:	c3                   	ret
    3b93:	e8 98 e7 ff ff       	call   2330 <__stack_chk_fail@plt>
    3b98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000003ba0 <timer_thread>:
    3ba0:	f3 0f 1e fa          	endbr64
    3ba4:	41 57                	push   %r15
    3ba6:	48 8d 35 63 24 00 00 	lea    0x2463(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    3bad:	49 89 ff             	mov    %rdi,%r15
    3bb0:	41 56                	push   %r14
    3bb2:	41 55                	push   %r13
    3bb4:	41 54                	push   %r12
    3bb6:	55                   	push   %rbp
    3bb7:	53                   	push   %rbx
    3bb8:	48 83 ec 58          	sub    $0x58,%rsp
    3bbc:	8b 17                	mov    (%rdi),%edx
    3bbe:	bf 01 00 00 00       	mov    $0x1,%edi
    3bc3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3bcc:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3bd1:	31 c0                	xor    %eax,%eax
    3bd3:	e8 78 e8 ff ff       	call   2450 <__printf_chk@plt>
    3bd8:	66 0f 6f 05 60 2d 00 00 	movdqa 0x2d60(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3be0:	ba 88 13 00 00       	mov    $0x1388,%edx
    3be5:	31 c0                	xor    %eax,%eax
    3be7:	48 8d 35 34 24 00 00 	lea    0x2434(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    3bee:	bf 01 00 00 00       	mov    $0x1,%edi
    3bf3:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3bf8:	e8 53 e8 ff ff       	call   2450 <__printf_chk@plt>
    3bfd:	45 8b 77 64          	mov    0x64(%r15),%r14d
    3c01:	45 85 f6             	test   %r14d,%r14d
    3c04:	0f 84 a2 00 00 00    	je     3cac <timer_thread+0x10c>
    3c0a:	45 31 ed             	xor    %r13d,%r13d
    3c0d:	45 31 f6             	xor    %r14d,%r14d
    3c10:	49 89 e4             	mov    %rsp,%r12
    3c13:	31 db                	xor    %ebx,%ebx
    3c15:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3c1a:	4c 89 e6             	mov    %r12,%rsi
    3c1d:	48 89 ef             	mov    %rbp,%rdi
    3c20:	41 83 c5 01          	add    $0x1,%r13d
    3c24:	e8 27 e7 ff ff       	call   2350 <nanosleep@plt>
    3c29:	49 63 47 48          	movslq 0x48(%r15),%rax
    3c2d:	45 8d 46 01          	lea    0x1(%r14),%r8d
    3c31:	85 c0                	test   %eax,%eax
    3c33:	7e 4d                	jle    3c82 <timer_thread+0xe2>
    3c35:	49 8b 77 40          	mov    0x40(%r15),%rsi
    3c39:	49 63 fe             	movslq %r14d,%rdi
    3c3c:	48 c1 e7 08          	shl    $0x8,%rdi
    3c40:	4c 8d 0c c6          	lea    (%rsi,%rax,8),%r9
    3c44:	0f 1f 40 00          	nopl   0x0(%rax)
    3c48:	4c 8b 16             	mov    (%rsi),%r10
    3c4b:	44 89 c0             	mov    %r8d,%eax
    3c4e:	48 83 c6 08          	add    $0x8,%rsi
    3c52:	99                   	cltd
    3c53:	41 f7 7a 60          	idivl  0x60(%r10)
    3c57:	49 8b 4a 58          	mov    0x58(%r10),%rcx
    3c5b:	48 63 d2             	movslq %edx,%rdx
    3c5e:	48 c1 e2 08          	shl    $0x8,%rdx
    3c62:	48 8d 04 11          	lea    (%rcx,%rdx,1),%rax
    3c66:	48 01 f9             	add    %rdi,%rcx
    3c69:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    3c73:	c7 81 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rcx)
    3c7d:	4c 39 ce             	cmp    %r9,%rsi
    3c80:	75 c6                	jne    3c48 <timer_thread+0xa8>
    3c82:	0f ae f0             	mfence
    3c85:	49 8b 47 40          	mov    0x40(%r15),%rax
    3c89:	45 89 c6             	mov    %r8d,%r14d
    3c8c:	48 8b 00             	mov    (%rax),%rax
    3c8f:	44 39 40 60          	cmp    %r8d,0x60(%rax)
    3c93:	41 8b 47 64          	mov    0x64(%r15),%eax
    3c97:	44 0f 4e f3          	cmovle %ebx,%r14d
    3c9b:	85 c0                	test   %eax,%eax
    3c9d:	74 0d                	je     3cac <timer_thread+0x10c>
    3c9f:	41 81 fd 88 13 00 00 	cmp    $0x1388,%r13d
    3ca6:	0f 85 6e ff ff ff    	jne    3c1a <timer_thread+0x7a>
    3cac:	48 8d 3d 85 23 00 00 	lea    0x2385(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    3cb3:	e8 38 e6 ff ff       	call   22f0 <puts@plt>
    3cb8:	49 63 57 4c          	movslq 0x4c(%r15),%rdx
    3cbc:	85 d2                	test   %edx,%edx
    3cbe:	7e 4e                	jle    3d0e <timer_thread+0x16e>
    3cc0:	49 63 47 60          	movslq 0x60(%r15),%rax
    3cc4:	85 c0                	test   %eax,%eax
    3cc6:	7e 46                	jle    3d0e <timer_thread+0x16e>
    3cc8:	48 c1 e0 08          	shl    $0x8,%rax
    3ccc:	4d 8b 47 40          	mov    0x40(%r15),%r8
    3cd0:	48 8d 34 d5 00 00 00 00 	lea    0x0(,%rdx,8),%rsi
    3cd8:	31 ff                	xor    %edi,%edi
    3cda:	48 89 c1             	mov    %rax,%rcx
    3cdd:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3ce1:	48 8b 40 58          	mov    0x58(%rax),%rax
    3ce5:	48 8d 14 01          	lea    (%rcx,%rax,1),%rdx
    3ce9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3cf0:	c7 80 b8 00 00 00 00 00 00 00 	movl   $0x0,0xb8(%rax)
    3cfa:	48 05 00 01 00 00    	add    $0x100,%rax
    3d00:	48 39 c2             	cmp    %rax,%rdx
    3d03:	75 eb                	jne    3cf0 <timer_thread+0x150>
    3d05:	48 83 c7 08          	add    $0x8,%rdi
    3d09:	48 39 fe             	cmp    %rdi,%rsi
    3d0c:	75 cf                	jne    3cdd <timer_thread+0x13d>
    3d0e:	0f ae f0             	mfence
    3d11:	66 0f 6f 05 37 2c 00 00 	movdqa 0x2c37(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    3d19:	48 8d 2d 3d 23 00 00 	lea    0x233d(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    3d20:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    3d25:	49 63 47 48          	movslq 0x48(%r15),%rax
    3d29:	45 8d 6e 01          	lea    0x1(%r14),%r13d
    3d2d:	85 c0                	test   %eax,%eax
    3d2f:	7e 48                	jle    3d79 <timer_thread+0x1d9>
    3d31:	49 8b 77 40          	mov    0x40(%r15),%rsi
    3d35:	49 63 fe             	movslq %r14d,%rdi
    3d38:	48 c1 e7 08          	shl    $0x8,%rdi
    3d3c:	4c 8d 04 c6          	lea    (%rsi,%rax,8),%r8
    3d40:	48 8b 1e             	mov    (%rsi),%rbx
    3d43:	44 89 e8             	mov    %r13d,%eax
    3d46:	48 83 c6 08          	add    $0x8,%rsi
    3d4a:	99                   	cltd
    3d4b:	f7 7b 60             	idivl  0x60(%rbx)
    3d4e:	48 8b 4b 58          	mov    0x58(%rbx),%rcx
    3d52:	48 63 d2             	movslq %edx,%rdx
    3d55:	48 c1 e2 08          	shl    $0x8,%rdx
    3d59:	48 8d 04 11          	lea    (%rcx,%rdx,1),%rax
    3d5d:	48 01 f9             	add    %rdi,%rcx
    3d60:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    3d6a:	c7 81 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rcx)
    3d74:	49 39 f0             	cmp    %rsi,%r8
    3d77:	75 c7                	jne    3d40 <timer_thread+0x1a0>
    3d79:	0f ae f0             	mfence
    3d7c:	49 8b 47 40          	mov    0x40(%r15),%rax
    3d80:	48 8b 00             	mov    (%rax),%rax
    3d83:	44 39 68 60          	cmp    %r13d,0x60(%rax)
    3d87:	7f 03                	jg     3d8c <timer_thread+0x1ec>
    3d89:	45 31 ed             	xor    %r13d,%r13d
    3d8c:	45 8b 47 50          	mov    0x50(%r15),%r8d
    3d90:	45 85 c0             	test   %r8d,%r8d
    3d93:	0f 8e e9 00 00 00    	jle    3e82 <timer_thread+0x2e2>
    3d99:	31 db                	xor    %ebx,%ebx
    3d9b:	45 31 e4             	xor    %r12d,%r12d
    3d9e:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3da4:	0f 1f 40 00          	nopl   0x0(%rax)
    3da8:	45 31 f6             	xor    %r14d,%r14d
    3dab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3db0:	45 85 c0             	test   %r8d,%r8d
    3db3:	0f 8e 8d 00 00 00    	jle    3e46 <timer_thread+0x2a6>
    3db9:	49 8b 47 40          	mov    0x40(%r15),%rax
    3dbd:	4c 89 f1             	mov    %r14,%rcx
    3dc0:	49 63 f8             	movslq %r8d,%rdi
    3dc3:	31 d2                	xor    %edx,%edx
    3dc5:	48 c1 e1 08          	shl    $0x8,%rcx
    3dc9:	48 8b 04 18          	mov    (%rax,%rbx,1),%rax
    3dcd:	48 03 48 58          	add    0x58(%rax),%rcx
    3dd1:	eb 23                	jmp    3df6 <timer_thread+0x256>
    3dd3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3dd8:	48 8b b1 a8 00 00 00 	mov    0xa8(%rcx),%rsi
    3ddf:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    3de4:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    3de8:	48 85 f6             	test   %rsi,%rsi
    3deb:	7f 24                	jg     3e11 <timer_thread+0x271>
    3ded:	48 83 c2 01          	add    $0x1,%rdx
    3df1:	48 39 fa             	cmp    %rdi,%rdx
    3df4:	74 50                	je     3e46 <timer_thread+0x2a6>
    3df6:	48 8b b1 a8 00 00 00 	mov    0xa8(%rcx),%rsi
    3dfd:	48 89 d0             	mov    %rdx,%rax
    3e00:	48 c1 e0 05          	shl    $0x5,%rax
    3e04:	48 8b 34 06          	mov    (%rsi,%rax,1),%rsi
    3e08:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    3e0c:	48 85 f6             	test   %rsi,%rsi
    3e0f:	7e c7                	jle    3dd8 <timer_thread+0x238>
    3e11:	48 8b b1 a8 00 00 00 	mov    0xa8(%rcx),%rsi
    3e18:	bf 01 00 00 00       	mov    $0x1,%edi
    3e1d:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    3e22:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3e26:	48 8b 89 a8 00 00 00 	mov    0xa8(%rcx),%rcx
    3e2d:	48 89 ee             	mov    %rbp,%rsi
    3e30:	48 8b 04 01          	mov    (%rcx,%rax,1),%rax
    3e34:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3e38:	31 c0                	xor    %eax,%eax
    3e3a:	e8 11 e6 ff ff       	call   2450 <__printf_chk@plt>
    3e3f:	45 8b 47 50          	mov    0x50(%r15),%r8d
    3e43:	45 31 c9             	xor    %r9d,%r9d
    3e46:	49 83 c6 01          	add    $0x1,%r14
    3e4a:	45 39 f0             	cmp    %r14d,%r8d
    3e4d:	0f 8f 5d ff ff ff    	jg     3db0 <timer_thread+0x210>
    3e53:	41 83 c4 01          	add    $0x1,%r12d
    3e57:	45 39 c4             	cmp    %r8d,%r12d
    3e5a:	7d 09                	jge    3e65 <timer_thread+0x2c5>
    3e5c:	48 83 c3 08          	add    $0x8,%rbx
    3e60:	e9 43 ff ff ff       	jmp    3da8 <timer_thread+0x208>
    3e65:	41 83 f9 01          	cmp    $0x1,%r9d
    3e69:	74 17                	je     3e82 <timer_thread+0x2e2>
    3e6b:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3e70:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3e75:	45 89 ee             	mov    %r13d,%r14d
    3e78:	e8 d3 e4 ff ff       	call   2350 <nanosleep@plt>
    3e7d:	e9 a3 fe ff ff       	jmp    3d25 <timer_thread+0x185>
    3e82:	48 8d 3d cb 21 00 00 	lea    0x21cb(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3e89:	4c 8d 25 f0 21 00 00 	lea    0x21f0(%rip),%r12        # 6080 <_IO_stdin_used+0x80>
    3e90:	e8 5b e4 ff ff       	call   22f0 <puts@plt>
    3e95:	41 8b 47 64          	mov    0x64(%r15),%eax
    3e99:	48 8d 2d ce 21 00 00 	lea    0x21ce(%rip),%rbp        # 606e <_IO_stdin_used+0x6e>
    3ea0:	85 c0                	test   %eax,%eax
    3ea2:	0f 84 a5 00 00 00    	je     3f4d <timer_thread+0x3ad>
    3ea8:	41 8b 57 4c          	mov    0x4c(%r15),%edx
    3eac:	31 db                	xor    %ebx,%ebx
    3eae:	85 d2                	test   %edx,%edx
    3eb0:	7e 21                	jle    3ed3 <timer_thread+0x333>
    3eb2:	49 8b 4f 40          	mov    0x40(%r15),%rcx
    3eb6:	48 8b 04 d9          	mov    (%rcx,%rbx,8),%rax
    3eba:	83 78 08 02          	cmpl   $0x2,0x8(%rax)
    3ebe:	c7 40 64 00 00 00 00 	movl   $0x0,0x64(%rax)
    3ec5:	0f 84 af 00 00 00    	je     3f7a <timer_thread+0x3da>
    3ecb:	48 83 c3 01          	add    $0x1,%rbx
    3ecf:	39 da                	cmp    %ebx,%edx
    3ed1:	7f e3                	jg     3eb6 <timer_thread+0x316>
    3ed3:	49 63 57 48          	movslq 0x48(%r15),%rdx
    3ed7:	85 d2                	test   %edx,%edx
    3ed9:	7e 53                	jle    3f2e <timer_thread+0x38e>
    3edb:	49 63 47 60          	movslq 0x60(%r15),%rax
    3edf:	85 c0                	test   %eax,%eax
    3ee1:	7e 4b                	jle    3f2e <timer_thread+0x38e>
    3ee3:	48 c1 e0 08          	shl    $0x8,%rax
    3ee7:	4d 8b 47 40          	mov    0x40(%r15),%r8
    3eeb:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3ef3:	31 c9                	xor    %ecx,%ecx
    3ef5:	48 89 c6             	mov    %rax,%rsi
    3ef8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3f00:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3f04:	48 8b 40 58          	mov    0x58(%rax),%rax
    3f08:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3f0c:	0f 1f 40 00          	nopl   0x0(%rax)
    3f10:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    3f1a:	48 05 00 01 00 00    	add    $0x100,%rax
    3f20:	48 39 d0             	cmp    %rdx,%rax
    3f23:	75 eb                	jne    3f10 <timer_thread+0x370>
    3f25:	48 83 c1 08          	add    $0x8,%rcx
    3f29:	48 39 f9             	cmp    %rdi,%rcx
    3f2c:	75 d2                	jne    3f00 <timer_thread+0x360>
    3f2e:	0f ae f0             	mfence
    3f31:	4c 89 e7             	mov    %r12,%rdi
    3f34:	e8 b7 e3 ff ff       	call   22f0 <puts@plt>
    3f39:	41 c7 47 64 00 00 00 00 	movl   $0x0,0x64(%r15)
    3f41:	41 8b 47 64          	mov    0x64(%r15),%eax
    3f45:	85 c0                	test   %eax,%eax
    3f47:	0f 85 5b ff ff ff    	jne    3ea8 <timer_thread+0x308>
    3f4d:	48 8d 3d 33 21 00 00 	lea    0x2133(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3f54:	e8 97 e3 ff ff       	call   22f0 <puts@plt>
    3f59:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3f5e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3f67:	75 46                	jne    3faf <timer_thread+0x40f>
    3f69:	48 83 c4 58          	add    $0x58,%rsp
    3f6d:	31 c0                	xor    %eax,%eax
    3f6f:	5b                   	pop    %rbx
    3f70:	5d                   	pop    %rbp
    3f71:	41 5c                	pop    %r12
    3f73:	41 5d                	pop    %r13
    3f75:	41 5e                	pop    %r14
    3f77:	41 5f                	pop    %r15
    3f79:	c3                   	ret
    3f7a:	48 89 ef             	mov    %rbp,%rdi
    3f7d:	e8 6e e3 ff ff       	call   22f0 <puts@plt>
    3f82:	49 8b 47 40          	mov    0x40(%r15),%rax
    3f86:	be 01 00 00 00       	mov    $0x1,%esi
    3f8b:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    3f8f:	48 83 c3 01          	add    $0x1,%rbx
    3f93:	8b b8 d0 00 00 00    	mov    0xd0(%rax),%edi
    3f99:	e8 62 e4 ff ff       	call   2400 <eventfd_write@plt>
    3f9e:	41 8b 57 4c          	mov    0x4c(%r15),%edx
    3fa2:	39 da                	cmp    %ebx,%edx
    3fa4:	0f 8f 08 ff ff ff    	jg     3eb2 <timer_thread+0x312>
    3faa:	e9 24 ff ff ff       	jmp    3ed3 <timer_thread+0x333>
    3faf:	e8 7c e3 ff ff       	call   2330 <__stack_chk_fail@plt>
    3fb4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3fbf:	90                   	nop

0000000000003fc0 <fatal_error>:
    3fc0:	f3 0f 1e fa          	endbr64
    3fc4:	50                   	push   %rax
    3fc5:	58                   	pop    %rax
    3fc6:	48 83 ec 08          	sub    $0x8,%rsp
    3fca:	e8 c1 e4 ff ff       	call   2490 <perror@plt>
    3fcf:	bf 01 00 00 00       	mov    $0x1,%edi
    3fd4:	e8 c7 e4 ff ff       	call   24a0 <exit@plt>
    3fd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003fe0 <strtolower>:
    3fe0:	f3 0f 1e fa          	endbr64
    3fe4:	55                   	push   %rbp
    3fe5:	53                   	push   %rbx
    3fe6:	48 83 ec 08          	sub    $0x8,%rsp
    3fea:	48 0f be 1f          	movsbq (%rdi),%rbx
    3fee:	84 db                	test   %bl,%bl
    3ff0:	74 24                	je     4016 <strtolower+0x36>
    3ff2:	48 89 fd             	mov    %rdi,%rbp
    3ff5:	e8 16 e5 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3ffa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4000:	48 8b 10             	mov    (%rax),%rdx
    4003:	48 83 c5 01          	add    $0x1,%rbp
    4007:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    400a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    400d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4012:	84 db                	test   %bl,%bl
    4014:	75 ea                	jne    4000 <strtolower+0x20>
    4016:	48 83 c4 08          	add    $0x8,%rsp
    401a:	5b                   	pop    %rbx
    401b:	5d                   	pop    %rbp
    401c:	c3                   	ret
    401d:	0f 1f 00             	nopl   (%rax)

0000000000004020 <zh_malloc>:
    4020:	f3 0f 1e fa          	endbr64
    4024:	48 83 ec 08          	sub    $0x8,%rsp
    4028:	e8 e3 e3 ff ff       	call   2410 <malloc@plt>
    402d:	48 85 c0             	test   %rax,%rax
    4030:	74 05                	je     4037 <zh_malloc+0x17>
    4032:	48 83 c4 08          	add    $0x8,%rsp
    4036:	c3                   	ret
    4037:	48 8b 0d e2 4f 00 00 	mov    0x4fe2(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    403e:	ba 28 00 00 00       	mov    $0x28,%edx
    4043:	be 01 00 00 00       	mov    $0x1,%esi
    4048:	48 8d 3d b1 23 00 00 	lea    0x23b1(%rip),%rdi        # 6400 <_IO_stdin_used+0x400>
    404f:	e8 6c e4 ff ff       	call   24c0 <fwrite@plt>
    4054:	bf 01 00 00 00       	mov    $0x1,%edi
    4059:	e8 42 e4 ff ff       	call   24a0 <exit@plt>
    405e:	66 90                	xchg   %ax,%ax

0000000000004060 <get_filename_ext>:
    4060:	f3 0f 1e fa          	endbr64
    4064:	53                   	push   %rbx
    4065:	be 2e 00 00 00       	mov    $0x2e,%esi
    406a:	48 89 fb             	mov    %rdi,%rbx
    406d:	e8 ee e2 ff ff       	call   2360 <strrchr@plt>
    4072:	48 85 c0             	test   %rax,%rax
    4075:	74 11                	je     4088 <get_filename_ext+0x28>
    4077:	48 39 c3             	cmp    %rax,%rbx
    407a:	74 0c                	je     4088 <get_filename_ext+0x28>
    407c:	48 83 c0 01          	add    $0x1,%rax
    4080:	5b                   	pop    %rbx
    4081:	c3                   	ret
    4082:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4088:	48 8d 05 40 20 00 00 	lea    0x2040(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
    408f:	5b                   	pop    %rbx
    4090:	c3                   	ret
    4091:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    409c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000040a0 <send_headers>:
    40a0:	f3 0f 1e fa          	endbr64
    40a4:	41 55                	push   %r13
    40a6:	49 89 f5             	mov    %rsi,%r13
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
    40dd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    40e2:	84 db                	test   %bl,%bl
    40e4:	74 24                	je     410a <send_headers+0x6a>
    40e6:	e8 25 e4 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    40eb:	48 8b 08             	mov    (%rax),%rcx
    40ee:	4c 89 e0             	mov    %r12,%rax
    40f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    40f8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    40fb:	48 83 c0 01          	add    $0x1,%rax
    40ff:	88 50 ff             	mov    %dl,-0x1(%rax)
    4102:	48 0f be 18          	movsbq (%rax),%rbx
    4106:	84 db                	test   %bl,%bl
    4108:	75 ee                	jne    40f8 <send_headers+0x58>
    410a:	bf 11 00 00 00       	mov    $0x11,%edi
    410f:	e8 fc e2 ff ff       	call   2410 <malloc@plt>
    4114:	48 85 c0             	test   %rax,%rax
    4117:	0f 84 7e 04 00 00    	je     459b <send_headers+0x4fb>
    411d:	66 0f 6f 05 3b 28 00 00 	movdqa 0x283b(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    4125:	48 89 45 00          	mov    %rax,0x0(%rbp)
    4129:	bf 17 00 00 00       	mov    $0x17,%edi
    412e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4136:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    413a:	0f 11 00             	movups %xmm0,(%rax)
    413d:	e8 ce e2 ff ff       	call   2410 <malloc@plt>
    4142:	48 85 c0             	test   %rax,%rax
    4145:	0f 84 50 04 00 00    	je     459b <send_headers+0x4fb>
    414b:	66 0f 6f 05 1d 28 00 00 	movdqa 0x281d(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4153:	48 89 45 10          	mov    %rax,0x10(%rbp)
    4157:	4c 89 e7             	mov    %r12,%rdi
    415a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    4164:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    416c:	0f 11 00             	movups %xmm0,(%rax)
    416f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    4173:	be 2e 00 00 00       	mov    $0x2e,%esi
    4178:	e8 e3 e1 ff ff       	call   2360 <strrchr@plt>
    417d:	48 85 c0             	test   %rax,%rax
    4180:	0f 84 ea 02 00 00    	je     4470 <send_headers+0x3d0>
    4186:	4c 39 e0             	cmp    %r12,%rax
    4189:	0f 84 e1 02 00 00    	je     4470 <send_headers+0x3d0>
    418f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    4193:	48 8d 3d 03 1f 00 00 	lea    0x1f03(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    419a:	48 89 de             	mov    %rbx,%rsi
    419d:	e8 0e e2 ff ff       	call   23b0 <strcmp@plt>
    41a2:	85 c0                	test   %eax,%eax
    41a4:	75 20                	jne    41c6 <send_headers+0x126>
    41a6:	66 0f 6f 05 d2 27 00 00 	movdqa 0x27d2(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    41ae:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41b6:	66 0f 6f 05 d2 27 00 00 	movdqa 0x27d2(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    41be:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    41c6:	48 89 de             	mov    %rbx,%rsi
    41c9:	48 8d 3d d1 1e 00 00 	lea    0x1ed1(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    41d0:	e8 db e1 ff ff       	call   23b0 <strcmp@plt>
    41d5:	85 c0                	test   %eax,%eax
    41d7:	75 20                	jne    41f9 <send_headers+0x159>
    41d9:	66 0f 6f 05 9f 27 00 00 	movdqa 0x279f(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    41e1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41e9:	66 0f 6f 05 9f 27 00 00 	movdqa 0x279f(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    41f1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    41f9:	48 89 de             	mov    %rbx,%rsi
    41fc:	48 8d 3d a3 1e 00 00 	lea    0x1ea3(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    4203:	e8 a8 e1 ff ff       	call   23b0 <strcmp@plt>
    4208:	85 c0                	test   %eax,%eax
    420a:	0f 84 10 02 00 00    	je     4420 <send_headers+0x380>
    4210:	48 89 de             	mov    %rbx,%rsi
    4213:	48 8d 3d 90 1e 00 00 	lea    0x1e90(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    421a:	e8 91 e1 ff ff       	call   23b0 <strcmp@plt>
    421f:	85 c0                	test   %eax,%eax
    4221:	0f 84 a9 02 00 00    	je     44d0 <send_headers+0x430>
    4227:	48 89 de             	mov    %rbx,%rsi
    422a:	48 8d 3d 7d 1e 00 00 	lea    0x1e7d(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    4231:	e8 7a e1 ff ff       	call   23b0 <strcmp@plt>
    4236:	85 c0                	test   %eax,%eax
    4238:	0f 84 6a 02 00 00    	je     44a8 <send_headers+0x408>
    423e:	48 89 de             	mov    %rbx,%rsi
    4241:	48 8d 3d a9 1e 00 00 	lea    0x1ea9(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    4248:	e8 63 e1 ff ff       	call   23b0 <strcmp@plt>
    424d:	85 c0                	test   %eax,%eax
    424f:	0f 84 2b 02 00 00    	je     4480 <send_headers+0x3e0>
    4255:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4258:	0f 84 52 01 00 00    	je     43b0 <send_headers+0x310>
    425e:	48 89 de             	mov    %rbx,%rsi
    4261:	48 8d 3d 4a 1e 00 00 	lea    0x1e4a(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    4268:	e8 43 e1 ff ff       	call   23b0 <strcmp@plt>
    426d:	85 c0                	test   %eax,%eax
    426f:	0f 84 ab 02 00 00    	je     4520 <send_headers+0x480>
    4275:	48 89 de             	mov    %rbx,%rsi
    4278:	48 8d 3d 37 1e 00 00 	lea    0x1e37(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    427f:	e8 2c e1 ff ff       	call   23b0 <strcmp@plt>
    4284:	85 c0                	test   %eax,%eax
    4286:	0f 84 6c 02 00 00    	je     44f8 <send_headers+0x458>
    428c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4294:	4c 89 e7             	mov    %r12,%rdi
    4297:	e8 84 e0 ff ff       	call   2320 <strlen@plt>
    429c:	48 89 c7             	mov    %rax,%rdi
    429f:	48 89 c3             	mov    %rax,%rbx
    42a2:	e8 69 e1 ff ff       	call   2410 <malloc@plt>
    42a7:	48 85 c0             	test   %rax,%rax
    42aa:	0f 84 eb 02 00 00    	je     459b <send_headers+0x4fb>
    42b0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    42b4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
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
    42e1:	4d 89 e8             	mov    %r13,%r8
    42e4:	48 8d 0d cf 1d 00 00 	lea    0x1dcf(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    42eb:	4c 89 e7             	mov    %r12,%rdi
    42ee:	31 c0                	xor    %eax,%eax
    42f0:	ba 00 04 00 00       	mov    $0x400,%edx
    42f5:	be 01 00 00 00       	mov    $0x1,%esi
    42fa:	e8 21 e2 ff ff       	call   2520 <__sprintf_chk@plt>
    42ff:	4c 89 e7             	mov    %r12,%rdi
    4302:	e8 19 e0 ff ff       	call   2320 <strlen@plt>
    4307:	48 89 c7             	mov    %rax,%rdi
    430a:	48 89 c3             	mov    %rax,%rbx
    430d:	e8 fe e0 ff ff       	call   2410 <malloc@plt>
    4312:	48 85 c0             	test   %rax,%rax
    4315:	0f 84 80 02 00 00    	je     459b <send_headers+0x4fb>
    431b:	48 89 45 30          	mov    %rax,0x30(%rbp)
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
    434c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    4351:	bf 02 00 00 00       	mov    $0x2,%edi
    4356:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    435e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4366:	e8 a5 e0 ff ff       	call   2410 <malloc@plt>
    436b:	48 85 c0             	test   %rax,%rax
    436e:	0f 84 27 02 00 00    	je     459b <send_headers+0x4fb>
    4374:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    437c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    4380:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4388:	66 89 10             	mov    %dx,(%rax)
    438b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4393:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    439c:	0f 85 20 02 00 00    	jne    45c2 <send_headers+0x522>
    43a2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    43a9:	5b                   	pop    %rbx
    43aa:	5d                   	pop    %rbp
    43ab:	41 5c                	pop    %r12
    43ad:	41 5d                	pop    %r13
    43af:	c3                   	ret
    43b0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    43b4:	0f 85 a4 fe ff ff    	jne    425e <send_headers+0x1be>
    43ba:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    43be:	0f 85 9a fe ff ff    	jne    425e <send_headers+0x1be>
    43c4:	66 0f 6f 05 14 26 00 00 	movdqa 0x2614(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
    43cc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    43d6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    43de:	66 0f 6f 05 0a 26 00 00 	movdqa 0x260a(%rip),%xmm0        # 69f0 <_IO_stdin_used+0x9f0>
    43e6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    43ee:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    43f6:	e9 63 fe ff ff       	jmp    425e <send_headers+0x1be>
    43fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4400:	89 da                	mov    %ebx,%edx
    4402:	48 89 c7             	mov    %rax,%rdi
    4405:	4c 89 e6             	mov    %r12,%rsi
    4408:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    440d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4412:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4415:	c1 e9 03             	shr    $0x3,%ecx
    4418:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    441b:	e9 c1 fe ff ff       	jmp    42e1 <send_headers+0x241>
    4420:	66 0f 6f 05 58 25 00 00 	movdqa 0x2558(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4428:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4430:	66 0f 6f 05 68 25 00 00 	movdqa 0x2568(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    4438:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4440:	e9 cb fd ff ff       	jmp    4210 <send_headers+0x170>
    4445:	0f 1f 00             	nopl   (%rax)
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
    4470:	48 8d 1d 58 1c 00 00 	lea    0x1c58(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    4477:	e9 94 fd ff ff       	jmp    4210 <send_headers+0x170>
    447c:	0f 1f 40 00          	nopl   0x0(%rax)
    4480:	66 0f 6f 05 38 25 00 00 	movdqa 0x2538(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4488:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4490:	66 0f 6f 05 38 25 00 00 	movdqa 0x2538(%rip),%xmm0        # 69d0 <_IO_stdin_used+0x9d0>
    4498:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44a0:	e9 b0 fd ff ff       	jmp    4255 <send_headers+0x1b5>
    44a5:	0f 1f 00             	nopl   (%rax)
    44a8:	66 0f 6f 05 10 25 00 00 	movdqa 0x2510(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    44b0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44b8:	66 0f 6f 05 10 25 00 00 	movdqa 0x2510(%rip),%xmm0        # 69d0 <_IO_stdin_used+0x9d0>
    44c0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44c8:	e9 71 fd ff ff       	jmp    423e <send_headers+0x19e>
    44cd:	0f 1f 00             	nopl   (%rax)
    44d0:	66 0f 6f 05 a8 24 00 00 	movdqa 0x24a8(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    44d8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    44e0:	66 0f 6f 05 c8 24 00 00 	movdqa 0x24c8(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    44e8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    44f0:	e9 32 fd ff ff       	jmp    4227 <send_headers+0x187>
    44f5:	0f 1f 00             	nopl   (%rax)
    44f8:	66 0f 6f 05 c0 24 00 00 	movdqa 0x24c0(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4500:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4508:	66 0f 6f 05 00 25 00 00 	movdqa 0x2500(%rip),%xmm0        # 6a10 <_IO_stdin_used+0xa10>
    4510:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4518:	e9 6f fd ff ff       	jmp    428c <send_headers+0x1ec>
    451d:	0f 1f 00             	nopl   (%rax)
    4520:	66 0f 6f 05 98 24 00 00 	movdqa 0x2498(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4528:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4530:	66 0f 6f 05 c8 24 00 00 	movdqa 0x24c8(%rip),%xmm0        # 6a00 <_IO_stdin_used+0xa00>
    4538:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4540:	e9 30 fd ff ff       	jmp    4275 <send_headers+0x1d5>
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
    459b:	48 8b 0d 7e 4a 00 00 	mov    0x4a7e(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    45a2:	ba 28 00 00 00       	mov    $0x28,%edx
    45a7:	be 01 00 00 00       	mov    $0x1,%esi
    45ac:	48 8d 3d 4d 1e 00 00 	lea    0x1e4d(%rip),%rdi        # 6400 <_IO_stdin_used+0x400>
    45b3:	e8 08 df ff ff       	call   24c0 <fwrite@plt>
    45b8:	bf 01 00 00 00       	mov    $0x1,%edi
    45bd:	e8 de de ff ff       	call   24a0 <exit@plt>
    45c2:	e8 69 dd ff ff       	call   2330 <__stack_chk_fail@plt>
    45c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000045d0 <copy_file_contents>:
    45d0:	f3 0f 1e fa          	endbr64
    45d4:	41 55                	push   %r13
    45d6:	49 89 d5             	mov    %rdx,%r13
    45d9:	41 54                	push   %r12
    45db:	49 89 fc             	mov    %rdi,%r12
    45de:	48 89 f7             	mov    %rsi,%rdi
    45e1:	55                   	push   %rbp
    45e2:	53                   	push   %rbx
    45e3:	48 89 f3             	mov    %rsi,%rbx
    45e6:	48 83 ec 08          	sub    $0x8,%rsp
    45ea:	e8 21 de ff ff       	call   2410 <malloc@plt>
    45ef:	48 85 c0             	test   %rax,%rax
    45f2:	74 77                	je     466b <copy_file_contents+0x9b>
    45f4:	4c 89 e7             	mov    %r12,%rdi
    45f7:	48 89 c5             	mov    %rax,%rbp
    45fa:	31 f6                	xor    %esi,%esi
    45fc:	31 c0                	xor    %eax,%eax
    45fe:	e8 7d de ff ff       	call   2480 <open@plt>
    4603:	41 89 c4             	mov    %eax,%r12d
    4606:	85 c0                	test   %eax,%eax
    4608:	78 55                	js     465f <copy_file_contents+0x8f>
    460a:	48 89 da             	mov    %rbx,%rdx
    460d:	48 89 ee             	mov    %rbp,%rsi
    4610:	89 c7                	mov    %eax,%edi
    4612:	e8 79 dd ff ff       	call   2390 <read@plt>
    4617:	48 98                	cltq
    4619:	48 39 d8             	cmp    %rbx,%rax
    461c:	7c 22                	jl     4640 <copy_file_contents+0x70>
    461e:	44 89 e7             	mov    %r12d,%edi
    4621:	e8 4a dd ff ff       	call   2370 <close@plt>
    4626:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    462a:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    462e:	48 83 c4 08          	add    $0x8,%rsp
    4632:	5b                   	pop    %rbx
    4633:	5d                   	pop    %rbp
    4634:	41 5c                	pop    %r12
    4636:	41 5d                	pop    %r13
    4638:	c3                   	ret
    4639:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4640:	48 8b 0d d9 49 00 00 	mov    0x49d9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4647:	ba 1a 00 00 00       	mov    $0x1a,%edx
    464c:	be 01 00 00 00       	mov    $0x1,%esi
    4651:	48 8d 3d 78 1a 00 00 	lea    0x1a78(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    4658:	e8 63 de ff ff       	call   24c0 <fwrite@plt>
    465d:	eb bf                	jmp    461e <copy_file_contents+0x4e>
    465f:	48 8d 3d 99 1b 00 00 	lea    0x1b99(%rip),%rdi        # 61ff <_IO_stdin_used+0x1ff>
    4666:	e8 55 f9 ff ff       	call   3fc0 <fatal_error>
    466b:	48 8b 0d ae 49 00 00 	mov    0x49ae(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4672:	ba 28 00 00 00       	mov    $0x28,%edx
    4677:	be 01 00 00 00       	mov    $0x1,%esi
    467c:	48 8d 3d 7d 1d 00 00 	lea    0x1d7d(%rip),%rdi        # 6400 <_IO_stdin_used+0x400>
    4683:	e8 38 de ff ff       	call   24c0 <fwrite@plt>
    4688:	bf 01 00 00 00       	mov    $0x1,%edi
    468d:	e8 0e de ff ff       	call   24a0 <exit@plt>
    4692:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    469d:	0f 1f 00             	nopl   (%rax)

00000000000046a0 <add_write_request>:
    46a0:	f3 0f 1e fa          	endbr64
    46a4:	8b 46 44             	mov    0x44(%rsi),%eax
    46a7:	48 89 fa             	mov    %rdi,%rdx
    46aa:	48 89 f7             	mov    %rsi,%rdi
    46ad:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    46b3:	8d 70 01             	lea    0x1(%rax),%esi
    46b6:	48 8b 07             	mov    (%rdi),%rax
    46b9:	44 8b 00             	mov    (%rax),%r8d
    46bc:	f6 c1 02             	test   $0x2,%cl
    46bf:	74 00                	je     46c1 <add_write_request+0x21>
    46c1:	89 f0                	mov    %esi,%eax
    46c3:	44 29 c0             	sub    %r8d,%eax
    46c6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    46c9:	0f 82 71 de ff ff    	jb     2540 <add_write_request.cold>
    46cf:	c1 e9 0a             	shr    $0xa,%ecx
    46d2:	48 83 ec 08          	sub    $0x8,%rsp
    46d6:	8b 47 44             	mov    0x44(%rdi),%eax
    46d9:	23 47 58             	and    0x58(%rdi),%eax
    46dc:	83 e1 01             	and    $0x1,%ecx
    46df:	89 77 44             	mov    %esi,0x44(%rdi)
    46e2:	8b 72 08             	mov    0x8(%rdx),%esi
    46e5:	66 0f ef c0          	pxor   %xmm0,%xmm0
    46e9:	d3 e0                	shl    %cl,%eax
    46eb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    46ee:	48 c1 e0 06          	shl    $0x6,%rax
    46f2:	48 03 47 38          	add    0x38(%rdi),%rax
    46f6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    46fc:	89 70 04             	mov    %esi,0x4(%rax)
    46ff:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    4703:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4709:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4711:	48 89 70 10          	mov    %rsi,0x10(%rax)
    4715:	89 48 18             	mov    %ecx,0x18(%rax)
    4718:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    471f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4727:	48 89 50 20          	mov    %rdx,0x20(%rax)
    472b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    472f:	e8 0c dc ff ff       	call   2340 <io_uring_submit@plt>
    4734:	31 c0                	xor    %eax,%eax
    4736:	48 83 c4 08          	add    $0x8,%rsp
    473a:	c3                   	ret
    473b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004740 <add_read_request>:
    4740:	f3 0f 1e fa          	endbr64
    4744:	41 55                	push   %r13
    4746:	41 89 fd             	mov    %edi,%r13d
    4749:	41 54                	push   %r12
    474b:	55                   	push   %rbp
    474c:	53                   	push   %rbx
    474d:	48 89 f3             	mov    %rsi,%rbx
    4750:	48 83 ec 08          	sub    $0x8,%rsp
    4754:	8b 46 44             	mov    0x44(%rsi),%eax
    4757:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    475d:	48 8b 16             	mov    (%rsi),%rdx
    4760:	83 c0 01             	add    $0x1,%eax
    4763:	8b 32                	mov    (%rdx),%esi
    4765:	f6 c1 02             	test   $0x2,%cl
    4768:	74 00                	je     476a <add_read_request+0x2a>
    476a:	89 c2                	mov    %eax,%edx
    476c:	29 f2                	sub    %esi,%edx
    476e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4771:	0f 82 d9 dd ff ff    	jb     2550 <add_read_request.cold>
    4777:	8b 6b 44             	mov    0x44(%rbx),%ebp
    477a:	c1 e9 0a             	shr    $0xa,%ecx
    477d:	89 43 44             	mov    %eax,0x44(%rbx)
    4780:	bf 20 00 00 00       	mov    $0x20,%edi
    4785:	83 e1 01             	and    $0x1,%ecx
    4788:	23 6b 58             	and    0x58(%rbx),%ebp
    478b:	d3 e5                	shl    %cl,%ebp
    478d:	48 c1 e5 06          	shl    $0x6,%rbp
    4791:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4795:	e8 76 dc ff ff       	call   2410 <malloc@plt>
    479a:	be 01 00 00 00       	mov    $0x1,%esi
    479f:	bf 00 20 00 00       	mov    $0x2000,%edi
    47a4:	49 89 c4             	mov    %rax,%r12
    47a7:	e8 f4 db ff ff       	call   23a0 <calloc@plt>
    47ac:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    47b1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    47b5:	48 89 df             	mov    %rbx,%rdi
    47b8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    47bd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    47c2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    47cb:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    47d3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    47d7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    47db:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    47e2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    47ea:	48 89 45 10          	mov    %rax,0x10(%rbp)
    47ee:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    47f6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    47fe:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4802:	e8 39 db ff ff       	call   2340 <io_uring_submit@plt>
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
    4820:	f3 0f 1e fa          	endbr64
    4824:	41 56                	push   %r14
    4826:	41 89 f6             	mov    %esi,%r14d
    4829:	41 55                	push   %r13
    482b:	49 89 fd             	mov    %rdi,%r13
    482e:	bf 20 00 00 00       	mov    $0x20,%edi
    4833:	41 54                	push   %r12
    4835:	55                   	push   %rbp
    4836:	48 89 d5             	mov    %rdx,%rbp
    4839:	53                   	push   %rbx
    483a:	e8 d1 db ff ff       	call   2410 <malloc@plt>
    483f:	48 85 c0             	test   %rax,%rax
    4842:	0f 84 dd 00 00 00    	je     4925 <_send_static_string_content+0x105>
    4848:	48 89 c3             	mov    %rax,%rbx
    484b:	4c 89 ef             	mov    %r13,%rdi
    484e:	e8 cd da ff ff       	call   2320 <strlen@plt>
    4853:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    485a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    485e:	48 89 c7             	mov    %rax,%rdi
    4861:	49 89 c4             	mov    %rax,%r12
    4864:	e8 a7 db ff ff       	call   2410 <malloc@plt>
    4869:	48 89 c7             	mov    %rax,%rdi
    486c:	48 85 c0             	test   %rax,%rax
    486f:	0f 84 b0 00 00 00    	je     4925 <_send_static_string_content+0x105>
    4875:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4879:	4c 89 e2             	mov    %r12,%rdx
    487c:	4c 89 ee             	mov    %r13,%rsi
    487f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4883:	e8 58 db ff ff       	call   23e0 <memcpy@plt>
    4888:	8b 45 44             	mov    0x44(%rbp),%eax
    488b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    4891:	8d 50 01             	lea    0x1(%rax),%edx
    4894:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4898:	8b 30                	mov    (%rax),%esi
    489a:	f6 c1 02             	test   $0x2,%cl
    489d:	0f 85 7d 00 00 00    	jne    4920 <_send_static_string_content+0x100>
    48a3:	89 d0                	mov    %edx,%eax
    48a5:	29 f0                	sub    %esi,%eax
    48a7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    48aa:	0f 82 aa dc ff ff    	jb     255a <_send_static_string_content.cold>
    48b0:	c1 e9 0a             	shr    $0xa,%ecx
    48b3:	8b 45 44             	mov    0x44(%rbp),%eax
    48b6:	23 45 58             	and    0x58(%rbp),%eax
    48b9:	89 55 44             	mov    %edx,0x44(%rbp)
    48bc:	83 e1 01             	and    $0x1,%ecx
    48bf:	8b 53 04             	mov    0x4(%rbx),%edx
    48c2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    48c8:	66 0f ef c0          	pxor   %xmm0,%xmm0
    48cc:	d3 e0                	shl    %cl,%eax
    48ce:	8b 4b 08             	mov    0x8(%rbx),%ecx
    48d1:	48 89 ef             	mov    %rbp,%rdi
    48d4:	48 c1 e0 06          	shl    $0x6,%rax
    48d8:	48 03 45 38          	add    0x38(%rbp),%rax
    48dc:	89 48 04             	mov    %ecx,0x4(%rax)
    48df:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    48e3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    48e9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    48f1:	48 89 48 10          	mov    %rcx,0x10(%rax)
    48f5:	89 50 18             	mov    %edx,0x18(%rax)
    48f8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    48ff:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4907:	48 89 58 20          	mov    %rbx,0x20(%rax)
    490b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    490f:	5b                   	pop    %rbx
    4910:	5d                   	pop    %rbp
    4911:	41 5c                	pop    %r12
    4913:	41 5d                	pop    %r13
    4915:	41 5e                	pop    %r14
    4917:	e9 24 da ff ff       	jmp    2340 <io_uring_submit@plt>
    491c:	0f 1f 40 00          	nopl   0x0(%rax)
    4920:	e9 7e ff ff ff       	jmp    48a3 <_send_static_string_content+0x83>
    4925:	48 8b 0d f4 46 00 00 	mov    0x46f4(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    492c:	ba 28 00 00 00       	mov    $0x28,%edx
    4931:	be 01 00 00 00       	mov    $0x1,%esi
    4936:	48 8d 3d c3 1a 00 00 	lea    0x1ac3(%rip),%rdi        # 6400 <_IO_stdin_used+0x400>
    493d:	e8 7e db ff ff       	call   24c0 <fwrite@plt>
    4942:	bf 01 00 00 00       	mov    $0x1,%edi
    4947:	e8 54 db ff ff       	call   24a0 <exit@plt>
    494c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004950 <handle_unimplemented_method>:
    4950:	f3 0f 1e fa          	endbr64
    4954:	48 89 f2             	mov    %rsi,%rdx
    4957:	89 fe                	mov    %edi,%esi
    4959:	48 8b 3d b8 46 00 00 	mov    0x46b8(%rip),%rdi        # 9018 <unimplemented_content>
    4960:	e9 bb fe ff ff       	jmp    4820 <_send_static_string_content>
    4965:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004970 <handle_http_404>:
    4970:	f3 0f 1e fa          	endbr64
    4974:	48 89 f2             	mov    %rsi,%rdx
    4977:	89 fe                	mov    %edi,%esi
    4979:	48 8b 3d 90 46 00 00 	mov    0x4690(%rip),%rdi        # 9010 <http_404_content>
    4980:	e9 9b fe ff ff       	jmp    4820 <_send_static_string_content>
    4985:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004990 <handle_get_method>:
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
    49bf:	e8 5c d9 ff ff       	call   2320 <strlen@plt>
    49c4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    49c9:	48 89 c3             	mov    %rax,%rbx
    49cc:	0f 84 b6 00 00 00    	je     4a88 <handle_get_method+0xf8>
    49d2:	b8 69 63 00 00       	mov    $0x6369,%eax
    49d7:	48 89 ee             	mov    %rbp,%rsi
    49da:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    49de:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    49e3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    49eb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    49f3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    49fe:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    4a06:	e8 b5 d9 ff ff       	call   23c0 <__memcpy_chk@plt>
    4a0b:	48 89 e6             	mov    %rsp,%rsi
    4a0e:	4c 89 f7             	mov    %r14,%rdi
    4a11:	e8 ba d9 ff ff       	call   23d0 <stat@plt>
    4a16:	83 f8 ff             	cmp    $0xffffffff,%eax
    4a19:	0f 84 d3 00 00 00    	je     4af2 <handle_get_method+0x162>
    4a1f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4a23:	25 00 f0 00 00       	and    $0xf000,%eax
    4a28:	3d 00 80 00 00       	cmp    $0x8000,%eax
    4a2d:	0f 84 f5 00 00 00    	je     4b28 <handle_get_method+0x198>
    4a33:	48 8b 3d d6 45 00 00 	mov    0x45d6(%rip),%rdi        # 9010 <http_404_content>
    4a3a:	4c 89 ea             	mov    %r13,%rdx
    4a3d:	44 89 e6             	mov    %r12d,%esi
    4a40:	e8 db fd ff ff       	call   4820 <_send_static_string_content>
    4a45:	4c 89 f2             	mov    %r14,%rdx
    4a48:	bf 01 00 00 00       	mov    $0x1,%edi
    4a4d:	31 c0                	xor    %eax,%eax
    4a4f:	48 8d 35 ca 16 00 00 	lea    0x16ca(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    4a56:	e8 f5 d9 ff ff       	call   2450 <__printf_chk@plt>
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
    4a88:	ba 69 63 00 00       	mov    $0x6369,%edx
    4a8d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4a95:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4a9a:	48 89 ee             	mov    %rbp,%rsi
    4a9d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    4aa5:	48 89 c2             	mov    %rax,%rdx
    4aa8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4ab0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    4abb:	e8 00 d9 ff ff       	call   23c0 <__memcpy_chk@plt>
    4ac0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4ac5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    4aca:	48 8d 35 1a 16 00 00 	lea    0x161a(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    4ad1:	48 29 d9             	sub    %rbx,%rcx
    4ad4:	ba 0b 00 00 00       	mov    $0xb,%edx
    4ad9:	e8 e2 d8 ff ff       	call   23c0 <__memcpy_chk@plt>
    4ade:	48 89 e6             	mov    %rsp,%rsi
    4ae1:	4c 89 f7             	mov    %r14,%rdi
    4ae4:	e8 e7 d8 ff ff       	call   23d0 <stat@plt>
    4ae9:	83 f8 ff             	cmp    $0xffffffff,%eax
    4aec:	0f 85 2d ff ff ff    	jne    4a1f <handle_get_method+0x8f>
    4af2:	4c 89 f2             	mov    %r14,%rdx
    4af5:	48 89 e9             	mov    %rbp,%rcx
    4af8:	48 8d 35 f7 15 00 00 	lea    0x15f7(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    4aff:	31 c0                	xor    %eax,%eax
    4b01:	bf 01 00 00 00       	mov    $0x1,%edi
    4b06:	e8 45 d9 ff ff       	call   2450 <__printf_chk@plt>
    4b0b:	48 8b 3d fe 44 00 00 	mov    0x44fe(%rip),%rdi        # 9010 <http_404_content>
    4b12:	4c 89 ea             	mov    %r13,%rdx
    4b15:	44 89 e6             	mov    %r12d,%esi
    4b18:	e8 03 fd ff ff       	call   4820 <_send_static_string_content>
    4b1d:	e9 39 ff ff ff       	jmp    4a5b <handle_get_method+0xcb>
    4b22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b28:	bf 70 00 00 00       	mov    $0x70,%edi
    4b2d:	e8 de d8 ff ff       	call   2410 <malloc@plt>
    4b32:	48 89 c3             	mov    %rax,%rbx
    4b35:	48 85 c0             	test   %rax,%rax
    4b38:	74 5d                	je     4b97 <handle_get_method+0x207>
    4b3a:	44 89 60 08          	mov    %r12d,0x8(%rax)
    4b3e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4b43:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4b47:	4c 89 f7             	mov    %r14,%rdi
    4b4a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    4b51:	e8 4a f5 ff ff       	call   40a0 <send_headers>
    4b56:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4b5b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    4b5f:	4c 89 f7             	mov    %r14,%rdi
    4b62:	e8 69 fa ff ff       	call   45d0 <copy_file_contents>
    4b67:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    4b6c:	4c 89 f2             	mov    %r14,%rdx
    4b6f:	31 c0                	xor    %eax,%eax
    4b71:	48 8d 35 96 15 00 00 	lea    0x1596(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    4b78:	bf 01 00 00 00       	mov    $0x1,%edi
    4b7d:	e8 ce d8 ff ff       	call   2450 <__printf_chk@plt>
    4b82:	4c 89 ee             	mov    %r13,%rsi
    4b85:	48 89 df             	mov    %rbx,%rdi
    4b88:	e8 13 fb ff ff       	call   46a0 <add_write_request>
    4b8d:	e9 c9 fe ff ff       	jmp    4a5b <handle_get_method+0xcb>
    4b92:	e8 99 d7 ff ff       	call   2330 <__stack_chk_fail@plt>
    4b97:	48 8b 0d 82 44 00 00 	mov    0x4482(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4b9e:	ba 28 00 00 00       	mov    $0x28,%edx
    4ba3:	be 01 00 00 00       	mov    $0x1,%esi
    4ba8:	48 8d 3d 51 18 00 00 	lea    0x1851(%rip),%rdi        # 6400 <_IO_stdin_used+0x400>
    4baf:	e8 0c d9 ff ff       	call   24c0 <fwrite@plt>
    4bb4:	bf 01 00 00 00       	mov    $0x1,%edi
    4bb9:	e8 e2 d8 ff ff       	call   24a0 <exit@plt>
    4bbe:	66 90                	xchg   %ax,%ax

0000000000004bc0 <handle_http_method>:
    4bc0:	f3 0f 1e fa          	endbr64
    4bc4:	41 57                	push   %r15
    4bc6:	41 56                	push   %r14
    4bc8:	4c 8d 35 b6 14 00 00 	lea    0x14b6(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
    4bcf:	41 55                	push   %r13
    4bd1:	49 89 d5             	mov    %rdx,%r13
    4bd4:	41 54                	push   %r12
    4bd6:	41 89 f4             	mov    %esi,%r12d
    4bd9:	4c 89 f6             	mov    %r14,%rsi
    4bdc:	55                   	push   %rbp
    4bdd:	53                   	push   %rbx
    4bde:	48 83 ec 18          	sub    $0x18,%rsp
    4be2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4beb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4bf0:	31 c0                	xor    %eax,%eax
    4bf2:	49 89 e7             	mov    %rsp,%r15
    4bf5:	4c 89 fa             	mov    %r15,%rdx
    4bf8:	e8 83 d7 ff ff       	call   2380 <strtok_r@plt>
    4bfd:	48 0f be 18          	movsbq (%rax),%rbx
    4c01:	48 89 c5             	mov    %rax,%rbp
    4c04:	84 db                	test   %bl,%bl
    4c06:	74 1d                	je     4c25 <handle_http_method+0x65>
    4c08:	e8 03 d9 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    4c0d:	48 89 ea             	mov    %rbp,%rdx
    4c10:	48 8b 08             	mov    (%rax),%rcx
    4c13:	48 83 c2 01          	add    $0x1,%rdx
    4c17:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    4c1a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    4c1d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4c21:	84 db                	test   %bl,%bl
    4c23:	75 eb                	jne    4c10 <handle_http_method+0x50>
    4c25:	4c 89 fa             	mov    %r15,%rdx
    4c28:	4c 89 f6             	mov    %r14,%rsi
    4c2b:	31 ff                	xor    %edi,%edi
    4c2d:	e8 4e d7 ff ff       	call   2380 <strtok_r@plt>
    4c32:	48 8d 35 fa 14 00 00 	lea    0x14fa(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    4c39:	48 89 ef             	mov    %rbp,%rdi
    4c3c:	48 89 c3             	mov    %rax,%rbx
    4c3f:	e8 6c d7 ff ff       	call   23b0 <strcmp@plt>
    4c44:	4c 89 ea             	mov    %r13,%rdx
    4c47:	44 89 e6             	mov    %r12d,%esi
    4c4a:	85 c0                	test   %eax,%eax
    4c4c:	75 2a                	jne    4c78 <handle_http_method+0xb8>
    4c4e:	48 89 df             	mov    %rbx,%rdi
    4c51:	e8 3a fd ff ff       	call   4990 <handle_get_method>
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
    4c78:	48 8b 3d 99 43 00 00 	mov    0x4399(%rip),%rdi        # 9018 <unimplemented_content>
    4c7f:	e8 9c fb ff ff       	call   4820 <_send_static_string_content>
    4c84:	eb d0                	jmp    4c56 <handle_http_method+0x96>
    4c86:	e8 a5 d6 ff ff       	call   2330 <__stack_chk_fail@plt>
    4c8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004c90 <get_line>:
    4c90:	f3 0f 1e fa          	endbr64
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
    4cb5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4cb9:	88 06                	mov    %al,(%rsi)
    4cbb:	3c 0d                	cmp    $0xd,%al
    4cbd:	75 e9                	jne    4ca8 <get_line+0x18>
    4cbf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4cc2:	75 e4                	jne    4ca8 <get_line+0x18>
    4cc4:	c6 06 00             	movb   $0x0,(%rsi)
    4cc7:	31 c0                	xor    %eax,%eax
    4cc9:	c3                   	ret
    4cca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4cd0:	b8 01 00 00 00       	mov    $0x1,%eax
    4cd5:	c3                   	ret
    4cd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004ce0 <handle_client_request>:
    4ce0:	f3 0f 1e fa          	endbr64
    4ce4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4ceb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4cef:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4cf8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4d00:	31 c0                	xor    %eax,%eax
    4d02:	49 89 e2             	mov    %rsp,%r10
    4d05:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4d0d:	4c 89 d0             	mov    %r10,%rax
    4d10:	eb 13                	jmp    4d25 <handle_client_request+0x45>
    4d12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4d18:	48 83 c0 01          	add    $0x1,%rax
    4d1c:	48 83 c1 01          	add    $0x1,%rcx
    4d20:	4c 39 c8             	cmp    %r9,%rax
    4d23:	74 4b                	je     4d70 <handle_client_request+0x90>
    4d25:	44 0f b6 01          	movzbl (%rcx),%r8d
    4d29:	44 88 00             	mov    %r8b,(%rax)
    4d2c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4d30:	75 e6                	jne    4d18 <handle_client_request+0x38>
    4d32:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4d36:	75 e0                	jne    4d18 <handle_client_request+0x38>
    4d38:	c6 00 00             	movb   $0x0,(%rax)
    4d3b:	8b 47 08             	mov    0x8(%rdi),%eax
    4d3e:	48 89 f2             	mov    %rsi,%rdx
    4d41:	4c 89 d7             	mov    %r10,%rdi
    4d44:	89 c6                	mov    %eax,%esi
    4d46:	e8 75 fe ff ff       	call   4bc0 <handle_http_method>
    4d4b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4d53:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d5c:	75 39                	jne    4d97 <handle_client_request+0xb7>
    4d5e:	31 c0                	xor    %eax,%eax
    4d60:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4d67:	c3                   	ret
    4d68:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4d70:	48 8b 0d a9 42 00 00 	mov    0x42a9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4d77:	ba 12 00 00 00       	mov    $0x12,%edx
    4d7c:	be 01 00 00 00       	mov    $0x1,%esi
    4d81:	48 8d 3d af 13 00 00 	lea    0x13af(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    4d88:	e8 33 d7 ff ff       	call   24c0 <fwrite@plt>
    4d8d:	bf 01 00 00 00       	mov    $0x1,%edi
    4d92:	e8 09 d7 ff ff       	call   24a0 <exit@plt>
    4d97:	e8 94 d5 ff ff       	call   2330 <__stack_chk_fail@plt>
    4d9c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004da0 <add_accept_request>:
    4da0:	f3 0f 1e fa          	endbr64
    4da4:	55                   	push   %rbp
    4da5:	53                   	push   %rbx
    4da6:	48 89 cb             	mov    %rcx,%rbx
    4da9:	48 83 ec 08          	sub    $0x8,%rsp
    4dad:	8b 41 44             	mov    0x44(%rcx),%eax
    4db0:	4c 8b 03             	mov    (%rbx),%r8
    4db3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    4db9:	83 c0 01             	add    $0x1,%eax
    4dbc:	45 8b 08             	mov    (%r8),%r9d
    4dbf:	f6 c1 02             	test   $0x2,%cl
    4dc2:	74 00                	je     4dc4 <add_accept_request+0x24>
    4dc4:	41 89 c0             	mov    %eax,%r8d
    4dc7:	45 29 c8             	sub    %r9d,%r8d
    4dca:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4dce:	0f 82 96 d7 ff ff    	jb     256a <add_accept_request.cold>
    4dd4:	c1 e9 0a             	shr    $0xa,%ecx
    4dd7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4dda:	23 6b 58             	and    0x58(%rbx),%ebp
    4ddd:	89 43 44             	mov    %eax,0x44(%rbx)
    4de0:	83 e1 01             	and    $0x1,%ecx
    4de3:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4de7:	d3 e5                	shl    %cl,%ebp
    4de9:	48 c1 e5 06          	shl    $0x6,%rbp
    4ded:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4df1:	89 7d 04             	mov    %edi,0x4(%rbp)
    4df4:	bf 10 00 00 00       	mov    $0x10,%edi
    4df9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    4e00:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    4e04:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    4e08:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    4e10:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    4e18:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4e1c:	e8 ef d5 ff ff       	call   2410 <malloc@plt>
    4e21:	48 89 df             	mov    %rbx,%rdi
    4e24:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    4e2a:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4e2e:	48 83 c4 08          	add    $0x8,%rsp
    4e32:	5b                   	pop    %rbx
    4e33:	5d                   	pop    %rbp
    4e34:	e9 07 d5 ff ff       	jmp    2340 <io_uring_submit@plt>
    4e39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004e40 <io_thread>:
    4e40:	f3 0f 1e fa          	endbr64
    4e44:	41 57                	push   %r15
    4e46:	31 d2                	xor    %edx,%edx
    4e48:	41 56                	push   %r14
    4e4a:	41 55                	push   %r13
    4e4c:	41 54                	push   %r12
    4e4e:	55                   	push   %rbp
    4e4f:	48 89 fd             	mov    %rdi,%rbp
    4e52:	53                   	push   %rbx
    4e53:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4e5a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4e63:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4e6b:	48 8b 87 c8 00 00 00 	mov    0xc8(%rdi),%rax
    4e72:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4e77:	bf 00 01 00 00       	mov    $0x100,%edi
    4e7c:	48 89 de             	mov    %rbx,%rsi
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
    4f3f:	e8 ac d4 ff ff       	call   23f0 <io_uring_queue_init@plt>
    4f44:	48 8b bd c8 00 00 00 	mov    0xc8(%rbp),%rdi
    4f4b:	31 f6                	xor    %esi,%esi
    4f4d:	e8 8e d5 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
    4f52:	31 d2                	xor    %edx,%edx
    4f54:	be 01 00 00 00       	mov    $0x1,%esi
    4f59:	bf 02 00 00 00       	mov    $0x2,%edi
    4f5e:	e8 cd d5 ff ff       	call   2530 <socket@plt>
    4f63:	83 f8 ff             	cmp    $0xffffffff,%eax
    4f66:	0f 84 02 06 00 00    	je     556e <io_thread+0x72e>
    4f6c:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4f71:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4f77:	89 c7                	mov    %eax,%edi
    4f79:	41 89 c4             	mov    %eax,%r12d
    4f7c:	ba 02 00 00 00       	mov    $0x2,%edx
    4f81:	be 01 00 00 00       	mov    $0x1,%esi
    4f86:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    4f8e:	e8 6d d3 ff ff       	call   2300 <setsockopt@plt>
    4f93:	85 c0                	test   %eax,%eax
    4f95:	0f 88 c7 05 00 00    	js     5562 <io_thread+0x722>
    4f9b:	8b 05 8f 1a 00 00    	mov    0x1a8f(%rip),%eax        # 6a30 <_IO_stdin_used+0xa30>
    4fa1:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    4fa6:	ba 10 00 00 00       	mov    $0x10,%edx
    4fab:	44 89 e7             	mov    %r12d,%edi
    4fae:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4fb7:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    4fbf:	89 44 24 40          	mov    %eax,0x40(%rsp)
    4fc3:	e8 98 d4 ff ff       	call   2460 <bind@plt>
    4fc8:	85 c0                	test   %eax,%eax
    4fca:	0f 88 86 05 00 00    	js     5556 <io_thread+0x716>
    4fd0:	be 0a 00 00 00       	mov    $0xa,%esi
    4fd5:	44 89 e7             	mov    %r12d,%edi
    4fd8:	e8 43 d4 ff ff       	call   2420 <listen@plt>
    4fdd:	85 c0                	test   %eax,%eax
    4fdf:	0f 88 65 05 00 00    	js     554a <io_thread+0x70a>
    4fe5:	ba db 18 00 00       	mov    $0x18db,%edx
    4fea:	48 8d 35 8b 11 00 00 	lea    0x118b(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4ff1:	bf 01 00 00 00       	mov    $0x1,%edi
    4ff6:	31 c0                	xor    %eax,%eax
    4ff8:	e8 53 d4 ff ff       	call   2450 <__printf_chk@plt>
    4ffd:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5002:	48 89 d9             	mov    %rbx,%rcx
    5005:	44 89 e7             	mov    %r12d,%edi
    5008:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    500d:	48 89 c6             	mov    %rax,%rsi
    5010:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    5015:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    501a:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    5022:	e8 79 fd ff ff       	call   4da0 <add_accept_request>
    5027:	bf 01 00 00 00       	mov    $0x1,%edi
    502c:	be 10 00 00 00       	mov    $0x10,%esi
    5031:	e8 6a d3 ff ff       	call   23a0 <calloc@plt>
    5036:	bf 0a 00 00 00       	mov    $0xa,%edi
    503b:	49 89 c5             	mov    %rax,%r13
    503e:	e8 cd d3 ff ff       	call   2410 <malloc@plt>
    5043:	48 85 c0             	test   %rax,%rax
    5046:	0f 84 d7 04 00 00    	je     5523 <io_thread+0x6e3>
    504c:	49 89 45 00          	mov    %rax,0x0(%r13)
    5050:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5057:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    505e:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    5066:	8d 50 01             	lea    0x1(%rax),%edx
    5069:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    506e:	8b 30                	mov    (%rax),%esi
    5070:	f6 c1 02             	test   $0x2,%cl
    5073:	0f 85 27 04 00 00    	jne    54a0 <io_thread+0x660>
    5079:	89 d0                	mov    %edx,%eax
    507b:	29 f0                	sub    %esi,%eax
    507d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5084:	0f 82 ea d4 ff ff    	jb     2574 <io_thread.cold>
    508a:	c1 e9 0a             	shr    $0xa,%ecx
    508d:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5094:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5098:	48 89 df             	mov    %rbx,%rdi
    509b:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    50a2:	83 e1 01             	and    $0x1,%ecx
    50a5:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    50ac:	48 8d b5 d0 00 00 00 	lea    0xd0(%rbp),%rsi
    50b3:	8b 95 d0 00 00 00    	mov    0xd0(%rbp),%edx
    50b9:	d3 e0                	shl    %cl,%eax
    50bb:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    50c0:	48 c1 e0 06          	shl    $0x6,%rax
    50c4:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    50cc:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    50d2:	89 50 04             	mov    %edx,0x4(%rax)
    50d5:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    50dd:	4c 89 68 10          	mov    %r13,0x10(%rax)
    50e1:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    50e9:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    50f1:	48 89 70 20          	mov    %rsi,0x20(%rax)
    50f5:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    50f9:	e8 42 d2 ff ff       	call   2340 <io_uring_submit@plt>
    50fe:	8b 45 64             	mov    0x64(%rbp),%eax
    5101:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5106:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    510e:	83 f8 01             	cmp    $0x1,%eax
    5111:	0f 85 af 01 00 00    	jne    52c6 <io_thread+0x486>
    5117:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    511c:	4d 89 ce             	mov    %r9,%r14
    511f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5124:	0f 1f 40 00          	nopl   0x0(%rax)
    5128:	48 8d 3d 63 10 00 00 	lea    0x1063(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    512f:	e8 bc d1 ff ff       	call   22f0 <puts@plt>
    5134:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    513b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    5142:	c1 e9 0b             	shr    $0xb,%ecx
    5145:	83 e1 01             	and    $0x1,%ecx
    5148:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5150:	8b 00                	mov    (%rax),%eax
    5152:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    515a:	8b 16                	mov    (%rsi),%edx
    515c:	39 d0                	cmp    %edx,%eax
    515e:	74 36                	je     5196 <io_thread+0x356>
    5160:	89 f8                	mov    %edi,%eax
    5162:	21 d0                	and    %edx,%eax
    5164:	d3 e0                	shl    %cl,%eax
    5166:	48 c1 e0 04          	shl    $0x4,%rax
    516a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    5172:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    517a:	0f 85 80 01 00 00    	jne    5300 <io_thread+0x4c0>
    5180:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5184:	0f 85 1e 03 00 00    	jne    54a8 <io_thread+0x668>
    518a:	8b 40 08             	mov    0x8(%rax),%eax
    518d:	83 c2 01             	add    $0x1,%edx
    5190:	89 16                	mov    %edx,(%rsi)
    5192:	85 c0                	test   %eax,%eax
    5194:	79 b2                	jns    5148 <io_thread+0x308>
    5196:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    519f:	90                   	nop
    51a0:	45 31 c0             	xor    %r8d,%r8d
    51a3:	31 d2                	xor    %edx,%edx
    51a5:	b9 01 00 00 00       	mov    $0x1,%ecx
    51aa:	4c 89 f6             	mov    %r14,%rsi
    51ad:	48 89 df             	mov    %rbx,%rdi
    51b0:	e8 8b d2 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    51b5:	41 89 c7             	mov    %eax,%r15d
    51b8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    51bd:	48 83 38 01          	cmpq   $0x1,(%rax)
    51c1:	0f 84 f1 02 00 00    	je     54b8 <io_thread+0x678>
    51c7:	48 8d 3d ea 0f 00 00 	lea    0xfea(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    51ce:	e8 1d d1 ff ff       	call   22f0 <puts@plt>
    51d3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    51d8:	4c 8b 22             	mov    (%rdx),%r12
    51db:	45 85 ff             	test   %r15d,%r15d
    51de:	0f 88 2e 03 00 00    	js     5512 <io_thread+0x6d2>
    51e4:	8b 42 08             	mov    0x8(%rdx),%eax
    51e7:	45 8b 04 24          	mov    (%r12),%r8d
    51eb:	85 c0                	test   %eax,%eax
    51ed:	0f 88 e5 02 00 00    	js     54d8 <io_thread+0x698>
    51f3:	41 83 f8 01          	cmp    $0x1,%r8d
    51f7:	0f 84 3b 01 00 00    	je     5338 <io_thread+0x4f8>
    51fd:	41 83 f8 02          	cmp    $0x2,%r8d
    5201:	0f 84 b1 01 00 00    	je     53b8 <io_thread+0x578>
    5207:	45 85 c0             	test   %r8d,%r8d
    520a:	0f 84 70 01 00 00    	je     5380 <io_thread+0x540>
    5210:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5218:	8b 02                	mov    (%rdx),%eax
    521a:	83 c0 01             	add    $0x1,%eax
    521d:	89 02                	mov    %eax,(%rdx)
    521f:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5226:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    522d:	8d 50 01             	lea    0x1(%rax),%edx
    5230:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5235:	8b 30                	mov    (%rax),%esi
    5237:	f6 c1 02             	test   $0x2,%cl
    523a:	74 00                	je     523c <io_thread+0x3fc>
    523c:	89 d0                	mov    %edx,%eax
    523e:	29 f0                	sub    %esi,%eax
    5240:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5247:	0f 82 27 d3 ff ff    	jb     2574 <io_thread.cold>
    524d:	c1 e9 0a             	shr    $0xa,%ecx
    5250:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    5255:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5259:	48 89 df             	mov    %rbx,%rdi
    525c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5263:	83 e1 01             	and    $0x1,%ecx
    5266:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    526d:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5274:	d3 e0                	shl    %cl,%eax
    5276:	8b 95 d0 00 00 00    	mov    0xd0(%rbp),%edx
    527c:	48 c1 e0 06          	shl    $0x6,%rax
    5280:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5288:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    528e:	89 50 04             	mov    %edx,0x4(%rax)
    5291:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5299:	4c 89 68 10          	mov    %r13,0x10(%rax)
    529d:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    52a5:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    52ad:	48 89 70 20          	mov    %rsi,0x20(%rax)
    52b1:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    52b5:	e8 86 d0 ff ff       	call   2340 <io_uring_submit@plt>
    52ba:	8b 45 64             	mov    0x64(%rbp),%eax
    52bd:	83 f8 01             	cmp    $0x1,%eax
    52c0:	0f 84 62 fe ff ff    	je     5128 <io_thread+0x2e8>
    52c6:	48 8d 3d 24 0f 00 00 	lea    0xf24(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    52cd:	e8 1e d0 ff ff       	call   22f0 <puts@plt>
    52d2:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    52da:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    52e3:	0f 85 35 02 00 00    	jne    551e <io_thread+0x6de>
    52e9:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    52f0:	31 c0                	xor    %eax,%eax
    52f2:	5b                   	pop    %rbx
    52f3:	5d                   	pop    %rbp
    52f4:	41 5c                	pop    %r12
    52f6:	41 5d                	pop    %r13
    52f8:	41 5e                	pop    %r14
    52fa:	41 5f                	pop    %r15
    52fc:	c3                   	ret
    52fd:	0f 1f 00             	nopl   (%rax)
    5300:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    5305:	48 85 c0             	test   %rax,%rax
    5308:	0f 84 92 fe ff ff    	je     51a0 <io_thread+0x360>
    530e:	48 83 38 01          	cmpq   $0x1,(%rax)
    5312:	0f 84 a0 01 00 00    	je     54b8 <io_thread+0x678>
    5318:	48 8d 3d 99 0e 00 00 	lea    0xe99(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    531f:	e8 cc cf ff ff       	call   22f0 <puts@plt>
    5324:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5329:	4c 8b 22             	mov    (%rdx),%r12
    532c:	e9 b3 fe ff ff       	jmp    51e4 <io_thread+0x3a4>
    5331:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5338:	85 c0                	test   %eax,%eax
    533a:	0f 85 c0 00 00 00    	jne    5400 <io_thread+0x5c0>
    5340:	48 8b 0d d9 3c 00 00 	mov    0x3cd9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5347:	ba 0f 00 00 00       	mov    $0xf,%edx
    534c:	be 01 00 00 00       	mov    $0x1,%esi
    5351:	48 8d 3d 89 0e 00 00 	lea    0xe89(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    5358:	e8 63 d1 ff ff       	call   24c0 <fwrite@plt>
    535d:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5362:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5368:	48 85 c0             	test   %rax,%rax
    536b:	0f 84 ae fe ff ff    	je     521f <io_thread+0x3df>
    5371:	e9 9a fe ff ff       	jmp    5210 <io_thread+0x3d0>
    5376:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5380:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    5385:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    538a:	48 89 d9             	mov    %rbx,%rcx
    538d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5391:	e8 0a fa ff ff       	call   4da0 <add_accept_request>
    5396:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    539b:	48 89 de             	mov    %rbx,%rsi
    539e:	8b 78 08             	mov    0x8(%rax),%edi
    53a1:	e8 9a f3 ff ff       	call   4740 <add_read_request>
    53a6:	4c 89 e7             	mov    %r12,%rdi
    53a9:	e8 12 cf ff ff       	call   22c0 <free@plt>
    53ae:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    53b3:	eb b3                	jmp    5368 <io_thread+0x528>
    53b5:	0f 1f 00             	nopl   (%rax)
    53b8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    53bd:	45 31 ff             	xor    %r15d,%r15d
    53c0:	85 c0                	test   %eax,%eax
    53c2:	7e 20                	jle    53e4 <io_thread+0x5a4>
    53c4:	0f 1f 40 00          	nopl   0x0(%rax)
    53c8:	4c 89 f8             	mov    %r15,%rax
    53cb:	49 83 c7 01          	add    $0x1,%r15
    53cf:	48 c1 e0 04          	shl    $0x4,%rax
    53d3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    53d8:	e8 e3 ce ff ff       	call   22c0 <free@plt>
    53dd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    53e2:	7f e4                	jg     53c8 <io_thread+0x588>
    53e4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    53e9:	e8 82 cf ff ff       	call   2370 <close@plt>
    53ee:	4c 89 e7             	mov    %r12,%rdi
    53f1:	e8 ca ce ff ff       	call   22c0 <free@plt>
    53f6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    53fb:	e9 68 ff ff ff       	jmp    5368 <io_thread+0x528>
    5400:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5405:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    540a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5412:	eb 11                	jmp    5425 <io_thread+0x5e5>
    5414:	0f 1f 40 00          	nopl   0x0(%rax)
    5418:	48 83 c0 01          	add    $0x1,%rax
    541c:	48 83 c2 01          	add    $0x1,%rdx
    5420:	48 39 c6             	cmp    %rax,%rsi
    5423:	74 4b                	je     5470 <io_thread+0x630>
    5425:	0f b6 0a             	movzbl (%rdx),%ecx
    5428:	88 08                	mov    %cl,(%rax)
    542a:	80 f9 0d             	cmp    $0xd,%cl
    542d:	75 e9                	jne    5418 <io_thread+0x5d8>
    542f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5433:	75 e3                	jne    5418 <io_thread+0x5d8>
    5435:	c6 00 00             	movb   $0x0,(%rax)
    5438:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    543d:	48 89 da             	mov    %rbx,%rdx
    5440:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5445:	e8 76 f7 ff ff       	call   4bc0 <handle_http_method>
    544a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    544f:	e8 6c ce ff ff       	call   22c0 <free@plt>
    5454:	4c 89 e7             	mov    %r12,%rdi
    5457:	e8 64 ce ff ff       	call   22c0 <free@plt>
    545c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5461:	e9 02 ff ff ff       	jmp    5368 <io_thread+0x528>
    5466:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5470:	48 8b 0d a9 3b 00 00 	mov    0x3ba9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5477:	ba 12 00 00 00       	mov    $0x12,%edx
    547c:	be 01 00 00 00       	mov    $0x1,%esi
    5481:	48 8d 3d af 0c 00 00 	lea    0xcaf(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    5488:	e8 33 d0 ff ff       	call   24c0 <fwrite@plt>
    548d:	bf 01 00 00 00       	mov    $0x1,%edi
    5492:	e8 09 d0 ff ff       	call   24a0 <exit@plt>
    5497:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    54a0:	e9 d4 fb ff ff       	jmp    5079 <io_thread+0x239>
    54a5:	0f 1f 00             	nopl   (%rax)
    54a8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    54ad:	e9 5c fe ff ff       	jmp    530e <io_thread+0x4ce>
    54b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    54b8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    54c0:	48 8d 3d dd 0c 00 00 	lea    0xcdd(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    54c7:	8b 02                	mov    (%rdx),%eax
    54c9:	83 c0 01             	add    $0x1,%eax
    54cc:	89 02                	mov    %eax,(%rdx)
    54ce:	e8 1d ce ff ff       	call   22f0 <puts@plt>
    54d3:	e9 ee fd ff ff       	jmp    52c6 <io_thread+0x486>
    54d8:	f7 d8                	neg    %eax
    54da:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    54df:	89 c7                	mov    %eax,%edi
    54e1:	e8 1a d0 ff ff       	call   2500 <strerror@plt>
    54e6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    54eb:	be 01 00 00 00       	mov    $0x1,%esi
    54f0:	48 8b 3d 29 3b 00 00 	mov    0x3b29(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    54f7:	48 89 c1             	mov    %rax,%rcx
    54fa:	48 8d 15 2f 0f 00 00 	lea    0xf2f(%rip),%rdx        # 6430 <_IO_stdin_used+0x430>
    5501:	31 c0                	xor    %eax,%eax
    5503:	e8 c8 cf ff ff       	call   24d0 <__fprintf_chk@plt>
    5508:	bf 01 00 00 00       	mov    $0x1,%edi
    550d:	e8 8e cf ff ff       	call   24a0 <exit@plt>
    5512:	48 8d 3d b6 0c 00 00 	lea    0xcb6(%rip),%rdi        # 61cf <_IO_stdin_used+0x1cf>
    5519:	e8 a2 ea ff ff       	call   3fc0 <fatal_error>
    551e:	e8 0d ce ff ff       	call   2330 <__stack_chk_fail@plt>
    5523:	48 8b 0d f6 3a 00 00 	mov    0x3af6(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    552a:	ba 28 00 00 00       	mov    $0x28,%edx
    552f:	be 01 00 00 00       	mov    $0x1,%esi
    5534:	48 8d 3d c5 0e 00 00 	lea    0xec5(%rip),%rdi        # 6400 <_IO_stdin_used+0x400>
    553b:	e8 80 cf ff ff       	call   24c0 <fwrite@plt>
    5540:	bf 01 00 00 00       	mov    $0x1,%edi
    5545:	e8 56 cf ff ff       	call   24a0 <exit@plt>
    554a:	48 8d 3d 22 0c 00 00 	lea    0xc22(%rip),%rdi        # 6173 <_IO_stdin_used+0x173>
    5551:	e8 6a ea ff ff       	call   3fc0 <fatal_error>
    5556:	48 8d 3d 0f 0c 00 00 	lea    0xc0f(%rip),%rdi        # 616c <_IO_stdin_used+0x16c>
    555d:	e8 5e ea ff ff       	call   3fc0 <fatal_error>
    5562:	48 8d 3d ea 0b 00 00 	lea    0xbea(%rip),%rdi        # 6153 <_IO_stdin_used+0x153>
    5569:	e8 52 ea ff ff       	call   3fc0 <fatal_error>
    556e:	48 8d 3d d5 0b 00 00 	lea    0xbd5(%rip),%rdi        # 614a <_IO_stdin_used+0x14a>
    5575:	e8 46 ea ff ff       	call   3fc0 <fatal_error>
    557a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005580 <sendm>:
    5580:	f3 0f 1e fa          	endbr64
    5584:	8b 97 b8 00 00 00    	mov    0xb8(%rdi),%edx
    558a:	48 89 f8             	mov    %rdi,%rax
    558d:	83 fa 01             	cmp    $0x1,%edx
    5590:	74 06                	je     5598 <sendm+0x18>
    5592:	31 c0                	xor    %eax,%eax
    5594:	c3                   	ret
    5595:	0f 1f 00             	nopl   (%rax)
    5598:	8b 57 74             	mov    0x74(%rdi),%edx
    559b:	85 d2                	test   %edx,%edx
    559d:	7e f3                	jle    5592 <sendm+0x12>
    559f:	45 31 d2             	xor    %r10d,%r10d
    55a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    55a8:	8b 50 70             	mov    0x70(%rax),%edx
    55ab:	44 39 d2             	cmp    %r10d,%edx
    55ae:	74 61                	je     5611 <sendm+0x91>
    55b0:	48 8b 90 a8 00 00 00 	mov    0xa8(%rax),%rdx
    55b7:	4c 89 d6             	mov    %r10,%rsi
    55ba:	48 c1 e6 05          	shl    $0x5,%rsi
    55be:	48 8b 4c 32 08       	mov    0x8(%rdx,%rsi,1),%rcx
    55c3:	48 8b 51 08          	mov    0x8(%rcx),%rdx
    55c7:	4c 63 41 10          	movslq 0x10(%rcx),%r8
    55cb:	4c 39 c2             	cmp    %r8,%rdx
    55ce:	7d 41                	jge    5611 <sendm+0x91>
    55d0:	4c 8b 09             	mov    (%rcx),%r9
    55d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    55d8:	48 8b 50 48          	mov    0x48(%rax),%rdx
    55dc:	48 83 c2 01          	add    $0x1,%rdx
    55e0:	48 89 50 48          	mov    %rdx,0x48(%rax)
    55e4:	48 8b 90 a8 00 00 00 	mov    0xa8(%rax),%rdx
    55eb:	48 83 44 32 10 01    	addq   $0x1,0x10(%rdx,%rsi,1)
    55f1:	48 8b 51 08          	mov    0x8(%rcx),%rdx
    55f5:	48 8d 7a 01          	lea    0x1(%rdx),%rdi
    55f9:	48 89 79 08          	mov    %rdi,0x8(%rcx)
    55fd:	48 8b b8 c0 00 00 00 	mov    0xc0(%rax),%rdi
    5604:	49 89 3c d1          	mov    %rdi,(%r9,%rdx,8)
    5608:	48 8b 51 08          	mov    0x8(%rcx),%rdx
    560c:	49 39 d0             	cmp    %rdx,%r8
    560f:	7f c7                	jg     55d8 <sendm+0x58>
    5611:	8b 50 74             	mov    0x74(%rax),%edx
    5614:	49 83 c2 01          	add    $0x1,%r10
    5618:	44 39 d2             	cmp    %r10d,%edx
    561b:	7f 8b                	jg     55a8 <sendm+0x28>
    561d:	31 c0                	xor    %eax,%eax
    561f:	c3                   	ret

0000000000005620 <receive>:
    5620:	f3 0f 1e fa          	endbr64
    5624:	8b 57 74             	mov    0x74(%rdi),%edx
    5627:	85 d2                	test   %edx,%edx
    5629:	0f 8e e1 00 00 00    	jle    5710 <receive+0xf0>
    562f:	48 89 f8             	mov    %rdi,%rax
    5632:	45 31 db             	xor    %r11d,%r11d
    5635:	0f 1f 00             	nopl   (%rax)
    5638:	48 8b 90 a8 00 00 00 	mov    0xa8(%rax),%rdx
    563f:	4c 89 df             	mov    %r11,%rdi
    5642:	48 c1 e7 05          	shl    $0x5,%rdi
    5646:	4c 8b 0c 3a          	mov    (%rdx,%rdi,1),%r9
    564a:	49 8b 51 08          	mov    0x8(%r9),%rdx
    564e:	48 85 d2             	test   %rdx,%rdx
    5651:	0f 8e a1 00 00 00    	jle    56f8 <receive+0xd8>
    5657:	4d 8b 11             	mov    (%r9),%r10
    565a:	31 d2                	xor    %edx,%edx
    565c:	eb 13                	jmp    5671 <receive+0x51>
    565e:	66 90                	xchg   %ax,%ax
    5660:	49 8b 49 08          	mov    0x8(%r9),%rcx
    5664:	48 83 c2 01          	add    $0x1,%rdx
    5668:	48 39 d1             	cmp    %rdx,%rcx
    566b:	0f 8e 87 00 00 00    	jle    56f8 <receive+0xd8>
    5671:	48 8b 88 b0 00 00 00 	mov    0xb0(%rax),%rcx
    5678:	49 8b 34 d2          	mov    (%r10,%rdx,8),%rsi
    567c:	48 83 c1 01          	add    $0x1,%rcx
    5680:	4c 8b 46 10          	mov    0x10(%rsi),%r8
    5684:	48 89 88 b0 00 00 00 	mov    %rcx,0xb0(%rax)
    568b:	48 8b 48 48          	mov    0x48(%rax),%rcx
    568f:	48 83 c1 01          	add    $0x1,%rcx
    5693:	48 89 48 48          	mov    %rcx,0x48(%rax)
    5697:	48 8b 88 a8 00 00 00 	mov    0xa8(%rax),%rcx
    569e:	48 83 44 39 18 01    	addq   $0x1,0x18(%rcx,%rdi,1)
    56a4:	48 63 08             	movslq (%rax),%rcx
    56a7:	49 39 c8             	cmp    %rcx,%r8
    56aa:	75 b4                	jne    5660 <receive+0x40>
    56ac:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    56b0:	48 63 48 70          	movslq 0x70(%rax),%rcx
    56b4:	48 39 ce             	cmp    %rcx,%rsi
    56b7:	75 a7                	jne    5660 <receive+0x40>
    56b9:	48 83 ec 08          	sub    $0x8,%rsp
    56bd:	48 63 50 70          	movslq 0x70(%rax),%rdx
    56c1:	48 63 00             	movslq (%rax),%rax
    56c4:	31 c9                	xor    %ecx,%ecx
    56c6:	bf 01 00 00 00       	mov    $0x1,%edi
    56cb:	48 39 f2             	cmp    %rsi,%rdx
    56ce:	48 8d 35 83 0d 00 00 	lea    0xd83(%rip),%rsi        # 6458 <_IO_stdin_used+0x458>
    56d5:	0f 94 c1             	sete   %cl
    56d8:	31 d2                	xor    %edx,%edx
    56da:	4c 39 c0             	cmp    %r8,%rax
    56dd:	0f 94 c2             	sete   %dl
    56e0:	31 c0                	xor    %eax,%eax
    56e2:	e8 69 cd ff ff       	call   2450 <__printf_chk@plt>
    56e7:	bf 01 00 00 00       	mov    $0x1,%edi
    56ec:	e8 af cd ff ff       	call   24a0 <exit@plt>
    56f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    56f8:	49 c7 41 08 00 00 00 00 	movq   $0x0,0x8(%r9)
    5700:	8b 50 74             	mov    0x74(%rax),%edx
    5703:	49 83 c3 01          	add    $0x1,%r11
    5707:	44 39 da             	cmp    %r11d,%edx
    570a:	0f 8f 28 ff ff ff    	jg     5638 <receive+0x18>
    5710:	c3                   	ret
    5711:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    571c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005720 <barriered_work>:
    5720:	f3 0f 1e fa          	endbr64
    5724:	41 54                	push   %r12
    5726:	55                   	push   %rbp
    5727:	53                   	push   %rbx
    5728:	8b 57 70             	mov    0x70(%rdi),%edx
    572b:	48 89 fb             	mov    %rdi,%rbx
    572e:	8b 07                	mov    (%rdi),%eax
    5730:	39 c2                	cmp    %eax,%edx
    5732:	0f 84 d8 00 00 00    	je     5810 <barriered_work+0xf0>
    5738:	e8 e3 fe ff ff       	call   5620 <receive>
    573d:	8b 83 80 00 00 00    	mov    0x80(%rbx),%eax
    5743:	83 f8 01             	cmp    $0x1,%eax
    5746:	75 1f                	jne    5767 <barriered_work+0x47>
    5748:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5750:	48 8b 43 48          	mov    0x48(%rbx),%rax
    5754:	48 83 c0 01          	add    $0x1,%rax
    5758:	48 89 43 48          	mov    %rax,0x48(%rbx)
    575c:	8b 83 80 00 00 00    	mov    0x80(%rbx),%eax
    5762:	83 f8 01             	cmp    $0x1,%eax
    5765:	74 e9                	je     5750 <barriered_work+0x30>
    5767:	8b 83 b8 00 00 00    	mov    0xb8(%rbx),%eax
    576d:	83 f8 01             	cmp    $0x1,%eax
    5770:	74 0a                	je     577c <barriered_work+0x5c>
    5772:	0f ae f8             	sfence
    5775:	31 c0                	xor    %eax,%eax
    5777:	5b                   	pop    %rbx
    5778:	5d                   	pop    %rbp
    5779:	41 5c                	pop    %r12
    577b:	c3                   	ret
    577c:	8b 43 74             	mov    0x74(%rbx),%eax
    577f:	85 c0                	test   %eax,%eax
    5781:	7e ef                	jle    5772 <barriered_work+0x52>
    5783:	45 31 c9             	xor    %r9d,%r9d
    5786:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5790:	8b 43 70             	mov    0x70(%rbx),%eax
    5793:	44 39 c8             	cmp    %r9d,%eax
    5796:	74 61                	je     57f9 <barriered_work+0xd9>
    5798:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    579f:	4c 89 c9             	mov    %r9,%rcx
    57a2:	48 c1 e1 05          	shl    $0x5,%rcx
    57a6:	48 8b 54 08 08       	mov    0x8(%rax,%rcx,1),%rdx
    57ab:	48 8b 42 08          	mov    0x8(%rdx),%rax
    57af:	48 63 7a 10          	movslq 0x10(%rdx),%rdi
    57b3:	48 39 f8             	cmp    %rdi,%rax
    57b6:	7d 41                	jge    57f9 <barriered_work+0xd9>
    57b8:	4c 8b 02             	mov    (%rdx),%r8
    57bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    57c0:	48 8b 43 48          	mov    0x48(%rbx),%rax
    57c4:	48 83 c0 01          	add    $0x1,%rax
    57c8:	48 89 43 48          	mov    %rax,0x48(%rbx)
    57cc:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    57d3:	48 83 44 08 10 01    	addq   $0x1,0x10(%rax,%rcx,1)
    57d9:	48 8b 42 08          	mov    0x8(%rdx),%rax
    57dd:	48 8d 70 01          	lea    0x1(%rax),%rsi
    57e1:	48 89 72 08          	mov    %rsi,0x8(%rdx)
    57e5:	48 8b b3 c0 00 00 00 	mov    0xc0(%rbx),%rsi
    57ec:	49 89 34 c0          	mov    %rsi,(%r8,%rax,8)
    57f0:	48 8b 42 08          	mov    0x8(%rdx),%rax
    57f4:	48 39 f8             	cmp    %rdi,%rax
    57f7:	7c c7                	jl     57c0 <barriered_work+0xa0>
    57f9:	8b 43 74             	mov    0x74(%rbx),%eax
    57fc:	49 83 c1 01          	add    $0x1,%r9
    5800:	44 39 c8             	cmp    %r9d,%eax
    5803:	7f 8b                	jg     5790 <barriered_work+0x70>
    5805:	e9 68 ff ff ff       	jmp    5772 <barriered_work+0x52>
    580a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5810:	e8 0b fe ff ff       	call   5620 <receive>
    5815:	8b 33                	mov    (%rbx),%esi
    5817:	8b 43 74             	mov    0x74(%rbx),%eax
    581a:	85 c0                	test   %eax,%eax
    581c:	0f 8e a1 00 00 00    	jle    58c3 <barriered_work+0x1a3>
    5822:	4c 63 d6             	movslq %esi,%r10
    5825:	45 31 db             	xor    %r11d,%r11d
    5828:	83 c6 01             	add    $0x1,%esi
    582b:	49 c1 e2 08          	shl    $0x8,%r10
    582f:	90                   	nop
    5830:	8b 43 74             	mov    0x74(%rbx),%eax
    5833:	4d 89 d8             	mov    %r11,%r8
    5836:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    583e:	31 c9                	xor    %ecx,%ecx
    5840:	49 c1 e0 05          	shl    $0x5,%r8
    5844:	85 c0                	test   %eax,%eax
    5846:	7e 6b                	jle    58b3 <barriered_work+0x193>
    5848:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5850:	44 8b 63 74          	mov    0x74(%rbx),%r12d
    5854:	48 8b 43 68          	mov    0x68(%rbx),%rax
    5858:	48 8b 40 40          	mov    0x40(%rax),%rax
    585c:	4a 8b 04 08          	mov    (%rax,%r9,1),%rax
    5860:	48 8b 78 58          	mov    0x58(%rax),%rdi
    5864:	4c 01 d7             	add    %r10,%rdi
    5867:	48 8b bf a8 00 00 00 	mov    0xa8(%rdi),%rdi
    586e:	48 8b 43 68          	mov    0x68(%rbx),%rax
    5872:	48 8b 40 40          	mov    0x40(%rax),%rax
    5876:	48 8b 2c c8          	mov    (%rax,%rcx,8),%rbp
    587a:	89 f0                	mov    %esi,%eax
    587c:	99                   	cltd
    587d:	41 f7 fc             	idiv   %r12d
    5880:	89 d0                	mov    %edx,%eax
    5882:	f7 d8                	neg    %eax
    5884:	0f 48 c2             	cmovs  %edx,%eax
    5887:	48 89 ca             	mov    %rcx,%rdx
    588a:	48 83 c1 01          	add    $0x1,%rcx
    588e:	48 c1 e2 05          	shl    $0x5,%rdx
    5892:	48 98                	cltq
    5894:	48 8b 54 17 08       	mov    0x8(%rdi,%rdx,1),%rdx
    5899:	48 c1 e0 08          	shl    $0x8,%rax
    589d:	48 03 45 58          	add    0x58(%rbp),%rax
    58a1:	48 8b 80 a8 00 00 00 	mov    0xa8(%rax),%rax
    58a8:	4a 89 14 00          	mov    %rdx,(%rax,%r8,1)
    58ac:	8b 43 74             	mov    0x74(%rbx),%eax
    58af:	39 c8                	cmp    %ecx,%eax
    58b1:	7f 9d                	jg     5850 <barriered_work+0x130>
    58b3:	8b 43 74             	mov    0x74(%rbx),%eax
    58b6:	49 83 c3 01          	add    $0x1,%r11
    58ba:	44 39 d8             	cmp    %r11d,%eax
    58bd:	0f 8f 6d ff ff ff    	jg     5830 <barriered_work+0x110>
    58c3:	0f ae f8             	sfence
    58c6:	48 8b b3 88 00 00 00 	mov    0x88(%rbx),%rsi
    58cd:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    58d4:	31 ff                	xor    %edi,%edi
    58d6:	48 c1 e0 05          	shl    $0x5,%rax
    58da:	48 01 c6             	add    %rax,%rsi
    58dd:	e8 2e ca ff ff       	call   2310 <clock_gettime@plt>
    58e2:	48 8b 43 68          	mov    0x68(%rbx),%rax
    58e6:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    58ed:	8b 70 10             	mov    0x10(%rax),%esi
    58f0:	8d 6e 01             	lea    0x1(%rsi),%ebp
    58f3:	89 68 10             	mov    %ebp,0x10(%rax)
    58f6:	8b 83 80 00 00 00    	mov    0x80(%rbx),%eax
    58fc:	83 f8 01             	cmp    $0x1,%eax
    58ff:	75 3f                	jne    5940 <barriered_work+0x220>
    5901:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5908:	48 8b 43 48          	mov    0x48(%rbx),%rax
    590c:	48 83 c0 01          	add    $0x1,%rax
    5910:	48 89 43 48          	mov    %rax,0x48(%rbx)
    5914:	48 8b 53 60          	mov    0x60(%rbx),%rdx
    5918:	48 8b 4b 68          	mov    0x68(%rbx),%rcx
    591c:	48 63 43 70          	movslq 0x70(%rbx),%rax
    5920:	48 63 3b             	movslq (%rbx),%rdi
    5923:	48 8b 49 40          	mov    0x40(%rcx),%rcx
    5927:	48 c1 e7 08          	shl    $0x8,%rdi
    592b:	48 8b 04 c1          	mov    (%rcx,%rax,8),%rax
    592f:	48 03 78 58          	add    0x58(%rax),%rdi
    5933:	ff d2                	call   *%rdx
    5935:	8b 83 80 00 00 00    	mov    0x80(%rbx),%eax
    593b:	83 f8 01             	cmp    $0x1,%eax
    593e:	74 c8                	je     5908 <barriered_work+0x1e8>
    5940:	48 8b 43 68          	mov    0x68(%rbx),%rax
    5944:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    594b:	3b 68 10             	cmp    0x10(%rax),%ebp
    594e:	0f 85 d6 00 00 00    	jne    5a2a <barriered_work+0x30a>
    5954:	48 8b 93 88 00 00 00 	mov    0x88(%rbx),%rdx
    595b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5962:	31 ff                	xor    %edi,%edi
    5964:	48 c1 e0 05          	shl    $0x5,%rax
    5968:	48 8d 74 02 10       	lea    0x10(%rdx,%rax,1),%rsi
    596d:	e8 9e c9 ff ff       	call   2310 <clock_gettime@plt>
    5972:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    5979:	48 8b 8b 90 00 00 00 	mov    0x90(%rbx),%rcx
    5980:	48 83 c0 01          	add    $0x1,%rax
    5984:	48 99                	cqto
    5986:	48 f7 f9             	idiv   %rcx
    5989:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
    5990:	8b 83 b8 00 00 00    	mov    0xb8(%rbx),%eax
    5996:	83 f8 01             	cmp    $0x1,%eax
    5999:	0f 85 d3 fd ff ff    	jne    5772 <barriered_work+0x52>
    599f:	8b 43 74             	mov    0x74(%rbx),%eax
    59a2:	85 c0                	test   %eax,%eax
    59a4:	0f 8e c8 fd ff ff    	jle    5772 <barriered_work+0x52>
    59aa:	45 31 c9             	xor    %r9d,%r9d
    59ad:	0f 1f 00             	nopl   (%rax)
    59b0:	8b 43 70             	mov    0x70(%rbx),%eax
    59b3:	44 39 c8             	cmp    %r9d,%eax
    59b6:	74 61                	je     5a19 <barriered_work+0x2f9>
    59b8:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    59bf:	4c 89 c9             	mov    %r9,%rcx
    59c2:	48 c1 e1 05          	shl    $0x5,%rcx
    59c6:	48 8b 54 08 08       	mov    0x8(%rax,%rcx,1),%rdx
    59cb:	48 8b 42 08          	mov    0x8(%rdx),%rax
    59cf:	48 63 7a 10          	movslq 0x10(%rdx),%rdi
    59d3:	48 39 c7             	cmp    %rax,%rdi
    59d6:	7e 41                	jle    5a19 <barriered_work+0x2f9>
    59d8:	4c 8b 02             	mov    (%rdx),%r8
    59db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    59e0:	48 8b 43 48          	mov    0x48(%rbx),%rax
    59e4:	48 83 c0 01          	add    $0x1,%rax
    59e8:	48 89 43 48          	mov    %rax,0x48(%rbx)
    59ec:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    59f3:	48 83 44 08 10 01    	addq   $0x1,0x10(%rax,%rcx,1)
    59f9:	48 8b 42 08          	mov    0x8(%rdx),%rax
    59fd:	48 8d 70 01          	lea    0x1(%rax),%rsi
    5a01:	48 89 72 08          	mov    %rsi,0x8(%rdx)
    5a05:	48 8b b3 c0 00 00 00 	mov    0xc0(%rbx),%rsi
    5a0c:	49 89 34 c0          	mov    %rsi,(%r8,%rax,8)
    5a10:	48 8b 42 08          	mov    0x8(%rdx),%rax
    5a14:	48 39 f8             	cmp    %rdi,%rax
    5a17:	7c c7                	jl     59e0 <barriered_work+0x2c0>
    5a19:	8b 43 74             	mov    0x74(%rbx),%eax
    5a1c:	49 83 c1 01          	add    $0x1,%r9
    5a20:	44 39 c8             	cmp    %r9d,%eax
    5a23:	7f 8b                	jg     59b0 <barriered_work+0x290>
    5a25:	e9 48 fd ff ff       	jmp    5772 <barriered_work+0x52>
    5a2a:	48 8d 3d d3 07 00 00 	lea    0x7d3(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    5a31:	e8 ba c8 ff ff       	call   22f0 <puts@plt>
    5a36:	e9 19 ff ff ff       	jmp    5954 <barriered_work+0x234>
    5a3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005a40 <barriered_work_ingest>:
    5a40:	f3 0f 1e fa          	endbr64
    5a44:	48 83 ec 08          	sub    $0x8,%rsp
    5a48:	48 8b 47 68          	mov    0x68(%rdi),%rax
    5a4c:	48 8b 80 c0 00 00 00 	mov    0xc0(%rax),%rax
    5a53:	8b 00                	mov    (%rax),%eax
    5a55:	85 c0                	test   %eax,%eax
    5a57:	7e 63                	jle    5abc <barriered_work_ingest+0x7c>
    5a59:	31 c0                	xor    %eax,%eax
    5a5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5a60:	48 8b 4f 68          	mov    0x68(%rdi),%rcx
    5a64:	48 89 c2             	mov    %rax,%rdx
    5a67:	48 c1 e2 04          	shl    $0x4,%rdx
    5a6b:	48 8b 89 c0 00 00 00 	mov    0xc0(%rcx),%rcx
    5a72:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    5a76:	48 01 d6             	add    %rdx,%rsi
    5a79:	8b 4e 08             	mov    0x8(%rsi),%ecx
    5a7c:	83 f9 01             	cmp    $0x1,%ecx
    5a7f:	75 28                	jne    5aa9 <barriered_work_ingest+0x69>
    5a81:	48 8b 8f a0 00 00 00 	mov    0xa0(%rdi),%rcx
    5a88:	48 83 c1 01          	add    $0x1,%rcx
    5a8c:	48 89 8f a0 00 00 00 	mov    %rcx,0xa0(%rdi)
    5a93:	48 8b 4f 68          	mov    0x68(%rdi),%rcx
    5a97:	48 8b 89 c0 00 00 00 	mov    0xc0(%rcx),%rcx
    5a9e:	48 03 51 08          	add    0x8(%rcx),%rdx
    5aa2:	c7 42 08 00 00 00 00 	movl   $0x0,0x8(%rdx)
    5aa9:	48 8b 57 68          	mov    0x68(%rdi),%rdx
    5aad:	48 83 c0 01          	add    $0x1,%rax
    5ab1:	48 8b 92 c0 00 00 00 	mov    0xc0(%rdx),%rdx
    5ab8:	39 02                	cmp    %eax,(%rdx)
    5aba:	7f a4                	jg     5a60 <barriered_work_ingest+0x20>
    5abc:	0f ae f8             	sfence
    5abf:	e8 5c fc ff ff       	call   5720 <barriered_work>
    5ac4:	31 c0                	xor    %eax,%eax
    5ac6:	48 83 c4 08          	add    $0x8,%rsp
    5aca:	c3                   	ret
    5acb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005ad0 <barriered_nulltask>:
    5ad0:	f3 0f 1e fa          	endbr64
    5ad4:	31 c0                	xor    %eax,%eax
    5ad6:	c3                   	ret
    5ad7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005ae0 <barriered_steal>:
    5ae0:	f3 0f 1e fa          	endbr64
    5ae4:	31 c0                	xor    %eax,%eax
    5ae6:	c3                   	ret
    5ae7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005af0 <after>:
    5af0:	f3 0f 1e fa          	endbr64
    5af4:	31 c0                	xor    %eax,%eax
    5af6:	48 39 d7             	cmp    %rdx,%rdi
    5af9:	7e 08                	jle    5b03 <after+0x13>
    5afb:	31 c0                	xor    %eax,%eax
    5afd:	48 39 ce             	cmp    %rcx,%rsi
    5b00:	0f 9f c0             	setg   %al
    5b03:	c3                   	ret
    5b04:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5b0f:	90                   	nop

0000000000005b10 <within>:
    5b10:	f3 0f 1e fa          	endbr64
    5b14:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5b19:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    5b1e:	31 c0                	xor    %eax,%eax
    5b20:	48 39 d7             	cmp    %rdx,%rdi
    5b23:	7f 18                	jg     5b3d <within+0x2d>
    5b25:	4d 39 d8             	cmp    %r11,%r8
    5b28:	0f 9e c2             	setle  %dl
    5b2b:	48 39 ce             	cmp    %rcx,%rsi
    5b2e:	0f 9e c0             	setle  %al
    5b31:	21 c2                	and    %eax,%edx
    5b33:	31 c0                	xor    %eax,%eax
    5b35:	4d 39 d1             	cmp    %r10,%r9
    5b38:	0f 9e c0             	setle  %al
    5b3b:	21 d0                	and    %edx,%eax
    5b3d:	c3                   	ret
    5b3e:	66 90                	xchg   %ax,%ax

0000000000005b40 <overlap>:
    5b40:	f3 0f 1e fa          	endbr64
    5b44:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5b49:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5b4e:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    5b53:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    5b58:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
    5b5d:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    5b62:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5b67:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    5b6c:	48 39 fe             	cmp    %rdi,%rsi
    5b6f:	7d 2f                	jge    5ba0 <overlap+0x60>
    5b71:	48 39 ca             	cmp    %rcx,%rdx
    5b74:	7d 62                	jge    5bd8 <overlap+0x98>
    5b76:	4d 39 da             	cmp    %r11,%r10
    5b79:	7e 0e                	jle    5b89 <overlap+0x49>
    5b7b:	b8 01 00 00 00       	mov    $0x1,%eax
    5b80:	4d 39 c1             	cmp    %r8,%r9
    5b83:	0f 8f 7f 00 00 00    	jg     5c08 <overlap+0xc8>
    5b89:	31 c0                	xor    %eax,%eax
    5b8b:	4d 39 c1             	cmp    %r8,%r9
    5b8e:	7c 4c                	jl     5bdc <overlap+0x9c>
    5b90:	31 c0                	xor    %eax,%eax
    5b92:	4d 39 da             	cmp    %r11,%r10
    5b95:	0f 9d c0             	setge  %al
    5b98:	c3                   	ret
    5b99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5ba0:	7e 4e                	jle    5bf0 <overlap+0xb0>
    5ba2:	48 39 ca             	cmp    %rcx,%rdx
    5ba5:	7f 39                	jg     5be0 <overlap+0xa0>
    5ba7:	75 31                	jne    5bda <overlap+0x9a>
    5ba9:	4d 39 c1             	cmp    %r8,%r9
    5bac:	7f 2c                	jg     5bda <overlap+0x9a>
    5bae:	b8 01 00 00 00       	mov    $0x1,%eax
    5bb3:	4d 39 da             	cmp    %r11,%r10
    5bb6:	7e 24                	jle    5bdc <overlap+0x9c>
    5bb8:	48 39 ca             	cmp    %rcx,%rdx
    5bbb:	0f 94 c2             	sete   %dl
    5bbe:	48 39 fe             	cmp    %rdi,%rsi
    5bc1:	0f 94 c0             	sete   %al
    5bc4:	21 c2                	and    %eax,%edx
    5bc6:	31 c0                	xor    %eax,%eax
    5bc8:	4d 39 c1             	cmp    %r8,%r9
    5bcb:	0f 94 c0             	sete   %al
    5bce:	21 d0                	and    %edx,%eax
    5bd0:	c3                   	ret
    5bd1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5bd8:	74 af                	je     5b89 <overlap+0x49>
    5bda:	31 c0                	xor    %eax,%eax
    5bdc:	c3                   	ret
    5bdd:	0f 1f 00             	nopl   (%rax)
    5be0:	4d 39 c1             	cmp    %r8,%r9
    5be3:	7d c4                	jge    5ba9 <overlap+0x69>
    5be5:	b8 01 00 00 00       	mov    $0x1,%eax
    5bea:	4d 39 da             	cmp    %r11,%r10
    5bed:	7d ba                	jge    5ba9 <overlap+0x69>
    5bef:	c3                   	ret
    5bf0:	48 39 ca             	cmp    %rcx,%rdx
    5bf3:	7c 94                	jl     5b89 <overlap+0x49>
    5bf5:	4d 39 c1             	cmp    %r8,%r9
    5bf8:	7e b4                	jle    5bae <overlap+0x6e>
    5bfa:	48 39 ca             	cmp    %rcx,%rdx
    5bfd:	74 91                	je     5b90 <overlap+0x50>
    5bff:	eb d9                	jmp    5bda <overlap+0x9a>
    5c01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5c08:	c3                   	ret
    5c09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005c10 <verify>:
    5c10:	f3 0f 1e fa          	endbr64
    5c14:	85 f6                	test   %esi,%esi
    5c16:	0f 8e 2b 03 00 00    	jle    5f47 <verify+0x337>
    5c1c:	41 57                	push   %r15
    5c1e:	41 56                	push   %r14
    5c20:	45 31 f6             	xor    %r14d,%r14d
    5c23:	41 55                	push   %r13
    5c25:	4c 8d 6f 58          	lea    0x58(%rdi),%r13
    5c29:	41 54                	push   %r12
    5c2b:	41 89 f4             	mov    %esi,%r12d
    5c2e:	55                   	push   %rbp
    5c2f:	53                   	push   %rbx
    5c30:	48 83 ec 48          	sub    $0x48,%rsp
    5c34:	4c 89 6c 24 08       	mov    %r13,0x8(%rsp)
    5c39:	4c 89 2c 24          	mov    %r13,(%rsp)
    5c3d:	31 ed                	xor    %ebp,%ebp
    5c3f:	4d 89 ef             	mov    %r13,%r15
    5c42:	41 39 ee             	cmp    %ebp,%r14d
    5c45:	0f 84 5a 02 00 00    	je     5ea5 <verify+0x295>
    5c4b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5c50:	8b 50 08             	mov    0x8(%rax),%edx
    5c53:	85 d2                	test   %edx,%edx
    5c55:	0f 8e 4a 02 00 00    	jle    5ea5 <verify+0x295>
    5c5b:	89 6c 24 24          	mov    %ebp,0x24(%rsp)
    5c5f:	31 db                	xor    %ebx,%ebx
    5c61:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    5c66:	44 89 f2             	mov    %r14d,%edx
    5c69:	48 8d 35 a4 05 00 00 	lea    0x5a4(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    5c70:	bf 01 00 00 00       	mov    $0x1,%edi
    5c75:	31 c0                	xor    %eax,%eax
    5c77:	e8 d4 c7 ff ff       	call   2450 <__printf_chk@plt>
    5c7c:	48 8b 04 24          	mov    (%rsp),%rax
    5c80:	8b 40 08             	mov    0x8(%rax),%eax
    5c83:	85 c0                	test   %eax,%eax
    5c85:	0f 8e ff 01 00 00    	jle    5e8a <verify+0x27a>
    5c8b:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5c90:	48 89 d8             	mov    %rbx,%rax
    5c93:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    5c98:	45 31 e4             	xor    %r12d,%r12d
    5c9b:	48 c1 e0 08          	shl    $0x8,%rax
    5c9f:	44 89 74 24 34       	mov    %r14d,0x34(%rsp)
    5ca4:	4c 89 7c 24 38       	mov    %r15,0x38(%rsp)
    5ca9:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5cae:	48 03 07             	add    (%rdi),%rax
    5cb1:	49 89 c5             	mov    %rax,%r13
    5cb4:	0f 1f 40 00          	nopl   0x0(%rax)
    5cb8:	48 8b 1c 24          	mov    (%rsp),%rbx
    5cbc:	4c 89 e5             	mov    %r12,%rbp
    5cbf:	49 8b 8d 98 00 00 00 	mov    0x98(%r13),%rcx
    5cc6:	48 8d 35 5c 05 00 00 	lea    0x55c(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    5ccd:	48 c1 e5 08          	shl    $0x8,%rbp
    5cd1:	bf 01 00 00 00       	mov    $0x1,%edi
    5cd6:	48 8b 03             	mov    (%rbx),%rax
    5cd9:	48 01 e8             	add    %rbp,%rax
    5cdc:	48 8b 90 98 00 00 00 	mov    0x98(%rax),%rdx
    5ce3:	31 c0                	xor    %eax,%eax
    5ce5:	e8 66 c7 ff ff       	call   2450 <__printf_chk@plt>
    5cea:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5cef:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    5cf4:	4c 03 28             	add    (%rax),%r13
    5cf7:	49 8b 85 98 00 00 00 	mov    0x98(%r13),%rax
    5cfe:	48 85 c0             	test   %rax,%rax
    5d01:	0f 8e 62 01 00 00    	jle    5e69 <verify+0x259>
    5d07:	48 8b 13             	mov    (%rbx),%rdx
    5d0a:	4c 89 64 24 18       	mov    %r12,0x18(%rsp)
    5d0f:	45 31 ff             	xor    %r15d,%r15d
    5d12:	48 01 ea             	add    %rbp,%rdx
    5d15:	0f 1f 00             	nopl   (%rax)
    5d18:	48 8b 82 98 00 00 00 	mov    0x98(%rdx),%rax
    5d1f:	4d 89 fc             	mov    %r15,%r12
    5d22:	31 db                	xor    %ebx,%ebx
    5d24:	49 c1 e4 05          	shl    $0x5,%r12
    5d28:	48 85 c0             	test   %rax,%rax
    5d2b:	7f 47                	jg     5d74 <verify+0x164>
    5d2d:	e9 1e 01 00 00       	jmp    5e50 <verify+0x240>
    5d32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5d38:	48 39 f1             	cmp    %rsi,%rcx
    5d3b:	0f 8d 7f 01 00 00    	jge    5ec0 <verify+0x2b0>
    5d41:	4d 39 da             	cmp    %r11,%r10
    5d44:	7e 09                	jle    5d4f <verify+0x13f>
    5d46:	49 39 c6             	cmp    %rax,%r14
    5d49:	0f 8c 91 00 00 00    	jl     5de0 <verify+0x1d0>
    5d4f:	4d 39 da             	cmp    %r11,%r10
    5d52:	0f 8d b3 01 00 00    	jge    5f0b <verify+0x2fb>
    5d58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5d60:	48 8b 82 98 00 00 00 	mov    0x98(%rdx),%rax
    5d67:	48 83 c3 01          	add    $0x1,%rbx
    5d6b:	48 39 d8             	cmp    %rbx,%rax
    5d6e:	0f 8e dc 00 00 00    	jle    5e50 <verify+0x240>
    5d74:	48 8b 82 88 00 00 00 	mov    0x88(%rdx),%rax
    5d7b:	49 89 d9             	mov    %rbx,%r9
    5d7e:	49 8b 8d 88 00 00 00 	mov    0x88(%r13),%rcx
    5d85:	49 c1 e1 05          	shl    $0x5,%r9
    5d89:	4c 01 e1             	add    %r12,%rcx
    5d8c:	4c 01 c8             	add    %r9,%rax
    5d8f:	4c 8b 01             	mov    (%rcx),%r8
    5d92:	48 8b 38             	mov    (%rax),%rdi
    5d95:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    5d99:	4c 8b 59 10          	mov    0x10(%rcx),%r11
    5d9d:	4c 8b 71 18          	mov    0x18(%rcx),%r14
    5da1:	4c 8b 50 10          	mov    0x10(%rax),%r10
    5da5:	48 8b 48 08          	mov    0x8(%rax),%rcx
    5da9:	48 8b 40 18          	mov    0x18(%rax),%rax
    5dad:	4c 39 c7             	cmp    %r8,%rdi
    5db0:	7c 86                	jl     5d38 <verify+0x128>
    5db2:	0f 8e 38 01 00 00    	jle    5ef0 <verify+0x2e0>
    5db8:	48 39 f1             	cmp    %rsi,%rcx
    5dbb:	0f 8f 0f 01 00 00    	jg     5ed0 <verify+0x2c0>
    5dc1:	75 9d                	jne    5d60 <verify+0x150>
    5dc3:	4d 39 da             	cmp    %r11,%r10
    5dc6:	7f 98                	jg     5d60 <verify+0x150>
    5dc8:	49 39 c6             	cmp    %rax,%r14
    5dcb:	7d 13                	jge    5de0 <verify+0x1d0>
    5dcd:	4c 39 c7             	cmp    %r8,%rdi
    5dd0:	75 8e                	jne    5d60 <verify+0x150>
    5dd2:	48 39 f1             	cmp    %rsi,%rcx
    5dd5:	75 89                	jne    5d60 <verify+0x150>
    5dd7:	4d 39 da             	cmp    %r11,%r10
    5dda:	75 84                	jne    5d60 <verify+0x150>
    5ddc:	0f 1f 40 00          	nopl   0x0(%rax)
    5de0:	48 8b b2 88 00 00 00 	mov    0x88(%rdx),%rsi
    5de7:	bf 01 00 00 00       	mov    $0x1,%edi
    5dec:	48 83 c3 01          	add    $0x1,%rbx
    5df0:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    5df7:	48 8b 8a 88 00 00 00 	mov    0x88(%rdx),%rcx
    5dfe:	49 8b 95 88 00 00 00 	mov    0x88(%r13),%rdx
    5e05:	4e 8b 44 20 08       	mov    0x8(%rax,%r12,1),%r8
    5e0a:	31 c0                	xor    %eax,%eax
    5e0c:	4a 8b 4c 09 10       	mov    0x10(%rcx,%r9,1),%rcx
    5e11:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    5e15:	4e 8b 4c 0e 18       	mov    0x18(%rsi,%r9,1),%r9
    5e1a:	48 8d 35 5f 06 00 00 	lea    0x65f(%rip),%rsi        # 6480 <_IO_stdin_used+0x480>
    5e21:	e8 2a c6 ff ff       	call   2450 <__printf_chk@plt>
    5e26:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5e2b:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    5e30:	4c 03 28             	add    (%rax),%r13
    5e33:	48 8b 04 24          	mov    (%rsp),%rax
    5e37:	48 8b 10             	mov    (%rax),%rdx
    5e3a:	48 01 ea             	add    %rbp,%rdx
    5e3d:	48 8b 82 98 00 00 00 	mov    0x98(%rdx),%rax
    5e44:	48 39 d8             	cmp    %rbx,%rax
    5e47:	0f 8f 27 ff ff ff    	jg     5d74 <verify+0x164>
    5e4d:	0f 1f 00             	nopl   (%rax)
    5e50:	49 8b 85 98 00 00 00 	mov    0x98(%r13),%rax
    5e57:	49 83 c7 01          	add    $0x1,%r15
    5e5b:	4c 39 f8             	cmp    %r15,%rax
    5e5e:	0f 8f b4 fe ff ff    	jg     5d18 <verify+0x108>
    5e64:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    5e69:	48 8b 04 24          	mov    (%rsp),%rax
    5e6d:	49 83 c4 01          	add    $0x1,%r12
    5e71:	44 39 60 08          	cmp    %r12d,0x8(%rax)
    5e75:	0f 8f 3d fe ff ff    	jg     5cb8 <verify+0xa8>
    5e7b:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    5e80:	44 8b 74 24 34       	mov    0x34(%rsp),%r14d
    5e85:	4c 8b 7c 24 38       	mov    0x38(%rsp),%r15
    5e8a:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5e8f:	48 83 c3 01          	add    $0x1,%rbx
    5e93:	39 58 08             	cmp    %ebx,0x8(%rax)
    5e96:	0f 8f ca fd ff ff    	jg     5c66 <verify+0x56>
    5e9c:	8b 6c 24 24          	mov    0x24(%rsp),%ebp
    5ea0:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    5ea5:	8d 45 01             	lea    0x1(%rbp),%eax
    5ea8:	48 81 04 24 40 01 00 00 	addq   $0x140,(%rsp)
    5eb0:	41 39 c4             	cmp    %eax,%r12d
    5eb3:	74 64                	je     5f19 <verify+0x309>
    5eb5:	89 c5                	mov    %eax,%ebp
    5eb7:	e9 86 fd ff ff       	jmp    5c42 <verify+0x32>
    5ebc:	0f 1f 40 00          	nopl   0x0(%rax)
    5ec0:	0f 85 9a fe ff ff    	jne    5d60 <verify+0x150>
    5ec6:	e9 84 fe ff ff       	jmp    5d4f <verify+0x13f>
    5ecb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5ed0:	49 39 c6             	cmp    %rax,%r14
    5ed3:	0f 8e ea fe ff ff    	jle    5dc3 <verify+0x1b3>
    5ed9:	4d 39 da             	cmp    %r11,%r10
    5edc:	0f 8d e1 fe ff ff    	jge    5dc3 <verify+0x1b3>
    5ee2:	e9 f9 fe ff ff       	jmp    5de0 <verify+0x1d0>
    5ee7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5ef0:	48 39 f1             	cmp    %rsi,%rcx
    5ef3:	0f 8c 56 fe ff ff    	jl     5d4f <verify+0x13f>
    5ef9:	4d 39 da             	cmp    %r11,%r10
    5efc:	0f 8e c6 fe ff ff    	jle    5dc8 <verify+0x1b8>
    5f02:	48 39 f1             	cmp    %rsi,%rcx
    5f05:	0f 85 55 fe ff ff    	jne    5d60 <verify+0x150>
    5f0b:	49 39 c6             	cmp    %rax,%r14
    5f0e:	0f 8f 4c fe ff ff    	jg     5d60 <verify+0x150>
    5f14:	e9 c7 fe ff ff       	jmp    5de0 <verify+0x1d0>
    5f19:	48 81 44 24 08 40 01 00 00 	addq   $0x140,0x8(%rsp)
    5f22:	4d 89 fd             	mov    %r15,%r13
    5f25:	41 8d 46 01          	lea    0x1(%r14),%eax
    5f29:	41 39 ee             	cmp    %ebp,%r14d
    5f2c:	74 08                	je     5f36 <verify+0x326>
    5f2e:	41 89 c6             	mov    %eax,%r14d
    5f31:	e9 03 fd ff ff       	jmp    5c39 <verify+0x29>
    5f36:	48 83 c4 48          	add    $0x48,%rsp
    5f3a:	31 c0                	xor    %eax,%eax
    5f3c:	5b                   	pop    %rbx
    5f3d:	5d                   	pop    %rbp
    5f3e:	41 5c                	pop    %r12
    5f40:	41 5d                	pop    %r13
    5f42:	41 5e                	pop    %r14
    5f44:	41 5f                	pop    %r15
    5f46:	c3                   	ret
    5f47:	31 c0                	xor    %eax,%eax
    5f49:	c3                   	ret

Disassembly of section .fini:

0000000000005f4c <_fini>:
    5f4c:	f3 0f 1e fa          	endbr64
    5f50:	48 83 ec 08          	sub    $0x8,%rsp
    5f54:	48 83 c4 08          	add    $0x8,%rsp
    5f58:	c3                   	ret
