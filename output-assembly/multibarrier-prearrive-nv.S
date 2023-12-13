
multibarrier-prearrive-nv:     file format elf64-x86-64


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
    2556:	48 8d 3d a2 3c 00 00 	lea    0x3ca2(%rip),%rdi        # 61ff <_IO_stdin_used+0x1ff>
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
    2596:	48 8d 3d 32 3c 00 00 	lea    0x3c32(%rip),%rdi        # 61cf <_IO_stdin_used+0x1cf>
    259d:	e8 9e ff ff ff       	call   2540 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    25a2:	48 8d 3d aa 3b 00 00 	lea    0x3baa(%rip),%rdi        # 6153 <_IO_stdin_used+0x153>
    25a9:	e8 92 ff ff ff       	call   2540 <fatal_error>
    fatal_error("listen()");
    25ae:	48 8d 3d be 3b 00 00 	lea    0x3bbe(%rip),%rdi        # 6173 <_IO_stdin_used+0x173>
    25b5:	e8 86 ff ff ff       	call   2540 <fatal_error>
    25ba:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25c2:	0f 0b                	ud2
    25c4:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25cc:	0f 0b                	ud2
      fatal_error("socket()");
    25ce:	48 8d 3d 75 3b 00 00 	lea    0x3b75(%rip),%rdi        # 614a <_IO_stdin_used+0x14a>
    25d5:	e8 66 ff ff ff       	call   2540 <fatal_error>
      fatal_error("bind()");
    25da:	48 8d 3d 8b 3b 00 00 	lea    0x3b8b(%rip),%rdi        # 616c <_IO_stdin_used+0x16c>
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
    25f6:	48 8d 3d b3 3e 00 00 	lea    0x3eb3(%rip),%rdi        # 64b0 <_IO_stdin_used+0x4b0>
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
    2607:	48 83 ec 78          	sub    $0x78,%rsp
    260b:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2614:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    2619:	48 8d 05 20 0f 00 00 	lea    0xf20(%rip),%rax        # 3540 <barriered_reset>
    2620:	66 48 0f 6e e8       	movq   %rax,%xmm5
    2625:	0f 16 2d 4c 66 00 00 	movhps 0x664c(%rip),%xmm5        # 8c78 <__do_global_dtors_aux_fini_array_entry+0x8>
    262c:	0f 29 6c 24 30       	movaps %xmm5,0x30(%rsp)
    2631:	e8 ba fc ff ff       	call   22f0 <puts@plt>
    2636:	bf 0a 00 00 00       	mov    $0xa,%edi
    263b:	e8 90 fc ff ff       	call   22d0 <putchar@plt>
    2640:	48 8d 3d f7 3b 00 00 	lea    0x3bf7(%rip),%rdi        # 623e <_IO_stdin_used+0x23e>
    2647:	e8 a4 fc ff ff       	call   22f0 <puts@plt>
    264c:	ba 02 00 00 00       	mov    $0x2,%edx
    2651:	48 8d 35 02 3c 00 00 	lea    0x3c02(%rip),%rsi        # 625a <_IO_stdin_used+0x25a>
    2658:	31 c0                	xor    %eax,%eax
    265a:	bf 01 00 00 00       	mov    $0x1,%edi
    265f:	e8 ec fd ff ff       	call   2450 <__printf_chk@plt>
    2664:	ba 05 00 00 00       	mov    $0x5,%edx
    2669:	48 8d 35 04 3c 00 00 	lea    0x3c04(%rip),%rsi        # 6274 <_IO_stdin_used+0x274>
    2670:	31 c0                	xor    %eax,%eax
    2672:	bf 01 00 00 00       	mov    $0x1,%edi
    2677:	e8 d4 fd ff ff       	call   2450 <__printf_chk@plt>
    267c:	ba 01 00 00 00       	mov    $0x1,%edx
    2681:	48 8d 35 00 3c 00 00 	lea    0x3c00(%rip),%rsi        # 6288 <_IO_stdin_used+0x288>
    2688:	31 c0                	xor    %eax,%eax
    268a:	bf 01 00 00 00       	mov    $0x1,%edi
    268f:	e8 bc fd ff ff       	call   2450 <__printf_chk@plt>
    2694:	ba 01 00 00 00       	mov    $0x1,%edx
    2699:	48 8d 35 f9 3b 00 00 	lea    0x3bf9(%rip),%rsi        # 6299 <_IO_stdin_used+0x299>
    26a0:	31 c0                	xor    %eax,%eax
    26a2:	bf 01 00 00 00       	mov    $0x1,%edi
    26a7:	e8 a4 fd ff ff       	call   2450 <__printf_chk@plt>
    26ac:	ba 01 00 00 00       	mov    $0x1,%edx
    26b1:	48 8d 35 f9 3b 00 00 	lea    0x3bf9(%rip),%rsi        # 62b1 <_IO_stdin_used+0x2b1>
    26b8:	31 c0                	xor    %eax,%eax
    26ba:	bf 01 00 00 00       	mov    $0x1,%edi
    26bf:	e8 8c fd ff ff       	call   2450 <__printf_chk@plt>
    26c4:	ba 01 00 00 00       	mov    $0x1,%edx
    26c9:	48 8d 35 48 3e 00 00 	lea    0x3e48(%rip),%rsi        # 6518 <_IO_stdin_used+0x518>
    26d0:	31 c0                	xor    %eax,%eax
    26d2:	bf 01 00 00 00       	mov    $0x1,%edi
    26d7:	e8 74 fd ff ff       	call   2450 <__printf_chk@plt>
    26dc:	ba 01 00 00 00       	mov    $0x1,%edx
    26e1:	48 8d 35 60 3e 00 00 	lea    0x3e60(%rip),%rsi        # 6548 <_IO_stdin_used+0x548>
    26e8:	31 c0                	xor    %eax,%eax
    26ea:	bf 01 00 00 00       	mov    $0x1,%edi
    26ef:	e8 5c fd ff ff       	call   2450 <__printf_chk@plt>
    26f4:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    26f9:	48 8d 35 cd 3b 00 00 	lea    0x3bcd(%rip),%rsi        # 62cd <_IO_stdin_used+0x2cd>
    2700:	31 c0                	xor    %eax,%eax
    2702:	bf 01 00 00 00       	mov    $0x1,%edi
    2707:	e8 44 fd ff ff       	call   2450 <__printf_chk@plt>
    270c:	ba 05 00 00 00       	mov    $0x5,%edx
    2711:	48 8d 35 cf 3b 00 00 	lea    0x3bcf(%rip),%rsi        # 62e7 <_IO_stdin_used+0x2e7>
    2718:	31 c0                	xor    %eax,%eax
    271a:	bf 01 00 00 00       	mov    $0x1,%edi
    271f:	e8 2c fd ff ff       	call   2450 <__printf_chk@plt>
    2724:	48 8d 3d a3 39 00 00 	lea    0x39a3(%rip),%rdi        # 60ce <_IO_stdin_used+0xce>
    272b:	e8 c0 fb ff ff       	call   22f0 <puts@plt>
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    2730:	be 18 00 00 00       	mov    $0x18,%esi
    2735:	bf 02 00 00 00       	mov    $0x2,%edi
    273a:	e8 61 fc ff ff       	call   23a0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    273f:	be b0 00 00 00       	mov    $0xb0,%esi
    2744:	bf 05 00 00 00       	mov    $0x5,%edi
  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
    2749:	49 89 c6             	mov    %rax,%r14
    274c:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2751:	e8 4a fc ff ff       	call   23a0 <calloc@plt>
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2756:	be 10 00 00 00       	mov    $0x10,%esi
    275b:	bf 01 00 00 00       	mov    $0x1,%edi
    2760:	49 83 ee 18          	sub    $0x18,%r14
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2764:	48 89 04 24          	mov    %rax,(%rsp)
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    2768:	4d 89 f5             	mov    %r14,%r13
    276b:	41 89 ee             	mov    %ebp,%r14d
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    276e:	e8 2d fc ff ff       	call   23a0 <calloc@plt>
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2773:	be 10 00 00 00       	mov    $0x10,%esi
    2778:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    277d:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2783:	48 89 c3             	mov    %rax,%rbx
    2786:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    278b:	e8 10 fc ff ff       	call   23a0 <calloc@plt>
    2790:	4c 8b 14 24          	mov    (%rsp),%r10
  int curcpu = 0;
    2794:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    279c:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
    27a0:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < total_threads ; x++) {
    27a7:	4d 89 d7             	mov    %r10,%r15
  int external_thread_index = 0;
    27aa:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
            thread_data[x].tasks[y].run = barriered_work; 
    27b2:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    27b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27c0:	be 08 00 00 00       	mov    $0x8,%esi
    27c5:	bf 02 00 00 00       	mov    $0x2,%edi
    27ca:	45 89 f4             	mov    %r14d,%r12d
    27cd:	e8 ce fb ff ff       	call   23a0 <calloc@plt>
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27d2:	be 80 00 00 00       	mov    $0x80,%esi
    27d7:	bf 01 00 00 00       	mov    $0x1,%edi
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    27dc:	48 89 c3             	mov    %rax,%rbx
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    27df:	e8 bc fb ff ff       	call   23a0 <calloc@plt>
    27e4:	44 89 74 24 08       	mov    %r14d,0x8(%rsp)
    27e9:	48 89 04 24          	mov    %rax,(%rsp)
    if (x % 2 == 1) {
    27ed:	44 89 f0             	mov    %r14d,%eax
    27f0:	41 83 c6 01          	add    $0x1,%r14d
    27f4:	83 e0 01             	and    $0x1,%eax
    27f7:	85 c0                	test   %eax,%eax
    27f9:	0f 84 31 0a 00 00    	je     3230 <main+0xc40>
      my_thread_data[0] = &thread_data[other]; 
    27ff:	49 8d 8f 50 ff ff ff 	lea    -0xb0(%r15),%rcx
      my_thread_data[1] = &thread_data[x]; 
    2806:	4c 89 7b 08          	mov    %r15,0x8(%rbx)
    280a:	4d 89 f8             	mov    %r15,%r8
    280d:	31 c0                	xor    %eax,%eax
      my_thread_data[0] = &thread_data[other]; 
    280f:	48 89 0b             	mov    %rcx,(%rbx)
    2812:	44 89 e2             	mov    %r12d,%edx
    2815:	bf 01 00 00 00       	mov    $0x1,%edi
      other = abs(x - 1) % total_threads;
    281a:	41 8d 6c 24 ff       	lea    -0x1(%r12),%ebp
      thread_data[x].thread_index = 1;
    281f:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
    2826:	48 8d 35 ce 3a 00 00 	lea    0x3ace(%rip),%rsi        # 62fb <_IO_stdin_used+0x2fb>
    282d:	e8 1e fc ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[other];
    2832:	49 8d 45 18          	lea    0x18(%r13),%rax
    2836:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    283b:	4d 89 6f 38          	mov    %r13,0x38(%r15)
    283f:	45 8b 07             	mov    (%r15),%r8d
    2842:	89 e9                	mov    %ebp,%ecx
    2844:	44 89 e2             	mov    %r12d,%edx
    2847:	48 8d 35 22 3d 00 00 	lea    0x3d22(%rip),%rsi        # 6570 <_IO_stdin_used+0x570>
    284e:	bf 01 00 00 00       	mov    $0x1,%edi
    2853:	31 c0                	xor    %eax,%eax
    2855:	e8 f6 fb ff ff       	call   2450 <__printf_chk@plt>
    285a:	8b 4c 24 20          	mov    0x20(%rsp),%ecx
    285e:	31 c0                	xor    %eax,%eax
    2860:	44 89 e2             	mov    %r12d,%edx
    thread_data[x].other = other;
    2863:	41 89 af a8 00 00 00 	mov    %ebp,0xa8(%r15)
    286a:	48 8d 35 2f 3d 00 00 	lea    0x3d2f(%rip),%rsi        # 65a0 <_IO_stdin_used+0x5a0>
    2871:	bf 01 00 00 00       	mov    $0x1,%edi
    2876:	e8 d5 fb ff ff       	call   2450 <__printf_chk@plt>
      if (x < thread_count) {
    287b:	83 7c 24 08 01       	cmpl   $0x1,0x8(%rsp)
    2880:	0f 86 1a 0a 00 00    	jbe    32a0 <main+0xcb0>
          CPU_SET(j, sendercpu);
    2886:	48 8b 04 24          	mov    (%rsp),%rax
    288a:	48 81 08 ff 0f 00 00 	orq    $0xfff,(%rax)
    thread_data[x].cpu_set = sendercpu;
    2891:	48 8b 04 24          	mov    (%rsp),%rax
    thread_data[x].threads = my_thread_data;
    2895:	49 89 5f 10          	mov    %rbx,0x10(%r15)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2899:	31 db                	xor    %ebx,%ebx
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    289b:	be 10 00 00 00       	mov    $0x10,%esi
    thread_data[x].real_thread_index = x;
    28a0:	45 89 67 04          	mov    %r12d,0x4(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28a4:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].cpu_set = sendercpu;
    28a9:	49 89 87 a0 00 00 00 	mov    %rax,0xa0(%r15)
    thread_data[x].thread_count = 2;
    28b0:	48 8b 05 89 41 00 00 	mov    0x4189(%rip),%rax        # 6a40 <_IO_stdin_used+0xa40>
    thread_data[x].task_count = total_barrier_count;
    28b7:	41 c7 47 30 03 00 00 00 	movl   $0x3,0x30(%r15)
    thread_data[x].thread_count = 2;
    28bf:	49 89 47 18          	mov    %rax,0x18(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28c3:	e8 d8 fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28c8:	be 10 00 00 00       	mov    $0x10,%esi
    28cd:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    28d2:	49 89 47 58          	mov    %rax,0x58(%r15)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28d6:	e8 c5 fa ff ff       	call   23a0 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28db:	be 28 00 00 00       	mov    $0x28,%esi
    28e0:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    28e5:	66 0f 6f 15 33 41 00 00 	movdqa 0x4133(%rip),%xmm2        # 6a20 <_IO_stdin_used+0xa20>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    28ed:	49 89 47 60          	mov    %rax,0x60(%r15)
    thread_data[x].timestamp_count = 0;
    28f1:	41 0f 11 57 70       	movups %xmm2,0x70(%r15)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    28f6:	e8 a5 fa ff ff       	call   23a0 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    28fb:	be 00 02 00 00       	mov    $0x200,%esi
    2900:	bf 03 00 00 00       	mov    $0x3,%edi
    thread_data[x].task_timestamp_count = 0;
    2905:	66 0f 6f 1d 13 41 00 00 	movdqa 0x4113(%rip),%xmm3        # 6a20 <_IO_stdin_used+0xa20>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    290d:	49 89 87 80 00 00 00 	mov    %rax,0x80(%r15)
    thread_data[x].task_timestamp_count = 0;
    2914:	41 0f 11 9f 88 00 00 00 	movups %xmm3,0x88(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    291c:	e8 7f fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    2921:	44 89 74 24 44       	mov    %r14d,0x44(%rsp)
      thread_data[x].tasks = barriers;
    2926:	49 89 47 28          	mov    %rax,0x28(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    292a:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks[y].protected = do_protected_write; 
    292d:	4c 63 f3             	movslq %ebx,%r14
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2930:	be 20 00 00 00       	mov    $0x20,%esi
    2935:	bf 02 00 00 00       	mov    $0x2,%edi
        thread_data[x].tasks[y].protected = do_protected_write; 
    293a:	4d 89 f5             	mov    %r14,%r13
    293d:	48 8d 05 bc 0b 00 00 	lea    0xbbc(%rip),%rax        # 3500 <do_protected_write>
    2944:	49 c1 e5 09          	shl    $0x9,%r13
    2948:	4a 8d 2c 2a          	lea    (%rdx,%r13,1),%rbp
    294c:	48 89 85 20 01 00 00 	mov    %rax,0x120(%rbp)
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2953:	e8 48 fa ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    2958:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    295c:	48 89 85 68 01 00 00 	mov    %rax,0x168(%rbp)
        for (int b = 0 ; b < 2 ; b++) {
    2963:	48 89 c5             	mov    %rax,%rbp
    2966:	48 8d 40 40          	lea    0x40(%rax),%rax
    296a:	48 89 04 24          	mov    %rax,(%rsp)
    296e:	44 89 64 24 10       	mov    %r12d,0x10(%rsp)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2973:	be 08 00 00 00       	mov    $0x8,%esi
    2978:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < 2 ; b++) {
    297d:	48 83 c5 20          	add    $0x20,%rbp
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2981:	e8 1a fa ff ff       	call   23a0 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2986:	be 08 00 00 00       	mov    $0x8,%esi
    298b:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2990:	49 89 c4             	mov    %rax,%r12
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2993:	e8 08 fa ff ff       	call   23a0 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    2998:	be 18 00 00 00       	mov    $0x18,%esi
    299d:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    29a2:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    29a5:	e8 f6 f9 ff ff       	call   23a0 <calloc@plt>
          data[0].messages_count = 0;
    29aa:	66 0f 6f 05 7e 40 00 00 	movdqa 0x407e(%rip),%xmm0        # 6a30 <_IO_stdin_used+0xa30>
          mailboxes[b].higher = &data[1];
    29b2:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    29b6:	48 89 45 e0          	mov    %rax,-0x20(%rbp)
          mailboxes[b].higher = &data[1];
    29ba:	48 89 75 e8          	mov    %rsi,-0x18(%rbp)
          data[0].messages = messages;
    29be:	4c 89 20             	mov    %r12,(%rax)
          data[1].messages = messages2;
    29c1:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    29c5:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    29c9:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < 2 ; b++) {
    29cd:	48 39 2c 24          	cmp    %rbp,(%rsp)
    29d1:	75 a0                	jne    2973 <main+0x383>
        char *message = malloc(sizeof(char) * 256);
    29d3:	be 01 00 00 00       	mov    $0x1,%esi
    29d8:	bf 00 01 00 00       	mov    $0x100,%edi
    29dd:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    29e1:	44 8b 64 24 10       	mov    0x10(%rsp),%r12d
    29e6:	e8 b5 f9 ff ff       	call   23a0 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    29eb:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    29f0:	48 89 c5             	mov    %rax,%rbp
        struct Message *messaged = malloc(sizeof(struct Message));
    29f3:	e8 18 fa ff ff       	call   2410 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    29f8:	48 89 ef             	mov    %rbp,%rdi
    29fb:	41 89 d9             	mov    %ebx,%r9d
    29fe:	45 89 e0             	mov    %r12d,%r8d
    2a01:	48 8d 0d b8 3b 00 00 	lea    0x3bb8(%rip),%rcx        # 65c0 <_IO_stdin_used+0x5c0>
    2a08:	48 89 04 24          	mov    %rax,(%rsp)
    2a0c:	ba 00 01 00 00       	mov    $0x100,%edx
    2a11:	31 c0                	xor    %eax,%eax
    2a13:	be 01 00 00 00       	mov    $0x1,%esi
    2a18:	e8 03 fb ff ff       	call   2520 <__sprintf_chk@plt>
        messaged->message = message;
    2a1d:	4c 8b 14 24          	mov    (%rsp),%r10
        messaged->thread_index = thread_data[x].thread_index;
    2a21:	49 63 07             	movslq (%r15),%rax
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a24:	be 20 00 00 00       	mov    $0x20,%esi
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a29:	49 8b 57 28          	mov    0x28(%r15),%rdx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a2d:	bf 63 00 00 00       	mov    $0x63,%edi
        messaged->message = message;
    2a32:	49 89 2a             	mov    %rbp,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a35:	8d 6b 01             	lea    0x1(%rbx),%ebp
        messaged->thread_index = thread_data[x].thread_index;
    2a38:	49 89 42 08          	mov    %rax,0x8(%r10)
    2a3c:	89 44 24 08          	mov    %eax,0x8(%rsp)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a40:	89 e8                	mov    %ebp,%eax
        messaged->task_index = y;
    2a42:	4d 89 72 10          	mov    %r14,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a46:	83 e0 01             	and    $0x1,%eax
    2a49:	4e 8d 34 2a          	lea    (%rdx,%r13,1),%r14
    2a4d:	41 89 86 88 01 00 00 	mov    %eax,0x188(%r14)
        thread_data[x].tasks[y].message = messaged;
    2a54:	4d 89 96 80 01 00 00 	mov    %r10,0x180(%r14)
        thread_data[x].tasks[y].snapshot_count = 99;
    2a5b:	49 c7 86 50 01 00 00 63 00 00 00 	movq   $0x63,0x150(%r14)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2a66:	48 89 14 24          	mov    %rdx,(%rsp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a6a:	e8 31 f9 ff ff       	call   23a0 <calloc@plt>
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2a6f:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
        if (y == barrier_count - 1) {
    2a73:	83 fb 01             	cmp    $0x1,%ebx
        thread_data[x].tasks[y].task_index = y;
    2a76:	41 89 1e             	mov    %ebx,(%r14)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2a79:	49 89 86 48 01 00 00 	mov    %rax,0x148(%r14)
        if (y == barrier_count - 1) {
    2a80:	48 8b 14 24          	mov    (%rsp),%rdx
        thread_data[x].tasks[y].available = 1;
    2a84:	48 b8 01 00 00 00 03 00 00 00 	movabs $0x300000001,%rax
    2a8e:	49 89 86 38 01 00 00 	mov    %rax,0x138(%r14)
        thread_data[x].tasks[y].sending = 1;
    2a95:	48 b8 01 00 00 00 02 00 00 00 	movabs $0x200000001,%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2a9f:	49 c7 86 58 01 00 00 00 00 00 00 	movq   $0x0,0x158(%r14)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    2aaa:	41 89 8e 30 01 00 00 	mov    %ecx,0x130(%r14)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2ab1:	4d 89 be 28 01 00 00 	mov    %r15,0x128(%r14)
        thread_data[x].tasks[y].arrived = 0;
    2ab8:	41 c7 86 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r14)
        thread_data[x].tasks[y].thread_count = 2;
    2ac3:	41 c7 86 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%r14)
        thread_data[x].tasks[y].sending = 1;
    2ace:	49 89 86 78 01 00 00 	mov    %rax,0x178(%r14)
        if (y == barrier_count - 1) {
    2ad5:	0f 84 35 07 00 00    	je     3210 <main+0xc20>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2adb:	44 39 e3             	cmp    %r12d,%ebx
    2ade:	75 60                	jne    2b40 <main+0x550>
    2ae0:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
    2ae4:	85 db                	test   %ebx,%ebx
    2ae6:	7f 58                	jg     2b40 <main+0x550>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2ae8:	44 89 e2             	mov    %r12d,%edx
    2aeb:	48 8d 35 f6 3a 00 00 	lea    0x3af6(%rip),%rsi        # 65e8 <_IO_stdin_used+0x5e8>
    2af2:	bf 01 00 00 00       	mov    $0x1,%edi
    2af7:	31 c0                	xor    %eax,%eax
    2af9:	e8 52 f9 ff ff       	call   2450 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2afe:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    2b03:	48 63 c3             	movslq %ebx,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b06:	49 8b 57 28          	mov    0x28(%r15),%rdx
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b0a:	48 c1 e0 04          	shl    $0x4,%rax
    2b0e:	48 01 c8             	add    %rcx,%rax
    2b11:	49 89 47 40          	mov    %rax,0x40(%r15)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2b15:	48 8d 05 34 2f 00 00 	lea    0x2f34(%rip),%rax        # 5a50 <barriered_work_ingest>
    2b1c:	4a 89 84 2a 18 01 00 00 	mov    %rax,0x118(%rdx,%r13,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2b24:	8d 43 01             	lea    0x1(%rbx),%eax
    2b27:	89 44 24 18          	mov    %eax,0x18(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b2b:	83 fd 03             	cmp    $0x3,%ebp
    2b2e:	74 23                	je     2b53 <main+0x563>
    2b30:	bb 01 00 00 00       	mov    $0x1,%ebx
    2b35:	e9 f3 fd ff ff       	jmp    292d <main+0x33d>
    2b3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            thread_data[x].tasks[y].run = barriered_work; 
    2b40:	48 8d 05 09 2a 00 00 	lea    0x2a09(%rip),%rax        # 5550 <barriered_work>
    2b47:	49 89 86 18 01 00 00 	mov    %rax,0x118(%r14)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2b4e:	83 fd 03             	cmp    $0x3,%ebp
    2b51:	75 dd                	jne    2b30 <main+0x540>
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b53:	48 b8 02 00 00 00 01 00 00 00 	movabs $0x100000002,%rax
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b5d:	44 8b 74 24 44       	mov    0x44(%rsp),%r14d
  for (int x = 0 ; x < total_threads ; x++) {
    2b62:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2b67:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2b71:	c7 82 00 04 00 00 02 00 00 00 	movl   $0x2,0x400(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2b7b:	66 0f 6f 64 24 30    	movdqa 0x30(%rsp),%xmm4
      thread_data[x].tasks[barrier_count].thread_count = 2; 
    2b81:	48 89 82 34 05 00 00 	mov    %rax,0x534(%rdx)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2b88:	41 8b 07             	mov    (%r15),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2b8b:	4c 89 ba 28 05 00 00 	mov    %r15,0x528(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2b92:	49 81 c7 b0 00 00 00 	add    $0xb0,%r15
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2b99:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2b9f:	c7 82 7c 05 00 00 02 00 00 00 	movl   $0x2,0x57c(%rdx)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2ba9:	c7 82 3c 05 00 00 03 00 00 00 	movl   $0x3,0x53c(%rdx)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2bb3:	0f 11 a2 18 05 00 00 	movups %xmm4,0x518(%rdx)
  for (int x = 0 ; x < total_threads ; x++) {
    2bba:	41 83 fe 05          	cmp    $0x5,%r14d
    2bbe:	0f 85 fc fb ff ff    	jne    27c0 <main+0x1d0>
    2bc4:	4c 8b 54 24 50       	mov    0x50(%rsp),%r10
    2bc9:	ba 03 00 00 00       	mov    $0x3,%edx
    2bce:	48 8d 35 43 37 00 00 	lea    0x3743(%rip),%rsi        # 6318 <_IO_stdin_used+0x318>
    2bd5:	31 c0                	xor    %eax,%eax
    2bd7:	bf 01 00 00 00       	mov    $0x1,%edi
    2bdc:	4c 89 14 24          	mov    %r10,(%rsp)
    2be0:	e8 6b f8 ff ff       	call   2450 <__printf_chk@plt>
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2be5:	be 08 00 00 00       	mov    $0x8,%esi
    2bea:	bf 02 00 00 00       	mov    $0x2,%edi
    2bef:	e8 ac f7 ff ff       	call   23a0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    2bf4:	4c 8b 14 24          	mov    (%rsp),%r10
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bf8:	be 38 00 00 00       	mov    $0x38,%esi
    2bfd:	bf 05 00 00 00       	mov    $0x5,%edi
    my_thread_data[0] = &thread_data[x]; 
    2c02:	4d 8d ba 10 02 00 00 	lea    0x210(%r10),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    2c09:	4c 89 50 08          	mov    %r10,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c0d:	4d 8d b2 b0 00 00 00 	lea    0xb0(%r10),%r14
    thread_data[x].threads = my_thread_data;
    2c14:	49 89 82 20 02 00 00 	mov    %rax,0x220(%r10)
    my_thread_data[0] = &thread_data[x]; 
    2c1b:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    2c1e:	49 8b 42 28          	mov    0x28(%r10),%rax
    thread_data[x].thread_count = 2;
    2c22:	41 c7 82 28 02 00 00 02 00 00 00 	movl   $0x2,0x228(%r10)
    thread_data[x].thread_index = 0;
    2c2d:	41 c7 82 10 02 00 00 00 00 00 00 	movl   $0x0,0x210(%r10)
    thread_data[x].task_count = total_barrier_count;
    2c38:	41 c7 82 40 02 00 00 03 00 00 00 	movl   $0x3,0x240(%r10)
    thread_data[n].tasks[0].scheduled = 1;
    2c43:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
    2c4d:	49 8b 82 d8 00 00 00 	mov    0xd8(%r10),%rax
    2c54:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    2c59:	c7 80 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c63:	e8 38 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c68:	be 38 00 00 00       	mov    $0x38,%esi
    2c6d:	bf 05 00 00 00       	mov    $0x5,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c72:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c75:	e8 26 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c7a:	be 38 00 00 00       	mov    $0x38,%esi
    2c7f:	bf 05 00 00 00       	mov    $0x5,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c84:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c87:	e8 14 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c8c:	be 38 00 00 00       	mov    $0x38,%esi
    2c91:	bf 05 00 00 00       	mov    $0x5,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c96:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2c9a:	e8 01 f7 ff ff       	call   23a0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2c9f:	be 08 00 00 00       	mov    $0x8,%esi
    2ca4:	bf 05 00 00 00       	mov    $0x5,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ca9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2cae:	e8 ed f6 ff ff       	call   23a0 <calloc@plt>

  thread_data[thread_count].type = TIMER;
    2cb3:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2cb8:	be 08 00 00 00       	mov    $0x8,%esi
    2cbd:	bf 05 00 00 00       	mov    $0x5,%edi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2cc2:	48 89 c3             	mov    %rax,%rbx
  thread_data[thread_count].task_count = total_barrier_count;
    2cc5:	48 8b 05 7c 3d 00 00 	mov    0x3d7c(%rip),%rax        # 6a48 <_IO_stdin_used+0xa48>
  thread_data[thread_count].type = TIMER;
    2ccc:	41 c7 82 68 01 00 00 00 00 00 00 	movl   $0x0,0x168(%r10)
  thread_data[thread_count].task_count = total_barrier_count;
    2cd7:	49 89 82 90 01 00 00 	mov    %rax,0x190(%r10)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    2cde:	e8 bd f6 ff ff       	call   23a0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    2ce3:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2ce8:	ba 02 00 00 00       	mov    $0x2,%edx
    2ced:	48 8d 35 33 36 00 00 	lea    0x3633(%rip),%rsi        # 6327 <_IO_stdin_used+0x327>
    2cf4:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2cf8:	bf 01 00 00 00       	mov    $0x1,%edi
    2cfd:	49 8d 8a 60 01 00 00 	lea    0x160(%r10),%rcx
    2d04:	4d 8d a2 c0 02 00 00 	lea    0x2c0(%r10),%r12
    2d0b:	4c 89 10             	mov    %r10,(%rax)
  }
  thread_data[thread_count].threads = my_thread_data;
    2d0e:	49 89 82 70 01 00 00 	mov    %rax,0x170(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2d15:	48 89 48 10          	mov    %rcx,0x10(%rax)
    2d19:	4c 89 60 20          	mov    %r12,0x20(%rax)
  thread_data[thread_count].thread_count = thread_count;
    2d1d:	41 c7 82 78 01 00 00 02 00 00 00 	movl   $0x2,0x178(%r10)
  thread_data[thread_count].my_thread_count = 2;
    2d28:	41 c7 82 80 01 00 00 02 00 00 00 	movl   $0x2,0x180(%r10)
  thread_data[thread_count].thread_index = 0;
    2d33:	41 c7 82 60 01 00 00 00 00 00 00 	movl   $0x0,0x160(%r10)
    my_thread_data[n] = &thread_data[n]; 
    2d3e:	4c 89 78 18          	mov    %r15,0x18(%rax)
    2d42:	31 c0                	xor    %eax,%eax
    2d44:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    2d49:	e8 02 f7 ff ff       	call   2450 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2d4e:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    2d53:	49 8d 75 70          	lea    0x70(%r13),%rsi
    2d57:	48 8d 7b 10          	lea    0x10(%rbx),%rdi
    2d5b:	48 8d 15 be 0b 00 00 	lea    0xbbe(%rip),%rdx        # 3920 <timer_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    thread_data[x].type = WORKER;
    thread_data[x].running = 1;
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2d62:	4c 8d 2d 47 08 00 00 	lea    0x847(%rip),%r13        # 35b0 <barriered_thread>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2d69:	e8 02 f7 ff ff       	call   2470 <pthread_create@plt>
    thread_data[x].type = WORKER;
    2d6e:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2d73:	31 d2                	xor    %edx,%edx
    2d75:	31 c0                	xor    %eax,%eax
    2d77:	4c 8d 0d 8a 38 00 00 	lea    0x388a(%rip),%r9        # 6608 <_IO_stdin_used+0x608>
    2d7e:	bf 01 00 00 00       	mov    $0x1,%edi
    2d83:	41 c7 42 08 01 00 00 00 	movl   $0x1,0x8(%r10)
    2d8b:	4c 89 ce             	mov    %r9,%rsi
    thread_data[x].running = 1;
    2d8e:	41 c7 42 34 01 00 00 00 	movl   $0x1,0x34(%r10)
    2d96:	e8 b5 f6 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2d9b:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2da0:	4c 89 ea             	mov    %r13,%rdx
    2da3:	48 89 ee             	mov    %rbp,%rsi
    2da6:	48 89 df             	mov    %rbx,%rdi
    2da9:	e8 c2 f6 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2dae:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2db3:	48 8b 3b             	mov    (%rbx),%rdi
    2db6:	be 08 00 00 00       	mov    $0x8,%esi
    2dbb:	49 8b 92 a0 00 00 00 	mov    0xa0(%r10),%rdx
    2dc2:	e8 19 f5 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
    thread_data[x].type = WORKER;
    2dc7:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2dcc:	ba 01 00 00 00       	mov    $0x1,%edx
    2dd1:	31 c0                	xor    %eax,%eax
    2dd3:	4c 8d 0d 2e 38 00 00 	lea    0x382e(%rip),%r9        # 6608 <_IO_stdin_used+0x608>
    2dda:	bf 01 00 00 00       	mov    $0x1,%edi
    2ddf:	41 c7 82 b8 00 00 00 01 00 00 00 	movl   $0x1,0xb8(%r10)
    2dea:	4c 89 ce             	mov    %r9,%rsi
    thread_data[x].running = 1;
    2ded:	41 c7 82 e4 00 00 00 01 00 00 00 	movl   $0x1,0xe4(%r10)
    2df8:	e8 53 f6 ff ff       	call   2450 <__printf_chk@plt>
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    2dfd:	4c 89 f1             	mov    %r14,%rcx
    2e00:	48 8d 75 38          	lea    0x38(%rbp),%rsi
    2e04:	4c 89 ea             	mov    %r13,%rdx
    2e07:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    2e0b:	4c 8d 6c 24 60       	lea    0x60(%rsp),%r13
    2e10:	e8 5b f6 ff ff       	call   2470 <pthread_create@plt>
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    2e15:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2e1a:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
    2e1e:	be 08 00 00 00       	mov    $0x8,%esi
    2e23:	49 8b 92 50 01 00 00 	mov    0x150(%r10),%rdx
    2e2a:	e8 b1 f4 ff ff       	call   22e0 <pthread_setaffinity_np@plt>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2e2f:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e34:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].task_count = 0;
    2e39:	48 8b 2d 10 3c 00 00 	mov    0x3c10(%rip),%rbp        # 6a50 <_IO_stdin_used+0xa50>
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e40:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    2e45:	49 89 aa 40 02 00 00 	mov    %rbp,0x240(%r10)
    thread_data[x].type = IO;
    2e4c:	41 c7 82 18 02 00 00 02 00 00 00 	movl   $0x2,0x218(%r10)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e57:	e8 44 f5 ff ff       	call   23a0 <calloc@plt>
    2e5c:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e61:	31 ff                	xor    %edi,%edi
    2e63:	be 00 08 00 00       	mov    $0x800,%esi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2e68:	49 89 82 58 02 00 00 	mov    %rax,0x258(%r10)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e6f:	e8 3c f6 ff ff       	call   24b0 <eventfd@plt>
    2e74:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2e79:	be 08 00 00 00       	mov    $0x8,%esi
    2e7e:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2e83:	41 89 82 60 02 00 00 	mov    %eax,0x260(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2e8a:	e8 11 f5 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    2e8f:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2e94:	ba 03 00 00 00       	mov    $0x3,%edx
    2e99:	48 8d 35 a5 34 00 00 	lea    0x34a5(%rip),%rsi        # 6345 <_IO_stdin_used+0x345>
    2ea0:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2ea4:	bf 01 00 00 00       	mov    $0x1,%edi
    2ea9:	4c 89 10             	mov    %r10,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    2eac:	49 89 82 20 02 00 00 	mov    %rax,0x220(%r10)
    2eb3:	31 c0                	xor    %eax,%eax
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    2eb5:	41 c7 82 28 02 00 00 02 00 00 00 	movl   $0x2,0x228(%r10)
    thread_data[x].thread_index = x;
    2ec0:	41 c7 82 10 02 00 00 03 00 00 00 	movl   $0x3,0x210(%r10)
    2ecb:	e8 80 f5 ff ff       	call   2450 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2ed0:	48 8b 34 24          	mov    (%rsp),%rsi
    2ed4:	4c 89 f9             	mov    %r15,%rcx
    2ed7:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    2edb:	48 8d 15 ae 1c 00 00 	lea    0x1cae(%rip),%rdx        # 4b90 <io_thread>
    2ee2:	48 81 c6 a8 00 00 00 	add    $0xa8,%rsi
    2ee9:	e8 82 f5 ff ff       	call   2470 <pthread_create@plt>
    2eee:	ba 04 00 00 00       	mov    $0x4,%edx
    2ef3:	48 8d 35 62 34 00 00 	lea    0x3462(%rip),%rsi        # 635c <_IO_stdin_used+0x35c>
    2efa:	31 c0                	xor    %eax,%eax
    2efc:	bf 01 00 00 00       	mov    $0x1,%edi
    2f01:	e8 4a f5 ff ff       	call   2450 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    2f06:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    2f0b:	48 8b 7c 24 48       	mov    0x48(%rsp),%rdi

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f10:	be 08 00 00 00       	mov    $0x8,%esi
    thread_data[x].task_count = 0;
    2f15:	49 89 aa f0 02 00 00 	mov    %rbp,0x2f0(%r10)
    thread_data[x].buffers = &buffers[buffer_index];
    2f1c:	49 89 ba 00 03 00 00 	mov    %rdi,0x300(%r10)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f23:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x].type = EXTERNAL;
    2f28:	41 c7 82 c8 02 00 00 03 00 00 00 	movl   $0x3,0x2c8(%r10)
    thread_data[x].buffers = &buffers[buffer_index];
    2f33:	4c 89 14 24          	mov    %r10,(%rsp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    2f37:	e8 64 f4 ff ff       	call   23a0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    2f3c:	4c 8b 14 24          	mov    (%rsp),%r10
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f40:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2f45:	4c 89 e1             	mov    %r12,%rcx
    thread_data[x].thread_count = thread_count;
    2f48:	48 8b 3d f1 3a 00 00 	mov    0x3af1(%rip),%rdi        # 6a40 <_IO_stdin_used+0xa40>
      my_thread_data[n] = &thread_data[n]; 
    2f4f:	4c 89 70 08          	mov    %r14,0x8(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f53:	48 8d 15 06 09 00 00 	lea    0x906(%rip),%rdx        # 3860 <external_thread>
    2f5a:	4c 8d 25 36 34 00 00 	lea    0x3436(%rip),%r12        # 6397 <_IO_stdin_used+0x397>
      my_thread_data[n] = &thread_data[n]; 
    2f61:	4c 89 10             	mov    %r10,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f64:	48 81 c6 e0 00 00 00 	add    $0xe0,%rsi
    2f6b:	31 ed                	xor    %ebp,%ebp
    thread_data[x].thread_count = thread_count;
    2f6d:	49 89 ba d8 02 00 00 	mov    %rdi,0x2d8(%r10)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f74:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
    thread_data[x].threads = my_thread_data;
    2f78:	49 89 82 d0 02 00 00 	mov    %rax,0x2d0(%r10)
    thread_data[x].thread_index = x;
    2f7f:	41 c7 82 c0 02 00 00 04 00 00 00 	movl   $0x4,0x2c0(%r10)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2f8a:	e8 e1 f4 ff ff       	call   2470 <pthread_create@plt>
    2f8f:	48 8d 3d e3 33 00 00 	lea    0x33e3(%rip),%rdi        # 6379 <_IO_stdin_used+0x379>
    2f96:	e8 55 f3 ff ff       	call   22f0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    2f9b:	4c 8b 34 24          	mov    (%rsp),%r14
    2f9f:	90                   	nop
    void * result; 
    pthread_join(thread[x], &result);
    2fa0:	48 8b 3c eb          	mov    (%rbx,%rbp,8),%rdi
    2fa4:	4c 89 ee             	mov    %r13,%rsi
    2fa7:	e8 44 f5 ff ff       	call   24f0 <pthread_join@plt>
    2fac:	89 ea                	mov    %ebp,%edx
    2fae:	4c 89 e6             	mov    %r12,%rsi
    2fb1:	bf 01 00 00 00       	mov    $0x1,%edi
    2fb6:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2fb8:	48 83 c5 01          	add    $0x1,%rbp
    2fbc:	e8 8f f4 ff ff       	call   2450 <__printf_chk@plt>
    2fc1:	48 83 fd 05          	cmp    $0x5,%rbp
    2fc5:	75 d9                	jne    2fa0 <main+0x9b0>
    2fc7:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    2fcc:	4d 89 f2             	mov    %r14,%r10
    2fcf:	4d 8d 7e 28          	lea    0x28(%r14),%r15
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
    2fd3:	45 31 c9             	xor    %r9d,%r9d
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    2fd6:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
  long total = 0;
    2fde:	45 31 f6             	xor    %r14d,%r14d
  long received = 0;
    2fe1:	31 ed                	xor    %ebp,%ebp
  long sents = 0;
    2fe3:	45 31 e4             	xor    %r12d,%r12d
    2fe6:	48 89 04 24          	mov    %rax,(%rsp)
    2fea:	4d 89 f0             	mov    %r14,%r8
    2fed:	4d 89 fe             	mov    %r15,%r14
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    2ff0:	49 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r13
    2ffa:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    2fff:	4d 89 cf             	mov    %r9,%r15
    3002:	bf 0a 00 00 00       	mov    $0xa,%edi
    3007:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    300c:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    3010:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    3015:	e8 b6 f2 ff ff       	call   22d0 <putchar@plt>
    301a:	48 8b 04 24          	mov    (%rsp),%rax
    301e:	bf 01 00 00 00       	mov    $0x1,%edi
    3023:	83 f3 01             	xor    $0x1,%ebx
    3026:	48 8d 35 7e 33 00 00 	lea    0x337e(%rip),%rsi        # 63ab <_IO_stdin_used+0x3ab>
    302d:	48 8b 10             	mov    (%rax),%rdx
    3030:	31 c0                	xor    %eax,%eax
    3032:	e8 19 f4 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3037:	49 63 56 08          	movslq 0x8(%r14),%rdx
    303b:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    3040:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3045:	85 d2                	test   %edx,%edx
    3047:	0f 8e b1 03 00 00    	jle    33fe <main+0xe0e>
    304d:	49 8b 06             	mov    (%r14),%rax
    3050:	48 c1 e2 09          	shl    $0x9,%rdx
    3054:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    long v = 0;
    3058:	31 d2                	xor    %edx,%edx
    305a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      v += thread_data[me].tasks[n].v;
    3060:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3067:	48 05 00 02 00 00    	add    $0x200,%rax
    306d:	48 39 f0             	cmp    %rsi,%rax
    3070:	75 ee                	jne    3060 <main+0xa70>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3072:	48 63 c3             	movslq %ebx,%rax
    3075:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    307a:	48 f7 d8             	neg    %rax
    307d:	25 b0 00 00 00       	and    $0xb0,%eax
    3082:	48 01 f8             	add    %rdi,%rax
    3085:	48 63 70 30          	movslq 0x30(%rax),%rsi
    3089:	85 f6                	test   %esi,%esi
    308b:	7e 25                	jle    30b2 <main+0xac2>
    308d:	48 8b 40 28          	mov    0x28(%rax),%rax
    3091:	48 c1 e6 09          	shl    $0x9,%rsi
    3095:	48 01 c6             	add    %rax,%rsi
    3098:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      v += thread_data[other].tasks[n].v;
    30a0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    30a7:	48 05 00 02 00 00    	add    $0x200,%rax
    30ad:	48 39 f0             	cmp    %rsi,%rax
    30b0:	75 ee                	jne    30a0 <main+0xab0>
    30b2:	48 8d 35 07 33 00 00 	lea    0x3307(%rip),%rsi        # 63c0 <_IO_stdin_used+0x3c0>
    30b9:	bf 01 00 00 00       	mov    $0x1,%edi
    30be:	31 c0                	xor    %eax,%eax
    30c0:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    30c5:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    30ca:	e8 81 f3 ff ff       	call   2450 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    30cf:	48 8b 04 24          	mov    (%rsp),%rax
    30d3:	bf 01 00 00 00       	mov    $0x1,%edi
    30d8:	48 8b 30             	mov    (%rax),%rsi
    30db:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    30e5:	48 f7 ee             	imul   %rsi
    30e8:	48 c1 fe 3f          	sar    $0x3f,%rsi
    30ec:	31 c0                	xor    %eax,%eax
    30ee:	48 d1 fa             	sar    %rdx
    30f1:	48 29 f2             	sub    %rsi,%rdx
    30f4:	48 8d 35 35 35 00 00 	lea    0x3535(%rip),%rsi        # 6630 <_IO_stdin_used+0x630>
    30fb:	e8 50 f3 ff ff       	call   2450 <__printf_chk@plt>
    3100:	bf 0a 00 00 00       	mov    $0xa,%edi
    3105:	e8 c6 f1 ff ff       	call   22d0 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    310a:	49 63 56 08          	movslq 0x8(%r14),%rdx
    310e:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    3113:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    3118:	85 d2                	test   %edx,%edx
    311a:	7e 4b                	jle    3167 <main+0xb77>
    311c:	49 8b 06             	mov    (%r14),%rax
    311f:	48 c1 e2 09          	shl    $0x9,%rdx
    3123:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3127:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3130:	48 8b 90 68 01 00 00 	mov    0x168(%rax),%rdx
      total += thread_data[x].tasks[n].n;
    3137:	4c 03 80 08 01 00 00 	add    0x108(%rax),%r8
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    313e:	48 05 00 02 00 00    	add    $0x200,%rax
      ingests += thread_data[x].tasks[n].ingest_count;
    3144:	4c 03 b8 60 ff ff ff 	add    -0xa0(%rax),%r15
      sends += thread_data[x].tasks[n].sends;
    314b:	4c 03 88 70 ff ff ff 	add    -0x90(%rax),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    3152:	4c 03 62 10          	add    0x10(%rdx),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    3156:	48 03 6a 18          	add    0x18(%rdx),%rbp
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    315a:	4c 03 62 30          	add    0x30(%rdx),%r12
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    315e:	48 03 6a 38          	add    0x38(%rdx),%rbp
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3162:	48 39 c6             	cmp    %rax,%rsi
    3165:	75 c9                	jne    3130 <main+0xb40>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3167:	31 db                	xor    %ebx,%ebx
    3169:	49 83 7e 68 00       	cmpq   $0x0,0x68(%r14)
    316e:	7e 74                	jle    31e4 <main+0xbf4>
    3170:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    3175:	48 89 6c 24 10       	mov    %rbp,0x10(%rsp)
    317a:	4c 89 f5             	mov    %r14,%rbp
    317d:	4d 89 ce             	mov    %r9,%r14
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3180:	48 8b 45 58          	mov    0x58(%rbp),%rax
    3184:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    3188:	48 83 ec 08          	sub    $0x8,%rsp
    318c:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3191:	48 83 c3 01          	add    $0x1,%rbx
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3195:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3199:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    319d:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    31a1:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    31a4:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    31a8:	4c 2b 01             	sub    (%rcx),%r8
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    31ab:	49 f7 e5             	mul    %r13
    31ae:	8b 49 20             	mov    0x20(%rcx),%ecx
    31b1:	56                   	push   %rsi
    31b2:	31 c0                	xor    %eax,%eax
    31b4:	48 8d 35 95 34 00 00 	lea    0x3495(%rip),%rsi        # 6650 <_IO_stdin_used+0x650>
    31bb:	48 c1 ea 12          	shr    $0x12,%rdx
    31bf:	49 89 d1             	mov    %rdx,%r9
    31c2:	ba 02 00 00 00       	mov    $0x2,%edx
    31c7:	e8 84 f2 ff ff       	call   2450 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    31cc:	58                   	pop    %rax
    31cd:	5a                   	pop    %rdx
    31ce:	48 39 5d 68          	cmp    %rbx,0x68(%rbp)
    31d2:	7f ac                	jg     3180 <main+0xb90>
    31d4:	4d 89 f1             	mov    %r14,%r9
    31d7:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    31dc:	49 89 ee             	mov    %rbp,%r14
    31df:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
  for (int x = 0 ; x < thread_count ; x++) {
    31e4:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    31e8:	48 83 04 24 18       	addq   $0x18,(%rsp)
    31ed:	49 81 c6 b0 00 00 00 	add    $0xb0,%r14
    31f4:	85 c9                	test   %ecx,%ecx
    31f6:	0f 85 d4 00 00 00    	jne    32d0 <main+0xce0>
    31fc:	c7 44 24 08 01 00 00 00 	movl   $0x1,0x8(%rsp)
    3204:	e9 f9 fd ff ff       	jmp    3002 <main+0xa12>
    3209:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          thread_data[x].tasks[y].run = barriered_work; 
    3210:	48 8d 05 39 23 00 00 	lea    0x2339(%rip),%rax        # 5550 <barriered_work>
    3217:	bb 02 00 00 00       	mov    $0x2,%ebx
    321c:	49 89 86 18 01 00 00 	mov    %rax,0x118(%r14)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3223:	e9 05 f7 ff ff       	jmp    292d <main+0x33d>
    3228:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      other = (x + 1) % total_threads;
    3230:	b8 cd cc cc cc       	mov    $0xcccccccd,%eax
    3235:	45 89 f2             	mov    %r14d,%r10d
    3238:	44 89 f5             	mov    %r14d,%ebp
      my_thread_data[0] = &thread_data[x]; 
    323b:	4c 89 3b             	mov    %r15,(%rbx)
      other = (x + 1) % total_threads;
    323e:	4c 0f af d0          	imul   %rax,%r10
    3242:	4c 89 f9             	mov    %r15,%rcx
      thread_data[x].thread_index = 0;
    3245:	41 c7 07 00 00 00 00 	movl   $0x0,(%r15)
    324c:	48 8d 35 b6 30 00 00 	lea    0x30b6(%rip),%rsi        # 6309 <_IO_stdin_used+0x309>
    3253:	bf 01 00 00 00       	mov    $0x1,%edi
      other = (x + 1) % total_threads;
    3258:	49 c1 ea 22          	shr    $0x22,%r10
    325c:	43 8d 04 92          	lea    (%r10,%r10,4),%eax
    3260:	29 c5                	sub    %eax,%ebp
      my_thread_data[1] = &thread_data[other]; 
    3262:	48 63 c5             	movslq %ebp,%rax
    3265:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3269:	4c 8d 04 50          	lea    (%rax,%rdx,2),%r8
    326d:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    3272:	44 89 e2             	mov    %r12d,%edx
    3275:	49 c1 e0 04          	shl    $0x4,%r8
    3279:	49 01 c0             	add    %rax,%r8
    327c:	31 c0                	xor    %eax,%eax
    327e:	4c 89 43 08          	mov    %r8,0x8(%rbx)
    3282:	e8 c9 f1 ff ff       	call   2450 <__printf_chk@plt>
      thread_data[x].protected_state = &protected_state[x];
    3287:	49 8d 45 18          	lea    0x18(%r13),%rax
    328b:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3290:	49 89 c5             	mov    %rax,%r13
    3293:	e9 a3 f5 ff ff       	jmp    283b <main+0x24b>
    3298:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        CPU_SET(curcpu, sendercpu);
    32a0:	48 63 44 24 20       	movslq 0x20(%rsp),%rax
    32a5:	48 89 c1             	mov    %rax,%rcx
    32a8:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    32ae:	77 14                	ja     32c4 <main+0xcd4>
    32b0:	48 8b 3c 24          	mov    (%rsp),%rdi
    32b4:	48 c1 e8 06          	shr    $0x6,%rax
    32b8:	ba 01 00 00 00       	mov    $0x1,%edx
    32bd:	48 d3 e2             	shl    %cl,%rdx
    32c0:	48 09 14 c7          	or     %rdx,(%rdi,%rax,8)
        curcpu += 2;
    32c4:	83 44 24 20 02       	addl   $0x2,0x20(%rsp)
    32c9:	e9 c3 f5 ff ff       	jmp    2891 <main+0x2a1>
    32ce:	66 90                	xchg   %ax,%ax
    32d0:	4c 89 c2             	mov    %r8,%rdx
    32d3:	48 8d 35 f3 30 00 00 	lea    0x30f3(%rip),%rsi        # 63cd <_IO_stdin_used+0x3cd>
    32da:	31 c0                	xor    %eax,%eax
    32dc:	4d 89 c6             	mov    %r8,%r14
    32df:	bf 01 00 00 00       	mov    $0x1,%edi
    32e4:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    32e9:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    32f3:	4c 89 3c 24          	mov    %r15,(%rsp)
    32f7:	e8 54 f1 ff ff       	call   2450 <__printf_chk@plt>
    32fc:	bf 0a 00 00 00       	mov    $0xa,%edi
    3301:	e8 ca ef ff ff       	call   22d0 <putchar@plt>
    3306:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    330b:	bf 01 00 00 00       	mov    $0x1,%edi
    3310:	48 8d 35 89 33 00 00 	lea    0x3389(%rip),%rsi        # 66a0 <_IO_stdin_used+0x6a0>
    3317:	48 8b 50 08          	mov    0x8(%rax),%rdx
    331b:	31 c0                	xor    %eax,%eax
    331d:	e8 2e f1 ff ff       	call   2450 <__printf_chk@plt>
    3322:	4c 8b 0c 24          	mov    (%rsp),%r9
    3326:	bf 01 00 00 00       	mov    $0x1,%edi
    332b:	48 8d 35 96 33 00 00 	lea    0x3396(%rip),%rsi        # 66c8 <_IO_stdin_used+0x6c8>
    3332:	4c 89 c8             	mov    %r9,%rax
    3335:	49 c1 f9 3f          	sar    $0x3f,%r9
    3339:	48 f7 eb             	imul   %rbx
    333c:	31 c0                	xor    %eax,%eax
    333e:	48 d1 fa             	sar    %rdx
    3341:	4c 29 ca             	sub    %r9,%rdx
    3344:	e8 07 f1 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3349:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    334e:	bf 01 00 00 00       	mov    $0x1,%edi
    3353:	48 8d 35 9e 33 00 00 	lea    0x339e(%rip),%rsi        # 66f8 <_IO_stdin_used+0x6f8>
    335a:	4c 89 d8             	mov    %r11,%rax
    335d:	49 c1 fb 3f          	sar    $0x3f,%r11
    3361:	48 f7 eb             	imul   %rbx
    3364:	31 c0                	xor    %eax,%eax
    3366:	48 d1 fa             	sar    %rdx
    3369:	4c 29 da             	sub    %r11,%rdx
    336c:	e8 df f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3371:	4c 89 f0             	mov    %r14,%rax
    3374:	4c 89 f1             	mov    %r14,%rcx
    3377:	bf 01 00 00 00       	mov    $0x1,%edi
    337c:	48 f7 eb             	imul   %rbx
    337f:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3383:	48 8d 35 9e 33 00 00 	lea    0x339e(%rip),%rsi        # 6728 <_IO_stdin_used+0x728>
    338a:	31 c0                	xor    %eax,%eax
    338c:	48 d1 fa             	sar    %rdx
    338f:	48 29 ca             	sub    %rcx,%rdx
    3392:	e8 b9 f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3397:	4c 89 e0             	mov    %r12,%rax
    339a:	49 c1 fc 3f          	sar    $0x3f,%r12
    339e:	48 8d 35 3c 30 00 00 	lea    0x303c(%rip),%rsi        # 63e1 <_IO_stdin_used+0x3e1>
    33a5:	48 f7 eb             	imul   %rbx
    33a8:	bf 01 00 00 00       	mov    $0x1,%edi
    33ad:	31 c0                	xor    %eax,%eax
    33af:	48 d1 fa             	sar    %rdx
    33b2:	4c 29 e2             	sub    %r12,%rdx
    33b5:	e8 96 f0 ff ff       	call   2450 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    33ba:	48 89 e8             	mov    %rbp,%rax
    33bd:	48 c1 fd 3f          	sar    $0x3f,%rbp
    33c1:	48 8d 35 2a 30 00 00 	lea    0x302a(%rip),%rsi        # 63f2 <_IO_stdin_used+0x3f2>
    33c8:	48 f7 eb             	imul   %rbx
    33cb:	bf 01 00 00 00       	mov    $0x1,%edi
    33d0:	48 d1 fa             	sar    %rdx
    33d3:	48 29 ea             	sub    %rbp,%rdx
    33d6:	31 c0                	xor    %eax,%eax
    33d8:	e8 73 f0 ff ff       	call   2450 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    33dd:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    33e2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    33eb:	75 18                	jne    3405 <main+0xe15>
    33ed:	48 83 c4 78          	add    $0x78,%rsp
    33f1:	31 c0                	xor    %eax,%eax
    33f3:	5b                   	pop    %rbx
    33f4:	5d                   	pop    %rbp
    33f5:	41 5c                	pop    %r12
    33f7:	41 5d                	pop    %r13
    33f9:	41 5e                	pop    %r14
    33fb:	41 5f                	pop    %r15
    33fd:	c3                   	ret
    long v = 0;
    33fe:	31 d2                	xor    %edx,%edx
    3400:	e9 6d fc ff ff       	jmp    3072 <main+0xa82>
}
    3405:	e8 26 ef ff ff       	call   2330 <__stack_chk_fail@plt>
    340a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000003410 <_start>:
    3410:	f3 0f 1e fa          	endbr64
    3414:	31 ed                	xor    %ebp,%ebp
    3416:	49 89 d1             	mov    %rdx,%r9
    3419:	5e                   	pop    %rsi
    341a:	48 89 e2             	mov    %rsp,%rdx
    341d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3421:	50                   	push   %rax
    3422:	54                   	push   %rsp
    3423:	45 31 c0             	xor    %r8d,%r8d
    3426:	31 c9                	xor    %ecx,%ecx
    3428:	48 8d 3d c1 f1 ff ff 	lea    -0xe3f(%rip),%rdi        # 25f0 <main>
    342f:	ff 15 a3 5b 00 00    	call   *0x5ba3(%rip)        # 8fd8 <__libc_start_main@GLIBC_2.34>
    3435:	f4                   	hlt
    3436:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003440 <deregister_tm_clones>:
    3440:	48 8d 3d d9 5b 00 00 	lea    0x5bd9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3447:	48 8d 05 d2 5b 00 00 	lea    0x5bd2(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    344e:	48 39 f8             	cmp    %rdi,%rax
    3451:	74 15                	je     3468 <deregister_tm_clones+0x28>
    3453:	48 8b 05 86 5b 00 00 	mov    0x5b86(%rip),%rax        # 8fe0 <_ITM_deregisterTMCloneTable@Base>
    345a:	48 85 c0             	test   %rax,%rax
    345d:	74 09                	je     3468 <deregister_tm_clones+0x28>
    345f:	ff e0                	jmp    *%rax
    3461:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3468:	c3                   	ret
    3469:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003470 <register_tm_clones>:
    3470:	48 8d 3d a9 5b 00 00 	lea    0x5ba9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3477:	48 8d 35 a2 5b 00 00 	lea    0x5ba2(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    347e:	48 29 fe             	sub    %rdi,%rsi
    3481:	48 89 f0             	mov    %rsi,%rax
    3484:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3488:	48 c1 f8 03          	sar    $0x3,%rax
    348c:	48 01 c6             	add    %rax,%rsi
    348f:	48 d1 fe             	sar    %rsi
    3492:	74 14                	je     34a8 <register_tm_clones+0x38>
    3494:	48 8b 05 55 5b 00 00 	mov    0x5b55(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    349b:	48 85 c0             	test   %rax,%rax
    349e:	74 08                	je     34a8 <register_tm_clones+0x38>
    34a0:	ff e0                	jmp    *%rax
    34a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    34a8:	c3                   	ret
    34a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000034b0 <__do_global_dtors_aux>:
    34b0:	f3 0f 1e fa          	endbr64
    34b4:	80 3d 6d 5b 00 00 00 	cmpb   $0x0,0x5b6d(%rip)        # 9028 <completed.0>
    34bb:	75 2b                	jne    34e8 <__do_global_dtors_aux+0x38>
    34bd:	55                   	push   %rbp
    34be:	48 83 3d 32 5b 00 00 00 	cmpq   $0x0,0x5b32(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    34c6:	48 89 e5             	mov    %rsp,%rbp
    34c9:	74 0c                	je     34d7 <__do_global_dtors_aux+0x27>
    34cb:	48 8b 3d 36 5b 00 00 	mov    0x5b36(%rip),%rdi        # 9008 <__dso_handle>
    34d2:	e8 d9 ed ff ff       	call   22b0 <__cxa_finalize@plt>
    34d7:	e8 64 ff ff ff       	call   3440 <deregister_tm_clones>
    34dc:	c6 05 45 5b 00 00 01 	movb   $0x1,0x5b45(%rip)        # 9028 <completed.0>
    34e3:	5d                   	pop    %rbp
    34e4:	c3                   	ret
    34e5:	0f 1f 00             	nopl   (%rax)
    34e8:	c3                   	ret
    34e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000034f0 <frame_dummy>:
    34f0:	f3 0f 1e fa          	endbr64
    34f4:	e9 77 ff ff ff       	jmp    3470 <register_tm_clones>
    34f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003500 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3500:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3504:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    350b:	48 8b 40 38          	mov    0x38(%rax),%rax
  data->v++; // thread local
    350f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3517:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    351b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    351f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3526:	48 85 c9             	test   %rcx,%rcx
    3529:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3530:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3534:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3538:	31 c0                	xor    %eax,%eax
    353a:	c3                   	ret
    353b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003540 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3540:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3544:	48 63 8f 3c 01 00 00 	movslq 0x13c(%rdi),%rcx
    354b:	85 c9                	test   %ecx,%ecx
    354d:	7e 4f                	jle    359e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    354f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    3556:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    355d:	48 c1 e1 09          	shl    $0x9,%rcx
    3561:	48 8b 50 10          	mov    0x10(%rax),%rdx
    3565:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    3569:	48 8b 70 28          	mov    0x28(%rax),%rsi
    356d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    356f:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    3573:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3578:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    3580:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3588:	c7 84 06 38 01 00 00 01 00 00 00 	movl   $0x1,0x138(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    3593:	48 05 00 02 00 00    	add    $0x200,%rax
    3599:	48 39 c1             	cmp    %rax,%rcx
    359c:	75 da                	jne    3578 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    359e:	0f ae f8             	sfence
}
    35a1:	31 c0                	xor    %eax,%eax
    35a3:	c3                   	ret
    35a4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    35af:	90                   	nop

00000000000035b0 <barriered_thread>:
void* barriered_thread(void *arg) {
    35b0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    35b4:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
    35b8:	0f 85 90 02 00 00    	jne    384e <barriered_thread+0x29e>
void* barriered_thread(void *arg) {
    35be:	41 56                	push   %r14
    35c0:	41 55                	push   %r13
    35c2:	49 89 fd             	mov    %rdi,%r13
    35c5:	41 54                	push   %r12
    35c7:	55                   	push   %rbp
    35c8:	31 ed                	xor    %ebp,%ebp
    35ca:	53                   	push   %rbx
    35cb:	31 db                	xor    %ebx,%ebx
    35cd:	0f 1f 00             	nopl   (%rax)
    if (t >= data->task_count) {
    35d0:	41 8b 55 30          	mov    0x30(%r13),%edx
    35d4:	39 da                	cmp    %ebx,%edx
    35d6:	7f 12                	jg     35ea <barriered_thread+0x3a>
      data->cycles++;
    35d8:	49 83 85 98 00 00 00 01 	addq   $0x1,0x98(%r13)
    for (; t < data->task_count; t++) {
    35e0:	31 db                	xor    %ebx,%ebx
    35e2:	85 d2                	test   %edx,%edx
    35e4:	0f 8e 56 01 00 00    	jle    3740 <barriered_thread+0x190>
    35ea:	4c 63 e3             	movslq %ebx,%r12
    35ed:	49 c1 e4 09          	shl    $0x9,%r12
    35f1:	eb 17                	jmp    360a <barriered_thread+0x5a>
    35f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    35f8:	83 c3 01             	add    $0x1,%ebx
    35fb:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    3602:	39 d3                	cmp    %edx,%ebx
    3604:	0f 8d 36 01 00 00    	jge    3740 <barriered_thread+0x190>
      if (data->tasks[t].available == 1) {
    360a:	49 8b 45 28          	mov    0x28(%r13),%rax
    360e:	4a 8d 34 20          	lea    (%rax,%r12,1),%rsi
    3612:	83 be 38 01 00 00 01 	cmpl   $0x1,0x138(%rsi)
    3619:	75 dd                	jne    35f8 <barriered_thread+0x48>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    361b:	41 8b 7d 18          	mov    0x18(%r13),%edi
          previous = t - 1;
    361f:	83 ea 01             	sub    $0x1,%edx
    3622:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3625:	85 db                	test   %ebx,%ebx
    3627:	0f 4f d1             	cmovg  %ecx,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    362a:	85 ff                	test   %edi,%edi
    362c:	0f 8e 3e 01 00 00    	jle    3770 <barriered_thread+0x1c0>
    3632:	49 8b 45 10          	mov    0x10(%r13),%rax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3636:	48 63 ca             	movslq %edx,%rcx
    3639:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    363c:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    363f:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    3646:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    364d:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    3651:	45 31 f6             	xor    %r14d,%r14d
    3654:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3658:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    3660:	48 8b 10             	mov    (%rax),%rdx
    3663:	4c 8b 5a 28          	mov    0x28(%rdx),%r11
    3667:	49 01 cb             	add    %rcx,%r11
    366a:	4c 89 da             	mov    %r11,%rdx
    366d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    3674:	75 04                	jne    367a <barriered_thread+0xca>
            arrived++;
    3676:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    367a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    3681:	75 04                	jne    3687 <barriered_thread+0xd7>
            prearrive++;
    3683:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3687:	48 83 c0 08          	add    $0x8,%rax
    368b:	48 39 f0             	cmp    %rsi,%rax
    368e:	75 d0                	jne    3660 <barriered_thread+0xb0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    3690:	44 39 d7             	cmp    %r10d,%edi
    3693:	0f 84 c7 00 00 00    	je     3760 <barriered_thread+0x1b0>
    3699:	45 85 d2             	test   %r10d,%r10d
    369c:	0f 84 be 00 00 00    	je     3760 <barriered_thread+0x1b0>
        if (arrived == 0 || arrived == data->thread_count) {
    36a2:	45 85 f6             	test   %r14d,%r14d
    36a5:	74 0a                	je     36b1 <barriered_thread+0x101>
    36a7:	45 39 75 18          	cmp    %r14d,0x18(%r13)
    36ab:	0f 85 8f 00 00 00    	jne    3740 <barriered_thread+0x190>
    36b1:	49 8b 45 28          	mov    0x28(%r13),%rax
          data->tasks[t].prearrive++;
    36b5:	4c 01 e0             	add    %r12,%rax
    36b8:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    36bf:	85 db                	test   %ebx,%ebx
    36c1:	75 0e                	jne    36d1 <barriered_thread+0x121>
    36c3:	49 8b 75 70          	mov    0x70(%r13),%rsi
    36c7:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    36cb:	0f 8c 5f 01 00 00    	jl     3830 <barriered_thread+0x280>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    36d1:	49 63 4d 00          	movslq 0x0(%r13),%rcx
    36d5:	49 8b 55 10          	mov    0x10(%r13),%rdx
          data->tasks[t].available = 0;
    36d9:	c7 80 38 01 00 00 00 00 00 00 	movl   $0x0,0x138(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    36e3:	48 8b 14 ca          	mov    (%rdx,%rcx,8),%rdx
    36e7:	48 8b 7a 28          	mov    0x28(%rdx),%rdi
    36eb:	4c 01 e7             	add    %r12,%rdi
    36ee:	ff 90 18 01 00 00    	call   *0x118(%rax)
          data->tasks[t].arrived++;
    36f4:	49 8b 45 28          	mov    0x28(%r13),%rax
    36f8:	4c 01 e0             	add    %r12,%rax
    36fb:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3702:	41 8b 45 30          	mov    0x30(%r13),%eax
          data->iteration_count++;
    3706:	49 83 45 68 01       	addq   $0x1,0x68(%r13)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    370b:	83 e8 01             	sub    $0x1,%eax
    370e:	39 d8                	cmp    %ebx,%eax
    3710:	0f 84 b2 00 00 00    	je     37c8 <barriered_thread+0x218>
          asm volatile ("sfence" ::: "memory");
    3716:	0f ae f8             	sfence
          if (waiting == 0) {
    3719:	85 ed                	test   %ebp,%ebp
    371b:	0f 84 d7 00 00 00    	je     37f8 <barriered_thread+0x248>
    for (; t < data->task_count; t++) {
    3721:	41 8b 55 30          	mov    0x30(%r13),%edx
    3725:	83 c3 01             	add    $0x1,%ebx
    3728:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    372f:	39 d3                	cmp    %edx,%ebx
    3731:	0f 8c d3 fe ff ff    	jl     360a <barriered_thread+0x5a>
    3737:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  while (data->running == 1) {
    3740:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
    3745:	0f 84 85 fe ff ff    	je     35d0 <barriered_thread+0x20>
}
    374b:	5b                   	pop    %rbx
    374c:	31 c0                	xor    %eax,%eax
    374e:	5d                   	pop    %rbp
    374f:	41 5c                	pop    %r12
    3751:	41 5d                	pop    %r13
    3753:	41 5e                	pop    %r14
    3755:	c3                   	ret
    3756:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
    3760:	83 fd 01             	cmp    $0x1,%ebp
    3763:	74 1b                	je     3780 <barriered_thread+0x1d0>
        int arrived = 0; 
    3765:	31 ed                	xor    %ebp,%ebp
    3767:	e9 36 ff ff ff       	jmp    36a2 <barriered_thread+0xf2>
    376c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    3770:	83 fd 01             	cmp    $0x1,%ebp
    3773:	0f 85 3c ff ff ff    	jne    36b5 <barriered_thread+0x105>
        int arrived = 0; 
    3779:	45 31 f6             	xor    %r14d,%r14d
    377c:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3780:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    3787:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    378c:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    378e:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3792:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    3799:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    379e:	e8 6d eb ff ff       	call   2310 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    37a3:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
    37aa:	48 83 c0 01          	add    $0x1,%rax
    37ae:	48 99                	cqto
    37b0:	49 f7 bd 90 00 00 00 	idivq  0x90(%r13)
    37b7:	49 89 95 88 00 00 00 	mov    %rdx,0x88(%r13)
            waiting = 0; 
    37be:	e9 df fe ff ff       	jmp    36a2 <barriered_thread+0xf2>
    37c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    37c8:	49 8b 75 70          	mov    0x70(%r13),%rsi
    37cc:	49 3b 75 78          	cmp    0x78(%r13),%rsi
    37d0:	0f 8d 40 ff ff ff    	jge    3716 <barriered_thread+0x166>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    37d6:	48 c1 e6 04          	shl    $0x4,%rsi
    37da:	bf 04 00 00 00       	mov    $0x4,%edi
    37df:	49 03 75 60          	add    0x60(%r13),%rsi
    37e3:	e8 28 eb ff ff       	call   2310 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    37e8:	49 83 45 70 01       	addq   $0x1,0x70(%r13)
    37ed:	e9 24 ff ff ff       	jmp    3716 <barriered_thread+0x166>
    37f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    37f8:	49 8b 85 88 00 00 00 	mov    0x88(%r13),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    37ff:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3804:	bd 01 00 00 00       	mov    $0x1,%ebp
            data->task_snapshot[data->task_timestamp_count].task = t;
    3809:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    380d:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    3814:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3818:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    381b:	e8 f0 ea ff ff       	call   2310 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3820:	41 8b 55 30          	mov    0x30(%r13),%edx
    3824:	e9 cf fd ff ff       	jmp    35f8 <barriered_thread+0x48>
    3829:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3830:	48 c1 e6 04          	shl    $0x4,%rsi
    3834:	bf 04 00 00 00       	mov    $0x4,%edi
    3839:	49 03 75 58          	add    0x58(%r13),%rsi
    383d:	e8 ce ea ff ff       	call   2310 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3842:	49 8b 45 28          	mov    0x28(%r13),%rax
    3846:	4c 01 e0             	add    %r12,%rax
    3849:	e9 83 fe ff ff       	jmp    36d1 <barriered_thread+0x121>
}
    384e:	31 c0                	xor    %eax,%eax
    3850:	c3                   	ret
    3851:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    385c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003860 <external_thread>:
void * external_thread(void *arg) {
    3860:	f3 0f 1e fa          	endbr64
    3864:	41 55                	push   %r13
    3866:	41 54                	push   %r12
    3868:	55                   	push   %rbp
    3869:	53                   	push   %rbx
    386a:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    386e:	66 0f 6f 05 ca 30 00 00 	movdqa 0x30ca(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
void * external_thread(void *arg) {
    3876:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    387f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3884:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3886:	83 7f 34 01          	cmpl   $0x1,0x34(%rdi)
  struct timespec req = {
    388a:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    388e:	75 64                	jne    38f4 <external_thread+0x94>
    3890:	49 89 fd             	mov    %rdi,%r13
    3893:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3898:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    389b:	4c 8d 25 62 27 00 00 	lea    0x2762(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    38a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    nanosleep(&req , &rem);
    38a8:	48 89 ee             	mov    %rbp,%rsi
    38ab:	48 89 df             	mov    %rbx,%rdi
    38ae:	e8 9d ea ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    38b3:	49 8b 45 40          	mov    0x40(%r13),%rax
    38b7:	48 63 10             	movslq (%rax),%rdx
    38ba:	85 d2                	test   %edx,%edx
    38bc:	7e 2c                	jle    38ea <external_thread+0x8a>
    38be:	48 8b 40 08          	mov    0x8(%rax),%rax
    38c2:	48 c1 e2 04          	shl    $0x4,%rdx
    38c6:	48 01 c2             	add    %rax,%rdx
    38c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    38d0:	8b 48 08             	mov    0x8(%rax),%ecx
    38d3:	85 c9                	test   %ecx,%ecx
    38d5:	75 0a                	jne    38e1 <external_thread+0x81>
        data->buffers->buffer[x].data = "Hello world";
    38d7:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    38da:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    38e1:	48 83 c0 10          	add    $0x10,%rax
    38e5:	48 39 c2             	cmp    %rax,%rdx
    38e8:	75 e6                	jne    38d0 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    38ea:	0f ae f0             	mfence
  while (data->running == 1) {
    38ed:	41 83 7d 34 01       	cmpl   $0x1,0x34(%r13)
    38f2:	74 b4                	je     38a8 <external_thread+0x48>
}
    38f4:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    38f9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3902:	75 0d                	jne    3911 <external_thread+0xb1>
    3904:	48 83 c4 38          	add    $0x38,%rsp
    3908:	31 c0                	xor    %eax,%eax
    390a:	5b                   	pop    %rbx
    390b:	5d                   	pop    %rbp
    390c:	41 5c                	pop    %r12
    390e:	41 5d                	pop    %r13
    3910:	c3                   	ret
    3911:	e8 1a ea ff ff       	call   2330 <__stack_chk_fail@plt>
    3916:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003920 <timer_thread>:
void* timer_thread(void *arg) {
    3920:	f3 0f 1e fa          	endbr64
    3924:	41 57                	push   %r15
    3926:	48 8d 35 e3 26 00 00 	lea    0x26e3(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    392d:	49 89 ff             	mov    %rdi,%r15
    3930:	41 56                	push   %r14
    3932:	41 55                	push   %r13
    3934:	41 54                	push   %r12
    3936:	55                   	push   %rbp
    3937:	53                   	push   %rbx
    3938:	48 83 ec 58          	sub    $0x58,%rsp
    393c:	8b 17                	mov    (%rdi),%edx
    393e:	bf 01 00 00 00       	mov    $0x1,%edi
    3943:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    394c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3951:	31 c0                	xor    %eax,%eax
    3953:	e8 f8 ea ff ff       	call   2450 <__printf_chk@plt>
  struct timespec preempt = {
    3958:	66 0f 6f 05 e0 2f 00 00 	movdqa 0x2fe0(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3960:	ba 88 13 00 00       	mov    $0x1388,%edx
    3965:	31 c0                	xor    %eax,%eax
    3967:	48 8d 35 b4 26 00 00 	lea    0x26b4(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    396e:	bf 01 00 00 00       	mov    $0x1,%edi
    3973:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3978:	e8 d3 ea ff ff       	call   2450 <__printf_chk@plt>
  while (data->running && n < times) {
    397d:	45 8b 67 34          	mov    0x34(%r15),%r12d
    3981:	45 85 e4             	test   %r12d,%r12d
    3984:	0f 84 9b 00 00 00    	je     3a25 <timer_thread+0x105>
  int n = 0;
    398a:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    398d:	45 31 e4             	xor    %r12d,%r12d
    3990:	49 89 e5             	mov    %rsp,%r13
    y++;
    3993:	31 db                	xor    %ebx,%ebx
    3995:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    399a:	48 89 ef             	mov    %rbp,%rdi
    399d:	4c 89 ee             	mov    %r13,%rsi
    n++;
    39a0:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    39a4:	e8 a7 e9 ff ff       	call   2350 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    39a9:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    39ad:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    39b2:	85 c0                	test   %eax,%eax
    39b4:	7e 47                	jle    39fd <timer_thread+0xdd>
    39b6:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    39ba:	49 c1 e4 09          	shl    $0x9,%r12
    39be:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    39c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    39c8:	4c 8b 11             	mov    (%rcx),%r10
    39cb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    39cd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    39d1:	99                   	cltd
    39d2:	41 f7 7a 30          	idivl  0x30(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    39d6:	49 8b 72 28          	mov    0x28(%r10),%rsi
    39da:	48 63 d2             	movslq %edx,%rdx
    39dd:	48 c1 e2 09          	shl    $0x9,%rdx
    39e1:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    39ec:	42 c7 84 26 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    39f8:	49 39 c8             	cmp    %rcx,%r8
    39fb:	75 cb                	jne    39c8 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    39fd:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3a00:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3a04:	41 8b 57 34          	mov    0x34(%r15),%edx
    if (y >= data->threads[0]->task_count) {
    3a08:	48 8b 00             	mov    (%rax),%rax
    y++;
    3a0b:	39 78 30             	cmp    %edi,0x30(%rax)
    3a0e:	0f 4e fb             	cmovle %ebx,%edi
    3a11:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3a14:	85 d2                	test   %edx,%edx
    3a16:	74 0d                	je     3a25 <timer_thread+0x105>
    3a18:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    3a1f:	0f 85 75 ff ff ff    	jne    399a <timer_thread+0x7a>
    3a25:	48 8d 3d 0c 26 00 00 	lea    0x260c(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    3a2c:	e8 bf e8 ff ff       	call   22f0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3a31:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3a35:	85 d2                	test   %edx,%edx
    3a37:	7e 6b                	jle    3aa4 <timer_thread+0x184>
    for (int y = 0 ; y < data->task_count ; y++) {
    3a39:	49 63 47 30          	movslq 0x30(%r15),%rax
    3a3d:	85 c0                	test   %eax,%eax
    3a3f:	7e 63                	jle    3aa4 <timer_thread+0x184>
    3a41:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    3a45:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3a49:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    3a51:	31 ff                	xor    %edi,%edi
    3a53:	48 89 c2             	mov    %rax,%rdx
    3a56:	49 8b 04 38          	mov    (%r8,%rdi,1),%rax
    3a5a:	48 8b 40 28          	mov    0x28(%rax),%rax
    3a5e:	48 8d 34 02          	lea    (%rdx,%rax,1),%rsi
    3a62:	f6 c6 02             	test   $0x2,%dh
    3a65:	74 15                	je     3a7c <timer_thread+0x15c>
    3a67:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3a71:	48 05 00 02 00 00    	add    $0x200,%rax
    3a77:	48 39 c6             	cmp    %rax,%rsi
    3a7a:	74 1f                	je     3a9b <timer_thread+0x17b>
      data->threads[x]->tasks[y].sending = 0;
    3a7c:	c7 80 78 01 00 00 00 00 00 00 	movl   $0x0,0x178(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3a86:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    3a8c:	c7 80 78 ff ff ff 00 00 00 00 	movl   $0x0,-0x88(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3a96:	48 39 c6             	cmp    %rax,%rsi
    3a99:	75 e1                	jne    3a7c <timer_thread+0x15c>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3a9b:	48 83 c7 08          	add    $0x8,%rdi
    3a9f:	48 39 f9             	cmp    %rdi,%rcx
    3aa2:	75 b2                	jne    3a56 <timer_thread+0x136>
  asm volatile ("mfence" ::: "memory");
    3aa4:	0f ae f0             	mfence
  struct timespec drain = {
    3aa7:	66 0f 6f 05 a1 2e 00 00 	movdqa 0x2ea1(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    3aaf:	48 8d 2d a7 25 00 00 	lea    0x25a7(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    3ab6:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3abb:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    3abf:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ac4:	85 c0                	test   %eax,%eax
    3ac6:	7e 4c                	jle    3b14 <timer_thread+0x1f4>
    3ac8:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    3acc:	4d 63 c4             	movslq %r12d,%r8
    3acf:	49 c1 e0 09          	shl    $0x9,%r8
    3ad3:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3ad7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    3ae0:	48 8b 19             	mov    (%rcx),%rbx
    3ae3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ae5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    3ae9:	99                   	cltd
    3aea:	f7 7b 30             	idivl  0x30(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    3aed:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    3af1:	48 63 d2             	movslq %edx,%rdx
    3af4:	48 c1 e2 09          	shl    $0x9,%rdx
    3af8:	c7 84 16 40 01 00 00 01 00 00 00 	movl   $0x1,0x140(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    3b03:	42 c7 84 06 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b0f:	4c 39 c9             	cmp    %r9,%rcx
    3b12:	75 cc                	jne    3ae0 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    3b14:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    3b17:	49 8b 47 10          	mov    0x10(%r15),%rax
    y++;
    3b1b:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    3b1e:	48 8b 10             	mov    (%rax),%rdx
    y++;
    3b21:	39 7a 30             	cmp    %edi,0x30(%rdx)
    3b24:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3b28:	41 8b 7f 20          	mov    0x20(%r15),%edi
    3b2c:	85 ff                	test   %edi,%edi
    3b2e:	0f 8e bc 00 00 00    	jle    3bf0 <timer_thread+0x2d0>
    3b34:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    3b37:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3b3d:	0f 1f 00             	nopl   (%rax)
    3b40:	4a 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbx
            all_empty = 0;
    3b48:	45 31 f6             	xor    %r14d,%r14d
    3b4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3b50:	48 8b 14 18          	mov    (%rax,%rbx,1),%rdx
    3b54:	4c 89 f0             	mov    %r14,%rax
    3b57:	48 c1 e0 09          	shl    $0x9,%rax
    3b5b:	48 03 42 28          	add    0x28(%rdx),%rax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3b5f:	31 d2                	xor    %edx,%edx
    3b61:	48 8b 80 68 01 00 00 	mov    0x168(%rax),%rax
    3b68:	eb 16                	jmp    3b80 <timer_thread+0x260>
    3b6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3b70:	4d 85 c0             	test   %r8,%r8
    3b73:	7f 1f                	jg     3b94 <timer_thread+0x274>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    3b75:	83 c2 01             	add    $0x1,%edx
    3b78:	48 83 c0 20          	add    $0x20,%rax
    3b7c:	39 fa                	cmp    %edi,%edx
    3b7e:	74 2a                	je     3baa <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3b80:	48 8b 08             	mov    (%rax),%rcx
    3b83:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3b87:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3b8b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3b8f:	48 85 c9             	test   %rcx,%rcx
    3b92:	7e dc                	jle    3b70 <timer_thread+0x250>
    3b94:	bf 01 00 00 00       	mov    $0x1,%edi
    3b99:	48 89 ee             	mov    %rbp,%rsi
    3b9c:	31 c0                	xor    %eax,%eax
    3b9e:	e8 ad e8 ff ff       	call   2450 <__printf_chk@plt>
            break;
    3ba3:	41 8b 7f 20          	mov    0x20(%r15),%edi
            all_empty = 0;
    3ba7:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3baa:	49 83 c6 01          	add    $0x1,%r14
    3bae:	44 39 f7             	cmp    %r14d,%edi
    3bb1:	7e 0d                	jle    3bc0 <timer_thread+0x2a0>
    3bb3:	49 8b 47 10          	mov    0x10(%r15),%rax
    3bb7:	eb 97                	jmp    3b50 <timer_thread+0x230>
    3bb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    3bc0:	49 83 c5 01          	add    $0x1,%r13
    3bc4:	44 39 ef             	cmp    %r13d,%edi
    3bc7:	7e 0d                	jle    3bd6 <timer_thread+0x2b6>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    3bc9:	85 ff                	test   %edi,%edi
    3bcb:	7e 09                	jle    3bd6 <timer_thread+0x2b6>
    3bcd:	49 8b 47 10          	mov    0x10(%r15),%rax
    3bd1:	e9 6a ff ff ff       	jmp    3b40 <timer_thread+0x220>
    if (all_empty == 1) {
    3bd6:	41 83 f9 01          	cmp    $0x1,%r9d
    3bda:	74 14                	je     3bf0 <timer_thread+0x2d0>
      nanosleep(&drain , &drainrem);
    3bdc:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3be1:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3be6:	e8 65 e7 ff ff       	call   2350 <nanosleep@plt>
    3beb:	e9 cb fe ff ff       	jmp    3abb <timer_thread+0x19b>
    3bf0:	48 8d 3d 5d 24 00 00 	lea    0x245d(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3bf7:	e8 f4 e6 ff ff       	call   22f0 <puts@plt>
  while (data->running) {
    3bfc:	41 8b 47 34          	mov    0x34(%r15),%eax
    3c00:	85 c0                	test   %eax,%eax
    3c02:	0f 84 cf 00 00 00    	je     3cd7 <timer_thread+0x3b7>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c08:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3c0c:	85 c9                	test   %ecx,%ecx
    3c0e:	7e 2d                	jle    3c3d <timer_thread+0x31d>
    3c10:	49 8b 47 10          	mov    0x10(%r15),%rax
    3c14:	31 db                	xor    %ebx,%ebx
    3c16:	48 8d 2d 51 24 00 00 	lea    0x2451(%rip),%rbp        # 606e <_IO_stdin_used+0x6e>
    3c1d:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->running = 0;
    3c20:	48 8b 14 d8          	mov    (%rax,%rbx,8),%rdx
      if (data->threads[x]->type == IO) {
    3c24:	83 7a 08 02          	cmpl   $0x2,0x8(%rdx)
      data->threads[x]->running = 0;
    3c28:	c7 42 34 00 00 00 00 	movl   $0x0,0x34(%rdx)
      if (data->threads[x]->type == IO) {
    3c2f:	0f 84 cf 00 00 00    	je     3d04 <timer_thread+0x3e4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c35:	48 83 c3 01          	add    $0x1,%rbx
    3c39:	39 d9                	cmp    %ebx,%ecx
    3c3b:	7f e3                	jg     3c20 <timer_thread+0x300>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3c3d:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3c41:	85 d2                	test   %edx,%edx
    3c43:	7e 7b                	jle    3cc0 <timer_thread+0x3a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    3c45:	49 63 47 30          	movslq 0x30(%r15),%rax
    3c49:	85 c0                	test   %eax,%eax
    3c4b:	7e 73                	jle    3cc0 <timer_thread+0x3a0>
    3c4d:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3c51:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3c55:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    3c5d:	31 c9                	xor    %ecx,%ecx
    3c5f:	48 89 c6             	mov    %rax,%rsi
    3c62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c68:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    3c6c:	48 8b 40 28          	mov    0x28(%rax),%rax
    3c70:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3c74:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3c7a:	74 1c                	je     3c98 <timer_thread+0x378>
    3c7c:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3c86:	48 05 00 02 00 00    	add    $0x200,%rax
    3c8c:	48 39 d0             	cmp    %rdx,%rax
    3c8f:	74 26                	je     3cb7 <timer_thread+0x397>
    3c91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    3c98:	c7 80 40 01 00 00 00 00 00 00 	movl   $0x0,0x140(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3ca2:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    3ca8:	c7 80 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3cb2:	48 39 d0             	cmp    %rdx,%rax
    3cb5:	75 e1                	jne    3c98 <timer_thread+0x378>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3cb7:	48 83 c1 08          	add    $0x8,%rcx
    3cbb:	48 39 f9             	cmp    %rdi,%rcx
    3cbe:	75 a8                	jne    3c68 <timer_thread+0x348>
    asm volatile ("mfence" ::: "memory");
    3cc0:	0f ae f0             	mfence
    3cc3:	48 8d 3d b6 23 00 00 	lea    0x23b6(%rip),%rdi        # 6080 <_IO_stdin_used+0x80>
    3cca:	e8 21 e6 ff ff       	call   22f0 <puts@plt>
    data->running = 0;
    3ccf:	41 c7 47 34 00 00 00 00 	movl   $0x0,0x34(%r15)
    3cd7:	48 8d 3d a9 23 00 00 	lea    0x23a9(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3cde:	e8 0d e6 ff ff       	call   22f0 <puts@plt>
}
    3ce3:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3ce8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3cf1:	75 47                	jne    3d3a <timer_thread+0x41a>
    3cf3:	48 83 c4 58          	add    $0x58,%rsp
    3cf7:	31 c0                	xor    %eax,%eax
    3cf9:	5b                   	pop    %rbx
    3cfa:	5d                   	pop    %rbp
    3cfb:	41 5c                	pop    %r12
    3cfd:	41 5d                	pop    %r13
    3cff:	41 5e                	pop    %r14
    3d01:	41 5f                	pop    %r15
    3d03:	c3                   	ret
    3d04:	48 89 ef             	mov    %rbp,%rdi
    3d07:	e8 e4 e5 ff ff       	call   22f0 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    3d0c:	49 8b 47 10          	mov    0x10(%r15),%rax
    3d10:	be 01 00 00 00       	mov    $0x1,%esi
    3d15:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d19:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    3d1d:	8b 78 50             	mov    0x50(%rax),%edi
    3d20:	e8 db e6 ff ff       	call   2400 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3d25:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3d29:	39 d9                	cmp    %ebx,%ecx
    3d2b:	0f 8e 0c ff ff ff    	jle    3c3d <timer_thread+0x31d>
    3d31:	49 8b 47 10          	mov    0x10(%r15),%rax
    3d35:	e9 e6 fe ff ff       	jmp    3c20 <timer_thread+0x300>
}
    3d3a:	e8 f1 e5 ff ff       	call   2330 <__stack_chk_fail@plt>
    3d3f:	90                   	nop

0000000000003d40 <strtolower>:
void strtolower(char *str) {
    3d40:	f3 0f 1e fa          	endbr64
    3d44:	55                   	push   %rbp
    3d45:	53                   	push   %rbx
    3d46:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3d4a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3d4e:	84 db                	test   %bl,%bl
    3d50:	74 24                	je     3d76 <strtolower+0x36>
    3d52:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3d55:	e8 b6 e7 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3d5a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3d60:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3d63:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3d67:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3d6a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3d6d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3d72:	84 db                	test   %bl,%bl
    3d74:	75 ea                	jne    3d60 <strtolower+0x20>
}
    3d76:	48 83 c4 08          	add    $0x8,%rsp
    3d7a:	5b                   	pop    %rbx
    3d7b:	5d                   	pop    %rbp
    3d7c:	c3                   	ret
    3d7d:	0f 1f 00             	nopl   (%rax)

0000000000003d80 <zh_malloc>:
void *zh_malloc(size_t size) {
    3d80:	f3 0f 1e fa          	endbr64
    3d84:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3d88:	e8 83 e6 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3d8d:	48 85 c0             	test   %rax,%rax
    3d90:	74 05                	je     3d97 <zh_malloc+0x17>
}
    3d92:	48 83 c4 08          	add    $0x8,%rsp
    3d96:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3d97:	48 8b 0d 82 52 00 00 	mov    0x5282(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3d9e:	ba 28 00 00 00       	mov    $0x28,%edx
    3da3:	be 01 00 00 00       	mov    $0x1,%esi
    3da8:	48 8d 3d 59 26 00 00 	lea    0x2659(%rip),%rdi        # 6408 <_IO_stdin_used+0x408>
    3daf:	e8 0c e7 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    3db4:	bf 01 00 00 00       	mov    $0x1,%edi
    3db9:	e8 e2 e6 ff ff       	call   24a0 <exit@plt>
    3dbe:	66 90                	xchg   %ax,%ax

0000000000003dc0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3dc0:	f3 0f 1e fa          	endbr64
    3dc4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    3dc5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3dca:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3dcd:	e8 8e e5 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3dd2:	48 85 c0             	test   %rax,%rax
    3dd5:	74 11                	je     3de8 <get_filename_ext+0x28>
    3dd7:	48 39 c3             	cmp    %rax,%rbx
    3dda:	74 0c                	je     3de8 <get_filename_ext+0x28>
    return dot + 1;
    3ddc:	48 83 c0 01          	add    $0x1,%rax
}
    3de0:	5b                   	pop    %rbx
    3de1:	c3                   	ret
    3de2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    3de8:	48 8d 05 e0 22 00 00 	lea    0x22e0(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
}
    3def:	5b                   	pop    %rbx
    3df0:	c3                   	ret
    3df1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3dfc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003e00 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3e00:	f3 0f 1e fa          	endbr64
    3e04:	41 55                	push   %r13
    3e06:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3e09:	48 89 fe             	mov    %rdi,%rsi
    3e0c:	41 54                	push   %r12
    3e0e:	55                   	push   %rbp
    3e0f:	48 89 d5             	mov    %rdx,%rbp
    3e12:	ba 00 04 00 00       	mov    $0x400,%edx
    3e17:	53                   	push   %rbx
    3e18:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3e1f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3e28:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3e30:	31 c0                	xor    %eax,%eax
    3e32:	49 89 e4             	mov    %rsp,%r12
    3e35:	4c 89 e7             	mov    %r12,%rdi
    3e38:	e8 f3 e5 ff ff       	call   2430 <__strcpy_chk@plt>
    for (; *str; ++str)
    3e3d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3e42:	84 db                	test   %bl,%bl
    3e44:	74 24                	je     3e6a <send_headers+0x6a>
        *str = (char)tolower(*str);
    3e46:	e8 c5 e6 ff ff       	call   2510 <__ctype_tolower_loc@plt>
    3e4b:	48 8b 08             	mov    (%rax),%rcx
    3e4e:	4c 89 e0             	mov    %r12,%rax
    3e51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3e58:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3e5b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3e5f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3e62:	48 0f be 18          	movsbq (%rax),%rbx
    3e66:	84 db                	test   %bl,%bl
    3e68:	75 ee                	jne    3e58 <send_headers+0x58>
    void *buf = malloc(size);
    3e6a:	bf 11 00 00 00       	mov    $0x11,%edi
    3e6f:	e8 9c e5 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3e74:	48 85 c0             	test   %rax,%rax
    3e77:	0f 84 7e 04 00 00    	je     42fb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3e7d:	66 0f 6f 05 db 2a 00 00 	movdqa 0x2adb(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    iov[0].iov_base = zh_malloc(slen);
    3e85:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    3e89:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3e8e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3e96:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3e9a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3e9d:	e8 6e e5 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    3ea2:	48 85 c0             	test   %rax,%rax
    3ea5:	0f 84 50 04 00 00    	je     42fb <send_headers+0x4fb>
    3eab:	66 0f 6f 05 bd 2a 00 00 	movdqa 0x2abd(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    iov[1].iov_base = zh_malloc(slen);
    3eb3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    3eb7:	4c 89 e7             	mov    %r12,%rdi
    3eba:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3ec4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3ecc:	0f 11 00             	movups %xmm0,(%rax)
    3ecf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3ed3:	be 2e 00 00 00       	mov    $0x2e,%esi
    3ed8:	e8 83 e4 ff ff       	call   2360 <strrchr@plt>
    if (!dot || dot == filename)
    3edd:	48 85 c0             	test   %rax,%rax
    3ee0:	0f 84 ea 02 00 00    	je     41d0 <send_headers+0x3d0>
    3ee6:	4c 39 e0             	cmp    %r12,%rax
    3ee9:	0f 84 e1 02 00 00    	je     41d0 <send_headers+0x3d0>
    return dot + 1;
    3eef:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3ef3:	48 8d 3d a3 21 00 00 	lea    0x21a3(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3efa:	48 89 de             	mov    %rbx,%rsi
    3efd:	e8 ae e4 ff ff       	call   23b0 <strcmp@plt>
    3f02:	85 c0                	test   %eax,%eax
    3f04:	75 20                	jne    3f26 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3f06:	66 0f 6f 05 72 2a 00 00 	movdqa 0x2a72(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    3f0e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3f16:	66 0f 6f 05 72 2a 00 00 	movdqa 0x2a72(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    3f1e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    3f26:	48 89 de             	mov    %rbx,%rsi
    3f29:	48 8d 3d 71 21 00 00 	lea    0x2171(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3f30:	e8 7b e4 ff ff       	call   23b0 <strcmp@plt>
    3f35:	85 c0                	test   %eax,%eax
    3f37:	75 20                	jne    3f59 <send_headers+0x159>
    3f39:	66 0f 6f 05 3f 2a 00 00 	movdqa 0x2a3f(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    3f41:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3f49:	66 0f 6f 05 3f 2a 00 00 	movdqa 0x2a3f(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    3f51:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    3f59:	48 89 de             	mov    %rbx,%rsi
    3f5c:	48 8d 3d 43 21 00 00 	lea    0x2143(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3f63:	e8 48 e4 ff ff       	call   23b0 <strcmp@plt>
    3f68:	85 c0                	test   %eax,%eax
    3f6a:	0f 84 10 02 00 00    	je     4180 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    3f70:	48 89 de             	mov    %rbx,%rsi
    3f73:	48 8d 3d 30 21 00 00 	lea    0x2130(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3f7a:	e8 31 e4 ff ff       	call   23b0 <strcmp@plt>
    3f7f:	85 c0                	test   %eax,%eax
    3f81:	0f 84 a9 02 00 00    	je     4230 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    3f87:	48 89 de             	mov    %rbx,%rsi
    3f8a:	48 8d 3d 1d 21 00 00 	lea    0x211d(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3f91:	e8 1a e4 ff ff       	call   23b0 <strcmp@plt>
    3f96:	85 c0                	test   %eax,%eax
    3f98:	0f 84 6a 02 00 00    	je     4208 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    3f9e:	48 89 de             	mov    %rbx,%rsi
    3fa1:	48 8d 3d 49 21 00 00 	lea    0x2149(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3fa8:	e8 03 e4 ff ff       	call   23b0 <strcmp@plt>
    3fad:	85 c0                	test   %eax,%eax
    3faf:	0f 84 2b 02 00 00    	je     41e0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    3fb5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3fb8:	0f 84 52 01 00 00    	je     4110 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    3fbe:	48 89 de             	mov    %rbx,%rsi
    3fc1:	48 8d 3d ea 20 00 00 	lea    0x20ea(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3fc8:	e8 e3 e3 ff ff       	call   23b0 <strcmp@plt>
    3fcd:	85 c0                	test   %eax,%eax
    3fcf:	0f 84 ab 02 00 00    	je     4280 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    3fd5:	48 89 de             	mov    %rbx,%rsi
    3fd8:	48 8d 3d d7 20 00 00 	lea    0x20d7(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3fdf:	e8 cc e3 ff ff       	call   23b0 <strcmp@plt>
    3fe4:	85 c0                	test   %eax,%eax
    3fe6:	0f 84 6c 02 00 00    	je     4258 <send_headers+0x458>
    slen = strlen(send_buffer);
    3fec:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3ff4:	4c 89 e7             	mov    %r12,%rdi
    3ff7:	e8 24 e3 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    3ffc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3fff:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4002:	e8 09 e4 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4007:	48 85 c0             	test   %rax,%rax
    400a:	0f 84 eb 02 00 00    	je     42fb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4010:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4014:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4018:	83 fb 08             	cmp    $0x8,%ebx
    401b:	0f 83 3f 01 00 00    	jae    4160 <send_headers+0x360>
    4021:	f6 c3 04             	test   $0x4,%bl
    4024:	0f 85 7b 02 00 00    	jne    42a5 <send_headers+0x4a5>
    402a:	85 db                	test   %ebx,%ebx
    402c:	74 13                	je     4041 <send_headers+0x241>
    402e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4036:	88 10                	mov    %dl,(%rax)
    4038:	f6 c3 02             	test   $0x2,%bl
    403b:	0f 85 96 02 00 00    	jne    42d7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4041:	4d 89 e8             	mov    %r13,%r8
    4044:	48 8d 0d 6f 20 00 00 	lea    0x206f(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    404b:	4c 89 e7             	mov    %r12,%rdi
    404e:	31 c0                	xor    %eax,%eax
    4050:	ba 00 04 00 00       	mov    $0x400,%edx
    4055:	be 01 00 00 00       	mov    $0x1,%esi
    405a:	e8 c1 e4 ff ff       	call   2520 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    405f:	4c 89 e7             	mov    %r12,%rdi
    4062:	e8 b9 e2 ff ff       	call   2320 <strlen@plt>
    void *buf = malloc(size);
    4067:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    406a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    406d:	e8 9e e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4072:	48 85 c0             	test   %rax,%rax
    4075:	0f 84 80 02 00 00    	je     42fb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    407b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    407f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4083:	83 fb 08             	cmp    $0x8,%ebx
    4086:	0f 83 1c 01 00 00    	jae    41a8 <send_headers+0x3a8>
    408c:	f6 c3 04             	test   $0x4,%bl
    408f:	0f 85 29 02 00 00    	jne    42be <send_headers+0x4be>
    4095:	85 db                	test   %ebx,%ebx
    4097:	74 13                	je     40ac <send_headers+0x2ac>
    4099:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    40a1:	88 10                	mov    %dl,(%rax)
    40a3:	f6 c3 02             	test   $0x2,%bl
    40a6:	0f 85 3d 02 00 00    	jne    42e9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40ac:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    40b1:	bf 02 00 00 00       	mov    $0x2,%edi
    40b6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    40be:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    40c6:	e8 45 e3 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    40cb:	48 85 c0             	test   %rax,%rax
    40ce:	0f 84 27 02 00 00    	je     42fb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    40d4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    40dc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    40e0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    40e8:	66 89 10             	mov    %dx,(%rax)
}
    40eb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    40f3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    40fc:	0f 85 20 02 00 00    	jne    4322 <send_headers+0x522>
    4102:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4109:	5b                   	pop    %rbx
    410a:	5d                   	pop    %rbp
    410b:	41 5c                	pop    %r12
    410d:	41 5d                	pop    %r13
    410f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4110:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4114:	0f 85 a4 fe ff ff    	jne    3fbe <send_headers+0x1be>
    411a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    411e:	0f 85 9a fe ff ff    	jne    3fbe <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4124:	66 0f 6f 05 b4 28 00 00 	movdqa 0x28b4(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
    412c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4136:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    413e:	66 0f 6f 05 aa 28 00 00 	movdqa 0x28aa(%rip),%xmm0        # 69f0 <_IO_stdin_used+0x9f0>
    4146:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    414e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4156:	e9 63 fe ff ff       	jmp    3fbe <send_headers+0x1be>
    415b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4160:	89 da                	mov    %ebx,%edx
    4162:	48 89 c7             	mov    %rax,%rdi
    4165:	4c 89 e6             	mov    %r12,%rsi
    4168:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    416d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4172:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4175:	c1 e9 03             	shr    $0x3,%ecx
    4178:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    417b:	e9 c1 fe ff ff       	jmp    4041 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4180:	66 0f 6f 05 f8 27 00 00 	movdqa 0x27f8(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4188:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4190:	66 0f 6f 05 08 28 00 00 	movdqa 0x2808(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    4198:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    41a0:	e9 cb fd ff ff       	jmp    3f70 <send_headers+0x170>
    41a5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    41a8:	89 da                	mov    %ebx,%edx
    41aa:	48 89 c7             	mov    %rax,%rdi
    41ad:	4c 89 e6             	mov    %r12,%rsi
    41b0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    41b5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    41ba:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    41bd:	c1 e9 03             	shr    $0x3,%ecx
    41c0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    41c3:	e9 e4 fe ff ff       	jmp    40ac <send_headers+0x2ac>
    41c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    41d0:	48 8d 1d f8 1e 00 00 	lea    0x1ef8(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    41d7:	e9 94 fd ff ff       	jmp    3f70 <send_headers+0x170>
    41dc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    41e0:	66 0f 6f 05 d8 27 00 00 	movdqa 0x27d8(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    41e8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41f0:	66 0f 6f 05 d8 27 00 00 	movdqa 0x27d8(%rip),%xmm0        # 69d0 <_IO_stdin_used+0x9d0>
    41f8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4200:	e9 b0 fd ff ff       	jmp    3fb5 <send_headers+0x1b5>
    4205:	0f 1f 00             	nopl   (%rax)
    4208:	66 0f 6f 05 b0 27 00 00 	movdqa 0x27b0(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4210:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4218:	66 0f 6f 05 b0 27 00 00 	movdqa 0x27b0(%rip),%xmm0        # 69d0 <_IO_stdin_used+0x9d0>
    4220:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4228:	e9 71 fd ff ff       	jmp    3f9e <send_headers+0x19e>
    422d:	0f 1f 00             	nopl   (%rax)
    4230:	66 0f 6f 05 48 27 00 00 	movdqa 0x2748(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4238:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4240:	66 0f 6f 05 68 27 00 00 	movdqa 0x2768(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    4248:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4250:	e9 32 fd ff ff       	jmp    3f87 <send_headers+0x187>
    4255:	0f 1f 00             	nopl   (%rax)
    4258:	66 0f 6f 05 60 27 00 00 	movdqa 0x2760(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4260:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4268:	66 0f 6f 05 a0 27 00 00 	movdqa 0x27a0(%rip),%xmm0        # 6a10 <_IO_stdin_used+0xa10>
    4270:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4278:	e9 6f fd ff ff       	jmp    3fec <send_headers+0x1ec>
    427d:	0f 1f 00             	nopl   (%rax)
    4280:	66 0f 6f 05 38 27 00 00 	movdqa 0x2738(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4288:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4290:	66 0f 6f 05 68 27 00 00 	movdqa 0x2768(%rip),%xmm0        # 6a00 <_IO_stdin_used+0xa00>
    4298:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    42a0:	e9 30 fd ff ff       	jmp    3fd5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    42a5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    42ac:	89 db                	mov    %ebx,%ebx
    42ae:	89 10                	mov    %edx,(%rax)
    42b0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    42b5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    42b9:	e9 83 fd ff ff       	jmp    4041 <send_headers+0x241>
    42be:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    42c5:	89 db                	mov    %ebx,%ebx
    42c7:	89 10                	mov    %edx,(%rax)
    42c9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    42ce:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    42d2:	e9 d5 fd ff ff       	jmp    40ac <send_headers+0x2ac>
    42d7:	89 db                	mov    %ebx,%ebx
    42d9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    42df:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    42e4:	e9 58 fd ff ff       	jmp    4041 <send_headers+0x241>
    42e9:	89 db                	mov    %ebx,%ebx
    42eb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    42f1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    42f6:	e9 b1 fd ff ff       	jmp    40ac <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    42fb:	48 8b 0d 1e 4d 00 00 	mov    0x4d1e(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4302:	ba 28 00 00 00       	mov    $0x28,%edx
    4307:	be 01 00 00 00       	mov    $0x1,%esi
    430c:	48 8d 3d f5 20 00 00 	lea    0x20f5(%rip),%rdi        # 6408 <_IO_stdin_used+0x408>
    4313:	e8 a8 e1 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4318:	bf 01 00 00 00       	mov    $0x1,%edi
    431d:	e8 7e e1 ff ff       	call   24a0 <exit@plt>
}
    4322:	e8 09 e0 ff ff       	call   2330 <__stack_chk_fail@plt>
    4327:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004330 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4330:	f3 0f 1e fa          	endbr64
    4334:	41 55                	push   %r13
    4336:	49 89 d5             	mov    %rdx,%r13
    4339:	41 54                	push   %r12
    433b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    433e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4341:	55                   	push   %rbp
    4342:	53                   	push   %rbx
    4343:	48 89 f3             	mov    %rsi,%rbx
    4346:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    434a:	e8 c1 e0 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    434f:	48 85 c0             	test   %rax,%rax
    4352:	74 6b                	je     43bf <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4354:	4c 89 e7             	mov    %r12,%rdi
    4357:	48 89 c5             	mov    %rax,%rbp
    435a:	31 f6                	xor    %esi,%esi
    435c:	31 c0                	xor    %eax,%eax
    435e:	e8 1d e1 ff ff       	call   2480 <open@plt>
    4363:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4366:	85 c0                	test   %eax,%eax
    4368:	0f 88 e8 e1 ff ff    	js     2556 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    436e:	48 89 da             	mov    %rbx,%rdx
    4371:	48 89 ee             	mov    %rbp,%rsi
    4374:	89 c7                	mov    %eax,%edi
    4376:	e8 15 e0 ff ff       	call   2390 <read@plt>
    if (ret < file_size) {
    437b:	48 98                	cltq
    437d:	48 39 d8             	cmp    %rbx,%rax
    4380:	7c 1e                	jl     43a0 <copy_file_contents+0x70>
    close(fd);
    4382:	44 89 e7             	mov    %r12d,%edi
    4385:	e8 e6 df ff ff       	call   2370 <close@plt>
    iov->iov_base = buf;
    438a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    438e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4392:	48 83 c4 08          	add    $0x8,%rsp
    4396:	5b                   	pop    %rbx
    4397:	5d                   	pop    %rbp
    4398:	41 5c                	pop    %r12
    439a:	41 5d                	pop    %r13
    439c:	c3                   	ret
    439d:	0f 1f 00             	nopl   (%rax)
    43a0:	48 8b 0d 79 4c 00 00 	mov    0x4c79(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    43a7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    43ac:	be 01 00 00 00       	mov    $0x1,%esi
    43b1:	48 8d 3d 18 1d 00 00 	lea    0x1d18(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    43b8:	e8 03 e1 ff ff       	call   24c0 <fwrite@plt>
    43bd:	eb c3                	jmp    4382 <copy_file_contents+0x52>
    43bf:	48 8b 0d 5a 4c 00 00 	mov    0x4c5a(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    43c6:	ba 28 00 00 00       	mov    $0x28,%edx
    43cb:	be 01 00 00 00       	mov    $0x1,%esi
    43d0:	48 8d 3d 31 20 00 00 	lea    0x2031(%rip),%rdi        # 6408 <_IO_stdin_used+0x408>
    43d7:	e8 e4 e0 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    43dc:	bf 01 00 00 00       	mov    $0x1,%edi
    43e1:	e8 ba e0 ff ff       	call   24a0 <exit@plt>
    43e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000043f0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    43f0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    43f4:	8b 46 44             	mov    0x44(%rsi),%eax
    43f7:	48 89 fa             	mov    %rdi,%rdx
    43fa:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    43fd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4403:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4406:	48 8b 07             	mov    (%rdi),%rax
    4409:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    440c:	f6 c1 02             	test   $0x2,%cl
    440f:	74 00                	je     4411 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4411:	89 f0                	mov    %esi,%eax
    4413:	44 29 c0             	sub    %r8d,%eax
    4416:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4419:	0f 82 43 e1 ff ff    	jb     2562 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    441f:	c1 e9 0a             	shr    $0xa,%ecx
    4422:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4426:	8b 47 44             	mov    0x44(%rdi),%eax
    4429:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    442c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    442f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4432:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4435:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4439:	d3 e0                	shl    %cl,%eax
    443b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    443e:	48 c1 e0 06          	shl    $0x6,%rax
    4442:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4446:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    444c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    444f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4453:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4459:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4461:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4465:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4468:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    446f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4477:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    447b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    447f:	e8 bc de ff ff       	call   2340 <io_uring_submit@plt>
}
    4484:	31 c0                	xor    %eax,%eax
    4486:	48 83 c4 08          	add    $0x8,%rsp
    448a:	c3                   	ret
    448b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004490 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4490:	f3 0f 1e fa          	endbr64
    4494:	41 55                	push   %r13
    4496:	41 89 fd             	mov    %edi,%r13d
    4499:	41 54                	push   %r12
    449b:	55                   	push   %rbp
    449c:	53                   	push   %rbx
    449d:	48 89 f3             	mov    %rsi,%rbx
    44a0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    44a4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    44a7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    44ad:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    44b0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    44b3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    44b5:	f6 c1 02             	test   $0x2,%cl
    44b8:	74 00                	je     44ba <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    44ba:	89 c2                	mov    %eax,%edx
    44bc:	29 f2                	sub    %esi,%edx
    44be:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    44c1:	0f 82 ab e0 ff ff    	jb     2572 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    44c7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    44ca:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    44cd:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    44d0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    44d5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    44d8:	23 6b 58             	and    0x58(%rbx),%ebp
    44db:	d3 e5                	shl    %cl,%ebp
    44dd:	48 c1 e5 06          	shl    $0x6,%rbp
    44e1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    44e5:	e8 26 df ff ff       	call   2410 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    44ea:	be 01 00 00 00       	mov    $0x1,%esi
    44ef:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    44f4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    44f7:	e8 a4 de ff ff       	call   23a0 <calloc@plt>
    req->client_socket = client_socket;
    44fc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4501:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4505:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4508:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    450d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4512:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    451b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4523:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4527:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    452b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4532:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    453a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    453e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4546:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    454e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4552:	e8 e9 dd ff ff       	call   2340 <io_uring_submit@plt>
}
    4557:	48 83 c4 08          	add    $0x8,%rsp
    455b:	31 c0                	xor    %eax,%eax
    455d:	5b                   	pop    %rbx
    455e:	5d                   	pop    %rbp
    455f:	41 5c                	pop    %r12
    4561:	41 5d                	pop    %r13
    4563:	c3                   	ret
    4564:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    456f:	90                   	nop

0000000000004570 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4570:	f3 0f 1e fa          	endbr64
    4574:	41 56                	push   %r14
    4576:	41 89 f6             	mov    %esi,%r14d
    4579:	41 55                	push   %r13
    457b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    457e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4583:	41 54                	push   %r12
    4585:	55                   	push   %rbp
    4586:	48 89 d5             	mov    %rdx,%rbp
    4589:	53                   	push   %rbx
    void *buf = malloc(size);
    458a:	e8 81 de ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    458f:	48 85 c0             	test   %rax,%rax
    4592:	0f 84 dd 00 00 00    	je     4675 <_send_static_string_content+0x105>
    4598:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    459b:	4c 89 ef             	mov    %r13,%rdi
    459e:	e8 7d dd ff ff       	call   2320 <strlen@plt>
    req->iovec_count = 1;
    45a3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    45aa:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    45ae:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    45b1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    45b4:	e8 57 de ff ff       	call   2410 <malloc@plt>
    45b9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    45bc:	48 85 c0             	test   %rax,%rax
    45bf:	0f 84 b0 00 00 00    	je     4675 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    45c5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    45c9:	4c 89 e2             	mov    %r12,%rdx
    45cc:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    45cf:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    45d3:	e8 08 de ff ff       	call   23e0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    45d8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    45db:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    45e1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    45e4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    45e8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    45ea:	f6 c1 02             	test   $0x2,%cl
    45ed:	0f 85 7d 00 00 00    	jne    4670 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    45f3:	89 d0                	mov    %edx,%eax
    45f5:	29 f0                	sub    %esi,%eax
    45f7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    45fa:	0f 82 7c df ff ff    	jb     257c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4600:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4603:	8b 45 44             	mov    0x44(%rbp),%eax
    4606:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4609:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    460c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    460f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4612:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4618:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    461c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    461e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4621:	48 89 ef             	mov    %rbp,%rdi
    4624:	48 c1 e0 06          	shl    $0x6,%rax
    4628:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    462c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    462f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4633:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4639:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4641:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4645:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4648:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    464f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4657:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    465b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    465f:	5b                   	pop    %rbx
    4660:	5d                   	pop    %rbp
    4661:	41 5c                	pop    %r12
    4663:	41 5d                	pop    %r13
    4665:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4667:	e9 d4 dc ff ff       	jmp    2340 <io_uring_submit@plt>
    466c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4670:	e9 7e ff ff ff       	jmp    45f3 <_send_static_string_content+0x83>
    4675:	48 8b 0d a4 49 00 00 	mov    0x49a4(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    467c:	ba 28 00 00 00       	mov    $0x28,%edx
    4681:	be 01 00 00 00       	mov    $0x1,%esi
    4686:	48 8d 3d 7b 1d 00 00 	lea    0x1d7b(%rip),%rdi        # 6408 <_IO_stdin_used+0x408>
    468d:	e8 2e de ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4692:	bf 01 00 00 00       	mov    $0x1,%edi
    4697:	e8 04 de ff ff       	call   24a0 <exit@plt>
    469c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000046a0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    46a0:	f3 0f 1e fa          	endbr64
    46a4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    46a7:	89 fe                	mov    %edi,%esi
    46a9:	48 8b 3d 68 49 00 00 	mov    0x4968(%rip),%rdi        # 9018 <unimplemented_content>
    46b0:	e9 bb fe ff ff       	jmp    4570 <_send_static_string_content>
    46b5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000046c0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    46c0:	f3 0f 1e fa          	endbr64
    46c4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    46c7:	89 fe                	mov    %edi,%esi
    46c9:	48 8b 3d 40 49 00 00 	mov    0x4940(%rip),%rdi        # 9010 <http_404_content>
    46d0:	e9 9b fe ff ff       	jmp    4570 <_send_static_string_content>
    46d5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000046e0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    46e0:	f3 0f 1e fa          	endbr64
    46e4:	41 56                	push   %r14
    46e6:	41 55                	push   %r13
    46e8:	49 89 d5             	mov    %rdx,%r13
    46eb:	41 54                	push   %r12
    46ed:	41 89 f4             	mov    %esi,%r12d
    46f0:	55                   	push   %rbp
    46f1:	48 89 fd             	mov    %rdi,%rbp
    46f4:	53                   	push   %rbx
    46f5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    46fc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4705:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    470d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    470f:	e8 0c dc ff ff       	call   2320 <strlen@plt>
    4714:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4719:	48 89 c3             	mov    %rax,%rbx
    471c:	0f 84 b6 00 00 00    	je     47d8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4722:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4727:	48 89 ee             	mov    %rbp,%rsi
    472a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    472e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4733:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    473b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4743:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    474e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4756:	e8 65 dc ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    475b:	48 89 e6             	mov    %rsp,%rsi
    475e:	4c 89 f7             	mov    %r14,%rdi
    4761:	e8 6a dc ff ff       	call   23d0 <stat@plt>
    4766:	83 f8 ff             	cmp    $0xffffffff,%eax
    4769:	0f 84 d3 00 00 00    	je     4842 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    476f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4773:	25 00 f0 00 00       	and    $0xf000,%eax
    4778:	3d 00 80 00 00       	cmp    $0x8000,%eax
    477d:	0f 84 f5 00 00 00    	je     4878 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4783:	48 8b 3d 86 48 00 00 	mov    0x4886(%rip),%rdi        # 9010 <http_404_content>
    478a:	4c 89 ea             	mov    %r13,%rdx
    478d:	44 89 e6             	mov    %r12d,%esi
    4790:	e8 db fd ff ff       	call   4570 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4795:	4c 89 f2             	mov    %r14,%rdx
    4798:	bf 01 00 00 00       	mov    $0x1,%edi
    479d:	31 c0                	xor    %eax,%eax
    479f:	48 8d 35 7a 19 00 00 	lea    0x197a(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    47a6:	e8 a5 dc ff ff       	call   2450 <__printf_chk@plt>
}
    47ab:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    47b3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    47bc:	0f 85 20 01 00 00    	jne    48e2 <handle_get_method+0x202>
    47c2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    47c9:	5b                   	pop    %rbx
    47ca:	5d                   	pop    %rbp
    47cb:	41 5c                	pop    %r12
    47cd:	41 5d                	pop    %r13
    47cf:	41 5e                	pop    %r14
    47d1:	c3                   	ret
    47d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    47d8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    47dd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    47e5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    47ea:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    47ed:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    47f5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    47f8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4800:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    480b:	e8 b0 db ff ff       	call   23c0 <__memcpy_chk@plt>
    4810:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4815:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    481a:	48 8d 35 ca 18 00 00 	lea    0x18ca(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    4821:	48 29 d9             	sub    %rbx,%rcx
    4824:	ba 0b 00 00 00       	mov    $0xb,%edx
    4829:	e8 92 db ff ff       	call   23c0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    482e:	48 89 e6             	mov    %rsp,%rsi
    4831:	4c 89 f7             	mov    %r14,%rdi
    4834:	e8 97 db ff ff       	call   23d0 <stat@plt>
    4839:	83 f8 ff             	cmp    $0xffffffff,%eax
    483c:	0f 85 2d ff ff ff    	jne    476f <handle_get_method+0x8f>
    4842:	4c 89 f2             	mov    %r14,%rdx
    4845:	48 89 e9             	mov    %rbp,%rcx
    4848:	48 8d 35 a7 18 00 00 	lea    0x18a7(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    484f:	31 c0                	xor    %eax,%eax
    4851:	bf 01 00 00 00       	mov    $0x1,%edi
    4856:	e8 f5 db ff ff       	call   2450 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    485b:	48 8b 3d ae 47 00 00 	mov    0x47ae(%rip),%rdi        # 9010 <http_404_content>
    4862:	4c 89 ea             	mov    %r13,%rdx
    4865:	44 89 e6             	mov    %r12d,%esi
    4868:	e8 03 fd ff ff       	call   4570 <_send_static_string_content>
}
    486d:	e9 39 ff ff ff       	jmp    47ab <handle_get_method+0xcb>
    4872:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4878:	bf 70 00 00 00       	mov    $0x70,%edi
    487d:	e8 8e db ff ff       	call   2410 <malloc@plt>
    4882:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4885:	48 85 c0             	test   %rax,%rax
    4888:	74 5d                	je     48e7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    488a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    488e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4893:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4897:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    489a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    48a1:	e8 5a f5 ff ff       	call   3e00 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    48a6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    48ab:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    48af:	4c 89 f7             	mov    %r14,%rdi
    48b2:	e8 79 fa ff ff       	call   4330 <copy_file_contents>
    48b7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    48bc:	4c 89 f2             	mov    %r14,%rdx
    48bf:	31 c0                	xor    %eax,%eax
    48c1:	48 8d 35 46 18 00 00 	lea    0x1846(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    48c8:	bf 01 00 00 00       	mov    $0x1,%edi
    48cd:	e8 7e db ff ff       	call   2450 <__printf_chk@plt>
            add_write_request(req, ring);
    48d2:	4c 89 ee             	mov    %r13,%rsi
    48d5:	48 89 df             	mov    %rbx,%rdi
    48d8:	e8 13 fb ff ff       	call   43f0 <add_write_request>
    48dd:	e9 c9 fe ff ff       	jmp    47ab <handle_get_method+0xcb>
}
    48e2:	e8 49 da ff ff       	call   2330 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    48e7:	48 8b 0d 32 47 00 00 	mov    0x4732(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    48ee:	ba 28 00 00 00       	mov    $0x28,%edx
    48f3:	be 01 00 00 00       	mov    $0x1,%esi
    48f8:	48 8d 3d 09 1b 00 00 	lea    0x1b09(%rip),%rdi        # 6408 <_IO_stdin_used+0x408>
    48ff:	e8 bc db ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4904:	bf 01 00 00 00       	mov    $0x1,%edi
    4909:	e8 92 db ff ff       	call   24a0 <exit@plt>
    490e:	66 90                	xchg   %ax,%ax

0000000000004910 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4910:	f3 0f 1e fa          	endbr64
    4914:	41 57                	push   %r15
    4916:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4918:	4c 8d 35 66 17 00 00 	lea    0x1766(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    491f:	41 55                	push   %r13
    4921:	49 89 d5             	mov    %rdx,%r13
    4924:	41 54                	push   %r12
    4926:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4929:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    492c:	55                   	push   %rbp
    492d:	53                   	push   %rbx
    492e:	48 83 ec 18          	sub    $0x18,%rsp
    4932:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    493b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4940:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4942:	49 89 e7             	mov    %rsp,%r15
    4945:	4c 89 fa             	mov    %r15,%rdx
    4948:	e8 33 da ff ff       	call   2380 <strtok_r@plt>
    for (; *str; ++str)
    494d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4951:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4954:	84 db                	test   %bl,%bl
    4956:	74 1d                	je     4975 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4958:	e8 b3 db ff ff       	call   2510 <__ctype_tolower_loc@plt>
    495d:	48 89 ea             	mov    %rbp,%rdx
    4960:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4963:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4967:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    496a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    496d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4971:	84 db                	test   %bl,%bl
    4973:	75 eb                	jne    4960 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4975:	4c 89 fa             	mov    %r15,%rdx
    4978:	4c 89 f6             	mov    %r14,%rsi
    497b:	31 ff                	xor    %edi,%edi
    497d:	e8 fe d9 ff ff       	call   2380 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4982:	48 8d 35 aa 17 00 00 	lea    0x17aa(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    4989:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    498c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    498f:	e8 1c da ff ff       	call   23b0 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4994:	4c 89 ea             	mov    %r13,%rdx
    4997:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    499a:	85 c0                	test   %eax,%eax
    499c:	75 2a                	jne    49c8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    499e:	48 89 df             	mov    %rbx,%rdi
    49a1:	e8 3a fd ff ff       	call   46e0 <handle_get_method>
}
    49a6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    49ab:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    49b4:	75 20                	jne    49d6 <handle_http_method+0xc6>
    49b6:	48 83 c4 18          	add    $0x18,%rsp
    49ba:	5b                   	pop    %rbx
    49bb:	5d                   	pop    %rbp
    49bc:	41 5c                	pop    %r12
    49be:	41 5d                	pop    %r13
    49c0:	41 5e                	pop    %r14
    49c2:	41 5f                	pop    %r15
    49c4:	c3                   	ret
    49c5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    49c8:	48 8b 3d 49 46 00 00 	mov    0x4649(%rip),%rdi        # 9018 <unimplemented_content>
    49cf:	e8 9c fb ff ff       	call   4570 <_send_static_string_content>
}
    49d4:	eb d0                	jmp    49a6 <handle_http_method+0x96>
    49d6:	e8 55 d9 ff ff       	call   2330 <__stack_chk_fail@plt>
    49db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000049e0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    49e0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    49e4:	85 d2                	test   %edx,%edx
    49e6:	7e 38                	jle    4a20 <get_line+0x40>
    49e8:	48 63 d2             	movslq %edx,%rdx
    49eb:	48 83 c7 01          	add    $0x1,%rdi
    49ef:	48 01 f2             	add    %rsi,%rdx
    49f2:	eb 11                	jmp    4a05 <get_line+0x25>
    49f4:	0f 1f 40 00          	nopl   0x0(%rax)
    49f8:	48 83 c6 01          	add    $0x1,%rsi
    49fc:	48 83 c7 01          	add    $0x1,%rdi
    4a00:	48 39 d6             	cmp    %rdx,%rsi
    4a03:	74 1b                	je     4a20 <get_line+0x40>
        dest[i] = src[i];
    4a05:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4a09:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4a0b:	3c 0d                	cmp    $0xd,%al
    4a0d:	75 e9                	jne    49f8 <get_line+0x18>
    4a0f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4a12:	75 e4                	jne    49f8 <get_line+0x18>
            dest[i] = '\0';
    4a14:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4a17:	31 c0                	xor    %eax,%eax
    4a19:	c3                   	ret
    4a1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4a20:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4a25:	c3                   	ret
    4a26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004a30 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4a30:	f3 0f 1e fa          	endbr64
    4a34:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    4a3b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    4a3f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a48:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4a50:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4a52:	49 89 e2             	mov    %rsp,%r10
    4a55:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    4a5d:	4c 89 d0             	mov    %r10,%rax
    4a60:	eb 13                	jmp    4a75 <handle_client_request+0x45>
    4a62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4a68:	48 83 c0 01          	add    $0x1,%rax
    4a6c:	48 83 c1 01          	add    $0x1,%rcx
    4a70:	4c 39 c8             	cmp    %r9,%rax
    4a73:	74 4b                	je     4ac0 <handle_client_request+0x90>
        dest[i] = src[i];
    4a75:	44 0f b6 01          	movzbl (%rcx),%r8d
    4a79:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4a7c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4a80:	75 e6                	jne    4a68 <handle_client_request+0x38>
    4a82:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4a86:	75 e0                	jne    4a68 <handle_client_request+0x38>
            dest[i] = '\0';
    4a88:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4a8b:	8b 47 08             	mov    0x8(%rdi),%eax
    4a8e:	48 89 f2             	mov    %rsi,%rdx
    4a91:	4c 89 d7             	mov    %r10,%rdi
    4a94:	89 c6                	mov    %eax,%esi
    4a96:	e8 75 fe ff ff       	call   4910 <handle_http_method>
}
    4a9b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4aa3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4aac:	75 39                	jne    4ae7 <handle_client_request+0xb7>
    4aae:	31 c0                	xor    %eax,%eax
    4ab0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4ab7:	c3                   	ret
    4ab8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4ac0:	48 8b 0d 59 45 00 00 	mov    0x4559(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4ac7:	ba 12 00 00 00       	mov    $0x12,%edx
    4acc:	be 01 00 00 00       	mov    $0x1,%esi
    4ad1:	48 8d 3d 5f 16 00 00 	lea    0x165f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    4ad8:	e8 e3 d9 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    4add:	bf 01 00 00 00       	mov    $0x1,%edi
    4ae2:	e8 b9 d9 ff ff       	call   24a0 <exit@plt>
}
    4ae7:	e8 44 d8 ff ff       	call   2330 <__stack_chk_fail@plt>
    4aec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004af0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4af0:	f3 0f 1e fa          	endbr64
    4af4:	55                   	push   %rbp
    4af5:	53                   	push   %rbx
    4af6:	48 89 cb             	mov    %rcx,%rbx
    4af9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4afd:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4b00:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4b03:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4b09:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4b0c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4b0f:	f6 c1 02             	test   $0x2,%cl
    4b12:	74 00                	je     4b14 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4b14:	41 89 c0             	mov    %eax,%r8d
    4b17:	45 29 c8             	sub    %r9d,%r8d
    4b1a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4b1e:	0f 82 68 da ff ff    	jb     258c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4b24:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4b27:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4b2a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4b2d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4b30:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4b33:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4b37:	d3 e5                	shl    %cl,%ebp
    4b39:	48 c1 e5 06          	shl    $0x6,%rbp
    4b3d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4b41:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4b44:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4b49:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4b50:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4b54:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4b58:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4b60:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4b68:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4b6c:	e8 9f d8 ff ff       	call   2410 <malloc@plt>
  io_uring_submit(ring);
    4b71:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4b74:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4b7a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4b7e:	48 83 c4 08          	add    $0x8,%rsp
    4b82:	5b                   	pop    %rbx
    4b83:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4b84:	e9 b7 d7 ff ff       	jmp    2340 <io_uring_submit@plt>
    4b89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004b90 <io_thread>:
void* io_thread(void *arg) {
    4b90:	f3 0f 1e fa          	endbr64
    4b94:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4b96:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4b98:	41 56                	push   %r14
    4b9a:	41 55                	push   %r13
    4b9c:	41 54                	push   %r12
    4b9e:	55                   	push   %rbp
    4b9f:	48 89 fd             	mov    %rdi,%rbp
    4ba2:	53                   	push   %rbx
    4ba3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4baa:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4bb3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4bbb:	48 8b 47 48          	mov    0x48(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4bbf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4bc4:	bf 00 01 00 00       	mov    $0x100,%edi
    4bc9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4bcc:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4bd0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4bd5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4bda:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4bdf:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4be4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4bec:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4bf1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4bf9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4bfe:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4c06:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4c0b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4c13:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4c18:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4c20:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4c25:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4c2d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4c35:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4c3d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4c45:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4c4d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4c55:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4c5d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4c65:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4c6d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4c75:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4c7d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4c84:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4c8c:	e8 5f d7 ff ff       	call   23f0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4c91:	48 8b 7d 48          	mov    0x48(%rbp),%rdi
    4c95:	31 f6                	xor    %esi,%esi
    4c97:	e8 44 d8 ff ff       	call   24e0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4c9c:	31 d2                	xor    %edx,%edx
    4c9e:	be 01 00 00 00       	mov    $0x1,%esi
    4ca3:	bf 02 00 00 00       	mov    $0x2,%edi
    4ca8:	e8 83 d8 ff ff       	call   2530 <socket@plt>
  if (sock == -1)
    4cad:	83 f8 ff             	cmp    $0xffffffff,%eax
    4cb0:	0f 84 18 d9 ff ff    	je     25ce <io_thread.cold+0x38>
  if (setsockopt(sock,
    4cb6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4cbb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4cc1:	89 c7                	mov    %eax,%edi
    4cc3:	41 89 c4             	mov    %eax,%r12d
    4cc6:	ba 02 00 00 00       	mov    $0x2,%edx
    4ccb:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4cd0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4cd8:	e8 23 d6 ff ff       	call   2300 <setsockopt@plt>
    4cdd:	85 c0                	test   %eax,%eax
    4cdf:	0f 88 bd d8 ff ff    	js     25a2 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4ce5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4cea:	ba 10 00 00 00       	mov    $0x10,%edx
    4cef:	44 89 e7             	mov    %r12d,%edi
    4cf2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4cfb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4d03:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4d0b:	e8 50 d7 ff ff       	call   2460 <bind@plt>
    4d10:	85 c0                	test   %eax,%eax
    4d12:	0f 88 c2 d8 ff ff    	js     25da <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4d18:	be 0a 00 00 00       	mov    $0xa,%esi
    4d1d:	44 89 e7             	mov    %r12d,%edi
    4d20:	e8 fb d6 ff ff       	call   2420 <listen@plt>
    4d25:	85 c0                	test   %eax,%eax
    4d27:	0f 88 81 d8 ff ff    	js     25ae <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4d2d:	ba db 18 00 00       	mov    $0x18db,%edx
    4d32:	48 8d 35 43 14 00 00 	lea    0x1443(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4d39:	bf 01 00 00 00       	mov    $0x1,%edi
    4d3e:	31 c0                	xor    %eax,%eax
    4d40:	e8 0b d7 ff ff       	call   2450 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4d45:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4d4a:	48 89 d9             	mov    %rbx,%rcx
    4d4d:	44 89 e7             	mov    %r12d,%edi
    4d50:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4d55:	48 89 c6             	mov    %rax,%rsi
    4d58:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4d5d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4d62:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4d6a:	e8 81 fd ff ff       	call   4af0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4d6f:	bf 01 00 00 00       	mov    $0x1,%edi
    4d74:	be 10 00 00 00       	mov    $0x10,%esi
    4d79:	e8 22 d6 ff ff       	call   23a0 <calloc@plt>
    void *buf = malloc(size);
    4d7e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4d83:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4d86:	e8 85 d6 ff ff       	call   2410 <malloc@plt>
    if (!buf) {
    4d8b:	48 85 c0             	test   %rax,%rax
    4d8e:	0f 84 ae 04 00 00    	je     5242 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    4d94:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4d98:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4d9f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    4da6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4dae:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4db1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4db6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4db8:	f6 c1 02             	test   $0x2,%cl
    4dbb:	0f 85 0f 04 00 00    	jne    51d0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    4dc1:	89 d0                	mov    %edx,%eax
    4dc3:	29 f0                	sub    %esi,%eax
    4dc5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4dcc:	0f 82 f2 d7 ff ff    	jb     25c4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4dd2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4dd5:	48 8d 75 50          	lea    0x50(%rbp),%rsi
	sqe->addr3 = 0;
    4dd9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4ddd:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4de0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4de7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4dea:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4df1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4df8:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4dfa:	8b 55 50             	mov    0x50(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4dfd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4e02:	48 c1 e0 06          	shl    $0x6,%rax
    4e06:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4e0e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4e14:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4e17:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4e1f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4e23:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4e2b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4e33:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4e37:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4e3b:	e8 00 d5 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    4e40:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4e44:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4e49:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4e51:	0f 85 d7 01 00 00    	jne    502e <io_thread+0x49e>
    4e57:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4e5c:	4d 89 ce             	mov    %r9,%r14
    4e5f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4e64:	0f 1f 40 00          	nopl   0x0(%rax)
    4e68:	48 8d 3d 23 13 00 00 	lea    0x1323(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4e6f:	e8 7c d4 ff ff       	call   22f0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4e74:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4e7b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4e82:	c1 e9 0b             	shr    $0xb,%ecx
    4e85:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4e88:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4e90:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4e92:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4e9a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4e9c:	39 d0                	cmp    %edx,%eax
    4e9e:	74 36                	je     4ed6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4ea0:	89 f8                	mov    %edi,%eax
    4ea2:	21 d0                	and    %edx,%eax
    4ea4:	d3 e0                	shl    %cl,%eax
    4ea6:	48 c1 e0 04          	shl    $0x4,%rax
    4eaa:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4eb2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4eba:	0f 85 a8 01 00 00    	jne    5068 <io_thread+0x4d8>
    4ec0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4ec4:	0f 85 0e 03 00 00    	jne    51d8 <io_thread+0x648>
			if (cqe->res < 0)
    4eca:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4ecd:	83 c2 01             	add    $0x1,%edx
    4ed0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4ed2:	85 c0                	test   %eax,%eax
    4ed4:	79 b2                	jns    4e88 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    4ed6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    4edf:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4ee0:	45 31 c0             	xor    %r8d,%r8d
    4ee3:	31 d2                	xor    %edx,%edx
    4ee5:	b9 01 00 00 00       	mov    $0x1,%ecx
    4eea:	4c 89 f6             	mov    %r14,%rsi
    4eed:	48 89 df             	mov    %rbx,%rdi
    4ef0:	e8 4b d5 ff ff       	call   2440 <__io_uring_get_cqe@plt>
    4ef5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    4ef8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4efd:	48 83 38 01          	cmpq   $0x1,(%rax)
    4f01:	0f 84 e1 02 00 00    	je     51e8 <io_thread+0x658>
    4f07:	48 8d 3d aa 12 00 00 	lea    0x12aa(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4f0e:	e8 dd d3 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4f13:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4f18:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4f1b:	45 85 ff             	test   %r15d,%r15d
    4f1e:	0f 88 72 d6 ff ff    	js     2596 <io_thread.cold>
      if (cqe->res < 0) {
    4f24:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    4f27:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    4f2b:	85 c0                	test   %eax,%eax
    4f2d:	0f 88 d5 02 00 00    	js     5208 <io_thread+0x678>
      switch (req->event_type) {
    4f33:	41 83 f8 01          	cmp    $0x1,%r8d
    4f37:	0f 84 7b 01 00 00    	je     50b8 <io_thread+0x528>
    4f3d:	41 83 f8 02          	cmp    $0x2,%r8d
    4f41:	0f 84 a1 01 00 00    	je     50e8 <io_thread+0x558>
    4f47:	45 85 c0             	test   %r8d,%r8d
    4f4a:	0f 85 50 01 00 00    	jne    50a0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4f50:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    4f55:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    4f5a:	48 89 d9             	mov    %rbx,%rcx
    4f5d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4f61:	e8 8a fb ff ff       	call   4af0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    4f66:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f6b:	48 89 de             	mov    %rbx,%rsi
    4f6e:	8b 78 08             	mov    0x8(%rax),%edi
    4f71:	e8 1a f5 ff ff       	call   4490 <add_read_request>
              free(req);
    4f76:	4c 89 e7             	mov    %r12,%rdi
    4f79:	e8 42 d3 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4f7e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    4f83:	48 85 c0             	test   %rax,%rax
    4f86:	0f 85 14 01 00 00    	jne    50a0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    4f8c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4f93:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4f9a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4f9d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4fa2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4fa4:	f6 c1 02             	test   $0x2,%cl
    4fa7:	74 00                	je     4fa9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    4fa9:	89 d0                	mov    %edx,%eax
    4fab:	29 f0                	sub    %esi,%eax
    4fad:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4fb4:	0f 82 00 d6 ff ff    	jb     25ba <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    4fba:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    4fbd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    4fc2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    4fc6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4fc9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4fd0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4fd3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4fda:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4fe1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4fe3:	8b 55 50             	mov    0x50(%rbp),%edx
    4fe6:	48 c1 e0 06          	shl    $0x6,%rax
    4fea:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4ff2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4ff8:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4ffb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5003:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5007:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    500f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5017:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    501b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    501f:	e8 1c d3 ff ff       	call   2340 <io_uring_submit@plt>
  while (data->running == 1) {
    5024:	83 7d 34 01          	cmpl   $0x1,0x34(%rbp)
    5028:	0f 84 3a fe ff ff    	je     4e68 <io_thread+0x2d8>
    502e:	48 8d 3d bc 11 00 00 	lea    0x11bc(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    5035:	e8 b6 d2 ff ff       	call   22f0 <puts@plt>
}
    503a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5042:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    504b:	0f 85 18 02 00 00    	jne    5269 <io_thread+0x6d9>
    5051:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5058:	31 c0                	xor    %eax,%eax
    505a:	5b                   	pop    %rbx
    505b:	5d                   	pop    %rbp
    505c:	41 5c                	pop    %r12
    505e:	41 5d                	pop    %r13
    5060:	41 5e                	pop    %r14
    5062:	41 5f                	pop    %r15
    5064:	c3                   	ret
    5065:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5068:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    506d:	48 85 c0             	test   %rax,%rax
    5070:	0f 84 6a fe ff ff    	je     4ee0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5076:	48 83 38 01          	cmpq   $0x1,(%rax)
    507a:	0f 84 68 01 00 00    	je     51e8 <io_thread+0x658>
    5080:	48 8d 3d 31 11 00 00 	lea    0x1131(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    5087:	e8 64 d2 ff ff       	call   22f0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    508c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5091:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5094:	e9 8b fe ff ff       	jmp    4f24 <io_thread+0x394>
    5099:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    50a0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    50a8:	8b 02                	mov    (%rdx),%eax
    50aa:	83 c0 01             	add    $0x1,%eax
    50ad:	89 02                	mov    %eax,(%rdx)
}
    50af:	e9 d8 fe ff ff       	jmp    4f8c <io_thread+0x3fc>
    50b4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    50b8:	85 c0                	test   %eax,%eax
    50ba:	75 74                	jne    5130 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    50bc:	48 8b 0d 5d 3f 00 00 	mov    0x3f5d(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    50c3:	ba 0f 00 00 00       	mov    $0xf,%edx
    50c8:	be 01 00 00 00       	mov    $0x1,%esi
    50cd:	48 8d 3d 0d 11 00 00 	lea    0x110d(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    50d4:	e8 e7 d3 ff ff       	call   24c0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    50d9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    50de:	e9 a0 fe ff ff       	jmp    4f83 <io_thread+0x3f3>
    50e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    50e8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    50ed:	45 31 ff             	xor    %r15d,%r15d
    50f0:	85 c0                	test   %eax,%eax
    50f2:	7e 20                	jle    5114 <io_thread+0x584>
    50f4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    50f8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    50fb:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    50ff:	48 c1 e0 04          	shl    $0x4,%rax
    5103:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5108:	e8 b3 d1 ff ff       	call   22c0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    510d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5112:	7f e4                	jg     50f8 <io_thread+0x568>
              close(req->client_socket);
    5114:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5119:	e8 52 d2 ff ff       	call   2370 <close@plt>
              free(req);
    511e:	4c 89 e7             	mov    %r12,%rdi
    5121:	e8 9a d1 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5126:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    512b:	e9 53 fe ff ff       	jmp    4f83 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5130:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5135:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    513a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5142:	eb 11                	jmp    5155 <io_thread+0x5c5>
    5144:	0f 1f 40 00          	nopl   0x0(%rax)
    5148:	48 83 c0 01          	add    $0x1,%rax
    514c:	48 83 c2 01          	add    $0x1,%rdx
    5150:	48 39 c6             	cmp    %rax,%rsi
    5153:	74 4b                	je     51a0 <io_thread+0x610>
        dest[i] = src[i];
    5155:	0f b6 0a             	movzbl (%rdx),%ecx
    5158:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    515a:	80 f9 0d             	cmp    $0xd,%cl
    515d:	75 e9                	jne    5148 <io_thread+0x5b8>
    515f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5163:	75 e3                	jne    5148 <io_thread+0x5b8>
            dest[i] = '\0';
    5165:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5168:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    516d:	48 89 da             	mov    %rbx,%rdx
    5170:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5175:	e8 96 f7 ff ff       	call   4910 <handle_http_method>
              free(req->iov[0].iov_base);
    517a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    517f:	e8 3c d1 ff ff       	call   22c0 <free@plt>
              free(req);
    5184:	4c 89 e7             	mov    %r12,%rdi
    5187:	e8 34 d1 ff ff       	call   22c0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    518c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5191:	e9 ed fd ff ff       	jmp    4f83 <io_thread+0x3f3>
    5196:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    51a0:	48 8b 0d 79 3e 00 00 	mov    0x3e79(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    51a7:	ba 12 00 00 00       	mov    $0x12,%edx
    51ac:	be 01 00 00 00       	mov    $0x1,%esi
    51b1:	48 8d 3d 7f 0f 00 00 	lea    0xf7f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    51b8:	e8 03 d3 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    51bd:	bf 01 00 00 00       	mov    $0x1,%edi
    51c2:	e8 d9 d2 ff ff       	call   24a0 <exit@plt>
    51c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    51d0:	e9 ec fb ff ff       	jmp    4dc1 <io_thread+0x231>
    51d5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    51d8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    51dd:	e9 94 fe ff ff       	jmp    5076 <io_thread+0x4e6>
    51e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    51e8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    51f0:	48 8d 3d ad 0f 00 00 	lea    0xfad(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    51f7:	8b 02                	mov    (%rdx),%eax
    51f9:	83 c0 01             	add    $0x1,%eax
    51fc:	89 02                	mov    %eax,(%rdx)
    51fe:	e8 ed d0 ff ff       	call   22f0 <puts@plt>
    5203:	e9 26 fe ff ff       	jmp    502e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5208:	f7 d8                	neg    %eax
    520a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    520f:	89 c7                	mov    %eax,%edi
    5211:	e8 ea d2 ff ff       	call   2500 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5216:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    521b:	be 01 00 00 00       	mov    $0x1,%esi
    5220:	48 8b 3d f9 3d 00 00 	mov    0x3df9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    5227:	48 89 c1             	mov    %rax,%rcx
    522a:	48 8d 15 07 12 00 00 	lea    0x1207(%rip),%rdx        # 6438 <_IO_stdin_used+0x438>
    5231:	31 c0                	xor    %eax,%eax
    5233:	e8 98 d2 ff ff       	call   24d0 <__fprintf_chk@plt>
          exit(1);
    5238:	bf 01 00 00 00       	mov    $0x1,%edi
    523d:	e8 5e d2 ff ff       	call   24a0 <exit@plt>
    5242:	48 8b 0d d7 3d 00 00 	mov    0x3dd7(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5249:	ba 28 00 00 00       	mov    $0x28,%edx
    524e:	be 01 00 00 00       	mov    $0x1,%esi
    5253:	48 8d 3d ae 11 00 00 	lea    0x11ae(%rip),%rdi        # 6408 <_IO_stdin_used+0x408>
    525a:	e8 61 d2 ff ff       	call   24c0 <fwrite@plt>
        exit(1);
    525f:	bf 01 00 00 00       	mov    $0x1,%edi
    5264:	e8 37 d2 ff ff       	call   24a0 <exit@plt>
}
    5269:	e8 c2 d0 ff ff       	call   2330 <__stack_chk_fail@plt>
    526e:	66 90                	xchg   %ax,%ax

0000000000005270 <sendm>:
int sendm(struct BarrierTask *data) {
    5270:	f3 0f 1e fa          	endbr64
    5274:	41 57                	push   %r15
    5276:	41 56                	push   %r14
    5278:	41 55                	push   %r13
    527a:	41 54                	push   %r12
    527c:	55                   	push   %rbp
    527d:	53                   	push   %rbx
    527e:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->sending == 1) {
    5282:	83 bf 78 01 00 00 01 	cmpl   $0x1,0x178(%rdi)
    5289:	0f 85 99 01 00 00    	jne    5428 <sendm+0x1b8>
    528f:	48 8d b7 80 01 00 00 	lea    0x180(%rdi),%rsi
      for (int n = 0 ; n < data->thread_count; n++) {
    5296:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    529c:	48 89 fa             	mov    %rdi,%rdx
    529f:	31 c9                	xor    %ecx,%ecx
    52a1:	48 89 34 24          	mov    %rsi,(%rsp)
    52a5:	48 8d b7 88 01 00 00 	lea    0x188(%rdi),%rsi
    52ac:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    52b1:	85 c0                	test   %eax,%eax
    52b3:	0f 8e ce 00 00 00    	jle    5387 <sendm+0x117>
    52b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    52c0:	39 8a 30 01 00 00    	cmp    %ecx,0x130(%rdx)
    52c6:	0f 84 af 00 00 00    	je     537b <sendm+0x10b>
        struct Data *them = data->mailboxes[n].higher;
    52cc:	49 89 ca             	mov    %rcx,%r10
    52cf:	49 c1 e2 05          	shl    $0x5,%r10
    52d3:	4c 03 92 68 01 00 00 	add    0x168(%rdx),%r10
    52da:	4d 8b 5a 08          	mov    0x8(%r10),%r11
        for (; them->messages_count < min;) {
    52de:	49 8b 5b 08          	mov    0x8(%r11),%rbx
    52e2:	4d 63 4b 10          	movslq 0x10(%r11),%r9
    52e6:	4c 39 cb             	cmp    %r9,%rbx
    52e9:	0f 8d 83 00 00 00    	jge    5372 <sendm+0x102>
    52ef:	4c 89 cf             	mov    %r9,%rdi
    52f2:	48 8b aa 08 01 00 00 	mov    0x108(%rdx),%rbp
    52f9:	4d 8b 72 10          	mov    0x10(%r10),%r14
    52fd:	48 29 df             	sub    %rbx,%rdi
          them->messages[them->messages_count++] = data->message; 
    5300:	49 8b 33             	mov    (%r11),%rsi
    5303:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    5307:	48 83 f8 02          	cmp    $0x2,%rax
    530b:	0f 86 ff 00 00 00    	jbe    5410 <sendm+0x1a0>
    5311:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5319:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5321:	4c 8d 24 06          	lea    (%rsi,%rax,1),%r12
    5325:	4e 8d 2c 06          	lea    (%rsi,%r8,1),%r13
    5329:	4c 39 2c 24          	cmp    %r13,(%rsp)
    532d:	73 71                	jae    53a0 <sendm+0x130>
    532f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5334:	4d 39 fc             	cmp    %r15,%r12
    5337:	73 67                	jae    53a0 <sendm+0x130>
    5339:	48 8d 1c 06          	lea    (%rsi,%rax,1),%rbx
    533d:	49 01 f0             	add    %rsi,%r8
    5340:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
        for (; them->messages_count < min;) {
    5347:	48 83 c3 08          	add    $0x8,%rbx
          them->messages[them->messages_count++] = data->message; 
    534b:	48 89 43 f8          	mov    %rax,-0x8(%rbx)
        for (; them->messages_count < min;) {
    534f:	49 39 d8             	cmp    %rbx,%r8
    5352:	75 ec                	jne    5340 <sendm+0xd0>
    5354:	0f 1f 40 00          	nopl   0x0(%rax)
    5358:	48 01 fd             	add    %rdi,%rbp
    535b:	4c 01 f7             	add    %r14,%rdi
    535e:	48 89 aa 08 01 00 00 	mov    %rbp,0x108(%rdx)
    5365:	49 89 7a 10          	mov    %rdi,0x10(%r10)
    5369:	4d 89 4b 08          	mov    %r9,0x8(%r11)
    536d:	4a 89 44 ce f8       	mov    %rax,-0x8(%rsi,%r9,8)
        asm volatile ("sfence" ::: "memory");
    5372:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5375:	8b 82 34 01 00 00    	mov    0x134(%rdx),%eax
    537b:	48 83 c1 01          	add    $0x1,%rcx
    537f:	39 c8                	cmp    %ecx,%eax
    5381:	0f 8f 39 ff ff ff    	jg     52c0 <sendm+0x50>
}
    5387:	48 83 c4 18          	add    $0x18,%rsp
    538b:	31 c0                	xor    %eax,%eax
    538d:	5b                   	pop    %rbx
    538e:	5d                   	pop    %rbp
    538f:	41 5c                	pop    %r12
    5391:	41 5d                	pop    %r13
    5393:	41 5e                	pop    %r14
    5395:	41 5f                	pop    %r15
    5397:	c3                   	ret
    5398:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    53a0:	49 89 fd             	mov    %rdi,%r13
    53a3:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    53aa:	4d 89 e0             	mov    %r12,%r8
    53ad:	49 d1 ed             	shr    %r13
    53b0:	49 c1 e5 04          	shl    $0x4,%r13
    53b4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    53b9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    53bd:	41 83 e5 10          	and    $0x10,%r13d
    53c1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    53c5:	74 11                	je     53d8 <sendm+0x168>
          them->messages[them->messages_count++] = data->message; 
    53c7:	49 83 c0 10          	add    $0x10,%r8
    53cb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    53d0:	4d 39 f8             	cmp    %r15,%r8
    53d3:	74 15                	je     53ea <sendm+0x17a>
    53d5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    53d8:	41 0f 11 00          	movups %xmm0,(%r8)
    53dc:	49 83 c0 20          	add    $0x20,%r8
    53e0:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
        for (; them->messages_count < min;) {
    53e5:	4d 39 f8             	cmp    %r15,%r8
    53e8:	75 ee                	jne    53d8 <sendm+0x168>
    53ea:	49 89 f8             	mov    %rdi,%r8
    53ed:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    53f1:	49 01 d8             	add    %rbx,%r8
    53f4:	40 f6 c7 01          	test   $0x1,%dil
    53f8:	0f 84 5a ff ff ff    	je     5358 <sendm+0xe8>
          them->messages[them->messages_count++] = data->message; 
    53fe:	48 8b 82 80 01 00 00 	mov    0x180(%rdx),%rax
    5405:	4a 89 04 c6          	mov    %rax,(%rsi,%r8,8)
        for (; them->messages_count < min;) {
    5409:	e9 4a ff ff ff       	jmp    5358 <sendm+0xe8>
    540e:	66 90                	xchg   %ax,%ax
    5410:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    5418:	4e 8d 04 cd 00 00 00 00 	lea    0x0(,%r9,8),%r8
    5420:	e9 14 ff ff ff       	jmp    5339 <sendm+0xc9>
    5425:	0f 1f 00             	nopl   (%rax)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5428:	48 8d 3d d5 0d 00 00 	lea    0xdd5(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    542f:	e8 bc ce ff ff       	call   22f0 <puts@plt>
    5434:	e9 4e ff ff ff       	jmp    5387 <sendm+0x117>
    5439:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005440 <receive>:
int receive(struct BarrierTask *data) {
    5440:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5444:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    544a:	85 c0                	test   %eax,%eax
    544c:	0f 8e f1 00 00 00    	jle    5543 <receive+0x103>
int receive(struct BarrierTask *data) {
    5452:	41 54                	push   %r12
    5454:	48 89 fa             	mov    %rdi,%rdx
    5457:	55                   	push   %rbp
    5458:	31 ed                	xor    %ebp,%ebp
    545a:	53                   	push   %rbx
    545b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5460:	48 89 ee             	mov    %rbp,%rsi
    5463:	48 c1 e6 05          	shl    $0x5,%rsi
    5467:	48 03 b2 68 01 00 00 	add    0x168(%rdx),%rsi
    546e:	4c 8b 26             	mov    (%rsi),%r12
    for (int x = 0 ; x < me->messages_count ; x++) {
    5471:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    5476:	48 85 ff             	test   %rdi,%rdi
    5479:	0f 8e a1 00 00 00    	jle    5520 <receive+0xe0>
      data->sends++;
    547f:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    5486:	4d 8b 04 24          	mov    (%r12),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    548a:	4c 63 1a             	movslq (%rdx),%r11
    548d:	49 89 c9             	mov    %rcx,%r9
    5490:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5494:	49 f7 d9             	neg    %r9
    5497:	48 01 c7             	add    %rax,%rdi
    549a:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    549e:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    54a5:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    54a9:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    54ac:	49 29 c8             	sub    %rcx,%r8
    54af:	eb 10                	jmp    54c1 <receive+0x81>
    54b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    54b8:	48 83 c0 01          	add    $0x1,%rax
    54bc:	48 39 c7             	cmp    %rax,%rdi
    54bf:	74 5f                	je     5520 <receive+0xe0>
      data->n++;
    54c1:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    54c5:	48 89 82 70 01 00 00 	mov    %rax,0x170(%rdx)
      data->n++;
    54cc:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    54d3:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    54d7:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    54db:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    54e0:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    54e4:	75 d2                	jne    54b8 <receive+0x78>
    54e6:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    54ed:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    54f1:	75 c5                	jne    54b8 <receive+0x78>
    54f3:	bf 01 00 00 00       	mov    $0x1,%edi
    54f8:	b9 01 00 00 00       	mov    $0x1,%ecx
    54fd:	ba 01 00 00 00       	mov    $0x1,%edx
    5502:	31 c0                	xor    %eax,%eax
    5504:	48 8d 35 55 0f 00 00 	lea    0xf55(%rip),%rsi        # 6460 <_IO_stdin_used+0x460>
    550b:	e8 40 cf ff ff       	call   2450 <__printf_chk@plt>
        exit(1);
    5510:	bf 01 00 00 00       	mov    $0x1,%edi
    5515:	e8 86 cf ff ff       	call   24a0 <exit@plt>
    551a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5520:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    5529:	0f ae f8             	sfence
  for (int n = 0 ; n < data->thread_count; n++) {
    552c:	48 83 c5 01          	add    $0x1,%rbp
    5530:	39 aa 34 01 00 00    	cmp    %ebp,0x134(%rdx)
    5536:	0f 8f 24 ff ff ff    	jg     5460 <receive+0x20>
}
    553c:	5b                   	pop    %rbx
    553d:	31 c0                	xor    %eax,%eax
    553f:	5d                   	pop    %rbp
    5540:	41 5c                	pop    %r12
    5542:	c3                   	ret
    5543:	31 c0                	xor    %eax,%eax
    5545:	c3                   	ret
    5546:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005550 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5550:	f3 0f 1e fa          	endbr64
    5554:	41 57                	push   %r15
    5556:	41 56                	push   %r14
    5558:	41 55                	push   %r13
    555a:	41 54                	push   %r12
    555c:	55                   	push   %rbp
    555d:	53                   	push   %rbx
    555e:	48 89 fb             	mov    %rdi,%rbx
    5561:	48 83 ec 18          	sub    $0x18,%rsp
  if (data->thread_index == data->task_index) {
    5565:	8b 07                	mov    (%rdi),%eax
    5567:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    556d:	0f 84 3d 01 00 00    	je     56b0 <barriered_work+0x160>
    receive(data);
    5573:	e8 c8 fe ff ff       	call   5440 <receive>
    while (data->scheduled == 1) {
    5578:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    557f:	75 1b                	jne    559c <barriered_work+0x4c>
    5581:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    5588:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    5590:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5593:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    559a:	74 ec                	je     5588 <barriered_work+0x38>
  if (data->sending == 1) {
    559c:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    55a3:	0f 85 74 02 00 00    	jne    581d <barriered_work+0x2cd>
      for (int n = 0 ; n < data->thread_count; n++) {
    55a9:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    55af:	85 c0                	test   %eax,%eax
    55b1:	0f 8e 72 02 00 00    	jle    5829 <barriered_work+0x2d9>
    55b7:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    55be:	31 d2                	xor    %edx,%edx
    55c0:	48 89 0c 24          	mov    %rcx,(%rsp)
    55c4:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    55cb:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
        if (n == data->thread_index) { continue; }
    55d0:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    55d6:	0f 84 bf 00 00 00    	je     569b <barriered_work+0x14b>
        struct Data *them = data->mailboxes[n].higher;
    55dc:	49 89 d1             	mov    %rdx,%r9
    55df:	49 c1 e1 05          	shl    $0x5,%r9
    55e3:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    55ea:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    55ee:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    55f2:	4d 63 42 10          	movslq 0x10(%r10),%r8
    55f6:	4d 39 c3             	cmp    %r8,%r11
    55f9:	0f 8d 93 00 00 00    	jge    5692 <barriered_work+0x142>
    55ff:	4c 89 c6             	mov    %r8,%rsi
    5602:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5609:	4d 8b 71 10          	mov    0x10(%r9),%r14
    560d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5610:	49 8b 0a             	mov    (%r10),%rcx
    5613:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5617:	48 83 f8 02          	cmp    $0x2,%rax
    561b:	0f 86 8f 02 00 00    	jbe    58b0 <barriered_work+0x360>
    5621:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5629:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5631:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5635:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5639:	4c 39 2c 24          	cmp    %r13,(%rsp)
    563d:	0f 83 fd 01 00 00    	jae    5840 <barriered_work+0x2f0>
    5643:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5648:	4d 39 fc             	cmp    %r15,%r12
    564b:	0f 83 ef 01 00 00    	jae    5840 <barriered_work+0x2f0>
    5651:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5655:	48 01 cf             	add    %rcx,%rdi
    5658:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5660:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5667:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    566b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    566f:	49 39 fb             	cmp    %rdi,%r11
    5672:	75 ec                	jne    5660 <barriered_work+0x110>
    5674:	0f 1f 40 00          	nopl   0x0(%rax)
    5678:	48 01 f5             	add    %rsi,%rbp
    567b:	4c 01 f6             	add    %r14,%rsi
    567e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5685:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5689:	4d 89 42 08          	mov    %r8,0x8(%r10)
    568d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    5692:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    5695:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    569b:	48 83 c2 01          	add    $0x1,%rdx
    569f:	39 d0                	cmp    %edx,%eax
    56a1:	0f 8f 29 ff ff ff    	jg     55d0 <barriered_work+0x80>
    56a7:	e9 7d 01 00 00       	jmp    5829 <barriered_work+0x2d9>
    56ac:	0f 1f 40 00          	nopl   0x0(%rax)
      receive(data);
    56b0:	e8 8b fd ff ff       	call   5440 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    56b5:	4c 63 8b 34 01 00 00 	movslq 0x134(%rbx),%r9
        int t = data->task_index;
    56bc:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    56be:	45 85 c9             	test   %r9d,%r9d
    56c1:	0f 8e 85 00 00 00    	jle    574c <barriered_work+0x1fc>
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    56c7:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    56ce:	4c 63 d8             	movslq %eax,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    56d1:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    56d4:	49 c1 e3 09          	shl    $0x9,%r11
    56d8:	4c 8b 52 10          	mov    0x10(%rdx),%r10
              int next_task = abs((t + 1) % (data->thread_count));
    56dc:	99                   	cltd
    56dd:	41 f7 f9             	idiv   %r9d
    56e0:	4c 89 d7             	mov    %r10,%rdi
    56e3:	4f 8d 24 ca          	lea    (%r10,%r9,8),%r12
    56e7:	89 d0                	mov    %edx,%eax
    56e9:	f7 d8                	neg    %eax
    56eb:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    56ee:	45 31 c0             	xor    %r8d,%r8d
              int next_task = abs((t + 1) % (data->thread_count));
    56f1:	48 63 ea             	movslq %edx,%rbp
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    56f4:	48 c1 e5 09          	shl    $0x9,%rbp
    56f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
int barriered_work(struct BarrierTask *data) {
    5700:	31 c0                	xor    %eax,%eax
    5702:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5708:	49 8b 14 c2          	mov    (%r10,%rax,8),%rdx
    570c:	48 8b 52 28          	mov    0x28(%rdx),%rdx
    5710:	48 8b 8c 2a 68 01 00 00 	mov    0x168(%rdx,%rbp,1),%rcx
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5718:	48 8b 17             	mov    (%rdi),%rdx
    571b:	48 8b 72 28          	mov    0x28(%rdx),%rsi
    571f:	48 89 c2             	mov    %rax,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    5722:	48 83 c0 01          	add    $0x1,%rax
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
    5726:	48 c1 e2 05          	shl    $0x5,%rdx
    572a:	4a 03 94 1e 68 01 00 00 	add    0x168(%rsi,%r11,1),%rdx
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
    5732:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    5736:	4a 89 14 01          	mov    %rdx,(%rcx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    573a:	49 39 c1             	cmp    %rax,%r9
    573d:	75 c9                	jne    5708 <barriered_work+0x1b8>
        for (int y = 0; y < data->thread_count ; y++) {
    573f:	48 83 c7 08          	add    $0x8,%rdi
    5743:	49 83 c0 20          	add    $0x20,%r8
    5747:	49 39 fc             	cmp    %rdi,%r12
    574a:	75 b4                	jne    5700 <barriered_work+0x1b0>
      asm volatile ("sfence" ::: "memory");
    574c:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    574f:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    5756:	31 ff                	xor    %edi,%edi
    5758:	48 c1 e6 05          	shl    $0x5,%rsi
    575c:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    5763:	e8 a8 cb ff ff       	call   2310 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5768:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    576f:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5776:	48 8b 50 38          	mov    0x38(%rax),%rdx
    577a:	8b 4a 10             	mov    0x10(%rdx),%ecx
    577d:	8d 69 01             	lea    0x1(%rcx),%ebp
    5780:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    5783:	75 53                	jne    57d8 <barriered_work+0x288>
    5785:	0f 1f 00             	nopl   (%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    5788:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    578f:	48 8b 40 10          	mov    0x10(%rax),%rax
    5793:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    5796:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    579e:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    57a2:	48 c1 e7 09          	shl    $0x9,%rdi
    57a6:	48 03 78 28          	add    0x28(%rax),%rdi
    57aa:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    57b0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    57b3:	83 bb 40 01 00 00 01 	cmpl   $0x1,0x140(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    57ba:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    57c1:	74 c5                	je     5788 <barriered_work+0x238>
    if (modcount != data->thread->protected_state->modcount) {
    57c3:	48 8b 40 38          	mov    0x38(%rax),%rax
    57c7:	3b 68 10             	cmp    0x10(%rax),%ebp
    57ca:	74 0c                	je     57d8 <barriered_work+0x288>
    57cc:	48 8d 3d 3d 0a 00 00 	lea    0xa3d(%rip),%rdi        # 6210 <_IO_stdin_used+0x210>
    57d3:	e8 18 cb ff ff       	call   22f0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    57d8:	48 8b b3 58 01 00 00 	mov    0x158(%rbx),%rsi
    57df:	31 ff                	xor    %edi,%edi
    57e1:	48 c1 e6 05          	shl    $0x5,%rsi
    57e5:	48 03 b3 48 01 00 00 	add    0x148(%rbx),%rsi
    57ec:	48 83 c6 10          	add    $0x10,%rsi
    57f0:	e8 1b cb ff ff       	call   2310 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    57f5:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    57fc:	48 83 c0 01          	add    $0x1,%rax
    5800:	48 99                	cqto
    5802:	48 f7 bb 50 01 00 00 	idivq  0x150(%rbx)
  if (data->sending == 1) {
    5809:	83 bb 78 01 00 00 01 	cmpl   $0x1,0x178(%rbx)
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5810:	48 89 93 58 01 00 00 	mov    %rdx,0x158(%rbx)
  if (data->sending == 1) {
    5817:	0f 84 a8 00 00 00    	je     58c5 <barriered_work+0x375>
    581d:	48 8d 3d e0 09 00 00 	lea    0x9e0(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    5824:	e8 c7 ca ff ff       	call   22f0 <puts@plt>
  asm volatile ("sfence" ::: "memory");
    5829:	0f ae f8             	sfence
}
    582c:	48 83 c4 18          	add    $0x18,%rsp
    5830:	31 c0                	xor    %eax,%eax
    5832:	5b                   	pop    %rbx
    5833:	5d                   	pop    %rbp
    5834:	41 5c                	pop    %r12
    5836:	41 5d                	pop    %r13
    5838:	41 5e                	pop    %r14
    583a:	41 5f                	pop    %r15
    583c:	c3                   	ret
    583d:	0f 1f 00             	nopl   (%rax)
    5840:	49 89 f5             	mov    %rsi,%r13
    5843:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    584a:	4c 89 e7             	mov    %r12,%rdi
    584d:	49 d1 ed             	shr    %r13
    5850:	49 c1 e5 04          	shl    $0x4,%r13
    5854:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5859:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    585d:	41 83 e5 10          	and    $0x10,%r13d
    5861:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5865:	74 11                	je     5878 <barriered_work+0x328>
          them->messages[them->messages_count++] = data->message; 
    5867:	48 83 c7 10          	add    $0x10,%rdi
    586b:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    5870:	49 39 ff             	cmp    %rdi,%r15
    5873:	74 13                	je     5888 <barriered_work+0x338>
    5875:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    5878:	0f 11 07             	movups %xmm0,(%rdi)
    587b:	48 83 c7 20          	add    $0x20,%rdi
    587f:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5883:	49 39 ff             	cmp    %rdi,%r15
    5886:	75 f0                	jne    5878 <barriered_work+0x328>
    5888:	48 89 f7             	mov    %rsi,%rdi
    588b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    588f:	4c 01 df             	add    %r11,%rdi
    5892:	40 f6 c6 01          	test   $0x1,%sil
    5896:	0f 84 dc fd ff ff    	je     5678 <barriered_work+0x128>
          them->messages[them->messages_count++] = data->message; 
    589c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    58a3:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    58a7:	e9 cc fd ff ff       	jmp    5678 <barriered_work+0x128>
    58ac:	0f 1f 40 00          	nopl   0x0(%rax)
    58b0:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    58b8:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    58c0:	e9 8c fd ff ff       	jmp    5651 <barriered_work+0x101>
      for (int n = 0 ; n < data->thread_count; n++) {
    58c5:	48 8d 8b 80 01 00 00 	lea    0x180(%rbx),%rcx
    58cc:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    58d2:	31 d2                	xor    %edx,%edx
    58d4:	48 89 0c 24          	mov    %rcx,(%rsp)
    58d8:	48 8d 8b 88 01 00 00 	lea    0x188(%rbx),%rcx
    58df:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    58e4:	85 c0                	test   %eax,%eax
    58e6:	0f 8e 3d ff ff ff    	jle    5829 <barriered_work+0x2d9>
    58ec:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    58f0:	39 93 30 01 00 00    	cmp    %edx,0x130(%rbx)
    58f6:	0f 84 af 00 00 00    	je     59ab <barriered_work+0x45b>
        struct Data *them = data->mailboxes[n].higher;
    58fc:	49 89 d1             	mov    %rdx,%r9
    58ff:	49 c1 e1 05          	shl    $0x5,%r9
    5903:	4c 03 8b 68 01 00 00 	add    0x168(%rbx),%r9
    590a:	4d 8b 51 08          	mov    0x8(%r9),%r10
        for (; them->messages_count < min;) {
    590e:	4d 8b 5a 08          	mov    0x8(%r10),%r11
    5912:	4d 63 42 10          	movslq 0x10(%r10),%r8
    5916:	4d 39 d8             	cmp    %r11,%r8
    5919:	0f 8e 83 00 00 00    	jle    59a2 <barriered_work+0x452>
    591f:	4c 89 c6             	mov    %r8,%rsi
    5922:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
    5929:	4d 8b 71 10          	mov    0x10(%r9),%r14
    592d:	4c 29 de             	sub    %r11,%rsi
          them->messages[them->messages_count++] = data->message; 
    5930:	49 8b 0a             	mov    (%r10),%rcx
    5933:	48 8d 46 ff          	lea    -0x1(%rsi),%rax
    5937:	48 83 f8 02          	cmp    $0x2,%rax
    593b:	0f 86 ef 00 00 00    	jbe    5a30 <barriered_work+0x4e0>
    5941:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5949:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5951:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5955:	4c 8d 2c 39          	lea    (%rcx,%rdi,1),%r13
    5959:	4c 39 2c 24          	cmp    %r13,(%rsp)
    595d:	73 61                	jae    59c0 <barriered_work+0x470>
    595f:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5964:	4d 39 fc             	cmp    %r15,%r12
    5967:	73 57                	jae    59c0 <barriered_work+0x470>
    5969:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    596d:	48 01 cf             	add    %rcx,%rdi
    5970:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
        for (; them->messages_count < min;) {
    5977:	49 83 c3 08          	add    $0x8,%r11
          them->messages[them->messages_count++] = data->message; 
    597b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
        for (; them->messages_count < min;) {
    597f:	49 39 fb             	cmp    %rdi,%r11
    5982:	75 ec                	jne    5970 <barriered_work+0x420>
    5984:	0f 1f 40 00          	nopl   0x0(%rax)
    5988:	48 01 f5             	add    %rsi,%rbp
    598b:	4c 01 f6             	add    %r14,%rsi
    598e:	48 89 ab 08 01 00 00 	mov    %rbp,0x108(%rbx)
    5995:	49 89 71 10          	mov    %rsi,0x10(%r9)
    5999:	4d 89 42 08          	mov    %r8,0x8(%r10)
    599d:	4a 89 44 c1 f8       	mov    %rax,-0x8(%rcx,%r8,8)
        asm volatile ("sfence" ::: "memory");
    59a2:	0f ae f8             	sfence
      for (int n = 0 ; n < data->thread_count; n++) {
    59a5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    59ab:	48 83 c2 01          	add    $0x1,%rdx
    59af:	39 d0                	cmp    %edx,%eax
    59b1:	0f 8f 39 ff ff ff    	jg     58f0 <barriered_work+0x3a0>
    59b7:	e9 6d fe ff ff       	jmp    5829 <barriered_work+0x2d9>
    59bc:	0f 1f 40 00          	nopl   0x0(%rax)
    59c0:	49 89 f5             	mov    %rsi,%r13
    59c3:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    59ca:	4c 89 e7             	mov    %r12,%rdi
    59cd:	49 d1 ed             	shr    %r13
    59d0:	49 c1 e5 04          	shl    $0x4,%r13
    59d4:	66 48 0f 6e c0       	movq   %rax,%xmm0
    59d9:	4f 8d 3c 2c          	lea    (%r12,%r13,1),%r15
    59dd:	41 83 e5 10          	and    $0x10,%r13d
    59e1:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    59e5:	74 11                	je     59f8 <barriered_work+0x4a8>
          them->messages[them->messages_count++] = data->message; 
    59e7:	48 83 c7 10          	add    $0x10,%rdi
    59eb:	41 0f 11 04 24       	movups %xmm0,(%r12)
        for (; them->messages_count < min;) {
    59f0:	4c 39 ff             	cmp    %r15,%rdi
    59f3:	74 13                	je     5a08 <barriered_work+0x4b8>
    59f5:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    59f8:	0f 11 07             	movups %xmm0,(%rdi)
    59fb:	48 83 c7 20          	add    $0x20,%rdi
    59ff:	0f 11 47 f0          	movups %xmm0,-0x10(%rdi)
        for (; them->messages_count < min;) {
    5a03:	4c 39 ff             	cmp    %r15,%rdi
    5a06:	75 f0                	jne    59f8 <barriered_work+0x4a8>
    5a08:	48 89 f7             	mov    %rsi,%rdi
    5a0b:	48 83 e7 fe          	and    $0xfffffffffffffffe,%rdi
    5a0f:	4c 01 df             	add    %r11,%rdi
    5a12:	40 f6 c6 01          	test   $0x1,%sil
    5a16:	0f 84 6c ff ff ff    	je     5988 <barriered_work+0x438>
          them->messages[them->messages_count++] = data->message; 
    5a1c:	48 8b 83 80 01 00 00 	mov    0x180(%rbx),%rax
    5a23:	48 89 04 f9          	mov    %rax,(%rcx,%rdi,8)
        for (; them->messages_count < min;) {
    5a27:	e9 5c ff ff ff       	jmp    5988 <barriered_work+0x438>
    5a2c:	0f 1f 40 00          	nopl   0x0(%rax)
    5a30:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5a38:	4a 8d 3c c5 00 00 00 00 	lea    0x0(,%r8,8),%rdi
    5a40:	e9 24 ff ff ff       	jmp    5969 <barriered_work+0x419>
    5a45:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005a50 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5a50:	f3 0f 1e fa          	endbr64
    5a54:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5a58:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    5a5f:	48 8b 40 40          	mov    0x40(%rax),%rax
    5a63:	48 63 10             	movslq (%rax),%rdx
    5a66:	85 d2                	test   %edx,%edx
    5a68:	7e 2c                	jle    5a96 <barriered_work_ingest+0x46>
    5a6a:	48 8b 40 08          	mov    0x8(%rax),%rax
    5a6e:	48 c1 e2 04          	shl    $0x4,%rdx
    5a72:	48 01 c2             	add    %rax,%rdx
    5a75:	0f 1f 00             	nopl   (%rax)
    if (data->thread->buffers->buffer[x].available == 1) {
    5a78:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    5a7c:	75 0f                	jne    5a8d <barriered_work_ingest+0x3d>
      data->ingest_count++;
    5a7e:	48 83 87 60 01 00 00 01 	addq   $0x1,0x160(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5a86:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5a8d:	48 83 c0 10          	add    $0x10,%rax
    5a91:	48 39 d0             	cmp    %rdx,%rax
    5a94:	75 e2                	jne    5a78 <barriered_work_ingest+0x28>
  asm volatile ("sfence" ::: "memory");
    5a96:	0f ae f8             	sfence
  barriered_work(data);
    5a99:	e8 b2 fa ff ff       	call   5550 <barriered_work>
}
    5a9e:	31 c0                	xor    %eax,%eax
    5aa0:	48 83 c4 08          	add    $0x8,%rsp
    5aa4:	c3                   	ret
    5aa5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005ab0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5ab0:	f3 0f 1e fa          	endbr64
}
    5ab4:	31 c0                	xor    %eax,%eax
    5ab6:	c3                   	ret
    5ab7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005ac0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5ac0:	f3 0f 1e fa          	endbr64
    5ac4:	31 c0                	xor    %eax,%eax
    5ac6:	c3                   	ret
    5ac7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005ad0 <after>:
int after(struct timespec left, struct timespec right) {
    5ad0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5ad4:	31 c0                	xor    %eax,%eax
    5ad6:	48 39 d7             	cmp    %rdx,%rdi
    5ad9:	7e 08                	jle    5ae3 <after+0x13>
    5adb:	31 c0                	xor    %eax,%eax
    5add:	48 39 ce             	cmp    %rcx,%rsi
    5ae0:	0f 9f c0             	setg   %al
}
    5ae3:	c3                   	ret
    5ae4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5aef:	90                   	nop

0000000000005af0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5af0:	f3 0f 1e fa          	endbr64
    5af4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5af9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    5afe:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5b00:	48 39 d7             	cmp    %rdx,%rdi
    5b03:	7f 18                	jg     5b1d <within+0x2d>
    5b05:	4d 39 d8             	cmp    %r11,%r8
    5b08:	0f 9e c2             	setle  %dl
    5b0b:	48 39 ce             	cmp    %rcx,%rsi
    5b0e:	0f 9e c0             	setle  %al
    5b11:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5b13:	31 c0                	xor    %eax,%eax
    5b15:	4d 39 d1             	cmp    %r10,%r9
    5b18:	0f 9e c0             	setle  %al
    5b1b:	21 d0                	and    %edx,%eax
}
    5b1d:	c3                   	ret
    5b1e:	66 90                	xchg   %ax,%ax

0000000000005b20 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5b20:	f3 0f 1e fa          	endbr64
    5b24:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5b29:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    5b2e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5b33:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5b38:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    5b3d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5b42:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5b47:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    5b4c:	48 39 fe             	cmp    %rdi,%rsi
    5b4f:	7d 2f                	jge    5b80 <overlap+0x60>
    5b51:	48 39 ca             	cmp    %rcx,%rdx
    5b54:	7d 62                	jge    5bb8 <overlap+0x98>
    5b56:	4d 39 da             	cmp    %r11,%r10
    5b59:	7d 0e                	jge    5b69 <overlap+0x49>
    return 1;
    5b5b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5b60:	4d 39 c1             	cmp    %r8,%r9
    5b63:	0f 8c 7f 00 00 00    	jl     5be8 <overlap+0xc8>
  return 0;
    5b69:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5b6b:	4d 39 c1             	cmp    %r8,%r9
    5b6e:	7f 4c                	jg     5bbc <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5b70:	31 c0                	xor    %eax,%eax
    5b72:	4d 39 da             	cmp    %r11,%r10
    5b75:	0f 9e c0             	setle  %al
    5b78:	c3                   	ret
    5b79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5b80:	7e 4e                	jle    5bd0 <overlap+0xb0>
    5b82:	48 39 ca             	cmp    %rcx,%rdx
    5b85:	7f 39                	jg     5bc0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5b87:	75 31                	jne    5bba <overlap+0x9a>
    5b89:	4d 39 c1             	cmp    %r8,%r9
    5b8c:	7c 2c                	jl     5bba <overlap+0x9a>
    return 1;
    5b8e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5b93:	4d 39 da             	cmp    %r11,%r10
    5b96:	7d 24                	jge    5bbc <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5b98:	48 39 ca             	cmp    %rcx,%rdx
    5b9b:	0f 94 c2             	sete   %dl
    5b9e:	48 39 fe             	cmp    %rdi,%rsi
    5ba1:	0f 94 c0             	sete   %al
    5ba4:	21 c2                	and    %eax,%edx
    5ba6:	31 c0                	xor    %eax,%eax
    5ba8:	4d 39 c1             	cmp    %r8,%r9
    5bab:	0f 94 c0             	sete   %al
    5bae:	21 d0                	and    %edx,%eax
    5bb0:	c3                   	ret
    5bb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5bb8:	74 af                	je     5b69 <overlap+0x49>
  return 0;
    5bba:	31 c0                	xor    %eax,%eax
}
    5bbc:	c3                   	ret
    5bbd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5bc0:	4d 39 da             	cmp    %r11,%r10
    5bc3:	7e c4                	jle    5b89 <overlap+0x69>
    return 1;
    5bc5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5bca:	4d 39 c1             	cmp    %r8,%r9
    5bcd:	7e ba                	jle    5b89 <overlap+0x69>
    5bcf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5bd0:	48 39 ca             	cmp    %rcx,%rdx
    5bd3:	7c 94                	jl     5b69 <overlap+0x49>
    5bd5:	4d 39 c1             	cmp    %r8,%r9
    5bd8:	7d b4                	jge    5b8e <overlap+0x6e>
    5bda:	48 39 ca             	cmp    %rcx,%rdx
    5bdd:	74 91                	je     5b70 <overlap+0x50>
    5bdf:	eb d9                	jmp    5bba <overlap+0x9a>
    5be1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5be8:	c3                   	ret
    5be9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005bf0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5bf0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5bf4:	85 f6                	test   %esi,%esi
    5bf6:	0f 8e 44 03 00 00    	jle    5f40 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    5bfc:	41 57                	push   %r15
    5bfe:	41 89 f7             	mov    %esi,%r15d
    5c01:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5c03:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5c06:	41 55                	push   %r13
    5c08:	41 54                	push   %r12
    5c0a:	55                   	push   %rbp
    5c0b:	53                   	push   %rbx
    5c0c:	48 8d 5f 28          	lea    0x28(%rdi),%rbx
    5c10:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5c14:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5c19:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5c1e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    5c21:	45 39 e6             	cmp    %r12d,%r14d
    5c24:	0f 84 4e 02 00 00    	je     5e78 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5c2a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5c2f:	8b 50 08             	mov    0x8(%rax),%edx
    5c32:	85 d2                	test   %edx,%edx
    5c34:	0f 8e 3e 02 00 00    	jle    5e78 <verify+0x288>
    5c3a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    5c3f:	31 c9                	xor    %ecx,%ecx
    5c41:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    5c46:	31 c0                	xor    %eax,%eax
    5c48:	44 89 f2             	mov    %r14d,%edx
    5c4b:	bf 01 00 00 00       	mov    $0x1,%edi
    5c50:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5c55:	48 8d 35 c4 05 00 00 	lea    0x5c4(%rip),%rsi        # 6220 <_IO_stdin_used+0x220>
    5c5c:	e8 ef c7 ff ff       	call   2450 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5c61:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5c66:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    5c6b:	8b 40 08             	mov    0x8(%rax),%eax
    5c6e:	85 c0                	test   %eax,%eax
    5c70:	0f 8e e6 01 00 00    	jle    5e5c <verify+0x26c>
    5c76:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5c79:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    5c7e:	31 db                	xor    %ebx,%ebx
    5c80:	48 c1 e0 09          	shl    $0x9,%rax
    5c84:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    5c89:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5c8e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5c93:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    5c98:	4c 8b 20             	mov    (%rax),%r12
    5c9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5ca0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    5ca5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    5caa:	49 89 de             	mov    %rbx,%r14
    5cad:	48 8d 35 81 05 00 00 	lea    0x581(%rip),%rsi        # 6235 <_IO_stdin_used+0x235>
    5cb4:	49 c1 e6 09          	shl    $0x9,%r14
    5cb8:	bf 01 00 00 00       	mov    $0x1,%edi
    5cbd:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5cc1:	4b 8b 8c 3c 58 01 00 00 	mov    0x158(%r12,%r15,1),%rcx
    5cc9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    5cce:	4a 8b 94 30 58 01 00 00 	mov    0x158(%rax,%r14,1),%rdx
    5cd6:	31 c0                	xor    %eax,%eax
    5cd8:	e8 73 c7 ff ff       	call   2450 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5cdd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5ce2:	4c 8b 20             	mov    (%rax),%r12
    5ce5:	4b 83 bc 3c 58 01 00 00 00 	cmpq   $0x0,0x158(%r12,%r15,1)
    5cee:	0f 8e 47 01 00 00    	jle    5e3b <verify+0x24b>
    5cf4:	4c 03 75 00          	add    0x0(%rbp),%r14
    5cf8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5cfd:	ba 01 00 00 00       	mov    $0x1,%edx
    5d02:	4d 89 f5             	mov    %r14,%r13
    5d05:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    5d0c:	4d 85 f6             	test   %r14,%r14
    5d0f:	0f 8e 21 01 00 00    	jle    5e36 <verify+0x246>
    5d15:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5d18:	48 89 d5             	mov    %rdx,%rbp
    5d1b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5d20:	31 db                	xor    %ebx,%ebx
    5d22:	4d 89 f2             	mov    %r14,%r10
    5d25:	48 c1 e5 05          	shl    $0x5,%rbp
    5d29:	48 83 ed 20          	sub    $0x20,%rbp
    5d2d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    5d31:	49 89 ee             	mov    %rbp,%r14
    5d34:	48 89 dd             	mov    %rbx,%rbp
    5d37:	48 89 d3             	mov    %rdx,%rbx
    5d3a:	eb 31                	jmp    5d6d <verify+0x17d>
    5d3c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5d40:	4c 39 c2             	cmp    %r8,%rdx
    5d43:	0f 8d 57 01 00 00    	jge    5ea0 <verify+0x2b0>
    5d49:	4c 39 df             	cmp    %r11,%rdi
    5d4c:	7e 05                	jle    5d53 <verify+0x163>
    5d4e:	49 39 c1             	cmp    %rax,%r9
    5d51:	7c 75                	jl     5dc8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5d53:	4c 39 df             	cmp    %r11,%rdi
    5d56:	0f 8d ab 01 00 00    	jge    5f07 <verify+0x317>
    5d5c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5d60:	48 83 c5 01          	add    $0x1,%rbp
    5d64:	49 39 ea             	cmp    %rbp,%r10
    5d67:	0f 8e a9 00 00 00    	jle    5e16 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5d6d:	49 8b 97 48 01 00 00 	mov    0x148(%r15),%rdx
    5d74:	48 89 e8             	mov    %rbp,%rax
    5d77:	48 c1 e0 05          	shl    $0x5,%rax
    5d7b:	49 03 85 48 01 00 00 	add    0x148(%r13),%rax
    5d82:	4c 01 f2             	add    %r14,%rdx
    5d85:	48 8b 08             	mov    (%rax),%rcx
    5d88:	48 8b 78 10          	mov    0x10(%rax),%rdi
    5d8c:	48 8b 32             	mov    (%rdx),%rsi
    5d8f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    5d93:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    5d97:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    5d9b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    5d9f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    5da3:	48 39 f1             	cmp    %rsi,%rcx
    5da6:	7c 98                	jl     5d40 <verify+0x150>
    5da8:	0f 8e 42 01 00 00    	jle    5ef0 <verify+0x300>
    5dae:	4c 39 c2             	cmp    %r8,%rdx
    5db1:	0f 8f f9 00 00 00    	jg     5eb0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5db7:	75 a7                	jne    5d60 <verify+0x170>
    5db9:	4c 39 df             	cmp    %r11,%rdi
    5dbc:	7f a2                	jg     5d60 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5dbe:	49 39 c1             	cmp    %rax,%r9
    5dc1:	7c 9d                	jl     5d60 <verify+0x170>
    5dc3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5dc8:	49 89 c1             	mov    %rax,%r9
    5dcb:	48 89 f9             	mov    %rdi,%rcx
    5dce:	48 89 f2             	mov    %rsi,%rdx
    5dd1:	bf 01 00 00 00       	mov    $0x1,%edi
    5dd6:	48 8d 35 ab 06 00 00 	lea    0x6ab(%rip),%rsi        # 6488 <_IO_stdin_used+0x488>
    5ddd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5ddf:	48 83 c5 01          	add    $0x1,%rbp
    5de3:	e8 68 c6 ff ff       	call   2450 <__printf_chk@plt>
    5de8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5ded:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    5df2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5df5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5dfa:	4d 8b 95 58 01 00 00 	mov    0x158(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5e01:	4c 8b 20             	mov    (%rax),%r12
    5e04:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5e09:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5e0d:	49 39 ea             	cmp    %rbp,%r10
    5e10:	0f 8f 57 ff ff ff    	jg     5d6d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5e16:	48 89 da             	mov    %rbx,%rdx
    5e19:	49 3b 9f 58 01 00 00 	cmp    0x158(%r15),%rbx
    5e20:	7d 14                	jge    5e36 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5e22:	4d 8b b5 58 01 00 00 	mov    0x158(%r13),%r14
    5e29:	48 83 c2 01          	add    $0x1,%rdx
    5e2d:	4d 85 f6             	test   %r14,%r14
    5e30:	0f 8f e2 fe ff ff    	jg     5d18 <verify+0x128>
    5e36:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5e3b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5e40:	48 83 c3 01          	add    $0x1,%rbx
    5e44:	39 58 08             	cmp    %ebx,0x8(%rax)
    5e47:	0f 8f 53 fe ff ff    	jg     5ca0 <verify+0xb0>
    5e4d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    5e52:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    5e57:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5e5c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5e61:	48 83 c1 01          	add    $0x1,%rcx
    5e65:	39 48 08             	cmp    %ecx,0x8(%rax)
    5e68:	0f 8f d8 fd ff ff    	jg     5c46 <verify+0x56>
    5e6e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    5e73:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    5e78:	48 81 44 24 10 b0 00 00 00 	addq   $0xb0,0x10(%rsp)
    5e81:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    5e86:	41 39 c7             	cmp    %eax,%r15d
    5e89:	0f 84 86 00 00 00    	je     5f15 <verify+0x325>
    5e8f:	41 89 c4             	mov    %eax,%r12d
    5e92:	e9 8a fd ff ff       	jmp    5c21 <verify+0x31>
    5e97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ea0:	0f 85 ba fe ff ff    	jne    5d60 <verify+0x170>
    5ea6:	e9 a8 fe ff ff       	jmp    5d53 <verify+0x163>
    5eab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5eb0:	49 39 c1             	cmp    %rax,%r9
    5eb3:	7e 09                	jle    5ebe <verify+0x2ce>
    5eb5:	4c 39 df             	cmp    %r11,%rdi
    5eb8:	0f 8c 0a ff ff ff    	jl     5dc8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ebe:	4c 39 df             	cmp    %r11,%rdi
    5ec1:	0f 8f 99 fe ff ff    	jg     5d60 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5ec7:	49 39 c1             	cmp    %rax,%r9
    5eca:	0f 8d f8 fe ff ff    	jge    5dc8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ed0:	48 39 f1             	cmp    %rsi,%rcx
    5ed3:	0f 85 87 fe ff ff    	jne    5d60 <verify+0x170>
    5ed9:	4c 39 c2             	cmp    %r8,%rdx
    5edc:	0f 85 7e fe ff ff    	jne    5d60 <verify+0x170>
    5ee2:	4c 39 df             	cmp    %r11,%rdi
    5ee5:	0f 84 dd fe ff ff    	je     5dc8 <verify+0x1d8>
    5eeb:	e9 70 fe ff ff       	jmp    5d60 <verify+0x170>
    5ef0:	4c 39 c2             	cmp    %r8,%rdx
    5ef3:	0f 8c 5a fe ff ff    	jl     5d53 <verify+0x163>
    5ef9:	4c 39 df             	cmp    %r11,%rdi
    5efc:	7e c9                	jle    5ec7 <verify+0x2d7>
    5efe:	4c 39 c2             	cmp    %r8,%rdx
    5f01:	0f 85 59 fe ff ff    	jne    5d60 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5f07:	49 39 c1             	cmp    %rax,%r9
    5f0a:	0f 8f 50 fe ff ff    	jg     5d60 <verify+0x170>
    5f10:	e9 b3 fe ff ff       	jmp    5dc8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    5f15:	48 81 44 24 18 b0 00 00 00 	addq   $0xb0,0x18(%rsp)
    5f1e:	41 8d 46 01          	lea    0x1(%r14),%eax
    5f22:	45 39 e6             	cmp    %r12d,%r14d
    5f25:	74 08                	je     5f2f <verify+0x33f>
    5f27:	41 89 c6             	mov    %eax,%r14d
    5f2a:	e9 ea fc ff ff       	jmp    5c19 <verify+0x29>
}
    5f2f:	48 83 c4 58          	add    $0x58,%rsp
    5f33:	31 c0                	xor    %eax,%eax
    5f35:	5b                   	pop    %rbx
    5f36:	5d                   	pop    %rbp
    5f37:	41 5c                	pop    %r12
    5f39:	41 5d                	pop    %r13
    5f3b:	41 5e                	pop    %r14
    5f3d:	41 5f                	pop    %r15
    5f3f:	c3                   	ret
    5f40:	31 c0                	xor    %eax,%eax
    5f42:	c3                   	ret

Disassembly of section .fini:

0000000000005f44 <_fini>:
    5f44:	f3 0f 1e fa          	endbr64
    5f48:	48 83 ec 08          	sub    $0x8,%rsp
    5f4c:	48 83 c4 08          	add    $0x8,%rsp
    5f50:	c3                   	ret
