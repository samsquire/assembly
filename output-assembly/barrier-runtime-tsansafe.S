
barrier-runtime-tsansafe:     file format elf64-x86-64


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
    2020:	ff 35 6a 6e 00 00    	push   0x6e6a(%rip)        # 8e90 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 6c 6e 00 00    	jmp    *0x6e6c(%rip)        # 8e98 <_GLOBAL_OFFSET_TABLE_+0x10>
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

Disassembly of section .plt.got:

00000000000022a0 <__cxa_finalize@plt>:
    22a0:	f3 0f 1e fa          	endbr64
    22a4:	ff 25 4e 6d 00 00    	jmp    *0x6d4e(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    22aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

00000000000022b0 <free@plt>:
    22b0:	f3 0f 1e fa          	endbr64
    22b4:	ff 25 e6 6b 00 00    	jmp    *0x6be6(%rip)        # 8ea0 <free@GLIBC_2.2.5>
    22ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000022c0 <putchar@plt>:
    22c0:	f3 0f 1e fa          	endbr64
    22c4:	ff 25 de 6b 00 00    	jmp    *0x6bde(%rip)        # 8ea8 <putchar@GLIBC_2.2.5>
    22ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000022d0 <puts@plt>:
    22d0:	f3 0f 1e fa          	endbr64
    22d4:	ff 25 d6 6b 00 00    	jmp    *0x6bd6(%rip)        # 8eb0 <puts@GLIBC_2.2.5>
    22da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000022e0 <setsockopt@plt>:
    22e0:	f3 0f 1e fa          	endbr64
    22e4:	ff 25 ce 6b 00 00    	jmp    *0x6bce(%rip)        # 8eb8 <setsockopt@GLIBC_2.2.5>
    22ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000022f0 <clock_gettime@plt>:
    22f0:	f3 0f 1e fa          	endbr64
    22f4:	ff 25 c6 6b 00 00    	jmp    *0x6bc6(%rip)        # 8ec0 <clock_gettime@GLIBC_2.17>
    22fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002300 <strlen@plt>:
    2300:	f3 0f 1e fa          	endbr64
    2304:	ff 25 be 6b 00 00    	jmp    *0x6bbe(%rip)        # 8ec8 <strlen@GLIBC_2.2.5>
    230a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002310 <__stack_chk_fail@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 b6 6b 00 00    	jmp    *0x6bb6(%rip)        # 8ed0 <__stack_chk_fail@GLIBC_2.4>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002320 <io_uring_submit@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 ae 6b 00 00    	jmp    *0x6bae(%rip)        # 8ed8 <io_uring_submit@LIBURING_2.0>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <nanosleep@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 a6 6b 00 00    	jmp    *0x6ba6(%rip)        # 8ee0 <nanosleep@GLIBC_2.2.5>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <strrchr@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 9e 6b 00 00    	jmp    *0x6b9e(%rip)        # 8ee8 <strrchr@GLIBC_2.2.5>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <close@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 96 6b 00 00    	jmp    *0x6b96(%rip)        # 8ef0 <close@GLIBC_2.2.5>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <strtok_r@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 8e 6b 00 00    	jmp    *0x6b8e(%rip)        # 8ef8 <strtok_r@GLIBC_2.2.5>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <read@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 86 6b 00 00    	jmp    *0x6b86(%rip)        # 8f00 <read@GLIBC_2.2.5>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <calloc@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 7e 6b 00 00    	jmp    *0x6b7e(%rip)        # 8f08 <calloc@GLIBC_2.2.5>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <strcmp@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 76 6b 00 00    	jmp    *0x6b76(%rip)        # 8f10 <strcmp@GLIBC_2.2.5>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <__memcpy_chk@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 6e 6b 00 00    	jmp    *0x6b6e(%rip)        # 8f18 <__memcpy_chk@GLIBC_2.3.4>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <stat@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 66 6b 00 00    	jmp    *0x6b66(%rip)        # 8f20 <stat@GLIBC_2.33>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <memcpy@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 5e 6b 00 00    	jmp    *0x6b5e(%rip)        # 8f28 <memcpy@GLIBC_2.14>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <io_uring_queue_init@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 56 6b 00 00    	jmp    *0x6b56(%rip)        # 8f30 <io_uring_queue_init@LIBURING_2.0>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <eventfd_write@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 4e 6b 00 00    	jmp    *0x6b4e(%rip)        # 8f38 <eventfd_write@GLIBC_2.7>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <malloc@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 46 6b 00 00    	jmp    *0x6b46(%rip)        # 8f40 <malloc@GLIBC_2.2.5>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <listen@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 3e 6b 00 00    	jmp    *0x6b3e(%rip)        # 8f48 <listen@GLIBC_2.2.5>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <__strcpy_chk@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 36 6b 00 00    	jmp    *0x6b36(%rip)        # 8f50 <__strcpy_chk@GLIBC_2.3.4>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <__io_uring_get_cqe@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 2e 6b 00 00    	jmp    *0x6b2e(%rip)        # 8f58 <__io_uring_get_cqe@LIBURING_2.0>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <__printf_chk@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 26 6b 00 00    	jmp    *0x6b26(%rip)        # 8f60 <__printf_chk@GLIBC_2.3.4>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <bind@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 1e 6b 00 00    	jmp    *0x6b1e(%rip)        # 8f68 <bind@GLIBC_2.2.5>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <pthread_create@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 16 6b 00 00    	jmp    *0x6b16(%rip)        # 8f70 <pthread_create@GLIBC_2.34>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <open@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 0e 6b 00 00    	jmp    *0x6b0e(%rip)        # 8f78 <open@GLIBC_2.2.5>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <perror@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 06 6b 00 00    	jmp    *0x6b06(%rip)        # 8f80 <perror@GLIBC_2.2.5>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <exit@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 fe 6a 00 00    	jmp    *0x6afe(%rip)        # 8f88 <exit@GLIBC_2.2.5>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <eventfd@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 f6 6a 00 00    	jmp    *0x6af6(%rip)        # 8f90 <eventfd@GLIBC_2.7>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <fwrite@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 ee 6a 00 00    	jmp    *0x6aee(%rip)        # 8f98 <fwrite@GLIBC_2.2.5>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <__fprintf_chk@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 e6 6a 00 00    	jmp    *0x6ae6(%rip)        # 8fa0 <__fprintf_chk@GLIBC_2.3.4>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <io_uring_register_eventfd@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 de 6a 00 00    	jmp    *0x6ade(%rip)        # 8fa8 <io_uring_register_eventfd@LIBURING_2.0>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <pthread_join@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 d6 6a 00 00    	jmp    *0x6ad6(%rip)        # 8fb0 <pthread_join@GLIBC_2.34>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <strerror@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 ce 6a 00 00    	jmp    *0x6ace(%rip)        # 8fb8 <strerror@GLIBC_2.2.5>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <__ctype_tolower_loc@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 c6 6a 00 00    	jmp    *0x6ac6(%rip)        # 8fc0 <__ctype_tolower_loc@GLIBC_2.3>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <__sprintf_chk@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 be 6a 00 00    	jmp    *0x6abe(%rip)        # 8fc8 <__sprintf_chk@GLIBC_2.3.4>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <socket@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 b6 6a 00 00    	jmp    *0x6ab6(%rip)        # 8fd0 <socket@GLIBC_2.2.5>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000002520 <add_write_request.cold>:
    2520:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    2526:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    252e:	0f 0b                	ud2

0000000000002530 <add_read_request.cold>:
    2530:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2538:	0f 0b                	ud2

000000000000253a <_send_static_string_content.cold>:
    253a:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    2540:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2548:	0f 0b                	ud2

000000000000254a <add_accept_request.cold>:
    254a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2552:	0f 0b                	ud2

0000000000002554 <io_thread.cold>:
    2554:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    255c:	0f 0b                	ud2
    255e:	66 90                	xchg   %ax,%ax

0000000000002560 <main>:
    2560:	f3 0f 1e fa          	endbr64
    2564:	41 57                	push   %r15
    2566:	48 8d 3d 5b 3f 00 00 	lea    0x3f5b(%rip),%rdi        # 64c8 <_IO_stdin_used+0x4c8>
    256d:	41 56                	push   %r14
    256f:	41 55                	push   %r13
    2571:	41 54                	push   %r12
    2573:	55                   	push   %rbp
    2574:	53                   	push   %rbx
    2575:	48 83 ec 68          	sub    $0x68,%rsp
    2579:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2582:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    2587:	31 c0                	xor    %eax,%eax
    2589:	e8 42 fd ff ff       	call   22d0 <puts@plt>
    258e:	bf 0a 00 00 00       	mov    $0xa,%edi
    2593:	e8 28 fd ff ff       	call   22c0 <putchar@plt>
    2598:	48 8d 3d 93 3c 00 00 	lea    0x3c93(%rip),%rdi        # 6232 <_IO_stdin_used+0x232>
    259f:	e8 2c fd ff ff       	call   22d0 <puts@plt>
    25a4:	ba 06 00 00 00       	mov    $0x6,%edx
    25a9:	48 8d 35 9e 3c 00 00 	lea    0x3c9e(%rip),%rsi        # 624e <_IO_stdin_used+0x24e>
    25b0:	31 c0                	xor    %eax,%eax
    25b2:	bf 01 00 00 00       	mov    $0x1,%edi
    25b7:	e8 74 fe ff ff       	call   2430 <__printf_chk@plt>
    25bc:	ba 09 00 00 00       	mov    $0x9,%edx
    25c1:	48 8d 35 a0 3c 00 00 	lea    0x3ca0(%rip),%rsi        # 6268 <_IO_stdin_used+0x268>
    25c8:	31 c0                	xor    %eax,%eax
    25ca:	bf 01 00 00 00       	mov    $0x1,%edi
    25cf:	e8 5c fe ff ff       	call   2430 <__printf_chk@plt>
    25d4:	ba 01 00 00 00       	mov    $0x1,%edx
    25d9:	48 8d 35 9c 3c 00 00 	lea    0x3c9c(%rip),%rsi        # 627c <_IO_stdin_used+0x27c>
    25e0:	31 c0                	xor    %eax,%eax
    25e2:	bf 01 00 00 00       	mov    $0x1,%edi
    25e7:	e8 44 fe ff ff       	call   2430 <__printf_chk@plt>
    25ec:	ba 01 00 00 00       	mov    $0x1,%edx
    25f1:	48 8d 35 95 3c 00 00 	lea    0x3c95(%rip),%rsi        # 628d <_IO_stdin_used+0x28d>
    25f8:	31 c0                	xor    %eax,%eax
    25fa:	bf 01 00 00 00       	mov    $0x1,%edi
    25ff:	e8 2c fe ff ff       	call   2430 <__printf_chk@plt>
    2604:	ba 01 00 00 00       	mov    $0x1,%edx
    2609:	48 8d 35 95 3c 00 00 	lea    0x3c95(%rip),%rsi        # 62a5 <_IO_stdin_used+0x2a5>
    2610:	31 c0                	xor    %eax,%eax
    2612:	bf 01 00 00 00       	mov    $0x1,%edi
    2617:	e8 14 fe ff ff       	call   2430 <__printf_chk@plt>
    261c:	ba 01 00 00 00       	mov    $0x1,%edx
    2621:	48 8d 35 00 3f 00 00 	lea    0x3f00(%rip),%rsi        # 6528 <_IO_stdin_used+0x528>
    2628:	31 c0                	xor    %eax,%eax
    262a:	bf 01 00 00 00       	mov    $0x1,%edi
    262f:	e8 fc fd ff ff       	call   2430 <__printf_chk@plt>
    2634:	ba 01 00 00 00       	mov    $0x1,%edx
    2639:	48 8d 35 18 3f 00 00 	lea    0x3f18(%rip),%rsi        # 6558 <_IO_stdin_used+0x558>
    2640:	31 c0                	xor    %eax,%eax
    2642:	bf 01 00 00 00       	mov    $0x1,%edi
    2647:	e8 e4 fd ff ff       	call   2430 <__printf_chk@plt>
    264c:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2651:	48 8d 35 69 3c 00 00 	lea    0x3c69(%rip),%rsi        # 62c1 <_IO_stdin_used+0x2c1>
    2658:	31 c0                	xor    %eax,%eax
    265a:	bf 01 00 00 00       	mov    $0x1,%edi
    265f:	e8 cc fd ff ff       	call   2430 <__printf_chk@plt>
    2664:	ba 1e 00 00 00       	mov    $0x1e,%edx
    2669:	48 8d 35 6b 3c 00 00 	lea    0x3c6b(%rip),%rsi        # 62db <_IO_stdin_used+0x2db>
    2670:	31 c0                	xor    %eax,%eax
    2672:	bf 01 00 00 00       	mov    $0x1,%edi
    2677:	e8 b4 fd ff ff       	call   2430 <__printf_chk@plt>
    267c:	48 8d 3d 4b 3a 00 00 	lea    0x3a4b(%rip),%rdi        # 60ce <_IO_stdin_used+0xce>
    2683:	e8 48 fc ff ff       	call   22d0 <puts@plt>
    2688:	be 18 00 00 00       	mov    $0x18,%esi
    268d:	bf 01 00 00 00       	mov    $0x1,%edi
    2692:	e8 e9 fc ff ff       	call   2380 <calloc@plt>
    2697:	be 98 00 00 00       	mov    $0x98,%esi
    269c:	bf 09 00 00 00       	mov    $0x9,%edi
    26a1:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    26a6:	e8 d5 fc ff ff       	call   2380 <calloc@plt>
    26ab:	be 10 00 00 00       	mov    $0x10,%esi
    26b0:	bf 01 00 00 00       	mov    $0x1,%edi
    26b5:	48 89 04 24          	mov    %rax,(%rsp)
    26b9:	e8 c2 fc ff ff       	call   2380 <calloc@plt>
    26be:	be 10 00 00 00       	mov    $0x10,%esi
    26c3:	bf 01 00 00 00       	mov    $0x1,%edi
    26c8:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    26ce:	48 89 c3             	mov    %rax,%rbx
    26d1:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    26d6:	e8 a5 fc ff ff       	call   2380 <calloc@plt>
    26db:	4c 8b 14 24          	mov    (%rsp),%r10
    26df:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
    26e7:	31 d2                	xor    %edx,%edx
    26e9:	48 89 43 08          	mov    %rax,0x8(%rbx)
    26ed:	49 89 d0             	mov    %rdx,%r8
    26f0:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    26f7:	4c 89 d5             	mov    %r10,%rbp
    26fa:	4c 89 54 24 40       	mov    %r10,0x40(%rsp)
    26ff:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    2704:	0f 1f 40 00          	nopl   0x0(%rax)
    2708:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    270d:	44 89 45 00          	mov    %r8d,0x0(%rbp)
    2711:	be 10 00 00 00       	mov    $0x10,%esi
    2716:	31 db                	xor    %ebx,%ebx
    2718:	c7 45 28 07 00 00 00 	movl   $0x7,0x28(%rbp)
    271f:	bf 64 00 00 00       	mov    $0x64,%edi
    2724:	48 89 45 10          	mov    %rax,0x10(%rbp)
    2728:	48 8b 05 c9 42 00 00 	mov    0x42c9(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
    272f:	44 89 04 24          	mov    %r8d,(%rsp)
    2733:	48 89 45 18          	mov    %rax,0x18(%rbp)
    2737:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    273c:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    2741:	48 89 45 30          	mov    %rax,0x30(%rbp)
    2745:	e8 36 fc ff ff       	call   2380 <calloc@plt>
    274a:	be 10 00 00 00       	mov    $0x10,%esi
    274f:	bf 64 00 00 00       	mov    $0x64,%edi
    2754:	48 89 45 50          	mov    %rax,0x50(%rbp)
    2758:	e8 23 fc ff ff       	call   2380 <calloc@plt>
    275d:	be 28 00 00 00       	mov    $0x28,%esi
    2762:	bf 64 00 00 00       	mov    $0x64,%edi
    2767:	66 0f 6f 15 61 42 00 00 	movdqa 0x4261(%rip),%xmm2        # 69d0 <_IO_stdin_used+0x9d0>
    276f:	48 89 45 58          	mov    %rax,0x58(%rbp)
    2773:	0f 11 55 68          	movups %xmm2,0x68(%rbp)
    2777:	e8 04 fc ff ff       	call   2380 <calloc@plt>
    277c:	be 80 02 00 00       	mov    $0x280,%esi
    2781:	bf 07 00 00 00       	mov    $0x7,%edi
    2786:	66 0f 6f 1d 42 42 00 00 	movdqa 0x4242(%rip),%xmm3        # 69d0 <_IO_stdin_used+0x9d0>
    278e:	48 89 45 78          	mov    %rax,0x78(%rbp)
    2792:	0f 11 9d 80 00 00 00 	movups %xmm3,0x80(%rbp)
    2799:	e8 e2 fb ff ff       	call   2380 <calloc@plt>
    279e:	48 89 6c 24 08       	mov    %rbp,0x8(%rsp)
    27a3:	48 89 45 20          	mov    %rax,0x20(%rbp)
    27a7:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    27ac:	49 89 c7             	mov    %rax,%r15
    27af:	90                   	nop
    27b0:	4c 63 f3             	movslq %ebx,%r14
    27b3:	89 6c 24 20          	mov    %ebp,0x20(%rsp)
    27b7:	4f 8d 2c b6          	lea    (%r14,%r14,4),%r13
    27bb:	49 c1 e5 07          	shl    $0x7,%r13
    27bf:	39 eb                	cmp    %ebp,%ebx
    27c1:	0f 84 c1 09 00 00    	je     3188 <main+0xc28>
    27c7:	be 20 00 00 00       	mov    $0x20,%esi
    27cc:	bf 06 00 00 00       	mov    $0x6,%edi
    27d1:	e8 aa fb ff ff       	call   2380 <calloc@plt>
    27d6:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    27da:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    27df:	4c 8d a0 c0 00 00 00 	lea    0xc0(%rax),%r12
    27e6:	4b 89 84 2f 28 02 00 00 	mov    %rax,0x228(%r15,%r13,1)
    27ee:	49 89 c7             	mov    %rax,%r15
    27f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    27f8:	be 08 00 00 00       	mov    $0x8,%esi
    27fd:	bf 01 00 00 00       	mov    $0x1,%edi
    2802:	49 83 c7 20          	add    $0x20,%r15
    2806:	e8 75 fb ff ff       	call   2380 <calloc@plt>
    280b:	be 08 00 00 00       	mov    $0x8,%esi
    2810:	bf 01 00 00 00       	mov    $0x1,%edi
    2815:	48 89 c5             	mov    %rax,%rbp
    2818:	e8 63 fb ff ff       	call   2380 <calloc@plt>
    281d:	be 00 01 00 00       	mov    $0x100,%esi
    2822:	bf 02 00 00 00       	mov    $0x2,%edi
    2827:	48 89 c3             	mov    %rax,%rbx
    282a:	e8 51 fb ff ff       	call   2380 <calloc@plt>
    282f:	66 0f 6f 05 a9 41 00 00 	movdqa 0x41a9(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
    2837:	48 8d b0 00 01 00 00 	lea    0x100(%rax),%rsi
    283e:	49 89 47 e0          	mov    %rax,-0x20(%r15)
    2842:	49 89 77 e8          	mov    %rsi,-0x18(%r15)
    2846:	48 89 28             	mov    %rbp,(%rax)
    2849:	48 89 98 00 01 00 00 	mov    %rbx,0x100(%rax)
    2850:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
    2857:	0f 29 80 80 01 00 00 	movaps %xmm0,0x180(%rax)
    285e:	4d 39 fc             	cmp    %r15,%r12
    2861:	75 95                	jne    27f8 <main+0x298>
    2863:	be 01 00 00 00       	mov    $0x1,%esi
    2868:	bf 00 01 00 00       	mov    $0x100,%edi
    286d:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    2871:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    2876:	e8 05 fb ff ff       	call   2380 <calloc@plt>
    287b:	bf 18 00 00 00       	mov    $0x18,%edi
    2880:	49 89 c4             	mov    %rax,%r12
    2883:	e8 68 fb ff ff       	call   23f0 <malloc@plt>
    2888:	44 8b 04 24          	mov    (%rsp),%r8d
    288c:	4c 89 e7             	mov    %r12,%rdi
    288f:	41 89 d9             	mov    %ebx,%r9d
    2892:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2897:	48 8d 0d e2 3c 00 00 	lea    0x3ce2(%rip),%rcx        # 6580 <_IO_stdin_used+0x580>
    289e:	ba 00 01 00 00       	mov    $0x100,%edx
    28a3:	31 c0                	xor    %eax,%eax
    28a5:	be 01 00 00 00       	mov    $0x1,%esi
    28aa:	e8 51 fc ff ff       	call   2500 <__sprintf_chk@plt>
    28af:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    28b4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    28b9:	ba ab aa aa aa       	mov    $0xaaaaaaab,%edx
    28be:	be 20 00 00 00       	mov    $0x20,%esi
    28c3:	bf 3f 42 0f 00       	mov    $0xf423f,%edi
    28c8:	4d 89 72 10          	mov    %r14,0x10(%r10)
    28cc:	44 8d 73 01          	lea    0x1(%rbx),%r14d
    28d0:	4c 8b 78 20          	mov    0x20(%rax),%r15
    28d4:	44 89 f0             	mov    %r14d,%eax
    28d7:	44 89 f1             	mov    %r14d,%ecx
    28da:	4d 89 22             	mov    %r12,(%r10)
    28dd:	48 0f af c2          	imul   %rdx,%rax
    28e1:	4f 8d 24 2f          	lea    (%r15,%r13,1),%r12
    28e5:	49 89 6a 08          	mov    %rbp,0x8(%r10)
    28e9:	4d 89 94 24 40 02 00 00 	mov    %r10,0x240(%r12)
    28f1:	49 c7 84 24 10 02 00 00 3f 42 0f 00 	movq   $0xf423f,0x210(%r12)
    28fd:	48 c1 e8 22          	shr    $0x22,%rax
    2901:	8d 04 40             	lea    (%rax,%rax,2),%eax
    2904:	01 c0                	add    %eax,%eax
    2906:	29 c1                	sub    %eax,%ecx
    2908:	41 89 8c 24 48 02 00 00 	mov    %ecx,0x248(%r12)
    2910:	e8 6b fa ff ff       	call   2380 <calloc@plt>
    2915:	8b 0c 24             	mov    (%rsp),%ecx
    2918:	41 89 1c 24          	mov    %ebx,(%r12)
    291c:	49 89 84 24 08 02 00 00 	mov    %rax,0x208(%r12)
    2924:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    2929:	49 c7 84 24 18 02 00 00 00 00 00 00 	movq   $0x0,0x218(%r12)
    2935:	49 89 84 24 28 01 00 00 	mov    %rax,0x128(%r12)
    293d:	48 8b 05 bc 40 00 00 	mov    0x40bc(%rip),%rax        # 6a00 <_IO_stdin_used+0xa00>
    2944:	41 89 8c 24 30 01 00 00 	mov    %ecx,0x130(%r12)
    294c:	49 89 84 24 80 01 00 00 	mov    %rax,0x180(%r12)
    2954:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
    295e:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
    296a:	41 c7 84 24 34 01 00 00 06 00 00 00 	movl   $0x6,0x134(%r12)
    2976:	49 89 84 24 38 02 00 00 	mov    %rax,0x238(%r12)
    297e:	83 fb 05             	cmp    $0x5,%ebx
    2981:	0f 84 e1 07 00 00    	je     3168 <main+0xc08>
    2987:	8b 44 24 20          	mov    0x20(%rsp),%eax
    298b:	39 c3                	cmp    %eax,%ebx
    298d:	75 59                	jne    29e8 <main+0x488>
    298f:	8b 74 24 28          	mov    0x28(%rsp),%esi
    2993:	85 f6                	test   %esi,%esi
    2995:	75 51                	jne    29e8 <main+0x488>
    2997:	89 ca                	mov    %ecx,%edx
    2999:	48 8d 35 08 3c 00 00 	lea    0x3c08(%rip),%rsi        # 65a8 <_IO_stdin_used+0x5a8>
    29a0:	bf 01 00 00 00       	mov    $0x1,%edi
    29a5:	31 c0                	xor    %eax,%eax
    29a7:	e8 84 fa ff ff       	call   2430 <__printf_chk@plt>
    29ac:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    29b1:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    29b6:	c7 44 24 28 01 00 00 00 	movl   $0x1,0x28(%rsp)
    29be:	4c 8b 78 20          	mov    0x20(%rax),%r15
    29c2:	48 89 48 38          	mov    %rcx,0x38(%rax)
    29c6:	48 8d 05 c3 2b 00 00 	lea    0x2bc3(%rip),%rax        # 5590 <barriered_work_ingest>
    29cd:	4b 89 84 2f 18 01 00 00 	mov    %rax,0x118(%r15,%r13,1)
    29d5:	41 83 fe 07          	cmp    $0x7,%r14d
    29d9:	74 22                	je     29fd <main+0x49d>
    29db:	44 89 f3             	mov    %r14d,%ebx
    29de:	e9 cd fd ff ff       	jmp    27b0 <main+0x250>
    29e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    29e8:	48 8d 05 21 28 00 00 	lea    0x2821(%rip),%rax        # 5210 <barriered_work>
    29ef:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
    29f7:	41 83 fe 07          	cmp    $0x7,%r14d
    29fb:	75 de                	jne    29db <main+0x47b>
    29fd:	48 8d 05 dc 08 00 00 	lea    0x8dc(%rip),%rax        # 32e0 <barriered_reset>
    2a04:	49 89 e8             	mov    %rbp,%r8
    2a07:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    2a0c:	41 c7 87 80 0f 00 00 00 00 00 00 	movl   $0x0,0xf80(%r15)
    2a17:	49 89 87 18 10 00 00 	mov    %rax,0x1018(%r15)
    2a1e:	8b 04 24             	mov    (%rsp),%eax
    2a21:	49 83 c0 01          	add    $0x1,%r8
    2a25:	49 89 af 28 10 00 00 	mov    %rbp,0x1028(%r15)
    2a2c:	48 81 c5 98 00 00 00 	add    $0x98,%rbp
    2a33:	41 89 87 30 10 00 00 	mov    %eax,0x1030(%r15)
    2a3a:	48 8b 05 bf 3f 00 00 	mov    0x3fbf(%rip),%rax        # 6a00 <_IO_stdin_used+0xa00>
    2a41:	41 c7 87 00 0f 00 00 06 00 00 00 	movl   $0x6,0xf00(%r15)
    2a4c:	41 c7 87 34 10 00 00 06 00 00 00 	movl   $0x6,0x1034(%r15)
    2a57:	41 c7 87 3c 11 00 00 06 00 00 00 	movl   $0x6,0x113c(%r15)
    2a62:	49 89 87 80 10 00 00 	mov    %rax,0x1080(%r15)
    2a69:	49 83 f8 09          	cmp    $0x9,%r8
    2a6d:	0f 85 95 fc ff ff    	jne    2708 <main+0x1a8>
    2a73:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    2a78:	48 8b 5c 24 48       	mov    0x48(%rsp),%rbx
    2a7d:	b9 01 00 00 00       	mov    $0x1,%ecx
    2a82:	49 8d b2 b0 03 00 00 	lea    0x3b0(%r10),%rsi
    2a89:	4d 8d 6a 20          	lea    0x20(%r10),%r13
    2a8d:	4d 89 92 38 04 00 00 	mov    %r10,0x438(%r10)
    2a94:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    2a99:	49 8d 82 28 04 00 00 	lea    0x428(%r10),%rax
    2aa0:	41 c7 82 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r10)
    2aab:	41 c7 82 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r10)
    2ab6:	41 c7 82 50 04 00 00 07 00 00 00 	movl   $0x7,0x450(%r10)
    2ac1:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2ac6:	4c 89 e8             	mov    %r13,%rax
    2ac9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    2ad0:	48 8b 10             	mov    (%rax),%rdx
    2ad3:	89 cf                	mov    %ecx,%edi
    2ad5:	87 ba 00 02 00 00    	xchg   %edi,0x200(%rdx)
    2adb:	48 05 98 00 00 00    	add    $0x98,%rax
    2ae1:	48 39 c6             	cmp    %rax,%rsi
    2ae4:	75 ea                	jne    2ad0 <main+0x570>
    2ae6:	be 38 00 00 00       	mov    $0x38,%esi
    2aeb:	bf 09 00 00 00       	mov    $0x9,%edi
    2af0:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    2af5:	e8 86 f8 ff ff       	call   2380 <calloc@plt>
    2afa:	be 38 00 00 00       	mov    $0x38,%esi
    2aff:	bf 09 00 00 00       	mov    $0x9,%edi
    2b04:	48 89 c5             	mov    %rax,%rbp
    2b07:	e8 74 f8 ff ff       	call   2380 <calloc@plt>
    2b0c:	be 38 00 00 00       	mov    $0x38,%esi
    2b11:	bf 09 00 00 00       	mov    $0x9,%edi
    2b16:	48 89 04 24          	mov    %rax,(%rsp)
    2b1a:	e8 61 f8 ff ff       	call   2380 <calloc@plt>
    2b1f:	be 08 00 00 00       	mov    $0x8,%esi
    2b24:	bf 09 00 00 00       	mov    $0x9,%edi
    2b29:	49 89 c7             	mov    %rax,%r15
    2b2c:	e8 4f f8 ff ff       	call   2380 <calloc@plt>
    2b31:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2b36:	ba 06 00 00 00       	mov    $0x6,%edx
    2b3b:	48 8d 35 ad 37 00 00 	lea    0x37ad(%rip),%rsi        # 62ef <_IO_stdin_used+0x2ef>
    2b42:	49 89 c6             	mov    %rax,%r14
    2b45:	48 8b 05 bc 3e 00 00 	mov    0x3ebc(%rip),%rax        # 6a08 <_IO_stdin_used+0xa08>
    2b4c:	bf 01 00 00 00       	mov    $0x1,%edi
    2b51:	4d 89 92 a0 03 00 00 	mov    %r10,0x3a0(%r10)
    2b58:	4d 89 f4             	mov    %r14,%r12
    2b5b:	49 89 82 b8 03 00 00 	mov    %rax,0x3b8(%r10)
    2b62:	31 c0                	xor    %eax,%eax
    2b64:	41 c7 82 a8 03 00 00 06 00 00 00 	movl   $0x6,0x3a8(%r10)
    2b6f:	49 c7 82 90 03 00 00 00 00 00 00 	movq   $0x0,0x390(%r10)
    2b7a:	e8 b1 f8 ff ff       	call   2430 <__printf_chk@plt>
    2b7f:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2b84:	49 8d 7e 30          	lea    0x30(%r14),%rdi
    2b88:	48 8d b5 50 01 00 00 	lea    0x150(%rbp),%rsi
    2b8f:	48 8d 15 8a 0b 00 00 	lea    0xb8a(%rip),%rdx        # 3720 <timer_thread>
    2b96:	49 8d 8a 90 03 00 00 	lea    0x390(%r10),%rcx
    2b9d:	e8 ae f8 ff ff       	call   2450 <pthread_create@plt>
    2ba2:	45 31 c0             	xor    %r8d,%r8d
    2ba5:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
    2baa:	49 89 dd             	mov    %rbx,%r13
    2bad:	44 89 c3             	mov    %r8d,%ebx
    2bb0:	89 da                	mov    %ebx,%edx
    2bb2:	41 c7 45 04 01 00 00 00 	movl   $0x1,0x4(%r13)
    2bba:	31 c0                	xor    %eax,%eax
    2bbc:	83 c3 01             	add    $0x1,%ebx
    2bbf:	41 c7 45 2c 01 00 00 00 	movl   $0x1,0x2c(%r13)
    2bc7:	48 8d 35 fa 39 00 00 	lea    0x39fa(%rip),%rsi        # 65c8 <_IO_stdin_used+0x5c8>
    2bce:	bf 01 00 00 00       	mov    $0x1,%edi
    2bd3:	e8 58 f8 ff ff       	call   2430 <__printf_chk@plt>
    2bd8:	4c 89 e9             	mov    %r13,%rcx
    2bdb:	48 89 ee             	mov    %rbp,%rsi
    2bde:	4c 89 e7             	mov    %r12,%rdi
    2be1:	48 8d 15 88 07 00 00 	lea    0x788(%rip),%rdx        # 3370 <barriered_thread>
    2be8:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    2bef:	49 83 c4 08          	add    $0x8,%r12
    2bf3:	48 83 c5 38          	add    $0x38,%rbp
    2bf7:	e8 54 f8 ff ff       	call   2450 <pthread_create@plt>
    2bfc:	83 fb 06             	cmp    $0x6,%ebx
    2bff:	75 af                	jne    2bb0 <main+0x650>
    2c01:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2c06:	48 8b 1d 03 3e 00 00 	mov    0x3e03(%rip),%rbx        # 6a10 <_IO_stdin_used+0xa10>
    2c0d:	be d8 00 00 00       	mov    $0xd8,%esi
    2c12:	bf 01 00 00 00       	mov    $0x1,%edi
    2c17:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    2c1c:	45 31 e4             	xor    %r12d,%r12d
    2c1f:	48 8d 6c 24 50       	lea    0x50(%rsp),%rbp
    2c24:	49 89 9a 50 04 00 00 	mov    %rbx,0x450(%r10)
    2c2b:	41 c7 82 2c 04 00 00 02 00 00 00 	movl   $0x2,0x42c(%r10)
    2c36:	e8 45 f7 ff ff       	call   2380 <calloc@plt>
    2c3b:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2c40:	be 00 08 00 00       	mov    $0x800,%esi
    2c45:	31 ff                	xor    %edi,%edi
    2c47:	49 89 82 68 04 00 00 	mov    %rax,0x468(%r10)
    2c4e:	e8 3d f8 ff ff       	call   2490 <eventfd@plt>
    2c53:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2c58:	ba 07 00 00 00       	mov    $0x7,%edx
    2c5d:	48 8d 35 a9 36 00 00 	lea    0x36a9(%rip),%rsi        # 630d <_IO_stdin_used+0x30d>
    2c64:	bf 01 00 00 00       	mov    $0x1,%edi
    2c69:	41 89 82 70 04 00 00 	mov    %eax,0x470(%r10)
    2c70:	31 c0                	xor    %eax,%eax
    2c72:	4d 89 92 38 04 00 00 	mov    %r10,0x438(%r10)
    2c79:	41 c7 82 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r10)
    2c84:	41 c7 82 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r10)
    2c8f:	e8 9c f7 ff ff       	call   2430 <__printf_chk@plt>
    2c94:	48 8b 34 24          	mov    (%rsp),%rsi
    2c98:	49 8d 7e 38          	lea    0x38(%r14),%rdi
    2c9c:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    2ca1:	48 8d 15 18 1d 00 00 	lea    0x1d18(%rip),%rdx        # 49c0 <io_thread>
    2ca8:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2caf:	e8 9c f7 ff ff       	call   2450 <pthread_create@plt>
    2cb4:	ba 08 00 00 00       	mov    $0x8,%edx
    2cb9:	48 8d 35 64 36 00 00 	lea    0x3664(%rip),%rsi        # 6324 <_IO_stdin_used+0x324>
    2cc0:	31 c0                	xor    %eax,%eax
    2cc2:	bf 01 00 00 00       	mov    $0x1,%edi
    2cc7:	e8 64 f7 ff ff       	call   2430 <__printf_chk@plt>
    2ccc:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2cd1:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    2cd6:	49 8d b7 c0 01 00 00 	lea    0x1c0(%r15),%rsi
    2cdd:	49 8d 7e 40          	lea    0x40(%r14),%rdi
    2ce1:	48 8d 15 78 09 00 00 	lea    0x978(%rip),%rdx        # 3660 <external_thread>
    2ce8:	49 89 82 f8 04 00 00 	mov    %rax,0x4f8(%r10)
    2cef:	48 8b 05 02 3d 00 00 	mov    0x3d02(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
    2cf6:	49 8d 8a c0 04 00 00 	lea    0x4c0(%r10),%rcx
    2cfd:	49 89 9a e8 04 00 00 	mov    %rbx,0x4e8(%r10)
    2d04:	48 8d 1d 54 36 00 00 	lea    0x3654(%rip),%rbx        # 635f <_IO_stdin_used+0x35f>
    2d0b:	49 89 82 d8 04 00 00 	mov    %rax,0x4d8(%r10)
    2d12:	48 8b 05 ff 3c 00 00 	mov    0x3cff(%rip),%rax        # 6a18 <_IO_stdin_used+0xa18>
    2d19:	4d 89 92 d0 04 00 00 	mov    %r10,0x4d0(%r10)
    2d20:	49 89 82 c0 04 00 00 	mov    %rax,0x4c0(%r10)
    2d27:	4c 89 14 24          	mov    %r10,(%rsp)
    2d2b:	e8 20 f7 ff ff       	call   2450 <pthread_create@plt>
    2d30:	48 8d 3d 0a 36 00 00 	lea    0x360a(%rip),%rdi        # 6341 <_IO_stdin_used+0x341>
    2d37:	e8 94 f5 ff ff       	call   22d0 <puts@plt>
    2d3c:	4c 8b 3c 24          	mov    (%rsp),%r15
    2d40:	4b 8b 3c e6          	mov    (%r14,%r12,8),%rdi
    2d44:	48 89 ee             	mov    %rbp,%rsi
    2d47:	e8 84 f7 ff ff       	call   24d0 <pthread_join@plt>
    2d4c:	44 89 e2             	mov    %r12d,%edx
    2d4f:	48 89 de             	mov    %rbx,%rsi
    2d52:	bf 01 00 00 00       	mov    $0x1,%edi
    2d57:	31 c0                	xor    %eax,%eax
    2d59:	49 83 c4 01          	add    $0x1,%r12
    2d5d:	e8 ce f6 ff ff       	call   2430 <__printf_chk@plt>
    2d62:	49 83 fc 09          	cmp    $0x9,%r12
    2d66:	75 d8                	jne    2d40 <main+0x7e0>
    2d68:	4d 89 fa             	mov    %r15,%r10
    2d6b:	31 ed                	xor    %ebp,%ebp
    2d6d:	31 c9                	xor    %ecx,%ecx
    2d6f:	45 31 db             	xor    %r11d,%r11d
    2d72:	45 31 c9             	xor    %r9d,%r9d
    2d75:	48 89 2c 24          	mov    %rbp,(%rsp)
    2d79:	45 31 e4             	xor    %r12d,%r12d
    2d7c:	31 db                	xor    %ebx,%ebx
    2d7e:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2d83:	4d 89 e6             	mov    %r12,%r14
    2d86:	49 bf db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r15
    2d90:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    2d95:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    2d9a:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    2d9f:	90                   	nop
    2da0:	49 63 45 08          	movslq 0x8(%r13),%rax
    2da4:	85 c0                	test   %eax,%eax
    2da6:	0f 8e a6 00 00 00    	jle    2e52 <main+0x8f2>
    2dac:	49 8b 4d 00          	mov    0x0(%r13),%rcx
    2db0:	48 8d 34 80          	lea    (%rax,%rax,4),%rsi
    2db4:	48 8b 2c 24          	mov    (%rsp),%rbp
    2db8:	48 c1 e6 07          	shl    $0x7,%rsi
    2dbc:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    2dc1:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    2dc6:	48 8d 91 08 01 00 00 	lea    0x108(%rcx),%rdx
    2dcd:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2dd2:	48 01 d6             	add    %rdx,%rsi
    2dd5:	0f 1f 00             	nopl   (%rax)
    2dd8:	4c 03 32             	add    (%rdx),%r14
    2ddb:	48 8b 82 20 01 00 00 	mov    0x120(%rdx),%rax
    2de2:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
    2de9:	4c 03 82 88 fd ff ff 	add    -0x278(%rdx),%r8
    2df0:	48 03 8a 98 fe ff ff 	add    -0x168(%rdx),%rcx
    2df7:	48 03 68 10          	add    0x10(%rax),%rbp
    2dfb:	48 03 58 18          	add    0x18(%rax),%rbx
    2dff:	48 03 68 30          	add    0x30(%rax),%rbp
    2e03:	48 03 58 38          	add    0x38(%rax),%rbx
    2e07:	48 03 68 50          	add    0x50(%rax),%rbp
    2e0b:	48 03 58 58          	add    0x58(%rax),%rbx
    2e0f:	48 03 68 70          	add    0x70(%rax),%rbp
    2e13:	48 03 58 78          	add    0x78(%rax),%rbx
    2e17:	48 03 a8 90 00 00 00 	add    0x90(%rax),%rbp
    2e1e:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
    2e25:	4c 03 8a a8 fe ff ff 	add    -0x158(%rdx),%r9
    2e2c:	48 03 a8 b0 00 00 00 	add    0xb0(%rax),%rbp
    2e33:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
    2e3a:	48 39 f2             	cmp    %rsi,%rdx
    2e3d:	75 99                	jne    2dd8 <main+0x878>
    2e3f:	48 89 2c 24          	mov    %rbp,(%rsp)
    2e43:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    2e48:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    2e4d:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    2e52:	45 31 e4             	xor    %r12d,%r12d
    2e55:	49 83 7d 50 00       	cmpq   $0x0,0x50(%r13)
    2e5a:	7e 73                	jle    2ecf <main+0x96f>
    2e5c:	4c 89 ed             	mov    %r13,%rbp
    2e5f:	49 89 dd             	mov    %rbx,%r13
    2e62:	4c 89 e3             	mov    %r12,%rbx
    2e65:	0f 1f 00             	nopl   (%rax)
    2e68:	48 8b 7d 30          	mov    0x30(%rbp),%rdi
    2e6c:	48 89 de             	mov    %rbx,%rsi
    2e6f:	48 83 c3 01          	add    $0x1,%rbx
    2e73:	48 c1 e6 04          	shl    $0x4,%rsi
    2e77:	48 01 f7             	add    %rsi,%rdi
    2e7a:	48 03 75 38          	add    0x38(%rbp),%rsi
    2e7e:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    2e82:	48 2b 57 08          	sub    0x8(%rdi),%rdx
    2e86:	48 89 d0             	mov    %rdx,%rax
    2e89:	49 f7 e7             	mul    %r15
    2e8c:	31 c0                	xor    %eax,%eax
    2e8e:	48 89 d1             	mov    %rdx,%rcx
    2e91:	48 8b 16             	mov    (%rsi),%rdx
    2e94:	48 8d 35 d8 34 00 00 	lea    0x34d8(%rip),%rsi        # 6373 <_IO_stdin_used+0x373>
    2e9b:	48 2b 17             	sub    (%rdi),%rdx
    2e9e:	48 c1 e9 12          	shr    $0x12,%rcx
    2ea2:	bf 01 00 00 00       	mov    $0x1,%edi
    2ea7:	e8 84 f5 ff ff       	call   2430 <__printf_chk@plt>
    2eac:	48 8b 55 40          	mov    0x40(%rbp),%rdx
    2eb0:	bf 01 00 00 00       	mov    $0x1,%edi
    2eb5:	31 c0                	xor    %eax,%eax
    2eb7:	48 8d 35 d3 34 00 00 	lea    0x34d3(%rip),%rsi        # 6391 <_IO_stdin_used+0x391>
    2ebe:	e8 6d f5 ff ff       	call   2430 <__printf_chk@plt>
    2ec3:	48 39 5d 50          	cmp    %rbx,0x50(%rbp)
    2ec7:	7f 9f                	jg     2e68 <main+0x908>
    2ec9:	4c 89 eb             	mov    %r13,%rbx
    2ecc:	49 89 ed             	mov    %rbp,%r13
    2ecf:	45 31 e4             	xor    %r12d,%r12d
    2ed2:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    2ed7:	0f 8e 93 00 00 00    	jle    2f70 <main+0xa10>
    2edd:	4c 89 e8             	mov    %r13,%rax
    2ee0:	49 89 dd             	mov    %rbx,%r13
    2ee3:	4c 89 e3             	mov    %r12,%rbx
    2ee6:	49 89 c4             	mov    %rax,%r12
    2ee9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    2ef0:	49 8b 44 24 58       	mov    0x58(%r12),%rax
    2ef5:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    2ef9:	48 83 ec 08          	sub    $0x8,%rsp
    2efd:	48 8d 35 ec 36 00 00 	lea    0x36ec(%rip),%rsi        # 65f0 <_IO_stdin_used+0x5f0>
    2f04:	bf 01 00 00 00       	mov    $0x1,%edi
    2f09:	48 83 c3 01          	add    $0x1,%rbx
    2f0d:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    2f11:	48 8b 69 18          	mov    0x18(%rcx),%rbp
    2f15:	48 2b 69 08          	sub    0x8(%rcx),%rbp
    2f19:	48 89 e8             	mov    %rbp,%rax
    2f1c:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    2f20:	4c 2b 01             	sub    (%rcx),%r8
    2f23:	49 f7 e7             	mul    %r15
    2f26:	8b 49 20             	mov    0x20(%rcx),%ecx
    2f29:	55                   	push   %rbp
    2f2a:	31 c0                	xor    %eax,%eax
    2f2c:	48 c1 ea 12          	shr    $0x12,%rdx
    2f30:	49 89 d1             	mov    %rdx,%r9
    2f33:	ba 06 00 00 00       	mov    $0x6,%edx
    2f38:	e8 f3 f4 ff ff       	call   2430 <__printf_chk@plt>
    2f3d:	48 8d 35 69 34 00 00 	lea    0x3469(%rip),%rsi        # 63ad <_IO_stdin_used+0x3ad>
    2f44:	bf 01 00 00 00       	mov    $0x1,%edi
    2f49:	48 b8 ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%rax
    2f53:	48 f7 e5             	mul    %rbp
    2f56:	31 c0                	xor    %eax,%eax
    2f58:	48 c1 ea 02          	shr    $0x2,%rdx
    2f5c:	e8 cf f4 ff ff       	call   2430 <__printf_chk@plt>
    2f61:	58                   	pop    %rax
    2f62:	5a                   	pop    %rdx
    2f63:	49 39 5c 24 68       	cmp    %rbx,0x68(%r12)
    2f68:	7f 86                	jg     2ef0 <main+0x990>
    2f6a:	4c 89 eb             	mov    %r13,%rbx
    2f6d:	4d 89 e5             	mov    %r12,%r13
    2f70:	49 8b 55 70          	mov    0x70(%r13),%rdx
    2f74:	48 8d 35 26 34 00 00 	lea    0x3426(%rip),%rsi        # 63a1 <_IO_stdin_used+0x3a1>
    2f7b:	bf 01 00 00 00       	mov    $0x1,%edi
    2f80:	31 c0                	xor    %eax,%eax
    2f82:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    2f89:	e8 a2 f4 ff ff       	call   2430 <__printf_chk@plt>
    2f8e:	4c 39 6c 24 20       	cmp    %r13,0x20(%rsp)
    2f93:	0f 85 07 fe ff ff    	jne    2da0 <main+0x840>
    2f99:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2f9e:	4c 8b 54 24 28       	mov    0x28(%rsp),%r10
    2fa3:	4c 89 f2             	mov    %r14,%rdx
    2fa6:	31 c0                	xor    %eax,%eax
    2fa8:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2fad:	bf 01 00 00 00       	mov    $0x1,%edi
    2fb2:	48 8b 2c 24          	mov    (%rsp),%rbp
    2fb6:	4d 89 f4             	mov    %r14,%r12
    2fb9:	48 8d 35 ff 33 00 00 	lea    0x33ff(%rip),%rsi        # 63bf <_IO_stdin_used+0x3bf>
    2fc0:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    2fc5:	49 bd 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%r13
    2fcf:	4c 89 0c 24          	mov    %r9,(%rsp)
    2fd3:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    2fd8:	e8 53 f4 ff ff       	call   2430 <__printf_chk@plt>
    2fdd:	bf 0a 00 00 00       	mov    $0xa,%edi
    2fe2:	e8 d9 f2 ff ff       	call   22c0 <putchar@plt>
    2fe7:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    2fec:	48 8d 35 e0 33 00 00 	lea    0x33e0(%rip),%rsi        # 63d3 <_IO_stdin_used+0x3d3>
    2ff3:	31 c0                	xor    %eax,%eax
    2ff5:	bf 01 00 00 00       	mov    $0x1,%edi
    2ffa:	49 8b 16             	mov    (%r14),%rdx
    2ffd:	e8 2e f4 ff ff       	call   2430 <__printf_chk@plt>
    3002:	48 8b 14 24          	mov    (%rsp),%rdx
    3006:	bf 01 00 00 00       	mov    $0x1,%edi
    300b:	31 c0                	xor    %eax,%eax
    300d:	48 8d 35 d4 33 00 00 	lea    0x33d4(%rip),%rsi        # 63e8 <_IO_stdin_used+0x3e8>
    3014:	e8 17 f4 ff ff       	call   2430 <__printf_chk@plt>
    3019:	bf 0a 00 00 00       	mov    $0xa,%edi
    301e:	e8 9d f2 ff ff       	call   22c0 <putchar@plt>
    3023:	49 8b 36             	mov    (%r14),%rsi
    3026:	bf 01 00 00 00       	mov    $0x1,%edi
    302b:	48 89 f0             	mov    %rsi,%rax
    302e:	49 f7 ed             	imul   %r13
    3031:	31 c0                	xor    %eax,%eax
    3033:	48 01 f2             	add    %rsi,%rdx
    3036:	48 c1 fe 3f          	sar    $0x3f,%rsi
    303a:	48 c1 fa 04          	sar    $0x4,%rdx
    303e:	48 29 f2             	sub    %rsi,%rdx
    3041:	48 8d 35 e0 35 00 00 	lea    0x35e0(%rip),%rsi        # 6628 <_IO_stdin_used+0x628>
    3048:	e8 e3 f3 ff ff       	call   2430 <__printf_chk@plt>
    304d:	49 8b 56 08          	mov    0x8(%r14),%rdx
    3051:	bf 01 00 00 00       	mov    $0x1,%edi
    3056:	31 c0                	xor    %eax,%eax
    3058:	48 8d 35 e9 35 00 00 	lea    0x35e9(%rip),%rsi        # 6648 <_IO_stdin_used+0x648>
    305f:	e8 cc f3 ff ff       	call   2430 <__printf_chk@plt>
    3064:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    3069:	bf 01 00 00 00       	mov    $0x1,%edi
    306e:	48 8d 35 fb 35 00 00 	lea    0x35fb(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    3075:	4c 89 d8             	mov    %r11,%rax
    3078:	49 f7 ed             	imul   %r13
    307b:	31 c0                	xor    %eax,%eax
    307d:	4c 01 da             	add    %r11,%rdx
    3080:	49 c1 fb 3f          	sar    $0x3f,%r11
    3084:	48 c1 fa 04          	sar    $0x4,%rdx
    3088:	4c 29 da             	sub    %r11,%rdx
    308b:	e8 a0 f3 ff ff       	call   2430 <__printf_chk@plt>
    3090:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3095:	bf 01 00 00 00       	mov    $0x1,%edi
    309a:	48 8d 35 ff 35 00 00 	lea    0x35ff(%rip),%rsi        # 66a0 <_IO_stdin_used+0x6a0>
    30a1:	48 89 c8             	mov    %rcx,%rax
    30a4:	49 f7 ed             	imul   %r13
    30a7:	31 c0                	xor    %eax,%eax
    30a9:	48 01 ca             	add    %rcx,%rdx
    30ac:	48 c1 f9 3f          	sar    $0x3f,%rcx
    30b0:	48 c1 fa 04          	sar    $0x4,%rdx
    30b4:	48 29 ca             	sub    %rcx,%rdx
    30b7:	e8 74 f3 ff ff       	call   2430 <__printf_chk@plt>
    30bc:	4c 89 e0             	mov    %r12,%rax
    30bf:	bf 01 00 00 00       	mov    $0x1,%edi
    30c4:	48 8d 35 05 36 00 00 	lea    0x3605(%rip),%rsi        # 66d0 <_IO_stdin_used+0x6d0>
    30cb:	49 f7 ed             	imul   %r13
    30ce:	4c 01 e2             	add    %r12,%rdx
    30d1:	49 c1 fc 3f          	sar    $0x3f,%r12
    30d5:	31 c0                	xor    %eax,%eax
    30d7:	48 c1 fa 04          	sar    $0x4,%rdx
    30db:	4c 29 e2             	sub    %r12,%rdx
    30de:	e8 4d f3 ff ff       	call   2430 <__printf_chk@plt>
    30e3:	48 89 e8             	mov    %rbp,%rax
    30e6:	bf 01 00 00 00       	mov    $0x1,%edi
    30eb:	48 8d 35 03 33 00 00 	lea    0x3303(%rip),%rsi        # 63f5 <_IO_stdin_used+0x3f5>
    30f2:	49 f7 ed             	imul   %r13
    30f5:	31 c0                	xor    %eax,%eax
    30f7:	48 01 ea             	add    %rbp,%rdx
    30fa:	48 c1 fd 3f          	sar    $0x3f,%rbp
    30fe:	48 c1 fa 04          	sar    $0x4,%rdx
    3102:	48 29 ea             	sub    %rbp,%rdx
    3105:	e8 26 f3 ff ff       	call   2430 <__printf_chk@plt>
    310a:	48 89 d8             	mov    %rbx,%rax
    310d:	bf 01 00 00 00       	mov    $0x1,%edi
    3112:	48 8d 35 ed 32 00 00 	lea    0x32ed(%rip),%rsi        # 6406 <_IO_stdin_used+0x406>
    3119:	49 f7 ed             	imul   %r13
    311c:	31 c0                	xor    %eax,%eax
    311e:	48 01 da             	add    %rbx,%rdx
    3121:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3125:	48 c1 fa 04          	sar    $0x4,%rdx
    3129:	48 29 da             	sub    %rbx,%rdx
    312c:	e8 ff f2 ff ff       	call   2430 <__printf_chk@plt>
    3131:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    3136:	be 06 00 00 00       	mov    $0x6,%esi
    313b:	e8 f0 25 00 00       	call   5730 <verify>
    3140:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    3145:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    314e:	75 4c                	jne    319c <main+0xc3c>
    3150:	48 83 c4 68          	add    $0x68,%rsp
    3154:	31 c0                	xor    %eax,%eax
    3156:	5b                   	pop    %rbx
    3157:	5d                   	pop    %rbp
    3158:	41 5c                	pop    %r12
    315a:	41 5d                	pop    %r13
    315c:	41 5e                	pop    %r14
    315e:	41 5f                	pop    %r15
    3160:	c3                   	ret
    3161:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3168:	48 8d 05 a1 20 00 00 	lea    0x20a1(%rip),%rax        # 5210 <barriered_work>
    316f:	41 be 06 00 00 00    	mov    $0x6,%r14d
    3175:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
    317d:	e9 59 f8 ff ff       	jmp    29db <main+0x47b>
    3182:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3188:	48 8d 05 11 01 00 00 	lea    0x111(%rip),%rax        # 32a0 <do_protected_write>
    318f:	4b 89 84 2f 20 01 00 00 	mov    %rax,0x120(%r15,%r13,1)
    3197:	e9 2b f6 ff ff       	jmp    27c7 <main+0x267>
    319c:	e8 6f f1 ff ff       	call   2310 <__stack_chk_fail@plt>
    31a1:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    31ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000031b0 <_start>:
    31b0:	f3 0f 1e fa          	endbr64
    31b4:	31 ed                	xor    %ebp,%ebp
    31b6:	49 89 d1             	mov    %rdx,%r9
    31b9:	5e                   	pop    %rsi
    31ba:	48 89 e2             	mov    %rsp,%rdx
    31bd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    31c1:	50                   	push   %rax
    31c2:	54                   	push   %rsp
    31c3:	45 31 c0             	xor    %r8d,%r8d
    31c6:	31 c9                	xor    %ecx,%ecx
    31c8:	48 8d 3d 91 f3 ff ff 	lea    -0xc6f(%rip),%rdi        # 2560 <main>
    31cf:	ff 15 03 5e 00 00    	call   *0x5e03(%rip)        # 8fd8 <__libc_start_main@GLIBC_2.34>
    31d5:	f4                   	hlt
    31d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000031e0 <deregister_tm_clones>:
    31e0:	48 8d 3d 39 5e 00 00 	lea    0x5e39(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    31e7:	48 8d 05 32 5e 00 00 	lea    0x5e32(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    31ee:	48 39 f8             	cmp    %rdi,%rax
    31f1:	74 15                	je     3208 <deregister_tm_clones+0x28>
    31f3:	48 8b 05 e6 5d 00 00 	mov    0x5de6(%rip),%rax        # 8fe0 <_ITM_deregisterTMCloneTable@Base>
    31fa:	48 85 c0             	test   %rax,%rax
    31fd:	74 09                	je     3208 <deregister_tm_clones+0x28>
    31ff:	ff e0                	jmp    *%rax
    3201:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3208:	c3                   	ret
    3209:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003210 <register_tm_clones>:
    3210:	48 8d 3d 09 5e 00 00 	lea    0x5e09(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3217:	48 8d 35 02 5e 00 00 	lea    0x5e02(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    321e:	48 29 fe             	sub    %rdi,%rsi
    3221:	48 89 f0             	mov    %rsi,%rax
    3224:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3228:	48 c1 f8 03          	sar    $0x3,%rax
    322c:	48 01 c6             	add    %rax,%rsi
    322f:	48 d1 fe             	sar    %rsi
    3232:	74 14                	je     3248 <register_tm_clones+0x38>
    3234:	48 8b 05 b5 5d 00 00 	mov    0x5db5(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    323b:	48 85 c0             	test   %rax,%rax
    323e:	74 08                	je     3248 <register_tm_clones+0x38>
    3240:	ff e0                	jmp    *%rax
    3242:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3248:	c3                   	ret
    3249:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003250 <__do_global_dtors_aux>:
    3250:	f3 0f 1e fa          	endbr64
    3254:	80 3d cd 5d 00 00 00 	cmpb   $0x0,0x5dcd(%rip)        # 9028 <completed.0>
    325b:	75 2b                	jne    3288 <__do_global_dtors_aux+0x38>
    325d:	55                   	push   %rbp
    325e:	48 83 3d 92 5d 00 00 00 	cmpq   $0x0,0x5d92(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    3266:	48 89 e5             	mov    %rsp,%rbp
    3269:	74 0c                	je     3277 <__do_global_dtors_aux+0x27>
    326b:	48 8b 3d 96 5d 00 00 	mov    0x5d96(%rip),%rdi        # 9008 <__dso_handle>
    3272:	e8 29 f0 ff ff       	call   22a0 <__cxa_finalize@plt>
    3277:	e8 64 ff ff ff       	call   31e0 <deregister_tm_clones>
    327c:	c6 05 a5 5d 00 00 01 	movb   $0x1,0x5da5(%rip)        # 9028 <completed.0>
    3283:	5d                   	pop    %rbp
    3284:	c3                   	ret
    3285:	0f 1f 00             	nopl   (%rax)
    3288:	c3                   	ret
    3289:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003290 <frame_dummy>:
    3290:	f3 0f 1e fa          	endbr64
    3294:	e9 77 ff ff ff       	jmp    3210 <register_tm_clones>
    3299:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000032a0 <do_protected_write>:
    32a0:	f3 0f 1e fa          	endbr64
    32a4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    32ab:	48 8b 40 30          	mov    0x30(%rax),%rax
    32af:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
    32b7:	48 8b 48 08          	mov    0x8(%rax),%rcx
    32bb:	48 83 00 01          	addq   $0x1,(%rax)
    32bf:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    32c6:	48 85 c9             	test   %rcx,%rcx
    32c9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    32d0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    32d4:	48 89 50 08          	mov    %rdx,0x8(%rax)
    32d8:	31 c0                	xor    %eax,%eax
    32da:	c3                   	ret
    32db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000032e0 <barriered_reset>:
    32e0:	f3 0f 1e fa          	endbr64
    32e4:	48 63 8f 84 01 00 00 	movslq 0x184(%rdi),%rcx
    32eb:	85 c9                	test   %ecx,%ecx
    32ed:	7e 6c                	jle    335b <barriered_reset+0x7b>
    32ef:	48 63 87 30 01 00 00 	movslq 0x130(%rdi),%rax
    32f6:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    32fd:	48 8d 0c 89          	lea    (%rcx,%rcx,4),%rcx
    3301:	48 c1 e1 07          	shl    $0x7,%rcx
    3305:	48 8d 3c c0          	lea    (%rax,%rax,8),%rdi
    3309:	49 8b 70 20          	mov    0x20(%r8),%rsi
    330d:	48 8d 04 78          	lea    (%rax,%rdi,2),%rax
    3311:	49 8b 78 10          	mov    0x10(%r8),%rdi
    3315:	48 8d 96 80 01 00 00 	lea    0x180(%rsi),%rdx
    331c:	48 8d 8c 0e 80 01 00 00 	lea    0x180(%rsi,%rcx,1),%rcx
    3324:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3328:	48 8b 40 20          	mov    0x20(%rax),%rax
    332c:	48 05 00 01 00 00    	add    $0x100,%rax
    3332:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3338:	83 40 80 01          	addl   $0x1,-0x80(%rax)
    333c:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
    3343:	83 00 01             	addl   $0x1,(%rax)
    3346:	48 05 80 02 00 00    	add    $0x280,%rax
    334c:	c7 82 80 fd ff ff 01 00 00 00 	movl   $0x1,-0x280(%rdx)
    3356:	48 39 ca             	cmp    %rcx,%rdx
    3359:	75 dd                	jne    3338 <barriered_reset+0x58>
    335b:	0f ae f0             	mfence
    335e:	31 c0                	xor    %eax,%eax
    3360:	c3                   	ret
    3361:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    336c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003370 <barriered_thread>:
    3370:	f3 0f 1e fa          	endbr64
    3374:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
    3378:	0f 85 d4 02 00 00    	jne    3652 <barriered_thread+0x2e2>
    337e:	41 57                	push   %r15
    3380:	41 56                	push   %r14
    3382:	45 31 f6             	xor    %r14d,%r14d
    3385:	41 55                	push   %r13
    3387:	45 31 ed             	xor    %r13d,%r13d
    338a:	41 54                	push   %r12
    338c:	49 89 fc             	mov    %rdi,%r12
    338f:	55                   	push   %rbp
    3390:	53                   	push   %rbx
    3391:	31 db                	xor    %ebx,%ebx
    3393:	48 83 ec 08          	sub    $0x8,%rsp
    3397:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    33a0:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    33a5:	39 da                	cmp    %ebx,%edx
    33a7:	7f 13                	jg     33bc <barriered_thread+0x4c>
    33a9:	49 83 84 24 90 00 00 00 01 	addq   $0x1,0x90(%r12)
    33b2:	31 db                	xor    %ebx,%ebx
    33b4:	85 d2                	test   %edx,%edx
    33b6:	0f 8e 74 01 00 00    	jle    3530 <barriered_thread+0x1c0>
    33bc:	48 63 c3             	movslq %ebx,%rax
    33bf:	48 8d 2c 80          	lea    (%rax,%rax,4),%rbp
    33c3:	48 c1 e5 07          	shl    $0x7,%rbp
    33c7:	eb 19                	jmp    33e2 <barriered_thread+0x72>
    33c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    33d0:	83 c3 01             	add    $0x1,%ebx
    33d3:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    33da:	39 d3                	cmp    %edx,%ebx
    33dc:	0f 8d 4e 01 00 00    	jge    3530 <barriered_thread+0x1c0>
    33e2:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    33e7:	48 8d 0c 28          	lea    (%rax,%rbp,1),%rcx
    33eb:	83 b9 80 01 00 00 01 	cmpl   $0x1,0x180(%rcx)
    33f2:	75 dc                	jne    33d0 <barriered_thread+0x60>
    33f4:	41 8b 7c 24 18       	mov    0x18(%r12),%edi
    33f9:	83 ea 01             	sub    $0x1,%edx
    33fc:	8d 73 ff             	lea    -0x1(%rbx),%esi
    33ff:	85 db                	test   %ebx,%ebx
    3401:	0f 4f d6             	cmovg  %esi,%edx
    3404:	85 ff                	test   %edi,%edi
    3406:	0f 8e 34 02 00 00    	jle    3640 <barriered_thread+0x2d0>
    340c:	48 63 d2             	movslq %edx,%rdx
    340f:	44 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9d
    3416:	45 31 d2             	xor    %r10d,%r10d
    3419:	45 31 ff             	xor    %r15d,%r15d
    341c:	48 8d 34 92          	lea    (%rdx,%rdx,4),%rsi
    3420:	48 63 d7             	movslq %edi,%rdx
    3423:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    342a:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    342f:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3433:	48 c1 e6 07          	shl    $0x7,%rsi
    3437:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
    343b:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    343f:	90                   	nop
    3440:	48 8b 50 20          	mov    0x20(%rax),%rdx
    3444:	48 01 f2             	add    %rsi,%rdx
    3447:	44 3b 8a 80 00 00 00 	cmp    0x80(%rdx),%r9d
    344e:	75 04                	jne    3454 <barriered_thread+0xe4>
    3450:	41 83 c7 01          	add    $0x1,%r15d
    3454:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    345b:	75 04                	jne    3461 <barriered_thread+0xf1>
    345d:	41 83 c2 01          	add    $0x1,%r10d
    3461:	48 05 98 00 00 00    	add    $0x98,%rax
    3467:	48 39 c8             	cmp    %rcx,%rax
    346a:	75 d4                	jne    3440 <barriered_thread+0xd0>
    346c:	44 39 d7             	cmp    %r10d,%edi
    346f:	0f 84 db 00 00 00    	je     3550 <barriered_thread+0x1e0>
    3475:	45 85 d2             	test   %r10d,%r10d
    3478:	0f 84 d2 00 00 00    	je     3550 <barriered_thread+0x1e0>
    347e:	45 85 ff             	test   %r15d,%r15d
    3481:	74 0b                	je     348e <barriered_thread+0x11e>
    3483:	45 39 7c 24 18       	cmp    %r15d,0x18(%r12)
    3488:	0f 85 a2 00 00 00    	jne    3530 <barriered_thread+0x1c0>
    348e:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3493:	48 01 e8             	add    %rbp,%rax
    3496:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
    349d:	85 db                	test   %ebx,%ebx
    349f:	75 10                	jne    34b1 <barriered_thread+0x141>
    34a1:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    34a6:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    34ab:	0f 8c 67 01 00 00    	jl     3618 <barriered_thread+0x2a8>
    34b1:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    34bb:	49 63 14 24          	movslq (%r12),%rdx
    34bf:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    34c3:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
    34c7:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
    34cc:	48 8d 14 d1          	lea    (%rcx,%rdx,8),%rdx
    34d0:	48 8b 7a 20          	mov    0x20(%rdx),%rdi
    34d4:	48 01 ef             	add    %rbp,%rdi
    34d7:	ff 90 18 01 00 00    	call   *0x118(%rax)
    34dd:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    34e2:	48 01 e8             	add    %rbp,%rax
    34e5:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
    34ec:	41 8b 44 24 28       	mov    0x28(%r12),%eax
    34f1:	49 83 44 24 60 01    	addq   $0x1,0x60(%r12)
    34f7:	83 e8 01             	sub    $0x1,%eax
    34fa:	39 d8                	cmp    %ebx,%eax
    34fc:	0f 84 a6 00 00 00    	je     35a8 <barriered_thread+0x238>
    3502:	0f ae f0             	mfence
    3505:	45 85 f6             	test   %r14d,%r14d
    3508:	0f 84 d2 00 00 00    	je     35e0 <barriered_thread+0x270>
    350e:	41 83 fe 03          	cmp    $0x3,%r14d
    3512:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    3517:	45 0f 44 f5          	cmove  %r13d,%r14d
    351b:	83 c3 01             	add    $0x1,%ebx
    351e:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    3525:	39 d3                	cmp    %edx,%ebx
    3527:	0f 8c b5 fe ff ff    	jl     33e2 <barriered_thread+0x72>
    352d:	0f 1f 00             	nopl   (%rax)
    3530:	41 83 7c 24 2c 01    	cmpl   $0x1,0x2c(%r12)
    3536:	0f 84 64 fe ff ff    	je     33a0 <barriered_thread+0x30>
    353c:	48 83 c4 08          	add    $0x8,%rsp
    3540:	31 c0                	xor    %eax,%eax
    3542:	5b                   	pop    %rbx
    3543:	5d                   	pop    %rbp
    3544:	41 5c                	pop    %r12
    3546:	41 5d                	pop    %r13
    3548:	41 5e                	pop    %r14
    354a:	41 5f                	pop    %r15
    354c:	c3                   	ret
    354d:	0f 1f 00             	nopl   (%rax)
    3550:	41 83 fe 01          	cmp    $0x1,%r14d
    3554:	0f 85 24 ff ff ff    	jne    347e <barriered_thread+0x10e>
    355a:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3562:	bf 04 00 00 00       	mov    $0x4,%edi
    3567:	41 be 03 00 00 00    	mov    $0x3,%r14d
    356d:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3571:	49 8b 44 24 78       	mov    0x78(%r12),%rax
    3576:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    357b:	e8 70 ed ff ff       	call   22f0 <clock_gettime@plt>
    3580:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3588:	48 83 c0 01          	add    $0x1,%rax
    358c:	48 99                	cqto
    358e:	49 f7 bc 24 88 00 00 00 	idivq  0x88(%r12)
    3596:	49 89 94 24 80 00 00 00 	mov    %rdx,0x80(%r12)
    359e:	e9 db fe ff ff       	jmp    347e <barriered_thread+0x10e>
    35a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    35a8:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    35ad:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    35b2:	0f 8d 4a ff ff ff    	jge    3502 <barriered_thread+0x192>
    35b8:	48 c1 e6 04          	shl    $0x4,%rsi
    35bc:	bf 04 00 00 00       	mov    $0x4,%edi
    35c1:	49 03 74 24 58       	add    0x58(%r12),%rsi
    35c6:	e8 25 ed ff ff       	call   22f0 <clock_gettime@plt>
    35cb:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
    35d1:	e9 2c ff ff ff       	jmp    3502 <barriered_thread+0x192>
    35d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    35e0:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    35e8:	bf 04 00 00 00       	mov    $0x4,%edi
    35ed:	41 be 01 00 00 00    	mov    $0x1,%r14d
    35f3:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    35f7:	49 8b 44 24 78       	mov    0x78(%r12),%rax
    35fc:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3600:	89 5e 20             	mov    %ebx,0x20(%rsi)
    3603:	e8 e8 ec ff ff       	call   22f0 <clock_gettime@plt>
    3608:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    360d:	e9 be fd ff ff       	jmp    33d0 <barriered_thread+0x60>
    3612:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3618:	48 c1 e6 04          	shl    $0x4,%rsi
    361c:	bf 04 00 00 00       	mov    $0x4,%edi
    3621:	49 03 74 24 50       	add    0x50(%r12),%rsi
    3626:	e8 c5 ec ff ff       	call   22f0 <clock_gettime@plt>
    362b:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3630:	48 01 e8             	add    %rbp,%rax
    3633:	e9 79 fe ff ff       	jmp    34b1 <barriered_thread+0x141>
    3638:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3640:	41 83 fe 01          	cmp    $0x1,%r14d
    3644:	0f 85 49 fe ff ff    	jne    3493 <barriered_thread+0x123>
    364a:	45 31 ff             	xor    %r15d,%r15d
    364d:	e9 08 ff ff ff       	jmp    355a <barriered_thread+0x1ea>
    3652:	31 c0                	xor    %eax,%eax
    3654:	c3                   	ret
    3655:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003660 <external_thread>:
    3660:	f3 0f 1e fa          	endbr64
    3664:	41 55                	push   %r13
    3666:	41 54                	push   %r12
    3668:	55                   	push   %rbp
    3669:	53                   	push   %rbx
    366a:	48 83 ec 38          	sub    $0x38,%rsp
    366e:	66 0f 6f 05 7a 32 00 00 	movdqa 0x327a(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    3676:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    367f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3684:	31 c0                	xor    %eax,%eax
    3686:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
    368a:	0f 29 04 24          	movaps %xmm0,(%rsp)
    368e:	75 64                	jne    36f4 <external_thread+0x94>
    3690:	49 89 fd             	mov    %rdi,%r13
    3693:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3698:	48 89 e3             	mov    %rsp,%rbx
    369b:	4c 8d 25 62 29 00 00 	lea    0x2962(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    36a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    36a8:	48 89 ee             	mov    %rbp,%rsi
    36ab:	48 89 df             	mov    %rbx,%rdi
    36ae:	e8 7d ec ff ff       	call   2330 <nanosleep@plt>
    36b3:	49 8b 45 38          	mov    0x38(%r13),%rax
    36b7:	48 63 10             	movslq (%rax),%rdx
    36ba:	85 d2                	test   %edx,%edx
    36bc:	7e 2c                	jle    36ea <external_thread+0x8a>
    36be:	48 8b 40 08          	mov    0x8(%rax),%rax
    36c2:	48 c1 e2 04          	shl    $0x4,%rdx
    36c6:	48 01 c2             	add    %rax,%rdx
    36c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    36d0:	8b 48 08             	mov    0x8(%rax),%ecx
    36d3:	85 c9                	test   %ecx,%ecx
    36d5:	75 0a                	jne    36e1 <external_thread+0x81>
    36d7:	4c 89 20             	mov    %r12,(%rax)
    36da:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    36e1:	48 83 c0 10          	add    $0x10,%rax
    36e5:	48 39 c2             	cmp    %rax,%rdx
    36e8:	75 e6                	jne    36d0 <external_thread+0x70>
    36ea:	0f ae f0             	mfence
    36ed:	41 83 7d 2c 01       	cmpl   $0x1,0x2c(%r13)
    36f2:	74 b4                	je     36a8 <external_thread+0x48>
    36f4:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    36f9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3702:	75 0d                	jne    3711 <external_thread+0xb1>
    3704:	48 83 c4 38          	add    $0x38,%rsp
    3708:	31 c0                	xor    %eax,%eax
    370a:	5b                   	pop    %rbx
    370b:	5d                   	pop    %rbp
    370c:	41 5c                	pop    %r12
    370e:	41 5d                	pop    %r13
    3710:	c3                   	ret
    3711:	e8 fa eb ff ff       	call   2310 <__stack_chk_fail@plt>
    3716:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003720 <timer_thread>:
    3720:	f3 0f 1e fa          	endbr64
    3724:	41 57                	push   %r15
    3726:	48 8d 35 e3 28 00 00 	lea    0x28e3(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    372d:	49 89 ff             	mov    %rdi,%r15
    3730:	41 56                	push   %r14
    3732:	41 55                	push   %r13
    3734:	41 54                	push   %r12
    3736:	55                   	push   %rbp
    3737:	53                   	push   %rbx
    3738:	48 83 ec 58          	sub    $0x58,%rsp
    373c:	8b 17                	mov    (%rdi),%edx
    373e:	bf 01 00 00 00       	mov    $0x1,%edi
    3743:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    374c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3751:	31 c0                	xor    %eax,%eax
    3753:	e8 d8 ec ff ff       	call   2430 <__printf_chk@plt>
    3758:	66 0f 6f 05 90 31 00 00 	movdqa 0x3190(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    3760:	ba 30 75 00 00       	mov    $0x7530,%edx
    3765:	31 c0                	xor    %eax,%eax
    3767:	48 8d 35 b4 28 00 00 	lea    0x28b4(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    376e:	bf 01 00 00 00       	mov    $0x1,%edi
    3773:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3778:	e8 b3 ec ff ff       	call   2430 <__printf_chk@plt>
    377d:	4d 63 77 2c          	movslq 0x2c(%r15),%r14
    3781:	45 85 f6             	test   %r14d,%r14d
    3784:	0f 84 b8 00 00 00    	je     3842 <timer_thread+0x122>
    378a:	45 31 ed             	xor    %r13d,%r13d
    378d:	45 31 f6             	xor    %r14d,%r14d
    3790:	48 89 e5             	mov    %rsp,%rbp
    3793:	45 31 e4             	xor    %r12d,%r12d
    3796:	48 8d 5c 24 10       	lea    0x10(%rsp),%rbx
    379b:	48 89 df             	mov    %rbx,%rdi
    379e:	48 89 ee             	mov    %rbp,%rsi
    37a1:	41 83 c5 01          	add    $0x1,%r13d
    37a5:	e8 86 eb ff ff       	call   2330 <nanosleep@plt>
    37aa:	45 8b 47 18          	mov    0x18(%r15),%r8d
    37ae:	41 8d 7e 01          	lea    0x1(%r14),%edi
    37b2:	45 85 c0             	test   %r8d,%r8d
    37b5:	7e 65                	jle    381c <timer_thread+0xfc>
    37b7:	4f 8d 04 b6          	lea    (%r14,%r14,4),%r8
    37bb:	31 c9                	xor    %ecx,%ecx
    37bd:	31 f6                	xor    %esi,%esi
    37bf:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    37c5:	49 c1 e0 07          	shl    $0x7,%r8
    37c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    37d0:	4d 8b 57 10          	mov    0x10(%r15),%r10
    37d4:	89 f8                	mov    %edi,%eax
    37d6:	99                   	cltd
    37d7:	49 01 ca             	add    %rcx,%r10
    37da:	41 f7 7a 28          	idivl  0x28(%r10)
    37de:	48 63 d2             	movslq %edx,%rdx
    37e1:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    37e5:	44 89 ca             	mov    %r9d,%edx
    37e8:	48 c1 e0 07          	shl    $0x7,%rax
    37ec:	49 03 42 20          	add    0x20(%r10),%rax
    37f0:	48 05 00 02 00 00    	add    $0x200,%rax
    37f6:	87 10                	xchg   %edx,(%rax)
    37f8:	49 8b 47 10          	mov    0x10(%r15),%rax
    37fc:	48 8b 44 08 20       	mov    0x20(%rax,%rcx,1),%rax
    3801:	44 89 e2             	mov    %r12d,%edx
    3804:	42 87 94 00 00 02 00 00 	xchg   %edx,0x200(%rax,%r8,1)
    380c:	83 c6 01             	add    $0x1,%esi
    380f:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3816:	41 39 77 18          	cmp    %esi,0x18(%r15)
    381a:	7f b4                	jg     37d0 <timer_thread+0xb0>
    381c:	0f ae f0             	mfence
    381f:	49 8b 47 10          	mov    0x10(%r15),%rax
    3823:	41 8b 77 2c          	mov    0x2c(%r15),%esi
    3827:	39 78 28             	cmp    %edi,0x28(%rax)
    382a:	41 0f 4e fc          	cmovle %r12d,%edi
    382e:	4c 63 f7             	movslq %edi,%r14
    3831:	85 f6                	test   %esi,%esi
    3833:	74 0d                	je     3842 <timer_thread+0x122>
    3835:	41 81 fd 30 75 00 00 	cmp    $0x7530,%r13d
    383c:	0f 85 59 ff ff ff    	jne    379b <timer_thread+0x7b>
    3842:	48 8d 3d ef 27 00 00 	lea    0x27ef(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    3849:	e8 82 ea ff ff       	call   22d0 <puts@plt>
    384e:	49 63 47 1c          	movslq 0x1c(%r15),%rax
    3852:	85 c0                	test   %eax,%eax
    3854:	7e 5f                	jle    38b5 <timer_thread+0x195>
    3856:	41 8b 57 28          	mov    0x28(%r15),%edx
    385a:	85 d2                	test   %edx,%edx
    385c:	7e 57                	jle    38b5 <timer_thread+0x195>
    385e:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    3862:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3866:	48 8d 34 48          	lea    (%rax,%rcx,2),%rsi
    386a:	48 63 c2             	movslq %edx,%rax
    386d:	31 c9                	xor    %ecx,%ecx
    386f:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3873:	48 c1 e6 03          	shl    $0x3,%rsi
    3877:	48 c1 e0 07          	shl    $0x7,%rax
    387b:	48 8d b8 38 02 00 00 	lea    0x238(%rax),%rdi
    3882:	49 8b 54 08 20       	mov    0x20(%r8,%rcx,1),%rdx
    3887:	48 8d 82 38 02 00 00 	lea    0x238(%rdx),%rax
    388e:	48 01 fa             	add    %rdi,%rdx
    3891:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3898:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    389e:	48 05 80 02 00 00    	add    $0x280,%rax
    38a4:	48 39 d0             	cmp    %rdx,%rax
    38a7:	75 ef                	jne    3898 <timer_thread+0x178>
    38a9:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    38b0:	48 39 f1             	cmp    %rsi,%rcx
    38b3:	75 cd                	jne    3882 <timer_thread+0x162>
    38b5:	0f ae f0             	mfence
    38b8:	66 0f 6f 05 40 30 00 00 	movdqa 0x3040(%rip),%xmm0        # 6900 <_IO_stdin_used+0x900>
    38c0:	48 8d 2d 96 27 00 00 	lea    0x2796(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    38c7:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    38cc:	41 8b 57 18          	mov    0x18(%r15),%edx
    38d0:	45 8d 6e 01          	lea    0x1(%r14),%r13d
    38d4:	85 d2                	test   %edx,%edx
    38d6:	7e 64                	jle    393c <timer_thread+0x21c>
    38d8:	4b 8d 3c b6          	lea    (%r14,%r14,4),%rdi
    38dc:	31 c9                	xor    %ecx,%ecx
    38de:	31 f6                	xor    %esi,%esi
    38e0:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    38e6:	48 c1 e7 07          	shl    $0x7,%rdi
    38ea:	45 31 c0             	xor    %r8d,%r8d
    38ed:	0f 1f 00             	nopl   (%rax)
    38f0:	4d 8b 57 10          	mov    0x10(%r15),%r10
    38f4:	44 89 e8             	mov    %r13d,%eax
    38f7:	44 89 cb             	mov    %r9d,%ebx
    38fa:	99                   	cltd
    38fb:	49 01 ca             	add    %rcx,%r10
    38fe:	41 f7 7a 28          	idivl  0x28(%r10)
    3902:	48 63 c2             	movslq %edx,%rax
    3905:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3909:	48 c1 e0 07          	shl    $0x7,%rax
    390d:	49 03 42 20          	add    0x20(%r10),%rax
    3911:	48 05 00 02 00 00    	add    $0x200,%rax
    3917:	87 18                	xchg   %ebx,(%rax)
    3919:	49 8b 47 10          	mov    0x10(%r15),%rax
    391d:	48 8b 44 08 20       	mov    0x20(%rax,%rcx,1),%rax
    3922:	44 89 c3             	mov    %r8d,%ebx
    3925:	87 9c 38 00 02 00 00 	xchg   %ebx,0x200(%rax,%rdi,1)
    392c:	83 c6 01             	add    $0x1,%esi
    392f:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3936:	41 39 77 18          	cmp    %esi,0x18(%r15)
    393a:	7f b4                	jg     38f0 <timer_thread+0x1d0>
    393c:	0f ae f0             	mfence
    393f:	49 8b 47 10          	mov    0x10(%r15),%rax
    3943:	44 39 68 28          	cmp    %r13d,0x28(%rax)
    3947:	7f 03                	jg     394c <timer_thread+0x22c>
    3949:	45 31 ed             	xor    %r13d,%r13d
    394c:	41 8b 7f 18          	mov    0x18(%r15),%edi
    3950:	85 ff                	test   %edi,%edi
    3952:	0f 8e b3 00 00 00    	jle    3a0b <timer_thread+0x2eb>
    3958:	31 db                	xor    %ebx,%ebx
    395a:	45 31 e4             	xor    %r12d,%r12d
    395d:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3963:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3968:	45 31 f6             	xor    %r14d,%r14d
    396b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3970:	85 ff                	test   %edi,%edi
    3972:	7e 5c                	jle    39d0 <timer_thread+0x2b0>
    3974:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3978:	4b 8d 04 b6          	lea    (%r14,%r14,4),%rax
    397c:	48 c1 e0 07          	shl    $0x7,%rax
    3980:	48 03 44 1a 20       	add    0x20(%rdx,%rbx,1),%rax
    3985:	31 d2                	xor    %edx,%edx
    3987:	48 8b 80 28 02 00 00 	mov    0x228(%rax),%rax
    398e:	eb 10                	jmp    39a0 <timer_thread+0x280>
    3990:	4d 85 c0             	test   %r8,%r8
    3993:	7f 25                	jg     39ba <timer_thread+0x29a>
    3995:	83 c2 01             	add    $0x1,%edx
    3998:	48 83 c0 20          	add    $0x20,%rax
    399c:	39 fa                	cmp    %edi,%edx
    399e:	74 30                	je     39d0 <timer_thread+0x2b0>
    39a0:	48 8b 08             	mov    (%rax),%rcx
    39a3:	48 8b 70 08          	mov    0x8(%rax),%rsi
    39a7:	48 8b 89 80 00 00 00 	mov    0x80(%rcx),%rcx
    39ae:	4c 8b 86 80 00 00 00 	mov    0x80(%rsi),%r8
    39b5:	48 85 c9             	test   %rcx,%rcx
    39b8:	7e d6                	jle    3990 <timer_thread+0x270>
    39ba:	bf 01 00 00 00       	mov    $0x1,%edi
    39bf:	48 89 ee             	mov    %rbp,%rsi
    39c2:	31 c0                	xor    %eax,%eax
    39c4:	e8 67 ea ff ff       	call   2430 <__printf_chk@plt>
    39c9:	41 8b 7f 18          	mov    0x18(%r15),%edi
    39cd:	45 31 c9             	xor    %r9d,%r9d
    39d0:	49 83 c6 01          	add    $0x1,%r14
    39d4:	44 39 f7             	cmp    %r14d,%edi
    39d7:	7f 97                	jg     3970 <timer_thread+0x250>
    39d9:	41 83 c4 01          	add    $0x1,%r12d
    39dd:	41 39 fc             	cmp    %edi,%r12d
    39e0:	7d 0c                	jge    39ee <timer_thread+0x2ce>
    39e2:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    39e9:	e9 7a ff ff ff       	jmp    3968 <timer_thread+0x248>
    39ee:	41 83 f9 01          	cmp    $0x1,%r9d
    39f2:	74 17                	je     3a0b <timer_thread+0x2eb>
    39f4:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    39f9:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    39fe:	4d 63 f5             	movslq %r13d,%r14
    3a01:	e8 2a e9 ff ff       	call   2330 <nanosleep@plt>
    3a06:	e9 c1 fe ff ff       	jmp    38cc <timer_thread+0x1ac>
    3a0b:	48 8d 3d 42 26 00 00 	lea    0x2642(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3a12:	e8 b9 e8 ff ff       	call   22d0 <puts@plt>
    3a17:	41 8b 4f 2c          	mov    0x2c(%r15),%ecx
    3a1b:	85 c9                	test   %ecx,%ecx
    3a1d:	0f 84 b0 00 00 00    	je     3ad3 <timer_thread+0x3b3>
    3a23:	41 8b 57 1c          	mov    0x1c(%r15),%edx
    3a27:	85 d2                	test   %edx,%edx
    3a29:	7e 38                	jle    3a63 <timer_thread+0x343>
    3a2b:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3a2f:	31 db                	xor    %ebx,%ebx
    3a31:	31 ed                	xor    %ebp,%ebp
    3a33:	4c 8d 25 34 26 00 00 	lea    0x2634(%rip),%r12        # 606e <_IO_stdin_used+0x6e>
    3a3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3a40:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    3a44:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
    3a48:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
    3a4f:	0f 84 ab 00 00 00    	je     3b00 <timer_thread+0x3e0>
    3a55:	83 c5 01             	add    $0x1,%ebp
    3a58:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3a5f:	39 d5                	cmp    %edx,%ebp
    3a61:	7c dd                	jl     3a40 <timer_thread+0x320>
    3a63:	41 8b 47 18          	mov    0x18(%r15),%eax
    3a67:	85 c0                	test   %eax,%eax
    3a69:	7e 51                	jle    3abc <timer_thread+0x39c>
    3a6b:	41 8b 47 28          	mov    0x28(%r15),%eax
    3a6f:	31 f6                	xor    %esi,%esi
    3a71:	45 31 c0             	xor    %r8d,%r8d
    3a74:	31 ff                	xor    %edi,%edi
    3a76:	85 c0                	test   %eax,%eax
    3a78:	7e 42                	jle    3abc <timer_thread+0x39c>
    3a7a:	31 d2                	xor    %edx,%edx
    3a7c:	0f 1f 40 00          	nopl   0x0(%rax)
    3a80:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3a84:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    3a88:	89 fb                	mov    %edi,%ebx
    3a8a:	48 c1 e0 07          	shl    $0x7,%rax
    3a8e:	48 03 44 31 20       	add    0x20(%rcx,%rsi,1),%rax
    3a93:	48 05 00 02 00 00    	add    $0x200,%rax
    3a99:	87 18                	xchg   %ebx,(%rax)
    3a9b:	41 8b 47 28          	mov    0x28(%r15),%eax
    3a9f:	48 83 c2 01          	add    $0x1,%rdx
    3aa3:	39 d0                	cmp    %edx,%eax
    3aa5:	7f d9                	jg     3a80 <timer_thread+0x360>
    3aa7:	41 83 c0 01          	add    $0x1,%r8d
    3aab:	45 3b 47 18          	cmp    0x18(%r15),%r8d
    3aaf:	7d 0b                	jge    3abc <timer_thread+0x39c>
    3ab1:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
    3ab8:	85 c0                	test   %eax,%eax
    3aba:	7f be                	jg     3a7a <timer_thread+0x35a>
    3abc:	0f ae f0             	mfence
    3abf:	48 8d 3d ba 25 00 00 	lea    0x25ba(%rip),%rdi        # 6080 <_IO_stdin_used+0x80>
    3ac6:	e8 05 e8 ff ff       	call   22d0 <puts@plt>
    3acb:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
    3ad3:	48 8d 3d ad 25 00 00 	lea    0x25ad(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3ada:	e8 f1 e7 ff ff       	call   22d0 <puts@plt>
    3adf:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3ae4:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3aed:	75 4a                	jne    3b39 <timer_thread+0x419>
    3aef:	48 83 c4 58          	add    $0x58,%rsp
    3af3:	31 c0                	xor    %eax,%eax
    3af5:	5b                   	pop    %rbx
    3af6:	5d                   	pop    %rbp
    3af7:	41 5c                	pop    %r12
    3af9:	41 5d                	pop    %r13
    3afb:	41 5e                	pop    %r14
    3afd:	41 5f                	pop    %r15
    3aff:	c3                   	ret
    3b00:	4c 89 e7             	mov    %r12,%rdi
    3b03:	83 c5 01             	add    $0x1,%ebp
    3b06:	e8 c5 e7 ff ff       	call   22d0 <puts@plt>
    3b0b:	49 8b 47 10          	mov    0x10(%r15),%rax
    3b0f:	be 01 00 00 00       	mov    $0x1,%esi
    3b14:	8b 7c 18 48          	mov    0x48(%rax,%rbx,1),%edi
    3b18:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3b1f:	e8 bc e8 ff ff       	call   23e0 <eventfd_write@plt>
    3b24:	41 8b 57 1c          	mov    0x1c(%r15),%edx
    3b28:	39 d5                	cmp    %edx,%ebp
    3b2a:	0f 8d 33 ff ff ff    	jge    3a63 <timer_thread+0x343>
    3b30:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3b34:	e9 07 ff ff ff       	jmp    3a40 <timer_thread+0x320>
    3b39:	e8 d2 e7 ff ff       	call   2310 <__stack_chk_fail@plt>
    3b3e:	66 90                	xchg   %ax,%ax

0000000000003b40 <fatal_error>:
    3b40:	f3 0f 1e fa          	endbr64
    3b44:	50                   	push   %rax
    3b45:	58                   	pop    %rax
    3b46:	48 83 ec 08          	sub    $0x8,%rsp
    3b4a:	e8 21 e9 ff ff       	call   2470 <perror@plt>
    3b4f:	bf 01 00 00 00       	mov    $0x1,%edi
    3b54:	e8 27 e9 ff ff       	call   2480 <exit@plt>
    3b59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003b60 <strtolower>:
    3b60:	f3 0f 1e fa          	endbr64
    3b64:	55                   	push   %rbp
    3b65:	53                   	push   %rbx
    3b66:	48 83 ec 08          	sub    $0x8,%rsp
    3b6a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3b6e:	84 db                	test   %bl,%bl
    3b70:	74 24                	je     3b96 <strtolower+0x36>
    3b72:	48 89 fd             	mov    %rdi,%rbp
    3b75:	e8 76 e9 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3b7a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3b80:	48 8b 10             	mov    (%rax),%rdx
    3b83:	48 83 c5 01          	add    $0x1,%rbp
    3b87:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3b8a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    3b8d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3b92:	84 db                	test   %bl,%bl
    3b94:	75 ea                	jne    3b80 <strtolower+0x20>
    3b96:	48 83 c4 08          	add    $0x8,%rsp
    3b9a:	5b                   	pop    %rbx
    3b9b:	5d                   	pop    %rbp
    3b9c:	c3                   	ret
    3b9d:	0f 1f 00             	nopl   (%rax)

0000000000003ba0 <zh_malloc>:
    3ba0:	f3 0f 1e fa          	endbr64
    3ba4:	48 83 ec 08          	sub    $0x8,%rsp
    3ba8:	e8 43 e8 ff ff       	call   23f0 <malloc@plt>
    3bad:	48 85 c0             	test   %rax,%rax
    3bb0:	74 05                	je     3bb7 <zh_malloc+0x17>
    3bb2:	48 83 c4 08          	add    $0x8,%rsp
    3bb6:	c3                   	ret
    3bb7:	48 8b 0d 62 54 00 00 	mov    0x5462(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3bbe:	ba 28 00 00 00       	mov    $0x28,%edx
    3bc3:	be 01 00 00 00       	mov    $0x1,%esi
    3bc8:	48 8d 3d 51 28 00 00 	lea    0x2851(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    3bcf:	e8 cc e8 ff ff       	call   24a0 <fwrite@plt>
    3bd4:	bf 01 00 00 00       	mov    $0x1,%edi
    3bd9:	e8 a2 e8 ff ff       	call   2480 <exit@plt>
    3bde:	66 90                	xchg   %ax,%ax

0000000000003be0 <get_filename_ext>:
    3be0:	f3 0f 1e fa          	endbr64
    3be4:	53                   	push   %rbx
    3be5:	be 2e 00 00 00       	mov    $0x2e,%esi
    3bea:	48 89 fb             	mov    %rdi,%rbx
    3bed:	e8 4e e7 ff ff       	call   2340 <strrchr@plt>
    3bf2:	48 85 c0             	test   %rax,%rax
    3bf5:	74 11                	je     3c08 <get_filename_ext+0x28>
    3bf7:	48 39 c3             	cmp    %rax,%rbx
    3bfa:	74 0c                	je     3c08 <get_filename_ext+0x28>
    3bfc:	48 83 c0 01          	add    $0x1,%rax
    3c00:	5b                   	pop    %rbx
    3c01:	c3                   	ret
    3c02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c08:	48 8d 05 c0 24 00 00 	lea    0x24c0(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
    3c0f:	5b                   	pop    %rbx
    3c10:	c3                   	ret
    3c11:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3c1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003c20 <send_headers>:
    3c20:	f3 0f 1e fa          	endbr64
    3c24:	41 55                	push   %r13
    3c26:	49 89 f5             	mov    %rsi,%r13
    3c29:	48 89 fe             	mov    %rdi,%rsi
    3c2c:	41 54                	push   %r12
    3c2e:	55                   	push   %rbp
    3c2f:	48 89 d5             	mov    %rdx,%rbp
    3c32:	ba 00 04 00 00       	mov    $0x400,%edx
    3c37:	53                   	push   %rbx
    3c38:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3c3f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3c48:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3c50:	31 c0                	xor    %eax,%eax
    3c52:	49 89 e4             	mov    %rsp,%r12
    3c55:	4c 89 e7             	mov    %r12,%rdi
    3c58:	e8 b3 e7 ff ff       	call   2410 <__strcpy_chk@plt>
    3c5d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3c62:	84 db                	test   %bl,%bl
    3c64:	74 24                	je     3c8a <send_headers+0x6a>
    3c66:	e8 85 e8 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3c6b:	48 8b 08             	mov    (%rax),%rcx
    3c6e:	4c 89 e0             	mov    %r12,%rax
    3c71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3c78:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    3c7b:	48 83 c0 01          	add    $0x1,%rax
    3c7f:	88 50 ff             	mov    %dl,-0x1(%rax)
    3c82:	48 0f be 18          	movsbq (%rax),%rbx
    3c86:	84 db                	test   %bl,%bl
    3c88:	75 ee                	jne    3c78 <send_headers+0x58>
    3c8a:	bf 11 00 00 00       	mov    $0x11,%edi
    3c8f:	e8 5c e7 ff ff       	call   23f0 <malloc@plt>
    3c94:	48 85 c0             	test   %rax,%rax
    3c97:	0f 84 7e 04 00 00    	je     411b <send_headers+0x4fb>
    3c9d:	66 0f 6f 05 6b 2c 00 00 	movdqa 0x2c6b(%rip),%xmm0        # 6910 <_IO_stdin_used+0x910>
    3ca5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    3ca9:	bf 17 00 00 00       	mov    $0x17,%edi
    3cae:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3cb6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3cba:	0f 11 00             	movups %xmm0,(%rax)
    3cbd:	e8 2e e7 ff ff       	call   23f0 <malloc@plt>
    3cc2:	48 85 c0             	test   %rax,%rax
    3cc5:	0f 84 50 04 00 00    	je     411b <send_headers+0x4fb>
    3ccb:	66 0f 6f 05 4d 2c 00 00 	movdqa 0x2c4d(%rip),%xmm0        # 6920 <_IO_stdin_used+0x920>
    3cd3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    3cd7:	4c 89 e7             	mov    %r12,%rdi
    3cda:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    3ce4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3cec:	0f 11 00             	movups %xmm0,(%rax)
    3cef:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    3cf3:	be 2e 00 00 00       	mov    $0x2e,%esi
    3cf8:	e8 43 e6 ff ff       	call   2340 <strrchr@plt>
    3cfd:	48 85 c0             	test   %rax,%rax
    3d00:	0f 84 ea 02 00 00    	je     3ff0 <send_headers+0x3d0>
    3d06:	4c 39 e0             	cmp    %r12,%rax
    3d09:	0f 84 e1 02 00 00    	je     3ff0 <send_headers+0x3d0>
    3d0f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    3d13:	48 8d 3d 83 23 00 00 	lea    0x2383(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3d1a:	48 89 de             	mov    %rbx,%rsi
    3d1d:	e8 6e e6 ff ff       	call   2390 <strcmp@plt>
    3d22:	85 c0                	test   %eax,%eax
    3d24:	75 20                	jne    3d46 <send_headers+0x126>
    3d26:	66 0f 6f 05 02 2c 00 00 	movdqa 0x2c02(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3d2e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3d36:	66 0f 6f 05 02 2c 00 00 	movdqa 0x2c02(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3d3e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3d46:	48 89 de             	mov    %rbx,%rsi
    3d49:	48 8d 3d 51 23 00 00 	lea    0x2351(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3d50:	e8 3b e6 ff ff       	call   2390 <strcmp@plt>
    3d55:	85 c0                	test   %eax,%eax
    3d57:	75 20                	jne    3d79 <send_headers+0x159>
    3d59:	66 0f 6f 05 cf 2b 00 00 	movdqa 0x2bcf(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3d61:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3d69:	66 0f 6f 05 cf 2b 00 00 	movdqa 0x2bcf(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3d71:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3d79:	48 89 de             	mov    %rbx,%rsi
    3d7c:	48 8d 3d 23 23 00 00 	lea    0x2323(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3d83:	e8 08 e6 ff ff       	call   2390 <strcmp@plt>
    3d88:	85 c0                	test   %eax,%eax
    3d8a:	0f 84 10 02 00 00    	je     3fa0 <send_headers+0x380>
    3d90:	48 89 de             	mov    %rbx,%rsi
    3d93:	48 8d 3d 10 23 00 00 	lea    0x2310(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3d9a:	e8 f1 e5 ff ff       	call   2390 <strcmp@plt>
    3d9f:	85 c0                	test   %eax,%eax
    3da1:	0f 84 a9 02 00 00    	je     4050 <send_headers+0x430>
    3da7:	48 89 de             	mov    %rbx,%rsi
    3daa:	48 8d 3d fd 22 00 00 	lea    0x22fd(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3db1:	e8 da e5 ff ff       	call   2390 <strcmp@plt>
    3db6:	85 c0                	test   %eax,%eax
    3db8:	0f 84 6a 02 00 00    	je     4028 <send_headers+0x408>
    3dbe:	48 89 de             	mov    %rbx,%rsi
    3dc1:	48 8d 3d 29 23 00 00 	lea    0x2329(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3dc8:	e8 c3 e5 ff ff       	call   2390 <strcmp@plt>
    3dcd:	85 c0                	test   %eax,%eax
    3dcf:	0f 84 2b 02 00 00    	je     4000 <send_headers+0x3e0>
    3dd5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3dd8:	0f 84 52 01 00 00    	je     3f30 <send_headers+0x310>
    3dde:	48 89 de             	mov    %rbx,%rsi
    3de1:	48 8d 3d ca 22 00 00 	lea    0x22ca(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3de8:	e8 a3 e5 ff ff       	call   2390 <strcmp@plt>
    3ded:	85 c0                	test   %eax,%eax
    3def:	0f 84 ab 02 00 00    	je     40a0 <send_headers+0x480>
    3df5:	48 89 de             	mov    %rbx,%rsi
    3df8:	48 8d 3d b7 22 00 00 	lea    0x22b7(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3dff:	e8 8c e5 ff ff       	call   2390 <strcmp@plt>
    3e04:	85 c0                	test   %eax,%eax
    3e06:	0f 84 6c 02 00 00    	je     4078 <send_headers+0x458>
    3e0c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3e14:	4c 89 e7             	mov    %r12,%rdi
    3e17:	e8 e4 e4 ff ff       	call   2300 <strlen@plt>
    3e1c:	48 89 c7             	mov    %rax,%rdi
    3e1f:	48 89 c3             	mov    %rax,%rbx
    3e22:	e8 c9 e5 ff ff       	call   23f0 <malloc@plt>
    3e27:	48 85 c0             	test   %rax,%rax
    3e2a:	0f 84 eb 02 00 00    	je     411b <send_headers+0x4fb>
    3e30:	48 89 45 20          	mov    %rax,0x20(%rbp)
    3e34:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    3e38:	83 fb 08             	cmp    $0x8,%ebx
    3e3b:	0f 83 3f 01 00 00    	jae    3f80 <send_headers+0x360>
    3e41:	f6 c3 04             	test   $0x4,%bl
    3e44:	0f 85 7b 02 00 00    	jne    40c5 <send_headers+0x4a5>
    3e4a:	85 db                	test   %ebx,%ebx
    3e4c:	74 13                	je     3e61 <send_headers+0x241>
    3e4e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3e56:	88 10                	mov    %dl,(%rax)
    3e58:	f6 c3 02             	test   $0x2,%bl
    3e5b:	0f 85 96 02 00 00    	jne    40f7 <send_headers+0x4d7>
    3e61:	4d 89 e8             	mov    %r13,%r8
    3e64:	48 8d 0d 4f 22 00 00 	lea    0x224f(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    3e6b:	4c 89 e7             	mov    %r12,%rdi
    3e6e:	31 c0                	xor    %eax,%eax
    3e70:	ba 00 04 00 00       	mov    $0x400,%edx
    3e75:	be 01 00 00 00       	mov    $0x1,%esi
    3e7a:	e8 81 e6 ff ff       	call   2500 <__sprintf_chk@plt>
    3e7f:	4c 89 e7             	mov    %r12,%rdi
    3e82:	e8 79 e4 ff ff       	call   2300 <strlen@plt>
    3e87:	48 89 c7             	mov    %rax,%rdi
    3e8a:	48 89 c3             	mov    %rax,%rbx
    3e8d:	e8 5e e5 ff ff       	call   23f0 <malloc@plt>
    3e92:	48 85 c0             	test   %rax,%rax
    3e95:	0f 84 80 02 00 00    	je     411b <send_headers+0x4fb>
    3e9b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    3e9f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    3ea3:	83 fb 08             	cmp    $0x8,%ebx
    3ea6:	0f 83 1c 01 00 00    	jae    3fc8 <send_headers+0x3a8>
    3eac:	f6 c3 04             	test   $0x4,%bl
    3eaf:	0f 85 29 02 00 00    	jne    40de <send_headers+0x4be>
    3eb5:	85 db                	test   %ebx,%ebx
    3eb7:	74 13                	je     3ecc <send_headers+0x2ac>
    3eb9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3ec1:	88 10                	mov    %dl,(%rax)
    3ec3:	f6 c3 02             	test   $0x2,%bl
    3ec6:	0f 85 3d 02 00 00    	jne    4109 <send_headers+0x4e9>
    3ecc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    3ed1:	bf 02 00 00 00       	mov    $0x2,%edi
    3ed6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    3ede:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    3ee6:	e8 05 e5 ff ff       	call   23f0 <malloc@plt>
    3eeb:	48 85 c0             	test   %rax,%rax
    3eee:	0f 84 27 02 00 00    	je     411b <send_headers+0x4fb>
    3ef4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    3efc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    3f00:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    3f08:	66 89 10             	mov    %dx,(%rax)
    3f0b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    3f13:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3f1c:	0f 85 20 02 00 00    	jne    4142 <send_headers+0x522>
    3f22:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    3f29:	5b                   	pop    %rbx
    3f2a:	5d                   	pop    %rbp
    3f2b:	41 5c                	pop    %r12
    3f2d:	41 5d                	pop    %r13
    3f2f:	c3                   	ret
    3f30:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    3f34:	0f 85 a4 fe ff ff    	jne    3dde <send_headers+0x1be>
    3f3a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    3f3e:	0f 85 9a fe ff ff    	jne    3dde <send_headers+0x1be>
    3f44:	66 0f 6f 05 44 2a 00 00 	movdqa 0x2a44(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    3f4c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    3f56:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3f5e:	66 0f 6f 05 3a 2a 00 00 	movdqa 0x2a3a(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    3f66:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    3f6e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    3f76:	e9 63 fe ff ff       	jmp    3dde <send_headers+0x1be>
    3f7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3f80:	89 da                	mov    %ebx,%edx
    3f82:	48 89 c7             	mov    %rax,%rdi
    3f85:	4c 89 e6             	mov    %r12,%rsi
    3f88:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    3f8d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    3f92:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3f95:	c1 e9 03             	shr    $0x3,%ecx
    3f98:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    3f9b:	e9 c1 fe ff ff       	jmp    3e61 <send_headers+0x241>
    3fa0:	66 0f 6f 05 88 29 00 00 	movdqa 0x2988(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3fa8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3fb0:	66 0f 6f 05 98 29 00 00 	movdqa 0x2998(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    3fb8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    3fc0:	e9 cb fd ff ff       	jmp    3d90 <send_headers+0x170>
    3fc5:	0f 1f 00             	nopl   (%rax)
    3fc8:	89 da                	mov    %ebx,%edx
    3fca:	48 89 c7             	mov    %rax,%rdi
    3fcd:	4c 89 e6             	mov    %r12,%rsi
    3fd0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    3fd5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    3fda:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3fdd:	c1 e9 03             	shr    $0x3,%ecx
    3fe0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    3fe3:	e9 e4 fe ff ff       	jmp    3ecc <send_headers+0x2ac>
    3fe8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3ff0:	48 8d 1d d8 20 00 00 	lea    0x20d8(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    3ff7:	e9 94 fd ff ff       	jmp    3d90 <send_headers+0x170>
    3ffc:	0f 1f 40 00          	nopl   0x0(%rax)
    4000:	66 0f 6f 05 68 29 00 00 	movdqa 0x2968(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4008:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4010:	66 0f 6f 05 68 29 00 00 	movdqa 0x2968(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4018:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4020:	e9 b0 fd ff ff       	jmp    3dd5 <send_headers+0x1b5>
    4025:	0f 1f 00             	nopl   (%rax)
    4028:	66 0f 6f 05 40 29 00 00 	movdqa 0x2940(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4030:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4038:	66 0f 6f 05 40 29 00 00 	movdqa 0x2940(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4040:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4048:	e9 71 fd ff ff       	jmp    3dbe <send_headers+0x19e>
    404d:	0f 1f 00             	nopl   (%rax)
    4050:	66 0f 6f 05 d8 28 00 00 	movdqa 0x28d8(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4058:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4060:	66 0f 6f 05 f8 28 00 00 	movdqa 0x28f8(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    4068:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4070:	e9 32 fd ff ff       	jmp    3da7 <send_headers+0x187>
    4075:	0f 1f 00             	nopl   (%rax)
    4078:	66 0f 6f 05 f0 28 00 00 	movdqa 0x28f0(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4080:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4088:	66 0f 6f 05 30 29 00 00 	movdqa 0x2930(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4090:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4098:	e9 6f fd ff ff       	jmp    3e0c <send_headers+0x1ec>
    409d:	0f 1f 00             	nopl   (%rax)
    40a0:	66 0f 6f 05 c8 28 00 00 	movdqa 0x28c8(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    40a8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40b0:	66 0f 6f 05 f8 28 00 00 	movdqa 0x28f8(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    40b8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    40c0:	e9 30 fd ff ff       	jmp    3df5 <send_headers+0x1d5>
    40c5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    40cc:	89 db                	mov    %ebx,%ebx
    40ce:	89 10                	mov    %edx,(%rax)
    40d0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    40d5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    40d9:	e9 83 fd ff ff       	jmp    3e61 <send_headers+0x241>
    40de:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    40e5:	89 db                	mov    %ebx,%ebx
    40e7:	89 10                	mov    %edx,(%rax)
    40e9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    40ee:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    40f2:	e9 d5 fd ff ff       	jmp    3ecc <send_headers+0x2ac>
    40f7:	89 db                	mov    %ebx,%ebx
    40f9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    40ff:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4104:	e9 58 fd ff ff       	jmp    3e61 <send_headers+0x241>
    4109:	89 db                	mov    %ebx,%ebx
    410b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4111:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4116:	e9 b1 fd ff ff       	jmp    3ecc <send_headers+0x2ac>
    411b:	48 8b 0d fe 4e 00 00 	mov    0x4efe(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4122:	ba 28 00 00 00       	mov    $0x28,%edx
    4127:	be 01 00 00 00       	mov    $0x1,%esi
    412c:	48 8d 3d ed 22 00 00 	lea    0x22ed(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    4133:	e8 68 e3 ff ff       	call   24a0 <fwrite@plt>
    4138:	bf 01 00 00 00       	mov    $0x1,%edi
    413d:	e8 3e e3 ff ff       	call   2480 <exit@plt>
    4142:	e8 c9 e1 ff ff       	call   2310 <__stack_chk_fail@plt>
    4147:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004150 <copy_file_contents>:
    4150:	f3 0f 1e fa          	endbr64
    4154:	41 55                	push   %r13
    4156:	49 89 d5             	mov    %rdx,%r13
    4159:	41 54                	push   %r12
    415b:	49 89 fc             	mov    %rdi,%r12
    415e:	48 89 f7             	mov    %rsi,%rdi
    4161:	55                   	push   %rbp
    4162:	53                   	push   %rbx
    4163:	48 89 f3             	mov    %rsi,%rbx
    4166:	48 83 ec 08          	sub    $0x8,%rsp
    416a:	e8 81 e2 ff ff       	call   23f0 <malloc@plt>
    416f:	48 85 c0             	test   %rax,%rax
    4172:	74 77                	je     41eb <copy_file_contents+0x9b>
    4174:	4c 89 e7             	mov    %r12,%rdi
    4177:	48 89 c5             	mov    %rax,%rbp
    417a:	31 f6                	xor    %esi,%esi
    417c:	31 c0                	xor    %eax,%eax
    417e:	e8 dd e2 ff ff       	call   2460 <open@plt>
    4183:	41 89 c4             	mov    %eax,%r12d
    4186:	85 c0                	test   %eax,%eax
    4188:	78 55                	js     41df <copy_file_contents+0x8f>
    418a:	48 89 da             	mov    %rbx,%rdx
    418d:	48 89 ee             	mov    %rbp,%rsi
    4190:	89 c7                	mov    %eax,%edi
    4192:	e8 d9 e1 ff ff       	call   2370 <read@plt>
    4197:	48 98                	cltq
    4199:	48 39 d8             	cmp    %rbx,%rax
    419c:	7c 22                	jl     41c0 <copy_file_contents+0x70>
    419e:	44 89 e7             	mov    %r12d,%edi
    41a1:	e8 aa e1 ff ff       	call   2350 <close@plt>
    41a6:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    41aa:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    41ae:	48 83 c4 08          	add    $0x8,%rsp
    41b2:	5b                   	pop    %rbx
    41b3:	5d                   	pop    %rbp
    41b4:	41 5c                	pop    %r12
    41b6:	41 5d                	pop    %r13
    41b8:	c3                   	ret
    41b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    41c0:	48 8b 0d 59 4e 00 00 	mov    0x4e59(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    41c7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    41cc:	be 01 00 00 00       	mov    $0x1,%esi
    41d1:	48 8d 3d f8 1e 00 00 	lea    0x1ef8(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    41d8:	e8 c3 e2 ff ff       	call   24a0 <fwrite@plt>
    41dd:	eb bf                	jmp    419e <copy_file_contents+0x4e>
    41df:	48 8d 3d 19 20 00 00 	lea    0x2019(%rip),%rdi        # 61ff <_IO_stdin_used+0x1ff>
    41e6:	e8 55 f9 ff ff       	call   3b40 <fatal_error>
    41eb:	48 8b 0d 2e 4e 00 00 	mov    0x4e2e(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    41f2:	ba 28 00 00 00       	mov    $0x28,%edx
    41f7:	be 01 00 00 00       	mov    $0x1,%esi
    41fc:	48 8d 3d 1d 22 00 00 	lea    0x221d(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    4203:	e8 98 e2 ff ff       	call   24a0 <fwrite@plt>
    4208:	bf 01 00 00 00       	mov    $0x1,%edi
    420d:	e8 6e e2 ff ff       	call   2480 <exit@plt>
    4212:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    421d:	0f 1f 00             	nopl   (%rax)

0000000000004220 <add_write_request>:
    4220:	f3 0f 1e fa          	endbr64
    4224:	8b 46 44             	mov    0x44(%rsi),%eax
    4227:	48 89 fa             	mov    %rdi,%rdx
    422a:	48 89 f7             	mov    %rsi,%rdi
    422d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    4233:	8d 70 01             	lea    0x1(%rax),%esi
    4236:	48 8b 07             	mov    (%rdi),%rax
    4239:	44 8b 00             	mov    (%rax),%r8d
    423c:	f6 c1 02             	test   $0x2,%cl
    423f:	74 00                	je     4241 <add_write_request+0x21>
    4241:	89 f0                	mov    %esi,%eax
    4243:	44 29 c0             	sub    %r8d,%eax
    4246:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4249:	0f 82 d1 e2 ff ff    	jb     2520 <add_write_request.cold>
    424f:	c1 e9 0a             	shr    $0xa,%ecx
    4252:	48 83 ec 08          	sub    $0x8,%rsp
    4256:	8b 47 44             	mov    0x44(%rdi),%eax
    4259:	23 47 58             	and    0x58(%rdi),%eax
    425c:	83 e1 01             	and    $0x1,%ecx
    425f:	89 77 44             	mov    %esi,0x44(%rdi)
    4262:	8b 72 08             	mov    0x8(%rdx),%esi
    4265:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4269:	d3 e0                	shl    %cl,%eax
    426b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    426e:	48 c1 e0 06          	shl    $0x6,%rax
    4272:	48 03 47 38          	add    0x38(%rdi),%rax
    4276:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    427c:	89 70 04             	mov    %esi,0x4(%rax)
    427f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    4283:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4289:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4291:	48 89 70 10          	mov    %rsi,0x10(%rax)
    4295:	89 48 18             	mov    %ecx,0x18(%rax)
    4298:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    429f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    42a7:	48 89 50 20          	mov    %rdx,0x20(%rax)
    42ab:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    42af:	e8 6c e0 ff ff       	call   2320 <io_uring_submit@plt>
    42b4:	31 c0                	xor    %eax,%eax
    42b6:	48 83 c4 08          	add    $0x8,%rsp
    42ba:	c3                   	ret
    42bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000042c0 <add_read_request>:
    42c0:	f3 0f 1e fa          	endbr64
    42c4:	41 55                	push   %r13
    42c6:	41 89 fd             	mov    %edi,%r13d
    42c9:	41 54                	push   %r12
    42cb:	55                   	push   %rbp
    42cc:	53                   	push   %rbx
    42cd:	48 89 f3             	mov    %rsi,%rbx
    42d0:	48 83 ec 08          	sub    $0x8,%rsp
    42d4:	8b 46 44             	mov    0x44(%rsi),%eax
    42d7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    42dd:	48 8b 16             	mov    (%rsi),%rdx
    42e0:	83 c0 01             	add    $0x1,%eax
    42e3:	8b 32                	mov    (%rdx),%esi
    42e5:	f6 c1 02             	test   $0x2,%cl
    42e8:	74 00                	je     42ea <add_read_request+0x2a>
    42ea:	89 c2                	mov    %eax,%edx
    42ec:	29 f2                	sub    %esi,%edx
    42ee:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    42f1:	0f 82 39 e2 ff ff    	jb     2530 <add_read_request.cold>
    42f7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    42fa:	c1 e9 0a             	shr    $0xa,%ecx
    42fd:	89 43 44             	mov    %eax,0x44(%rbx)
    4300:	bf 20 00 00 00       	mov    $0x20,%edi
    4305:	83 e1 01             	and    $0x1,%ecx
    4308:	23 6b 58             	and    0x58(%rbx),%ebp
    430b:	d3 e5                	shl    %cl,%ebp
    430d:	48 c1 e5 06          	shl    $0x6,%rbp
    4311:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4315:	e8 d6 e0 ff ff       	call   23f0 <malloc@plt>
    431a:	be 01 00 00 00       	mov    $0x1,%esi
    431f:	bf 00 20 00 00       	mov    $0x2000,%edi
    4324:	49 89 c4             	mov    %rax,%r12
    4327:	e8 54 e0 ff ff       	call   2380 <calloc@plt>
    432c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    4331:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4335:	48 89 df             	mov    %rbx,%rdi
    4338:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    433d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    4342:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    434b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    4353:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    4357:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    435b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    4362:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    436a:	48 89 45 10          	mov    %rax,0x10(%rbp)
    436e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    4376:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    437e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4382:	e8 99 df ff ff       	call   2320 <io_uring_submit@plt>
    4387:	48 83 c4 08          	add    $0x8,%rsp
    438b:	31 c0                	xor    %eax,%eax
    438d:	5b                   	pop    %rbx
    438e:	5d                   	pop    %rbp
    438f:	41 5c                	pop    %r12
    4391:	41 5d                	pop    %r13
    4393:	c3                   	ret
    4394:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    439f:	90                   	nop

00000000000043a0 <_send_static_string_content>:
    43a0:	f3 0f 1e fa          	endbr64
    43a4:	41 56                	push   %r14
    43a6:	41 89 f6             	mov    %esi,%r14d
    43a9:	41 55                	push   %r13
    43ab:	49 89 fd             	mov    %rdi,%r13
    43ae:	bf 20 00 00 00       	mov    $0x20,%edi
    43b3:	41 54                	push   %r12
    43b5:	55                   	push   %rbp
    43b6:	48 89 d5             	mov    %rdx,%rbp
    43b9:	53                   	push   %rbx
    43ba:	e8 31 e0 ff ff       	call   23f0 <malloc@plt>
    43bf:	48 85 c0             	test   %rax,%rax
    43c2:	0f 84 dd 00 00 00    	je     44a5 <_send_static_string_content+0x105>
    43c8:	48 89 c3             	mov    %rax,%rbx
    43cb:	4c 89 ef             	mov    %r13,%rdi
    43ce:	e8 2d df ff ff       	call   2300 <strlen@plt>
    43d3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    43da:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    43de:	48 89 c7             	mov    %rax,%rdi
    43e1:	49 89 c4             	mov    %rax,%r12
    43e4:	e8 07 e0 ff ff       	call   23f0 <malloc@plt>
    43e9:	48 89 c7             	mov    %rax,%rdi
    43ec:	48 85 c0             	test   %rax,%rax
    43ef:	0f 84 b0 00 00 00    	je     44a5 <_send_static_string_content+0x105>
    43f5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    43f9:	4c 89 e2             	mov    %r12,%rdx
    43fc:	4c 89 ee             	mov    %r13,%rsi
    43ff:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4403:	e8 b8 df ff ff       	call   23c0 <memcpy@plt>
    4408:	8b 45 44             	mov    0x44(%rbp),%eax
    440b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    4411:	8d 50 01             	lea    0x1(%rax),%edx
    4414:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4418:	8b 30                	mov    (%rax),%esi
    441a:	f6 c1 02             	test   $0x2,%cl
    441d:	0f 85 7d 00 00 00    	jne    44a0 <_send_static_string_content+0x100>
    4423:	89 d0                	mov    %edx,%eax
    4425:	29 f0                	sub    %esi,%eax
    4427:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    442a:	0f 82 0a e1 ff ff    	jb     253a <_send_static_string_content.cold>
    4430:	c1 e9 0a             	shr    $0xa,%ecx
    4433:	8b 45 44             	mov    0x44(%rbp),%eax
    4436:	23 45 58             	and    0x58(%rbp),%eax
    4439:	89 55 44             	mov    %edx,0x44(%rbp)
    443c:	83 e1 01             	and    $0x1,%ecx
    443f:	8b 53 04             	mov    0x4(%rbx),%edx
    4442:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    4448:	66 0f ef c0          	pxor   %xmm0,%xmm0
    444c:	d3 e0                	shl    %cl,%eax
    444e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    4451:	48 89 ef             	mov    %rbp,%rdi
    4454:	48 c1 e0 06          	shl    $0x6,%rax
    4458:	48 03 45 38          	add    0x38(%rbp),%rax
    445c:	89 48 04             	mov    %ecx,0x4(%rax)
    445f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    4463:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4469:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4471:	48 89 48 10          	mov    %rcx,0x10(%rax)
    4475:	89 50 18             	mov    %edx,0x18(%rax)
    4478:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    447f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4487:	48 89 58 20          	mov    %rbx,0x20(%rax)
    448b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    448f:	5b                   	pop    %rbx
    4490:	5d                   	pop    %rbp
    4491:	41 5c                	pop    %r12
    4493:	41 5d                	pop    %r13
    4495:	41 5e                	pop    %r14
    4497:	e9 84 de ff ff       	jmp    2320 <io_uring_submit@plt>
    449c:	0f 1f 40 00          	nopl   0x0(%rax)
    44a0:	e9 7e ff ff ff       	jmp    4423 <_send_static_string_content+0x83>
    44a5:	48 8b 0d 74 4b 00 00 	mov    0x4b74(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    44ac:	ba 28 00 00 00       	mov    $0x28,%edx
    44b1:	be 01 00 00 00       	mov    $0x1,%esi
    44b6:	48 8d 3d 63 1f 00 00 	lea    0x1f63(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    44bd:	e8 de df ff ff       	call   24a0 <fwrite@plt>
    44c2:	bf 01 00 00 00       	mov    $0x1,%edi
    44c7:	e8 b4 df ff ff       	call   2480 <exit@plt>
    44cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000044d0 <handle_unimplemented_method>:
    44d0:	f3 0f 1e fa          	endbr64
    44d4:	48 89 f2             	mov    %rsi,%rdx
    44d7:	89 fe                	mov    %edi,%esi
    44d9:	48 8b 3d 38 4b 00 00 	mov    0x4b38(%rip),%rdi        # 9018 <unimplemented_content>
    44e0:	e9 bb fe ff ff       	jmp    43a0 <_send_static_string_content>
    44e5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000044f0 <handle_http_404>:
    44f0:	f3 0f 1e fa          	endbr64
    44f4:	48 89 f2             	mov    %rsi,%rdx
    44f7:	89 fe                	mov    %edi,%esi
    44f9:	48 8b 3d 10 4b 00 00 	mov    0x4b10(%rip),%rdi        # 9010 <http_404_content>
    4500:	e9 9b fe ff ff       	jmp    43a0 <_send_static_string_content>
    4505:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004510 <handle_get_method>:
    4510:	f3 0f 1e fa          	endbr64
    4514:	41 56                	push   %r14
    4516:	41 55                	push   %r13
    4518:	49 89 d5             	mov    %rdx,%r13
    451b:	41 54                	push   %r12
    451d:	41 89 f4             	mov    %esi,%r12d
    4520:	55                   	push   %rbp
    4521:	48 89 fd             	mov    %rdi,%rbp
    4524:	53                   	push   %rbx
    4525:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    452c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4535:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    453d:	31 c0                	xor    %eax,%eax
    453f:	e8 bc dd ff ff       	call   2300 <strlen@plt>
    4544:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4549:	48 89 c3             	mov    %rax,%rbx
    454c:	0f 84 b6 00 00 00    	je     4608 <handle_get_method+0xf8>
    4552:	b8 69 63 00 00       	mov    $0x6369,%eax
    4557:	48 89 ee             	mov    %rbp,%rsi
    455a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    455e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4563:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    456b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4573:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    457e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    4586:	e8 15 de ff ff       	call   23a0 <__memcpy_chk@plt>
    458b:	48 89 e6             	mov    %rsp,%rsi
    458e:	4c 89 f7             	mov    %r14,%rdi
    4591:	e8 1a de ff ff       	call   23b0 <stat@plt>
    4596:	83 f8 ff             	cmp    $0xffffffff,%eax
    4599:	0f 84 d3 00 00 00    	je     4672 <handle_get_method+0x162>
    459f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    45a3:	25 00 f0 00 00       	and    $0xf000,%eax
    45a8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    45ad:	0f 84 f5 00 00 00    	je     46a8 <handle_get_method+0x198>
    45b3:	48 8b 3d 56 4a 00 00 	mov    0x4a56(%rip),%rdi        # 9010 <http_404_content>
    45ba:	4c 89 ea             	mov    %r13,%rdx
    45bd:	44 89 e6             	mov    %r12d,%esi
    45c0:	e8 db fd ff ff       	call   43a0 <_send_static_string_content>
    45c5:	4c 89 f2             	mov    %r14,%rdx
    45c8:	bf 01 00 00 00       	mov    $0x1,%edi
    45cd:	31 c0                	xor    %eax,%eax
    45cf:	48 8d 35 4a 1b 00 00 	lea    0x1b4a(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    45d6:	e8 55 de ff ff       	call   2430 <__printf_chk@plt>
    45db:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    45e3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    45ec:	0f 85 20 01 00 00    	jne    4712 <handle_get_method+0x202>
    45f2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    45f9:	5b                   	pop    %rbx
    45fa:	5d                   	pop    %rbp
    45fb:	41 5c                	pop    %r12
    45fd:	41 5d                	pop    %r13
    45ff:	41 5e                	pop    %r14
    4601:	c3                   	ret
    4602:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4608:	ba 69 63 00 00       	mov    $0x6369,%edx
    460d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4615:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    461a:	48 89 ee             	mov    %rbp,%rsi
    461d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    4625:	48 89 c2             	mov    %rax,%rdx
    4628:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4630:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    463b:	e8 60 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    4640:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4645:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    464a:	48 8d 35 9a 1a 00 00 	lea    0x1a9a(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    4651:	48 29 d9             	sub    %rbx,%rcx
    4654:	ba 0b 00 00 00       	mov    $0xb,%edx
    4659:	e8 42 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    465e:	48 89 e6             	mov    %rsp,%rsi
    4661:	4c 89 f7             	mov    %r14,%rdi
    4664:	e8 47 dd ff ff       	call   23b0 <stat@plt>
    4669:	83 f8 ff             	cmp    $0xffffffff,%eax
    466c:	0f 85 2d ff ff ff    	jne    459f <handle_get_method+0x8f>
    4672:	4c 89 f2             	mov    %r14,%rdx
    4675:	48 89 e9             	mov    %rbp,%rcx
    4678:	48 8d 35 77 1a 00 00 	lea    0x1a77(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    467f:	31 c0                	xor    %eax,%eax
    4681:	bf 01 00 00 00       	mov    $0x1,%edi
    4686:	e8 a5 dd ff ff       	call   2430 <__printf_chk@plt>
    468b:	48 8b 3d 7e 49 00 00 	mov    0x497e(%rip),%rdi        # 9010 <http_404_content>
    4692:	4c 89 ea             	mov    %r13,%rdx
    4695:	44 89 e6             	mov    %r12d,%esi
    4698:	e8 03 fd ff ff       	call   43a0 <_send_static_string_content>
    469d:	e9 39 ff ff ff       	jmp    45db <handle_get_method+0xcb>
    46a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    46a8:	bf 70 00 00 00       	mov    $0x70,%edi
    46ad:	e8 3e dd ff ff       	call   23f0 <malloc@plt>
    46b2:	48 89 c3             	mov    %rax,%rbx
    46b5:	48 85 c0             	test   %rax,%rax
    46b8:	74 5d                	je     4717 <handle_get_method+0x207>
    46ba:	44 89 60 08          	mov    %r12d,0x8(%rax)
    46be:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    46c3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    46c7:	4c 89 f7             	mov    %r14,%rdi
    46ca:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    46d1:	e8 4a f5 ff ff       	call   3c20 <send_headers>
    46d6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    46db:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    46df:	4c 89 f7             	mov    %r14,%rdi
    46e2:	e8 69 fa ff ff       	call   4150 <copy_file_contents>
    46e7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    46ec:	4c 89 f2             	mov    %r14,%rdx
    46ef:	31 c0                	xor    %eax,%eax
    46f1:	48 8d 35 16 1a 00 00 	lea    0x1a16(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    46f8:	bf 01 00 00 00       	mov    $0x1,%edi
    46fd:	e8 2e dd ff ff       	call   2430 <__printf_chk@plt>
    4702:	4c 89 ee             	mov    %r13,%rsi
    4705:	48 89 df             	mov    %rbx,%rdi
    4708:	e8 13 fb ff ff       	call   4220 <add_write_request>
    470d:	e9 c9 fe ff ff       	jmp    45db <handle_get_method+0xcb>
    4712:	e8 f9 db ff ff       	call   2310 <__stack_chk_fail@plt>
    4717:	48 8b 0d 02 49 00 00 	mov    0x4902(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    471e:	ba 28 00 00 00       	mov    $0x28,%edx
    4723:	be 01 00 00 00       	mov    $0x1,%esi
    4728:	48 8d 3d f1 1c 00 00 	lea    0x1cf1(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    472f:	e8 6c dd ff ff       	call   24a0 <fwrite@plt>
    4734:	bf 01 00 00 00       	mov    $0x1,%edi
    4739:	e8 42 dd ff ff       	call   2480 <exit@plt>
    473e:	66 90                	xchg   %ax,%ax

0000000000004740 <handle_http_method>:
    4740:	f3 0f 1e fa          	endbr64
    4744:	41 57                	push   %r15
    4746:	41 56                	push   %r14
    4748:	4c 8d 35 36 19 00 00 	lea    0x1936(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
    474f:	41 55                	push   %r13
    4751:	49 89 d5             	mov    %rdx,%r13
    4754:	41 54                	push   %r12
    4756:	41 89 f4             	mov    %esi,%r12d
    4759:	4c 89 f6             	mov    %r14,%rsi
    475c:	55                   	push   %rbp
    475d:	53                   	push   %rbx
    475e:	48 83 ec 18          	sub    $0x18,%rsp
    4762:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    476b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4770:	31 c0                	xor    %eax,%eax
    4772:	49 89 e7             	mov    %rsp,%r15
    4775:	4c 89 fa             	mov    %r15,%rdx
    4778:	e8 e3 db ff ff       	call   2360 <strtok_r@plt>
    477d:	48 0f be 18          	movsbq (%rax),%rbx
    4781:	48 89 c5             	mov    %rax,%rbp
    4784:	84 db                	test   %bl,%bl
    4786:	74 1d                	je     47a5 <handle_http_method+0x65>
    4788:	e8 63 dd ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    478d:	48 89 ea             	mov    %rbp,%rdx
    4790:	48 8b 08             	mov    (%rax),%rcx
    4793:	48 83 c2 01          	add    $0x1,%rdx
    4797:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    479a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    479d:	48 0f be 1a          	movsbq (%rdx),%rbx
    47a1:	84 db                	test   %bl,%bl
    47a3:	75 eb                	jne    4790 <handle_http_method+0x50>
    47a5:	4c 89 fa             	mov    %r15,%rdx
    47a8:	4c 89 f6             	mov    %r14,%rsi
    47ab:	31 ff                	xor    %edi,%edi
    47ad:	e8 ae db ff ff       	call   2360 <strtok_r@plt>
    47b2:	48 8d 35 7a 19 00 00 	lea    0x197a(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    47b9:	48 89 ef             	mov    %rbp,%rdi
    47bc:	48 89 c3             	mov    %rax,%rbx
    47bf:	e8 cc db ff ff       	call   2390 <strcmp@plt>
    47c4:	4c 89 ea             	mov    %r13,%rdx
    47c7:	44 89 e6             	mov    %r12d,%esi
    47ca:	85 c0                	test   %eax,%eax
    47cc:	75 2a                	jne    47f8 <handle_http_method+0xb8>
    47ce:	48 89 df             	mov    %rbx,%rdi
    47d1:	e8 3a fd ff ff       	call   4510 <handle_get_method>
    47d6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    47db:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    47e4:	75 20                	jne    4806 <handle_http_method+0xc6>
    47e6:	48 83 c4 18          	add    $0x18,%rsp
    47ea:	5b                   	pop    %rbx
    47eb:	5d                   	pop    %rbp
    47ec:	41 5c                	pop    %r12
    47ee:	41 5d                	pop    %r13
    47f0:	41 5e                	pop    %r14
    47f2:	41 5f                	pop    %r15
    47f4:	c3                   	ret
    47f5:	0f 1f 00             	nopl   (%rax)
    47f8:	48 8b 3d 19 48 00 00 	mov    0x4819(%rip),%rdi        # 9018 <unimplemented_content>
    47ff:	e8 9c fb ff ff       	call   43a0 <_send_static_string_content>
    4804:	eb d0                	jmp    47d6 <handle_http_method+0x96>
    4806:	e8 05 db ff ff       	call   2310 <__stack_chk_fail@plt>
    480b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004810 <get_line>:
    4810:	f3 0f 1e fa          	endbr64
    4814:	85 d2                	test   %edx,%edx
    4816:	7e 38                	jle    4850 <get_line+0x40>
    4818:	48 63 d2             	movslq %edx,%rdx
    481b:	48 83 c7 01          	add    $0x1,%rdi
    481f:	48 01 f2             	add    %rsi,%rdx
    4822:	eb 11                	jmp    4835 <get_line+0x25>
    4824:	0f 1f 40 00          	nopl   0x0(%rax)
    4828:	48 83 c6 01          	add    $0x1,%rsi
    482c:	48 83 c7 01          	add    $0x1,%rdi
    4830:	48 39 d6             	cmp    %rdx,%rsi
    4833:	74 1b                	je     4850 <get_line+0x40>
    4835:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4839:	88 06                	mov    %al,(%rsi)
    483b:	3c 0d                	cmp    $0xd,%al
    483d:	75 e9                	jne    4828 <get_line+0x18>
    483f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4842:	75 e4                	jne    4828 <get_line+0x18>
    4844:	c6 06 00             	movb   $0x0,(%rsi)
    4847:	31 c0                	xor    %eax,%eax
    4849:	c3                   	ret
    484a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4850:	b8 01 00 00 00       	mov    $0x1,%eax
    4855:	c3                   	ret
    4856:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004860 <handle_client_request>:
    4860:	f3 0f 1e fa          	endbr64
    4864:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    486b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    486f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4878:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4880:	31 c0                	xor    %eax,%eax
    4882:	49 89 e2             	mov    %rsp,%r10
    4885:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    488d:	4c 89 d0             	mov    %r10,%rax
    4890:	eb 13                	jmp    48a5 <handle_client_request+0x45>
    4892:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4898:	48 83 c0 01          	add    $0x1,%rax
    489c:	48 83 c1 01          	add    $0x1,%rcx
    48a0:	4c 39 c8             	cmp    %r9,%rax
    48a3:	74 4b                	je     48f0 <handle_client_request+0x90>
    48a5:	44 0f b6 01          	movzbl (%rcx),%r8d
    48a9:	44 88 00             	mov    %r8b,(%rax)
    48ac:	41 80 f8 0d          	cmp    $0xd,%r8b
    48b0:	75 e6                	jne    4898 <handle_client_request+0x38>
    48b2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    48b6:	75 e0                	jne    4898 <handle_client_request+0x38>
    48b8:	c6 00 00             	movb   $0x0,(%rax)
    48bb:	8b 47 08             	mov    0x8(%rdi),%eax
    48be:	48 89 f2             	mov    %rsi,%rdx
    48c1:	4c 89 d7             	mov    %r10,%rdi
    48c4:	89 c6                	mov    %eax,%esi
    48c6:	e8 75 fe ff ff       	call   4740 <handle_http_method>
    48cb:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    48d3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    48dc:	75 39                	jne    4917 <handle_client_request+0xb7>
    48de:	31 c0                	xor    %eax,%eax
    48e0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    48e7:	c3                   	ret
    48e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    48f0:	48 8b 0d 29 47 00 00 	mov    0x4729(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    48f7:	ba 12 00 00 00       	mov    $0x12,%edx
    48fc:	be 01 00 00 00       	mov    $0x1,%esi
    4901:	48 8d 3d 2f 18 00 00 	lea    0x182f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    4908:	e8 93 db ff ff       	call   24a0 <fwrite@plt>
    490d:	bf 01 00 00 00       	mov    $0x1,%edi
    4912:	e8 69 db ff ff       	call   2480 <exit@plt>
    4917:	e8 f4 d9 ff ff       	call   2310 <__stack_chk_fail@plt>
    491c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004920 <add_accept_request>:
    4920:	f3 0f 1e fa          	endbr64
    4924:	55                   	push   %rbp
    4925:	53                   	push   %rbx
    4926:	48 89 cb             	mov    %rcx,%rbx
    4929:	48 83 ec 08          	sub    $0x8,%rsp
    492d:	8b 41 44             	mov    0x44(%rcx),%eax
    4930:	4c 8b 03             	mov    (%rbx),%r8
    4933:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    4939:	83 c0 01             	add    $0x1,%eax
    493c:	45 8b 08             	mov    (%r8),%r9d
    493f:	f6 c1 02             	test   $0x2,%cl
    4942:	74 00                	je     4944 <add_accept_request+0x24>
    4944:	41 89 c0             	mov    %eax,%r8d
    4947:	45 29 c8             	sub    %r9d,%r8d
    494a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    494e:	0f 82 f6 db ff ff    	jb     254a <add_accept_request.cold>
    4954:	c1 e9 0a             	shr    $0xa,%ecx
    4957:	8b 6b 44             	mov    0x44(%rbx),%ebp
    495a:	23 6b 58             	and    0x58(%rbx),%ebp
    495d:	89 43 44             	mov    %eax,0x44(%rbx)
    4960:	83 e1 01             	and    $0x1,%ecx
    4963:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4967:	d3 e5                	shl    %cl,%ebp
    4969:	48 c1 e5 06          	shl    $0x6,%rbp
    496d:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4971:	89 7d 04             	mov    %edi,0x4(%rbp)
    4974:	bf 10 00 00 00       	mov    $0x10,%edi
    4979:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    4980:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    4984:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    4988:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    4990:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    4998:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    499c:	e8 4f da ff ff       	call   23f0 <malloc@plt>
    49a1:	48 89 df             	mov    %rbx,%rdi
    49a4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    49aa:	48 89 45 20          	mov    %rax,0x20(%rbp)
    49ae:	48 83 c4 08          	add    $0x8,%rsp
    49b2:	5b                   	pop    %rbx
    49b3:	5d                   	pop    %rbp
    49b4:	e9 67 d9 ff ff       	jmp    2320 <io_uring_submit@plt>
    49b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000049c0 <io_thread>:
    49c0:	f3 0f 1e fa          	endbr64
    49c4:	41 57                	push   %r15
    49c6:	31 d2                	xor    %edx,%edx
    49c8:	41 56                	push   %r14
    49ca:	41 55                	push   %r13
    49cc:	41 54                	push   %r12
    49ce:	55                   	push   %rbp
    49cf:	48 89 fd             	mov    %rdi,%rbp
    49d2:	53                   	push   %rbx
    49d3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    49da:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    49e3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    49eb:	48 8b 47 40          	mov    0x40(%rdi),%rax
    49ef:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    49f4:	bf 00 01 00 00       	mov    $0x100,%edi
    49f9:	48 89 de             	mov    %rbx,%rsi
    49fc:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4a00:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4a05:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4a0a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4a0f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4a14:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4a1c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4a21:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4a29:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4a2e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4a36:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4a3b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4a43:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4a48:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4a50:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4a55:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4a5d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4a65:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4a6d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4a75:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4a7d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4a85:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4a8d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4a95:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4a9d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4aa5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4aad:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4ab4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    4abc:	e8 0f d9 ff ff       	call   23d0 <io_uring_queue_init@plt>
    4ac1:	48 8b 7d 40          	mov    0x40(%rbp),%rdi
    4ac5:	31 f6                	xor    %esi,%esi
    4ac7:	e8 f4 d9 ff ff       	call   24c0 <io_uring_register_eventfd@plt>
    4acc:	31 d2                	xor    %edx,%edx
    4ace:	be 01 00 00 00       	mov    $0x1,%esi
    4ad3:	bf 02 00 00 00       	mov    $0x2,%edi
    4ad8:	e8 33 da ff ff       	call   2510 <socket@plt>
    4add:	83 f8 ff             	cmp    $0xffffffff,%eax
    4ae0:	0f 84 08 06 00 00    	je     50ee <io_thread+0x72e>
    4ae6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4aeb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4af1:	89 c7                	mov    %eax,%edi
    4af3:	41 89 c4             	mov    %eax,%r12d
    4af6:	ba 02 00 00 00       	mov    $0x2,%edx
    4afb:	be 01 00 00 00       	mov    $0x1,%esi
    4b00:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    4b08:	e8 d3 d7 ff ff       	call   22e0 <setsockopt@plt>
    4b0d:	85 c0                	test   %eax,%eax
    4b0f:	0f 88 cd 05 00 00    	js     50e2 <io_thread+0x722>
    4b15:	8b 05 d5 1e 00 00    	mov    0x1ed5(%rip),%eax        # 69f0 <_IO_stdin_used+0x9f0>
    4b1b:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    4b20:	ba 10 00 00 00       	mov    $0x10,%edx
    4b25:	44 89 e7             	mov    %r12d,%edi
    4b28:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4b31:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    4b39:	89 44 24 40          	mov    %eax,0x40(%rsp)
    4b3d:	e8 fe d8 ff ff       	call   2440 <bind@plt>
    4b42:	85 c0                	test   %eax,%eax
    4b44:	0f 88 8c 05 00 00    	js     50d6 <io_thread+0x716>
    4b4a:	be 0a 00 00 00       	mov    $0xa,%esi
    4b4f:	44 89 e7             	mov    %r12d,%edi
    4b52:	e8 a9 d8 ff ff       	call   2400 <listen@plt>
    4b57:	85 c0                	test   %eax,%eax
    4b59:	0f 88 6b 05 00 00    	js     50ca <io_thread+0x70a>
    4b5f:	ba db 18 00 00       	mov    $0x18db,%edx
    4b64:	48 8d 35 11 16 00 00 	lea    0x1611(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4b6b:	bf 01 00 00 00       	mov    $0x1,%edi
    4b70:	31 c0                	xor    %eax,%eax
    4b72:	e8 b9 d8 ff ff       	call   2430 <__printf_chk@plt>
    4b77:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4b7c:	48 89 d9             	mov    %rbx,%rcx
    4b7f:	44 89 e7             	mov    %r12d,%edi
    4b82:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4b87:	48 89 c6             	mov    %rax,%rsi
    4b8a:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4b8f:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    4b94:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    4b9c:	e8 7f fd ff ff       	call   4920 <add_accept_request>
    4ba1:	bf 01 00 00 00       	mov    $0x1,%edi
    4ba6:	be 10 00 00 00       	mov    $0x10,%esi
    4bab:	e8 d0 d7 ff ff       	call   2380 <calloc@plt>
    4bb0:	bf 0a 00 00 00       	mov    $0xa,%edi
    4bb5:	49 89 c5             	mov    %rax,%r13
    4bb8:	e8 33 d8 ff ff       	call   23f0 <malloc@plt>
    4bbd:	48 85 c0             	test   %rax,%rax
    4bc0:	0f 84 dd 04 00 00    	je     50a3 <io_thread+0x6e3>
    4bc6:	49 89 45 00          	mov    %rax,0x0(%r13)
    4bca:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4bd1:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4bd8:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    4be0:	8d 50 01             	lea    0x1(%rax),%edx
    4be3:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4be8:	8b 30                	mov    (%rax),%esi
    4bea:	f6 c1 02             	test   $0x2,%cl
    4bed:	0f 85 2d 04 00 00    	jne    5020 <io_thread+0x660>
    4bf3:	89 d0                	mov    %edx,%eax
    4bf5:	29 f0                	sub    %esi,%eax
    4bf7:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4bfe:	0f 82 50 d9 ff ff    	jb     2554 <io_thread.cold>
    4c04:	c1 e9 0a             	shr    $0xa,%ecx
    4c07:	48 8d 75 48          	lea    0x48(%rbp),%rsi
    4c0b:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4c0f:	48 89 df             	mov    %rbx,%rdi
    4c12:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4c19:	83 e1 01             	and    $0x1,%ecx
    4c1c:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4c23:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4c2a:	d3 e0                	shl    %cl,%eax
    4c2c:	8b 55 48             	mov    0x48(%rbp),%edx
    4c2f:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4c34:	48 c1 e0 06          	shl    $0x6,%rax
    4c38:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4c40:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4c46:	89 50 04             	mov    %edx,0x4(%rax)
    4c49:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4c51:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4c55:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    4c5d:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4c65:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4c69:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4c6d:	e8 ae d6 ff ff       	call   2320 <io_uring_submit@plt>
    4c72:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
    4c76:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4c7b:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4c83:	0f 85 b8 01 00 00    	jne    4e41 <io_thread+0x481>
    4c89:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4c8e:	4d 89 ce             	mov    %r9,%r14
    4c91:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4c96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4ca0:	48 8d 3d eb 14 00 00 	lea    0x14eb(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4ca7:	e8 24 d6 ff ff       	call   22d0 <puts@plt>
    4cac:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4cb3:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    4cba:	c1 e9 0b             	shr    $0xb,%ecx
    4cbd:	83 e1 01             	and    $0x1,%ecx
    4cc0:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4cc8:	8b 00                	mov    (%rax),%eax
    4cca:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4cd2:	8b 16                	mov    (%rsi),%edx
    4cd4:	39 d0                	cmp    %edx,%eax
    4cd6:	74 36                	je     4d0e <io_thread+0x34e>
    4cd8:	89 f8                	mov    %edi,%eax
    4cda:	21 d0                	and    %edx,%eax
    4cdc:	d3 e0                	shl    %cl,%eax
    4cde:	48 c1 e0 04          	shl    $0x4,%rax
    4ce2:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    4cea:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4cf2:	0f 85 88 01 00 00    	jne    4e80 <io_thread+0x4c0>
    4cf8:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4cfc:	0f 85 26 03 00 00    	jne    5028 <io_thread+0x668>
    4d02:	8b 40 08             	mov    0x8(%rax),%eax
    4d05:	83 c2 01             	add    $0x1,%edx
    4d08:	89 16                	mov    %edx,(%rsi)
    4d0a:	85 c0                	test   %eax,%eax
    4d0c:	79 b2                	jns    4cc0 <io_thread+0x300>
    4d0e:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    4d17:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4d20:	45 31 c0             	xor    %r8d,%r8d
    4d23:	31 d2                	xor    %edx,%edx
    4d25:	b9 01 00 00 00       	mov    $0x1,%ecx
    4d2a:	4c 89 f6             	mov    %r14,%rsi
    4d2d:	48 89 df             	mov    %rbx,%rdi
    4d30:	e8 eb d6 ff ff       	call   2420 <__io_uring_get_cqe@plt>
    4d35:	41 89 c7             	mov    %eax,%r15d
    4d38:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4d3d:	48 83 38 01          	cmpq   $0x1,(%rax)
    4d41:	0f 84 f1 02 00 00    	je     5038 <io_thread+0x678>
    4d47:	48 8d 3d 6a 14 00 00 	lea    0x146a(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4d4e:	e8 7d d5 ff ff       	call   22d0 <puts@plt>
    4d53:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4d58:	4c 8b 22             	mov    (%rdx),%r12
    4d5b:	45 85 ff             	test   %r15d,%r15d
    4d5e:	0f 88 2e 03 00 00    	js     5092 <io_thread+0x6d2>
    4d64:	8b 42 08             	mov    0x8(%rdx),%eax
    4d67:	45 8b 04 24          	mov    (%r12),%r8d
    4d6b:	85 c0                	test   %eax,%eax
    4d6d:	0f 88 e5 02 00 00    	js     5058 <io_thread+0x698>
    4d73:	41 83 f8 01          	cmp    $0x1,%r8d
    4d77:	0f 84 3b 01 00 00    	je     4eb8 <io_thread+0x4f8>
    4d7d:	41 83 f8 02          	cmp    $0x2,%r8d
    4d81:	0f 84 b1 01 00 00    	je     4f38 <io_thread+0x578>
    4d87:	45 85 c0             	test   %r8d,%r8d
    4d8a:	0f 84 70 01 00 00    	je     4f00 <io_thread+0x540>
    4d90:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4d98:	8b 02                	mov    (%rdx),%eax
    4d9a:	83 c0 01             	add    $0x1,%eax
    4d9d:	89 02                	mov    %eax,(%rdx)
    4d9f:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4da6:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4dad:	8d 50 01             	lea    0x1(%rax),%edx
    4db0:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4db5:	8b 30                	mov    (%rax),%esi
    4db7:	f6 c1 02             	test   $0x2,%cl
    4dba:	74 00                	je     4dbc <io_thread+0x3fc>
    4dbc:	89 d0                	mov    %edx,%eax
    4dbe:	29 f0                	sub    %esi,%eax
    4dc0:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4dc7:	0f 82 87 d7 ff ff    	jb     2554 <io_thread.cold>
    4dcd:	c1 e9 0a             	shr    $0xa,%ecx
    4dd0:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    4dd5:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4dd9:	48 89 df             	mov    %rbx,%rdi
    4ddc:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4de3:	83 e1 01             	and    $0x1,%ecx
    4de6:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4ded:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4df4:	d3 e0                	shl    %cl,%eax
    4df6:	8b 55 48             	mov    0x48(%rbp),%edx
    4df9:	48 c1 e0 06          	shl    $0x6,%rax
    4dfd:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4e05:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4e0b:	89 50 04             	mov    %edx,0x4(%rax)
    4e0e:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4e16:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4e1a:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    4e22:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4e2a:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4e2e:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4e32:	e8 e9 d4 ff ff       	call   2320 <io_uring_submit@plt>
    4e37:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
    4e3b:	0f 84 5f fe ff ff    	je     4ca0 <io_thread+0x2e0>
    4e41:	48 8d 3d a9 13 00 00 	lea    0x13a9(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    4e48:	e8 83 d4 ff ff       	call   22d0 <puts@plt>
    4e4d:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    4e55:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4e5e:	0f 85 3a 02 00 00    	jne    509e <io_thread+0x6de>
    4e64:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    4e6b:	31 c0                	xor    %eax,%eax
    4e6d:	5b                   	pop    %rbx
    4e6e:	5d                   	pop    %rbp
    4e6f:	41 5c                	pop    %r12
    4e71:	41 5d                	pop    %r13
    4e73:	41 5e                	pop    %r14
    4e75:	41 5f                	pop    %r15
    4e77:	c3                   	ret
    4e78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4e80:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    4e85:	48 85 c0             	test   %rax,%rax
    4e88:	0f 84 92 fe ff ff    	je     4d20 <io_thread+0x360>
    4e8e:	48 83 38 01          	cmpq   $0x1,(%rax)
    4e92:	0f 84 a0 01 00 00    	je     5038 <io_thread+0x678>
    4e98:	48 8d 3d 19 13 00 00 	lea    0x1319(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4e9f:	e8 2c d4 ff ff       	call   22d0 <puts@plt>
    4ea4:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4ea9:	4c 8b 22             	mov    (%rdx),%r12
    4eac:	e9 b3 fe ff ff       	jmp    4d64 <io_thread+0x3a4>
    4eb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4eb8:	85 c0                	test   %eax,%eax
    4eba:	0f 85 c0 00 00 00    	jne    4f80 <io_thread+0x5c0>
    4ec0:	48 8b 0d 59 41 00 00 	mov    0x4159(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4ec7:	ba 0f 00 00 00       	mov    $0xf,%edx
    4ecc:	be 01 00 00 00       	mov    $0x1,%esi
    4ed1:	48 8d 3d 09 13 00 00 	lea    0x1309(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    4ed8:	e8 c3 d5 ff ff       	call   24a0 <fwrite@plt>
    4edd:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4ee2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4ee8:	48 85 c0             	test   %rax,%rax
    4eeb:	0f 84 ae fe ff ff    	je     4d9f <io_thread+0x3df>
    4ef1:	e9 9a fe ff ff       	jmp    4d90 <io_thread+0x3d0>
    4ef6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4f00:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    4f05:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    4f0a:	48 89 d9             	mov    %rbx,%rcx
    4f0d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4f11:	e8 0a fa ff ff       	call   4920 <add_accept_request>
    4f16:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f1b:	48 89 de             	mov    %rbx,%rsi
    4f1e:	8b 78 08             	mov    0x8(%rax),%edi
    4f21:	e8 9a f3 ff ff       	call   42c0 <add_read_request>
    4f26:	4c 89 e7             	mov    %r12,%rdi
    4f29:	e8 82 d3 ff ff       	call   22b0 <free@plt>
    4f2e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f33:	eb b3                	jmp    4ee8 <io_thread+0x528>
    4f35:	0f 1f 00             	nopl   (%rax)
    4f38:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    4f3d:	45 31 ff             	xor    %r15d,%r15d
    4f40:	85 c0                	test   %eax,%eax
    4f42:	7e 20                	jle    4f64 <io_thread+0x5a4>
    4f44:	0f 1f 40 00          	nopl   0x0(%rax)
    4f48:	4c 89 f8             	mov    %r15,%rax
    4f4b:	49 83 c7 01          	add    $0x1,%r15
    4f4f:	48 c1 e0 04          	shl    $0x4,%rax
    4f53:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    4f58:	e8 53 d3 ff ff       	call   22b0 <free@plt>
    4f5d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    4f62:	7f e4                	jg     4f48 <io_thread+0x588>
    4f64:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    4f69:	e8 e2 d3 ff ff       	call   2350 <close@plt>
    4f6e:	4c 89 e7             	mov    %r12,%rdi
    4f71:	e8 3a d3 ff ff       	call   22b0 <free@plt>
    4f76:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f7b:	e9 68 ff ff ff       	jmp    4ee8 <io_thread+0x528>
    4f80:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    4f85:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4f8a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    4f92:	eb 11                	jmp    4fa5 <io_thread+0x5e5>
    4f94:	0f 1f 40 00          	nopl   0x0(%rax)
    4f98:	48 83 c0 01          	add    $0x1,%rax
    4f9c:	48 83 c2 01          	add    $0x1,%rdx
    4fa0:	48 39 c6             	cmp    %rax,%rsi
    4fa3:	74 4b                	je     4ff0 <io_thread+0x630>
    4fa5:	0f b6 0a             	movzbl (%rdx),%ecx
    4fa8:	88 08                	mov    %cl,(%rax)
    4faa:	80 f9 0d             	cmp    $0xd,%cl
    4fad:	75 e9                	jne    4f98 <io_thread+0x5d8>
    4faf:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    4fb3:	75 e3                	jne    4f98 <io_thread+0x5d8>
    4fb5:	c6 00 00             	movb   $0x0,(%rax)
    4fb8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    4fbd:	48 89 da             	mov    %rbx,%rdx
    4fc0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    4fc5:	e8 76 f7 ff ff       	call   4740 <handle_http_method>
    4fca:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    4fcf:	e8 dc d2 ff ff       	call   22b0 <free@plt>
    4fd4:	4c 89 e7             	mov    %r12,%rdi
    4fd7:	e8 d4 d2 ff ff       	call   22b0 <free@plt>
    4fdc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4fe1:	e9 02 ff ff ff       	jmp    4ee8 <io_thread+0x528>
    4fe6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4ff0:	48 8b 0d 29 40 00 00 	mov    0x4029(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4ff7:	ba 12 00 00 00       	mov    $0x12,%edx
    4ffc:	be 01 00 00 00       	mov    $0x1,%esi
    5001:	48 8d 3d 2f 11 00 00 	lea    0x112f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    5008:	e8 93 d4 ff ff       	call   24a0 <fwrite@plt>
    500d:	bf 01 00 00 00       	mov    $0x1,%edi
    5012:	e8 69 d4 ff ff       	call   2480 <exit@plt>
    5017:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5020:	e9 ce fb ff ff       	jmp    4bf3 <io_thread+0x233>
    5025:	0f 1f 00             	nopl   (%rax)
    5028:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    502d:	e9 5c fe ff ff       	jmp    4e8e <io_thread+0x4ce>
    5032:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5038:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5040:	48 8d 3d 5d 11 00 00 	lea    0x115d(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    5047:	8b 02                	mov    (%rdx),%eax
    5049:	83 c0 01             	add    $0x1,%eax
    504c:	89 02                	mov    %eax,(%rdx)
    504e:	e8 7d d2 ff ff       	call   22d0 <puts@plt>
    5053:	e9 e9 fd ff ff       	jmp    4e41 <io_thread+0x481>
    5058:	f7 d8                	neg    %eax
    505a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    505f:	89 c7                	mov    %eax,%edi
    5061:	e8 7a d4 ff ff       	call   24e0 <strerror@plt>
    5066:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    506b:	be 01 00 00 00       	mov    $0x1,%esi
    5070:	48 8b 3d a9 3f 00 00 	mov    0x3fa9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    5077:	48 89 c1             	mov    %rax,%rcx
    507a:	48 8d 15 cf 13 00 00 	lea    0x13cf(%rip),%rdx        # 6450 <_IO_stdin_used+0x450>
    5081:	31 c0                	xor    %eax,%eax
    5083:	e8 28 d4 ff ff       	call   24b0 <__fprintf_chk@plt>
    5088:	bf 01 00 00 00       	mov    $0x1,%edi
    508d:	e8 ee d3 ff ff       	call   2480 <exit@plt>
    5092:	48 8d 3d 36 11 00 00 	lea    0x1136(%rip),%rdi        # 61cf <_IO_stdin_used+0x1cf>
    5099:	e8 a2 ea ff ff       	call   3b40 <fatal_error>
    509e:	e8 6d d2 ff ff       	call   2310 <__stack_chk_fail@plt>
    50a3:	48 8b 0d 76 3f 00 00 	mov    0x3f76(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    50aa:	ba 28 00 00 00       	mov    $0x28,%edx
    50af:	be 01 00 00 00       	mov    $0x1,%esi
    50b4:	48 8d 3d 65 13 00 00 	lea    0x1365(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    50bb:	e8 e0 d3 ff ff       	call   24a0 <fwrite@plt>
    50c0:	bf 01 00 00 00       	mov    $0x1,%edi
    50c5:	e8 b6 d3 ff ff       	call   2480 <exit@plt>
    50ca:	48 8d 3d a2 10 00 00 	lea    0x10a2(%rip),%rdi        # 6173 <_IO_stdin_used+0x173>
    50d1:	e8 6a ea ff ff       	call   3b40 <fatal_error>
    50d6:	48 8d 3d 8f 10 00 00 	lea    0x108f(%rip),%rdi        # 616c <_IO_stdin_used+0x16c>
    50dd:	e8 5e ea ff ff       	call   3b40 <fatal_error>
    50e2:	48 8d 3d 6a 10 00 00 	lea    0x106a(%rip),%rdi        # 6153 <_IO_stdin_used+0x153>
    50e9:	e8 52 ea ff ff       	call   3b40 <fatal_error>
    50ee:	48 8d 3d 55 10 00 00 	lea    0x1055(%rip),%rdi        # 614a <_IO_stdin_used+0x14a>
    50f5:	e8 46 ea ff ff       	call   3b40 <fatal_error>
    50fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005100 <receive>:
    5100:	f3 0f 1e fa          	endbr64
    5104:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    510a:	85 c0                	test   %eax,%eax
    510c:	0f 8e ed 00 00 00    	jle    51ff <receive+0xff>
    5112:	41 54                	push   %r12
    5114:	4c 63 e0             	movslq %eax,%r12
    5117:	48 89 fa             	mov    %rdi,%rdx
    511a:	55                   	push   %rbp
    511b:	49 c1 e4 05          	shl    $0x5,%r12
    511f:	53                   	push   %rbx
    5120:	48 8b b7 28 02 00 00 	mov    0x228(%rdi),%rsi
    5127:	49 01 f4             	add    %rsi,%r12
    512a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5130:	48 8b 2e             	mov    (%rsi),%rbp
    5133:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    513a:	48 85 ff             	test   %rdi,%rdi
    513d:	0f 8e 9d 00 00 00    	jle    51e0 <receive+0xe0>
    5143:	48 8b 8a 30 02 00 00 	mov    0x230(%rdx),%rcx
    514a:	4c 8b 45 00          	mov    0x0(%rbp),%r8
    514e:	4c 63 1a             	movslq (%rdx),%r11
    5151:	49 89 c9             	mov    %rcx,%r9
    5154:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5158:	49 f7 d9             	neg    %r9
    515b:	48 01 c7             	add    %rax,%rdi
    515e:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
    5162:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
    5169:	4c 8b 46 18          	mov    0x18(%rsi),%r8
    516d:	49 29 c9             	sub    %rcx,%r9
    5170:	49 29 c8             	sub    %rcx,%r8
    5173:	eb 0c                	jmp    5181 <receive+0x81>
    5175:	0f 1f 00             	nopl   (%rax)
    5178:	48 83 c0 01          	add    $0x1,%rax
    517c:	48 39 f8             	cmp    %rdi,%rax
    517f:	74 5f                	je     51e0 <receive+0xe0>
    5181:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    5185:	48 89 82 30 02 00 00 	mov    %rax,0x230(%rdx)
    518c:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
    5193:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5197:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
    519b:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    51a0:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    51a4:	75 d2                	jne    5178 <receive+0x78>
    51a6:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    51ad:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    51b1:	75 c5                	jne    5178 <receive+0x78>
    51b3:	bf 01 00 00 00       	mov    $0x1,%edi
    51b8:	b9 01 00 00 00       	mov    $0x1,%ecx
    51bd:	ba 01 00 00 00       	mov    $0x1,%edx
    51c2:	31 c0                	xor    %eax,%eax
    51c4:	48 8d 35 ad 12 00 00 	lea    0x12ad(%rip),%rsi        # 6478 <_IO_stdin_used+0x478>
    51cb:	e8 60 d2 ff ff       	call   2430 <__printf_chk@plt>
    51d0:	bf 01 00 00 00       	mov    $0x1,%edi
    51d5:	e8 a6 d2 ff ff       	call   2480 <exit@plt>
    51da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    51e0:	48 c7 85 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rbp)
    51eb:	48 83 c6 20          	add    $0x20,%rsi
    51ef:	49 39 f4             	cmp    %rsi,%r12
    51f2:	0f 85 38 ff ff ff    	jne    5130 <receive+0x30>
    51f8:	5b                   	pop    %rbx
    51f9:	31 c0                	xor    %eax,%eax
    51fb:	5d                   	pop    %rbp
    51fc:	41 5c                	pop    %r12
    51fe:	c3                   	ret
    51ff:	31 c0                	xor    %eax,%eax
    5201:	c3                   	ret
    5202:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    520d:	0f 1f 00             	nopl   (%rax)

0000000000005210 <barriered_work>:
    5210:	f3 0f 1e fa          	endbr64
    5214:	41 57                	push   %r15
    5216:	41 56                	push   %r14
    5218:	41 55                	push   %r13
    521a:	41 54                	push   %r12
    521c:	55                   	push   %rbp
    521d:	48 8d af 00 02 00 00 	lea    0x200(%rdi),%rbp
    5224:	53                   	push   %rbx
    5225:	48 89 fb             	mov    %rdi,%rbx
    5228:	48 83 ec 28          	sub    $0x28,%rsp
    522c:	8b 07                	mov    (%rdi),%eax
    522e:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    5234:	0f 84 56 01 00 00    	je     5390 <barriered_work+0x180>
    523a:	e8 c1 fe ff ff       	call   5100 <receive>
    523f:	eb 12                	jmp    5253 <barriered_work+0x43>
    5241:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5248:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    5250:	0f ae f8             	sfence
    5253:	8b 45 00             	mov    0x0(%rbp),%eax
    5256:	83 f8 01             	cmp    $0x1,%eax
    5259:	74 ed                	je     5248 <barriered_work+0x38>
    525b:	83 bb 38 02 00 00 01 	cmpl   $0x1,0x238(%rbx)
    5262:	74 14                	je     5278 <barriered_work+0x68>
    5264:	0f ae f0             	mfence
    5267:	48 83 c4 28          	add    $0x28,%rsp
    526b:	31 c0                	xor    %eax,%eax
    526d:	5b                   	pop    %rbx
    526e:	5d                   	pop    %rbp
    526f:	41 5c                	pop    %r12
    5271:	41 5d                	pop    %r13
    5273:	41 5e                	pop    %r14
    5275:	41 5f                	pop    %r15
    5277:	c3                   	ret
    5278:	48 63 83 34 01 00 00 	movslq 0x134(%rbx),%rax
    527f:	85 c0                	test   %eax,%eax
    5281:	7e e1                	jle    5264 <barriered_work+0x54>
    5283:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5288:	48 8d 83 40 02 00 00 	lea    0x240(%rbx),%rax
    528f:	44 8b b3 30 01 00 00 	mov    0x130(%rbx),%r14d
    5296:	31 c9                	xor    %ecx,%ecx
    5298:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    529d:	48 8d 83 48 02 00 00 	lea    0x248(%rbx),%rax
    52a4:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    52a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    52b0:	41 39 ce             	cmp    %ecx,%r14d
    52b3:	0f 84 bc 00 00 00    	je     5375 <barriered_work+0x165>
    52b9:	49 89 c9             	mov    %rcx,%r9
    52bc:	49 c1 e1 05          	shl    $0x5,%r9
    52c0:	4c 03 8b 28 02 00 00 	add    0x228(%rbx),%r9
    52c7:	4d 8b 51 08          	mov    0x8(%r9),%r10
    52cb:	49 8b aa 80 00 00 00 	mov    0x80(%r10),%rbp
    52d2:	4d 63 82 88 00 00 00 	movslq 0x88(%r10),%r8
    52d9:	4c 39 c5             	cmp    %r8,%rbp
    52dc:	0f 8d 93 00 00 00    	jge    5375 <barriered_work+0x165>
    52e2:	4d 89 c3             	mov    %r8,%r11
    52e5:	4c 8b ab 08 01 00 00 	mov    0x108(%rbx),%r13
    52ec:	4d 8b 61 10          	mov    0x10(%r9),%r12
    52f0:	49 29 eb             	sub    %rbp,%r11
    52f3:	49 8b 3a             	mov    (%r10),%rdi
    52f6:	49 8d 43 ff          	lea    -0x1(%r11),%rax
    52fa:	48 83 f8 02          	cmp    $0x2,%rax
    52fe:	0f 86 6c 02 00 00    	jbe    5570 <barriered_work+0x360>
    5304:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    530c:	4a 8d 34 c5 00 00 00 00 	lea    0x0(,%r8,8),%rsi
    5314:	48 8d 14 07          	lea    (%rdi,%rax,1),%rdx
    5318:	4c 8d 3c 37          	lea    (%rdi,%rsi,1),%r15
    531c:	4c 39 7c 24 10       	cmp    %r15,0x10(%rsp)
    5321:	0f 83 f1 01 00 00    	jae    5518 <barriered_work+0x308>
    5327:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
    532c:	4c 39 fa             	cmp    %r15,%rdx
    532f:	0f 83 e3 01 00 00    	jae    5518 <barriered_work+0x308>
    5335:	48 01 f8             	add    %rdi,%rax
    5338:	48 01 fe             	add    %rdi,%rsi
    533b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5340:	4c 8b bb 40 02 00 00 	mov    0x240(%rbx),%r15
    5347:	48 83 c0 08          	add    $0x8,%rax
    534b:	4c 89 78 f8          	mov    %r15,-0x8(%rax)
    534f:	48 39 f0             	cmp    %rsi,%rax
    5352:	75 ec                	jne    5340 <barriered_work+0x130>
    5354:	0f 1f 40 00          	nopl   0x0(%rax)
    5358:	4d 01 dd             	add    %r11,%r13
    535b:	4d 01 dc             	add    %r11,%r12
    535e:	4c 89 ab 08 01 00 00 	mov    %r13,0x108(%rbx)
    5365:	4d 89 61 10          	mov    %r12,0x10(%r9)
    5369:	4d 89 82 80 00 00 00 	mov    %r8,0x80(%r10)
    5370:	4e 89 7c c7 f8       	mov    %r15,-0x8(%rdi,%r8,8)
    5375:	48 83 c1 01          	add    $0x1,%rcx
    5379:	48 39 4c 24 08       	cmp    %rcx,0x8(%rsp)
    537e:	0f 85 2c ff ff ff    	jne    52b0 <barriered_work+0xa0>
    5384:	e9 db fe ff ff       	jmp    5264 <barriered_work+0x54>
    5389:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5390:	e8 6b fd ff ff       	call   5100 <receive>
    5395:	8b 8b 34 01 00 00    	mov    0x134(%rbx),%ecx
    539b:	8b 03                	mov    (%rbx),%eax
    539d:	85 c9                	test   %ecx,%ecx
    539f:	0f 8e 8e 00 00 00    	jle    5433 <barriered_work+0x223>
    53a5:	48 63 d0             	movslq %eax,%rdx
    53a8:	83 c0 01             	add    $0x1,%eax
    53ab:	4c 63 d1             	movslq %ecx,%r10
    53ae:	4c 8d 1c 92          	lea    (%rdx,%rdx,4),%r11
    53b2:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    53b9:	49 c1 e2 05          	shl    $0x5,%r10
    53bd:	49 c1 e3 07          	shl    $0x7,%r11
    53c1:	4c 8b 62 10          	mov    0x10(%rdx),%r12
    53c5:	99                   	cltd
    53c6:	f7 f9                	idiv   %ecx
    53c8:	4d 8d 74 24 20       	lea    0x20(%r12),%r14
    53cd:	89 d0                	mov    %edx,%eax
    53cf:	f7 d8                	neg    %eax
    53d1:	0f 48 c2             	cmovs  %edx,%eax
    53d4:	31 ff                	xor    %edi,%edi
    53d6:	45 31 ed             	xor    %r13d,%r13d
    53d9:	48 98                	cltq
    53db:	4c 8d 0c 80          	lea    (%rax,%rax,4),%r9
    53df:	49 c1 e1 07          	shl    $0x7,%r9
    53e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    53e8:	4b 8b 44 2c 20       	mov    0x20(%r12,%r13,1),%rax
    53ed:	4c 89 f2             	mov    %r14,%rdx
    53f0:	4a 8b 84 18 28 02 00 00 	mov    0x228(%rax,%r11,1),%rax
    53f8:	4d 8d 04 02          	lea    (%r10,%rax,1),%r8
    53fc:	0f 1f 40 00          	nopl   0x0(%rax)
    5400:	48 8b 0a             	mov    (%rdx),%rcx
    5403:	48 8b 70 08          	mov    0x8(%rax),%rsi
    5407:	48 83 c0 20          	add    $0x20,%rax
    540b:	48 81 c2 98 00 00 00 	add    $0x98,%rdx
    5412:	4a 8b 8c 09 28 02 00 00 	mov    0x228(%rcx,%r9,1),%rcx
    541a:	48 89 34 39          	mov    %rsi,(%rcx,%rdi,1)
    541e:	4c 39 c0             	cmp    %r8,%rax
    5421:	75 dd                	jne    5400 <barriered_work+0x1f0>
    5423:	48 83 c7 20          	add    $0x20,%rdi
    5427:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    542e:	4c 39 d7             	cmp    %r10,%rdi
    5431:	75 b5                	jne    53e8 <barriered_work+0x1d8>
    5433:	0f ae f0             	mfence
    5436:	48 8b b3 18 02 00 00 	mov    0x218(%rbx),%rsi
    543d:	31 ff                	xor    %edi,%edi
    543f:	48 c1 e6 05          	shl    $0x5,%rsi
    5443:	48 03 b3 08 02 00 00 	add    0x208(%rbx),%rsi
    544a:	e8 a1 ce ff ff       	call   22f0 <clock_gettime@plt>
    544f:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    5456:	48 8b 40 30          	mov    0x30(%rax),%rax
    545a:	8b 70 10             	mov    0x10(%rax),%esi
    545d:	44 8d 66 01          	lea    0x1(%rsi),%r12d
    5461:	44 89 60 10          	mov    %r12d,0x10(%rax)
    5465:	eb 47                	jmp    54ae <barriered_work+0x29e>
    5467:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5470:	48 63 83 30 01 00 00 	movslq 0x130(%rbx),%rax
    5477:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    547e:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    5486:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    548a:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    548e:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    5492:	48 63 13             	movslq (%rbx),%rdx
    5495:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    5499:	48 8d 3c 92          	lea    (%rdx,%rdx,4),%rdi
    549d:	48 c1 e7 07          	shl    $0x7,%rdi
    54a1:	48 03 78 20          	add    0x20(%rax),%rdi
    54a5:	ff 93 20 01 00 00    	call   *0x120(%rbx)
    54ab:	0f ae f8             	sfence
    54ae:	8b 45 00             	mov    0x0(%rbp),%eax
    54b1:	83 f8 01             	cmp    $0x1,%eax
    54b4:	74 ba                	je     5470 <barriered_work+0x260>
    54b6:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    54bd:	48 8b 40 30          	mov    0x30(%rax),%rax
    54c1:	44 39 60 10          	cmp    %r12d,0x10(%rax)
    54c5:	75 3d                	jne    5504 <barriered_work+0x2f4>
    54c7:	48 8b b3 18 02 00 00 	mov    0x218(%rbx),%rsi
    54ce:	31 ff                	xor    %edi,%edi
    54d0:	48 c1 e6 05          	shl    $0x5,%rsi
    54d4:	48 03 b3 08 02 00 00 	add    0x208(%rbx),%rsi
    54db:	48 83 c6 10          	add    $0x10,%rsi
    54df:	e8 0c ce ff ff       	call   22f0 <clock_gettime@plt>
    54e4:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    54eb:	48 83 c0 01          	add    $0x1,%rax
    54ef:	48 99                	cqto
    54f1:	48 f7 bb 10 02 00 00 	idivq  0x210(%rbx)
    54f8:	48 89 93 18 02 00 00 	mov    %rdx,0x218(%rbx)
    54ff:	e9 60 fd ff ff       	jmp    5264 <barriered_work+0x54>
    5504:	48 8d 3d f9 0c 00 00 	lea    0xcf9(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    550b:	e8 c0 cd ff ff       	call   22d0 <puts@plt>
    5510:	eb b5                	jmp    54c7 <barriered_work+0x2b7>
    5512:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5518:	4c 8b bb 40 02 00 00 	mov    0x240(%rbx),%r15
    551f:	4c 89 d8             	mov    %r11,%rax
    5522:	48 d1 e8             	shr    %rax
    5525:	66 49 0f 6e c7       	movq   %r15,%xmm0
    552a:	48 c1 e0 04          	shl    $0x4,%rax
    552e:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5532:	48 01 d0             	add    %rdx,%rax
    5535:	0f 1f 00             	nopl   (%rax)
    5538:	0f 11 02             	movups %xmm0,(%rdx)
    553b:	48 83 c2 10          	add    $0x10,%rdx
    553f:	48 39 d0             	cmp    %rdx,%rax
    5542:	75 f4                	jne    5538 <barriered_work+0x328>
    5544:	4c 89 d8             	mov    %r11,%rax
    5547:	48 83 e0 fe          	and    $0xfffffffffffffffe,%rax
    554b:	48 01 e8             	add    %rbp,%rax
    554e:	41 f6 c3 01          	test   $0x1,%r11b
    5552:	0f 84 00 fe ff ff    	je     5358 <barriered_work+0x148>
    5558:	4c 8b bb 40 02 00 00 	mov    0x240(%rbx),%r15
    555f:	4c 89 3c c7          	mov    %r15,(%rdi,%rax,8)
    5563:	e9 f0 fd ff ff       	jmp    5358 <barriered_work+0x148>
    5568:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5570:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    5578:	4a 8d 34 c5 00 00 00 00 	lea    0x0(,%r8,8),%rsi
    5580:	e9 b0 fd ff ff       	jmp    5335 <barriered_work+0x125>
    5585:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005590 <barriered_work_ingest>:
    5590:	f3 0f 1e fa          	endbr64
    5594:	48 83 ec 08          	sub    $0x8,%rsp
    5598:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    559f:	48 8b 40 38          	mov    0x38(%rax),%rax
    55a3:	48 63 10             	movslq (%rax),%rdx
    55a6:	85 d2                	test   %edx,%edx
    55a8:	7e 2c                	jle    55d6 <barriered_work_ingest+0x46>
    55aa:	48 8b 40 08          	mov    0x8(%rax),%rax
    55ae:	48 c1 e2 04          	shl    $0x4,%rdx
    55b2:	48 01 c2             	add    %rax,%rdx
    55b5:	0f 1f 00             	nopl   (%rax)
    55b8:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    55bc:	75 0f                	jne    55cd <barriered_work_ingest+0x3d>
    55be:	48 83 87 20 02 00 00 01 	addq   $0x1,0x220(%rdi)
    55c6:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    55cd:	48 83 c0 10          	add    $0x10,%rax
    55d1:	48 39 d0             	cmp    %rdx,%rax
    55d4:	75 e2                	jne    55b8 <barriered_work_ingest+0x28>
    55d6:	0f ae f0             	mfence
    55d9:	e8 32 fc ff ff       	call   5210 <barriered_work>
    55de:	31 c0                	xor    %eax,%eax
    55e0:	48 83 c4 08          	add    $0x8,%rsp
    55e4:	c3                   	ret
    55e5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000055f0 <barriered_nulltask>:
    55f0:	f3 0f 1e fa          	endbr64
    55f4:	31 c0                	xor    %eax,%eax
    55f6:	c3                   	ret
    55f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005600 <barriered_steal>:
    5600:	f3 0f 1e fa          	endbr64
    5604:	31 c0                	xor    %eax,%eax
    5606:	c3                   	ret
    5607:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005610 <after>:
    5610:	f3 0f 1e fa          	endbr64
    5614:	31 c0                	xor    %eax,%eax
    5616:	48 39 d7             	cmp    %rdx,%rdi
    5619:	7e 08                	jle    5623 <after+0x13>
    561b:	31 c0                	xor    %eax,%eax
    561d:	48 39 ce             	cmp    %rcx,%rsi
    5620:	0f 9f c0             	setg   %al
    5623:	c3                   	ret
    5624:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    562f:	90                   	nop

0000000000005630 <within>:
    5630:	f3 0f 1e fa          	endbr64
    5634:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5639:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    563e:	31 c0                	xor    %eax,%eax
    5640:	48 39 d7             	cmp    %rdx,%rdi
    5643:	7f 18                	jg     565d <within+0x2d>
    5645:	4d 39 d8             	cmp    %r11,%r8
    5648:	0f 9e c2             	setle  %dl
    564b:	48 39 ce             	cmp    %rcx,%rsi
    564e:	0f 9e c0             	setle  %al
    5651:	21 c2                	and    %eax,%edx
    5653:	31 c0                	xor    %eax,%eax
    5655:	4d 39 d1             	cmp    %r10,%r9
    5658:	0f 9e c0             	setle  %al
    565b:	21 d0                	and    %edx,%eax
    565d:	c3                   	ret
    565e:	66 90                	xchg   %ax,%ax

0000000000005660 <overlap>:
    5660:	f3 0f 1e fa          	endbr64
    5664:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5669:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    566e:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    5673:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    5678:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
    567d:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    5682:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5687:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    568c:	48 39 fe             	cmp    %rdi,%rsi
    568f:	7d 2f                	jge    56c0 <overlap+0x60>
    5691:	48 39 ca             	cmp    %rcx,%rdx
    5694:	7d 62                	jge    56f8 <overlap+0x98>
    5696:	4d 39 da             	cmp    %r11,%r10
    5699:	7e 0e                	jle    56a9 <overlap+0x49>
    569b:	b8 01 00 00 00       	mov    $0x1,%eax
    56a0:	4d 39 c1             	cmp    %r8,%r9
    56a3:	0f 8f 7f 00 00 00    	jg     5728 <overlap+0xc8>
    56a9:	31 c0                	xor    %eax,%eax
    56ab:	4d 39 c1             	cmp    %r8,%r9
    56ae:	7c 4c                	jl     56fc <overlap+0x9c>
    56b0:	31 c0                	xor    %eax,%eax
    56b2:	4d 39 da             	cmp    %r11,%r10
    56b5:	0f 9d c0             	setge  %al
    56b8:	c3                   	ret
    56b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    56c0:	7e 4e                	jle    5710 <overlap+0xb0>
    56c2:	48 39 ca             	cmp    %rcx,%rdx
    56c5:	7f 39                	jg     5700 <overlap+0xa0>
    56c7:	75 31                	jne    56fa <overlap+0x9a>
    56c9:	4d 39 c1             	cmp    %r8,%r9
    56cc:	7f 2c                	jg     56fa <overlap+0x9a>
    56ce:	b8 01 00 00 00       	mov    $0x1,%eax
    56d3:	4d 39 da             	cmp    %r11,%r10
    56d6:	7e 24                	jle    56fc <overlap+0x9c>
    56d8:	48 39 ca             	cmp    %rcx,%rdx
    56db:	0f 94 c2             	sete   %dl
    56de:	48 39 fe             	cmp    %rdi,%rsi
    56e1:	0f 94 c0             	sete   %al
    56e4:	21 c2                	and    %eax,%edx
    56e6:	31 c0                	xor    %eax,%eax
    56e8:	4d 39 c1             	cmp    %r8,%r9
    56eb:	0f 94 c0             	sete   %al
    56ee:	21 d0                	and    %edx,%eax
    56f0:	c3                   	ret
    56f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    56f8:	74 af                	je     56a9 <overlap+0x49>
    56fa:	31 c0                	xor    %eax,%eax
    56fc:	c3                   	ret
    56fd:	0f 1f 00             	nopl   (%rax)
    5700:	4d 39 c1             	cmp    %r8,%r9
    5703:	7d c4                	jge    56c9 <overlap+0x69>
    5705:	b8 01 00 00 00       	mov    $0x1,%eax
    570a:	4d 39 da             	cmp    %r11,%r10
    570d:	7d ba                	jge    56c9 <overlap+0x69>
    570f:	c3                   	ret
    5710:	48 39 ca             	cmp    %rcx,%rdx
    5713:	7c 94                	jl     56a9 <overlap+0x49>
    5715:	4d 39 c1             	cmp    %r8,%r9
    5718:	7e b4                	jle    56ce <overlap+0x6e>
    571a:	48 39 ca             	cmp    %rcx,%rdx
    571d:	74 91                	je     56b0 <overlap+0x50>
    571f:	eb d9                	jmp    56fa <overlap+0x9a>
    5721:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5728:	c3                   	ret
    5729:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005730 <verify>:
    5730:	f3 0f 1e fa          	endbr64
    5734:	85 f6                	test   %esi,%esi
    5736:	0f 8e 2d 03 00 00    	jle    5a69 <verify+0x339>
    573c:	41 57                	push   %r15
    573e:	41 89 f7             	mov    %esi,%r15d
    5741:	41 56                	push   %r14
    5743:	45 31 f6             	xor    %r14d,%r14d
    5746:	41 55                	push   %r13
    5748:	41 54                	push   %r12
    574a:	55                   	push   %rbp
    574b:	53                   	push   %rbx
    574c:	48 8d 5f 20          	lea    0x20(%rdi),%rbx
    5750:	48 83 ec 48          	sub    $0x48,%rsp
    5754:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5759:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    575e:	31 ed                	xor    %ebp,%ebp
    5760:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    5765:	41 89 ec             	mov    %ebp,%r12d
    5768:	45 39 f4             	cmp    %r14d,%r12d
    576b:	0f 84 4b 02 00 00    	je     59bc <verify+0x28c>
    5771:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5776:	8b 50 08             	mov    0x8(%rax),%edx
    5779:	85 d2                	test   %edx,%edx
    577b:	0f 8e 3b 02 00 00    	jle    59bc <verify+0x28c>
    5781:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    5789:	45 31 ed             	xor    %r13d,%r13d
    578c:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    5791:	44 89 f2             	mov    %r14d,%edx
    5794:	48 8d 35 79 0a 00 00 	lea    0xa79(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    579b:	bf 01 00 00 00       	mov    $0x1,%edi
    57a0:	31 c0                	xor    %eax,%eax
    57a2:	e8 89 cc ff ff       	call   2430 <__printf_chk@plt>
    57a7:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    57ac:	8b 40 08             	mov    0x8(%rax),%eax
    57af:	85 c0                	test   %eax,%eax
    57b1:	0f 8e e5 01 00 00    	jle    599c <verify+0x26c>
    57b7:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    57bc:	44 89 6c 24 34       	mov    %r13d,0x34(%rsp)
    57c1:	31 db                	xor    %ebx,%ebx
    57c3:	44 89 74 24 38       	mov    %r14d,0x38(%rsp)
    57c8:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    57cd:	48 8b 28             	mov    (%rax),%rbp
    57d0:	4c 8b 6c 24 08       	mov    0x8(%rsp),%r13
    57d5:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    57d9:	4c 8b 3c 24          	mov    (%rsp),%r15
    57dd:	48 8d 35 45 0a 00 00 	lea    0xa45(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    57e4:	49 89 c6             	mov    %rax,%r14
    57e7:	bf 01 00 00 00       	mov    $0x1,%edi
    57ec:	49 8b 45 00          	mov    0x0(%r13),%rax
    57f0:	49 c1 e6 07          	shl    $0x7,%r14
    57f4:	4a 8b 8c 3d 18 02 00 00 	mov    0x218(%rbp,%r15,1),%rcx
    57fc:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    5801:	4a 8b 94 30 18 02 00 00 	mov    0x218(%rax,%r14,1),%rdx
    5809:	31 c0                	xor    %eax,%eax
    580b:	e8 20 cc ff ff       	call   2430 <__printf_chk@plt>
    5810:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5815:	48 8b 28             	mov    (%rax),%rbp
    5818:	4a 83 bc 3d 18 02 00 00 00 	cmpq   $0x0,0x218(%rbp,%r15,1)
    5821:	0f 8e 54 01 00 00    	jle    597b <verify+0x24b>
    5827:	4d 03 75 00          	add    0x0(%r13),%r14
    582b:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    5830:	ba 01 00 00 00       	mov    $0x1,%edx
    5835:	4d 89 f3             	mov    %r14,%r11
    5838:	4d 8b b3 18 02 00 00 	mov    0x218(%r11),%r14
    583f:	4d 85 f6             	test   %r14,%r14
    5842:	0f 8e 2e 01 00 00    	jle    5976 <verify+0x246>
    5848:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5850:	48 8b 04 24          	mov    (%rsp),%rax
    5854:	49 89 d4             	mov    %rdx,%r12
    5857:	31 db                	xor    %ebx,%ebx
    5859:	49 89 d5             	mov    %rdx,%r13
    585c:	49 c1 e4 05          	shl    $0x5,%r12
    5860:	49 83 ec 20          	sub    $0x20,%r12
    5864:	4c 8d 7c 05 00       	lea    0x0(%rbp,%rax,1),%r15
    5869:	eb 32                	jmp    589d <verify+0x16d>
    586b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5870:	4c 39 c2             	cmp    %r8,%rdx
    5873:	0f 8d 67 01 00 00    	jge    59e0 <verify+0x2b0>
    5879:	4c 39 d7             	cmp    %r10,%rdi
    587c:	7e 09                	jle    5887 <verify+0x157>
    587e:	49 39 c1             	cmp    %rax,%r9
    5881:	0f 8c 81 00 00 00    	jl     5908 <verify+0x1d8>
    5887:	4c 39 d7             	cmp    %r10,%rdi
    588a:	0f 8d 9b 01 00 00    	jge    5a2b <verify+0x2fb>
    5890:	48 83 c3 01          	add    $0x1,%rbx
    5894:	49 39 de             	cmp    %rbx,%r14
    5897:	0f 8e b9 00 00 00    	jle    5956 <verify+0x226>
    589d:	49 8b 97 08 02 00 00 	mov    0x208(%r15),%rdx
    58a4:	48 89 d8             	mov    %rbx,%rax
    58a7:	48 c1 e0 05          	shl    $0x5,%rax
    58ab:	49 03 83 08 02 00 00 	add    0x208(%r11),%rax
    58b2:	4c 01 e2             	add    %r12,%rdx
    58b5:	48 8b 08             	mov    (%rax),%rcx
    58b8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    58bc:	48 8b 32             	mov    (%rdx),%rsi
    58bf:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    58c3:	4c 8b 52 10          	mov    0x10(%rdx),%r10
    58c7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    58cb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    58cf:	48 8b 40 18          	mov    0x18(%rax),%rax
    58d3:	48 39 f1             	cmp    %rsi,%rcx
    58d6:	7c 98                	jl     5870 <verify+0x140>
    58d8:	0f 8e 32 01 00 00    	jle    5a10 <verify+0x2e0>
    58de:	4c 39 c2             	cmp    %r8,%rdx
    58e1:	0f 8f 09 01 00 00    	jg     59f0 <verify+0x2c0>
    58e7:	75 a7                	jne    5890 <verify+0x160>
    58e9:	4c 39 d7             	cmp    %r10,%rdi
    58ec:	7f a2                	jg     5890 <verify+0x160>
    58ee:	49 39 c1             	cmp    %rax,%r9
    58f1:	7d 15                	jge    5908 <verify+0x1d8>
    58f3:	48 39 f1             	cmp    %rsi,%rcx
    58f6:	75 98                	jne    5890 <verify+0x160>
    58f8:	4c 39 c2             	cmp    %r8,%rdx
    58fb:	75 93                	jne    5890 <verify+0x160>
    58fd:	4c 39 d7             	cmp    %r10,%rdi
    5900:	75 8e                	jne    5890 <verify+0x160>
    5902:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5908:	49 89 c1             	mov    %rax,%r9
    590b:	48 89 f9             	mov    %rdi,%rcx
    590e:	48 89 f2             	mov    %rsi,%rdx
    5911:	bf 01 00 00 00       	mov    $0x1,%edi
    5916:	48 8d 35 83 0b 00 00 	lea    0xb83(%rip),%rsi        # 64a0 <_IO_stdin_used+0x4a0>
    591d:	31 c0                	xor    %eax,%eax
    591f:	48 83 c3 01          	add    $0x1,%rbx
    5923:	e8 08 cb ff ff       	call   2430 <__printf_chk@plt>
    5928:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    592d:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    5932:	4c 03 18             	add    (%rax),%r11
    5935:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    593a:	4d 8b b3 18 02 00 00 	mov    0x218(%r11),%r14
    5941:	48 8b 28             	mov    (%rax),%rbp
    5944:	48 8b 04 24          	mov    (%rsp),%rax
    5948:	4c 8d 7c 05 00       	lea    0x0(%rbp,%rax,1),%r15
    594d:	49 39 de             	cmp    %rbx,%r14
    5950:	0f 8f 47 ff ff ff    	jg     589d <verify+0x16d>
    5956:	4c 89 ea             	mov    %r13,%rdx
    5959:	4d 3b af 18 02 00 00 	cmp    0x218(%r15),%r13
    5960:	7d 14                	jge    5976 <verify+0x246>
    5962:	4d 8b b3 18 02 00 00 	mov    0x218(%r11),%r14
    5969:	48 83 c2 01          	add    $0x1,%rdx
    596d:	4d 85 f6             	test   %r14,%r14
    5970:	0f 8f da fe ff ff    	jg     5850 <verify+0x120>
    5976:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    597b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5980:	48 83 c3 01          	add    $0x1,%rbx
    5984:	39 58 08             	cmp    %ebx,0x8(%rax)
    5987:	0f 8f 43 fe ff ff    	jg     57d0 <verify+0xa0>
    598d:	44 8b 6c 24 34       	mov    0x34(%rsp),%r13d
    5992:	44 8b 74 24 38       	mov    0x38(%rsp),%r14d
    5997:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
    599c:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    59a1:	48 81 04 24 80 02 00 00 	addq   $0x280,(%rsp)
    59a9:	41 83 c5 01          	add    $0x1,%r13d
    59ad:	44 39 68 08          	cmp    %r13d,0x8(%rax)
    59b1:	0f 8f da fd ff ff    	jg     5791 <verify+0x61>
    59b7:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    59bc:	48 81 44 24 08 98 00 00 00 	addq   $0x98,0x8(%rsp)
    59c5:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    59ca:	41 39 c7             	cmp    %eax,%r15d
    59cd:	74 6a                	je     5a39 <verify+0x309>
    59cf:	41 89 c4             	mov    %eax,%r12d
    59d2:	e9 91 fd ff ff       	jmp    5768 <verify+0x38>
    59d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    59e0:	0f 85 aa fe ff ff    	jne    5890 <verify+0x160>
    59e6:	e9 9c fe ff ff       	jmp    5887 <verify+0x157>
    59eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    59f0:	4c 39 d7             	cmp    %r10,%rdi
    59f3:	0f 8d f0 fe ff ff    	jge    58e9 <verify+0x1b9>
    59f9:	49 39 c1             	cmp    %rax,%r9
    59fc:	0f 8e e7 fe ff ff    	jle    58e9 <verify+0x1b9>
    5a02:	e9 01 ff ff ff       	jmp    5908 <verify+0x1d8>
    5a07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5a10:	4c 39 c2             	cmp    %r8,%rdx
    5a13:	0f 8c 6e fe ff ff    	jl     5887 <verify+0x157>
    5a19:	4c 39 d7             	cmp    %r10,%rdi
    5a1c:	0f 8e cc fe ff ff    	jle    58ee <verify+0x1be>
    5a22:	4c 39 c2             	cmp    %r8,%rdx
    5a25:	0f 85 65 fe ff ff    	jne    5890 <verify+0x160>
    5a2b:	49 39 c1             	cmp    %rax,%r9
    5a2e:	0f 8f 5c fe ff ff    	jg     5890 <verify+0x160>
    5a34:	e9 cf fe ff ff       	jmp    5908 <verify+0x1d8>
    5a39:	48 81 44 24 10 98 00 00 00 	addq   $0x98,0x10(%rsp)
    5a42:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    5a47:	41 8d 46 01          	lea    0x1(%r14),%eax
    5a4b:	45 39 f4             	cmp    %r14d,%r12d
    5a4e:	74 08                	je     5a58 <verify+0x328>
    5a50:	41 89 c6             	mov    %eax,%r14d
    5a53:	e9 01 fd ff ff       	jmp    5759 <verify+0x29>
    5a58:	48 83 c4 48          	add    $0x48,%rsp
    5a5c:	31 c0                	xor    %eax,%eax
    5a5e:	5b                   	pop    %rbx
    5a5f:	5d                   	pop    %rbp
    5a60:	41 5c                	pop    %r12
    5a62:	41 5d                	pop    %r13
    5a64:	41 5e                	pop    %r14
    5a66:	41 5f                	pop    %r15
    5a68:	c3                   	ret
    5a69:	31 c0                	xor    %eax,%eax
    5a6b:	c3                   	ret

Disassembly of section .fini:

0000000000005a6c <_fini>:
    5a6c:	f3 0f 1e fa          	endbr64
    5a70:	48 83 ec 08          	sub    $0x8,%rsp
    5a74:	48 83 c4 08          	add    $0x8,%rsp
    5a78:	c3                   	ret
