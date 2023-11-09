
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

0000000000002520 <fatal_error>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	50                   	push   %rax
    2525:	58                   	pop    %rax
    2526:	50                   	push   %rax
    2527:	e8 44 ff ff ff       	call   2470 <perror@plt>
    252c:	bf 01 00 00 00       	mov    $0x1,%edi
    2531:	e8 4a ff ff ff       	call   2480 <exit@plt>

0000000000002536 <copy_file_contents.cold>:
    2536:	48 8d 3d c2 3c 00 00 	lea    0x3cc2(%rip),%rdi        # 61ff <_IO_stdin_used+0x1ff>
    253d:	e8 de ff ff ff       	call   2520 <fatal_error>

0000000000002542 <add_write_request.cold>:
    2542:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    2548:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2550:	0f 0b                	ud2

0000000000002552 <add_read_request.cold>:
    2552:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    255a:	0f 0b                	ud2

000000000000255c <_send_static_string_content.cold>:
    255c:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    2562:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    256a:	0f 0b                	ud2

000000000000256c <add_accept_request.cold>:
    256c:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2574:	0f 0b                	ud2

0000000000002576 <io_thread.cold>:
    2576:	48 8d 3d 52 3c 00 00 	lea    0x3c52(%rip),%rdi        # 61cf <_IO_stdin_used+0x1cf>
    257d:	e8 9e ff ff ff       	call   2520 <fatal_error>
    2582:	48 8d 3d ca 3b 00 00 	lea    0x3bca(%rip),%rdi        # 6153 <_IO_stdin_used+0x153>
    2589:	e8 92 ff ff ff       	call   2520 <fatal_error>
    258e:	48 8d 3d de 3b 00 00 	lea    0x3bde(%rip),%rdi        # 6173 <_IO_stdin_used+0x173>
    2595:	e8 86 ff ff ff       	call   2520 <fatal_error>
    259a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25a2:	0f 0b                	ud2
    25a4:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25ac:	0f 0b                	ud2
    25ae:	48 8d 3d 95 3b 00 00 	lea    0x3b95(%rip),%rdi        # 614a <_IO_stdin_used+0x14a>
    25b5:	e8 66 ff ff ff       	call   2520 <fatal_error>
    25ba:	48 8d 3d ab 3b 00 00 	lea    0x3bab(%rip),%rdi        # 616c <_IO_stdin_used+0x16c>
    25c1:	e8 5a ff ff ff       	call   2520 <fatal_error>
    25c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000025d0 <main>:
    25d0:	f3 0f 1e fa          	endbr64
    25d4:	41 57                	push   %r15
    25d6:	48 8d 3d eb 3e 00 00 	lea    0x3eeb(%rip),%rdi        # 64c8 <_IO_stdin_used+0x4c8>
    25dd:	41 56                	push   %r14
    25df:	41 55                	push   %r13
    25e1:	41 54                	push   %r12
    25e3:	55                   	push   %rbp
    25e4:	53                   	push   %rbx
    25e5:	48 83 ec 68          	sub    $0x68,%rsp
    25e9:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    25f2:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    25f7:	31 c0                	xor    %eax,%eax
    25f9:	e8 d2 fc ff ff       	call   22d0 <puts@plt>
    25fe:	bf 0a 00 00 00       	mov    $0xa,%edi
    2603:	e8 b8 fc ff ff       	call   22c0 <putchar@plt>
    2608:	48 8d 3d 23 3c 00 00 	lea    0x3c23(%rip),%rdi        # 6232 <_IO_stdin_used+0x232>
    260f:	e8 bc fc ff ff       	call   22d0 <puts@plt>
    2614:	ba 06 00 00 00       	mov    $0x6,%edx
    2619:	48 8d 35 2e 3c 00 00 	lea    0x3c2e(%rip),%rsi        # 624e <_IO_stdin_used+0x24e>
    2620:	31 c0                	xor    %eax,%eax
    2622:	bf 01 00 00 00       	mov    $0x1,%edi
    2627:	e8 04 fe ff ff       	call   2430 <__printf_chk@plt>
    262c:	ba 09 00 00 00       	mov    $0x9,%edx
    2631:	48 8d 35 30 3c 00 00 	lea    0x3c30(%rip),%rsi        # 6268 <_IO_stdin_used+0x268>
    2638:	31 c0                	xor    %eax,%eax
    263a:	bf 01 00 00 00       	mov    $0x1,%edi
    263f:	e8 ec fd ff ff       	call   2430 <__printf_chk@plt>
    2644:	ba 01 00 00 00       	mov    $0x1,%edx
    2649:	48 8d 35 2c 3c 00 00 	lea    0x3c2c(%rip),%rsi        # 627c <_IO_stdin_used+0x27c>
    2650:	31 c0                	xor    %eax,%eax
    2652:	bf 01 00 00 00       	mov    $0x1,%edi
    2657:	e8 d4 fd ff ff       	call   2430 <__printf_chk@plt>
    265c:	ba 01 00 00 00       	mov    $0x1,%edx
    2661:	48 8d 35 25 3c 00 00 	lea    0x3c25(%rip),%rsi        # 628d <_IO_stdin_used+0x28d>
    2668:	31 c0                	xor    %eax,%eax
    266a:	bf 01 00 00 00       	mov    $0x1,%edi
    266f:	e8 bc fd ff ff       	call   2430 <__printf_chk@plt>
    2674:	ba 01 00 00 00       	mov    $0x1,%edx
    2679:	48 8d 35 25 3c 00 00 	lea    0x3c25(%rip),%rsi        # 62a5 <_IO_stdin_used+0x2a5>
    2680:	31 c0                	xor    %eax,%eax
    2682:	bf 01 00 00 00       	mov    $0x1,%edi
    2687:	e8 a4 fd ff ff       	call   2430 <__printf_chk@plt>
    268c:	ba 01 00 00 00       	mov    $0x1,%edx
    2691:	48 8d 35 90 3e 00 00 	lea    0x3e90(%rip),%rsi        # 6528 <_IO_stdin_used+0x528>
    2698:	31 c0                	xor    %eax,%eax
    269a:	bf 01 00 00 00       	mov    $0x1,%edi
    269f:	e8 8c fd ff ff       	call   2430 <__printf_chk@plt>
    26a4:	ba 01 00 00 00       	mov    $0x1,%edx
    26a9:	48 8d 35 a8 3e 00 00 	lea    0x3ea8(%rip),%rsi        # 6558 <_IO_stdin_used+0x558>
    26b0:	31 c0                	xor    %eax,%eax
    26b2:	bf 01 00 00 00       	mov    $0x1,%edi
    26b7:	e8 74 fd ff ff       	call   2430 <__printf_chk@plt>
    26bc:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    26c1:	48 8d 35 f9 3b 00 00 	lea    0x3bf9(%rip),%rsi        # 62c1 <_IO_stdin_used+0x2c1>
    26c8:	31 c0                	xor    %eax,%eax
    26ca:	bf 01 00 00 00       	mov    $0x1,%edi
    26cf:	e8 5c fd ff ff       	call   2430 <__printf_chk@plt>
    26d4:	ba 1e 00 00 00       	mov    $0x1e,%edx
    26d9:	48 8d 35 fb 3b 00 00 	lea    0x3bfb(%rip),%rsi        # 62db <_IO_stdin_used+0x2db>
    26e0:	31 c0                	xor    %eax,%eax
    26e2:	bf 01 00 00 00       	mov    $0x1,%edi
    26e7:	e8 44 fd ff ff       	call   2430 <__printf_chk@plt>
    26ec:	48 8d 3d db 39 00 00 	lea    0x39db(%rip),%rdi        # 60ce <_IO_stdin_used+0xce>
    26f3:	e8 d8 fb ff ff       	call   22d0 <puts@plt>
    26f8:	be 18 00 00 00       	mov    $0x18,%esi
    26fd:	bf 01 00 00 00       	mov    $0x1,%edi
    2702:	e8 79 fc ff ff       	call   2380 <calloc@plt>
    2707:	be 98 00 00 00       	mov    $0x98,%esi
    270c:	bf 09 00 00 00       	mov    $0x9,%edi
    2711:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2716:	e8 65 fc ff ff       	call   2380 <calloc@plt>
    271b:	be 10 00 00 00       	mov    $0x10,%esi
    2720:	bf 01 00 00 00       	mov    $0x1,%edi
    2725:	48 89 04 24          	mov    %rax,(%rsp)
    2729:	e8 52 fc ff ff       	call   2380 <calloc@plt>
    272e:	be 10 00 00 00       	mov    $0x10,%esi
    2733:	bf 01 00 00 00       	mov    $0x1,%edi
    2738:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    273e:	48 89 c3             	mov    %rax,%rbx
    2741:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2746:	e8 35 fc ff ff       	call   2380 <calloc@plt>
    274b:	4c 8b 14 24          	mov    (%rsp),%r10
    274f:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
    2757:	31 c9                	xor    %ecx,%ecx
    2759:	48 89 43 08          	mov    %rax,0x8(%rbx)
    275d:	49 89 c8             	mov    %rcx,%r8
    2760:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    2767:	4d 89 d4             	mov    %r10,%r12
    276a:	4c 89 54 24 40       	mov    %r10,0x40(%rsp)
    276f:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    2774:	0f 1f 40 00          	nopl   0x0(%rax)
    2778:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    277d:	45 89 04 24          	mov    %r8d,(%r12)
    2781:	be 10 00 00 00       	mov    $0x10,%esi
    2786:	31 db                	xor    %ebx,%ebx
    2788:	41 c7 44 24 28 07 00 00 00 	movl   $0x7,0x28(%r12)
    2791:	bf 64 00 00 00       	mov    $0x64,%edi
    2796:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    279b:	48 8b 05 4e 42 00 00 	mov    0x424e(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    27a2:	44 89 04 24          	mov    %r8d,(%rsp)
    27a6:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    27ab:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    27b0:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    27b5:	49 89 44 24 30       	mov    %rax,0x30(%r12)
    27ba:	e8 c1 fb ff ff       	call   2380 <calloc@plt>
    27bf:	be 10 00 00 00       	mov    $0x10,%esi
    27c4:	bf 64 00 00 00       	mov    $0x64,%edi
    27c9:	49 89 44 24 50       	mov    %rax,0x50(%r12)
    27ce:	e8 ad fb ff ff       	call   2380 <calloc@plt>
    27d3:	be 28 00 00 00       	mov    $0x28,%esi
    27d8:	bf 64 00 00 00       	mov    $0x64,%edi
    27dd:	66 0f 6f 15 eb 41 00 00 	movdqa 0x41eb(%rip),%xmm2        # 69d0 <_IO_stdin_used+0x9d0>
    27e5:	49 89 44 24 58       	mov    %rax,0x58(%r12)
    27ea:	41 0f 11 54 24 68    	movups %xmm2,0x68(%r12)
    27f0:	e8 8b fb ff ff       	call   2380 <calloc@plt>
    27f5:	be 80 02 00 00       	mov    $0x280,%esi
    27fa:	bf 07 00 00 00       	mov    $0x7,%edi
    27ff:	66 0f 6f 1d c9 41 00 00 	movdqa 0x41c9(%rip),%xmm3        # 69d0 <_IO_stdin_used+0x9d0>
    2807:	49 89 44 24 78       	mov    %rax,0x78(%r12)
    280c:	41 0f 11 9c 24 80 00 00 00 	movups %xmm3,0x80(%r12)
    2815:	e8 66 fb ff ff       	call   2380 <calloc@plt>
    281a:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
    281f:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    2824:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
    2829:	49 89 c7             	mov    %rax,%r15
    282c:	0f 1f 40 00          	nopl   0x0(%rax)
    2830:	4c 63 f3             	movslq %ebx,%r14
    2833:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
    2838:	4f 8d 2c b6          	lea    (%r14,%r14,4),%r13
    283c:	49 c1 e5 07          	shl    $0x7,%r13
    2840:	44 39 e3             	cmp    %r12d,%ebx
    2843:	0f 84 e7 09 00 00    	je     3230 <main+0xc60>
    2849:	be 20 00 00 00       	mov    $0x20,%esi
    284e:	bf 06 00 00 00       	mov    $0x6,%edi
    2853:	e8 28 fb ff ff       	call   2380 <calloc@plt>
    2858:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    285c:	4c 89 64 24 18       	mov    %r12,0x18(%rsp)
    2861:	48 8d a8 c0 00 00 00 	lea    0xc0(%rax),%rbp
    2868:	4b 89 84 2f 28 02 00 00 	mov    %rax,0x228(%r15,%r13,1)
    2870:	49 89 c7             	mov    %rax,%r15
    2873:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2878:	be 08 00 00 00       	mov    $0x8,%esi
    287d:	bf 01 00 00 00       	mov    $0x1,%edi
    2882:	49 83 c7 20          	add    $0x20,%r15
    2886:	e8 f5 fa ff ff       	call   2380 <calloc@plt>
    288b:	be 08 00 00 00       	mov    $0x8,%esi
    2890:	bf 01 00 00 00       	mov    $0x1,%edi
    2895:	49 89 c4             	mov    %rax,%r12
    2898:	e8 e3 fa ff ff       	call   2380 <calloc@plt>
    289d:	be 00 01 00 00       	mov    $0x100,%esi
    28a2:	bf 02 00 00 00       	mov    $0x2,%edi
    28a7:	48 89 c3             	mov    %rax,%rbx
    28aa:	e8 d1 fa ff ff       	call   2380 <calloc@plt>
    28af:	66 0f 6f 05 29 41 00 00 	movdqa 0x4129(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
    28b7:	48 8d b0 00 01 00 00 	lea    0x100(%rax),%rsi
    28be:	49 89 47 e0          	mov    %rax,-0x20(%r15)
    28c2:	49 89 77 e8          	mov    %rsi,-0x18(%r15)
    28c6:	4c 89 20             	mov    %r12,(%rax)
    28c9:	48 89 98 00 01 00 00 	mov    %rbx,0x100(%rax)
    28d0:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
    28d7:	0f 29 80 80 01 00 00 	movaps %xmm0,0x180(%rax)
    28de:	4c 39 fd             	cmp    %r15,%rbp
    28e1:	75 95                	jne    2878 <main+0x2a8>
    28e3:	be 01 00 00 00       	mov    $0x1,%esi
    28e8:	bf 00 01 00 00       	mov    $0x100,%edi
    28ed:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    28f1:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    28f6:	e8 85 fa ff ff       	call   2380 <calloc@plt>
    28fb:	bf 18 00 00 00       	mov    $0x18,%edi
    2900:	48 89 c5             	mov    %rax,%rbp
    2903:	e8 e8 fa ff ff       	call   23f0 <malloc@plt>
    2908:	44 8b 04 24          	mov    (%rsp),%r8d
    290c:	48 89 ef             	mov    %rbp,%rdi
    290f:	41 89 d9             	mov    %ebx,%r9d
    2912:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2917:	48 8d 0d 62 3c 00 00 	lea    0x3c62(%rip),%rcx        # 6580 <_IO_stdin_used+0x580>
    291e:	ba 00 01 00 00       	mov    $0x100,%edx
    2923:	31 c0                	xor    %eax,%eax
    2925:	be 01 00 00 00       	mov    $0x1,%esi
    292a:	e8 d1 fb ff ff       	call   2500 <__sprintf_chk@plt>
    292f:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    2934:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    2939:	ba ab aa aa aa       	mov    $0xaaaaaaab,%edx
    293e:	be 20 00 00 00       	mov    $0x20,%esi
    2943:	bf 3f 42 0f 00       	mov    $0xf423f,%edi
    2948:	4d 89 72 10          	mov    %r14,0x10(%r10)
    294c:	44 8d 73 01          	lea    0x1(%rbx),%r14d
    2950:	4c 8b 78 20          	mov    0x20(%rax),%r15
    2954:	44 89 f0             	mov    %r14d,%eax
    2957:	44 89 f1             	mov    %r14d,%ecx
    295a:	49 89 2a             	mov    %rbp,(%r10)
    295d:	48 0f af c2          	imul   %rdx,%rax
    2961:	4b 8d 2c 2f          	lea    (%r15,%r13,1),%rbp
    2965:	4d 89 62 08          	mov    %r12,0x8(%r10)
    2969:	4c 89 95 40 02 00 00 	mov    %r10,0x240(%rbp)
    2970:	48 c7 85 10 02 00 00 3f 42 0f 00 	movq   $0xf423f,0x210(%rbp)
    297b:	48 c1 e8 22          	shr    $0x22,%rax
    297f:	8d 04 40             	lea    (%rax,%rax,2),%eax
    2982:	01 c0                	add    %eax,%eax
    2984:	29 c1                	sub    %eax,%ecx
    2986:	89 8d 48 02 00 00    	mov    %ecx,0x248(%rbp)
    298c:	e8 ef f9 ff ff       	call   2380 <calloc@plt>
    2991:	8b 0c 24             	mov    (%rsp),%ecx
    2994:	89 5d 00             	mov    %ebx,0x0(%rbp)
    2997:	48 89 85 08 02 00 00 	mov    %rax,0x208(%rbp)
    299e:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    29a3:	48 c7 85 18 02 00 00 00 00 00 00 	movq   $0x0,0x218(%rbp)
    29ae:	48 89 85 28 01 00 00 	mov    %rax,0x128(%rbp)
    29b5:	48 8b 05 3c 40 00 00 	mov    0x403c(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
    29bc:	89 8d 30 01 00 00    	mov    %ecx,0x130(%rbp)
    29c2:	48 89 85 80 01 00 00 	mov    %rax,0x180(%rbp)
    29c9:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
    29d3:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
    29dd:	c7 85 34 01 00 00 06 00 00 00 	movl   $0x6,0x134(%rbp)
    29e7:	48 89 85 38 02 00 00 	mov    %rax,0x238(%rbp)
    29ee:	83 fb 05             	cmp    $0x5,%ebx
    29f1:	0f 84 19 08 00 00    	je     3210 <main+0xc40>
    29f7:	8b 44 24 20          	mov    0x20(%rsp),%eax
    29fb:	39 c3                	cmp    %eax,%ebx
    29fd:	75 61                	jne    2a60 <main+0x490>
    29ff:	8b 5c 24 28          	mov    0x28(%rsp),%ebx
    2a03:	85 db                	test   %ebx,%ebx
    2a05:	7f 59                	jg     2a60 <main+0x490>
    2a07:	89 ca                	mov    %ecx,%edx
    2a09:	bf 01 00 00 00       	mov    $0x1,%edi
    2a0e:	48 8d 35 93 3b 00 00 	lea    0x3b93(%rip),%rsi        # 65a8 <_IO_stdin_used+0x5a8>
    2a15:	31 c0                	xor    %eax,%eax
    2a17:	e8 14 fa ff ff       	call   2430 <__printf_chk@plt>
    2a1c:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    2a21:	48 63 c3             	movslq %ebx,%rax
    2a24:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    2a29:	48 89 c1             	mov    %rax,%rcx
    2a2c:	48 c1 e0 04          	shl    $0x4,%rax
    2a30:	48 01 f8             	add    %rdi,%rax
    2a33:	4c 8b 7a 20          	mov    0x20(%rdx),%r15
    2a37:	48 89 42 38          	mov    %rax,0x38(%rdx)
    2a3b:	48 8d 05 be 2b 00 00 	lea    0x2bbe(%rip),%rax        # 5600 <barriered_work_ingest>
    2a42:	4b 89 84 2f 18 01 00 00 	mov    %rax,0x118(%r15,%r13,1)
    2a4a:	8d 41 01             	lea    0x1(%rcx),%eax
    2a4d:	89 44 24 28          	mov    %eax,0x28(%rsp)
    2a51:	41 83 fe 07          	cmp    $0x7,%r14d
    2a55:	74 1d                	je     2a74 <main+0x4a4>
    2a57:	44 89 f3             	mov    %r14d,%ebx
    2a5a:	e9 d1 fd ff ff       	jmp    2830 <main+0x260>
    2a5f:	90                   	nop
    2a60:	48 8d 05 19 28 00 00 	lea    0x2819(%rip),%rax        # 5280 <barriered_work>
    2a67:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
    2a6e:	41 83 fe 07          	cmp    $0x7,%r14d
    2a72:	75 e3                	jne    2a57 <main+0x487>
    2a74:	48 8d 05 05 09 00 00 	lea    0x905(%rip),%rax        # 3380 <barriered_reset>
    2a7b:	4d 89 e0             	mov    %r12,%r8
    2a7e:	4c 8b 64 24 08       	mov    0x8(%rsp),%r12
    2a83:	41 c7 87 80 0f 00 00 00 00 00 00 	movl   $0x0,0xf80(%r15)
    2a8e:	49 89 87 18 10 00 00 	mov    %rax,0x1018(%r15)
    2a95:	8b 04 24             	mov    (%rsp),%eax
    2a98:	49 83 c0 01          	add    $0x1,%r8
    2a9c:	4d 89 a7 28 10 00 00 	mov    %r12,0x1028(%r15)
    2aa3:	49 81 c4 98 00 00 00 	add    $0x98,%r12
    2aaa:	41 89 87 30 10 00 00 	mov    %eax,0x1030(%r15)
    2ab1:	48 8b 05 40 3f 00 00 	mov    0x3f40(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
    2ab8:	41 c7 87 00 0f 00 00 06 00 00 00 	movl   $0x6,0xf00(%r15)
    2ac3:	41 c7 87 34 10 00 00 06 00 00 00 	movl   $0x6,0x1034(%r15)
    2ace:	41 c7 87 3c 11 00 00 06 00 00 00 	movl   $0x6,0x113c(%r15)
    2ad9:	49 89 87 80 10 00 00 	mov    %rax,0x1080(%r15)
    2ae0:	49 83 f8 09          	cmp    $0x9,%r8
    2ae4:	0f 85 8e fc ff ff    	jne    2778 <main+0x1a8>
    2aea:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    2aef:	4c 8b 44 24 48       	mov    0x48(%rsp),%r8
    2af4:	b9 01 00 00 00       	mov    $0x1,%ecx
    2af9:	49 8d b2 b0 03 00 00 	lea    0x3b0(%r10),%rsi
    2b00:	4d 8d 6a 20          	lea    0x20(%r10),%r13
    2b04:	4d 89 92 38 04 00 00 	mov    %r10,0x438(%r10)
    2b0b:	41 c7 82 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r10)
    2b16:	4c 89 e8             	mov    %r13,%rax
    2b19:	41 c7 82 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r10)
    2b24:	41 c7 82 50 04 00 00 07 00 00 00 	movl   $0x7,0x450(%r10)
    2b2f:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    2b34:	0f 1f 40 00          	nopl   0x0(%rax)
    2b38:	48 8b 10             	mov    (%rax),%rdx
    2b3b:	89 cf                	mov    %ecx,%edi
    2b3d:	87 ba 00 02 00 00    	xchg   %edi,0x200(%rdx)
    2b43:	48 05 98 00 00 00    	add    $0x98,%rax
    2b49:	48 39 f0             	cmp    %rsi,%rax
    2b4c:	75 ea                	jne    2b38 <main+0x568>
    2b4e:	be 38 00 00 00       	mov    $0x38,%esi
    2b53:	bf 09 00 00 00       	mov    $0x9,%edi
    2b58:	4c 89 44 24 28       	mov    %r8,0x28(%rsp)
    2b5d:	45 31 f6             	xor    %r14d,%r14d
    2b60:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2b65:	4c 8d 3d a4 08 00 00 	lea    0x8a4(%rip),%r15        # 3410 <barriered_thread>
    2b6c:	e8 0f f8 ff ff       	call   2380 <calloc@plt>
    2b71:	be 38 00 00 00       	mov    $0x38,%esi
    2b76:	bf 09 00 00 00       	mov    $0x9,%edi
    2b7b:	48 89 c3             	mov    %rax,%rbx
    2b7e:	e8 fd f7 ff ff       	call   2380 <calloc@plt>
    2b83:	be 38 00 00 00       	mov    $0x38,%esi
    2b88:	bf 09 00 00 00       	mov    $0x9,%edi
    2b8d:	48 89 04 24          	mov    %rax,(%rsp)
    2b91:	e8 ea f7 ff ff       	call   2380 <calloc@plt>
    2b96:	be 08 00 00 00       	mov    $0x8,%esi
    2b9b:	bf 09 00 00 00       	mov    $0x9,%edi
    2ba0:	48 89 c5             	mov    %rax,%rbp
    2ba3:	e8 d8 f7 ff ff       	call   2380 <calloc@plt>
    2ba8:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2bad:	ba 06 00 00 00       	mov    $0x6,%edx
    2bb2:	48 8d 35 36 37 00 00 	lea    0x3736(%rip),%rsi        # 62ef <_IO_stdin_used+0x2ef>
    2bb9:	49 89 c4             	mov    %rax,%r12
    2bbc:	48 8b 05 3d 3e 00 00 	mov    0x3e3d(%rip),%rax        # 6a00 <_IO_stdin_used+0xa00>
    2bc3:	bf 01 00 00 00       	mov    $0x1,%edi
    2bc8:	4d 89 92 a0 03 00 00 	mov    %r10,0x3a0(%r10)
    2bcf:	49 89 82 b8 03 00 00 	mov    %rax,0x3b8(%r10)
    2bd6:	31 c0                	xor    %eax,%eax
    2bd8:	41 c7 82 a8 03 00 00 06 00 00 00 	movl   $0x6,0x3a8(%r10)
    2be3:	49 c7 82 90 03 00 00 00 00 00 00 	movq   $0x0,0x390(%r10)
    2bee:	e8 3d f8 ff ff       	call   2430 <__printf_chk@plt>
    2bf3:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2bf8:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
    2bfd:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2c04:	48 8d 15 b5 0b 00 00 	lea    0xbb5(%rip),%rdx        # 37c0 <timer_thread>
    2c0b:	49 8d 8a 90 03 00 00 	lea    0x390(%r10),%rcx
    2c12:	e8 39 f8 ff ff       	call   2450 <pthread_create@plt>
    2c17:	4c 89 e0             	mov    %r12,%rax
    2c1a:	4c 89 64 24 18       	mov    %r12,0x18(%rsp)
    2c1f:	45 89 f4             	mov    %r14d,%r12d
    2c22:	4d 89 ee             	mov    %r13,%r14
    2c25:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    2c2a:	48 89 6c 24 10       	mov    %rbp,0x10(%rsp)
    2c2f:	48 89 c5             	mov    %rax,%rbp
    2c32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    2c38:	41 c7 45 04 01 00 00 00 	movl   $0x1,0x4(%r13)
    2c40:	44 89 e2             	mov    %r12d,%edx
    2c43:	bf 01 00 00 00       	mov    $0x1,%edi
    2c48:	31 c0                	xor    %eax,%eax
    2c4a:	41 c7 45 2c 01 00 00 00 	movl   $0x1,0x2c(%r13)
    2c52:	48 8d 35 6f 39 00 00 	lea    0x396f(%rip),%rsi        # 65c8 <_IO_stdin_used+0x5c8>
    2c59:	41 83 c4 01          	add    $0x1,%r12d
    2c5d:	e8 ce f7 ff ff       	call   2430 <__printf_chk@plt>
    2c62:	4c 89 e9             	mov    %r13,%rcx
    2c65:	48 89 de             	mov    %rbx,%rsi
    2c68:	48 89 ef             	mov    %rbp,%rdi
    2c6b:	4c 89 fa             	mov    %r15,%rdx
    2c6e:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    2c75:	48 83 c5 08          	add    $0x8,%rbp
    2c79:	48 83 c3 38          	add    $0x38,%rbx
    2c7d:	e8 ce f7 ff ff       	call   2450 <pthread_create@plt>
    2c82:	41 83 fc 06          	cmp    $0x6,%r12d
    2c86:	75 b0                	jne    2c38 <main+0x668>
    2c88:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2c8d:	48 8b 1d 74 3d 00 00 	mov    0x3d74(%rip),%rbx        # 6a08 <_IO_stdin_used+0xa08>
    2c94:	be d8 00 00 00       	mov    $0xd8,%esi
    2c99:	4d 89 f5             	mov    %r14,%r13
    2c9c:	bf 01 00 00 00       	mov    $0x1,%edi
    2ca1:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    2ca6:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    2cab:	45 31 f6             	xor    %r14d,%r14d
    2cae:	49 89 9a 50 04 00 00 	mov    %rbx,0x450(%r10)
    2cb5:	41 c7 82 2c 04 00 00 02 00 00 00 	movl   $0x2,0x42c(%r10)
    2cc0:	e8 bb f6 ff ff       	call   2380 <calloc@plt>
    2cc5:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2cca:	be 00 08 00 00       	mov    $0x800,%esi
    2ccf:	31 ff                	xor    %edi,%edi
    2cd1:	49 89 82 68 04 00 00 	mov    %rax,0x468(%r10)
    2cd8:	e8 b3 f7 ff ff       	call   2490 <eventfd@plt>
    2cdd:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2ce2:	ba 07 00 00 00       	mov    $0x7,%edx
    2ce7:	48 8d 35 1f 36 00 00 	lea    0x361f(%rip),%rsi        # 630d <_IO_stdin_used+0x30d>
    2cee:	bf 01 00 00 00       	mov    $0x1,%edi
    2cf3:	41 89 82 70 04 00 00 	mov    %eax,0x470(%r10)
    2cfa:	31 c0                	xor    %eax,%eax
    2cfc:	4d 89 92 38 04 00 00 	mov    %r10,0x438(%r10)
    2d03:	41 c7 82 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r10)
    2d0e:	41 c7 82 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r10)
    2d19:	e8 12 f7 ff ff       	call   2430 <__printf_chk@plt>
    2d1e:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2d23:	48 8b 34 24          	mov    (%rsp),%rsi
    2d27:	49 8d 7c 24 38       	lea    0x38(%r12),%rdi
    2d2c:	48 8d 15 5d 1d 00 00 	lea    0x1d5d(%rip),%rdx        # 4a90 <io_thread>
    2d33:	49 8d 8a 28 04 00 00 	lea    0x428(%r10),%rcx
    2d3a:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2d41:	e8 0a f7 ff ff       	call   2450 <pthread_create@plt>
    2d46:	ba 08 00 00 00       	mov    $0x8,%edx
    2d4b:	48 8d 35 d2 35 00 00 	lea    0x35d2(%rip),%rsi        # 6324 <_IO_stdin_used+0x324>
    2d52:	31 c0                	xor    %eax,%eax
    2d54:	bf 01 00 00 00       	mov    $0x1,%edi
    2d59:	e8 d2 f6 ff ff       	call   2430 <__printf_chk@plt>
    2d5e:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2d63:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    2d68:	48 8d b5 c0 01 00 00 	lea    0x1c0(%rbp),%rsi
    2d6f:	49 8d 7c 24 40       	lea    0x40(%r12),%rdi
    2d74:	48 8d 15 85 09 00 00 	lea    0x985(%rip),%rdx        # 3700 <external_thread>
    2d7b:	49 8d 8a c0 04 00 00 	lea    0x4c0(%r10),%rcx
    2d82:	4c 89 14 24          	mov    %r10,(%rsp)
    2d86:	48 8d 6c 24 50       	lea    0x50(%rsp),%rbp
    2d8b:	49 89 82 f8 04 00 00 	mov    %rax,0x4f8(%r10)
    2d92:	48 8b 05 57 3c 00 00 	mov    0x3c57(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    2d99:	49 89 9a e8 04 00 00 	mov    %rbx,0x4e8(%r10)
    2da0:	48 8d 1d b8 35 00 00 	lea    0x35b8(%rip),%rbx        # 635f <_IO_stdin_used+0x35f>
    2da7:	49 89 82 d8 04 00 00 	mov    %rax,0x4d8(%r10)
    2dae:	48 8b 05 5b 3c 00 00 	mov    0x3c5b(%rip),%rax        # 6a10 <_IO_stdin_used+0xa10>
    2db5:	4d 89 92 d0 04 00 00 	mov    %r10,0x4d0(%r10)
    2dbc:	49 89 82 c0 04 00 00 	mov    %rax,0x4c0(%r10)
    2dc3:	e8 88 f6 ff ff       	call   2450 <pthread_create@plt>
    2dc8:	48 8d 3d 72 35 00 00 	lea    0x3572(%rip),%rdi        # 6341 <_IO_stdin_used+0x341>
    2dcf:	e8 fc f4 ff ff       	call   22d0 <puts@plt>
    2dd4:	4c 8b 3c 24          	mov    (%rsp),%r15
    2dd8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    2de0:	4b 8b 3c f4          	mov    (%r12,%r14,8),%rdi
    2de4:	48 89 ee             	mov    %rbp,%rsi
    2de7:	e8 e4 f6 ff ff       	call   24d0 <pthread_join@plt>
    2dec:	44 89 f2             	mov    %r14d,%edx
    2def:	48 89 de             	mov    %rbx,%rsi
    2df2:	bf 01 00 00 00       	mov    $0x1,%edi
    2df7:	31 c0                	xor    %eax,%eax
    2df9:	49 83 c6 01          	add    $0x1,%r14
    2dfd:	e8 2e f6 ff ff       	call   2430 <__printf_chk@plt>
    2e02:	49 83 fe 09          	cmp    $0x9,%r14
    2e06:	75 d8                	jne    2de0 <main+0x810>
    2e08:	4d 89 fa             	mov    %r15,%r10
    2e0b:	31 ed                	xor    %ebp,%ebp
    2e0d:	31 c9                	xor    %ecx,%ecx
    2e0f:	45 31 c9             	xor    %r9d,%r9d
    2e12:	45 31 e4             	xor    %r12d,%r12d
    2e15:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2e1a:	45 31 db             	xor    %r11d,%r11d
    2e1d:	31 db                	xor    %ebx,%ebx
    2e1f:	4c 89 24 24          	mov    %r12,(%rsp)
    2e23:	4d 89 de             	mov    %r11,%r14
    2e26:	49 bf db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r15
    2e30:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    2e35:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    2e3a:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    2e3f:	90                   	nop
    2e40:	49 63 45 08          	movslq 0x8(%r13),%rax
    2e44:	85 c0                	test   %eax,%eax
    2e46:	0f 8e a6 00 00 00    	jle    2ef2 <main+0x922>
    2e4c:	49 8b 4d 00          	mov    0x0(%r13),%rcx
    2e50:	48 8d 34 80          	lea    (%rax,%rax,4),%rsi
    2e54:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    2e59:	48 c1 e6 07          	shl    $0x7,%rsi
    2e5d:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2e62:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    2e67:	48 8d 91 08 01 00 00 	lea    0x108(%rcx),%rdx
    2e6e:	48 8b 0c 24          	mov    (%rsp),%rcx
    2e72:	48 01 d6             	add    %rdx,%rsi
    2e75:	0f 1f 00             	nopl   (%rax)
    2e78:	48 03 0a             	add    (%rdx),%rcx
    2e7b:	48 8b 82 20 01 00 00 	mov    0x120(%rdx),%rax
    2e82:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
    2e89:	4c 03 82 88 fd ff ff 	add    -0x278(%rdx),%r8
    2e90:	4c 03 b2 98 fe ff ff 	add    -0x168(%rdx),%r14
    2e97:	48 03 68 10          	add    0x10(%rax),%rbp
    2e9b:	48 03 58 18          	add    0x18(%rax),%rbx
    2e9f:	48 03 68 30          	add    0x30(%rax),%rbp
    2ea3:	48 03 58 38          	add    0x38(%rax),%rbx
    2ea7:	48 03 68 50          	add    0x50(%rax),%rbp
    2eab:	48 03 58 58          	add    0x58(%rax),%rbx
    2eaf:	48 03 68 70          	add    0x70(%rax),%rbp
    2eb3:	48 03 58 78          	add    0x78(%rax),%rbx
    2eb7:	48 03 a8 90 00 00 00 	add    0x90(%rax),%rbp
    2ebe:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
    2ec5:	4c 03 8a a8 fe ff ff 	add    -0x158(%rdx),%r9
    2ecc:	48 03 a8 b0 00 00 00 	add    0xb0(%rax),%rbp
    2ed3:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
    2eda:	48 39 f2             	cmp    %rsi,%rdx
    2edd:	75 99                	jne    2e78 <main+0x8a8>
    2edf:	48 89 0c 24          	mov    %rcx,(%rsp)
    2ee3:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    2ee8:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2eed:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    2ef2:	45 31 e4             	xor    %r12d,%r12d
    2ef5:	49 83 7d 50 00       	cmpq   $0x0,0x50(%r13)
    2efa:	7e 73                	jle    2f6f <main+0x99f>
    2efc:	4c 89 ed             	mov    %r13,%rbp
    2eff:	49 89 dd             	mov    %rbx,%r13
    2f02:	4c 89 e3             	mov    %r12,%rbx
    2f05:	0f 1f 00             	nopl   (%rax)
    2f08:	48 8b 7d 30          	mov    0x30(%rbp),%rdi
    2f0c:	48 89 de             	mov    %rbx,%rsi
    2f0f:	48 83 c3 01          	add    $0x1,%rbx
    2f13:	48 c1 e6 04          	shl    $0x4,%rsi
    2f17:	48 01 f7             	add    %rsi,%rdi
    2f1a:	48 03 75 38          	add    0x38(%rbp),%rsi
    2f1e:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    2f22:	48 2b 57 08          	sub    0x8(%rdi),%rdx
    2f26:	48 89 d0             	mov    %rdx,%rax
    2f29:	49 f7 e7             	mul    %r15
    2f2c:	31 c0                	xor    %eax,%eax
    2f2e:	48 89 d1             	mov    %rdx,%rcx
    2f31:	48 8b 16             	mov    (%rsi),%rdx
    2f34:	48 8d 35 38 34 00 00 	lea    0x3438(%rip),%rsi        # 6373 <_IO_stdin_used+0x373>
    2f3b:	48 2b 17             	sub    (%rdi),%rdx
    2f3e:	48 c1 e9 12          	shr    $0x12,%rcx
    2f42:	bf 01 00 00 00       	mov    $0x1,%edi
    2f47:	e8 e4 f4 ff ff       	call   2430 <__printf_chk@plt>
    2f4c:	48 8b 55 40          	mov    0x40(%rbp),%rdx
    2f50:	bf 01 00 00 00       	mov    $0x1,%edi
    2f55:	31 c0                	xor    %eax,%eax
    2f57:	48 8d 35 33 34 00 00 	lea    0x3433(%rip),%rsi        # 6391 <_IO_stdin_used+0x391>
    2f5e:	e8 cd f4 ff ff       	call   2430 <__printf_chk@plt>
    2f63:	48 39 5d 50          	cmp    %rbx,0x50(%rbp)
    2f67:	7f 9f                	jg     2f08 <main+0x938>
    2f69:	4c 89 eb             	mov    %r13,%rbx
    2f6c:	49 89 ed             	mov    %rbp,%r13
    2f6f:	45 31 e4             	xor    %r12d,%r12d
    2f72:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    2f77:	0f 8e 92 00 00 00    	jle    300f <main+0xa3f>
    2f7d:	4c 89 ed             	mov    %r13,%rbp
    2f80:	49 89 dd             	mov    %rbx,%r13
    2f83:	4c 89 e3             	mov    %r12,%rbx
    2f86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    2f90:	48 8b 45 58          	mov    0x58(%rbp),%rax
    2f94:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    2f98:	48 83 ec 08          	sub    $0x8,%rsp
    2f9c:	48 8d 35 4d 36 00 00 	lea    0x364d(%rip),%rsi        # 65f0 <_IO_stdin_used+0x5f0>
    2fa3:	bf 01 00 00 00       	mov    $0x1,%edi
    2fa8:	48 83 c3 01          	add    $0x1,%rbx
    2fac:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    2fb0:	4c 8b 61 18          	mov    0x18(%rcx),%r12
    2fb4:	4c 2b 61 08          	sub    0x8(%rcx),%r12
    2fb8:	4c 89 e0             	mov    %r12,%rax
    2fbb:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    2fbf:	4c 2b 01             	sub    (%rcx),%r8
    2fc2:	49 f7 e7             	mul    %r15
    2fc5:	8b 49 20             	mov    0x20(%rcx),%ecx
    2fc8:	41 54                	push   %r12
    2fca:	31 c0                	xor    %eax,%eax
    2fcc:	48 c1 ea 12          	shr    $0x12,%rdx
    2fd0:	49 89 d1             	mov    %rdx,%r9
    2fd3:	ba 06 00 00 00       	mov    $0x6,%edx
    2fd8:	e8 53 f4 ff ff       	call   2430 <__printf_chk@plt>
    2fdd:	48 8d 35 c9 33 00 00 	lea    0x33c9(%rip),%rsi        # 63ad <_IO_stdin_used+0x3ad>
    2fe4:	bf 01 00 00 00       	mov    $0x1,%edi
    2fe9:	48 b8 ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%rax
    2ff3:	49 f7 e4             	mul    %r12
    2ff6:	31 c0                	xor    %eax,%eax
    2ff8:	48 c1 ea 02          	shr    $0x2,%rdx
    2ffc:	e8 2f f4 ff ff       	call   2430 <__printf_chk@plt>
    3001:	58                   	pop    %rax
    3002:	5a                   	pop    %rdx
    3003:	48 39 5d 68          	cmp    %rbx,0x68(%rbp)
    3007:	7f 87                	jg     2f90 <main+0x9c0>
    3009:	4c 89 eb             	mov    %r13,%rbx
    300c:	49 89 ed             	mov    %rbp,%r13
    300f:	49 8b 55 70          	mov    0x70(%r13),%rdx
    3013:	48 8d 35 87 33 00 00 	lea    0x3387(%rip),%rsi        # 63a1 <_IO_stdin_used+0x3a1>
    301a:	bf 01 00 00 00       	mov    $0x1,%edi
    301f:	31 c0                	xor    %eax,%eax
    3021:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    3028:	e8 03 f4 ff ff       	call   2430 <__printf_chk@plt>
    302d:	4c 39 6c 24 20       	cmp    %r13,0x20(%rsp)
    3032:	0f 85 08 fe ff ff    	jne    2e40 <main+0x870>
    3038:	4c 8b 24 24          	mov    (%rsp),%r12
    303c:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3041:	bf 01 00 00 00       	mov    $0x1,%edi
    3046:	31 c0                	xor    %eax,%eax
    3048:	4c 8b 54 24 28       	mov    0x28(%rsp),%r10
    304d:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    3052:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
    3057:	48 8d 35 61 33 00 00 	lea    0x3361(%rip),%rsi        # 63bf <_IO_stdin_used+0x3bf>
    305e:	4c 89 e2             	mov    %r12,%rdx
    3061:	4c 89 0c 24          	mov    %r9,(%rsp)
    3065:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    306a:	49 bd 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%r13
    3074:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    3079:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    307e:	e8 ad f3 ff ff       	call   2430 <__printf_chk@plt>
    3083:	bf 0a 00 00 00       	mov    $0xa,%edi
    3088:	e8 33 f2 ff ff       	call   22c0 <putchar@plt>
    308d:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    3092:	48 8d 35 3a 33 00 00 	lea    0x333a(%rip),%rsi        # 63d3 <_IO_stdin_used+0x3d3>
    3099:	31 c0                	xor    %eax,%eax
    309b:	bf 01 00 00 00       	mov    $0x1,%edi
    30a0:	49 8b 16             	mov    (%r14),%rdx
    30a3:	e8 88 f3 ff ff       	call   2430 <__printf_chk@plt>
    30a8:	48 8b 14 24          	mov    (%rsp),%rdx
    30ac:	bf 01 00 00 00       	mov    $0x1,%edi
    30b1:	31 c0                	xor    %eax,%eax
    30b3:	48 8d 35 2e 33 00 00 	lea    0x332e(%rip),%rsi        # 63e8 <_IO_stdin_used+0x3e8>
    30ba:	e8 71 f3 ff ff       	call   2430 <__printf_chk@plt>
    30bf:	bf 0a 00 00 00       	mov    $0xa,%edi
    30c4:	e8 f7 f1 ff ff       	call   22c0 <putchar@plt>
    30c9:	49 8b 36             	mov    (%r14),%rsi
    30cc:	bf 01 00 00 00       	mov    $0x1,%edi
    30d1:	48 89 f0             	mov    %rsi,%rax
    30d4:	49 f7 ed             	imul   %r13
    30d7:	31 c0                	xor    %eax,%eax
    30d9:	48 01 f2             	add    %rsi,%rdx
    30dc:	48 c1 fe 3f          	sar    $0x3f,%rsi
    30e0:	48 c1 fa 04          	sar    $0x4,%rdx
    30e4:	48 29 f2             	sub    %rsi,%rdx
    30e7:	48 8d 35 3a 35 00 00 	lea    0x353a(%rip),%rsi        # 6628 <_IO_stdin_used+0x628>
    30ee:	e8 3d f3 ff ff       	call   2430 <__printf_chk@plt>
    30f3:	49 8b 56 08          	mov    0x8(%r14),%rdx
    30f7:	bf 01 00 00 00       	mov    $0x1,%edi
    30fc:	31 c0                	xor    %eax,%eax
    30fe:	48 8d 35 43 35 00 00 	lea    0x3543(%rip),%rsi        # 6648 <_IO_stdin_used+0x648>
    3105:	e8 26 f3 ff ff       	call   2430 <__printf_chk@plt>
    310a:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    310f:	bf 01 00 00 00       	mov    $0x1,%edi
    3114:	48 8d 35 55 35 00 00 	lea    0x3555(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    311b:	4c 89 d8             	mov    %r11,%rax
    311e:	49 f7 ed             	imul   %r13
    3121:	31 c0                	xor    %eax,%eax
    3123:	4c 01 da             	add    %r11,%rdx
    3126:	49 c1 fb 3f          	sar    $0x3f,%r11
    312a:	48 c1 fa 04          	sar    $0x4,%rdx
    312e:	4c 29 da             	sub    %r11,%rdx
    3131:	e8 fa f2 ff ff       	call   2430 <__printf_chk@plt>
    3136:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    313b:	bf 01 00 00 00       	mov    $0x1,%edi
    3140:	48 8d 35 59 35 00 00 	lea    0x3559(%rip),%rsi        # 66a0 <_IO_stdin_used+0x6a0>
    3147:	48 89 c8             	mov    %rcx,%rax
    314a:	49 f7 ed             	imul   %r13
    314d:	31 c0                	xor    %eax,%eax
    314f:	48 01 ca             	add    %rcx,%rdx
    3152:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3156:	48 c1 fa 04          	sar    $0x4,%rdx
    315a:	48 29 ca             	sub    %rcx,%rdx
    315d:	e8 ce f2 ff ff       	call   2430 <__printf_chk@plt>
    3162:	4c 89 e0             	mov    %r12,%rax
    3165:	bf 01 00 00 00       	mov    $0x1,%edi
    316a:	48 8d 35 5f 35 00 00 	lea    0x355f(%rip),%rsi        # 66d0 <_IO_stdin_used+0x6d0>
    3171:	49 f7 ed             	imul   %r13
    3174:	4c 01 e2             	add    %r12,%rdx
    3177:	49 c1 fc 3f          	sar    $0x3f,%r12
    317b:	31 c0                	xor    %eax,%eax
    317d:	48 c1 fa 04          	sar    $0x4,%rdx
    3181:	4c 29 e2             	sub    %r12,%rdx
    3184:	e8 a7 f2 ff ff       	call   2430 <__printf_chk@plt>
    3189:	48 89 e8             	mov    %rbp,%rax
    318c:	bf 01 00 00 00       	mov    $0x1,%edi
    3191:	48 8d 35 5d 32 00 00 	lea    0x325d(%rip),%rsi        # 63f5 <_IO_stdin_used+0x3f5>
    3198:	49 f7 ed             	imul   %r13
    319b:	31 c0                	xor    %eax,%eax
    319d:	48 01 ea             	add    %rbp,%rdx
    31a0:	48 c1 fd 3f          	sar    $0x3f,%rbp
    31a4:	48 c1 fa 04          	sar    $0x4,%rdx
    31a8:	48 29 ea             	sub    %rbp,%rdx
    31ab:	e8 80 f2 ff ff       	call   2430 <__printf_chk@plt>
    31b0:	48 89 d8             	mov    %rbx,%rax
    31b3:	bf 01 00 00 00       	mov    $0x1,%edi
    31b8:	48 8d 35 47 32 00 00 	lea    0x3247(%rip),%rsi        # 6406 <_IO_stdin_used+0x406>
    31bf:	49 f7 ed             	imul   %r13
    31c2:	31 c0                	xor    %eax,%eax
    31c4:	48 01 da             	add    %rbx,%rdx
    31c7:	48 c1 fb 3f          	sar    $0x3f,%rbx
    31cb:	48 c1 fa 04          	sar    $0x4,%rdx
    31cf:	48 29 da             	sub    %rbx,%rdx
    31d2:	e8 59 f2 ff ff       	call   2430 <__printf_chk@plt>
    31d7:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    31dc:	be 06 00 00 00       	mov    $0x6,%esi
    31e1:	e8 ba 25 00 00       	call   57a0 <verify>
    31e6:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    31eb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    31f4:	75 4e                	jne    3244 <main+0xc74>
    31f6:	48 83 c4 68          	add    $0x68,%rsp
    31fa:	31 c0                	xor    %eax,%eax
    31fc:	5b                   	pop    %rbx
    31fd:	5d                   	pop    %rbp
    31fe:	41 5c                	pop    %r12
    3200:	41 5d                	pop    %r13
    3202:	41 5e                	pop    %r14
    3204:	41 5f                	pop    %r15
    3206:	c3                   	ret
    3207:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3210:	48 8d 05 69 20 00 00 	lea    0x2069(%rip),%rax        # 5280 <barriered_work>
    3217:	41 be 06 00 00 00    	mov    $0x6,%r14d
    321d:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
    3224:	e9 2e f8 ff ff       	jmp    2a57 <main+0x487>
    3229:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3230:	48 8d 05 09 01 00 00 	lea    0x109(%rip),%rax        # 3340 <do_protected_write>
    3237:	4b 89 84 2f 20 01 00 00 	mov    %rax,0x120(%r15,%r13,1)
    323f:	e9 05 f6 ff ff       	jmp    2849 <main+0x279>
    3244:	e8 c7 f0 ff ff       	call   2310 <__stack_chk_fail@plt>
    3249:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003250 <_start>:
    3250:	f3 0f 1e fa          	endbr64
    3254:	31 ed                	xor    %ebp,%ebp
    3256:	49 89 d1             	mov    %rdx,%r9
    3259:	5e                   	pop    %rsi
    325a:	48 89 e2             	mov    %rsp,%rdx
    325d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3261:	50                   	push   %rax
    3262:	54                   	push   %rsp
    3263:	45 31 c0             	xor    %r8d,%r8d
    3266:	31 c9                	xor    %ecx,%ecx
    3268:	48 8d 3d 61 f3 ff ff 	lea    -0xc9f(%rip),%rdi        # 25d0 <main>
    326f:	ff 15 63 5d 00 00    	call   *0x5d63(%rip)        # 8fd8 <__libc_start_main@GLIBC_2.34>
    3275:	f4                   	hlt
    3276:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003280 <deregister_tm_clones>:
    3280:	48 8d 3d 99 5d 00 00 	lea    0x5d99(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3287:	48 8d 05 92 5d 00 00 	lea    0x5d92(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    328e:	48 39 f8             	cmp    %rdi,%rax
    3291:	74 15                	je     32a8 <deregister_tm_clones+0x28>
    3293:	48 8b 05 46 5d 00 00 	mov    0x5d46(%rip),%rax        # 8fe0 <_ITM_deregisterTMCloneTable@Base>
    329a:	48 85 c0             	test   %rax,%rax
    329d:	74 09                	je     32a8 <deregister_tm_clones+0x28>
    329f:	ff e0                	jmp    *%rax
    32a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    32a8:	c3                   	ret
    32a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000032b0 <register_tm_clones>:
    32b0:	48 8d 3d 69 5d 00 00 	lea    0x5d69(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    32b7:	48 8d 35 62 5d 00 00 	lea    0x5d62(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    32be:	48 29 fe             	sub    %rdi,%rsi
    32c1:	48 89 f0             	mov    %rsi,%rax
    32c4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    32c8:	48 c1 f8 03          	sar    $0x3,%rax
    32cc:	48 01 c6             	add    %rax,%rsi
    32cf:	48 d1 fe             	sar    %rsi
    32d2:	74 14                	je     32e8 <register_tm_clones+0x38>
    32d4:	48 8b 05 15 5d 00 00 	mov    0x5d15(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    32db:	48 85 c0             	test   %rax,%rax
    32de:	74 08                	je     32e8 <register_tm_clones+0x38>
    32e0:	ff e0                	jmp    *%rax
    32e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    32e8:	c3                   	ret
    32e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000032f0 <__do_global_dtors_aux>:
    32f0:	f3 0f 1e fa          	endbr64
    32f4:	80 3d 2d 5d 00 00 00 	cmpb   $0x0,0x5d2d(%rip)        # 9028 <completed.0>
    32fb:	75 2b                	jne    3328 <__do_global_dtors_aux+0x38>
    32fd:	55                   	push   %rbp
    32fe:	48 83 3d f2 5c 00 00 00 	cmpq   $0x0,0x5cf2(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    3306:	48 89 e5             	mov    %rsp,%rbp
    3309:	74 0c                	je     3317 <__do_global_dtors_aux+0x27>
    330b:	48 8b 3d f6 5c 00 00 	mov    0x5cf6(%rip),%rdi        # 9008 <__dso_handle>
    3312:	e8 89 ef ff ff       	call   22a0 <__cxa_finalize@plt>
    3317:	e8 64 ff ff ff       	call   3280 <deregister_tm_clones>
    331c:	c6 05 05 5d 00 00 01 	movb   $0x1,0x5d05(%rip)        # 9028 <completed.0>
    3323:	5d                   	pop    %rbp
    3324:	c3                   	ret
    3325:	0f 1f 00             	nopl   (%rax)
    3328:	c3                   	ret
    3329:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003330 <frame_dummy>:
    3330:	f3 0f 1e fa          	endbr64
    3334:	e9 77 ff ff ff       	jmp    32b0 <register_tm_clones>
    3339:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003340 <do_protected_write>:
    3340:	f3 0f 1e fa          	endbr64
    3344:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    334b:	48 8b 40 30          	mov    0x30(%rax),%rax
    334f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
    3357:	48 8b 48 08          	mov    0x8(%rax),%rcx
    335b:	48 83 00 01          	addq   $0x1,(%rax)
    335f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3366:	48 85 c9             	test   %rcx,%rcx
    3369:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3370:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3374:	48 89 50 08          	mov    %rdx,0x8(%rax)
    3378:	31 c0                	xor    %eax,%eax
    337a:	c3                   	ret
    337b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003380 <barriered_reset>:
    3380:	f3 0f 1e fa          	endbr64
    3384:	48 63 8f 84 01 00 00 	movslq 0x184(%rdi),%rcx
    338b:	85 c9                	test   %ecx,%ecx
    338d:	7e 6c                	jle    33fb <barriered_reset+0x7b>
    338f:	48 63 87 30 01 00 00 	movslq 0x130(%rdi),%rax
    3396:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    339d:	48 8d 0c 89          	lea    (%rcx,%rcx,4),%rcx
    33a1:	48 c1 e1 07          	shl    $0x7,%rcx
    33a5:	48 8d 3c c0          	lea    (%rax,%rax,8),%rdi
    33a9:	49 8b 70 20          	mov    0x20(%r8),%rsi
    33ad:	48 8d 04 78          	lea    (%rax,%rdi,2),%rax
    33b1:	49 8b 78 10          	mov    0x10(%r8),%rdi
    33b5:	48 8d 96 80 01 00 00 	lea    0x180(%rsi),%rdx
    33bc:	48 8d 8c 0e 80 01 00 00 	lea    0x180(%rsi,%rcx,1),%rcx
    33c4:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    33c8:	48 8b 40 20          	mov    0x20(%rax),%rax
    33cc:	48 05 00 01 00 00    	add    $0x100,%rax
    33d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    33d8:	83 40 80 01          	addl   $0x1,-0x80(%rax)
    33dc:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
    33e3:	83 00 01             	addl   $0x1,(%rax)
    33e6:	48 05 80 02 00 00    	add    $0x280,%rax
    33ec:	c7 82 80 fd ff ff 01 00 00 00 	movl   $0x1,-0x280(%rdx)
    33f6:	48 39 ca             	cmp    %rcx,%rdx
    33f9:	75 dd                	jne    33d8 <barriered_reset+0x58>
    33fb:	0f ae f0             	mfence
    33fe:	31 c0                	xor    %eax,%eax
    3400:	c3                   	ret
    3401:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    340c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003410 <barriered_thread>:
    3410:	f3 0f 1e fa          	endbr64
    3414:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
    3418:	0f 85 d4 02 00 00    	jne    36f2 <barriered_thread+0x2e2>
    341e:	41 57                	push   %r15
    3420:	41 56                	push   %r14
    3422:	45 31 f6             	xor    %r14d,%r14d
    3425:	41 55                	push   %r13
    3427:	45 31 ed             	xor    %r13d,%r13d
    342a:	41 54                	push   %r12
    342c:	49 89 fc             	mov    %rdi,%r12
    342f:	55                   	push   %rbp
    3430:	53                   	push   %rbx
    3431:	31 db                	xor    %ebx,%ebx
    3433:	48 83 ec 08          	sub    $0x8,%rsp
    3437:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3440:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    3445:	39 da                	cmp    %ebx,%edx
    3447:	7f 13                	jg     345c <barriered_thread+0x4c>
    3449:	49 83 84 24 90 00 00 00 01 	addq   $0x1,0x90(%r12)
    3452:	31 db                	xor    %ebx,%ebx
    3454:	85 d2                	test   %edx,%edx
    3456:	0f 8e 74 01 00 00    	jle    35d0 <barriered_thread+0x1c0>
    345c:	48 63 c3             	movslq %ebx,%rax
    345f:	48 8d 2c 80          	lea    (%rax,%rax,4),%rbp
    3463:	48 c1 e5 07          	shl    $0x7,%rbp
    3467:	eb 19                	jmp    3482 <barriered_thread+0x72>
    3469:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3470:	83 c3 01             	add    $0x1,%ebx
    3473:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    347a:	39 d3                	cmp    %edx,%ebx
    347c:	0f 8d 4e 01 00 00    	jge    35d0 <barriered_thread+0x1c0>
    3482:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3487:	48 8d 0c 28          	lea    (%rax,%rbp,1),%rcx
    348b:	83 b9 80 01 00 00 01 	cmpl   $0x1,0x180(%rcx)
    3492:	75 dc                	jne    3470 <barriered_thread+0x60>
    3494:	41 8b 7c 24 18       	mov    0x18(%r12),%edi
    3499:	83 ea 01             	sub    $0x1,%edx
    349c:	8d 73 ff             	lea    -0x1(%rbx),%esi
    349f:	85 db                	test   %ebx,%ebx
    34a1:	0f 4f d6             	cmovg  %esi,%edx
    34a4:	85 ff                	test   %edi,%edi
    34a6:	0f 8e 34 02 00 00    	jle    36e0 <barriered_thread+0x2d0>
    34ac:	48 63 d2             	movslq %edx,%rdx
    34af:	44 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9d
    34b6:	45 31 d2             	xor    %r10d,%r10d
    34b9:	45 31 ff             	xor    %r15d,%r15d
    34bc:	48 8d 34 92          	lea    (%rdx,%rdx,4),%rsi
    34c0:	48 63 d7             	movslq %edi,%rdx
    34c3:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    34ca:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    34cf:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    34d3:	48 c1 e6 07          	shl    $0x7,%rsi
    34d7:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
    34db:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    34df:	90                   	nop
    34e0:	48 8b 50 20          	mov    0x20(%rax),%rdx
    34e4:	48 01 f2             	add    %rsi,%rdx
    34e7:	44 3b 8a 80 00 00 00 	cmp    0x80(%rdx),%r9d
    34ee:	75 04                	jne    34f4 <barriered_thread+0xe4>
    34f0:	41 83 c7 01          	add    $0x1,%r15d
    34f4:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    34fb:	75 04                	jne    3501 <barriered_thread+0xf1>
    34fd:	41 83 c2 01          	add    $0x1,%r10d
    3501:	48 05 98 00 00 00    	add    $0x98,%rax
    3507:	48 39 c8             	cmp    %rcx,%rax
    350a:	75 d4                	jne    34e0 <barriered_thread+0xd0>
    350c:	44 39 d7             	cmp    %r10d,%edi
    350f:	0f 84 db 00 00 00    	je     35f0 <barriered_thread+0x1e0>
    3515:	45 85 d2             	test   %r10d,%r10d
    3518:	0f 84 d2 00 00 00    	je     35f0 <barriered_thread+0x1e0>
    351e:	45 85 ff             	test   %r15d,%r15d
    3521:	74 0b                	je     352e <barriered_thread+0x11e>
    3523:	45 39 7c 24 18       	cmp    %r15d,0x18(%r12)
    3528:	0f 85 a2 00 00 00    	jne    35d0 <barriered_thread+0x1c0>
    352e:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3533:	48 01 e8             	add    %rbp,%rax
    3536:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
    353d:	85 db                	test   %ebx,%ebx
    353f:	75 10                	jne    3551 <barriered_thread+0x141>
    3541:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    3546:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    354b:	0f 8c 67 01 00 00    	jl     36b8 <barriered_thread+0x2a8>
    3551:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    355b:	49 63 14 24          	movslq (%r12),%rdx
    355f:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3563:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
    3567:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
    356c:	48 8d 14 d1          	lea    (%rcx,%rdx,8),%rdx
    3570:	48 8b 7a 20          	mov    0x20(%rdx),%rdi
    3574:	48 01 ef             	add    %rbp,%rdi
    3577:	ff 90 18 01 00 00    	call   *0x118(%rax)
    357d:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3582:	48 01 e8             	add    %rbp,%rax
    3585:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
    358c:	41 8b 44 24 28       	mov    0x28(%r12),%eax
    3591:	49 83 44 24 60 01    	addq   $0x1,0x60(%r12)
    3597:	83 e8 01             	sub    $0x1,%eax
    359a:	39 d8                	cmp    %ebx,%eax
    359c:	0f 84 a6 00 00 00    	je     3648 <barriered_thread+0x238>
    35a2:	0f ae f0             	mfence
    35a5:	45 85 f6             	test   %r14d,%r14d
    35a8:	0f 84 d2 00 00 00    	je     3680 <barriered_thread+0x270>
    35ae:	41 83 fe 03          	cmp    $0x3,%r14d
    35b2:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    35b7:	45 0f 44 f5          	cmove  %r13d,%r14d
    35bb:	83 c3 01             	add    $0x1,%ebx
    35be:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    35c5:	39 d3                	cmp    %edx,%ebx
    35c7:	0f 8c b5 fe ff ff    	jl     3482 <barriered_thread+0x72>
    35cd:	0f 1f 00             	nopl   (%rax)
    35d0:	41 83 7c 24 2c 01    	cmpl   $0x1,0x2c(%r12)
    35d6:	0f 84 64 fe ff ff    	je     3440 <barriered_thread+0x30>
    35dc:	48 83 c4 08          	add    $0x8,%rsp
    35e0:	31 c0                	xor    %eax,%eax
    35e2:	5b                   	pop    %rbx
    35e3:	5d                   	pop    %rbp
    35e4:	41 5c                	pop    %r12
    35e6:	41 5d                	pop    %r13
    35e8:	41 5e                	pop    %r14
    35ea:	41 5f                	pop    %r15
    35ec:	c3                   	ret
    35ed:	0f 1f 00             	nopl   (%rax)
    35f0:	41 83 fe 01          	cmp    $0x1,%r14d
    35f4:	0f 85 24 ff ff ff    	jne    351e <barriered_thread+0x10e>
    35fa:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3602:	bf 04 00 00 00       	mov    $0x4,%edi
    3607:	41 be 03 00 00 00    	mov    $0x3,%r14d
    360d:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3611:	49 8b 44 24 78       	mov    0x78(%r12),%rax
    3616:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    361b:	e8 d0 ec ff ff       	call   22f0 <clock_gettime@plt>
    3620:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3628:	48 83 c0 01          	add    $0x1,%rax
    362c:	48 99                	cqto
    362e:	49 f7 bc 24 88 00 00 00 	idivq  0x88(%r12)
    3636:	49 89 94 24 80 00 00 00 	mov    %rdx,0x80(%r12)
    363e:	e9 db fe ff ff       	jmp    351e <barriered_thread+0x10e>
    3643:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3648:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    364d:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    3652:	0f 8d 4a ff ff ff    	jge    35a2 <barriered_thread+0x192>
    3658:	48 c1 e6 04          	shl    $0x4,%rsi
    365c:	bf 04 00 00 00       	mov    $0x4,%edi
    3661:	49 03 74 24 58       	add    0x58(%r12),%rsi
    3666:	e8 85 ec ff ff       	call   22f0 <clock_gettime@plt>
    366b:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
    3671:	e9 2c ff ff ff       	jmp    35a2 <barriered_thread+0x192>
    3676:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3680:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3688:	bf 04 00 00 00       	mov    $0x4,%edi
    368d:	41 be 01 00 00 00    	mov    $0x1,%r14d
    3693:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3697:	49 8b 44 24 78       	mov    0x78(%r12),%rax
    369c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    36a0:	89 5e 20             	mov    %ebx,0x20(%rsi)
    36a3:	e8 48 ec ff ff       	call   22f0 <clock_gettime@plt>
    36a8:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    36ad:	e9 be fd ff ff       	jmp    3470 <barriered_thread+0x60>
    36b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    36b8:	48 c1 e6 04          	shl    $0x4,%rsi
    36bc:	bf 04 00 00 00       	mov    $0x4,%edi
    36c1:	49 03 74 24 50       	add    0x50(%r12),%rsi
    36c6:	e8 25 ec ff ff       	call   22f0 <clock_gettime@plt>
    36cb:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    36d0:	48 01 e8             	add    %rbp,%rax
    36d3:	e9 79 fe ff ff       	jmp    3551 <barriered_thread+0x141>
    36d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    36e0:	41 83 fe 01          	cmp    $0x1,%r14d
    36e4:	0f 85 49 fe ff ff    	jne    3533 <barriered_thread+0x123>
    36ea:	45 31 ff             	xor    %r15d,%r15d
    36ed:	e9 08 ff ff ff       	jmp    35fa <barriered_thread+0x1ea>
    36f2:	31 c0                	xor    %eax,%eax
    36f4:	c3                   	ret
    36f5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000003700 <external_thread>:
    3700:	f3 0f 1e fa          	endbr64
    3704:	41 55                	push   %r13
    3706:	41 54                	push   %r12
    3708:	55                   	push   %rbp
    3709:	53                   	push   %rbx
    370a:	48 83 ec 38          	sub    $0x38,%rsp
    370e:	66 0f 6f 05 da 31 00 00 	movdqa 0x31da(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    3716:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    371f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3724:	31 c0                	xor    %eax,%eax
    3726:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
    372a:	0f 29 04 24          	movaps %xmm0,(%rsp)
    372e:	75 64                	jne    3794 <external_thread+0x94>
    3730:	49 89 fd             	mov    %rdi,%r13
    3733:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3738:	48 89 e3             	mov    %rsp,%rbx
    373b:	4c 8d 25 c2 28 00 00 	lea    0x28c2(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    3742:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3748:	48 89 ee             	mov    %rbp,%rsi
    374b:	48 89 df             	mov    %rbx,%rdi
    374e:	e8 dd eb ff ff       	call   2330 <nanosleep@plt>
    3753:	49 8b 45 38          	mov    0x38(%r13),%rax
    3757:	48 63 10             	movslq (%rax),%rdx
    375a:	85 d2                	test   %edx,%edx
    375c:	7e 2c                	jle    378a <external_thread+0x8a>
    375e:	48 8b 40 08          	mov    0x8(%rax),%rax
    3762:	48 c1 e2 04          	shl    $0x4,%rdx
    3766:	48 01 c2             	add    %rax,%rdx
    3769:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3770:	8b 48 08             	mov    0x8(%rax),%ecx
    3773:	85 c9                	test   %ecx,%ecx
    3775:	75 0a                	jne    3781 <external_thread+0x81>
    3777:	4c 89 20             	mov    %r12,(%rax)
    377a:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    3781:	48 83 c0 10          	add    $0x10,%rax
    3785:	48 39 c2             	cmp    %rax,%rdx
    3788:	75 e6                	jne    3770 <external_thread+0x70>
    378a:	0f ae f0             	mfence
    378d:	41 83 7d 2c 01       	cmpl   $0x1,0x2c(%r13)
    3792:	74 b4                	je     3748 <external_thread+0x48>
    3794:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3799:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    37a2:	75 0d                	jne    37b1 <external_thread+0xb1>
    37a4:	48 83 c4 38          	add    $0x38,%rsp
    37a8:	31 c0                	xor    %eax,%eax
    37aa:	5b                   	pop    %rbx
    37ab:	5d                   	pop    %rbp
    37ac:	41 5c                	pop    %r12
    37ae:	41 5d                	pop    %r13
    37b0:	c3                   	ret
    37b1:	e8 5a eb ff ff       	call   2310 <__stack_chk_fail@plt>
    37b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000037c0 <timer_thread>:
    37c0:	f3 0f 1e fa          	endbr64
    37c4:	41 57                	push   %r15
    37c6:	48 8d 35 43 28 00 00 	lea    0x2843(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    37cd:	49 89 ff             	mov    %rdi,%r15
    37d0:	41 56                	push   %r14
    37d2:	41 55                	push   %r13
    37d4:	41 54                	push   %r12
    37d6:	55                   	push   %rbp
    37d7:	53                   	push   %rbx
    37d8:	48 83 ec 68          	sub    $0x68,%rsp
    37dc:	8b 17                	mov    (%rdi),%edx
    37de:	bf 01 00 00 00       	mov    $0x1,%edi
    37e3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    37ec:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    37f1:	31 c0                	xor    %eax,%eax
    37f3:	e8 38 ec ff ff       	call   2430 <__printf_chk@plt>
    37f8:	66 0f 6f 05 f0 30 00 00 	movdqa 0x30f0(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    3800:	ba 30 75 00 00       	mov    $0x7530,%edx
    3805:	31 c0                	xor    %eax,%eax
    3807:	48 8d 35 14 28 00 00 	lea    0x2814(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    380e:	bf 01 00 00 00       	mov    $0x1,%edi
    3813:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
    3818:	e8 13 ec ff ff       	call   2430 <__printf_chk@plt>
    381d:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3821:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    3825:	85 c0                	test   %eax,%eax
    3827:	0f 84 c6 00 00 00    	je     38f3 <timer_thread+0x133>
    382d:	45 31 f6             	xor    %r14d,%r14d
    3830:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3835:	48 8d 5c 24 20       	lea    0x20(%rsp),%rbx
    383a:	45 31 e4             	xor    %r12d,%r12d
    383d:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
    3845:	48 89 df             	mov    %rbx,%rdi
    3848:	48 89 ee             	mov    %rbp,%rsi
    384b:	41 83 c6 01          	add    $0x1,%r14d
    384f:	e8 dc ea ff ff       	call   2330 <nanosleep@plt>
    3854:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    3858:	45 8b 47 18          	mov    0x18(%r15),%r8d
    385c:	8d 78 01             	lea    0x1(%rax),%edi
    385f:	45 85 c0             	test   %r8d,%r8d
    3862:	7e 68                	jle    38cc <timer_thread+0x10c>
    3864:	4c 63 6c 24 0c       	movslq 0xc(%rsp),%r13
    3869:	31 c9                	xor    %ecx,%ecx
    386b:	31 f6                	xor    %esi,%esi
    386d:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3873:	4f 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%r8
    3878:	49 c1 e0 07          	shl    $0x7,%r8
    387c:	0f 1f 40 00          	nopl   0x0(%rax)
    3880:	4d 8b 5f 10          	mov    0x10(%r15),%r11
    3884:	89 f8                	mov    %edi,%eax
    3886:	99                   	cltd
    3887:	49 01 cb             	add    %rcx,%r11
    388a:	41 f7 7b 28          	idivl  0x28(%r11)
    388e:	48 63 d2             	movslq %edx,%rdx
    3891:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    3895:	44 89 ca             	mov    %r9d,%edx
    3898:	48 c1 e0 07          	shl    $0x7,%rax
    389c:	49 03 43 20          	add    0x20(%r11),%rax
    38a0:	48 05 00 02 00 00    	add    $0x200,%rax
    38a6:	87 10                	xchg   %edx,(%rax)
    38a8:	49 8b 47 10          	mov    0x10(%r15),%rax
    38ac:	48 8b 44 08 20       	mov    0x20(%rax,%rcx,1),%rax
    38b1:	44 89 e2             	mov    %r12d,%edx
    38b4:	42 87 94 00 00 02 00 00 	xchg   %edx,0x200(%rax,%r8,1)
    38bc:	83 c6 01             	add    $0x1,%esi
    38bf:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    38c6:	41 39 77 18          	cmp    %esi,0x18(%r15)
    38ca:	7f b4                	jg     3880 <timer_thread+0xc0>
    38cc:	0f ae f0             	mfence
    38cf:	49 8b 47 10          	mov    0x10(%r15),%rax
    38d3:	41 8b 77 2c          	mov    0x2c(%r15),%esi
    38d7:	39 78 28             	cmp    %edi,0x28(%rax)
    38da:	41 0f 4e fc          	cmovle %r12d,%edi
    38de:	89 7c 24 0c          	mov    %edi,0xc(%rsp)
    38e2:	85 f6                	test   %esi,%esi
    38e4:	74 0d                	je     38f3 <timer_thread+0x133>
    38e6:	41 81 fe 30 75 00 00 	cmp    $0x7530,%r14d
    38ed:	0f 85 52 ff ff ff    	jne    3845 <timer_thread+0x85>
    38f3:	48 8d 3d 3e 27 00 00 	lea    0x273e(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    38fa:	e8 d1 e9 ff ff       	call   22d0 <puts@plt>
    38ff:	49 63 47 1c          	movslq 0x1c(%r15),%rax
    3903:	85 c0                	test   %eax,%eax
    3905:	0f 8e 8c 00 00 00    	jle    3997 <timer_thread+0x1d7>
    390b:	41 8b 57 28          	mov    0x28(%r15),%edx
    390f:	85 d2                	test   %edx,%edx
    3911:	0f 8e 80 00 00 00    	jle    3997 <timer_thread+0x1d7>
    3917:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    391b:	4d 8b 4f 10          	mov    0x10(%r15),%r9
    391f:	48 8d 3c 48          	lea    (%rax,%rcx,2),%rdi
    3923:	48 63 c2             	movslq %edx,%rax
    3926:	31 c9                	xor    %ecx,%ecx
    3928:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    392c:	48 c1 e7 03          	shl    $0x3,%rdi
    3930:	48 c1 e0 07          	shl    $0x7,%rax
    3934:	4c 8d 80 38 02 00 00 	lea    0x238(%rax),%r8
    393b:	49 8b 74 09 20       	mov    0x20(%r9,%rcx,1),%rsi
    3940:	4a 8d 14 06          	lea    (%rsi,%r8,1),%rdx
    3944:	48 8d 86 38 02 00 00 	lea    0x238(%rsi),%rax
    394b:	49 89 d3             	mov    %rdx,%r11
    394e:	49 29 c3             	sub    %rax,%r11
    3951:	41 81 e3 80 00 00 00 	and    $0x80,%r11d
    3958:	74 16                	je     3970 <timer_thread+0x1b0>
    395a:	48 8d 86 b8 04 00 00 	lea    0x4b8(%rsi),%rax
    3961:	c7 86 38 02 00 00 00 00 00 00 	movl   $0x0,0x238(%rsi)
    396b:	48 39 c2             	cmp    %rax,%rdx
    396e:	74 1b                	je     398b <timer_thread+0x1cb>
    3970:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    3976:	48 05 00 05 00 00    	add    $0x500,%rax
    397c:	c7 80 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%rax)
    3986:	48 39 c2             	cmp    %rax,%rdx
    3989:	75 e5                	jne    3970 <timer_thread+0x1b0>
    398b:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3992:	48 39 cf             	cmp    %rcx,%rdi
    3995:	75 a4                	jne    393b <timer_thread+0x17b>
    3997:	0f ae f0             	mfence
    399a:	66 0f 6f 05 5e 2f 00 00 	movdqa 0x2f5e(%rip),%xmm0        # 6900 <_IO_stdin_used+0x900>
    39a2:	45 31 f6             	xor    %r14d,%r14d
    39a5:	48 8d 2d b1 26 00 00 	lea    0x26b1(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    39ac:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    39b1:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    39b5:	41 8b 57 18          	mov    0x18(%r15),%edx
    39b9:	8d 70 01             	lea    0x1(%rax),%esi
    39bc:	85 d2                	test   %edx,%edx
    39be:	7e 66                	jle    3a26 <timer_thread+0x266>
    39c0:	4c 63 6c 24 0c       	movslq 0xc(%rsp),%r13
    39c5:	31 c9                	xor    %ecx,%ecx
    39c7:	31 ff                	xor    %edi,%edi
    39c9:	4f 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%r8
    39ce:	49 c1 e0 07          	shl    $0x7,%r8
    39d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    39d8:	4d 8b 4f 10          	mov    0x10(%r15),%r9
    39dc:	89 f0                	mov    %esi,%eax
    39de:	bb 01 00 00 00       	mov    $0x1,%ebx
    39e3:	99                   	cltd
    39e4:	49 01 c9             	add    %rcx,%r9
    39e7:	41 f7 79 28          	idivl  0x28(%r9)
    39eb:	48 63 c2             	movslq %edx,%rax
    39ee:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    39f2:	48 c1 e0 07          	shl    $0x7,%rax
    39f6:	49 03 41 20          	add    0x20(%r9),%rax
    39fa:	48 05 00 02 00 00    	add    $0x200,%rax
    3a00:	87 18                	xchg   %ebx,(%rax)
    3a02:	49 8b 47 10          	mov    0x10(%r15),%rax
    3a06:	48 8b 44 08 20       	mov    0x20(%rax,%rcx,1),%rax
    3a0b:	44 89 f3             	mov    %r14d,%ebx
    3a0e:	42 87 9c 00 00 02 00 00 	xchg   %ebx,0x200(%rax,%r8,1)
    3a16:	83 c7 01             	add    $0x1,%edi
    3a19:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3a20:	41 39 7f 18          	cmp    %edi,0x18(%r15)
    3a24:	7f b2                	jg     39d8 <timer_thread+0x218>
    3a26:	0f ae f0             	mfence
    3a29:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3a2d:	41 8b 7f 18          	mov    0x18(%r15),%edi
    3a31:	39 72 28             	cmp    %esi,0x28(%rdx)
    3a34:	41 0f 4e f6          	cmovle %r14d,%esi
    3a38:	89 74 24 0c          	mov    %esi,0xc(%rsp)
    3a3c:	85 ff                	test   %edi,%edi
    3a3e:	0f 8e bf 00 00 00    	jle    3b03 <timer_thread+0x343>
    3a44:	31 db                	xor    %ebx,%ebx
    3a46:	45 31 e4             	xor    %r12d,%r12d
    3a49:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    3a4f:	90                   	nop
    3a50:	45 31 ed             	xor    %r13d,%r13d
    3a53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3a58:	4b 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%rax
    3a5d:	48 c1 e0 07          	shl    $0x7,%rax
    3a61:	48 03 44 1a 20       	add    0x20(%rdx,%rbx,1),%rax
    3a66:	31 d2                	xor    %edx,%edx
    3a68:	48 8b 80 28 02 00 00 	mov    0x228(%rax),%rax
    3a6f:	eb 17                	jmp    3a88 <timer_thread+0x2c8>
    3a71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3a78:	4d 85 c0             	test   %r8,%r8
    3a7b:	7f 25                	jg     3aa2 <timer_thread+0x2e2>
    3a7d:	83 c2 01             	add    $0x1,%edx
    3a80:	48 83 c0 20          	add    $0x20,%rax
    3a84:	39 fa                	cmp    %edi,%edx
    3a86:	74 30                	je     3ab8 <timer_thread+0x2f8>
    3a88:	48 8b 08             	mov    (%rax),%rcx
    3a8b:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3a8f:	48 8b 89 80 00 00 00 	mov    0x80(%rcx),%rcx
    3a96:	4c 8b 86 80 00 00 00 	mov    0x80(%rsi),%r8
    3a9d:	48 85 c9             	test   %rcx,%rcx
    3aa0:	7e d6                	jle    3a78 <timer_thread+0x2b8>
    3aa2:	bf 01 00 00 00       	mov    $0x1,%edi
    3aa7:	48 89 ee             	mov    %rbp,%rsi
    3aaa:	31 c0                	xor    %eax,%eax
    3aac:	e8 7f e9 ff ff       	call   2430 <__printf_chk@plt>
    3ab1:	41 8b 7f 18          	mov    0x18(%r15),%edi
    3ab5:	45 31 db             	xor    %r11d,%r11d
    3ab8:	49 83 c5 01          	add    $0x1,%r13
    3abc:	44 39 ef             	cmp    %r13d,%edi
    3abf:	7e 0f                	jle    3ad0 <timer_thread+0x310>
    3ac1:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3ac5:	eb 91                	jmp    3a58 <timer_thread+0x298>
    3ac7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3ad0:	41 83 c4 01          	add    $0x1,%r12d
    3ad4:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3adb:	44 39 e7             	cmp    %r12d,%edi
    3ade:	7e 09                	jle    3ae9 <timer_thread+0x329>
    3ae0:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3ae4:	e9 67 ff ff ff       	jmp    3a50 <timer_thread+0x290>
    3ae9:	41 83 fb 01          	cmp    $0x1,%r11d
    3aed:	74 14                	je     3b03 <timer_thread+0x343>
    3aef:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    3af4:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    3af9:	e8 32 e8 ff ff       	call   2330 <nanosleep@plt>
    3afe:	e9 ae fe ff ff       	jmp    39b1 <timer_thread+0x1f1>
    3b03:	48 8d 3d 4a 25 00 00 	lea    0x254a(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3b0a:	e8 c1 e7 ff ff       	call   22d0 <puts@plt>
    3b0f:	41 8b 4f 2c          	mov    0x2c(%r15),%ecx
    3b13:	85 c9                	test   %ecx,%ecx
    3b15:	0f 84 b0 00 00 00    	je     3bcb <timer_thread+0x40b>
    3b1b:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3b1f:	85 c9                	test   %ecx,%ecx
    3b21:	7e 38                	jle    3b5b <timer_thread+0x39b>
    3b23:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3b27:	31 db                	xor    %ebx,%ebx
    3b29:	31 ed                	xor    %ebp,%ebp
    3b2b:	4c 8d 25 3c 25 00 00 	lea    0x253c(%rip),%r12        # 606e <_IO_stdin_used+0x6e>
    3b32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3b38:	48 8d 04 1a          	lea    (%rdx,%rbx,1),%rax
    3b3c:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
    3b40:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
    3b47:	0f 84 ab 00 00 00    	je     3bf8 <timer_thread+0x438>
    3b4d:	83 c5 01             	add    $0x1,%ebp
    3b50:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3b57:	39 cd                	cmp    %ecx,%ebp
    3b59:	7c dd                	jl     3b38 <timer_thread+0x378>
    3b5b:	41 8b 47 18          	mov    0x18(%r15),%eax
    3b5f:	85 c0                	test   %eax,%eax
    3b61:	7e 51                	jle    3bb4 <timer_thread+0x3f4>
    3b63:	41 8b 47 28          	mov    0x28(%r15),%eax
    3b67:	31 f6                	xor    %esi,%esi
    3b69:	45 31 c0             	xor    %r8d,%r8d
    3b6c:	31 ff                	xor    %edi,%edi
    3b6e:	85 c0                	test   %eax,%eax
    3b70:	7e 42                	jle    3bb4 <timer_thread+0x3f4>
    3b72:	31 d2                	xor    %edx,%edx
    3b74:	0f 1f 40 00          	nopl   0x0(%rax)
    3b78:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3b7c:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    3b80:	89 fb                	mov    %edi,%ebx
    3b82:	48 c1 e0 07          	shl    $0x7,%rax
    3b86:	48 03 44 31 20       	add    0x20(%rcx,%rsi,1),%rax
    3b8b:	48 05 00 02 00 00    	add    $0x200,%rax
    3b91:	87 18                	xchg   %ebx,(%rax)
    3b93:	41 8b 47 28          	mov    0x28(%r15),%eax
    3b97:	48 83 c2 01          	add    $0x1,%rdx
    3b9b:	39 d0                	cmp    %edx,%eax
    3b9d:	7f d9                	jg     3b78 <timer_thread+0x3b8>
    3b9f:	41 83 c0 01          	add    $0x1,%r8d
    3ba3:	45 3b 47 18          	cmp    0x18(%r15),%r8d
    3ba7:	7d 0b                	jge    3bb4 <timer_thread+0x3f4>
    3ba9:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
    3bb0:	85 c0                	test   %eax,%eax
    3bb2:	7f be                	jg     3b72 <timer_thread+0x3b2>
    3bb4:	0f ae f0             	mfence
    3bb7:	48 8d 3d c2 24 00 00 	lea    0x24c2(%rip),%rdi        # 6080 <_IO_stdin_used+0x80>
    3bbe:	e8 0d e7 ff ff       	call   22d0 <puts@plt>
    3bc3:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
    3bcb:	48 8d 3d b5 24 00 00 	lea    0x24b5(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3bd2:	e8 f9 e6 ff ff       	call   22d0 <puts@plt>
    3bd7:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    3bdc:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3be5:	75 4a                	jne    3c31 <timer_thread+0x471>
    3be7:	48 83 c4 68          	add    $0x68,%rsp
    3beb:	31 c0                	xor    %eax,%eax
    3bed:	5b                   	pop    %rbx
    3bee:	5d                   	pop    %rbp
    3bef:	41 5c                	pop    %r12
    3bf1:	41 5d                	pop    %r13
    3bf3:	41 5e                	pop    %r14
    3bf5:	41 5f                	pop    %r15
    3bf7:	c3                   	ret
    3bf8:	4c 89 e7             	mov    %r12,%rdi
    3bfb:	83 c5 01             	add    $0x1,%ebp
    3bfe:	e8 cd e6 ff ff       	call   22d0 <puts@plt>
    3c03:	49 8b 47 10          	mov    0x10(%r15),%rax
    3c07:	be 01 00 00 00       	mov    $0x1,%esi
    3c0c:	8b 7c 18 48          	mov    0x48(%rax,%rbx,1),%edi
    3c10:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3c17:	e8 c4 e7 ff ff       	call   23e0 <eventfd_write@plt>
    3c1c:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3c20:	39 cd                	cmp    %ecx,%ebp
    3c22:	0f 8d 33 ff ff ff    	jge    3b5b <timer_thread+0x39b>
    3c28:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3c2c:	e9 07 ff ff ff       	jmp    3b38 <timer_thread+0x378>
    3c31:	e8 da e6 ff ff       	call   2310 <__stack_chk_fail@plt>
    3c36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003c40 <strtolower>:
    3c40:	f3 0f 1e fa          	endbr64
    3c44:	55                   	push   %rbp
    3c45:	53                   	push   %rbx
    3c46:	48 83 ec 08          	sub    $0x8,%rsp
    3c4a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3c4e:	84 db                	test   %bl,%bl
    3c50:	74 24                	je     3c76 <strtolower+0x36>
    3c52:	48 89 fd             	mov    %rdi,%rbp
    3c55:	e8 96 e8 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3c5a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c60:	48 8b 10             	mov    (%rax),%rdx
    3c63:	48 83 c5 01          	add    $0x1,%rbp
    3c67:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3c6a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    3c6d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3c72:	84 db                	test   %bl,%bl
    3c74:	75 ea                	jne    3c60 <strtolower+0x20>
    3c76:	48 83 c4 08          	add    $0x8,%rsp
    3c7a:	5b                   	pop    %rbx
    3c7b:	5d                   	pop    %rbp
    3c7c:	c3                   	ret
    3c7d:	0f 1f 00             	nopl   (%rax)

0000000000003c80 <zh_malloc>:
    3c80:	f3 0f 1e fa          	endbr64
    3c84:	48 83 ec 08          	sub    $0x8,%rsp
    3c88:	e8 63 e7 ff ff       	call   23f0 <malloc@plt>
    3c8d:	48 85 c0             	test   %rax,%rax
    3c90:	74 05                	je     3c97 <zh_malloc+0x17>
    3c92:	48 83 c4 08          	add    $0x8,%rsp
    3c96:	c3                   	ret
    3c97:	48 8b 0d 82 53 00 00 	mov    0x5382(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3c9e:	ba 28 00 00 00       	mov    $0x28,%edx
    3ca3:	be 01 00 00 00       	mov    $0x1,%esi
    3ca8:	48 8d 3d 71 27 00 00 	lea    0x2771(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    3caf:	e8 ec e7 ff ff       	call   24a0 <fwrite@plt>
    3cb4:	bf 01 00 00 00       	mov    $0x1,%edi
    3cb9:	e8 c2 e7 ff ff       	call   2480 <exit@plt>
    3cbe:	66 90                	xchg   %ax,%ax

0000000000003cc0 <get_filename_ext>:
    3cc0:	f3 0f 1e fa          	endbr64
    3cc4:	53                   	push   %rbx
    3cc5:	be 2e 00 00 00       	mov    $0x2e,%esi
    3cca:	48 89 fb             	mov    %rdi,%rbx
    3ccd:	e8 6e e6 ff ff       	call   2340 <strrchr@plt>
    3cd2:	48 85 c0             	test   %rax,%rax
    3cd5:	74 11                	je     3ce8 <get_filename_ext+0x28>
    3cd7:	48 39 c3             	cmp    %rax,%rbx
    3cda:	74 0c                	je     3ce8 <get_filename_ext+0x28>
    3cdc:	48 83 c0 01          	add    $0x1,%rax
    3ce0:	5b                   	pop    %rbx
    3ce1:	c3                   	ret
    3ce2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3ce8:	48 8d 05 e0 23 00 00 	lea    0x23e0(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
    3cef:	5b                   	pop    %rbx
    3cf0:	c3                   	ret
    3cf1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3cfc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003d00 <send_headers>:
    3d00:	f3 0f 1e fa          	endbr64
    3d04:	41 55                	push   %r13
    3d06:	49 89 f5             	mov    %rsi,%r13
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
    3d38:	e8 d3 e6 ff ff       	call   2410 <__strcpy_chk@plt>
    3d3d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3d42:	84 db                	test   %bl,%bl
    3d44:	74 24                	je     3d6a <send_headers+0x6a>
    3d46:	e8 a5 e7 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3d4b:	48 8b 08             	mov    (%rax),%rcx
    3d4e:	4c 89 e0             	mov    %r12,%rax
    3d51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3d58:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    3d5b:	48 83 c0 01          	add    $0x1,%rax
    3d5f:	88 50 ff             	mov    %dl,-0x1(%rax)
    3d62:	48 0f be 18          	movsbq (%rax),%rbx
    3d66:	84 db                	test   %bl,%bl
    3d68:	75 ee                	jne    3d58 <send_headers+0x58>
    3d6a:	bf 11 00 00 00       	mov    $0x11,%edi
    3d6f:	e8 7c e6 ff ff       	call   23f0 <malloc@plt>
    3d74:	48 85 c0             	test   %rax,%rax
    3d77:	0f 84 7e 04 00 00    	je     41fb <send_headers+0x4fb>
    3d7d:	66 0f 6f 05 8b 2b 00 00 	movdqa 0x2b8b(%rip),%xmm0        # 6910 <_IO_stdin_used+0x910>
    3d85:	48 89 45 00          	mov    %rax,0x0(%rbp)
    3d89:	bf 17 00 00 00       	mov    $0x17,%edi
    3d8e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3d96:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3d9a:	0f 11 00             	movups %xmm0,(%rax)
    3d9d:	e8 4e e6 ff ff       	call   23f0 <malloc@plt>
    3da2:	48 85 c0             	test   %rax,%rax
    3da5:	0f 84 50 04 00 00    	je     41fb <send_headers+0x4fb>
    3dab:	66 0f 6f 05 6d 2b 00 00 	movdqa 0x2b6d(%rip),%xmm0        # 6920 <_IO_stdin_used+0x920>
    3db3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    3db7:	4c 89 e7             	mov    %r12,%rdi
    3dba:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    3dc4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3dcc:	0f 11 00             	movups %xmm0,(%rax)
    3dcf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    3dd3:	be 2e 00 00 00       	mov    $0x2e,%esi
    3dd8:	e8 63 e5 ff ff       	call   2340 <strrchr@plt>
    3ddd:	48 85 c0             	test   %rax,%rax
    3de0:	0f 84 ea 02 00 00    	je     40d0 <send_headers+0x3d0>
    3de6:	4c 39 e0             	cmp    %r12,%rax
    3de9:	0f 84 e1 02 00 00    	je     40d0 <send_headers+0x3d0>
    3def:	48 8d 58 01          	lea    0x1(%rax),%rbx
    3df3:	48 8d 3d a3 22 00 00 	lea    0x22a3(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3dfa:	48 89 de             	mov    %rbx,%rsi
    3dfd:	e8 8e e5 ff ff       	call   2390 <strcmp@plt>
    3e02:	85 c0                	test   %eax,%eax
    3e04:	75 20                	jne    3e26 <send_headers+0x126>
    3e06:	66 0f 6f 05 22 2b 00 00 	movdqa 0x2b22(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3e0e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3e16:	66 0f 6f 05 22 2b 00 00 	movdqa 0x2b22(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3e1e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3e26:	48 89 de             	mov    %rbx,%rsi
    3e29:	48 8d 3d 71 22 00 00 	lea    0x2271(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3e30:	e8 5b e5 ff ff       	call   2390 <strcmp@plt>
    3e35:	85 c0                	test   %eax,%eax
    3e37:	75 20                	jne    3e59 <send_headers+0x159>
    3e39:	66 0f 6f 05 ef 2a 00 00 	movdqa 0x2aef(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3e41:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3e49:	66 0f 6f 05 ef 2a 00 00 	movdqa 0x2aef(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3e51:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3e59:	48 89 de             	mov    %rbx,%rsi
    3e5c:	48 8d 3d 43 22 00 00 	lea    0x2243(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3e63:	e8 28 e5 ff ff       	call   2390 <strcmp@plt>
    3e68:	85 c0                	test   %eax,%eax
    3e6a:	0f 84 10 02 00 00    	je     4080 <send_headers+0x380>
    3e70:	48 89 de             	mov    %rbx,%rsi
    3e73:	48 8d 3d 30 22 00 00 	lea    0x2230(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3e7a:	e8 11 e5 ff ff       	call   2390 <strcmp@plt>
    3e7f:	85 c0                	test   %eax,%eax
    3e81:	0f 84 a9 02 00 00    	je     4130 <send_headers+0x430>
    3e87:	48 89 de             	mov    %rbx,%rsi
    3e8a:	48 8d 3d 1d 22 00 00 	lea    0x221d(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3e91:	e8 fa e4 ff ff       	call   2390 <strcmp@plt>
    3e96:	85 c0                	test   %eax,%eax
    3e98:	0f 84 6a 02 00 00    	je     4108 <send_headers+0x408>
    3e9e:	48 89 de             	mov    %rbx,%rsi
    3ea1:	48 8d 3d 49 22 00 00 	lea    0x2249(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3ea8:	e8 e3 e4 ff ff       	call   2390 <strcmp@plt>
    3ead:	85 c0                	test   %eax,%eax
    3eaf:	0f 84 2b 02 00 00    	je     40e0 <send_headers+0x3e0>
    3eb5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3eb8:	0f 84 52 01 00 00    	je     4010 <send_headers+0x310>
    3ebe:	48 89 de             	mov    %rbx,%rsi
    3ec1:	48 8d 3d ea 21 00 00 	lea    0x21ea(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3ec8:	e8 c3 e4 ff ff       	call   2390 <strcmp@plt>
    3ecd:	85 c0                	test   %eax,%eax
    3ecf:	0f 84 ab 02 00 00    	je     4180 <send_headers+0x480>
    3ed5:	48 89 de             	mov    %rbx,%rsi
    3ed8:	48 8d 3d d7 21 00 00 	lea    0x21d7(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3edf:	e8 ac e4 ff ff       	call   2390 <strcmp@plt>
    3ee4:	85 c0                	test   %eax,%eax
    3ee6:	0f 84 6c 02 00 00    	je     4158 <send_headers+0x458>
    3eec:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3ef4:	4c 89 e7             	mov    %r12,%rdi
    3ef7:	e8 04 e4 ff ff       	call   2300 <strlen@plt>
    3efc:	48 89 c7             	mov    %rax,%rdi
    3eff:	48 89 c3             	mov    %rax,%rbx
    3f02:	e8 e9 e4 ff ff       	call   23f0 <malloc@plt>
    3f07:	48 85 c0             	test   %rax,%rax
    3f0a:	0f 84 eb 02 00 00    	je     41fb <send_headers+0x4fb>
    3f10:	48 89 45 20          	mov    %rax,0x20(%rbp)
    3f14:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
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
    3f41:	4d 89 e8             	mov    %r13,%r8
    3f44:	48 8d 0d 6f 21 00 00 	lea    0x216f(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    3f4b:	4c 89 e7             	mov    %r12,%rdi
    3f4e:	31 c0                	xor    %eax,%eax
    3f50:	ba 00 04 00 00       	mov    $0x400,%edx
    3f55:	be 01 00 00 00       	mov    $0x1,%esi
    3f5a:	e8 a1 e5 ff ff       	call   2500 <__sprintf_chk@plt>
    3f5f:	4c 89 e7             	mov    %r12,%rdi
    3f62:	e8 99 e3 ff ff       	call   2300 <strlen@plt>
    3f67:	48 89 c7             	mov    %rax,%rdi
    3f6a:	48 89 c3             	mov    %rax,%rbx
    3f6d:	e8 7e e4 ff ff       	call   23f0 <malloc@plt>
    3f72:	48 85 c0             	test   %rax,%rax
    3f75:	0f 84 80 02 00 00    	je     41fb <send_headers+0x4fb>
    3f7b:	48 89 45 30          	mov    %rax,0x30(%rbp)
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
    3fac:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    3fb1:	bf 02 00 00 00       	mov    $0x2,%edi
    3fb6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    3fbe:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    3fc6:	e8 25 e4 ff ff       	call   23f0 <malloc@plt>
    3fcb:	48 85 c0             	test   %rax,%rax
    3fce:	0f 84 27 02 00 00    	je     41fb <send_headers+0x4fb>
    3fd4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    3fdc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    3fe0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    3fe8:	66 89 10             	mov    %dx,(%rax)
    3feb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    3ff3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3ffc:	0f 85 20 02 00 00    	jne    4222 <send_headers+0x522>
    4002:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4009:	5b                   	pop    %rbx
    400a:	5d                   	pop    %rbp
    400b:	41 5c                	pop    %r12
    400d:	41 5d                	pop    %r13
    400f:	c3                   	ret
    4010:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4014:	0f 85 a4 fe ff ff    	jne    3ebe <send_headers+0x1be>
    401a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    401e:	0f 85 9a fe ff ff    	jne    3ebe <send_headers+0x1be>
    4024:	66 0f 6f 05 64 29 00 00 	movdqa 0x2964(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    402c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4036:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    403e:	66 0f 6f 05 5a 29 00 00 	movdqa 0x295a(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    4046:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    404e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4056:	e9 63 fe ff ff       	jmp    3ebe <send_headers+0x1be>
    405b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4060:	89 da                	mov    %ebx,%edx
    4062:	48 89 c7             	mov    %rax,%rdi
    4065:	4c 89 e6             	mov    %r12,%rsi
    4068:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    406d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4072:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4075:	c1 e9 03             	shr    $0x3,%ecx
    4078:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    407b:	e9 c1 fe ff ff       	jmp    3f41 <send_headers+0x241>
    4080:	66 0f 6f 05 a8 28 00 00 	movdqa 0x28a8(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4088:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4090:	66 0f 6f 05 b8 28 00 00 	movdqa 0x28b8(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    4098:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40a0:	e9 cb fd ff ff       	jmp    3e70 <send_headers+0x170>
    40a5:	0f 1f 00             	nopl   (%rax)
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
    40d0:	48 8d 1d f8 1f 00 00 	lea    0x1ff8(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    40d7:	e9 94 fd ff ff       	jmp    3e70 <send_headers+0x170>
    40dc:	0f 1f 40 00          	nopl   0x0(%rax)
    40e0:	66 0f 6f 05 88 28 00 00 	movdqa 0x2888(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    40e8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40f0:	66 0f 6f 05 88 28 00 00 	movdqa 0x2888(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    40f8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4100:	e9 b0 fd ff ff       	jmp    3eb5 <send_headers+0x1b5>
    4105:	0f 1f 00             	nopl   (%rax)
    4108:	66 0f 6f 05 60 28 00 00 	movdqa 0x2860(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4110:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4118:	66 0f 6f 05 60 28 00 00 	movdqa 0x2860(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4120:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4128:	e9 71 fd ff ff       	jmp    3e9e <send_headers+0x19e>
    412d:	0f 1f 00             	nopl   (%rax)
    4130:	66 0f 6f 05 f8 27 00 00 	movdqa 0x27f8(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4138:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4140:	66 0f 6f 05 18 28 00 00 	movdqa 0x2818(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    4148:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4150:	e9 32 fd ff ff       	jmp    3e87 <send_headers+0x187>
    4155:	0f 1f 00             	nopl   (%rax)
    4158:	66 0f 6f 05 10 28 00 00 	movdqa 0x2810(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4160:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4168:	66 0f 6f 05 50 28 00 00 	movdqa 0x2850(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4170:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4178:	e9 6f fd ff ff       	jmp    3eec <send_headers+0x1ec>
    417d:	0f 1f 00             	nopl   (%rax)
    4180:	66 0f 6f 05 e8 27 00 00 	movdqa 0x27e8(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4188:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4190:	66 0f 6f 05 18 28 00 00 	movdqa 0x2818(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    4198:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    41a0:	e9 30 fd ff ff       	jmp    3ed5 <send_headers+0x1d5>
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
    41fb:	48 8b 0d 1e 4e 00 00 	mov    0x4e1e(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4202:	ba 28 00 00 00       	mov    $0x28,%edx
    4207:	be 01 00 00 00       	mov    $0x1,%esi
    420c:	48 8d 3d 0d 22 00 00 	lea    0x220d(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    4213:	e8 88 e2 ff ff       	call   24a0 <fwrite@plt>
    4218:	bf 01 00 00 00       	mov    $0x1,%edi
    421d:	e8 5e e2 ff ff       	call   2480 <exit@plt>
    4222:	e8 e9 e0 ff ff       	call   2310 <__stack_chk_fail@plt>
    4227:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004230 <copy_file_contents>:
    4230:	f3 0f 1e fa          	endbr64
    4234:	41 55                	push   %r13
    4236:	49 89 d5             	mov    %rdx,%r13
    4239:	41 54                	push   %r12
    423b:	49 89 fc             	mov    %rdi,%r12
    423e:	48 89 f7             	mov    %rsi,%rdi
    4241:	55                   	push   %rbp
    4242:	53                   	push   %rbx
    4243:	48 89 f3             	mov    %rsi,%rbx
    4246:	48 83 ec 08          	sub    $0x8,%rsp
    424a:	e8 a1 e1 ff ff       	call   23f0 <malloc@plt>
    424f:	48 85 c0             	test   %rax,%rax
    4252:	74 6b                	je     42bf <copy_file_contents+0x8f>
    4254:	4c 89 e7             	mov    %r12,%rdi
    4257:	48 89 c5             	mov    %rax,%rbp
    425a:	31 f6                	xor    %esi,%esi
    425c:	31 c0                	xor    %eax,%eax
    425e:	e8 fd e1 ff ff       	call   2460 <open@plt>
    4263:	41 89 c4             	mov    %eax,%r12d
    4266:	85 c0                	test   %eax,%eax
    4268:	0f 88 c8 e2 ff ff    	js     2536 <copy_file_contents.cold>
    426e:	48 89 da             	mov    %rbx,%rdx
    4271:	48 89 ee             	mov    %rbp,%rsi
    4274:	89 c7                	mov    %eax,%edi
    4276:	e8 f5 e0 ff ff       	call   2370 <read@plt>
    427b:	48 98                	cltq
    427d:	48 39 d8             	cmp    %rbx,%rax
    4280:	7c 1e                	jl     42a0 <copy_file_contents+0x70>
    4282:	44 89 e7             	mov    %r12d,%edi
    4285:	e8 c6 e0 ff ff       	call   2350 <close@plt>
    428a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    428e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    4292:	48 83 c4 08          	add    $0x8,%rsp
    4296:	5b                   	pop    %rbx
    4297:	5d                   	pop    %rbp
    4298:	41 5c                	pop    %r12
    429a:	41 5d                	pop    %r13
    429c:	c3                   	ret
    429d:	0f 1f 00             	nopl   (%rax)
    42a0:	48 8b 0d 79 4d 00 00 	mov    0x4d79(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    42a7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    42ac:	be 01 00 00 00       	mov    $0x1,%esi
    42b1:	48 8d 3d 18 1e 00 00 	lea    0x1e18(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    42b8:	e8 e3 e1 ff ff       	call   24a0 <fwrite@plt>
    42bd:	eb c3                	jmp    4282 <copy_file_contents+0x52>
    42bf:	48 8b 0d 5a 4d 00 00 	mov    0x4d5a(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    42c6:	ba 28 00 00 00       	mov    $0x28,%edx
    42cb:	be 01 00 00 00       	mov    $0x1,%esi
    42d0:	48 8d 3d 49 21 00 00 	lea    0x2149(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    42d7:	e8 c4 e1 ff ff       	call   24a0 <fwrite@plt>
    42dc:	bf 01 00 00 00       	mov    $0x1,%edi
    42e1:	e8 9a e1 ff ff       	call   2480 <exit@plt>
    42e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000042f0 <add_write_request>:
    42f0:	f3 0f 1e fa          	endbr64
    42f4:	8b 46 44             	mov    0x44(%rsi),%eax
    42f7:	48 89 fa             	mov    %rdi,%rdx
    42fa:	48 89 f7             	mov    %rsi,%rdi
    42fd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    4303:	8d 70 01             	lea    0x1(%rax),%esi
    4306:	48 8b 07             	mov    (%rdi),%rax
    4309:	44 8b 00             	mov    (%rax),%r8d
    430c:	f6 c1 02             	test   $0x2,%cl
    430f:	74 00                	je     4311 <add_write_request+0x21>
    4311:	89 f0                	mov    %esi,%eax
    4313:	44 29 c0             	sub    %r8d,%eax
    4316:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4319:	0f 82 23 e2 ff ff    	jb     2542 <add_write_request.cold>
    431f:	c1 e9 0a             	shr    $0xa,%ecx
    4322:	48 83 ec 08          	sub    $0x8,%rsp
    4326:	8b 47 44             	mov    0x44(%rdi),%eax
    4329:	23 47 58             	and    0x58(%rdi),%eax
    432c:	83 e1 01             	and    $0x1,%ecx
    432f:	89 77 44             	mov    %esi,0x44(%rdi)
    4332:	8b 72 08             	mov    0x8(%rdx),%esi
    4335:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4339:	d3 e0                	shl    %cl,%eax
    433b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    433e:	48 c1 e0 06          	shl    $0x6,%rax
    4342:	48 03 47 38          	add    0x38(%rdi),%rax
    4346:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    434c:	89 70 04             	mov    %esi,0x4(%rax)
    434f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    4353:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4359:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4361:	48 89 70 10          	mov    %rsi,0x10(%rax)
    4365:	89 48 18             	mov    %ecx,0x18(%rax)
    4368:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    436f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4377:	48 89 50 20          	mov    %rdx,0x20(%rax)
    437b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    437f:	e8 9c df ff ff       	call   2320 <io_uring_submit@plt>
    4384:	31 c0                	xor    %eax,%eax
    4386:	48 83 c4 08          	add    $0x8,%rsp
    438a:	c3                   	ret
    438b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004390 <add_read_request>:
    4390:	f3 0f 1e fa          	endbr64
    4394:	41 55                	push   %r13
    4396:	41 89 fd             	mov    %edi,%r13d
    4399:	41 54                	push   %r12
    439b:	55                   	push   %rbp
    439c:	53                   	push   %rbx
    439d:	48 89 f3             	mov    %rsi,%rbx
    43a0:	48 83 ec 08          	sub    $0x8,%rsp
    43a4:	8b 46 44             	mov    0x44(%rsi),%eax
    43a7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    43ad:	48 8b 16             	mov    (%rsi),%rdx
    43b0:	83 c0 01             	add    $0x1,%eax
    43b3:	8b 32                	mov    (%rdx),%esi
    43b5:	f6 c1 02             	test   $0x2,%cl
    43b8:	74 00                	je     43ba <add_read_request+0x2a>
    43ba:	89 c2                	mov    %eax,%edx
    43bc:	29 f2                	sub    %esi,%edx
    43be:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    43c1:	0f 82 8b e1 ff ff    	jb     2552 <add_read_request.cold>
    43c7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    43ca:	c1 e9 0a             	shr    $0xa,%ecx
    43cd:	89 43 44             	mov    %eax,0x44(%rbx)
    43d0:	bf 20 00 00 00       	mov    $0x20,%edi
    43d5:	83 e1 01             	and    $0x1,%ecx
    43d8:	23 6b 58             	and    0x58(%rbx),%ebp
    43db:	d3 e5                	shl    %cl,%ebp
    43dd:	48 c1 e5 06          	shl    $0x6,%rbp
    43e1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    43e5:	e8 06 e0 ff ff       	call   23f0 <malloc@plt>
    43ea:	be 01 00 00 00       	mov    $0x1,%esi
    43ef:	bf 00 20 00 00       	mov    $0x2000,%edi
    43f4:	49 89 c4             	mov    %rax,%r12
    43f7:	e8 84 df ff ff       	call   2380 <calloc@plt>
    43fc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    4401:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4405:	48 89 df             	mov    %rbx,%rdi
    4408:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    440d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    4412:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    441b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    4423:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    4427:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    442b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    4432:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    443a:	48 89 45 10          	mov    %rax,0x10(%rbp)
    443e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    4446:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    444e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4452:	e8 c9 de ff ff       	call   2320 <io_uring_submit@plt>
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
    4470:	f3 0f 1e fa          	endbr64
    4474:	41 56                	push   %r14
    4476:	41 89 f6             	mov    %esi,%r14d
    4479:	41 55                	push   %r13
    447b:	49 89 fd             	mov    %rdi,%r13
    447e:	bf 20 00 00 00       	mov    $0x20,%edi
    4483:	41 54                	push   %r12
    4485:	55                   	push   %rbp
    4486:	48 89 d5             	mov    %rdx,%rbp
    4489:	53                   	push   %rbx
    448a:	e8 61 df ff ff       	call   23f0 <malloc@plt>
    448f:	48 85 c0             	test   %rax,%rax
    4492:	0f 84 dd 00 00 00    	je     4575 <_send_static_string_content+0x105>
    4498:	48 89 c3             	mov    %rax,%rbx
    449b:	4c 89 ef             	mov    %r13,%rdi
    449e:	e8 5d de ff ff       	call   2300 <strlen@plt>
    44a3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    44aa:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    44ae:	48 89 c7             	mov    %rax,%rdi
    44b1:	49 89 c4             	mov    %rax,%r12
    44b4:	e8 37 df ff ff       	call   23f0 <malloc@plt>
    44b9:	48 89 c7             	mov    %rax,%rdi
    44bc:	48 85 c0             	test   %rax,%rax
    44bf:	0f 84 b0 00 00 00    	je     4575 <_send_static_string_content+0x105>
    44c5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    44c9:	4c 89 e2             	mov    %r12,%rdx
    44cc:	4c 89 ee             	mov    %r13,%rsi
    44cf:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    44d3:	e8 e8 de ff ff       	call   23c0 <memcpy@plt>
    44d8:	8b 45 44             	mov    0x44(%rbp),%eax
    44db:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    44e1:	8d 50 01             	lea    0x1(%rax),%edx
    44e4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    44e8:	8b 30                	mov    (%rax),%esi
    44ea:	f6 c1 02             	test   $0x2,%cl
    44ed:	0f 85 7d 00 00 00    	jne    4570 <_send_static_string_content+0x100>
    44f3:	89 d0                	mov    %edx,%eax
    44f5:	29 f0                	sub    %esi,%eax
    44f7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    44fa:	0f 82 5c e0 ff ff    	jb     255c <_send_static_string_content.cold>
    4500:	c1 e9 0a             	shr    $0xa,%ecx
    4503:	8b 45 44             	mov    0x44(%rbp),%eax
    4506:	23 45 58             	and    0x58(%rbp),%eax
    4509:	89 55 44             	mov    %edx,0x44(%rbp)
    450c:	83 e1 01             	and    $0x1,%ecx
    450f:	8b 53 04             	mov    0x4(%rbx),%edx
    4512:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    4518:	66 0f ef c0          	pxor   %xmm0,%xmm0
    451c:	d3 e0                	shl    %cl,%eax
    451e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    4521:	48 89 ef             	mov    %rbp,%rdi
    4524:	48 c1 e0 06          	shl    $0x6,%rax
    4528:	48 03 45 38          	add    0x38(%rbp),%rax
    452c:	89 48 04             	mov    %ecx,0x4(%rax)
    452f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    4533:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4539:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4541:	48 89 48 10          	mov    %rcx,0x10(%rax)
    4545:	89 50 18             	mov    %edx,0x18(%rax)
    4548:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    454f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4557:	48 89 58 20          	mov    %rbx,0x20(%rax)
    455b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    455f:	5b                   	pop    %rbx
    4560:	5d                   	pop    %rbp
    4561:	41 5c                	pop    %r12
    4563:	41 5d                	pop    %r13
    4565:	41 5e                	pop    %r14
    4567:	e9 b4 dd ff ff       	jmp    2320 <io_uring_submit@plt>
    456c:	0f 1f 40 00          	nopl   0x0(%rax)
    4570:	e9 7e ff ff ff       	jmp    44f3 <_send_static_string_content+0x83>
    4575:	48 8b 0d a4 4a 00 00 	mov    0x4aa4(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    457c:	ba 28 00 00 00       	mov    $0x28,%edx
    4581:	be 01 00 00 00       	mov    $0x1,%esi
    4586:	48 8d 3d 93 1e 00 00 	lea    0x1e93(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    458d:	e8 0e df ff ff       	call   24a0 <fwrite@plt>
    4592:	bf 01 00 00 00       	mov    $0x1,%edi
    4597:	e8 e4 de ff ff       	call   2480 <exit@plt>
    459c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000045a0 <handle_unimplemented_method>:
    45a0:	f3 0f 1e fa          	endbr64
    45a4:	48 89 f2             	mov    %rsi,%rdx
    45a7:	89 fe                	mov    %edi,%esi
    45a9:	48 8b 3d 68 4a 00 00 	mov    0x4a68(%rip),%rdi        # 9018 <unimplemented_content>
    45b0:	e9 bb fe ff ff       	jmp    4470 <_send_static_string_content>
    45b5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000045c0 <handle_http_404>:
    45c0:	f3 0f 1e fa          	endbr64
    45c4:	48 89 f2             	mov    %rsi,%rdx
    45c7:	89 fe                	mov    %edi,%esi
    45c9:	48 8b 3d 40 4a 00 00 	mov    0x4a40(%rip),%rdi        # 9010 <http_404_content>
    45d0:	e9 9b fe ff ff       	jmp    4470 <_send_static_string_content>
    45d5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000045e0 <handle_get_method>:
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
    460f:	e8 ec dc ff ff       	call   2300 <strlen@plt>
    4614:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4619:	48 89 c3             	mov    %rax,%rbx
    461c:	0f 84 b6 00 00 00    	je     46d8 <handle_get_method+0xf8>
    4622:	b8 69 63 00 00       	mov    $0x6369,%eax
    4627:	48 89 ee             	mov    %rbp,%rsi
    462a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    462e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4633:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    463b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4643:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    464e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    4656:	e8 45 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    465b:	48 89 e6             	mov    %rsp,%rsi
    465e:	4c 89 f7             	mov    %r14,%rdi
    4661:	e8 4a dd ff ff       	call   23b0 <stat@plt>
    4666:	83 f8 ff             	cmp    $0xffffffff,%eax
    4669:	0f 84 d3 00 00 00    	je     4742 <handle_get_method+0x162>
    466f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4673:	25 00 f0 00 00       	and    $0xf000,%eax
    4678:	3d 00 80 00 00       	cmp    $0x8000,%eax
    467d:	0f 84 f5 00 00 00    	je     4778 <handle_get_method+0x198>
    4683:	48 8b 3d 86 49 00 00 	mov    0x4986(%rip),%rdi        # 9010 <http_404_content>
    468a:	4c 89 ea             	mov    %r13,%rdx
    468d:	44 89 e6             	mov    %r12d,%esi
    4690:	e8 db fd ff ff       	call   4470 <_send_static_string_content>
    4695:	4c 89 f2             	mov    %r14,%rdx
    4698:	bf 01 00 00 00       	mov    $0x1,%edi
    469d:	31 c0                	xor    %eax,%eax
    469f:	48 8d 35 7a 1a 00 00 	lea    0x1a7a(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    46a6:	e8 85 dd ff ff       	call   2430 <__printf_chk@plt>
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
    46d8:	ba 69 63 00 00       	mov    $0x6369,%edx
    46dd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    46e5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    46ea:	48 89 ee             	mov    %rbp,%rsi
    46ed:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    46f5:	48 89 c2             	mov    %rax,%rdx
    46f8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4700:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    470b:	e8 90 dc ff ff       	call   23a0 <__memcpy_chk@plt>
    4710:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4715:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    471a:	48 8d 35 ca 19 00 00 	lea    0x19ca(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    4721:	48 29 d9             	sub    %rbx,%rcx
    4724:	ba 0b 00 00 00       	mov    $0xb,%edx
    4729:	e8 72 dc ff ff       	call   23a0 <__memcpy_chk@plt>
    472e:	48 89 e6             	mov    %rsp,%rsi
    4731:	4c 89 f7             	mov    %r14,%rdi
    4734:	e8 77 dc ff ff       	call   23b0 <stat@plt>
    4739:	83 f8 ff             	cmp    $0xffffffff,%eax
    473c:	0f 85 2d ff ff ff    	jne    466f <handle_get_method+0x8f>
    4742:	4c 89 f2             	mov    %r14,%rdx
    4745:	48 89 e9             	mov    %rbp,%rcx
    4748:	48 8d 35 a7 19 00 00 	lea    0x19a7(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    474f:	31 c0                	xor    %eax,%eax
    4751:	bf 01 00 00 00       	mov    $0x1,%edi
    4756:	e8 d5 dc ff ff       	call   2430 <__printf_chk@plt>
    475b:	48 8b 3d ae 48 00 00 	mov    0x48ae(%rip),%rdi        # 9010 <http_404_content>
    4762:	4c 89 ea             	mov    %r13,%rdx
    4765:	44 89 e6             	mov    %r12d,%esi
    4768:	e8 03 fd ff ff       	call   4470 <_send_static_string_content>
    476d:	e9 39 ff ff ff       	jmp    46ab <handle_get_method+0xcb>
    4772:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4778:	bf 70 00 00 00       	mov    $0x70,%edi
    477d:	e8 6e dc ff ff       	call   23f0 <malloc@plt>
    4782:	48 89 c3             	mov    %rax,%rbx
    4785:	48 85 c0             	test   %rax,%rax
    4788:	74 5d                	je     47e7 <handle_get_method+0x207>
    478a:	44 89 60 08          	mov    %r12d,0x8(%rax)
    478e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4793:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4797:	4c 89 f7             	mov    %r14,%rdi
    479a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    47a1:	e8 5a f5 ff ff       	call   3d00 <send_headers>
    47a6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    47ab:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    47af:	4c 89 f7             	mov    %r14,%rdi
    47b2:	e8 79 fa ff ff       	call   4230 <copy_file_contents>
    47b7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    47bc:	4c 89 f2             	mov    %r14,%rdx
    47bf:	31 c0                	xor    %eax,%eax
    47c1:	48 8d 35 46 19 00 00 	lea    0x1946(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    47c8:	bf 01 00 00 00       	mov    $0x1,%edi
    47cd:	e8 5e dc ff ff       	call   2430 <__printf_chk@plt>
    47d2:	4c 89 ee             	mov    %r13,%rsi
    47d5:	48 89 df             	mov    %rbx,%rdi
    47d8:	e8 13 fb ff ff       	call   42f0 <add_write_request>
    47dd:	e9 c9 fe ff ff       	jmp    46ab <handle_get_method+0xcb>
    47e2:	e8 29 db ff ff       	call   2310 <__stack_chk_fail@plt>
    47e7:	48 8b 0d 32 48 00 00 	mov    0x4832(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    47ee:	ba 28 00 00 00       	mov    $0x28,%edx
    47f3:	be 01 00 00 00       	mov    $0x1,%esi
    47f8:	48 8d 3d 21 1c 00 00 	lea    0x1c21(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    47ff:	e8 9c dc ff ff       	call   24a0 <fwrite@plt>
    4804:	bf 01 00 00 00       	mov    $0x1,%edi
    4809:	e8 72 dc ff ff       	call   2480 <exit@plt>
    480e:	66 90                	xchg   %ax,%ax

0000000000004810 <handle_http_method>:
    4810:	f3 0f 1e fa          	endbr64
    4814:	41 57                	push   %r15
    4816:	41 56                	push   %r14
    4818:	4c 8d 35 66 18 00 00 	lea    0x1866(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
    481f:	41 55                	push   %r13
    4821:	49 89 d5             	mov    %rdx,%r13
    4824:	41 54                	push   %r12
    4826:	41 89 f4             	mov    %esi,%r12d
    4829:	4c 89 f6             	mov    %r14,%rsi
    482c:	55                   	push   %rbp
    482d:	53                   	push   %rbx
    482e:	48 83 ec 18          	sub    $0x18,%rsp
    4832:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    483b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4840:	31 c0                	xor    %eax,%eax
    4842:	49 89 e7             	mov    %rsp,%r15
    4845:	4c 89 fa             	mov    %r15,%rdx
    4848:	e8 13 db ff ff       	call   2360 <strtok_r@plt>
    484d:	48 0f be 18          	movsbq (%rax),%rbx
    4851:	48 89 c5             	mov    %rax,%rbp
    4854:	84 db                	test   %bl,%bl
    4856:	74 1d                	je     4875 <handle_http_method+0x65>
    4858:	e8 93 dc ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    485d:	48 89 ea             	mov    %rbp,%rdx
    4860:	48 8b 08             	mov    (%rax),%rcx
    4863:	48 83 c2 01          	add    $0x1,%rdx
    4867:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    486a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    486d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4871:	84 db                	test   %bl,%bl
    4873:	75 eb                	jne    4860 <handle_http_method+0x50>
    4875:	4c 89 fa             	mov    %r15,%rdx
    4878:	4c 89 f6             	mov    %r14,%rsi
    487b:	31 ff                	xor    %edi,%edi
    487d:	e8 de da ff ff       	call   2360 <strtok_r@plt>
    4882:	48 8d 35 aa 18 00 00 	lea    0x18aa(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    4889:	48 89 ef             	mov    %rbp,%rdi
    488c:	48 89 c3             	mov    %rax,%rbx
    488f:	e8 fc da ff ff       	call   2390 <strcmp@plt>
    4894:	4c 89 ea             	mov    %r13,%rdx
    4897:	44 89 e6             	mov    %r12d,%esi
    489a:	85 c0                	test   %eax,%eax
    489c:	75 2a                	jne    48c8 <handle_http_method+0xb8>
    489e:	48 89 df             	mov    %rbx,%rdi
    48a1:	e8 3a fd ff ff       	call   45e0 <handle_get_method>
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
    48c8:	48 8b 3d 49 47 00 00 	mov    0x4749(%rip),%rdi        # 9018 <unimplemented_content>
    48cf:	e8 9c fb ff ff       	call   4470 <_send_static_string_content>
    48d4:	eb d0                	jmp    48a6 <handle_http_method+0x96>
    48d6:	e8 35 da ff ff       	call   2310 <__stack_chk_fail@plt>
    48db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000048e0 <get_line>:
    48e0:	f3 0f 1e fa          	endbr64
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
    4905:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4909:	88 06                	mov    %al,(%rsi)
    490b:	3c 0d                	cmp    $0xd,%al
    490d:	75 e9                	jne    48f8 <get_line+0x18>
    490f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4912:	75 e4                	jne    48f8 <get_line+0x18>
    4914:	c6 06 00             	movb   $0x0,(%rsi)
    4917:	31 c0                	xor    %eax,%eax
    4919:	c3                   	ret
    491a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4920:	b8 01 00 00 00       	mov    $0x1,%eax
    4925:	c3                   	ret
    4926:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004930 <handle_client_request>:
    4930:	f3 0f 1e fa          	endbr64
    4934:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    493b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    493f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4948:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4950:	31 c0                	xor    %eax,%eax
    4952:	49 89 e2             	mov    %rsp,%r10
    4955:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    495d:	4c 89 d0             	mov    %r10,%rax
    4960:	eb 13                	jmp    4975 <handle_client_request+0x45>
    4962:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4968:	48 83 c0 01          	add    $0x1,%rax
    496c:	48 83 c1 01          	add    $0x1,%rcx
    4970:	4c 39 c8             	cmp    %r9,%rax
    4973:	74 4b                	je     49c0 <handle_client_request+0x90>
    4975:	44 0f b6 01          	movzbl (%rcx),%r8d
    4979:	44 88 00             	mov    %r8b,(%rax)
    497c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4980:	75 e6                	jne    4968 <handle_client_request+0x38>
    4982:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4986:	75 e0                	jne    4968 <handle_client_request+0x38>
    4988:	c6 00 00             	movb   $0x0,(%rax)
    498b:	8b 47 08             	mov    0x8(%rdi),%eax
    498e:	48 89 f2             	mov    %rsi,%rdx
    4991:	4c 89 d7             	mov    %r10,%rdi
    4994:	89 c6                	mov    %eax,%esi
    4996:	e8 75 fe ff ff       	call   4810 <handle_http_method>
    499b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    49a3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    49ac:	75 39                	jne    49e7 <handle_client_request+0xb7>
    49ae:	31 c0                	xor    %eax,%eax
    49b0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    49b7:	c3                   	ret
    49b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    49c0:	48 8b 0d 59 46 00 00 	mov    0x4659(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    49c7:	ba 12 00 00 00       	mov    $0x12,%edx
    49cc:	be 01 00 00 00       	mov    $0x1,%esi
    49d1:	48 8d 3d 5f 17 00 00 	lea    0x175f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    49d8:	e8 c3 da ff ff       	call   24a0 <fwrite@plt>
    49dd:	bf 01 00 00 00       	mov    $0x1,%edi
    49e2:	e8 99 da ff ff       	call   2480 <exit@plt>
    49e7:	e8 24 d9 ff ff       	call   2310 <__stack_chk_fail@plt>
    49ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000049f0 <add_accept_request>:
    49f0:	f3 0f 1e fa          	endbr64
    49f4:	55                   	push   %rbp
    49f5:	53                   	push   %rbx
    49f6:	48 89 cb             	mov    %rcx,%rbx
    49f9:	48 83 ec 08          	sub    $0x8,%rsp
    49fd:	8b 41 44             	mov    0x44(%rcx),%eax
    4a00:	4c 8b 03             	mov    (%rbx),%r8
    4a03:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    4a09:	83 c0 01             	add    $0x1,%eax
    4a0c:	45 8b 08             	mov    (%r8),%r9d
    4a0f:	f6 c1 02             	test   $0x2,%cl
    4a12:	74 00                	je     4a14 <add_accept_request+0x24>
    4a14:	41 89 c0             	mov    %eax,%r8d
    4a17:	45 29 c8             	sub    %r9d,%r8d
    4a1a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4a1e:	0f 82 48 db ff ff    	jb     256c <add_accept_request.cold>
    4a24:	c1 e9 0a             	shr    $0xa,%ecx
    4a27:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4a2a:	23 6b 58             	and    0x58(%rbx),%ebp
    4a2d:	89 43 44             	mov    %eax,0x44(%rbx)
    4a30:	83 e1 01             	and    $0x1,%ecx
    4a33:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4a37:	d3 e5                	shl    %cl,%ebp
    4a39:	48 c1 e5 06          	shl    $0x6,%rbp
    4a3d:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4a41:	89 7d 04             	mov    %edi,0x4(%rbp)
    4a44:	bf 10 00 00 00       	mov    $0x10,%edi
    4a49:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    4a50:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    4a54:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    4a58:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    4a60:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    4a68:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4a6c:	e8 7f d9 ff ff       	call   23f0 <malloc@plt>
    4a71:	48 89 df             	mov    %rbx,%rdi
    4a74:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    4a7a:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4a7e:	48 83 c4 08          	add    $0x8,%rsp
    4a82:	5b                   	pop    %rbx
    4a83:	5d                   	pop    %rbp
    4a84:	e9 97 d8 ff ff       	jmp    2320 <io_uring_submit@plt>
    4a89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004a90 <io_thread>:
    4a90:	f3 0f 1e fa          	endbr64
    4a94:	41 57                	push   %r15
    4a96:	31 d2                	xor    %edx,%edx
    4a98:	41 56                	push   %r14
    4a9a:	41 55                	push   %r13
    4a9c:	41 54                	push   %r12
    4a9e:	55                   	push   %rbp
    4a9f:	48 89 fd             	mov    %rdi,%rbp
    4aa2:	53                   	push   %rbx
    4aa3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4aaa:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4ab3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4abb:	48 8b 47 40          	mov    0x40(%rdi),%rax
    4abf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4ac4:	bf 00 01 00 00       	mov    $0x100,%edi
    4ac9:	48 89 de             	mov    %rbx,%rsi
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
    4b8c:	e8 3f d8 ff ff       	call   23d0 <io_uring_queue_init@plt>
    4b91:	48 8b 7d 40          	mov    0x40(%rbp),%rdi
    4b95:	31 f6                	xor    %esi,%esi
    4b97:	e8 24 d9 ff ff       	call   24c0 <io_uring_register_eventfd@plt>
    4b9c:	31 d2                	xor    %edx,%edx
    4b9e:	be 01 00 00 00       	mov    $0x1,%esi
    4ba3:	bf 02 00 00 00       	mov    $0x2,%edi
    4ba8:	e8 63 d9 ff ff       	call   2510 <socket@plt>
    4bad:	83 f8 ff             	cmp    $0xffffffff,%eax
    4bb0:	0f 84 f8 d9 ff ff    	je     25ae <io_thread.cold+0x38>
    4bb6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4bbb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4bc1:	89 c7                	mov    %eax,%edi
    4bc3:	41 89 c4             	mov    %eax,%r12d
    4bc6:	ba 02 00 00 00       	mov    $0x2,%edx
    4bcb:	be 01 00 00 00       	mov    $0x1,%esi
    4bd0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    4bd8:	e8 03 d7 ff ff       	call   22e0 <setsockopt@plt>
    4bdd:	85 c0                	test   %eax,%eax
    4bdf:	0f 88 9d d9 ff ff    	js     2582 <io_thread.cold+0xc>
    4be5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    4bea:	ba 10 00 00 00       	mov    $0x10,%edx
    4bef:	44 89 e7             	mov    %r12d,%edi
    4bf2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4bfb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    4c03:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
    4c0b:	e8 30 d8 ff ff       	call   2440 <bind@plt>
    4c10:	85 c0                	test   %eax,%eax
    4c12:	0f 88 a2 d9 ff ff    	js     25ba <io_thread.cold+0x44>
    4c18:	be 0a 00 00 00       	mov    $0xa,%esi
    4c1d:	44 89 e7             	mov    %r12d,%edi
    4c20:	e8 db d7 ff ff       	call   2400 <listen@plt>
    4c25:	85 c0                	test   %eax,%eax
    4c27:	0f 88 61 d9 ff ff    	js     258e <io_thread.cold+0x18>
    4c2d:	ba db 18 00 00       	mov    $0x18db,%edx
    4c32:	48 8d 35 43 15 00 00 	lea    0x1543(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4c39:	bf 01 00 00 00       	mov    $0x1,%edi
    4c3e:	31 c0                	xor    %eax,%eax
    4c40:	e8 eb d7 ff ff       	call   2430 <__printf_chk@plt>
    4c45:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4c4a:	48 89 d9             	mov    %rbx,%rcx
    4c4d:	44 89 e7             	mov    %r12d,%edi
    4c50:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4c55:	48 89 c6             	mov    %rax,%rsi
    4c58:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4c5d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    4c62:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    4c6a:	e8 81 fd ff ff       	call   49f0 <add_accept_request>
    4c6f:	bf 01 00 00 00       	mov    $0x1,%edi
    4c74:	be 10 00 00 00       	mov    $0x10,%esi
    4c79:	e8 02 d7 ff ff       	call   2380 <calloc@plt>
    4c7e:	bf 0a 00 00 00       	mov    $0xa,%edi
    4c83:	49 89 c5             	mov    %rax,%r13
    4c86:	e8 65 d7 ff ff       	call   23f0 <malloc@plt>
    4c8b:	48 85 c0             	test   %rax,%rax
    4c8e:	0f 84 ae 04 00 00    	je     5142 <io_thread+0x6b2>
    4c94:	49 89 45 00          	mov    %rax,0x0(%r13)
    4c98:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4c9f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4ca6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    4cae:	8d 50 01             	lea    0x1(%rax),%edx
    4cb1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4cb6:	8b 30                	mov    (%rax),%esi
    4cb8:	f6 c1 02             	test   $0x2,%cl
    4cbb:	0f 85 0f 04 00 00    	jne    50d0 <io_thread+0x640>
    4cc1:	89 d0                	mov    %edx,%eax
    4cc3:	29 f0                	sub    %esi,%eax
    4cc5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4ccc:	0f 82 d2 d8 ff ff    	jb     25a4 <io_thread.cold+0x2e>
    4cd2:	c1 e9 0a             	shr    $0xa,%ecx
    4cd5:	48 8d 75 48          	lea    0x48(%rbp),%rsi
    4cd9:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4cdd:	48 89 df             	mov    %rbx,%rdi
    4ce0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4ce7:	83 e1 01             	and    $0x1,%ecx
    4cea:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4cf1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4cf8:	d3 e0                	shl    %cl,%eax
    4cfa:	8b 55 48             	mov    0x48(%rbp),%edx
    4cfd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4d02:	48 c1 e0 06          	shl    $0x6,%rax
    4d06:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4d0e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4d14:	89 50 04             	mov    %edx,0x4(%rax)
    4d17:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4d1f:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4d23:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    4d2b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4d33:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4d37:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4d3b:	e8 e0 d5 ff ff       	call   2320 <io_uring_submit@plt>
    4d40:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
    4d44:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4d49:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4d51:	0f 85 d7 01 00 00    	jne    4f2e <io_thread+0x49e>
    4d57:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4d5c:	4d 89 ce             	mov    %r9,%r14
    4d5f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4d64:	0f 1f 40 00          	nopl   0x0(%rax)
    4d68:	48 8d 3d 23 14 00 00 	lea    0x1423(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4d6f:	e8 5c d5 ff ff       	call   22d0 <puts@plt>
    4d74:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4d7b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    4d82:	c1 e9 0b             	shr    $0xb,%ecx
    4d85:	83 e1 01             	and    $0x1,%ecx
    4d88:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4d90:	8b 00                	mov    (%rax),%eax
    4d92:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4d9a:	8b 16                	mov    (%rsi),%edx
    4d9c:	39 d0                	cmp    %edx,%eax
    4d9e:	74 36                	je     4dd6 <io_thread+0x346>
    4da0:	89 f8                	mov    %edi,%eax
    4da2:	21 d0                	and    %edx,%eax
    4da4:	d3 e0                	shl    %cl,%eax
    4da6:	48 c1 e0 04          	shl    $0x4,%rax
    4daa:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    4db2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4dba:	0f 85 a8 01 00 00    	jne    4f68 <io_thread+0x4d8>
    4dc0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4dc4:	0f 85 0e 03 00 00    	jne    50d8 <io_thread+0x648>
    4dca:	8b 40 08             	mov    0x8(%rax),%eax
    4dcd:	83 c2 01             	add    $0x1,%edx
    4dd0:	89 16                	mov    %edx,(%rsi)
    4dd2:	85 c0                	test   %eax,%eax
    4dd4:	79 b2                	jns    4d88 <io_thread+0x2f8>
    4dd6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    4ddf:	90                   	nop
    4de0:	45 31 c0             	xor    %r8d,%r8d
    4de3:	31 d2                	xor    %edx,%edx
    4de5:	b9 01 00 00 00       	mov    $0x1,%ecx
    4dea:	4c 89 f6             	mov    %r14,%rsi
    4ded:	48 89 df             	mov    %rbx,%rdi
    4df0:	e8 2b d6 ff ff       	call   2420 <__io_uring_get_cqe@plt>
    4df5:	41 89 c7             	mov    %eax,%r15d
    4df8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4dfd:	48 83 38 01          	cmpq   $0x1,(%rax)
    4e01:	0f 84 e1 02 00 00    	je     50e8 <io_thread+0x658>
    4e07:	48 8d 3d aa 13 00 00 	lea    0x13aa(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4e0e:	e8 bd d4 ff ff       	call   22d0 <puts@plt>
    4e13:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4e18:	4c 8b 22             	mov    (%rdx),%r12
    4e1b:	45 85 ff             	test   %r15d,%r15d
    4e1e:	0f 88 52 d7 ff ff    	js     2576 <io_thread.cold>
    4e24:	8b 42 08             	mov    0x8(%rdx),%eax
    4e27:	45 8b 04 24          	mov    (%r12),%r8d
    4e2b:	85 c0                	test   %eax,%eax
    4e2d:	0f 88 d5 02 00 00    	js     5108 <io_thread+0x678>
    4e33:	41 83 f8 01          	cmp    $0x1,%r8d
    4e37:	0f 84 7b 01 00 00    	je     4fb8 <io_thread+0x528>
    4e3d:	41 83 f8 02          	cmp    $0x2,%r8d
    4e41:	0f 84 a1 01 00 00    	je     4fe8 <io_thread+0x558>
    4e47:	45 85 c0             	test   %r8d,%r8d
    4e4a:	0f 85 50 01 00 00    	jne    4fa0 <io_thread+0x510>
    4e50:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    4e55:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    4e5a:	48 89 d9             	mov    %rbx,%rcx
    4e5d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4e61:	e8 8a fb ff ff       	call   49f0 <add_accept_request>
    4e66:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4e6b:	48 89 de             	mov    %rbx,%rsi
    4e6e:	8b 78 08             	mov    0x8(%rax),%edi
    4e71:	e8 1a f5 ff ff       	call   4390 <add_read_request>
    4e76:	4c 89 e7             	mov    %r12,%rdi
    4e79:	e8 32 d4 ff ff       	call   22b0 <free@plt>
    4e7e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4e83:	48 85 c0             	test   %rax,%rax
    4e86:	0f 85 14 01 00 00    	jne    4fa0 <io_thread+0x510>
    4e8c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4e93:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4e9a:	8d 50 01             	lea    0x1(%rax),%edx
    4e9d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4ea2:	8b 30                	mov    (%rax),%esi
    4ea4:	f6 c1 02             	test   $0x2,%cl
    4ea7:	74 00                	je     4ea9 <io_thread+0x419>
    4ea9:	89 d0                	mov    %edx,%eax
    4eab:	29 f0                	sub    %esi,%eax
    4ead:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4eb4:	0f 82 e0 d6 ff ff    	jb     259a <io_thread.cold+0x24>
    4eba:	c1 e9 0a             	shr    $0xa,%ecx
    4ebd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    4ec2:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4ec6:	48 89 df             	mov    %rbx,%rdi
    4ec9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4ed0:	83 e1 01             	and    $0x1,%ecx
    4ed3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4eda:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4ee1:	d3 e0                	shl    %cl,%eax
    4ee3:	8b 55 48             	mov    0x48(%rbp),%edx
    4ee6:	48 c1 e0 06          	shl    $0x6,%rax
    4eea:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4ef2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4ef8:	89 50 04             	mov    %edx,0x4(%rax)
    4efb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4f03:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4f07:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    4f0f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4f17:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4f1b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4f1f:	e8 fc d3 ff ff       	call   2320 <io_uring_submit@plt>
    4f24:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
    4f28:	0f 84 3a fe ff ff    	je     4d68 <io_thread+0x2d8>
    4f2e:	48 8d 3d bc 12 00 00 	lea    0x12bc(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    4f35:	e8 96 d3 ff ff       	call   22d0 <puts@plt>
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
    4f68:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    4f6d:	48 85 c0             	test   %rax,%rax
    4f70:	0f 84 6a fe ff ff    	je     4de0 <io_thread+0x350>
    4f76:	48 83 38 01          	cmpq   $0x1,(%rax)
    4f7a:	0f 84 68 01 00 00    	je     50e8 <io_thread+0x658>
    4f80:	48 8d 3d 31 12 00 00 	lea    0x1231(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4f87:	e8 44 d3 ff ff       	call   22d0 <puts@plt>
    4f8c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4f91:	4c 8b 22             	mov    (%rdx),%r12
    4f94:	e9 8b fe ff ff       	jmp    4e24 <io_thread+0x394>
    4f99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4fa0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4fa8:	8b 02                	mov    (%rdx),%eax
    4faa:	83 c0 01             	add    $0x1,%eax
    4fad:	89 02                	mov    %eax,(%rdx)
    4faf:	e9 d8 fe ff ff       	jmp    4e8c <io_thread+0x3fc>
    4fb4:	0f 1f 40 00          	nopl   0x0(%rax)
    4fb8:	85 c0                	test   %eax,%eax
    4fba:	75 74                	jne    5030 <io_thread+0x5a0>
    4fbc:	48 8b 0d 5d 40 00 00 	mov    0x405d(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4fc3:	ba 0f 00 00 00       	mov    $0xf,%edx
    4fc8:	be 01 00 00 00       	mov    $0x1,%esi
    4fcd:	48 8d 3d 0d 12 00 00 	lea    0x120d(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    4fd4:	e8 c7 d4 ff ff       	call   24a0 <fwrite@plt>
    4fd9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4fde:	e9 a0 fe ff ff       	jmp    4e83 <io_thread+0x3f3>
    4fe3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4fe8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    4fed:	45 31 ff             	xor    %r15d,%r15d
    4ff0:	85 c0                	test   %eax,%eax
    4ff2:	7e 20                	jle    5014 <io_thread+0x584>
    4ff4:	0f 1f 40 00          	nopl   0x0(%rax)
    4ff8:	4c 89 f8             	mov    %r15,%rax
    4ffb:	49 83 c7 01          	add    $0x1,%r15
    4fff:	48 c1 e0 04          	shl    $0x4,%rax
    5003:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5008:	e8 a3 d2 ff ff       	call   22b0 <free@plt>
    500d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5012:	7f e4                	jg     4ff8 <io_thread+0x568>
    5014:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5019:	e8 32 d3 ff ff       	call   2350 <close@plt>
    501e:	4c 89 e7             	mov    %r12,%rdi
    5021:	e8 8a d2 ff ff       	call   22b0 <free@plt>
    5026:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    502b:	e9 53 fe ff ff       	jmp    4e83 <io_thread+0x3f3>
    5030:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5035:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    503a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5042:	eb 11                	jmp    5055 <io_thread+0x5c5>
    5044:	0f 1f 40 00          	nopl   0x0(%rax)
    5048:	48 83 c0 01          	add    $0x1,%rax
    504c:	48 83 c2 01          	add    $0x1,%rdx
    5050:	48 39 c6             	cmp    %rax,%rsi
    5053:	74 4b                	je     50a0 <io_thread+0x610>
    5055:	0f b6 0a             	movzbl (%rdx),%ecx
    5058:	88 08                	mov    %cl,(%rax)
    505a:	80 f9 0d             	cmp    $0xd,%cl
    505d:	75 e9                	jne    5048 <io_thread+0x5b8>
    505f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5063:	75 e3                	jne    5048 <io_thread+0x5b8>
    5065:	c6 00 00             	movb   $0x0,(%rax)
    5068:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    506d:	48 89 da             	mov    %rbx,%rdx
    5070:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5075:	e8 96 f7 ff ff       	call   4810 <handle_http_method>
    507a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    507f:	e8 2c d2 ff ff       	call   22b0 <free@plt>
    5084:	4c 89 e7             	mov    %r12,%rdi
    5087:	e8 24 d2 ff ff       	call   22b0 <free@plt>
    508c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5091:	e9 ed fd ff ff       	jmp    4e83 <io_thread+0x3f3>
    5096:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    50a0:	48 8b 0d 79 3f 00 00 	mov    0x3f79(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    50a7:	ba 12 00 00 00       	mov    $0x12,%edx
    50ac:	be 01 00 00 00       	mov    $0x1,%esi
    50b1:	48 8d 3d 7f 10 00 00 	lea    0x107f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    50b8:	e8 e3 d3 ff ff       	call   24a0 <fwrite@plt>
    50bd:	bf 01 00 00 00       	mov    $0x1,%edi
    50c2:	e8 b9 d3 ff ff       	call   2480 <exit@plt>
    50c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    50d0:	e9 ec fb ff ff       	jmp    4cc1 <io_thread+0x231>
    50d5:	0f 1f 00             	nopl   (%rax)
    50d8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    50dd:	e9 94 fe ff ff       	jmp    4f76 <io_thread+0x4e6>
    50e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    50e8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    50f0:	48 8d 3d ad 10 00 00 	lea    0x10ad(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    50f7:	8b 02                	mov    (%rdx),%eax
    50f9:	83 c0 01             	add    $0x1,%eax
    50fc:	89 02                	mov    %eax,(%rdx)
    50fe:	e8 cd d1 ff ff       	call   22d0 <puts@plt>
    5103:	e9 26 fe ff ff       	jmp    4f2e <io_thread+0x49e>
    5108:	f7 d8                	neg    %eax
    510a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    510f:	89 c7                	mov    %eax,%edi
    5111:	e8 ca d3 ff ff       	call   24e0 <strerror@plt>
    5116:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    511b:	be 01 00 00 00       	mov    $0x1,%esi
    5120:	48 8b 3d f9 3e 00 00 	mov    0x3ef9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    5127:	48 89 c1             	mov    %rax,%rcx
    512a:	48 8d 15 1f 13 00 00 	lea    0x131f(%rip),%rdx        # 6450 <_IO_stdin_used+0x450>
    5131:	31 c0                	xor    %eax,%eax
    5133:	e8 78 d3 ff ff       	call   24b0 <__fprintf_chk@plt>
    5138:	bf 01 00 00 00       	mov    $0x1,%edi
    513d:	e8 3e d3 ff ff       	call   2480 <exit@plt>
    5142:	48 8b 0d d7 3e 00 00 	mov    0x3ed7(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5149:	ba 28 00 00 00       	mov    $0x28,%edx
    514e:	be 01 00 00 00       	mov    $0x1,%esi
    5153:	48 8d 3d c6 12 00 00 	lea    0x12c6(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    515a:	e8 41 d3 ff ff       	call   24a0 <fwrite@plt>
    515f:	bf 01 00 00 00       	mov    $0x1,%edi
    5164:	e8 17 d3 ff ff       	call   2480 <exit@plt>
    5169:	e8 a2 d1 ff ff       	call   2310 <__stack_chk_fail@plt>
    516e:	66 90                	xchg   %ax,%ax

0000000000005170 <receive>:
    5170:	f3 0f 1e fa          	endbr64
    5174:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    517a:	85 c0                	test   %eax,%eax
    517c:	0f 8e ed 00 00 00    	jle    526f <receive+0xff>
    5182:	41 54                	push   %r12
    5184:	4c 63 e0             	movslq %eax,%r12
    5187:	48 89 fa             	mov    %rdi,%rdx
    518a:	55                   	push   %rbp
    518b:	49 c1 e4 05          	shl    $0x5,%r12
    518f:	53                   	push   %rbx
    5190:	48 8b b7 28 02 00 00 	mov    0x228(%rdi),%rsi
    5197:	49 01 f4             	add    %rsi,%r12
    519a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    51a0:	48 8b 2e             	mov    (%rsi),%rbp
    51a3:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    51aa:	48 85 ff             	test   %rdi,%rdi
    51ad:	0f 8e 9d 00 00 00    	jle    5250 <receive+0xe0>
    51b3:	48 8b 8a 30 02 00 00 	mov    0x230(%rdx),%rcx
    51ba:	4c 8b 45 00          	mov    0x0(%rbp),%r8
    51be:	4c 63 1a             	movslq (%rdx),%r11
    51c1:	49 89 c9             	mov    %rcx,%r9
    51c4:	48 8d 41 01          	lea    0x1(%rcx),%rax
    51c8:	49 f7 d9             	neg    %r9
    51cb:	48 01 c7             	add    %rax,%rdi
    51ce:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
    51d2:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
    51d9:	4c 8b 46 18          	mov    0x18(%rsi),%r8
    51dd:	49 29 c9             	sub    %rcx,%r9
    51e0:	49 29 c8             	sub    %rcx,%r8
    51e3:	eb 0c                	jmp    51f1 <receive+0x81>
    51e5:	0f 1f 00             	nopl   (%rax)
    51e8:	48 83 c0 01          	add    $0x1,%rax
    51ec:	48 39 c7             	cmp    %rax,%rdi
    51ef:	74 5f                	je     5250 <receive+0xe0>
    51f1:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    51f5:	48 89 82 30 02 00 00 	mov    %rax,0x230(%rdx)
    51fc:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
    5203:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5207:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
    520b:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5210:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5214:	75 d2                	jne    51e8 <receive+0x78>
    5216:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    521d:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5221:	75 c5                	jne    51e8 <receive+0x78>
    5223:	bf 01 00 00 00       	mov    $0x1,%edi
    5228:	b9 01 00 00 00       	mov    $0x1,%ecx
    522d:	ba 01 00 00 00       	mov    $0x1,%edx
    5232:	31 c0                	xor    %eax,%eax
    5234:	48 8d 35 3d 12 00 00 	lea    0x123d(%rip),%rsi        # 6478 <_IO_stdin_used+0x478>
    523b:	e8 f0 d1 ff ff       	call   2430 <__printf_chk@plt>
    5240:	bf 01 00 00 00       	mov    $0x1,%edi
    5245:	e8 36 d2 ff ff       	call   2480 <exit@plt>
    524a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5250:	48 c7 85 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rbp)
    525b:	48 83 c6 20          	add    $0x20,%rsi
    525f:	49 39 f4             	cmp    %rsi,%r12
    5262:	0f 85 38 ff ff ff    	jne    51a0 <receive+0x30>
    5268:	5b                   	pop    %rbx
    5269:	31 c0                	xor    %eax,%eax
    526b:	5d                   	pop    %rbp
    526c:	41 5c                	pop    %r12
    526e:	c3                   	ret
    526f:	31 c0                	xor    %eax,%eax
    5271:	c3                   	ret
    5272:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    527d:	0f 1f 00             	nopl   (%rax)

0000000000005280 <barriered_work>:
    5280:	f3 0f 1e fa          	endbr64
    5284:	41 57                	push   %r15
    5286:	41 56                	push   %r14
    5288:	41 55                	push   %r13
    528a:	41 54                	push   %r12
    528c:	55                   	push   %rbp
    528d:	53                   	push   %rbx
    528e:	48 89 fb             	mov    %rdi,%rbx
    5291:	48 83 ec 28          	sub    $0x28,%rsp
    5295:	8b 07                	mov    (%rdi),%eax
    5297:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    529d:	0f 84 4d 01 00 00    	je     53f0 <barriered_work+0x170>
    52a3:	e8 c8 fe ff ff       	call   5170 <receive>
    52a8:	eb 11                	jmp    52bb <barriered_work+0x3b>
    52aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    52b0:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    52b8:	0f ae f8             	sfence
    52bb:	8b 83 00 02 00 00    	mov    0x200(%rbx),%eax
    52c1:	83 f8 01             	cmp    $0x1,%eax
    52c4:	74 ea                	je     52b0 <barriered_work+0x30>
    52c6:	83 bb 38 02 00 00 01 	cmpl   $0x1,0x238(%rbx)
    52cd:	74 14                	je     52e3 <barriered_work+0x63>
    52cf:	0f ae f0             	mfence
    52d2:	48 83 c4 28          	add    $0x28,%rsp
    52d6:	31 c0                	xor    %eax,%eax
    52d8:	5b                   	pop    %rbx
    52d9:	5d                   	pop    %rbp
    52da:	41 5c                	pop    %r12
    52dc:	41 5d                	pop    %r13
    52de:	41 5e                	pop    %r14
    52e0:	41 5f                	pop    %r15
    52e2:	c3                   	ret
    52e3:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    52e9:	85 c0                	test   %eax,%eax
    52eb:	7e e2                	jle    52cf <barriered_work+0x4f>
    52ed:	8b bb 30 01 00 00    	mov    0x130(%rbx),%edi
    52f3:	4c 63 f8             	movslq %eax,%r15
    52f6:	48 8d 83 40 02 00 00 	lea    0x240(%rbx),%rax
    52fd:	31 d2                	xor    %edx,%edx
    52ff:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5304:	48 8d 83 48 02 00 00 	lea    0x248(%rbx),%rax
    530b:	89 7c 24 04          	mov    %edi,0x4(%rsp)
    530f:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5314:	0f 1f 40 00          	nopl   0x0(%rax)
    5318:	39 54 24 04          	cmp    %edx,0x4(%rsp)
    531c:	0f 84 bc 00 00 00    	je     53de <barriered_work+0x15e>
    5322:	49 89 d0             	mov    %rdx,%r8
    5325:	49 c1 e0 05          	shl    $0x5,%r8
    5329:	4c 03 83 28 02 00 00 	add    0x228(%rbx),%r8
    5330:	4d 8b 48 08          	mov    0x8(%r8),%r9
    5334:	4d 8b 99 80 00 00 00 	mov    0x80(%r9),%r11
    533b:	49 63 b9 88 00 00 00 	movslq 0x88(%r9),%rdi
    5342:	49 39 fb             	cmp    %rdi,%r11
    5345:	0f 8d 93 00 00 00    	jge    53de <barriered_work+0x15e>
    534b:	49 89 fa             	mov    %rdi,%r10
    534e:	4c 8b b3 08 01 00 00 	mov    0x108(%rbx),%r14
    5355:	49 8b 68 10          	mov    0x10(%r8),%rbp
    5359:	4d 29 da             	sub    %r11,%r10
    535c:	49 8b 09             	mov    (%r9),%rcx
    535f:	49 8d 42 ff          	lea    -0x1(%r10),%rax
    5363:	48 83 f8 02          	cmp    $0x2,%rax
    5367:	0f 86 7b 02 00 00    	jbe    55e8 <barriered_work+0x368>
    536d:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5375:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    537d:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5381:	4c 8d 2c 31          	lea    (%rcx,%rsi,1),%r13
    5385:	4c 39 6c 24 08       	cmp    %r13,0x8(%rsp)
    538a:	0f 83 e0 01 00 00    	jae    5570 <barriered_work+0x2f0>
    5390:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    5395:	4d 39 ec             	cmp    %r13,%r12
    5398:	0f 83 d2 01 00 00    	jae    5570 <barriered_work+0x2f0>
    539e:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    53a2:	48 01 ce             	add    %rcx,%rsi
    53a5:	0f 1f 00             	nopl   (%rax)
    53a8:	48 8b 83 40 02 00 00 	mov    0x240(%rbx),%rax
    53af:	49 83 c3 08          	add    $0x8,%r11
    53b3:	49 89 43 f8          	mov    %rax,-0x8(%r11)
    53b7:	4c 39 de             	cmp    %r11,%rsi
    53ba:	75 ec                	jne    53a8 <barriered_work+0x128>
    53bc:	0f 1f 40 00          	nopl   0x0(%rax)
    53c0:	4b 8d 34 16          	lea    (%r14,%r10,1),%rsi
    53c4:	4c 01 d5             	add    %r10,%rbp
    53c7:	48 89 b3 08 01 00 00 	mov    %rsi,0x108(%rbx)
    53ce:	49 89 68 10          	mov    %rbp,0x10(%r8)
    53d2:	49 89 b9 80 00 00 00 	mov    %rdi,0x80(%r9)
    53d9:	48 89 44 f9 f8       	mov    %rax,-0x8(%rcx,%rdi,8)
    53de:	48 83 c2 01          	add    $0x1,%rdx
    53e2:	4c 39 fa             	cmp    %r15,%rdx
    53e5:	0f 85 2d ff ff ff    	jne    5318 <barriered_work+0x98>
    53eb:	e9 df fe ff ff       	jmp    52cf <barriered_work+0x4f>
    53f0:	e8 7b fd ff ff       	call   5170 <receive>
    53f5:	8b 8b 34 01 00 00    	mov    0x134(%rbx),%ecx
    53fb:	8b 03                	mov    (%rbx),%eax
    53fd:	85 c9                	test   %ecx,%ecx
    53ff:	0f 8e 8e 00 00 00    	jle    5493 <barriered_work+0x213>
    5405:	48 63 d0             	movslq %eax,%rdx
    5408:	83 c0 01             	add    $0x1,%eax
    540b:	4c 63 d9             	movslq %ecx,%r11
    540e:	48 8d 2c 92          	lea    (%rdx,%rdx,4),%rbp
    5412:	99                   	cltd
    5413:	f7 f9                	idiv   %ecx
    5415:	48 c1 e5 07          	shl    $0x7,%rbp
    5419:	89 d0                	mov    %edx,%eax
    541b:	f7 d8                	neg    %eax
    541d:	0f 48 c2             	cmovs  %edx,%eax
    5420:	49 c1 e3 05          	shl    $0x5,%r11
    5424:	31 ff                	xor    %edi,%edi
    5426:	48 98                	cltq
    5428:	4c 8d 0c 80          	lea    (%rax,%rax,4),%r9
    542c:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    5433:	49 c1 e1 07          	shl    $0x7,%r9
    5437:	4c 8b 60 10          	mov    0x10(%rax),%r12
    543b:	49 83 c4 20          	add    $0x20,%r12
    543f:	4d 89 e2             	mov    %r12,%r10
    5442:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5448:	49 8b 02             	mov    (%r10),%rax
    544b:	4c 89 e2             	mov    %r12,%rdx
    544e:	48 8b 84 28 28 02 00 00 	mov    0x228(%rax,%rbp,1),%rax
    5456:	4d 8d 04 03          	lea    (%r11,%rax,1),%r8
    545a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5460:	48 8b 0a             	mov    (%rdx),%rcx
    5463:	48 8b 70 08          	mov    0x8(%rax),%rsi
    5467:	48 83 c0 20          	add    $0x20,%rax
    546b:	48 81 c2 98 00 00 00 	add    $0x98,%rdx
    5472:	4a 8b 8c 09 28 02 00 00 	mov    0x228(%rcx,%r9,1),%rcx
    547a:	48 89 34 39          	mov    %rsi,(%rcx,%rdi,1)
    547e:	4c 39 c0             	cmp    %r8,%rax
    5481:	75 dd                	jne    5460 <barriered_work+0x1e0>
    5483:	48 83 c7 20          	add    $0x20,%rdi
    5487:	49 81 c2 98 00 00 00 	add    $0x98,%r10
    548e:	4c 39 df             	cmp    %r11,%rdi
    5491:	75 b5                	jne    5448 <barriered_work+0x1c8>
    5493:	0f ae f0             	mfence
    5496:	48 8b b3 18 02 00 00 	mov    0x218(%rbx),%rsi
    549d:	31 ff                	xor    %edi,%edi
    549f:	48 c1 e6 05          	shl    $0x5,%rsi
    54a3:	48 03 b3 08 02 00 00 	add    0x208(%rbx),%rsi
    54aa:	e8 41 ce ff ff       	call   22f0 <clock_gettime@plt>
    54af:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    54b6:	48 8b 40 30          	mov    0x30(%rax),%rax
    54ba:	8b 78 10             	mov    0x10(%rax),%edi
    54bd:	8d 6f 01             	lea    0x1(%rdi),%ebp
    54c0:	89 68 10             	mov    %ebp,0x10(%rax)
    54c3:	eb 41                	jmp    5506 <barriered_work+0x286>
    54c5:	0f 1f 00             	nopl   (%rax)
    54c8:	48 63 83 30 01 00 00 	movslq 0x130(%rbx),%rax
    54cf:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    54d6:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    54de:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    54e2:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    54e6:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    54ea:	48 63 13             	movslq (%rbx),%rdx
    54ed:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    54f1:	48 8d 3c 92          	lea    (%rdx,%rdx,4),%rdi
    54f5:	48 c1 e7 07          	shl    $0x7,%rdi
    54f9:	48 03 78 20          	add    0x20(%rax),%rdi
    54fd:	ff 93 20 01 00 00    	call   *0x120(%rbx)
    5503:	0f ae f8             	sfence
    5506:	8b 83 00 02 00 00    	mov    0x200(%rbx),%eax
    550c:	83 f8 01             	cmp    $0x1,%eax
    550f:	74 b7                	je     54c8 <barriered_work+0x248>
    5511:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    5518:	48 8b 40 30          	mov    0x30(%rax),%rax
    551c:	39 68 10             	cmp    %ebp,0x10(%rax)
    551f:	75 3d                	jne    555e <barriered_work+0x2de>
    5521:	48 8b b3 18 02 00 00 	mov    0x218(%rbx),%rsi
    5528:	31 ff                	xor    %edi,%edi
    552a:	48 c1 e6 05          	shl    $0x5,%rsi
    552e:	48 03 b3 08 02 00 00 	add    0x208(%rbx),%rsi
    5535:	48 83 c6 10          	add    $0x10,%rsi
    5539:	e8 b2 cd ff ff       	call   22f0 <clock_gettime@plt>
    553e:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    5545:	48 83 c0 01          	add    $0x1,%rax
    5549:	48 99                	cqto
    554b:	48 f7 bb 10 02 00 00 	idivq  0x210(%rbx)
    5552:	48 89 93 18 02 00 00 	mov    %rdx,0x218(%rbx)
    5559:	e9 71 fd ff ff       	jmp    52cf <barriered_work+0x4f>
    555e:	48 8d 3d 9f 0c 00 00 	lea    0xc9f(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    5565:	e8 66 cd ff ff       	call   22d0 <puts@plt>
    556a:	eb b5                	jmp    5521 <barriered_work+0x2a1>
    556c:	0f 1f 40 00          	nopl   0x0(%rax)
    5570:	48 8b 83 40 02 00 00 	mov    0x240(%rbx),%rax
    5577:	4d 89 d5             	mov    %r10,%r13
    557a:	4c 89 e6             	mov    %r12,%rsi
    557d:	49 d1 ed             	shr    %r13
    5580:	49 c1 e5 04          	shl    $0x4,%r13
    5584:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5589:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
    558e:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5592:	4d 01 e5             	add    %r12,%r13
    5595:	f6 44 24 18 10       	testb  $0x10,0x18(%rsp)
    559a:	74 14                	je     55b0 <barriered_work+0x330>
    559c:	48 83 c6 10          	add    $0x10,%rsi
    55a0:	41 0f 11 04 24       	movups %xmm0,(%r12)
    55a5:	49 39 f5             	cmp    %rsi,%r13
    55a8:	74 16                	je     55c0 <barriered_work+0x340>
    55aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    55b0:	0f 11 06             	movups %xmm0,(%rsi)
    55b3:	48 83 c6 20          	add    $0x20,%rsi
    55b7:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
    55bb:	49 39 f5             	cmp    %rsi,%r13
    55be:	75 f0                	jne    55b0 <barriered_work+0x330>
    55c0:	4c 89 d6             	mov    %r10,%rsi
    55c3:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    55c7:	4c 01 de             	add    %r11,%rsi
    55ca:	41 f6 c2 01          	test   $0x1,%r10b
    55ce:	0f 84 ec fd ff ff    	je     53c0 <barriered_work+0x140>
    55d4:	48 8b 83 40 02 00 00 	mov    0x240(%rbx),%rax
    55db:	48 89 04 f1          	mov    %rax,(%rcx,%rsi,8)
    55df:	e9 dc fd ff ff       	jmp    53c0 <barriered_work+0x140>
    55e4:	0f 1f 40 00          	nopl   0x0(%rax)
    55e8:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    55f0:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    55f8:	e9 a1 fd ff ff       	jmp    539e <barriered_work+0x11e>
    55fd:	0f 1f 00             	nopl   (%rax)

0000000000005600 <barriered_work_ingest>:
    5600:	f3 0f 1e fa          	endbr64
    5604:	48 83 ec 08          	sub    $0x8,%rsp
    5608:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    560f:	48 8b 40 38          	mov    0x38(%rax),%rax
    5613:	48 63 10             	movslq (%rax),%rdx
    5616:	85 d2                	test   %edx,%edx
    5618:	7e 2c                	jle    5646 <barriered_work_ingest+0x46>
    561a:	48 8b 40 08          	mov    0x8(%rax),%rax
    561e:	48 c1 e2 04          	shl    $0x4,%rdx
    5622:	48 01 c2             	add    %rax,%rdx
    5625:	0f 1f 00             	nopl   (%rax)
    5628:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    562c:	75 0f                	jne    563d <barriered_work_ingest+0x3d>
    562e:	48 83 87 20 02 00 00 01 	addq   $0x1,0x220(%rdi)
    5636:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    563d:	48 83 c0 10          	add    $0x10,%rax
    5641:	48 39 d0             	cmp    %rdx,%rax
    5644:	75 e2                	jne    5628 <barriered_work_ingest+0x28>
    5646:	0f ae f0             	mfence
    5649:	e8 32 fc ff ff       	call   5280 <barriered_work>
    564e:	31 c0                	xor    %eax,%eax
    5650:	48 83 c4 08          	add    $0x8,%rsp
    5654:	c3                   	ret
    5655:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005660 <barriered_nulltask>:
    5660:	f3 0f 1e fa          	endbr64
    5664:	31 c0                	xor    %eax,%eax
    5666:	c3                   	ret
    5667:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005670 <barriered_steal>:
    5670:	f3 0f 1e fa          	endbr64
    5674:	31 c0                	xor    %eax,%eax
    5676:	c3                   	ret
    5677:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005680 <after>:
    5680:	f3 0f 1e fa          	endbr64
    5684:	31 c0                	xor    %eax,%eax
    5686:	48 39 d7             	cmp    %rdx,%rdi
    5689:	7e 08                	jle    5693 <after+0x13>
    568b:	31 c0                	xor    %eax,%eax
    568d:	48 39 ce             	cmp    %rcx,%rsi
    5690:	0f 9f c0             	setg   %al
    5693:	c3                   	ret
    5694:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    569f:	90                   	nop

00000000000056a0 <within>:
    56a0:	f3 0f 1e fa          	endbr64
    56a4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    56a9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    56ae:	31 c0                	xor    %eax,%eax
    56b0:	48 39 d7             	cmp    %rdx,%rdi
    56b3:	7f 18                	jg     56cd <within+0x2d>
    56b5:	4d 39 d8             	cmp    %r11,%r8
    56b8:	0f 9e c2             	setle  %dl
    56bb:	48 39 ce             	cmp    %rcx,%rsi
    56be:	0f 9e c0             	setle  %al
    56c1:	21 c2                	and    %eax,%edx
    56c3:	31 c0                	xor    %eax,%eax
    56c5:	4d 39 d1             	cmp    %r10,%r9
    56c8:	0f 9e c0             	setle  %al
    56cb:	21 d0                	and    %edx,%eax
    56cd:	c3                   	ret
    56ce:	66 90                	xchg   %ax,%ax

00000000000056d0 <overlap>:
    56d0:	f3 0f 1e fa          	endbr64
    56d4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    56d9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    56de:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    56e3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    56e8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    56ed:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
    56f2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    56f7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    56fc:	48 39 fe             	cmp    %rdi,%rsi
    56ff:	7d 2f                	jge    5730 <overlap+0x60>
    5701:	48 39 ca             	cmp    %rcx,%rdx
    5704:	7d 62                	jge    5768 <overlap+0x98>
    5706:	4d 39 da             	cmp    %r11,%r10
    5709:	7d 0e                	jge    5719 <overlap+0x49>
    570b:	b8 01 00 00 00       	mov    $0x1,%eax
    5710:	4d 39 c1             	cmp    %r8,%r9
    5713:	0f 8c 7f 00 00 00    	jl     5798 <overlap+0xc8>
    5719:	31 c0                	xor    %eax,%eax
    571b:	4d 39 c1             	cmp    %r8,%r9
    571e:	7f 4c                	jg     576c <overlap+0x9c>
    5720:	31 c0                	xor    %eax,%eax
    5722:	4d 39 da             	cmp    %r11,%r10
    5725:	0f 9e c0             	setle  %al
    5728:	c3                   	ret
    5729:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5730:	7e 4e                	jle    5780 <overlap+0xb0>
    5732:	48 39 ca             	cmp    %rcx,%rdx
    5735:	7f 39                	jg     5770 <overlap+0xa0>
    5737:	75 31                	jne    576a <overlap+0x9a>
    5739:	4d 39 c1             	cmp    %r8,%r9
    573c:	7c 2c                	jl     576a <overlap+0x9a>
    573e:	b8 01 00 00 00       	mov    $0x1,%eax
    5743:	4d 39 da             	cmp    %r11,%r10
    5746:	7d 24                	jge    576c <overlap+0x9c>
    5748:	48 39 ca             	cmp    %rcx,%rdx
    574b:	0f 94 c2             	sete   %dl
    574e:	48 39 fe             	cmp    %rdi,%rsi
    5751:	0f 94 c0             	sete   %al
    5754:	21 c2                	and    %eax,%edx
    5756:	31 c0                	xor    %eax,%eax
    5758:	4d 39 c1             	cmp    %r8,%r9
    575b:	0f 94 c0             	sete   %al
    575e:	21 d0                	and    %edx,%eax
    5760:	c3                   	ret
    5761:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5768:	74 af                	je     5719 <overlap+0x49>
    576a:	31 c0                	xor    %eax,%eax
    576c:	c3                   	ret
    576d:	0f 1f 00             	nopl   (%rax)
    5770:	4d 39 da             	cmp    %r11,%r10
    5773:	7e c4                	jle    5739 <overlap+0x69>
    5775:	b8 01 00 00 00       	mov    $0x1,%eax
    577a:	4d 39 c1             	cmp    %r8,%r9
    577d:	7e ba                	jle    5739 <overlap+0x69>
    577f:	c3                   	ret
    5780:	48 39 ca             	cmp    %rcx,%rdx
    5783:	7c 94                	jl     5719 <overlap+0x49>
    5785:	4d 39 c1             	cmp    %r8,%r9
    5788:	7d b4                	jge    573e <overlap+0x6e>
    578a:	48 39 ca             	cmp    %rcx,%rdx
    578d:	74 91                	je     5720 <overlap+0x50>
    578f:	eb d9                	jmp    576a <overlap+0x9a>
    5791:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5798:	c3                   	ret
    5799:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000057a0 <verify>:
    57a0:	f3 0f 1e fa          	endbr64
    57a4:	85 f6                	test   %esi,%esi
    57a6:	0f 8e 49 03 00 00    	jle    5af5 <verify+0x355>
    57ac:	41 57                	push   %r15
    57ae:	41 89 f7             	mov    %esi,%r15d
    57b1:	41 56                	push   %r14
    57b3:	45 31 f6             	xor    %r14d,%r14d
    57b6:	41 55                	push   %r13
    57b8:	41 54                	push   %r12
    57ba:	55                   	push   %rbp
    57bb:	53                   	push   %rbx
    57bc:	48 8d 5f 20          	lea    0x20(%rdi),%rbx
    57c0:	48 83 ec 48          	sub    $0x48,%rsp
    57c4:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    57c9:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    57ce:	45 31 e4             	xor    %r12d,%r12d
    57d1:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    57d6:	45 39 e6             	cmp    %r12d,%r14d
    57d9:	0f 84 47 02 00 00    	je     5a26 <verify+0x286>
    57df:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    57e4:	8b 50 08             	mov    0x8(%rax),%edx
    57e7:	85 d2                	test   %edx,%edx
    57e9:	0f 8e 37 02 00 00    	jle    5a26 <verify+0x286>
    57ef:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    57f7:	31 ed                	xor    %ebp,%ebp
    57f9:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    57fe:	44 89 7c 24 34       	mov    %r15d,0x34(%rsp)
    5803:	45 89 f7             	mov    %r14d,%r15d
    5806:	41 89 ee             	mov    %ebp,%r14d
    5809:	44 89 fa             	mov    %r15d,%edx
    580c:	48 8d 35 01 0a 00 00 	lea    0xa01(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    5813:	bf 01 00 00 00       	mov    $0x1,%edi
    5818:	31 c0                	xor    %eax,%eax
    581a:	e8 11 cc ff ff       	call   2430 <__printf_chk@plt>
    581f:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5824:	8b 40 08             	mov    0x8(%rax),%eax
    5827:	85 c0                	test   %eax,%eax
    5829:	0f 8e cf 01 00 00    	jle    59fe <verify+0x25e>
    582f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5834:	44 89 74 24 38       	mov    %r14d,0x38(%rsp)
    5839:	31 db                	xor    %ebx,%ebx
    583b:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    5840:	4c 8b 20             	mov    (%rax),%r12
    5843:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5848:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    584d:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    5851:	4c 8b 3c 24          	mov    (%rsp),%r15
    5855:	48 8d 35 cd 09 00 00 	lea    0x9cd(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    585c:	49 89 c6             	mov    %rax,%r14
    585f:	bf 01 00 00 00       	mov    $0x1,%edi
    5864:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5868:	49 c1 e6 07          	shl    $0x7,%r14
    586c:	4b 8b 8c 3c 18 02 00 00 	mov    0x218(%r12,%r15,1),%rcx
    5874:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    5879:	4a 8b 94 30 18 02 00 00 	mov    0x218(%rax,%r14,1),%rdx
    5881:	31 c0                	xor    %eax,%eax
    5883:	e8 a8 cb ff ff       	call   2430 <__printf_chk@plt>
    5888:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    588d:	4c 8b 20             	mov    (%rax),%r12
    5890:	4b 83 bc 3c 18 02 00 00 00 	cmpq   $0x0,0x218(%r12,%r15,1)
    5899:	0f 8e 43 01 00 00    	jle    59e2 <verify+0x242>
    589f:	4c 03 75 00          	add    0x0(%rbp),%r14
    58a3:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    58a8:	ba 01 00 00 00       	mov    $0x1,%edx
    58ad:	4d 89 f5             	mov    %r14,%r13
    58b0:	4d 8b b5 18 02 00 00 	mov    0x218(%r13),%r14
    58b7:	4d 85 f6             	test   %r14,%r14
    58ba:	0f 8e 1d 01 00 00    	jle    59dd <verify+0x23d>
    58c0:	48 89 d5             	mov    %rdx,%rbp
    58c3:	48 8b 04 24          	mov    (%rsp),%rax
    58c7:	31 db                	xor    %ebx,%ebx
    58c9:	4d 89 f2             	mov    %r14,%r10
    58cc:	48 c1 e5 05          	shl    $0x5,%rbp
    58d0:	48 83 ed 20          	sub    $0x20,%rbp
    58d4:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    58d8:	49 89 ee             	mov    %rbp,%r14
    58db:	48 89 dd             	mov    %rbx,%rbp
    58de:	48 89 d3             	mov    %rdx,%rbx
    58e1:	eb 32                	jmp    5915 <verify+0x175>
    58e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    58e8:	4c 39 c2             	cmp    %r8,%rdx
    58eb:	0f 8d 57 01 00 00    	jge    5a48 <verify+0x2a8>
    58f1:	4c 39 df             	cmp    %r11,%rdi
    58f4:	7e 05                	jle    58fb <verify+0x15b>
    58f6:	49 39 c1             	cmp    %rax,%r9
    58f9:	7c 75                	jl     5970 <verify+0x1d0>
    58fb:	4c 39 df             	cmp    %r11,%rdi
    58fe:	0f 8d b3 01 00 00    	jge    5ab7 <verify+0x317>
    5904:	0f 1f 40 00          	nopl   0x0(%rax)
    5908:	48 83 c5 01          	add    $0x1,%rbp
    590c:	49 39 ea             	cmp    %rbp,%r10
    590f:	0f 8e a8 00 00 00    	jle    59bd <verify+0x21d>
    5915:	49 8b 97 08 02 00 00 	mov    0x208(%r15),%rdx
    591c:	48 89 e8             	mov    %rbp,%rax
    591f:	48 c1 e0 05          	shl    $0x5,%rax
    5923:	49 03 85 08 02 00 00 	add    0x208(%r13),%rax
    592a:	4c 01 f2             	add    %r14,%rdx
    592d:	48 8b 08             	mov    (%rax),%rcx
    5930:	48 8b 78 10          	mov    0x10(%rax),%rdi
    5934:	48 8b 32             	mov    (%rdx),%rsi
    5937:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    593b:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    593f:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    5943:	48 8b 50 08          	mov    0x8(%rax),%rdx
    5947:	48 8b 40 18          	mov    0x18(%rax),%rax
    594b:	48 39 f1             	cmp    %rsi,%rcx
    594e:	7c 98                	jl     58e8 <verify+0x148>
    5950:	0f 8e 4a 01 00 00    	jle    5aa0 <verify+0x300>
    5956:	4c 39 c2             	cmp    %r8,%rdx
    5959:	0f 8f f9 00 00 00    	jg     5a58 <verify+0x2b8>
    595f:	75 a7                	jne    5908 <verify+0x168>
    5961:	4c 39 df             	cmp    %r11,%rdi
    5964:	7f a2                	jg     5908 <verify+0x168>
    5966:	49 39 c1             	cmp    %rax,%r9
    5969:	7c 9d                	jl     5908 <verify+0x168>
    596b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5970:	49 89 c1             	mov    %rax,%r9
    5973:	48 89 f9             	mov    %rdi,%rcx
    5976:	48 89 f2             	mov    %rsi,%rdx
    5979:	bf 01 00 00 00       	mov    $0x1,%edi
    597e:	48 8d 35 1b 0b 00 00 	lea    0xb1b(%rip),%rsi        # 64a0 <_IO_stdin_used+0x4a0>
    5985:	31 c0                	xor    %eax,%eax
    5987:	48 83 c5 01          	add    $0x1,%rbp
    598b:	e8 a0 ca ff ff       	call   2430 <__printf_chk@plt>
    5990:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5995:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    599a:	4c 03 28             	add    (%rax),%r13
    599d:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    59a2:	4d 8b 95 18 02 00 00 	mov    0x218(%r13),%r10
    59a9:	4c 8b 20             	mov    (%rax),%r12
    59ac:	48 8b 04 24          	mov    (%rsp),%rax
    59b0:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    59b4:	49 39 ea             	cmp    %rbp,%r10
    59b7:	0f 8f 58 ff ff ff    	jg     5915 <verify+0x175>
    59bd:	48 89 da             	mov    %rbx,%rdx
    59c0:	49 3b 9f 18 02 00 00 	cmp    0x218(%r15),%rbx
    59c7:	7d 14                	jge    59dd <verify+0x23d>
    59c9:	4d 8b b5 18 02 00 00 	mov    0x218(%r13),%r14
    59d0:	48 83 c2 01          	add    $0x1,%rdx
    59d4:	4d 85 f6             	test   %r14,%r14
    59d7:	0f 8f e3 fe ff ff    	jg     58c0 <verify+0x120>
    59dd:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    59e2:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    59e7:	48 83 c3 01          	add    $0x1,%rbx
    59eb:	39 58 08             	cmp    %ebx,0x8(%rax)
    59ee:	0f 8f 54 fe ff ff    	jg     5848 <verify+0xa8>
    59f4:	44 8b 74 24 38       	mov    0x38(%rsp),%r14d
    59f9:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
    59fe:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5a03:	48 81 04 24 80 02 00 00 	addq   $0x280,(%rsp)
    5a0b:	41 83 c6 01          	add    $0x1,%r14d
    5a0f:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    5a13:	0f 8f f0 fd ff ff    	jg     5809 <verify+0x69>
    5a19:	45 89 fe             	mov    %r15d,%r14d
    5a1c:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    5a21:	44 8b 7c 24 34       	mov    0x34(%rsp),%r15d
    5a26:	48 81 44 24 08 98 00 00 00 	addq   $0x98,0x8(%rsp)
    5a2f:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    5a34:	41 39 c7             	cmp    %eax,%r15d
    5a37:	0f 84 88 00 00 00    	je     5ac5 <verify+0x325>
    5a3d:	41 89 c4             	mov    %eax,%r12d
    5a40:	e9 91 fd ff ff       	jmp    57d6 <verify+0x36>
    5a45:	0f 1f 00             	nopl   (%rax)
    5a48:	0f 85 ba fe ff ff    	jne    5908 <verify+0x168>
    5a4e:	e9 a8 fe ff ff       	jmp    58fb <verify+0x15b>
    5a53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5a58:	49 39 c1             	cmp    %rax,%r9
    5a5b:	7e 09                	jle    5a66 <verify+0x2c6>
    5a5d:	4c 39 df             	cmp    %r11,%rdi
    5a60:	0f 8c 0a ff ff ff    	jl     5970 <verify+0x1d0>
    5a66:	4c 39 df             	cmp    %r11,%rdi
    5a69:	0f 8f 99 fe ff ff    	jg     5908 <verify+0x168>
    5a6f:	49 39 c1             	cmp    %rax,%r9
    5a72:	0f 8d f8 fe ff ff    	jge    5970 <verify+0x1d0>
    5a78:	48 39 f1             	cmp    %rsi,%rcx
    5a7b:	0f 85 87 fe ff ff    	jne    5908 <verify+0x168>
    5a81:	4c 39 c2             	cmp    %r8,%rdx
    5a84:	0f 85 7e fe ff ff    	jne    5908 <verify+0x168>
    5a8a:	4c 39 df             	cmp    %r11,%rdi
    5a8d:	0f 84 dd fe ff ff    	je     5970 <verify+0x1d0>
    5a93:	e9 70 fe ff ff       	jmp    5908 <verify+0x168>
    5a98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5aa0:	4c 39 c2             	cmp    %r8,%rdx
    5aa3:	0f 8c 52 fe ff ff    	jl     58fb <verify+0x15b>
    5aa9:	4c 39 df             	cmp    %r11,%rdi
    5aac:	7e c1                	jle    5a6f <verify+0x2cf>
    5aae:	4c 39 c2             	cmp    %r8,%rdx
    5ab1:	0f 85 51 fe ff ff    	jne    5908 <verify+0x168>
    5ab7:	49 39 c1             	cmp    %rax,%r9
    5aba:	0f 8f 48 fe ff ff    	jg     5908 <verify+0x168>
    5ac0:	e9 ab fe ff ff       	jmp    5970 <verify+0x1d0>
    5ac5:	48 81 44 24 10 98 00 00 00 	addq   $0x98,0x10(%rsp)
    5ace:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    5ad3:	41 8d 46 01          	lea    0x1(%r14),%eax
    5ad7:	45 39 e6             	cmp    %r12d,%r14d
    5ada:	74 08                	je     5ae4 <verify+0x344>
    5adc:	41 89 c6             	mov    %eax,%r14d
    5adf:	e9 e5 fc ff ff       	jmp    57c9 <verify+0x29>
    5ae4:	48 83 c4 48          	add    $0x48,%rsp
    5ae8:	31 c0                	xor    %eax,%eax
    5aea:	5b                   	pop    %rbx
    5aeb:	5d                   	pop    %rbp
    5aec:	41 5c                	pop    %r12
    5aee:	41 5d                	pop    %r13
    5af0:	41 5e                	pop    %r14
    5af2:	41 5f                	pop    %r15
    5af4:	c3                   	ret
    5af5:	31 c0                	xor    %eax,%eax
    5af7:	c3                   	ret

Disassembly of section .fini:

0000000000005af8 <_fini>:
    5af8:	f3 0f 1e fa          	endbr64
    5afc:	48 83 ec 08          	sub    $0x8,%rsp
    5b00:	48 83 c4 08          	add    $0x8,%rsp
    5b04:	c3                   	ret
