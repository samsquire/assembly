
barrier-runtime-1to1:     file format elf64-x86-64


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
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    2520:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

static inline void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
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
  if (a < b) { return a; }
  if (b < a) { return b; }
  return a;
}

int main() {
    2560:	f3 0f 1e fa          	endbr64
    2564:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2566:	48 8d 3d 7b 3f 00 00 	lea    0x3f7b(%rip),%rdi        # 64e8 <_IO_stdin_used+0x4e8>
    256d:	41 56                	push   %r14
    256f:	41 55                	push   %r13
    2571:	41 54                	push   %r12
    2573:	55                   	push   %rbp
    2574:	53                   	push   %rbx
    2575:	48 83 ec 58          	sub    $0x58,%rsp
    2579:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2582:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
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
    261c:	ba 0f 27 00 00       	mov    $0x270f,%edx
    2621:	48 8d 35 20 3f 00 00 	lea    0x3f20(%rip),%rsi        # 6548 <_IO_stdin_used+0x548>
    2628:	31 c0                	xor    %eax,%eax
    262a:	bf 01 00 00 00       	mov    $0x1,%edi
    262f:	e8 fc fd ff ff       	call   2430 <__printf_chk@plt>
    2634:	ba 0f 27 00 00       	mov    $0x270f,%edx
    2639:	48 8d 35 38 3f 00 00 	lea    0x3f38(%rip),%rsi        # 6578 <_IO_stdin_used+0x578>
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
  printf("intrathread message buffer size = %ld\n", messages_limit);
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  struct ProtectedState *protected_state = calloc(1, sizeof(struct ProtectedState));
    2688:	be 18 00 00 00       	mov    $0x18,%esi
    268d:	bf 01 00 00 00       	mov    $0x1,%edi
    2692:	e8 e9 fc ff ff       	call   2380 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2697:	be 98 00 00 00       	mov    $0x98,%esi
    269c:	bf 09 00 00 00       	mov    $0x9,%edi
  struct ProtectedState *protected_state = calloc(1, sizeof(struct ProtectedState));
    26a1:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    26a6:	e8 d5 fc ff ff       	call   2380 <calloc@plt>
  int barrier_count = cluster_size;
  int total_barrier_count = cluster_size + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    26ab:	be 10 00 00 00       	mov    $0x10,%esi
    26b0:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    26b5:	48 89 04 24          	mov    %rax,(%rsp)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    26b9:	e8 c2 fc ff ff       	call   2380 <calloc@plt>
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    26be:	be 10 00 00 00       	mov    $0x10,%esi
    26c3:	bf 0f 27 00 00       	mov    $0x270f,%edi
    buffers[x].count = buffer_size;
    26c8:	c7 00 0f 27 00 00    	movl   $0x270f,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    26ce:	48 89 c3             	mov    %rax,%rbx
    26d1:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    26d6:	e8 a5 fc ff ff       	call   2380 <calloc@plt>
    26db:	4c 8b 04 24          	mov    (%rsp),%r8
    26df:	48 89 43 08          	mov    %rax,0x8(%rbx)
    for (int y = 0 ; y < buffer_size; y++) {
    26e3:	48 8d 90 f0 70 02 00 	lea    0x270f0(%rax),%rdx
    26ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      buffers[x].buffer[y].available = 0;
    26f0:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    for (int y = 0 ; y < buffer_size; y++) {
    26f7:	48 83 c0 10          	add    $0x10,%rax
    26fb:	48 39 d0             	cmp    %rdx,%rax
    26fe:	75 f0                	jne    26f0 <main+0x190>
    2700:	4c 89 04 24          	mov    %r8,(%rsp)
    2704:	4d 89 c6             	mov    %r8,%r14
    }
  }
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int current_thread = 0;
  for (int x = 0 ; x < thread_count; x++) {
    2707:	31 db                	xor    %ebx,%ebx
    2709:	4c 8d 2d 90 3e 00 00 	lea    0x3e90(%rip),%r13        # 65a0 <_IO_stdin_used+0x5a0>
    2710:	48 8d 2d d8 3b 00 00 	lea    0x3bd8(%rip),%rbp        # 62ef <_IO_stdin_used+0x2ef>
    2717:	4c 8d 25 ed 3b 00 00 	lea    0x3bed(%rip),%r12        # 630b <_IO_stdin_used+0x30b>
    271e:	89 da                	mov    %ebx,%edx
    2720:	4c 89 ee             	mov    %r13,%rsi
    2723:	bf 01 00 00 00       	mov    $0x1,%edi
    2728:	31 c0                	xor    %eax,%eax
    272a:	e8 01 fd ff ff       	call   2430 <__printf_chk@plt>
    int cluster_start = x;
    printf("Creating cluster starting from %d\n", cluster_start);
    for (int cluster_index = 0 ; cluster_index < cluster_size && x < thread_count; cluster_index++) {
    272f:	45 31 ff             	xor    %r15d,%r15d
      thread_data[x].threads = &thread_data[cluster_start];
      thread_data[x].thread_count = cluster_size;
      thread_data[x].thread_index = cluster_index;
    2732:	45 89 3e             	mov    %r15d,(%r14)
    2735:	89 d9                	mov    %ebx,%ecx
    2737:	89 da                	mov    %ebx,%edx
    2739:	48 89 ee             	mov    %rbp,%rsi
      thread_data[x].threads = &thread_data[cluster_start];
    273c:	4d 89 76 10          	mov    %r14,0x10(%r14)
    2740:	bf 01 00 00 00       	mov    $0x1,%edi
    2745:	31 c0                	xor    %eax,%eax
    for (int cluster_index = 0 ; cluster_index < cluster_size && x < thread_count; cluster_index++) {
    2747:	41 83 c7 01          	add    $0x1,%r15d
      thread_data[x].thread_count = cluster_size;
    274b:	41 c7 46 18 03 00 00 00 	movl   $0x3,0x18(%r14)
    2753:	e8 d8 fc ff ff       	call   2430 <__printf_chk@plt>
    for (int cluster_index = 0 ; cluster_index < cluster_size && x < thread_count; cluster_index++) {
    2758:	41 83 ff 03          	cmp    $0x3,%r15d
    275c:	75 d4                	jne    2732 <main+0x1d2>
      printf("thread %d is in cluster %d\n", x, cluster_start);
    }
    x += cluster_size;
    275e:	8d 53 03             	lea    0x3(%rbx),%edx
    2761:	4c 89 e6             	mov    %r12,%rsi
    2764:	bf 01 00 00 00       	mov    $0x1,%edi
    2769:	31 c0                	xor    %eax,%eax
    276b:	e8 c0 fc ff ff       	call   2430 <__printf_chk@plt>
  for (int x = 0 ; x < thread_count; x++) {
    2770:	49 81 c6 60 02 00 00 	add    $0x260,%r14
    2777:	83 fb 04             	cmp    $0x4,%ebx
    277a:	74 07                	je     2783 <main+0x223>
    277c:	bb 04 00 00 00       	mov    $0x4,%ebx
    2781:	eb 9b                	jmp    271e <main+0x1be>
    2783:	4c 8b 04 24          	mov    (%rsp),%r8
  int external_thread_index = 0;
    2787:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    278f:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    printf("to %d\n", x);

  }

  for (int x = 0 ; x < total_threads ; x++) {
    2798:	c7 04 24 00 00 00 00 	movl   $0x0,(%rsp)
    279f:	4d 89 c7             	mov    %r8,%r15
          thread_data[x].tasks[y].run = barriered_work; 
        } else {
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    27a2:	4c 89 44 24 38       	mov    %r8,0x38(%rsp)
    27a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    if (x < thread_count) {
    27b0:	83 3c 24 05          	cmpl   $0x5,(%rsp)
    27b4:	7e 11                	jle    27c7 <main+0x267>
      thread_data[x].threads = thread_data;
    27b6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
      thread_data[x].thread_count = thread_count;
    27bb:	41 c7 47 18 06 00 00 00 	movl   $0x6,0x18(%r15)
      thread_data[x].threads = thread_data;
    27c3:	49 89 47 10          	mov    %rax,0x10(%r15)
    thread_data[x].protected_state = protected_state;
    27c7:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    thread_data[x].total_thread_count = total_threads;
    27cc:	41 c7 47 1c 09 00 00 00 	movl   $0x9,0x1c(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    27d4:	be 10 00 00 00       	mov    $0x10,%esi
      for (int y = 0 ; y < total_barrier_count ; y++) {
    27d9:	31 db                	xor    %ebx,%ebx
    thread_data[x].task_count = total_barrier_count;
    27db:	41 c7 47 28 04 00 00 00 	movl   $0x4,0x28(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    27e3:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].protected_state = protected_state;
    27e8:	49 89 47 30          	mov    %rax,0x30(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    27ec:	e8 8f fb ff ff       	call   2380 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27f1:	be 10 00 00 00       	mov    $0x10,%esi
    27f6:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    27fb:	49 89 47 50          	mov    %rax,0x50(%r15)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27ff:	e8 7c fb ff ff       	call   2380 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2804:	be 28 00 00 00       	mov    $0x28,%esi
    2809:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    280e:	66 0f 6f 05 fa 41 00 00 	movdqa 0x41fa(%rip),%xmm0        # 6a10 <_IO_stdin_used+0xa10>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2816:	49 89 47 58          	mov    %rax,0x58(%r15)
    thread_data[x].timestamp_count = 0;
    281a:	41 0f 11 47 68       	movups %xmm0,0x68(%r15)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    281f:	e8 5c fb ff ff       	call   2380 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2824:	be 98 00 00 00       	mov    $0x98,%esi
    2829:	bf 04 00 00 00       	mov    $0x4,%edi
    thread_data[x].task_timestamp_count = 0;
    282e:	66 0f 6f 0d da 41 00 00 	movdqa 0x41da(%rip),%xmm1        # 6a10 <_IO_stdin_used+0xa10>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2836:	49 89 47 78          	mov    %rax,0x78(%r15)
    thread_data[x].task_timestamp_count = 0;
    283a:	41 0f 11 8f 80 00 00 00 	movups %xmm1,0x80(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2842:	e8 39 fb ff ff       	call   2380 <calloc@plt>
      thread_data[x].tasks = barriers;
    2847:	49 89 47 20          	mov    %rax,0x20(%r15)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    284b:	49 89 c6             	mov    %rax,%r14
            thread_data[x].tasks[y].protected = do_protected_write; 
    284e:	4c 63 eb             	movslq %ebx,%r13
    2851:	4b 8d 44 ed 00       	lea    0x0(%r13,%r13,8),%rax
    2856:	4d 8d 64 45 00       	lea    0x0(%r13,%rax,2),%r12
    285b:	49 c1 e4 03          	shl    $0x3,%r12
    285f:	4b 8d 2c 26          	lea    (%r14,%r12,1),%rbp
        if (x == y) {
    2863:	39 1c 24             	cmp    %ebx,(%rsp)
    2866:	0f 84 e4 09 00 00    	je     3250 <main+0xcf0>
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    286c:	be 20 00 00 00       	mov    $0x20,%esi
    2871:	bf 06 00 00 00       	mov    $0x6,%edi
    2876:	e8 05 fb ff ff       	call   2380 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    287b:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    287f:	4c 89 64 24 10       	mov    %r12,0x10(%rsp)
    2884:	49 89 c6             	mov    %rax,%r14
    2887:	48 89 45 70          	mov    %rax,0x70(%rbp)
        for (int b = 0 ; b < thread_count ; b++) {
    288b:	48 8d a8 c0 00 00 00 	lea    0xc0(%rax),%rbp
    2892:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2898:	be 08 00 00 00       	mov    $0x8,%esi
    289d:	bf 0f 27 00 00       	mov    $0x270f,%edi
        for (int b = 0 ; b < thread_count ; b++) {
    28a2:	49 83 c6 20          	add    $0x20,%r14
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    28a6:	e8 d5 fa ff ff       	call   2380 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    28ab:	be 08 00 00 00       	mov    $0x8,%esi
    28b0:	bf 0f 27 00 00       	mov    $0x270f,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    28b5:	49 89 c4             	mov    %rax,%r12
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    28b8:	e8 c3 fa ff ff       	call   2380 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    28bd:	be 18 00 00 00       	mov    $0x18,%esi
    28c2:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    28c7:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    28ca:	e8 b1 fa ff ff       	call   2380 <calloc@plt>
          mailboxes[b].higher = &data[1];
    28cf:	48 8d 70 18          	lea    0x18(%rax),%rsi
          data[0].messages_count = 0;
    28d3:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
          mailboxes[b].lower = &data[0];
    28db:	49 89 46 e0          	mov    %rax,-0x20(%r14)
          mailboxes[b].higher = &data[1];
    28df:	49 89 76 e8          	mov    %rsi,-0x18(%r14)
          data[0].messages = messages;
    28e3:	4c 89 20             	mov    %r12,(%rax)
          data[1].messages = messages2;
    28e6:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_limit = messages_limit;
    28ea:	48 c7 40 10 0f 27 00 00 	movq   $0x270f,0x10(%rax)
          data[1].messages_count = 0;
    28f2:	48 c7 40 20 00 00 00 00 	movq   $0x0,0x20(%rax)
          data[1].messages_limit = messages_limit;
    28fa:	48 c7 40 28 0f 27 00 00 	movq   $0x270f,0x28(%rax)
        for (int b = 0 ; b < thread_count ; b++) {
    2902:	4c 39 f5             	cmp    %r14,%rbp
    2905:	75 91                	jne    2898 <main+0x338>
        char *message = malloc(sizeof(char) * 256);
    2907:	be 01 00 00 00       	mov    $0x1,%esi
    290c:	bf 00 01 00 00       	mov    $0x100,%edi
    2911:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2915:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
    291a:	e8 61 fa ff ff       	call   2380 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    291f:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2924:	48 89 c5             	mov    %rax,%rbp
        struct Message *messaged = malloc(sizeof(struct Message));
    2927:	e8 c4 fa ff ff       	call   23f0 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    292c:	44 8b 04 24          	mov    (%rsp),%r8d
    2930:	48 89 ef             	mov    %rbp,%rdi
    2933:	41 89 d9             	mov    %ebx,%r9d
    2936:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    293b:	48 8d 0d 86 3c 00 00 	lea    0x3c86(%rip),%rcx        # 65c8 <_IO_stdin_used+0x5c8>
    2942:	ba 00 01 00 00       	mov    $0x100,%edx
    2947:	31 c0                	xor    %eax,%eax
    2949:	be 01 00 00 00       	mov    $0x1,%esi
    294e:	e8 ad fb ff ff       	call   2500 <__sprintf_chk@plt>
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2953:	4d 8b 77 20          	mov    0x20(%r15),%r14
        messaged->message = message;
    2957:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    295c:	be 20 00 00 00       	mov    $0x20,%esi
        messaged->thread_index = x;
    2961:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
        messaged->message = message;
    2966:	49 89 2a             	mov    %rbp,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2969:	8d 6b 01             	lea    0x1(%rbx),%ebp
        messaged->task_index = y;
    296c:	4d 89 6a 10          	mov    %r13,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2970:	4f 8d 2c 26          	lea    (%r14,%r12,1),%r13
        messaged->thread_index = x;
    2974:	49 89 42 08          	mov    %rax,0x8(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2978:	41 89 ad 90 00 00 00 	mov    %ebp,0x90(%r13)
        thread_data[x].tasks[y].message = messaged;
    297f:	4d 89 95 88 00 00 00 	mov    %r10,0x88(%r13)
        thread_data[x].tasks[y].sending = 1;
    2986:	41 c7 85 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r13)
        thread_data[x].tasks[y].snapshot_count = 999999;
    2991:	49 c7 45 58 3f 42 0f 00 	movq   $0xf423f,0x58(%r13)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2999:	49 8b 7d 58          	mov    0x58(%r13),%rdi
    299d:	e8 de f9 ff ff       	call   2380 <calloc@plt>
    29a2:	49 89 45 50          	mov    %rax,0x50(%r13)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    29a6:	41 8b 07             	mov    (%r15),%eax
        thread_data[x].tasks[y].current_snapshot = 0;
    29a9:	49 c7 45 60 00 00 00 00 	movq   $0x0,0x60(%r13)
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
    29b1:	41 89 45 38          	mov    %eax,0x38(%r13)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    29b5:	4d 89 7d 30          	mov    %r15,0x30(%r13)
        thread_data[x].tasks[y].available = 1;
    29b9:	41 c7 45 40 01 00 00 00 	movl   $0x1,0x40(%r13)
        thread_data[x].tasks[y].arrived = 0;
    29c1:	41 c7 45 08 00 00 00 00 	movl   $0x0,0x8(%r13)
        thread_data[x].tasks[y].thread_count = thread_count;
    29c9:	41 c7 45 3c 06 00 00 00 	movl   $0x6,0x3c(%r13)
        thread_data[x].tasks[y].task_count = total_barrier_count;
    29d1:	41 c7 45 44 04 00 00 00 	movl   $0x4,0x44(%r13)
        thread_data[x].tasks[y].worker_count = thread_count;
    29d9:	41 c7 85 84 00 00 00 06 00 00 00 	movl   $0x6,0x84(%r13)
        thread_data[x].tasks[y].task_index = y;
    29e4:	41 89 5d 00          	mov    %ebx,0x0(%r13)
        if (y == barrier_count - 1) {
    29e8:	83 fb 02             	cmp    $0x2,%ebx
    29eb:	0f 84 6f 08 00 00    	je     3260 <main+0xd00>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    29f1:	8b 14 24             	mov    (%rsp),%edx
    29f4:	39 da                	cmp    %ebx,%edx
    29f6:	0f 85 3c 08 00 00    	jne    3238 <main+0xcd8>
    29fc:	8b 4c 24 20          	mov    0x20(%rsp),%ecx
    2a00:	85 c9                	test   %ecx,%ecx
    2a02:	0f 85 30 08 00 00    	jne    3238 <main+0xcd8>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2a08:	48 8d 35 e1 3b 00 00 	lea    0x3be1(%rip),%rsi        # 65f0 <_IO_stdin_used+0x5f0>
    2a0f:	bf 01 00 00 00       	mov    $0x1,%edi
    2a14:	31 c0                	xor    %eax,%eax
    2a16:	e8 15 fa ff ff       	call   2430 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a1b:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a20:	4d 8b 77 20          	mov    0x20(%r15),%r14
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a24:	c7 44 24 20 01 00 00 00 	movl   $0x1,0x20(%rsp)
    2a2c:	49 89 47 38          	mov    %rax,0x38(%r15)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a30:	4d 01 f4             	add    %r14,%r12
    2a33:	48 8d 05 a6 2a 00 00 	lea    0x2aa6(%rip),%rax        # 54e0 <barriered_work_ingest>
    2a3a:	49 89 44 24 20       	mov    %rax,0x20(%r12)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2a3f:	83 fd 04             	cmp    $0x4,%ebp
    2a42:	74 0c                	je     2a50 <main+0x4f0>
  int external_thread_index = 0;
    2a44:	89 eb                	mov    %ebp,%ebx
    2a46:	e9 03 fe ff ff       	jmp    284e <main+0x2ee>
    2a4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            thread_data[x].tasks[y].run = barriered_work; 

          }
        }
      }
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2a50:	48 8d 05 59 09 00 00 	lea    0x959(%rip),%rax        # 33b0 <barriered_reset>
  for (int x = 0 ; x < total_threads ; x++) {
    2a57:	83 04 24 01          	addl   $0x1,(%rsp)
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2a5b:	49 89 86 e8 01 00 00 	mov    %rax,0x1e8(%r14)
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2a62:	4d 89 be f8 01 00 00 	mov    %r15,0x1f8(%r14)
  for (int x = 0 ; x < total_threads ; x++) {
    2a69:	49 81 c7 98 00 00 00 	add    $0x98,%r15
      thread_data[x].tasks[barrier_count].available = 1; 
    2a70:	41 c7 86 08 02 00 00 01 00 00 00 	movl   $0x1,0x208(%r14)
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2a7b:	41 c7 86 d0 01 00 00 00 00 00 00 	movl   $0x0,0x1d0(%r14)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2a86:	41 c7 86 c8 01 00 00 03 00 00 00 	movl   $0x3,0x1c8(%r14)
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
    2a91:	41 c7 86 04 02 00 00 06 00 00 00 	movl   $0x6,0x204(%r14)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2a9c:	41 8b 87 68 ff ff ff 	mov    -0x98(%r15),%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2aa3:	48 83 44 24 18 01    	addq   $0x1,0x18(%rsp)
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    2aa9:	41 89 86 00 02 00 00 	mov    %eax,0x200(%r14)
  for (int x = 0 ; x < total_threads ; x++) {
    2ab0:	8b 04 24             	mov    (%rsp),%eax
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2ab3:	41 c7 86 4c 02 00 00 06 00 00 00 	movl   $0x6,0x24c(%r14)
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    2abe:	41 c7 86 0c 02 00 00 04 00 00 00 	movl   $0x4,0x20c(%r14)
  for (int x = 0 ; x < total_threads ; x++) {
    2ac9:	83 f8 09             	cmp    $0x9,%eax
    2acc:	0f 85 de fc ff ff    	jne    27b0 <main+0x250>

      current_thread += cluster_size;
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].threads = thread_data;
    2ad2:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ad7:	be 38 00 00 00       	mov    $0x38,%esi
    2adc:	bf 09 00 00 00       	mov    $0x9,%edi
  thread_data[thread_count].thread_count = thread_count;
  thread_data[thread_count].thread_index = 0;

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
  for (int x = 0 ; x < thread_count ; x++) {
    2ae1:	45 31 ff             	xor    %r15d,%r15d
    2ae4:	4c 8d 35 25 3b 00 00 	lea    0x3b25(%rip),%r14        # 6610 <_IO_stdin_used+0x610>
    thread_data[x].threads = thread_data;
    2aeb:	49 8d 80 28 04 00 00 	lea    0x428(%r8),%rax
    thread_data[n].tasks[0].scheduled = 1;
    2af2:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    thread_data[x].threads = thread_data;
    2af7:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    2afc:	49 8b 40 20          	mov    0x20(%r8),%rax
    thread_data[x].threads = thread_data;
    2b00:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    thread_data[x].thread_count = thread_count;
    2b07:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    thread_data[x].thread_index = x;
    2b12:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    thread_data[x].task_count = total_barrier_count;
    2b1d:	41 c7 80 50 04 00 00 04 00 00 00 	movl   $0x4,0x450(%r8)
    thread_data[n].tasks[0].scheduled = 1;
    2b28:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2b2f:	49 8b 80 b8 00 00 00 	mov    0xb8(%r8),%rax
    2b36:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2b3d:	49 8b 80 50 01 00 00 	mov    0x150(%r8),%rax
    2b44:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2b4b:	49 8b 80 e8 01 00 00 	mov    0x1e8(%r8),%rax
    2b52:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2b59:	49 8b 80 80 02 00 00 	mov    0x280(%r8),%rax
    2b60:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2b67:	49 8b 80 18 03 00 00 	mov    0x318(%r8),%rax
    2b6e:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b75:	e8 06 f8 ff ff       	call   2380 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b7a:	be 38 00 00 00       	mov    $0x38,%esi
    2b7f:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b84:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b87:	e8 f4 f7 ff ff       	call   2380 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b8c:	be 38 00 00 00       	mov    $0x38,%esi
    2b91:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b96:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b9a:	e8 e1 f7 ff ff       	call   2380 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2b9f:	be 08 00 00 00       	mov    $0x8,%esi
    2ba4:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ba9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bae:	e8 cd f7 ff ff       	call   2380 <calloc@plt>
  thread_data[thread_count].type = TIMER;
    2bb3:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2bb8:	ba 06 00 00 00       	mov    $0x6,%edx
    2bbd:	48 8d 35 4e 37 00 00 	lea    0x374e(%rip),%rsi        # 6312 <_IO_stdin_used+0x312>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bc4:	49 89 c4             	mov    %rax,%r12
    2bc7:	bf 01 00 00 00       	mov    $0x1,%edi
    2bcc:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].type = TIMER;
    2bce:	41 c7 80 94 03 00 00 00 00 00 00 	movl   $0x0,0x394(%r8)
  thread_data[thread_count].running = 1;
    2bd9:	4c 89 e5             	mov    %r12,%rbp
    2bdc:	41 c7 80 bc 03 00 00 01 00 00 00 	movl   $0x1,0x3bc(%r8)
  thread_data[thread_count].task_count = total_barrier_count;
    2be7:	41 c7 80 b8 03 00 00 04 00 00 00 	movl   $0x4,0x3b8(%r8)
  thread_data[thread_count].threads = thread_data;
    2bf2:	4d 89 80 a0 03 00 00 	mov    %r8,0x3a0(%r8)
  thread_data[thread_count].thread_count = thread_count;
    2bf9:	41 c7 80 a8 03 00 00 06 00 00 00 	movl   $0x6,0x3a8(%r8)
  thread_data[thread_count].thread_index = 0;
    2c04:	41 c7 80 90 03 00 00 00 00 00 00 	movl   $0x0,0x390(%r8)
    2c0f:	e8 1c f8 ff ff       	call   2430 <__printf_chk@plt>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2c14:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2c19:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
    2c1e:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2c25:	48 8d 15 34 0b 00 00 	lea    0xb34(%rip),%rdx        # 3760 <timer_thread>
    2c2c:	49 8d 88 90 03 00 00 	lea    0x390(%r8),%rcx
    2c33:	e8 18 f8 ff ff       	call   2450 <pthread_create@plt>
    2c38:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2c3d:	4c 89 64 24 18       	mov    %r12,0x18(%rsp)
    2c42:	45 89 fc             	mov    %r15d,%r12d
    2c45:	4d 89 c5             	mov    %r8,%r13
    2c48:	4d 89 c7             	mov    %r8,%r15
    2c4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    thread_data[x].type = WORKER;
    2c50:	41 c7 45 04 01 00 00 00 	movl   $0x1,0x4(%r13)
    2c58:	44 89 e2             	mov    %r12d,%edx
    2c5b:	4c 89 f6             	mov    %r14,%rsi
    2c5e:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2c60:	41 c7 45 2c 01 00 00 00 	movl   $0x1,0x2c(%r13)
    2c68:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < thread_count ; x++) {
    2c6d:	41 83 c4 01          	add    $0x1,%r12d
    2c71:	e8 ba f7 ff ff       	call   2430 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2c76:	4c 89 e9             	mov    %r13,%rcx
    2c79:	48 89 de             	mov    %rbx,%rsi
    2c7c:	48 89 ef             	mov    %rbp,%rdi
    2c7f:	48 8d 15 9a 07 00 00 	lea    0x79a(%rip),%rdx        # 3420 <barriered_thread>
  for (int x = 0 ; x < thread_count ; x++) {
    2c86:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    2c8d:	48 83 c5 08          	add    $0x8,%rbp
    2c91:	48 83 c3 38          	add    $0x38,%rbx
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2c95:	e8 b6 f7 ff ff       	call   2450 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2c9a:	41 83 fc 06          	cmp    $0x6,%r12d
    2c9e:	75 b0                	jne    2c50 <main+0x6f0>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ca0:	be d8 00 00 00       	mov    $0xd8,%esi
    2ca5:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    2caa:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    2caf:	41 c7 87 2c 04 00 00 02 00 00 00 	movl   $0x2,0x42c(%r15)
    thread_data[x].task_count = 0;
    2cba:	4c 89 7c 24 18       	mov    %r15,0x18(%rsp)
    2cbf:	31 db                	xor    %ebx,%ebx
    2cc1:	4c 8d 6c 24 40       	lea    0x40(%rsp),%r13
    2cc6:	48 8d 2d b5 36 00 00 	lea    0x36b5(%rip),%rbp        # 6382 <_IO_stdin_used+0x382>
    thread_data[x].running = 1;
    2ccd:	41 c7 87 54 04 00 00 01 00 00 00 	movl   $0x1,0x454(%r15)
    thread_data[x].task_count = 0;
    2cd8:	41 c7 87 50 04 00 00 00 00 00 00 	movl   $0x0,0x450(%r15)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ce3:	e8 98 f6 ff ff       	call   2380 <calloc@plt>
    2ce8:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2ced:	be 00 08 00 00       	mov    $0x800,%esi
    2cf2:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2cf4:	49 89 80 68 04 00 00 	mov    %rax,0x468(%r8)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2cfb:	e8 90 f7 ff ff       	call   2490 <eventfd@plt>
    2d00:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2d05:	ba 07 00 00 00       	mov    $0x7,%edx
    2d0a:	48 8d 35 1f 36 00 00 	lea    0x361f(%rip),%rsi        # 6330 <_IO_stdin_used+0x330>
    2d11:	bf 01 00 00 00       	mov    $0x1,%edi
    2d16:	41 89 80 70 04 00 00 	mov    %eax,0x470(%r8)
    2d1d:	31 c0                	xor    %eax,%eax
    thread_data[x].threads = thread_data;
    2d1f:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    thread_data[x].thread_count = thread_count;
    2d26:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    thread_data[x].thread_index = x;
    2d31:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    2d3c:	e8 ef f6 ff ff       	call   2430 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2d41:	48 8b 34 24          	mov    (%rsp),%rsi
    2d45:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2d4a:	49 8d 7c 24 38       	lea    0x38(%r12),%rdi
    2d4f:	48 8d 15 ca 1c 00 00 	lea    0x1cca(%rip),%rdx        # 4a20 <io_thread>
    2d56:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2d5d:	e8 ee f6 ff ff       	call   2450 <pthread_create@plt>
    2d62:	ba 08 00 00 00       	mov    $0x8,%edx
    2d67:	48 8d 35 d9 35 00 00 	lea    0x35d9(%rip),%rsi        # 6347 <_IO_stdin_used+0x347>
    2d6e:	31 c0                	xor    %eax,%eax
    2d70:	bf 01 00 00 00       	mov    $0x1,%edi
    2d75:	e8 b6 f6 ff ff       	call   2430 <__printf_chk@plt>
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    2d7a:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];
    2d7f:	48 8b 44 24 28       	mov    0x28(%rsp),%rax

    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2d84:	49 8d 7c 24 40       	lea    0x40(%r12),%rdi
    2d89:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2d8e:	48 8d 15 0b 09 00 00 	lea    0x90b(%rip),%rdx        # 36a0 <external_thread>
    thread_data[x].buffers = &buffers[buffer_index];
    2d95:	49 89 80 f8 04 00 00 	mov    %rax,0x4f8(%r8)
    thread_data[x].thread_count = thread_count;
    2d9c:	48 8b 05 85 3c 00 00 	mov    0x3c85(%rip),%rax        # 6a28 <_IO_stdin_used+0xa28>
    thread_data[x].type = EXTERNAL;
    2da3:	49 8d 88 c0 04 00 00 	lea    0x4c0(%r8),%rcx
    thread_data[x].threads = thread_data;
    2daa:	4d 89 80 d0 04 00 00 	mov    %r8,0x4d0(%r8)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2db1:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    thread_data[x].type = EXTERNAL;
    2db8:	41 c7 80 c4 04 00 00 03 00 00 00 	movl   $0x3,0x4c4(%r8)
    thread_data[x].running = 1;
    2dc3:	41 c7 80 ec 04 00 00 01 00 00 00 	movl   $0x1,0x4ec(%r8)
    thread_data[x].task_count = 0;
    2dce:	41 c7 80 e8 04 00 00 00 00 00 00 	movl   $0x0,0x4e8(%r8)
    thread_data[x].thread_count = thread_count;
    2dd9:	49 89 80 d8 04 00 00 	mov    %rax,0x4d8(%r8)
    thread_data[x].thread_index = x;
    2de0:	41 c7 80 c0 04 00 00 08 00 00 00 	movl   $0x8,0x4c0(%r8)
    thread_data[x].type = EXTERNAL;
    2deb:	4c 89 04 24          	mov    %r8,(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2def:	e8 5c f6 ff ff       	call   2450 <pthread_create@plt>
    2df4:	48 8d 3d 69 35 00 00 	lea    0x3569(%rip),%rdi        # 6364 <_IO_stdin_used+0x364>
    2dfb:	e8 d0 f4 ff ff       	call   22d0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    2e00:	4c 8b 34 24          	mov    (%rsp),%r14
    2e04:	0f 1f 40 00          	nopl   0x0(%rax)
    void * result; 
    pthread_join(thread[x], &result);
    2e08:	49 8b 3c dc          	mov    (%r12,%rbx,8),%rdi
    2e0c:	4c 89 ee             	mov    %r13,%rsi
    2e0f:	e8 bc f6 ff ff       	call   24d0 <pthread_join@plt>
    2e14:	89 da                	mov    %ebx,%edx
    2e16:	48 89 ee             	mov    %rbp,%rsi
    2e19:	bf 01 00 00 00       	mov    $0x1,%edi
    2e1e:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2e20:	48 83 c3 01          	add    $0x1,%rbx
    2e24:	e8 07 f6 ff ff       	call   2430 <__printf_chk@plt>
    2e29:	48 83 fb 09          	cmp    $0x9,%rbx
    2e2d:	75 d9                	jne    2e08 <main+0x8a8>
    2e2f:	49 8d 86 b0 03 00 00 	lea    0x3b0(%r14),%rax
  }
  long total = 0;
  long v = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
    2e36:	31 ed                	xor    %ebp,%ebp
  long sends = 0;
    2e38:	31 c9                	xor    %ecx,%ecx
  long ingests = 0;
    2e3a:	45 31 db             	xor    %r11d,%r11d
  long v = 0;
    2e3d:	45 31 c9             	xor    %r9d,%r9d
    2e40:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  long total = 0;
    2e45:	45 31 e4             	xor    %r12d,%r12d
    2e48:	4d 8d 6e 20          	lea    0x20(%r14),%r13
    2e4c:	4c 89 1c 24          	mov    %r11,(%rsp)
  long received = 0;
    2e50:	31 db                	xor    %ebx,%ebx
    2e52:	4d 89 e6             	mov    %r12,%r14
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
      struct timespec start = thread_data[x].start[n];
      struct timespec end = thread_data[x].end[n];
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2e55:	49 bf db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r15
    2e5f:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2e64:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    2e69:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    2e6e:	66 90                	xchg   %ax,%ax
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2e70:	49 63 55 08          	movslq 0x8(%r13),%rdx
    2e74:	85 d2                	test   %edx,%edx
    2e76:	0f 8e ce 00 00 00    	jle    2f4a <main+0x9ea>
    2e7c:	49 8b 45 00          	mov    0x0(%r13),%rax
    2e80:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
    2e84:	4c 8b 04 24          	mov    (%rsp),%r8
    2e88:	48 8d 14 72          	lea    (%rdx,%rsi,2),%rdx
    2e8c:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    2e91:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2e96:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    2e9b:	48 8d 14 d0          	lea    (%rax,%rdx,8),%rdx
    2e9f:	90                   	nop
      total += thread_data[x].tasks[n].n;
    2ea0:	48 8b 70 10          	mov    0x10(%rax),%rsi
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2ea4:	48 05 98 00 00 00    	add    $0x98,%rax
      total += thread_data[x].tasks[n].n;
    2eaa:	49 01 f6             	add    %rsi,%r14
      v += thread_data[x].tasks[n].v;
    2ead:	48 8b 70 80          	mov    -0x80(%rax),%rsi
    2eb1:	48 01 f1             	add    %rsi,%rcx
      ingests += thread_data[x].tasks[n].ingest_count;
    2eb4:	48 8b 70 d0          	mov    -0x30(%rax),%rsi
    2eb8:	49 01 f0             	add    %rsi,%r8
      sends += thread_data[x].tasks[n].sends;
    2ebb:	48 8b 70 e0          	mov    -0x20(%rax),%rsi
    2ebf:	49 01 f1             	add    %rsi,%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ec2:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2ec6:	48 03 6e 10          	add    0x10(%rsi),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2eca:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2ece:	48 03 5e 18          	add    0x18(%rsi),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ed2:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2ed6:	48 03 6e 30          	add    0x30(%rsi),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2eda:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2ede:	48 03 5e 38          	add    0x38(%rsi),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ee2:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2ee6:	48 03 6e 50          	add    0x50(%rsi),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2eea:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2eee:	48 03 5e 58          	add    0x58(%rsi),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ef2:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2ef6:	48 03 6e 70          	add    0x70(%rsi),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2efa:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2efe:	48 03 5e 78          	add    0x78(%rsi),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2f02:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f06:	48 03 ae 90 00 00 00 	add    0x90(%rsi),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2f0d:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f11:	48 03 9e 98 00 00 00 	add    0x98(%rsi),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2f18:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f1c:	48 03 ae b0 00 00 00 	add    0xb0(%rsi),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2f23:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f27:	48 03 9e b8 00 00 00 	add    0xb8(%rsi),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2f2e:	48 39 d0             	cmp    %rdx,%rax
    2f31:	0f 85 69 ff ff ff    	jne    2ea0 <main+0x940>
    2f37:	4c 89 04 24          	mov    %r8,(%rsp)
    2f3b:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    2f40:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2f45:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f4a:	45 31 e4             	xor    %r12d,%r12d
    2f4d:	49 83 7d 50 00       	cmpq   $0x0,0x50(%r13)
    2f52:	7e 73                	jle    2fc7 <main+0xa67>
    2f54:	4c 89 ed             	mov    %r13,%rbp
    2f57:	49 89 dd             	mov    %rbx,%r13
    2f5a:	4c 89 e3             	mov    %r12,%rbx
    2f5d:	0f 1f 00             	nopl   (%rax)
      struct timespec start = thread_data[x].start[n];
    2f60:	48 8b 7d 30          	mov    0x30(%rbp),%rdi
    2f64:	48 89 de             	mov    %rbx,%rsi
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f67:	48 83 c3 01          	add    $0x1,%rbx
    2f6b:	48 c1 e6 04          	shl    $0x4,%rsi
      struct timespec start = thread_data[x].start[n];
    2f6f:	48 01 f7             	add    %rsi,%rdi
      struct timespec end = thread_data[x].end[n];
    2f72:	48 03 75 38          	add    0x38(%rbp),%rsi
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    2f76:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    2f7a:	48 2b 57 08          	sub    0x8(%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2f7e:	48 89 d0             	mov    %rdx,%rax
    2f81:	49 f7 e7             	mul    %r15
    2f84:	31 c0                	xor    %eax,%eax
    2f86:	48 89 d1             	mov    %rdx,%rcx
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    2f89:	48 8b 16             	mov    (%rsi),%rdx
    2f8c:	48 8d 35 03 34 00 00 	lea    0x3403(%rip),%rsi        # 6396 <_IO_stdin_used+0x396>
    2f93:	48 2b 17             	sub    (%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2f96:	48 c1 e9 12          	shr    $0x12,%rcx
    2f9a:	bf 01 00 00 00       	mov    $0x1,%edi
    2f9f:	e8 8c f4 ff ff       	call   2430 <__printf_chk@plt>
    2fa4:	48 8b 55 40          	mov    0x40(%rbp),%rdx
    2fa8:	bf 01 00 00 00       	mov    $0x1,%edi
    2fad:	31 c0                	xor    %eax,%eax
    2faf:	48 8d 35 fe 33 00 00 	lea    0x33fe(%rip),%rsi        # 63b4 <_IO_stdin_used+0x3b4>
    2fb6:	e8 75 f4 ff ff       	call   2430 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2fbb:	48 39 5d 50          	cmp    %rbx,0x50(%rbp)
    2fbf:	7f 9f                	jg     2f60 <main+0xa00>
    2fc1:	4c 89 eb             	mov    %r13,%rbx
    2fc4:	49 89 ed             	mov    %rbp,%r13
      printf("%ld iterations\n", thread_data[x].iteration_count);
    }
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    2fc7:	45 31 e4             	xor    %r12d,%r12d
    2fca:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    2fcf:	0f 8e 96 00 00 00    	jle    306b <main+0xb0b>
    2fd5:	48 89 d8             	mov    %rbx,%rax
    2fd8:	4c 89 e5             	mov    %r12,%rbp
    2fdb:	4c 89 eb             	mov    %r13,%rbx
    2fde:	49 89 c5             	mov    %rax,%r13
    2fe1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    2fe8:	48 8b 43 58          	mov    0x58(%rbx),%rax
    2fec:	48 8d 54 ad 00       	lea    0x0(%rbp,%rbp,4),%rdx
    2ff1:	48 83 ec 08          	sub    $0x8,%rsp
    2ff5:	48 8d 35 3c 36 00 00 	lea    0x363c(%rip),%rsi        # 6638 <_IO_stdin_used+0x638>
    2ffc:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3001:	48 83 c5 01          	add    $0x1,%rbp
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3005:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3009:	4c 8b 61 18          	mov    0x18(%rcx),%r12
    300d:	4c 2b 61 08          	sub    0x8(%rcx),%r12
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3011:	4c 89 e0             	mov    %r12,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3014:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3018:	4c 2b 01             	sub    (%rcx),%r8
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    301b:	49 f7 e7             	mul    %r15
    301e:	8b 49 20             	mov    0x20(%rcx),%ecx
    3021:	41 54                	push   %r12
    3023:	31 c0                	xor    %eax,%eax
    3025:	48 c1 ea 12          	shr    $0x12,%rdx
    3029:	49 89 d1             	mov    %rdx,%r9
    302c:	ba 06 00 00 00       	mov    $0x6,%edx
    3031:	e8 fa f3 ff ff       	call   2430 <__printf_chk@plt>
    3036:	48 8d 35 93 33 00 00 	lea    0x3393(%rip),%rsi        # 63d0 <_IO_stdin_used+0x3d0>
    303d:	bf 01 00 00 00       	mov    $0x1,%edi
      printf("%ldns per thread\n", (seconds2 / thread_count));
    3042:	48 b8 ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%rax
    304c:	49 f7 e4             	mul    %r12
    304f:	31 c0                	xor    %eax,%eax
    3051:	48 c1 ea 02          	shr    $0x2,%rdx
    3055:	e8 d6 f3 ff ff       	call   2430 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    305a:	58                   	pop    %rax
    305b:	5a                   	pop    %rdx
    305c:	48 3b 6b 68          	cmp    0x68(%rbx),%rbp
    3060:	7c 86                	jl     2fe8 <main+0xa88>
    3062:	4c 89 e8             	mov    %r13,%rax
    3065:	49 89 dd             	mov    %rbx,%r13
    3068:	48 89 c3             	mov    %rax,%rbx
    306b:	49 8b 55 70          	mov    0x70(%r13),%rdx
    306f:	48 8d 35 4e 33 00 00 	lea    0x334e(%rip),%rsi        # 63c4 <_IO_stdin_used+0x3c4>
    3076:	bf 01 00 00 00       	mov    $0x1,%edi
    307b:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < thread_count ; x++) {
    307d:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    3084:	e8 a7 f3 ff ff       	call   2430 <__printf_chk@plt>
    3089:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    308e:	49 39 c5             	cmp    %rax,%r13
    3091:	0f 85 d9 fd ff ff    	jne    2e70 <main+0x910>
    3097:	4c 89 f2             	mov    %r14,%rdx
    309a:	48 8d 35 41 33 00 00 	lea    0x3341(%rip),%rsi        # 63e2 <_IO_stdin_used+0x3e2>
    30a1:	31 c0                	xor    %eax,%eax
    30a3:	4d 89 f4             	mov    %r14,%r12
    30a6:	bf 01 00 00 00       	mov    $0x1,%edi
    30ab:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total Protected %ld\n", protected_state->protected);
  printf("Total V %ld\n", v);
  printf("\n");
  printf("Total Protected per second %ld\n", protected_state->protected / DURATION);
    30b0:	49 bd 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%r13
    30ba:	e8 71 f3 ff ff       	call   2430 <__printf_chk@plt>
    30bf:	bf 0a 00 00 00       	mov    $0xa,%edi
    30c4:	e8 f7 f1 ff ff       	call   22c0 <putchar@plt>
    30c9:	4c 8b 7c 24 30       	mov    0x30(%rsp),%r15
    30ce:	48 8d 35 21 33 00 00 	lea    0x3321(%rip),%rsi        # 63f6 <_IO_stdin_used+0x3f6>
    30d5:	31 c0                	xor    %eax,%eax
    30d7:	bf 01 00 00 00       	mov    $0x1,%edi
    30dc:	49 8b 17             	mov    (%r15),%rdx
    30df:	e8 4c f3 ff ff       	call   2430 <__printf_chk@plt>
    30e4:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    30e9:	48 8d 35 1b 33 00 00 	lea    0x331b(%rip),%rsi        # 640b <_IO_stdin_used+0x40b>
    30f0:	31 c0                	xor    %eax,%eax
    30f2:	bf 01 00 00 00       	mov    $0x1,%edi
    30f7:	e8 34 f3 ff ff       	call   2430 <__printf_chk@plt>
    30fc:	bf 0a 00 00 00       	mov    $0xa,%edi
    3101:	e8 ba f1 ff ff       	call   22c0 <putchar@plt>
    3106:	49 8b 37             	mov    (%r15),%rsi
    3109:	bf 01 00 00 00       	mov    $0x1,%edi
    310e:	48 89 f0             	mov    %rsi,%rax
    3111:	49 f7 ed             	imul   %r13
    3114:	31 c0                	xor    %eax,%eax
    3116:	48 01 f2             	add    %rsi,%rdx
    3119:	48 c1 fe 3f          	sar    $0x3f,%rsi
    311d:	48 c1 fa 04          	sar    $0x4,%rdx
    3121:	48 29 f2             	sub    %rsi,%rdx
    3124:	48 8d 35 45 35 00 00 	lea    0x3545(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    312b:	e8 00 f3 ff ff       	call   2430 <__printf_chk@plt>
    3130:	49 8b 57 08          	mov    0x8(%r15),%rdx
    3134:	bf 01 00 00 00       	mov    $0x1,%edi
    3139:	31 c0                	xor    %eax,%eax
    313b:	48 8d 35 4e 35 00 00 	lea    0x354e(%rip),%rsi        # 6690 <_IO_stdin_used+0x690>
    3142:	e8 e9 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3147:	4c 8b 1c 24          	mov    (%rsp),%r11
    314b:	bf 01 00 00 00       	mov    $0x1,%edi
    3150:	48 8d 35 61 35 00 00 	lea    0x3561(%rip),%rsi        # 66b8 <_IO_stdin_used+0x6b8>
    3157:	4c 89 d8             	mov    %r11,%rax
    315a:	49 f7 ed             	imul   %r13
    315d:	31 c0                	xor    %eax,%eax
    315f:	4c 01 da             	add    %r11,%rdx
    3162:	49 c1 fb 3f          	sar    $0x3f,%r11
    3166:	48 c1 fa 04          	sar    $0x4,%rdx
    316a:	4c 29 da             	sub    %r11,%rdx
    316d:	e8 be f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3172:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    3177:	bf 01 00 00 00       	mov    $0x1,%edi
    317c:	48 8d 35 65 35 00 00 	lea    0x3565(%rip),%rsi        # 66e8 <_IO_stdin_used+0x6e8>
    3183:	48 89 c8             	mov    %rcx,%rax
    3186:	49 f7 ed             	imul   %r13
    3189:	31 c0                	xor    %eax,%eax
    318b:	48 01 ca             	add    %rcx,%rdx
    318e:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3192:	48 c1 fa 04          	sar    $0x4,%rdx
    3196:	48 29 ca             	sub    %rcx,%rdx
    3199:	e8 92 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    319e:	4c 89 f0             	mov    %r14,%rax
    31a1:	bf 01 00 00 00       	mov    $0x1,%edi
    31a6:	48 8d 35 6b 35 00 00 	lea    0x356b(%rip),%rsi        # 6718 <_IO_stdin_used+0x718>
    31ad:	49 f7 ed             	imul   %r13
    31b0:	4c 01 f2             	add    %r14,%rdx
    31b3:	49 c1 fc 3f          	sar    $0x3f,%r12
    31b7:	31 c0                	xor    %eax,%eax
    31b9:	48 c1 fa 04          	sar    $0x4,%rdx
    31bd:	4c 29 e2             	sub    %r12,%rdx
    31c0:	e8 6b f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    31c5:	48 89 e8             	mov    %rbp,%rax
    31c8:	bf 01 00 00 00       	mov    $0x1,%edi
    31cd:	48 8d 35 44 32 00 00 	lea    0x3244(%rip),%rsi        # 6418 <_IO_stdin_used+0x418>
    31d4:	49 f7 ed             	imul   %r13
    31d7:	31 c0                	xor    %eax,%eax
    31d9:	48 01 ea             	add    %rbp,%rdx
    31dc:	48 c1 fd 3f          	sar    $0x3f,%rbp
    31e0:	48 c1 fa 04          	sar    $0x4,%rdx
    31e4:	48 29 ea             	sub    %rbp,%rdx
    31e7:	e8 44 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    31ec:	48 89 d8             	mov    %rbx,%rax
    31ef:	bf 01 00 00 00       	mov    $0x1,%edi
    31f4:	48 8d 35 2e 32 00 00 	lea    0x322e(%rip),%rsi        # 6429 <_IO_stdin_used+0x429>
    31fb:	49 f7 ed             	imul   %r13
    31fe:	31 c0                	xor    %eax,%eax
    3200:	48 01 da             	add    %rbx,%rdx
    3203:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3207:	48 c1 fa 04          	sar    $0x4,%rdx
    320b:	48 29 da             	sub    %rbx,%rdx
    320e:	e8 1d f2 ff ff       	call   2430 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3213:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3218:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3221:	75 54                	jne    3277 <main+0xd17>
    3223:	48 83 c4 58          	add    $0x58,%rsp
    3227:	31 c0                	xor    %eax,%eax
    3229:	5b                   	pop    %rbx
    322a:	5d                   	pop    %rbp
    322b:	41 5c                	pop    %r12
    322d:	41 5d                	pop    %r13
    322f:	41 5e                	pop    %r14
    3231:	41 5f                	pop    %r15
    3233:	c3                   	ret
    3234:	0f 1f 40 00          	nopl   0x0(%rax)
            thread_data[x].tasks[y].run = barriered_work; 
    3238:	48 8d 05 11 20 00 00 	lea    0x2011(%rip),%rax        # 5250 <barriered_work>
    323f:	49 89 45 20          	mov    %rax,0x20(%r13)
    3243:	e9 f7 f7 ff ff       	jmp    2a3f <main+0x4df>
    3248:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
            thread_data[x].tasks[y].protected = do_protected_write; 
    3250:	48 8d 05 19 01 00 00 	lea    0x119(%rip),%rax        # 3370 <do_protected_write>
    3257:	48 89 45 28          	mov    %rax,0x28(%rbp)
    325b:	e9 0c f6 ff ff       	jmp    286c <main+0x30c>
          thread_data[x].tasks[y].run = barriered_work; 
    3260:	48 8d 05 e9 1f 00 00 	lea    0x1fe9(%rip),%rax        # 5250 <barriered_work>
    3267:	bd 03 00 00 00       	mov    $0x3,%ebp
    326c:	49 89 45 20          	mov    %rax,0x20(%r13)
  int external_thread_index = 0;
    3270:	89 eb                	mov    %ebp,%ebx
    3272:	e9 d7 f5 ff ff       	jmp    284e <main+0x2ee>
}
    3277:	e8 94 f0 ff ff       	call   2310 <__stack_chk_fail@plt>
    327c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003280 <_start>:
    3280:	f3 0f 1e fa          	endbr64
    3284:	31 ed                	xor    %ebp,%ebp
    3286:	49 89 d1             	mov    %rdx,%r9
    3289:	5e                   	pop    %rsi
    328a:	48 89 e2             	mov    %rsp,%rdx
    328d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3291:	50                   	push   %rax
    3292:	54                   	push   %rsp
    3293:	45 31 c0             	xor    %r8d,%r8d
    3296:	31 c9                	xor    %ecx,%ecx
    3298:	48 8d 3d c1 f2 ff ff 	lea    -0xd3f(%rip),%rdi        # 2560 <main>
    329f:	ff 15 33 5d 00 00    	call   *0x5d33(%rip)        # 8fd8 <__libc_start_main@GLIBC_2.34>
    32a5:	f4                   	hlt
    32a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000032b0 <deregister_tm_clones>:
    32b0:	48 8d 3d 69 5d 00 00 	lea    0x5d69(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    32b7:	48 8d 05 62 5d 00 00 	lea    0x5d62(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    32be:	48 39 f8             	cmp    %rdi,%rax
    32c1:	74 15                	je     32d8 <deregister_tm_clones+0x28>
    32c3:	48 8b 05 16 5d 00 00 	mov    0x5d16(%rip),%rax        # 8fe0 <_ITM_deregisterTMCloneTable@Base>
    32ca:	48 85 c0             	test   %rax,%rax
    32cd:	74 09                	je     32d8 <deregister_tm_clones+0x28>
    32cf:	ff e0                	jmp    *%rax
    32d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    32d8:	c3                   	ret
    32d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000032e0 <register_tm_clones>:
    32e0:	48 8d 3d 39 5d 00 00 	lea    0x5d39(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    32e7:	48 8d 35 32 5d 00 00 	lea    0x5d32(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    32ee:	48 29 fe             	sub    %rdi,%rsi
    32f1:	48 89 f0             	mov    %rsi,%rax
    32f4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    32f8:	48 c1 f8 03          	sar    $0x3,%rax
    32fc:	48 01 c6             	add    %rax,%rsi
    32ff:	48 d1 fe             	sar    %rsi
    3302:	74 14                	je     3318 <register_tm_clones+0x38>
    3304:	48 8b 05 e5 5c 00 00 	mov    0x5ce5(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    330b:	48 85 c0             	test   %rax,%rax
    330e:	74 08                	je     3318 <register_tm_clones+0x38>
    3310:	ff e0                	jmp    *%rax
    3312:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3318:	c3                   	ret
    3319:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003320 <__do_global_dtors_aux>:
    3320:	f3 0f 1e fa          	endbr64
    3324:	80 3d fd 5c 00 00 00 	cmpb   $0x0,0x5cfd(%rip)        # 9028 <completed.0>
    332b:	75 2b                	jne    3358 <__do_global_dtors_aux+0x38>
    332d:	55                   	push   %rbp
    332e:	48 83 3d c2 5c 00 00 00 	cmpq   $0x0,0x5cc2(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    3336:	48 89 e5             	mov    %rsp,%rbp
    3339:	74 0c                	je     3347 <__do_global_dtors_aux+0x27>
    333b:	48 8b 3d c6 5c 00 00 	mov    0x5cc6(%rip),%rdi        # 9008 <__dso_handle>
    3342:	e8 59 ef ff ff       	call   22a0 <__cxa_finalize@plt>
    3347:	e8 64 ff ff ff       	call   32b0 <deregister_tm_clones>
    334c:	c6 05 d5 5c 00 00 01 	movb   $0x1,0x5cd5(%rip)        # 9028 <completed.0>
    3353:	5d                   	pop    %rbp
    3354:	c3                   	ret
    3355:	0f 1f 00             	nopl   (%rax)
    3358:	c3                   	ret
    3359:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003360 <frame_dummy>:
    3360:	f3 0f 1e fa          	endbr64
    3364:	e9 77 ff ff ff       	jmp    32e0 <register_tm_clones>
    3369:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003370 <do_protected_write>:
int do_protected_write(volatile struct BarrierTask *data) {
    3370:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3374:	48 8b 47 30          	mov    0x30(%rdi),%rax
  data->v++; // thread local
    3378:	48 8b 57 18          	mov    0x18(%rdi),%rdx
  struct ProtectedState *protected = data->thread->protected_state;
    337c:	48 8b 40 30          	mov    0x30(%rax),%rax
  data->v++; // thread local
    3380:	48 83 c2 01          	add    $0x1,%rdx
    3384:	48 89 57 18          	mov    %rdx,0x18(%rdi)
  if (protected->balance > 0) {
    3388:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    338c:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    3390:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3397:	48 85 c9             	test   %rcx,%rcx
    339a:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    33a1:	48 0f 4f d6          	cmovg  %rsi,%rdx
    33a5:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    33a9:	31 c0                	xor    %eax,%eax
    33ab:	c3                   	ret
    33ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000033b0 <barriered_reset>:
int barriered_reset(volatile struct BarrierTask *data) {
    33b0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    33b4:	8b 47 44             	mov    0x44(%rdi),%eax
int barriered_reset(volatile struct BarrierTask *data) {
    33b7:	48 89 fa             	mov    %rdi,%rdx
    for (int x = 0 ; x < data->task_count ; x++) {
    33ba:	85 c0                	test   %eax,%eax
    33bc:	7e 55                	jle    3413 <barriered_reset+0x63>
    33be:	31 c9                	xor    %ecx,%ecx
    33c0:	31 f6                	xor    %esi,%esi
    33c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    33c8:	48 8b 7a 30          	mov    0x30(%rdx),%rdi
    33cc:	48 63 42 38          	movslq 0x38(%rdx),%rax
    for (int x = 0 ; x < data->task_count ; x++) {
    33d0:	83 c6 01             	add    $0x1,%esi
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    33d3:	4c 8d 04 c0          	lea    (%rax,%rax,8),%r8
    33d7:	4a 8d 04 40          	lea    (%rax,%r8,2),%rax
    33db:	4c 8b 47 10          	mov    0x10(%rdi),%r8
    33df:	49 8d 04 c0          	lea    (%r8,%rax,8),%rax
    33e3:	48 8b 78 20          	mov    0x20(%rax),%rdi
    33e7:	48 01 cf             	add    %rcx,%rdi
    33ea:	8b 47 08             	mov    0x8(%rdi),%eax
    33ed:	83 c0 01             	add    $0x1,%eax
    33f0:	89 47 08             	mov    %eax,0x8(%rdi)
      data->thread->tasks[x].available = 1; 
    33f3:	48 8b 42 30          	mov    0x30(%rdx),%rax
    33f7:	48 8b 78 20          	mov    0x20(%rax),%rdi
    33fb:	48 01 cf             	add    %rcx,%rdi
    for (int x = 0 ; x < data->task_count ; x++) {
    33fe:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
      data->thread->tasks[x].available = 1; 
    3405:	c7 47 40 01 00 00 00 	movl   $0x1,0x40(%rdi)
    for (int x = 0 ; x < data->task_count ; x++) {
    340c:	8b 42 44             	mov    0x44(%rdx),%eax
    340f:	39 f0                	cmp    %esi,%eax
    3411:	7f b5                	jg     33c8 <barriered_reset+0x18>
  asm volatile ("mfence" ::: "memory");
    3413:	0f ae f0             	mfence
}
    3416:	31 c0                	xor    %eax,%eax
    3418:	c3                   	ret
    3419:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003420 <barriered_thread>:
void* barriered_thread(void *arg) {
    3420:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3424:	8b 47 2c             	mov    0x2c(%rdi),%eax
    3427:	83 f8 01             	cmp    $0x1,%eax
    342a:	0f 85 60 02 00 00    	jne    3690 <barriered_thread+0x270>
void* barriered_thread(void *arg) {
    3430:	41 55                	push   %r13
  int waiting = 0;
    3432:	45 31 ed             	xor    %r13d,%r13d
void* barriered_thread(void *arg) {
    3435:	41 54                	push   %r12
    3437:	49 89 fc             	mov    %rdi,%r12
    343a:	55                   	push   %rbp
    343b:	53                   	push   %rbx
  int t = 0;
    343c:	31 db                	xor    %ebx,%ebx
void* barriered_thread(void *arg) {
    343e:	48 83 ec 08          	sub    $0x8,%rsp
    if (t >= data->task_count) {
    3442:	44 8b 57 28          	mov    0x28(%rdi),%r10d
    3446:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3450:	44 39 d3             	cmp    %r10d,%ebx
    3453:	7c 14                	jl     3469 <barriered_thread+0x49>
      data->cycles++;
    3455:	49 83 84 24 90 00 00 00 01 	addq   $0x1,0x90(%r12)
      t = 0;
    345e:	31 db                	xor    %ebx,%ebx
    for (; t < data->task_count; t++) {
    3460:	45 85 d2             	test   %r10d,%r10d
    3463:	0f 8e 67 01 00 00    	jle    35d0 <barriered_thread+0x1b0>
    3469:	48 63 c3             	movslq %ebx,%rax
    346c:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3470:	48 8d 2c 50          	lea    (%rax,%rdx,2),%rbp
    3474:	48 c1 e5 03          	shl    $0x3,%rbp
    3478:	eb 19                	jmp    3493 <barriered_thread+0x73>
    347a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3480:	83 c3 01             	add    $0x1,%ebx
    3483:	48 81 c5 98 00 00 00 	add    $0x98,%rbp
    348a:	44 39 d3             	cmp    %r10d,%ebx
    348d:	0f 8d 3d 01 00 00    	jge    35d0 <barriered_thread+0x1b0>
      if (data->tasks[t].available == 1) {
    3493:	49 8b 54 24 20       	mov    0x20(%r12),%rdx
    3498:	48 01 ea             	add    %rbp,%rdx
    349b:	8b 42 40             	mov    0x40(%rdx),%eax
    349e:	83 f8 01             	cmp    $0x1,%eax
    34a1:	75 dd                	jne    3480 <barriered_thread+0x60>
        if (t > 0) {
    34a3:	85 db                	test   %ebx,%ebx
    34a5:	0f 8e 45 01 00 00    	jle    35f0 <barriered_thread+0x1d0>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    34ab:	45 8b 5c 24 18       	mov    0x18(%r12),%r11d
          previous = t - 1;
    34b0:	8d 43 ff             	lea    -0x1(%rbx),%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    34b3:	45 85 db             	test   %r11d,%r11d
    34b6:	7e 6d                	jle    3525 <barriered_thread+0x105>
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    34b8:	48 98                	cltq
    34ba:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    34be:	4c 8d 04 48          	lea    (%rax,%rcx,2),%r8
    34c2:	49 63 cb             	movslq %r11d,%rcx
    34c5:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    34ca:	48 8d 34 c9          	lea    (%rcx,%rcx,8),%rsi
    34ce:	49 c1 e0 03          	shl    $0x3,%r8
    34d2:	48 8d 0c 71          	lea    (%rcx,%rsi,2),%rcx
    34d6:	4c 8d 0c c8          	lea    (%rax,%rcx,8),%r9
        int arrived = 0; 
    34da:	31 c9                	xor    %ecx,%ecx
    34dc:	0f 1f 40 00          	nopl   0x0(%rax)
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    34e0:	48 8b 70 20          	mov    0x20(%rax),%rsi
    34e4:	4c 01 c6             	add    %r8,%rsi
    34e7:	8b 76 08             	mov    0x8(%rsi),%esi
    34ea:	8b 7a 08             	mov    0x8(%rdx),%edi
            arrived++;
    34ed:	39 f7                	cmp    %esi,%edi
    34ef:	40 0f 94 c6          	sete   %sil
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    34f3:	48 05 98 00 00 00    	add    $0x98,%rax
            arrived++;
    34f9:	40 0f b6 f6          	movzbl %sil,%esi
    34fd:	01 f1                	add    %esi,%ecx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    34ff:	4c 39 c8             	cmp    %r9,%rax
    3502:	75 dc                	jne    34e0 <barriered_thread+0xc0>
        if (arrived == 0 || arrived == data->thread_count) {
    3504:	44 39 d9             	cmp    %r11d,%ecx
    3507:	74 08                	je     3511 <barriered_thread+0xf1>
    3509:	85 c9                	test   %ecx,%ecx
    350b:	0f 85 bf 00 00 00    	jne    35d0 <barriered_thread+0x1b0>
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    3511:	85 db                	test   %ebx,%ebx
    3513:	75 10                	jne    3525 <barriered_thread+0x105>
    3515:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    351a:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    351f:	0f 8c 53 01 00 00    	jl     3678 <barriered_thread+0x258>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3525:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    352d:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3531:	49 8b 44 24 78       	mov    0x78(%r12),%rax
          if (waiting == 1) {
    3536:	41 83 fd 01          	cmp    $0x1,%r13d
    353a:	0f 84 00 01 00 00    	je     3640 <barriered_thread+0x220>
            data->task_snapshot[data->task_timestamp_count].task = t;
    3540:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3544:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3549:	41 bd 01 00 00 00    	mov    $0x1,%r13d
            data->task_snapshot[data->task_timestamp_count].task = t;
    354f:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3552:	e8 99 ed ff ff       	call   22f0 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3557:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    355c:	48 01 e8             	add    %rbp,%rax
    355f:	c7 40 40 00 00 00 00 	movl   $0x0,0x40(%rax)
          data->tasks[t].run(&data->threads[data->thread_index].tasks[t]);
    3566:	48 8b 50 20          	mov    0x20(%rax),%rdx
    356a:	49 63 04 24          	movslq (%r12),%rax
    356e:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    3572:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    3576:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
    357b:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    357f:	48 8b 78 20          	mov    0x20(%rax),%rdi
    3583:	48 01 ef             	add    %rbp,%rdi
    3586:	ff d2                	call   *%rdx
          data->tasks[t].arrived++;
    3588:	49 8b 54 24 20       	mov    0x20(%r12),%rdx
    358d:	48 01 ea             	add    %rbp,%rdx
    3590:	8b 42 08             	mov    0x8(%rdx),%eax
    3593:	83 c0 01             	add    $0x1,%eax
    3596:	89 42 08             	mov    %eax,0x8(%rdx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3599:	41 8b 44 24 28       	mov    0x28(%r12),%eax
          data->iteration_count++;
    359e:	49 83 44 24 60 01    	addq   $0x1,0x60(%r12)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    35a4:	83 e8 01             	sub    $0x1,%eax
    35a7:	39 d8                	cmp    %ebx,%eax
    35a9:	74 65                	je     3610 <barriered_thread+0x1f0>
          asm volatile ("mfence" ::: "memory");
    35ab:	0f ae f0             	mfence
    for (; t < data->task_count; t++) {
    35ae:	45 8b 54 24 28       	mov    0x28(%r12),%r10d
    35b3:	83 c3 01             	add    $0x1,%ebx
    35b6:	48 81 c5 98 00 00 00 	add    $0x98,%rbp
    35bd:	44 39 d3             	cmp    %r10d,%ebx
    35c0:	0f 8c cd fe ff ff    	jl     3493 <barriered_thread+0x73>
    35c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  while (data->running == 1) {
    35d0:	41 8b 44 24 2c       	mov    0x2c(%r12),%eax
    35d5:	83 f8 01             	cmp    $0x1,%eax
    35d8:	0f 84 72 fe ff ff    	je     3450 <barriered_thread+0x30>
}
    35de:	48 83 c4 08          	add    $0x8,%rsp
    35e2:	31 c0                	xor    %eax,%eax
    35e4:	5b                   	pop    %rbx
    35e5:	5d                   	pop    %rbp
    35e6:	41 5c                	pop    %r12
    35e8:	41 5d                	pop    %r13
    35ea:	c3                   	ret
    35eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    35f0:	45 8b 5c 24 18       	mov    0x18(%r12),%r11d
          previous = data->task_count - 1;
    35f5:	41 8d 42 ff          	lea    -0x1(%r10),%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    35f9:	45 85 db             	test   %r11d,%r11d
    35fc:	0f 8f b6 fe ff ff    	jg     34b8 <barriered_thread+0x98>
    3602:	e9 0a ff ff ff       	jmp    3511 <barriered_thread+0xf1>
    3607:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3610:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    3615:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    361a:	7d 8f                	jge    35ab <barriered_thread+0x18b>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    361c:	48 c1 e6 04          	shl    $0x4,%rsi
    3620:	bf 04 00 00 00       	mov    $0x4,%edi
    3625:	49 03 74 24 58       	add    0x58(%r12),%rsi
    362a:	e8 c1 ec ff ff       	call   22f0 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    362f:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
    3635:	e9 71 ff ff ff       	jmp    35ab <barriered_thread+0x18b>
    363a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3640:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3645:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 0;
    364a:	45 31 ed             	xor    %r13d,%r13d
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    364d:	e8 9e ec ff ff       	call   22f0 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3652:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    365a:	48 83 c0 01          	add    $0x1,%rax
    365e:	48 99                	cqto
    3660:	49 f7 bc 24 88 00 00 00 	idivq  0x88(%r12)
    3668:	49 89 94 24 80 00 00 00 	mov    %rdx,0x80(%r12)
          if (waiting == 3) {
    3670:	e9 e2 fe ff ff       	jmp    3557 <barriered_thread+0x137>
    3675:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3678:	48 c1 e6 04          	shl    $0x4,%rsi
    367c:	bf 04 00 00 00       	mov    $0x4,%edi
    3681:	49 03 74 24 50       	add    0x50(%r12),%rsi
    3686:	e8 65 ec ff ff       	call   22f0 <clock_gettime@plt>
    368b:	e9 95 fe ff ff       	jmp    3525 <barriered_thread+0x105>
}
    3690:	31 c0                	xor    %eax,%eax
    3692:	c3                   	ret
    3693:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    369e:	66 90                	xchg   %ax,%ax

00000000000036a0 <external_thread>:
void * external_thread(void *arg) {
    36a0:	f3 0f 1e fa          	endbr64
    36a4:	41 55                	push   %r13
    36a6:	41 54                	push   %r12
    36a8:	55                   	push   %rbp
    36a9:	53                   	push   %rbx
    36aa:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    36ae:	66 0f 6f 05 7a 32 00 00 	movdqa 0x327a(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
void * external_thread(void *arg) {
    36b6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    36bf:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    36c4:	31 c0                	xor    %eax,%eax
  struct timespec req = {
    36c6:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    36ca:	8b 47 2c             	mov    0x2c(%rdi),%eax
    36cd:	83 f8 01             	cmp    $0x1,%eax
    36d0:	75 64                	jne    3736 <external_thread+0x96>
    36d2:	49 89 fd             	mov    %rdi,%r13
    36d5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    36da:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    36dd:	4c 8d 25 20 29 00 00 	lea    0x2920(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    36e4:	0f 1f 40 00          	nopl   0x0(%rax)
    nanosleep(&req , &rem);
    36e8:	48 89 ee             	mov    %rbp,%rsi
    36eb:	48 89 df             	mov    %rbx,%rdi
    36ee:	e8 3d ec ff ff       	call   2330 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    36f3:	49 8b 45 38          	mov    0x38(%r13),%rax
    36f7:	48 63 08             	movslq (%rax),%rcx
    36fa:	85 c9                	test   %ecx,%ecx
    36fc:	7e 2c                	jle    372a <external_thread+0x8a>
    36fe:	48 8b 40 08          	mov    0x8(%rax),%rax
    3702:	48 c1 e1 04          	shl    $0x4,%rcx
    3706:	48 01 c1             	add    %rax,%rcx
    3709:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    3710:	8b 50 08             	mov    0x8(%rax),%edx
    3713:	85 d2                	test   %edx,%edx
    3715:	75 0a                	jne    3721 <external_thread+0x81>
        data->buffers->buffer[x].data = "Hello world";
    3717:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    371a:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3721:	48 83 c0 10          	add    $0x10,%rax
    3725:	48 39 c1             	cmp    %rax,%rcx
    3728:	75 e6                	jne    3710 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    372a:	0f ae f0             	mfence
  while (data->running == 1) {
    372d:	41 8b 45 2c          	mov    0x2c(%r13),%eax
    3731:	83 f8 01             	cmp    $0x1,%eax
    3734:	74 b2                	je     36e8 <external_thread+0x48>
}
    3736:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    373b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3744:	75 0d                	jne    3753 <external_thread+0xb3>
    3746:	48 83 c4 38          	add    $0x38,%rsp
    374a:	31 c0                	xor    %eax,%eax
    374c:	5b                   	pop    %rbx
    374d:	5d                   	pop    %rbp
    374e:	41 5c                	pop    %r12
    3750:	41 5d                	pop    %r13
    3752:	c3                   	ret
    3753:	e8 b8 eb ff ff       	call   2310 <__stack_chk_fail@plt>
    3758:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000003760 <timer_thread>:
void* timer_thread(void *arg) {
    3760:	f3 0f 1e fa          	endbr64
    3764:	41 57                	push   %r15
    3766:	48 8d 35 a3 28 00 00 	lea    0x28a3(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    376d:	49 89 ff             	mov    %rdi,%r15
    3770:	41 56                	push   %r14
    3772:	41 55                	push   %r13
    3774:	41 54                	push   %r12
    3776:	55                   	push   %rbp
    3777:	53                   	push   %rbx
    3778:	48 83 ec 58          	sub    $0x58,%rsp
    377c:	8b 17                	mov    (%rdi),%edx
    377e:	bf 01 00 00 00       	mov    $0x1,%edi
    3783:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    378c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3791:	31 c0                	xor    %eax,%eax
    3793:	e8 98 ec ff ff       	call   2430 <__printf_chk@plt>
  struct timespec preempt = {
    3798:	66 0f 6f 05 90 31 00 00 	movdqa 0x3190(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    37a0:	ba 30 75 00 00       	mov    $0x7530,%edx
    37a5:	31 c0                	xor    %eax,%eax
    37a7:	48 8d 35 74 28 00 00 	lea    0x2874(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    37ae:	bf 01 00 00 00       	mov    $0x1,%edi
    37b3:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    37b8:	e8 73 ec ff ff       	call   2430 <__printf_chk@plt>
  while (data->running && n < times) {
    37bd:	4d 63 77 2c          	movslq 0x2c(%r15),%r14
    37c1:	45 85 f6             	test   %r14d,%r14d
    37c4:	0f 84 a9 00 00 00    	je     3873 <timer_thread+0x113>
  int n = 0;
    37ca:	45 31 ed             	xor    %r13d,%r13d
  int y = 0;
    37cd:	45 31 f6             	xor    %r14d,%r14d
    37d0:	49 89 e4             	mov    %rsp,%r12
    if (y >= data->threads[0].task_count) {
    37d3:	31 db                	xor    %ebx,%ebx
    37d5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    37da:	48 89 ef             	mov    %rbp,%rdi
    37dd:	4c 89 e6             	mov    %r12,%rsi
    n++;
    37e0:	41 83 c5 01          	add    $0x1,%r13d
    nanosleep(&preempt , &rem2);
    37e4:	e8 47 eb ff ff       	call   2330 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    37e9:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    37ed:	41 8d 7e 01          	lea    0x1(%r14),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    37f1:	85 c0                	test   %eax,%eax
    37f3:	7e 59                	jle    384e <timer_thread+0xee>
        data->threads[x].tasks[y].scheduled = 0;
    37f5:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    37f9:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    37fd:	4d 8d 04 56          	lea    (%r14,%rdx,2),%r8
    3801:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3805:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3809:	49 c1 e0 03          	shl    $0x3,%r8
    380d:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    3811:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x].task_count;
    3818:	89 f8                	mov    %edi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    381a:	48 8b 71 20          	mov    0x20(%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    381e:	99                   	cltd
    381f:	f7 79 28             	idivl  0x28(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3822:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    3829:	48 63 d2             	movslq %edx,%rdx
    382c:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    3830:	48 8d 04 42          	lea    (%rdx,%rax,2),%rax
    3834:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
        data->threads[x].tasks[y].scheduled = 0;
    3838:	4c 01 c6             	add    %r8,%rsi
        data->threads[x].tasks[next].scheduled = 1;
    383b:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
        data->threads[x].tasks[y].scheduled = 0;
    3842:	c7 46 48 00 00 00 00 	movl   $0x0,0x48(%rsi)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3849:	4c 39 c9             	cmp    %r9,%rcx
    384c:	75 ca                	jne    3818 <timer_thread+0xb8>
    asm volatile ("mfence" ::: "memory");
    384e:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    3851:	49 8b 47 10          	mov    0x10(%r15),%rax
    3855:	39 78 28             	cmp    %edi,0x28(%rax)
  while (data->running && n < times) {
    3858:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    if (y >= data->threads[0].task_count) {
    385c:	0f 4e fb             	cmovle %ebx,%edi
    385f:	4c 63 f7             	movslq %edi,%r14
  while (data->running && n < times) {
    3862:	85 c0                	test   %eax,%eax
    3864:	74 0d                	je     3873 <timer_thread+0x113>
    3866:	41 81 fd 30 75 00 00 	cmp    $0x7530,%r13d
    386d:	0f 85 67 ff ff ff    	jne    37da <timer_thread+0x7a>
    3873:	48 8d 3d be 27 00 00 	lea    0x27be(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    387a:	e8 51 ea ff ff       	call   22d0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    387f:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3883:	85 d2                	test   %edx,%edx
    3885:	7e 5a                	jle    38e1 <timer_thread+0x181>
    for (int y = 0 ; y < data->task_count ; y++) {
    3887:	49 63 47 28          	movslq 0x28(%r15),%rax
    388b:	85 c0                	test   %eax,%eax
    388d:	7e 52                	jle    38e1 <timer_thread+0x181>
    388f:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
      data->threads[x].tasks[y].sending = 0;
    3893:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3897:	48 8d 3c 4a          	lea    (%rdx,%rcx,2),%rdi
    389b:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    389f:	31 c9                	xor    %ecx,%ecx
    38a1:	48 8d 34 50          	lea    (%rax,%rdx,2),%rsi
    38a5:	48 c1 e7 03          	shl    $0x3,%rdi
    38a9:	48 c1 e6 03          	shl    $0x3,%rsi
    for (int y = 0 ; y < data->task_count ; y++) {
    38ad:	49 8b 44 08 20       	mov    0x20(%r8,%rcx,1),%rax
    38b2:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    38b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      data->threads[x].tasks[y].sending = 0;
    38c0:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    38ca:	48 05 98 00 00 00    	add    $0x98,%rax
    38d0:	48 39 d0             	cmp    %rdx,%rax
    38d3:	75 eb                	jne    38c0 <timer_thread+0x160>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    38d5:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    38dc:	48 39 f9             	cmp    %rdi,%rcx
    38df:	75 cc                	jne    38ad <timer_thread+0x14d>
  asm volatile ("mfence" ::: "memory");
    38e1:	0f ae f0             	mfence
  struct timespec drain = {
    38e4:	66 0f 6f 05 54 30 00 00 	movdqa 0x3054(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    38ec:	48 8d 2d 6a 27 00 00 	lea    0x276a(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    38f3:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    38f8:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    38fc:	45 8d 6e 01          	lea    0x1(%r14),%r13d
    for (int x = 0 ; x < data->thread_count ; x++) {
    3900:	85 c0                	test   %eax,%eax
    3902:	7e 53                	jle    3957 <timer_thread+0x1f7>
        data->threads[x].tasks[y].scheduled = 0;
    3904:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    3908:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    390c:	49 8d 3c 56          	lea    (%r14,%rdx,2),%rdi
    3910:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3914:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3918:	48 c1 e7 03          	shl    $0x3,%rdi
    391c:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
        int next = (y + 1) % data->threads[x].task_count;
    3920:	44 89 e8             	mov    %r13d,%eax
        data->threads[x].tasks[next].scheduled = 1;
    3923:	48 8b 71 20          	mov    0x20(%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    3927:	99                   	cltd
    3928:	f7 79 28             	idivl  0x28(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    392b:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    3932:	48 63 c2             	movslq %edx,%rax
    3935:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3939:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    393d:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
        data->threads[x].tasks[y].scheduled = 0;
    3941:	48 01 fe             	add    %rdi,%rsi
        data->threads[x].tasks[next].scheduled = 1;
    3944:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
        data->threads[x].tasks[y].scheduled = 0;
    394b:	c7 46 48 00 00 00 00 	movl   $0x0,0x48(%rsi)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3952:	49 39 c8             	cmp    %rcx,%r8
    3955:	75 c9                	jne    3920 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    3957:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    395a:	49 8b 47 10          	mov    0x10(%r15),%rax
    395e:	44 39 68 28          	cmp    %r13d,0x28(%rax)
    3962:	7f 03                	jg     3967 <timer_thread+0x207>
      y = 0;
    3964:	45 31 ed             	xor    %r13d,%r13d
    for (int x = 0 ; x < data->thread_count ; x++) {
    3967:	45 8b 47 18          	mov    0x18(%r15),%r8d
    396b:	45 85 c0             	test   %r8d,%r8d
    396e:	0f 8e dd 00 00 00    	jle    3a51 <timer_thread+0x2f1>
    3974:	31 db                	xor    %ebx,%ebx
    3976:	45 31 e4             	xor    %r12d,%r12d
    int all_empty = 1;
    3979:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    397f:	90                   	nop
            all_empty = 0;
    3980:	45 31 f6             	xor    %r14d,%r14d
    3983:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        for (int k = 0 ; k < data->thread_count; k++) {
    3988:	45 85 c0             	test   %r8d,%r8d
    398b:	0f 8e 81 00 00 00    	jle    3a12 <timer_thread+0x2b2>
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3991:	49 8b 47 10          	mov    0x10(%r15),%rax
    3995:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    3999:	49 63 f8             	movslq %r8d,%rdi
    399c:	49 8d 14 56          	lea    (%r14,%rdx,2),%rdx
    39a0:	48 8b 44 18 20       	mov    0x20(%rax,%rbx,1),%rax
    39a5:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    39a9:	31 d2                	xor    %edx,%edx
    39ab:	eb 1e                	jmp    39cb <timer_thread+0x26b>
    39ad:	0f 1f 00             	nopl   (%rax)
    39b0:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    39b4:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    39b9:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    39bd:	48 85 f6             	test   %rsi,%rsi
    39c0:	7f 21                	jg     39e3 <timer_thread+0x283>
        for (int k = 0 ; k < data->thread_count; k++) {
    39c2:	48 83 c2 01          	add    $0x1,%rdx
    39c6:	48 39 d7             	cmp    %rdx,%rdi
    39c9:	74 47                	je     3a12 <timer_thread+0x2b2>
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    39cb:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    39cf:	48 89 d0             	mov    %rdx,%rax
    39d2:	48 c1 e0 05          	shl    $0x5,%rax
    39d6:	48 8b 34 06          	mov    (%rsi,%rax,1),%rsi
    39da:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    39de:	48 85 f6             	test   %rsi,%rsi
    39e1:	7e cd                	jle    39b0 <timer_thread+0x250>
            printf("%d %ld %ld left\n", k, ((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count, ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count);
    39e3:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    39e7:	bf 01 00 00 00       	mov    $0x1,%edi
    39ec:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    39f1:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    39f5:	48 8b 49 70          	mov    0x70(%rcx),%rcx
    39f9:	48 89 ee             	mov    %rbp,%rsi
    39fc:	48 8b 04 01          	mov    (%rcx,%rax,1),%rax
    3a00:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3a04:	31 c0                	xor    %eax,%eax
    3a06:	e8 25 ea ff ff       	call   2430 <__printf_chk@plt>
      for (int y = 0 ; y < data->thread_count ; y++) {
    3a0b:	45 8b 47 18          	mov    0x18(%r15),%r8d
            all_empty = 0;
    3a0f:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->thread_count ; y++) {
    3a12:	49 83 c6 01          	add    $0x1,%r14
    3a16:	45 39 f0             	cmp    %r14d,%r8d
    3a19:	0f 8f 69 ff ff ff    	jg     3988 <timer_thread+0x228>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a1f:	41 83 c4 01          	add    $0x1,%r12d
    3a23:	45 39 c4             	cmp    %r8d,%r12d
    3a26:	7d 0c                	jge    3a34 <timer_thread+0x2d4>
    3a28:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
      for (int y = 0 ; y < data->thread_count ; y++) {
    3a2f:	e9 4c ff ff ff       	jmp    3980 <timer_thread+0x220>
    if (all_empty == 1) {
    3a34:	41 83 f9 01          	cmp    $0x1,%r9d
    3a38:	74 17                	je     3a51 <timer_thread+0x2f1>
      nanosleep(&drain , &drainrem);
    3a3a:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3a3f:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3a44:	4d 63 f5             	movslq %r13d,%r14
    3a47:	e8 e4 e8 ff ff       	call   2330 <nanosleep@plt>
    3a4c:	e9 a7 fe ff ff       	jmp    38f8 <timer_thread+0x198>
    3a51:	48 8d 3d fc 25 00 00 	lea    0x25fc(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3a58:	48 8d 2d 21 26 00 00 	lea    0x2621(%rip),%rbp        # 6080 <_IO_stdin_used+0x80>
    3a5f:	e8 6c e8 ff ff       	call   22d0 <puts@plt>
  while (data->running) {
    3a64:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3a68:	48 8d 1d ff 25 00 00 	lea    0x25ff(%rip),%rbx        # 606e <_IO_stdin_used+0x6e>
    3a6f:	85 c0                	test   %eax,%eax
    3a71:	0f 84 b6 00 00 00    	je     3b2d <timer_thread+0x3cd>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3a77:	41 8b 57 1c          	mov    0x1c(%r15),%edx
    3a7b:	45 31 e4             	xor    %r12d,%r12d
    3a7e:	45 31 ed             	xor    %r13d,%r13d
    3a81:	85 d2                	test   %edx,%edx
    3a83:	7e 29                	jle    3aae <timer_thread+0x34e>
    3a85:	49 8b 4f 10          	mov    0x10(%r15),%rcx
      data->threads[x].running = 0;
    3a89:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
      if (data->threads[x].type == IO) {
    3a8d:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
      data->threads[x].running = 0;
    3a91:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
      if (data->threads[x].type == IO) {
    3a98:	0f 84 bc 00 00 00    	je     3b5a <timer_thread+0x3fa>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3a9e:	41 83 c5 01          	add    $0x1,%r13d
    3aa2:	49 81 c4 98 00 00 00 	add    $0x98,%r12
    3aa9:	41 39 d5             	cmp    %edx,%r13d
    3aac:	7c db                	jl     3a89 <timer_thread+0x329>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3aae:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3ab2:	85 d2                	test   %edx,%edx
    3ab4:	7e 58                	jle    3b0e <timer_thread+0x3ae>
      for (int y = 0 ; y < data->task_count ; y++) {
    3ab6:	49 63 47 28          	movslq 0x28(%r15),%rax
    3aba:	85 c0                	test   %eax,%eax
    3abc:	7e 50                	jle    3b0e <timer_thread+0x3ae>
    3abe:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
        data->threads[x].tasks[y].scheduled = 0;
    3ac2:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3ac6:	48 8d 3c 4a          	lea    (%rdx,%rcx,2),%rdi
    3aca:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3ace:	31 c9                	xor    %ecx,%ecx
    3ad0:	48 8d 34 50          	lea    (%rax,%rdx,2),%rsi
    3ad4:	48 c1 e7 03          	shl    $0x3,%rdi
    3ad8:	48 c1 e6 03          	shl    $0x3,%rsi
    3adc:	0f 1f 40 00          	nopl   0x0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3ae0:	49 8b 44 08 20       	mov    0x20(%r8,%rcx,1),%rax
    3ae5:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3ae9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x].tasks[y].scheduled = 0;
    3af0:	c7 40 48 00 00 00 00 	movl   $0x0,0x48(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3af7:	48 05 98 00 00 00    	add    $0x98,%rax
    3afd:	48 39 d0             	cmp    %rdx,%rax
    3b00:	75 ee                	jne    3af0 <timer_thread+0x390>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b02:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3b09:	48 39 f9             	cmp    %rdi,%rcx
    3b0c:	75 d2                	jne    3ae0 <timer_thread+0x380>
    asm volatile ("mfence" ::: "memory");
    3b0e:	0f ae f0             	mfence
    3b11:	48 89 ef             	mov    %rbp,%rdi
    3b14:	e8 b7 e7 ff ff       	call   22d0 <puts@plt>
    data->running = 0;
    3b19:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
  while (data->running) {
    3b21:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3b25:	85 c0                	test   %eax,%eax
    3b27:	0f 85 4a ff ff ff    	jne    3a77 <timer_thread+0x317>
    3b2d:	48 8d 3d 53 25 00 00 	lea    0x2553(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3b34:	e8 97 e7 ff ff       	call   22d0 <puts@plt>
}
    3b39:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3b3e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3b47:	75 49                	jne    3b92 <timer_thread+0x432>
    3b49:	48 83 c4 58          	add    $0x58,%rsp
    3b4d:	31 c0                	xor    %eax,%eax
    3b4f:	5b                   	pop    %rbx
    3b50:	5d                   	pop    %rbp
    3b51:	41 5c                	pop    %r12
    3b53:	41 5d                	pop    %r13
    3b55:	41 5e                	pop    %r14
    3b57:	41 5f                	pop    %r15
    3b59:	c3                   	ret
    3b5a:	48 89 df             	mov    %rbx,%rdi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b5d:	41 83 c5 01          	add    $0x1,%r13d
    3b61:	e8 6a e7 ff ff       	call   22d0 <puts@plt>
        eventfd_write(data->threads[x]._eventfd, 1);
    3b66:	49 8b 47 10          	mov    0x10(%r15),%rax
    3b6a:	be 01 00 00 00       	mov    $0x1,%esi
    3b6f:	42 8b 7c 20 48       	mov    0x48(%rax,%r12,1),%edi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b74:	49 81 c4 98 00 00 00 	add    $0x98,%r12
        eventfd_write(data->threads[x]._eventfd, 1);
    3b7b:	e8 60 e8 ff ff       	call   23e0 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b80:	41 8b 57 1c          	mov    0x1c(%r15),%edx
    3b84:	41 39 d5             	cmp    %edx,%r13d
    3b87:	0f 8c f8 fe ff ff    	jl     3a85 <timer_thread+0x325>
    3b8d:	e9 1c ff ff ff       	jmp    3aae <timer_thread+0x34e>
}
    3b92:	e8 79 e7 ff ff       	call   2310 <__stack_chk_fail@plt>
    3b97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000003ba0 <fatal_error>:
void fatal_error(const char *syscall) {
    3ba0:	f3 0f 1e fa          	endbr64
    3ba4:	50                   	push   %rax
    3ba5:	58                   	pop    %rax
    3ba6:	48 83 ec 08          	sub    $0x8,%rsp
    perror(syscall);
    3baa:	e8 c1 e8 ff ff       	call   2470 <perror@plt>
    exit(1);
    3baf:	bf 01 00 00 00       	mov    $0x1,%edi
    3bb4:	e8 c7 e8 ff ff       	call   2480 <exit@plt>
    3bb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003bc0 <strtolower>:
void strtolower(char *str) {
    3bc0:	f3 0f 1e fa          	endbr64
    3bc4:	55                   	push   %rbp
    3bc5:	53                   	push   %rbx
    3bc6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3bca:	48 0f be 1f          	movsbq (%rdi),%rbx
    3bce:	84 db                	test   %bl,%bl
    3bd0:	74 24                	je     3bf6 <strtolower+0x36>
    3bd2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3bd5:	e8 16 e9 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3bda:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3be0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3be3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3be7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3bea:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3bed:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3bf2:	84 db                	test   %bl,%bl
    3bf4:	75 ea                	jne    3be0 <strtolower+0x20>
}
    3bf6:	48 83 c4 08          	add    $0x8,%rsp
    3bfa:	5b                   	pop    %rbx
    3bfb:	5d                   	pop    %rbp
    3bfc:	c3                   	ret
    3bfd:	0f 1f 00             	nopl   (%rax)

0000000000003c00 <zh_malloc>:
void *zh_malloc(size_t size) {
    3c00:	f3 0f 1e fa          	endbr64
    3c04:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3c08:	e8 e3 e7 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3c0d:	48 85 c0             	test   %rax,%rax
    3c10:	74 05                	je     3c17 <zh_malloc+0x17>
}
    3c12:	48 83 c4 08          	add    $0x8,%rsp
    3c16:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3c17:	48 8b 0d 02 54 00 00 	mov    0x5402(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3c1e:	ba 28 00 00 00       	mov    $0x28,%edx
    3c23:	be 01 00 00 00       	mov    $0x1,%esi
    3c28:	48 8d 3d 11 28 00 00 	lea    0x2811(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    3c2f:	e8 6c e8 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    3c34:	bf 01 00 00 00       	mov    $0x1,%edi
    3c39:	e8 42 e8 ff ff       	call   2480 <exit@plt>
    3c3e:	66 90                	xchg   %ax,%ax

0000000000003c40 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3c40:	f3 0f 1e fa          	endbr64
    3c44:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    3c45:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3c4a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3c4d:	e8 ee e6 ff ff       	call   2340 <strrchr@plt>
    if (!dot || dot == filename)
    3c52:	48 85 c0             	test   %rax,%rax
    3c55:	74 11                	je     3c68 <get_filename_ext+0x28>
    3c57:	48 39 c3             	cmp    %rax,%rbx
    3c5a:	74 0c                	je     3c68 <get_filename_ext+0x28>
    return dot + 1;
    3c5c:	48 83 c0 01          	add    $0x1,%rax
}
    3c60:	5b                   	pop    %rbx
    3c61:	c3                   	ret
    3c62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    3c68:	48 8d 05 60 24 00 00 	lea    0x2460(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
}
    3c6f:	5b                   	pop    %rbx
    3c70:	c3                   	ret
    3c71:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3c7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003c80 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3c80:	f3 0f 1e fa          	endbr64
    3c84:	41 55                	push   %r13
    3c86:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3c89:	48 89 fe             	mov    %rdi,%rsi
    3c8c:	41 54                	push   %r12
    3c8e:	55                   	push   %rbp
    3c8f:	48 89 d5             	mov    %rdx,%rbp
    3c92:	ba 00 04 00 00       	mov    $0x400,%edx
    3c97:	53                   	push   %rbx
    3c98:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3c9f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3ca8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3cb0:	31 c0                	xor    %eax,%eax
    3cb2:	49 89 e4             	mov    %rsp,%r12
    3cb5:	4c 89 e7             	mov    %r12,%rdi
    3cb8:	e8 53 e7 ff ff       	call   2410 <__strcpy_chk@plt>
    for (; *str; ++str)
    3cbd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3cc2:	84 db                	test   %bl,%bl
    3cc4:	74 24                	je     3cea <send_headers+0x6a>
        *str = (char)tolower(*str);
    3cc6:	e8 25 e8 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3ccb:	48 8b 08             	mov    (%rax),%rcx
    3cce:	4c 89 e0             	mov    %r12,%rax
    3cd1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3cd8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3cdb:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3cdf:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3ce2:	48 0f be 18          	movsbq (%rax),%rbx
    3ce6:	84 db                	test   %bl,%bl
    3ce8:	75 ee                	jne    3cd8 <send_headers+0x58>
    void *buf = malloc(size);
    3cea:	bf 11 00 00 00       	mov    $0x11,%edi
    3cef:	e8 fc e6 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3cf4:	48 85 c0             	test   %rax,%rax
    3cf7:	0f 84 7e 04 00 00    	je     417b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3cfd:	66 0f 6f 05 4b 2c 00 00 	movdqa 0x2c4b(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    iov[0].iov_base = zh_malloc(slen);
    3d05:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    3d09:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3d0e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3d16:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3d1a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3d1d:	e8 ce e6 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3d22:	48 85 c0             	test   %rax,%rax
    3d25:	0f 84 50 04 00 00    	je     417b <send_headers+0x4fb>
    3d2b:	66 0f 6f 05 2d 2c 00 00 	movdqa 0x2c2d(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    iov[1].iov_base = zh_malloc(slen);
    3d33:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    3d37:	4c 89 e7             	mov    %r12,%rdi
    3d3a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3d44:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3d4c:	0f 11 00             	movups %xmm0,(%rax)
    3d4f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3d53:	be 2e 00 00 00       	mov    $0x2e,%esi
    3d58:	e8 e3 e5 ff ff       	call   2340 <strrchr@plt>
    if (!dot || dot == filename)
    3d5d:	48 85 c0             	test   %rax,%rax
    3d60:	0f 84 ea 02 00 00    	je     4050 <send_headers+0x3d0>
    3d66:	4c 39 e0             	cmp    %r12,%rax
    3d69:	0f 84 e1 02 00 00    	je     4050 <send_headers+0x3d0>
    return dot + 1;
    3d6f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3d73:	48 8d 3d 23 23 00 00 	lea    0x2323(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3d7a:	48 89 de             	mov    %rbx,%rsi
    3d7d:	e8 0e e6 ff ff       	call   2390 <strcmp@plt>
    3d82:	85 c0                	test   %eax,%eax
    3d84:	75 20                	jne    3da6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3d86:	66 0f 6f 05 e2 2b 00 00 	movdqa 0x2be2(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    3d8e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3d96:	66 0f 6f 05 e2 2b 00 00 	movdqa 0x2be2(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    3d9e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    3da6:	48 89 de             	mov    %rbx,%rsi
    3da9:	48 8d 3d f1 22 00 00 	lea    0x22f1(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3db0:	e8 db e5 ff ff       	call   2390 <strcmp@plt>
    3db5:	85 c0                	test   %eax,%eax
    3db7:	75 20                	jne    3dd9 <send_headers+0x159>
    3db9:	66 0f 6f 05 af 2b 00 00 	movdqa 0x2baf(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    3dc1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3dc9:	66 0f 6f 05 af 2b 00 00 	movdqa 0x2baf(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    3dd1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    3dd9:	48 89 de             	mov    %rbx,%rsi
    3ddc:	48 8d 3d c3 22 00 00 	lea    0x22c3(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3de3:	e8 a8 e5 ff ff       	call   2390 <strcmp@plt>
    3de8:	85 c0                	test   %eax,%eax
    3dea:	0f 84 10 02 00 00    	je     4000 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    3df0:	48 89 de             	mov    %rbx,%rsi
    3df3:	48 8d 3d b0 22 00 00 	lea    0x22b0(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3dfa:	e8 91 e5 ff ff       	call   2390 <strcmp@plt>
    3dff:	85 c0                	test   %eax,%eax
    3e01:	0f 84 a9 02 00 00    	je     40b0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    3e07:	48 89 de             	mov    %rbx,%rsi
    3e0a:	48 8d 3d 9d 22 00 00 	lea    0x229d(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3e11:	e8 7a e5 ff ff       	call   2390 <strcmp@plt>
    3e16:	85 c0                	test   %eax,%eax
    3e18:	0f 84 6a 02 00 00    	je     4088 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    3e1e:	48 89 de             	mov    %rbx,%rsi
    3e21:	48 8d 3d c9 22 00 00 	lea    0x22c9(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3e28:	e8 63 e5 ff ff       	call   2390 <strcmp@plt>
    3e2d:	85 c0                	test   %eax,%eax
    3e2f:	0f 84 2b 02 00 00    	je     4060 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    3e35:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3e38:	0f 84 52 01 00 00    	je     3f90 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    3e3e:	48 89 de             	mov    %rbx,%rsi
    3e41:	48 8d 3d 6a 22 00 00 	lea    0x226a(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3e48:	e8 43 e5 ff ff       	call   2390 <strcmp@plt>
    3e4d:	85 c0                	test   %eax,%eax
    3e4f:	0f 84 ab 02 00 00    	je     4100 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    3e55:	48 89 de             	mov    %rbx,%rsi
    3e58:	48 8d 3d 57 22 00 00 	lea    0x2257(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3e5f:	e8 2c e5 ff ff       	call   2390 <strcmp@plt>
    3e64:	85 c0                	test   %eax,%eax
    3e66:	0f 84 6c 02 00 00    	je     40d8 <send_headers+0x458>
    slen = strlen(send_buffer);
    3e6c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3e74:	4c 89 e7             	mov    %r12,%rdi
    3e77:	e8 84 e4 ff ff       	call   2300 <strlen@plt>
    void *buf = malloc(size);
    3e7c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3e7f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3e82:	e8 69 e5 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3e87:	48 85 c0             	test   %rax,%rax
    3e8a:	0f 84 eb 02 00 00    	je     417b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    3e90:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    3e94:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    3e98:	83 fb 08             	cmp    $0x8,%ebx
    3e9b:	0f 83 3f 01 00 00    	jae    3fe0 <send_headers+0x360>
    3ea1:	f6 c3 04             	test   $0x4,%bl
    3ea4:	0f 85 7b 02 00 00    	jne    4125 <send_headers+0x4a5>
    3eaa:	85 db                	test   %ebx,%ebx
    3eac:	74 13                	je     3ec1 <send_headers+0x241>
    3eae:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3eb6:	88 10                	mov    %dl,(%rax)
    3eb8:	f6 c3 02             	test   $0x2,%bl
    3ebb:	0f 85 96 02 00 00    	jne    4157 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3ec1:	4d 89 e8             	mov    %r13,%r8
    3ec4:	48 8d 0d ef 21 00 00 	lea    0x21ef(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    3ecb:	4c 89 e7             	mov    %r12,%rdi
    3ece:	31 c0                	xor    %eax,%eax
    3ed0:	ba 00 04 00 00       	mov    $0x400,%edx
    3ed5:	be 01 00 00 00       	mov    $0x1,%esi
    3eda:	e8 21 e6 ff ff       	call   2500 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    3edf:	4c 89 e7             	mov    %r12,%rdi
    3ee2:	e8 19 e4 ff ff       	call   2300 <strlen@plt>
    void *buf = malloc(size);
    3ee7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3eea:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3eed:	e8 fe e4 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3ef2:	48 85 c0             	test   %rax,%rax
    3ef5:	0f 84 80 02 00 00    	je     417b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    3efb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    3eff:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    3f03:	83 fb 08             	cmp    $0x8,%ebx
    3f06:	0f 83 1c 01 00 00    	jae    4028 <send_headers+0x3a8>
    3f0c:	f6 c3 04             	test   $0x4,%bl
    3f0f:	0f 85 29 02 00 00    	jne    413e <send_headers+0x4be>
    3f15:	85 db                	test   %ebx,%ebx
    3f17:	74 13                	je     3f2c <send_headers+0x2ac>
    3f19:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3f21:	88 10                	mov    %dl,(%rax)
    3f23:	f6 c3 02             	test   $0x2,%bl
    3f26:	0f 85 3d 02 00 00    	jne    4169 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3f2c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    3f31:	bf 02 00 00 00       	mov    $0x2,%edi
    3f36:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    3f3e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    3f46:	e8 a5 e4 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3f4b:	48 85 c0             	test   %rax,%rax
    3f4e:	0f 84 27 02 00 00    	je     417b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3f54:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    3f5c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    3f60:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    3f68:	66 89 10             	mov    %dx,(%rax)
}
    3f6b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    3f73:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3f7c:	0f 85 20 02 00 00    	jne    41a2 <send_headers+0x522>
    3f82:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    3f89:	5b                   	pop    %rbx
    3f8a:	5d                   	pop    %rbp
    3f8b:	41 5c                	pop    %r12
    3f8d:	41 5d                	pop    %r13
    3f8f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    3f90:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    3f94:	0f 85 a4 fe ff ff    	jne    3e3e <send_headers+0x1be>
    3f9a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    3f9e:	0f 85 9a fe ff ff    	jne    3e3e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3fa4:	66 0f 6f 05 24 2a 00 00 	movdqa 0x2a24(%rip),%xmm0        # 69d0 <_IO_stdin_used+0x9d0>
    3fac:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    3fb6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3fbe:	66 0f 6f 05 1a 2a 00 00 	movdqa 0x2a1a(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
    3fc6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    3fce:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    3fd6:	e9 63 fe ff ff       	jmp    3e3e <send_headers+0x1be>
    3fdb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    3fe0:	89 da                	mov    %ebx,%edx
    3fe2:	48 89 c7             	mov    %rax,%rdi
    3fe5:	4c 89 e6             	mov    %r12,%rsi
    3fe8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    3fed:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    3ff2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3ff5:	c1 e9 03             	shr    $0x3,%ecx
    3ff8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    3ffb:	e9 c1 fe ff ff       	jmp    3ec1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4000:	66 0f 6f 05 68 29 00 00 	movdqa 0x2968(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4008:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4010:	66 0f 6f 05 78 29 00 00 	movdqa 0x2978(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    4018:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4020:	e9 cb fd ff ff       	jmp    3df0 <send_headers+0x170>
    4025:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4028:	89 da                	mov    %ebx,%edx
    402a:	48 89 c7             	mov    %rax,%rdi
    402d:	4c 89 e6             	mov    %r12,%rsi
    4030:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4035:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    403a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    403d:	c1 e9 03             	shr    $0x3,%ecx
    4040:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4043:	e9 e4 fe ff ff       	jmp    3f2c <send_headers+0x2ac>
    4048:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4050:	48 8d 1d 78 20 00 00 	lea    0x2078(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    4057:	e9 94 fd ff ff       	jmp    3df0 <send_headers+0x170>
    405c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4060:	66 0f 6f 05 48 29 00 00 	movdqa 0x2948(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    4068:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4070:	66 0f 6f 05 48 29 00 00 	movdqa 0x2948(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4078:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4080:	e9 b0 fd ff ff       	jmp    3e35 <send_headers+0x1b5>
    4085:	0f 1f 00             	nopl   (%rax)
    4088:	66 0f 6f 05 20 29 00 00 	movdqa 0x2920(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    4090:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4098:	66 0f 6f 05 20 29 00 00 	movdqa 0x2920(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    40a0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40a8:	e9 71 fd ff ff       	jmp    3e1e <send_headers+0x19e>
    40ad:	0f 1f 00             	nopl   (%rax)
    40b0:	66 0f 6f 05 b8 28 00 00 	movdqa 0x28b8(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    40b8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40c0:	66 0f 6f 05 d8 28 00 00 	movdqa 0x28d8(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    40c8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40d0:	e9 32 fd ff ff       	jmp    3e07 <send_headers+0x187>
    40d5:	0f 1f 00             	nopl   (%rax)
    40d8:	66 0f 6f 05 d0 28 00 00 	movdqa 0x28d0(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    40e0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40e8:	66 0f 6f 05 10 29 00 00 	movdqa 0x2910(%rip),%xmm0        # 6a00 <_IO_stdin_used+0xa00>
    40f0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    40f8:	e9 6f fd ff ff       	jmp    3e6c <send_headers+0x1ec>
    40fd:	0f 1f 00             	nopl   (%rax)
    4100:	66 0f 6f 05 a8 28 00 00 	movdqa 0x28a8(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    4108:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4110:	66 0f 6f 05 d8 28 00 00 	movdqa 0x28d8(%rip),%xmm0        # 69f0 <_IO_stdin_used+0x9f0>
    4118:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4120:	e9 30 fd ff ff       	jmp    3e55 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4125:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    412c:	89 db                	mov    %ebx,%ebx
    412e:	89 10                	mov    %edx,(%rax)
    4130:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4135:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4139:	e9 83 fd ff ff       	jmp    3ec1 <send_headers+0x241>
    413e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4145:	89 db                	mov    %ebx,%ebx
    4147:	89 10                	mov    %edx,(%rax)
    4149:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    414e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4152:	e9 d5 fd ff ff       	jmp    3f2c <send_headers+0x2ac>
    4157:	89 db                	mov    %ebx,%ebx
    4159:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    415f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4164:	e9 58 fd ff ff       	jmp    3ec1 <send_headers+0x241>
    4169:	89 db                	mov    %ebx,%ebx
    416b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4171:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4176:	e9 b1 fd ff ff       	jmp    3f2c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    417b:	48 8b 0d 9e 4e 00 00 	mov    0x4e9e(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4182:	ba 28 00 00 00       	mov    $0x28,%edx
    4187:	be 01 00 00 00       	mov    $0x1,%esi
    418c:	48 8d 3d ad 22 00 00 	lea    0x22ad(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    4193:	e8 08 e3 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    4198:	bf 01 00 00 00       	mov    $0x1,%edi
    419d:	e8 de e2 ff ff       	call   2480 <exit@plt>
}
    41a2:	e8 69 e1 ff ff       	call   2310 <__stack_chk_fail@plt>
    41a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000041b0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    41b0:	f3 0f 1e fa          	endbr64
    41b4:	41 55                	push   %r13
    41b6:	49 89 d5             	mov    %rdx,%r13
    41b9:	41 54                	push   %r12
    41bb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    41be:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    41c1:	55                   	push   %rbp
    41c2:	53                   	push   %rbx
    41c3:	48 89 f3             	mov    %rsi,%rbx
    41c6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    41ca:	e8 21 e2 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    41cf:	48 85 c0             	test   %rax,%rax
    41d2:	74 77                	je     424b <copy_file_contents+0x9b>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    41d4:	4c 89 e7             	mov    %r12,%rdi
    41d7:	48 89 c5             	mov    %rax,%rbp
    41da:	31 f6                	xor    %esi,%esi
    41dc:	31 c0                	xor    %eax,%eax
    41de:	e8 7d e2 ff ff       	call   2460 <open@plt>
    41e3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    41e6:	85 c0                	test   %eax,%eax
    41e8:	78 55                	js     423f <copy_file_contents+0x8f>
		       "the destination buffer");

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    41ea:	48 89 da             	mov    %rbx,%rdx
    41ed:	48 89 ee             	mov    %rbp,%rsi
    41f0:	89 c7                	mov    %eax,%edi
    41f2:	e8 79 e1 ff ff       	call   2370 <read@plt>
    if (ret < file_size) {
    41f7:	48 98                	cltq
    41f9:	48 39 d8             	cmp    %rbx,%rax
    41fc:	7c 22                	jl     4220 <copy_file_contents+0x70>
    close(fd);
    41fe:	44 89 e7             	mov    %r12d,%edi
    4201:	e8 4a e1 ff ff       	call   2350 <close@plt>
    iov->iov_base = buf;
    4206:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    420a:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    420e:	48 83 c4 08          	add    $0x8,%rsp
    4212:	5b                   	pop    %rbx
    4213:	5d                   	pop    %rbp
    4214:	41 5c                	pop    %r12
    4216:	41 5d                	pop    %r13
    4218:	c3                   	ret
    4219:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4220:	48 8b 0d f9 4d 00 00 	mov    0x4df9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4227:	ba 1a 00 00 00       	mov    $0x1a,%edx
    422c:	be 01 00 00 00       	mov    $0x1,%esi
    4231:	48 8d 3d 98 1e 00 00 	lea    0x1e98(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    4238:	e8 63 e2 ff ff       	call   24a0 <fwrite@plt>
    423d:	eb bf                	jmp    41fe <copy_file_contents+0x4e>
        fatal_error("read");
    423f:	48 8d 3d b9 1f 00 00 	lea    0x1fb9(%rip),%rdi        # 61ff <_IO_stdin_used+0x1ff>
    4246:	e8 55 f9 ff ff       	call   3ba0 <fatal_error>
    424b:	48 8b 0d ce 4d 00 00 	mov    0x4dce(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4252:	ba 28 00 00 00       	mov    $0x28,%edx
    4257:	be 01 00 00 00       	mov    $0x1,%esi
    425c:	48 8d 3d dd 21 00 00 	lea    0x21dd(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    4263:	e8 38 e2 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    4268:	bf 01 00 00 00       	mov    $0x1,%edi
    426d:	e8 0e e2 ff ff       	call   2480 <exit@plt>
    4272:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    427d:	0f 1f 00             	nopl   (%rax)

0000000000004280 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4280:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
static inline struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4284:	8b 46 44             	mov    0x44(%rsi),%eax
    4287:	48 89 fa             	mov    %rdi,%rdx
    428a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    428d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4293:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4296:	48 8b 07             	mov    (%rdi),%rax
    4299:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    429c:	f6 c1 02             	test   $0x2,%cl
    429f:	74 00                	je     42a1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    42a1:	89 f0                	mov    %esi,%eax
    42a3:	44 29 c0             	sub    %r8d,%eax
    42a6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    42a9:	0f 82 71 e2 ff ff    	jb     2520 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    42af:	c1 e9 0a             	shr    $0xa,%ecx
    42b2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    42b6:	8b 47 44             	mov    0x44(%rdi),%eax
    42b9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    42bc:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    42bf:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    42c2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    42c5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    42c9:	d3 e0                	shl    %cl,%eax
    42cb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    42ce:	48 c1 e0 06          	shl    $0x6,%rax
    42d2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    42d6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    42dc:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    42df:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    42e3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    42e9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    42f1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    42f5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    42f8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    42ff:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4307:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    430b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    430f:	e8 0c e0 ff ff       	call   2320 <io_uring_submit@plt>
}
    4314:	31 c0                	xor    %eax,%eax
    4316:	48 83 c4 08          	add    $0x8,%rsp
    431a:	c3                   	ret
    431b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004320 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4320:	f3 0f 1e fa          	endbr64
    4324:	41 55                	push   %r13
    4326:	41 89 fd             	mov    %edi,%r13d
    4329:	41 54                	push   %r12
    432b:	55                   	push   %rbp
    432c:	53                   	push   %rbx
    432d:	48 89 f3             	mov    %rsi,%rbx
    4330:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4334:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4337:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    433d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4340:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4343:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4345:	f6 c1 02             	test   $0x2,%cl
    4348:	74 00                	je     434a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    434a:	89 c2                	mov    %eax,%edx
    434c:	29 f2                	sub    %esi,%edx
    434e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4351:	0f 82 d9 e1 ff ff    	jb     2530 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4357:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    435a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    435d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4360:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    4365:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4368:	23 6b 58             	and    0x58(%rbx),%ebp
    436b:	d3 e5                	shl    %cl,%ebp
    436d:	48 c1 e5 06          	shl    $0x6,%rbp
    4371:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4375:	e8 76 e0 ff ff       	call   23f0 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    437a:	be 01 00 00 00       	mov    $0x1,%esi
    437f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4384:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4387:	e8 f4 df ff ff       	call   2380 <calloc@plt>
    req->client_socket = client_socket;
    438c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4391:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4395:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4398:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    439d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    43a2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    43ab:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    43b3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    43b7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    43bb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    43c2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    43ca:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    43ce:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    43d6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    43de:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    43e2:	e8 39 df ff ff       	call   2320 <io_uring_submit@plt>
}
    43e7:	48 83 c4 08          	add    $0x8,%rsp
    43eb:	31 c0                	xor    %eax,%eax
    43ed:	5b                   	pop    %rbx
    43ee:	5d                   	pop    %rbp
    43ef:	41 5c                	pop    %r12
    43f1:	41 5d                	pop    %r13
    43f3:	c3                   	ret
    43f4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    43ff:	90                   	nop

0000000000004400 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4400:	f3 0f 1e fa          	endbr64
    4404:	41 56                	push   %r14
    4406:	41 89 f6             	mov    %esi,%r14d
    4409:	41 55                	push   %r13
    440b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    440e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4413:	41 54                	push   %r12
    4415:	55                   	push   %rbp
    4416:	48 89 d5             	mov    %rdx,%rbp
    4419:	53                   	push   %rbx
    void *buf = malloc(size);
    441a:	e8 d1 df ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    441f:	48 85 c0             	test   %rax,%rax
    4422:	0f 84 dd 00 00 00    	je     4505 <_send_static_string_content+0x105>
    4428:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    442b:	4c 89 ef             	mov    %r13,%rdi
    442e:	e8 cd de ff ff       	call   2300 <strlen@plt>
    req->iovec_count = 1;
    4433:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    443a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    443e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4441:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4444:	e8 a7 df ff ff       	call   23f0 <malloc@plt>
    4449:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    444c:	48 85 c0             	test   %rax,%rax
    444f:	0f 84 b0 00 00 00    	je     4505 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4455:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4459:	4c 89 e2             	mov    %r12,%rdx
    445c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    445f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4463:	e8 58 df ff ff       	call   23c0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    4468:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    446b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4471:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4474:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4478:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    447a:	f6 c1 02             	test   $0x2,%cl
    447d:	0f 85 7d 00 00 00    	jne    4500 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4483:	89 d0                	mov    %edx,%eax
    4485:	29 f0                	sub    %esi,%eax
    4487:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    448a:	0f 82 aa e0 ff ff    	jb     253a <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4490:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4493:	8b 45 44             	mov    0x44(%rbp),%eax
    4496:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4499:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    449c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    449f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    44a2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    44a8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    44ac:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    44ae:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    44b1:	48 89 ef             	mov    %rbp,%rdi
    44b4:	48 c1 e0 06          	shl    $0x6,%rax
    44b8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    44bc:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    44bf:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    44c3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    44c9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    44d1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    44d5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    44d8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    44df:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    44e7:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    44eb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    44ef:	5b                   	pop    %rbx
    44f0:	5d                   	pop    %rbp
    44f1:	41 5c                	pop    %r12
    44f3:	41 5d                	pop    %r13
    44f5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    44f7:	e9 24 de ff ff       	jmp    2320 <io_uring_submit@plt>
    44fc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4500:	e9 7e ff ff ff       	jmp    4483 <_send_static_string_content+0x83>
    4505:	48 8b 0d 14 4b 00 00 	mov    0x4b14(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    450c:	ba 28 00 00 00       	mov    $0x28,%edx
    4511:	be 01 00 00 00       	mov    $0x1,%esi
    4516:	48 8d 3d 23 1f 00 00 	lea    0x1f23(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    451d:	e8 7e df ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    4522:	bf 01 00 00 00       	mov    $0x1,%edi
    4527:	e8 54 df ff ff       	call   2480 <exit@plt>
    452c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004530 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4530:	f3 0f 1e fa          	endbr64
    4534:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4537:	89 fe                	mov    %edi,%esi
    4539:	48 8b 3d d8 4a 00 00 	mov    0x4ad8(%rip),%rdi        # 9018 <unimplemented_content>
    4540:	e9 bb fe ff ff       	jmp    4400 <_send_static_string_content>
    4545:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004550 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4550:	f3 0f 1e fa          	endbr64
    4554:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4557:	89 fe                	mov    %edi,%esi
    4559:	48 8b 3d b0 4a 00 00 	mov    0x4ab0(%rip),%rdi        # 9010 <http_404_content>
    4560:	e9 9b fe ff ff       	jmp    4400 <_send_static_string_content>
    4565:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004570 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4570:	f3 0f 1e fa          	endbr64
    4574:	41 56                	push   %r14
    4576:	41 55                	push   %r13
    4578:	49 89 d5             	mov    %rdx,%r13
    457b:	41 54                	push   %r12
    457d:	41 89 f4             	mov    %esi,%r12d
    4580:	55                   	push   %rbp
    4581:	48 89 fd             	mov    %rdi,%rbp
    4584:	53                   	push   %rbx
    4585:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    458c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4595:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    459d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    459f:	e8 5c dd ff ff       	call   2300 <strlen@plt>
    45a4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    45a9:	48 89 c3             	mov    %rax,%rbx
    45ac:	0f 84 b6 00 00 00    	je     4668 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    45b2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    45b7:	48 89 ee             	mov    %rbp,%rsi
    45ba:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    45be:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    45c3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    45cb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    45d3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    45de:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    45e6:	e8 b5 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    45eb:	48 89 e6             	mov    %rsp,%rsi
    45ee:	4c 89 f7             	mov    %r14,%rdi
    45f1:	e8 ba dd ff ff       	call   23b0 <stat@plt>
    45f6:	83 f8 ff             	cmp    $0xffffffff,%eax
    45f9:	0f 84 d3 00 00 00    	je     46d2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    45ff:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4603:	25 00 f0 00 00       	and    $0xf000,%eax
    4608:	3d 00 80 00 00       	cmp    $0x8000,%eax
    460d:	0f 84 f5 00 00 00    	je     4708 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4613:	48 8b 3d f6 49 00 00 	mov    0x49f6(%rip),%rdi        # 9010 <http_404_content>
    461a:	4c 89 ea             	mov    %r13,%rdx
    461d:	44 89 e6             	mov    %r12d,%esi
    4620:	e8 db fd ff ff       	call   4400 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4625:	4c 89 f2             	mov    %r14,%rdx
    4628:	bf 01 00 00 00       	mov    $0x1,%edi
    462d:	31 c0                	xor    %eax,%eax
    462f:	48 8d 35 ea 1a 00 00 	lea    0x1aea(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    4636:	e8 f5 dd ff ff       	call   2430 <__printf_chk@plt>
}
    463b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4643:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    464c:	0f 85 20 01 00 00    	jne    4772 <handle_get_method+0x202>
    4652:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4659:	5b                   	pop    %rbx
    465a:	5d                   	pop    %rbp
    465b:	41 5c                	pop    %r12
    465d:	41 5d                	pop    %r13
    465f:	41 5e                	pop    %r14
    4661:	c3                   	ret
    4662:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4668:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    466d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4675:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    467a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    467d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4685:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4688:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4690:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    469b:	e8 00 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    46a0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    46a5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    46aa:	48 8d 35 3a 1a 00 00 	lea    0x1a3a(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    46b1:	48 29 d9             	sub    %rbx,%rcx
    46b4:	ba 0b 00 00 00       	mov    $0xb,%edx
    46b9:	e8 e2 dc ff ff       	call   23a0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    46be:	48 89 e6             	mov    %rsp,%rsi
    46c1:	4c 89 f7             	mov    %r14,%rdi
    46c4:	e8 e7 dc ff ff       	call   23b0 <stat@plt>
    46c9:	83 f8 ff             	cmp    $0xffffffff,%eax
    46cc:	0f 85 2d ff ff ff    	jne    45ff <handle_get_method+0x8f>
    46d2:	4c 89 f2             	mov    %r14,%rdx
    46d5:	48 89 e9             	mov    %rbp,%rcx
    46d8:	48 8d 35 17 1a 00 00 	lea    0x1a17(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    46df:	31 c0                	xor    %eax,%eax
    46e1:	bf 01 00 00 00       	mov    $0x1,%edi
    46e6:	e8 45 dd ff ff       	call   2430 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    46eb:	48 8b 3d 1e 49 00 00 	mov    0x491e(%rip),%rdi        # 9010 <http_404_content>
    46f2:	4c 89 ea             	mov    %r13,%rdx
    46f5:	44 89 e6             	mov    %r12d,%esi
    46f8:	e8 03 fd ff ff       	call   4400 <_send_static_string_content>
}
    46fd:	e9 39 ff ff ff       	jmp    463b <handle_get_method+0xcb>
    4702:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4708:	bf 70 00 00 00       	mov    $0x70,%edi
    470d:	e8 de dc ff ff       	call   23f0 <malloc@plt>
    4712:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4715:	48 85 c0             	test   %rax,%rax
    4718:	74 5d                	je     4777 <handle_get_method+0x207>
            req->client_socket = client_socket;
    471a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    471e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4723:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4727:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    472a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4731:	e8 4a f5 ff ff       	call   3c80 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4736:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    473b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    473f:	4c 89 f7             	mov    %r14,%rdi
    4742:	e8 69 fa ff ff       	call   41b0 <copy_file_contents>
    4747:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    474c:	4c 89 f2             	mov    %r14,%rdx
    474f:	31 c0                	xor    %eax,%eax
    4751:	48 8d 35 b6 19 00 00 	lea    0x19b6(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    4758:	bf 01 00 00 00       	mov    $0x1,%edi
    475d:	e8 ce dc ff ff       	call   2430 <__printf_chk@plt>
            add_write_request(req, ring);
    4762:	4c 89 ee             	mov    %r13,%rsi
    4765:	48 89 df             	mov    %rbx,%rdi
    4768:	e8 13 fb ff ff       	call   4280 <add_write_request>
    476d:	e9 c9 fe ff ff       	jmp    463b <handle_get_method+0xcb>
}
    4772:	e8 99 db ff ff       	call   2310 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4777:	48 8b 0d a2 48 00 00 	mov    0x48a2(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    477e:	ba 28 00 00 00       	mov    $0x28,%edx
    4783:	be 01 00 00 00       	mov    $0x1,%esi
    4788:	48 8d 3d b1 1c 00 00 	lea    0x1cb1(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    478f:	e8 0c dd ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    4794:	bf 01 00 00 00       	mov    $0x1,%edi
    4799:	e8 e2 dc ff ff       	call   2480 <exit@plt>
    479e:	66 90                	xchg   %ax,%ax

00000000000047a0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    47a0:	f3 0f 1e fa          	endbr64
    47a4:	41 57                	push   %r15
    47a6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    47a8:	4c 8d 35 d6 18 00 00 	lea    0x18d6(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    47af:	41 55                	push   %r13
    47b1:	49 89 d5             	mov    %rdx,%r13
    47b4:	41 54                	push   %r12
    47b6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    47b9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    47bc:	55                   	push   %rbp
    47bd:	53                   	push   %rbx
    47be:	48 83 ec 18          	sub    $0x18,%rsp
    47c2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    47cb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    47d0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    47d2:	49 89 e7             	mov    %rsp,%r15
    47d5:	4c 89 fa             	mov    %r15,%rdx
    47d8:	e8 83 db ff ff       	call   2360 <strtok_r@plt>
    for (; *str; ++str)
    47dd:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    47e1:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    47e4:	84 db                	test   %bl,%bl
    47e6:	74 1d                	je     4805 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    47e8:	e8 03 dd ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    47ed:	48 89 ea             	mov    %rbp,%rdx
    47f0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    47f3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    47f7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    47fa:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    47fd:	48 0f be 1a          	movsbq (%rdx),%rbx
    4801:	84 db                	test   %bl,%bl
    4803:	75 eb                	jne    47f0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4805:	4c 89 fa             	mov    %r15,%rdx
    4808:	4c 89 f6             	mov    %r14,%rsi
    480b:	31 ff                	xor    %edi,%edi
    480d:	e8 4e db ff ff       	call   2360 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4812:	48 8d 35 1a 19 00 00 	lea    0x191a(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    4819:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    481c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    481f:	e8 6c db ff ff       	call   2390 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4824:	4c 89 ea             	mov    %r13,%rdx
    4827:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    482a:	85 c0                	test   %eax,%eax
    482c:	75 2a                	jne    4858 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    482e:	48 89 df             	mov    %rbx,%rdi
    4831:	e8 3a fd ff ff       	call   4570 <handle_get_method>
}
    4836:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    483b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4844:	75 20                	jne    4866 <handle_http_method+0xc6>
    4846:	48 83 c4 18          	add    $0x18,%rsp
    484a:	5b                   	pop    %rbx
    484b:	5d                   	pop    %rbp
    484c:	41 5c                	pop    %r12
    484e:	41 5d                	pop    %r13
    4850:	41 5e                	pop    %r14
    4852:	41 5f                	pop    %r15
    4854:	c3                   	ret
    4855:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4858:	48 8b 3d b9 47 00 00 	mov    0x47b9(%rip),%rdi        # 9018 <unimplemented_content>
    485f:	e8 9c fb ff ff       	call   4400 <_send_static_string_content>
}
    4864:	eb d0                	jmp    4836 <handle_http_method+0x96>
    4866:	e8 a5 da ff ff       	call   2310 <__stack_chk_fail@plt>
    486b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004870 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4870:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4874:	85 d2                	test   %edx,%edx
    4876:	7e 38                	jle    48b0 <get_line+0x40>
    4878:	48 63 d2             	movslq %edx,%rdx
    487b:	48 83 c7 01          	add    $0x1,%rdi
    487f:	48 01 f2             	add    %rsi,%rdx
    4882:	eb 11                	jmp    4895 <get_line+0x25>
    4884:	0f 1f 40 00          	nopl   0x0(%rax)
    4888:	48 83 c6 01          	add    $0x1,%rsi
    488c:	48 83 c7 01          	add    $0x1,%rdi
    4890:	48 39 d6             	cmp    %rdx,%rsi
    4893:	74 1b                	je     48b0 <get_line+0x40>
        dest[i] = src[i];
    4895:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4899:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    489b:	3c 0d                	cmp    $0xd,%al
    489d:	75 e9                	jne    4888 <get_line+0x18>
    489f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    48a2:	75 e4                	jne    4888 <get_line+0x18>
            dest[i] = '\0';
    48a4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    48a7:	31 c0                	xor    %eax,%eax
    48a9:	c3                   	ret
    48aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    48b0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    48b5:	c3                   	ret
    48b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000048c0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    48c0:	f3 0f 1e fa          	endbr64
    48c4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    48cb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    48cf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    48d8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    48e0:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    48e2:	49 89 e2             	mov    %rsp,%r10
    48e5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    48ed:	4c 89 d0             	mov    %r10,%rax
    48f0:	eb 13                	jmp    4905 <handle_client_request+0x45>
    48f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    48f8:	48 83 c0 01          	add    $0x1,%rax
    48fc:	48 83 c1 01          	add    $0x1,%rcx
    4900:	4c 39 c8             	cmp    %r9,%rax
    4903:	74 4b                	je     4950 <handle_client_request+0x90>
        dest[i] = src[i];
    4905:	44 0f b6 01          	movzbl (%rcx),%r8d
    4909:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    490c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4910:	75 e6                	jne    48f8 <handle_client_request+0x38>
    4912:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4916:	75 e0                	jne    48f8 <handle_client_request+0x38>
            dest[i] = '\0';
    4918:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    491b:	8b 47 08             	mov    0x8(%rdi),%eax
    491e:	48 89 f2             	mov    %rsi,%rdx
    4921:	4c 89 d7             	mov    %r10,%rdi
    4924:	89 c6                	mov    %eax,%esi
    4926:	e8 75 fe ff ff       	call   47a0 <handle_http_method>
}
    492b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4933:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    493c:	75 39                	jne    4977 <handle_client_request+0xb7>
    493e:	31 c0                	xor    %eax,%eax
    4940:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4947:	c3                   	ret
    4948:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4950:	48 8b 0d c9 46 00 00 	mov    0x46c9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4957:	ba 12 00 00 00       	mov    $0x12,%edx
    495c:	be 01 00 00 00       	mov    $0x1,%esi
    4961:	48 8d 3d cf 17 00 00 	lea    0x17cf(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    4968:	e8 33 db ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    496d:	bf 01 00 00 00       	mov    $0x1,%edi
    4972:	e8 09 db ff ff       	call   2480 <exit@plt>
}
    4977:	e8 94 d9 ff ff       	call   2310 <__stack_chk_fail@plt>
    497c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004980 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4980:	f3 0f 1e fa          	endbr64
    4984:	55                   	push   %rbp
    4985:	53                   	push   %rbx
    4986:	48 89 cb             	mov    %rcx,%rbx
    4989:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    498d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4990:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4993:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4999:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    499c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    499f:	f6 c1 02             	test   $0x2,%cl
    49a2:	74 00                	je     49a4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    49a4:	41 89 c0             	mov    %eax,%r8d
    49a7:	45 29 c8             	sub    %r9d,%r8d
    49aa:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    49ae:	0f 82 96 db ff ff    	jb     254a <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    49b4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    49b7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    49ba:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    49bd:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    49c0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    49c3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    49c7:	d3 e5                	shl    %cl,%ebp
    49c9:	48 c1 e5 06          	shl    $0x6,%rbp
    49cd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    49d1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    49d4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    49d9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    49e0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    49e4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    49e8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    49f0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    49f8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    49fc:	e8 ef d9 ff ff       	call   23f0 <malloc@plt>
  io_uring_submit(ring);
    4a01:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4a04:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4a0a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4a0e:	48 83 c4 08          	add    $0x8,%rsp
    4a12:	5b                   	pop    %rbx
    4a13:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4a14:	e9 07 d9 ff ff       	jmp    2320 <io_uring_submit@plt>
    4a19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004a20 <io_thread>:
void* io_thread(void *arg) {
    4a20:	f3 0f 1e fa          	endbr64
    4a24:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4a26:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4a28:	41 56                	push   %r14
    4a2a:	41 55                	push   %r13
    4a2c:	41 54                	push   %r12
    4a2e:	55                   	push   %rbp
    4a2f:	48 89 fd             	mov    %rdi,%rbp
    4a32:	53                   	push   %rbx
    4a33:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4a3a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a43:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4a4b:	48 8b 47 40          	mov    0x40(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4a4f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4a54:	bf 00 01 00 00       	mov    $0x100,%edi
    4a59:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4a5c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4a60:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4a65:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4a6a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4a6f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4a74:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4a7c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4a81:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4a89:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4a8e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4a96:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4a9b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4aa3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4aa8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4ab0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4ab5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4abd:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4ac5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4acd:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4ad5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4add:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4ae5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4aed:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4af5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4afd:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4b05:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4b0d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4b14:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4b1c:	e8 af d8 ff ff       	call   23d0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4b21:	48 8b 7d 40          	mov    0x40(%rbp),%rdi
    4b25:	31 f6                	xor    %esi,%esi
    4b27:	e8 94 d9 ff ff       	call   24c0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4b2c:	31 d2                	xor    %edx,%edx
    4b2e:	be 01 00 00 00       	mov    $0x1,%esi
    4b33:	bf 02 00 00 00       	mov    $0x2,%edi
    4b38:	e8 d3 d9 ff ff       	call   2510 <socket@plt>
  if (sock == -1)
    4b3d:	83 f8 ff             	cmp    $0xffffffff,%eax
    4b40:	0f 84 08 06 00 00    	je     514e <io_thread+0x72e>
  if (setsockopt(sock,
    4b46:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4b4b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4b51:	89 c7                	mov    %eax,%edi
    4b53:	41 89 c4             	mov    %eax,%r12d
    4b56:	ba 02 00 00 00       	mov    $0x2,%edx
    4b5b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4b60:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4b68:	e8 73 d7 ff ff       	call   22e0 <setsockopt@plt>
    4b6d:	85 c0                	test   %eax,%eax
    4b6f:	0f 88 cd 05 00 00    	js     5142 <io_thread+0x722>
  srv_addr.sin_family = AF_INET;
    4b75:	8b 05 a5 1e 00 00    	mov    0x1ea5(%rip),%eax        # 6a20 <_IO_stdin_used+0xa20>
  return __builtin___memset_chk (__dest, __ch, __len,
    4b7b:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4b80:	ba 10 00 00 00       	mov    $0x10,%edx
    4b85:	44 89 e7             	mov    %r12d,%edi
    4b88:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4b91:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4b99:	89 44 24 40          	mov    %eax,0x40(%rsp)
  if (bind(sock,
    4b9d:	e8 9e d8 ff ff       	call   2440 <bind@plt>
    4ba2:	85 c0                	test   %eax,%eax
    4ba4:	0f 88 8c 05 00 00    	js     5136 <io_thread+0x716>
  if (listen(sock, 10) < 0) {
    4baa:	be 0a 00 00 00       	mov    $0xa,%esi
    4baf:	44 89 e7             	mov    %r12d,%edi
    4bb2:	e8 49 d8 ff ff       	call   2400 <listen@plt>
    4bb7:	85 c0                	test   %eax,%eax
    4bb9:	0f 88 6b 05 00 00    	js     512a <io_thread+0x70a>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4bbf:	ba 50 00 00 00       	mov    $0x50,%edx
    4bc4:	48 8d 35 b1 15 00 00 	lea    0x15b1(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4bcb:	bf 01 00 00 00       	mov    $0x1,%edi
    4bd0:	31 c0                	xor    %eax,%eax
    4bd2:	e8 59 d8 ff ff       	call   2430 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4bd7:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4bdc:	48 89 d9             	mov    %rbx,%rcx
    4bdf:	44 89 e7             	mov    %r12d,%edi
    4be2:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4be7:	48 89 c6             	mov    %rax,%rsi
    4bea:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    4bef:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4bf4:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4bfc:	e8 7f fd ff ff       	call   4980 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4c01:	bf 01 00 00 00       	mov    $0x1,%edi
    4c06:	be 10 00 00 00       	mov    $0x10,%esi
    4c0b:	e8 70 d7 ff ff       	call   2380 <calloc@plt>
    void *buf = malloc(size);
    4c10:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4c15:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4c18:	e8 d3 d7 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    4c1d:	48 85 c0             	test   %rax,%rax
    4c20:	0f 84 dd 04 00 00    	je     5103 <io_thread+0x6e3>
  iov->iov_base = zh_malloc(10);
    4c26:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4c2a:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4c31:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    4c38:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4c40:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4c43:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4c48:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4c4a:	f6 c1 02             	test   $0x2,%cl
    4c4d:	0f 85 2d 04 00 00    	jne    5080 <io_thread+0x660>
	if (next - head <= sq->ring_entries) {
    4c53:	89 d0                	mov    %edx,%eax
    4c55:	29 f0                	sub    %esi,%eax
    4c57:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4c5e:	0f 82 f0 d8 ff ff    	jb     2554 <io_thread.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4c64:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4c67:	48 8d 75 48          	lea    0x48(%rbp),%rsi
	sqe->addr3 = 0;
    4c6b:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4c6f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c72:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4c79:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c7c:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4c83:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c8a:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4c8c:	8b 55 48             	mov    0x48(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4c8f:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4c94:	48 c1 e0 06          	shl    $0x6,%rax
    4c98:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4ca0:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4ca6:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4ca9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4cb1:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4cb5:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4cbd:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4cc5:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4cc9:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4ccd:	e8 4e d6 ff ff       	call   2320 <io_uring_submit@plt>
  while (data->running == 1) {
    4cd2:	8b 45 2c             	mov    0x2c(%rbp),%eax
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4cd5:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4cda:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4ce2:	83 f8 01             	cmp    $0x1,%eax
    4ce5:	0f 85 b8 01 00 00    	jne    4ea3 <io_thread+0x483>
    4ceb:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4cf0:	4d 89 ce             	mov    %r9,%r14
    4cf3:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4cf8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4d00:	48 8d 3d 8b 14 00 00 	lea    0x148b(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4d07:	e8 c4 d5 ff ff       	call   22d0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4d0c:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4d13:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4d1a:	c1 e9 0b             	shr    $0xb,%ecx
    4d1d:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4d20:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4d28:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4d2a:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4d32:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4d34:	39 d0                	cmp    %edx,%eax
    4d36:	74 36                	je     4d6e <io_thread+0x34e>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4d38:	89 f8                	mov    %edi,%eax
    4d3a:	21 d0                	and    %edx,%eax
    4d3c:	d3 e0                	shl    %cl,%eax
    4d3e:	48 c1 e0 04          	shl    $0x4,%rax
    4d42:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4d4a:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4d52:	0f 85 88 01 00 00    	jne    4ee0 <io_thread+0x4c0>
    4d58:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4d5c:	0f 85 26 03 00 00    	jne    5088 <io_thread+0x668>
			if (cqe->res < 0)
    4d62:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4d65:	83 c2 01             	add    $0x1,%edx
    4d68:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4d6a:	85 c0                	test   %eax,%eax
    4d6c:	79 b2                	jns    4d20 <io_thread+0x300>
	*cqe_ptr = cqe;
    4d6e:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    4d77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4d80:	45 31 c0             	xor    %r8d,%r8d
    4d83:	31 d2                	xor    %edx,%edx
    4d85:	b9 01 00 00 00       	mov    $0x1,%ecx
    4d8a:	4c 89 f6             	mov    %r14,%rsi
    4d8d:	48 89 df             	mov    %rbx,%rdi
    4d90:	e8 8b d6 ff ff       	call   2420 <__io_uring_get_cqe@plt>
    4d95:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    4d98:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4d9d:	48 83 38 01          	cmpq   $0x1,(%rax)
    4da1:	0f 84 f1 02 00 00    	je     5098 <io_thread+0x678>
    4da7:	48 8d 3d 0a 14 00 00 	lea    0x140a(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4dae:	e8 1d d5 ff ff       	call   22d0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4db3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4db8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4dbb:	45 85 ff             	test   %r15d,%r15d
    4dbe:	0f 88 2e 03 00 00    	js     50f2 <io_thread+0x6d2>
      if (cqe->res < 0) {
    4dc4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    4dc7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    4dcb:	85 c0                	test   %eax,%eax
    4dcd:	0f 88 e5 02 00 00    	js     50b8 <io_thread+0x698>
      switch (req->event_type) {
    4dd3:	41 83 f8 01          	cmp    $0x1,%r8d
    4dd7:	0f 84 3b 01 00 00    	je     4f18 <io_thread+0x4f8>
    4ddd:	41 83 f8 02          	cmp    $0x2,%r8d
    4de1:	0f 84 b1 01 00 00    	je     4f98 <io_thread+0x578>
    4de7:	45 85 c0             	test   %r8d,%r8d
    4dea:	0f 84 70 01 00 00    	je     4f60 <io_thread+0x540>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4df0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4df8:	8b 02                	mov    (%rdx),%eax
    4dfa:	83 c0 01             	add    $0x1,%eax
    4dfd:	89 02                	mov    %eax,(%rdx)
	unsigned int head, next = sq->sqe_tail + 1;
    4dff:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e06:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4e0d:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4e10:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4e15:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4e17:	f6 c1 02             	test   $0x2,%cl
    4e1a:	74 00                	je     4e1c <io_thread+0x3fc>
	if (next - head <= sq->ring_entries) {
    4e1c:	89 d0                	mov    %edx,%eax
    4e1e:	29 f0                	sub    %esi,%eax
    4e20:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4e27:	0f 82 27 d7 ff ff    	jb     2554 <io_thread.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4e2d:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    4e30:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    4e35:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    4e39:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e3c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e43:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e46:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4e4d:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e54:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4e56:	8b 55 48             	mov    0x48(%rbp),%edx
    4e59:	48 c1 e0 06          	shl    $0x6,%rax
    4e5d:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4e65:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4e6b:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4e6e:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4e76:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4e7a:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4e82:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4e8a:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4e8e:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    4e92:	e8 89 d4 ff ff       	call   2320 <io_uring_submit@plt>
  while (data->running == 1) {
    4e97:	8b 45 2c             	mov    0x2c(%rbp),%eax
    4e9a:	83 f8 01             	cmp    $0x1,%eax
    4e9d:	0f 84 5d fe ff ff    	je     4d00 <io_thread+0x2e0>
    4ea3:	48 8d 3d 47 13 00 00 	lea    0x1347(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    4eaa:	e8 21 d4 ff ff       	call   22d0 <puts@plt>
}
    4eaf:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    4eb7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4ec0:	0f 85 38 02 00 00    	jne    50fe <io_thread+0x6de>
    4ec6:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    4ecd:	31 c0                	xor    %eax,%eax
    4ecf:	5b                   	pop    %rbx
    4ed0:	5d                   	pop    %rbp
    4ed1:	41 5c                	pop    %r12
    4ed3:	41 5d                	pop    %r13
    4ed5:	41 5e                	pop    %r14
    4ed7:	41 5f                	pop    %r15
    4ed9:	c3                   	ret
    4eda:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    4ee0:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    4ee5:	48 85 c0             	test   %rax,%rax
    4ee8:	0f 84 92 fe ff ff    	je     4d80 <io_thread+0x360>
      if (cqe->user_data == 1) {
    4eee:	48 83 38 01          	cmpq   $0x1,(%rax)
    4ef2:	0f 84 a0 01 00 00    	je     5098 <io_thread+0x678>
    4ef8:	48 8d 3d b9 12 00 00 	lea    0x12b9(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4eff:	e8 cc d3 ff ff       	call   22d0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4f04:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4f09:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4f0c:	e9 b3 fe ff ff       	jmp    4dc4 <io_thread+0x3a4>
    4f11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
              if (!cqe->res) {
    4f18:	85 c0                	test   %eax,%eax
    4f1a:	0f 85 c0 00 00 00    	jne    4fe0 <io_thread+0x5c0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4f20:	48 8b 0d f9 40 00 00 	mov    0x40f9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4f27:	ba 0f 00 00 00       	mov    $0xf,%edx
    4f2c:	be 01 00 00 00       	mov    $0x1,%esi
    4f31:	48 8d 3d a9 12 00 00 	lea    0x12a9(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    4f38:	e8 63 d5 ff ff       	call   24a0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    4f3d:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
	if (cqe)
    4f48:	48 85 c0             	test   %rax,%rax
    4f4b:	0f 84 ae fe ff ff    	je     4dff <io_thread+0x3df>
    4f51:	e9 9a fe ff ff       	jmp    4df0 <io_thread+0x3d0>
    4f56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4f60:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    4f65:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    4f6a:	48 89 d9             	mov    %rbx,%rcx
    4f6d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4f71:	e8 0a fa ff ff       	call   4980 <add_accept_request>
              add_read_request(cqe->res, &ring);
    4f76:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f7b:	48 89 de             	mov    %rbx,%rsi
    4f7e:	8b 78 08             	mov    0x8(%rax),%edi
    4f81:	e8 9a f3 ff ff       	call   4320 <add_read_request>
              free(req);
    4f86:	4c 89 e7             	mov    %r12,%rdi
    4f89:	e8 22 d3 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4f8e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    4f93:	eb b3                	jmp    4f48 <io_thread+0x528>
    4f95:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    4f98:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    4f9d:	45 31 ff             	xor    %r15d,%r15d
    4fa0:	85 c0                	test   %eax,%eax
    4fa2:	7e 20                	jle    4fc4 <io_thread+0x5a4>
    4fa4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    4fa8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    4fab:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    4faf:	48 c1 e0 04          	shl    $0x4,%rax
    4fb3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    4fb8:	e8 f3 d2 ff ff       	call   22b0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    4fbd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    4fc2:	7f e4                	jg     4fa8 <io_thread+0x588>
              close(req->client_socket);
    4fc4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    4fc9:	e8 82 d3 ff ff       	call   2350 <close@plt>
              free(req);
    4fce:	4c 89 e7             	mov    %r12,%rdi
    4fd1:	e8 da d2 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4fd6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    4fdb:	e9 68 ff ff ff       	jmp    4f48 <io_thread+0x528>
    for (int i = 0; i < dest_sz; i++) {
    4fe0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    4fe5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4fea:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    4ff2:	eb 11                	jmp    5005 <io_thread+0x5e5>
    4ff4:	0f 1f 40 00          	nopl   0x0(%rax)
    4ff8:	48 83 c0 01          	add    $0x1,%rax
    4ffc:	48 83 c2 01          	add    $0x1,%rdx
    5000:	48 39 c6             	cmp    %rax,%rsi
    5003:	74 4b                	je     5050 <io_thread+0x630>
        dest[i] = src[i];
    5005:	0f b6 0a             	movzbl (%rdx),%ecx
    5008:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    500a:	80 f9 0d             	cmp    $0xd,%cl
    500d:	75 e9                	jne    4ff8 <io_thread+0x5d8>
    500f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5013:	75 e3                	jne    4ff8 <io_thread+0x5d8>
            dest[i] = '\0';
    5015:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5018:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    501d:	48 89 da             	mov    %rbx,%rdx
    5020:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5025:	e8 76 f7 ff ff       	call   47a0 <handle_http_method>
              free(req->iov[0].iov_base);
    502a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    502f:	e8 7c d2 ff ff       	call   22b0 <free@plt>
              free(req);
    5034:	4c 89 e7             	mov    %r12,%rdi
    5037:	e8 74 d2 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    503c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5041:	e9 02 ff ff ff       	jmp    4f48 <io_thread+0x528>
    5046:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5050:	48 8b 0d c9 3f 00 00 	mov    0x3fc9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5057:	ba 12 00 00 00       	mov    $0x12,%edx
    505c:	be 01 00 00 00       	mov    $0x1,%esi
    5061:	48 8d 3d cf 10 00 00 	lea    0x10cf(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    5068:	e8 33 d4 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    506d:	bf 01 00 00 00       	mov    $0x1,%edi
    5072:	e8 09 d4 ff ff       	call   2480 <exit@plt>
    5077:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5080:	e9 ce fb ff ff       	jmp    4c53 <io_thread+0x233>
    5085:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5088:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    508d:	e9 5c fe ff ff       	jmp    4eee <io_thread+0x4ce>
    5092:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5098:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    50a0:	48 8d 3d fd 10 00 00 	lea    0x10fd(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    50a7:	8b 02                	mov    (%rdx),%eax
    50a9:	83 c0 01             	add    $0x1,%eax
    50ac:	89 02                	mov    %eax,(%rdx)
    50ae:	e8 1d d2 ff ff       	call   22d0 <puts@plt>
    50b3:	e9 eb fd ff ff       	jmp    4ea3 <io_thread+0x483>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    50b8:	f7 d8                	neg    %eax
    50ba:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    50bf:	89 c7                	mov    %eax,%edi
    50c1:	e8 1a d4 ff ff       	call   24e0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    50c6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    50cb:	be 01 00 00 00       	mov    $0x1,%esi
    50d0:	48 8b 3d 49 3f 00 00 	mov    0x3f49(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    50d7:	48 89 c1             	mov    %rax,%rcx
    50da:	48 8d 15 8f 13 00 00 	lea    0x138f(%rip),%rdx        # 6470 <_IO_stdin_used+0x470>
    50e1:	31 c0                	xor    %eax,%eax
    50e3:	e8 c8 d3 ff ff       	call   24b0 <__fprintf_chk@plt>
          exit(1);
    50e8:	bf 01 00 00 00       	mov    $0x1,%edi
    50ed:	e8 8e d3 ff ff       	call   2480 <exit@plt>
          fatal_error("io_uring_wait_cqe");
    50f2:	48 8d 3d d6 10 00 00 	lea    0x10d6(%rip),%rdi        # 61cf <_IO_stdin_used+0x1cf>
    50f9:	e8 a2 ea ff ff       	call   3ba0 <fatal_error>
}
    50fe:	e8 0d d2 ff ff       	call   2310 <__stack_chk_fail@plt>
    5103:	48 8b 0d 16 3f 00 00 	mov    0x3f16(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    510a:	ba 28 00 00 00       	mov    $0x28,%edx
    510f:	be 01 00 00 00       	mov    $0x1,%esi
    5114:	48 8d 3d 25 13 00 00 	lea    0x1325(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    511b:	e8 80 d3 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    5120:	bf 01 00 00 00       	mov    $0x1,%edi
    5125:	e8 56 d3 ff ff       	call   2480 <exit@plt>
    fatal_error("listen()");
    512a:	48 8d 3d 42 10 00 00 	lea    0x1042(%rip),%rdi        # 6173 <_IO_stdin_used+0x173>
    5131:	e8 6a ea ff ff       	call   3ba0 <fatal_error>
      fatal_error("bind()");
    5136:	48 8d 3d 2f 10 00 00 	lea    0x102f(%rip),%rdi        # 616c <_IO_stdin_used+0x16c>
    513d:	e8 5e ea ff ff       	call   3ba0 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    5142:	48 8d 3d 0a 10 00 00 	lea    0x100a(%rip),%rdi        # 6153 <_IO_stdin_used+0x153>
    5149:	e8 52 ea ff ff       	call   3ba0 <fatal_error>
      fatal_error("socket()");
    514e:	48 8d 3d f5 0f 00 00 	lea    0xff5(%rip),%rdi        # 614a <_IO_stdin_used+0x14a>
    5155:	e8 46 ea ff ff       	call   3ba0 <fatal_error>
    515a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005160 <receive>:
int receive(volatile struct BarrierTask *data) {
    5160:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5164:	8b 57 3c             	mov    0x3c(%rdi),%edx
    5167:	85 d2                	test   %edx,%edx
    5169:	0f 8e d1 00 00 00    	jle    5240 <receive+0xe0>
    516f:	48 89 f8             	mov    %rdi,%rax
    5172:	45 31 db             	xor    %r11d,%r11d
    5175:	0f 1f 00             	nopl   (%rax)
    struct Data *me = data->mailboxes[n].lower;
    5178:	48 8b 50 70          	mov    0x70(%rax),%rdx
    517c:	4c 89 df             	mov    %r11,%rdi
    517f:	48 c1 e7 05          	shl    $0x5,%rdi
    5183:	4c 8b 0c 3a          	mov    (%rdx,%rdi,1),%r9
    for (int x = 0 ; x < me->messages_count ; x++) {
    5187:	49 8b 51 08          	mov    0x8(%r9),%rdx
    518b:	48 85 d2             	test   %rdx,%rdx
    518e:	0f 8e 94 00 00 00    	jle    5228 <receive+0xc8>
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5194:	4d 8b 11             	mov    (%r9),%r10
    5197:	31 d2                	xor    %edx,%edx
    5199:	eb 12                	jmp    51ad <receive+0x4d>
    519b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    51a0:	49 8b 49 08          	mov    0x8(%r9),%rcx
    51a4:	48 83 c2 01          	add    $0x1,%rdx
    51a8:	48 39 d1             	cmp    %rdx,%rcx
    51ab:	7e 7b                	jle    5228 <receive+0xc8>
      data->sends++;
    51ad:	48 8b 48 78          	mov    0x78(%rax),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    51b1:	49 8b 34 d2          	mov    (%r10,%rdx,8),%rsi
      data->sends++;
    51b5:	48 83 c1 01          	add    $0x1,%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    51b9:	4c 8b 46 10          	mov    0x10(%rsi),%r8
      data->sends++;
    51bd:	48 89 48 78          	mov    %rcx,0x78(%rax)
      data->n++;
    51c1:	48 8b 48 10          	mov    0x10(%rax),%rcx
    51c5:	48 83 c1 01          	add    $0x1,%rcx
    51c9:	48 89 48 10          	mov    %rcx,0x10(%rax)
      data->mailboxes[n].received++;
    51cd:	48 8b 48 70          	mov    0x70(%rax),%rcx
    51d1:	48 83 44 39 18 01    	addq   $0x1,0x18(%rcx,%rdi,1)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    51d7:	48 63 08             	movslq (%rax),%rcx
    51da:	49 39 c8             	cmp    %rcx,%r8
    51dd:	75 c1                	jne    51a0 <receive+0x40>
    51df:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    51e3:	48 63 48 38          	movslq 0x38(%rax),%rcx
    51e7:	48 39 ce             	cmp    %rcx,%rsi
    51ea:	75 b4                	jne    51a0 <receive+0x40>
int receive(volatile struct BarrierTask *data) {
    51ec:	48 83 ec 08          	sub    $0x8,%rsp
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread_index);
    51f0:	48 63 50 38          	movslq 0x38(%rax),%rdx
    51f4:	48 63 00             	movslq (%rax),%rax
    51f7:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    51f9:	bf 01 00 00 00       	mov    $0x1,%edi
    51fe:	48 39 f2             	cmp    %rsi,%rdx
    5201:	48 8d 35 90 12 00 00 	lea    0x1290(%rip),%rsi        # 6498 <_IO_stdin_used+0x498>
    5208:	0f 94 c1             	sete   %cl
    520b:	31 d2                	xor    %edx,%edx
    520d:	4c 39 c0             	cmp    %r8,%rax
    5210:	0f 94 c2             	sete   %dl
    5213:	31 c0                	xor    %eax,%eax
    5215:	e8 16 d2 ff ff       	call   2430 <__printf_chk@plt>
        exit(1);
    521a:	bf 01 00 00 00       	mov    $0x1,%edi
    521f:	e8 5c d2 ff ff       	call   2480 <exit@plt>
    5224:	0f 1f 40 00          	nopl   0x0(%rax)
    me->messages_count = 0;
    5228:	49 c7 41 08 00 00 00 00 	movq   $0x0,0x8(%r9)
  for (int n = 0 ; n < data->thread_count; n++) {
    5230:	8b 50 3c             	mov    0x3c(%rax),%edx
    5233:	49 83 c3 01          	add    $0x1,%r11
    5237:	44 39 da             	cmp    %r11d,%edx
    523a:	0f 8f 38 ff ff ff    	jg     5178 <receive+0x18>
}
    5240:	c3                   	ret
    5241:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    524c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005250 <barriered_work>:
int barriered_work(volatile struct BarrierTask *data) {
    5250:	f3 0f 1e fa          	endbr64
    5254:	41 55                	push   %r13
    5256:	41 54                	push   %r12
    5258:	55                   	push   %rbp
    5259:	53                   	push   %rbx
    525a:	48 89 fb             	mov    %rdi,%rbx
    525d:	48 83 ec 08          	sub    $0x8,%rsp
  if (data->thread_index == data->task_index) {
    5261:	8b 57 38             	mov    0x38(%rdi),%edx
    5264:	8b 07                	mov    (%rdi),%eax
    5266:	39 c2                	cmp    %eax,%edx
    5268:	0f 84 d2 00 00 00    	je     5340 <barriered_work+0xf0>
    receive(data);
    526e:	e8 ed fe ff ff       	call   5160 <receive>
    while (data->scheduled == 1) {
    5273:	8b 43 48             	mov    0x48(%rbx),%eax
    5276:	83 f8 01             	cmp    $0x1,%eax
    5279:	75 19                	jne    5294 <barriered_work+0x44>
    527b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->n++;
    5280:	48 8b 43 10          	mov    0x10(%rbx),%rax
    5284:	48 83 c0 01          	add    $0x1,%rax
    5288:	48 89 43 10          	mov    %rax,0x10(%rbx)
    while (data->scheduled == 1) {
    528c:	8b 43 48             	mov    0x48(%rbx),%eax
    528f:	83 f8 01             	cmp    $0x1,%eax
    5292:	74 ec                	je     5280 <barriered_work+0x30>
    if (data->sending == 1) {
    5294:	8b 83 80 00 00 00    	mov    0x80(%rbx),%eax
    529a:	83 f8 01             	cmp    $0x1,%eax
    529d:	74 10                	je     52af <barriered_work+0x5f>
  asm volatile ("mfence" ::: "memory");
    529f:	0f ae f0             	mfence
}
    52a2:	48 83 c4 08          	add    $0x8,%rsp
    52a6:	31 c0                	xor    %eax,%eax
    52a8:	5b                   	pop    %rbx
    52a9:	5d                   	pop    %rbp
    52aa:	41 5c                	pop    %r12
    52ac:	41 5d                	pop    %r13
    52ae:	c3                   	ret
        for (int n = 0 ; n < data->thread_count; n++) {
    52af:	8b 43 3c             	mov    0x3c(%rbx),%eax
    52b2:	85 c0                	test   %eax,%eax
    52b4:	7e e9                	jle    529f <barriered_work+0x4f>
    52b6:	45 31 c9             	xor    %r9d,%r9d
    52b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          if (n == data->thread_index) { continue; }
    52c0:	8b 43 38             	mov    0x38(%rbx),%eax
    52c3:	44 39 c8             	cmp    %r9d,%eax
    52c6:	74 5e                	je     5326 <barriered_work+0xd6>
          struct Data *them = data->mailboxes[n].higher;
    52c8:	48 8b 43 70          	mov    0x70(%rbx),%rax
    52cc:	4c 89 c9             	mov    %r9,%rcx
    52cf:	48 c1 e1 05          	shl    $0x5,%rcx
    52d3:	48 8b 54 08 08       	mov    0x8(%rax,%rcx,1),%rdx
          for (; them->messages_count < min;) {
    52d8:	48 8b 42 08          	mov    0x8(%rdx),%rax
    52dc:	48 63 7a 10          	movslq 0x10(%rdx),%rdi
    52e0:	48 39 f8             	cmp    %rdi,%rax
    52e3:	7d 41                	jge    5326 <barriered_work+0xd6>
            them->messages[them->messages_count++] = data->message; 
    52e5:	4c 8b 02             	mov    (%rdx),%r8
    52e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
            data->n++;
    52f0:	48 8b 43 10          	mov    0x10(%rbx),%rax
    52f4:	48 83 c0 01          	add    $0x1,%rax
    52f8:	48 89 43 10          	mov    %rax,0x10(%rbx)
            data->mailboxes[n].sent++;
    52fc:	48 8b 43 70          	mov    0x70(%rbx),%rax
    5300:	48 83 44 08 10 01    	addq   $0x1,0x10(%rax,%rcx,1)
            them->messages[them->messages_count++] = data->message; 
    5306:	48 8b 42 08          	mov    0x8(%rdx),%rax
    530a:	48 8d 70 01          	lea    0x1(%rax),%rsi
    530e:	48 89 72 08          	mov    %rsi,0x8(%rdx)
    5312:	48 8b b3 88 00 00 00 	mov    0x88(%rbx),%rsi
    5319:	49 89 34 c0          	mov    %rsi,(%r8,%rax,8)
          for (; them->messages_count < min;) {
    531d:	48 8b 42 08          	mov    0x8(%rdx),%rax
    5321:	48 39 f8             	cmp    %rdi,%rax
    5324:	7c ca                	jl     52f0 <barriered_work+0xa0>
        for (int n = 0 ; n < data->thread_count; n++) {
    5326:	8b 43 3c             	mov    0x3c(%rbx),%eax
    5329:	49 83 c1 01          	add    $0x1,%r9
    532d:	44 39 c8             	cmp    %r9d,%eax
    5330:	7f 8e                	jg     52c0 <barriered_work+0x70>
    5332:	e9 68 ff ff ff       	jmp    529f <barriered_work+0x4f>
    5337:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      receive(data);
    5340:	e8 1b fe ff ff       	call   5160 <receive>
        int t = data->task_index;
    5345:	8b 3b                	mov    (%rbx),%edi
        for (int y = 0; y < data->thread_count ; y++) {
    5347:	8b 43 3c             	mov    0x3c(%rbx),%eax
    534a:	85 c0                	test   %eax,%eax
    534c:	0f 8e b4 00 00 00    	jle    5406 <barriered_work+0x1b6>
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5352:	48 63 c7             	movslq %edi,%rax
    5355:	45 31 d2             	xor    %r10d,%r10d
    5358:	45 31 e4             	xor    %r12d,%r12d
              int next_task = abs((t + 1) % (data->thread_count));
    535b:	83 c7 01             	add    $0x1,%edi
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    535e:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    5362:	48 8d 2c 50          	lea    (%rax,%rdx,2),%rbp
    5366:	48 c1 e5 03          	shl    $0x3,%rbp
    536a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          for (int b = 0; b < data->thread_count ; b++) {
    5370:	8b 43 3c             	mov    0x3c(%rbx),%eax
    5373:	4d 89 e3             	mov    %r12,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    5376:	31 f6                	xor    %esi,%esi
    5378:	31 c9                	xor    %ecx,%ecx
    537a:	49 c1 e3 05          	shl    $0x5,%r11
          for (int b = 0; b < data->thread_count ; b++) {
    537e:	85 c0                	test   %eax,%eax
    5380:	7e 6d                	jle    53ef <barriered_work+0x19f>
    5382:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              int next_task = abs((t + 1) % (data->thread_count));
    5388:	44 8b 6b 3c          	mov    0x3c(%rbx),%r13d
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    538c:	48 8b 43 30          	mov    0x30(%rbx),%rax
    5390:	48 8b 40 10          	mov    0x10(%rax),%rax
    5394:	4a 8b 54 10 20       	mov    0x20(%rax,%r10,1),%rdx
    5399:	48 01 ea             	add    %rbp,%rdx
    539c:	4c 8b 42 70          	mov    0x70(%rdx),%r8
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    53a0:	48 8b 43 30          	mov    0x30(%rbx),%rax
    53a4:	4c 8b 48 10          	mov    0x10(%rax),%r9
              int next_task = abs((t + 1) % (data->thread_count));
    53a8:	89 f8                	mov    %edi,%eax
    53aa:	99                   	cltd
    53ab:	41 f7 fd             	idiv   %r13d
    53ae:	89 d0                	mov    %edx,%eax
    53b0:	f7 d8                	neg    %eax
    53b2:	0f 49 d0             	cmovns %eax,%edx
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    53b5:	48 63 d2             	movslq %edx,%rdx
    53b8:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    53bc:	48 8d 14 42          	lea    (%rdx,%rax,2),%rdx
    53c0:	49 8b 44 31 20       	mov    0x20(%r9,%rsi,1),%rax
          for (int b = 0; b < data->thread_count ; b++) {
    53c5:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    53cc:	48 8d 04 d0          	lea    (%rax,%rdx,8),%rax
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    53d0:	48 89 ca             	mov    %rcx,%rdx
          for (int b = 0; b < data->thread_count ; b++) {
    53d3:	48 83 c1 01          	add    $0x1,%rcx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    53d7:	48 c1 e2 05          	shl    $0x5,%rdx
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    53db:	48 8b 40 70          	mov    0x70(%rax),%rax
    53df:	49 8b 54 10 08       	mov    0x8(%r8,%rdx,1),%rdx
    53e4:	4a 89 14 18          	mov    %rdx,(%rax,%r11,1)
          for (int b = 0; b < data->thread_count ; b++) {
    53e8:	8b 43 3c             	mov    0x3c(%rbx),%eax
    53eb:	39 c8                	cmp    %ecx,%eax
    53ed:	7f 99                	jg     5388 <barriered_work+0x138>
        for (int y = 0; y < data->thread_count ; y++) {
    53ef:	8b 43 3c             	mov    0x3c(%rbx),%eax
    53f2:	49 83 c4 01          	add    $0x1,%r12
    53f6:	49 81 c2 98 00 00 00 	add    $0x98,%r10
    53fd:	44 39 e0             	cmp    %r12d,%eax
    5400:	0f 8f 6a ff ff ff    	jg     5370 <barriered_work+0x120>
      asm volatile ("mfence" ::: "memory");
    5406:	0f ae f0             	mfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5409:	48 8b 73 50          	mov    0x50(%rbx),%rsi
    540d:	48 8b 43 60          	mov    0x60(%rbx),%rax
    5411:	31 ff                	xor    %edi,%edi
    5413:	48 c1 e0 05          	shl    $0x5,%rax
    5417:	48 01 c6             	add    %rax,%rsi
    541a:	e8 d1 ce ff ff       	call   22f0 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    541f:	48 8b 43 30          	mov    0x30(%rbx),%rax
    5423:	48 8b 40 30          	mov    0x30(%rax),%rax
    5427:	8b 78 10             	mov    0x10(%rax),%edi
    542a:	8d 6f 01             	lea    0x1(%rdi),%ebp
    542d:	89 68 10             	mov    %ebp,0x10(%rax)
    while (data->scheduled == 1) {
    5430:	8b 43 48             	mov    0x48(%rbx),%eax
    5433:	83 f8 01             	cmp    $0x1,%eax
    5436:	75 4d                	jne    5485 <barriered_work+0x235>
    5438:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->n++;
    5440:	48 8b 43 10          	mov    0x10(%rbx),%rax
    5444:	48 83 c0 01          	add    $0x1,%rax
    5448:	48 89 43 10          	mov    %rax,0x10(%rbx)
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    544c:	48 8b 4b 28          	mov    0x28(%rbx),%rcx
    5450:	48 8b 73 30          	mov    0x30(%rbx),%rsi
    5454:	48 63 43 38          	movslq 0x38(%rbx),%rax
    5458:	48 63 13             	movslq (%rbx),%rdx
    545b:	48 8d 3c c0          	lea    (%rax,%rax,8),%rdi
    545f:	48 8d 04 78          	lea    (%rax,%rdi,2),%rax
    5463:	48 8b 7e 10          	mov    0x10(%rsi),%rdi
    5467:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
    546b:	48 8d 14 72          	lea    (%rdx,%rsi,2),%rdx
    546f:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    5473:	48 8b 40 20          	mov    0x20(%rax),%rax
    5477:	48 8d 3c d0          	lea    (%rax,%rdx,8),%rdi
    547b:	ff d1                	call   *%rcx
    while (data->scheduled == 1) {
    547d:	8b 43 48             	mov    0x48(%rbx),%eax
    5480:	83 f8 01             	cmp    $0x1,%eax
    5483:	74 bb                	je     5440 <barriered_work+0x1f0>
    if (modcount != data->thread->protected_state->modcount) {
    5485:	48 8b 43 30          	mov    0x30(%rbx),%rax
    5489:	48 8b 40 30          	mov    0x30(%rax),%rax
    548d:	3b 68 10             	cmp    0x10(%rax),%ebp
    5490:	75 32                	jne    54c4 <barriered_work+0x274>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5492:	48 8b 53 50          	mov    0x50(%rbx),%rdx
    5496:	48 8b 43 60          	mov    0x60(%rbx),%rax
    549a:	31 ff                	xor    %edi,%edi
    549c:	48 c1 e0 05          	shl    $0x5,%rax
    54a0:	48 8d 74 02 10       	lea    0x10(%rdx,%rax,1),%rsi
    54a5:	e8 46 ce ff ff       	call   22f0 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    54aa:	48 8b 43 60          	mov    0x60(%rbx),%rax
    54ae:	48 8b 4b 58          	mov    0x58(%rbx),%rcx
    54b2:	48 83 c0 01          	add    $0x1,%rax
    54b6:	48 99                	cqto
    54b8:	48 f7 f9             	idiv   %rcx
    54bb:	48 89 53 60          	mov    %rdx,0x60(%rbx)
    54bf:	e9 db fd ff ff       	jmp    529f <barriered_work+0x4f>
    54c4:	48 8d 3d 39 0d 00 00 	lea    0xd39(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    54cb:	e8 00 ce ff ff       	call   22d0 <puts@plt>
    54d0:	eb c0                	jmp    5492 <barriered_work+0x242>
    54d2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    54dd:	0f 1f 00             	nopl   (%rax)

00000000000054e0 <barriered_work_ingest>:
int barriered_work_ingest(volatile struct BarrierTask *data) {
    54e0:	f3 0f 1e fa          	endbr64
    54e4:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    54e8:	48 8b 47 30          	mov    0x30(%rdi),%rax
    54ec:	48 8b 40 38          	mov    0x38(%rax),%rax
    54f0:	8b 00                	mov    (%rax),%eax
    54f2:	85 c0                	test   %eax,%eax
    54f4:	7e 57                	jle    554d <barriered_work_ingest+0x6d>
    54f6:	31 c0                	xor    %eax,%eax
    54f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    if (data->thread->buffers->buffer[x].available == 1) {
    5500:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
    5504:	48 89 c2             	mov    %rax,%rdx
    5507:	48 c1 e2 04          	shl    $0x4,%rdx
    550b:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    550f:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    5513:	48 01 d6             	add    %rdx,%rsi
    5516:	8b 4e 08             	mov    0x8(%rsi),%ecx
    5519:	83 f9 01             	cmp    $0x1,%ecx
    551c:	75 1f                	jne    553d <barriered_work_ingest+0x5d>
      data->ingest_count++;
    551e:	48 8b 4f 68          	mov    0x68(%rdi),%rcx
    5522:	48 83 c1 01          	add    $0x1,%rcx
    5526:	48 89 4f 68          	mov    %rcx,0x68(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    552a:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
    552e:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    5532:	48 03 51 08          	add    0x8(%rcx),%rdx
    5536:	c7 42 08 00 00 00 00 	movl   $0x0,0x8(%rdx)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    553d:	48 8b 57 30          	mov    0x30(%rdi),%rdx
    5541:	48 83 c0 01          	add    $0x1,%rax
    5545:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    5549:	39 02                	cmp    %eax,(%rdx)
    554b:	7f b3                	jg     5500 <barriered_work_ingest+0x20>
  asm volatile ("mfence" ::: "memory");
    554d:	0f ae f0             	mfence
  barriered_work(data);
    5550:	e8 fb fc ff ff       	call   5250 <barriered_work>
}
    5555:	31 c0                	xor    %eax,%eax
    5557:	48 83 c4 08          	add    $0x8,%rsp
    555b:	c3                   	ret
    555c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005560 <barriered_nulltask>:
int barriered_nulltask(volatile struct BarrierTask *data) {
    5560:	f3 0f 1e fa          	endbr64
}
    5564:	31 c0                	xor    %eax,%eax
    5566:	c3                   	ret
    5567:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005570 <barriered_steal>:
int barriered_steal(volatile struct BarrierTask *data) {
    5570:	f3 0f 1e fa          	endbr64
    5574:	31 c0                	xor    %eax,%eax
    5576:	c3                   	ret
    5577:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005580 <after>:
int after(struct timespec left, struct timespec right) {
    5580:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5584:	31 c0                	xor    %eax,%eax
    5586:	48 39 d7             	cmp    %rdx,%rdi
    5589:	7e 08                	jle    5593 <after+0x13>
    558b:	31 c0                	xor    %eax,%eax
    558d:	48 39 ce             	cmp    %rcx,%rsi
    5590:	0f 9f c0             	setg   %al
}
    5593:	c3                   	ret
    5594:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    559f:	90                   	nop

00000000000055a0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    55a0:	f3 0f 1e fa          	endbr64
    55a4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    55a9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    55ae:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    55b0:	48 39 d7             	cmp    %rdx,%rdi
    55b3:	7f 18                	jg     55cd <within+0x2d>
    55b5:	4d 39 d8             	cmp    %r11,%r8
    55b8:	0f 9e c2             	setle  %dl
    55bb:	48 39 ce             	cmp    %rcx,%rsi
    55be:	0f 9e c0             	setle  %al
    55c1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    55c3:	31 c0                	xor    %eax,%eax
    55c5:	4d 39 d1             	cmp    %r10,%r9
    55c8:	0f 9e c0             	setle  %al
    55cb:	21 d0                	and    %edx,%eax
}
    55cd:	c3                   	ret
    55ce:	66 90                	xchg   %ax,%ax

00000000000055d0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    55d0:	f3 0f 1e fa          	endbr64
    55d4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    55d9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    55de:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    55e3:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    55e8:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
    55ed:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
  if (after(left.start, right.start) && after(right.end, left.end)) {
    55f2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    55f7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    55fc:	48 39 fe             	cmp    %rdi,%rsi
    55ff:	7d 2f                	jge    5630 <overlap+0x60>
    5601:	48 39 ca             	cmp    %rcx,%rdx
    5604:	7d 62                	jge    5668 <overlap+0x98>
    5606:	4d 39 da             	cmp    %r11,%r10
    5609:	7e 0e                	jle    5619 <overlap+0x49>
    return 1;
    560b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5610:	4d 39 c1             	cmp    %r8,%r9
    5613:	0f 8f 7f 00 00 00    	jg     5698 <overlap+0xc8>
  return 0;
    5619:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    561b:	4d 39 c1             	cmp    %r8,%r9
    561e:	7c 4c                	jl     566c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5620:	31 c0                	xor    %eax,%eax
    5622:	4d 39 da             	cmp    %r11,%r10
    5625:	0f 9d c0             	setge  %al
    5628:	c3                   	ret
    5629:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5630:	7e 4e                	jle    5680 <overlap+0xb0>
    5632:	48 39 ca             	cmp    %rcx,%rdx
    5635:	7f 39                	jg     5670 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5637:	75 31                	jne    566a <overlap+0x9a>
    5639:	4d 39 c1             	cmp    %r8,%r9
    563c:	7f 2c                	jg     566a <overlap+0x9a>
    return 1;
    563e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5643:	4d 39 da             	cmp    %r11,%r10
    5646:	7e 24                	jle    566c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5648:	48 39 ca             	cmp    %rcx,%rdx
    564b:	0f 94 c2             	sete   %dl
    564e:	48 39 fe             	cmp    %rdi,%rsi
    5651:	0f 94 c0             	sete   %al
    5654:	21 c2                	and    %eax,%edx
    5656:	31 c0                	xor    %eax,%eax
    5658:	4d 39 c1             	cmp    %r8,%r9
    565b:	0f 94 c0             	sete   %al
    565e:	21 d0                	and    %edx,%eax
    5660:	c3                   	ret
    5661:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5668:	74 af                	je     5619 <overlap+0x49>
  return 0;
    566a:	31 c0                	xor    %eax,%eax
}
    566c:	c3                   	ret
    566d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5670:	4d 39 c1             	cmp    %r8,%r9
    5673:	7d c4                	jge    5639 <overlap+0x69>
    return 1;
    5675:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    567a:	4d 39 da             	cmp    %r11,%r10
    567d:	7d ba                	jge    5639 <overlap+0x69>
    567f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5680:	48 39 ca             	cmp    %rcx,%rdx
    5683:	7c 94                	jl     5619 <overlap+0x49>
    5685:	4d 39 c1             	cmp    %r8,%r9
    5688:	7e b4                	jle    563e <overlap+0x6e>
    568a:	48 39 ca             	cmp    %rcx,%rdx
    568d:	74 91                	je     5620 <overlap+0x50>
    568f:	eb d9                	jmp    566a <overlap+0x9a>
    5691:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5698:	c3                   	ret
    5699:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000056a0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    56a0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    56a4:	85 f6                	test   %esi,%esi
    56a6:	0f 8e 0d 03 00 00    	jle    59b9 <verify+0x319>
int verify(struct KernelThread *thread_data, int thread_count) {
    56ac:	41 57                	push   %r15
  for (int x = 0 ; x < thread_count; x++) {
    56ae:	45 31 ff             	xor    %r15d,%r15d
int verify(struct KernelThread *thread_data, int thread_count) {
    56b1:	41 56                	push   %r14
    56b3:	41 89 f6             	mov    %esi,%r14d
    56b6:	41 55                	push   %r13
    56b8:	4c 8d 6f 20          	lea    0x20(%rdi),%r13
    56bc:	41 54                	push   %r12
    56be:	55                   	push   %rbp
    56bf:	53                   	push   %rbx
    56c0:	48 83 ec 48          	sub    $0x48,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    56c4:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    56c9:	4c 89 6c 24 08       	mov    %r13,0x8(%rsp)
    56ce:	45 31 e4             	xor    %r12d,%r12d
    56d1:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
      if (z != x)  {
    56d6:	45 39 e7             	cmp    %r12d,%r15d
    56d9:	0f 84 37 02 00 00    	je     5916 <verify+0x276>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    56df:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    56e4:	8b 50 08             	mov    0x8(%rax),%edx
    56e7:	85 d2                	test   %edx,%edx
    56e9:	0f 8e 27 02 00 00    	jle    5916 <verify+0x276>
    56ef:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    56f8:	31 ed                	xor    %ebp,%ebp
    56fa:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    56ff:	44 89 fa             	mov    %r15d,%edx
    5702:	48 8d 35 0b 0b 00 00 	lea    0xb0b(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    5709:	bf 01 00 00 00       	mov    $0x1,%edi
    570e:	31 c0                	xor    %eax,%eax
    5710:	e8 1b cd ff ff       	call   2430 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5715:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    571a:	8b 40 08             	mov    0x8(%rax),%eax
    571d:	85 c0                	test   %eax,%eax
    571f:	0f 8e d2 01 00 00    	jle    58f7 <verify+0x257>
    5725:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    572a:	89 6c 24 34          	mov    %ebp,0x34(%rsp)
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    572e:	45 31 e4             	xor    %r12d,%r12d
    5731:	44 89 7c 24 38       	mov    %r15d,0x38(%rsp)
    5736:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    573b:	44 89 74 24 3c       	mov    %r14d,0x3c(%rsp)
    5740:	4c 03 28             	add    (%rax),%r13
    5743:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5748:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    574d:	4b 8d 04 e4          	lea    (%r12,%r12,8),%rax
    5751:	49 8b 4d 60          	mov    0x60(%r13),%rcx
    5755:	48 8d 35 cd 0a 00 00 	lea    0xacd(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    575c:	49 8d 2c 44          	lea    (%r12,%rax,2),%rbp
    5760:	bf 01 00 00 00       	mov    $0x1,%edi
    5765:	48 8b 03             	mov    (%rbx),%rax
    5768:	48 c1 e5 03          	shl    $0x3,%rbp
    576c:	48 01 e8             	add    %rbp,%rax
    576f:	48 8b 50 60          	mov    0x60(%rax),%rdx
    5773:	31 c0                	xor    %eax,%eax
    5775:	e8 b6 cc ff ff       	call   2430 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    577a:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    577f:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    5784:	4c 03 28             	add    (%rax),%r13
    5787:	49 8b 45 60          	mov    0x60(%r13),%rax
    578b:	48 85 c0             	test   %rax,%rax
    578e:	0f 8e 42 01 00 00    	jle    58d6 <verify+0x236>
    5794:	48 8b 13             	mov    (%rbx),%rdx
    5797:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    579c:	45 31 ff             	xor    %r15d,%r15d
    579f:	48 01 ea             	add    %rbp,%rdx
    57a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    57a8:	48 8b 42 60          	mov    0x60(%rdx),%rax
    57ac:	4d 89 fc             	mov    %r15,%r12
    57af:	31 db                	xor    %ebx,%ebx
    57b1:	49 c1 e4 05          	shl    $0x5,%r12
    57b5:	48 85 c0             	test   %rax,%rax
    57b8:	7f 37                	jg     57f1 <verify+0x151>
    57ba:	e9 01 01 00 00       	jmp    58c0 <verify+0x220>
    57bf:	90                   	nop
  return left.tv_sec > right.tv_sec &&
    57c0:	48 39 f1             	cmp    %rsi,%rcx
    57c3:	0f 8d 6f 01 00 00    	jge    5938 <verify+0x298>
    57c9:	4d 39 da             	cmp    %r11,%r10
    57cc:	7e 09                	jle    57d7 <verify+0x137>
    57ce:	49 39 c6             	cmp    %rax,%r14
    57d1:	0f 8c 81 00 00 00    	jl     5858 <verify+0x1b8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    57d7:	4d 39 da             	cmp    %r11,%r10
    57da:	0f 8d 9b 01 00 00    	jge    597b <verify+0x2db>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    57e0:	48 8b 42 60          	mov    0x60(%rdx),%rax
    57e4:	48 83 c3 01          	add    $0x1,%rbx
    57e8:	48 39 d8             	cmp    %rbx,%rax
    57eb:	0f 8e cf 00 00 00    	jle    58c0 <verify+0x220>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    57f1:	48 8b 42 50          	mov    0x50(%rdx),%rax
    57f5:	49 89 d9             	mov    %rbx,%r9
    57f8:	49 8b 4d 50          	mov    0x50(%r13),%rcx
    57fc:	49 c1 e1 05          	shl    $0x5,%r9
    5800:	4c 01 e1             	add    %r12,%rcx
    5803:	4c 01 c8             	add    %r9,%rax
    5806:	4c 8b 01             	mov    (%rcx),%r8
    5809:	48 8b 38             	mov    (%rax),%rdi
    580c:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    5810:	4c 8b 59 10          	mov    0x10(%rcx),%r11
    5814:	4c 8b 71 18          	mov    0x18(%rcx),%r14
    5818:	4c 8b 50 10          	mov    0x10(%rax),%r10
    581c:	48 8b 48 08          	mov    0x8(%rax),%rcx
    5820:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    5824:	4c 39 c7             	cmp    %r8,%rdi
    5827:	7c 97                	jl     57c0 <verify+0x120>
    5829:	0f 8e 31 01 00 00    	jle    5960 <verify+0x2c0>
    582f:	48 39 f1             	cmp    %rsi,%rcx
    5832:	0f 8f 10 01 00 00    	jg     5948 <verify+0x2a8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5838:	75 a6                	jne    57e0 <verify+0x140>
    583a:	4d 39 da             	cmp    %r11,%r10
    583d:	7f a1                	jg     57e0 <verify+0x140>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    583f:	49 39 c6             	cmp    %rax,%r14
    5842:	7d 14                	jge    5858 <verify+0x1b8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5844:	4c 39 c7             	cmp    %r8,%rdi
    5847:	75 97                	jne    57e0 <verify+0x140>
    5849:	48 39 f1             	cmp    %rsi,%rcx
    584c:	75 92                	jne    57e0 <verify+0x140>
    584e:	4d 39 da             	cmp    %r11,%r10
    5851:	75 8d                	jne    57e0 <verify+0x140>
    5853:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
    5858:	48 8b 72 50          	mov    0x50(%rdx),%rsi
    585c:	49 8b 45 50          	mov    0x50(%r13),%rax
    5860:	bf 01 00 00 00       	mov    $0x1,%edi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5865:	48 83 c3 01          	add    $0x1,%rbx
                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
    5869:	48 8b 4a 50          	mov    0x50(%rdx),%rcx
    586d:	49 8b 55 50          	mov    0x50(%r13),%rdx
    5871:	4e 8b 44 20 08       	mov    0x8(%rax,%r12,1),%r8
    5876:	31 c0                	xor    %eax,%eax
    5878:	4a 8b 4c 09 10       	mov    0x10(%rcx,%r9,1),%rcx
    587d:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    5881:	4e 8b 4c 0e 18       	mov    0x18(%rsi,%r9,1),%r9
    5886:	48 8d 35 33 0c 00 00 	lea    0xc33(%rip),%rsi        # 64c0 <_IO_stdin_used+0x4c0>
    588d:	e8 9e cb ff ff       	call   2430 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5892:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5897:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    589c:	4c 03 28             	add    (%rax),%r13
    589f:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    58a4:	48 8b 10             	mov    (%rax),%rdx
    58a7:	48 01 ea             	add    %rbp,%rdx
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    58aa:	48 8b 42 60          	mov    0x60(%rdx),%rax
    58ae:	48 39 d8             	cmp    %rbx,%rax
    58b1:	0f 8f 3a ff ff ff    	jg     57f1 <verify+0x151>
    58b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    58c0:	49 8b 45 60          	mov    0x60(%r13),%rax
    58c4:	49 83 c7 01          	add    $0x1,%r15
    58c8:	4c 39 f8             	cmp    %r15,%rax
    58cb:	0f 8f d7 fe ff ff    	jg     57a8 <verify+0x108>
    58d1:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    58d6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    58db:	49 83 c4 01          	add    $0x1,%r12
    58df:	44 39 60 08          	cmp    %r12d,0x8(%rax)
    58e3:	0f 8f 5f fe ff ff    	jg     5748 <verify+0xa8>
    58e9:	8b 6c 24 34          	mov    0x34(%rsp),%ebp
    58ed:	44 8b 7c 24 38       	mov    0x38(%rsp),%r15d
    58f2:	44 8b 74 24 3c       	mov    0x3c(%rsp),%r14d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    58f7:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    58fc:	83 c5 01             	add    $0x1,%ebp
    58ff:	48 81 44 24 18 98 00 00 00 	addq   $0x98,0x18(%rsp)
    5908:	39 68 08             	cmp    %ebp,0x8(%rax)
    590b:	0f 8f ee fd ff ff    	jg     56ff <verify+0x5f>
    5911:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    5916:	48 81 44 24 08 98 00 00 00 	addq   $0x98,0x8(%rsp)
    591f:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    5924:	41 39 c6             	cmp    %eax,%r14d
    5927:	74 60                	je     5989 <verify+0x2e9>
    5929:	41 89 c4             	mov    %eax,%r12d
    592c:	e9 a5 fd ff ff       	jmp    56d6 <verify+0x36>
    5931:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5938:	0f 85 a2 fe ff ff    	jne    57e0 <verify+0x140>
    593e:	e9 94 fe ff ff       	jmp    57d7 <verify+0x137>
    5943:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5948:	49 39 c6             	cmp    %rax,%r14
    594b:	0f 8e e9 fe ff ff    	jle    583a <verify+0x19a>
    5951:	4d 39 da             	cmp    %r11,%r10
    5954:	0f 8d e0 fe ff ff    	jge    583a <verify+0x19a>
    595a:	e9 f9 fe ff ff       	jmp    5858 <verify+0x1b8>
    595f:	90                   	nop
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5960:	48 39 f1             	cmp    %rsi,%rcx
    5963:	0f 8c 6e fe ff ff    	jl     57d7 <verify+0x137>
    5969:	4d 39 da             	cmp    %r11,%r10
    596c:	0f 8e cd fe ff ff    	jle    583f <verify+0x19f>
    5972:	48 39 f1             	cmp    %rsi,%rcx
    5975:	0f 85 65 fe ff ff    	jne    57e0 <verify+0x140>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    597b:	49 39 c6             	cmp    %rax,%r14
    597e:	0f 8f 5c fe ff ff    	jg     57e0 <verify+0x140>
    5984:	e9 cf fe ff ff       	jmp    5858 <verify+0x1b8>
  for (int x = 0 ; x < thread_count; x++) {
    5989:	48 81 44 24 10 98 00 00 00 	addq   $0x98,0x10(%rsp)
    5992:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    5997:	41 8d 47 01          	lea    0x1(%r15),%eax
    599b:	45 39 e7             	cmp    %r12d,%r15d
    599e:	74 08                	je     59a8 <verify+0x308>
    59a0:	41 89 c7             	mov    %eax,%r15d
    59a3:	e9 21 fd ff ff       	jmp    56c9 <verify+0x29>
}
    59a8:	48 83 c4 48          	add    $0x48,%rsp
    59ac:	31 c0                	xor    %eax,%eax
    59ae:	5b                   	pop    %rbx
    59af:	5d                   	pop    %rbp
    59b0:	41 5c                	pop    %r12
    59b2:	41 5d                	pop    %r13
    59b4:	41 5e                	pop    %r14
    59b6:	41 5f                	pop    %r15
    59b8:	c3                   	ret
    59b9:	31 c0                	xor    %eax,%eax
    59bb:	c3                   	ret
    59bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000059c0 <min>:
int min(int a, int b) {
    59c0:	f3 0f 1e fa          	endbr64
}
    59c4:	39 f7                	cmp    %esi,%edi
    59c6:	89 f0                	mov    %esi,%eax
    59c8:	0f 4e c7             	cmovle %edi,%eax
    59cb:	c3                   	ret

Disassembly of section .fini:

00000000000059cc <_fini>:
    59cc:	f3 0f 1e fa          	endbr64
    59d0:	48 83 ec 08          	sub    $0x8,%rsp
    59d4:	48 83 c4 08          	add    $0x8,%rsp
    59d8:	c3                   	ret
