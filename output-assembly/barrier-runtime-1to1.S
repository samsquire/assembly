
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
    25d6:	48 8d 3d 0b 3f 00 00 	lea    0x3f0b(%rip),%rdi        # 64e8 <_IO_stdin_used+0x4e8>
    25dd:	41 56                	push   %r14
    25df:	41 55                	push   %r13
    25e1:	41 54                	push   %r12
    25e3:	55                   	push   %rbp
    25e4:	53                   	push   %rbx
    25e5:	48 83 ec 58          	sub    $0x58,%rsp
    25e9:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    25f2:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
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
    268c:	ba 0f 27 00 00       	mov    $0x270f,%edx
    2691:	48 8d 35 b0 3e 00 00 	lea    0x3eb0(%rip),%rsi        # 6548 <_IO_stdin_used+0x548>
    2698:	31 c0                	xor    %eax,%eax
    269a:	bf 01 00 00 00       	mov    $0x1,%edi
    269f:	e8 8c fd ff ff       	call   2430 <__printf_chk@plt>
    26a4:	ba 0f 27 00 00       	mov    $0x270f,%edx
    26a9:	48 8d 35 c8 3e 00 00 	lea    0x3ec8(%rip),%rsi        # 6578 <_IO_stdin_used+0x578>
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
    2711:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2716:	e8 65 fc ff ff       	call   2380 <calloc@plt>
    271b:	be 10 00 00 00       	mov    $0x10,%esi
    2720:	bf 01 00 00 00       	mov    $0x1,%edi
    2725:	48 89 04 24          	mov    %rax,(%rsp)
    2729:	e8 52 fc ff ff       	call   2380 <calloc@plt>
    272e:	be 10 00 00 00       	mov    $0x10,%esi
    2733:	bf 0f 27 00 00       	mov    $0x270f,%edi
    2738:	c7 00 0f 27 00 00    	movl   $0x270f,(%rax)
    273e:	48 89 c3             	mov    %rax,%rbx
    2741:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2746:	e8 35 fc ff ff       	call   2380 <calloc@plt>
    274b:	4c 8b 04 24          	mov    (%rsp),%r8
    274f:	48 89 43 08          	mov    %rax,0x8(%rbx)
    2753:	48 8d 88 f0 70 02 00 	lea    0x270f0(%rax),%rcx
    275a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    2760:	48 8d 50 10          	lea    0x10(%rax),%rdx
    2764:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    276b:	c7 40 18 00 00 00 00 	movl   $0x0,0x18(%rax)
    2772:	c7 40 28 00 00 00 00 	movl   $0x0,0x28(%rax)
    2779:	48 8d 42 20          	lea    0x20(%rdx),%rax
    277d:	48 39 c8             	cmp    %rcx,%rax
    2780:	75 de                	jne    2760 <main+0x190>
    2782:	4c 89 04 24          	mov    %r8,(%rsp)
    2786:	4d 89 c6             	mov    %r8,%r14
    2789:	31 db                	xor    %ebx,%ebx
    278b:	4c 8d 2d 0e 3e 00 00 	lea    0x3e0e(%rip),%r13        # 65a0 <_IO_stdin_used+0x5a0>
    2792:	48 8d 2d 56 3b 00 00 	lea    0x3b56(%rip),%rbp        # 62ef <_IO_stdin_used+0x2ef>
    2799:	4c 8d 25 6b 3b 00 00 	lea    0x3b6b(%rip),%r12        # 630b <_IO_stdin_used+0x30b>
    27a0:	89 da                	mov    %ebx,%edx
    27a2:	4c 89 ee             	mov    %r13,%rsi
    27a5:	bf 01 00 00 00       	mov    $0x1,%edi
    27aa:	31 c0                	xor    %eax,%eax
    27ac:	e8 7f fc ff ff       	call   2430 <__printf_chk@plt>
    27b1:	45 31 ff             	xor    %r15d,%r15d
    27b4:	45 89 3e             	mov    %r15d,(%r14)
    27b7:	89 d9                	mov    %ebx,%ecx
    27b9:	89 da                	mov    %ebx,%edx
    27bb:	48 89 ee             	mov    %rbp,%rsi
    27be:	4d 89 76 10          	mov    %r14,0x10(%r14)
    27c2:	bf 01 00 00 00       	mov    $0x1,%edi
    27c7:	31 c0                	xor    %eax,%eax
    27c9:	41 83 c7 01          	add    $0x1,%r15d
    27cd:	41 c7 46 18 03 00 00 00 	movl   $0x3,0x18(%r14)
    27d5:	e8 56 fc ff ff       	call   2430 <__printf_chk@plt>
    27da:	41 83 ff 03          	cmp    $0x3,%r15d
    27de:	75 d4                	jne    27b4 <main+0x1e4>
    27e0:	8d 53 03             	lea    0x3(%rbx),%edx
    27e3:	4c 89 e6             	mov    %r12,%rsi
    27e6:	bf 01 00 00 00       	mov    $0x1,%edi
    27eb:	31 c0                	xor    %eax,%eax
    27ed:	e8 3e fc ff ff       	call   2430 <__printf_chk@plt>
    27f2:	49 81 c6 60 02 00 00 	add    $0x260,%r14
    27f9:	83 fb 04             	cmp    $0x4,%ebx
    27fc:	74 07                	je     2805 <main+0x235>
    27fe:	bb 04 00 00 00       	mov    $0x4,%ebx
    2803:	eb 9b                	jmp    27a0 <main+0x1d0>
    2805:	4c 8b 04 24          	mov    (%rsp),%r8
    2809:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    2811:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    281a:	c7 04 24 00 00 00 00 	movl   $0x0,(%rsp)
    2821:	4d 89 c7             	mov    %r8,%r15
    2824:	4c 89 44 24 38       	mov    %r8,0x38(%rsp)
    2829:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    2830:	83 3c 24 05          	cmpl   $0x5,(%rsp)
    2834:	7e 11                	jle    2847 <main+0x277>
    2836:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    283b:	41 c7 47 18 06 00 00 00 	movl   $0x6,0x18(%r15)
    2843:	49 89 47 10          	mov    %rax,0x10(%r15)
    2847:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    284c:	41 c7 47 1c 09 00 00 00 	movl   $0x9,0x1c(%r15)
    2854:	be 10 00 00 00       	mov    $0x10,%esi
    2859:	31 db                	xor    %ebx,%ebx
    285b:	41 c7 47 28 04 00 00 00 	movl   $0x4,0x28(%r15)
    2863:	bf 64 00 00 00       	mov    $0x64,%edi
    2868:	49 89 47 30          	mov    %rax,0x30(%r15)
    286c:	e8 0f fb ff ff       	call   2380 <calloc@plt>
    2871:	be 10 00 00 00       	mov    $0x10,%esi
    2876:	bf 64 00 00 00       	mov    $0x64,%edi
    287b:	49 89 47 50          	mov    %rax,0x50(%r15)
    287f:	e8 fc fa ff ff       	call   2380 <calloc@plt>
    2884:	be 28 00 00 00       	mov    $0x28,%esi
    2889:	bf 64 00 00 00       	mov    $0x64,%edi
    288e:	66 0f 6f 05 7a 41 00 00 	movdqa 0x417a(%rip),%xmm0        # 6a10 <_IO_stdin_used+0xa10>
    2896:	49 89 47 58          	mov    %rax,0x58(%r15)
    289a:	41 0f 11 47 68       	movups %xmm0,0x68(%r15)
    289f:	e8 dc fa ff ff       	call   2380 <calloc@plt>
    28a4:	be 98 00 00 00       	mov    $0x98,%esi
    28a9:	bf 04 00 00 00       	mov    $0x4,%edi
    28ae:	66 0f 6f 0d 5a 41 00 00 	movdqa 0x415a(%rip),%xmm1        # 6a10 <_IO_stdin_used+0xa10>
    28b6:	49 89 47 78          	mov    %rax,0x78(%r15)
    28ba:	41 0f 11 8f 80 00 00 00 	movups %xmm1,0x80(%r15)
    28c2:	e8 b9 fa ff ff       	call   2380 <calloc@plt>
    28c7:	49 89 47 20          	mov    %rax,0x20(%r15)
    28cb:	49 89 c6             	mov    %rax,%r14
    28ce:	4c 63 eb             	movslq %ebx,%r13
    28d1:	4b 8d 44 ed 00       	lea    0x0(%r13,%r13,8),%rax
    28d6:	4d 8d 64 45 00       	lea    0x0(%r13,%rax,2),%r12
    28db:	49 c1 e4 03          	shl    $0x3,%r12
    28df:	4b 8d 2c 26          	lea    (%r14,%r12,1),%rbp
    28e3:	39 1c 24             	cmp    %ebx,(%rsp)
    28e6:	0f 84 04 0a 00 00    	je     32f0 <main+0xd20>
    28ec:	be 20 00 00 00       	mov    $0x20,%esi
    28f1:	bf 06 00 00 00       	mov    $0x6,%edi
    28f6:	e8 85 fa ff ff       	call   2380 <calloc@plt>
    28fb:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    28ff:	4c 89 64 24 10       	mov    %r12,0x10(%rsp)
    2904:	49 89 c6             	mov    %rax,%r14
    2907:	48 89 45 70          	mov    %rax,0x70(%rbp)
    290b:	48 8d a8 c0 00 00 00 	lea    0xc0(%rax),%rbp
    2912:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    2918:	be 08 00 00 00       	mov    $0x8,%esi
    291d:	bf 0f 27 00 00       	mov    $0x270f,%edi
    2922:	49 83 c6 20          	add    $0x20,%r14
    2926:	e8 55 fa ff ff       	call   2380 <calloc@plt>
    292b:	be 08 00 00 00       	mov    $0x8,%esi
    2930:	bf 0f 27 00 00       	mov    $0x270f,%edi
    2935:	49 89 c4             	mov    %rax,%r12
    2938:	e8 43 fa ff ff       	call   2380 <calloc@plt>
    293d:	be 18 00 00 00       	mov    $0x18,%esi
    2942:	bf 02 00 00 00       	mov    $0x2,%edi
    2947:	48 89 c3             	mov    %rax,%rbx
    294a:	e8 31 fa ff ff       	call   2380 <calloc@plt>
    294f:	48 8d 70 18          	lea    0x18(%rax),%rsi
    2953:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    295b:	49 89 46 e0          	mov    %rax,-0x20(%r14)
    295f:	49 89 76 e8          	mov    %rsi,-0x18(%r14)
    2963:	4c 89 20             	mov    %r12,(%rax)
    2966:	48 89 58 18          	mov    %rbx,0x18(%rax)
    296a:	48 c7 40 10 0f 27 00 00 	movq   $0x270f,0x10(%rax)
    2972:	48 c7 40 20 00 00 00 00 	movq   $0x0,0x20(%rax)
    297a:	48 c7 40 28 0f 27 00 00 	movq   $0x270f,0x28(%rax)
    2982:	4c 39 f5             	cmp    %r14,%rbp
    2985:	75 91                	jne    2918 <main+0x348>
    2987:	be 01 00 00 00       	mov    $0x1,%esi
    298c:	bf 00 01 00 00       	mov    $0x100,%edi
    2991:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2995:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
    299a:	e8 e1 f9 ff ff       	call   2380 <calloc@plt>
    299f:	bf 18 00 00 00       	mov    $0x18,%edi
    29a4:	48 89 c5             	mov    %rax,%rbp
    29a7:	e8 44 fa ff ff       	call   23f0 <malloc@plt>
    29ac:	44 8b 04 24          	mov    (%rsp),%r8d
    29b0:	48 89 ef             	mov    %rbp,%rdi
    29b3:	41 89 d9             	mov    %ebx,%r9d
    29b6:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    29bb:	48 8d 0d 06 3c 00 00 	lea    0x3c06(%rip),%rcx        # 65c8 <_IO_stdin_used+0x5c8>
    29c2:	ba 00 01 00 00       	mov    $0x100,%edx
    29c7:	31 c0                	xor    %eax,%eax
    29c9:	be 01 00 00 00       	mov    $0x1,%esi
    29ce:	e8 2d fb ff ff       	call   2500 <__sprintf_chk@plt>
    29d3:	4d 8b 77 20          	mov    0x20(%r15),%r14
    29d7:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    29dc:	be 20 00 00 00       	mov    $0x20,%esi
    29e1:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    29e6:	49 89 2a             	mov    %rbp,(%r10)
    29e9:	8d 6b 01             	lea    0x1(%rbx),%ebp
    29ec:	4d 89 6a 10          	mov    %r13,0x10(%r10)
    29f0:	4f 8d 2c 26          	lea    (%r14,%r12,1),%r13
    29f4:	49 89 42 08          	mov    %rax,0x8(%r10)
    29f8:	41 89 ad 90 00 00 00 	mov    %ebp,0x90(%r13)
    29ff:	4d 89 95 88 00 00 00 	mov    %r10,0x88(%r13)
    2a06:	41 c7 85 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r13)
    2a11:	49 c7 45 58 3f 42 0f 00 	movq   $0xf423f,0x58(%r13)
    2a19:	49 8b 7d 58          	mov    0x58(%r13),%rdi
    2a1d:	e8 5e f9 ff ff       	call   2380 <calloc@plt>
    2a22:	49 89 45 50          	mov    %rax,0x50(%r13)
    2a26:	41 8b 07             	mov    (%r15),%eax
    2a29:	49 c7 45 60 00 00 00 00 	movq   $0x0,0x60(%r13)
    2a31:	41 89 45 38          	mov    %eax,0x38(%r13)
    2a35:	4d 89 7d 30          	mov    %r15,0x30(%r13)
    2a39:	41 c7 45 40 01 00 00 00 	movl   $0x1,0x40(%r13)
    2a41:	41 c7 45 08 00 00 00 00 	movl   $0x0,0x8(%r13)
    2a49:	41 c7 45 3c 06 00 00 00 	movl   $0x6,0x3c(%r13)
    2a51:	41 c7 45 44 04 00 00 00 	movl   $0x4,0x44(%r13)
    2a59:	41 c7 85 84 00 00 00 06 00 00 00 	movl   $0x6,0x84(%r13)
    2a64:	41 89 5d 00          	mov    %ebx,0x0(%r13)
    2a68:	83 fb 02             	cmp    $0x2,%ebx
    2a6b:	0f 84 8f 08 00 00    	je     3300 <main+0xd30>
    2a71:	8b 14 24             	mov    (%rsp),%edx
    2a74:	39 da                	cmp    %ebx,%edx
    2a76:	0f 85 5c 08 00 00    	jne    32d8 <main+0xd08>
    2a7c:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    2a80:	85 db                	test   %ebx,%ebx
    2a82:	0f 8f 50 08 00 00    	jg     32d8 <main+0xd08>
    2a88:	bf 01 00 00 00       	mov    $0x1,%edi
    2a8d:	48 8d 35 5c 3b 00 00 	lea    0x3b5c(%rip),%rsi        # 65f0 <_IO_stdin_used+0x5f0>
    2a94:	31 c0                	xor    %eax,%eax
    2a96:	e8 95 f9 ff ff       	call   2430 <__printf_chk@plt>
    2a9b:	48 63 c3             	movslq %ebx,%rax
    2a9e:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    2aa3:	4d 8b 77 20          	mov    0x20(%r15),%r14
    2aa7:	48 89 c1             	mov    %rax,%rcx
    2aaa:	48 c1 e0 04          	shl    $0x4,%rax
    2aae:	48 01 f8             	add    %rdi,%rax
    2ab1:	4d 01 f4             	add    %r14,%r12
    2ab4:	49 89 47 38          	mov    %rax,0x38(%r15)
    2ab8:	48 8d 05 a1 2a 00 00 	lea    0x2aa1(%rip),%rax        # 5560 <barriered_work_ingest>
    2abf:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    2ac4:	8d 41 01             	lea    0x1(%rcx),%eax
    2ac7:	89 44 24 20          	mov    %eax,0x20(%rsp)
    2acb:	83 fd 04             	cmp    $0x4,%ebp
    2ace:	74 10                	je     2ae0 <main+0x510>
    2ad0:	89 eb                	mov    %ebp,%ebx
    2ad2:	e9 f7 fd ff ff       	jmp    28ce <main+0x2fe>
    2ad7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    2ae0:	48 8d 05 69 09 00 00 	lea    0x969(%rip),%rax        # 3450 <barriered_reset>
    2ae7:	83 04 24 01          	addl   $0x1,(%rsp)
    2aeb:	49 89 86 e8 01 00 00 	mov    %rax,0x1e8(%r14)
    2af2:	4d 89 be f8 01 00 00 	mov    %r15,0x1f8(%r14)
    2af9:	49 81 c7 98 00 00 00 	add    $0x98,%r15
    2b00:	41 c7 86 08 02 00 00 01 00 00 00 	movl   $0x1,0x208(%r14)
    2b0b:	41 c7 86 d0 01 00 00 00 00 00 00 	movl   $0x0,0x1d0(%r14)
    2b16:	41 c7 86 c8 01 00 00 03 00 00 00 	movl   $0x3,0x1c8(%r14)
    2b21:	41 c7 86 04 02 00 00 06 00 00 00 	movl   $0x6,0x204(%r14)
    2b2c:	41 8b 87 68 ff ff ff 	mov    -0x98(%r15),%eax
    2b33:	48 83 44 24 18 01    	addq   $0x1,0x18(%rsp)
    2b39:	41 89 86 00 02 00 00 	mov    %eax,0x200(%r14)
    2b40:	8b 04 24             	mov    (%rsp),%eax
    2b43:	41 c7 86 4c 02 00 00 06 00 00 00 	movl   $0x6,0x24c(%r14)
    2b4e:	41 c7 86 0c 02 00 00 04 00 00 00 	movl   $0x4,0x20c(%r14)
    2b59:	83 f8 09             	cmp    $0x9,%eax
    2b5c:	0f 85 ce fc ff ff    	jne    2830 <main+0x260>
    2b62:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    2b67:	be 38 00 00 00       	mov    $0x38,%esi
    2b6c:	bf 09 00 00 00       	mov    $0x9,%edi
    2b71:	45 31 ff             	xor    %r15d,%r15d
    2b74:	4c 8d 35 95 3a 00 00 	lea    0x3a95(%rip),%r14        # 6610 <_IO_stdin_used+0x610>
    2b7b:	49 8b 40 20          	mov    0x20(%r8),%rax
    2b7f:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    2b84:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    2b8b:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    2b96:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    2ba1:	41 c7 80 50 04 00 00 04 00 00 00 	movl   $0x4,0x450(%r8)
    2bac:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2bb3:	49 8b 80 b8 00 00 00 	mov    0xb8(%r8),%rax
    2bba:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2bc1:	49 8b 80 50 01 00 00 	mov    0x150(%r8),%rax
    2bc8:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2bcf:	49 8b 80 e8 01 00 00 	mov    0x1e8(%r8),%rax
    2bd6:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2bdd:	49 8b 80 80 02 00 00 	mov    0x280(%r8),%rax
    2be4:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2beb:	49 8b 80 18 03 00 00 	mov    0x318(%r8),%rax
    2bf2:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2bf9:	e8 82 f7 ff ff       	call   2380 <calloc@plt>
    2bfe:	be 38 00 00 00       	mov    $0x38,%esi
    2c03:	bf 09 00 00 00       	mov    $0x9,%edi
    2c08:	48 89 c3             	mov    %rax,%rbx
    2c0b:	e8 70 f7 ff ff       	call   2380 <calloc@plt>
    2c10:	be 38 00 00 00       	mov    $0x38,%esi
    2c15:	bf 09 00 00 00       	mov    $0x9,%edi
    2c1a:	48 89 04 24          	mov    %rax,(%rsp)
    2c1e:	e8 5d f7 ff ff       	call   2380 <calloc@plt>
    2c23:	be 08 00 00 00       	mov    $0x8,%esi
    2c28:	bf 09 00 00 00       	mov    $0x9,%edi
    2c2d:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2c32:	e8 49 f7 ff ff       	call   2380 <calloc@plt>
    2c37:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    2c3c:	ba 06 00 00 00       	mov    $0x6,%edx
    2c41:	48 8d 35 ca 36 00 00 	lea    0x36ca(%rip),%rsi        # 6312 <_IO_stdin_used+0x312>
    2c48:	49 89 c4             	mov    %rax,%r12
    2c4b:	bf 01 00 00 00       	mov    $0x1,%edi
    2c50:	31 c0                	xor    %eax,%eax
    2c52:	41 c7 80 94 03 00 00 00 00 00 00 	movl   $0x0,0x394(%r8)
    2c5d:	4c 89 e5             	mov    %r12,%rbp
    2c60:	41 c7 80 bc 03 00 00 01 00 00 00 	movl   $0x1,0x3bc(%r8)
    2c6b:	41 c7 80 b8 03 00 00 04 00 00 00 	movl   $0x4,0x3b8(%r8)
    2c76:	4d 89 80 a0 03 00 00 	mov    %r8,0x3a0(%r8)
    2c7d:	41 c7 80 a8 03 00 00 06 00 00 00 	movl   $0x6,0x3a8(%r8)
    2c88:	41 c7 80 90 03 00 00 00 00 00 00 	movl   $0x0,0x390(%r8)
    2c93:	e8 98 f7 ff ff       	call   2430 <__printf_chk@plt>
    2c98:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    2c9d:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
    2ca2:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2ca9:	48 8d 15 60 0b 00 00 	lea    0xb60(%rip),%rdx        # 3810 <timer_thread>
    2cb0:	49 8d 88 90 03 00 00 	lea    0x390(%r8),%rcx
    2cb7:	e8 94 f7 ff ff       	call   2450 <pthread_create@plt>
    2cbc:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    2cc1:	4c 89 64 24 10       	mov    %r12,0x10(%rsp)
    2cc6:	45 89 fc             	mov    %r15d,%r12d
    2cc9:	4d 89 c5             	mov    %r8,%r13
    2ccc:	4d 89 c7             	mov    %r8,%r15
    2ccf:	90                   	nop
    2cd0:	41 c7 45 04 01 00 00 00 	movl   $0x1,0x4(%r13)
    2cd8:	44 89 e2             	mov    %r12d,%edx
    2cdb:	4c 89 f6             	mov    %r14,%rsi
    2cde:	31 c0                	xor    %eax,%eax
    2ce0:	41 c7 45 2c 01 00 00 00 	movl   $0x1,0x2c(%r13)
    2ce8:	bf 01 00 00 00       	mov    $0x1,%edi
    2ced:	41 83 c4 01          	add    $0x1,%r12d
    2cf1:	e8 3a f7 ff ff       	call   2430 <__printf_chk@plt>
    2cf6:	4c 89 e9             	mov    %r13,%rcx
    2cf9:	48 89 de             	mov    %rbx,%rsi
    2cfc:	48 89 ef             	mov    %rbp,%rdi
    2cff:	48 8d 15 ba 07 00 00 	lea    0x7ba(%rip),%rdx        # 34c0 <barriered_thread>
    2d06:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    2d0d:	48 83 c5 08          	add    $0x8,%rbp
    2d11:	48 83 c3 38          	add    $0x38,%rbx
    2d15:	e8 36 f7 ff ff       	call   2450 <pthread_create@plt>
    2d1a:	41 83 fc 06          	cmp    $0x6,%r12d
    2d1e:	75 b0                	jne    2cd0 <main+0x700>
    2d20:	be d8 00 00 00       	mov    $0xd8,%esi
    2d25:	bf 01 00 00 00       	mov    $0x1,%edi
    2d2a:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
    2d2f:	41 c7 87 2c 04 00 00 02 00 00 00 	movl   $0x2,0x42c(%r15)
    2d3a:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    2d3f:	31 db                	xor    %ebx,%ebx
    2d41:	4c 8d 6c 24 40       	lea    0x40(%rsp),%r13
    2d46:	48 8d 2d 35 36 00 00 	lea    0x3635(%rip),%rbp        # 6382 <_IO_stdin_used+0x382>
    2d4d:	41 c7 87 54 04 00 00 01 00 00 00 	movl   $0x1,0x454(%r15)
    2d58:	41 c7 87 50 04 00 00 00 00 00 00 	movl   $0x0,0x450(%r15)
    2d63:	e8 18 f6 ff ff       	call   2380 <calloc@plt>
    2d68:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    2d6d:	be 00 08 00 00       	mov    $0x800,%esi
    2d72:	31 ff                	xor    %edi,%edi
    2d74:	49 89 80 68 04 00 00 	mov    %rax,0x468(%r8)
    2d7b:	e8 10 f7 ff ff       	call   2490 <eventfd@plt>
    2d80:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    2d85:	ba 07 00 00 00       	mov    $0x7,%edx
    2d8a:	48 8d 35 9f 35 00 00 	lea    0x359f(%rip),%rsi        # 6330 <_IO_stdin_used+0x330>
    2d91:	bf 01 00 00 00       	mov    $0x1,%edi
    2d96:	41 89 80 70 04 00 00 	mov    %eax,0x470(%r8)
    2d9d:	31 c0                	xor    %eax,%eax
    2d9f:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    2da6:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    2db1:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    2dbc:	e8 6f f6 ff ff       	call   2430 <__printf_chk@plt>
    2dc1:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    2dc6:	48 8b 34 24          	mov    (%rsp),%rsi
    2dca:	49 8d 7c 24 38       	lea    0x38(%r12),%rdi
    2dcf:	48 8d 15 0a 1d 00 00 	lea    0x1d0a(%rip),%rdx        # 4ae0 <io_thread>
    2dd6:	49 8d 88 28 04 00 00 	lea    0x428(%r8),%rcx
    2ddd:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2de4:	e8 67 f6 ff ff       	call   2450 <pthread_create@plt>
    2de9:	ba 08 00 00 00       	mov    $0x8,%edx
    2dee:	48 8d 35 52 35 00 00 	lea    0x3552(%rip),%rsi        # 6347 <_IO_stdin_used+0x347>
    2df5:	31 c0                	xor    %eax,%eax
    2df7:	bf 01 00 00 00       	mov    $0x1,%edi
    2dfc:	e8 2f f6 ff ff       	call   2430 <__printf_chk@plt>
    2e01:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    2e06:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    2e0b:	49 8d 7c 24 40       	lea    0x40(%r12),%rdi
    2e10:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2e15:	48 8d 15 34 09 00 00 	lea    0x934(%rip),%rdx        # 3750 <external_thread>
    2e1c:	49 89 80 f8 04 00 00 	mov    %rax,0x4f8(%r8)
    2e23:	48 8b 05 f6 3b 00 00 	mov    0x3bf6(%rip),%rax        # 6a20 <_IO_stdin_used+0xa20>
    2e2a:	49 8d 88 c0 04 00 00 	lea    0x4c0(%r8),%rcx
    2e31:	4d 89 80 d0 04 00 00 	mov    %r8,0x4d0(%r8)
    2e38:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    2e3f:	41 c7 80 c4 04 00 00 03 00 00 00 	movl   $0x3,0x4c4(%r8)
    2e4a:	41 c7 80 ec 04 00 00 01 00 00 00 	movl   $0x1,0x4ec(%r8)
    2e55:	41 c7 80 e8 04 00 00 00 00 00 00 	movl   $0x0,0x4e8(%r8)
    2e60:	49 89 80 d8 04 00 00 	mov    %rax,0x4d8(%r8)
    2e67:	41 c7 80 c0 04 00 00 08 00 00 00 	movl   $0x8,0x4c0(%r8)
    2e72:	4c 89 04 24          	mov    %r8,(%rsp)
    2e76:	e8 d5 f5 ff ff       	call   2450 <pthread_create@plt>
    2e7b:	48 8d 3d e2 34 00 00 	lea    0x34e2(%rip),%rdi        # 6364 <_IO_stdin_used+0x364>
    2e82:	e8 49 f4 ff ff       	call   22d0 <puts@plt>
    2e87:	4c 8b 34 24          	mov    (%rsp),%r14
    2e8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2e90:	49 8b 3c dc          	mov    (%r12,%rbx,8),%rdi
    2e94:	4c 89 ee             	mov    %r13,%rsi
    2e97:	e8 34 f6 ff ff       	call   24d0 <pthread_join@plt>
    2e9c:	89 da                	mov    %ebx,%edx
    2e9e:	48 89 ee             	mov    %rbp,%rsi
    2ea1:	bf 01 00 00 00       	mov    $0x1,%edi
    2ea6:	31 c0                	xor    %eax,%eax
    2ea8:	48 83 c3 01          	add    $0x1,%rbx
    2eac:	e8 7f f5 ff ff       	call   2430 <__printf_chk@plt>
    2eb1:	48 83 fb 09          	cmp    $0x9,%rbx
    2eb5:	75 d9                	jne    2e90 <main+0x8c0>
    2eb7:	49 8d 86 b0 03 00 00 	lea    0x3b0(%r14),%rax
    2ebe:	31 ed                	xor    %ebp,%ebp
    2ec0:	31 c9                	xor    %ecx,%ecx
    2ec2:	45 31 c9             	xor    %r9d,%r9d
    2ec5:	45 31 e4             	xor    %r12d,%r12d
    2ec8:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    2ecd:	45 31 db             	xor    %r11d,%r11d
    2ed0:	4d 8d 6e 20          	lea    0x20(%r14),%r13
    2ed4:	4c 89 24 24          	mov    %r12,(%rsp)
    2ed8:	31 db                	xor    %ebx,%ebx
    2eda:	4d 89 de             	mov    %r11,%r14
    2edd:	49 bf db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r15
    2ee7:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2eec:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    2ef1:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    2ef6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    2f00:	49 63 55 08          	movslq 0x8(%r13),%rdx
    2f04:	85 d2                	test   %edx,%edx
    2f06:	0f 8e ce 00 00 00    	jle    2fda <main+0xa0a>
    2f0c:	49 8b 45 00          	mov    0x0(%r13),%rax
    2f10:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
    2f14:	48 8b 0c 24          	mov    (%rsp),%rcx
    2f18:	48 8d 14 72          	lea    (%rdx,%rsi,2),%rdx
    2f1c:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    2f21:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2f26:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    2f2b:	48 8d 14 d0          	lea    (%rax,%rdx,8),%rdx
    2f2f:	90                   	nop
    2f30:	48 8b 70 10          	mov    0x10(%rax),%rsi
    2f34:	48 05 98 00 00 00    	add    $0x98,%rax
    2f3a:	48 01 f1             	add    %rsi,%rcx
    2f3d:	48 8b 70 80          	mov    -0x80(%rax),%rsi
    2f41:	49 01 f0             	add    %rsi,%r8
    2f44:	48 8b 70 d0          	mov    -0x30(%rax),%rsi
    2f48:	49 01 f6             	add    %rsi,%r14
    2f4b:	48 8b 70 e0          	mov    -0x20(%rax),%rsi
    2f4f:	49 01 f1             	add    %rsi,%r9
    2f52:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f56:	48 03 6e 10          	add    0x10(%rsi),%rbp
    2f5a:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f5e:	48 03 5e 18          	add    0x18(%rsi),%rbx
    2f62:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f66:	48 03 6e 30          	add    0x30(%rsi),%rbp
    2f6a:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f6e:	48 03 5e 38          	add    0x38(%rsi),%rbx
    2f72:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f76:	48 03 6e 50          	add    0x50(%rsi),%rbp
    2f7a:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f7e:	48 03 5e 58          	add    0x58(%rsi),%rbx
    2f82:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f86:	48 03 6e 70          	add    0x70(%rsi),%rbp
    2f8a:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f8e:	48 03 5e 78          	add    0x78(%rsi),%rbx
    2f92:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2f96:	48 03 ae 90 00 00 00 	add    0x90(%rsi),%rbp
    2f9d:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2fa1:	48 03 9e 98 00 00 00 	add    0x98(%rsi),%rbx
    2fa8:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2fac:	48 03 ae b0 00 00 00 	add    0xb0(%rsi),%rbp
    2fb3:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2fb7:	48 03 9e b8 00 00 00 	add    0xb8(%rsi),%rbx
    2fbe:	48 39 d0             	cmp    %rdx,%rax
    2fc1:	0f 85 69 ff ff ff    	jne    2f30 <main+0x960>
    2fc7:	48 89 0c 24          	mov    %rcx,(%rsp)
    2fcb:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    2fd0:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2fd5:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    2fda:	45 31 e4             	xor    %r12d,%r12d
    2fdd:	49 83 7d 50 00       	cmpq   $0x0,0x50(%r13)
    2fe2:	7e 73                	jle    3057 <main+0xa87>
    2fe4:	4c 89 ed             	mov    %r13,%rbp
    2fe7:	49 89 dd             	mov    %rbx,%r13
    2fea:	4c 89 e3             	mov    %r12,%rbx
    2fed:	0f 1f 00             	nopl   (%rax)
    2ff0:	48 8b 7d 30          	mov    0x30(%rbp),%rdi
    2ff4:	48 89 de             	mov    %rbx,%rsi
    2ff7:	48 83 c3 01          	add    $0x1,%rbx
    2ffb:	48 c1 e6 04          	shl    $0x4,%rsi
    2fff:	48 01 f7             	add    %rsi,%rdi
    3002:	48 03 75 38          	add    0x38(%rbp),%rsi
    3006:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    300a:	48 2b 57 08          	sub    0x8(%rdi),%rdx
    300e:	48 89 d0             	mov    %rdx,%rax
    3011:	49 f7 e7             	mul    %r15
    3014:	31 c0                	xor    %eax,%eax
    3016:	48 89 d1             	mov    %rdx,%rcx
    3019:	48 8b 16             	mov    (%rsi),%rdx
    301c:	48 8d 35 73 33 00 00 	lea    0x3373(%rip),%rsi        # 6396 <_IO_stdin_used+0x396>
    3023:	48 2b 17             	sub    (%rdi),%rdx
    3026:	48 c1 e9 12          	shr    $0x12,%rcx
    302a:	bf 01 00 00 00       	mov    $0x1,%edi
    302f:	e8 fc f3 ff ff       	call   2430 <__printf_chk@plt>
    3034:	48 8b 55 40          	mov    0x40(%rbp),%rdx
    3038:	bf 01 00 00 00       	mov    $0x1,%edi
    303d:	31 c0                	xor    %eax,%eax
    303f:	48 8d 35 6e 33 00 00 	lea    0x336e(%rip),%rsi        # 63b4 <_IO_stdin_used+0x3b4>
    3046:	e8 e5 f3 ff ff       	call   2430 <__printf_chk@plt>
    304b:	48 39 5d 50          	cmp    %rbx,0x50(%rbp)
    304f:	7f 9f                	jg     2ff0 <main+0xa20>
    3051:	4c 89 eb             	mov    %r13,%rbx
    3054:	49 89 ed             	mov    %rbp,%r13
    3057:	45 31 e4             	xor    %r12d,%r12d
    305a:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    305f:	0f 8e 96 00 00 00    	jle    30fb <main+0xb2b>
    3065:	48 89 d8             	mov    %rbx,%rax
    3068:	4c 89 e5             	mov    %r12,%rbp
    306b:	4c 89 eb             	mov    %r13,%rbx
    306e:	49 89 c5             	mov    %rax,%r13
    3071:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3078:	48 8b 43 58          	mov    0x58(%rbx),%rax
    307c:	48 8d 54 ad 00       	lea    0x0(%rbp,%rbp,4),%rdx
    3081:	48 83 ec 08          	sub    $0x8,%rsp
    3085:	48 8d 35 ac 35 00 00 	lea    0x35ac(%rip),%rsi        # 6638 <_IO_stdin_used+0x638>
    308c:	bf 01 00 00 00       	mov    $0x1,%edi
    3091:	48 83 c5 01          	add    $0x1,%rbp
    3095:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    3099:	4c 8b 61 18          	mov    0x18(%rcx),%r12
    309d:	4c 2b 61 08          	sub    0x8(%rcx),%r12
    30a1:	4c 89 e0             	mov    %r12,%rax
    30a4:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    30a8:	4c 2b 01             	sub    (%rcx),%r8
    30ab:	49 f7 e7             	mul    %r15
    30ae:	8b 49 20             	mov    0x20(%rcx),%ecx
    30b1:	41 54                	push   %r12
    30b3:	31 c0                	xor    %eax,%eax
    30b5:	48 c1 ea 12          	shr    $0x12,%rdx
    30b9:	49 89 d1             	mov    %rdx,%r9
    30bc:	ba 06 00 00 00       	mov    $0x6,%edx
    30c1:	e8 6a f3 ff ff       	call   2430 <__printf_chk@plt>
    30c6:	48 8d 35 03 33 00 00 	lea    0x3303(%rip),%rsi        # 63d0 <_IO_stdin_used+0x3d0>
    30cd:	bf 01 00 00 00       	mov    $0x1,%edi
    30d2:	48 b8 ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%rax
    30dc:	49 f7 e4             	mul    %r12
    30df:	31 c0                	xor    %eax,%eax
    30e1:	48 c1 ea 02          	shr    $0x2,%rdx
    30e5:	e8 46 f3 ff ff       	call   2430 <__printf_chk@plt>
    30ea:	58                   	pop    %rax
    30eb:	5a                   	pop    %rdx
    30ec:	48 39 6b 68          	cmp    %rbp,0x68(%rbx)
    30f0:	7f 86                	jg     3078 <main+0xaa8>
    30f2:	4c 89 e8             	mov    %r13,%rax
    30f5:	49 89 dd             	mov    %rbx,%r13
    30f8:	48 89 c3             	mov    %rax,%rbx
    30fb:	49 8b 55 70          	mov    0x70(%r13),%rdx
    30ff:	48 8d 35 be 32 00 00 	lea    0x32be(%rip),%rsi        # 63c4 <_IO_stdin_used+0x3c4>
    3106:	bf 01 00 00 00       	mov    $0x1,%edi
    310b:	31 c0                	xor    %eax,%eax
    310d:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    3114:	e8 17 f3 ff ff       	call   2430 <__printf_chk@plt>
    3119:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    311e:	49 39 c5             	cmp    %rax,%r13
    3121:	0f 85 d9 fd ff ff    	jne    2f00 <main+0x930>
    3127:	4c 8b 24 24          	mov    (%rsp),%r12
    312b:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3130:	bf 01 00 00 00       	mov    $0x1,%edi
    3135:	31 c0                	xor    %eax,%eax
    3137:	48 8d 35 a4 32 00 00 	lea    0x32a4(%rip),%rsi        # 63e2 <_IO_stdin_used+0x3e2>
    313e:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    3143:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    3148:	49 bd 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%r13
    3152:	4c 89 e2             	mov    %r12,%rdx
    3155:	4c 89 0c 24          	mov    %r9,(%rsp)
    3159:	e8 d2 f2 ff ff       	call   2430 <__printf_chk@plt>
    315e:	bf 0a 00 00 00       	mov    $0xa,%edi
    3163:	e8 58 f1 ff ff       	call   22c0 <putchar@plt>
    3168:	4c 8b 7c 24 30       	mov    0x30(%rsp),%r15
    316d:	48 8d 35 82 32 00 00 	lea    0x3282(%rip),%rsi        # 63f6 <_IO_stdin_used+0x3f6>
    3174:	31 c0                	xor    %eax,%eax
    3176:	bf 01 00 00 00       	mov    $0x1,%edi
    317b:	49 8b 17             	mov    (%r15),%rdx
    317e:	e8 ad f2 ff ff       	call   2430 <__printf_chk@plt>
    3183:	48 8b 14 24          	mov    (%rsp),%rdx
    3187:	bf 01 00 00 00       	mov    $0x1,%edi
    318c:	31 c0                	xor    %eax,%eax
    318e:	48 8d 35 76 32 00 00 	lea    0x3276(%rip),%rsi        # 640b <_IO_stdin_used+0x40b>
    3195:	e8 96 f2 ff ff       	call   2430 <__printf_chk@plt>
    319a:	bf 0a 00 00 00       	mov    $0xa,%edi
    319f:	e8 1c f1 ff ff       	call   22c0 <putchar@plt>
    31a4:	49 8b 37             	mov    (%r15),%rsi
    31a7:	bf 01 00 00 00       	mov    $0x1,%edi
    31ac:	48 89 f0             	mov    %rsi,%rax
    31af:	49 f7 ed             	imul   %r13
    31b2:	31 c0                	xor    %eax,%eax
    31b4:	48 01 f2             	add    %rsi,%rdx
    31b7:	48 c1 fe 3f          	sar    $0x3f,%rsi
    31bb:	48 c1 fa 04          	sar    $0x4,%rdx
    31bf:	48 29 f2             	sub    %rsi,%rdx
    31c2:	48 8d 35 a7 34 00 00 	lea    0x34a7(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    31c9:	e8 62 f2 ff ff       	call   2430 <__printf_chk@plt>
    31ce:	49 8b 57 08          	mov    0x8(%r15),%rdx
    31d2:	bf 01 00 00 00       	mov    $0x1,%edi
    31d7:	31 c0                	xor    %eax,%eax
    31d9:	48 8d 35 b0 34 00 00 	lea    0x34b0(%rip),%rsi        # 6690 <_IO_stdin_used+0x690>
    31e0:	e8 4b f2 ff ff       	call   2430 <__printf_chk@plt>
    31e5:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    31ea:	bf 01 00 00 00       	mov    $0x1,%edi
    31ef:	48 8d 35 c2 34 00 00 	lea    0x34c2(%rip),%rsi        # 66b8 <_IO_stdin_used+0x6b8>
    31f6:	4c 89 d8             	mov    %r11,%rax
    31f9:	49 f7 ed             	imul   %r13
    31fc:	31 c0                	xor    %eax,%eax
    31fe:	4c 01 da             	add    %r11,%rdx
    3201:	49 c1 fb 3f          	sar    $0x3f,%r11
    3205:	48 c1 fa 04          	sar    $0x4,%rdx
    3209:	4c 29 da             	sub    %r11,%rdx
    320c:	e8 1f f2 ff ff       	call   2430 <__printf_chk@plt>
    3211:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    3216:	bf 01 00 00 00       	mov    $0x1,%edi
    321b:	48 8d 35 c6 34 00 00 	lea    0x34c6(%rip),%rsi        # 66e8 <_IO_stdin_used+0x6e8>
    3222:	48 89 c8             	mov    %rcx,%rax
    3225:	49 f7 ed             	imul   %r13
    3228:	31 c0                	xor    %eax,%eax
    322a:	48 01 ca             	add    %rcx,%rdx
    322d:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3231:	48 c1 fa 04          	sar    $0x4,%rdx
    3235:	48 29 ca             	sub    %rcx,%rdx
    3238:	e8 f3 f1 ff ff       	call   2430 <__printf_chk@plt>
    323d:	4c 89 e0             	mov    %r12,%rax
    3240:	bf 01 00 00 00       	mov    $0x1,%edi
    3245:	48 8d 35 cc 34 00 00 	lea    0x34cc(%rip),%rsi        # 6718 <_IO_stdin_used+0x718>
    324c:	49 f7 ed             	imul   %r13
    324f:	4c 01 e2             	add    %r12,%rdx
    3252:	49 c1 fc 3f          	sar    $0x3f,%r12
    3256:	31 c0                	xor    %eax,%eax
    3258:	48 c1 fa 04          	sar    $0x4,%rdx
    325c:	4c 29 e2             	sub    %r12,%rdx
    325f:	e8 cc f1 ff ff       	call   2430 <__printf_chk@plt>
    3264:	48 89 e8             	mov    %rbp,%rax
    3267:	bf 01 00 00 00       	mov    $0x1,%edi
    326c:	48 8d 35 a5 31 00 00 	lea    0x31a5(%rip),%rsi        # 6418 <_IO_stdin_used+0x418>
    3273:	49 f7 ed             	imul   %r13
    3276:	31 c0                	xor    %eax,%eax
    3278:	48 01 ea             	add    %rbp,%rdx
    327b:	48 c1 fd 3f          	sar    $0x3f,%rbp
    327f:	48 c1 fa 04          	sar    $0x4,%rdx
    3283:	48 29 ea             	sub    %rbp,%rdx
    3286:	e8 a5 f1 ff ff       	call   2430 <__printf_chk@plt>
    328b:	48 89 d8             	mov    %rbx,%rax
    328e:	bf 01 00 00 00       	mov    $0x1,%edi
    3293:	48 8d 35 8f 31 00 00 	lea    0x318f(%rip),%rsi        # 6429 <_IO_stdin_used+0x429>
    329a:	49 f7 ed             	imul   %r13
    329d:	31 c0                	xor    %eax,%eax
    329f:	48 01 da             	add    %rbx,%rdx
    32a2:	48 c1 fb 3f          	sar    $0x3f,%rbx
    32a6:	48 c1 fa 04          	sar    $0x4,%rdx
    32aa:	48 29 da             	sub    %rbx,%rdx
    32ad:	e8 7e f1 ff ff       	call   2430 <__printf_chk@plt>
    32b2:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    32b7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    32c0:	75 55                	jne    3317 <main+0xd47>
    32c2:	48 83 c4 58          	add    $0x58,%rsp
    32c6:	31 c0                	xor    %eax,%eax
    32c8:	5b                   	pop    %rbx
    32c9:	5d                   	pop    %rbp
    32ca:	41 5c                	pop    %r12
    32cc:	41 5d                	pop    %r13
    32ce:	41 5e                	pop    %r14
    32d0:	41 5f                	pop    %r15
    32d2:	c3                   	ret
    32d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    32d8:	48 8d 05 f1 1f 00 00 	lea    0x1ff1(%rip),%rax        # 52d0 <barriered_work>
    32df:	49 89 45 20          	mov    %rax,0x20(%r13)
    32e3:	e9 e3 f7 ff ff       	jmp    2acb <main+0x4fb>
    32e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    32f0:	48 8d 05 19 01 00 00 	lea    0x119(%rip),%rax        # 3410 <do_protected_write>
    32f7:	48 89 45 28          	mov    %rax,0x28(%rbp)
    32fb:	e9 ec f5 ff ff       	jmp    28ec <main+0x31c>
    3300:	48 8d 05 c9 1f 00 00 	lea    0x1fc9(%rip),%rax        # 52d0 <barriered_work>
    3307:	bd 03 00 00 00       	mov    $0x3,%ebp
    330c:	49 89 45 20          	mov    %rax,0x20(%r13)
    3310:	89 eb                	mov    %ebp,%ebx
    3312:	e9 b7 f5 ff ff       	jmp    28ce <main+0x2fe>
    3317:	e8 f4 ef ff ff       	call   2310 <__stack_chk_fail@plt>
    331c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003320 <_start>:
    3320:	f3 0f 1e fa          	endbr64
    3324:	31 ed                	xor    %ebp,%ebp
    3326:	49 89 d1             	mov    %rdx,%r9
    3329:	5e                   	pop    %rsi
    332a:	48 89 e2             	mov    %rsp,%rdx
    332d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3331:	50                   	push   %rax
    3332:	54                   	push   %rsp
    3333:	45 31 c0             	xor    %r8d,%r8d
    3336:	31 c9                	xor    %ecx,%ecx
    3338:	48 8d 3d 91 f2 ff ff 	lea    -0xd6f(%rip),%rdi        # 25d0 <main>
    333f:	ff 15 93 5c 00 00    	call   *0x5c93(%rip)        # 8fd8 <__libc_start_main@GLIBC_2.34>
    3345:	f4                   	hlt
    3346:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003350 <deregister_tm_clones>:
    3350:	48 8d 3d c9 5c 00 00 	lea    0x5cc9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3357:	48 8d 05 c2 5c 00 00 	lea    0x5cc2(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    335e:	48 39 f8             	cmp    %rdi,%rax
    3361:	74 15                	je     3378 <deregister_tm_clones+0x28>
    3363:	48 8b 05 76 5c 00 00 	mov    0x5c76(%rip),%rax        # 8fe0 <_ITM_deregisterTMCloneTable@Base>
    336a:	48 85 c0             	test   %rax,%rax
    336d:	74 09                	je     3378 <deregister_tm_clones+0x28>
    336f:	ff e0                	jmp    *%rax
    3371:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3378:	c3                   	ret
    3379:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003380 <register_tm_clones>:
    3380:	48 8d 3d 99 5c 00 00 	lea    0x5c99(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3387:	48 8d 35 92 5c 00 00 	lea    0x5c92(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    338e:	48 29 fe             	sub    %rdi,%rsi
    3391:	48 89 f0             	mov    %rsi,%rax
    3394:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3398:	48 c1 f8 03          	sar    $0x3,%rax
    339c:	48 01 c6             	add    %rax,%rsi
    339f:	48 d1 fe             	sar    %rsi
    33a2:	74 14                	je     33b8 <register_tm_clones+0x38>
    33a4:	48 8b 05 45 5c 00 00 	mov    0x5c45(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    33ab:	48 85 c0             	test   %rax,%rax
    33ae:	74 08                	je     33b8 <register_tm_clones+0x38>
    33b0:	ff e0                	jmp    *%rax
    33b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    33b8:	c3                   	ret
    33b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000033c0 <__do_global_dtors_aux>:
    33c0:	f3 0f 1e fa          	endbr64
    33c4:	80 3d 5d 5c 00 00 00 	cmpb   $0x0,0x5c5d(%rip)        # 9028 <completed.0>
    33cb:	75 2b                	jne    33f8 <__do_global_dtors_aux+0x38>
    33cd:	55                   	push   %rbp
    33ce:	48 83 3d 22 5c 00 00 00 	cmpq   $0x0,0x5c22(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    33d6:	48 89 e5             	mov    %rsp,%rbp
    33d9:	74 0c                	je     33e7 <__do_global_dtors_aux+0x27>
    33db:	48 8b 3d 26 5c 00 00 	mov    0x5c26(%rip),%rdi        # 9008 <__dso_handle>
    33e2:	e8 b9 ee ff ff       	call   22a0 <__cxa_finalize@plt>
    33e7:	e8 64 ff ff ff       	call   3350 <deregister_tm_clones>
    33ec:	c6 05 35 5c 00 00 01 	movb   $0x1,0x5c35(%rip)        # 9028 <completed.0>
    33f3:	5d                   	pop    %rbp
    33f4:	c3                   	ret
    33f5:	0f 1f 00             	nopl   (%rax)
    33f8:	c3                   	ret
    33f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003400 <frame_dummy>:
    3400:	f3 0f 1e fa          	endbr64
    3404:	e9 77 ff ff ff       	jmp    3380 <register_tm_clones>
    3409:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003410 <do_protected_write>:
    3410:	f3 0f 1e fa          	endbr64
    3414:	48 8b 47 30          	mov    0x30(%rdi),%rax
    3418:	48 8b 57 18          	mov    0x18(%rdi),%rdx
    341c:	48 8b 40 30          	mov    0x30(%rax),%rax
    3420:	48 83 c2 01          	add    $0x1,%rdx
    3424:	48 89 57 18          	mov    %rdx,0x18(%rdi)
    3428:	48 8b 48 08          	mov    0x8(%rax),%rcx
    342c:	48 83 00 01          	addq   $0x1,(%rax)
    3430:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3437:	48 85 c9             	test   %rcx,%rcx
    343a:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3441:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3445:	48 89 50 08          	mov    %rdx,0x8(%rax)
    3449:	31 c0                	xor    %eax,%eax
    344b:	c3                   	ret
    344c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003450 <barriered_reset>:
    3450:	f3 0f 1e fa          	endbr64
    3454:	8b 47 44             	mov    0x44(%rdi),%eax
    3457:	48 89 fa             	mov    %rdi,%rdx
    345a:	85 c0                	test   %eax,%eax
    345c:	7e 55                	jle    34b3 <barriered_reset+0x63>
    345e:	31 c9                	xor    %ecx,%ecx
    3460:	31 f6                	xor    %esi,%esi
    3462:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3468:	48 8b 7a 30          	mov    0x30(%rdx),%rdi
    346c:	48 63 42 38          	movslq 0x38(%rdx),%rax
    3470:	83 c6 01             	add    $0x1,%esi
    3473:	4c 8d 04 c0          	lea    (%rax,%rax,8),%r8
    3477:	4a 8d 04 40          	lea    (%rax,%r8,2),%rax
    347b:	4c 8b 47 10          	mov    0x10(%rdi),%r8
    347f:	49 8d 04 c0          	lea    (%r8,%rax,8),%rax
    3483:	48 8b 78 20          	mov    0x20(%rax),%rdi
    3487:	48 01 cf             	add    %rcx,%rdi
    348a:	8b 47 08             	mov    0x8(%rdi),%eax
    348d:	83 c0 01             	add    $0x1,%eax
    3490:	89 47 08             	mov    %eax,0x8(%rdi)
    3493:	48 8b 42 30          	mov    0x30(%rdx),%rax
    3497:	48 8b 78 20          	mov    0x20(%rax),%rdi
    349b:	48 01 cf             	add    %rcx,%rdi
    349e:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    34a5:	c7 47 40 01 00 00 00 	movl   $0x1,0x40(%rdi)
    34ac:	8b 42 44             	mov    0x44(%rdx),%eax
    34af:	39 f0                	cmp    %esi,%eax
    34b1:	7f b5                	jg     3468 <barriered_reset+0x18>
    34b3:	0f ae f0             	mfence
    34b6:	31 c0                	xor    %eax,%eax
    34b8:	c3                   	ret
    34b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000034c0 <barriered_thread>:
    34c0:	f3 0f 1e fa          	endbr64
    34c4:	8b 47 2c             	mov    0x2c(%rdi),%eax
    34c7:	83 f8 01             	cmp    $0x1,%eax
    34ca:	0f 85 70 02 00 00    	jne    3740 <barriered_thread+0x280>
    34d0:	41 55                	push   %r13
    34d2:	45 31 ed             	xor    %r13d,%r13d
    34d5:	41 54                	push   %r12
    34d7:	49 89 fc             	mov    %rdi,%r12
    34da:	55                   	push   %rbp
    34db:	53                   	push   %rbx
    34dc:	31 db                	xor    %ebx,%ebx
    34de:	48 83 ec 08          	sub    $0x8,%rsp
    34e2:	44 8b 57 28          	mov    0x28(%rdi),%r10d
    34e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    34f0:	44 39 d3             	cmp    %r10d,%ebx
    34f3:	0f 8d 8f 01 00 00    	jge    3688 <barriered_thread+0x1c8>
    34f9:	48 63 c3             	movslq %ebx,%rax
    34fc:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3500:	48 8d 2c 50          	lea    (%rax,%rdx,2),%rbp
    3504:	48 c1 e5 03          	shl    $0x3,%rbp
    3508:	eb 19                	jmp    3523 <barriered_thread+0x63>
    350a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3510:	83 c3 01             	add    $0x1,%ebx
    3513:	48 81 c5 98 00 00 00 	add    $0x98,%rbp
    351a:	44 39 d3             	cmp    %r10d,%ebx
    351d:	0f 8d 3d 01 00 00    	jge    3660 <barriered_thread+0x1a0>
    3523:	49 8b 54 24 20       	mov    0x20(%r12),%rdx
    3528:	48 01 ea             	add    %rbp,%rdx
    352b:	8b 42 40             	mov    0x40(%rdx),%eax
    352e:	83 f8 01             	cmp    $0x1,%eax
    3531:	75 dd                	jne    3510 <barriered_thread+0x50>
    3533:	85 db                	test   %ebx,%ebx
    3535:	0f 8e 65 01 00 00    	jle    36a0 <barriered_thread+0x1e0>
    353b:	45 8b 5c 24 18       	mov    0x18(%r12),%r11d
    3540:	8d 43 ff             	lea    -0x1(%rbx),%eax
    3543:	45 85 db             	test   %r11d,%r11d
    3546:	7e 6d                	jle    35b5 <barriered_thread+0xf5>
    3548:	48 98                	cltq
    354a:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    354e:	4c 8d 04 48          	lea    (%rax,%rcx,2),%r8
    3552:	49 63 cb             	movslq %r11d,%rcx
    3555:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    355a:	48 8d 34 c9          	lea    (%rcx,%rcx,8),%rsi
    355e:	49 c1 e0 03          	shl    $0x3,%r8
    3562:	48 8d 0c 71          	lea    (%rcx,%rsi,2),%rcx
    3566:	4c 8d 0c c8          	lea    (%rax,%rcx,8),%r9
    356a:	31 c9                	xor    %ecx,%ecx
    356c:	0f 1f 40 00          	nopl   0x0(%rax)
    3570:	48 8b 70 20          	mov    0x20(%rax),%rsi
    3574:	4c 01 c6             	add    %r8,%rsi
    3577:	8b 76 08             	mov    0x8(%rsi),%esi
    357a:	8b 7a 08             	mov    0x8(%rdx),%edi
    357d:	39 f7                	cmp    %esi,%edi
    357f:	40 0f 94 c6          	sete   %sil
    3583:	48 05 98 00 00 00    	add    $0x98,%rax
    3589:	40 0f b6 f6          	movzbl %sil,%esi
    358d:	01 f1                	add    %esi,%ecx
    358f:	4c 39 c8             	cmp    %r9,%rax
    3592:	75 dc                	jne    3570 <barriered_thread+0xb0>
    3594:	44 39 d9             	cmp    %r11d,%ecx
    3597:	74 08                	je     35a1 <barriered_thread+0xe1>
    3599:	85 c9                	test   %ecx,%ecx
    359b:	0f 85 bf 00 00 00    	jne    3660 <barriered_thread+0x1a0>
    35a1:	85 db                	test   %ebx,%ebx
    35a3:	75 10                	jne    35b5 <barriered_thread+0xf5>
    35a5:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    35aa:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    35af:	0f 8c 73 01 00 00    	jl     3728 <barriered_thread+0x268>
    35b5:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    35bd:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    35c1:	49 8b 44 24 78       	mov    0x78(%r12),%rax
    35c6:	41 83 fd 01          	cmp    $0x1,%r13d
    35ca:	0f 84 20 01 00 00    	je     36f0 <barriered_thread+0x230>
    35d0:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    35d4:	bf 04 00 00 00       	mov    $0x4,%edi
    35d9:	41 bd 01 00 00 00    	mov    $0x1,%r13d
    35df:	89 5e 20             	mov    %ebx,0x20(%rsi)
    35e2:	e8 09 ed ff ff       	call   22f0 <clock_gettime@plt>
    35e7:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    35ec:	48 01 e8             	add    %rbp,%rax
    35ef:	c7 40 40 00 00 00 00 	movl   $0x0,0x40(%rax)
    35f6:	48 8b 50 20          	mov    0x20(%rax),%rdx
    35fa:	49 63 04 24          	movslq (%r12),%rax
    35fe:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    3602:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    3606:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
    360b:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    360f:	48 8b 78 20          	mov    0x20(%rax),%rdi
    3613:	48 01 ef             	add    %rbp,%rdi
    3616:	ff d2                	call   *%rdx
    3618:	49 8b 54 24 20       	mov    0x20(%r12),%rdx
    361d:	48 01 ea             	add    %rbp,%rdx
    3620:	8b 42 08             	mov    0x8(%rdx),%eax
    3623:	83 c0 01             	add    $0x1,%eax
    3626:	89 42 08             	mov    %eax,0x8(%rdx)
    3629:	41 8b 44 24 28       	mov    0x28(%r12),%eax
    362e:	49 83 44 24 60 01    	addq   $0x1,0x60(%r12)
    3634:	83 e8 01             	sub    $0x1,%eax
    3637:	39 d8                	cmp    %ebx,%eax
    3639:	0f 84 81 00 00 00    	je     36c0 <barriered_thread+0x200>
    363f:	0f ae f0             	mfence
    3642:	45 8b 54 24 28       	mov    0x28(%r12),%r10d
    3647:	83 c3 01             	add    $0x1,%ebx
    364a:	48 81 c5 98 00 00 00 	add    $0x98,%rbp
    3651:	44 39 d3             	cmp    %r10d,%ebx
    3654:	0f 8c c9 fe ff ff    	jl     3523 <barriered_thread+0x63>
    365a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3660:	41 8b 44 24 2c       	mov    0x2c(%r12),%eax
    3665:	83 f8 01             	cmp    $0x1,%eax
    3668:	0f 84 82 fe ff ff    	je     34f0 <barriered_thread+0x30>
    366e:	48 83 c4 08          	add    $0x8,%rsp
    3672:	31 c0                	xor    %eax,%eax
    3674:	5b                   	pop    %rbx
    3675:	5d                   	pop    %rbp
    3676:	41 5c                	pop    %r12
    3678:	41 5d                	pop    %r13
    367a:	c3                   	ret
    367b:	41 8b 44 24 2c       	mov    0x2c(%r12),%eax
    3680:	83 f8 01             	cmp    $0x1,%eax
    3683:	75 e9                	jne    366e <barriered_thread+0x1ae>
    3685:	0f 1f 00             	nopl   (%rax)
    3688:	49 83 84 24 90 00 00 00 01 	addq   $0x1,0x90(%r12)
    3691:	45 85 d2             	test   %r10d,%r10d
    3694:	7e e5                	jle    367b <barriered_thread+0x1bb>
    3696:	31 db                	xor    %ebx,%ebx
    3698:	e9 5c fe ff ff       	jmp    34f9 <barriered_thread+0x39>
    369d:	0f 1f 00             	nopl   (%rax)
    36a0:	45 8b 5c 24 18       	mov    0x18(%r12),%r11d
    36a5:	41 8d 42 ff          	lea    -0x1(%r10),%eax
    36a9:	45 85 db             	test   %r11d,%r11d
    36ac:	0f 8f 96 fe ff ff    	jg     3548 <barriered_thread+0x88>
    36b2:	e9 ea fe ff ff       	jmp    35a1 <barriered_thread+0xe1>
    36b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    36c0:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    36c5:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    36ca:	0f 8d 6f ff ff ff    	jge    363f <barriered_thread+0x17f>
    36d0:	48 c1 e6 04          	shl    $0x4,%rsi
    36d4:	bf 04 00 00 00       	mov    $0x4,%edi
    36d9:	49 03 74 24 58       	add    0x58(%r12),%rsi
    36de:	e8 0d ec ff ff       	call   22f0 <clock_gettime@plt>
    36e3:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
    36e9:	e9 51 ff ff ff       	jmp    363f <barriered_thread+0x17f>
    36ee:	66 90                	xchg   %ax,%ax
    36f0:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    36f5:	bf 04 00 00 00       	mov    $0x4,%edi
    36fa:	45 31 ed             	xor    %r13d,%r13d
    36fd:	e8 ee eb ff ff       	call   22f0 <clock_gettime@plt>
    3702:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    370a:	48 83 c0 01          	add    $0x1,%rax
    370e:	48 99                	cqto
    3710:	49 f7 bc 24 88 00 00 00 	idivq  0x88(%r12)
    3718:	49 89 94 24 80 00 00 00 	mov    %rdx,0x80(%r12)
    3720:	e9 c2 fe ff ff       	jmp    35e7 <barriered_thread+0x127>
    3725:	0f 1f 00             	nopl   (%rax)
    3728:	48 c1 e6 04          	shl    $0x4,%rsi
    372c:	bf 04 00 00 00       	mov    $0x4,%edi
    3731:	49 03 74 24 50       	add    0x50(%r12),%rsi
    3736:	e8 b5 eb ff ff       	call   22f0 <clock_gettime@plt>
    373b:	e9 75 fe ff ff       	jmp    35b5 <barriered_thread+0xf5>
    3740:	31 c0                	xor    %eax,%eax
    3742:	c3                   	ret
    3743:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    374e:	66 90                	xchg   %ax,%ax

0000000000003750 <external_thread>:
    3750:	f3 0f 1e fa          	endbr64
    3754:	41 55                	push   %r13
    3756:	41 54                	push   %r12
    3758:	55                   	push   %rbp
    3759:	53                   	push   %rbx
    375a:	48 83 ec 38          	sub    $0x38,%rsp
    375e:	66 0f 6f 05 ca 31 00 00 	movdqa 0x31ca(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3766:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    376f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3774:	31 c0                	xor    %eax,%eax
    3776:	0f 29 04 24          	movaps %xmm0,(%rsp)
    377a:	8b 47 2c             	mov    0x2c(%rdi),%eax
    377d:	83 f8 01             	cmp    $0x1,%eax
    3780:	75 64                	jne    37e6 <external_thread+0x96>
    3782:	49 89 fd             	mov    %rdi,%r13
    3785:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    378a:	48 89 e3             	mov    %rsp,%rbx
    378d:	4c 8d 25 70 28 00 00 	lea    0x2870(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    3794:	0f 1f 40 00          	nopl   0x0(%rax)
    3798:	48 89 ee             	mov    %rbp,%rsi
    379b:	48 89 df             	mov    %rbx,%rdi
    379e:	e8 8d eb ff ff       	call   2330 <nanosleep@plt>
    37a3:	49 8b 45 38          	mov    0x38(%r13),%rax
    37a7:	48 63 08             	movslq (%rax),%rcx
    37aa:	85 c9                	test   %ecx,%ecx
    37ac:	7e 2c                	jle    37da <external_thread+0x8a>
    37ae:	48 8b 40 08          	mov    0x8(%rax),%rax
    37b2:	48 c1 e1 04          	shl    $0x4,%rcx
    37b6:	48 01 c1             	add    %rax,%rcx
    37b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    37c0:	8b 50 08             	mov    0x8(%rax),%edx
    37c3:	85 d2                	test   %edx,%edx
    37c5:	75 0a                	jne    37d1 <external_thread+0x81>
    37c7:	4c 89 20             	mov    %r12,(%rax)
    37ca:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    37d1:	48 83 c0 10          	add    $0x10,%rax
    37d5:	48 39 c1             	cmp    %rax,%rcx
    37d8:	75 e6                	jne    37c0 <external_thread+0x70>
    37da:	0f ae f0             	mfence
    37dd:	41 8b 45 2c          	mov    0x2c(%r13),%eax
    37e1:	83 f8 01             	cmp    $0x1,%eax
    37e4:	74 b2                	je     3798 <external_thread+0x48>
    37e6:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    37eb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    37f4:	75 0d                	jne    3803 <external_thread+0xb3>
    37f6:	48 83 c4 38          	add    $0x38,%rsp
    37fa:	31 c0                	xor    %eax,%eax
    37fc:	5b                   	pop    %rbx
    37fd:	5d                   	pop    %rbp
    37fe:	41 5c                	pop    %r12
    3800:	41 5d                	pop    %r13
    3802:	c3                   	ret
    3803:	e8 08 eb ff ff       	call   2310 <__stack_chk_fail@plt>
    3808:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000003810 <timer_thread>:
    3810:	f3 0f 1e fa          	endbr64
    3814:	41 57                	push   %r15
    3816:	48 8d 35 f3 27 00 00 	lea    0x27f3(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    381d:	49 89 ff             	mov    %rdi,%r15
    3820:	41 56                	push   %r14
    3822:	41 55                	push   %r13
    3824:	41 54                	push   %r12
    3826:	55                   	push   %rbp
    3827:	53                   	push   %rbx
    3828:	48 83 ec 58          	sub    $0x58,%rsp
    382c:	8b 17                	mov    (%rdi),%edx
    382e:	bf 01 00 00 00       	mov    $0x1,%edi
    3833:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    383c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3841:	31 c0                	xor    %eax,%eax
    3843:	e8 e8 eb ff ff       	call   2430 <__printf_chk@plt>
    3848:	66 0f 6f 05 e0 30 00 00 	movdqa 0x30e0(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3850:	ba 30 75 00 00       	mov    $0x7530,%edx
    3855:	31 c0                	xor    %eax,%eax
    3857:	48 8d 35 c4 27 00 00 	lea    0x27c4(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    385e:	bf 01 00 00 00       	mov    $0x1,%edi
    3863:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3868:	e8 c3 eb ff ff       	call   2430 <__printf_chk@plt>
    386d:	45 8b 6f 2c          	mov    0x2c(%r15),%r13d
    3871:	45 85 ed             	test   %r13d,%r13d
    3874:	0f 84 a9 00 00 00    	je     3923 <timer_thread+0x113>
    387a:	45 31 f6             	xor    %r14d,%r14d
    387d:	45 31 ed             	xor    %r13d,%r13d
    3880:	49 89 e4             	mov    %rsp,%r12
    3883:	31 db                	xor    %ebx,%ebx
    3885:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    388a:	48 89 ef             	mov    %rbp,%rdi
    388d:	4c 89 e6             	mov    %r12,%rsi
    3890:	41 83 c6 01          	add    $0x1,%r14d
    3894:	e8 97 ea ff ff       	call   2330 <nanosleep@plt>
    3899:	49 63 47 18          	movslq 0x18(%r15),%rax
    389d:	41 8d 7d 01          	lea    0x1(%r13),%edi
    38a1:	85 c0                	test   %eax,%eax
    38a3:	7e 59                	jle    38fe <timer_thread+0xee>
    38a5:	4b 8d 54 ed 00       	lea    0x0(%r13,%r13,8),%rdx
    38aa:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    38ae:	4d 8d 44 55 00       	lea    0x0(%r13,%rdx,2),%r8
    38b3:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    38b7:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    38bb:	49 c1 e0 03          	shl    $0x3,%r8
    38bf:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    38c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    38c8:	89 f8                	mov    %edi,%eax
    38ca:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    38ce:	99                   	cltd
    38cf:	f7 79 28             	idivl  0x28(%rcx)
    38d2:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    38d9:	48 63 d2             	movslq %edx,%rdx
    38dc:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    38e0:	48 8d 04 42          	lea    (%rdx,%rax,2),%rax
    38e4:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    38e8:	4c 01 c6             	add    %r8,%rsi
    38eb:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    38f2:	c7 46 48 00 00 00 00 	movl   $0x0,0x48(%rsi)
    38f9:	49 39 c9             	cmp    %rcx,%r9
    38fc:	75 ca                	jne    38c8 <timer_thread+0xb8>
    38fe:	0f ae f0             	mfence
    3901:	49 8b 47 10          	mov    0x10(%r15),%rax
    3905:	39 78 28             	cmp    %edi,0x28(%rax)
    3908:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    390c:	0f 4e fb             	cmovle %ebx,%edi
    390f:	4c 63 ef             	movslq %edi,%r13
    3912:	85 c0                	test   %eax,%eax
    3914:	74 0d                	je     3923 <timer_thread+0x113>
    3916:	41 81 fe 30 75 00 00 	cmp    $0x7530,%r14d
    391d:	0f 85 67 ff ff ff    	jne    388a <timer_thread+0x7a>
    3923:	48 8d 3d 0e 27 00 00 	lea    0x270e(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    392a:	e8 a1 e9 ff ff       	call   22d0 <puts@plt>
    392f:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3933:	85 d2                	test   %edx,%edx
    3935:	7e 72                	jle    39a9 <timer_thread+0x199>
    3937:	49 63 47 28          	movslq 0x28(%r15),%rax
    393b:	85 c0                	test   %eax,%eax
    393d:	7e 6a                	jle    39a9 <timer_thread+0x199>
    393f:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3943:	4d 8b 4f 10          	mov    0x10(%r15),%r9
    3947:	31 f6                	xor    %esi,%esi
    3949:	4c 8d 04 4a          	lea    (%rdx,%rcx,2),%r8
    394d:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3951:	48 8d 3c 50          	lea    (%rax,%rdx,2),%rdi
    3955:	49 c1 e0 03          	shl    $0x3,%r8
    3959:	48 c1 e7 03          	shl    $0x3,%rdi
    395d:	49 8b 44 31 20       	mov    0x20(%r9,%rsi,1),%rax
    3962:	48 8d 0c 07          	lea    (%rdi,%rax,1),%rcx
    3966:	40 f6 c7 08          	test   $0x8,%dil
    396a:	74 15                	je     3981 <timer_thread+0x171>
    396c:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    3976:	48 05 98 00 00 00    	add    $0x98,%rax
    397c:	48 39 c1             	cmp    %rax,%rcx
    397f:	74 1c                	je     399d <timer_thread+0x18d>
    3981:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    398b:	48 05 30 01 00 00    	add    $0x130,%rax
    3991:	c7 40 e8 00 00 00 00 	movl   $0x0,-0x18(%rax)
    3998:	48 39 c1             	cmp    %rax,%rcx
    399b:	75 e4                	jne    3981 <timer_thread+0x171>
    399d:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
    39a4:	49 39 f0             	cmp    %rsi,%r8
    39a7:	75 b4                	jne    395d <timer_thread+0x14d>
    39a9:	0f ae f0             	mfence
    39ac:	66 0f 6f 05 8c 2f 00 00 	movdqa 0x2f8c(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    39b4:	48 8d 2d a2 26 00 00 	lea    0x26a2(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    39bb:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    39c0:	49 63 47 18          	movslq 0x18(%r15),%rax
    39c4:	41 8d 7d 01          	lea    0x1(%r13),%edi
    39c8:	85 c0                	test   %eax,%eax
    39ca:	7e 5a                	jle    3a26 <timer_thread+0x216>
    39cc:	4d 63 ed             	movslq %r13d,%r13
    39cf:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    39d3:	4b 8d 54 ed 00       	lea    0x0(%r13,%r13,8),%rdx
    39d8:	4d 8d 44 55 00       	lea    0x0(%r13,%rdx,2),%r8
    39dd:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    39e1:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    39e5:	49 c1 e0 03          	shl    $0x3,%r8
    39e9:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    39ed:	0f 1f 00             	nopl   (%rax)
    39f0:	89 f8                	mov    %edi,%eax
    39f2:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    39f6:	99                   	cltd
    39f7:	f7 79 28             	idivl  0x28(%rcx)
    39fa:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3a01:	48 63 c2             	movslq %edx,%rax
    3a04:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3a08:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3a0c:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    3a10:	4c 01 c6             	add    %r8,%rsi
    3a13:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    3a1a:	c7 46 48 00 00 00 00 	movl   $0x0,0x48(%rsi)
    3a21:	49 39 c9             	cmp    %rcx,%r9
    3a24:	75 ca                	jne    39f0 <timer_thread+0x1e0>
    3a26:	0f ae f0             	mfence
    3a29:	49 8b 47 10          	mov    0x10(%r15),%rax
    3a2d:	45 8b 47 18          	mov    0x18(%r15),%r8d
    3a31:	45 31 ed             	xor    %r13d,%r13d
    3a34:	39 78 28             	cmp    %edi,0x28(%rax)
    3a37:	44 0f 4f ef          	cmovg  %edi,%r13d
    3a3b:	45 85 c0             	test   %r8d,%r8d
    3a3e:	0f 8e df 00 00 00    	jle    3b23 <timer_thread+0x313>
    3a44:	31 db                	xor    %ebx,%ebx
    3a46:	45 31 e4             	xor    %r12d,%r12d
    3a49:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3a4f:	90                   	nop
    3a50:	45 31 f6             	xor    %r14d,%r14d
    3a53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3a58:	48 8b 44 18 20       	mov    0x20(%rax,%rbx,1),%rax
    3a5d:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    3a61:	49 63 f8             	movslq %r8d,%rdi
    3a64:	49 8d 14 56          	lea    (%r14,%rdx,2),%rdx
    3a68:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    3a6c:	31 c0                	xor    %eax,%eax
    3a6e:	eb 1b                	jmp    3a8b <timer_thread+0x27b>
    3a70:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    3a74:	48 8b 74 16 08       	mov    0x8(%rsi,%rdx,1),%rsi
    3a79:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    3a7d:	48 85 f6             	test   %rsi,%rsi
    3a80:	7f 21                	jg     3aa3 <timer_thread+0x293>
    3a82:	48 83 c0 01          	add    $0x1,%rax
    3a86:	48 39 f8             	cmp    %rdi,%rax
    3a89:	74 49                	je     3ad4 <timer_thread+0x2c4>
    3a8b:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    3a8f:	48 89 c2             	mov    %rax,%rdx
    3a92:	48 c1 e2 05          	shl    $0x5,%rdx
    3a96:	48 8b 34 16          	mov    (%rsi,%rdx,1),%rsi
    3a9a:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    3a9e:	48 85 f6             	test   %rsi,%rsi
    3aa1:	7e cd                	jle    3a70 <timer_thread+0x260>
    3aa3:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    3aa7:	bf 01 00 00 00       	mov    $0x1,%edi
    3aac:	48 8b 74 16 08       	mov    0x8(%rsi,%rdx,1),%rsi
    3ab1:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3ab5:	48 8b 49 70          	mov    0x70(%rcx),%rcx
    3ab9:	48 89 ee             	mov    %rbp,%rsi
    3abc:	48 8b 14 11          	mov    (%rcx,%rdx,1),%rdx
    3ac0:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    3ac4:	89 c2                	mov    %eax,%edx
    3ac6:	31 c0                	xor    %eax,%eax
    3ac8:	e8 63 e9 ff ff       	call   2430 <__printf_chk@plt>
    3acd:	45 8b 47 18          	mov    0x18(%r15),%r8d
    3ad1:	45 31 c9             	xor    %r9d,%r9d
    3ad4:	49 83 c6 01          	add    $0x1,%r14
    3ad8:	45 39 f0             	cmp    %r14d,%r8d
    3adb:	7e 13                	jle    3af0 <timer_thread+0x2e0>
    3add:	49 8b 47 10          	mov    0x10(%r15),%rax
    3ae1:	e9 72 ff ff ff       	jmp    3a58 <timer_thread+0x248>
    3ae6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3af0:	41 83 c4 01          	add    $0x1,%r12d
    3af4:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3afb:	45 39 e0             	cmp    %r12d,%r8d
    3afe:	7e 09                	jle    3b09 <timer_thread+0x2f9>
    3b00:	49 8b 47 10          	mov    0x10(%r15),%rax
    3b04:	e9 47 ff ff ff       	jmp    3a50 <timer_thread+0x240>
    3b09:	41 83 f9 01          	cmp    $0x1,%r9d
    3b0d:	74 14                	je     3b23 <timer_thread+0x313>
    3b0f:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3b14:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3b19:	e8 12 e8 ff ff       	call   2330 <nanosleep@plt>
    3b1e:	e9 9d fe ff ff       	jmp    39c0 <timer_thread+0x1b0>
    3b23:	48 8d 3d 2a 25 00 00 	lea    0x252a(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3b2a:	48 8d 2d 4f 25 00 00 	lea    0x254f(%rip),%rbp        # 6080 <_IO_stdin_used+0x80>
    3b31:	e8 9a e7 ff ff       	call   22d0 <puts@plt>
    3b36:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3b3a:	48 8d 1d 2d 25 00 00 	lea    0x252d(%rip),%rbx        # 606e <_IO_stdin_used+0x6e>
    3b41:	85 c0                	test   %eax,%eax
    3b43:	0f 84 d3 00 00 00    	je     3c1c <timer_thread+0x40c>
    3b49:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3b4d:	45 31 e4             	xor    %r12d,%r12d
    3b50:	45 31 ed             	xor    %r13d,%r13d
    3b53:	85 c9                	test   %ecx,%ecx
    3b55:	7e 29                	jle    3b80 <timer_thread+0x370>
    3b57:	49 8b 47 10          	mov    0x10(%r15),%rax
    3b5b:	4a 8d 14 20          	lea    (%rax,%r12,1),%rdx
    3b5f:	83 7a 04 02          	cmpl   $0x2,0x4(%rdx)
    3b63:	c7 42 2c 00 00 00 00 	movl   $0x0,0x2c(%rdx)
    3b6a:	0f 84 d9 00 00 00    	je     3c49 <timer_thread+0x439>
    3b70:	41 83 c5 01          	add    $0x1,%r13d
    3b74:	49 81 c4 98 00 00 00 	add    $0x98,%r12
    3b7b:	41 39 cd             	cmp    %ecx,%r13d
    3b7e:	7c db                	jl     3b5b <timer_thread+0x34b>
    3b80:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3b84:	85 d2                	test   %edx,%edx
    3b86:	7e 75                	jle    3bfd <timer_thread+0x3ed>
    3b88:	49 63 47 28          	movslq 0x28(%r15),%rax
    3b8c:	85 c0                	test   %eax,%eax
    3b8e:	7e 6d                	jle    3bfd <timer_thread+0x3ed>
    3b90:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3b94:	4d 8b 4f 10          	mov    0x10(%r15),%r9
    3b98:	31 f6                	xor    %esi,%esi
    3b9a:	4c 8d 04 4a          	lea    (%rdx,%rcx,2),%r8
    3b9e:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3ba2:	48 8d 3c 50          	lea    (%rax,%rdx,2),%rdi
    3ba6:	49 c1 e0 03          	shl    $0x3,%r8
    3baa:	48 c1 e7 03          	shl    $0x3,%rdi
    3bae:	66 90                	xchg   %ax,%ax
    3bb0:	49 8b 44 31 20       	mov    0x20(%r9,%rsi,1),%rax
    3bb5:	48 8d 0c 38          	lea    (%rax,%rdi,1),%rcx
    3bb9:	40 f6 c7 08          	test   $0x8,%dil
    3bbd:	74 19                	je     3bd8 <timer_thread+0x3c8>
    3bbf:	c7 40 48 00 00 00 00 	movl   $0x0,0x48(%rax)
    3bc6:	48 05 98 00 00 00    	add    $0x98,%rax
    3bcc:	48 39 c8             	cmp    %rcx,%rax
    3bcf:	74 20                	je     3bf1 <timer_thread+0x3e1>
    3bd1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3bd8:	c7 40 48 00 00 00 00 	movl   $0x0,0x48(%rax)
    3bdf:	48 05 30 01 00 00    	add    $0x130,%rax
    3be5:	c7 40 b0 00 00 00 00 	movl   $0x0,-0x50(%rax)
    3bec:	48 39 c8             	cmp    %rcx,%rax
    3bef:	75 e7                	jne    3bd8 <timer_thread+0x3c8>
    3bf1:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
    3bf8:	4c 39 c6             	cmp    %r8,%rsi
    3bfb:	75 b3                	jne    3bb0 <timer_thread+0x3a0>
    3bfd:	0f ae f0             	mfence
    3c00:	48 89 ef             	mov    %rbp,%rdi
    3c03:	e8 c8 e6 ff ff       	call   22d0 <puts@plt>
    3c08:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
    3c10:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3c14:	85 c0                	test   %eax,%eax
    3c16:	0f 85 2d ff ff ff    	jne    3b49 <timer_thread+0x339>
    3c1c:	48 8d 3d 64 24 00 00 	lea    0x2464(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3c23:	e8 a8 e6 ff ff       	call   22d0 <puts@plt>
    3c28:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3c2d:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3c36:	75 49                	jne    3c81 <timer_thread+0x471>
    3c38:	48 83 c4 58          	add    $0x58,%rsp
    3c3c:	31 c0                	xor    %eax,%eax
    3c3e:	5b                   	pop    %rbx
    3c3f:	5d                   	pop    %rbp
    3c40:	41 5c                	pop    %r12
    3c42:	41 5d                	pop    %r13
    3c44:	41 5e                	pop    %r14
    3c46:	41 5f                	pop    %r15
    3c48:	c3                   	ret
    3c49:	48 89 df             	mov    %rbx,%rdi
    3c4c:	41 83 c5 01          	add    $0x1,%r13d
    3c50:	e8 7b e6 ff ff       	call   22d0 <puts@plt>
    3c55:	49 8b 47 10          	mov    0x10(%r15),%rax
    3c59:	be 01 00 00 00       	mov    $0x1,%esi
    3c5e:	42 8b 7c 20 48       	mov    0x48(%rax,%r12,1),%edi
    3c63:	49 81 c4 98 00 00 00 	add    $0x98,%r12
    3c6a:	e8 71 e7 ff ff       	call   23e0 <eventfd_write@plt>
    3c6f:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3c73:	41 39 cd             	cmp    %ecx,%r13d
    3c76:	0f 8c db fe ff ff    	jl     3b57 <timer_thread+0x347>
    3c7c:	e9 ff fe ff ff       	jmp    3b80 <timer_thread+0x370>
    3c81:	e8 8a e6 ff ff       	call   2310 <__stack_chk_fail@plt>
    3c86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003c90 <strtolower>:
    3c90:	f3 0f 1e fa          	endbr64
    3c94:	55                   	push   %rbp
    3c95:	53                   	push   %rbx
    3c96:	48 83 ec 08          	sub    $0x8,%rsp
    3c9a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3c9e:	84 db                	test   %bl,%bl
    3ca0:	74 24                	je     3cc6 <strtolower+0x36>
    3ca2:	48 89 fd             	mov    %rdi,%rbp
    3ca5:	e8 46 e8 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3caa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3cb0:	48 8b 10             	mov    (%rax),%rdx
    3cb3:	48 83 c5 01          	add    $0x1,%rbp
    3cb7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3cba:	88 55 ff             	mov    %dl,-0x1(%rbp)
    3cbd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3cc2:	84 db                	test   %bl,%bl
    3cc4:	75 ea                	jne    3cb0 <strtolower+0x20>
    3cc6:	48 83 c4 08          	add    $0x8,%rsp
    3cca:	5b                   	pop    %rbx
    3ccb:	5d                   	pop    %rbp
    3ccc:	c3                   	ret
    3ccd:	0f 1f 00             	nopl   (%rax)

0000000000003cd0 <zh_malloc>:
    3cd0:	f3 0f 1e fa          	endbr64
    3cd4:	48 83 ec 08          	sub    $0x8,%rsp
    3cd8:	e8 13 e7 ff ff       	call   23f0 <malloc@plt>
    3cdd:	48 85 c0             	test   %rax,%rax
    3ce0:	74 05                	je     3ce7 <zh_malloc+0x17>
    3ce2:	48 83 c4 08          	add    $0x8,%rsp
    3ce6:	c3                   	ret
    3ce7:	48 8b 0d 32 53 00 00 	mov    0x5332(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3cee:	ba 28 00 00 00       	mov    $0x28,%edx
    3cf3:	be 01 00 00 00       	mov    $0x1,%esi
    3cf8:	48 8d 3d 41 27 00 00 	lea    0x2741(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    3cff:	e8 9c e7 ff ff       	call   24a0 <fwrite@plt>
    3d04:	bf 01 00 00 00       	mov    $0x1,%edi
    3d09:	e8 72 e7 ff ff       	call   2480 <exit@plt>
    3d0e:	66 90                	xchg   %ax,%ax

0000000000003d10 <get_filename_ext>:
    3d10:	f3 0f 1e fa          	endbr64
    3d14:	53                   	push   %rbx
    3d15:	be 2e 00 00 00       	mov    $0x2e,%esi
    3d1a:	48 89 fb             	mov    %rdi,%rbx
    3d1d:	e8 1e e6 ff ff       	call   2340 <strrchr@plt>
    3d22:	48 85 c0             	test   %rax,%rax
    3d25:	74 11                	je     3d38 <get_filename_ext+0x28>
    3d27:	48 39 c3             	cmp    %rax,%rbx
    3d2a:	74 0c                	je     3d38 <get_filename_ext+0x28>
    3d2c:	48 83 c0 01          	add    $0x1,%rax
    3d30:	5b                   	pop    %rbx
    3d31:	c3                   	ret
    3d32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3d38:	48 8d 05 90 23 00 00 	lea    0x2390(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
    3d3f:	5b                   	pop    %rbx
    3d40:	c3                   	ret
    3d41:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3d4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003d50 <send_headers>:
    3d50:	f3 0f 1e fa          	endbr64
    3d54:	41 55                	push   %r13
    3d56:	49 89 f5             	mov    %rsi,%r13
    3d59:	48 89 fe             	mov    %rdi,%rsi
    3d5c:	41 54                	push   %r12
    3d5e:	55                   	push   %rbp
    3d5f:	48 89 d5             	mov    %rdx,%rbp
    3d62:	ba 00 04 00 00       	mov    $0x400,%edx
    3d67:	53                   	push   %rbx
    3d68:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3d6f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3d78:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3d80:	31 c0                	xor    %eax,%eax
    3d82:	49 89 e4             	mov    %rsp,%r12
    3d85:	4c 89 e7             	mov    %r12,%rdi
    3d88:	e8 83 e6 ff ff       	call   2410 <__strcpy_chk@plt>
    3d8d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3d92:	84 db                	test   %bl,%bl
    3d94:	74 24                	je     3dba <send_headers+0x6a>
    3d96:	e8 55 e7 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3d9b:	48 8b 08             	mov    (%rax),%rcx
    3d9e:	4c 89 e0             	mov    %r12,%rax
    3da1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3da8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    3dab:	48 83 c0 01          	add    $0x1,%rax
    3daf:	88 50 ff             	mov    %dl,-0x1(%rax)
    3db2:	48 0f be 18          	movsbq (%rax),%rbx
    3db6:	84 db                	test   %bl,%bl
    3db8:	75 ee                	jne    3da8 <send_headers+0x58>
    3dba:	bf 11 00 00 00       	mov    $0x11,%edi
    3dbf:	e8 2c e6 ff ff       	call   23f0 <malloc@plt>
    3dc4:	48 85 c0             	test   %rax,%rax
    3dc7:	0f 84 7e 04 00 00    	je     424b <send_headers+0x4fb>
    3dcd:	66 0f 6f 05 7b 2b 00 00 	movdqa 0x2b7b(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    3dd5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    3dd9:	bf 17 00 00 00       	mov    $0x17,%edi
    3dde:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3de6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3dea:	0f 11 00             	movups %xmm0,(%rax)
    3ded:	e8 fe e5 ff ff       	call   23f0 <malloc@plt>
    3df2:	48 85 c0             	test   %rax,%rax
    3df5:	0f 84 50 04 00 00    	je     424b <send_headers+0x4fb>
    3dfb:	66 0f 6f 05 5d 2b 00 00 	movdqa 0x2b5d(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    3e03:	48 89 45 10          	mov    %rax,0x10(%rbp)
    3e07:	4c 89 e7             	mov    %r12,%rdi
    3e0a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    3e14:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3e1c:	0f 11 00             	movups %xmm0,(%rax)
    3e1f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    3e23:	be 2e 00 00 00       	mov    $0x2e,%esi
    3e28:	e8 13 e5 ff ff       	call   2340 <strrchr@plt>
    3e2d:	48 85 c0             	test   %rax,%rax
    3e30:	0f 84 ea 02 00 00    	je     4120 <send_headers+0x3d0>
    3e36:	4c 39 e0             	cmp    %r12,%rax
    3e39:	0f 84 e1 02 00 00    	je     4120 <send_headers+0x3d0>
    3e3f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    3e43:	48 8d 3d 53 22 00 00 	lea    0x2253(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3e4a:	48 89 de             	mov    %rbx,%rsi
    3e4d:	e8 3e e5 ff ff       	call   2390 <strcmp@plt>
    3e52:	85 c0                	test   %eax,%eax
    3e54:	75 20                	jne    3e76 <send_headers+0x126>
    3e56:	66 0f 6f 05 12 2b 00 00 	movdqa 0x2b12(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    3e5e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3e66:	66 0f 6f 05 12 2b 00 00 	movdqa 0x2b12(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    3e6e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3e76:	48 89 de             	mov    %rbx,%rsi
    3e79:	48 8d 3d 21 22 00 00 	lea    0x2221(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3e80:	e8 0b e5 ff ff       	call   2390 <strcmp@plt>
    3e85:	85 c0                	test   %eax,%eax
    3e87:	75 20                	jne    3ea9 <send_headers+0x159>
    3e89:	66 0f 6f 05 df 2a 00 00 	movdqa 0x2adf(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    3e91:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3e99:	66 0f 6f 05 df 2a 00 00 	movdqa 0x2adf(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    3ea1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3ea9:	48 89 de             	mov    %rbx,%rsi
    3eac:	48 8d 3d f3 21 00 00 	lea    0x21f3(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3eb3:	e8 d8 e4 ff ff       	call   2390 <strcmp@plt>
    3eb8:	85 c0                	test   %eax,%eax
    3eba:	0f 84 10 02 00 00    	je     40d0 <send_headers+0x380>
    3ec0:	48 89 de             	mov    %rbx,%rsi
    3ec3:	48 8d 3d e0 21 00 00 	lea    0x21e0(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3eca:	e8 c1 e4 ff ff       	call   2390 <strcmp@plt>
    3ecf:	85 c0                	test   %eax,%eax
    3ed1:	0f 84 a9 02 00 00    	je     4180 <send_headers+0x430>
    3ed7:	48 89 de             	mov    %rbx,%rsi
    3eda:	48 8d 3d cd 21 00 00 	lea    0x21cd(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3ee1:	e8 aa e4 ff ff       	call   2390 <strcmp@plt>
    3ee6:	85 c0                	test   %eax,%eax
    3ee8:	0f 84 6a 02 00 00    	je     4158 <send_headers+0x408>
    3eee:	48 89 de             	mov    %rbx,%rsi
    3ef1:	48 8d 3d f9 21 00 00 	lea    0x21f9(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3ef8:	e8 93 e4 ff ff       	call   2390 <strcmp@plt>
    3efd:	85 c0                	test   %eax,%eax
    3eff:	0f 84 2b 02 00 00    	je     4130 <send_headers+0x3e0>
    3f05:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3f08:	0f 84 52 01 00 00    	je     4060 <send_headers+0x310>
    3f0e:	48 89 de             	mov    %rbx,%rsi
    3f11:	48 8d 3d 9a 21 00 00 	lea    0x219a(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3f18:	e8 73 e4 ff ff       	call   2390 <strcmp@plt>
    3f1d:	85 c0                	test   %eax,%eax
    3f1f:	0f 84 ab 02 00 00    	je     41d0 <send_headers+0x480>
    3f25:	48 89 de             	mov    %rbx,%rsi
    3f28:	48 8d 3d 87 21 00 00 	lea    0x2187(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3f2f:	e8 5c e4 ff ff       	call   2390 <strcmp@plt>
    3f34:	85 c0                	test   %eax,%eax
    3f36:	0f 84 6c 02 00 00    	je     41a8 <send_headers+0x458>
    3f3c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3f44:	4c 89 e7             	mov    %r12,%rdi
    3f47:	e8 b4 e3 ff ff       	call   2300 <strlen@plt>
    3f4c:	48 89 c7             	mov    %rax,%rdi
    3f4f:	48 89 c3             	mov    %rax,%rbx
    3f52:	e8 99 e4 ff ff       	call   23f0 <malloc@plt>
    3f57:	48 85 c0             	test   %rax,%rax
    3f5a:	0f 84 eb 02 00 00    	je     424b <send_headers+0x4fb>
    3f60:	48 89 45 20          	mov    %rax,0x20(%rbp)
    3f64:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    3f68:	83 fb 08             	cmp    $0x8,%ebx
    3f6b:	0f 83 3f 01 00 00    	jae    40b0 <send_headers+0x360>
    3f71:	f6 c3 04             	test   $0x4,%bl
    3f74:	0f 85 7b 02 00 00    	jne    41f5 <send_headers+0x4a5>
    3f7a:	85 db                	test   %ebx,%ebx
    3f7c:	74 13                	je     3f91 <send_headers+0x241>
    3f7e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3f86:	88 10                	mov    %dl,(%rax)
    3f88:	f6 c3 02             	test   $0x2,%bl
    3f8b:	0f 85 96 02 00 00    	jne    4227 <send_headers+0x4d7>
    3f91:	4d 89 e8             	mov    %r13,%r8
    3f94:	48 8d 0d 1f 21 00 00 	lea    0x211f(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    3f9b:	4c 89 e7             	mov    %r12,%rdi
    3f9e:	31 c0                	xor    %eax,%eax
    3fa0:	ba 00 04 00 00       	mov    $0x400,%edx
    3fa5:	be 01 00 00 00       	mov    $0x1,%esi
    3faa:	e8 51 e5 ff ff       	call   2500 <__sprintf_chk@plt>
    3faf:	4c 89 e7             	mov    %r12,%rdi
    3fb2:	e8 49 e3 ff ff       	call   2300 <strlen@plt>
    3fb7:	48 89 c7             	mov    %rax,%rdi
    3fba:	48 89 c3             	mov    %rax,%rbx
    3fbd:	e8 2e e4 ff ff       	call   23f0 <malloc@plt>
    3fc2:	48 85 c0             	test   %rax,%rax
    3fc5:	0f 84 80 02 00 00    	je     424b <send_headers+0x4fb>
    3fcb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    3fcf:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    3fd3:	83 fb 08             	cmp    $0x8,%ebx
    3fd6:	0f 83 1c 01 00 00    	jae    40f8 <send_headers+0x3a8>
    3fdc:	f6 c3 04             	test   $0x4,%bl
    3fdf:	0f 85 29 02 00 00    	jne    420e <send_headers+0x4be>
    3fe5:	85 db                	test   %ebx,%ebx
    3fe7:	74 13                	je     3ffc <send_headers+0x2ac>
    3fe9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3ff1:	88 10                	mov    %dl,(%rax)
    3ff3:	f6 c3 02             	test   $0x2,%bl
    3ff6:	0f 85 3d 02 00 00    	jne    4239 <send_headers+0x4e9>
    3ffc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    4001:	bf 02 00 00 00       	mov    $0x2,%edi
    4006:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    400e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4016:	e8 d5 e3 ff ff       	call   23f0 <malloc@plt>
    401b:	48 85 c0             	test   %rax,%rax
    401e:	0f 84 27 02 00 00    	je     424b <send_headers+0x4fb>
    4024:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    402c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    4030:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4038:	66 89 10             	mov    %dx,(%rax)
    403b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4043:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    404c:	0f 85 20 02 00 00    	jne    4272 <send_headers+0x522>
    4052:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4059:	5b                   	pop    %rbx
    405a:	5d                   	pop    %rbp
    405b:	41 5c                	pop    %r12
    405d:	41 5d                	pop    %r13
    405f:	c3                   	ret
    4060:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4064:	0f 85 a4 fe ff ff    	jne    3f0e <send_headers+0x1be>
    406a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    406e:	0f 85 9a fe ff ff    	jne    3f0e <send_headers+0x1be>
    4074:	66 0f 6f 05 54 29 00 00 	movdqa 0x2954(%rip),%xmm0        # 69d0 <_IO_stdin_used+0x9d0>
    407c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4086:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    408e:	66 0f 6f 05 4a 29 00 00 	movdqa 0x294a(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
    4096:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    409e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    40a6:	e9 63 fe ff ff       	jmp    3f0e <send_headers+0x1be>
    40ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    40b0:	89 da                	mov    %ebx,%edx
    40b2:	48 89 c7             	mov    %rax,%rdi
    40b5:	4c 89 e6             	mov    %r12,%rsi
    40b8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    40bd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    40c2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    40c5:	c1 e9 03             	shr    $0x3,%ecx
    40c8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    40cb:	e9 c1 fe ff ff       	jmp    3f91 <send_headers+0x241>
    40d0:	66 0f 6f 05 98 28 00 00 	movdqa 0x2898(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    40d8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40e0:	66 0f 6f 05 a8 28 00 00 	movdqa 0x28a8(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    40e8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40f0:	e9 cb fd ff ff       	jmp    3ec0 <send_headers+0x170>
    40f5:	0f 1f 00             	nopl   (%rax)
    40f8:	89 da                	mov    %ebx,%edx
    40fa:	48 89 c7             	mov    %rax,%rdi
    40fd:	4c 89 e6             	mov    %r12,%rsi
    4100:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4105:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    410a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    410d:	c1 e9 03             	shr    $0x3,%ecx
    4110:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4113:	e9 e4 fe ff ff       	jmp    3ffc <send_headers+0x2ac>
    4118:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4120:	48 8d 1d a8 1f 00 00 	lea    0x1fa8(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    4127:	e9 94 fd ff ff       	jmp    3ec0 <send_headers+0x170>
    412c:	0f 1f 40 00          	nopl   0x0(%rax)
    4130:	66 0f 6f 05 78 28 00 00 	movdqa 0x2878(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    4138:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4140:	66 0f 6f 05 78 28 00 00 	movdqa 0x2878(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4148:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4150:	e9 b0 fd ff ff       	jmp    3f05 <send_headers+0x1b5>
    4155:	0f 1f 00             	nopl   (%rax)
    4158:	66 0f 6f 05 50 28 00 00 	movdqa 0x2850(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    4160:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4168:	66 0f 6f 05 50 28 00 00 	movdqa 0x2850(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4170:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4178:	e9 71 fd ff ff       	jmp    3eee <send_headers+0x19e>
    417d:	0f 1f 00             	nopl   (%rax)
    4180:	66 0f 6f 05 e8 27 00 00 	movdqa 0x27e8(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4188:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4190:	66 0f 6f 05 08 28 00 00 	movdqa 0x2808(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    4198:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    41a0:	e9 32 fd ff ff       	jmp    3ed7 <send_headers+0x187>
    41a5:	0f 1f 00             	nopl   (%rax)
    41a8:	66 0f 6f 05 00 28 00 00 	movdqa 0x2800(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    41b0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41b8:	66 0f 6f 05 40 28 00 00 	movdqa 0x2840(%rip),%xmm0        # 6a00 <_IO_stdin_used+0xa00>
    41c0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    41c8:	e9 6f fd ff ff       	jmp    3f3c <send_headers+0x1ec>
    41cd:	0f 1f 00             	nopl   (%rax)
    41d0:	66 0f 6f 05 d8 27 00 00 	movdqa 0x27d8(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    41d8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41e0:	66 0f 6f 05 08 28 00 00 	movdqa 0x2808(%rip),%xmm0        # 69f0 <_IO_stdin_used+0x9f0>
    41e8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    41f0:	e9 30 fd ff ff       	jmp    3f25 <send_headers+0x1d5>
    41f5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    41fc:	89 db                	mov    %ebx,%ebx
    41fe:	89 10                	mov    %edx,(%rax)
    4200:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4205:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4209:	e9 83 fd ff ff       	jmp    3f91 <send_headers+0x241>
    420e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4215:	89 db                	mov    %ebx,%ebx
    4217:	89 10                	mov    %edx,(%rax)
    4219:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    421e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4222:	e9 d5 fd ff ff       	jmp    3ffc <send_headers+0x2ac>
    4227:	89 db                	mov    %ebx,%ebx
    4229:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    422f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4234:	e9 58 fd ff ff       	jmp    3f91 <send_headers+0x241>
    4239:	89 db                	mov    %ebx,%ebx
    423b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4241:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4246:	e9 b1 fd ff ff       	jmp    3ffc <send_headers+0x2ac>
    424b:	48 8b 0d ce 4d 00 00 	mov    0x4dce(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4252:	ba 28 00 00 00       	mov    $0x28,%edx
    4257:	be 01 00 00 00       	mov    $0x1,%esi
    425c:	48 8d 3d dd 21 00 00 	lea    0x21dd(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    4263:	e8 38 e2 ff ff       	call   24a0 <fwrite@plt>
    4268:	bf 01 00 00 00       	mov    $0x1,%edi
    426d:	e8 0e e2 ff ff       	call   2480 <exit@plt>
    4272:	e8 99 e0 ff ff       	call   2310 <__stack_chk_fail@plt>
    4277:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004280 <copy_file_contents>:
    4280:	f3 0f 1e fa          	endbr64
    4284:	41 55                	push   %r13
    4286:	49 89 d5             	mov    %rdx,%r13
    4289:	41 54                	push   %r12
    428b:	49 89 fc             	mov    %rdi,%r12
    428e:	48 89 f7             	mov    %rsi,%rdi
    4291:	55                   	push   %rbp
    4292:	53                   	push   %rbx
    4293:	48 89 f3             	mov    %rsi,%rbx
    4296:	48 83 ec 08          	sub    $0x8,%rsp
    429a:	e8 51 e1 ff ff       	call   23f0 <malloc@plt>
    429f:	48 85 c0             	test   %rax,%rax
    42a2:	74 6b                	je     430f <copy_file_contents+0x8f>
    42a4:	4c 89 e7             	mov    %r12,%rdi
    42a7:	48 89 c5             	mov    %rax,%rbp
    42aa:	31 f6                	xor    %esi,%esi
    42ac:	31 c0                	xor    %eax,%eax
    42ae:	e8 ad e1 ff ff       	call   2460 <open@plt>
    42b3:	41 89 c4             	mov    %eax,%r12d
    42b6:	85 c0                	test   %eax,%eax
    42b8:	0f 88 78 e2 ff ff    	js     2536 <copy_file_contents.cold>
    42be:	48 89 da             	mov    %rbx,%rdx
    42c1:	48 89 ee             	mov    %rbp,%rsi
    42c4:	89 c7                	mov    %eax,%edi
    42c6:	e8 a5 e0 ff ff       	call   2370 <read@plt>
    42cb:	48 98                	cltq
    42cd:	48 39 d8             	cmp    %rbx,%rax
    42d0:	7c 1e                	jl     42f0 <copy_file_contents+0x70>
    42d2:	44 89 e7             	mov    %r12d,%edi
    42d5:	e8 76 e0 ff ff       	call   2350 <close@plt>
    42da:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    42de:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    42e2:	48 83 c4 08          	add    $0x8,%rsp
    42e6:	5b                   	pop    %rbx
    42e7:	5d                   	pop    %rbp
    42e8:	41 5c                	pop    %r12
    42ea:	41 5d                	pop    %r13
    42ec:	c3                   	ret
    42ed:	0f 1f 00             	nopl   (%rax)
    42f0:	48 8b 0d 29 4d 00 00 	mov    0x4d29(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    42f7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    42fc:	be 01 00 00 00       	mov    $0x1,%esi
    4301:	48 8d 3d c8 1d 00 00 	lea    0x1dc8(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    4308:	e8 93 e1 ff ff       	call   24a0 <fwrite@plt>
    430d:	eb c3                	jmp    42d2 <copy_file_contents+0x52>
    430f:	48 8b 0d 0a 4d 00 00 	mov    0x4d0a(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4316:	ba 28 00 00 00       	mov    $0x28,%edx
    431b:	be 01 00 00 00       	mov    $0x1,%esi
    4320:	48 8d 3d 19 21 00 00 	lea    0x2119(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    4327:	e8 74 e1 ff ff       	call   24a0 <fwrite@plt>
    432c:	bf 01 00 00 00       	mov    $0x1,%edi
    4331:	e8 4a e1 ff ff       	call   2480 <exit@plt>
    4336:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004340 <add_write_request>:
    4340:	f3 0f 1e fa          	endbr64
    4344:	8b 46 44             	mov    0x44(%rsi),%eax
    4347:	48 89 fa             	mov    %rdi,%rdx
    434a:	48 89 f7             	mov    %rsi,%rdi
    434d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    4353:	8d 70 01             	lea    0x1(%rax),%esi
    4356:	48 8b 07             	mov    (%rdi),%rax
    4359:	44 8b 00             	mov    (%rax),%r8d
    435c:	f6 c1 02             	test   $0x2,%cl
    435f:	74 00                	je     4361 <add_write_request+0x21>
    4361:	89 f0                	mov    %esi,%eax
    4363:	44 29 c0             	sub    %r8d,%eax
    4366:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4369:	0f 82 d3 e1 ff ff    	jb     2542 <add_write_request.cold>
    436f:	c1 e9 0a             	shr    $0xa,%ecx
    4372:	48 83 ec 08          	sub    $0x8,%rsp
    4376:	8b 47 44             	mov    0x44(%rdi),%eax
    4379:	23 47 58             	and    0x58(%rdi),%eax
    437c:	83 e1 01             	and    $0x1,%ecx
    437f:	89 77 44             	mov    %esi,0x44(%rdi)
    4382:	8b 72 08             	mov    0x8(%rdx),%esi
    4385:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4389:	d3 e0                	shl    %cl,%eax
    438b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    438e:	48 c1 e0 06          	shl    $0x6,%rax
    4392:	48 03 47 38          	add    0x38(%rdi),%rax
    4396:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    439c:	89 70 04             	mov    %esi,0x4(%rax)
    439f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    43a3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    43a9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    43b1:	48 89 70 10          	mov    %rsi,0x10(%rax)
    43b5:	89 48 18             	mov    %ecx,0x18(%rax)
    43b8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    43bf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    43c7:	48 89 50 20          	mov    %rdx,0x20(%rax)
    43cb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    43cf:	e8 4c df ff ff       	call   2320 <io_uring_submit@plt>
    43d4:	31 c0                	xor    %eax,%eax
    43d6:	48 83 c4 08          	add    $0x8,%rsp
    43da:	c3                   	ret
    43db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000043e0 <add_read_request>:
    43e0:	f3 0f 1e fa          	endbr64
    43e4:	41 55                	push   %r13
    43e6:	41 89 fd             	mov    %edi,%r13d
    43e9:	41 54                	push   %r12
    43eb:	55                   	push   %rbp
    43ec:	53                   	push   %rbx
    43ed:	48 89 f3             	mov    %rsi,%rbx
    43f0:	48 83 ec 08          	sub    $0x8,%rsp
    43f4:	8b 46 44             	mov    0x44(%rsi),%eax
    43f7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    43fd:	48 8b 16             	mov    (%rsi),%rdx
    4400:	83 c0 01             	add    $0x1,%eax
    4403:	8b 32                	mov    (%rdx),%esi
    4405:	f6 c1 02             	test   $0x2,%cl
    4408:	74 00                	je     440a <add_read_request+0x2a>
    440a:	89 c2                	mov    %eax,%edx
    440c:	29 f2                	sub    %esi,%edx
    440e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4411:	0f 82 3b e1 ff ff    	jb     2552 <add_read_request.cold>
    4417:	8b 6b 44             	mov    0x44(%rbx),%ebp
    441a:	c1 e9 0a             	shr    $0xa,%ecx
    441d:	89 43 44             	mov    %eax,0x44(%rbx)
    4420:	bf 20 00 00 00       	mov    $0x20,%edi
    4425:	83 e1 01             	and    $0x1,%ecx
    4428:	23 6b 58             	and    0x58(%rbx),%ebp
    442b:	d3 e5                	shl    %cl,%ebp
    442d:	48 c1 e5 06          	shl    $0x6,%rbp
    4431:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4435:	e8 b6 df ff ff       	call   23f0 <malloc@plt>
    443a:	be 01 00 00 00       	mov    $0x1,%esi
    443f:	bf 00 20 00 00       	mov    $0x2000,%edi
    4444:	49 89 c4             	mov    %rax,%r12
    4447:	e8 34 df ff ff       	call   2380 <calloc@plt>
    444c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    4451:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4455:	48 89 df             	mov    %rbx,%rdi
    4458:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    445d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    4462:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    446b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    4473:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    4477:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    447b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    4482:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    448a:	48 89 45 10          	mov    %rax,0x10(%rbp)
    448e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    4496:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    449e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    44a2:	e8 79 de ff ff       	call   2320 <io_uring_submit@plt>
    44a7:	48 83 c4 08          	add    $0x8,%rsp
    44ab:	31 c0                	xor    %eax,%eax
    44ad:	5b                   	pop    %rbx
    44ae:	5d                   	pop    %rbp
    44af:	41 5c                	pop    %r12
    44b1:	41 5d                	pop    %r13
    44b3:	c3                   	ret
    44b4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    44bf:	90                   	nop

00000000000044c0 <_send_static_string_content>:
    44c0:	f3 0f 1e fa          	endbr64
    44c4:	41 56                	push   %r14
    44c6:	41 89 f6             	mov    %esi,%r14d
    44c9:	41 55                	push   %r13
    44cb:	49 89 fd             	mov    %rdi,%r13
    44ce:	bf 20 00 00 00       	mov    $0x20,%edi
    44d3:	41 54                	push   %r12
    44d5:	55                   	push   %rbp
    44d6:	48 89 d5             	mov    %rdx,%rbp
    44d9:	53                   	push   %rbx
    44da:	e8 11 df ff ff       	call   23f0 <malloc@plt>
    44df:	48 85 c0             	test   %rax,%rax
    44e2:	0f 84 dd 00 00 00    	je     45c5 <_send_static_string_content+0x105>
    44e8:	48 89 c3             	mov    %rax,%rbx
    44eb:	4c 89 ef             	mov    %r13,%rdi
    44ee:	e8 0d de ff ff       	call   2300 <strlen@plt>
    44f3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    44fa:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    44fe:	48 89 c7             	mov    %rax,%rdi
    4501:	49 89 c4             	mov    %rax,%r12
    4504:	e8 e7 de ff ff       	call   23f0 <malloc@plt>
    4509:	48 89 c7             	mov    %rax,%rdi
    450c:	48 85 c0             	test   %rax,%rax
    450f:	0f 84 b0 00 00 00    	je     45c5 <_send_static_string_content+0x105>
    4515:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4519:	4c 89 e2             	mov    %r12,%rdx
    451c:	4c 89 ee             	mov    %r13,%rsi
    451f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4523:	e8 98 de ff ff       	call   23c0 <memcpy@plt>
    4528:	8b 45 44             	mov    0x44(%rbp),%eax
    452b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    4531:	8d 50 01             	lea    0x1(%rax),%edx
    4534:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4538:	8b 30                	mov    (%rax),%esi
    453a:	f6 c1 02             	test   $0x2,%cl
    453d:	0f 85 7d 00 00 00    	jne    45c0 <_send_static_string_content+0x100>
    4543:	89 d0                	mov    %edx,%eax
    4545:	29 f0                	sub    %esi,%eax
    4547:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    454a:	0f 82 0c e0 ff ff    	jb     255c <_send_static_string_content.cold>
    4550:	c1 e9 0a             	shr    $0xa,%ecx
    4553:	8b 45 44             	mov    0x44(%rbp),%eax
    4556:	23 45 58             	and    0x58(%rbp),%eax
    4559:	89 55 44             	mov    %edx,0x44(%rbp)
    455c:	83 e1 01             	and    $0x1,%ecx
    455f:	8b 53 04             	mov    0x4(%rbx),%edx
    4562:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    4568:	66 0f ef c0          	pxor   %xmm0,%xmm0
    456c:	d3 e0                	shl    %cl,%eax
    456e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    4571:	48 89 ef             	mov    %rbp,%rdi
    4574:	48 c1 e0 06          	shl    $0x6,%rax
    4578:	48 03 45 38          	add    0x38(%rbp),%rax
    457c:	89 48 04             	mov    %ecx,0x4(%rax)
    457f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    4583:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4589:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4591:	48 89 48 10          	mov    %rcx,0x10(%rax)
    4595:	89 50 18             	mov    %edx,0x18(%rax)
    4598:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    459f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    45a7:	48 89 58 20          	mov    %rbx,0x20(%rax)
    45ab:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    45af:	5b                   	pop    %rbx
    45b0:	5d                   	pop    %rbp
    45b1:	41 5c                	pop    %r12
    45b3:	41 5d                	pop    %r13
    45b5:	41 5e                	pop    %r14
    45b7:	e9 64 dd ff ff       	jmp    2320 <io_uring_submit@plt>
    45bc:	0f 1f 40 00          	nopl   0x0(%rax)
    45c0:	e9 7e ff ff ff       	jmp    4543 <_send_static_string_content+0x83>
    45c5:	48 8b 0d 54 4a 00 00 	mov    0x4a54(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    45cc:	ba 28 00 00 00       	mov    $0x28,%edx
    45d1:	be 01 00 00 00       	mov    $0x1,%esi
    45d6:	48 8d 3d 63 1e 00 00 	lea    0x1e63(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    45dd:	e8 be de ff ff       	call   24a0 <fwrite@plt>
    45e2:	bf 01 00 00 00       	mov    $0x1,%edi
    45e7:	e8 94 de ff ff       	call   2480 <exit@plt>
    45ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000045f0 <handle_unimplemented_method>:
    45f0:	f3 0f 1e fa          	endbr64
    45f4:	48 89 f2             	mov    %rsi,%rdx
    45f7:	89 fe                	mov    %edi,%esi
    45f9:	48 8b 3d 18 4a 00 00 	mov    0x4a18(%rip),%rdi        # 9018 <unimplemented_content>
    4600:	e9 bb fe ff ff       	jmp    44c0 <_send_static_string_content>
    4605:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004610 <handle_http_404>:
    4610:	f3 0f 1e fa          	endbr64
    4614:	48 89 f2             	mov    %rsi,%rdx
    4617:	89 fe                	mov    %edi,%esi
    4619:	48 8b 3d f0 49 00 00 	mov    0x49f0(%rip),%rdi        # 9010 <http_404_content>
    4620:	e9 9b fe ff ff       	jmp    44c0 <_send_static_string_content>
    4625:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004630 <handle_get_method>:
    4630:	f3 0f 1e fa          	endbr64
    4634:	41 56                	push   %r14
    4636:	41 55                	push   %r13
    4638:	49 89 d5             	mov    %rdx,%r13
    463b:	41 54                	push   %r12
    463d:	41 89 f4             	mov    %esi,%r12d
    4640:	55                   	push   %rbp
    4641:	48 89 fd             	mov    %rdi,%rbp
    4644:	53                   	push   %rbx
    4645:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    464c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4655:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    465d:	31 c0                	xor    %eax,%eax
    465f:	e8 9c dc ff ff       	call   2300 <strlen@plt>
    4664:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4669:	48 89 c3             	mov    %rax,%rbx
    466c:	0f 84 b6 00 00 00    	je     4728 <handle_get_method+0xf8>
    4672:	b8 69 63 00 00       	mov    $0x6369,%eax
    4677:	48 89 ee             	mov    %rbp,%rsi
    467a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    467e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4683:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    468b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4693:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    469e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    46a6:	e8 f5 dc ff ff       	call   23a0 <__memcpy_chk@plt>
    46ab:	48 89 e6             	mov    %rsp,%rsi
    46ae:	4c 89 f7             	mov    %r14,%rdi
    46b1:	e8 fa dc ff ff       	call   23b0 <stat@plt>
    46b6:	83 f8 ff             	cmp    $0xffffffff,%eax
    46b9:	0f 84 d3 00 00 00    	je     4792 <handle_get_method+0x162>
    46bf:	8b 44 24 18          	mov    0x18(%rsp),%eax
    46c3:	25 00 f0 00 00       	and    $0xf000,%eax
    46c8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    46cd:	0f 84 f5 00 00 00    	je     47c8 <handle_get_method+0x198>
    46d3:	48 8b 3d 36 49 00 00 	mov    0x4936(%rip),%rdi        # 9010 <http_404_content>
    46da:	4c 89 ea             	mov    %r13,%rdx
    46dd:	44 89 e6             	mov    %r12d,%esi
    46e0:	e8 db fd ff ff       	call   44c0 <_send_static_string_content>
    46e5:	4c 89 f2             	mov    %r14,%rdx
    46e8:	bf 01 00 00 00       	mov    $0x1,%edi
    46ed:	31 c0                	xor    %eax,%eax
    46ef:	48 8d 35 2a 1a 00 00 	lea    0x1a2a(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    46f6:	e8 35 dd ff ff       	call   2430 <__printf_chk@plt>
    46fb:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4703:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    470c:	0f 85 20 01 00 00    	jne    4832 <handle_get_method+0x202>
    4712:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4719:	5b                   	pop    %rbx
    471a:	5d                   	pop    %rbp
    471b:	41 5c                	pop    %r12
    471d:	41 5d                	pop    %r13
    471f:	41 5e                	pop    %r14
    4721:	c3                   	ret
    4722:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4728:	ba 69 63 00 00       	mov    $0x6369,%edx
    472d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4735:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    473a:	48 89 ee             	mov    %rbp,%rsi
    473d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    4745:	48 89 c2             	mov    %rax,%rdx
    4748:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4750:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    475b:	e8 40 dc ff ff       	call   23a0 <__memcpy_chk@plt>
    4760:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4765:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    476a:	48 8d 35 7a 19 00 00 	lea    0x197a(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    4771:	48 29 d9             	sub    %rbx,%rcx
    4774:	ba 0b 00 00 00       	mov    $0xb,%edx
    4779:	e8 22 dc ff ff       	call   23a0 <__memcpy_chk@plt>
    477e:	48 89 e6             	mov    %rsp,%rsi
    4781:	4c 89 f7             	mov    %r14,%rdi
    4784:	e8 27 dc ff ff       	call   23b0 <stat@plt>
    4789:	83 f8 ff             	cmp    $0xffffffff,%eax
    478c:	0f 85 2d ff ff ff    	jne    46bf <handle_get_method+0x8f>
    4792:	4c 89 f2             	mov    %r14,%rdx
    4795:	48 89 e9             	mov    %rbp,%rcx
    4798:	48 8d 35 57 19 00 00 	lea    0x1957(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    479f:	31 c0                	xor    %eax,%eax
    47a1:	bf 01 00 00 00       	mov    $0x1,%edi
    47a6:	e8 85 dc ff ff       	call   2430 <__printf_chk@plt>
    47ab:	48 8b 3d 5e 48 00 00 	mov    0x485e(%rip),%rdi        # 9010 <http_404_content>
    47b2:	4c 89 ea             	mov    %r13,%rdx
    47b5:	44 89 e6             	mov    %r12d,%esi
    47b8:	e8 03 fd ff ff       	call   44c0 <_send_static_string_content>
    47bd:	e9 39 ff ff ff       	jmp    46fb <handle_get_method+0xcb>
    47c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    47c8:	bf 70 00 00 00       	mov    $0x70,%edi
    47cd:	e8 1e dc ff ff       	call   23f0 <malloc@plt>
    47d2:	48 89 c3             	mov    %rax,%rbx
    47d5:	48 85 c0             	test   %rax,%rax
    47d8:	74 5d                	je     4837 <handle_get_method+0x207>
    47da:	44 89 60 08          	mov    %r12d,0x8(%rax)
    47de:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    47e3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    47e7:	4c 89 f7             	mov    %r14,%rdi
    47ea:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    47f1:	e8 5a f5 ff ff       	call   3d50 <send_headers>
    47f6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    47fb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    47ff:	4c 89 f7             	mov    %r14,%rdi
    4802:	e8 79 fa ff ff       	call   4280 <copy_file_contents>
    4807:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    480c:	4c 89 f2             	mov    %r14,%rdx
    480f:	31 c0                	xor    %eax,%eax
    4811:	48 8d 35 f6 18 00 00 	lea    0x18f6(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    4818:	bf 01 00 00 00       	mov    $0x1,%edi
    481d:	e8 0e dc ff ff       	call   2430 <__printf_chk@plt>
    4822:	4c 89 ee             	mov    %r13,%rsi
    4825:	48 89 df             	mov    %rbx,%rdi
    4828:	e8 13 fb ff ff       	call   4340 <add_write_request>
    482d:	e9 c9 fe ff ff       	jmp    46fb <handle_get_method+0xcb>
    4832:	e8 d9 da ff ff       	call   2310 <__stack_chk_fail@plt>
    4837:	48 8b 0d e2 47 00 00 	mov    0x47e2(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    483e:	ba 28 00 00 00       	mov    $0x28,%edx
    4843:	be 01 00 00 00       	mov    $0x1,%esi
    4848:	48 8d 3d f1 1b 00 00 	lea    0x1bf1(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    484f:	e8 4c dc ff ff       	call   24a0 <fwrite@plt>
    4854:	bf 01 00 00 00       	mov    $0x1,%edi
    4859:	e8 22 dc ff ff       	call   2480 <exit@plt>
    485e:	66 90                	xchg   %ax,%ax

0000000000004860 <handle_http_method>:
    4860:	f3 0f 1e fa          	endbr64
    4864:	41 57                	push   %r15
    4866:	41 56                	push   %r14
    4868:	4c 8d 35 16 18 00 00 	lea    0x1816(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
    486f:	41 55                	push   %r13
    4871:	49 89 d5             	mov    %rdx,%r13
    4874:	41 54                	push   %r12
    4876:	41 89 f4             	mov    %esi,%r12d
    4879:	4c 89 f6             	mov    %r14,%rsi
    487c:	55                   	push   %rbp
    487d:	53                   	push   %rbx
    487e:	48 83 ec 18          	sub    $0x18,%rsp
    4882:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    488b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4890:	31 c0                	xor    %eax,%eax
    4892:	49 89 e7             	mov    %rsp,%r15
    4895:	4c 89 fa             	mov    %r15,%rdx
    4898:	e8 c3 da ff ff       	call   2360 <strtok_r@plt>
    489d:	48 0f be 18          	movsbq (%rax),%rbx
    48a1:	48 89 c5             	mov    %rax,%rbp
    48a4:	84 db                	test   %bl,%bl
    48a6:	74 1d                	je     48c5 <handle_http_method+0x65>
    48a8:	e8 43 dc ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    48ad:	48 89 ea             	mov    %rbp,%rdx
    48b0:	48 8b 08             	mov    (%rax),%rcx
    48b3:	48 83 c2 01          	add    $0x1,%rdx
    48b7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    48ba:	88 4a ff             	mov    %cl,-0x1(%rdx)
    48bd:	48 0f be 1a          	movsbq (%rdx),%rbx
    48c1:	84 db                	test   %bl,%bl
    48c3:	75 eb                	jne    48b0 <handle_http_method+0x50>
    48c5:	4c 89 fa             	mov    %r15,%rdx
    48c8:	4c 89 f6             	mov    %r14,%rsi
    48cb:	31 ff                	xor    %edi,%edi
    48cd:	e8 8e da ff ff       	call   2360 <strtok_r@plt>
    48d2:	48 8d 35 5a 18 00 00 	lea    0x185a(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    48d9:	48 89 ef             	mov    %rbp,%rdi
    48dc:	48 89 c3             	mov    %rax,%rbx
    48df:	e8 ac da ff ff       	call   2390 <strcmp@plt>
    48e4:	4c 89 ea             	mov    %r13,%rdx
    48e7:	44 89 e6             	mov    %r12d,%esi
    48ea:	85 c0                	test   %eax,%eax
    48ec:	75 2a                	jne    4918 <handle_http_method+0xb8>
    48ee:	48 89 df             	mov    %rbx,%rdi
    48f1:	e8 3a fd ff ff       	call   4630 <handle_get_method>
    48f6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    48fb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4904:	75 20                	jne    4926 <handle_http_method+0xc6>
    4906:	48 83 c4 18          	add    $0x18,%rsp
    490a:	5b                   	pop    %rbx
    490b:	5d                   	pop    %rbp
    490c:	41 5c                	pop    %r12
    490e:	41 5d                	pop    %r13
    4910:	41 5e                	pop    %r14
    4912:	41 5f                	pop    %r15
    4914:	c3                   	ret
    4915:	0f 1f 00             	nopl   (%rax)
    4918:	48 8b 3d f9 46 00 00 	mov    0x46f9(%rip),%rdi        # 9018 <unimplemented_content>
    491f:	e8 9c fb ff ff       	call   44c0 <_send_static_string_content>
    4924:	eb d0                	jmp    48f6 <handle_http_method+0x96>
    4926:	e8 e5 d9 ff ff       	call   2310 <__stack_chk_fail@plt>
    492b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004930 <get_line>:
    4930:	f3 0f 1e fa          	endbr64
    4934:	85 d2                	test   %edx,%edx
    4936:	7e 38                	jle    4970 <get_line+0x40>
    4938:	48 63 d2             	movslq %edx,%rdx
    493b:	48 83 c7 01          	add    $0x1,%rdi
    493f:	48 01 f2             	add    %rsi,%rdx
    4942:	eb 11                	jmp    4955 <get_line+0x25>
    4944:	0f 1f 40 00          	nopl   0x0(%rax)
    4948:	48 83 c6 01          	add    $0x1,%rsi
    494c:	48 83 c7 01          	add    $0x1,%rdi
    4950:	48 39 d6             	cmp    %rdx,%rsi
    4953:	74 1b                	je     4970 <get_line+0x40>
    4955:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4959:	88 06                	mov    %al,(%rsi)
    495b:	3c 0d                	cmp    $0xd,%al
    495d:	75 e9                	jne    4948 <get_line+0x18>
    495f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4962:	75 e4                	jne    4948 <get_line+0x18>
    4964:	c6 06 00             	movb   $0x0,(%rsi)
    4967:	31 c0                	xor    %eax,%eax
    4969:	c3                   	ret
    496a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4970:	b8 01 00 00 00       	mov    $0x1,%eax
    4975:	c3                   	ret
    4976:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004980 <handle_client_request>:
    4980:	f3 0f 1e fa          	endbr64
    4984:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    498b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    498f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4998:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    49a0:	31 c0                	xor    %eax,%eax
    49a2:	49 89 e2             	mov    %rsp,%r10
    49a5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    49ad:	4c 89 d0             	mov    %r10,%rax
    49b0:	eb 13                	jmp    49c5 <handle_client_request+0x45>
    49b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    49b8:	48 83 c0 01          	add    $0x1,%rax
    49bc:	48 83 c1 01          	add    $0x1,%rcx
    49c0:	4c 39 c8             	cmp    %r9,%rax
    49c3:	74 4b                	je     4a10 <handle_client_request+0x90>
    49c5:	44 0f b6 01          	movzbl (%rcx),%r8d
    49c9:	44 88 00             	mov    %r8b,(%rax)
    49cc:	41 80 f8 0d          	cmp    $0xd,%r8b
    49d0:	75 e6                	jne    49b8 <handle_client_request+0x38>
    49d2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    49d6:	75 e0                	jne    49b8 <handle_client_request+0x38>
    49d8:	c6 00 00             	movb   $0x0,(%rax)
    49db:	8b 47 08             	mov    0x8(%rdi),%eax
    49de:	48 89 f2             	mov    %rsi,%rdx
    49e1:	4c 89 d7             	mov    %r10,%rdi
    49e4:	89 c6                	mov    %eax,%esi
    49e6:	e8 75 fe ff ff       	call   4860 <handle_http_method>
    49eb:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    49f3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    49fc:	75 39                	jne    4a37 <handle_client_request+0xb7>
    49fe:	31 c0                	xor    %eax,%eax
    4a00:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4a07:	c3                   	ret
    4a08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4a10:	48 8b 0d 09 46 00 00 	mov    0x4609(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4a17:	ba 12 00 00 00       	mov    $0x12,%edx
    4a1c:	be 01 00 00 00       	mov    $0x1,%esi
    4a21:	48 8d 3d 0f 17 00 00 	lea    0x170f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    4a28:	e8 73 da ff ff       	call   24a0 <fwrite@plt>
    4a2d:	bf 01 00 00 00       	mov    $0x1,%edi
    4a32:	e8 49 da ff ff       	call   2480 <exit@plt>
    4a37:	e8 d4 d8 ff ff       	call   2310 <__stack_chk_fail@plt>
    4a3c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a40 <add_accept_request>:
    4a40:	f3 0f 1e fa          	endbr64
    4a44:	55                   	push   %rbp
    4a45:	53                   	push   %rbx
    4a46:	48 89 cb             	mov    %rcx,%rbx
    4a49:	48 83 ec 08          	sub    $0x8,%rsp
    4a4d:	8b 41 44             	mov    0x44(%rcx),%eax
    4a50:	4c 8b 03             	mov    (%rbx),%r8
    4a53:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    4a59:	83 c0 01             	add    $0x1,%eax
    4a5c:	45 8b 08             	mov    (%r8),%r9d
    4a5f:	f6 c1 02             	test   $0x2,%cl
    4a62:	74 00                	je     4a64 <add_accept_request+0x24>
    4a64:	41 89 c0             	mov    %eax,%r8d
    4a67:	45 29 c8             	sub    %r9d,%r8d
    4a6a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4a6e:	0f 82 f8 da ff ff    	jb     256c <add_accept_request.cold>
    4a74:	c1 e9 0a             	shr    $0xa,%ecx
    4a77:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4a7a:	23 6b 58             	and    0x58(%rbx),%ebp
    4a7d:	89 43 44             	mov    %eax,0x44(%rbx)
    4a80:	83 e1 01             	and    $0x1,%ecx
    4a83:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4a87:	d3 e5                	shl    %cl,%ebp
    4a89:	48 c1 e5 06          	shl    $0x6,%rbp
    4a8d:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4a91:	89 7d 04             	mov    %edi,0x4(%rbp)
    4a94:	bf 10 00 00 00       	mov    $0x10,%edi
    4a99:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    4aa0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    4aa4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    4aa8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    4ab0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    4ab8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4abc:	e8 2f d9 ff ff       	call   23f0 <malloc@plt>
    4ac1:	48 89 df             	mov    %rbx,%rdi
    4ac4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    4aca:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4ace:	48 83 c4 08          	add    $0x8,%rsp
    4ad2:	5b                   	pop    %rbx
    4ad3:	5d                   	pop    %rbp
    4ad4:	e9 47 d8 ff ff       	jmp    2320 <io_uring_submit@plt>
    4ad9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004ae0 <io_thread>:
    4ae0:	f3 0f 1e fa          	endbr64
    4ae4:	41 57                	push   %r15
    4ae6:	31 d2                	xor    %edx,%edx
    4ae8:	41 56                	push   %r14
    4aea:	41 55                	push   %r13
    4aec:	41 54                	push   %r12
    4aee:	55                   	push   %rbp
    4aef:	48 89 fd             	mov    %rdi,%rbp
    4af2:	53                   	push   %rbx
    4af3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4afa:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b03:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4b0b:	48 8b 47 40          	mov    0x40(%rdi),%rax
    4b0f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4b14:	bf 00 01 00 00       	mov    $0x100,%edi
    4b19:	48 89 de             	mov    %rbx,%rsi
    4b1c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4b20:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4b25:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4b2a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4b2f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4b34:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4b3c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4b41:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4b49:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4b4e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4b56:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4b5b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4b63:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4b68:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4b70:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4b75:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4b7d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4b85:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4b8d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4b95:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4b9d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4ba5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4bad:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4bb5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4bbd:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4bc5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4bcd:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4bd4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    4bdc:	e8 ef d7 ff ff       	call   23d0 <io_uring_queue_init@plt>
    4be1:	48 8b 7d 40          	mov    0x40(%rbp),%rdi
    4be5:	31 f6                	xor    %esi,%esi
    4be7:	e8 d4 d8 ff ff       	call   24c0 <io_uring_register_eventfd@plt>
    4bec:	31 d2                	xor    %edx,%edx
    4bee:	be 01 00 00 00       	mov    $0x1,%esi
    4bf3:	bf 02 00 00 00       	mov    $0x2,%edi
    4bf8:	e8 13 d9 ff ff       	call   2510 <socket@plt>
    4bfd:	83 f8 ff             	cmp    $0xffffffff,%eax
    4c00:	0f 84 a8 d9 ff ff    	je     25ae <io_thread.cold+0x38>
    4c06:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4c0b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4c11:	89 c7                	mov    %eax,%edi
    4c13:	41 89 c4             	mov    %eax,%r12d
    4c16:	ba 02 00 00 00       	mov    $0x2,%edx
    4c1b:	be 01 00 00 00       	mov    $0x1,%esi
    4c20:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    4c28:	e8 b3 d6 ff ff       	call   22e0 <setsockopt@plt>
    4c2d:	85 c0                	test   %eax,%eax
    4c2f:	0f 88 4d d9 ff ff    	js     2582 <io_thread.cold+0xc>
    4c35:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    4c3a:	ba 10 00 00 00       	mov    $0x10,%edx
    4c3f:	44 89 e7             	mov    %r12d,%edi
    4c42:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4c4b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    4c53:	c7 44 24 40 02 00 00 50 	movl   $0x50000002,0x40(%rsp)
    4c5b:	e8 e0 d7 ff ff       	call   2440 <bind@plt>
    4c60:	85 c0                	test   %eax,%eax
    4c62:	0f 88 52 d9 ff ff    	js     25ba <io_thread.cold+0x44>
    4c68:	be 0a 00 00 00       	mov    $0xa,%esi
    4c6d:	44 89 e7             	mov    %r12d,%edi
    4c70:	e8 8b d7 ff ff       	call   2400 <listen@plt>
    4c75:	85 c0                	test   %eax,%eax
    4c77:	0f 88 11 d9 ff ff    	js     258e <io_thread.cold+0x18>
    4c7d:	ba 50 00 00 00       	mov    $0x50,%edx
    4c82:	48 8d 35 f3 14 00 00 	lea    0x14f3(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4c89:	bf 01 00 00 00       	mov    $0x1,%edi
    4c8e:	31 c0                	xor    %eax,%eax
    4c90:	e8 9b d7 ff ff       	call   2430 <__printf_chk@plt>
    4c95:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4c9a:	48 89 d9             	mov    %rbx,%rcx
    4c9d:	44 89 e7             	mov    %r12d,%edi
    4ca0:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4ca5:	48 89 c6             	mov    %rax,%rsi
    4ca8:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    4cad:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    4cb2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    4cba:	e8 81 fd ff ff       	call   4a40 <add_accept_request>
    4cbf:	bf 01 00 00 00       	mov    $0x1,%edi
    4cc4:	be 10 00 00 00       	mov    $0x10,%esi
    4cc9:	e8 b2 d6 ff ff       	call   2380 <calloc@plt>
    4cce:	bf 0a 00 00 00       	mov    $0xa,%edi
    4cd3:	49 89 c5             	mov    %rax,%r13
    4cd6:	e8 15 d7 ff ff       	call   23f0 <malloc@plt>
    4cdb:	48 85 c0             	test   %rax,%rax
    4cde:	0f 84 ce 04 00 00    	je     51b2 <io_thread+0x6d2>
    4ce4:	49 89 45 00          	mov    %rax,0x0(%r13)
    4ce8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4cef:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4cf6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    4cfe:	8d 50 01             	lea    0x1(%rax),%edx
    4d01:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4d06:	8b 30                	mov    (%rax),%esi
    4d08:	f6 c1 02             	test   $0x2,%cl
    4d0b:	0f 85 2f 04 00 00    	jne    5140 <io_thread+0x660>
    4d11:	89 d0                	mov    %edx,%eax
    4d13:	29 f0                	sub    %esi,%eax
    4d15:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4d1c:	0f 82 82 d8 ff ff    	jb     25a4 <io_thread.cold+0x2e>
    4d22:	c1 e9 0a             	shr    $0xa,%ecx
    4d25:	48 8d 75 48          	lea    0x48(%rbp),%rsi
    4d29:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4d2d:	48 89 df             	mov    %rbx,%rdi
    4d30:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4d37:	83 e1 01             	and    $0x1,%ecx
    4d3a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4d41:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4d48:	d3 e0                	shl    %cl,%eax
    4d4a:	8b 55 48             	mov    0x48(%rbp),%edx
    4d4d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4d52:	48 c1 e0 06          	shl    $0x6,%rax
    4d56:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4d5e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4d64:	89 50 04             	mov    %edx,0x4(%rax)
    4d67:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4d6f:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4d73:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    4d7b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4d83:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4d87:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4d8b:	e8 90 d5 ff ff       	call   2320 <io_uring_submit@plt>
    4d90:	8b 45 2c             	mov    0x2c(%rbp),%eax
    4d93:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4d98:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4da0:	83 f8 01             	cmp    $0x1,%eax
    4da3:	0f 85 e7 01 00 00    	jne    4f90 <io_thread+0x4b0>
    4da9:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4dae:	4d 89 ce             	mov    %r9,%r14
    4db1:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4db6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4dc0:	48 8d 3d cb 13 00 00 	lea    0x13cb(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4dc7:	e8 04 d5 ff ff       	call   22d0 <puts@plt>
    4dcc:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4dd3:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    4dda:	c1 e9 0b             	shr    $0xb,%ecx
    4ddd:	83 e1 01             	and    $0x1,%ecx
    4de0:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4de8:	8b 00                	mov    (%rax),%eax
    4dea:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4df2:	8b 16                	mov    (%rsi),%edx
    4df4:	39 d0                	cmp    %edx,%eax
    4df6:	74 36                	je     4e2e <io_thread+0x34e>
    4df8:	89 f8                	mov    %edi,%eax
    4dfa:	21 d0                	and    %edx,%eax
    4dfc:	d3 e0                	shl    %cl,%eax
    4dfe:	48 c1 e0 04          	shl    $0x4,%rax
    4e02:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    4e0a:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4e12:	0f 85 b8 01 00 00    	jne    4fd0 <io_thread+0x4f0>
    4e18:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4e1c:	0f 85 26 03 00 00    	jne    5148 <io_thread+0x668>
    4e22:	8b 40 08             	mov    0x8(%rax),%eax
    4e25:	83 c2 01             	add    $0x1,%edx
    4e28:	89 16                	mov    %edx,(%rsi)
    4e2a:	85 c0                	test   %eax,%eax
    4e2c:	79 b2                	jns    4de0 <io_thread+0x300>
    4e2e:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    4e37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4e40:	45 31 c0             	xor    %r8d,%r8d
    4e43:	31 d2                	xor    %edx,%edx
    4e45:	b9 01 00 00 00       	mov    $0x1,%ecx
    4e4a:	4c 89 f6             	mov    %r14,%rsi
    4e4d:	48 89 df             	mov    %rbx,%rdi
    4e50:	e8 cb d5 ff ff       	call   2420 <__io_uring_get_cqe@plt>
    4e55:	41 89 c7             	mov    %eax,%r15d
    4e58:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4e5d:	48 83 38 01          	cmpq   $0x1,(%rax)
    4e61:	0f 84 f1 02 00 00    	je     5158 <io_thread+0x678>
    4e67:	48 8d 3d 4a 13 00 00 	lea    0x134a(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4e6e:	e8 5d d4 ff ff       	call   22d0 <puts@plt>
    4e73:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4e78:	4c 8b 22             	mov    (%rdx),%r12
    4e7b:	45 85 ff             	test   %r15d,%r15d
    4e7e:	0f 88 f2 d6 ff ff    	js     2576 <io_thread.cold>
    4e84:	8b 42 08             	mov    0x8(%rdx),%eax
    4e87:	45 8b 04 24          	mov    (%r12),%r8d
    4e8b:	85 c0                	test   %eax,%eax
    4e8d:	0f 88 e5 02 00 00    	js     5178 <io_thread+0x698>
    4e93:	41 83 f8 01          	cmp    $0x1,%r8d
    4e97:	0f 84 83 01 00 00    	je     5020 <io_thread+0x540>
    4e9d:	41 83 f8 02          	cmp    $0x2,%r8d
    4ea1:	0f 84 a9 01 00 00    	je     5050 <io_thread+0x570>
    4ea7:	45 85 c0             	test   %r8d,%r8d
    4eaa:	0f 85 58 01 00 00    	jne    5008 <io_thread+0x528>
    4eb0:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    4eb5:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    4eba:	48 89 d9             	mov    %rbx,%rcx
    4ebd:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4ec1:	e8 7a fb ff ff       	call   4a40 <add_accept_request>
    4ec6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4ecb:	48 89 de             	mov    %rbx,%rsi
    4ece:	8b 78 08             	mov    0x8(%rax),%edi
    4ed1:	e8 0a f5 ff ff       	call   43e0 <add_read_request>
    4ed6:	4c 89 e7             	mov    %r12,%rdi
    4ed9:	e8 d2 d3 ff ff       	call   22b0 <free@plt>
    4ede:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4ee3:	48 85 c0             	test   %rax,%rax
    4ee6:	0f 85 1c 01 00 00    	jne    5008 <io_thread+0x528>
    4eec:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4ef3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4efa:	8d 50 01             	lea    0x1(%rax),%edx
    4efd:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4f02:	8b 30                	mov    (%rax),%esi
    4f04:	f6 c1 02             	test   $0x2,%cl
    4f07:	74 00                	je     4f09 <io_thread+0x429>
    4f09:	89 d0                	mov    %edx,%eax
    4f0b:	29 f0                	sub    %esi,%eax
    4f0d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4f14:	0f 82 80 d6 ff ff    	jb     259a <io_thread.cold+0x24>
    4f1a:	c1 e9 0a             	shr    $0xa,%ecx
    4f1d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    4f22:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4f26:	48 89 df             	mov    %rbx,%rdi
    4f29:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4f30:	83 e1 01             	and    $0x1,%ecx
    4f33:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4f3a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4f41:	d3 e0                	shl    %cl,%eax
    4f43:	8b 55 48             	mov    0x48(%rbp),%edx
    4f46:	48 c1 e0 06          	shl    $0x6,%rax
    4f4a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4f52:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4f58:	89 50 04             	mov    %edx,0x4(%rax)
    4f5b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4f63:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4f67:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    4f6f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4f77:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4f7b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4f7f:	e8 9c d3 ff ff       	call   2320 <io_uring_submit@plt>
    4f84:	8b 45 2c             	mov    0x2c(%rbp),%eax
    4f87:	83 f8 01             	cmp    $0x1,%eax
    4f8a:	0f 84 30 fe ff ff    	je     4dc0 <io_thread+0x2e0>
    4f90:	48 8d 3d 5a 12 00 00 	lea    0x125a(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    4f97:	e8 34 d3 ff ff       	call   22d0 <puts@plt>
    4f9c:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    4fa4:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4fad:	0f 85 26 02 00 00    	jne    51d9 <io_thread+0x6f9>
    4fb3:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    4fba:	31 c0                	xor    %eax,%eax
    4fbc:	5b                   	pop    %rbx
    4fbd:	5d                   	pop    %rbp
    4fbe:	41 5c                	pop    %r12
    4fc0:	41 5d                	pop    %r13
    4fc2:	41 5e                	pop    %r14
    4fc4:	41 5f                	pop    %r15
    4fc6:	c3                   	ret
    4fc7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4fd0:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    4fd5:	48 85 c0             	test   %rax,%rax
    4fd8:	0f 84 62 fe ff ff    	je     4e40 <io_thread+0x360>
    4fde:	48 83 38 01          	cmpq   $0x1,(%rax)
    4fe2:	0f 84 70 01 00 00    	je     5158 <io_thread+0x678>
    4fe8:	48 8d 3d c9 11 00 00 	lea    0x11c9(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4fef:	e8 dc d2 ff ff       	call   22d0 <puts@plt>
    4ff4:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4ff9:	4c 8b 22             	mov    (%rdx),%r12
    4ffc:	e9 83 fe ff ff       	jmp    4e84 <io_thread+0x3a4>
    5001:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5008:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5010:	8b 02                	mov    (%rdx),%eax
    5012:	83 c0 01             	add    $0x1,%eax
    5015:	89 02                	mov    %eax,(%rdx)
    5017:	e9 d0 fe ff ff       	jmp    4eec <io_thread+0x40c>
    501c:	0f 1f 40 00          	nopl   0x0(%rax)
    5020:	85 c0                	test   %eax,%eax
    5022:	75 7c                	jne    50a0 <io_thread+0x5c0>
    5024:	48 8b 0d f5 3f 00 00 	mov    0x3ff5(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    502b:	ba 0f 00 00 00       	mov    $0xf,%edx
    5030:	be 01 00 00 00       	mov    $0x1,%esi
    5035:	48 8d 3d a5 11 00 00 	lea    0x11a5(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    503c:	e8 5f d4 ff ff       	call   24a0 <fwrite@plt>
    5041:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5046:	e9 98 fe ff ff       	jmp    4ee3 <io_thread+0x403>
    504b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5050:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5055:	45 31 ff             	xor    %r15d,%r15d
    5058:	85 c0                	test   %eax,%eax
    505a:	7e 20                	jle    507c <io_thread+0x59c>
    505c:	0f 1f 40 00          	nopl   0x0(%rax)
    5060:	4c 89 f8             	mov    %r15,%rax
    5063:	49 83 c7 01          	add    $0x1,%r15
    5067:	48 c1 e0 04          	shl    $0x4,%rax
    506b:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5070:	e8 3b d2 ff ff       	call   22b0 <free@plt>
    5075:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    507a:	7f e4                	jg     5060 <io_thread+0x580>
    507c:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5081:	e8 ca d2 ff ff       	call   2350 <close@plt>
    5086:	4c 89 e7             	mov    %r12,%rdi
    5089:	e8 22 d2 ff ff       	call   22b0 <free@plt>
    508e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5093:	e9 4b fe ff ff       	jmp    4ee3 <io_thread+0x403>
    5098:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    50a0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    50a5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    50aa:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    50b2:	eb 11                	jmp    50c5 <io_thread+0x5e5>
    50b4:	0f 1f 40 00          	nopl   0x0(%rax)
    50b8:	48 83 c0 01          	add    $0x1,%rax
    50bc:	48 83 c2 01          	add    $0x1,%rdx
    50c0:	48 39 c6             	cmp    %rax,%rsi
    50c3:	74 4b                	je     5110 <io_thread+0x630>
    50c5:	0f b6 0a             	movzbl (%rdx),%ecx
    50c8:	88 08                	mov    %cl,(%rax)
    50ca:	80 f9 0d             	cmp    $0xd,%cl
    50cd:	75 e9                	jne    50b8 <io_thread+0x5d8>
    50cf:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    50d3:	75 e3                	jne    50b8 <io_thread+0x5d8>
    50d5:	c6 00 00             	movb   $0x0,(%rax)
    50d8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    50dd:	48 89 da             	mov    %rbx,%rdx
    50e0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    50e5:	e8 76 f7 ff ff       	call   4860 <handle_http_method>
    50ea:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    50ef:	e8 bc d1 ff ff       	call   22b0 <free@plt>
    50f4:	4c 89 e7             	mov    %r12,%rdi
    50f7:	e8 b4 d1 ff ff       	call   22b0 <free@plt>
    50fc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5101:	e9 dd fd ff ff       	jmp    4ee3 <io_thread+0x403>
    5106:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5110:	48 8b 0d 09 3f 00 00 	mov    0x3f09(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5117:	ba 12 00 00 00       	mov    $0x12,%edx
    511c:	be 01 00 00 00       	mov    $0x1,%esi
    5121:	48 8d 3d 0f 10 00 00 	lea    0x100f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    5128:	e8 73 d3 ff ff       	call   24a0 <fwrite@plt>
    512d:	bf 01 00 00 00       	mov    $0x1,%edi
    5132:	e8 49 d3 ff ff       	call   2480 <exit@plt>
    5137:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5140:	e9 cc fb ff ff       	jmp    4d11 <io_thread+0x231>
    5145:	0f 1f 00             	nopl   (%rax)
    5148:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    514d:	e9 8c fe ff ff       	jmp    4fde <io_thread+0x4fe>
    5152:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5158:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5160:	48 8d 3d 3d 10 00 00 	lea    0x103d(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    5167:	8b 02                	mov    (%rdx),%eax
    5169:	83 c0 01             	add    $0x1,%eax
    516c:	89 02                	mov    %eax,(%rdx)
    516e:	e8 5d d1 ff ff       	call   22d0 <puts@plt>
    5173:	e9 18 fe ff ff       	jmp    4f90 <io_thread+0x4b0>
    5178:	f7 d8                	neg    %eax
    517a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    517f:	89 c7                	mov    %eax,%edi
    5181:	e8 5a d3 ff ff       	call   24e0 <strerror@plt>
    5186:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    518b:	be 01 00 00 00       	mov    $0x1,%esi
    5190:	48 8b 3d 89 3e 00 00 	mov    0x3e89(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    5197:	48 89 c1             	mov    %rax,%rcx
    519a:	48 8d 15 cf 12 00 00 	lea    0x12cf(%rip),%rdx        # 6470 <_IO_stdin_used+0x470>
    51a1:	31 c0                	xor    %eax,%eax
    51a3:	e8 08 d3 ff ff       	call   24b0 <__fprintf_chk@plt>
    51a8:	bf 01 00 00 00       	mov    $0x1,%edi
    51ad:	e8 ce d2 ff ff       	call   2480 <exit@plt>
    51b2:	48 8b 0d 67 3e 00 00 	mov    0x3e67(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    51b9:	ba 28 00 00 00       	mov    $0x28,%edx
    51be:	be 01 00 00 00       	mov    $0x1,%esi
    51c3:	48 8d 3d 76 12 00 00 	lea    0x1276(%rip),%rdi        # 6440 <_IO_stdin_used+0x440>
    51ca:	e8 d1 d2 ff ff       	call   24a0 <fwrite@plt>
    51cf:	bf 01 00 00 00       	mov    $0x1,%edi
    51d4:	e8 a7 d2 ff ff       	call   2480 <exit@plt>
    51d9:	e8 32 d1 ff ff       	call   2310 <__stack_chk_fail@plt>
    51de:	66 90                	xchg   %ax,%ax

00000000000051e0 <receive>:
    51e0:	f3 0f 1e fa          	endbr64
    51e4:	8b 57 3c             	mov    0x3c(%rdi),%edx
    51e7:	85 d2                	test   %edx,%edx
    51e9:	0f 8e d1 00 00 00    	jle    52c0 <receive+0xe0>
    51ef:	48 89 f8             	mov    %rdi,%rax
    51f2:	45 31 db             	xor    %r11d,%r11d
    51f5:	0f 1f 00             	nopl   (%rax)
    51f8:	48 8b 50 70          	mov    0x70(%rax),%rdx
    51fc:	4c 89 df             	mov    %r11,%rdi
    51ff:	48 c1 e7 05          	shl    $0x5,%rdi
    5203:	4c 8b 0c 3a          	mov    (%rdx,%rdi,1),%r9
    5207:	49 8b 51 08          	mov    0x8(%r9),%rdx
    520b:	48 85 d2             	test   %rdx,%rdx
    520e:	0f 8e 94 00 00 00    	jle    52a8 <receive+0xc8>
    5214:	4d 8b 11             	mov    (%r9),%r10
    5217:	31 d2                	xor    %edx,%edx
    5219:	eb 12                	jmp    522d <receive+0x4d>
    521b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5220:	49 8b 49 08          	mov    0x8(%r9),%rcx
    5224:	48 83 c2 01          	add    $0x1,%rdx
    5228:	48 39 d1             	cmp    %rdx,%rcx
    522b:	7e 7b                	jle    52a8 <receive+0xc8>
    522d:	48 8b 48 78          	mov    0x78(%rax),%rcx
    5231:	49 8b 34 d2          	mov    (%r10,%rdx,8),%rsi
    5235:	48 83 c1 01          	add    $0x1,%rcx
    5239:	4c 8b 46 10          	mov    0x10(%rsi),%r8
    523d:	48 89 48 78          	mov    %rcx,0x78(%rax)
    5241:	48 8b 48 10          	mov    0x10(%rax),%rcx
    5245:	48 83 c1 01          	add    $0x1,%rcx
    5249:	48 89 48 10          	mov    %rcx,0x10(%rax)
    524d:	48 8b 48 70          	mov    0x70(%rax),%rcx
    5251:	48 83 44 39 18 01    	addq   $0x1,0x18(%rcx,%rdi,1)
    5257:	48 63 08             	movslq (%rax),%rcx
    525a:	49 39 c8             	cmp    %rcx,%r8
    525d:	75 c1                	jne    5220 <receive+0x40>
    525f:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    5263:	48 63 48 38          	movslq 0x38(%rax),%rcx
    5267:	48 39 ce             	cmp    %rcx,%rsi
    526a:	75 b4                	jne    5220 <receive+0x40>
    526c:	48 83 ec 08          	sub    $0x8,%rsp
    5270:	48 63 50 38          	movslq 0x38(%rax),%rdx
    5274:	48 63 00             	movslq (%rax),%rax
    5277:	31 c9                	xor    %ecx,%ecx
    5279:	bf 01 00 00 00       	mov    $0x1,%edi
    527e:	48 39 f2             	cmp    %rsi,%rdx
    5281:	48 8d 35 10 12 00 00 	lea    0x1210(%rip),%rsi        # 6498 <_IO_stdin_used+0x498>
    5288:	0f 94 c1             	sete   %cl
    528b:	31 d2                	xor    %edx,%edx
    528d:	4c 39 c0             	cmp    %r8,%rax
    5290:	0f 94 c2             	sete   %dl
    5293:	31 c0                	xor    %eax,%eax
    5295:	e8 96 d1 ff ff       	call   2430 <__printf_chk@plt>
    529a:	bf 01 00 00 00       	mov    $0x1,%edi
    529f:	e8 dc d1 ff ff       	call   2480 <exit@plt>
    52a4:	0f 1f 40 00          	nopl   0x0(%rax)
    52a8:	49 c7 41 08 00 00 00 00 	movq   $0x0,0x8(%r9)
    52b0:	8b 50 3c             	mov    0x3c(%rax),%edx
    52b3:	49 83 c3 01          	add    $0x1,%r11
    52b7:	44 39 da             	cmp    %r11d,%edx
    52ba:	0f 8f 38 ff ff ff    	jg     51f8 <receive+0x18>
    52c0:	c3                   	ret
    52c1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    52cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000052d0 <barriered_work>:
    52d0:	f3 0f 1e fa          	endbr64
    52d4:	41 55                	push   %r13
    52d6:	41 54                	push   %r12
    52d8:	55                   	push   %rbp
    52d9:	53                   	push   %rbx
    52da:	48 89 fb             	mov    %rdi,%rbx
    52dd:	48 83 ec 08          	sub    $0x8,%rsp
    52e1:	8b 57 38             	mov    0x38(%rdi),%edx
    52e4:	8b 07                	mov    (%rdi),%eax
    52e6:	39 c2                	cmp    %eax,%edx
    52e8:	0f 84 d2 00 00 00    	je     53c0 <barriered_work+0xf0>
    52ee:	e8 ed fe ff ff       	call   51e0 <receive>
    52f3:	8b 43 48             	mov    0x48(%rbx),%eax
    52f6:	83 f8 01             	cmp    $0x1,%eax
    52f9:	75 19                	jne    5314 <barriered_work+0x44>
    52fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5300:	48 8b 43 10          	mov    0x10(%rbx),%rax
    5304:	48 83 c0 01          	add    $0x1,%rax
    5308:	48 89 43 10          	mov    %rax,0x10(%rbx)
    530c:	8b 43 48             	mov    0x48(%rbx),%eax
    530f:	83 f8 01             	cmp    $0x1,%eax
    5312:	74 ec                	je     5300 <barriered_work+0x30>
    5314:	8b 83 80 00 00 00    	mov    0x80(%rbx),%eax
    531a:	83 f8 01             	cmp    $0x1,%eax
    531d:	74 10                	je     532f <barriered_work+0x5f>
    531f:	0f ae f0             	mfence
    5322:	48 83 c4 08          	add    $0x8,%rsp
    5326:	31 c0                	xor    %eax,%eax
    5328:	5b                   	pop    %rbx
    5329:	5d                   	pop    %rbp
    532a:	41 5c                	pop    %r12
    532c:	41 5d                	pop    %r13
    532e:	c3                   	ret
    532f:	8b 43 3c             	mov    0x3c(%rbx),%eax
    5332:	85 c0                	test   %eax,%eax
    5334:	7e e9                	jle    531f <barriered_work+0x4f>
    5336:	45 31 c9             	xor    %r9d,%r9d
    5339:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5340:	8b 43 38             	mov    0x38(%rbx),%eax
    5343:	44 39 c8             	cmp    %r9d,%eax
    5346:	74 5e                	je     53a6 <barriered_work+0xd6>
    5348:	48 8b 43 70          	mov    0x70(%rbx),%rax
    534c:	4c 89 c9             	mov    %r9,%rcx
    534f:	48 c1 e1 05          	shl    $0x5,%rcx
    5353:	48 8b 54 08 08       	mov    0x8(%rax,%rcx,1),%rdx
    5358:	48 8b 42 08          	mov    0x8(%rdx),%rax
    535c:	48 63 7a 10          	movslq 0x10(%rdx),%rdi
    5360:	48 39 f8             	cmp    %rdi,%rax
    5363:	7d 41                	jge    53a6 <barriered_work+0xd6>
    5365:	4c 8b 02             	mov    (%rdx),%r8
    5368:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5370:	48 8b 43 10          	mov    0x10(%rbx),%rax
    5374:	48 83 c0 01          	add    $0x1,%rax
    5378:	48 89 43 10          	mov    %rax,0x10(%rbx)
    537c:	48 8b 43 70          	mov    0x70(%rbx),%rax
    5380:	48 83 44 08 10 01    	addq   $0x1,0x10(%rax,%rcx,1)
    5386:	48 8b 42 08          	mov    0x8(%rdx),%rax
    538a:	48 8d 70 01          	lea    0x1(%rax),%rsi
    538e:	48 89 72 08          	mov    %rsi,0x8(%rdx)
    5392:	48 8b b3 88 00 00 00 	mov    0x88(%rbx),%rsi
    5399:	49 89 34 c0          	mov    %rsi,(%r8,%rax,8)
    539d:	48 8b 42 08          	mov    0x8(%rdx),%rax
    53a1:	48 39 f8             	cmp    %rdi,%rax
    53a4:	7c ca                	jl     5370 <barriered_work+0xa0>
    53a6:	8b 43 3c             	mov    0x3c(%rbx),%eax
    53a9:	49 83 c1 01          	add    $0x1,%r9
    53ad:	44 39 c8             	cmp    %r9d,%eax
    53b0:	7f 8e                	jg     5340 <barriered_work+0x70>
    53b2:	e9 68 ff ff ff       	jmp    531f <barriered_work+0x4f>
    53b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    53c0:	e8 1b fe ff ff       	call   51e0 <receive>
    53c5:	8b 3b                	mov    (%rbx),%edi
    53c7:	8b 43 3c             	mov    0x3c(%rbx),%eax
    53ca:	85 c0                	test   %eax,%eax
    53cc:	0f 8e b4 00 00 00    	jle    5486 <barriered_work+0x1b6>
    53d2:	48 63 c7             	movslq %edi,%rax
    53d5:	45 31 d2             	xor    %r10d,%r10d
    53d8:	45 31 e4             	xor    %r12d,%r12d
    53db:	83 c7 01             	add    $0x1,%edi
    53de:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    53e2:	48 8d 2c 50          	lea    (%rax,%rdx,2),%rbp
    53e6:	48 c1 e5 03          	shl    $0x3,%rbp
    53ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    53f0:	8b 43 3c             	mov    0x3c(%rbx),%eax
    53f3:	4d 89 e3             	mov    %r12,%r11
    53f6:	31 f6                	xor    %esi,%esi
    53f8:	31 c9                	xor    %ecx,%ecx
    53fa:	49 c1 e3 05          	shl    $0x5,%r11
    53fe:	85 c0                	test   %eax,%eax
    5400:	7e 6d                	jle    546f <barriered_work+0x19f>
    5402:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5408:	44 8b 6b 3c          	mov    0x3c(%rbx),%r13d
    540c:	48 8b 43 30          	mov    0x30(%rbx),%rax
    5410:	48 8b 40 10          	mov    0x10(%rax),%rax
    5414:	4a 8b 54 10 20       	mov    0x20(%rax,%r10,1),%rdx
    5419:	48 01 ea             	add    %rbp,%rdx
    541c:	4c 8b 42 70          	mov    0x70(%rdx),%r8
    5420:	48 8b 43 30          	mov    0x30(%rbx),%rax
    5424:	4c 8b 48 10          	mov    0x10(%rax),%r9
    5428:	89 f8                	mov    %edi,%eax
    542a:	99                   	cltd
    542b:	41 f7 fd             	idiv   %r13d
    542e:	89 d0                	mov    %edx,%eax
    5430:	f7 d8                	neg    %eax
    5432:	0f 49 d0             	cmovns %eax,%edx
    5435:	48 63 d2             	movslq %edx,%rdx
    5438:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    543c:	48 8d 14 42          	lea    (%rdx,%rax,2),%rdx
    5440:	49 8b 44 31 20       	mov    0x20(%r9,%rsi,1),%rax
    5445:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
    544c:	48 8d 04 d0          	lea    (%rax,%rdx,8),%rax
    5450:	48 89 ca             	mov    %rcx,%rdx
    5453:	48 83 c1 01          	add    $0x1,%rcx
    5457:	48 c1 e2 05          	shl    $0x5,%rdx
    545b:	48 8b 40 70          	mov    0x70(%rax),%rax
    545f:	49 8b 54 10 08       	mov    0x8(%r8,%rdx,1),%rdx
    5464:	4a 89 14 18          	mov    %rdx,(%rax,%r11,1)
    5468:	8b 43 3c             	mov    0x3c(%rbx),%eax
    546b:	39 c8                	cmp    %ecx,%eax
    546d:	7f 99                	jg     5408 <barriered_work+0x138>
    546f:	8b 43 3c             	mov    0x3c(%rbx),%eax
    5472:	49 83 c4 01          	add    $0x1,%r12
    5476:	49 81 c2 98 00 00 00 	add    $0x98,%r10
    547d:	44 39 e0             	cmp    %r12d,%eax
    5480:	0f 8f 6a ff ff ff    	jg     53f0 <barriered_work+0x120>
    5486:	0f ae f0             	mfence
    5489:	48 8b 73 50          	mov    0x50(%rbx),%rsi
    548d:	48 8b 43 60          	mov    0x60(%rbx),%rax
    5491:	31 ff                	xor    %edi,%edi
    5493:	48 c1 e0 05          	shl    $0x5,%rax
    5497:	48 01 c6             	add    %rax,%rsi
    549a:	e8 51 ce ff ff       	call   22f0 <clock_gettime@plt>
    549f:	48 8b 43 30          	mov    0x30(%rbx),%rax
    54a3:	48 8b 40 30          	mov    0x30(%rax),%rax
    54a7:	8b 78 10             	mov    0x10(%rax),%edi
    54aa:	8d 6f 01             	lea    0x1(%rdi),%ebp
    54ad:	89 68 10             	mov    %ebp,0x10(%rax)
    54b0:	8b 43 48             	mov    0x48(%rbx),%eax
    54b3:	83 f8 01             	cmp    $0x1,%eax
    54b6:	75 4d                	jne    5505 <barriered_work+0x235>
    54b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    54c0:	48 8b 43 10          	mov    0x10(%rbx),%rax
    54c4:	48 83 c0 01          	add    $0x1,%rax
    54c8:	48 89 43 10          	mov    %rax,0x10(%rbx)
    54cc:	48 8b 4b 28          	mov    0x28(%rbx),%rcx
    54d0:	48 8b 73 30          	mov    0x30(%rbx),%rsi
    54d4:	48 63 43 38          	movslq 0x38(%rbx),%rax
    54d8:	48 63 13             	movslq (%rbx),%rdx
    54db:	48 8d 3c c0          	lea    (%rax,%rax,8),%rdi
    54df:	48 8d 04 78          	lea    (%rax,%rdi,2),%rax
    54e3:	48 8b 7e 10          	mov    0x10(%rsi),%rdi
    54e7:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
    54eb:	48 8d 14 72          	lea    (%rdx,%rsi,2),%rdx
    54ef:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    54f3:	48 8b 40 20          	mov    0x20(%rax),%rax
    54f7:	48 8d 3c d0          	lea    (%rax,%rdx,8),%rdi
    54fb:	ff d1                	call   *%rcx
    54fd:	8b 43 48             	mov    0x48(%rbx),%eax
    5500:	83 f8 01             	cmp    $0x1,%eax
    5503:	74 bb                	je     54c0 <barriered_work+0x1f0>
    5505:	48 8b 43 30          	mov    0x30(%rbx),%rax
    5509:	48 8b 40 30          	mov    0x30(%rax),%rax
    550d:	3b 68 10             	cmp    0x10(%rax),%ebp
    5510:	75 32                	jne    5544 <barriered_work+0x274>
    5512:	48 8b 53 50          	mov    0x50(%rbx),%rdx
    5516:	48 8b 43 60          	mov    0x60(%rbx),%rax
    551a:	31 ff                	xor    %edi,%edi
    551c:	48 c1 e0 05          	shl    $0x5,%rax
    5520:	48 8d 74 02 10       	lea    0x10(%rdx,%rax,1),%rsi
    5525:	e8 c6 cd ff ff       	call   22f0 <clock_gettime@plt>
    552a:	48 8b 43 60          	mov    0x60(%rbx),%rax
    552e:	48 8b 4b 58          	mov    0x58(%rbx),%rcx
    5532:	48 83 c0 01          	add    $0x1,%rax
    5536:	48 99                	cqto
    5538:	48 f7 f9             	idiv   %rcx
    553b:	48 89 53 60          	mov    %rdx,0x60(%rbx)
    553f:	e9 db fd ff ff       	jmp    531f <barriered_work+0x4f>
    5544:	48 8d 3d b9 0c 00 00 	lea    0xcb9(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    554b:	e8 80 cd ff ff       	call   22d0 <puts@plt>
    5550:	eb c0                	jmp    5512 <barriered_work+0x242>
    5552:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    555d:	0f 1f 00             	nopl   (%rax)

0000000000005560 <barriered_work_ingest>:
    5560:	f3 0f 1e fa          	endbr64
    5564:	48 83 ec 08          	sub    $0x8,%rsp
    5568:	48 8b 47 30          	mov    0x30(%rdi),%rax
    556c:	48 8b 40 38          	mov    0x38(%rax),%rax
    5570:	8b 00                	mov    (%rax),%eax
    5572:	85 c0                	test   %eax,%eax
    5574:	7e 57                	jle    55cd <barriered_work_ingest+0x6d>
    5576:	31 c0                	xor    %eax,%eax
    5578:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5580:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
    5584:	48 89 c2             	mov    %rax,%rdx
    5587:	48 c1 e2 04          	shl    $0x4,%rdx
    558b:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    558f:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    5593:	48 01 d6             	add    %rdx,%rsi
    5596:	8b 4e 08             	mov    0x8(%rsi),%ecx
    5599:	83 f9 01             	cmp    $0x1,%ecx
    559c:	75 1f                	jne    55bd <barriered_work_ingest+0x5d>
    559e:	48 8b 4f 68          	mov    0x68(%rdi),%rcx
    55a2:	48 83 c1 01          	add    $0x1,%rcx
    55a6:	48 89 4f 68          	mov    %rcx,0x68(%rdi)
    55aa:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
    55ae:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    55b2:	48 03 51 08          	add    0x8(%rcx),%rdx
    55b6:	c7 42 08 00 00 00 00 	movl   $0x0,0x8(%rdx)
    55bd:	48 8b 57 30          	mov    0x30(%rdi),%rdx
    55c1:	48 83 c0 01          	add    $0x1,%rax
    55c5:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    55c9:	39 02                	cmp    %eax,(%rdx)
    55cb:	7f b3                	jg     5580 <barriered_work_ingest+0x20>
    55cd:	0f ae f0             	mfence
    55d0:	e8 fb fc ff ff       	call   52d0 <barriered_work>
    55d5:	31 c0                	xor    %eax,%eax
    55d7:	48 83 c4 08          	add    $0x8,%rsp
    55db:	c3                   	ret
    55dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000055e0 <barriered_nulltask>:
    55e0:	f3 0f 1e fa          	endbr64
    55e4:	31 c0                	xor    %eax,%eax
    55e6:	c3                   	ret
    55e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000055f0 <barriered_steal>:
    55f0:	f3 0f 1e fa          	endbr64
    55f4:	31 c0                	xor    %eax,%eax
    55f6:	c3                   	ret
    55f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005600 <after>:
    5600:	f3 0f 1e fa          	endbr64
    5604:	31 c0                	xor    %eax,%eax
    5606:	48 39 d7             	cmp    %rdx,%rdi
    5609:	7e 08                	jle    5613 <after+0x13>
    560b:	31 c0                	xor    %eax,%eax
    560d:	48 39 ce             	cmp    %rcx,%rsi
    5610:	0f 9f c0             	setg   %al
    5613:	c3                   	ret
    5614:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    561f:	90                   	nop

0000000000005620 <within>:
    5620:	f3 0f 1e fa          	endbr64
    5624:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5629:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    562e:	31 c0                	xor    %eax,%eax
    5630:	48 39 d7             	cmp    %rdx,%rdi
    5633:	7f 18                	jg     564d <within+0x2d>
    5635:	4d 39 d8             	cmp    %r11,%r8
    5638:	0f 9e c2             	setle  %dl
    563b:	48 39 ce             	cmp    %rcx,%rsi
    563e:	0f 9e c0             	setle  %al
    5641:	21 c2                	and    %eax,%edx
    5643:	31 c0                	xor    %eax,%eax
    5645:	4d 39 d1             	cmp    %r10,%r9
    5648:	0f 9e c0             	setle  %al
    564b:	21 d0                	and    %edx,%eax
    564d:	c3                   	ret
    564e:	66 90                	xchg   %ax,%ax

0000000000005650 <overlap>:
    5650:	f3 0f 1e fa          	endbr64
    5654:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5659:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    565e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5663:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5668:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    566d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
    5672:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5677:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    567c:	48 39 fe             	cmp    %rdi,%rsi
    567f:	7d 2f                	jge    56b0 <overlap+0x60>
    5681:	48 39 ca             	cmp    %rcx,%rdx
    5684:	7d 62                	jge    56e8 <overlap+0x98>
    5686:	4d 39 da             	cmp    %r11,%r10
    5689:	7d 0e                	jge    5699 <overlap+0x49>
    568b:	b8 01 00 00 00       	mov    $0x1,%eax
    5690:	4d 39 c1             	cmp    %r8,%r9
    5693:	0f 8c 7f 00 00 00    	jl     5718 <overlap+0xc8>
    5699:	31 c0                	xor    %eax,%eax
    569b:	4d 39 c1             	cmp    %r8,%r9
    569e:	7f 4c                	jg     56ec <overlap+0x9c>
    56a0:	31 c0                	xor    %eax,%eax
    56a2:	4d 39 da             	cmp    %r11,%r10
    56a5:	0f 9e c0             	setle  %al
    56a8:	c3                   	ret
    56a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    56b0:	7e 4e                	jle    5700 <overlap+0xb0>
    56b2:	48 39 ca             	cmp    %rcx,%rdx
    56b5:	7f 39                	jg     56f0 <overlap+0xa0>
    56b7:	75 31                	jne    56ea <overlap+0x9a>
    56b9:	4d 39 c1             	cmp    %r8,%r9
    56bc:	7c 2c                	jl     56ea <overlap+0x9a>
    56be:	b8 01 00 00 00       	mov    $0x1,%eax
    56c3:	4d 39 da             	cmp    %r11,%r10
    56c6:	7d 24                	jge    56ec <overlap+0x9c>
    56c8:	48 39 ca             	cmp    %rcx,%rdx
    56cb:	0f 94 c2             	sete   %dl
    56ce:	48 39 fe             	cmp    %rdi,%rsi
    56d1:	0f 94 c0             	sete   %al
    56d4:	21 c2                	and    %eax,%edx
    56d6:	31 c0                	xor    %eax,%eax
    56d8:	4d 39 c1             	cmp    %r8,%r9
    56db:	0f 94 c0             	sete   %al
    56de:	21 d0                	and    %edx,%eax
    56e0:	c3                   	ret
    56e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    56e8:	74 af                	je     5699 <overlap+0x49>
    56ea:	31 c0                	xor    %eax,%eax
    56ec:	c3                   	ret
    56ed:	0f 1f 00             	nopl   (%rax)
    56f0:	4d 39 da             	cmp    %r11,%r10
    56f3:	7e c4                	jle    56b9 <overlap+0x69>
    56f5:	b8 01 00 00 00       	mov    $0x1,%eax
    56fa:	4d 39 c1             	cmp    %r8,%r9
    56fd:	7e ba                	jle    56b9 <overlap+0x69>
    56ff:	c3                   	ret
    5700:	48 39 ca             	cmp    %rcx,%rdx
    5703:	7c 94                	jl     5699 <overlap+0x49>
    5705:	4d 39 c1             	cmp    %r8,%r9
    5708:	7d b4                	jge    56be <overlap+0x6e>
    570a:	48 39 ca             	cmp    %rcx,%rdx
    570d:	74 91                	je     56a0 <overlap+0x50>
    570f:	eb d9                	jmp    56ea <overlap+0x9a>
    5711:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5718:	c3                   	ret
    5719:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005720 <verify>:
    5720:	f3 0f 1e fa          	endbr64
    5724:	85 f6                	test   %esi,%esi
    5726:	0f 8e 27 03 00 00    	jle    5a53 <verify+0x333>
    572c:	41 57                	push   %r15
    572e:	41 56                	push   %r14
    5730:	41 89 f6             	mov    %esi,%r14d
    5733:	41 55                	push   %r13
    5735:	4c 8d 6f 20          	lea    0x20(%rdi),%r13
    5739:	41 54                	push   %r12
    573b:	55                   	push   %rbp
    573c:	31 ed                	xor    %ebp,%ebp
    573e:	53                   	push   %rbx
    573f:	48 83 ec 48          	sub    $0x48,%rsp
    5743:	4c 89 6c 24 08       	mov    %r13,0x8(%rsp)
    5748:	4c 89 2c 24          	mov    %r13,(%rsp)
    574c:	45 31 e4             	xor    %r12d,%r12d
    574f:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    5754:	44 39 e5             	cmp    %r12d,%ebp
    5757:	0f 84 2e 02 00 00    	je     598b <verify+0x26b>
    575d:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5762:	8b 50 08             	mov    0x8(%rax),%edx
    5765:	85 d2                	test   %edx,%edx
    5767:	0f 8e 1e 02 00 00    	jle    598b <verify+0x26b>
    576d:	c7 44 24 2c 00 00 00 00 	movl   $0x0,0x2c(%rsp)
    5775:	45 31 ff             	xor    %r15d,%r15d
    5778:	44 89 64 24 38       	mov    %r12d,0x38(%rsp)
    577d:	89 ea                	mov    %ebp,%edx
    577f:	48 8d 35 8e 0a 00 00 	lea    0xa8e(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    5786:	bf 01 00 00 00       	mov    $0x1,%edi
    578b:	31 c0                	xor    %eax,%eax
    578d:	e8 9e cc ff ff       	call   2430 <__printf_chk@plt>
    5792:	48 8b 04 24          	mov    (%rsp),%rax
    5796:	8b 40 08             	mov    0x8(%rax),%eax
    5799:	85 c0                	test   %eax,%eax
    579b:	0f 8e c7 01 00 00    	jle    5968 <verify+0x248>
    57a1:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    57a6:	44 89 74 24 3c       	mov    %r14d,0x3c(%rsp)
    57ab:	45 31 e4             	xor    %r12d,%r12d
    57ae:	89 eb                	mov    %ebp,%ebx
    57b0:	4c 8b 28             	mov    (%rax),%r13
    57b3:	4d 01 fd             	add    %r15,%r13
    57b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    57c0:	48 8b 3c 24          	mov    (%rsp),%rdi
    57c4:	4b 8d 04 e4          	lea    (%r12,%r12,8),%rax
    57c8:	49 8b 4d 60          	mov    0x60(%r13),%rcx
    57cc:	48 8d 35 56 0a 00 00 	lea    0xa56(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    57d3:	49 8d 2c 44          	lea    (%r12,%rax,2),%rbp
    57d7:	48 8b 07             	mov    (%rdi),%rax
    57da:	48 c1 e5 03          	shl    $0x3,%rbp
    57de:	bf 01 00 00 00       	mov    $0x1,%edi
    57e3:	48 01 e8             	add    %rbp,%rax
    57e6:	48 8b 50 60          	mov    0x60(%rax),%rdx
    57ea:	31 c0                	xor    %eax,%eax
    57ec:	e8 3f cc ff ff       	call   2430 <__printf_chk@plt>
    57f1:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    57f6:	4c 8b 28             	mov    (%rax),%r13
    57f9:	4d 01 fd             	add    %r15,%r13
    57fc:	49 8b 45 60          	mov    0x60(%r13),%rax
    5800:	48 85 c0             	test   %rax,%rax
    5803:	0f 8e 46 01 00 00    	jle    594f <verify+0x22f>
    5809:	48 8b 3c 24          	mov    (%rsp),%rdi
    580d:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    5812:	45 31 f6             	xor    %r14d,%r14d
    5815:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    581a:	41 89 dc             	mov    %ebx,%r12d
    581d:	48 8b 17             	mov    (%rdi),%rdx
    5820:	48 01 ea             	add    %rbp,%rdx
    5823:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5828:	48 8b 42 60          	mov    0x60(%rdx),%rax
    582c:	4c 89 f5             	mov    %r14,%rbp
    582f:	31 db                	xor    %ebx,%ebx
    5831:	48 c1 e5 05          	shl    $0x5,%rbp
    5835:	48 85 c0             	test   %rax,%rax
    5838:	0f 8e f8 00 00 00    	jle    5936 <verify+0x216>
    583e:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
    5843:	eb 34                	jmp    5879 <verify+0x159>
    5845:	0f 1f 00             	nopl   (%rax)
    5848:	48 39 fe             	cmp    %rdi,%rsi
    584b:	0f 8d 5f 01 00 00    	jge    59b0 <verify+0x290>
    5851:	4d 39 d3             	cmp    %r10,%r11
    5854:	7e 05                	jle    585b <verify+0x13b>
    5856:	49 39 c6             	cmp    %rax,%r14
    5859:	7c 75                	jl     58d0 <verify+0x1b0>
    585b:	4d 39 d3             	cmp    %r10,%r11
    585e:	0f 8d b3 01 00 00    	jge    5a17 <verify+0x2f7>
    5864:	0f 1f 40 00          	nopl   0x0(%rax)
    5868:	48 8b 42 60          	mov    0x60(%rdx),%rax
    586c:	48 83 c3 01          	add    $0x1,%rbx
    5870:	48 39 d8             	cmp    %rbx,%rax
    5873:	0f 8e b8 00 00 00    	jle    5931 <verify+0x211>
    5879:	48 8b 42 50          	mov    0x50(%rdx),%rax
    587d:	48 89 d9             	mov    %rbx,%rcx
    5880:	49 8b 75 50          	mov    0x50(%r13),%rsi
    5884:	48 c1 e1 05          	shl    $0x5,%rcx
    5888:	48 01 ee             	add    %rbp,%rsi
    588b:	48 01 c8             	add    %rcx,%rax
    588e:	4c 8b 0e             	mov    (%rsi),%r9
    5891:	4c 8b 00             	mov    (%rax),%r8
    5894:	48 8b 7e 08          	mov    0x8(%rsi),%rdi
    5898:	4c 8b 56 10          	mov    0x10(%rsi),%r10
    589c:	4c 8b 76 18          	mov    0x18(%rsi),%r14
    58a0:	4c 8b 58 10          	mov    0x10(%rax),%r11
    58a4:	48 8b 70 08          	mov    0x8(%rax),%rsi
    58a8:	48 8b 40 18          	mov    0x18(%rax),%rax
    58ac:	4d 39 c8             	cmp    %r9,%r8
    58af:	7c 97                	jl     5848 <verify+0x128>
    58b1:	0f 8e 49 01 00 00    	jle    5a00 <verify+0x2e0>
    58b7:	48 39 fe             	cmp    %rdi,%rsi
    58ba:	0f 8f 00 01 00 00    	jg     59c0 <verify+0x2a0>
    58c0:	75 a6                	jne    5868 <verify+0x148>
    58c2:	4d 39 d3             	cmp    %r10,%r11
    58c5:	7f a1                	jg     5868 <verify+0x148>
    58c7:	49 39 c6             	cmp    %rax,%r14
    58ca:	7c 9c                	jl     5868 <verify+0x148>
    58cc:	0f 1f 40 00          	nopl   0x0(%rax)
    58d0:	48 8b 7a 50          	mov    0x50(%rdx),%rdi
    58d4:	49 8b 75 50          	mov    0x50(%r13),%rsi
    58d8:	48 83 c3 01          	add    $0x1,%rbx
    58dc:	48 8b 42 50          	mov    0x50(%rdx),%rax
    58e0:	49 8b 55 50          	mov    0x50(%r13),%rdx
    58e4:	4c 8b 4c 0f 18       	mov    0x18(%rdi,%rcx,1),%r9
    58e9:	4c 8b 44 2e 08       	mov    0x8(%rsi,%rbp,1),%r8
    58ee:	bf 01 00 00 00       	mov    $0x1,%edi
    58f3:	48 8d 35 c6 0b 00 00 	lea    0xbc6(%rip),%rsi        # 64c0 <_IO_stdin_used+0x4c0>
    58fa:	48 8b 44 08 10       	mov    0x10(%rax,%rcx,1),%rax
    58ff:	48 8b 14 2a          	mov    (%rdx,%rbp,1),%rdx
    5903:	48 89 c1             	mov    %rax,%rcx
    5906:	31 c0                	xor    %eax,%eax
    5908:	e8 23 cb ff ff       	call   2430 <__printf_chk@plt>
    590d:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5912:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5917:	4c 8b 28             	mov    (%rax),%r13
    591a:	48 8b 04 24          	mov    (%rsp),%rax
    591e:	48 03 10             	add    (%rax),%rdx
    5921:	4d 01 fd             	add    %r15,%r13
    5924:	48 8b 42 60          	mov    0x60(%rdx),%rax
    5928:	48 39 d8             	cmp    %rbx,%rax
    592b:	0f 8f 48 ff ff ff    	jg     5879 <verify+0x159>
    5931:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    5936:	49 8b 45 60          	mov    0x60(%r13),%rax
    593a:	49 83 c6 01          	add    $0x1,%r14
    593e:	4c 39 f0             	cmp    %r14,%rax
    5941:	0f 8f e1 fe ff ff    	jg     5828 <verify+0x108>
    5947:	44 89 e3             	mov    %r12d,%ebx
    594a:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
    594f:	48 8b 04 24          	mov    (%rsp),%rax
    5953:	49 83 c4 01          	add    $0x1,%r12
    5957:	44 39 60 08          	cmp    %r12d,0x8(%rax)
    595b:	0f 8f 5f fe ff ff    	jg     57c0 <verify+0xa0>
    5961:	44 8b 74 24 3c       	mov    0x3c(%rsp),%r14d
    5966:	89 dd                	mov    %ebx,%ebp
    5968:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    596d:	83 44 24 2c 01       	addl   $0x1,0x2c(%rsp)
    5972:	49 81 c7 98 00 00 00 	add    $0x98,%r15
    5979:	8b 44 24 2c          	mov    0x2c(%rsp),%eax
    597d:	39 47 08             	cmp    %eax,0x8(%rdi)
    5980:	0f 8f f7 fd ff ff    	jg     577d <verify+0x5d>
    5986:	44 8b 64 24 38       	mov    0x38(%rsp),%r12d
    598b:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    5990:	48 81 04 24 98 00 00 00 	addq   $0x98,(%rsp)
    5998:	41 39 c6             	cmp    %eax,%r14d
    599b:	0f 84 84 00 00 00    	je     5a25 <verify+0x305>
    59a1:	41 89 c4             	mov    %eax,%r12d
    59a4:	e9 ab fd ff ff       	jmp    5754 <verify+0x34>
    59a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    59b0:	0f 85 b2 fe ff ff    	jne    5868 <verify+0x148>
    59b6:	e9 a0 fe ff ff       	jmp    585b <verify+0x13b>
    59bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    59c0:	49 39 c6             	cmp    %rax,%r14
    59c3:	7e 09                	jle    59ce <verify+0x2ae>
    59c5:	4d 39 d3             	cmp    %r10,%r11
    59c8:	0f 8c 02 ff ff ff    	jl     58d0 <verify+0x1b0>
    59ce:	4d 39 d3             	cmp    %r10,%r11
    59d1:	0f 8f 91 fe ff ff    	jg     5868 <verify+0x148>
    59d7:	49 39 c6             	cmp    %rax,%r14
    59da:	0f 8d f0 fe ff ff    	jge    58d0 <verify+0x1b0>
    59e0:	4d 39 c8             	cmp    %r9,%r8
    59e3:	0f 85 7f fe ff ff    	jne    5868 <verify+0x148>
    59e9:	48 39 fe             	cmp    %rdi,%rsi
    59ec:	0f 85 76 fe ff ff    	jne    5868 <verify+0x148>
    59f2:	4d 39 d3             	cmp    %r10,%r11
    59f5:	0f 84 d5 fe ff ff    	je     58d0 <verify+0x1b0>
    59fb:	e9 68 fe ff ff       	jmp    5868 <verify+0x148>
    5a00:	48 39 fe             	cmp    %rdi,%rsi
    5a03:	0f 8c 52 fe ff ff    	jl     585b <verify+0x13b>
    5a09:	4d 39 d3             	cmp    %r10,%r11
    5a0c:	7e c9                	jle    59d7 <verify+0x2b7>
    5a0e:	48 39 fe             	cmp    %rdi,%rsi
    5a11:	0f 85 51 fe ff ff    	jne    5868 <verify+0x148>
    5a17:	49 39 c6             	cmp    %rax,%r14
    5a1a:	0f 8f 48 fe ff ff    	jg     5868 <verify+0x148>
    5a20:	e9 ab fe ff ff       	jmp    58d0 <verify+0x1b0>
    5a25:	48 81 44 24 08 98 00 00 00 	addq   $0x98,0x8(%rsp)
    5a2e:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    5a33:	8d 45 01             	lea    0x1(%rbp),%eax
    5a36:	44 39 e5             	cmp    %r12d,%ebp
    5a39:	74 07                	je     5a42 <verify+0x322>
    5a3b:	89 c5                	mov    %eax,%ebp
    5a3d:	e9 06 fd ff ff       	jmp    5748 <verify+0x28>
    5a42:	48 83 c4 48          	add    $0x48,%rsp
    5a46:	31 c0                	xor    %eax,%eax
    5a48:	5b                   	pop    %rbx
    5a49:	5d                   	pop    %rbp
    5a4a:	41 5c                	pop    %r12
    5a4c:	41 5d                	pop    %r13
    5a4e:	41 5e                	pop    %r14
    5a50:	41 5f                	pop    %r15
    5a52:	c3                   	ret
    5a53:	31 c0                	xor    %eax,%eax
    5a55:	c3                   	ret
    5a56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005a60 <min>:
    5a60:	f3 0f 1e fa          	endbr64
    5a64:	39 f7                	cmp    %esi,%edi
    5a66:	89 f0                	mov    %esi,%eax
    5a68:	0f 4e c7             	cmovle %edi,%eax
    5a6b:	c3                   	ret

Disassembly of section .fini:

0000000000005a6c <_fini>:
    5a6c:	f3 0f 1e fa          	endbr64
    5a70:	48 83 ec 08          	sub    $0x8,%rsp
    5a74:	48 83 c4 08          	add    $0x8,%rsp
    5a78:	c3                   	ret
