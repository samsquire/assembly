
barrier-runtime-server-elapsed:     file format elf64-x86-64


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
    26d4:	ba 0a 00 00 00       	mov    $0xa,%edx
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
    2711:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2716:	e8 65 fc ff ff       	call   2380 <calloc@plt>
    271b:	be 10 00 00 00       	mov    $0x10,%esi
    2720:	bf 01 00 00 00       	mov    $0x1,%edi
    2725:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    272a:	e8 51 fc ff ff       	call   2380 <calloc@plt>
    272f:	be 10 00 00 00       	mov    $0x10,%esi
    2734:	bf 01 00 00 00       	mov    $0x1,%edi
    2739:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    273f:	48 89 c3             	mov    %rax,%rbx
    2742:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2747:	e8 34 fc ff ff       	call   2380 <calloc@plt>
    274c:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    2751:	c7 44 24 34 00 00 00 00 	movl   $0x0,0x34(%rsp)
    2759:	31 d2                	xor    %edx,%edx
    275b:	48 89 43 08          	mov    %rax,0x8(%rbx)
    275f:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    2766:	4d 89 c7             	mov    %r8,%r15
    2769:	4c 89 44 24 48       	mov    %r8,0x48(%rsp)
    276e:	66 90                	xchg   %ax,%ax
    2770:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    2775:	41 89 17             	mov    %edx,(%r15)
    2778:	be 10 00 00 00       	mov    $0x10,%esi
    277d:	31 db                	xor    %ebx,%ebx
    277f:	41 c7 47 28 07 00 00 00 	movl   $0x7,0x28(%r15)
    2787:	bf 64 00 00 00       	mov    $0x64,%edi
    278c:	49 89 47 10          	mov    %rax,0x10(%r15)
    2790:	48 8b 05 59 42 00 00 	mov    0x4259(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    2797:	89 54 24 08          	mov    %edx,0x8(%rsp)
    279b:	49 89 47 18          	mov    %rax,0x18(%r15)
    279f:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    27a4:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    27a9:	49 89 47 30          	mov    %rax,0x30(%r15)
    27ad:	e8 ce fb ff ff       	call   2380 <calloc@plt>
    27b2:	be 10 00 00 00       	mov    $0x10,%esi
    27b7:	bf 64 00 00 00       	mov    $0x64,%edi
    27bc:	49 89 47 50          	mov    %rax,0x50(%r15)
    27c0:	e8 bb fb ff ff       	call   2380 <calloc@plt>
    27c5:	be 00 01 00 00       	mov    $0x100,%esi
    27ca:	bf 64 00 00 00       	mov    $0x64,%edi
    27cf:	66 0f 6f 15 f9 41 00 00 	movdqa 0x41f9(%rip),%xmm2        # 69d0 <_IO_stdin_used+0x9d0>
    27d7:	49 89 47 58          	mov    %rax,0x58(%r15)
    27db:	41 0f 11 57 68       	movups %xmm2,0x68(%r15)
    27e0:	e8 9b fb ff ff       	call   2380 <calloc@plt>
    27e5:	be 80 02 00 00       	mov    $0x280,%esi
    27ea:	bf 07 00 00 00       	mov    $0x7,%edi
    27ef:	66 0f 6f 1d d9 41 00 00 	movdqa 0x41d9(%rip),%xmm3        # 69d0 <_IO_stdin_used+0x9d0>
    27f7:	49 89 47 78          	mov    %rax,0x78(%r15)
    27fb:	41 0f 11 9f 80 00 00 00 	movups %xmm3,0x80(%r15)
    2803:	e8 78 fb ff ff       	call   2380 <calloc@plt>
    2808:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    280d:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    2812:	49 89 47 20          	mov    %rax,0x20(%r15)
    2816:	49 89 c7             	mov    %rax,%r15
    2819:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    2820:	4c 63 eb             	movslq %ebx,%r13
    2823:	44 89 74 24 28       	mov    %r14d,0x28(%rsp)
    2828:	4f 8d 64 ad 00       	lea    0x0(%r13,%r13,4),%r12
    282d:	49 c1 e4 07          	shl    $0x7,%r12
    2831:	44 39 f3             	cmp    %r14d,%ebx
    2834:	0f 84 0e 0a 00 00    	je     3248 <main+0xc78>
    283a:	be 00 02 00 00       	mov    $0x200,%esi
    283f:	bf 06 00 00 00       	mov    $0x6,%edi
    2844:	e8 37 fb ff ff       	call   2380 <calloc@plt>
    2849:	89 5c 24 18          	mov    %ebx,0x18(%rsp)
    284d:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    2852:	48 8d a8 00 0c 00 00 	lea    0xc00(%rax),%rbp
    2859:	4b 89 84 27 58 02 00 00 	mov    %rax,0x258(%r15,%r12,1)
    2861:	49 89 c7             	mov    %rax,%r15
    2864:	0f 1f 40 00          	nopl   0x0(%rax)
    2868:	be 08 00 00 00       	mov    $0x8,%esi
    286d:	bf 01 00 00 00       	mov    $0x1,%edi
    2872:	49 81 c7 00 02 00 00 	add    $0x200,%r15
    2879:	e8 02 fb ff ff       	call   2380 <calloc@plt>
    287e:	be 08 00 00 00       	mov    $0x8,%esi
    2883:	bf 01 00 00 00       	mov    $0x1,%edi
    2888:	49 89 c4             	mov    %rax,%r12
    288b:	e8 f0 fa ff ff       	call   2380 <calloc@plt>
    2890:	be 18 00 00 00       	mov    $0x18,%esi
    2895:	bf 02 00 00 00       	mov    $0x2,%edi
    289a:	48 89 c3             	mov    %rax,%rbx
    289d:	e8 de fa ff ff       	call   2380 <calloc@plt>
    28a2:	66 0f 6f 05 36 41 00 00 	movdqa 0x4136(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
    28aa:	48 8d 70 18          	lea    0x18(%rax),%rsi
    28ae:	49 89 87 00 fe ff ff 	mov    %rax,-0x200(%r15)
    28b5:	49 89 b7 80 fe ff ff 	mov    %rsi,-0x180(%r15)
    28bc:	4c 89 20             	mov    %r12,(%rax)
    28bf:	48 89 58 18          	mov    %rbx,0x18(%rax)
    28c3:	0f 11 40 08          	movups %xmm0,0x8(%rax)
    28c7:	0f 11 40 20          	movups %xmm0,0x20(%rax)
    28cb:	4c 39 fd             	cmp    %r15,%rbp
    28ce:	75 98                	jne    2868 <main+0x298>
    28d0:	be 01 00 00 00       	mov    $0x1,%esi
    28d5:	bf 00 01 00 00       	mov    $0x100,%edi
    28da:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
    28de:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
    28e3:	e8 98 fa ff ff       	call   2380 <calloc@plt>
    28e8:	bf 18 00 00 00       	mov    $0x18,%edi
    28ed:	48 89 c5             	mov    %rax,%rbp
    28f0:	e8 fb fa ff ff       	call   23f0 <malloc@plt>
    28f5:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    28fa:	48 89 ef             	mov    %rbp,%rdi
    28fd:	41 89 d9             	mov    %ebx,%r9d
    2900:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2905:	48 8d 0d 74 3c 00 00 	lea    0x3c74(%rip),%rcx        # 6580 <_IO_stdin_used+0x580>
    290c:	ba 00 01 00 00       	mov    $0x100,%edx
    2911:	31 c0                	xor    %eax,%eax
    2913:	be 01 00 00 00       	mov    $0x1,%esi
    2918:	e8 e3 fb ff ff       	call   2500 <__sprintf_chk@plt>
    291d:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    2922:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    2927:	ba ab aa aa aa       	mov    $0xaaaaaaab,%edx
    292c:	be 20 00 00 00       	mov    $0x20,%esi
    2931:	bf 3f 42 0f 00       	mov    $0xf423f,%edi
    2936:	4d 89 6a 10          	mov    %r13,0x10(%r10)
    293a:	44 8d 6b 01          	lea    0x1(%rbx),%r13d
    293e:	4c 8b 78 20          	mov    0x20(%rax),%r15
    2942:	44 89 e8             	mov    %r13d,%eax
    2945:	44 89 e9             	mov    %r13d,%ecx
    2948:	49 89 2a             	mov    %rbp,(%r10)
    294b:	48 0f af c2          	imul   %rdx,%rax
    294f:	4b 8d 2c 27          	lea    (%r15,%r12,1),%rbp
    2953:	4d 89 72 08          	mov    %r14,0x8(%r10)
    2957:	4c 89 95 70 02 00 00 	mov    %r10,0x270(%rbp)
    295e:	48 c7 85 40 02 00 00 3f 42 0f 00 	movq   $0xf423f,0x240(%rbp)
    2969:	48 c1 e8 22          	shr    $0x22,%rax
    296d:	8d 04 40             	lea    (%rax,%rax,2),%eax
    2970:	01 c0                	add    %eax,%eax
    2972:	29 c1                	sub    %eax,%ecx
    2974:	89 8d 78 02 00 00    	mov    %ecx,0x278(%rbp)
    297a:	e8 01 fa ff ff       	call   2380 <calloc@plt>
    297f:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2983:	89 5d 00             	mov    %ebx,0x0(%rbp)
    2986:	48 89 85 38 02 00 00 	mov    %rax,0x238(%rbp)
    298d:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    2992:	48 c7 85 48 02 00 00 00 00 00 00 	movq   $0x0,0x248(%rbp)
    299d:	48 89 85 18 02 00 00 	mov    %rax,0x218(%rbp)
    29a4:	48 b8 01 00 00 00 07 00 00 00 	movabs $0x700000001,%rax
    29ae:	48 89 85 28 02 00 00 	mov    %rax,0x228(%rbp)
    29b5:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
    29bf:	89 8d 20 02 00 00    	mov    %ecx,0x220(%rbp)
    29c5:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
    29cf:	c7 85 24 02 00 00 06 00 00 00 	movl   $0x6,0x224(%rbp)
    29d9:	48 89 85 68 02 00 00 	mov    %rax,0x268(%rbp)
    29e0:	83 fb 05             	cmp    $0x5,%ebx
    29e3:	0f 84 3f 08 00 00    	je     3228 <main+0xc58>
    29e9:	8b 44 24 28          	mov    0x28(%rsp),%eax
    29ed:	39 c3                	cmp    %eax,%ebx
    29ef:	75 67                	jne    2a58 <main+0x488>
    29f1:	8b 5c 24 34          	mov    0x34(%rsp),%ebx
    29f5:	85 db                	test   %ebx,%ebx
    29f7:	7f 5f                	jg     2a58 <main+0x488>
    29f9:	89 ca                	mov    %ecx,%edx
    29fb:	48 8d 35 a6 3b 00 00 	lea    0x3ba6(%rip),%rsi        # 65a8 <_IO_stdin_used+0x5a8>
    2a02:	bf 01 00 00 00       	mov    $0x1,%edi
    2a07:	31 c0                	xor    %eax,%eax
    2a09:	e8 22 fa ff ff       	call   2430 <__printf_chk@plt>
    2a0e:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    2a13:	48 63 c3             	movslq %ebx,%rax
    2a16:	48 89 c1             	mov    %rax,%rcx
    2a19:	48 c1 e0 04          	shl    $0x4,%rax
    2a1d:	48 01 d0             	add    %rdx,%rax
    2a20:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    2a25:	4c 8b 7a 20          	mov    0x20(%rdx),%r15
    2a29:	48 89 42 38          	mov    %rax,0x38(%rdx)
    2a2d:	48 8d 05 dc 2b 00 00 	lea    0x2bdc(%rip),%rax        # 5610 <barriered_work_ingest>
    2a34:	4b 89 84 27 08 02 00 00 	mov    %rax,0x208(%r15,%r12,1)
    2a3c:	8d 41 01             	lea    0x1(%rcx),%eax
    2a3f:	89 44 24 34          	mov    %eax,0x34(%rsp)
    2a43:	41 83 fd 07          	cmp    $0x7,%r13d
    2a47:	74 23                	je     2a6c <main+0x49c>
    2a49:	44 89 eb             	mov    %r13d,%ebx
    2a4c:	e9 cf fd ff ff       	jmp    2820 <main+0x250>
    2a51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    2a58:	48 8d 05 11 28 00 00 	lea    0x2811(%rip),%rax        # 5270 <barriered_work>
    2a5f:	48 89 85 08 02 00 00 	mov    %rax,0x208(%rbp)
    2a66:	41 83 fd 07          	cmp    $0x7,%r13d
    2a6a:	75 dd                	jne    2a49 <main+0x479>
    2a6c:	4c 89 f2             	mov    %r14,%rdx
    2a6f:	48 8d 05 2a 09 00 00 	lea    0x92a(%rip),%rax        # 33a0 <barriered_reset>
    2a76:	4d 89 fe             	mov    %r15,%r14
    2a79:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    2a7e:	49 89 86 08 11 00 00 	mov    %rax,0x1108(%r14)
    2a85:	8b 44 24 08          	mov    0x8(%rsp),%eax
    2a89:	48 83 c2 01          	add    $0x1,%rdx
    2a8d:	4d 89 be 18 11 00 00 	mov    %r15,0x1118(%r14)
    2a94:	49 81 c7 98 00 00 00 	add    $0x98,%r15
    2a9b:	41 89 86 20 11 00 00 	mov    %eax,0x1120(%r14)
    2aa2:	48 b8 01 00 00 00 07 00 00 00 	movabs $0x700000001,%rax
    2aac:	41 c7 86 80 0f 00 00 00 00 00 00 	movl   $0x0,0xf80(%r14)
    2ab7:	41 c7 86 00 0f 00 00 06 00 00 00 	movl   $0x6,0xf00(%r14)
    2ac2:	41 c7 86 6c 11 00 00 06 00 00 00 	movl   $0x6,0x116c(%r14)
    2acd:	41 c7 86 24 11 00 00 06 00 00 00 	movl   $0x6,0x1124(%r14)
    2ad8:	49 89 86 28 11 00 00 	mov    %rax,0x1128(%r14)
    2adf:	48 83 fa 09          	cmp    $0x9,%rdx
    2ae3:	0f 85 87 fc ff ff    	jne    2770 <main+0x1a0>
    2ae9:	4c 8b 44 24 48       	mov    0x48(%rsp),%r8
    2aee:	be 38 00 00 00       	mov    $0x38,%esi
    2af3:	bf 09 00 00 00       	mov    $0x9,%edi
    2af8:	45 31 ed             	xor    %r13d,%r13d
    2afb:	4c 8d 3d 2e 09 00 00 	lea    0x92e(%rip),%r15        # 3430 <barriered_thread>
    2b02:	49 8b 40 20          	mov    0x20(%r8),%rax
    2b06:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    2b0b:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    2b12:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    2b1d:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    2b28:	41 c7 80 50 04 00 00 07 00 00 00 	movl   $0x7,0x450(%r8)
    2b33:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2b3d:	49 8b 80 b8 00 00 00 	mov    0xb8(%r8),%rax
    2b44:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2b4e:	49 8b 80 50 01 00 00 	mov    0x150(%r8),%rax
    2b55:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2b5f:	49 8b 80 e8 01 00 00 	mov    0x1e8(%r8),%rax
    2b66:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2b70:	49 8b 80 80 02 00 00 	mov    0x280(%r8),%rax
    2b77:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2b81:	49 8b 80 18 03 00 00 	mov    0x318(%r8),%rax
    2b88:	c7 80 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rax)
    2b92:	e8 e9 f7 ff ff       	call   2380 <calloc@plt>
    2b97:	be 38 00 00 00       	mov    $0x38,%esi
    2b9c:	bf 09 00 00 00       	mov    $0x9,%edi
    2ba1:	48 89 c3             	mov    %rax,%rbx
    2ba4:	e8 d7 f7 ff ff       	call   2380 <calloc@plt>
    2ba9:	be 38 00 00 00       	mov    $0x38,%esi
    2bae:	bf 09 00 00 00       	mov    $0x9,%edi
    2bb3:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2bb8:	e8 c3 f7 ff ff       	call   2380 <calloc@plt>
    2bbd:	be 08 00 00 00       	mov    $0x8,%esi
    2bc2:	bf 09 00 00 00       	mov    $0x9,%edi
    2bc7:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2bcc:	e8 af f7 ff ff       	call   2380 <calloc@plt>
    2bd1:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2bd6:	ba 06 00 00 00       	mov    $0x6,%edx
    2bdb:	48 8d 35 0d 37 00 00 	lea    0x370d(%rip),%rsi        # 62ef <_IO_stdin_used+0x2ef>
    2be2:	49 89 c4             	mov    %rax,%r12
    2be5:	48 8b 05 0c 3e 00 00 	mov    0x3e0c(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
    2bec:	bf 01 00 00 00       	mov    $0x1,%edi
    2bf1:	4d 89 80 a0 03 00 00 	mov    %r8,0x3a0(%r8)
    2bf8:	4c 89 e5             	mov    %r12,%rbp
    2bfb:	49 89 80 b8 03 00 00 	mov    %rax,0x3b8(%r8)
    2c02:	31 c0                	xor    %eax,%eax
    2c04:	41 c7 80 a8 03 00 00 06 00 00 00 	movl   $0x6,0x3a8(%r8)
    2c0f:	49 c7 80 90 03 00 00 00 00 00 00 	movq   $0x0,0x390(%r8)
    2c1a:	e8 11 f8 ff ff       	call   2430 <__printf_chk@plt>
    2c1f:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2c24:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
    2c29:	45 89 ec             	mov    %r13d,%r12d
    2c2c:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2c33:	48 8d 15 76 0b 00 00 	lea    0xb76(%rip),%rdx        # 37b0 <timer_thread>
    2c3a:	49 89 ed             	mov    %rbp,%r13
    2c3d:	49 8d 88 90 03 00 00 	lea    0x390(%r8),%rcx
    2c44:	e8 07 f8 ff ff       	call   2450 <pthread_create@plt>
    2c49:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    2c4e:	66 90                	xchg   %ax,%ax
    2c50:	41 c7 46 04 01 00 00 00 	movl   $0x1,0x4(%r14)
    2c58:	44 89 e2             	mov    %r12d,%edx
    2c5b:	bf 01 00 00 00       	mov    $0x1,%edi
    2c60:	31 c0                	xor    %eax,%eax
    2c62:	41 c7 46 2c 01 00 00 00 	movl   $0x1,0x2c(%r14)
    2c6a:	48 8d 35 57 39 00 00 	lea    0x3957(%rip),%rsi        # 65c8 <_IO_stdin_used+0x5c8>
    2c71:	41 83 c4 01          	add    $0x1,%r12d
    2c75:	e8 b6 f7 ff ff       	call   2430 <__printf_chk@plt>
    2c7a:	4c 89 f1             	mov    %r14,%rcx
    2c7d:	48 89 de             	mov    %rbx,%rsi
    2c80:	48 89 ef             	mov    %rbp,%rdi
    2c83:	4c 89 fa             	mov    %r15,%rdx
    2c86:	49 81 c6 98 00 00 00 	add    $0x98,%r14
    2c8d:	48 83 c5 08          	add    $0x8,%rbp
    2c91:	48 83 c3 38          	add    $0x38,%rbx
    2c95:	e8 b6 f7 ff ff       	call   2450 <pthread_create@plt>
    2c9a:	41 83 fc 06          	cmp    $0x6,%r12d
    2c9e:	75 b0                	jne    2c50 <main+0x680>
    2ca0:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2ca5:	48 8b 1d 54 3d 00 00 	mov    0x3d54(%rip),%rbx        # 6a00 <_IO_stdin_used+0xa00>
    2cac:	be d8 00 00 00       	mov    $0xd8,%esi
    2cb1:	4d 89 ec             	mov    %r13,%r12
    2cb4:	bf 01 00 00 00       	mov    $0x1,%edi
    2cb9:	48 8d 2d 9f 36 00 00 	lea    0x369f(%rip),%rbp        # 635f <_IO_stdin_used+0x35f>
    2cc0:	49 89 98 50 04 00 00 	mov    %rbx,0x450(%r8)
    2cc7:	41 c7 80 2c 04 00 00 02 00 00 00 	movl   $0x2,0x42c(%r8)
    2cd2:	e8 a9 f6 ff ff       	call   2380 <calloc@plt>
    2cd7:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2cdc:	be 00 08 00 00       	mov    $0x800,%esi
    2ce1:	31 ff                	xor    %edi,%edi
    2ce3:	49 89 80 68 04 00 00 	mov    %rax,0x468(%r8)
    2cea:	e8 a1 f7 ff ff       	call   2490 <eventfd@plt>
    2cef:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2cf4:	ba 07 00 00 00       	mov    $0x7,%edx
    2cf9:	48 8d 35 0d 36 00 00 	lea    0x360d(%rip),%rsi        # 630d <_IO_stdin_used+0x30d>
    2d00:	bf 01 00 00 00       	mov    $0x1,%edi
    2d05:	41 89 80 70 04 00 00 	mov    %eax,0x470(%r8)
    2d0c:	31 c0                	xor    %eax,%eax
    2d0e:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    2d15:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    2d20:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    2d2b:	e8 00 f7 ff ff       	call   2430 <__printf_chk@plt>
    2d30:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2d35:	49 8d 7d 38          	lea    0x38(%r13),%rdi
    2d39:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2d3e:	48 8d 15 3b 1d 00 00 	lea    0x1d3b(%rip),%rdx        # 4a80 <io_thread>
    2d45:	49 8d 88 28 04 00 00 	lea    0x428(%r8),%rcx
    2d4c:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2d53:	e8 f8 f6 ff ff       	call   2450 <pthread_create@plt>
    2d58:	ba 08 00 00 00       	mov    $0x8,%edx
    2d5d:	48 8d 35 c0 35 00 00 	lea    0x35c0(%rip),%rsi        # 6324 <_IO_stdin_used+0x324>
    2d64:	31 c0                	xor    %eax,%eax
    2d66:	bf 01 00 00 00       	mov    $0x1,%edi
    2d6b:	e8 c0 f6 ff ff       	call   2430 <__printf_chk@plt>
    2d70:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2d75:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2d7a:	49 8d 7d 40          	lea    0x40(%r13),%rdi
    2d7e:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    2d83:	48 8d 15 66 09 00 00 	lea    0x966(%rip),%rdx        # 36f0 <external_thread>
    2d8a:	4c 8d 6c 24 50       	lea    0x50(%rsp),%r13
    2d8f:	49 89 80 f8 04 00 00 	mov    %rax,0x4f8(%r8)
    2d96:	48 8b 05 53 3c 00 00 	mov    0x3c53(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    2d9d:	49 8d 88 c0 04 00 00 	lea    0x4c0(%r8),%rcx
    2da4:	49 89 98 e8 04 00 00 	mov    %rbx,0x4e8(%r8)
    2dab:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    2db2:	31 db                	xor    %ebx,%ebx
    2db4:	49 89 80 d8 04 00 00 	mov    %rax,0x4d8(%r8)
    2dbb:	48 8b 05 46 3c 00 00 	mov    0x3c46(%rip),%rax        # 6a08 <_IO_stdin_used+0xa08>
    2dc2:	4d 89 80 d0 04 00 00 	mov    %r8,0x4d0(%r8)
    2dc9:	49 89 80 c0 04 00 00 	mov    %rax,0x4c0(%r8)
    2dd0:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    2dd5:	e8 76 f6 ff ff       	call   2450 <pthread_create@plt>
    2dda:	48 8d 3d 60 35 00 00 	lea    0x3560(%rip),%rdi        # 6341 <_IO_stdin_used+0x341>
    2de1:	e8 ea f4 ff ff       	call   22d0 <puts@plt>
    2de6:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    2deb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2df0:	49 8b 3c dc          	mov    (%r12,%rbx,8),%rdi
    2df4:	4c 89 ee             	mov    %r13,%rsi
    2df7:	e8 d4 f6 ff ff       	call   24d0 <pthread_join@plt>
    2dfc:	89 da                	mov    %ebx,%edx
    2dfe:	48 89 ee             	mov    %rbp,%rsi
    2e01:	bf 01 00 00 00       	mov    $0x1,%edi
    2e06:	31 c0                	xor    %eax,%eax
    2e08:	48 83 c3 01          	add    $0x1,%rbx
    2e0c:	e8 1f f6 ff ff       	call   2430 <__printf_chk@plt>
    2e11:	48 83 fb 09          	cmp    $0x9,%rbx
    2e15:	75 d9                	jne    2df0 <main+0x820>
    2e17:	49 8d 86 b0 03 00 00 	lea    0x3b0(%r14),%rax
    2e1e:	31 ed                	xor    %ebp,%ebp
    2e20:	31 c9                	xor    %ecx,%ecx
    2e22:	45 31 c9             	xor    %r9d,%r9d
    2e25:	45 31 e4             	xor    %r12d,%r12d
    2e28:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2e2d:	45 31 db             	xor    %r11d,%r11d
    2e30:	4d 8d 6e 20          	lea    0x20(%r14),%r13
    2e34:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
    2e39:	31 db                	xor    %ebx,%ebx
    2e3b:	4d 89 de             	mov    %r11,%r14
    2e3e:	49 bf db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r15
    2e48:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2e4d:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    2e52:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    2e57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    2e60:	49 63 45 08          	movslq 0x8(%r13),%rax
    2e64:	85 c0                	test   %eax,%eax
    2e66:	0f 8e c7 00 00 00    	jle    2f33 <main+0x963>
    2e6c:	49 8b 4d 00          	mov    0x0(%r13),%rcx
    2e70:	48 8d 34 80          	lea    (%rax,%rax,4),%rsi
    2e74:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2e79:	48 c1 e6 07          	shl    $0x7,%rsi
    2e7d:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    2e82:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    2e87:	48 8d 91 80 01 00 00 	lea    0x180(%rcx),%rdx
    2e8e:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    2e93:	48 01 d6             	add    %rdx,%rsi
    2e96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    2ea0:	48 8b 82 d8 00 00 00 	mov    0xd8(%rdx),%rax
    2ea7:	48 03 0a             	add    (%rdx),%rcx
    2eaa:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
    2eb1:	4c 03 9a 00 fe ff ff 	add    -0x200(%rdx),%r11
    2eb8:	4c 03 b2 50 fe ff ff 	add    -0x1b0(%rdx),%r14
    2ebf:	48 03 a8 00 01 00 00 	add    0x100(%rax),%rbp
    2ec6:	48 03 98 80 01 00 00 	add    0x180(%rax),%rbx
    2ecd:	48 03 a8 00 03 00 00 	add    0x300(%rax),%rbp
    2ed4:	48 03 98 80 03 00 00 	add    0x380(%rax),%rbx
    2edb:	48 03 a8 00 05 00 00 	add    0x500(%rax),%rbp
    2ee2:	48 03 98 80 05 00 00 	add    0x580(%rax),%rbx
    2ee9:	48 03 a8 00 07 00 00 	add    0x700(%rax),%rbp
    2ef0:	48 03 98 80 07 00 00 	add    0x780(%rax),%rbx
    2ef7:	48 03 a8 00 09 00 00 	add    0x900(%rax),%rbp
    2efe:	48 03 98 80 09 00 00 	add    0x980(%rax),%rbx
    2f05:	4c 03 8a 60 fe ff ff 	add    -0x1a0(%rdx),%r9
    2f0c:	48 03 a8 00 0b 00 00 	add    0xb00(%rax),%rbp
    2f13:	48 03 98 80 0b 00 00 	add    0xb80(%rax),%rbx
    2f1a:	48 39 f2             	cmp    %rsi,%rdx
    2f1d:	75 81                	jne    2ea0 <main+0x8d0>
    2f1f:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    2f24:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    2f29:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    2f2e:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    2f33:	45 31 e4             	xor    %r12d,%r12d
    2f36:	49 83 7d 50 00       	cmpq   $0x0,0x50(%r13)
    2f3b:	7e 7a                	jle    2fb7 <main+0x9e7>
    2f3d:	4c 89 ed             	mov    %r13,%rbp
    2f40:	49 89 dd             	mov    %rbx,%r13
    2f43:	4c 89 e3             	mov    %r12,%rbx
    2f46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    2f50:	48 8b 7d 30          	mov    0x30(%rbp),%rdi
    2f54:	48 89 de             	mov    %rbx,%rsi
    2f57:	48 83 c3 01          	add    $0x1,%rbx
    2f5b:	48 c1 e6 04          	shl    $0x4,%rsi
    2f5f:	48 01 f7             	add    %rsi,%rdi
    2f62:	48 03 75 38          	add    0x38(%rbp),%rsi
    2f66:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    2f6a:	48 2b 57 08          	sub    0x8(%rdi),%rdx
    2f6e:	48 89 d0             	mov    %rdx,%rax
    2f71:	49 f7 e7             	mul    %r15
    2f74:	31 c0                	xor    %eax,%eax
    2f76:	48 89 d1             	mov    %rdx,%rcx
    2f79:	48 8b 16             	mov    (%rsi),%rdx
    2f7c:	48 8d 35 f0 33 00 00 	lea    0x33f0(%rip),%rsi        # 6373 <_IO_stdin_used+0x373>
    2f83:	48 2b 17             	sub    (%rdi),%rdx
    2f86:	48 c1 e9 12          	shr    $0x12,%rcx
    2f8a:	bf 01 00 00 00       	mov    $0x1,%edi
    2f8f:	e8 9c f4 ff ff       	call   2430 <__printf_chk@plt>
    2f94:	48 8b 55 40          	mov    0x40(%rbp),%rdx
    2f98:	bf 01 00 00 00       	mov    $0x1,%edi
    2f9d:	31 c0                	xor    %eax,%eax
    2f9f:	48 8d 35 eb 33 00 00 	lea    0x33eb(%rip),%rsi        # 6391 <_IO_stdin_used+0x391>
    2fa6:	e8 85 f4 ff ff       	call   2430 <__printf_chk@plt>
    2fab:	48 39 5d 50          	cmp    %rbx,0x50(%rbp)
    2faf:	7f 9f                	jg     2f50 <main+0x980>
    2fb1:	4c 89 eb             	mov    %r13,%rbx
    2fb4:	49 89 ed             	mov    %rbp,%r13
    2fb7:	45 31 e4             	xor    %r12d,%r12d
    2fba:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    2fbf:	0f 8e 96 00 00 00    	jle    305b <main+0xa8b>
    2fc5:	4c 89 ed             	mov    %r13,%rbp
    2fc8:	49 89 dd             	mov    %rbx,%r13
    2fcb:	4c 89 e3             	mov    %r12,%rbx
    2fce:	66 90                	xchg   %ax,%ax
    2fd0:	48 89 d9             	mov    %rbx,%rcx
    2fd3:	48 83 ec 08          	sub    $0x8,%rsp
    2fd7:	48 8d 35 12 36 00 00 	lea    0x3612(%rip),%rsi        # 65f0 <_IO_stdin_used+0x5f0>
    2fde:	bf 01 00 00 00       	mov    $0x1,%edi
    2fe3:	48 c1 e1 08          	shl    $0x8,%rcx
    2fe7:	48 03 4d 58          	add    0x58(%rbp),%rcx
    2feb:	48 83 c3 01          	add    $0x1,%rbx
    2fef:	4c 8b a1 88 00 00 00 	mov    0x88(%rcx),%r12
    2ff6:	4c 2b 61 08          	sub    0x8(%rcx),%r12
    2ffa:	4c 89 e0             	mov    %r12,%rax
    2ffd:	4c 8b 81 80 00 00 00 	mov    0x80(%rcx),%r8
    3004:	4c 2b 01             	sub    (%rcx),%r8
    3007:	49 f7 e7             	mul    %r15
    300a:	8b 89 90 00 00 00    	mov    0x90(%rcx),%ecx
    3010:	41 54                	push   %r12
    3012:	31 c0                	xor    %eax,%eax
    3014:	48 c1 ea 12          	shr    $0x12,%rdx
    3018:	49 89 d1             	mov    %rdx,%r9
    301b:	ba 06 00 00 00       	mov    $0x6,%edx
    3020:	e8 0b f4 ff ff       	call   2430 <__printf_chk@plt>
    3025:	48 8d 35 81 33 00 00 	lea    0x3381(%rip),%rsi        # 63ad <_IO_stdin_used+0x3ad>
    302c:	bf 01 00 00 00       	mov    $0x1,%edi
    3031:	48 b8 ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%rax
    303b:	49 f7 e4             	mul    %r12
    303e:	31 c0                	xor    %eax,%eax
    3040:	48 c1 ea 02          	shr    $0x2,%rdx
    3044:	e8 e7 f3 ff ff       	call   2430 <__printf_chk@plt>
    3049:	58                   	pop    %rax
    304a:	5a                   	pop    %rdx
    304b:	48 39 5d 68          	cmp    %rbx,0x68(%rbp)
    304f:	0f 8f 7b ff ff ff    	jg     2fd0 <main+0xa00>
    3055:	4c 89 eb             	mov    %r13,%rbx
    3058:	49 89 ed             	mov    %rbp,%r13
    305b:	49 8b 55 70          	mov    0x70(%r13),%rdx
    305f:	48 8d 35 3b 33 00 00 	lea    0x333b(%rip),%rsi        # 63a1 <_IO_stdin_used+0x3a1>
    3066:	bf 01 00 00 00       	mov    $0x1,%edi
    306b:	31 c0                	xor    %eax,%eax
    306d:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    3074:	e8 b7 f3 ff ff       	call   2430 <__printf_chk@plt>
    3079:	4c 39 6c 24 28       	cmp    %r13,0x28(%rsp)
    307e:	0f 85 dc fd ff ff    	jne    2e60 <main+0x890>
    3084:	4c 8b 64 24 08       	mov    0x8(%rsp),%r12
    3089:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    308e:	48 8d 35 2a 33 00 00 	lea    0x332a(%rip),%rsi        # 63bf <_IO_stdin_used+0x3bf>
    3095:	31 c0                	xor    %eax,%eax
    3097:	bf 01 00 00 00       	mov    $0x1,%edi
    309c:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    30a1:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
    30a6:	49 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r13
    30b0:	4c 89 e2             	mov    %r12,%rdx
    30b3:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    30b8:	e8 73 f3 ff ff       	call   2430 <__printf_chk@plt>
    30bd:	bf 0a 00 00 00       	mov    $0xa,%edi
    30c2:	e8 f9 f1 ff ff       	call   22c0 <putchar@plt>
    30c7:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
    30cc:	48 8d 35 00 33 00 00 	lea    0x3300(%rip),%rsi        # 63d3 <_IO_stdin_used+0x3d3>
    30d3:	31 c0                	xor    %eax,%eax
    30d5:	bf 01 00 00 00       	mov    $0x1,%edi
    30da:	49 8b 16             	mov    (%r14),%rdx
    30dd:	e8 4e f3 ff ff       	call   2430 <__printf_chk@plt>
    30e2:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    30e7:	48 8d 35 fa 32 00 00 	lea    0x32fa(%rip),%rsi        # 63e8 <_IO_stdin_used+0x3e8>
    30ee:	31 c0                	xor    %eax,%eax
    30f0:	bf 01 00 00 00       	mov    $0x1,%edi
    30f5:	e8 36 f3 ff ff       	call   2430 <__printf_chk@plt>
    30fa:	bf 0a 00 00 00       	mov    $0xa,%edi
    30ff:	e8 bc f1 ff ff       	call   22c0 <putchar@plt>
    3104:	49 8b 36             	mov    (%r14),%rsi
    3107:	bf 01 00 00 00       	mov    $0x1,%edi
    310c:	48 89 f0             	mov    %rsi,%rax
    310f:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3113:	49 f7 ed             	imul   %r13
    3116:	31 c0                	xor    %eax,%eax
    3118:	48 c1 fa 02          	sar    $0x2,%rdx
    311c:	48 29 f2             	sub    %rsi,%rdx
    311f:	48 8d 35 02 35 00 00 	lea    0x3502(%rip),%rsi        # 6628 <_IO_stdin_used+0x628>
    3126:	e8 05 f3 ff ff       	call   2430 <__printf_chk@plt>
    312b:	49 8b 56 08          	mov    0x8(%r14),%rdx
    312f:	bf 01 00 00 00       	mov    $0x1,%edi
    3134:	31 c0                	xor    %eax,%eax
    3136:	48 8d 35 0b 35 00 00 	lea    0x350b(%rip),%rsi        # 6648 <_IO_stdin_used+0x648>
    313d:	e8 ee f2 ff ff       	call   2430 <__printf_chk@plt>
    3142:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    3147:	bf 01 00 00 00       	mov    $0x1,%edi
    314c:	48 8d 35 1d 35 00 00 	lea    0x351d(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    3153:	4c 89 d8             	mov    %r11,%rax
    3156:	49 c1 fb 3f          	sar    $0x3f,%r11
    315a:	49 f7 ed             	imul   %r13
    315d:	31 c0                	xor    %eax,%eax
    315f:	48 c1 fa 02          	sar    $0x2,%rdx
    3163:	4c 29 da             	sub    %r11,%rdx
    3166:	e8 c5 f2 ff ff       	call   2430 <__printf_chk@plt>
    316b:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3170:	bf 01 00 00 00       	mov    $0x1,%edi
    3175:	48 8d 35 24 35 00 00 	lea    0x3524(%rip),%rsi        # 66a0 <_IO_stdin_used+0x6a0>
    317c:	48 89 c8             	mov    %rcx,%rax
    317f:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3183:	49 f7 ed             	imul   %r13
    3186:	31 c0                	xor    %eax,%eax
    3188:	48 c1 fa 02          	sar    $0x2,%rdx
    318c:	48 29 ca             	sub    %rcx,%rdx
    318f:	e8 9c f2 ff ff       	call   2430 <__printf_chk@plt>
    3194:	4c 89 e0             	mov    %r12,%rax
    3197:	49 c1 fc 3f          	sar    $0x3f,%r12
    319b:	48 8d 35 2e 35 00 00 	lea    0x352e(%rip),%rsi        # 66d0 <_IO_stdin_used+0x6d0>
    31a2:	49 f7 ed             	imul   %r13
    31a5:	bf 01 00 00 00       	mov    $0x1,%edi
    31aa:	48 c1 fa 02          	sar    $0x2,%rdx
    31ae:	4c 29 e2             	sub    %r12,%rdx
    31b1:	31 c0                	xor    %eax,%eax
    31b3:	e8 78 f2 ff ff       	call   2430 <__printf_chk@plt>
    31b8:	48 89 e8             	mov    %rbp,%rax
    31bb:	48 c1 fd 3f          	sar    $0x3f,%rbp
    31bf:	48 8d 35 2f 32 00 00 	lea    0x322f(%rip),%rsi        # 63f5 <_IO_stdin_used+0x3f5>
    31c6:	49 f7 ed             	imul   %r13
    31c9:	bf 01 00 00 00       	mov    $0x1,%edi
    31ce:	31 c0                	xor    %eax,%eax
    31d0:	48 c1 fa 02          	sar    $0x2,%rdx
    31d4:	48 29 ea             	sub    %rbp,%rdx
    31d7:	e8 54 f2 ff ff       	call   2430 <__printf_chk@plt>
    31dc:	48 89 d8             	mov    %rbx,%rax
    31df:	48 c1 fb 3f          	sar    $0x3f,%rbx
    31e3:	48 8d 35 1c 32 00 00 	lea    0x321c(%rip),%rsi        # 6406 <_IO_stdin_used+0x406>
    31ea:	49 f7 ed             	imul   %r13
    31ed:	bf 01 00 00 00       	mov    $0x1,%edi
    31f2:	31 c0                	xor    %eax,%eax
    31f4:	48 c1 fa 02          	sar    $0x2,%rdx
    31f8:	48 29 da             	sub    %rbx,%rdx
    31fb:	e8 30 f2 ff ff       	call   2430 <__printf_chk@plt>
    3200:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    3205:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    320e:	75 4c                	jne    325c <main+0xc8c>
    3210:	48 83 c4 68          	add    $0x68,%rsp
    3214:	31 c0                	xor    %eax,%eax
    3216:	5b                   	pop    %rbx
    3217:	5d                   	pop    %rbp
    3218:	41 5c                	pop    %r12
    321a:	41 5d                	pop    %r13
    321c:	41 5e                	pop    %r14
    321e:	41 5f                	pop    %r15
    3220:	c3                   	ret
    3221:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3228:	48 8d 05 41 20 00 00 	lea    0x2041(%rip),%rax        # 5270 <barriered_work>
    322f:	41 bd 06 00 00 00    	mov    $0x6,%r13d
    3235:	48 89 85 08 02 00 00 	mov    %rax,0x208(%rbp)
    323c:	e9 08 f8 ff ff       	jmp    2a49 <main+0x479>
    3241:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3248:	48 8d 05 11 01 00 00 	lea    0x111(%rip),%rax        # 3360 <do_protected_write>
    324f:	4b 89 84 27 10 02 00 00 	mov    %rax,0x210(%r15,%r12,1)
    3257:	e9 de f5 ff ff       	jmp    283a <main+0x26a>
    325c:	e8 af f0 ff ff       	call   2310 <__stack_chk_fail@plt>
    3261:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    326b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003270 <_start>:
    3270:	f3 0f 1e fa          	endbr64
    3274:	31 ed                	xor    %ebp,%ebp
    3276:	49 89 d1             	mov    %rdx,%r9
    3279:	5e                   	pop    %rsi
    327a:	48 89 e2             	mov    %rsp,%rdx
    327d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3281:	50                   	push   %rax
    3282:	54                   	push   %rsp
    3283:	45 31 c0             	xor    %r8d,%r8d
    3286:	31 c9                	xor    %ecx,%ecx
    3288:	48 8d 3d 41 f3 ff ff 	lea    -0xcbf(%rip),%rdi        # 25d0 <main>
    328f:	ff 15 43 5d 00 00    	call   *0x5d43(%rip)        # 8fd8 <__libc_start_main@GLIBC_2.34>
    3295:	f4                   	hlt
    3296:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000032a0 <deregister_tm_clones>:
    32a0:	48 8d 3d 79 5d 00 00 	lea    0x5d79(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    32a7:	48 8d 05 72 5d 00 00 	lea    0x5d72(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    32ae:	48 39 f8             	cmp    %rdi,%rax
    32b1:	74 15                	je     32c8 <deregister_tm_clones+0x28>
    32b3:	48 8b 05 26 5d 00 00 	mov    0x5d26(%rip),%rax        # 8fe0 <_ITM_deregisterTMCloneTable@Base>
    32ba:	48 85 c0             	test   %rax,%rax
    32bd:	74 09                	je     32c8 <deregister_tm_clones+0x28>
    32bf:	ff e0                	jmp    *%rax
    32c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    32c8:	c3                   	ret
    32c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000032d0 <register_tm_clones>:
    32d0:	48 8d 3d 49 5d 00 00 	lea    0x5d49(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    32d7:	48 8d 35 42 5d 00 00 	lea    0x5d42(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    32de:	48 29 fe             	sub    %rdi,%rsi
    32e1:	48 89 f0             	mov    %rsi,%rax
    32e4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    32e8:	48 c1 f8 03          	sar    $0x3,%rax
    32ec:	48 01 c6             	add    %rax,%rsi
    32ef:	48 d1 fe             	sar    %rsi
    32f2:	74 14                	je     3308 <register_tm_clones+0x38>
    32f4:	48 8b 05 f5 5c 00 00 	mov    0x5cf5(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    32fb:	48 85 c0             	test   %rax,%rax
    32fe:	74 08                	je     3308 <register_tm_clones+0x38>
    3300:	ff e0                	jmp    *%rax
    3302:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3308:	c3                   	ret
    3309:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003310 <__do_global_dtors_aux>:
    3310:	f3 0f 1e fa          	endbr64
    3314:	80 3d 0d 5d 00 00 00 	cmpb   $0x0,0x5d0d(%rip)        # 9028 <completed.0>
    331b:	75 2b                	jne    3348 <__do_global_dtors_aux+0x38>
    331d:	55                   	push   %rbp
    331e:	48 83 3d d2 5c 00 00 00 	cmpq   $0x0,0x5cd2(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    3326:	48 89 e5             	mov    %rsp,%rbp
    3329:	74 0c                	je     3337 <__do_global_dtors_aux+0x27>
    332b:	48 8b 3d d6 5c 00 00 	mov    0x5cd6(%rip),%rdi        # 9008 <__dso_handle>
    3332:	e8 69 ef ff ff       	call   22a0 <__cxa_finalize@plt>
    3337:	e8 64 ff ff ff       	call   32a0 <deregister_tm_clones>
    333c:	c6 05 e5 5c 00 00 01 	movb   $0x1,0x5ce5(%rip)        # 9028 <completed.0>
    3343:	5d                   	pop    %rbp
    3344:	c3                   	ret
    3345:	0f 1f 00             	nopl   (%rax)
    3348:	c3                   	ret
    3349:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003350 <frame_dummy>:
    3350:	f3 0f 1e fa          	endbr64
    3354:	e9 77 ff ff ff       	jmp    32d0 <register_tm_clones>
    3359:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003360 <do_protected_write>:
    3360:	f3 0f 1e fa          	endbr64
    3364:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    336b:	48 8b 40 30          	mov    0x30(%rax),%rax
    336f:	48 83 87 00 02 00 00 01 	addq   $0x1,0x200(%rdi)
    3377:	48 8b 48 08          	mov    0x8(%rax),%rcx
    337b:	48 83 00 01          	addq   $0x1,(%rax)
    337f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3386:	48 85 c9             	test   %rcx,%rcx
    3389:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3390:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3394:	48 89 50 08          	mov    %rdx,0x8(%rax)
    3398:	31 c0                	xor    %eax,%eax
    339a:	c3                   	ret
    339b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000033a0 <barriered_reset>:
    33a0:	f3 0f 1e fa          	endbr64
    33a4:	48 63 8f 2c 02 00 00 	movslq 0x22c(%rdi),%rcx
    33ab:	85 c9                	test   %ecx,%ecx
    33ad:	7e 6c                	jle    341b <barriered_reset+0x7b>
    33af:	48 63 87 20 02 00 00 	movslq 0x220(%rdi),%rax
    33b6:	4c 8b 87 18 02 00 00 	mov    0x218(%rdi),%r8
    33bd:	48 8d 0c 89          	lea    (%rcx,%rcx,4),%rcx
    33c1:	48 c1 e1 07          	shl    $0x7,%rcx
    33c5:	48 8d 3c c0          	lea    (%rax,%rax,8),%rdi
    33c9:	49 8b 70 20          	mov    0x20(%r8),%rsi
    33cd:	48 8d 04 78          	lea    (%rax,%rdi,2),%rax
    33d1:	49 8b 78 10          	mov    0x10(%r8),%rdi
    33d5:	48 8d 96 28 02 00 00 	lea    0x228(%rsi),%rdx
    33dc:	48 8d 8c 0e 28 02 00 00 	lea    0x228(%rsi,%rcx,1),%rcx
    33e4:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    33e8:	48 8b 40 20          	mov    0x20(%rax),%rax
    33ec:	48 05 00 01 00 00    	add    $0x100,%rax
    33f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    33f8:	83 40 80 01          	addl   $0x1,-0x80(%rax)
    33fc:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
    3403:	83 00 01             	addl   $0x1,(%rax)
    3406:	48 05 80 02 00 00    	add    $0x280,%rax
    340c:	c7 82 80 fd ff ff 01 00 00 00 	movl   $0x1,-0x280(%rdx)
    3416:	48 39 ca             	cmp    %rcx,%rdx
    3419:	75 dd                	jne    33f8 <barriered_reset+0x58>
    341b:	0f ae f0             	mfence
    341e:	31 c0                	xor    %eax,%eax
    3420:	c3                   	ret
    3421:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    342c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003430 <barriered_thread>:
    3430:	f3 0f 1e fa          	endbr64
    3434:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
    3438:	0f 85 aa 02 00 00    	jne    36e8 <barriered_thread+0x2b8>
    343e:	41 56                	push   %r14
    3440:	41 55                	push   %r13
    3442:	45 31 ed             	xor    %r13d,%r13d
    3445:	41 54                	push   %r12
    3447:	49 89 fc             	mov    %rdi,%r12
    344a:	55                   	push   %rbp
    344b:	53                   	push   %rbx
    344c:	31 db                	xor    %ebx,%ebx
    344e:	66 90                	xchg   %ax,%ax
    3450:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    3455:	39 da                	cmp    %ebx,%edx
    3457:	7f 13                	jg     346c <barriered_thread+0x3c>
    3459:	49 83 84 24 90 00 00 00 01 	addq   $0x1,0x90(%r12)
    3462:	31 db                	xor    %ebx,%ebx
    3464:	85 d2                	test   %edx,%edx
    3466:	0f 8e 64 01 00 00    	jle    35d0 <barriered_thread+0x1a0>
    346c:	48 63 c3             	movslq %ebx,%rax
    346f:	48 8d 2c 80          	lea    (%rax,%rax,4),%rbp
    3473:	48 c1 e5 07          	shl    $0x7,%rbp
    3477:	eb 19                	jmp    3492 <barriered_thread+0x62>
    3479:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3480:	83 c3 01             	add    $0x1,%ebx
    3483:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    348a:	39 d3                	cmp    %edx,%ebx
    348c:	0f 8d 3e 01 00 00    	jge    35d0 <barriered_thread+0x1a0>
    3492:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3497:	48 8d 0c 28          	lea    (%rax,%rbp,1),%rcx
    349b:	83 b9 28 02 00 00 01 	cmpl   $0x1,0x228(%rcx)
    34a2:	75 dc                	jne    3480 <barriered_thread+0x50>
    34a4:	45 8b 44 24 18       	mov    0x18(%r12),%r8d
    34a9:	83 ea 01             	sub    $0x1,%edx
    34ac:	8d 73 ff             	lea    -0x1(%rbx),%esi
    34af:	85 db                	test   %ebx,%ebx
    34b1:	0f 4f d6             	cmovg  %esi,%edx
    34b4:	45 85 c0             	test   %r8d,%r8d
    34b7:	0f 8e b3 01 00 00    	jle    3670 <barriered_thread+0x240>
    34bd:	48 63 d2             	movslq %edx,%rdx
    34c0:	44 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9d
    34c7:	45 31 d2             	xor    %r10d,%r10d
    34ca:	45 31 f6             	xor    %r14d,%r14d
    34cd:	48 8d 34 92          	lea    (%rdx,%rdx,4),%rsi
    34d1:	49 63 d0             	movslq %r8d,%rdx
    34d4:	8b b9 00 01 00 00    	mov    0x100(%rcx),%edi
    34da:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    34df:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    34e3:	48 c1 e6 07          	shl    $0x7,%rsi
    34e7:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
    34eb:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    34ef:	90                   	nop
    34f0:	48 8b 50 20          	mov    0x20(%rax),%rdx
    34f4:	48 01 f2             	add    %rsi,%rdx
    34f7:	44 3b 8a 80 00 00 00 	cmp    0x80(%rdx),%r9d
    34fe:	75 04                	jne    3504 <barriered_thread+0xd4>
    3500:	41 83 c6 01          	add    $0x1,%r14d
    3504:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    350a:	75 04                	jne    3510 <barriered_thread+0xe0>
    350c:	41 83 c2 01          	add    $0x1,%r10d
    3510:	48 05 98 00 00 00    	add    $0x98,%rax
    3516:	48 39 c8             	cmp    %rcx,%rax
    3519:	75 d5                	jne    34f0 <barriered_thread+0xc0>
    351b:	45 39 d0             	cmp    %r10d,%r8d
    351e:	0f 84 cc 00 00 00    	je     35f0 <barriered_thread+0x1c0>
    3524:	45 85 d2             	test   %r10d,%r10d
    3527:	0f 84 c3 00 00 00    	je     35f0 <barriered_thread+0x1c0>
    352d:	45 85 f6             	test   %r14d,%r14d
    3530:	74 0b                	je     353d <barriered_thread+0x10d>
    3532:	45 39 74 24 18       	cmp    %r14d,0x18(%r12)
    3537:	0f 85 93 00 00 00    	jne    35d0 <barriered_thread+0x1a0>
    353d:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3542:	48 01 e8             	add    %rbp,%rax
    3545:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
    354c:	85 db                	test   %ebx,%ebx
    354e:	75 10                	jne    3560 <barriered_thread+0x130>
    3550:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    3555:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    355a:	0f 8c 68 01 00 00    	jl     36c8 <barriered_thread+0x298>
    3560:	c7 80 28 02 00 00 00 00 00 00 	movl   $0x0,0x228(%rax)
    356a:	49 63 14 24          	movslq (%r12),%rdx
    356e:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3572:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
    3576:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
    357b:	48 8d 14 d1          	lea    (%rcx,%rdx,8),%rdx
    357f:	48 8b 7a 20          	mov    0x20(%rdx),%rdi
    3583:	48 01 ef             	add    %rbp,%rdi
    3586:	ff 90 08 02 00 00    	call   *0x208(%rax)
    358c:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3591:	48 01 e8             	add    %rbp,%rax
    3594:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
    359b:	41 8b 44 24 28       	mov    0x28(%r12),%eax
    35a0:	49 83 44 24 60 01    	addq   $0x1,0x60(%r12)
    35a6:	83 e8 01             	sub    $0x1,%eax
    35a9:	39 d8                	cmp    %ebx,%eax
    35ab:	74 5b                	je     3608 <barriered_thread+0x1d8>
    35ad:	0f ae f0             	mfence
    35b0:	45 85 ed             	test   %r13d,%r13d
    35b3:	0f 84 7f 00 00 00    	je     3638 <barriered_thread+0x208>
    35b9:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    35be:	83 c3 01             	add    $0x1,%ebx
    35c1:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    35c8:	39 d3                	cmp    %edx,%ebx
    35ca:	0f 8c c2 fe ff ff    	jl     3492 <barriered_thread+0x62>
    35d0:	41 83 7c 24 2c 01    	cmpl   $0x1,0x2c(%r12)
    35d6:	0f 84 74 fe ff ff    	je     3450 <barriered_thread+0x20>
    35dc:	5b                   	pop    %rbx
    35dd:	31 c0                	xor    %eax,%eax
    35df:	5d                   	pop    %rbp
    35e0:	41 5c                	pop    %r12
    35e2:	41 5d                	pop    %r13
    35e4:	41 5e                	pop    %r14
    35e6:	c3                   	ret
    35e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    35f0:	41 83 fd 01          	cmp    $0x1,%r13d
    35f4:	0f 84 86 00 00 00    	je     3680 <barriered_thread+0x250>
    35fa:	45 31 ed             	xor    %r13d,%r13d
    35fd:	e9 2b ff ff ff       	jmp    352d <barriered_thread+0xfd>
    3602:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3608:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    360d:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    3612:	7d 99                	jge    35ad <barriered_thread+0x17d>
    3614:	48 c1 e6 04          	shl    $0x4,%rsi
    3618:	bf 04 00 00 00       	mov    $0x4,%edi
    361d:	49 03 74 24 58       	add    0x58(%r12),%rsi
    3622:	e8 c9 ec ff ff       	call   22f0 <clock_gettime@plt>
    3627:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
    362d:	e9 7b ff ff ff       	jmp    35ad <barriered_thread+0x17d>
    3632:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3638:	49 8b b4 24 80 00 00 00 	mov    0x80(%r12),%rsi
    3640:	bf 04 00 00 00       	mov    $0x4,%edi
    3645:	41 bd 01 00 00 00    	mov    $0x1,%r13d
    364b:	48 c1 e6 08          	shl    $0x8,%rsi
    364f:	49 03 74 24 78       	add    0x78(%r12),%rsi
    3654:	89 9e 90 00 00 00    	mov    %ebx,0x90(%rsi)
    365a:	e8 91 ec ff ff       	call   22f0 <clock_gettime@plt>
    365f:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    3664:	e9 17 fe ff ff       	jmp    3480 <barriered_thread+0x50>
    3669:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3670:	41 83 fd 01          	cmp    $0x1,%r13d
    3674:	0f 85 c8 fe ff ff    	jne    3542 <barriered_thread+0x112>
    367a:	45 31 f6             	xor    %r14d,%r14d
    367d:	0f 1f 00             	nopl   (%rax)
    3680:	49 8b b4 24 80 00 00 00 	mov    0x80(%r12),%rsi
    3688:	bf 04 00 00 00       	mov    $0x4,%edi
    368d:	48 c1 e6 08          	shl    $0x8,%rsi
    3691:	49 03 74 24 78       	add    0x78(%r12),%rsi
    3696:	48 83 ee 80          	sub    $0xffffffffffffff80,%rsi
    369a:	e8 51 ec ff ff       	call   22f0 <clock_gettime@plt>
    369f:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    36a7:	48 83 c0 01          	add    $0x1,%rax
    36ab:	48 99                	cqto
    36ad:	49 f7 bc 24 88 00 00 00 	idivq  0x88(%r12)
    36b5:	49 89 94 24 80 00 00 00 	mov    %rdx,0x80(%r12)
    36bd:	e9 38 ff ff ff       	jmp    35fa <barriered_thread+0x1ca>
    36c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    36c8:	48 c1 e6 04          	shl    $0x4,%rsi
    36cc:	bf 04 00 00 00       	mov    $0x4,%edi
    36d1:	49 03 74 24 50       	add    0x50(%r12),%rsi
    36d6:	e8 15 ec ff ff       	call   22f0 <clock_gettime@plt>
    36db:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    36e0:	48 01 e8             	add    %rbp,%rax
    36e3:	e9 78 fe ff ff       	jmp    3560 <barriered_thread+0x130>
    36e8:	31 c0                	xor    %eax,%eax
    36ea:	c3                   	ret
    36eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000036f0 <external_thread>:
    36f0:	f3 0f 1e fa          	endbr64
    36f4:	41 55                	push   %r13
    36f6:	41 54                	push   %r12
    36f8:	55                   	push   %rbp
    36f9:	53                   	push   %rbx
    36fa:	48 83 ec 38          	sub    $0x38,%rsp
    36fe:	66 0f 6f 05 ea 31 00 00 	movdqa 0x31ea(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    3706:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    370f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3714:	31 c0                	xor    %eax,%eax
    3716:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
    371a:	0f 29 04 24          	movaps %xmm0,(%rsp)
    371e:	75 64                	jne    3784 <external_thread+0x94>
    3720:	49 89 fd             	mov    %rdi,%r13
    3723:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3728:	48 89 e3             	mov    %rsp,%rbx
    372b:	4c 8d 25 d2 28 00 00 	lea    0x28d2(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    3732:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3738:	48 89 ee             	mov    %rbp,%rsi
    373b:	48 89 df             	mov    %rbx,%rdi
    373e:	e8 ed eb ff ff       	call   2330 <nanosleep@plt>
    3743:	49 8b 45 38          	mov    0x38(%r13),%rax
    3747:	48 63 10             	movslq (%rax),%rdx
    374a:	85 d2                	test   %edx,%edx
    374c:	7e 2c                	jle    377a <external_thread+0x8a>
    374e:	48 8b 40 08          	mov    0x8(%rax),%rax
    3752:	48 c1 e2 04          	shl    $0x4,%rdx
    3756:	48 01 c2             	add    %rax,%rdx
    3759:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3760:	8b 48 08             	mov    0x8(%rax),%ecx
    3763:	85 c9                	test   %ecx,%ecx
    3765:	75 0a                	jne    3771 <external_thread+0x81>
    3767:	4c 89 20             	mov    %r12,(%rax)
    376a:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    3771:	48 83 c0 10          	add    $0x10,%rax
    3775:	48 39 c2             	cmp    %rax,%rdx
    3778:	75 e6                	jne    3760 <external_thread+0x70>
    377a:	0f ae f0             	mfence
    377d:	41 83 7d 2c 01       	cmpl   $0x1,0x2c(%r13)
    3782:	74 b4                	je     3738 <external_thread+0x48>
    3784:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3789:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3792:	75 0d                	jne    37a1 <external_thread+0xb1>
    3794:	48 83 c4 38          	add    $0x38,%rsp
    3798:	31 c0                	xor    %eax,%eax
    379a:	5b                   	pop    %rbx
    379b:	5d                   	pop    %rbp
    379c:	41 5c                	pop    %r12
    379e:	41 5d                	pop    %r13
    37a0:	c3                   	ret
    37a1:	e8 6a eb ff ff       	call   2310 <__stack_chk_fail@plt>
    37a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000037b0 <timer_thread>:
    37b0:	f3 0f 1e fa          	endbr64
    37b4:	41 57                	push   %r15
    37b6:	48 8d 35 53 28 00 00 	lea    0x2853(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    37bd:	49 89 ff             	mov    %rdi,%r15
    37c0:	41 56                	push   %r14
    37c2:	41 55                	push   %r13
    37c4:	41 54                	push   %r12
    37c6:	55                   	push   %rbp
    37c7:	53                   	push   %rbx
    37c8:	48 83 ec 58          	sub    $0x58,%rsp
    37cc:	8b 17                	mov    (%rdi),%edx
    37ce:	bf 01 00 00 00       	mov    $0x1,%edi
    37d3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    37dc:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    37e1:	31 c0                	xor    %eax,%eax
    37e3:	e8 48 ec ff ff       	call   2430 <__printf_chk@plt>
    37e8:	66 0f 6f 05 00 31 00 00 	movdqa 0x3100(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    37f0:	ba 10 27 00 00       	mov    $0x2710,%edx
    37f5:	31 c0                	xor    %eax,%eax
    37f7:	48 8d 35 24 28 00 00 	lea    0x2824(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    37fe:	bf 01 00 00 00       	mov    $0x1,%edi
    3803:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3808:	e8 23 ec ff ff       	call   2430 <__printf_chk@plt>
    380d:	45 8b 6f 2c          	mov    0x2c(%r15),%r13d
    3811:	45 85 ed             	test   %r13d,%r13d
    3814:	0f 84 a3 00 00 00    	je     38bd <timer_thread+0x10d>
    381a:	45 31 f6             	xor    %r14d,%r14d
    381d:	45 31 ed             	xor    %r13d,%r13d
    3820:	49 89 e4             	mov    %rsp,%r12
    3823:	31 db                	xor    %ebx,%ebx
    3825:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    382a:	48 89 ef             	mov    %rbp,%rdi
    382d:	4c 89 e6             	mov    %r12,%rsi
    3830:	41 83 c6 01          	add    $0x1,%r14d
    3834:	e8 f7 ea ff ff       	call   2330 <nanosleep@plt>
    3839:	49 63 47 18          	movslq 0x18(%r15),%rax
    383d:	41 8d 7d 01          	lea    0x1(%r13),%edi
    3841:	85 c0                	test   %eax,%eax
    3843:	7e 53                	jle    3898 <timer_thread+0xe8>
    3845:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3849:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    384d:	4f 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%r8
    3852:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3856:	49 c1 e0 07          	shl    $0x7,%r8
    385a:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    385e:	66 90                	xchg   %ax,%ax
    3860:	89 f8                	mov    %edi,%eax
    3862:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    3866:	99                   	cltd
    3867:	f7 79 28             	idivl  0x28(%rcx)
    386a:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3871:	48 63 d2             	movslq %edx,%rdx
    3874:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    3878:	48 c1 e0 07          	shl    $0x7,%rax
    387c:	c7 84 06 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rsi,%rax,1)
    3887:	42 c7 84 06 30 02 00 00 00 00 00 00 	movl   $0x0,0x230(%rsi,%r8,1)
    3893:	49 39 c9             	cmp    %rcx,%r9
    3896:	75 c8                	jne    3860 <timer_thread+0xb0>
    3898:	0f ae f0             	mfence
    389b:	49 8b 47 10          	mov    0x10(%r15),%rax
    389f:	41 8b 57 2c          	mov    0x2c(%r15),%edx
    38a3:	39 78 28             	cmp    %edi,0x28(%rax)
    38a6:	0f 4e fb             	cmovle %ebx,%edi
    38a9:	4c 63 ef             	movslq %edi,%r13
    38ac:	85 d2                	test   %edx,%edx
    38ae:	74 0d                	je     38bd <timer_thread+0x10d>
    38b0:	41 81 fe 10 27 00 00 	cmp    $0x2710,%r14d
    38b7:	0f 85 6d ff ff ff    	jne    382a <timer_thread+0x7a>
    38bd:	48 8d 3d 74 27 00 00 	lea    0x2774(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    38c4:	e8 07 ea ff ff       	call   22d0 <puts@plt>
    38c9:	49 63 47 1c          	movslq 0x1c(%r15),%rax
    38cd:	85 c0                	test   %eax,%eax
    38cf:	0f 8e 8c 00 00 00    	jle    3961 <timer_thread+0x1b1>
    38d5:	41 8b 57 28          	mov    0x28(%r15),%edx
    38d9:	85 d2                	test   %edx,%edx
    38db:	0f 8e 80 00 00 00    	jle    3961 <timer_thread+0x1b1>
    38e1:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    38e5:	4d 8b 4f 10          	mov    0x10(%r15),%r9
    38e9:	48 8d 3c 48          	lea    (%rax,%rcx,2),%rdi
    38ed:	48 63 c2             	movslq %edx,%rax
    38f0:	31 c9                	xor    %ecx,%ecx
    38f2:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    38f6:	48 c1 e7 03          	shl    $0x3,%rdi
    38fa:	48 c1 e0 07          	shl    $0x7,%rax
    38fe:	4c 8d 80 68 02 00 00 	lea    0x268(%rax),%r8
    3905:	49 8b 74 09 20       	mov    0x20(%r9,%rcx,1),%rsi
    390a:	4a 8d 14 06          	lea    (%rsi,%r8,1),%rdx
    390e:	48 8d 86 68 02 00 00 	lea    0x268(%rsi),%rax
    3915:	49 89 d2             	mov    %rdx,%r10
    3918:	49 29 c2             	sub    %rax,%r10
    391b:	41 81 e2 80 00 00 00 	and    $0x80,%r10d
    3922:	74 16                	je     393a <timer_thread+0x18a>
    3924:	48 8d 86 e8 04 00 00 	lea    0x4e8(%rsi),%rax
    392b:	c7 86 68 02 00 00 00 00 00 00 	movl   $0x0,0x268(%rsi)
    3935:	48 39 c2             	cmp    %rax,%rdx
    3938:	74 1b                	je     3955 <timer_thread+0x1a5>
    393a:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    3940:	48 05 00 05 00 00    	add    $0x500,%rax
    3946:	c7 80 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%rax)
    3950:	48 39 c2             	cmp    %rax,%rdx
    3953:	75 e5                	jne    393a <timer_thread+0x18a>
    3955:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    395c:	48 39 cf             	cmp    %rcx,%rdi
    395f:	75 a4                	jne    3905 <timer_thread+0x155>
    3961:	0f ae f0             	mfence
    3964:	66 0f 6f 05 94 2f 00 00 	movdqa 0x2f94(%rip),%xmm0        # 6900 <_IO_stdin_used+0x900>
    396c:	48 8d 2d ea 26 00 00 	lea    0x26ea(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    3973:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    3978:	49 63 47 18          	movslq 0x18(%r15),%rax
    397c:	41 8d 7d 01          	lea    0x1(%r13),%edi
    3980:	85 c0                	test   %eax,%eax
    3982:	7e 54                	jle    39d8 <timer_thread+0x228>
    3984:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3988:	4d 63 ed             	movslq %r13d,%r13
    398b:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    398f:	4f 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%r8
    3994:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3998:	49 c1 e0 07          	shl    $0x7,%r8
    399c:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    39a0:	89 f8                	mov    %edi,%eax
    39a2:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    39a6:	99                   	cltd
    39a7:	f7 79 28             	idivl  0x28(%rcx)
    39aa:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    39b1:	48 63 c2             	movslq %edx,%rax
    39b4:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    39b8:	48 c1 e0 07          	shl    $0x7,%rax
    39bc:	c7 84 06 30 02 00 00 01 00 00 00 	movl   $0x1,0x230(%rsi,%rax,1)
    39c7:	42 c7 84 06 30 02 00 00 00 00 00 00 	movl   $0x0,0x230(%rsi,%r8,1)
    39d3:	4c 39 c9             	cmp    %r9,%rcx
    39d6:	75 c8                	jne    39a0 <timer_thread+0x1f0>
    39d8:	0f ae f0             	mfence
    39db:	49 8b 57 10          	mov    0x10(%r15),%rdx
    39df:	45 31 ed             	xor    %r13d,%r13d
    39e2:	39 7a 28             	cmp    %edi,0x28(%rdx)
    39e5:	44 0f 4f ef          	cmovg  %edi,%r13d
    39e9:	41 8b 7f 18          	mov    0x18(%r15),%edi
    39ed:	85 ff                	test   %edi,%edi
    39ef:	0f 8e ae 00 00 00    	jle    3aa3 <timer_thread+0x2f3>
    39f5:	31 db                	xor    %ebx,%ebx
    39f7:	45 31 e4             	xor    %r12d,%r12d
    39fa:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3a00:	45 31 f6             	xor    %r14d,%r14d
    3a03:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3a08:	4b 8d 04 b6          	lea    (%r14,%r14,4),%rax
    3a0c:	48 c1 e0 07          	shl    $0x7,%rax
    3a10:	48 03 44 1a 20       	add    0x20(%rdx,%rbx,1),%rax
    3a15:	31 d2                	xor    %edx,%edx
    3a17:	48 8b 80 58 02 00 00 	mov    0x258(%rax),%rax
    3a1e:	eb 12                	jmp    3a32 <timer_thread+0x282>
    3a20:	4d 85 c0             	test   %r8,%r8
    3a23:	7f 24                	jg     3a49 <timer_thread+0x299>
    3a25:	83 c2 01             	add    $0x1,%edx
    3a28:	48 05 00 02 00 00    	add    $0x200,%rax
    3a2e:	39 fa                	cmp    %edi,%edx
    3a30:	74 2d                	je     3a5f <timer_thread+0x2af>
    3a32:	48 8b 08             	mov    (%rax),%rcx
    3a35:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    3a3c:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    3a40:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3a44:	48 85 c9             	test   %rcx,%rcx
    3a47:	7e d7                	jle    3a20 <timer_thread+0x270>
    3a49:	bf 01 00 00 00       	mov    $0x1,%edi
    3a4e:	48 89 ee             	mov    %rbp,%rsi
    3a51:	31 c0                	xor    %eax,%eax
    3a53:	e8 d8 e9 ff ff       	call   2430 <__printf_chk@plt>
    3a58:	41 8b 7f 18          	mov    0x18(%r15),%edi
    3a5c:	45 31 c9             	xor    %r9d,%r9d
    3a5f:	49 83 c6 01          	add    $0x1,%r14
    3a63:	44 39 f7             	cmp    %r14d,%edi
    3a66:	7e 08                	jle    3a70 <timer_thread+0x2c0>
    3a68:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3a6c:	eb 9a                	jmp    3a08 <timer_thread+0x258>
    3a6e:	66 90                	xchg   %ax,%ax
    3a70:	41 83 c4 01          	add    $0x1,%r12d
    3a74:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3a7b:	44 39 e7             	cmp    %r12d,%edi
    3a7e:	7e 09                	jle    3a89 <timer_thread+0x2d9>
    3a80:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3a84:	e9 77 ff ff ff       	jmp    3a00 <timer_thread+0x250>
    3a89:	41 83 f9 01          	cmp    $0x1,%r9d
    3a8d:	74 14                	je     3aa3 <timer_thread+0x2f3>
    3a8f:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3a94:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3a99:	e8 92 e8 ff ff       	call   2330 <nanosleep@plt>
    3a9e:	e9 d5 fe ff ff       	jmp    3978 <timer_thread+0x1c8>
    3aa3:	48 8d 3d aa 25 00 00 	lea    0x25aa(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3aaa:	e8 21 e8 ff ff       	call   22d0 <puts@plt>
    3aaf:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3ab3:	85 c0                	test   %eax,%eax
    3ab5:	0f 84 fb 00 00 00    	je     3bb6 <timer_thread+0x406>
    3abb:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3abf:	85 c9                	test   %ecx,%ecx
    3ac1:	7e 38                	jle    3afb <timer_thread+0x34b>
    3ac3:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3ac7:	31 db                	xor    %ebx,%ebx
    3ac9:	31 ed                	xor    %ebp,%ebp
    3acb:	4c 8d 25 9c 25 00 00 	lea    0x259c(%rip),%r12        # 606e <_IO_stdin_used+0x6e>
    3ad2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3ad8:	48 8d 04 1a          	lea    (%rdx,%rbx,1),%rax
    3adc:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
    3ae0:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
    3ae7:	0f 84 f6 00 00 00    	je     3be3 <timer_thread+0x433>
    3aed:	83 c5 01             	add    $0x1,%ebp
    3af0:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3af7:	39 cd                	cmp    %ecx,%ebp
    3af9:	7c dd                	jl     3ad8 <timer_thread+0x328>
    3afb:	49 63 47 18          	movslq 0x18(%r15),%rax
    3aff:	85 c0                	test   %eax,%eax
    3b01:	0f 8e 98 00 00 00    	jle    3b9f <timer_thread+0x3ef>
    3b07:	41 8b 57 28          	mov    0x28(%r15),%edx
    3b0b:	85 d2                	test   %edx,%edx
    3b0d:	0f 8e 8c 00 00 00    	jle    3b9f <timer_thread+0x3ef>
    3b13:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    3b17:	4d 8b 57 10          	mov    0x10(%r15),%r10
    3b1b:	4c 8d 04 48          	lea    (%rax,%rcx,2),%r8
    3b1f:	48 63 c2             	movslq %edx,%rax
    3b22:	31 c9                	xor    %ecx,%ecx
    3b24:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3b28:	49 c1 e0 03          	shl    $0x3,%r8
    3b2c:	48 c1 e0 07          	shl    $0x7,%rax
    3b30:	4c 8d 88 30 02 00 00 	lea    0x230(%rax),%r9
    3b37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3b40:	49 8b 74 0a 20       	mov    0x20(%r10,%rcx,1),%rsi
    3b45:	4a 8d 14 0e          	lea    (%rsi,%r9,1),%rdx
    3b49:	48 8d 86 30 02 00 00 	lea    0x230(%rsi),%rax
    3b50:	48 89 d7             	mov    %rdx,%rdi
    3b53:	48 29 c7             	sub    %rax,%rdi
    3b56:	81 e7 80 00 00 00    	and    $0x80,%edi
    3b5c:	74 1a                	je     3b78 <timer_thread+0x3c8>
    3b5e:	48 8d 86 b0 04 00 00 	lea    0x4b0(%rsi),%rax
    3b65:	c7 86 30 02 00 00 00 00 00 00 	movl   $0x0,0x230(%rsi)
    3b6f:	48 39 d0             	cmp    %rdx,%rax
    3b72:	74 1f                	je     3b93 <timer_thread+0x3e3>
    3b74:	0f 1f 40 00          	nopl   0x0(%rax)
    3b78:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    3b7e:	48 05 00 05 00 00    	add    $0x500,%rax
    3b84:	c7 80 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%rax)
    3b8e:	48 39 d0             	cmp    %rdx,%rax
    3b91:	75 e5                	jne    3b78 <timer_thread+0x3c8>
    3b93:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3b9a:	4c 39 c1             	cmp    %r8,%rcx
    3b9d:	75 a1                	jne    3b40 <timer_thread+0x390>
    3b9f:	0f ae f0             	mfence
    3ba2:	48 8d 3d d7 24 00 00 	lea    0x24d7(%rip),%rdi        # 6080 <_IO_stdin_used+0x80>
    3ba9:	e8 22 e7 ff ff       	call   22d0 <puts@plt>
    3bae:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
    3bb6:	48 8d 3d ca 24 00 00 	lea    0x24ca(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3bbd:	e8 0e e7 ff ff       	call   22d0 <puts@plt>
    3bc2:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3bc7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3bd0:	75 4a                	jne    3c1c <timer_thread+0x46c>
    3bd2:	48 83 c4 58          	add    $0x58,%rsp
    3bd6:	31 c0                	xor    %eax,%eax
    3bd8:	5b                   	pop    %rbx
    3bd9:	5d                   	pop    %rbp
    3bda:	41 5c                	pop    %r12
    3bdc:	41 5d                	pop    %r13
    3bde:	41 5e                	pop    %r14
    3be0:	41 5f                	pop    %r15
    3be2:	c3                   	ret
    3be3:	4c 89 e7             	mov    %r12,%rdi
    3be6:	83 c5 01             	add    $0x1,%ebp
    3be9:	e8 e2 e6 ff ff       	call   22d0 <puts@plt>
    3bee:	49 8b 47 10          	mov    0x10(%r15),%rax
    3bf2:	be 01 00 00 00       	mov    $0x1,%esi
    3bf7:	8b 7c 18 48          	mov    0x48(%rax,%rbx,1),%edi
    3bfb:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3c02:	e8 d9 e7 ff ff       	call   23e0 <eventfd_write@plt>
    3c07:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3c0b:	39 cd                	cmp    %ecx,%ebp
    3c0d:	0f 8d e8 fe ff ff    	jge    3afb <timer_thread+0x34b>
    3c13:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3c17:	e9 bc fe ff ff       	jmp    3ad8 <timer_thread+0x328>
    3c1c:	e8 ef e6 ff ff       	call   2310 <__stack_chk_fail@plt>
    3c21:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3c2c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003c30 <strtolower>:
    3c30:	f3 0f 1e fa          	endbr64
    3c34:	55                   	push   %rbp
    3c35:	53                   	push   %rbx
    3c36:	48 83 ec 08          	sub    $0x8,%rsp
    3c3a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3c3e:	84 db                	test   %bl,%bl
    3c40:	74 24                	je     3c66 <strtolower+0x36>
    3c42:	48 89 fd             	mov    %rdi,%rbp
    3c45:	e8 a6 e8 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3c4a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c50:	48 8b 10             	mov    (%rax),%rdx
    3c53:	48 83 c5 01          	add    $0x1,%rbp
    3c57:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3c5a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    3c5d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3c62:	84 db                	test   %bl,%bl
    3c64:	75 ea                	jne    3c50 <strtolower+0x20>
    3c66:	48 83 c4 08          	add    $0x8,%rsp
    3c6a:	5b                   	pop    %rbx
    3c6b:	5d                   	pop    %rbp
    3c6c:	c3                   	ret
    3c6d:	0f 1f 00             	nopl   (%rax)

0000000000003c70 <zh_malloc>:
    3c70:	f3 0f 1e fa          	endbr64
    3c74:	48 83 ec 08          	sub    $0x8,%rsp
    3c78:	e8 73 e7 ff ff       	call   23f0 <malloc@plt>
    3c7d:	48 85 c0             	test   %rax,%rax
    3c80:	74 05                	je     3c87 <zh_malloc+0x17>
    3c82:	48 83 c4 08          	add    $0x8,%rsp
    3c86:	c3                   	ret
    3c87:	48 8b 0d 92 53 00 00 	mov    0x5392(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3c8e:	ba 28 00 00 00       	mov    $0x28,%edx
    3c93:	be 01 00 00 00       	mov    $0x1,%esi
    3c98:	48 8d 3d 81 27 00 00 	lea    0x2781(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    3c9f:	e8 fc e7 ff ff       	call   24a0 <fwrite@plt>
    3ca4:	bf 01 00 00 00       	mov    $0x1,%edi
    3ca9:	e8 d2 e7 ff ff       	call   2480 <exit@plt>
    3cae:	66 90                	xchg   %ax,%ax

0000000000003cb0 <get_filename_ext>:
    3cb0:	f3 0f 1e fa          	endbr64
    3cb4:	53                   	push   %rbx
    3cb5:	be 2e 00 00 00       	mov    $0x2e,%esi
    3cba:	48 89 fb             	mov    %rdi,%rbx
    3cbd:	e8 7e e6 ff ff       	call   2340 <strrchr@plt>
    3cc2:	48 85 c0             	test   %rax,%rax
    3cc5:	74 11                	je     3cd8 <get_filename_ext+0x28>
    3cc7:	48 39 c3             	cmp    %rax,%rbx
    3cca:	74 0c                	je     3cd8 <get_filename_ext+0x28>
    3ccc:	48 83 c0 01          	add    $0x1,%rax
    3cd0:	5b                   	pop    %rbx
    3cd1:	c3                   	ret
    3cd2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3cd8:	48 8d 05 f0 23 00 00 	lea    0x23f0(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
    3cdf:	5b                   	pop    %rbx
    3ce0:	c3                   	ret
    3ce1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3cec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003cf0 <send_headers>:
    3cf0:	f3 0f 1e fa          	endbr64
    3cf4:	41 55                	push   %r13
    3cf6:	49 89 f5             	mov    %rsi,%r13
    3cf9:	48 89 fe             	mov    %rdi,%rsi
    3cfc:	41 54                	push   %r12
    3cfe:	55                   	push   %rbp
    3cff:	48 89 d5             	mov    %rdx,%rbp
    3d02:	ba 00 04 00 00       	mov    $0x400,%edx
    3d07:	53                   	push   %rbx
    3d08:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3d0f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3d18:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3d20:	31 c0                	xor    %eax,%eax
    3d22:	49 89 e4             	mov    %rsp,%r12
    3d25:	4c 89 e7             	mov    %r12,%rdi
    3d28:	e8 e3 e6 ff ff       	call   2410 <__strcpy_chk@plt>
    3d2d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3d32:	84 db                	test   %bl,%bl
    3d34:	74 24                	je     3d5a <send_headers+0x6a>
    3d36:	e8 b5 e7 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3d3b:	48 8b 08             	mov    (%rax),%rcx
    3d3e:	4c 89 e0             	mov    %r12,%rax
    3d41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3d48:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    3d4b:	48 83 c0 01          	add    $0x1,%rax
    3d4f:	88 50 ff             	mov    %dl,-0x1(%rax)
    3d52:	48 0f be 18          	movsbq (%rax),%rbx
    3d56:	84 db                	test   %bl,%bl
    3d58:	75 ee                	jne    3d48 <send_headers+0x58>
    3d5a:	bf 11 00 00 00       	mov    $0x11,%edi
    3d5f:	e8 8c e6 ff ff       	call   23f0 <malloc@plt>
    3d64:	48 85 c0             	test   %rax,%rax
    3d67:	0f 84 7e 04 00 00    	je     41eb <send_headers+0x4fb>
    3d6d:	66 0f 6f 05 9b 2b 00 00 	movdqa 0x2b9b(%rip),%xmm0        # 6910 <_IO_stdin_used+0x910>
    3d75:	48 89 45 00          	mov    %rax,0x0(%rbp)
    3d79:	bf 17 00 00 00       	mov    $0x17,%edi
    3d7e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3d86:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3d8a:	0f 11 00             	movups %xmm0,(%rax)
    3d8d:	e8 5e e6 ff ff       	call   23f0 <malloc@plt>
    3d92:	48 85 c0             	test   %rax,%rax
    3d95:	0f 84 50 04 00 00    	je     41eb <send_headers+0x4fb>
    3d9b:	66 0f 6f 05 7d 2b 00 00 	movdqa 0x2b7d(%rip),%xmm0        # 6920 <_IO_stdin_used+0x920>
    3da3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    3da7:	4c 89 e7             	mov    %r12,%rdi
    3daa:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    3db4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3dbc:	0f 11 00             	movups %xmm0,(%rax)
    3dbf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    3dc3:	be 2e 00 00 00       	mov    $0x2e,%esi
    3dc8:	e8 73 e5 ff ff       	call   2340 <strrchr@plt>
    3dcd:	48 85 c0             	test   %rax,%rax
    3dd0:	0f 84 ea 02 00 00    	je     40c0 <send_headers+0x3d0>
    3dd6:	4c 39 e0             	cmp    %r12,%rax
    3dd9:	0f 84 e1 02 00 00    	je     40c0 <send_headers+0x3d0>
    3ddf:	48 8d 58 01          	lea    0x1(%rax),%rbx
    3de3:	48 8d 3d b3 22 00 00 	lea    0x22b3(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3dea:	48 89 de             	mov    %rbx,%rsi
    3ded:	e8 9e e5 ff ff       	call   2390 <strcmp@plt>
    3df2:	85 c0                	test   %eax,%eax
    3df4:	75 20                	jne    3e16 <send_headers+0x126>
    3df6:	66 0f 6f 05 32 2b 00 00 	movdqa 0x2b32(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3dfe:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3e06:	66 0f 6f 05 32 2b 00 00 	movdqa 0x2b32(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3e0e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3e16:	48 89 de             	mov    %rbx,%rsi
    3e19:	48 8d 3d 81 22 00 00 	lea    0x2281(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3e20:	e8 6b e5 ff ff       	call   2390 <strcmp@plt>
    3e25:	85 c0                	test   %eax,%eax
    3e27:	75 20                	jne    3e49 <send_headers+0x159>
    3e29:	66 0f 6f 05 ff 2a 00 00 	movdqa 0x2aff(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3e31:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3e39:	66 0f 6f 05 ff 2a 00 00 	movdqa 0x2aff(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3e41:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3e49:	48 89 de             	mov    %rbx,%rsi
    3e4c:	48 8d 3d 53 22 00 00 	lea    0x2253(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3e53:	e8 38 e5 ff ff       	call   2390 <strcmp@plt>
    3e58:	85 c0                	test   %eax,%eax
    3e5a:	0f 84 10 02 00 00    	je     4070 <send_headers+0x380>
    3e60:	48 89 de             	mov    %rbx,%rsi
    3e63:	48 8d 3d 40 22 00 00 	lea    0x2240(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3e6a:	e8 21 e5 ff ff       	call   2390 <strcmp@plt>
    3e6f:	85 c0                	test   %eax,%eax
    3e71:	0f 84 a9 02 00 00    	je     4120 <send_headers+0x430>
    3e77:	48 89 de             	mov    %rbx,%rsi
    3e7a:	48 8d 3d 2d 22 00 00 	lea    0x222d(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3e81:	e8 0a e5 ff ff       	call   2390 <strcmp@plt>
    3e86:	85 c0                	test   %eax,%eax
    3e88:	0f 84 6a 02 00 00    	je     40f8 <send_headers+0x408>
    3e8e:	48 89 de             	mov    %rbx,%rsi
    3e91:	48 8d 3d 59 22 00 00 	lea    0x2259(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3e98:	e8 f3 e4 ff ff       	call   2390 <strcmp@plt>
    3e9d:	85 c0                	test   %eax,%eax
    3e9f:	0f 84 2b 02 00 00    	je     40d0 <send_headers+0x3e0>
    3ea5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3ea8:	0f 84 52 01 00 00    	je     4000 <send_headers+0x310>
    3eae:	48 89 de             	mov    %rbx,%rsi
    3eb1:	48 8d 3d fa 21 00 00 	lea    0x21fa(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3eb8:	e8 d3 e4 ff ff       	call   2390 <strcmp@plt>
    3ebd:	85 c0                	test   %eax,%eax
    3ebf:	0f 84 ab 02 00 00    	je     4170 <send_headers+0x480>
    3ec5:	48 89 de             	mov    %rbx,%rsi
    3ec8:	48 8d 3d e7 21 00 00 	lea    0x21e7(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3ecf:	e8 bc e4 ff ff       	call   2390 <strcmp@plt>
    3ed4:	85 c0                	test   %eax,%eax
    3ed6:	0f 84 6c 02 00 00    	je     4148 <send_headers+0x458>
    3edc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3ee4:	4c 89 e7             	mov    %r12,%rdi
    3ee7:	e8 14 e4 ff ff       	call   2300 <strlen@plt>
    3eec:	48 89 c7             	mov    %rax,%rdi
    3eef:	48 89 c3             	mov    %rax,%rbx
    3ef2:	e8 f9 e4 ff ff       	call   23f0 <malloc@plt>
    3ef7:	48 85 c0             	test   %rax,%rax
    3efa:	0f 84 eb 02 00 00    	je     41eb <send_headers+0x4fb>
    3f00:	48 89 45 20          	mov    %rax,0x20(%rbp)
    3f04:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    3f08:	83 fb 08             	cmp    $0x8,%ebx
    3f0b:	0f 83 3f 01 00 00    	jae    4050 <send_headers+0x360>
    3f11:	f6 c3 04             	test   $0x4,%bl
    3f14:	0f 85 7b 02 00 00    	jne    4195 <send_headers+0x4a5>
    3f1a:	85 db                	test   %ebx,%ebx
    3f1c:	74 13                	je     3f31 <send_headers+0x241>
    3f1e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3f26:	88 10                	mov    %dl,(%rax)
    3f28:	f6 c3 02             	test   $0x2,%bl
    3f2b:	0f 85 96 02 00 00    	jne    41c7 <send_headers+0x4d7>
    3f31:	4d 89 e8             	mov    %r13,%r8
    3f34:	48 8d 0d 7f 21 00 00 	lea    0x217f(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    3f3b:	4c 89 e7             	mov    %r12,%rdi
    3f3e:	31 c0                	xor    %eax,%eax
    3f40:	ba 00 04 00 00       	mov    $0x400,%edx
    3f45:	be 01 00 00 00       	mov    $0x1,%esi
    3f4a:	e8 b1 e5 ff ff       	call   2500 <__sprintf_chk@plt>
    3f4f:	4c 89 e7             	mov    %r12,%rdi
    3f52:	e8 a9 e3 ff ff       	call   2300 <strlen@plt>
    3f57:	48 89 c7             	mov    %rax,%rdi
    3f5a:	48 89 c3             	mov    %rax,%rbx
    3f5d:	e8 8e e4 ff ff       	call   23f0 <malloc@plt>
    3f62:	48 85 c0             	test   %rax,%rax
    3f65:	0f 84 80 02 00 00    	je     41eb <send_headers+0x4fb>
    3f6b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    3f6f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    3f73:	83 fb 08             	cmp    $0x8,%ebx
    3f76:	0f 83 1c 01 00 00    	jae    4098 <send_headers+0x3a8>
    3f7c:	f6 c3 04             	test   $0x4,%bl
    3f7f:	0f 85 29 02 00 00    	jne    41ae <send_headers+0x4be>
    3f85:	85 db                	test   %ebx,%ebx
    3f87:	74 13                	je     3f9c <send_headers+0x2ac>
    3f89:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3f91:	88 10                	mov    %dl,(%rax)
    3f93:	f6 c3 02             	test   $0x2,%bl
    3f96:	0f 85 3d 02 00 00    	jne    41d9 <send_headers+0x4e9>
    3f9c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    3fa1:	bf 02 00 00 00       	mov    $0x2,%edi
    3fa6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    3fae:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    3fb6:	e8 35 e4 ff ff       	call   23f0 <malloc@plt>
    3fbb:	48 85 c0             	test   %rax,%rax
    3fbe:	0f 84 27 02 00 00    	je     41eb <send_headers+0x4fb>
    3fc4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    3fcc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    3fd0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    3fd8:	66 89 10             	mov    %dx,(%rax)
    3fdb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    3fe3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3fec:	0f 85 20 02 00 00    	jne    4212 <send_headers+0x522>
    3ff2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    3ff9:	5b                   	pop    %rbx
    3ffa:	5d                   	pop    %rbp
    3ffb:	41 5c                	pop    %r12
    3ffd:	41 5d                	pop    %r13
    3fff:	c3                   	ret
    4000:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4004:	0f 85 a4 fe ff ff    	jne    3eae <send_headers+0x1be>
    400a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    400e:	0f 85 9a fe ff ff    	jne    3eae <send_headers+0x1be>
    4014:	66 0f 6f 05 74 29 00 00 	movdqa 0x2974(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    401c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4026:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    402e:	66 0f 6f 05 6a 29 00 00 	movdqa 0x296a(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    4036:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    403e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4046:	e9 63 fe ff ff       	jmp    3eae <send_headers+0x1be>
    404b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4050:	89 da                	mov    %ebx,%edx
    4052:	48 89 c7             	mov    %rax,%rdi
    4055:	4c 89 e6             	mov    %r12,%rsi
    4058:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    405d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4062:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4065:	c1 e9 03             	shr    $0x3,%ecx
    4068:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    406b:	e9 c1 fe ff ff       	jmp    3f31 <send_headers+0x241>
    4070:	66 0f 6f 05 b8 28 00 00 	movdqa 0x28b8(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4078:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4080:	66 0f 6f 05 c8 28 00 00 	movdqa 0x28c8(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    4088:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4090:	e9 cb fd ff ff       	jmp    3e60 <send_headers+0x170>
    4095:	0f 1f 00             	nopl   (%rax)
    4098:	89 da                	mov    %ebx,%edx
    409a:	48 89 c7             	mov    %rax,%rdi
    409d:	4c 89 e6             	mov    %r12,%rsi
    40a0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    40a5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    40aa:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    40ad:	c1 e9 03             	shr    $0x3,%ecx
    40b0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    40b3:	e9 e4 fe ff ff       	jmp    3f9c <send_headers+0x2ac>
    40b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    40c0:	48 8d 1d 08 20 00 00 	lea    0x2008(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    40c7:	e9 94 fd ff ff       	jmp    3e60 <send_headers+0x170>
    40cc:	0f 1f 40 00          	nopl   0x0(%rax)
    40d0:	66 0f 6f 05 98 28 00 00 	movdqa 0x2898(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    40d8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40e0:	66 0f 6f 05 98 28 00 00 	movdqa 0x2898(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    40e8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40f0:	e9 b0 fd ff ff       	jmp    3ea5 <send_headers+0x1b5>
    40f5:	0f 1f 00             	nopl   (%rax)
    40f8:	66 0f 6f 05 70 28 00 00 	movdqa 0x2870(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4100:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4108:	66 0f 6f 05 70 28 00 00 	movdqa 0x2870(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4110:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4118:	e9 71 fd ff ff       	jmp    3e8e <send_headers+0x19e>
    411d:	0f 1f 00             	nopl   (%rax)
    4120:	66 0f 6f 05 08 28 00 00 	movdqa 0x2808(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4128:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4130:	66 0f 6f 05 28 28 00 00 	movdqa 0x2828(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    4138:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4140:	e9 32 fd ff ff       	jmp    3e77 <send_headers+0x187>
    4145:	0f 1f 00             	nopl   (%rax)
    4148:	66 0f 6f 05 20 28 00 00 	movdqa 0x2820(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4150:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4158:	66 0f 6f 05 60 28 00 00 	movdqa 0x2860(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4160:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4168:	e9 6f fd ff ff       	jmp    3edc <send_headers+0x1ec>
    416d:	0f 1f 00             	nopl   (%rax)
    4170:	66 0f 6f 05 f8 27 00 00 	movdqa 0x27f8(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4178:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4180:	66 0f 6f 05 28 28 00 00 	movdqa 0x2828(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    4188:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4190:	e9 30 fd ff ff       	jmp    3ec5 <send_headers+0x1d5>
    4195:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    419c:	89 db                	mov    %ebx,%ebx
    419e:	89 10                	mov    %edx,(%rax)
    41a0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    41a5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    41a9:	e9 83 fd ff ff       	jmp    3f31 <send_headers+0x241>
    41ae:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    41b5:	89 db                	mov    %ebx,%ebx
    41b7:	89 10                	mov    %edx,(%rax)
    41b9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    41be:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    41c2:	e9 d5 fd ff ff       	jmp    3f9c <send_headers+0x2ac>
    41c7:	89 db                	mov    %ebx,%ebx
    41c9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    41cf:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    41d4:	e9 58 fd ff ff       	jmp    3f31 <send_headers+0x241>
    41d9:	89 db                	mov    %ebx,%ebx
    41db:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    41e1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    41e6:	e9 b1 fd ff ff       	jmp    3f9c <send_headers+0x2ac>
    41eb:	48 8b 0d 2e 4e 00 00 	mov    0x4e2e(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    41f2:	ba 28 00 00 00       	mov    $0x28,%edx
    41f7:	be 01 00 00 00       	mov    $0x1,%esi
    41fc:	48 8d 3d 1d 22 00 00 	lea    0x221d(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    4203:	e8 98 e2 ff ff       	call   24a0 <fwrite@plt>
    4208:	bf 01 00 00 00       	mov    $0x1,%edi
    420d:	e8 6e e2 ff ff       	call   2480 <exit@plt>
    4212:	e8 f9 e0 ff ff       	call   2310 <__stack_chk_fail@plt>
    4217:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004220 <copy_file_contents>:
    4220:	f3 0f 1e fa          	endbr64
    4224:	41 55                	push   %r13
    4226:	49 89 d5             	mov    %rdx,%r13
    4229:	41 54                	push   %r12
    422b:	49 89 fc             	mov    %rdi,%r12
    422e:	48 89 f7             	mov    %rsi,%rdi
    4231:	55                   	push   %rbp
    4232:	53                   	push   %rbx
    4233:	48 89 f3             	mov    %rsi,%rbx
    4236:	48 83 ec 08          	sub    $0x8,%rsp
    423a:	e8 b1 e1 ff ff       	call   23f0 <malloc@plt>
    423f:	48 85 c0             	test   %rax,%rax
    4242:	74 6b                	je     42af <copy_file_contents+0x8f>
    4244:	4c 89 e7             	mov    %r12,%rdi
    4247:	48 89 c5             	mov    %rax,%rbp
    424a:	31 f6                	xor    %esi,%esi
    424c:	31 c0                	xor    %eax,%eax
    424e:	e8 0d e2 ff ff       	call   2460 <open@plt>
    4253:	41 89 c4             	mov    %eax,%r12d
    4256:	85 c0                	test   %eax,%eax
    4258:	0f 88 d8 e2 ff ff    	js     2536 <copy_file_contents.cold>
    425e:	48 89 da             	mov    %rbx,%rdx
    4261:	48 89 ee             	mov    %rbp,%rsi
    4264:	89 c7                	mov    %eax,%edi
    4266:	e8 05 e1 ff ff       	call   2370 <read@plt>
    426b:	48 98                	cltq
    426d:	48 39 d8             	cmp    %rbx,%rax
    4270:	7c 1e                	jl     4290 <copy_file_contents+0x70>
    4272:	44 89 e7             	mov    %r12d,%edi
    4275:	e8 d6 e0 ff ff       	call   2350 <close@plt>
    427a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    427e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    4282:	48 83 c4 08          	add    $0x8,%rsp
    4286:	5b                   	pop    %rbx
    4287:	5d                   	pop    %rbp
    4288:	41 5c                	pop    %r12
    428a:	41 5d                	pop    %r13
    428c:	c3                   	ret
    428d:	0f 1f 00             	nopl   (%rax)
    4290:	48 8b 0d 89 4d 00 00 	mov    0x4d89(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4297:	ba 1a 00 00 00       	mov    $0x1a,%edx
    429c:	be 01 00 00 00       	mov    $0x1,%esi
    42a1:	48 8d 3d 28 1e 00 00 	lea    0x1e28(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    42a8:	e8 f3 e1 ff ff       	call   24a0 <fwrite@plt>
    42ad:	eb c3                	jmp    4272 <copy_file_contents+0x52>
    42af:	48 8b 0d 6a 4d 00 00 	mov    0x4d6a(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    42b6:	ba 28 00 00 00       	mov    $0x28,%edx
    42bb:	be 01 00 00 00       	mov    $0x1,%esi
    42c0:	48 8d 3d 59 21 00 00 	lea    0x2159(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    42c7:	e8 d4 e1 ff ff       	call   24a0 <fwrite@plt>
    42cc:	bf 01 00 00 00       	mov    $0x1,%edi
    42d1:	e8 aa e1 ff ff       	call   2480 <exit@plt>
    42d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000042e0 <add_write_request>:
    42e0:	f3 0f 1e fa          	endbr64
    42e4:	8b 46 44             	mov    0x44(%rsi),%eax
    42e7:	48 89 fa             	mov    %rdi,%rdx
    42ea:	48 89 f7             	mov    %rsi,%rdi
    42ed:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    42f3:	8d 70 01             	lea    0x1(%rax),%esi
    42f6:	48 8b 07             	mov    (%rdi),%rax
    42f9:	44 8b 00             	mov    (%rax),%r8d
    42fc:	f6 c1 02             	test   $0x2,%cl
    42ff:	74 00                	je     4301 <add_write_request+0x21>
    4301:	89 f0                	mov    %esi,%eax
    4303:	44 29 c0             	sub    %r8d,%eax
    4306:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4309:	0f 82 33 e2 ff ff    	jb     2542 <add_write_request.cold>
    430f:	c1 e9 0a             	shr    $0xa,%ecx
    4312:	48 83 ec 08          	sub    $0x8,%rsp
    4316:	8b 47 44             	mov    0x44(%rdi),%eax
    4319:	23 47 58             	and    0x58(%rdi),%eax
    431c:	83 e1 01             	and    $0x1,%ecx
    431f:	89 77 44             	mov    %esi,0x44(%rdi)
    4322:	8b 72 08             	mov    0x8(%rdx),%esi
    4325:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4329:	d3 e0                	shl    %cl,%eax
    432b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    432e:	48 c1 e0 06          	shl    $0x6,%rax
    4332:	48 03 47 38          	add    0x38(%rdi),%rax
    4336:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    433c:	89 70 04             	mov    %esi,0x4(%rax)
    433f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    4343:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4349:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4351:	48 89 70 10          	mov    %rsi,0x10(%rax)
    4355:	89 48 18             	mov    %ecx,0x18(%rax)
    4358:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    435f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4367:	48 89 50 20          	mov    %rdx,0x20(%rax)
    436b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    436f:	e8 ac df ff ff       	call   2320 <io_uring_submit@plt>
    4374:	31 c0                	xor    %eax,%eax
    4376:	48 83 c4 08          	add    $0x8,%rsp
    437a:	c3                   	ret
    437b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004380 <add_read_request>:
    4380:	f3 0f 1e fa          	endbr64
    4384:	41 55                	push   %r13
    4386:	41 89 fd             	mov    %edi,%r13d
    4389:	41 54                	push   %r12
    438b:	55                   	push   %rbp
    438c:	53                   	push   %rbx
    438d:	48 89 f3             	mov    %rsi,%rbx
    4390:	48 83 ec 08          	sub    $0x8,%rsp
    4394:	8b 46 44             	mov    0x44(%rsi),%eax
    4397:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    439d:	48 8b 16             	mov    (%rsi),%rdx
    43a0:	83 c0 01             	add    $0x1,%eax
    43a3:	8b 32                	mov    (%rdx),%esi
    43a5:	f6 c1 02             	test   $0x2,%cl
    43a8:	74 00                	je     43aa <add_read_request+0x2a>
    43aa:	89 c2                	mov    %eax,%edx
    43ac:	29 f2                	sub    %esi,%edx
    43ae:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    43b1:	0f 82 9b e1 ff ff    	jb     2552 <add_read_request.cold>
    43b7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    43ba:	c1 e9 0a             	shr    $0xa,%ecx
    43bd:	89 43 44             	mov    %eax,0x44(%rbx)
    43c0:	bf 20 00 00 00       	mov    $0x20,%edi
    43c5:	83 e1 01             	and    $0x1,%ecx
    43c8:	23 6b 58             	and    0x58(%rbx),%ebp
    43cb:	d3 e5                	shl    %cl,%ebp
    43cd:	48 c1 e5 06          	shl    $0x6,%rbp
    43d1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    43d5:	e8 16 e0 ff ff       	call   23f0 <malloc@plt>
    43da:	be 01 00 00 00       	mov    $0x1,%esi
    43df:	bf 00 20 00 00       	mov    $0x2000,%edi
    43e4:	49 89 c4             	mov    %rax,%r12
    43e7:	e8 94 df ff ff       	call   2380 <calloc@plt>
    43ec:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    43f1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    43f5:	48 89 df             	mov    %rbx,%rdi
    43f8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    43fd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    4402:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    440b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    4413:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    4417:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    441b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    4422:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    442a:	48 89 45 10          	mov    %rax,0x10(%rbp)
    442e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    4436:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    443e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4442:	e8 d9 de ff ff       	call   2320 <io_uring_submit@plt>
    4447:	48 83 c4 08          	add    $0x8,%rsp
    444b:	31 c0                	xor    %eax,%eax
    444d:	5b                   	pop    %rbx
    444e:	5d                   	pop    %rbp
    444f:	41 5c                	pop    %r12
    4451:	41 5d                	pop    %r13
    4453:	c3                   	ret
    4454:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    445f:	90                   	nop

0000000000004460 <_send_static_string_content>:
    4460:	f3 0f 1e fa          	endbr64
    4464:	41 56                	push   %r14
    4466:	41 89 f6             	mov    %esi,%r14d
    4469:	41 55                	push   %r13
    446b:	49 89 fd             	mov    %rdi,%r13
    446e:	bf 20 00 00 00       	mov    $0x20,%edi
    4473:	41 54                	push   %r12
    4475:	55                   	push   %rbp
    4476:	48 89 d5             	mov    %rdx,%rbp
    4479:	53                   	push   %rbx
    447a:	e8 71 df ff ff       	call   23f0 <malloc@plt>
    447f:	48 85 c0             	test   %rax,%rax
    4482:	0f 84 dd 00 00 00    	je     4565 <_send_static_string_content+0x105>
    4488:	48 89 c3             	mov    %rax,%rbx
    448b:	4c 89 ef             	mov    %r13,%rdi
    448e:	e8 6d de ff ff       	call   2300 <strlen@plt>
    4493:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    449a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    449e:	48 89 c7             	mov    %rax,%rdi
    44a1:	49 89 c4             	mov    %rax,%r12
    44a4:	e8 47 df ff ff       	call   23f0 <malloc@plt>
    44a9:	48 89 c7             	mov    %rax,%rdi
    44ac:	48 85 c0             	test   %rax,%rax
    44af:	0f 84 b0 00 00 00    	je     4565 <_send_static_string_content+0x105>
    44b5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    44b9:	4c 89 e2             	mov    %r12,%rdx
    44bc:	4c 89 ee             	mov    %r13,%rsi
    44bf:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    44c3:	e8 f8 de ff ff       	call   23c0 <memcpy@plt>
    44c8:	8b 45 44             	mov    0x44(%rbp),%eax
    44cb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    44d1:	8d 50 01             	lea    0x1(%rax),%edx
    44d4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    44d8:	8b 30                	mov    (%rax),%esi
    44da:	f6 c1 02             	test   $0x2,%cl
    44dd:	0f 85 7d 00 00 00    	jne    4560 <_send_static_string_content+0x100>
    44e3:	89 d0                	mov    %edx,%eax
    44e5:	29 f0                	sub    %esi,%eax
    44e7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    44ea:	0f 82 6c e0 ff ff    	jb     255c <_send_static_string_content.cold>
    44f0:	c1 e9 0a             	shr    $0xa,%ecx
    44f3:	8b 45 44             	mov    0x44(%rbp),%eax
    44f6:	23 45 58             	and    0x58(%rbp),%eax
    44f9:	89 55 44             	mov    %edx,0x44(%rbp)
    44fc:	83 e1 01             	and    $0x1,%ecx
    44ff:	8b 53 04             	mov    0x4(%rbx),%edx
    4502:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    4508:	66 0f ef c0          	pxor   %xmm0,%xmm0
    450c:	d3 e0                	shl    %cl,%eax
    450e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    4511:	48 89 ef             	mov    %rbp,%rdi
    4514:	48 c1 e0 06          	shl    $0x6,%rax
    4518:	48 03 45 38          	add    0x38(%rbp),%rax
    451c:	89 48 04             	mov    %ecx,0x4(%rax)
    451f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    4523:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4529:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4531:	48 89 48 10          	mov    %rcx,0x10(%rax)
    4535:	89 50 18             	mov    %edx,0x18(%rax)
    4538:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    453f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4547:	48 89 58 20          	mov    %rbx,0x20(%rax)
    454b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    454f:	5b                   	pop    %rbx
    4550:	5d                   	pop    %rbp
    4551:	41 5c                	pop    %r12
    4553:	41 5d                	pop    %r13
    4555:	41 5e                	pop    %r14
    4557:	e9 c4 dd ff ff       	jmp    2320 <io_uring_submit@plt>
    455c:	0f 1f 40 00          	nopl   0x0(%rax)
    4560:	e9 7e ff ff ff       	jmp    44e3 <_send_static_string_content+0x83>
    4565:	48 8b 0d b4 4a 00 00 	mov    0x4ab4(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    456c:	ba 28 00 00 00       	mov    $0x28,%edx
    4571:	be 01 00 00 00       	mov    $0x1,%esi
    4576:	48 8d 3d a3 1e 00 00 	lea    0x1ea3(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    457d:	e8 1e df ff ff       	call   24a0 <fwrite@plt>
    4582:	bf 01 00 00 00       	mov    $0x1,%edi
    4587:	e8 f4 de ff ff       	call   2480 <exit@plt>
    458c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004590 <handle_unimplemented_method>:
    4590:	f3 0f 1e fa          	endbr64
    4594:	48 89 f2             	mov    %rsi,%rdx
    4597:	89 fe                	mov    %edi,%esi
    4599:	48 8b 3d 78 4a 00 00 	mov    0x4a78(%rip),%rdi        # 9018 <unimplemented_content>
    45a0:	e9 bb fe ff ff       	jmp    4460 <_send_static_string_content>
    45a5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000045b0 <handle_http_404>:
    45b0:	f3 0f 1e fa          	endbr64
    45b4:	48 89 f2             	mov    %rsi,%rdx
    45b7:	89 fe                	mov    %edi,%esi
    45b9:	48 8b 3d 50 4a 00 00 	mov    0x4a50(%rip),%rdi        # 9010 <http_404_content>
    45c0:	e9 9b fe ff ff       	jmp    4460 <_send_static_string_content>
    45c5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000045d0 <handle_get_method>:
    45d0:	f3 0f 1e fa          	endbr64
    45d4:	41 56                	push   %r14
    45d6:	41 55                	push   %r13
    45d8:	49 89 d5             	mov    %rdx,%r13
    45db:	41 54                	push   %r12
    45dd:	41 89 f4             	mov    %esi,%r12d
    45e0:	55                   	push   %rbp
    45e1:	48 89 fd             	mov    %rdi,%rbp
    45e4:	53                   	push   %rbx
    45e5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    45ec:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    45f5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    45fd:	31 c0                	xor    %eax,%eax
    45ff:	e8 fc dc ff ff       	call   2300 <strlen@plt>
    4604:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4609:	48 89 c3             	mov    %rax,%rbx
    460c:	0f 84 b6 00 00 00    	je     46c8 <handle_get_method+0xf8>
    4612:	b8 69 63 00 00       	mov    $0x6369,%eax
    4617:	48 89 ee             	mov    %rbp,%rsi
    461a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    461e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4623:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    462b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4633:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    463e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    4646:	e8 55 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    464b:	48 89 e6             	mov    %rsp,%rsi
    464e:	4c 89 f7             	mov    %r14,%rdi
    4651:	e8 5a dd ff ff       	call   23b0 <stat@plt>
    4656:	83 f8 ff             	cmp    $0xffffffff,%eax
    4659:	0f 84 d3 00 00 00    	je     4732 <handle_get_method+0x162>
    465f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4663:	25 00 f0 00 00       	and    $0xf000,%eax
    4668:	3d 00 80 00 00       	cmp    $0x8000,%eax
    466d:	0f 84 f5 00 00 00    	je     4768 <handle_get_method+0x198>
    4673:	48 8b 3d 96 49 00 00 	mov    0x4996(%rip),%rdi        # 9010 <http_404_content>
    467a:	4c 89 ea             	mov    %r13,%rdx
    467d:	44 89 e6             	mov    %r12d,%esi
    4680:	e8 db fd ff ff       	call   4460 <_send_static_string_content>
    4685:	4c 89 f2             	mov    %r14,%rdx
    4688:	bf 01 00 00 00       	mov    $0x1,%edi
    468d:	31 c0                	xor    %eax,%eax
    468f:	48 8d 35 8a 1a 00 00 	lea    0x1a8a(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    4696:	e8 95 dd ff ff       	call   2430 <__printf_chk@plt>
    469b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    46a3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    46ac:	0f 85 20 01 00 00    	jne    47d2 <handle_get_method+0x202>
    46b2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    46b9:	5b                   	pop    %rbx
    46ba:	5d                   	pop    %rbp
    46bb:	41 5c                	pop    %r12
    46bd:	41 5d                	pop    %r13
    46bf:	41 5e                	pop    %r14
    46c1:	c3                   	ret
    46c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    46c8:	ba 69 63 00 00       	mov    $0x6369,%edx
    46cd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    46d5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    46da:	48 89 ee             	mov    %rbp,%rsi
    46dd:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    46e5:	48 89 c2             	mov    %rax,%rdx
    46e8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    46f0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    46fb:	e8 a0 dc ff ff       	call   23a0 <__memcpy_chk@plt>
    4700:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4705:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    470a:	48 8d 35 da 19 00 00 	lea    0x19da(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    4711:	48 29 d9             	sub    %rbx,%rcx
    4714:	ba 0b 00 00 00       	mov    $0xb,%edx
    4719:	e8 82 dc ff ff       	call   23a0 <__memcpy_chk@plt>
    471e:	48 89 e6             	mov    %rsp,%rsi
    4721:	4c 89 f7             	mov    %r14,%rdi
    4724:	e8 87 dc ff ff       	call   23b0 <stat@plt>
    4729:	83 f8 ff             	cmp    $0xffffffff,%eax
    472c:	0f 85 2d ff ff ff    	jne    465f <handle_get_method+0x8f>
    4732:	4c 89 f2             	mov    %r14,%rdx
    4735:	48 89 e9             	mov    %rbp,%rcx
    4738:	48 8d 35 b7 19 00 00 	lea    0x19b7(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    473f:	31 c0                	xor    %eax,%eax
    4741:	bf 01 00 00 00       	mov    $0x1,%edi
    4746:	e8 e5 dc ff ff       	call   2430 <__printf_chk@plt>
    474b:	48 8b 3d be 48 00 00 	mov    0x48be(%rip),%rdi        # 9010 <http_404_content>
    4752:	4c 89 ea             	mov    %r13,%rdx
    4755:	44 89 e6             	mov    %r12d,%esi
    4758:	e8 03 fd ff ff       	call   4460 <_send_static_string_content>
    475d:	e9 39 ff ff ff       	jmp    469b <handle_get_method+0xcb>
    4762:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4768:	bf 70 00 00 00       	mov    $0x70,%edi
    476d:	e8 7e dc ff ff       	call   23f0 <malloc@plt>
    4772:	48 89 c3             	mov    %rax,%rbx
    4775:	48 85 c0             	test   %rax,%rax
    4778:	74 5d                	je     47d7 <handle_get_method+0x207>
    477a:	44 89 60 08          	mov    %r12d,0x8(%rax)
    477e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4783:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4787:	4c 89 f7             	mov    %r14,%rdi
    478a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    4791:	e8 5a f5 ff ff       	call   3cf0 <send_headers>
    4796:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    479b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    479f:	4c 89 f7             	mov    %r14,%rdi
    47a2:	e8 79 fa ff ff       	call   4220 <copy_file_contents>
    47a7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    47ac:	4c 89 f2             	mov    %r14,%rdx
    47af:	31 c0                	xor    %eax,%eax
    47b1:	48 8d 35 56 19 00 00 	lea    0x1956(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    47b8:	bf 01 00 00 00       	mov    $0x1,%edi
    47bd:	e8 6e dc ff ff       	call   2430 <__printf_chk@plt>
    47c2:	4c 89 ee             	mov    %r13,%rsi
    47c5:	48 89 df             	mov    %rbx,%rdi
    47c8:	e8 13 fb ff ff       	call   42e0 <add_write_request>
    47cd:	e9 c9 fe ff ff       	jmp    469b <handle_get_method+0xcb>
    47d2:	e8 39 db ff ff       	call   2310 <__stack_chk_fail@plt>
    47d7:	48 8b 0d 42 48 00 00 	mov    0x4842(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    47de:	ba 28 00 00 00       	mov    $0x28,%edx
    47e3:	be 01 00 00 00       	mov    $0x1,%esi
    47e8:	48 8d 3d 31 1c 00 00 	lea    0x1c31(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    47ef:	e8 ac dc ff ff       	call   24a0 <fwrite@plt>
    47f4:	bf 01 00 00 00       	mov    $0x1,%edi
    47f9:	e8 82 dc ff ff       	call   2480 <exit@plt>
    47fe:	66 90                	xchg   %ax,%ax

0000000000004800 <handle_http_method>:
    4800:	f3 0f 1e fa          	endbr64
    4804:	41 57                	push   %r15
    4806:	41 56                	push   %r14
    4808:	4c 8d 35 76 18 00 00 	lea    0x1876(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
    480f:	41 55                	push   %r13
    4811:	49 89 d5             	mov    %rdx,%r13
    4814:	41 54                	push   %r12
    4816:	41 89 f4             	mov    %esi,%r12d
    4819:	4c 89 f6             	mov    %r14,%rsi
    481c:	55                   	push   %rbp
    481d:	53                   	push   %rbx
    481e:	48 83 ec 18          	sub    $0x18,%rsp
    4822:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    482b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4830:	31 c0                	xor    %eax,%eax
    4832:	49 89 e7             	mov    %rsp,%r15
    4835:	4c 89 fa             	mov    %r15,%rdx
    4838:	e8 23 db ff ff       	call   2360 <strtok_r@plt>
    483d:	48 0f be 18          	movsbq (%rax),%rbx
    4841:	48 89 c5             	mov    %rax,%rbp
    4844:	84 db                	test   %bl,%bl
    4846:	74 1d                	je     4865 <handle_http_method+0x65>
    4848:	e8 a3 dc ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    484d:	48 89 ea             	mov    %rbp,%rdx
    4850:	48 8b 08             	mov    (%rax),%rcx
    4853:	48 83 c2 01          	add    $0x1,%rdx
    4857:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    485a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    485d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4861:	84 db                	test   %bl,%bl
    4863:	75 eb                	jne    4850 <handle_http_method+0x50>
    4865:	4c 89 fa             	mov    %r15,%rdx
    4868:	4c 89 f6             	mov    %r14,%rsi
    486b:	31 ff                	xor    %edi,%edi
    486d:	e8 ee da ff ff       	call   2360 <strtok_r@plt>
    4872:	48 8d 35 ba 18 00 00 	lea    0x18ba(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    4879:	48 89 ef             	mov    %rbp,%rdi
    487c:	48 89 c3             	mov    %rax,%rbx
    487f:	e8 0c db ff ff       	call   2390 <strcmp@plt>
    4884:	4c 89 ea             	mov    %r13,%rdx
    4887:	44 89 e6             	mov    %r12d,%esi
    488a:	85 c0                	test   %eax,%eax
    488c:	75 2a                	jne    48b8 <handle_http_method+0xb8>
    488e:	48 89 df             	mov    %rbx,%rdi
    4891:	e8 3a fd ff ff       	call   45d0 <handle_get_method>
    4896:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    489b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    48a4:	75 20                	jne    48c6 <handle_http_method+0xc6>
    48a6:	48 83 c4 18          	add    $0x18,%rsp
    48aa:	5b                   	pop    %rbx
    48ab:	5d                   	pop    %rbp
    48ac:	41 5c                	pop    %r12
    48ae:	41 5d                	pop    %r13
    48b0:	41 5e                	pop    %r14
    48b2:	41 5f                	pop    %r15
    48b4:	c3                   	ret
    48b5:	0f 1f 00             	nopl   (%rax)
    48b8:	48 8b 3d 59 47 00 00 	mov    0x4759(%rip),%rdi        # 9018 <unimplemented_content>
    48bf:	e8 9c fb ff ff       	call   4460 <_send_static_string_content>
    48c4:	eb d0                	jmp    4896 <handle_http_method+0x96>
    48c6:	e8 45 da ff ff       	call   2310 <__stack_chk_fail@plt>
    48cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000048d0 <get_line>:
    48d0:	f3 0f 1e fa          	endbr64
    48d4:	85 d2                	test   %edx,%edx
    48d6:	7e 38                	jle    4910 <get_line+0x40>
    48d8:	48 63 d2             	movslq %edx,%rdx
    48db:	48 83 c7 01          	add    $0x1,%rdi
    48df:	48 01 f2             	add    %rsi,%rdx
    48e2:	eb 11                	jmp    48f5 <get_line+0x25>
    48e4:	0f 1f 40 00          	nopl   0x0(%rax)
    48e8:	48 83 c6 01          	add    $0x1,%rsi
    48ec:	48 83 c7 01          	add    $0x1,%rdi
    48f0:	48 39 d6             	cmp    %rdx,%rsi
    48f3:	74 1b                	je     4910 <get_line+0x40>
    48f5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    48f9:	88 06                	mov    %al,(%rsi)
    48fb:	3c 0d                	cmp    $0xd,%al
    48fd:	75 e9                	jne    48e8 <get_line+0x18>
    48ff:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4902:	75 e4                	jne    48e8 <get_line+0x18>
    4904:	c6 06 00             	movb   $0x0,(%rsi)
    4907:	31 c0                	xor    %eax,%eax
    4909:	c3                   	ret
    490a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4910:	b8 01 00 00 00       	mov    $0x1,%eax
    4915:	c3                   	ret
    4916:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004920 <handle_client_request>:
    4920:	f3 0f 1e fa          	endbr64
    4924:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    492b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    492f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4938:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4940:	31 c0                	xor    %eax,%eax
    4942:	49 89 e2             	mov    %rsp,%r10
    4945:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    494d:	4c 89 d0             	mov    %r10,%rax
    4950:	eb 13                	jmp    4965 <handle_client_request+0x45>
    4952:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4958:	48 83 c0 01          	add    $0x1,%rax
    495c:	48 83 c1 01          	add    $0x1,%rcx
    4960:	4c 39 c8             	cmp    %r9,%rax
    4963:	74 4b                	je     49b0 <handle_client_request+0x90>
    4965:	44 0f b6 01          	movzbl (%rcx),%r8d
    4969:	44 88 00             	mov    %r8b,(%rax)
    496c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4970:	75 e6                	jne    4958 <handle_client_request+0x38>
    4972:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4976:	75 e0                	jne    4958 <handle_client_request+0x38>
    4978:	c6 00 00             	movb   $0x0,(%rax)
    497b:	8b 47 08             	mov    0x8(%rdi),%eax
    497e:	48 89 f2             	mov    %rsi,%rdx
    4981:	4c 89 d7             	mov    %r10,%rdi
    4984:	89 c6                	mov    %eax,%esi
    4986:	e8 75 fe ff ff       	call   4800 <handle_http_method>
    498b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4993:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    499c:	75 39                	jne    49d7 <handle_client_request+0xb7>
    499e:	31 c0                	xor    %eax,%eax
    49a0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    49a7:	c3                   	ret
    49a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    49b0:	48 8b 0d 69 46 00 00 	mov    0x4669(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    49b7:	ba 12 00 00 00       	mov    $0x12,%edx
    49bc:	be 01 00 00 00       	mov    $0x1,%esi
    49c1:	48 8d 3d 6f 17 00 00 	lea    0x176f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    49c8:	e8 d3 da ff ff       	call   24a0 <fwrite@plt>
    49cd:	bf 01 00 00 00       	mov    $0x1,%edi
    49d2:	e8 a9 da ff ff       	call   2480 <exit@plt>
    49d7:	e8 34 d9 ff ff       	call   2310 <__stack_chk_fail@plt>
    49dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000049e0 <add_accept_request>:
    49e0:	f3 0f 1e fa          	endbr64
    49e4:	55                   	push   %rbp
    49e5:	53                   	push   %rbx
    49e6:	48 89 cb             	mov    %rcx,%rbx
    49e9:	48 83 ec 08          	sub    $0x8,%rsp
    49ed:	8b 41 44             	mov    0x44(%rcx),%eax
    49f0:	4c 8b 03             	mov    (%rbx),%r8
    49f3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    49f9:	83 c0 01             	add    $0x1,%eax
    49fc:	45 8b 08             	mov    (%r8),%r9d
    49ff:	f6 c1 02             	test   $0x2,%cl
    4a02:	74 00                	je     4a04 <add_accept_request+0x24>
    4a04:	41 89 c0             	mov    %eax,%r8d
    4a07:	45 29 c8             	sub    %r9d,%r8d
    4a0a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4a0e:	0f 82 58 db ff ff    	jb     256c <add_accept_request.cold>
    4a14:	c1 e9 0a             	shr    $0xa,%ecx
    4a17:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4a1a:	23 6b 58             	and    0x58(%rbx),%ebp
    4a1d:	89 43 44             	mov    %eax,0x44(%rbx)
    4a20:	83 e1 01             	and    $0x1,%ecx
    4a23:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4a27:	d3 e5                	shl    %cl,%ebp
    4a29:	48 c1 e5 06          	shl    $0x6,%rbp
    4a2d:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4a31:	89 7d 04             	mov    %edi,0x4(%rbp)
    4a34:	bf 10 00 00 00       	mov    $0x10,%edi
    4a39:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    4a40:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    4a44:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    4a48:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    4a50:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    4a58:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4a5c:	e8 8f d9 ff ff       	call   23f0 <malloc@plt>
    4a61:	48 89 df             	mov    %rbx,%rdi
    4a64:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    4a6a:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4a6e:	48 83 c4 08          	add    $0x8,%rsp
    4a72:	5b                   	pop    %rbx
    4a73:	5d                   	pop    %rbp
    4a74:	e9 a7 d8 ff ff       	jmp    2320 <io_uring_submit@plt>
    4a79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004a80 <io_thread>:
    4a80:	f3 0f 1e fa          	endbr64
    4a84:	41 57                	push   %r15
    4a86:	31 d2                	xor    %edx,%edx
    4a88:	41 56                	push   %r14
    4a8a:	41 55                	push   %r13
    4a8c:	41 54                	push   %r12
    4a8e:	55                   	push   %rbp
    4a8f:	48 89 fd             	mov    %rdi,%rbp
    4a92:	53                   	push   %rbx
    4a93:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4a9a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4aa3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4aab:	48 8b 47 40          	mov    0x40(%rdi),%rax
    4aaf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4ab4:	bf 00 01 00 00       	mov    $0x100,%edi
    4ab9:	48 89 de             	mov    %rbx,%rsi
    4abc:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4ac0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4ac5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4aca:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4acf:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4ad4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4adc:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4ae1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4ae9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4aee:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4af6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4afb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4b03:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4b08:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4b10:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4b15:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4b1d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4b25:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4b2d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4b35:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4b3d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4b45:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4b4d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4b55:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4b5d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4b65:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4b6d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4b74:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    4b7c:	e8 4f d8 ff ff       	call   23d0 <io_uring_queue_init@plt>
    4b81:	48 8b 7d 40          	mov    0x40(%rbp),%rdi
    4b85:	31 f6                	xor    %esi,%esi
    4b87:	e8 34 d9 ff ff       	call   24c0 <io_uring_register_eventfd@plt>
    4b8c:	31 d2                	xor    %edx,%edx
    4b8e:	be 01 00 00 00       	mov    $0x1,%esi
    4b93:	bf 02 00 00 00       	mov    $0x2,%edi
    4b98:	e8 73 d9 ff ff       	call   2510 <socket@plt>
    4b9d:	83 f8 ff             	cmp    $0xffffffff,%eax
    4ba0:	0f 84 08 da ff ff    	je     25ae <io_thread.cold+0x38>
    4ba6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4bab:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4bb1:	89 c7                	mov    %eax,%edi
    4bb3:	41 89 c4             	mov    %eax,%r12d
    4bb6:	ba 02 00 00 00       	mov    $0x2,%edx
    4bbb:	be 01 00 00 00       	mov    $0x1,%esi
    4bc0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    4bc8:	e8 13 d7 ff ff       	call   22e0 <setsockopt@plt>
    4bcd:	85 c0                	test   %eax,%eax
    4bcf:	0f 88 ad d9 ff ff    	js     2582 <io_thread.cold+0xc>
    4bd5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    4bda:	ba 10 00 00 00       	mov    $0x10,%edx
    4bdf:	44 89 e7             	mov    %r12d,%edi
    4be2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4beb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    4bf3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
    4bfb:	e8 40 d8 ff ff       	call   2440 <bind@plt>
    4c00:	85 c0                	test   %eax,%eax
    4c02:	0f 88 b2 d9 ff ff    	js     25ba <io_thread.cold+0x44>
    4c08:	be 0a 00 00 00       	mov    $0xa,%esi
    4c0d:	44 89 e7             	mov    %r12d,%edi
    4c10:	e8 eb d7 ff ff       	call   2400 <listen@plt>
    4c15:	85 c0                	test   %eax,%eax
    4c17:	0f 88 71 d9 ff ff    	js     258e <io_thread.cold+0x18>
    4c1d:	ba db 18 00 00       	mov    $0x18db,%edx
    4c22:	48 8d 35 53 15 00 00 	lea    0x1553(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4c29:	bf 01 00 00 00       	mov    $0x1,%edi
    4c2e:	31 c0                	xor    %eax,%eax
    4c30:	e8 fb d7 ff ff       	call   2430 <__printf_chk@plt>
    4c35:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4c3a:	48 89 d9             	mov    %rbx,%rcx
    4c3d:	44 89 e7             	mov    %r12d,%edi
    4c40:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4c45:	48 89 c6             	mov    %rax,%rsi
    4c48:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4c4d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    4c52:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    4c5a:	e8 81 fd ff ff       	call   49e0 <add_accept_request>
    4c5f:	bf 01 00 00 00       	mov    $0x1,%edi
    4c64:	be 10 00 00 00       	mov    $0x10,%esi
    4c69:	e8 12 d7 ff ff       	call   2380 <calloc@plt>
    4c6e:	bf 0a 00 00 00       	mov    $0xa,%edi
    4c73:	49 89 c5             	mov    %rax,%r13
    4c76:	e8 75 d7 ff ff       	call   23f0 <malloc@plt>
    4c7b:	48 85 c0             	test   %rax,%rax
    4c7e:	0f 84 ae 04 00 00    	je     5132 <io_thread+0x6b2>
    4c84:	49 89 45 00          	mov    %rax,0x0(%r13)
    4c88:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4c8f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4c96:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    4c9e:	8d 50 01             	lea    0x1(%rax),%edx
    4ca1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4ca6:	8b 30                	mov    (%rax),%esi
    4ca8:	f6 c1 02             	test   $0x2,%cl
    4cab:	0f 85 0f 04 00 00    	jne    50c0 <io_thread+0x640>
    4cb1:	89 d0                	mov    %edx,%eax
    4cb3:	29 f0                	sub    %esi,%eax
    4cb5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4cbc:	0f 82 e2 d8 ff ff    	jb     25a4 <io_thread.cold+0x2e>
    4cc2:	c1 e9 0a             	shr    $0xa,%ecx
    4cc5:	48 8d 75 48          	lea    0x48(%rbp),%rsi
    4cc9:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4ccd:	48 89 df             	mov    %rbx,%rdi
    4cd0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4cd7:	83 e1 01             	and    $0x1,%ecx
    4cda:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4ce1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4ce8:	d3 e0                	shl    %cl,%eax
    4cea:	8b 55 48             	mov    0x48(%rbp),%edx
    4ced:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4cf2:	48 c1 e0 06          	shl    $0x6,%rax
    4cf6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4cfe:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4d04:	89 50 04             	mov    %edx,0x4(%rax)
    4d07:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4d0f:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4d13:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    4d1b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4d23:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4d27:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4d2b:	e8 f0 d5 ff ff       	call   2320 <io_uring_submit@plt>
    4d30:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
    4d34:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4d39:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4d41:	0f 85 d7 01 00 00    	jne    4f1e <io_thread+0x49e>
    4d47:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4d4c:	4d 89 ce             	mov    %r9,%r14
    4d4f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4d54:	0f 1f 40 00          	nopl   0x0(%rax)
    4d58:	48 8d 3d 33 14 00 00 	lea    0x1433(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4d5f:	e8 6c d5 ff ff       	call   22d0 <puts@plt>
    4d64:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4d6b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    4d72:	c1 e9 0b             	shr    $0xb,%ecx
    4d75:	83 e1 01             	and    $0x1,%ecx
    4d78:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4d80:	8b 00                	mov    (%rax),%eax
    4d82:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4d8a:	8b 16                	mov    (%rsi),%edx
    4d8c:	39 d0                	cmp    %edx,%eax
    4d8e:	74 36                	je     4dc6 <io_thread+0x346>
    4d90:	89 f8                	mov    %edi,%eax
    4d92:	21 d0                	and    %edx,%eax
    4d94:	d3 e0                	shl    %cl,%eax
    4d96:	48 c1 e0 04          	shl    $0x4,%rax
    4d9a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    4da2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4daa:	0f 85 a8 01 00 00    	jne    4f58 <io_thread+0x4d8>
    4db0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4db4:	0f 85 0e 03 00 00    	jne    50c8 <io_thread+0x648>
    4dba:	8b 40 08             	mov    0x8(%rax),%eax
    4dbd:	83 c2 01             	add    $0x1,%edx
    4dc0:	89 16                	mov    %edx,(%rsi)
    4dc2:	85 c0                	test   %eax,%eax
    4dc4:	79 b2                	jns    4d78 <io_thread+0x2f8>
    4dc6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    4dcf:	90                   	nop
    4dd0:	45 31 c0             	xor    %r8d,%r8d
    4dd3:	31 d2                	xor    %edx,%edx
    4dd5:	b9 01 00 00 00       	mov    $0x1,%ecx
    4dda:	4c 89 f6             	mov    %r14,%rsi
    4ddd:	48 89 df             	mov    %rbx,%rdi
    4de0:	e8 3b d6 ff ff       	call   2420 <__io_uring_get_cqe@plt>
    4de5:	41 89 c7             	mov    %eax,%r15d
    4de8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4ded:	48 83 38 01          	cmpq   $0x1,(%rax)
    4df1:	0f 84 e1 02 00 00    	je     50d8 <io_thread+0x658>
    4df7:	48 8d 3d ba 13 00 00 	lea    0x13ba(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4dfe:	e8 cd d4 ff ff       	call   22d0 <puts@plt>
    4e03:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4e08:	4c 8b 22             	mov    (%rdx),%r12
    4e0b:	45 85 ff             	test   %r15d,%r15d
    4e0e:	0f 88 62 d7 ff ff    	js     2576 <io_thread.cold>
    4e14:	8b 42 08             	mov    0x8(%rdx),%eax
    4e17:	45 8b 04 24          	mov    (%r12),%r8d
    4e1b:	85 c0                	test   %eax,%eax
    4e1d:	0f 88 d5 02 00 00    	js     50f8 <io_thread+0x678>
    4e23:	41 83 f8 01          	cmp    $0x1,%r8d
    4e27:	0f 84 7b 01 00 00    	je     4fa8 <io_thread+0x528>
    4e2d:	41 83 f8 02          	cmp    $0x2,%r8d
    4e31:	0f 84 a1 01 00 00    	je     4fd8 <io_thread+0x558>
    4e37:	45 85 c0             	test   %r8d,%r8d
    4e3a:	0f 85 50 01 00 00    	jne    4f90 <io_thread+0x510>
    4e40:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    4e45:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    4e4a:	48 89 d9             	mov    %rbx,%rcx
    4e4d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4e51:	e8 8a fb ff ff       	call   49e0 <add_accept_request>
    4e56:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4e5b:	48 89 de             	mov    %rbx,%rsi
    4e5e:	8b 78 08             	mov    0x8(%rax),%edi
    4e61:	e8 1a f5 ff ff       	call   4380 <add_read_request>
    4e66:	4c 89 e7             	mov    %r12,%rdi
    4e69:	e8 42 d4 ff ff       	call   22b0 <free@plt>
    4e6e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4e73:	48 85 c0             	test   %rax,%rax
    4e76:	0f 85 14 01 00 00    	jne    4f90 <io_thread+0x510>
    4e7c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4e83:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4e8a:	8d 50 01             	lea    0x1(%rax),%edx
    4e8d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4e92:	8b 30                	mov    (%rax),%esi
    4e94:	f6 c1 02             	test   $0x2,%cl
    4e97:	74 00                	je     4e99 <io_thread+0x419>
    4e99:	89 d0                	mov    %edx,%eax
    4e9b:	29 f0                	sub    %esi,%eax
    4e9d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4ea4:	0f 82 f0 d6 ff ff    	jb     259a <io_thread.cold+0x24>
    4eaa:	c1 e9 0a             	shr    $0xa,%ecx
    4ead:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    4eb2:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4eb6:	48 89 df             	mov    %rbx,%rdi
    4eb9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4ec0:	83 e1 01             	and    $0x1,%ecx
    4ec3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4eca:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4ed1:	d3 e0                	shl    %cl,%eax
    4ed3:	8b 55 48             	mov    0x48(%rbp),%edx
    4ed6:	48 c1 e0 06          	shl    $0x6,%rax
    4eda:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4ee2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4ee8:	89 50 04             	mov    %edx,0x4(%rax)
    4eeb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4ef3:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4ef7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    4eff:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4f07:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4f0b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4f0f:	e8 0c d4 ff ff       	call   2320 <io_uring_submit@plt>
    4f14:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
    4f18:	0f 84 3a fe ff ff    	je     4d58 <io_thread+0x2d8>
    4f1e:	48 8d 3d cc 12 00 00 	lea    0x12cc(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    4f25:	e8 a6 d3 ff ff       	call   22d0 <puts@plt>
    4f2a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    4f32:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4f3b:	0f 85 18 02 00 00    	jne    5159 <io_thread+0x6d9>
    4f41:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    4f48:	31 c0                	xor    %eax,%eax
    4f4a:	5b                   	pop    %rbx
    4f4b:	5d                   	pop    %rbp
    4f4c:	41 5c                	pop    %r12
    4f4e:	41 5d                	pop    %r13
    4f50:	41 5e                	pop    %r14
    4f52:	41 5f                	pop    %r15
    4f54:	c3                   	ret
    4f55:	0f 1f 00             	nopl   (%rax)
    4f58:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    4f5d:	48 85 c0             	test   %rax,%rax
    4f60:	0f 84 6a fe ff ff    	je     4dd0 <io_thread+0x350>
    4f66:	48 83 38 01          	cmpq   $0x1,(%rax)
    4f6a:	0f 84 68 01 00 00    	je     50d8 <io_thread+0x658>
    4f70:	48 8d 3d 41 12 00 00 	lea    0x1241(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4f77:	e8 54 d3 ff ff       	call   22d0 <puts@plt>
    4f7c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4f81:	4c 8b 22             	mov    (%rdx),%r12
    4f84:	e9 8b fe ff ff       	jmp    4e14 <io_thread+0x394>
    4f89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4f90:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4f98:	8b 02                	mov    (%rdx),%eax
    4f9a:	83 c0 01             	add    $0x1,%eax
    4f9d:	89 02                	mov    %eax,(%rdx)
    4f9f:	e9 d8 fe ff ff       	jmp    4e7c <io_thread+0x3fc>
    4fa4:	0f 1f 40 00          	nopl   0x0(%rax)
    4fa8:	85 c0                	test   %eax,%eax
    4faa:	75 74                	jne    5020 <io_thread+0x5a0>
    4fac:	48 8b 0d 6d 40 00 00 	mov    0x406d(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4fb3:	ba 0f 00 00 00       	mov    $0xf,%edx
    4fb8:	be 01 00 00 00       	mov    $0x1,%esi
    4fbd:	48 8d 3d 1d 12 00 00 	lea    0x121d(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    4fc4:	e8 d7 d4 ff ff       	call   24a0 <fwrite@plt>
    4fc9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4fce:	e9 a0 fe ff ff       	jmp    4e73 <io_thread+0x3f3>
    4fd3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4fd8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    4fdd:	45 31 ff             	xor    %r15d,%r15d
    4fe0:	85 c0                	test   %eax,%eax
    4fe2:	7e 20                	jle    5004 <io_thread+0x584>
    4fe4:	0f 1f 40 00          	nopl   0x0(%rax)
    4fe8:	4c 89 f8             	mov    %r15,%rax
    4feb:	49 83 c7 01          	add    $0x1,%r15
    4fef:	48 c1 e0 04          	shl    $0x4,%rax
    4ff3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    4ff8:	e8 b3 d2 ff ff       	call   22b0 <free@plt>
    4ffd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5002:	7f e4                	jg     4fe8 <io_thread+0x568>
    5004:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5009:	e8 42 d3 ff ff       	call   2350 <close@plt>
    500e:	4c 89 e7             	mov    %r12,%rdi
    5011:	e8 9a d2 ff ff       	call   22b0 <free@plt>
    5016:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    501b:	e9 53 fe ff ff       	jmp    4e73 <io_thread+0x3f3>
    5020:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5025:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    502a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5032:	eb 11                	jmp    5045 <io_thread+0x5c5>
    5034:	0f 1f 40 00          	nopl   0x0(%rax)
    5038:	48 83 c0 01          	add    $0x1,%rax
    503c:	48 83 c2 01          	add    $0x1,%rdx
    5040:	48 39 c6             	cmp    %rax,%rsi
    5043:	74 4b                	je     5090 <io_thread+0x610>
    5045:	0f b6 0a             	movzbl (%rdx),%ecx
    5048:	88 08                	mov    %cl,(%rax)
    504a:	80 f9 0d             	cmp    $0xd,%cl
    504d:	75 e9                	jne    5038 <io_thread+0x5b8>
    504f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5053:	75 e3                	jne    5038 <io_thread+0x5b8>
    5055:	c6 00 00             	movb   $0x0,(%rax)
    5058:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    505d:	48 89 da             	mov    %rbx,%rdx
    5060:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5065:	e8 96 f7 ff ff       	call   4800 <handle_http_method>
    506a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    506f:	e8 3c d2 ff ff       	call   22b0 <free@plt>
    5074:	4c 89 e7             	mov    %r12,%rdi
    5077:	e8 34 d2 ff ff       	call   22b0 <free@plt>
    507c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5081:	e9 ed fd ff ff       	jmp    4e73 <io_thread+0x3f3>
    5086:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5090:	48 8b 0d 89 3f 00 00 	mov    0x3f89(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5097:	ba 12 00 00 00       	mov    $0x12,%edx
    509c:	be 01 00 00 00       	mov    $0x1,%esi
    50a1:	48 8d 3d 8f 10 00 00 	lea    0x108f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    50a8:	e8 f3 d3 ff ff       	call   24a0 <fwrite@plt>
    50ad:	bf 01 00 00 00       	mov    $0x1,%edi
    50b2:	e8 c9 d3 ff ff       	call   2480 <exit@plt>
    50b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    50c0:	e9 ec fb ff ff       	jmp    4cb1 <io_thread+0x231>
    50c5:	0f 1f 00             	nopl   (%rax)
    50c8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    50cd:	e9 94 fe ff ff       	jmp    4f66 <io_thread+0x4e6>
    50d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    50d8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    50e0:	48 8d 3d bd 10 00 00 	lea    0x10bd(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    50e7:	8b 02                	mov    (%rdx),%eax
    50e9:	83 c0 01             	add    $0x1,%eax
    50ec:	89 02                	mov    %eax,(%rdx)
    50ee:	e8 dd d1 ff ff       	call   22d0 <puts@plt>
    50f3:	e9 26 fe ff ff       	jmp    4f1e <io_thread+0x49e>
    50f8:	f7 d8                	neg    %eax
    50fa:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    50ff:	89 c7                	mov    %eax,%edi
    5101:	e8 da d3 ff ff       	call   24e0 <strerror@plt>
    5106:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    510b:	be 01 00 00 00       	mov    $0x1,%esi
    5110:	48 8b 3d 09 3f 00 00 	mov    0x3f09(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    5117:	48 89 c1             	mov    %rax,%rcx
    511a:	48 8d 15 2f 13 00 00 	lea    0x132f(%rip),%rdx        # 6450 <_IO_stdin_used+0x450>
    5121:	31 c0                	xor    %eax,%eax
    5123:	e8 88 d3 ff ff       	call   24b0 <__fprintf_chk@plt>
    5128:	bf 01 00 00 00       	mov    $0x1,%edi
    512d:	e8 4e d3 ff ff       	call   2480 <exit@plt>
    5132:	48 8b 0d e7 3e 00 00 	mov    0x3ee7(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5139:	ba 28 00 00 00       	mov    $0x28,%edx
    513e:	be 01 00 00 00       	mov    $0x1,%esi
    5143:	48 8d 3d d6 12 00 00 	lea    0x12d6(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    514a:	e8 51 d3 ff ff       	call   24a0 <fwrite@plt>
    514f:	bf 01 00 00 00       	mov    $0x1,%edi
    5154:	e8 27 d3 ff ff       	call   2480 <exit@plt>
    5159:	e8 b2 d1 ff ff       	call   2310 <__stack_chk_fail@plt>
    515e:	66 90                	xchg   %ax,%ax

0000000000005160 <receive>:
    5160:	f3 0f 1e fa          	endbr64
    5164:	8b 87 24 02 00 00    	mov    0x224(%rdi),%eax
    516a:	85 c0                	test   %eax,%eax
    516c:	0f 8e ed 00 00 00    	jle    525f <receive+0xff>
    5172:	41 54                	push   %r12
    5174:	4c 63 e0             	movslq %eax,%r12
    5177:	48 89 fa             	mov    %rdi,%rdx
    517a:	55                   	push   %rbp
    517b:	49 c1 e4 09          	shl    $0x9,%r12
    517f:	53                   	push   %rbx
    5180:	48 8b b7 58 02 00 00 	mov    0x258(%rdi),%rsi
    5187:	49 01 f4             	add    %rsi,%r12
    518a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5190:	48 8b 2e             	mov    (%rsi),%rbp
    5193:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
    5197:	48 85 ff             	test   %rdi,%rdi
    519a:	0f 8e a0 00 00 00    	jle    5240 <receive+0xe0>
    51a0:	48 8b 8a 60 02 00 00 	mov    0x260(%rdx),%rcx
    51a7:	4c 8b 45 00          	mov    0x0(%rbp),%r8
    51ab:	4c 63 1a             	movslq (%rdx),%r11
    51ae:	49 89 c9             	mov    %rcx,%r9
    51b1:	48 8d 41 01          	lea    0x1(%rcx),%rax
    51b5:	49 f7 d9             	neg    %r9
    51b8:	48 01 c7             	add    %rax,%rdi
    51bb:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
    51bf:	4c 8b 8a 80 01 00 00 	mov    0x180(%rdx),%r9
    51c6:	4c 8b 86 80 01 00 00 	mov    0x180(%rsi),%r8
    51cd:	49 29 c9             	sub    %rcx,%r9
    51d0:	49 29 c8             	sub    %rcx,%r8
    51d3:	eb 0c                	jmp    51e1 <receive+0x81>
    51d5:	0f 1f 00             	nopl   (%rax)
    51d8:	48 83 c0 01          	add    $0x1,%rax
    51dc:	48 39 c7             	cmp    %rax,%rdi
    51df:	74 5f                	je     5240 <receive+0xe0>
    51e1:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    51e5:	48 89 82 60 02 00 00 	mov    %rax,0x260(%rdx)
    51ec:	48 89 8a 80 01 00 00 	mov    %rcx,0x180(%rdx)
    51f3:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    51f7:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
    51fe:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5203:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5207:	75 cf                	jne    51d8 <receive+0x78>
    5209:	48 63 9a 20 02 00 00 	movslq 0x220(%rdx),%rbx
    5210:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5214:	75 c2                	jne    51d8 <receive+0x78>
    5216:	bf 01 00 00 00       	mov    $0x1,%edi
    521b:	b9 01 00 00 00       	mov    $0x1,%ecx
    5220:	ba 01 00 00 00       	mov    $0x1,%edx
    5225:	31 c0                	xor    %eax,%eax
    5227:	48 8d 35 4a 12 00 00 	lea    0x124a(%rip),%rsi        # 6478 <_IO_stdin_used+0x478>
    522e:	e8 fd d1 ff ff       	call   2430 <__printf_chk@plt>
    5233:	bf 01 00 00 00       	mov    $0x1,%edi
    5238:	e8 43 d2 ff ff       	call   2480 <exit@plt>
    523d:	0f 1f 00             	nopl   (%rax)
    5240:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    5247:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    524f:	49 39 f4             	cmp    %rsi,%r12
    5252:	0f 85 38 ff ff ff    	jne    5190 <receive+0x30>
    5258:	5b                   	pop    %rbx
    5259:	31 c0                	xor    %eax,%eax
    525b:	5d                   	pop    %rbp
    525c:	41 5c                	pop    %r12
    525e:	c3                   	ret
    525f:	31 c0                	xor    %eax,%eax
    5261:	c3                   	ret
    5262:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    526d:	0f 1f 00             	nopl   (%rax)

0000000000005270 <barriered_work>:
    5270:	f3 0f 1e fa          	endbr64
    5274:	41 57                	push   %r15
    5276:	41 56                	push   %r14
    5278:	41 55                	push   %r13
    527a:	41 54                	push   %r12
    527c:	55                   	push   %rbp
    527d:	53                   	push   %rbx
    527e:	48 89 fb             	mov    %rdi,%rbx
    5281:	48 83 ec 28          	sub    $0x28,%rsp
    5285:	8b 07                	mov    (%rdi),%eax
    5287:	39 87 20 02 00 00    	cmp    %eax,0x220(%rdi)
    528d:	0f 84 5d 01 00 00    	je     53f0 <barriered_work+0x180>
    5293:	e8 c8 fe ff ff       	call   5160 <receive>
    5298:	83 bb 30 02 00 00 01 	cmpl   $0x1,0x230(%rbx)
    529f:	75 1b                	jne    52bc <barriered_work+0x4c>
    52a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    52a8:	48 83 83 80 01 00 00 01 	addq   $0x1,0x180(%rbx)
    52b0:	0f ae f8             	sfence
    52b3:	83 bb 30 02 00 00 01 	cmpl   $0x1,0x230(%rbx)
    52ba:	74 ec                	je     52a8 <barriered_work+0x38>
    52bc:	83 bb 68 02 00 00 01 	cmpl   $0x1,0x268(%rbx)
    52c3:	74 14                	je     52d9 <barriered_work+0x69>
    52c5:	0f ae f0             	mfence
    52c8:	48 83 c4 28          	add    $0x28,%rsp
    52cc:	31 c0                	xor    %eax,%eax
    52ce:	5b                   	pop    %rbx
    52cf:	5d                   	pop    %rbp
    52d0:	41 5c                	pop    %r12
    52d2:	41 5d                	pop    %r13
    52d4:	41 5e                	pop    %r14
    52d6:	41 5f                	pop    %r15
    52d8:	c3                   	ret
    52d9:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    52df:	85 c0                	test   %eax,%eax
    52e1:	7e e2                	jle    52c5 <barriered_work+0x55>
    52e3:	8b bb 20 02 00 00    	mov    0x220(%rbx),%edi
    52e9:	4c 63 f8             	movslq %eax,%r15
    52ec:	48 8d 83 70 02 00 00 	lea    0x270(%rbx),%rax
    52f3:	31 d2                	xor    %edx,%edx
    52f5:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    52fa:	48 8d 83 78 02 00 00 	lea    0x278(%rbx),%rax
    5301:	89 7c 24 04          	mov    %edi,0x4(%rsp)
    5305:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    530a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5310:	39 54 24 04          	cmp    %edx,0x4(%rsp)
    5314:	0f 84 bc 00 00 00    	je     53d6 <barriered_work+0x166>
    531a:	49 89 d0             	mov    %rdx,%r8
    531d:	49 c1 e0 09          	shl    $0x9,%r8
    5321:	4c 03 83 58 02 00 00 	add    0x258(%rbx),%r8
    5328:	4d 8b 88 80 00 00 00 	mov    0x80(%r8),%r9
    532f:	4d 8b 59 08          	mov    0x8(%r9),%r11
    5333:	49 63 79 10          	movslq 0x10(%r9),%rdi
    5337:	49 39 fb             	cmp    %rdi,%r11
    533a:	0f 8d 96 00 00 00    	jge    53d6 <barriered_work+0x166>
    5340:	49 89 fa             	mov    %rdi,%r10
    5343:	4c 8b b3 80 01 00 00 	mov    0x180(%rbx),%r14
    534a:	49 8b a8 00 01 00 00 	mov    0x100(%r8),%rbp
    5351:	4d 29 da             	sub    %r11,%r10
    5354:	49 8b 09             	mov    (%r9),%rcx
    5357:	49 8d 42 ff          	lea    -0x1(%r10),%rax
    535b:	48 83 f8 02          	cmp    $0x2,%rax
    535f:	0f 86 93 02 00 00    	jbe    55f8 <barriered_work+0x388>
    5365:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    536d:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    5375:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5379:	4c 8d 2c 31          	lea    (%rcx,%rsi,1),%r13
    537d:	4c 39 6c 24 08       	cmp    %r13,0x8(%rsp)
    5382:	0f 83 f8 01 00 00    	jae    5580 <barriered_work+0x310>
    5388:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    538d:	4d 39 ec             	cmp    %r13,%r12
    5390:	0f 83 ea 01 00 00    	jae    5580 <barriered_work+0x310>
    5396:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    539a:	48 01 ce             	add    %rcx,%rsi
    539d:	0f 1f 00             	nopl   (%rax)
    53a0:	48 8b 83 70 02 00 00 	mov    0x270(%rbx),%rax
    53a7:	49 83 c3 08          	add    $0x8,%r11
    53ab:	49 89 43 f8          	mov    %rax,-0x8(%r11)
    53af:	4c 39 de             	cmp    %r11,%rsi
    53b2:	75 ec                	jne    53a0 <barriered_work+0x130>
    53b4:	0f 1f 40 00          	nopl   0x0(%rax)
    53b8:	4b 8d 34 16          	lea    (%r14,%r10,1),%rsi
    53bc:	4c 01 d5             	add    %r10,%rbp
    53bf:	48 89 b3 80 01 00 00 	mov    %rsi,0x180(%rbx)
    53c6:	49 89 a8 00 01 00 00 	mov    %rbp,0x100(%r8)
    53cd:	49 89 79 08          	mov    %rdi,0x8(%r9)
    53d1:	48 89 44 f9 f8       	mov    %rax,-0x8(%rcx,%rdi,8)
    53d6:	48 83 c2 01          	add    $0x1,%rdx
    53da:	4c 39 fa             	cmp    %r15,%rdx
    53dd:	0f 85 2d ff ff ff    	jne    5310 <barriered_work+0xa0>
    53e3:	e9 dd fe ff ff       	jmp    52c5 <barriered_work+0x55>
    53e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    53f0:	e8 6b fd ff ff       	call   5160 <receive>
    53f5:	8b 8b 24 02 00 00    	mov    0x224(%rbx),%ecx
    53fb:	8b 03                	mov    (%rbx),%eax
    53fd:	85 c9                	test   %ecx,%ecx
    53ff:	0f 8e 96 00 00 00    	jle    549b <barriered_work+0x22b>
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
    5420:	49 c1 e3 09          	shl    $0x9,%r11
    5424:	31 ff                	xor    %edi,%edi
    5426:	48 98                	cltq
    5428:	4c 8d 0c 80          	lea    (%rax,%rax,4),%r9
    542c:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    5433:	49 c1 e1 07          	shl    $0x7,%r9
    5437:	4c 8b 60 10          	mov    0x10(%rax),%r12
    543b:	49 83 c4 20          	add    $0x20,%r12
    543f:	4d 89 e2             	mov    %r12,%r10
    5442:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5448:	49 8b 02             	mov    (%r10),%rax
    544b:	4c 89 e2             	mov    %r12,%rdx
    544e:	48 8b 84 28 58 02 00 00 	mov    0x258(%rax,%rbp,1),%rax
    5456:	4d 8d 04 03          	lea    (%r11,%rax,1),%r8
    545a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5460:	48 8b 0a             	mov    (%rdx),%rcx
    5463:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    546a:	48 05 00 02 00 00    	add    $0x200,%rax
    5470:	48 81 c2 98 00 00 00 	add    $0x98,%rdx
    5477:	4a 8b 8c 09 58 02 00 00 	mov    0x258(%rcx,%r9,1),%rcx
    547f:	48 89 34 39          	mov    %rsi,(%rcx,%rdi,1)
    5483:	49 39 c0             	cmp    %rax,%r8
    5486:	75 d8                	jne    5460 <barriered_work+0x1f0>
    5488:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    548f:	49 81 c2 98 00 00 00 	add    $0x98,%r10
    5496:	4c 39 df             	cmp    %r11,%rdi
    5499:	75 ad                	jne    5448 <barriered_work+0x1d8>
    549b:	0f ae f0             	mfence
    549e:	48 8b b3 48 02 00 00 	mov    0x248(%rbx),%rsi
    54a5:	31 ff                	xor    %edi,%edi
    54a7:	48 c1 e6 05          	shl    $0x5,%rsi
    54ab:	48 03 b3 38 02 00 00 	add    0x238(%rbx),%rsi
    54b2:	e8 39 ce ff ff       	call   22f0 <clock_gettime@plt>
    54b7:	48 8b 93 18 02 00 00 	mov    0x218(%rbx),%rdx
    54be:	83 bb 30 02 00 00 01 	cmpl   $0x1,0x230(%rbx)
    54c5:	48 8b 42 30          	mov    0x30(%rdx),%rax
    54c9:	8b 78 10             	mov    0x10(%rax),%edi
    54cc:	8d 6f 01             	lea    0x1(%rdi),%ebp
    54cf:	89 68 10             	mov    %ebp,0x10(%rax)
    54d2:	74 13                	je     54e7 <barriered_work+0x277>
    54d4:	eb 6d                	jmp    5543 <barriered_work+0x2d3>
    54d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    54e0:	48 8b 93 18 02 00 00 	mov    0x218(%rbx),%rdx
    54e7:	48 63 83 20 02 00 00 	movslq 0x220(%rbx),%rax
    54ee:	48 83 83 80 01 00 00 01 	addq   $0x1,0x180(%rbx)
    54f6:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    54fa:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    54fe:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    5502:	48 63 13             	movslq (%rbx),%rdx
    5505:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    5509:	48 8d 3c 92          	lea    (%rdx,%rdx,4),%rdi
    550d:	48 c1 e7 07          	shl    $0x7,%rdi
    5511:	48 03 78 20          	add    0x20(%rax),%rdi
    5515:	ff 93 10 02 00 00    	call   *0x210(%rbx)
    551b:	0f ae f8             	sfence
    551e:	83 bb 30 02 00 00 01 	cmpl   $0x1,0x230(%rbx)
    5525:	74 b9                	je     54e0 <barriered_work+0x270>
    5527:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    552e:	48 8b 40 30          	mov    0x30(%rax),%rax
    5532:	3b 68 10             	cmp    0x10(%rax),%ebp
    5535:	74 0c                	je     5543 <barriered_work+0x2d3>
    5537:	48 8d 3d c6 0c 00 00 	lea    0xcc6(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    553e:	e8 8d cd ff ff       	call   22d0 <puts@plt>
    5543:	48 8b b3 48 02 00 00 	mov    0x248(%rbx),%rsi
    554a:	31 ff                	xor    %edi,%edi
    554c:	48 c1 e6 05          	shl    $0x5,%rsi
    5550:	48 03 b3 38 02 00 00 	add    0x238(%rbx),%rsi
    5557:	48 83 c6 10          	add    $0x10,%rsi
    555b:	e8 90 cd ff ff       	call   22f0 <clock_gettime@plt>
    5560:	48 8b 83 48 02 00 00 	mov    0x248(%rbx),%rax
    5567:	48 83 c0 01          	add    $0x1,%rax
    556b:	48 99                	cqto
    556d:	48 f7 bb 40 02 00 00 	idivq  0x240(%rbx)
    5574:	48 89 93 48 02 00 00 	mov    %rdx,0x248(%rbx)
    557b:	e9 45 fd ff ff       	jmp    52c5 <barriered_work+0x55>
    5580:	48 8b 83 70 02 00 00 	mov    0x270(%rbx),%rax
    5587:	4d 89 d5             	mov    %r10,%r13
    558a:	4c 89 e6             	mov    %r12,%rsi
    558d:	49 d1 ed             	shr    %r13
    5590:	49 c1 e5 04          	shl    $0x4,%r13
    5594:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5599:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
    559e:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    55a2:	4d 01 e5             	add    %r12,%r13
    55a5:	f6 44 24 18 10       	testb  $0x10,0x18(%rsp)
    55aa:	74 14                	je     55c0 <barriered_work+0x350>
    55ac:	48 83 c6 10          	add    $0x10,%rsi
    55b0:	41 0f 11 04 24       	movups %xmm0,(%r12)
    55b5:	49 39 f5             	cmp    %rsi,%r13
    55b8:	74 16                	je     55d0 <barriered_work+0x360>
    55ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    55c0:	0f 11 06             	movups %xmm0,(%rsi)
    55c3:	48 83 c6 20          	add    $0x20,%rsi
    55c7:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
    55cb:	49 39 f5             	cmp    %rsi,%r13
    55ce:	75 f0                	jne    55c0 <barriered_work+0x350>
    55d0:	4c 89 d6             	mov    %r10,%rsi
    55d3:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    55d7:	4c 01 de             	add    %r11,%rsi
    55da:	41 f6 c2 01          	test   $0x1,%r10b
    55de:	0f 84 d4 fd ff ff    	je     53b8 <barriered_work+0x148>
    55e4:	48 8b 83 70 02 00 00 	mov    0x270(%rbx),%rax
    55eb:	48 89 04 f1          	mov    %rax,(%rcx,%rsi,8)
    55ef:	e9 c4 fd ff ff       	jmp    53b8 <barriered_work+0x148>
    55f4:	0f 1f 40 00          	nopl   0x0(%rax)
    55f8:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5600:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    5608:	e9 89 fd ff ff       	jmp    5396 <barriered_work+0x126>
    560d:	0f 1f 00             	nopl   (%rax)

0000000000005610 <barriered_work_ingest>:
    5610:	f3 0f 1e fa          	endbr64
    5614:	48 83 ec 08          	sub    $0x8,%rsp
    5618:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    561f:	48 8b 40 38          	mov    0x38(%rax),%rax
    5623:	48 63 10             	movslq (%rax),%rdx
    5626:	85 d2                	test   %edx,%edx
    5628:	7e 2c                	jle    5656 <barriered_work_ingest+0x46>
    562a:	48 8b 40 08          	mov    0x8(%rax),%rax
    562e:	48 c1 e2 04          	shl    $0x4,%rdx
    5632:	48 01 c2             	add    %rax,%rdx
    5635:	0f 1f 00             	nopl   (%rax)
    5638:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    563c:	75 0f                	jne    564d <barriered_work_ingest+0x3d>
    563e:	48 83 87 50 02 00 00 01 	addq   $0x1,0x250(%rdi)
    5646:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    564d:	48 83 c0 10          	add    $0x10,%rax
    5651:	48 39 d0             	cmp    %rdx,%rax
    5654:	75 e2                	jne    5638 <barriered_work_ingest+0x28>
    5656:	0f ae f0             	mfence
    5659:	e8 12 fc ff ff       	call   5270 <barriered_work>
    565e:	31 c0                	xor    %eax,%eax
    5660:	48 83 c4 08          	add    $0x8,%rsp
    5664:	c3                   	ret
    5665:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005670 <barriered_nulltask>:
    5670:	f3 0f 1e fa          	endbr64
    5674:	31 c0                	xor    %eax,%eax
    5676:	c3                   	ret
    5677:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005680 <barriered_steal>:
    5680:	f3 0f 1e fa          	endbr64
    5684:	31 c0                	xor    %eax,%eax
    5686:	c3                   	ret
    5687:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005690 <after>:
    5690:	f3 0f 1e fa          	endbr64
    5694:	31 c0                	xor    %eax,%eax
    5696:	48 39 d7             	cmp    %rdx,%rdi
    5699:	7e 08                	jle    56a3 <after+0x13>
    569b:	31 c0                	xor    %eax,%eax
    569d:	48 39 ce             	cmp    %rcx,%rsi
    56a0:	0f 9f c0             	setg   %al
    56a3:	c3                   	ret
    56a4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    56af:	90                   	nop

00000000000056b0 <within>:
    56b0:	f3 0f 1e fa          	endbr64
    56b4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    56b9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    56be:	31 c0                	xor    %eax,%eax
    56c0:	48 39 d7             	cmp    %rdx,%rdi
    56c3:	7f 18                	jg     56dd <within+0x2d>
    56c5:	4d 39 d8             	cmp    %r11,%r8
    56c8:	0f 9e c2             	setle  %dl
    56cb:	48 39 ce             	cmp    %rcx,%rsi
    56ce:	0f 9e c0             	setle  %al
    56d1:	21 c2                	and    %eax,%edx
    56d3:	31 c0                	xor    %eax,%eax
    56d5:	4d 39 d1             	cmp    %r10,%r9
    56d8:	0f 9e c0             	setle  %al
    56db:	21 d0                	and    %edx,%eax
    56dd:	c3                   	ret
    56de:	66 90                	xchg   %ax,%ax

00000000000056e0 <overlap>:
    56e0:	f3 0f 1e fa          	endbr64
    56e4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    56e9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    56ee:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    56f3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    56f8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    56fd:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
    5702:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5707:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    570c:	48 39 fe             	cmp    %rdi,%rsi
    570f:	7d 2f                	jge    5740 <overlap+0x60>
    5711:	48 39 ca             	cmp    %rcx,%rdx
    5714:	7d 62                	jge    5778 <overlap+0x98>
    5716:	4d 39 da             	cmp    %r11,%r10
    5719:	7d 0e                	jge    5729 <overlap+0x49>
    571b:	b8 01 00 00 00       	mov    $0x1,%eax
    5720:	4d 39 c1             	cmp    %r8,%r9
    5723:	0f 8c 7f 00 00 00    	jl     57a8 <overlap+0xc8>
    5729:	31 c0                	xor    %eax,%eax
    572b:	4d 39 c1             	cmp    %r8,%r9
    572e:	7f 4c                	jg     577c <overlap+0x9c>
    5730:	31 c0                	xor    %eax,%eax
    5732:	4d 39 da             	cmp    %r11,%r10
    5735:	0f 9e c0             	setle  %al
    5738:	c3                   	ret
    5739:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5740:	7e 4e                	jle    5790 <overlap+0xb0>
    5742:	48 39 ca             	cmp    %rcx,%rdx
    5745:	7f 39                	jg     5780 <overlap+0xa0>
    5747:	75 31                	jne    577a <overlap+0x9a>
    5749:	4d 39 c1             	cmp    %r8,%r9
    574c:	7c 2c                	jl     577a <overlap+0x9a>
    574e:	b8 01 00 00 00       	mov    $0x1,%eax
    5753:	4d 39 da             	cmp    %r11,%r10
    5756:	7d 24                	jge    577c <overlap+0x9c>
    5758:	48 39 ca             	cmp    %rcx,%rdx
    575b:	0f 94 c2             	sete   %dl
    575e:	48 39 fe             	cmp    %rdi,%rsi
    5761:	0f 94 c0             	sete   %al
    5764:	21 c2                	and    %eax,%edx
    5766:	31 c0                	xor    %eax,%eax
    5768:	4d 39 c1             	cmp    %r8,%r9
    576b:	0f 94 c0             	sete   %al
    576e:	21 d0                	and    %edx,%eax
    5770:	c3                   	ret
    5771:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5778:	74 af                	je     5729 <overlap+0x49>
    577a:	31 c0                	xor    %eax,%eax
    577c:	c3                   	ret
    577d:	0f 1f 00             	nopl   (%rax)
    5780:	4d 39 da             	cmp    %r11,%r10
    5783:	7e c4                	jle    5749 <overlap+0x69>
    5785:	b8 01 00 00 00       	mov    $0x1,%eax
    578a:	4d 39 c1             	cmp    %r8,%r9
    578d:	7e ba                	jle    5749 <overlap+0x69>
    578f:	c3                   	ret
    5790:	48 39 ca             	cmp    %rcx,%rdx
    5793:	7c 94                	jl     5729 <overlap+0x49>
    5795:	4d 39 c1             	cmp    %r8,%r9
    5798:	7d b4                	jge    574e <overlap+0x6e>
    579a:	48 39 ca             	cmp    %rcx,%rdx
    579d:	74 91                	je     5730 <overlap+0x50>
    579f:	eb d9                	jmp    577a <overlap+0x9a>
    57a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    57a8:	c3                   	ret
    57a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000057b0 <verify>:
    57b0:	f3 0f 1e fa          	endbr64
    57b4:	85 f6                	test   %esi,%esi
    57b6:	0f 8e 49 03 00 00    	jle    5b05 <verify+0x355>
    57bc:	41 57                	push   %r15
    57be:	41 89 f7             	mov    %esi,%r15d
    57c1:	41 56                	push   %r14
    57c3:	45 31 f6             	xor    %r14d,%r14d
    57c6:	41 55                	push   %r13
    57c8:	41 54                	push   %r12
    57ca:	55                   	push   %rbp
    57cb:	53                   	push   %rbx
    57cc:	48 8d 5f 20          	lea    0x20(%rdi),%rbx
    57d0:	48 83 ec 48          	sub    $0x48,%rsp
    57d4:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    57d9:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    57de:	45 31 e4             	xor    %r12d,%r12d
    57e1:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    57e6:	45 39 e6             	cmp    %r12d,%r14d
    57e9:	0f 84 47 02 00 00    	je     5a36 <verify+0x286>
    57ef:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    57f4:	8b 50 08             	mov    0x8(%rax),%edx
    57f7:	85 d2                	test   %edx,%edx
    57f9:	0f 8e 37 02 00 00    	jle    5a36 <verify+0x286>
    57ff:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    5807:	31 ed                	xor    %ebp,%ebp
    5809:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    580e:	44 89 7c 24 34       	mov    %r15d,0x34(%rsp)
    5813:	45 89 f7             	mov    %r14d,%r15d
    5816:	41 89 ee             	mov    %ebp,%r14d
    5819:	44 89 fa             	mov    %r15d,%edx
    581c:	48 8d 35 f1 09 00 00 	lea    0x9f1(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    5823:	bf 01 00 00 00       	mov    $0x1,%edi
    5828:	31 c0                	xor    %eax,%eax
    582a:	e8 01 cc ff ff       	call   2430 <__printf_chk@plt>
    582f:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5834:	8b 40 08             	mov    0x8(%rax),%eax
    5837:	85 c0                	test   %eax,%eax
    5839:	0f 8e cf 01 00 00    	jle    5a0e <verify+0x25e>
    583f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5844:	44 89 74 24 38       	mov    %r14d,0x38(%rsp)
    5849:	31 db                	xor    %ebx,%ebx
    584b:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    5850:	4c 8b 20             	mov    (%rax),%r12
    5853:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5858:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    585d:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    5861:	4c 8b 3c 24          	mov    (%rsp),%r15
    5865:	48 8d 35 bd 09 00 00 	lea    0x9bd(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    586c:	49 89 c6             	mov    %rax,%r14
    586f:	bf 01 00 00 00       	mov    $0x1,%edi
    5874:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5878:	49 c1 e6 07          	shl    $0x7,%r14
    587c:	4b 8b 8c 3c 48 02 00 00 	mov    0x248(%r12,%r15,1),%rcx
    5884:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    5889:	4a 8b 94 30 48 02 00 00 	mov    0x248(%rax,%r14,1),%rdx
    5891:	31 c0                	xor    %eax,%eax
    5893:	e8 98 cb ff ff       	call   2430 <__printf_chk@plt>
    5898:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    589d:	4c 8b 20             	mov    (%rax),%r12
    58a0:	4b 83 bc 3c 48 02 00 00 00 	cmpq   $0x0,0x248(%r12,%r15,1)
    58a9:	0f 8e 43 01 00 00    	jle    59f2 <verify+0x242>
    58af:	4c 03 75 00          	add    0x0(%rbp),%r14
    58b3:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    58b8:	ba 01 00 00 00       	mov    $0x1,%edx
    58bd:	4d 89 f5             	mov    %r14,%r13
    58c0:	4d 8b b5 48 02 00 00 	mov    0x248(%r13),%r14
    58c7:	4d 85 f6             	test   %r14,%r14
    58ca:	0f 8e 1d 01 00 00    	jle    59ed <verify+0x23d>
    58d0:	48 89 d5             	mov    %rdx,%rbp
    58d3:	48 8b 04 24          	mov    (%rsp),%rax
    58d7:	31 db                	xor    %ebx,%ebx
    58d9:	4d 89 f2             	mov    %r14,%r10
    58dc:	48 c1 e5 05          	shl    $0x5,%rbp
    58e0:	48 83 ed 20          	sub    $0x20,%rbp
    58e4:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    58e8:	49 89 ee             	mov    %rbp,%r14
    58eb:	48 89 dd             	mov    %rbx,%rbp
    58ee:	48 89 d3             	mov    %rdx,%rbx
    58f1:	eb 32                	jmp    5925 <verify+0x175>
    58f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    58f8:	4c 39 c2             	cmp    %r8,%rdx
    58fb:	0f 8d 57 01 00 00    	jge    5a58 <verify+0x2a8>
    5901:	4c 39 df             	cmp    %r11,%rdi
    5904:	7e 05                	jle    590b <verify+0x15b>
    5906:	49 39 c1             	cmp    %rax,%r9
    5909:	7c 75                	jl     5980 <verify+0x1d0>
    590b:	4c 39 df             	cmp    %r11,%rdi
    590e:	0f 8d b3 01 00 00    	jge    5ac7 <verify+0x317>
    5914:	0f 1f 40 00          	nopl   0x0(%rax)
    5918:	48 83 c5 01          	add    $0x1,%rbp
    591c:	49 39 ea             	cmp    %rbp,%r10
    591f:	0f 8e a8 00 00 00    	jle    59cd <verify+0x21d>
    5925:	49 8b 97 38 02 00 00 	mov    0x238(%r15),%rdx
    592c:	48 89 e8             	mov    %rbp,%rax
    592f:	48 c1 e0 05          	shl    $0x5,%rax
    5933:	49 03 85 38 02 00 00 	add    0x238(%r13),%rax
    593a:	4c 01 f2             	add    %r14,%rdx
    593d:	48 8b 08             	mov    (%rax),%rcx
    5940:	48 8b 78 10          	mov    0x10(%rax),%rdi
    5944:	48 8b 32             	mov    (%rdx),%rsi
    5947:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    594b:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    594f:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    5953:	48 8b 50 08          	mov    0x8(%rax),%rdx
    5957:	48 8b 40 18          	mov    0x18(%rax),%rax
    595b:	48 39 f1             	cmp    %rsi,%rcx
    595e:	7c 98                	jl     58f8 <verify+0x148>
    5960:	0f 8e 4a 01 00 00    	jle    5ab0 <verify+0x300>
    5966:	4c 39 c2             	cmp    %r8,%rdx
    5969:	0f 8f f9 00 00 00    	jg     5a68 <verify+0x2b8>
    596f:	75 a7                	jne    5918 <verify+0x168>
    5971:	4c 39 df             	cmp    %r11,%rdi
    5974:	7f a2                	jg     5918 <verify+0x168>
    5976:	49 39 c1             	cmp    %rax,%r9
    5979:	7c 9d                	jl     5918 <verify+0x168>
    597b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5980:	49 89 c1             	mov    %rax,%r9
    5983:	48 89 f9             	mov    %rdi,%rcx
    5986:	48 89 f2             	mov    %rsi,%rdx
    5989:	bf 01 00 00 00       	mov    $0x1,%edi
    598e:	48 8d 35 0b 0b 00 00 	lea    0xb0b(%rip),%rsi        # 64a0 <_IO_stdin_used+0x4a0>
    5995:	31 c0                	xor    %eax,%eax
    5997:	48 83 c5 01          	add    $0x1,%rbp
    599b:	e8 90 ca ff ff       	call   2430 <__printf_chk@plt>
    59a0:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    59a5:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    59aa:	4c 03 28             	add    (%rax),%r13
    59ad:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    59b2:	4d 8b 95 48 02 00 00 	mov    0x248(%r13),%r10
    59b9:	4c 8b 20             	mov    (%rax),%r12
    59bc:	48 8b 04 24          	mov    (%rsp),%rax
    59c0:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    59c4:	49 39 ea             	cmp    %rbp,%r10
    59c7:	0f 8f 58 ff ff ff    	jg     5925 <verify+0x175>
    59cd:	48 89 da             	mov    %rbx,%rdx
    59d0:	49 3b 9f 48 02 00 00 	cmp    0x248(%r15),%rbx
    59d7:	7d 14                	jge    59ed <verify+0x23d>
    59d9:	4d 8b b5 48 02 00 00 	mov    0x248(%r13),%r14
    59e0:	48 83 c2 01          	add    $0x1,%rdx
    59e4:	4d 85 f6             	test   %r14,%r14
    59e7:	0f 8f e3 fe ff ff    	jg     58d0 <verify+0x120>
    59ed:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    59f2:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    59f7:	48 83 c3 01          	add    $0x1,%rbx
    59fb:	39 58 08             	cmp    %ebx,0x8(%rax)
    59fe:	0f 8f 54 fe ff ff    	jg     5858 <verify+0xa8>
    5a04:	44 8b 74 24 38       	mov    0x38(%rsp),%r14d
    5a09:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
    5a0e:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5a13:	48 81 04 24 80 02 00 00 	addq   $0x280,(%rsp)
    5a1b:	41 83 c6 01          	add    $0x1,%r14d
    5a1f:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    5a23:	0f 8f f0 fd ff ff    	jg     5819 <verify+0x69>
    5a29:	45 89 fe             	mov    %r15d,%r14d
    5a2c:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    5a31:	44 8b 7c 24 34       	mov    0x34(%rsp),%r15d
    5a36:	48 81 44 24 08 98 00 00 00 	addq   $0x98,0x8(%rsp)
    5a3f:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    5a44:	41 39 c7             	cmp    %eax,%r15d
    5a47:	0f 84 88 00 00 00    	je     5ad5 <verify+0x325>
    5a4d:	41 89 c4             	mov    %eax,%r12d
    5a50:	e9 91 fd ff ff       	jmp    57e6 <verify+0x36>
    5a55:	0f 1f 00             	nopl   (%rax)
    5a58:	0f 85 ba fe ff ff    	jne    5918 <verify+0x168>
    5a5e:	e9 a8 fe ff ff       	jmp    590b <verify+0x15b>
    5a63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5a68:	49 39 c1             	cmp    %rax,%r9
    5a6b:	7e 09                	jle    5a76 <verify+0x2c6>
    5a6d:	4c 39 df             	cmp    %r11,%rdi
    5a70:	0f 8c 0a ff ff ff    	jl     5980 <verify+0x1d0>
    5a76:	4c 39 df             	cmp    %r11,%rdi
    5a79:	0f 8f 99 fe ff ff    	jg     5918 <verify+0x168>
    5a7f:	49 39 c1             	cmp    %rax,%r9
    5a82:	0f 8d f8 fe ff ff    	jge    5980 <verify+0x1d0>
    5a88:	48 39 f1             	cmp    %rsi,%rcx
    5a8b:	0f 85 87 fe ff ff    	jne    5918 <verify+0x168>
    5a91:	4c 39 c2             	cmp    %r8,%rdx
    5a94:	0f 85 7e fe ff ff    	jne    5918 <verify+0x168>
    5a9a:	4c 39 df             	cmp    %r11,%rdi
    5a9d:	0f 84 dd fe ff ff    	je     5980 <verify+0x1d0>
    5aa3:	e9 70 fe ff ff       	jmp    5918 <verify+0x168>
    5aa8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5ab0:	4c 39 c2             	cmp    %r8,%rdx
    5ab3:	0f 8c 52 fe ff ff    	jl     590b <verify+0x15b>
    5ab9:	4c 39 df             	cmp    %r11,%rdi
    5abc:	7e c1                	jle    5a7f <verify+0x2cf>
    5abe:	4c 39 c2             	cmp    %r8,%rdx
    5ac1:	0f 85 51 fe ff ff    	jne    5918 <verify+0x168>
    5ac7:	49 39 c1             	cmp    %rax,%r9
    5aca:	0f 8f 48 fe ff ff    	jg     5918 <verify+0x168>
    5ad0:	e9 ab fe ff ff       	jmp    5980 <verify+0x1d0>
    5ad5:	48 81 44 24 10 98 00 00 00 	addq   $0x98,0x10(%rsp)
    5ade:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    5ae3:	41 8d 46 01          	lea    0x1(%r14),%eax
    5ae7:	45 39 e6             	cmp    %r12d,%r14d
    5aea:	74 08                	je     5af4 <verify+0x344>
    5aec:	41 89 c6             	mov    %eax,%r14d
    5aef:	e9 e5 fc ff ff       	jmp    57d9 <verify+0x29>
    5af4:	48 83 c4 48          	add    $0x48,%rsp
    5af8:	31 c0                	xor    %eax,%eax
    5afa:	5b                   	pop    %rbx
    5afb:	5d                   	pop    %rbp
    5afc:	41 5c                	pop    %r12
    5afe:	41 5d                	pop    %r13
    5b00:	41 5e                	pop    %r14
    5b02:	41 5f                	pop    %r15
    5b04:	c3                   	ret
    5b05:	31 c0                	xor    %eax,%eax
    5b07:	c3                   	ret

Disassembly of section .fini:

0000000000005b08 <_fini>:
    5b08:	f3 0f 1e fa          	endbr64
    5b0c:	48 83 ec 08          	sub    $0x8,%rsp
    5b10:	48 83 c4 08          	add    $0x8,%rsp
    5b14:	c3                   	ret
