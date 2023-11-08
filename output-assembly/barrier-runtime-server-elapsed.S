
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
struct Snapshot {
  struct timespec start;
  struct timespec end;
};

void fatal_error(const char *syscall) {
    2520:	f3 0f 1e fa          	endbr64
    2524:	50                   	push   %rax
    2525:	58                   	pop    %rax
    2526:	50                   	push   %rax
    perror(syscall);
    2527:	e8 44 ff ff ff       	call   2470 <perror@plt>
    exit(1);
    252c:	bf 01 00 00 00       	mov    $0x1,%edi
    2531:	e8 4a ff ff ff       	call   2480 <exit@plt>

0000000000002536 <copy_file_contents.cold>:
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");
    2536:	48 8d 3d c2 3c 00 00 	lea    0x3cc2(%rip),%rdi        # 61ff <_IO_stdin_used+0x1ff>
    253d:	e8 de ff ff ff       	call   2520 <fatal_error>

0000000000002542 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    2542:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
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
        break;
      }
      printf("Received wait finished\n");
      struct Request *req = (struct Request *) cqe->user_data;
      if (ret < 0)
          fatal_error("io_uring_wait_cqe");
    2576:	48 8d 3d 52 3c 00 00 	lea    0x3c52(%rip),%rdi        # 61cf <_IO_stdin_used+0x1cf>
    257d:	e8 9e ff ff ff       	call   2520 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    2582:	48 8d 3d ca 3b 00 00 	lea    0x3bca(%rip),%rdi        # 6153 <_IO_stdin_used+0x153>
    2589:	e8 92 ff ff ff       	call   2520 <fatal_error>
    fatal_error("listen()");
    258e:	48 8d 3d de 3b 00 00 	lea    0x3bde(%rip),%rdi        # 6173 <_IO_stdin_used+0x173>
    2595:	e8 86 ff ff ff       	call   2520 <fatal_error>
    259a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25a2:	0f 0b                	ud2
    25a4:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25ac:	0f 0b                	ud2
      fatal_error("socket()");
    25ae:	48 8d 3d 95 3b 00 00 	lea    0x3b95(%rip),%rdi        # 614a <_IO_stdin_used+0x14a>
    25b5:	e8 66 ff ff ff       	call   2520 <fatal_error>
      fatal_error("bind()");
    25ba:	48 8d 3d ab 3b 00 00 	lea    0x3bab(%rip),%rdi        # 616c <_IO_stdin_used+0x16c>
    25c1:	e8 5a ff ff ff       	call   2520 <fatal_error>
    25c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000025d0 <main>:
    }


  return 0;
}
int main() {
    25d0:	f3 0f 1e fa          	endbr64
    25d4:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
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
  printf("intrathread message buffer size = %ld\n", messages_limit);
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  struct ProtectedState *protected_state = calloc(1, sizeof(struct ProtectedState));
    26f8:	be 18 00 00 00       	mov    $0x18,%esi
    26fd:	bf 01 00 00 00       	mov    $0x1,%edi
    2702:	e8 79 fc ff ff       	call   2380 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2707:	be 00 01 00 00       	mov    $0x100,%esi
    270c:	bf 09 00 00 00       	mov    $0x9,%edi
  struct ProtectedState *protected_state = calloc(1, sizeof(struct ProtectedState));
    2711:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2716:	e8 65 fc ff ff       	call   2380 <calloc@plt>
  int barrier_count = thread_count;
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    271b:	be 10 00 00 00       	mov    $0x10,%esi
    2720:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2725:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    272a:	e8 51 fc ff ff       	call   2380 <calloc@plt>
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    272f:	be 00 01 00 00       	mov    $0x100,%esi
    2734:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    2739:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    273f:	48 89 c3             	mov    %rax,%rbx
    2742:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2747:	e8 34 fc ff ff       	call   2380 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    274c:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    }
  }
  int external_thread_index = 0;
    2751:	c7 44 24 34 00 00 00 00 	movl   $0x0,0x34(%rsp)
      buffers[x].buffer[y].available = 0;
    2759:	31 d2                	xor    %edx,%edx
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    275b:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
    275f:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    2769:	4d 89 c7             	mov    %r8,%r15
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    276c:	4c 89 44 24 48       	mov    %r8,0x48(%rsp)
    2771:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    thread_data[x].threads = thread_data;
    2778:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    thread_data[x].thread_index = x;
    277d:	41 89 17             	mov    %edx,(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2780:	be 10 00 00 00       	mov    $0x10,%esi
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2785:	31 db                	xor    %ebx,%ebx
    thread_data[x].task_count = total_barrier_count;
    2787:	41 c7 47 28 07 00 00 00 	movl   $0x7,0x28(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    278f:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].threads = thread_data;
    2794:	49 89 47 10          	mov    %rax,0x10(%r15)
    thread_data[x].thread_count = thread_count;
    2798:	48 8b 05 51 42 00 00 	mov    0x4251(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    279f:	89 54 24 08          	mov    %edx,0x8(%rsp)
    27a3:	49 89 47 18          	mov    %rax,0x18(%r15)
    thread_data[x].protected_state = protected_state;
    27a7:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    thread_data[x].thread_index = x;
    27ac:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    thread_data[x].protected_state = protected_state;
    27b1:	49 89 47 30          	mov    %rax,0x30(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    27b5:	e8 c6 fb ff ff       	call   2380 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27ba:	be 10 00 00 00       	mov    $0x10,%esi
    27bf:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    27c4:	49 89 47 50          	mov    %rax,0x50(%r15)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27c8:	e8 b3 fb ff ff       	call   2380 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    27cd:	be 28 00 00 00       	mov    $0x28,%esi
    27d2:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    27d7:	66 0f 6f 15 f1 41 00 00 	movdqa 0x41f1(%rip),%xmm2        # 69d0 <_IO_stdin_used+0x9d0>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27df:	49 89 47 58          	mov    %rax,0x58(%r15)
    thread_data[x].timestamp_count = 0;
    27e3:	41 0f 11 57 68       	movups %xmm2,0x68(%r15)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    27e8:	e8 93 fb ff ff       	call   2380 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    27ed:	be 80 05 00 00       	mov    $0x580,%esi
    27f2:	bf 07 00 00 00       	mov    $0x7,%edi
    thread_data[x].task_timestamp_count = 0;
    27f7:	66 0f 6f 1d d1 41 00 00 	movdqa 0x41d1(%rip),%xmm3        # 69d0 <_IO_stdin_used+0x9d0>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    27ff:	49 89 47 78          	mov    %rax,0x78(%r15)
    thread_data[x].task_timestamp_count = 0;
    2803:	41 0f 29 9f 80 00 00 00 	movaps %xmm3,0x80(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    280b:	e8 70 fb ff ff       	call   2380 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    2810:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    2815:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
      thread_data[x].tasks = barriers;
    281a:	49 89 47 20          	mov    %rax,0x20(%r15)
        thread_data[x].tasks[y].sending = 1;
    281e:	49 89 c7             	mov    %rax,%r15
    2821:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            thread_data[x].tasks[y].protected = do_protected_write; 
    2828:	4c 63 eb             	movslq %ebx,%r13
    282b:	44 89 74 24 28       	mov    %r14d,0x28(%rsp)
    2830:	4b 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%rax
    2835:	4d 8d 64 45 00       	lea    0x0(%r13,%rax,2),%r12
    283a:	49 c1 e4 07          	shl    $0x7,%r12
        if (x == y) {
    283e:	44 39 f3             	cmp    %r14d,%ebx
    2841:	0f 84 09 0a 00 00    	je     3250 <main+0xc80>
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2847:	be 00 02 00 00       	mov    $0x200,%esi
    284c:	bf 06 00 00 00       	mov    $0x6,%edi
    2851:	e8 2a fb ff ff       	call   2380 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    2856:	89 5c 24 18          	mov    %ebx,0x18(%rsp)
    285a:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    285f:	48 8d a8 00 0c 00 00 	lea    0xc00(%rax),%rbp
    2866:	4b 89 84 27 88 04 00 00 	mov    %rax,0x488(%r15,%r12,1)
        for (int b = 0 ; b < thread_count ; b++) {
    286e:	49 89 c7             	mov    %rax,%r15
    2871:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2878:	be 08 00 00 00       	mov    $0x8,%esi
    287d:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < thread_count ; b++) {
    2882:	49 81 c7 00 02 00 00 	add    $0x200,%r15
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2889:	e8 f2 fa ff ff       	call   2380 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    288e:	be 08 00 00 00       	mov    $0x8,%esi
    2893:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2898:	49 89 c4             	mov    %rax,%r12
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    289b:	e8 e0 fa ff ff       	call   2380 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    28a0:	be 00 01 00 00       	mov    $0x100,%esi
    28a5:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    28aa:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    28ad:	e8 ce fa ff ff       	call   2380 <calloc@plt>
          data[0].messages_count = 0;
    28b2:	66 0f 6f 05 26 41 00 00 	movdqa 0x4126(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
          mailboxes[b].higher = &data[1];
    28ba:	48 8d b0 00 01 00 00 	lea    0x100(%rax),%rsi
          mailboxes[b].lower = &data[0];
    28c1:	49 89 87 00 fe ff ff 	mov    %rax,-0x200(%r15)
          mailboxes[b].higher = &data[1];
    28c8:	49 89 b7 80 fe ff ff 	mov    %rsi,-0x180(%r15)
          data[0].messages = messages;
    28cf:	4c 89 20             	mov    %r12,(%rax)
          data[1].messages = messages2;
    28d2:	48 89 98 00 01 00 00 	mov    %rbx,0x100(%rax)
          data[0].messages_count = 0;
    28d9:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
          data[1].messages_count = 0;
    28e0:	0f 29 80 80 01 00 00 	movaps %xmm0,0x180(%rax)
        for (int b = 0 ; b < thread_count ; b++) {
    28e7:	49 39 ef             	cmp    %rbp,%r15
    28ea:	75 8c                	jne    2878 <main+0x2a8>
        char *message = malloc(sizeof(char) * 256);
    28ec:	be 01 00 00 00       	mov    $0x1,%esi
    28f1:	bf 00 01 00 00       	mov    $0x100,%edi
    28f6:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
    28fa:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
    28ff:	e8 7c fa ff ff       	call   2380 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    2904:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2909:	48 89 c5             	mov    %rax,%rbp
        struct Message *messaged = malloc(sizeof(struct Message));
    290c:	e8 df fa ff ff       	call   23f0 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2911:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    2916:	48 89 ef             	mov    %rbp,%rdi
    2919:	41 89 d9             	mov    %ebx,%r9d
    291c:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2921:	48 8d 0d 58 3c 00 00 	lea    0x3c58(%rip),%rcx        # 6580 <_IO_stdin_used+0x580>
    2928:	ba 00 01 00 00       	mov    $0x100,%edx
    292d:	31 c0                	xor    %eax,%eax
    292f:	be 01 00 00 00       	mov    $0x1,%esi
    2934:	e8 c7 fb ff ff       	call   2500 <__sprintf_chk@plt>
        messaged->message = message;
    2939:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    293e:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    2943:	ba ab aa aa aa       	mov    $0xaaaaaaab,%edx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2948:	be 20 00 00 00       	mov    $0x20,%esi
    294d:	bf 3f 42 0f 00       	mov    $0xf423f,%edi
        messaged->task_index = y;
    2952:	4d 89 6a 10          	mov    %r13,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2956:	44 8d 6b 01          	lea    0x1(%rbx),%r13d
    295a:	4c 8b 78 20          	mov    0x20(%rax),%r15
    295e:	44 89 e8             	mov    %r13d,%eax
    2961:	44 89 e9             	mov    %r13d,%ecx
        messaged->message = message;
    2964:	49 89 2a             	mov    %rbp,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2967:	48 0f af c2          	imul   %rdx,%rax
    296b:	4b 8d 2c 27          	lea    (%r15,%r12,1),%rbp
        messaged->thread_index = x;
    296f:	4d 89 72 08          	mov    %r14,0x8(%r10)
        thread_data[x].tasks[y].message = messaged;
    2973:	4c 89 95 10 05 00 00 	mov    %r10,0x510(%rbp)
        thread_data[x].tasks[y].snapshot_count = 999999;
    297a:	48 c7 85 80 03 00 00 3f 42 0f 00 	movq   $0xf423f,0x380(%rbp)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2985:	48 c1 e8 22          	shr    $0x22,%rax
    2989:	8d 04 40             	lea    (%rax,%rax,2),%eax
    298c:	01 c0                	add    %eax,%eax
    298e:	29 c1                	sub    %eax,%ecx
    2990:	89 8d 18 05 00 00    	mov    %ecx,0x518(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2996:	e8 e5 f9 ff ff       	call   2380 <calloc@plt>
        thread_data[x].tasks[y].thread_index = x;
    299b:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
        thread_data[x].tasks[y].task_index = y;
    299f:	89 5d 00             	mov    %ebx,0x0(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    29a2:	48 89 85 08 03 00 00 	mov    %rax,0x308(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    29a9:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    29ae:	48 c7 85 00 04 00 00 00 00 00 00 	movq   $0x0,0x400(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    29b9:	48 89 85 18 02 00 00 	mov    %rax,0x218(%rbp)
        thread_data[x].tasks[y].available = 1;
    29c0:	48 8b 05 31 40 00 00 	mov    0x4031(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
        thread_data[x].tasks[y].thread_index = x;
    29c7:	89 8d 20 02 00 00    	mov    %ecx,0x220(%rbp)
        thread_data[x].tasks[y].available = 1;
    29cd:	48 89 85 80 02 00 00 	mov    %rax,0x280(%rbp)
        thread_data[x].tasks[y].sending = 1;
    29d4:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
        thread_data[x].tasks[y].arrived = 0;
    29de:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        thread_data[x].tasks[y].thread_count = thread_count;
    29e8:	c7 85 24 02 00 00 06 00 00 00 	movl   $0x6,0x224(%rbp)
        thread_data[x].tasks[y].sending = 1;
    29f2:	48 89 85 08 05 00 00 	mov    %rax,0x508(%rbp)
        if (y == barrier_count - 1) {
    29f9:	83 fb 05             	cmp    $0x5,%ebx
    29fc:	0f 84 2e 08 00 00    	je     3230 <main+0xc60>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2a02:	8b 44 24 28          	mov    0x28(%rsp),%eax
    2a06:	39 c3                	cmp    %eax,%ebx
    2a08:	75 66                	jne    2a70 <main+0x4a0>
    2a0a:	8b 5c 24 34          	mov    0x34(%rsp),%ebx
    2a0e:	85 db                	test   %ebx,%ebx
    2a10:	7f 5e                	jg     2a70 <main+0x4a0>
    2a12:	89 ca                	mov    %ecx,%edx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2a14:	bf 01 00 00 00       	mov    $0x1,%edi
    2a19:	48 8d 35 88 3b 00 00 	lea    0x3b88(%rip),%rsi        # 65a8 <_IO_stdin_used+0x5a8>
    2a20:	31 c0                	xor    %eax,%eax
    2a22:	e8 09 fa ff ff       	call   2430 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a27:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    2a2c:	48 63 c3             	movslq %ebx,%rax
    2a2f:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    2a34:	48 89 c1             	mov    %rax,%rcx
    2a37:	48 c1 e0 04          	shl    $0x4,%rax
    2a3b:	48 01 f8             	add    %rdi,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a3e:	4c 8b 7a 20          	mov    0x20(%rdx),%r15
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a42:	48 89 42 38          	mov    %rax,0x38(%rdx)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a46:	48 8d 05 63 2b 00 00 	lea    0x2b63(%rip),%rax        # 55b0 <barriered_work_ingest>
    2a4d:	4b 89 84 27 08 02 00 00 	mov    %rax,0x208(%r15,%r12,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a55:	8d 41 01             	lea    0x1(%rcx),%eax
    2a58:	89 44 24 34          	mov    %eax,0x34(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2a5c:	41 83 fd 07          	cmp    $0x7,%r13d
    2a60:	74 22                	je     2a84 <main+0x4b4>
  int external_thread_index = 0;
    2a62:	44 89 eb             	mov    %r13d,%ebx
    2a65:	e9 be fd ff ff       	jmp    2828 <main+0x258>
    2a6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            thread_data[x].tasks[y].run = barriered_work; 
    2a70:	48 8d 05 99 27 00 00 	lea    0x2799(%rip),%rax        # 5210 <barriered_work>
    2a77:	48 89 85 08 02 00 00 	mov    %rax,0x208(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2a7e:	41 83 fd 07          	cmp    $0x7,%r13d
    2a82:	75 de                	jne    2a62 <main+0x492>

          }
        }
      }
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2a84:	4c 89 f2             	mov    %r14,%rdx
    2a87:	48 8d 05 12 09 00 00 	lea    0x912(%rip),%rax        # 33a0 <barriered_reset>
    2a8e:	4d 89 fe             	mov    %r15,%r14
    2a91:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    2a96:	49 89 86 08 23 00 00 	mov    %rax,0x2308(%r14)
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
      thread_data[x].tasks[barrier_count].thread_index = x; 
    2a9d:	8b 44 24 08          	mov    0x8(%rsp),%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2aa1:	48 83 c2 01          	add    $0x1,%rdx
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2aa5:	4d 89 be 18 23 00 00 	mov    %r15,0x2318(%r14)
  for (int x = 0 ; x < total_threads ; x++) {
    2aac:	49 81 c7 00 01 00 00 	add    $0x100,%r15
      thread_data[x].tasks[barrier_count].thread_index = x; 
    2ab3:	41 89 86 20 23 00 00 	mov    %eax,0x2320(%r14)
      thread_data[x].tasks[barrier_count].available = 1; 
    2aba:	48 8b 05 37 3f 00 00 	mov    0x3f37(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2ac1:	41 c7 86 80 21 00 00 00 00 00 00 	movl   $0x0,0x2180(%r14)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2acc:	41 c7 86 00 21 00 00 06 00 00 00 	movl   $0x6,0x2100(%r14)
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
    2ad7:	41 c7 86 24 23 00 00 06 00 00 00 	movl   $0x6,0x2324(%r14)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2ae2:	41 c7 86 0c 26 00 00 06 00 00 00 	movl   $0x6,0x260c(%r14)
      thread_data[x].tasks[barrier_count].available = 1; 
    2aed:	49 89 86 80 23 00 00 	mov    %rax,0x2380(%r14)
  for (int x = 0 ; x < total_threads ; x++) {
    2af4:	48 83 fa 09          	cmp    $0x9,%rdx
    2af8:	0f 85 7a fc ff ff    	jne    2778 <main+0x1a8>
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].threads = thread_data;
    2afe:	4c 8b 44 24 48       	mov    0x48(%rsp),%r8
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b03:	be 38 00 00 00       	mov    $0x38,%esi
    2b08:	bf 09 00 00 00       	mov    $0x9,%edi
  thread_data[thread_count].thread_count = thread_count;
  thread_data[thread_count].thread_index = 0;

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
  for (int x = 0 ; x < thread_count ; x++) {
    2b0d:	45 31 ed             	xor    %r13d,%r13d
    2b10:	4c 8d 3d f9 08 00 00 	lea    0x8f9(%rip),%r15        # 3410 <barriered_thread>
    thread_data[n].tasks[0].scheduled = 1;
    2b17:	49 8b 40 20          	mov    0x20(%r8),%rax
    2b1b:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    thread_data[x].threads = thread_data;
    2b20:	4d 89 80 10 07 00 00 	mov    %r8,0x710(%r8)
    thread_data[x].thread_count = thread_count;
    2b27:	41 c7 80 18 07 00 00 06 00 00 00 	movl   $0x6,0x718(%r8)
    thread_data[x].thread_index = x;
    2b32:	41 c7 80 00 07 00 00 07 00 00 00 	movl   $0x7,0x700(%r8)
    thread_data[x].task_count = total_barrier_count;
    2b3d:	41 c7 80 28 07 00 00 07 00 00 00 	movl   $0x7,0x728(%r8)
    thread_data[n].tasks[0].scheduled = 1;
    2b48:	c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rax)
    2b52:	49 8b 80 20 01 00 00 	mov    0x120(%r8),%rax
    2b59:	c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rax)
    2b63:	49 8b 80 20 02 00 00 	mov    0x220(%r8),%rax
    2b6a:	c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rax)
    2b74:	49 8b 80 20 03 00 00 	mov    0x320(%r8),%rax
    2b7b:	c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rax)
    2b85:	49 8b 80 20 04 00 00 	mov    0x420(%r8),%rax
    2b8c:	c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rax)
    2b96:	49 8b 80 20 05 00 00 	mov    0x520(%r8),%rax
    2b9d:	c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rax)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ba7:	e8 d4 f7 ff ff       	call   2380 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bac:	be 38 00 00 00       	mov    $0x38,%esi
    2bb1:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bb6:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bb9:	e8 c2 f7 ff ff       	call   2380 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bbe:	be 38 00 00 00       	mov    $0x38,%esi
    2bc3:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bc8:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bcd:	e8 ae f7 ff ff       	call   2380 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bd2:	be 08 00 00 00       	mov    $0x8,%esi
    2bd7:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bdc:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2be1:	e8 9a f7 ff ff       	call   2380 <calloc@plt>
  thread_data[thread_count].task_count = total_barrier_count;
    2be6:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2beb:	ba 06 00 00 00       	mov    $0x6,%edx
    2bf0:	48 8d 35 f8 36 00 00 	lea    0x36f8(%rip),%rsi        # 62ef <_IO_stdin_used+0x2ef>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bf7:	49 89 c4             	mov    %rax,%r12
  thread_data[thread_count].task_count = total_barrier_count;
    2bfa:	48 8b 05 ff 3d 00 00 	mov    0x3dff(%rip),%rax        # 6a00 <_IO_stdin_used+0xa00>
    2c01:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].threads = thread_data;
    2c06:	4d 89 80 10 06 00 00 	mov    %r8,0x610(%r8)
    2c0d:	4c 89 e5             	mov    %r12,%rbp
  thread_data[thread_count].task_count = total_barrier_count;
    2c10:	49 89 80 28 06 00 00 	mov    %rax,0x628(%r8)
    2c17:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2c19:	41 c7 80 18 06 00 00 06 00 00 00 	movl   $0x6,0x618(%r8)
  thread_data[thread_count].thread_index = 0;
    2c24:	49 c7 80 00 06 00 00 00 00 00 00 	movq   $0x0,0x600(%r8)
    2c2f:	e8 fc f7 ff ff       	call   2430 <__printf_chk@plt>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2c34:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2c39:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
    2c3e:	45 89 ec             	mov    %r13d,%r12d
    2c41:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2c48:	48 8d 15 31 0b 00 00 	lea    0xb31(%rip),%rdx        # 3780 <timer_thread>
    2c4f:	49 89 ed             	mov    %rbp,%r13
    2c52:	49 8d 88 00 06 00 00 	lea    0x600(%r8),%rcx
    2c59:	e8 f2 f7 ff ff       	call   2450 <pthread_create@plt>
    2c5e:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    2c63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    thread_data[x].type = WORKER;
    2c68:	41 c7 46 04 01 00 00 00 	movl   $0x1,0x4(%r14)
    2c70:	44 89 e2             	mov    %r12d,%edx
    2c73:	bf 01 00 00 00       	mov    $0x1,%edi
    2c78:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2c7a:	41 c7 46 2c 01 00 00 00 	movl   $0x1,0x2c(%r14)
    2c82:	48 8d 35 3f 39 00 00 	lea    0x393f(%rip),%rsi        # 65c8 <_IO_stdin_used+0x5c8>
  for (int x = 0 ; x < thread_count ; x++) {
    2c89:	41 83 c4 01          	add    $0x1,%r12d
    2c8d:	e8 9e f7 ff ff       	call   2430 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2c92:	4c 89 f1             	mov    %r14,%rcx
    2c95:	48 89 de             	mov    %rbx,%rsi
    2c98:	48 89 ef             	mov    %rbp,%rdi
    2c9b:	4c 89 fa             	mov    %r15,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2c9e:	49 81 c6 00 01 00 00 	add    $0x100,%r14
    2ca5:	48 83 c5 08          	add    $0x8,%rbp
    2ca9:	48 83 c3 38          	add    $0x38,%rbx
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2cad:	e8 9e f7 ff ff       	call   2450 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2cb2:	41 83 fc 06          	cmp    $0x6,%r12d
    2cb6:	75 b0                	jne    2c68 <main+0x698>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2cb8:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2cbd:	48 8b 1d 44 3d 00 00 	mov    0x3d44(%rip),%rbx        # 6a08 <_IO_stdin_used+0xa08>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2cc4:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    2cc9:	4d 89 ec             	mov    %r13,%r12
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ccc:	bf 01 00 00 00       	mov    $0x1,%edi
    2cd1:	48 8d 2d 87 36 00 00 	lea    0x3687(%rip),%rbp        # 635f <_IO_stdin_used+0x35f>
    thread_data[x].task_count = 0;
    2cd8:	49 89 98 28 07 00 00 	mov    %rbx,0x728(%r8)
    thread_data[x].type = IO;
    2cdf:	41 c7 80 04 07 00 00 02 00 00 00 	movl   $0x2,0x704(%r8)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2cea:	e8 91 f6 ff ff       	call   2380 <calloc@plt>
    2cef:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2cf4:	be 00 08 00 00       	mov    $0x800,%esi
    2cf9:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2cfb:	49 89 80 40 07 00 00 	mov    %rax,0x740(%r8)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2d02:	e8 89 f7 ff ff       	call   2490 <eventfd@plt>
    2d07:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2d0c:	ba 07 00 00 00       	mov    $0x7,%edx
    2d11:	48 8d 35 f5 35 00 00 	lea    0x35f5(%rip),%rsi        # 630d <_IO_stdin_used+0x30d>
    2d18:	bf 01 00 00 00       	mov    $0x1,%edi
    2d1d:	41 89 80 48 07 00 00 	mov    %eax,0x748(%r8)
    2d24:	31 c0                	xor    %eax,%eax
    thread_data[x].threads = thread_data;
    2d26:	4d 89 80 10 07 00 00 	mov    %r8,0x710(%r8)
    thread_data[x].thread_count = thread_count;
    2d2d:	41 c7 80 18 07 00 00 06 00 00 00 	movl   $0x6,0x718(%r8)
    thread_data[x].thread_index = x;
    2d38:	41 c7 80 00 07 00 00 07 00 00 00 	movl   $0x7,0x700(%r8)
    2d43:	e8 e8 f6 ff ff       	call   2430 <__printf_chk@plt>
    thread_data[x].type = IO;
    2d48:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2d4d:	49 8d 7d 38          	lea    0x38(%r13),%rdi
    2d51:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2d56:	48 8d 15 c3 1c 00 00 	lea    0x1cc3(%rip),%rdx        # 4a20 <io_thread>
    thread_data[x].type = IO;
    2d5d:	49 8d 88 00 07 00 00 	lea    0x700(%r8),%rcx
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2d64:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2d6b:	e8 e0 f6 ff ff       	call   2450 <pthread_create@plt>
    2d70:	ba 08 00 00 00       	mov    $0x8,%edx
    2d75:	48 8d 35 a8 35 00 00 	lea    0x35a8(%rip),%rsi        # 6324 <_IO_stdin_used+0x324>
    2d7c:	31 c0                	xor    %eax,%eax
    2d7e:	bf 01 00 00 00       	mov    $0x1,%edi
    2d83:	e8 a8 f6 ff ff       	call   2430 <__printf_chk@plt>
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2d88:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x].buffers = &buffers[buffer_index];
    2d8d:	48 8b 44 24 38       	mov    0x38(%rsp),%rax

    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2d92:	49 8d 7d 40          	lea    0x40(%r13),%rdi
    2d96:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    2d9b:	48 8d 15 1e 09 00 00 	lea    0x91e(%rip),%rdx        # 36c0 <external_thread>
    2da2:	4c 8d 6c 24 50       	lea    0x50(%rsp),%r13
    thread_data[x].buffers = &buffers[buffer_index];
    2da7:	49 89 80 38 08 00 00 	mov    %rax,0x838(%r8)
    thread_data[x].thread_count = thread_count;
    2dae:	48 8b 05 3b 3c 00 00 	mov    0x3c3b(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    thread_data[x].type = EXTERNAL;
    2db5:	49 8d 88 00 08 00 00 	lea    0x800(%r8),%rcx
    thread_data[x].task_count = 0;
    2dbc:	49 89 98 28 08 00 00 	mov    %rbx,0x828(%r8)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2dc3:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    2dca:	31 db                	xor    %ebx,%ebx
    thread_data[x].thread_count = thread_count;
    2dcc:	49 89 80 18 08 00 00 	mov    %rax,0x818(%r8)
    thread_data[x].thread_index = x;
    2dd3:	48 8b 05 36 3c 00 00 	mov    0x3c36(%rip),%rax        # 6a10 <_IO_stdin_used+0xa10>
    thread_data[x].threads = thread_data;
    2dda:	4d 89 80 10 08 00 00 	mov    %r8,0x810(%r8)
    thread_data[x].thread_index = x;
    2de1:	49 89 80 00 08 00 00 	mov    %rax,0x800(%r8)
    thread_data[x].type = EXTERNAL;
    2de8:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2ded:	e8 5e f6 ff ff       	call   2450 <pthread_create@plt>
    2df2:	48 8d 3d 48 35 00 00 	lea    0x3548(%rip),%rdi        # 6341 <_IO_stdin_used+0x341>
    2df9:	e8 d2 f4 ff ff       	call   22d0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    2dfe:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    2e03:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
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
    2e2d:	75 d9                	jne    2e08 <main+0x838>
    2e2f:	49 8d 86 20 06 00 00 	lea    0x620(%r14),%rax
  }
  long total = 0;
  long v = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
    2e36:	31 ed                	xor    %ebp,%ebp
  long sends = 0;
    2e38:	31 c9                	xor    %ecx,%ecx
  long v = 0;
    2e3a:	45 31 c9             	xor    %r9d,%r9d
  long total = 0;
    2e3d:	45 31 e4             	xor    %r12d,%r12d
    2e40:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  long ingests = 0;
    2e45:	45 31 db             	xor    %r11d,%r11d
    2e48:	4d 8d 6e 20          	lea    0x20(%r14),%r13
    2e4c:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
  long received = 0;
    2e51:	31 db                	xor    %ebx,%ebx
    2e53:	4d 89 de             	mov    %r11,%r14
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
      struct timespec start = thread_data[x].start[n];
      struct timespec end = thread_data[x].end[n];
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2e56:	49 bf db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r15
    2e60:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2e65:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    2e6a:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    2e6f:	90                   	nop
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2e70:	49 63 45 08          	movslq 0x8(%r13),%rax
    2e74:	85 c0                	test   %eax,%eax
    2e76:	0f 8e c0 00 00 00    	jle    2f3c <main+0x96c>
    2e7c:	48 8d 34 80          	lea    (%rax,%rax,4),%rsi
    2e80:	49 8b 55 00          	mov    0x0(%r13),%rdx
    2e84:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    2e89:	48 8d 34 70          	lea    (%rax,%rsi,2),%rsi
    2e8d:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2e92:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    2e97:	48 c1 e6 07          	shl    $0x7,%rsi
    2e9b:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    2ea0:	48 01 d6             	add    %rdx,%rsi
    2ea3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ea8:	48 8b 82 88 04 00 00 	mov    0x488(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    2eaf:	48 03 8a 80 01 00 00 	add    0x180(%rdx),%rcx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2eb6:	48 81 c2 80 05 00 00 	add    $0x580,%rdx
      v += thread_data[x].tasks[n].v;
    2ebd:	4c 03 9a 80 fc ff ff 	add    -0x380(%rdx),%r11
      ingests += thread_data[x].tasks[n].ingest_count;
    2ec4:	4c 03 b2 00 ff ff ff 	add    -0x100(%rdx),%r14
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ecb:	48 03 a8 00 01 00 00 	add    0x100(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ed2:	48 03 98 80 01 00 00 	add    0x180(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ed9:	48 03 a8 00 03 00 00 	add    0x300(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ee0:	48 03 98 80 03 00 00 	add    0x380(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ee7:	48 03 a8 00 05 00 00 	add    0x500(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2eee:	48 03 98 80 05 00 00 	add    0x580(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ef5:	48 03 a8 00 07 00 00 	add    0x700(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2efc:	48 03 98 80 07 00 00 	add    0x780(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2f03:	48 03 a8 00 09 00 00 	add    0x900(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2f0a:	48 03 98 80 09 00 00 	add    0x980(%rax),%rbx
      sends += thread_data[x].tasks[n].sends;
    2f11:	4c 03 4a 80          	add    -0x80(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2f15:	48 03 a8 00 0b 00 00 	add    0xb00(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2f1c:	48 03 98 80 0b 00 00 	add    0xb80(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2f23:	48 39 f2             	cmp    %rsi,%rdx
    2f26:	75 80                	jne    2ea8 <main+0x8d8>
    2f28:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    2f2d:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    2f32:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    2f37:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f3c:	45 31 e4             	xor    %r12d,%r12d
    2f3f:	49 83 7d 50 00       	cmpq   $0x0,0x50(%r13)
    2f44:	7e 71                	jle    2fb7 <main+0x9e7>
    2f46:	4c 89 ed             	mov    %r13,%rbp
    2f49:	49 89 dd             	mov    %rbx,%r13
    2f4c:	4c 89 e3             	mov    %r12,%rbx
    2f4f:	90                   	nop
      struct timespec start = thread_data[x].start[n];
    2f50:	48 8b 7d 30          	mov    0x30(%rbp),%rdi
    2f54:	48 89 de             	mov    %rbx,%rsi
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f57:	48 83 c3 01          	add    $0x1,%rbx
    2f5b:	48 c1 e6 04          	shl    $0x4,%rsi
      struct timespec start = thread_data[x].start[n];
    2f5f:	48 01 f7             	add    %rsi,%rdi
      struct timespec end = thread_data[x].end[n];
    2f62:	48 03 75 38          	add    0x38(%rbp),%rsi
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    2f66:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    2f6a:	48 2b 57 08          	sub    0x8(%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2f6e:	48 89 d0             	mov    %rdx,%rax
    2f71:	49 f7 e7             	mul    %r15
    2f74:	31 c0                	xor    %eax,%eax
    2f76:	48 89 d1             	mov    %rdx,%rcx
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    2f79:	48 8b 16             	mov    (%rsi),%rdx
    2f7c:	48 8d 35 f0 33 00 00 	lea    0x33f0(%rip),%rsi        # 6373 <_IO_stdin_used+0x373>
    2f83:	48 2b 17             	sub    (%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2f86:	48 c1 e9 12          	shr    $0x12,%rcx
    2f8a:	bf 01 00 00 00       	mov    $0x1,%edi
    2f8f:	e8 9c f4 ff ff       	call   2430 <__printf_chk@plt>
    2f94:	48 8b 55 40          	mov    0x40(%rbp),%rdx
    2f98:	bf 01 00 00 00       	mov    $0x1,%edi
    2f9d:	31 c0                	xor    %eax,%eax
    2f9f:	48 8d 35 eb 33 00 00 	lea    0x33eb(%rip),%rsi        # 6391 <_IO_stdin_used+0x391>
    2fa6:	e8 85 f4 ff ff       	call   2430 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2fab:	48 39 5d 50          	cmp    %rbx,0x50(%rbp)
    2faf:	7f 9f                	jg     2f50 <main+0x980>
    2fb1:	4c 89 eb             	mov    %r13,%rbx
    2fb4:	49 89 ed             	mov    %rbp,%r13
      printf("%ld iterations\n", thread_data[x].iteration_count);
    }
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    2fb7:	45 31 e4             	xor    %r12d,%r12d
    2fba:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    2fbf:	0f 8e 8a 00 00 00    	jle    304f <main+0xa7f>
    2fc5:	4c 89 ed             	mov    %r13,%rbp
    2fc8:	49 89 dd             	mov    %rbx,%r13
    2fcb:	4c 89 e3             	mov    %r12,%rbx
    2fce:	66 90                	xchg   %ax,%ax
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    2fd0:	48 8b 45 58          	mov    0x58(%rbp),%rax
    2fd4:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    2fd8:	48 83 ec 08          	sub    $0x8,%rsp
    2fdc:	48 8d 35 0d 36 00 00 	lea    0x360d(%rip),%rsi        # 65f0 <_IO_stdin_used+0x5f0>
    2fe3:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    2fe8:	48 83 c3 01          	add    $0x1,%rbx
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    2fec:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    2ff0:	4c 8b 61 18          	mov    0x18(%rcx),%r12
    2ff4:	4c 2b 61 08          	sub    0x8(%rcx),%r12
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    2ff8:	4c 89 e0             	mov    %r12,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    2ffb:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    2fff:	4c 2b 01             	sub    (%rcx),%r8
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3002:	49 f7 e7             	mul    %r15
    3005:	8b 49 20             	mov    0x20(%rcx),%ecx
    3008:	41 54                	push   %r12
    300a:	31 c0                	xor    %eax,%eax
    300c:	48 c1 ea 12          	shr    $0x12,%rdx
    3010:	49 89 d1             	mov    %rdx,%r9
    3013:	ba 06 00 00 00       	mov    $0x6,%edx
    3018:	e8 13 f4 ff ff       	call   2430 <__printf_chk@plt>
    301d:	48 8d 35 89 33 00 00 	lea    0x3389(%rip),%rsi        # 63ad <_IO_stdin_used+0x3ad>
    3024:	bf 01 00 00 00       	mov    $0x1,%edi
      printf("%ldns per thread\n", (seconds2 / thread_count));
    3029:	48 b8 ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%rax
    3033:	49 f7 e4             	mul    %r12
    3036:	31 c0                	xor    %eax,%eax
    3038:	48 c1 ea 02          	shr    $0x2,%rdx
    303c:	e8 ef f3 ff ff       	call   2430 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3041:	58                   	pop    %rax
    3042:	5a                   	pop    %rdx
    3043:	48 39 5d 68          	cmp    %rbx,0x68(%rbp)
    3047:	7f 87                	jg     2fd0 <main+0xa00>
    3049:	4c 89 eb             	mov    %r13,%rbx
    304c:	49 89 ed             	mov    %rbp,%r13
    304f:	49 8b 55 70          	mov    0x70(%r13),%rdx
    3053:	48 8d 35 47 33 00 00 	lea    0x3347(%rip),%rsi        # 63a1 <_IO_stdin_used+0x3a1>
    305a:	bf 01 00 00 00       	mov    $0x1,%edi
    305f:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < thread_count ; x++) {
    3061:	49 81 c5 00 01 00 00 	add    $0x100,%r13
    3068:	e8 c3 f3 ff ff       	call   2430 <__printf_chk@plt>
    306d:	4c 39 6c 24 28       	cmp    %r13,0x28(%rsp)
    3072:	0f 85 f8 fd ff ff    	jne    2e70 <main+0x8a0>
    3078:	4c 8b 64 24 08       	mov    0x8(%rsp),%r12
    307d:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3082:	48 8d 35 36 33 00 00 	lea    0x3336(%rip),%rsi        # 63bf <_IO_stdin_used+0x3bf>
    3089:	31 c0                	xor    %eax,%eax
    308b:	bf 01 00 00 00       	mov    $0x1,%edi
    3090:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    3095:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total Protected %ld\n", protected_state->protected);
  printf("Total V %ld\n", v);
  printf("\n");
  printf("Total Protected per second %ld\n", protected_state->protected / DURATION);
    309a:	49 bd 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%r13
    30a4:	4c 89 e2             	mov    %r12,%rdx
    30a7:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    30ac:	e8 7f f3 ff ff       	call   2430 <__printf_chk@plt>
    30b1:	bf 0a 00 00 00       	mov    $0xa,%edi
    30b6:	e8 05 f2 ff ff       	call   22c0 <putchar@plt>
    30bb:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
    30c0:	48 8d 35 0c 33 00 00 	lea    0x330c(%rip),%rsi        # 63d3 <_IO_stdin_used+0x3d3>
    30c7:	31 c0                	xor    %eax,%eax
    30c9:	bf 01 00 00 00       	mov    $0x1,%edi
    30ce:	49 8b 16             	mov    (%r14),%rdx
    30d1:	e8 5a f3 ff ff       	call   2430 <__printf_chk@plt>
    30d6:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    30db:	48 8d 35 06 33 00 00 	lea    0x3306(%rip),%rsi        # 63e8 <_IO_stdin_used+0x3e8>
    30e2:	31 c0                	xor    %eax,%eax
    30e4:	bf 01 00 00 00       	mov    $0x1,%edi
    30e9:	e8 42 f3 ff ff       	call   2430 <__printf_chk@plt>
    30ee:	bf 0a 00 00 00       	mov    $0xa,%edi
    30f3:	e8 c8 f1 ff ff       	call   22c0 <putchar@plt>
    30f8:	49 8b 36             	mov    (%r14),%rsi
    30fb:	bf 01 00 00 00       	mov    $0x1,%edi
    3100:	48 89 f0             	mov    %rsi,%rax
    3103:	49 f7 ed             	imul   %r13
    3106:	31 c0                	xor    %eax,%eax
    3108:	48 01 f2             	add    %rsi,%rdx
    310b:	48 c1 fe 3f          	sar    $0x3f,%rsi
    310f:	48 c1 fa 04          	sar    $0x4,%rdx
    3113:	48 29 f2             	sub    %rsi,%rdx
    3116:	48 8d 35 0b 35 00 00 	lea    0x350b(%rip),%rsi        # 6628 <_IO_stdin_used+0x628>
    311d:	e8 0e f3 ff ff       	call   2430 <__printf_chk@plt>
    3122:	49 8b 56 08          	mov    0x8(%r14),%rdx
    3126:	bf 01 00 00 00       	mov    $0x1,%edi
    312b:	31 c0                	xor    %eax,%eax
    312d:	48 8d 35 14 35 00 00 	lea    0x3514(%rip),%rsi        # 6648 <_IO_stdin_used+0x648>
    3134:	e8 f7 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3139:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    313e:	bf 01 00 00 00       	mov    $0x1,%edi
    3143:	48 8d 35 26 35 00 00 	lea    0x3526(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    314a:	4c 89 d8             	mov    %r11,%rax
    314d:	49 f7 ed             	imul   %r13
    3150:	31 c0                	xor    %eax,%eax
    3152:	4c 01 da             	add    %r11,%rdx
    3155:	49 c1 fb 3f          	sar    $0x3f,%r11
    3159:	48 c1 fa 04          	sar    $0x4,%rdx
    315d:	4c 29 da             	sub    %r11,%rdx
    3160:	e8 cb f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3165:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    316a:	bf 01 00 00 00       	mov    $0x1,%edi
    316f:	48 8d 35 2a 35 00 00 	lea    0x352a(%rip),%rsi        # 66a0 <_IO_stdin_used+0x6a0>
    3176:	48 89 c8             	mov    %rcx,%rax
    3179:	49 f7 ed             	imul   %r13
    317c:	31 c0                	xor    %eax,%eax
    317e:	48 01 ca             	add    %rcx,%rdx
    3181:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3185:	48 c1 fa 04          	sar    $0x4,%rdx
    3189:	48 29 ca             	sub    %rcx,%rdx
    318c:	e8 9f f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3191:	4c 89 e0             	mov    %r12,%rax
    3194:	bf 01 00 00 00       	mov    $0x1,%edi
    3199:	48 8d 35 30 35 00 00 	lea    0x3530(%rip),%rsi        # 66d0 <_IO_stdin_used+0x6d0>
    31a0:	49 f7 ed             	imul   %r13
    31a3:	4c 01 e2             	add    %r12,%rdx
    31a6:	49 c1 fc 3f          	sar    $0x3f,%r12
    31aa:	31 c0                	xor    %eax,%eax
    31ac:	48 c1 fa 04          	sar    $0x4,%rdx
    31b0:	4c 29 e2             	sub    %r12,%rdx
    31b3:	e8 78 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    31b8:	48 89 e8             	mov    %rbp,%rax
    31bb:	bf 01 00 00 00       	mov    $0x1,%edi
    31c0:	48 8d 35 2e 32 00 00 	lea    0x322e(%rip),%rsi        # 63f5 <_IO_stdin_used+0x3f5>
    31c7:	49 f7 ed             	imul   %r13
    31ca:	31 c0                	xor    %eax,%eax
    31cc:	48 01 ea             	add    %rbp,%rdx
    31cf:	48 c1 fd 3f          	sar    $0x3f,%rbp
    31d3:	48 c1 fa 04          	sar    $0x4,%rdx
    31d7:	48 29 ea             	sub    %rbp,%rdx
    31da:	e8 51 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    31df:	48 89 d8             	mov    %rbx,%rax
    31e2:	bf 01 00 00 00       	mov    $0x1,%edi
    31e7:	48 8d 35 18 32 00 00 	lea    0x3218(%rip),%rsi        # 6406 <_IO_stdin_used+0x406>
    31ee:	49 f7 ed             	imul   %r13
    31f1:	31 c0                	xor    %eax,%eax
    31f3:	48 01 da             	add    %rbx,%rdx
    31f6:	48 c1 fb 3f          	sar    $0x3f,%rbx
    31fa:	48 c1 fa 04          	sar    $0x4,%rdx
    31fe:	48 29 da             	sub    %rbx,%rdx
    3201:	e8 2a f2 ff ff       	call   2430 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3206:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    320b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3214:	75 4e                	jne    3264 <main+0xc94>
    3216:	48 83 c4 68          	add    $0x68,%rsp
    321a:	31 c0                	xor    %eax,%eax
    321c:	5b                   	pop    %rbx
    321d:	5d                   	pop    %rbp
    321e:	41 5c                	pop    %r12
    3220:	41 5d                	pop    %r13
    3222:	41 5e                	pop    %r14
    3224:	41 5f                	pop    %r15
    3226:	c3                   	ret
    3227:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          thread_data[x].tasks[y].run = barriered_work; 
    3230:	48 8d 05 d9 1f 00 00 	lea    0x1fd9(%rip),%rax        # 5210 <barriered_work>
    3237:	41 bd 06 00 00 00    	mov    $0x6,%r13d
    323d:	48 89 85 08 02 00 00 	mov    %rax,0x208(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3244:	e9 19 f8 ff ff       	jmp    2a62 <main+0x492>
    3249:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            thread_data[x].tasks[y].protected = do_protected_write; 
    3250:	48 8d 05 09 01 00 00 	lea    0x109(%rip),%rax        # 3360 <do_protected_write>
    3257:	4b 89 84 27 10 02 00 00 	mov    %rax,0x210(%r15,%r12,1)
    325f:	e9 e3 f5 ff ff       	jmp    2847 <main+0x277>
}
    3264:	e8 a7 f0 ff ff       	call   2310 <__stack_chk_fail@plt>
    3269:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

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
int do_protected_write(struct BarrierTask *data) {
    3360:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3364:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    336b:	48 8b 40 30          	mov    0x30(%rax),%rax
  data->v++; // thread local
    336f:	48 83 87 00 02 00 00 01 	addq   $0x1,0x200(%rdi)
  if (protected->balance > 0) {
    3377:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    337b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    337f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3386:	48 85 c9             	test   %rcx,%rcx
    3389:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3390:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3394:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3398:	31 c0                	xor    %eax,%eax
    339a:	c3                   	ret
    339b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000033a0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    33a0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    33a4:	48 63 87 84 02 00 00 	movslq 0x284(%rdi),%rax
    33ab:	85 c0                	test   %eax,%eax
    33ad:	7e 57                	jle    3406 <barriered_reset+0x66>
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    33af:	48 8b 8f 18 02 00 00 	mov    0x218(%rdi),%rcx
    33b6:	48 63 97 20 02 00 00 	movslq 0x220(%rdi),%rdx
      data->thread->tasks[x].available = 1; 
    33bd:	48 8b 71 20          	mov    0x20(%rcx),%rsi
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    33c1:	48 c1 e2 08          	shl    $0x8,%rdx
    33c5:	48 03 51 10          	add    0x10(%rcx),%rdx
    33c9:	48 8d 0c 80          	lea    (%rax,%rax,4),%rcx
    33cd:	48 8d 0c 48          	lea    (%rax,%rcx,2),%rcx
    33d1:	48 8b 52 20          	mov    0x20(%rdx),%rdx
      data->thread->tasks[x].available = 1; 
    33d5:	31 c0                	xor    %eax,%eax
    33d7:	48 c1 e1 07          	shl    $0x7,%rcx
    33db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    33e0:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index].tasks[x].prearrive++; 
    33e8:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    33f0:	c7 84 06 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    33fb:	48 05 80 05 00 00    	add    $0x580,%rax
    3401:	48 39 c1             	cmp    %rax,%rcx
    3404:	75 da                	jne    33e0 <barriered_reset+0x40>
  asm volatile ("mfence" ::: "memory");
    3406:	0f ae f0             	mfence
}
    3409:	31 c0                	xor    %eax,%eax
    340b:	c3                   	ret
    340c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003410 <barriered_thread>:
void* barriered_thread(void *arg) {
    3410:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3414:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
    3418:	0f 85 92 02 00 00    	jne    36b0 <barriered_thread+0x2a0>
void* barriered_thread(void *arg) {
    341e:	41 56                	push   %r14
    3420:	41 55                	push   %r13
    3422:	45 31 ed             	xor    %r13d,%r13d
    3425:	41 54                	push   %r12
    3427:	49 89 fc             	mov    %rdi,%r12
    342a:	55                   	push   %rbp
    342b:	53                   	push   %rbx
    342c:	31 db                	xor    %ebx,%ebx
    342e:	66 90                	xchg   %ax,%ax
    if (t >= data->task_count) {
    3430:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    3435:	39 da                	cmp    %ebx,%edx
    3437:	7f 13                	jg     344c <barriered_thread+0x3c>
      data->cycles++;
    3439:	49 83 84 24 90 00 00 00 01 	addq   $0x1,0x90(%r12)
    for (; t < data->task_count; t++) {
    3442:	31 db                	xor    %ebx,%ebx
    3444:	85 d2                	test   %edx,%edx
    3446:	0f 8e 5c 01 00 00    	jle    35a8 <barriered_thread+0x198>
    344c:	48 63 c3             	movslq %ebx,%rax
    344f:	48 8d 0c 80          	lea    (%rax,%rax,4),%rcx
    3453:	48 8d 2c 48          	lea    (%rax,%rcx,2),%rbp
    3457:	48 c1 e5 07          	shl    $0x7,%rbp
    345b:	eb 15                	jmp    3472 <barriered_thread+0x62>
    345d:	0f 1f 00             	nopl   (%rax)
    3460:	83 c3 01             	add    $0x1,%ebx
    3463:	48 81 c5 80 05 00 00 	add    $0x580,%rbp
    346a:	39 d3                	cmp    %edx,%ebx
    346c:	0f 8d 36 01 00 00    	jge    35a8 <barriered_thread+0x198>
      if (data->tasks[t].available == 1) {
    3472:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3477:	48 8d 0c 28          	lea    (%rax,%rbp,1),%rcx
    347b:	83 b9 80 02 00 00 01 	cmpl   $0x1,0x280(%rcx)
    3482:	75 dc                	jne    3460 <barriered_thread+0x50>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3484:	41 8b 7c 24 18       	mov    0x18(%r12),%edi
          previous = t - 1;
    3489:	83 ea 01             	sub    $0x1,%edx
    348c:	8d 73 ff             	lea    -0x1(%rbx),%esi
    348f:	85 db                	test   %ebx,%ebx
    3491:	0f 4f d6             	cmovg  %esi,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3494:	85 ff                	test   %edi,%edi
    3496:	0f 8e 9c 01 00 00    	jle    3638 <barriered_thread+0x228>
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    349c:	48 63 d2             	movslq %edx,%rdx
    349f:	44 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9d
        int prearrive = 0; 
    34a6:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    34a9:	45 31 f6             	xor    %r14d,%r14d
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    34ac:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
          if (data->threads[thread].tasks[previous].prearrive == data->tasks[t].prearrive) {
    34b0:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    34b7:	48 63 cf             	movslq %edi,%rcx
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    34ba:	48 8d 34 42          	lea    (%rdx,%rax,2),%rsi
    34be:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    34c3:	48 c1 e1 08          	shl    $0x8,%rcx
    34c7:	48 c1 e6 07          	shl    $0x7,%rsi
    34cb:	48 01 c1             	add    %rax,%rcx
    34ce:	66 90                	xchg   %ax,%ax
    34d0:	48 8b 50 20          	mov    0x20(%rax),%rdx
    34d4:	48 01 f2             	add    %rsi,%rdx
    34d7:	44 3b 8a 80 00 00 00 	cmp    0x80(%rdx),%r9d
    34de:	75 04                	jne    34e4 <barriered_thread+0xd4>
            arrived++;
    34e0:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread].tasks[previous].prearrive == data->tasks[t].prearrive) {
    34e4:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    34eb:	75 04                	jne    34f1 <barriered_thread+0xe1>
            prearrive++;
    34ed:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    34f1:	48 05 00 01 00 00    	add    $0x100,%rax
    34f7:	48 39 c8             	cmp    %rcx,%rax
    34fa:	75 d4                	jne    34d0 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    34fc:	44 39 d7             	cmp    %r10d,%edi
    34ff:	0f 84 bb 00 00 00    	je     35c0 <barriered_thread+0x1b0>
    3505:	45 85 d2             	test   %r10d,%r10d
    3508:	0f 84 b2 00 00 00    	je     35c0 <barriered_thread+0x1b0>
        if (arrived == 0 || arrived == data->thread_count) {
    350e:	45 85 f6             	test   %r14d,%r14d
    3511:	74 0b                	je     351e <barriered_thread+0x10e>
    3513:	45 39 74 24 18       	cmp    %r14d,0x18(%r12)
    3518:	0f 85 8a 00 00 00    	jne    35a8 <barriered_thread+0x198>
    351e:	49 8b 44 24 20       	mov    0x20(%r12),%rax
          data->tasks[t].prearrive++;
    3523:	48 01 e8             	add    %rbp,%rax
    3526:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    352d:	85 db                	test   %ebx,%ebx
    352f:	75 10                	jne    3541 <barriered_thread+0x131>
    3531:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    3536:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    353b:	0f 8c 4f 01 00 00    	jl     3690 <barriered_thread+0x280>
          data->tasks[t].available = 0;
    3541:	c7 80 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rax)
          data->tasks[t].run(&data->threads[data->thread_index].tasks[t]);
    354b:	49 63 14 24          	movslq (%r12),%rdx
    354f:	48 c1 e2 08          	shl    $0x8,%rdx
    3553:	49 03 54 24 10       	add    0x10(%r12),%rdx
    3558:	48 8b 7a 20          	mov    0x20(%rdx),%rdi
    355c:	48 01 ef             	add    %rbp,%rdi
    355f:	ff 90 08 02 00 00    	call   *0x208(%rax)
          data->tasks[t].arrived++;
    3565:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    356a:	48 01 e8             	add    %rbp,%rax
    356d:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3574:	41 8b 44 24 28       	mov    0x28(%r12),%eax
          data->iteration_count++;
    3579:	49 83 44 24 60 01    	addq   $0x1,0x60(%r12)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    357f:	83 e8 01             	sub    $0x1,%eax
    3582:	39 d8                	cmp    %ebx,%eax
    3584:	74 52                	je     35d8 <barriered_thread+0x1c8>
          asm volatile ("mfence" ::: "memory");
    3586:	0f ae f0             	mfence
          if (waiting == 0) {
    3589:	45 85 ed             	test   %r13d,%r13d
    358c:	74 72                	je     3600 <barriered_thread+0x1f0>
    for (; t < data->task_count; t++) {
    358e:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    3593:	83 c3 01             	add    $0x1,%ebx
    3596:	48 81 c5 80 05 00 00 	add    $0x580,%rbp
    359d:	39 d3                	cmp    %edx,%ebx
    359f:	0f 8c cd fe ff ff    	jl     3472 <barriered_thread+0x62>
    35a5:	0f 1f 00             	nopl   (%rax)
  while (data->running == 1) {
    35a8:	41 83 7c 24 2c 01    	cmpl   $0x1,0x2c(%r12)
    35ae:	0f 84 7c fe ff ff    	je     3430 <barriered_thread+0x20>
}
    35b4:	5b                   	pop    %rbx
    35b5:	31 c0                	xor    %eax,%eax
    35b7:	5d                   	pop    %rbp
    35b8:	41 5c                	pop    %r12
    35ba:	41 5d                	pop    %r13
    35bc:	41 5e                	pop    %r14
    35be:	c3                   	ret
    35bf:	90                   	nop
          if (waiting == 1) {
    35c0:	41 83 fd 01          	cmp    $0x1,%r13d
    35c4:	0f 84 7e 00 00 00    	je     3648 <barriered_thread+0x238>
        int arrived = 0; 
    35ca:	45 31 ed             	xor    %r13d,%r13d
    35cd:	e9 3c ff ff ff       	jmp    350e <barriered_thread+0xfe>
    35d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    35d8:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    35dd:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    35e2:	7d a2                	jge    3586 <barriered_thread+0x176>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    35e4:	48 c1 e6 04          	shl    $0x4,%rsi
    35e8:	bf 04 00 00 00       	mov    $0x4,%edi
    35ed:	49 03 74 24 58       	add    0x58(%r12),%rsi
    35f2:	e8 f9 ec ff ff       	call   22f0 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    35f7:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
    35fd:	eb 87                	jmp    3586 <barriered_thread+0x176>
    35ff:	90                   	nop
            data->task_snapshot[data->task_timestamp_count].task = t;
    3600:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3608:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    360d:	41 bd 01 00 00 00    	mov    $0x1,%r13d
            data->task_snapshot[data->task_timestamp_count].task = t;
    3613:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3617:	49 8b 44 24 78       	mov    0x78(%r12),%rax
    361c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3620:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3623:	e8 c8 ec ff ff       	call   22f0 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3628:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    362d:	e9 2e fe ff ff       	jmp    3460 <barriered_thread+0x50>
    3632:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (waiting == 1) {
    3638:	41 83 fd 01          	cmp    $0x1,%r13d
    363c:	0f 85 e1 fe ff ff    	jne    3523 <barriered_thread+0x113>
        int arrived = 0; 
    3642:	45 31 f6             	xor    %r14d,%r14d
    3645:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3648:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3650:	bf 04 00 00 00       	mov    $0x4,%edi
    3655:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3659:	49 8b 44 24 78       	mov    0x78(%r12),%rax
    365e:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3663:	e8 88 ec ff ff       	call   22f0 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3668:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3670:	48 83 c0 01          	add    $0x1,%rax
    3674:	48 99                	cqto
    3676:	49 f7 bc 24 88 00 00 00 	idivq  0x88(%r12)
    367e:	49 89 94 24 80 00 00 00 	mov    %rdx,0x80(%r12)
          if (waiting == 3) {
    3686:	e9 3f ff ff ff       	jmp    35ca <barriered_thread+0x1ba>
    368b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3690:	48 c1 e6 04          	shl    $0x4,%rsi
    3694:	bf 04 00 00 00       	mov    $0x4,%edi
    3699:	49 03 74 24 50       	add    0x50(%r12),%rsi
    369e:	e8 4d ec ff ff       	call   22f0 <clock_gettime@plt>
          data->tasks[t].available = 0;
    36a3:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    36a8:	48 01 e8             	add    %rbp,%rax
    36ab:	e9 91 fe ff ff       	jmp    3541 <barriered_thread+0x131>
}
    36b0:	31 c0                	xor    %eax,%eax
    36b2:	c3                   	ret
    36b3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    36be:	66 90                	xchg   %ax,%ax

00000000000036c0 <external_thread>:
void * external_thread(void *arg) {
    36c0:	f3 0f 1e fa          	endbr64
    36c4:	41 55                	push   %r13
    36c6:	41 54                	push   %r12
    36c8:	55                   	push   %rbp
    36c9:	53                   	push   %rbx
    36ca:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    36ce:	66 0f 6f 05 1a 32 00 00 	movdqa 0x321a(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
void * external_thread(void *arg) {
    36d6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    36df:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    36e4:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    36e6:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
  struct timespec req = {
    36ea:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    36ee:	75 6c                	jne    375c <external_thread+0x9c>
    36f0:	49 89 fd             	mov    %rdi,%r13
    36f3:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    36f8:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    36fb:	4c 8d 25 02 29 00 00 	lea    0x2902(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    3702:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    nanosleep(&req , &rem);
    3708:	48 89 ee             	mov    %rbp,%rsi
    370b:	48 89 df             	mov    %rbx,%rdi
    370e:	e8 1d ec ff ff       	call   2330 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3713:	49 8b 45 38          	mov    0x38(%r13),%rax
    3717:	48 63 10             	movslq (%rax),%rdx
    371a:	85 d2                	test   %edx,%edx
    371c:	7e 34                	jle    3752 <external_thread+0x92>
    371e:	48 8b 40 08          	mov    0x8(%rax),%rax
    3722:	48 c1 e2 08          	shl    $0x8,%rdx
    3726:	48 01 c2             	add    %rax,%rdx
    3729:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    3730:	8b 88 80 00 00 00    	mov    0x80(%rax),%ecx
    3736:	85 c9                	test   %ecx,%ecx
    3738:	75 0d                	jne    3747 <external_thread+0x87>
        data->buffers->buffer[x].data = "Hello world";
    373a:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    373d:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3747:	48 05 00 01 00 00    	add    $0x100,%rax
    374d:	48 39 c2             	cmp    %rax,%rdx
    3750:	75 de                	jne    3730 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    3752:	0f ae f0             	mfence
  while (data->running == 1) {
    3755:	41 83 7d 2c 01       	cmpl   $0x1,0x2c(%r13)
    375a:	74 ac                	je     3708 <external_thread+0x48>
}
    375c:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3761:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    376a:	75 0d                	jne    3779 <external_thread+0xb9>
    376c:	48 83 c4 38          	add    $0x38,%rsp
    3770:	31 c0                	xor    %eax,%eax
    3772:	5b                   	pop    %rbx
    3773:	5d                   	pop    %rbp
    3774:	41 5c                	pop    %r12
    3776:	41 5d                	pop    %r13
    3778:	c3                   	ret
    3779:	e8 92 eb ff ff       	call   2310 <__stack_chk_fail@plt>
    377e:	66 90                	xchg   %ax,%ax

0000000000003780 <timer_thread>:
void* timer_thread(void *arg) {
    3780:	f3 0f 1e fa          	endbr64
    3784:	41 57                	push   %r15
    3786:	48 8d 35 83 28 00 00 	lea    0x2883(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    378d:	49 89 ff             	mov    %rdi,%r15
    3790:	41 56                	push   %r14
    3792:	41 55                	push   %r13
    3794:	41 54                	push   %r12
    3796:	55                   	push   %rbp
    3797:	53                   	push   %rbx
    3798:	48 83 ec 58          	sub    $0x58,%rsp
    379c:	8b 17                	mov    (%rdi),%edx
    379e:	bf 01 00 00 00       	mov    $0x1,%edi
    37a3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    37ac:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    37b1:	31 c0                	xor    %eax,%eax
    37b3:	e8 78 ec ff ff       	call   2430 <__printf_chk@plt>
  struct timespec preempt = {
    37b8:	66 0f 6f 05 30 31 00 00 	movdqa 0x3130(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    37c0:	ba 30 75 00 00       	mov    $0x7530,%edx
    37c5:	31 c0                	xor    %eax,%eax
    37c7:	48 8d 35 54 28 00 00 	lea    0x2854(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    37ce:	bf 01 00 00 00       	mov    $0x1,%edi
    37d3:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    37d8:	e8 53 ec ff ff       	call   2430 <__printf_chk@plt>
  while (data->running && n < times) {
    37dd:	45 8b 6f 2c          	mov    0x2c(%r15),%r13d
    37e1:	45 85 ed             	test   %r13d,%r13d
    37e4:	0f 84 af 00 00 00    	je     3899 <timer_thread+0x119>
  int n = 0;
    37ea:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    37ed:	45 31 ed             	xor    %r13d,%r13d
    37f0:	49 89 e4             	mov    %rsp,%r12
    y++;
    37f3:	31 db                	xor    %ebx,%ebx
    37f5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    37fa:	48 89 ef             	mov    %rbp,%rdi
    37fd:	4c 89 e6             	mov    %r12,%rsi
    n++;
    3800:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3804:	e8 27 eb ff ff       	call   2330 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3809:	41 8b 47 18          	mov    0x18(%r15),%eax
    y++;
    380d:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3811:	85 c0                	test   %eax,%eax
    3813:	7e 5f                	jle    3874 <timer_thread+0xf4>
    3815:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x].tasks[y].scheduled = 0;
    3819:	4b 8d 54 ad 00       	lea    0x0(%r13,%r13,4),%rdx
    381e:	4c 63 c0             	movslq %eax,%r8
    3821:	4d 8d 4c 55 00       	lea    0x0(%r13,%rdx,2),%r9
    3826:	49 c1 e0 08          	shl    $0x8,%r8
    382a:	49 c1 e1 07          	shl    $0x7,%r9
    382e:	49 01 c8             	add    %rcx,%r8
    3831:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x].task_count;
    3838:	89 f8                	mov    %edi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    383a:	48 8b 71 20          	mov    0x20(%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    383e:	99                   	cltd
    383f:	f7 79 28             	idivl  0x28(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3842:	48 81 c1 00 01 00 00 	add    $0x100,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    3849:	48 63 d2             	movslq %edx,%rdx
    384c:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    3850:	48 8d 04 42          	lea    (%rdx,%rax,2),%rax
    3854:	48 c1 e0 07          	shl    $0x7,%rax
    3858:	c7 84 06 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rsi,%rax,1)
        data->threads[x].tasks[y].scheduled = 0;
    3863:	42 c7 84 0e 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rsi,%r9,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    386f:	49 39 c8             	cmp    %rcx,%r8
    3872:	75 c4                	jne    3838 <timer_thread+0xb8>
    asm volatile ("mfence" ::: "memory");
    3874:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    3877:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    387b:	41 8b 57 2c          	mov    0x2c(%r15),%edx
    y++;
    387f:	39 78 28             	cmp    %edi,0x28(%rax)
    3882:	0f 4e fb             	cmovle %ebx,%edi
    3885:	4c 63 ef             	movslq %edi,%r13
  while (data->running && n < times) {
    3888:	85 d2                	test   %edx,%edx
    388a:	74 0d                	je     3899 <timer_thread+0x119>
    388c:	41 81 fe 30 75 00 00 	cmp    $0x7530,%r14d
    3893:	0f 85 61 ff ff ff    	jne    37fa <timer_thread+0x7a>
    3899:	48 8d 3d 98 27 00 00 	lea    0x2798(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    38a0:	e8 2b ea ff ff       	call   22d0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    38a5:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    38a9:	85 d2                	test   %edx,%edx
    38ab:	7e 6a                	jle    3917 <timer_thread+0x197>
    for (int y = 0 ; y < data->task_count ; y++) {
    38ad:	49 63 47 28          	movslq 0x28(%r15),%rax
    38b1:	85 c0                	test   %eax,%eax
    38b3:	7e 62                	jle    3917 <timer_thread+0x197>
    38b5:	48 8d 0c 80          	lea    (%rax,%rax,4),%rcx
      data->threads[x].tasks[y].sending = 0;
    38b9:	4d 8b 47 10          	mov    0x10(%r15),%r8
    38bd:	48 c1 e2 08          	shl    $0x8,%rdx
    38c1:	31 f6                	xor    %esi,%esi
    38c3:	48 8d 3c 48          	lea    (%rax,%rcx,2),%rdi
    38c7:	48 c1 e7 07          	shl    $0x7,%rdi
    for (int y = 0 ; y < data->task_count ; y++) {
    38cb:	49 8b 44 30 20       	mov    0x20(%r8,%rsi,1),%rax
    38d0:	48 8d 0c 07          	lea    (%rdi,%rax,1),%rcx
    38d4:	40 f6 c7 80          	test   $0x80,%dil
    38d8:	74 15                	je     38ef <timer_thread+0x16f>
      data->threads[x].tasks[y].sending = 0;
    38da:	c7 80 08 05 00 00 00 00 00 00 	movl   $0x0,0x508(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    38e4:	48 05 80 05 00 00    	add    $0x580,%rax
    38ea:	48 39 c1             	cmp    %rax,%rcx
    38ed:	74 1c                	je     390b <timer_thread+0x18b>
      data->threads[x].tasks[y].sending = 0;
    38ef:	c7 80 08 05 00 00 00 00 00 00 	movl   $0x0,0x508(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    38f9:	48 05 00 0b 00 00    	add    $0xb00,%rax
      data->threads[x].tasks[y].sending = 0;
    38ff:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3906:	48 39 c1             	cmp    %rax,%rcx
    3909:	75 e4                	jne    38ef <timer_thread+0x16f>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    390b:	48 81 c6 00 01 00 00 	add    $0x100,%rsi
    3912:	48 39 f2             	cmp    %rsi,%rdx
    3915:	75 b4                	jne    38cb <timer_thread+0x14b>
  asm volatile ("mfence" ::: "memory");
    3917:	0f ae f0             	mfence
  struct timespec drain = {
    391a:	66 0f 6f 05 de 2f 00 00 	movdqa 0x2fde(%rip),%xmm0        # 6900 <_IO_stdin_used+0x900>
    3922:	48 8d 2d 34 27 00 00 	lea    0x2734(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    3929:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    392e:	41 8b 47 18          	mov    0x18(%r15),%eax
    y++;
    3932:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3936:	85 c0                	test   %eax,%eax
    3938:	7e 62                	jle    399c <timer_thread+0x21c>
        data->threads[x].tasks[y].scheduled = 0;
    393a:	4d 63 ed             	movslq %r13d,%r13
    393d:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3941:	4c 63 c0             	movslq %eax,%r8
    3944:	4b 8d 54 ad 00       	lea    0x0(%r13,%r13,4),%rdx
    3949:	49 c1 e0 08          	shl    $0x8,%r8
    394d:	4d 8d 4c 55 00       	lea    0x0(%r13,%rdx,2),%r9
    3952:	49 01 c8             	add    %rcx,%r8
    3955:	49 c1 e1 07          	shl    $0x7,%r9
    3959:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x].task_count;
    3960:	89 f8                	mov    %edi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    3962:	48 8b 71 20          	mov    0x20(%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    3966:	99                   	cltd
    3967:	f7 79 28             	idivl  0x28(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    396a:	48 81 c1 00 01 00 00 	add    $0x100,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    3971:	48 63 c2             	movslq %edx,%rax
    3974:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3978:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    397c:	48 c1 e0 07          	shl    $0x7,%rax
    3980:	c7 84 06 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rsi,%rax,1)
        data->threads[x].tasks[y].scheduled = 0;
    398b:	42 c7 84 0e 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rsi,%r9,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3997:	4c 39 c1             	cmp    %r8,%rcx
    399a:	75 c4                	jne    3960 <timer_thread+0x1e0>
    asm volatile ("mfence" ::: "memory");
    399c:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    399f:	49 8b 57 10          	mov    0x10(%r15),%rdx
    y++;
    39a3:	45 31 ed             	xor    %r13d,%r13d
    39a6:	39 7a 28             	cmp    %edi,0x28(%rdx)
    39a9:	44 0f 4f ef          	cmovg  %edi,%r13d
    for (int x = 0 ; x < data->thread_count ; x++) {
    39ad:	41 8b 7f 18          	mov    0x18(%r15),%edi
    39b1:	85 ff                	test   %edi,%edi
    39b3:	0f 8e c7 00 00 00    	jle    3a80 <timer_thread+0x300>
    39b9:	45 31 e4             	xor    %r12d,%r12d
    int all_empty = 1;
    39bc:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    39c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    39c8:	4c 89 e3             	mov    %r12,%rbx
            all_empty = 0;
    39cb:	45 31 f6             	xor    %r14d,%r14d
    39ce:	48 c1 e3 08          	shl    $0x8,%rbx
    39d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    39d8:	4b 8d 04 b6          	lea    (%r14,%r14,4),%rax
    39dc:	49 8d 04 46          	lea    (%r14,%rax,2),%rax
    39e0:	48 c1 e0 07          	shl    $0x7,%rax
    39e4:	48 03 44 1a 20       	add    0x20(%rdx,%rbx,1),%rax
        for (int k = 0 ; k < data->thread_count; k++) {
    39e9:	31 d2                	xor    %edx,%edx
    39eb:	48 8b 80 88 04 00 00 	mov    0x488(%rax),%rax
    39f2:	eb 16                	jmp    3a0a <timer_thread+0x28a>
    39f4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    39f8:	4d 85 c0             	test   %r8,%r8
    39fb:	7f 2a                	jg     3a27 <timer_thread+0x2a7>
        for (int k = 0 ; k < data->thread_count; k++) {
    39fd:	83 c2 01             	add    $0x1,%edx
    3a00:	48 05 00 02 00 00    	add    $0x200,%rax
    3a06:	39 fa                	cmp    %edi,%edx
    3a08:	74 33                	je     3a3d <timer_thread+0x2bd>
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3a0a:	48 8b 08             	mov    (%rax),%rcx
    3a0d:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    3a14:	48 8b 89 80 00 00 00 	mov    0x80(%rcx),%rcx
    3a1b:	4c 8b 86 80 00 00 00 	mov    0x80(%rsi),%r8
    3a22:	48 85 c9             	test   %rcx,%rcx
    3a25:	7e d1                	jle    39f8 <timer_thread+0x278>
    3a27:	bf 01 00 00 00       	mov    $0x1,%edi
    3a2c:	48 89 ee             	mov    %rbp,%rsi
    3a2f:	31 c0                	xor    %eax,%eax
    3a31:	e8 fa e9 ff ff       	call   2430 <__printf_chk@plt>
            break;
    3a36:	41 8b 7f 18          	mov    0x18(%r15),%edi
            all_empty = 0;
    3a3a:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->thread_count ; y++) {
    3a3d:	49 83 c6 01          	add    $0x1,%r14
    3a41:	44 39 f7             	cmp    %r14d,%edi
    3a44:	7e 0a                	jle    3a50 <timer_thread+0x2d0>
    3a46:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3a4a:	eb 8c                	jmp    39d8 <timer_thread+0x258>
    3a4c:	0f 1f 40 00          	nopl   0x0(%rax)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a50:	49 83 c4 01          	add    $0x1,%r12
    3a54:	44 39 e7             	cmp    %r12d,%edi
    3a57:	7e 0d                	jle    3a66 <timer_thread+0x2e6>
      for (int y = 0 ; y < data->thread_count ; y++) {
    3a59:	85 ff                	test   %edi,%edi
    3a5b:	7e 09                	jle    3a66 <timer_thread+0x2e6>
    3a5d:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3a61:	e9 62 ff ff ff       	jmp    39c8 <timer_thread+0x248>
    if (all_empty == 1) {
    3a66:	41 83 f9 01          	cmp    $0x1,%r9d
    3a6a:	74 14                	je     3a80 <timer_thread+0x300>
      nanosleep(&drain , &drainrem);
    3a6c:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3a71:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3a76:	e8 b5 e8 ff ff       	call   2330 <nanosleep@plt>
    3a7b:	e9 ae fe ff ff       	jmp    392e <timer_thread+0x1ae>
    3a80:	48 8d 3d cd 25 00 00 	lea    0x25cd(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3a87:	e8 44 e8 ff ff       	call   22d0 <puts@plt>
  while (data->running) {
    3a8c:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3a90:	85 c0                	test   %eax,%eax
    3a92:	0f 84 d2 00 00 00    	je     3b6a <timer_thread+0x3ea>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3a98:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3a9c:	85 c9                	test   %ecx,%ecx
    3a9e:	7e 34                	jle    3ad4 <timer_thread+0x354>
    3aa0:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3aa4:	31 db                	xor    %ebx,%ebx
    3aa6:	4c 8d 25 c1 25 00 00 	lea    0x25c1(%rip),%r12        # 606e <_IO_stdin_used+0x6e>
    3aad:	0f 1f 00             	nopl   (%rax)
      data->threads[x].running = 0;
    3ab0:	48 89 dd             	mov    %rbx,%rbp
    3ab3:	48 c1 e5 08          	shl    $0x8,%rbp
    3ab7:	48 8d 04 2a          	lea    (%rdx,%rbp,1),%rax
      if (data->threads[x].type == IO) {
    3abb:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
      data->threads[x].running = 0;
    3abf:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
      if (data->threads[x].type == IO) {
    3ac6:	0f 84 cb 00 00 00    	je     3b97 <timer_thread+0x417>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3acc:	48 83 c3 01          	add    $0x1,%rbx
    3ad0:	39 d9                	cmp    %ebx,%ecx
    3ad2:	7f dc                	jg     3ab0 <timer_thread+0x330>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ad4:	49 63 47 18          	movslq 0x18(%r15),%rax
    3ad8:	85 c0                	test   %eax,%eax
    3ada:	7e 77                	jle    3b53 <timer_thread+0x3d3>
      for (int y = 0 ; y < data->task_count ; y++) {
    3adc:	41 8b 57 28          	mov    0x28(%r15),%edx
    3ae0:	85 d2                	test   %edx,%edx
    3ae2:	7e 6f                	jle    3b53 <timer_thread+0x3d3>
    3ae4:	48 c1 e0 08          	shl    $0x8,%rax
        data->threads[x].tasks[y].scheduled = 0;
    3ae8:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3aec:	31 c9                	xor    %ecx,%ecx
    3aee:	48 89 c7             	mov    %rax,%rdi
    3af1:	48 63 c2             	movslq %edx,%rax
    3af4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3af8:	48 8d 34 50          	lea    (%rax,%rdx,2),%rsi
    3afc:	48 c1 e6 07          	shl    $0x7,%rsi
      for (int y = 0 ; y < data->task_count ; y++) {
    3b00:	49 8b 44 08 20       	mov    0x20(%r8,%rcx,1),%rax
    3b05:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3b09:	40 f6 c6 80          	test   $0x80,%sil
    3b0d:	74 19                	je     3b28 <timer_thread+0x3a8>
        data->threads[x].tasks[y].scheduled = 0;
    3b0f:	c7 80 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3b19:	48 05 80 05 00 00    	add    $0x580,%rax
    3b1f:	48 39 d0             	cmp    %rdx,%rax
    3b22:	74 23                	je     3b47 <timer_thread+0x3c7>
    3b24:	0f 1f 40 00          	nopl   0x0(%rax)
        data->threads[x].tasks[y].scheduled = 0;
    3b28:	c7 80 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3b32:	48 05 00 0b 00 00    	add    $0xb00,%rax
        data->threads[x].tasks[y].scheduled = 0;
    3b38:	c7 80 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3b42:	48 39 d0             	cmp    %rdx,%rax
    3b45:	75 e1                	jne    3b28 <timer_thread+0x3a8>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b47:	48 81 c1 00 01 00 00 	add    $0x100,%rcx
    3b4e:	48 39 f9             	cmp    %rdi,%rcx
    3b51:	75 ad                	jne    3b00 <timer_thread+0x380>
    asm volatile ("mfence" ::: "memory");
    3b53:	0f ae f0             	mfence
    3b56:	48 8d 3d 23 25 00 00 	lea    0x2523(%rip),%rdi        # 6080 <_IO_stdin_used+0x80>
    3b5d:	e8 6e e7 ff ff       	call   22d0 <puts@plt>
    data->running = 0;
    3b62:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
    3b6a:	48 8d 3d 16 25 00 00 	lea    0x2516(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3b71:	e8 5a e7 ff ff       	call   22d0 <puts@plt>
}
    3b76:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3b7b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3b84:	75 44                	jne    3bca <timer_thread+0x44a>
    3b86:	48 83 c4 58          	add    $0x58,%rsp
    3b8a:	31 c0                	xor    %eax,%eax
    3b8c:	5b                   	pop    %rbx
    3b8d:	5d                   	pop    %rbp
    3b8e:	41 5c                	pop    %r12
    3b90:	41 5d                	pop    %r13
    3b92:	41 5e                	pop    %r14
    3b94:	41 5f                	pop    %r15
    3b96:	c3                   	ret
    3b97:	4c 89 e7             	mov    %r12,%rdi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b9a:	48 83 c3 01          	add    $0x1,%rbx
    3b9e:	e8 2d e7 ff ff       	call   22d0 <puts@plt>
        eventfd_write(data->threads[x]._eventfd, 1);
    3ba3:	49 8b 47 10          	mov    0x10(%r15),%rax
    3ba7:	be 01 00 00 00       	mov    $0x1,%esi
    3bac:	8b 7c 28 48          	mov    0x48(%rax,%rbp,1),%edi
    3bb0:	e8 2b e8 ff ff       	call   23e0 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3bb5:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3bb9:	39 d9                	cmp    %ebx,%ecx
    3bbb:	0f 8e 13 ff ff ff    	jle    3ad4 <timer_thread+0x354>
    3bc1:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3bc5:	e9 e6 fe ff ff       	jmp    3ab0 <timer_thread+0x330>
}
    3bca:	e8 41 e7 ff ff       	call   2310 <__stack_chk_fail@plt>
    3bcf:	90                   	nop

0000000000003bd0 <strtolower>:
void strtolower(char *str) {
    3bd0:	f3 0f 1e fa          	endbr64
    3bd4:	55                   	push   %rbp
    3bd5:	53                   	push   %rbx
    3bd6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3bda:	48 0f be 1f          	movsbq (%rdi),%rbx
    3bde:	84 db                	test   %bl,%bl
    3be0:	74 24                	je     3c06 <strtolower+0x36>
    3be2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3be5:	e8 06 e9 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3bea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3bf0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3bf3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3bf7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3bfa:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3bfd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3c02:	84 db                	test   %bl,%bl
    3c04:	75 ea                	jne    3bf0 <strtolower+0x20>
}
    3c06:	48 83 c4 08          	add    $0x8,%rsp
    3c0a:	5b                   	pop    %rbx
    3c0b:	5d                   	pop    %rbp
    3c0c:	c3                   	ret
    3c0d:	0f 1f 00             	nopl   (%rax)

0000000000003c10 <zh_malloc>:
void *zh_malloc(size_t size) {
    3c10:	f3 0f 1e fa          	endbr64
    3c14:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3c18:	e8 d3 e7 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3c1d:	48 85 c0             	test   %rax,%rax
    3c20:	74 05                	je     3c27 <zh_malloc+0x17>
}
    3c22:	48 83 c4 08          	add    $0x8,%rsp
    3c26:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3c27:	48 8b 0d f2 53 00 00 	mov    0x53f2(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3c2e:	ba 28 00 00 00       	mov    $0x28,%edx
    3c33:	be 01 00 00 00       	mov    $0x1,%esi
    3c38:	48 8d 3d e1 27 00 00 	lea    0x27e1(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    3c3f:	e8 5c e8 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    3c44:	bf 01 00 00 00       	mov    $0x1,%edi
    3c49:	e8 32 e8 ff ff       	call   2480 <exit@plt>
    3c4e:	66 90                	xchg   %ax,%ax

0000000000003c50 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3c50:	f3 0f 1e fa          	endbr64
    3c54:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    3c55:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3c5a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3c5d:	e8 de e6 ff ff       	call   2340 <strrchr@plt>
    if (!dot || dot == filename)
    3c62:	48 85 c0             	test   %rax,%rax
    3c65:	74 11                	je     3c78 <get_filename_ext+0x28>
    3c67:	48 39 c3             	cmp    %rax,%rbx
    3c6a:	74 0c                	je     3c78 <get_filename_ext+0x28>
    return dot + 1;
    3c6c:	48 83 c0 01          	add    $0x1,%rax
}
    3c70:	5b                   	pop    %rbx
    3c71:	c3                   	ret
    3c72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    3c78:	48 8d 05 50 24 00 00 	lea    0x2450(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
}
    3c7f:	5b                   	pop    %rbx
    3c80:	c3                   	ret
    3c81:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3c8c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003c90 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3c90:	f3 0f 1e fa          	endbr64
    3c94:	41 55                	push   %r13
    3c96:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3c99:	48 89 fe             	mov    %rdi,%rsi
    3c9c:	41 54                	push   %r12
    3c9e:	55                   	push   %rbp
    3c9f:	48 89 d5             	mov    %rdx,%rbp
    3ca2:	ba 00 04 00 00       	mov    $0x400,%edx
    3ca7:	53                   	push   %rbx
    3ca8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3caf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3cb8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3cc0:	31 c0                	xor    %eax,%eax
    3cc2:	49 89 e4             	mov    %rsp,%r12
    3cc5:	4c 89 e7             	mov    %r12,%rdi
    3cc8:	e8 43 e7 ff ff       	call   2410 <__strcpy_chk@plt>
    for (; *str; ++str)
    3ccd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3cd2:	84 db                	test   %bl,%bl
    3cd4:	74 24                	je     3cfa <send_headers+0x6a>
        *str = (char)tolower(*str);
    3cd6:	e8 15 e8 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3cdb:	48 8b 08             	mov    (%rax),%rcx
    3cde:	4c 89 e0             	mov    %r12,%rax
    3ce1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3ce8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3ceb:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3cef:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3cf2:	48 0f be 18          	movsbq (%rax),%rbx
    3cf6:	84 db                	test   %bl,%bl
    3cf8:	75 ee                	jne    3ce8 <send_headers+0x58>
    void *buf = malloc(size);
    3cfa:	bf 11 00 00 00       	mov    $0x11,%edi
    3cff:	e8 ec e6 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3d04:	48 85 c0             	test   %rax,%rax
    3d07:	0f 84 7e 04 00 00    	je     418b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3d0d:	66 0f 6f 05 fb 2b 00 00 	movdqa 0x2bfb(%rip),%xmm0        # 6910 <_IO_stdin_used+0x910>
    iov[0].iov_base = zh_malloc(slen);
    3d15:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    3d19:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3d1e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3d26:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3d2a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3d2d:	e8 be e6 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3d32:	48 85 c0             	test   %rax,%rax
    3d35:	0f 84 50 04 00 00    	je     418b <send_headers+0x4fb>
    3d3b:	66 0f 6f 05 dd 2b 00 00 	movdqa 0x2bdd(%rip),%xmm0        # 6920 <_IO_stdin_used+0x920>
    iov[1].iov_base = zh_malloc(slen);
    3d43:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    3d47:	4c 89 e7             	mov    %r12,%rdi
    3d4a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3d54:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3d5c:	0f 11 00             	movups %xmm0,(%rax)
    3d5f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3d63:	be 2e 00 00 00       	mov    $0x2e,%esi
    3d68:	e8 d3 e5 ff ff       	call   2340 <strrchr@plt>
    if (!dot || dot == filename)
    3d6d:	48 85 c0             	test   %rax,%rax
    3d70:	0f 84 ea 02 00 00    	je     4060 <send_headers+0x3d0>
    3d76:	4c 39 e0             	cmp    %r12,%rax
    3d79:	0f 84 e1 02 00 00    	je     4060 <send_headers+0x3d0>
    return dot + 1;
    3d7f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3d83:	48 8d 3d 13 23 00 00 	lea    0x2313(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3d8a:	48 89 de             	mov    %rbx,%rsi
    3d8d:	e8 fe e5 ff ff       	call   2390 <strcmp@plt>
    3d92:	85 c0                	test   %eax,%eax
    3d94:	75 20                	jne    3db6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3d96:	66 0f 6f 05 92 2b 00 00 	movdqa 0x2b92(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3d9e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3da6:	66 0f 6f 05 92 2b 00 00 	movdqa 0x2b92(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3dae:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    3db6:	48 89 de             	mov    %rbx,%rsi
    3db9:	48 8d 3d e1 22 00 00 	lea    0x22e1(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3dc0:	e8 cb e5 ff ff       	call   2390 <strcmp@plt>
    3dc5:	85 c0                	test   %eax,%eax
    3dc7:	75 20                	jne    3de9 <send_headers+0x159>
    3dc9:	66 0f 6f 05 5f 2b 00 00 	movdqa 0x2b5f(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3dd1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3dd9:	66 0f 6f 05 5f 2b 00 00 	movdqa 0x2b5f(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3de1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    3de9:	48 89 de             	mov    %rbx,%rsi
    3dec:	48 8d 3d b3 22 00 00 	lea    0x22b3(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3df3:	e8 98 e5 ff ff       	call   2390 <strcmp@plt>
    3df8:	85 c0                	test   %eax,%eax
    3dfa:	0f 84 10 02 00 00    	je     4010 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    3e00:	48 89 de             	mov    %rbx,%rsi
    3e03:	48 8d 3d a0 22 00 00 	lea    0x22a0(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3e0a:	e8 81 e5 ff ff       	call   2390 <strcmp@plt>
    3e0f:	85 c0                	test   %eax,%eax
    3e11:	0f 84 a9 02 00 00    	je     40c0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    3e17:	48 89 de             	mov    %rbx,%rsi
    3e1a:	48 8d 3d 8d 22 00 00 	lea    0x228d(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3e21:	e8 6a e5 ff ff       	call   2390 <strcmp@plt>
    3e26:	85 c0                	test   %eax,%eax
    3e28:	0f 84 6a 02 00 00    	je     4098 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    3e2e:	48 89 de             	mov    %rbx,%rsi
    3e31:	48 8d 3d b9 22 00 00 	lea    0x22b9(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3e38:	e8 53 e5 ff ff       	call   2390 <strcmp@plt>
    3e3d:	85 c0                	test   %eax,%eax
    3e3f:	0f 84 2b 02 00 00    	je     4070 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    3e45:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3e48:	0f 84 52 01 00 00    	je     3fa0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    3e4e:	48 89 de             	mov    %rbx,%rsi
    3e51:	48 8d 3d 5a 22 00 00 	lea    0x225a(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3e58:	e8 33 e5 ff ff       	call   2390 <strcmp@plt>
    3e5d:	85 c0                	test   %eax,%eax
    3e5f:	0f 84 ab 02 00 00    	je     4110 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    3e65:	48 89 de             	mov    %rbx,%rsi
    3e68:	48 8d 3d 47 22 00 00 	lea    0x2247(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3e6f:	e8 1c e5 ff ff       	call   2390 <strcmp@plt>
    3e74:	85 c0                	test   %eax,%eax
    3e76:	0f 84 6c 02 00 00    	je     40e8 <send_headers+0x458>
    slen = strlen(send_buffer);
    3e7c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3e84:	4c 89 e7             	mov    %r12,%rdi
    3e87:	e8 74 e4 ff ff       	call   2300 <strlen@plt>
    void *buf = malloc(size);
    3e8c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3e8f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3e92:	e8 59 e5 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3e97:	48 85 c0             	test   %rax,%rax
    3e9a:	0f 84 eb 02 00 00    	je     418b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    3ea0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    3ea4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    3ea8:	83 fb 08             	cmp    $0x8,%ebx
    3eab:	0f 83 3f 01 00 00    	jae    3ff0 <send_headers+0x360>
    3eb1:	f6 c3 04             	test   $0x4,%bl
    3eb4:	0f 85 7b 02 00 00    	jne    4135 <send_headers+0x4a5>
    3eba:	85 db                	test   %ebx,%ebx
    3ebc:	74 13                	je     3ed1 <send_headers+0x241>
    3ebe:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3ec6:	88 10                	mov    %dl,(%rax)
    3ec8:	f6 c3 02             	test   $0x2,%bl
    3ecb:	0f 85 96 02 00 00    	jne    4167 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3ed1:	4d 89 e8             	mov    %r13,%r8
    3ed4:	48 8d 0d df 21 00 00 	lea    0x21df(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    3edb:	4c 89 e7             	mov    %r12,%rdi
    3ede:	31 c0                	xor    %eax,%eax
    3ee0:	ba 00 04 00 00       	mov    $0x400,%edx
    3ee5:	be 01 00 00 00       	mov    $0x1,%esi
    3eea:	e8 11 e6 ff ff       	call   2500 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    3eef:	4c 89 e7             	mov    %r12,%rdi
    3ef2:	e8 09 e4 ff ff       	call   2300 <strlen@plt>
    void *buf = malloc(size);
    3ef7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3efa:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3efd:	e8 ee e4 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3f02:	48 85 c0             	test   %rax,%rax
    3f05:	0f 84 80 02 00 00    	je     418b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    3f0b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    3f0f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    3f13:	83 fb 08             	cmp    $0x8,%ebx
    3f16:	0f 83 1c 01 00 00    	jae    4038 <send_headers+0x3a8>
    3f1c:	f6 c3 04             	test   $0x4,%bl
    3f1f:	0f 85 29 02 00 00    	jne    414e <send_headers+0x4be>
    3f25:	85 db                	test   %ebx,%ebx
    3f27:	74 13                	je     3f3c <send_headers+0x2ac>
    3f29:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3f31:	88 10                	mov    %dl,(%rax)
    3f33:	f6 c3 02             	test   $0x2,%bl
    3f36:	0f 85 3d 02 00 00    	jne    4179 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3f3c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    3f41:	bf 02 00 00 00       	mov    $0x2,%edi
    3f46:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    3f4e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    3f56:	e8 95 e4 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3f5b:	48 85 c0             	test   %rax,%rax
    3f5e:	0f 84 27 02 00 00    	je     418b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3f64:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    3f6c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    3f70:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    3f78:	66 89 10             	mov    %dx,(%rax)
}
    3f7b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    3f83:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3f8c:	0f 85 20 02 00 00    	jne    41b2 <send_headers+0x522>
    3f92:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    3f99:	5b                   	pop    %rbx
    3f9a:	5d                   	pop    %rbp
    3f9b:	41 5c                	pop    %r12
    3f9d:	41 5d                	pop    %r13
    3f9f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    3fa0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    3fa4:	0f 85 a4 fe ff ff    	jne    3e4e <send_headers+0x1be>
    3faa:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    3fae:	0f 85 9a fe ff ff    	jne    3e4e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3fb4:	66 0f 6f 05 d4 29 00 00 	movdqa 0x29d4(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    3fbc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    3fc6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3fce:	66 0f 6f 05 ca 29 00 00 	movdqa 0x29ca(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    3fd6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    3fde:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    3fe6:	e9 63 fe ff ff       	jmp    3e4e <send_headers+0x1be>
    3feb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    3ff0:	89 da                	mov    %ebx,%edx
    3ff2:	48 89 c7             	mov    %rax,%rdi
    3ff5:	4c 89 e6             	mov    %r12,%rsi
    3ff8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    3ffd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4002:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4005:	c1 e9 03             	shr    $0x3,%ecx
    4008:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    400b:	e9 c1 fe ff ff       	jmp    3ed1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4010:	66 0f 6f 05 18 29 00 00 	movdqa 0x2918(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4018:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4020:	66 0f 6f 05 28 29 00 00 	movdqa 0x2928(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    4028:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4030:	e9 cb fd ff ff       	jmp    3e00 <send_headers+0x170>
    4035:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4038:	89 da                	mov    %ebx,%edx
    403a:	48 89 c7             	mov    %rax,%rdi
    403d:	4c 89 e6             	mov    %r12,%rsi
    4040:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4045:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    404a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    404d:	c1 e9 03             	shr    $0x3,%ecx
    4050:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4053:	e9 e4 fe ff ff       	jmp    3f3c <send_headers+0x2ac>
    4058:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4060:	48 8d 1d 68 20 00 00 	lea    0x2068(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    4067:	e9 94 fd ff ff       	jmp    3e00 <send_headers+0x170>
    406c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4070:	66 0f 6f 05 f8 28 00 00 	movdqa 0x28f8(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4078:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4080:	66 0f 6f 05 f8 28 00 00 	movdqa 0x28f8(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4088:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4090:	e9 b0 fd ff ff       	jmp    3e45 <send_headers+0x1b5>
    4095:	0f 1f 00             	nopl   (%rax)
    4098:	66 0f 6f 05 d0 28 00 00 	movdqa 0x28d0(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    40a0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40a8:	66 0f 6f 05 d0 28 00 00 	movdqa 0x28d0(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    40b0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40b8:	e9 71 fd ff ff       	jmp    3e2e <send_headers+0x19e>
    40bd:	0f 1f 00             	nopl   (%rax)
    40c0:	66 0f 6f 05 68 28 00 00 	movdqa 0x2868(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    40c8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40d0:	66 0f 6f 05 88 28 00 00 	movdqa 0x2888(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    40d8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40e0:	e9 32 fd ff ff       	jmp    3e17 <send_headers+0x187>
    40e5:	0f 1f 00             	nopl   (%rax)
    40e8:	66 0f 6f 05 80 28 00 00 	movdqa 0x2880(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    40f0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40f8:	66 0f 6f 05 c0 28 00 00 	movdqa 0x28c0(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4100:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4108:	e9 6f fd ff ff       	jmp    3e7c <send_headers+0x1ec>
    410d:	0f 1f 00             	nopl   (%rax)
    4110:	66 0f 6f 05 58 28 00 00 	movdqa 0x2858(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4118:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4120:	66 0f 6f 05 88 28 00 00 	movdqa 0x2888(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    4128:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4130:	e9 30 fd ff ff       	jmp    3e65 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4135:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    413c:	89 db                	mov    %ebx,%ebx
    413e:	89 10                	mov    %edx,(%rax)
    4140:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4145:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4149:	e9 83 fd ff ff       	jmp    3ed1 <send_headers+0x241>
    414e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4155:	89 db                	mov    %ebx,%ebx
    4157:	89 10                	mov    %edx,(%rax)
    4159:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    415e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4162:	e9 d5 fd ff ff       	jmp    3f3c <send_headers+0x2ac>
    4167:	89 db                	mov    %ebx,%ebx
    4169:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    416f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4174:	e9 58 fd ff ff       	jmp    3ed1 <send_headers+0x241>
    4179:	89 db                	mov    %ebx,%ebx
    417b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4181:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4186:	e9 b1 fd ff ff       	jmp    3f3c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    418b:	48 8b 0d 8e 4e 00 00 	mov    0x4e8e(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4192:	ba 28 00 00 00       	mov    $0x28,%edx
    4197:	be 01 00 00 00       	mov    $0x1,%esi
    419c:	48 8d 3d 7d 22 00 00 	lea    0x227d(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    41a3:	e8 f8 e2 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    41a8:	bf 01 00 00 00       	mov    $0x1,%edi
    41ad:	e8 ce e2 ff ff       	call   2480 <exit@plt>
}
    41b2:	e8 59 e1 ff ff       	call   2310 <__stack_chk_fail@plt>
    41b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000041c0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    41c0:	f3 0f 1e fa          	endbr64
    41c4:	41 55                	push   %r13
    41c6:	49 89 d5             	mov    %rdx,%r13
    41c9:	41 54                	push   %r12
    41cb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    41ce:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    41d1:	55                   	push   %rbp
    41d2:	53                   	push   %rbx
    41d3:	48 89 f3             	mov    %rsi,%rbx
    41d6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    41da:	e8 11 e2 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    41df:	48 85 c0             	test   %rax,%rax
    41e2:	74 6b                	je     424f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    41e4:	4c 89 e7             	mov    %r12,%rdi
    41e7:	48 89 c5             	mov    %rax,%rbp
    41ea:	31 f6                	xor    %esi,%esi
    41ec:	31 c0                	xor    %eax,%eax
    41ee:	e8 6d e2 ff ff       	call   2460 <open@plt>
    41f3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    41f6:	85 c0                	test   %eax,%eax
    41f8:	0f 88 38 e3 ff ff    	js     2536 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    41fe:	48 89 da             	mov    %rbx,%rdx
    4201:	48 89 ee             	mov    %rbp,%rsi
    4204:	89 c7                	mov    %eax,%edi
    4206:	e8 65 e1 ff ff       	call   2370 <read@plt>
    if (ret < file_size) {
    420b:	48 98                	cltq
    420d:	48 39 d8             	cmp    %rbx,%rax
    4210:	7c 1e                	jl     4230 <copy_file_contents+0x70>
    close(fd);
    4212:	44 89 e7             	mov    %r12d,%edi
    4215:	e8 36 e1 ff ff       	call   2350 <close@plt>
    iov->iov_base = buf;
    421a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    421e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4222:	48 83 c4 08          	add    $0x8,%rsp
    4226:	5b                   	pop    %rbx
    4227:	5d                   	pop    %rbp
    4228:	41 5c                	pop    %r12
    422a:	41 5d                	pop    %r13
    422c:	c3                   	ret
    422d:	0f 1f 00             	nopl   (%rax)
    4230:	48 8b 0d e9 4d 00 00 	mov    0x4de9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4237:	ba 1a 00 00 00       	mov    $0x1a,%edx
    423c:	be 01 00 00 00       	mov    $0x1,%esi
    4241:	48 8d 3d 88 1e 00 00 	lea    0x1e88(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    4248:	e8 53 e2 ff ff       	call   24a0 <fwrite@plt>
    424d:	eb c3                	jmp    4212 <copy_file_contents+0x52>
    424f:	48 8b 0d ca 4d 00 00 	mov    0x4dca(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4256:	ba 28 00 00 00       	mov    $0x28,%edx
    425b:	be 01 00 00 00       	mov    $0x1,%esi
    4260:	48 8d 3d b9 21 00 00 	lea    0x21b9(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    4267:	e8 34 e2 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    426c:	bf 01 00 00 00       	mov    $0x1,%edi
    4271:	e8 0a e2 ff ff       	call   2480 <exit@plt>
    4276:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004280 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4280:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
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
    42a9:	0f 82 93 e2 ff ff    	jb     2542 <add_write_request.cold>
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
    4351:	0f 82 fb e1 ff ff    	jb     2552 <add_read_request.cold>
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
    448a:	0f 82 cc e0 ff ff    	jb     255c <_send_static_string_content.cold>
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
    4516:	48 8d 3d 03 1f 00 00 	lea    0x1f03(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
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
    4731:	e8 5a f5 ff ff       	call   3c90 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4736:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    473b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    473f:	4c 89 f7             	mov    %r14,%rdi
    4742:	e8 79 fa ff ff       	call   41c0 <copy_file_contents>
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
    4788:	48 8d 3d 91 1c 00 00 	lea    0x1c91(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
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
    49ae:	0f 82 b8 db ff ff    	jb     256c <add_accept_request.cold>
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
    4b40:	0f 84 68 da ff ff    	je     25ae <io_thread.cold+0x38>
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
    4b6f:	0f 88 0d da ff ff    	js     2582 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4b75:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4b7a:	ba 10 00 00 00       	mov    $0x10,%edx
    4b7f:	44 89 e7             	mov    %r12d,%edi
    4b82:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4b8b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4b93:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4b9b:	e8 a0 d8 ff ff       	call   2440 <bind@plt>
    4ba0:	85 c0                	test   %eax,%eax
    4ba2:	0f 88 12 da ff ff    	js     25ba <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4ba8:	be 0a 00 00 00       	mov    $0xa,%esi
    4bad:	44 89 e7             	mov    %r12d,%edi
    4bb0:	e8 4b d8 ff ff       	call   2400 <listen@plt>
    4bb5:	85 c0                	test   %eax,%eax
    4bb7:	0f 88 d1 d9 ff ff    	js     258e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4bbd:	ba db 18 00 00       	mov    $0x18db,%edx
    4bc2:	48 8d 35 b3 15 00 00 	lea    0x15b3(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4bc9:	bf 01 00 00 00       	mov    $0x1,%edi
    4bce:	31 c0                	xor    %eax,%eax
    4bd0:	e8 5b d8 ff ff       	call   2430 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4bd5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4bda:	48 89 d9             	mov    %rbx,%rcx
    4bdd:	44 89 e7             	mov    %r12d,%edi
    4be0:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4be5:	48 89 c6             	mov    %rax,%rsi
    4be8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4bed:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4bf2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4bfa:	e8 81 fd ff ff       	call   4980 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4bff:	bf 01 00 00 00       	mov    $0x1,%edi
    4c04:	be 10 00 00 00       	mov    $0x10,%esi
    4c09:	e8 72 d7 ff ff       	call   2380 <calloc@plt>
    void *buf = malloc(size);
    4c0e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4c13:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4c16:	e8 d5 d7 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    4c1b:	48 85 c0             	test   %rax,%rax
    4c1e:	0f 84 ae 04 00 00    	je     50d2 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    4c24:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4c28:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4c2f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    4c36:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4c3e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4c41:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4c46:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4c48:	f6 c1 02             	test   $0x2,%cl
    4c4b:	0f 85 0f 04 00 00    	jne    5060 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    4c51:	89 d0                	mov    %edx,%eax
    4c53:	29 f0                	sub    %esi,%eax
    4c55:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4c5c:	0f 82 42 d9 ff ff    	jb     25a4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4c62:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4c65:	48 8d 75 48          	lea    0x48(%rbp),%rsi
	sqe->addr3 = 0;
    4c69:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4c6d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c70:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4c77:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c7a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4c81:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c88:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4c8a:	8b 55 48             	mov    0x48(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4c8d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4c92:	48 c1 e0 06          	shl    $0x6,%rax
    4c96:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4c9e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4ca4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4ca7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4caf:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4cb3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4cbb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4cc3:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4cc7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4ccb:	e8 50 d6 ff ff       	call   2320 <io_uring_submit@plt>
  while (data->running == 1) {
    4cd0:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4cd4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4cd9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4ce1:	0f 85 d7 01 00 00    	jne    4ebe <io_thread+0x49e>
    4ce7:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4cec:	4d 89 ce             	mov    %r9,%r14
    4cef:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4cf4:	0f 1f 40 00          	nopl   0x0(%rax)
    4cf8:	48 8d 3d 93 14 00 00 	lea    0x1493(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4cff:	e8 cc d5 ff ff       	call   22d0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4d04:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4d0b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4d12:	c1 e9 0b             	shr    $0xb,%ecx
    4d15:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4d18:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4d20:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4d22:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4d2a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4d2c:	39 d0                	cmp    %edx,%eax
    4d2e:	74 36                	je     4d66 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4d30:	89 f8                	mov    %edi,%eax
    4d32:	21 d0                	and    %edx,%eax
    4d34:	d3 e0                	shl    %cl,%eax
    4d36:	48 c1 e0 04          	shl    $0x4,%rax
    4d3a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4d42:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4d4a:	0f 85 a8 01 00 00    	jne    4ef8 <io_thread+0x4d8>
    4d50:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4d54:	0f 85 0e 03 00 00    	jne    5068 <io_thread+0x648>
			if (cqe->res < 0)
    4d5a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4d5d:	83 c2 01             	add    $0x1,%edx
    4d60:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4d62:	85 c0                	test   %eax,%eax
    4d64:	79 b2                	jns    4d18 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    4d66:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    4d6f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4d70:	45 31 c0             	xor    %r8d,%r8d
    4d73:	31 d2                	xor    %edx,%edx
    4d75:	b9 01 00 00 00       	mov    $0x1,%ecx
    4d7a:	4c 89 f6             	mov    %r14,%rsi
    4d7d:	48 89 df             	mov    %rbx,%rdi
    4d80:	e8 9b d6 ff ff       	call   2420 <__io_uring_get_cqe@plt>
    4d85:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    4d88:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4d8d:	48 83 38 01          	cmpq   $0x1,(%rax)
    4d91:	0f 84 e1 02 00 00    	je     5078 <io_thread+0x658>
    4d97:	48 8d 3d 1a 14 00 00 	lea    0x141a(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4d9e:	e8 2d d5 ff ff       	call   22d0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4da3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4da8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4dab:	45 85 ff             	test   %r15d,%r15d
    4dae:	0f 88 c2 d7 ff ff    	js     2576 <io_thread.cold>
      if (cqe->res < 0) {
    4db4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    4db7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    4dbb:	85 c0                	test   %eax,%eax
    4dbd:	0f 88 d5 02 00 00    	js     5098 <io_thread+0x678>
      switch (req->event_type) {
    4dc3:	41 83 f8 01          	cmp    $0x1,%r8d
    4dc7:	0f 84 7b 01 00 00    	je     4f48 <io_thread+0x528>
    4dcd:	41 83 f8 02          	cmp    $0x2,%r8d
    4dd1:	0f 84 a1 01 00 00    	je     4f78 <io_thread+0x558>
    4dd7:	45 85 c0             	test   %r8d,%r8d
    4dda:	0f 85 50 01 00 00    	jne    4f30 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4de0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    4de5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    4dea:	48 89 d9             	mov    %rbx,%rcx
    4ded:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4df1:	e8 8a fb ff ff       	call   4980 <add_accept_request>
              add_read_request(cqe->res, &ring);
    4df6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4dfb:	48 89 de             	mov    %rbx,%rsi
    4dfe:	8b 78 08             	mov    0x8(%rax),%edi
    4e01:	e8 1a f5 ff ff       	call   4320 <add_read_request>
              free(req);
    4e06:	4c 89 e7             	mov    %r12,%rdi
    4e09:	e8 a2 d4 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4e0e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    4e13:	48 85 c0             	test   %rax,%rax
    4e16:	0f 85 14 01 00 00    	jne    4f30 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    4e1c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e23:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4e2a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4e2d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4e32:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4e34:	f6 c1 02             	test   $0x2,%cl
    4e37:	74 00                	je     4e39 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    4e39:	89 d0                	mov    %edx,%eax
    4e3b:	29 f0                	sub    %esi,%eax
    4e3d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4e44:	0f 82 50 d7 ff ff    	jb     259a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    4e4a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    4e4d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    4e52:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    4e56:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e59:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e60:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e63:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4e6a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e71:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4e73:	8b 55 48             	mov    0x48(%rbp),%edx
    4e76:	48 c1 e0 06          	shl    $0x6,%rax
    4e7a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4e82:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4e88:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4e8b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4e93:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4e97:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4e9f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4ea7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4eab:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    4eaf:	e8 6c d4 ff ff       	call   2320 <io_uring_submit@plt>
  while (data->running == 1) {
    4eb4:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
    4eb8:	0f 84 3a fe ff ff    	je     4cf8 <io_thread+0x2d8>
    4ebe:	48 8d 3d 2c 13 00 00 	lea    0x132c(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    4ec5:	e8 06 d4 ff ff       	call   22d0 <puts@plt>
}
    4eca:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    4ed2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4edb:	0f 85 18 02 00 00    	jne    50f9 <io_thread+0x6d9>
    4ee1:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    4ee8:	31 c0                	xor    %eax,%eax
    4eea:	5b                   	pop    %rbx
    4eeb:	5d                   	pop    %rbp
    4eec:	41 5c                	pop    %r12
    4eee:	41 5d                	pop    %r13
    4ef0:	41 5e                	pop    %r14
    4ef2:	41 5f                	pop    %r15
    4ef4:	c3                   	ret
    4ef5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    4ef8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    4efd:	48 85 c0             	test   %rax,%rax
    4f00:	0f 84 6a fe ff ff    	je     4d70 <io_thread+0x350>
      if (cqe->user_data == 1) {
    4f06:	48 83 38 01          	cmpq   $0x1,(%rax)
    4f0a:	0f 84 68 01 00 00    	je     5078 <io_thread+0x658>
    4f10:	48 8d 3d a1 12 00 00 	lea    0x12a1(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4f17:	e8 b4 d3 ff ff       	call   22d0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4f1c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4f21:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4f24:	e9 8b fe ff ff       	jmp    4db4 <io_thread+0x394>
    4f29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4f30:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4f38:	8b 02                	mov    (%rdx),%eax
    4f3a:	83 c0 01             	add    $0x1,%eax
    4f3d:	89 02                	mov    %eax,(%rdx)
}
    4f3f:	e9 d8 fe ff ff       	jmp    4e1c <io_thread+0x3fc>
    4f44:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    4f48:	85 c0                	test   %eax,%eax
    4f4a:	75 74                	jne    4fc0 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4f4c:	48 8b 0d cd 40 00 00 	mov    0x40cd(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4f53:	ba 0f 00 00 00       	mov    $0xf,%edx
    4f58:	be 01 00 00 00       	mov    $0x1,%esi
    4f5d:	48 8d 3d 7d 12 00 00 	lea    0x127d(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    4f64:	e8 37 d5 ff ff       	call   24a0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    4f69:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f6e:	e9 a0 fe ff ff       	jmp    4e13 <io_thread+0x3f3>
    4f73:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    4f78:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    4f7d:	45 31 ff             	xor    %r15d,%r15d
    4f80:	85 c0                	test   %eax,%eax
    4f82:	7e 20                	jle    4fa4 <io_thread+0x584>
    4f84:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    4f88:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    4f8b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    4f8f:	48 c1 e0 04          	shl    $0x4,%rax
    4f93:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    4f98:	e8 13 d3 ff ff       	call   22b0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    4f9d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    4fa2:	7f e4                	jg     4f88 <io_thread+0x568>
              close(req->client_socket);
    4fa4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    4fa9:	e8 a2 d3 ff ff       	call   2350 <close@plt>
              free(req);
    4fae:	4c 89 e7             	mov    %r12,%rdi
    4fb1:	e8 fa d2 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4fb6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    4fbb:	e9 53 fe ff ff       	jmp    4e13 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    4fc0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    4fc5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4fca:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    4fd2:	eb 11                	jmp    4fe5 <io_thread+0x5c5>
    4fd4:	0f 1f 40 00          	nopl   0x0(%rax)
    4fd8:	48 83 c0 01          	add    $0x1,%rax
    4fdc:	48 83 c2 01          	add    $0x1,%rdx
    4fe0:	48 39 c6             	cmp    %rax,%rsi
    4fe3:	74 4b                	je     5030 <io_thread+0x610>
        dest[i] = src[i];
    4fe5:	0f b6 0a             	movzbl (%rdx),%ecx
    4fe8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4fea:	80 f9 0d             	cmp    $0xd,%cl
    4fed:	75 e9                	jne    4fd8 <io_thread+0x5b8>
    4fef:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    4ff3:	75 e3                	jne    4fd8 <io_thread+0x5b8>
            dest[i] = '\0';
    4ff5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4ff8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    4ffd:	48 89 da             	mov    %rbx,%rdx
    5000:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5005:	e8 96 f7 ff ff       	call   47a0 <handle_http_method>
              free(req->iov[0].iov_base);
    500a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    500f:	e8 9c d2 ff ff       	call   22b0 <free@plt>
              free(req);
    5014:	4c 89 e7             	mov    %r12,%rdi
    5017:	e8 94 d2 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    501c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5021:	e9 ed fd ff ff       	jmp    4e13 <io_thread+0x3f3>
    5026:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5030:	48 8b 0d e9 3f 00 00 	mov    0x3fe9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5037:	ba 12 00 00 00       	mov    $0x12,%edx
    503c:	be 01 00 00 00       	mov    $0x1,%esi
    5041:	48 8d 3d ef 10 00 00 	lea    0x10ef(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    5048:	e8 53 d4 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    504d:	bf 01 00 00 00       	mov    $0x1,%edi
    5052:	e8 29 d4 ff ff       	call   2480 <exit@plt>
    5057:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5060:	e9 ec fb ff ff       	jmp    4c51 <io_thread+0x231>
    5065:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5068:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    506d:	e9 94 fe ff ff       	jmp    4f06 <io_thread+0x4e6>
    5072:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5078:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5080:	48 8d 3d 1d 11 00 00 	lea    0x111d(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    5087:	8b 02                	mov    (%rdx),%eax
    5089:	83 c0 01             	add    $0x1,%eax
    508c:	89 02                	mov    %eax,(%rdx)
    508e:	e8 3d d2 ff ff       	call   22d0 <puts@plt>
    5093:	e9 26 fe ff ff       	jmp    4ebe <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5098:	f7 d8                	neg    %eax
    509a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    509f:	89 c7                	mov    %eax,%edi
    50a1:	e8 3a d4 ff ff       	call   24e0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    50a6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    50ab:	be 01 00 00 00       	mov    $0x1,%esi
    50b0:	48 8b 3d 69 3f 00 00 	mov    0x3f69(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    50b7:	48 89 c1             	mov    %rax,%rcx
    50ba:	48 8d 15 8f 13 00 00 	lea    0x138f(%rip),%rdx        # 6450 <_IO_stdin_used+0x450>
    50c1:	31 c0                	xor    %eax,%eax
    50c3:	e8 e8 d3 ff ff       	call   24b0 <__fprintf_chk@plt>
          exit(1);
    50c8:	bf 01 00 00 00       	mov    $0x1,%edi
    50cd:	e8 ae d3 ff ff       	call   2480 <exit@plt>
    50d2:	48 8b 0d 47 3f 00 00 	mov    0x3f47(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    50d9:	ba 28 00 00 00       	mov    $0x28,%edx
    50de:	be 01 00 00 00       	mov    $0x1,%esi
    50e3:	48 8d 3d 36 13 00 00 	lea    0x1336(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    50ea:	e8 b1 d3 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    50ef:	bf 01 00 00 00       	mov    $0x1,%edi
    50f4:	e8 87 d3 ff ff       	call   2480 <exit@plt>
}
    50f9:	e8 12 d2 ff ff       	call   2310 <__stack_chk_fail@plt>
    50fe:	66 90                	xchg   %ax,%ax

0000000000005100 <receive>:
int receive(struct BarrierTask *data) {
    5100:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5104:	8b 87 24 02 00 00    	mov    0x224(%rdi),%eax
    510a:	85 c0                	test   %eax,%eax
    510c:	0f 8e f8 00 00 00    	jle    520a <receive+0x10a>
int receive(struct BarrierTask *data) {
    5112:	41 54                	push   %r12
    5114:	4c 63 e0             	movslq %eax,%r12
    5117:	48 89 fa             	mov    %rdi,%rdx
    511a:	55                   	push   %rbp
    511b:	49 c1 e4 09          	shl    $0x9,%r12
    511f:	53                   	push   %rbx
    5120:	48 8b b7 88 04 00 00 	mov    0x488(%rdi),%rsi
    5127:	49 01 f4             	add    %rsi,%r12
    512a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5130:	48 8b 2e             	mov    (%rsi),%rbp
    for (int x = 0 ; x < me->messages_count ; x++) {
    5133:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    513a:	48 85 ff             	test   %rdi,%rdi
    513d:	0f 8e a5 00 00 00    	jle    51e8 <receive+0xe8>
      data->sends++;
    5143:	48 8b 8a 00 05 00 00 	mov    0x500(%rdx),%rcx
    514a:	4c 8b 45 00          	mov    0x0(%rbp),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    514e:	4c 63 1a             	movslq (%rdx),%r11
    5151:	49 89 c9             	mov    %rcx,%r9
    5154:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5158:	49 f7 d9             	neg    %r9
    515b:	48 01 c7             	add    %rax,%rdi
    515e:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    5162:	4c 8b 8a 80 01 00 00 	mov    0x180(%rdx),%r9
      data->mailboxes[n].received++;
    5169:	4c 8b 86 80 01 00 00 	mov    0x180(%rsi),%r8
      data->n++;
    5170:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    5173:	49 29 c8             	sub    %rcx,%r8
    5176:	eb 11                	jmp    5189 <receive+0x89>
    5178:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5180:	48 83 c0 01          	add    $0x1,%rax
    5184:	48 39 c7             	cmp    %rax,%rdi
    5187:	74 5f                	je     51e8 <receive+0xe8>
      data->n++;
    5189:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    518d:	48 89 82 00 05 00 00 	mov    %rax,0x500(%rdx)
      data->n++;
    5194:	48 89 8a 80 01 00 00 	mov    %rcx,0x180(%rdx)
      data->mailboxes[n].received++;
    519b:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    519f:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    51a6:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    51ab:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    51af:	75 cf                	jne    5180 <receive+0x80>
    51b1:	48 63 9a 20 02 00 00 	movslq 0x220(%rdx),%rbx
    51b8:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    51bc:	75 c2                	jne    5180 <receive+0x80>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    51be:	bf 01 00 00 00       	mov    $0x1,%edi
    51c3:	b9 01 00 00 00       	mov    $0x1,%ecx
    51c8:	ba 01 00 00 00       	mov    $0x1,%edx
    51cd:	31 c0                	xor    %eax,%eax
    51cf:	48 8d 35 a2 12 00 00 	lea    0x12a2(%rip),%rsi        # 6478 <_IO_stdin_used+0x478>
    51d6:	e8 55 d2 ff ff       	call   2430 <__printf_chk@plt>
        exit(1);
    51db:	bf 01 00 00 00       	mov    $0x1,%edi
    51e0:	e8 9b d2 ff ff       	call   2480 <exit@plt>
    51e5:	0f 1f 00             	nopl   (%rax)
  for (int n = 0 ; n < data->thread_count; n++) {
    51e8:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    me->messages_count = 0;
    51ef:	48 c7 85 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rbp)
  for (int n = 0 ; n < data->thread_count; n++) {
    51fa:	49 39 f4             	cmp    %rsi,%r12
    51fd:	0f 85 2d ff ff ff    	jne    5130 <receive+0x30>
}
    5203:	5b                   	pop    %rbx
    5204:	31 c0                	xor    %eax,%eax
    5206:	5d                   	pop    %rbp
    5207:	41 5c                	pop    %r12
    5209:	c3                   	ret
    520a:	31 c0                	xor    %eax,%eax
    520c:	c3                   	ret
    520d:	0f 1f 00             	nopl   (%rax)

0000000000005210 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5210:	f3 0f 1e fa          	endbr64
    5214:	41 57                	push   %r15
    5216:	41 56                	push   %r14
    5218:	41 55                	push   %r13
    521a:	41 54                	push   %r12
    521c:	55                   	push   %rbp
    521d:	53                   	push   %rbx
    521e:	48 89 fb             	mov    %rdi,%rbx
    5221:	48 83 ec 28          	sub    $0x28,%rsp
  if (data->thread_index == data->task_index) {
    5225:	8b 07                	mov    (%rdi),%eax
    5227:	39 87 20 02 00 00    	cmp    %eax,0x220(%rdi)
    522d:	0f 84 65 01 00 00    	je     5398 <barriered_work+0x188>
    receive(data);
    5233:	e8 c8 fe ff ff       	call   5100 <receive>
    while (data->scheduled == 1) {
    5238:	83 bb 00 03 00 00 01 	cmpl   $0x1,0x300(%rbx)
    523f:	75 1b                	jne    525c <barriered_work+0x4c>
    5241:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    5248:	48 83 83 80 01 00 00 01 	addq   $0x1,0x180(%rbx)
      asm volatile ("sfence" ::: "memory");
    5250:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5253:	83 bb 00 03 00 00 01 	cmpl   $0x1,0x300(%rbx)
    525a:	74 ec                	je     5248 <barriered_work+0x38>
    if (data->sending == 1) {
    525c:	83 bb 08 05 00 00 01 	cmpl   $0x1,0x508(%rbx)
    5263:	74 14                	je     5279 <barriered_work+0x69>
  asm volatile ("mfence" ::: "memory");
    5265:	0f ae f0             	mfence
}
    5268:	48 83 c4 28          	add    $0x28,%rsp
    526c:	31 c0                	xor    %eax,%eax
    526e:	5b                   	pop    %rbx
    526f:	5d                   	pop    %rbp
    5270:	41 5c                	pop    %r12
    5272:	41 5d                	pop    %r13
    5274:	41 5e                	pop    %r14
    5276:	41 5f                	pop    %r15
    5278:	c3                   	ret
        for (int n = 0 ; n < data->thread_count; n++) {
    5279:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    527f:	85 c0                	test   %eax,%eax
    5281:	7e e2                	jle    5265 <barriered_work+0x55>
          if (n == data->thread_index) { continue; }
    5283:	8b b3 20 02 00 00    	mov    0x220(%rbx),%esi
    5289:	4c 63 f8             	movslq %eax,%r15
    528c:	48 8d 83 10 05 00 00 	lea    0x510(%rbx),%rax
    5293:	31 d2                	xor    %edx,%edx
    5295:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    529a:	48 8d 83 18 05 00 00 	lea    0x518(%rbx),%rax
    52a1:	89 74 24 04          	mov    %esi,0x4(%rsp)
    52a5:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    52aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    52b0:	39 54 24 04          	cmp    %edx,0x4(%rsp)
    52b4:	0f 84 c7 00 00 00    	je     5381 <barriered_work+0x171>
          struct Data *them = data->mailboxes[n].higher;
    52ba:	49 89 d0             	mov    %rdx,%r8
    52bd:	49 c1 e0 09          	shl    $0x9,%r8
    52c1:	4c 03 83 88 04 00 00 	add    0x488(%rbx),%r8
    52c8:	4d 8b 88 80 00 00 00 	mov    0x80(%r8),%r9
          for (; them->messages_count < min;) {
    52cf:	4d 8b 99 80 00 00 00 	mov    0x80(%r9),%r11
    52d6:	49 63 b9 88 00 00 00 	movslq 0x88(%r9),%rdi
    52dd:	49 39 fb             	cmp    %rdi,%r11
    52e0:	0f 8d 9b 00 00 00    	jge    5381 <barriered_work+0x171>
    52e6:	49 89 fa             	mov    %rdi,%r10
    52e9:	4c 8b b3 80 01 00 00 	mov    0x180(%rbx),%r14
    52f0:	49 8b a8 00 01 00 00 	mov    0x100(%r8),%rbp
    52f7:	4d 29 da             	sub    %r11,%r10
            them->messages[them->messages_count++] = data->message; 
    52fa:	49 8b 09             	mov    (%r9),%rcx
    52fd:	49 8d 42 ff          	lea    -0x1(%r10),%rax
    5301:	48 83 f8 02          	cmp    $0x2,%rax
    5305:	0f 86 85 02 00 00    	jbe    5590 <barriered_work+0x380>
    530b:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5313:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    531b:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    531f:	4c 8d 2c 31          	lea    (%rcx,%rsi,1),%r13
    5323:	4c 39 6c 24 08       	cmp    %r13,0x8(%rsp)
    5328:	0f 83 ea 01 00 00    	jae    5518 <barriered_work+0x308>
    532e:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    5333:	4d 39 ec             	cmp    %r13,%r12
    5336:	0f 83 dc 01 00 00    	jae    5518 <barriered_work+0x308>
    533c:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    5340:	48 01 ce             	add    %rcx,%rsi
    5343:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5348:	48 8b 83 10 05 00 00 	mov    0x510(%rbx),%rax
          for (; them->messages_count < min;) {
    534f:	49 83 c3 08          	add    $0x8,%r11
            them->messages[them->messages_count++] = data->message; 
    5353:	49 89 43 f8          	mov    %rax,-0x8(%r11)
          for (; them->messages_count < min;) {
    5357:	49 39 f3             	cmp    %rsi,%r11
    535a:	75 ec                	jne    5348 <barriered_work+0x138>
    535c:	0f 1f 40 00          	nopl   0x0(%rax)
    5360:	4b 8d 34 16          	lea    (%r14,%r10,1),%rsi
    5364:	4c 01 d5             	add    %r10,%rbp
    5367:	48 89 b3 80 01 00 00 	mov    %rsi,0x180(%rbx)
    536e:	49 89 a8 00 01 00 00 	mov    %rbp,0x100(%r8)
    5375:	49 89 b9 80 00 00 00 	mov    %rdi,0x80(%r9)
    537c:	48 89 44 f9 f8       	mov    %rax,-0x8(%rcx,%rdi,8)
        for (int n = 0 ; n < data->thread_count; n++) {
    5381:	48 83 c2 01          	add    $0x1,%rdx
    5385:	49 39 d7             	cmp    %rdx,%r15
    5388:	0f 85 22 ff ff ff    	jne    52b0 <barriered_work+0xa0>
    538e:	e9 d2 fe ff ff       	jmp    5265 <barriered_work+0x55>
    5393:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      receive(data);
    5398:	e8 63 fd ff ff       	call   5100 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    539d:	8b 8b 24 02 00 00    	mov    0x224(%rbx),%ecx
        int t = data->task_index;
    53a3:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    53a5:	85 c9                	test   %ecx,%ecx
    53a7:	0f 8e 8b 00 00 00    	jle    5438 <barriered_work+0x228>
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    53ad:	48 8b 93 18 02 00 00 	mov    0x218(%rbx),%rdx
    53b4:	48 8b 7a 10          	mov    0x10(%rdx),%rdi
    53b8:	48 63 d0             	movslq %eax,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
    53bb:	83 c0 01             	add    $0x1,%eax
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    53be:	48 8d 34 92          	lea    (%rdx,%rdx,4),%rsi
    53c2:	4c 8d 1c 72          	lea    (%rdx,%rsi,2),%r11
              int next_task = abs((t + 1) % (data->thread_count));
    53c6:	99                   	cltd
    53c7:	48 63 f1             	movslq %ecx,%rsi
    53ca:	f7 f9                	idiv   %ecx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    53cc:	49 c1 e3 07          	shl    $0x7,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    53d0:	89 d0                	mov    %edx,%eax
    53d2:	f7 d8                	neg    %eax
    53d4:	0f 48 c2             	cmovs  %edx,%eax
    53d7:	48 c1 e6 08          	shl    $0x8,%rsi
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    53db:	31 ed                	xor    %ebp,%ebp
    53dd:	48 98                	cltq
    53df:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    53e3:	4c 8d 14 50          	lea    (%rax,%rdx,2),%r10
    53e7:	49 c1 e2 07          	shl    $0x7,%r10
    53eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    53f0:	48 8b 44 2f 20       	mov    0x20(%rdi,%rbp,1),%rax
    53f5:	4c 8d 44 2d 00       	lea    0x0(%rbp,%rbp,1),%r8
    53fa:	4e 8b 8c 18 88 04 00 00 	mov    0x488(%rax,%r11,1),%r9
    5402:	31 c0                	xor    %eax,%eax
    5404:	0f 1f 40 00          	nopl   0x0(%rax)
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5408:	48 8b 54 07 20       	mov    0x20(%rdi,%rax,1),%rdx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    540d:	49 8b 8c 41 80 00 00 00 	mov    0x80(%r9,%rax,2),%rcx
          for (int b = 0; b < data->thread_count ; b++) {
    5415:	48 05 00 01 00 00    	add    $0x100,%rax
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    541b:	4a 8b 94 12 88 04 00 00 	mov    0x488(%rdx,%r10,1),%rdx
    5423:	4a 89 0c 02          	mov    %rcx,(%rdx,%r8,1)
          for (int b = 0; b < data->thread_count ; b++) {
    5427:	48 39 f0             	cmp    %rsi,%rax
    542a:	75 dc                	jne    5408 <barriered_work+0x1f8>
        for (int y = 0; y < data->thread_count ; y++) {
    542c:	48 81 c5 00 01 00 00 	add    $0x100,%rbp
    5433:	48 39 f5             	cmp    %rsi,%rbp
    5436:	75 b8                	jne    53f0 <barriered_work+0x1e0>
      asm volatile ("mfence" ::: "memory");
    5438:	0f ae f0             	mfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    543b:	48 8b b3 00 04 00 00 	mov    0x400(%rbx),%rsi
    5442:	31 ff                	xor    %edi,%edi
    5444:	48 c1 e6 05          	shl    $0x5,%rsi
    5448:	48 03 b3 08 03 00 00 	add    0x308(%rbx),%rsi
    544f:	e8 9c ce ff ff       	call   22f0 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    5454:	48 8b 93 18 02 00 00 	mov    0x218(%rbx),%rdx
    while (data->scheduled == 1) {
    545b:	83 bb 00 03 00 00 01 	cmpl   $0x1,0x300(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5462:	48 8b 42 30          	mov    0x30(%rdx),%rax
    5466:	8b 70 10             	mov    0x10(%rax),%esi
    5469:	8d 6e 01             	lea    0x1(%rsi),%ebp
    546c:	89 68 10             	mov    %ebp,0x10(%rax)
    while (data->scheduled == 1) {
    546f:	74 0e                	je     547f <barriered_work+0x26f>
    5471:	eb 64                	jmp    54d7 <barriered_work+0x2c7>
    5473:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (modcount != data->thread->protected_state->modcount) {
    5478:	48 8b 93 18 02 00 00 	mov    0x218(%rbx),%rdx
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    547f:	48 63 83 20 02 00 00 	movslq 0x220(%rbx),%rax
      data->n++;
    5486:	48 83 83 80 01 00 00 01 	addq   $0x1,0x180(%rbx)
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    548e:	48 c1 e0 08          	shl    $0x8,%rax
    5492:	48 03 42 10          	add    0x10(%rdx),%rax
    5496:	48 63 13             	movslq (%rbx),%rdx
    5499:	48 8d 0c 92          	lea    (%rdx,%rdx,4),%rcx
    549d:	48 8d 3c 4a          	lea    (%rdx,%rcx,2),%rdi
    54a1:	48 c1 e7 07          	shl    $0x7,%rdi
    54a5:	48 03 78 20          	add    0x20(%rax),%rdi
    54a9:	ff 93 10 02 00 00    	call   *0x210(%rbx)
      asm volatile ("sfence" ::: "memory");
    54af:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    54b2:	83 bb 00 03 00 00 01 	cmpl   $0x1,0x300(%rbx)
    54b9:	74 bd                	je     5478 <barriered_work+0x268>
    if (modcount != data->thread->protected_state->modcount) {
    54bb:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    54c2:	48 8b 40 30          	mov    0x30(%rax),%rax
    54c6:	3b 68 10             	cmp    0x10(%rax),%ebp
    54c9:	74 0c                	je     54d7 <barriered_work+0x2c7>
    54cb:	48 8d 3d 32 0d 00 00 	lea    0xd32(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    54d2:	e8 f9 cd ff ff       	call   22d0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    54d7:	48 8b b3 00 04 00 00 	mov    0x400(%rbx),%rsi
    54de:	31 ff                	xor    %edi,%edi
    54e0:	48 c1 e6 05          	shl    $0x5,%rsi
    54e4:	48 03 b3 08 03 00 00 	add    0x308(%rbx),%rsi
    54eb:	48 83 c6 10          	add    $0x10,%rsi
    54ef:	e8 fc cd ff ff       	call   22f0 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    54f4:	48 8b 83 00 04 00 00 	mov    0x400(%rbx),%rax
    54fb:	48 83 c0 01          	add    $0x1,%rax
    54ff:	48 99                	cqto
    5501:	48 f7 bb 80 03 00 00 	idivq  0x380(%rbx)
    5508:	48 89 93 00 04 00 00 	mov    %rdx,0x400(%rbx)
    550f:	e9 51 fd ff ff       	jmp    5265 <barriered_work+0x55>
    5514:	0f 1f 40 00          	nopl   0x0(%rax)
    5518:	48 8b 83 10 05 00 00 	mov    0x510(%rbx),%rax
    551f:	4d 89 d5             	mov    %r10,%r13
    5522:	4c 89 e6             	mov    %r12,%rsi
    5525:	49 d1 ed             	shr    %r13
    5528:	49 c1 e5 04          	shl    $0x4,%r13
    552c:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5531:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
    5536:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    553a:	4d 01 e5             	add    %r12,%r13
    553d:	f6 44 24 18 10       	testb  $0x10,0x18(%rsp)
    5542:	74 14                	je     5558 <barriered_work+0x348>
            them->messages[them->messages_count++] = data->message; 
    5544:	48 83 c6 10          	add    $0x10,%rsi
    5548:	41 0f 11 04 24       	movups %xmm0,(%r12)
          for (; them->messages_count < min;) {
    554d:	49 39 f5             	cmp    %rsi,%r13
    5550:	74 16                	je     5568 <barriered_work+0x358>
    5552:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    5558:	0f 11 06             	movups %xmm0,(%rsi)
    555b:	48 83 c6 20          	add    $0x20,%rsi
    555f:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
          for (; them->messages_count < min;) {
    5563:	49 39 f5             	cmp    %rsi,%r13
    5566:	75 f0                	jne    5558 <barriered_work+0x348>
    5568:	4c 89 d6             	mov    %r10,%rsi
    556b:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    556f:	4c 01 de             	add    %r11,%rsi
    5572:	41 f6 c2 01          	test   $0x1,%r10b
    5576:	0f 84 e4 fd ff ff    	je     5360 <barriered_work+0x150>
            them->messages[them->messages_count++] = data->message; 
    557c:	48 8b 83 10 05 00 00 	mov    0x510(%rbx),%rax
    5583:	48 89 04 f1          	mov    %rax,(%rcx,%rsi,8)
          for (; them->messages_count < min;) {
    5587:	e9 d4 fd ff ff       	jmp    5360 <barriered_work+0x150>
    558c:	0f 1f 40 00          	nopl   0x0(%rax)
    5590:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5598:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    55a0:	e9 97 fd ff ff       	jmp    533c <barriered_work+0x12c>
    55a5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000055b0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    55b0:	f3 0f 1e fa          	endbr64
    55b4:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    55b8:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    55bf:	48 8b 40 38          	mov    0x38(%rax),%rax
    55c3:	48 63 10             	movslq (%rax),%rdx
    55c6:	85 d2                	test   %edx,%edx
    55c8:	7e 34                	jle    55fe <barriered_work_ingest+0x4e>
    55ca:	48 8b 40 08          	mov    0x8(%rax),%rax
    55ce:	48 c1 e2 08          	shl    $0x8,%rdx
    55d2:	48 01 c2             	add    %rax,%rdx
    55d5:	0f 1f 00             	nopl   (%rax)
    if (data->thread->buffers->buffer[x].available == 1) {
    55d8:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    55df:	75 12                	jne    55f3 <barriered_work_ingest+0x43>
      data->ingest_count++;
    55e1:	48 83 87 80 04 00 00 01 	addq   $0x1,0x480(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    55e9:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    55f3:	48 05 00 01 00 00    	add    $0x100,%rax
    55f9:	48 39 d0             	cmp    %rdx,%rax
    55fc:	75 da                	jne    55d8 <barriered_work_ingest+0x28>
  asm volatile ("mfence" ::: "memory");
    55fe:	0f ae f0             	mfence
  barriered_work(data);
    5601:	e8 0a fc ff ff       	call   5210 <barriered_work>
}
    5606:	31 c0                	xor    %eax,%eax
    5608:	48 83 c4 08          	add    $0x8,%rsp
    560c:	c3                   	ret
    560d:	0f 1f 00             	nopl   (%rax)

0000000000005610 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5610:	f3 0f 1e fa          	endbr64
}
    5614:	31 c0                	xor    %eax,%eax
    5616:	c3                   	ret
    5617:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005620 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5620:	f3 0f 1e fa          	endbr64
    5624:	31 c0                	xor    %eax,%eax
    5626:	c3                   	ret
    5627:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005630 <after>:
int after(struct timespec left, struct timespec right) {
    5630:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5634:	31 c0                	xor    %eax,%eax
    5636:	48 39 d7             	cmp    %rdx,%rdi
    5639:	7e 08                	jle    5643 <after+0x13>
    563b:	31 c0                	xor    %eax,%eax
    563d:	48 39 ce             	cmp    %rcx,%rsi
    5640:	0f 9f c0             	setg   %al
}
    5643:	c3                   	ret
    5644:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    564f:	90                   	nop

0000000000005650 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5650:	f3 0f 1e fa          	endbr64
    5654:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5659:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    565e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5660:	48 39 d7             	cmp    %rdx,%rdi
    5663:	7f 18                	jg     567d <within+0x2d>
    5665:	4d 39 d8             	cmp    %r11,%r8
    5668:	0f 9e c2             	setle  %dl
    566b:	48 39 ce             	cmp    %rcx,%rsi
    566e:	0f 9e c0             	setle  %al
    5671:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5673:	31 c0                	xor    %eax,%eax
    5675:	4d 39 d1             	cmp    %r10,%r9
    5678:	0f 9e c0             	setle  %al
    567b:	21 d0                	and    %edx,%eax
}
    567d:	c3                   	ret
    567e:	66 90                	xchg   %ax,%ax

0000000000005680 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5680:	f3 0f 1e fa          	endbr64
    5684:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5689:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    568e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    5693:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    5698:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    569d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    56a2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    56a7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    56ac:	48 39 fe             	cmp    %rdi,%rsi
    56af:	7d 2f                	jge    56e0 <overlap+0x60>
    56b1:	48 39 ca             	cmp    %rcx,%rdx
    56b4:	7d 62                	jge    5718 <overlap+0x98>
    56b6:	4d 39 da             	cmp    %r11,%r10
    56b9:	7d 0e                	jge    56c9 <overlap+0x49>
    return 1;
    56bb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    56c0:	4d 39 c1             	cmp    %r8,%r9
    56c3:	0f 8c 7f 00 00 00    	jl     5748 <overlap+0xc8>
  return 0;
    56c9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    56cb:	4d 39 c1             	cmp    %r8,%r9
    56ce:	7f 4c                	jg     571c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    56d0:	31 c0                	xor    %eax,%eax
    56d2:	4d 39 da             	cmp    %r11,%r10
    56d5:	0f 9e c0             	setle  %al
    56d8:	c3                   	ret
    56d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    56e0:	7e 4e                	jle    5730 <overlap+0xb0>
    56e2:	48 39 ca             	cmp    %rcx,%rdx
    56e5:	7f 39                	jg     5720 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    56e7:	75 31                	jne    571a <overlap+0x9a>
    56e9:	4d 39 c1             	cmp    %r8,%r9
    56ec:	7c 2c                	jl     571a <overlap+0x9a>
    return 1;
    56ee:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    56f3:	4d 39 da             	cmp    %r11,%r10
    56f6:	7d 24                	jge    571c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    56f8:	48 39 ca             	cmp    %rcx,%rdx
    56fb:	0f 94 c2             	sete   %dl
    56fe:	48 39 fe             	cmp    %rdi,%rsi
    5701:	0f 94 c0             	sete   %al
    5704:	21 c2                	and    %eax,%edx
    5706:	31 c0                	xor    %eax,%eax
    5708:	4d 39 c1             	cmp    %r8,%r9
    570b:	0f 94 c0             	sete   %al
    570e:	21 d0                	and    %edx,%eax
    5710:	c3                   	ret
    5711:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5718:	74 af                	je     56c9 <overlap+0x49>
  return 0;
    571a:	31 c0                	xor    %eax,%eax
}
    571c:	c3                   	ret
    571d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5720:	4d 39 da             	cmp    %r11,%r10
    5723:	7e c4                	jle    56e9 <overlap+0x69>
    return 1;
    5725:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    572a:	4d 39 c1             	cmp    %r8,%r9
    572d:	7e ba                	jle    56e9 <overlap+0x69>
    572f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5730:	48 39 ca             	cmp    %rcx,%rdx
    5733:	7c 94                	jl     56c9 <overlap+0x49>
    5735:	4d 39 c1             	cmp    %r8,%r9
    5738:	7d b4                	jge    56ee <overlap+0x6e>
    573a:	48 39 ca             	cmp    %rcx,%rdx
    573d:	74 91                	je     56d0 <overlap+0x50>
    573f:	eb d9                	jmp    571a <overlap+0x9a>
    5741:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5748:	c3                   	ret
    5749:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005750 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5750:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5754:	85 f6                	test   %esi,%esi
    5756:	0f 8e 49 03 00 00    	jle    5aa5 <verify+0x355>
int verify(struct KernelThread *thread_data, int thread_count) {
    575c:	41 57                	push   %r15
    575e:	41 89 f7             	mov    %esi,%r15d
    5761:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5763:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5766:	41 55                	push   %r13
    5768:	41 54                	push   %r12
    576a:	55                   	push   %rbp
    576b:	53                   	push   %rbx
    576c:	48 8d 5f 20          	lea    0x20(%rdi),%rbx
    5770:	48 83 ec 48          	sub    $0x48,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5774:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5779:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    577e:	45 31 e4             	xor    %r12d,%r12d
    5781:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
      if (z != x)  {
    5786:	45 39 e6             	cmp    %r12d,%r14d
    5789:	0f 84 4f 02 00 00    	je     59de <verify+0x28e>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    578f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5794:	8b 50 08             	mov    0x8(%rax),%edx
    5797:	85 d2                	test   %edx,%edx
    5799:	0f 8e 3f 02 00 00    	jle    59de <verify+0x28e>
    579f:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    57a7:	31 ed                	xor    %ebp,%ebp
    57a9:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    57ae:	44 89 7c 24 34       	mov    %r15d,0x34(%rsp)
    57b3:	45 89 f7             	mov    %r14d,%r15d
    57b6:	41 89 ee             	mov    %ebp,%r14d
    57b9:	44 89 fa             	mov    %r15d,%edx
    57bc:	48 8d 35 51 0a 00 00 	lea    0xa51(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    57c3:	bf 01 00 00 00       	mov    $0x1,%edi
    57c8:	31 c0                	xor    %eax,%eax
    57ca:	e8 61 cc ff ff       	call   2430 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    57cf:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    57d4:	8b 40 08             	mov    0x8(%rax),%eax
    57d7:	85 c0                	test   %eax,%eax
    57d9:	0f 8e d7 01 00 00    	jle    59b6 <verify+0x266>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    57df:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    57e4:	44 89 74 24 38       	mov    %r14d,0x38(%rsp)
    57e9:	31 db                	xor    %ebx,%ebx
    57eb:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    57f0:	4c 8b 20             	mov    (%rax),%r12
    57f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    57f8:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    57fd:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    5801:	4c 8b 3c 24          	mov    (%rsp),%r15
    5805:	48 8d 35 1d 0a 00 00 	lea    0xa1d(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    580c:	48 8d 04 43          	lea    (%rbx,%rax,2),%rax
    5810:	bf 01 00 00 00       	mov    $0x1,%edi
    5815:	49 89 c6             	mov    %rax,%r14
    5818:	48 8b 45 00          	mov    0x0(%rbp),%rax
    581c:	4b 8b 8c 3c 00 04 00 00 	mov    0x400(%r12,%r15,1),%rcx
    5824:	49 c1 e6 07          	shl    $0x7,%r14
    5828:	4a 8b 94 30 00 04 00 00 	mov    0x400(%rax,%r14,1),%rdx
    5830:	31 c0                	xor    %eax,%eax
    5832:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    5837:	e8 f4 cb ff ff       	call   2430 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    583c:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5841:	4c 8b 20             	mov    (%rax),%r12
    5844:	4b 83 bc 3c 00 04 00 00 00 	cmpq   $0x0,0x400(%r12,%r15,1)
    584d:	0f 8e 47 01 00 00    	jle    599a <verify+0x24a>
    5853:	4c 03 75 00          	add    0x0(%rbp),%r14
    5857:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    585c:	ba 01 00 00 00       	mov    $0x1,%edx
    5861:	4d 89 f5             	mov    %r14,%r13
    5864:	4d 8b b5 00 04 00 00 	mov    0x400(%r13),%r14
    586b:	4d 85 f6             	test   %r14,%r14
    586e:	0f 8e 21 01 00 00    	jle    5995 <verify+0x245>
    5874:	0f 1f 40 00          	nopl   0x0(%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5878:	48 89 d5             	mov    %rdx,%rbp
    587b:	48 8b 04 24          	mov    (%rsp),%rax
    587f:	31 db                	xor    %ebx,%ebx
    5881:	4d 89 f2             	mov    %r14,%r10
    5884:	48 c1 e5 05          	shl    $0x5,%rbp
    5888:	48 83 ed 20          	sub    $0x20,%rbp
    588c:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    5890:	49 89 ee             	mov    %rbp,%r14
    5893:	48 89 dd             	mov    %rbx,%rbp
    5896:	48 89 d3             	mov    %rdx,%rbx
    5899:	eb 32                	jmp    58cd <verify+0x17d>
    589b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    58a0:	4c 39 c2             	cmp    %r8,%rdx
    58a3:	0f 8d 57 01 00 00    	jge    5a00 <verify+0x2b0>
    58a9:	4c 39 df             	cmp    %r11,%rdi
    58ac:	7e 05                	jle    58b3 <verify+0x163>
    58ae:	49 39 c1             	cmp    %rax,%r9
    58b1:	7c 75                	jl     5928 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    58b3:	4c 39 df             	cmp    %r11,%rdi
    58b6:	0f 8d ab 01 00 00    	jge    5a67 <verify+0x317>
    58bc:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    58c0:	48 83 c5 01          	add    $0x1,%rbp
    58c4:	49 39 ea             	cmp    %rbp,%r10
    58c7:	0f 8e a8 00 00 00    	jle    5975 <verify+0x225>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    58cd:	49 8b 97 08 03 00 00 	mov    0x308(%r15),%rdx
    58d4:	48 89 e8             	mov    %rbp,%rax
    58d7:	48 c1 e0 05          	shl    $0x5,%rax
    58db:	49 03 85 08 03 00 00 	add    0x308(%r13),%rax
    58e2:	4c 01 f2             	add    %r14,%rdx
    58e5:	48 8b 08             	mov    (%rax),%rcx
    58e8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    58ec:	48 8b 32             	mov    (%rdx),%rsi
    58ef:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    58f3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    58f7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    58fb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    58ff:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    5903:	48 39 f1             	cmp    %rsi,%rcx
    5906:	7c 98                	jl     58a0 <verify+0x150>
    5908:	0f 8e 42 01 00 00    	jle    5a50 <verify+0x300>
    590e:	4c 39 c2             	cmp    %r8,%rdx
    5911:	0f 8f f9 00 00 00    	jg     5a10 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5917:	75 a7                	jne    58c0 <verify+0x170>
    5919:	4c 39 df             	cmp    %r11,%rdi
    591c:	7f a2                	jg     58c0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    591e:	49 39 c1             	cmp    %rax,%r9
    5921:	7c 9d                	jl     58c0 <verify+0x170>
    5923:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5928:	49 89 c1             	mov    %rax,%r9
    592b:	48 89 f9             	mov    %rdi,%rcx
    592e:	48 89 f2             	mov    %rsi,%rdx
    5931:	bf 01 00 00 00       	mov    $0x1,%edi
    5936:	48 8d 35 63 0b 00 00 	lea    0xb63(%rip),%rsi        # 64a0 <_IO_stdin_used+0x4a0>
    593d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    593f:	48 83 c5 01          	add    $0x1,%rbp
    5943:	e8 e8 ca ff ff       	call   2430 <__printf_chk@plt>
    5948:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    594d:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    5952:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5955:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    595a:	4d 8b 95 00 04 00 00 	mov    0x400(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5961:	4c 8b 20             	mov    (%rax),%r12
    5964:	48 8b 04 24          	mov    (%rsp),%rax
    5968:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    596c:	49 39 ea             	cmp    %rbp,%r10
    596f:	0f 8f 58 ff ff ff    	jg     58cd <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5975:	48 89 da             	mov    %rbx,%rdx
    5978:	49 3b 9f 00 04 00 00 	cmp    0x400(%r15),%rbx
    597f:	7d 14                	jge    5995 <verify+0x245>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5981:	4d 8b b5 00 04 00 00 	mov    0x400(%r13),%r14
    5988:	48 83 c2 01          	add    $0x1,%rdx
    598c:	4d 85 f6             	test   %r14,%r14
    598f:	0f 8f e3 fe ff ff    	jg     5878 <verify+0x128>
    5995:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    599a:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    599f:	48 83 c3 01          	add    $0x1,%rbx
    59a3:	39 58 08             	cmp    %ebx,0x8(%rax)
    59a6:	0f 8f 4c fe ff ff    	jg     57f8 <verify+0xa8>
    59ac:	44 8b 74 24 38       	mov    0x38(%rsp),%r14d
    59b1:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    59b6:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    59bb:	48 81 04 24 80 05 00 00 	addq   $0x580,(%rsp)
    59c3:	41 83 c6 01          	add    $0x1,%r14d
    59c7:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    59cb:	0f 8f e8 fd ff ff    	jg     57b9 <verify+0x69>
    59d1:	45 89 fe             	mov    %r15d,%r14d
    59d4:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    59d9:	44 8b 7c 24 34       	mov    0x34(%rsp),%r15d
    for (int z = 0 ; z < thread_count; z++) {
    59de:	48 81 44 24 08 00 01 00 00 	addq   $0x100,0x8(%rsp)
    59e7:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    59ec:	41 39 c7             	cmp    %eax,%r15d
    59ef:	0f 84 80 00 00 00    	je     5a75 <verify+0x325>
    59f5:	41 89 c4             	mov    %eax,%r12d
    59f8:	e9 89 fd ff ff       	jmp    5786 <verify+0x36>
    59fd:	0f 1f 00             	nopl   (%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5a00:	0f 85 ba fe ff ff    	jne    58c0 <verify+0x170>
    5a06:	e9 a8 fe ff ff       	jmp    58b3 <verify+0x163>
    5a0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5a10:	49 39 c1             	cmp    %rax,%r9
    5a13:	7e 09                	jle    5a1e <verify+0x2ce>
    5a15:	4c 39 df             	cmp    %r11,%rdi
    5a18:	0f 8c 0a ff ff ff    	jl     5928 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5a1e:	4c 39 df             	cmp    %r11,%rdi
    5a21:	0f 8f 99 fe ff ff    	jg     58c0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5a27:	49 39 c1             	cmp    %rax,%r9
    5a2a:	0f 8d f8 fe ff ff    	jge    5928 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5a30:	48 39 f1             	cmp    %rsi,%rcx
    5a33:	0f 85 87 fe ff ff    	jne    58c0 <verify+0x170>
    5a39:	4c 39 c2             	cmp    %r8,%rdx
    5a3c:	0f 85 7e fe ff ff    	jne    58c0 <verify+0x170>
    5a42:	4c 39 df             	cmp    %r11,%rdi
    5a45:	0f 84 dd fe ff ff    	je     5928 <verify+0x1d8>
    5a4b:	e9 70 fe ff ff       	jmp    58c0 <verify+0x170>
    5a50:	4c 39 c2             	cmp    %r8,%rdx
    5a53:	0f 8c 5a fe ff ff    	jl     58b3 <verify+0x163>
    5a59:	4c 39 df             	cmp    %r11,%rdi
    5a5c:	7e c9                	jle    5a27 <verify+0x2d7>
    5a5e:	4c 39 c2             	cmp    %r8,%rdx
    5a61:	0f 85 59 fe ff ff    	jne    58c0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5a67:	49 39 c1             	cmp    %rax,%r9
    5a6a:	0f 8f 50 fe ff ff    	jg     58c0 <verify+0x170>
    5a70:	e9 b3 fe ff ff       	jmp    5928 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    5a75:	48 81 44 24 10 00 01 00 00 	addq   $0x100,0x10(%rsp)
    5a7e:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    5a83:	41 8d 46 01          	lea    0x1(%r14),%eax
    5a87:	45 39 e6             	cmp    %r12d,%r14d
    5a8a:	74 08                	je     5a94 <verify+0x344>
    5a8c:	41 89 c6             	mov    %eax,%r14d
    5a8f:	e9 e5 fc ff ff       	jmp    5779 <verify+0x29>
}
    5a94:	48 83 c4 48          	add    $0x48,%rsp
    5a98:	31 c0                	xor    %eax,%eax
    5a9a:	5b                   	pop    %rbx
    5a9b:	5d                   	pop    %rbp
    5a9c:	41 5c                	pop    %r12
    5a9e:	41 5d                	pop    %r13
    5aa0:	41 5e                	pop    %r14
    5aa2:	41 5f                	pop    %r15
    5aa4:	c3                   	ret
    5aa5:	31 c0                	xor    %eax,%eax
    5aa7:	c3                   	ret

Disassembly of section .fini:

0000000000005aa8 <_fini>:
    5aa8:	f3 0f 1e fa          	endbr64
    5aac:	48 83 ec 08          	sub    $0x8,%rsp
    5ab0:	48 83 c4 08          	add    $0x8,%rsp
    5ab4:	c3                   	ret
